#!/usr/bin/env python3
"""Run the test binary's actual bytes in a small RISC-V interpreter.

This is a sanity check, not part of the proof and not trusted by it. The
interpreter below is about a hundred lines written for this one binary; it
is not QEMU and not the Rocq model. It answers four questions the proof
cannot answer about itself:

  1. Does the binary run at all, and exit 0, on concrete inputs?
  2. Do the nine instructions of eff_close_time agree with the maths in
     CloseTimeSpec.v on random inputs? (The proof says they agree on all
     inputs. If this disagreed, the spec in Rocq and this transcription of
     it would differ, or the interpreter would be wrong.)
  3. Do the test's checks have teeth? A copy of the binary with one branch
     removed (the previous-close horizon check) must reach the trap.
  4. Which bound matters? A copy without the close-time horizon check
     instead must still pass.

Usage: sanity-run.py build/close_time_harness
"""
import random
import struct
import sys

M64 = (1 << 64) - 1
TWO32 = 1 << 32
HORIZON = TWO32 - 1 - 60
RESOLUTIONS = [10, 20, 30, 60, 90, 120]


class Trap(Exception):
    pass


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


class Machine:
    def __init__(self, elf):
        self.mem = {}
        self.x = [0] * 32
        e_entry, e_phoff = struct.unpack_from("<QQ", elf, 24)
        e_phentsize, e_phnum = struct.unpack_from("<HH", elf, 54)
        self.text = None
        for i in range(e_phnum):
            p_type, p_flags, p_off, p_vaddr, _, p_filesz, _, _ = struct.unpack_from(
                "<IIQQQQQQ", elf, e_phoff + i * e_phentsize)
            if p_type == 1:  # PT_LOAD
                for j in range(p_filesz):
                    self.mem[p_vaddr + j] = elf[p_off + j]
        self.pc = e_entry

    def launch(self, argv):
        """A Linux-style initial stack: argc, argv[], NULL, envp NULL, auxv end."""
        top = 0x7FFFFFF000
        ptrs = []
        for a in argv:
            top -= len(a) + 1
            for j, b in enumerate(a + b"\0"):
                self.mem[top + j] = b
            ptrs.append(top)
        words = [len(argv)] + ptrs + [0, 0, 0, 0]
        sp = (top - 8 * len(words)) & ~15
        for j, w in enumerate(words):
            self.store(sp + 8 * j, w, 8)
        self.x[2] = sp

    def load(self, a, n):
        try:
            return sum(self.mem[(a + j) & M64] << (8 * j) for j in range(n))
        except KeyError:
            raise Trap(f"load from unmapped {a:#x} at pc {self.pc:#x}")

    def store(self, a, v, n):
        for j in range(n):
            self.mem[(a + j) & M64] = (v >> (8 * j)) & 0xFF

    def step(self):
        """One instruction. Returns an exit status, or None to keep going."""
        w = self.load(self.pc, 4)
        op, rd, f3 = w & 0x7F, (w >> 7) & 31, (w >> 12) & 7
        rs1, rs2, f7 = (w >> 15) & 31, (w >> 20) & 31, w >> 25
        a, b = self.x[rs1], self.x[rs2]
        i_imm = sx(w >> 20, 12)
        nxt, res = self.pc + 4, None
        if op == 0x13:  # OP-IMM
            sh = (w >> 20) & 63
            res = {0: a + i_imm, 1: a << sh, 4: a ^ i_imm, 6: a | i_imm, 7: a & i_imm,
                   5: (sx(a, 64) >> sh) if w >> 30 & 1 else (a >> sh)}.get(f3)
        elif op == 0x1B:  # OP-IMM-32
            sh = rs2
            r = {0: a + i_imm, 1: a << sh,
                 5: (sx(a, 32) >> sh) if w >> 30 & 1 else ((a & 0xFFFFFFFF) >> sh)}.get(f3)
            res = None if r is None else sx(r, 32)
        elif op == 0x33:  # OP
            if f7 == 0:
                res = {0: a + b, 4: a ^ b, 6: a | b, 7: a & b}.get(f3)
            elif f7 == 0x20 and f3 == 0:
                res = a - b
        elif op == 0x3B:  # OP-32
            a32, b32 = a & 0xFFFFFFFF, b & 0xFFFFFFFF
            if f7 == 0 and f3 == 0:
                res = sx(a + b, 32)
            elif f7 == 0x20 and f3 == 0:
                res = sx(a - b, 32)
            elif f7 == 1 and f3 == 7:  # remuw; RISC-V defines x % 0 = x
                res = sx(a32 % b32 if b32 else a32, 32)
        elif op == 0x37:
            res = sx(w & 0xFFFFF000, 32)
        elif op == 0x17:
            res = self.pc + sx(w & 0xFFFFF000, 32)
        elif op == 0x03:  # LOAD
            addr = (a + i_imm) & M64
            res = {3: lambda: self.load(addr, 8), 4: lambda: self.load(addr, 1),
                   2: lambda: sx(self.load(addr, 4), 32)}.get(f3, lambda: None)()
        elif op == 0x23 and f3 == 3:  # sd
            self.store((a + sx((f7 << 5) | rd, 12)) & M64, b, 8)
            rd, res = 0, 0
        elif op == 0x63:  # BRANCH
            imm = sx(((w >> 31) << 12) | ((w >> 7 & 1) << 11) | ((w >> 25 & 63) << 5)
                     | ((w >> 8 & 15) << 1), 13)
            taken = {0: a == b, 1: a != b, 6: a < b, 7: a >= b}.get(f3)
            if taken is not None:
                nxt, rd, res = (self.pc + imm if taken else nxt), 0, 0
        elif op == 0x67 and f3 == 0:  # jalr
            res, nxt = self.pc + 4, (a + i_imm) & ~1 & M64
        elif w == 0x73:  # ecall
            if self.x[17] == 93:
                return self.x[10] & 0xFF
            raise Trap(f"unexpected system call {self.x[17]}")
        if res is None:
            raise Trap(f"illegal instruction {w:#010x} at pc {self.pc:#x}")
        if rd:
            self.x[rd] = res & M64
        self.pc = nxt
        return None

    def run(self, limit=100000):
        for _ in range(limit):
            status = self.step()
            if status is not None:
                return status
        raise Trap("did not halt")


def encode(close, prior, index):
    """17 characters whose low nibbles carry the input ('@' is nibble 0)."""
    nib = lambda v: bytes(0x40 | (v >> s & 15) for s in range(28, -4, -4))
    return nib(close) + nib(prior) + bytes([0x40 | index])


def spec_eff_close_time(c, r, p):
    """CloseTimeSpec.eff_close_time, transcribed."""
    if c == 0:
        return 0
    x = (c + r // 2) % TWO32
    return max((x - x % r) % TWO32, (p + 1) % TWO32)


def main():
    elf = open(sys.argv[1], "rb").read()
    rng = random.Random(2026)
    edge = [0, 1, 2, 9, 10, 15, 16, 2**31 - 1, 2**31, HORIZON - 1, HORIZON,
            HORIZON + 1, TWO32 - 2, TWO32 - 1]
    pick = lambda: rng.choice(edge) if rng.random() < 0.3 else rng.randrange(TWO32)

    # 1. whole program, real argv
    launches = [[b"t"], [b"t", b""], [b"t", b"short"], [b"t", b"a", b"b"],
                [b"t", encode(815_000_000, 814_999_990, 0)]]
    launches += [[b"t", encode(pick(), pick(), rng.randrange(8))] for _ in range(20000)]
    for argv in launches:
        m = Machine(elf)
        m.launch(argv)
        status = m.run()
        assert status == 0, (argv, status)
    print(f"1. whole program: {len(launches)} launches, all exited with status 0")

    # 2. the nine instructions against the spec
    n = 200000
    for _ in range(n):
        c, p = pick(), pick()
        r = rng.choice(RESOLUTIONS) if rng.random() < 0.7 else rng.randrange(1, TWO32)
        m = Machine(elf)
        m.pc, m.x[1] = 0x11018, 0xDEAD0
        m.x[10], m.x[11], m.x[12] = (sx(v, 32) & M64 for v in (c, r, p))
        while m.pc != 0xDEAD0:
            m.step()
        got, want = m.x[10], sx(spec_eff_close_time(c, r, p), 32) & M64
        assert got == want, (c, r, p, got, want)
    print(f"2. eff_close_time: {n} random inputs, all equal to the spec")

    # 3. remove the previous-close horizon check (bltu a1, s1 at 0x110d0):
    #    the trap must be reachable
    def without_branch(addr, word):
        off = 0x1000 + (addr - 0x11000)
        assert elf[off:off + 4] == struct.pack("<I", word), f"unexpected word at {addr:#x}"
        return elf[:off] + struct.pack("<I", 0x00000013) + elf[off + 4:]  # nop

    bad = [b"t", encode(100, TWO32 - 1, 2)]
    m = Machine(without_branch(0x110D0, 0x0695E863))
    m.launch(bad)
    try:
        status = m.run()
        raise SystemExit(f"3. FAILED: the mutant exited with status {status}")
    except Trap as t:
        assert "0x11138" in str(t), t
        print(f"3. mutant without the previous-close horizon check: {t}")
    m = Machine(elf)
    m.launch(bad)
    assert m.run() == 0
    print("   the same input on the real binary: exited with status 0")

    # 4. remove the close-time horizon check instead (bltu a1, s0 at 0x110cc).
    #    Nothing traps: a rounding that wraps gives 0, which loses to
    #    "previous close + 1". CloseTimeSpec.eff_on_boundary proves this.
    mutant = without_branch(0x110CC, 0x0685EA63)
    for _ in range(20000):
        c = rng.randrange(HORIZON + 1, TWO32) if rng.random() < 0.8 else pick()
        m = Machine(mutant)
        m.launch([b"t", encode(c, rng.randrange(HORIZON + 1), rng.randrange(6))])
        assert m.run() == 0
    print("4. mutant without the close-time horizon check: 20000 launches, "
          "all exited with status 0")


if __name__ == "__main__":
    main()
