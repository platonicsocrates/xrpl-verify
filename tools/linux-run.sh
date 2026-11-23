#!/bin/sh
# Optional cross-check, not part of the proof and not run by check.sh.
# Runs the test binary as a real riscv64 Linux process, under QEMU user-mode
# emulation in Docker, and reports its exit statuses:
#   - N launches with the same kind of inputs as tools/sanity-run.py
#   - launches with no argument, two arguments and a short argument
#   - a copy of the binary without the range check on the previous close
#     time, on an input that must reach the trap (SIGILL, status 132)
# Needs Docker with riscv64 emulation (Docker Desktop has it) and a built
# binary (tools/build-binary.sh or tools/check.sh).
#   sh tools/linux-run.sh          (N=20000 launches by default)
set -eu

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
N="${N:-20000}"
WORK="$ROOT/build/linux-run"
mkdir -p "$WORK"
cp "$ROOT/build/close_time_harness" "$WORK/harness"

python3 - "$WORK" "$N" <<'EOF'
import os, pathlib, random, struct, sys

work, n = pathlib.Path(sys.argv[1]), int(sys.argv[2])
TWO32 = 1 << 32
HORIZON = TWO32 - 1 - 60

def encode(close, prior, index):
    nib = lambda v: "".join(chr(0x40 | (v >> s & 15)) for s in range(28, -4, -4))
    return nib(close) + nib(prior) + chr(0x40 | index)

rng = random.Random(2026)
edge = [0, 1, 2, 9, 10, 15, 16, 2**31 - 1, 2**31, HORIZON - 1, HORIZON,
        HORIZON + 1, TWO32 - 2, TWO32 - 1]
pick = lambda: rng.choice(edge) if rng.random() < 0.3 else rng.randrange(TWO32)
(work / "args.txt").write_text(
    "".join(encode(pick(), pick(), rng.randrange(8)) + "\n" for _ in range(n)))

# The same mutant as sanity-run.py: bltu a1, s1 at 0x110d0 replaced by a nop.
elf = (work / "harness").read_bytes()
off = 0x1000 + (0x110D0 - 0x11000)
assert elf[off:off + 4] == struct.pack("<I", 0x0695E863), "unexpected word at 0x110d0"
(work / "mutant").write_bytes(elf[:off] + struct.pack("<I", 0x13) + elf[off + 4:])
os.chmod(work / "mutant", 0o755)
(work / "bad.txt").write_text(encode(100, TWO32 - 1, 2))
EOF

docker run --rm --platform linux/riscv64 -v "$WORK:/w:ro" busybox:1.37 sh -c '
  [ "$(uname -m)" = riscv64 ] || { echo "FAIL: not a riscv64 userland"; exit 2; }
  n=0; bad=0
  while read -r a; do
    /w/harness "$a"; s=$?; n=$((n + 1))
    [ "$s" -eq 0 ] || { bad=$((bad + 1)); echo "status $s on $a"; }
  done < /w/args.txt
  echo "launches: $n, exit status other than 0: $bad"
  /w/harness;        echo "no argument: status $?"
  /w/harness a b;    echo "two arguments: status $?"
  /w/harness short;  echo "short argument: status $?"
  /w/harness "$(cat /w/bad.txt)"; echo "trap input on the real binary: status $?"
  /w/mutant "$(cat /w/bad.txt)" 2>/dev/null; echo "trap input on the mutant: status $? (132 = SIGILL)"
  [ "$bad" -eq 0 ]
'
