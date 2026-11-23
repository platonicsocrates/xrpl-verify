# Binary-level verification of the XRP Ledger close-time computation

Machine-checked proofs, in Rocq, about the compiled RISC-V code of one
function of the XRP Ledger server (`xrpld`). The method is the one described
by Anthropic and Theorem in
[LLMs are making formal software verification feasible at a much larger scale](https://www.anthropic.com/research/formal-verification)
(22 October 2026): take a test, compile it, and prove that the binary cannot
fail on any input.

The function is `effCloseTime`, with `roundCloseTime`, from
[`include/xrpl/ledger/LedgerTiming.h`](https://github.com/XRPLF/rippled/blob/82217fbd0ac4234c3a97fedcf94f35e5796aa9f2/include/xrpl/ledger/LedgerTiming.h).
Consensus calls it to turn the close time agreed by validators into the
close time recorded in the ledger header (`RCLConsensus.cpp`).

The paper, [paper/xrpl-close-time.pdf](paper/xrpl-close-time.pdf) (11 pages),
gives the full account. This README summarises it.

## Results

All three are checked by Rocq 9.2.0 against Theorem's model of a Linux
process running a RISC-V binary
([rocq-linux-process-semantics](https://github.com/theorem-labs/rocq-linux-process-semantics),
"LPS", commit `d3f3a701`), the model used for the proofs in the article.

1. `eff_close_time_code` in [CloseTimeCode.v](proof/theories/CloseTimeCode.v).
   The function compiles to nine RISC-V instructions. Started with any
   32-bit close time, any non-zero 32-bit resolution and any 32-bit previous
   close time, they return `eff_close_time` as defined over the integers in
   [CloseTimeSpec.v](proof/theories/CloseTimeSpec.v), and leave memory and
   every register other than a0-a3 unchanged. This covers about 7.9 × 10^28
   input combinations.

2. Three theorems about that definition, with no machine code involved, in
   [CloseTimeSpec.v](proof/theories/CloseTimeSpec.v):
   - `eff_after_prior`: a ledger closes strictly after its predecessor.
   - `eff_on_boundary`: the close time is one second after the previous
     close, or it lies on a resolution boundary (10, 20, 30, 60, 90 or 120 s)
     within half a resolution of the agreed time.
   - `round_nearest`: rounding gives the nearest multiple of the resolution,
     with ties rounded up.

3. `harness_halts` in [HarnessHalts.v](proof/theories/HarnessHalts.v), sealed
   in [Checker.v](proof/theories/Checker.v). The test program
   ([close_time_harness.cpp](harness/close_time_harness.cpp)) decodes its
   argument into a close time, a previous close time and a resolution, calls
   the function, and traps if a property fails. The theorem is an instance
   of the model's own statement `halts_allowed_T`: for every valid launch of
   this binary (every argument list, environment and stack placement), every
   execution ends in `exit(0)`.
   [TrapIsFatal.v](proof/theories/TrapIsFatal.v) proves that the trap
   instruction is a fault in the model, so an execution that exits with
   status 0 never reached it. That each failing check in the C++ compiles to
   a branch to that instruction is read from the disassembly.

The existing unit tests for the two functions are 13 assertions on example
values (`src/tests/libxrpl/consensus/LedgerTiming.cpp`). On the five
argument triples of the `effCloseTime` tests the specification returns the
expected values; the tests themselves use 64-bit durations, so they exercise
different machine code.

## Comparison with the article

| | The article | This repository |
|---|---|---|
| Method | fuzz test → statement about the RISC-V binary → Rocq proof | the same |
| Model | Theorem's LPS | the same, at a newer commit |
| Checker | Rocq kernel, sealed against the model's statement | the same, with our own copy of Theorem's check |
| Scale | 239 entry points in 123 libraries | one function |
| Binary | median 18,000 instructions, with libc | 87 instructions, no libc |
| Proof size | about 600,000 lines each | 1,844 lines, plus 248 generated |
| Sanitizer builds (AddressSanitizer) | yes | no |
| Origin of the test | the library's maintainers | written for this work |
| Functional correctness (result 1) | in selected case studies | yes, for this function |

## Trusted computing base

- The Rocq kernel, including its bytecode virtual machine.
- LPS at commit `d3f3a701`: its RISC-V instruction semantics, its account of
  process start-up (the stack, `argv`) and its model of `exit`. Theorem
  describes the model as best-effort and incomplete (in the OSS Verify
  README). The binary makes no
  system call other than `exit` and uses no heap, files or threads, so most
  of the model's documented gaps do not arise.
- The correspondence between the memory image and the binary: LPS's
  `elf-snapshot` and the `rocq-read-file` plugin. `tools/check.sh` rebuilds
  the binary and re-derives the image for comparison.
- The statements. `halts_allowed_T` is Theorem's. The statement of result 1
  and the definitions in the first 42 lines of `CloseTimeSpec.v` are ours,
  and are the place to start a review.

The compiler, the proof scripts, the generated instruction lemmas and the
sanity interpreter are outside the trusted base. The theorems depend on no
axioms other than Rocq's primitive integers, strings and arrays
([allowed-axioms.txt](allowed-axioms.txt)), and no proof is admitted.

## Limitations

- The result covers nine instructions compiled from one function, for
  RISC-V, with clang 22.1.8 at `-Os`. Release builds of `xrpld` target
  x86-64 and arm64 with other compilers and options, and the same source may
  compile differently there.
- It has no bearing on consensus as a whole, on transaction processing, on
  the payment engine, or on `getNextLedgerTimeResolution`, the other
  function in the same header.
- The test and its properties were written for this work and are not the
  maintainers'.
- Result 3 covers inputs up to the horizon set by the test: 7 February 2136,
  06:27:15 UTC. Result 1 has no such restriction.
- LPS restricts the launches it admits (for example to at most 1024
  arguments, with no `/` in an argument after the program name). Its
  [SCOPE.md](https://github.com/theorem-labs/rocq-linux-process-semantics/blob/main/SCOPE.md)
  lists every restriction.
- The development has not been independently reviewed.

## Observations

- The first version of the test's last check computed
  `eff + resolution / 2` in 32 bits. Close to the horizon that sum wraps,
  and the test would have trapped on correct code. The proof could not be
  completed, and the obstruction was such an input. The check now uses
  64-bit arithmetic. The defect was found before the binary had been run.
- Close times are 32-bit seconds since 2000 and are exhausted on 7 February
  2136. This is a known property of the design. The theorems make its
  consequences precise: if the previous ledger closed in the final second,
  the next close time is not later, and within the final 60 seconds rounding
  can wrap to the year 2000. `CloseTimeSpec.v` contains both as examples.
- Only one of the test's two range checks is needed. A rounding that wraps
  yields zero, which is always smaller than the previous close time plus
  one, so the checks hold for every close time. `eff_on_boundary` proves
  this.

## Reproduction

The scripts assume macOS with Homebrew and need about 3 GB of disk. The
first run takes about 15 minutes on a recent laptop, most of it spent
building LPS (about 40 CPU-minutes). Both steps below were repeated from an
empty toolchain directory in a clean copy of this repository.

```bash
sh tools/setup-toolchain.sh
```

```bash
sh tools/check.sh
```

`check.sh` takes about a minute. It rebuilds the binary from the pinned
upstream commit and compares its SHA-256, re-derives the memory image, scans
the proof sources for admitted proofs, axioms and disabled kernel checks,
rebuilds every proof from scratch, reads Rocq's report of what each theorem
depends on and fails on anything outside the allow-list, and executes the
binary in a small independent interpreter, which reports:

- 20,005 launches of the binary, all exiting with status 0;
- 200,000 random inputs to the nine instructions, all agreeing with the
  specification;
- a copy of the binary without the range check on the previous close time
  reaches the trap, which confirms that the checks can fail;
- a copy without the range check on the close time still passes.

As a cross-check that does not rely on that interpreter, `tools/linux-run.sh`
runs the binary as a riscv64 Linux process under QEMU user-mode emulation
(it needs Docker). 20,000 launches all exit with status 0, and the copy
without the range check is killed by SIGILL on the trap input. QEMU user
mode is not a system that LPS models (it builds a different initial stack),
so these runs are outside the launches result 3 quantifies over; they show
how the binary behaves on a second implementation of RISC-V.

```bash
sh tools/linux-run.sh
```

The build is reproducible: it carries no debug information, and builds in
three directories from two separately fetched copies of the sources give
identical binaries.

Two further controls were carried out separately on 21 November 2026. A copy
of the memory image with one instruction changed (`addiw a2, a2, 1` to
`addiw a2, a2, 2`) is rejected: `CloseTimeCode.v` no longer checks. A
specification altered in the same way is rejected too.

The paper builds with [tectonic](https://tectonic-typesetting.github.io/)
(`brew install tectonic`):

```bash
tectonic paper/xrpl-close-time.tex
```

## Layout

| Path | Content |
|---|---|
| `paper/` | the paper: LaTeX source and PDF |
| `harness/` | the test and its six-instruction entry point |
| `proof/theories/CloseTimeSpec.v` | the specification, and result 2 |
| `proof/theories/CloseTimeCode.v` | result 1 |
| `proof/theories/HarnessHalts.v` | result 3 |
| `proof/theories/TrapIsFatal.v` | the trap is a fault in the model |
| `proof/theories/Checker.v` | seals result 3 to the model's statement; lists axioms |
| `proof/theories/Word32.v`, `SegsApp.v` | supporting lemmas |
| `proof/theories/HarnessMemImage*`, `HarnessCode.v` | the binary's bytes, and generated per-instruction lemmas |
| `tools/` | toolchain setup, binary build, lemma generator, check scripts, interpreter, Linux run |

Pinned inputs: `xrpld` commit `82217fbd` (20 November 2026), LPS commit
`d3f3a701`, Rocq 9.2.0 and its libraries at fixed versions. The binary was
built with zig 0.17.1 (Homebrew cannot pin it; a different compiler shows up
in the SHA-256 comparison). Binary SHA-256
`b7335d41d947f9aba48913556f7b42dd2926a9b50041ec649b9ee05f5825b257`.

## Future work

- Further protocol arithmetic of the same kind:
  `getNextLedgerTimeResolution`, quorum and threshold calculations, fee and
  reserve arithmetic, and encoders and decoders (decoding inverts encoding).
- Theorem's [OSS Verify](https://github.com/theorem-labs/oss-verify) accepts
  projects enrolled by a core maintainer. `xrpld` had no project in OSS-Fuzz
  on 21 November 2026, so this would begin with fuzz targets written by the
  maintainers. Four direct dependencies of `xrpld` have at least one
  published proof there (OpenSSL, zlib, fast_float, and Boost's Beast and
  JSON), for particular entry points and other versions.
- Ripple and Common Prefix are verifying models of XRP Ledger protocol logic
  in Lean 4. That work proves properties of a model; this work proves
  properties of compiled code. The two meet where a Lean model and the
  binary are shown to agree on a common specification.

## Licence

MIT; see [LICENSE](LICENSE). The proofs depend on Theorem's Linux process
semantics (MIT), and `Checker.v` follows the checker distributed with it. The
paper quotes a short excerpt of `LedgerTiming.h` from `xrpld` (ISC licence).
