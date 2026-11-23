#!/bin/sh
# Builds the RISC-V test binary from the pinned upstream XRP Ledger source.
# Output: build/close_time_harness (a static riscv64 Linux program, no libc).
set -eu

XRPL_FV_HOME="${XRPL_FV_HOME:-$HOME/.cache/xrpl-fv}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# xrpld (github.com/XRPLF/rippled), develop branch, 20 Nov 2026.
RIPPLED_REPO="https://github.com/XRPLF/rippled.git"
RIPPLED_COMMIT="82217fbd0ac4234c3a97fedcf94f35e5796aa9f2"
# Howard Hinnant's date library, the version xrpld's conanfile.py pins.
# xrpl/basics/chrono.h includes it.
DATE_URL="https://raw.githubusercontent.com/HowardHinnant/date/v3.0.4/include/date/date.h"

SRC="$XRPL_FV_HOME/src"
mkdir -p "$SRC/date/include/date" "$ROOT/build"

if [ ! -d "$SRC/rippled/.git" ]; then
  git init -q "$SRC/rippled"
  git -C "$SRC/rippled" remote add origin "$RIPPLED_REPO"
fi
if [ "$(git -C "$SRC/rippled" rev-parse HEAD 2>/dev/null || true)" != "$RIPPLED_COMMIT" ]; then
  git -C "$SRC/rippled" fetch -q --depth 1 origin "$RIPPLED_COMMIT"
  git -C "$SRC/rippled" checkout -q FETCH_HEAD
fi
[ -f "$SRC/date/include/date/date.h" ] || curl -fsSL "$DATE_URL" -o "$SRC/date/include/date/date.h"

# rv64imafd: no compressed instructions, so every instruction is 4 bytes.
# Compile with the C++ standard library headers, then link with no library at
# all: the test uses nothing from libc or libc++ at run time.
# No debug information (-g0, --strip-debug): it would record the directory
# the build ran in, and the binary would differ from one checkout to the next.
TARGET="-target riscv64-linux-musl -mcpu=generic_rv64+m+a+f+d"
zig c++ $TARGET -c -g0 \
  -std=c++20 -Os -DNDEBUG -fno-exceptions -fno-rtti -fno-builtin \
  -fno-stack-protector -fno-asynchronous-unwind-tables -mno-relax \
  -ffunction-sections -fdata-sections \
  -I "$SRC/rippled/include" -I "$SRC/date/include" \
  "$ROOT/harness/close_time_harness.cpp" -o "$ROOT/build/close_time_harness.o"
zig cc $TARGET -c -g0 -mno-relax "$ROOT/harness/start.S" -o "$ROOT/build/start.o"
zig ld.lld -static --build-id=none --strip-debug --gc-sections -z separate-code \
  -e _start "$ROOT/build/start.o" "$ROOT/build/close_time_harness.o" \
  -o "$ROOT/build/close_time_harness"

shasum -a 256 "$ROOT/build/close_time_harness"
shasum -a 256 "$SRC/rippled/include/xrpl/ledger/LedgerTiming.h" "$SRC/rippled/include/xrpl/basics/chrono.h"
