#!/bin/sh
# Checks everything, from the upstream source to the theorem. About a minute.
#   1. rebuild the RISC-V binary and compare its SHA-256
#   2. re-derive the memory image from that binary and compare it with the
#      one the proofs are about
#   3. scan the proof sources for admitted proofs, axioms and switched-off
#      kernel checks, then rebuild every proof from scratch with Rocq
#   4. read Rocq's own report of what each theorem depends on, and fail on
#      anything that is not in allowed-axioms.txt
#   5. run the binary's bytes in an independent interpreter (a sanity check)
# Needs tools/setup-toolchain.sh to have run once.
set -eu

XRPL_FV_HOME="${XRPL_FV_HOME:-$HOME/.cache/xrpl-fv}"
export OPAMROOT="$XRPL_FV_HOME/opam"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BINARY_SHA256="b7335d41d947f9aba48913556f7b42dd2926a9b50041ec649b9ee05f5825b257"
LEDGER_TIMING_SHA256="e15efa79e8a82de4ebcaf388e0ddb4b9ec34875157cb83deb6fb6f253ed4fa46"

sha() { shasum -a 256 "$1" | cut -d' ' -f1; }

echo "== 1/5 the binary"
sh tools/build-binary.sh > build.log 2>&1 || { cat build.log; exit 1; }
rm -f build.log
[ "$(sha "$XRPL_FV_HOME/src/rippled/include/xrpl/ledger/LedgerTiming.h")" = "$LEDGER_TIMING_SHA256" ] \
  || { echo "FAIL: LedgerTiming.h is not the pinned file"; exit 1; }
[ "$(sha build/close_time_harness)" = "$BINARY_SHA256" ] \
  || { echo "FAIL: the binary differs: $(sha build/close_time_harness)"; exit 1; }
echo "   sha256 $BINARY_SHA256"

echo "== 2/5 the memory image is that binary"
TMP="$(mktemp -d)"
python3 "$XRPL_FV_HOME/lps/tools/elf_snapshot.py" build/close_time_harness \
  "$TMP/HarnessMemImage.v" --prefix HarnessMemImage --module-name Harness \
  --namespace XrplVerify > /dev/null 2>&1
for f in HarnessMemImage.v HarnessMemImage_seg_000.hex HarnessMemImage_seg_001.hex; do
  cmp -s "$TMP/$f" "proof/theories/$f" || { echo "FAIL: $f differs"; exit 1; }
done
rm -rf "$TMP"
echo "   identical"

echo "== 3/5 the proofs"
python3 tools/check-proofs.py sources proof/theories/*.v \
  || { echo "FAIL: the sources assume something without proof"; exit 1; }
rm -rf proof/_build
( cd proof && opam exec --switch lps -- dune build 2>&1 ) > build/proof.log \
  || { cat build/proof.log; echo "FAIL: the proofs do not check"; exit 1; }
[ -f proof/_build/default/theories/Checker.vo ] || { echo "FAIL: no Checker.vo"; exit 1; }
echo "   Rocq accepted every file"

echo "== 4/5 the axioms"
# 8 = the number of specification theorems and examples Checker.v reports on.
python3 tools/check-proofs.py report build/proof.log allowed-axioms.txt 8 \
  || { echo "FAIL: a theorem depends on something that is not allowed"; exit 1; }

echo "== 5/5 sanity run of the binary"
python3 tools/sanity-run.py build/close_time_harness | sed 's/^/   /'

echo "== all checks passed"
