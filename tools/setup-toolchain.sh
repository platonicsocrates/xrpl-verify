#!/bin/sh
# Installs everything the proofs need, outside the repository:
#   - opam + Rocq 9.2.0 (the proof checker)
#   - Theorem's Linux Process Semantics (LPS), pinned to one commit
#   - zig (a clang cross-compiler with musl, for the RISC-V binary)
#
# Everything lands in $XRPL_FV_HOME (default ~/.cache/xrpl-fv). About 3 GB.
# The LPS build is the slow part: about 45 CPU-minutes.
set -eu

XRPL_FV_HOME="${XRPL_FV_HOME:-$HOME/.cache/xrpl-fv}"
LPS_REPO="https://github.com/theorem-labs/rocq-linux-process-semantics.git"
LPS_COMMIT="d3f3a701d99afeee638963228562f4b5ff6e96ba"
JOBS="${JOBS:-10}"   # each Rocq job can use 3 GB of memory

export OPAMROOT="$XRPL_FV_HOME/opam"
export OPAMYES=1
export OPAMJOBS="$JOBS"
export HOMEBREW_NO_AUTO_UPDATE=1

mkdir -p "$XRPL_FV_HOME"

echo "== 1/5 opam and zig"
command -v opam >/dev/null 2>&1 || brew install opam
command -v zig >/dev/null 2>&1 || brew install zig

echo "== 2/5 opam switch"
if [ ! -d "$OPAMROOT" ]; then
  opam init --bare --no-setup --disable-sandboxing
fi
if ! opam switch list --short | grep -qx lps; then
  opam switch create lps --packages=ocaml-base-compiler.4.14.2
fi
opam repo add rocq-released https://rocq-prover.org/opam/released --switch lps 2>/dev/null || true

echo "== 3/5 Rocq and libraries"
opam install --switch lps \
  dune.3.23.1 rocq-core.9.2.0 rocq-stdlib.9.2.0 rocq-stdpp.1.13.0 \
  rocq-stdpp-bitvector.1.13.0 coq-flocq.4.2.2 rocq-read-file.0.0.3

echo "== 4/5 LPS source at $LPS_COMMIT"
if [ ! -d "$XRPL_FV_HOME/lps/.git" ]; then
  git clone -q "$LPS_REPO" "$XRPL_FV_HOME/lps"
fi
git -C "$XRPL_FV_HOME/lps" fetch -q origin "$LPS_COMMIT" 2>/dev/null || true
git -C "$XRPL_FV_HOME/lps" checkout -q "$LPS_COMMIT"

echo "== 5/5 build and install the model (slow)"
opam pin add --switch lps --kind=path --no-action rocq-linux-process-semantics-core "$XRPL_FV_HOME/lps"
opam install --switch lps rocq-linux-process-semantics-core

echo "== done"
opam exec --switch lps -- rocq --version
# Homebrew cannot pin zig. The binary was built with zig 0.17.1 (clang 22.1.8);
# check.sh compares the binary's SHA-256, so another version shows up there.
ZIG_VERSION="$(zig version)"
echo "zig $ZIG_VERSION"
[ "$ZIG_VERSION" = "0.17.1" ] || echo "note: the proofs are about a binary built with zig 0.17.1"
