#!/usr/bin/env bash
# Compile contracts/*.sol and tests/contracts/*.sol to runtime bytecode in */build/.
# Usage: SOLC=/path/to/solc-0.8.28 scripts/compile.sh
set -euo pipefail
cd "$(dirname "$0")/.."
SOLC="${SOLC:-solc}"
"$SOLC" --version | grep -q "0.8.28" || { echo "expected solc 0.8.28 (set SOLC)" >&2; exit 1; }
compile() {  # compile() SRC_DIR: SRC_DIR/*.sol -> SRC_DIR/build/
  mkdir -p "$1/build"
  for f in "$1"/*.sol; do
    "$SOLC" --evm-version shanghai --optimize --optimize-runs 200 \
      --base-path . \
      @openzeppelin/contracts/=contracts/lib/openzeppelin-contracts/contracts/ \
      --bin-runtime --abi --storage-layout --hashes \
      -o "$1/build" --overwrite "$f"
  done
  # keep only the artifacts of the contracts named after their file
  for a in "$1"/build/*; do
    name="$(basename "$a")"; name="${name%%.*}"; name="${name%_storage}"
    [ -f "$1/$name.sol" ] || rm -f "$a"
  done
}
compile contracts
compile tests/contracts
ls contracts/build tests/contracts/build
