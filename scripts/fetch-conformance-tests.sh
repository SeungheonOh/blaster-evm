#!/usr/bin/env bash
# Fetch the Ethereum test fixtures run by the conformance runner (tests/README.md, "Conformance")
# into .lake/ethereum-tests: a sparse checkout of ethereum/legacytests at a pinned commit.
#
# Usage: scripts/fetch-conformance-tests.sh
set -euo pipefail
cd "$(dirname "$0")/.."

REPO=https://github.com/ethereum/legacytests
COMMIT=1f581b8ccdc4c63acf5f2c5c1b155c690c32a8eb
DEST=.lake/ethereum-tests

# Legacy VM tests (Constantinople), and the general state tests filled for Cancun in
# blockchain-test form, restricted to the directories with tests in the machine's scope.
STATE=Cancun/BlockchainTests/GeneralStateTests
PATHS=(
  /LICENSE
  /Constantinople/VMTests/
)
for d in Cancun Pyspecs Shanghai VMTests stArgsZeroOneBalance stBadOpcode stBugs stChainId \
         stEIP1559 stExample stExtCodeHash stMemoryStressTest stMemoryTest stRandom stRandom2 \
         stReturnDataTest stRevertTest stSelfBalance stShift stSolidityTest stSpecialTest \
         stSystemOperationsTest stTransactionTest; do
  PATHS+=("/$STATE/$d/")
done

if [ ! -d "$DEST/.git" ]; then
  mkdir -p "$DEST"
  git -C "$DEST" init -q
  git -C "$DEST" remote add origin "$REPO"
fi
git -C "$DEST" sparse-checkout set --no-cone "${PATHS[@]}"
if [ "$(git -C "$DEST" rev-parse -q --verify HEAD 2>/dev/null)" != "$COMMIT" ]; then
  git -C "$DEST" fetch -q --depth 1 --filter=blob:none origin "$COMMIT"
fi
git -C "$DEST" checkout -q --detach "$COMMIT"
echo "ethereum/legacytests $COMMIT in $DEST ($(du -sh "$DEST" --exclude=.git | cut -f1))"
