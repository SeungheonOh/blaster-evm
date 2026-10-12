#!/usr/bin/env bash
# Run the machine against the Ethereum test suites (docs/testing.md).
# Fetch the fixtures first with scripts/fetch-conformance-tests.sh.
#
# Usage: scripts/conformance.sh [--verbose] [PATH...]
#   Without PATH, runs every fetched fixture. Exits with status 1 if a test fails.
set -uo pipefail
cd "$(dirname "$0")/.."
source scripts/limits.sh

FIXTURES=.lake/ethereum-tests
args=()
paths=()
for a in "$@"; do
  if [ "$a" = --verbose ]; then args+=("$a"); else paths+=("$a"); fi
done
if [ ${#paths[@]} -eq 0 ]; then
  if [ ! -d "$FIXTURES/Constantinople" ]; then
    echo "no fixtures in $FIXTURES: run scripts/fetch-conformance-tests.sh" >&2
    exit 2
  fi
  paths=("$FIXTURES/Constantinople/VMTests" "$FIXTURES/Cancun/BlockchainTests/GeneralStateTests")
fi

acquire_check_lock
limited lake build conformance 2>&1 | grep -E "error|warning: .*Conformance" || true
limited .lake/build/bin/conformance "${args[@]}" "${paths[@]}"
