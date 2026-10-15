#!/usr/bin/env bash
# Check every proof file, one at a time, under the limits of scripts/limits.sh.
# Prefer this to `lake build Examples` / `lake test`: lake checks all the files of a
# library in parallel, and each check runs Lean, Blaster and Z3.
#
# Usage: [TIMEOUT=secs] scripts/check-all.sh [FILE...]
#   TIMEOUT (default 900) bounds every SMT query. Without FILE arguments all suites run.
# Prints one summary line per file and writes the messages to .lake/check-logs/. Without
# FILE arguments it also runs the conformance suite (scripts/conformance.sh) when its
# fixtures have been fetched.
set -uo pipefail
cd "$(dirname "$0")/.."
source scripts/limits.sh
export TIMEOUT="${TIMEOUT:-900}"

files=("$@")
all=0
if [ ${#files[@]} -eq 0 ]; then
  all=1
  files=(
    tests/Tests/Differential.lean
    tests/Tests/Symbolic/Machine.lean
    tests/Tests/Codegen/Packed.lean tests/Tests/Codegen/Signed.lean
    tests/Tests/Codegen/Messages.lean tests/Tests/Codegen/Dynamic.lean
    tests/Tests/Codegen/Caller.lean tests/Tests/Codegen/Loop.lean
    tests/Tests/UAL/Frontend.lean
    EvmBlaster/Examples/Config.lean EvmBlaster/Examples/Vault.lean
    EvmBlaster/Examples/VaultBuggy.lean EvmBlaster/Examples/Token.lean
    EvmBlaster/Examples/OZToken.lean EvmBlaster/Examples/WETH9.lean
    EvmBlaster/Examples/Timelock.lean EvmBlaster/Examples/Auction.lean
    EvmBlaster/Examples/MultiSig.lean EvmBlaster/Examples/OZPausableToken.lean
    vendor/Lean-blaster/Tests/Smt/SmtNat/SmtNatBitwise.lean
  )
fi

echo "building dependencies..."
acquire_check_lock
limited lake build EvmBlaster Tests.Differential.Cases Tests.Support.Run UAL blaster-evm Blaster:shared >/dev/null ||
  { echo "dependency build failed"; exit 1; }
flock -u 9

mkdir -p .lake/check-logs
failed=0
for f in "${files[@]}"; do
  log=".lake/check-logs/$(echo "$f" | tr '/' '_').log"
  start=$(date +%s)
  scripts/run-file.sh "$f" > "$log" 2>&1
  status=$?
  secs=$(( $(date +%s) - start ))
  ok=$(grep -cE "✅" "$log")
  bad=$(grep -cE $'\terror\t|⚠️ Undetermined|❌' "$log")
  if [ $status -ne 0 ] || [ "$bad" -ne 0 ]; then failed=1; mark="FAIL"; else mark="ok"; fi
  printf '%-4s %-58s %3d passed %3d failed %5ds\n' "$mark" "$f" "$ok" "$bad" "$secs"
done

# The UAL annotations of the Solidity examples, end to end (./blaster-evm). Every property
# is proved, but two in Crowdfund.sol, which has two deliberate bugs.
if [ $all -eq 1 ]; then
  log=.lake/check-logs/ual-examples.log
  start=$(date +%s)
  ./blaster-evm --no-cache examples/Bank.sol examples/Token.sol examples/Escrow.sol \
    examples/Vesting.sol > "$log" 2>&1
  status=$?
  ./blaster-evm --no-cache --json examples/Crowdfund.sol > "$log.json" 2>> "$log"
  cstatus=$?
  secs=$(( $(date +%s) - start ))
  ok=$(grep -c "✓" "$log")
  bad=$(grep -cE "✗|^ *[!?] " "$log")
  cproved=$(grep -c '^  "status": "proved"' "$log.json")
  cfalse=$(grep -c '^  "status": "falsified"' "$log.json")
  if [ $status -ne 0 ] || [ $cstatus -ne 1 ] || [ "$cproved" -ne 4 ] || [ "$cfalse" -ne 2 ]; then
    failed=1; mark="FAIL"
  else mark="ok"; fi
  printf '%-4s %-58s %3d passed %3d failed %5ds\n' "$mark" "UAL examples (./blaster-evm examples/)" \
    $((ok + cproved + cfalse)) "$bad" "$secs"
fi

# Conformance with the Ethereum test suites, when their fixtures have been fetched.
if [ $all -eq 1 ]; then
  if [ -d .lake/ethereum-tests/Constantinople ]; then
    log=.lake/check-logs/conformance.log
    start=$(date +%s)
    scripts/conformance.sh > "$log" 2>&1
    status=$?
    secs=$(( $(date +%s) - start ))
    # columns of the total line: pass, pass/OOG, inconclusive, out of scope, FAIL
    read -r ok bad < <(awk '/^total/ {print $2 + $3, $6}' "$log")
    if [ $status -ne 0 ]; then failed=1; mark="FAIL"; else mark="ok"; fi
    printf '%-4s %-58s %3d passed %3d failed %5ds\n' "$mark" "conformance (Ethereum tests)" \
      "${ok:-0}" "${bad:-0}" "$secs"
  else
    echo "skip conformance (fetch the fixtures with scripts/fetch-conformance-tests.sh)"
  fi
fi
exit $failed
