#!/usr/bin/env bash
# Check every proof file, one at a time, under the limits of scripts/limits.sh.
# Prefer this to `lake build Examples` / `lake test`: lake checks all the files of a
# library in parallel, and each check runs Lean, Blaster and Z3.
#
# Usage: [TIMEOUT=secs] scripts/check-all.sh [FILE...]
#   TIMEOUT (default 900) bounds every SMT query. Without FILE arguments all suites run.
# Prints one summary line per file and writes the messages to .lake/check-logs/.
set -uo pipefail
cd "$(dirname "$0")/.."
source scripts/limits.sh
export TIMEOUT="${TIMEOUT:-900}"

files=("$@")
if [ ${#files[@]} -eq 0 ]; then
  files=(
    tests/Tests/Differential.lean
    tests/Tests/Symbolic/Machine.lean
    tests/Tests/Codegen/Packed.lean tests/Tests/Codegen/Signed.lean
    tests/Tests/Codegen/Messages.lean tests/Tests/Codegen/Dynamic.lean
    tests/Tests/Codegen/Caller.lean tests/Tests/Codegen/Loop.lean
    EvmBlaster/Examples/Config.lean EvmBlaster/Examples/Vault.lean
    EvmBlaster/Examples/VaultBuggy.lean EvmBlaster/Examples/Token.lean
    EvmBlaster/Examples/OZToken.lean EvmBlaster/Examples/WETH9.lean
    vendor/Lean-blaster/Tests/Smt/SmtNat/SmtNatBitwise.lean
  )
fi

echo "building dependencies..."
acquire_check_lock
limited lake build EvmBlaster Tests.Differential.Cases Tests.Support.Run Blaster:shared >/dev/null ||
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
exit $failed
