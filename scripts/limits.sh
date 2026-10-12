# Resource limits for proof checks (sourced by the other scripts).
#
# Blaster runs Z3 as a child process and a single check can use several GB of memory, so
# heavy commands go through `limited`, which runs them in a transient systemd unit with a
# memory cap, a CPU quota and low priority. When the command ends (or is interrupted) the
# whole unit is stopped, Z3 children included. Without a user systemd manager it falls
# back to `nice` plus an address-space limit.
#
# Tunables (environment): CHECK_MEM (default 8G), CHECK_CPU (default 400%, i.e. 4 cores),
# CHECK_RUNTIME (wall-clock limit of one command, default 3600 seconds).

CHECK_MEM="${CHECK_MEM:-8G}"
CHECK_CPU="${CHECK_CPU:-400%}"
CHECK_RUNTIME="${CHECK_RUNTIME:-3600}"

# Cleanup on exit or interruption: stop the running unit, remove the temporary file.
CHECK_UNIT=""
CHECK_TMP=""
_check_cleanup() {
  [ -n "$CHECK_UNIT" ] && systemctl --user stop "$CHECK_UNIT" 2>/dev/null
  [ -n "$CHECK_TMP" ] && rm -f "$CHECK_TMP"
  return 0
}
trap _check_cleanup EXIT
trap '_check_cleanup; exit 130' INT TERM

limited() {
  if command -v systemd-run >/dev/null 2>&1 && systemd-run --user --scope -q true 2>/dev/null; then
    CHECK_UNIT="blaster-evm-check-$$-$RANDOM"
    # pass on the variables Lean and elan need (only those that are set)
    local envs=()
    for v in PATH HOME LEAN_PATH ELAN_HOME ELAN_TOOLCHAIN; do
      [ -n "${!v:-}" ] && envs+=(-E "$v=${!v}")
    done
    systemd-run --user --wait --pipe --quiet --same-dir --unit="$CHECK_UNIT" \
      -p MemoryMax="$CHECK_MEM" -p MemorySwapMax=0 -p CPUQuota="$CHECK_CPU" \
      -p RuntimeMaxSec="$CHECK_RUNTIME" --nice=10 \
      "${envs[@]}" "$@"
  else
    ( ulimit -v $((8 * 1024 * 1024)); exec timeout "$CHECK_RUNTIME" nice -n 10 "$@" )
  fi
}

# Serialise checks: only one proof check at a time on this machine.
acquire_check_lock() {
  local lock="${XDG_RUNTIME_DIR:-/tmp}/blaster-evm-check.lock"
  exec 9>"$lock"
  if ! flock -n 9; then
    echo "another check is running; waiting for it to finish..." >&2
    flock 9
  fi
}
