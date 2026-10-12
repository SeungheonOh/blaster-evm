#!/usr/bin/env bash
# Check one Lean file with Blaster's native plugin and print one line per message:
#   line:col  severity  first line of the message
# Usage: [TIMEOUT=secs] scripts/run-file.sh FILE [extra lean args]
# With TIMEOUT, every `blaster` / `#blaster` call of a temporary copy gets that SMT timeout
# (an undetermined goal then shows up as an error instead of running indefinitely).
# Runs under the limits of scripts/limits.sh, one check at a time.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/limits.sh
f="$1"; shift
export LEAN_PATH="$(lake env printenv LEAN_PATH)"
if [ -n "${TIMEOUT:-}" ]; then
  tmp="$(mktemp --suffix=.lean)"
  CHECK_TMP="$tmp"
  sed -E "s/(by|<;>) blaster$/\1 blaster (timeout: $TIMEOUT)/; s/^  blaster$/  blaster (timeout: $TIMEOUT)/; s/^#blaster /#blaster (timeout: $TIMEOUT) /" "$f" > "$tmp"
  f="$tmp"
fi
acquire_check_lock
limited lean --json --load-dynlib=vendor/Lean-blaster/.lake/build/lib/libBlaster.so "$@" "$f" |
  python3 -I scripts/lean_messages.py
