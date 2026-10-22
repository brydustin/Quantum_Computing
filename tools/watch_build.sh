#!/bin/bash
# Build SESSION verbosely and kill it if one command runs longer than LIMIT seconds
# (prints the command and line); prints the errors of a failed build.
# Usage: tools/watch_build.sh SESSION [LIMIT]
. "$(dirname "$0")/env.sh"
SES=${1:?session}; LIM=${2:-90}; LOG=$(mktemp)
cd "$P"
before=$(pgrep -x poly | sort)
"$ISABELLE" build -b -v -d "$AFP" -d . -d tools/check "$SES" > "$LOG" 2>&1 &
BP=$!
while kill -0 $BP 2>/dev/null; do
  sleep 5
  L=$(grep -o 'running for [0-9.]*s (line [0-9]* of theory "[^"]*")' "$LOG" | tail -1)
  T=$(echo "$L" | sed 's/running for \([0-9]*\).*/\1/')
  if [ -n "$T" ] && [ "$T" -gt "$LIM" ]; then
    echo "HANG: $L"; kill $BP; sleep 2
    # only the poly processes this build started (a running jEdit has its own)
    for p in $(comm -13 <(echo "$before") <(pgrep -x poly | sort)); do kill "$p"; done
    exit 3
  fi
done
wait $BP; rc=$?; echo "exit $rc"
[ $rc = 0 ] || "$ISABELLE" build_log -H Error "$SES" | grep -v "^\s*$" | head -80
rm -f "$LOG"; exit $rc
