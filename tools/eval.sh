#!/bin/bash
# Check a theory file up to LINE against a heap with per-command timings (isabelle eval_at,
# from the isa_agentic_cli_tools component); prints errors and the slowest commands.
# Usage: tools/eval.sh FILE [LINE|-] [LOGIC]   (TO=timeout seconds, default 60; XD=extra -d dir)
. "$(dirname "$0")/env.sh"
F=$(realpath "$1"); L=${2:--}; [ "$L" = - ] && L=$(wc -l < "$F"); LG=${3:-Vern_Paulsen_QC_Algorithms}
O=$(mktemp)
cd "$(dirname "$F")"
before=$(pgrep -x poly | sort)
timeout "${TO:-60}" "$ISABELLE" eval_at -t -d "$AFP" -d "$P" ${XD:+-d "$XD"} -l "$LG" "$(basename "$F")" "$L" > "$O" 2>&1; rc=$?
echo "rc $rc"
if [ $rc = 124 ]; then
  for p in $(comm -13 <(echo "$before") <(pgrep -x poly | sort)); do kill "$p" && echo "killed poly $p"; done
fi
grep -n -A12 "^Error\|\*\*\* " "$O" | head -"${NERR:-30}"
echo "-- slowest:"; grep "^Timing" "$O" | awk '{for(i=1;i<=NF;i++) if($i=="elapsed") print $(i-1), $3, $4}' | sort -rn | head -5
grep -v "^Timing" "$O" > "${OUT:-/dev/null}"; rm -f "$O"
