#!/bin/bash
# Check a scratch session in wip/ (default VP_WIP); full log in wip/chk_SESSION.log
# (grep it for 'running for' while a check is slow); kill leftover poly on timeout.
# Usage: [WIP=dir] tools/chk.sh [SESSION] [TIMEOUT_SECONDS]   (WIP: scratch dir, default wip/)
S=${1:-VP_WIP}; T=${2:-900}
P=$(cd "$(dirname "$0")/.." && pwd)
ISA=/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle
AFP=/home/dusty/Desktop/Isabelle/afp-2026-04-09/thys
W=${WIP:-$P/wip}
LOG="$W/chk_$S.log"
before=$(pgrep -x poly | sort)
timeout "$T" "$ISA" build -v -o build_progress_threshold=20 -d "$AFP" -d "$P" -d "$W" "$S" > "$LOG" 2>&1
rc=$?
if [ "$rc" = 124 ]; then
  # poly's cmdline does not name the session; kill the poly processes started by this check
  for pid in $(comm -13 <(echo "$before") <(pgrep -x poly | sort)); do kill "$pid" && echo "killed poly $pid"; done
  grep -a "running for" "$LOG" | tail -5
fi
grep -av "^Session\|^Building\|^Running\|^Finished\|^Timing\|^Loading\|running for\|^ML_\|^ISABELLE\|^Started\|^$" "$LOG" | tail -60
echo "EXIT $rc"
