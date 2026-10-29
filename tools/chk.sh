#!/bin/bash
# Check a scratch session in wip/ (default VP_WIP); full log in wip/chk_SESSION.log
# (grep it for 'running for' while a check is slow); on timeout only this build's process tree is killed.
# Usage: [WIP=dir] tools/chk.sh [SESSION] [TIMEOUT_SECONDS]   (WIP: scratch dir, default wip/)
S=${1:-VP_WIP}; T=${2:-900}
P=$(cd "$(dirname "$0")/.." && pwd)
ISA=/home/dusty/Desktop/Isabelle/Isabelle2026/bin/isabelle
AFP=/home/dusty/Desktop/Isabelle/afp-2026-10-29/thys
W=${WIP:-$P/wip}
LOG="$W/chk_$S.log"
# On timeout kill exactly this build's process tree (never a prover started meanwhile by jEdit).
tree() { for c in $(pgrep -P "$1"); do echo "$c"; tree "$c"; done; }
"$ISA" build -v -o build_progress_threshold=20 -d "$AFP" -d "$P" -d "$W" "$S" > "$LOG" 2>&1 &
bp=$!
for ((i = 0; i < T; i++)); do kill -0 "$bp" 2>/dev/null || break; sleep 1; done
if kill -0 "$bp" 2>/dev/null; then
  pids=$(tree "$bp")
  kill "$bp" $pids 2>/dev/null
  echo "killed build $bp and $(echo $pids | wc -w) descendants"
  rc=124
  grep -a "running for" "$LOG" | tail -5
else
  wait "$bp"; rc=$?
fi
grep -av "^Session\|^Building\|^Running\|^Finished\|^Timing\|^Loading\|running for\|^ML_\|^ISABELLE\|^Started\|^$" "$LOG" | tail -60
echo "EXIT $rc"
