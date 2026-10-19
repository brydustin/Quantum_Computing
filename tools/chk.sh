#!/bin/bash
# Check a scratch session in wip/ (default VP_WIP) with live progress; kill leftover poly on timeout.
# Usage: tools/chk.sh [SESSION] [TIMEOUT_SECONDS]
S=${1:-VP_WIP}; T=${2:-900}
P=$(cd "$(dirname "$0")/.." && pwd)
ISA=/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle
AFP=/home/dusty/Desktop/Isabelle/afp-2026-04-09/thys
timeout "$T" "$ISA" build -v -o build_progress_threshold=20 -d "$AFP" -d "$P" -d "$P/wip" "$S" 2>&1 \
  | grep -v "^Session\|^Building\|^Running\|^Finished\|^Timing\|^Loading" | tail -60
rc=${PIPESTATUS[0]}
if [ "$rc" = 124 ]; then
  for pid in $(pgrep -f "poly"); do
    grep -qa "$S" /proc/$pid/cmdline 2>/dev/null && kill "$pid" && echo "killed poly $pid"
  done
fi
echo "EXIT $rc"
