#!/bin/bash
# Full verification: strict build, oracle and redundancy checks, paper listings and counts.
# Exit status is nonzero if any step fails.
. "$(dirname "$0")/env.sh"
cd "$P"
rc=0
echo "== build"; tools/build_all.sh || exit 1
echo "== checks"
CHECKS="VP_Check_HFC VP_Check_Algorithms VP_Check_Notes VP_Check_Sylvester VP_Check_Search VP_Check_Demo VP_Check_Channels"
"$ISABELLE" build -d "$AFP" -d . -d tools/check $CHECKS > tools/check/output.log 2>&1 || rc=1
for s in HFC Algorithms HFC_Notes Notes Sylvester Search Demo Channels; do
  f=tools/check/output/$s.txt
  [ -f "$f" ] && { echo "-- $s"; grep -v "^note:" "$f"; }
done
[ $rc = 0 ] || grep -a "\*\*\*" tools/check/output.log | head -20
echo "== paper listings"; python3 tools/paper_listings.py | grep -v "^ok" || true
echo "== counts"; python3 tools/counts.py
exit $rc
