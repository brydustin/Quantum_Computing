#!/bin/bash
# The three submission folders: export, fresh build from the export alone, then per entry the
# archive, the unpacked entry, its metadata (tools/afp_meta) and the generated PDFs.
# Usage: tools/afp_package.sh [-f] [DIR]   (default ../AFP_Submissions; -f: fresh build)
. "$(dirname "$0")/env.sh"
F=; [ "$1" = -f ] && { F=-f; shift; }
DST=$(realpath -m "${1:-$P/../AFP_Submissions}")
EXP="$P/afp_export"
"$P/tools/afp_export.sh" -b $F "$EXP" > "$EXP.log" 2>&1; rc=$?
grep -v "^  " "$EXP.log" | tail -25
[ $rc = 0 ] || { echo "build from the export failed (see $EXP.log)"; exit 1; }
BI=$("$ISABELLE" getenv -b ISABELLE_BROWSER_INFO)
rm -rf "${DST:?}"; mkdir -p "$DST"
n=1
for e in Hermitian_Functional_Calculus Vern_Paulsen_QC HHL_Algorithm; do
  d="$DST/${n}_$e"; mkdir -p "$d"
  cp -r "$EXP/$e" "$EXP/$e.tar.gz" "$d/"
  cp "$P/tools/afp_meta/$e.md" "$d/SUBMISSION.md"
  for s in $(grep -h "^session " "$EXP/$e/ROOT" | awk '{print $2}'); do
    f="$BI/AFP/$s/document.pdf"; [ -f "$f" ] && cp "$f" "$d/$s.pdf"
  done
  n=$((n+1))
done
cp "$P/tools/afp_meta/README.md" "$DST/README.md"
ls -R "$DST" | grep -v "\.thy$" | head -60
