#!/bin/bash
# Assemble the three AFP entries from the tracked sources, with ROOT files in AFP form
# (repo-only options dropped), and with -b build them from the export alone: a fresh build of
# entry session with the AFP's document options (-f: fresh, also unchanged sessions; note that it
# rebuilds the ancestors too).  Each entry is also packed as .tar.gz.
# Usage: tools/afp_export.sh [-b [-f]] [DIR]   (default DIR: afp_export, ignored by git)
. "$(dirname "$0")/env.sh"
B=0; F=; [ "$1" = -b ] && { B=1; shift; }; [ "$1" = -f ] && { F=-f; shift; }
OUT=$(realpath -m "${1:-$P/afp_export}")
cd "$P"
rm -rf "${OUT:?}"; mkdir -p "$OUT"
put() {  # put ENTRY PATH...: tracked sources (no PDFs, no build output) under ENTRY
  git ls-files -- "${@:2}" | grep -v '\.pdf$\|/output/' | while read -r f; do
    d="$OUT/$1/${f#$STRIP}"; mkdir -p "$(dirname "$d")"; cp "$f" "$d"
  done
}
STRIP=Hermitian_Functional_Calculus/ put Hermitian_Functional_Calculus Hermitian_Functional_Calculus
STRIP= put Quantum_Computing_by_VP ROOT ':(glob)*.thy' document Essential_Functional_Analysis
STRIP=Algorithms/ put HHL_Algorithm Algorithms
# AFP options: documents come from the AFP's settings; keep only document = false and a timeout
python3 - "$OUT" <<'PY'
import re, sys, glob
for f in glob.glob(sys.argv[1] + '/*/ROOT'):
    s = open(f).read()
    def opts(m):
        o = m.group(1)
        keep = ['document = false'] if 'document = false' in o else []
        return 'options [' + ', '.join(keep + ['timeout = 1200']) + ']'
    s = re.sub(r'options \[([^\]]*)\]', opts, s, flags=re.S)
    open(f, 'w').write(s)
PY
for e in Hermitian_Functional_Calculus Quantum_Computing_by_VP HHL_Algorithm; do
  echo "$e: $(find "$OUT/$e" -name '*.thy' | wc -l) theories, $(cat $(find "$OUT/$e" -name '*.thy') | wc -l) lines"
  tar -C "$OUT" -czf "$OUT/$e.tar.gz" "$e"
done
[ $B = 1 ] || exit 0
"$ISABELLE" build $F -o document=pdf -o "document_variants=document:outline=/proof,/ML" -o browser_info \
  -d "$AFP" -d "$OUT/Hermitian_Functional_Calculus" -d "$OUT/Quantum_Computing_by_VP" -d "$OUT/HHL_Algorithm" \
  -D "$OUT/Hermitian_Functional_Calculus" -D "$OUT/Quantum_Computing_by_VP" -D "$OUT/HHL_Algorithm"
