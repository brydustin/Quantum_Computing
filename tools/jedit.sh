#!/bin/bash
# Usage: tools/jedit.sh [FILE [SESSION]]  (default: the notes capstone, session Quantum_Computing_by_VP)
# -R: the theories SESSION imports from other sessions come from a heap (built on first use);
# SESSION's own theories load from source.
# -norestore: don't bring back the previous jEdit view (it put ROOT in front of the capstone).
. "$(dirname "$0")/env.sh"
F=${1:-QC_Notes_Overview.thy}
S=${2:-Quantum_Computing_by_VP}
[ "${F#/}" = "$F" ] && F="$P/$F"
exec "$ISABELLE" jedit -d "$AFP" -d "$P" -R "$S" -j -norestore "$F"
