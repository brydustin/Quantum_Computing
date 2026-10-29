#!/bin/bash
# Usage: tools/jedit.sh [FILE [SESSION]]  (default: the notes capstone, session Quantum_Computing_CP_Maps)
# -R: the theories SESSION imports from other sessions come from a heap (built on first use);
# SESSION's own theories load from source.
# -norestore: don't bring back the previous jEdit view.
# jedit_front.bsh: -R focuses the session ROOT once the session starts; switch back to FILE.
. "$(dirname "$0")/env.sh"
F=${1:-QC_Notes_Overview.thy}
S=${2:-Quantum_Computing_CP_Maps}
[ "${F#/}" = "$F" ] && F="$P/$F"
exec "$ISABELLE" jedit -d "$AFP" -d "$P" -R "$S" -j -norestore -J "-Dqc.front=$F" -j "-run=$P/tools/jedit_front.bsh" "$F"
