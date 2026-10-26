#!/bin/bash
# Open a theory (default: the notes capstone) in jEdit. External theories come from the
# VP_External heap (tools/jedit/ROOT, built on first use); the project's theories load from source.
# -norestore: don't bring back the previous jEdit view (it put ROOT in front of the capstone).
. "$(dirname "$0")/env.sh"
F=${1:-QC_Notes_Overview.thy}
[ "${F#/}" = "$F" ] && F="$P/$F"
exec "$ISABELLE" jedit -d "$AFP" -d "$P" -d "$P/tools/jedit" -l VP_External -j -norestore "$F"
