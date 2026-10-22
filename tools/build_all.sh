#!/bin/bash
# Strict build of every project session, keeping heaps (-b) for the checks and evaluations.
# Usage: tools/build_all.sh [extra isabelle build options]
. "$(dirname "$0")/env.sh"
cd "$P"
"$ISABELLE" build -b "$@" -d "$AFP" -d . $SESSIONS
