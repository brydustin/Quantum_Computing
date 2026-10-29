#!/bin/bash
# tools/deps/scan.sh HEAP OUT.tsv [PREFIXES]: dependency scan of a built heap (see scan.ML).
source "$(dirname "$0")/../env.sh"
HEAP=$1 OUT=$2
export SCAN_OUT=$(realpath -m "$OUT")
export SCAN_PREFIXES=${3:-Quantum_Computing_CP_Maps.,Matrix_Analysis_Prerequisites.,HHL_Algorithm.}
"$ISABELLE" ML_process -d "$AFP" -d "$P" -l "$HEAP" -f "$(dirname "$0")/scan.ML"
