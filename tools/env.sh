# Shared settings for the tools; override by exporting ISABELLE or AFP.
P=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
ISABELLE=${ISABELLE:-/home/dusty/Desktop/Isabelle/Isabelle2026/bin/isabelle}
AFP=${AFP:-/home/dusty/Desktop/Isabelle/afp-2026-10-29/thys}
SESSIONS="Hermitian_Functional_Calculus Matrix_Analysis_Prerequisites Quantum_Computing_CP_Maps HHL_Algorithm Quantum_Search_Bound HHL_Explicit_Demo Kraus_Maps_Bridge"
