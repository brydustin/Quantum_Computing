# Shared settings for the tools; override by exporting ISABELLE or AFP.
P=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
ISABELLE=${ISABELLE:-/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle}
AFP=${AFP:-/home/dusty/Desktop/Isabelle/afp-2026-04-09/thys}
SESSIONS="Hermitian_Functional_Calculus Vern_Paulsen_QC Vern_Paulsen_QC_Sylvester HHL_Algorithm HHL_Algorithm_Search HHL_Algorithm_Demo HHL_Algorithm_Channels"
