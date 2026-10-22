# Shared settings for the tools; override by exporting ISABELLE or AFP.
P=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
ISABELLE=${ISABELLE:-/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle}
AFP=${AFP:-/home/dusty/Desktop/Isabelle/afp-2026-04-09/thys}
SESSIONS="Vern_Paulsen_QC_Notes Vern_Paulsen_QC_Sylvester Vern_Paulsen_QC_Search Vern_Paulsen_QC_Demo"
