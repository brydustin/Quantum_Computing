"""Audit tick 19 (2026-10-27): second dead-helper sweep — facts no proof uses and no text cites
(tools/deps/audit.py on the v24 scans), keeping the ones that are results or document a definition."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

for f, names in [("Day02_Trace_Projections.thy", ["mat_unit_mult_entry", "orthonormal_listD_carrier"]),
                 ("Day03_Unitary_Matrices.thy", ["householder_mult_vec_index"]),
                 ("Day17_Quantum_Noise.thy", ["block_of_mat_single"]),
                 ("Day30_Bit_Flip_Code.thy", ["syndrome_proj_two"]),
                 ("Day32_Phase_Flip_Code.thy", ["orthogonal_projections_carrier_left", "orthogonal_projections_carrier_right"])]:
    edit(f, remove=names)
print("installed")
