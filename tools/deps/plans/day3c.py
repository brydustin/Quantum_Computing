"""Audit tick 38 (2026-10-28): Day 3's unit_vec_extends_to_onb through corthogonal_normalize
(normalising a pairwise-orthogonal list gives an orthonormal list, IMD's inner_prod_distrib_left
for the scalars) and trace_eq_sum_eigenvalues through schur_theorem + similar_matI
(wip/d23/D03e.thy); vec_normalize_unit loses its unused carrier premise.  Day 3 is metis-free."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D03e.thy")
edit("Day03_Unitary_Matrices.thy",
     remove=["vec_normalize_unit", "unit_vec_extends_to_onb", "trace_eq_sum_eigenvalues"],
     insert_after=[("vec_normalize_unit",
                    [S["vec_normalize_unit"],
                     txt(r"Normalising a list of pairwise orthogonal nonzero vectors gives an orthonormal list."),
                     S["corthogonal_normalize"]]),
                   ("unit_vec_extends_to_onb", [S["unit_vec_extends_to_onb"]]),
                   ("trace_eq_sum_eigenvalues", [S["trace_eq_sum_eigenvalues"]])])
print("installed")
