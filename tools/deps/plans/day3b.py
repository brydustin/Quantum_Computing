"""Audit tick 36 (2026-10-28): Day 3's unitary facts without metis/smt - the IMD facts about
U|v> become facts about U *v v through Day 2's mat_mult_ket, orthonormality of columns and rows is
unitary_unit_col/orthogonal_col_of_unitary, and the norm of a nonzero vector is positive
(new Day 1 cpx_vec_length_pos); wip/d23/D03d.thy."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D03d.thy")
edit("Day01_Inner_Product.thy", insert_after=[("cpx_vec_length_zero_iff", [S["cpx_vec_length_pos"]])])
names = ["unitary_invertible", "unitary_cols_orthonormal", "unitary_rows_orthonormal", "unitary_isometry",
         "unitary_preserves_inner_prod", "eigenvec_normalize", "normalized_vec_norm"]
edit("Day03_Unitary_Matrices.thy", remove=names, insert_after=[(n, [S[n]]) for n in names])
print("installed")
