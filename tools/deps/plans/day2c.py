"""Audit tick 34 (2026-10-28): Day 2's trace toolkit without metis/smt (Tr_mat_unit,
mat_unit_orthonormal, Tr_hs_diagonal_sum(_square), Tr_uminus, Tr_diff, Tr_unitary_conjugation,
hs_inner_prod_as_trace via Tr_mult_entry, cols_mat_dagger_right, outer_sum_apply,
outer_sum_idempotent; wip/d23/D02c.thy), and three helpers the rewrites of ticks 21 and 27 left
dead: Day 8 outer_proj_idem/outer_proj_hermitian and Day 20 phi_entry_double_sum."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D02c.thy")
names = ["Tr_mat_unit", "mat_unit_orthonormal", "Tr_hs_diagonal_sum", "Tr_hs_diagonal_sum_square",
         "Tr_uminus", "Tr_diff", "Tr_unitary_conjugation", "hs_inner_prod_as_trace",
         "cols_mat_dagger_right", "outer_sum_apply", "outer_sum_idempotent"]
edit("Day02_Trace_Projections.thy", remove=names, insert_after=[(n, [S[n]]) for n in names])
edit("Day08_Measurements.thy", remove=["outer_proj_idem", "outer_proj_hermitian"])
edit("Day20_Positive_Functionals.thy", remove=["phi_entry_double_sum"])
print("installed")
