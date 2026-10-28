"""Audit tick 15 (2026-10-27): Day 2's three matrix-unit lemmas (<<E_ij|X>> = X_ij, X = sum X_ij E_ij,
Tr (M E_sr) = M_rs) as delta sums (wip/d23/D02.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D02.thy")
names = ["hs_inner_prod_mat_unit_left", "mat_unit_expansion", "Tr_mat_unit_mult"]
edit("Day02_Trace_Projections.thy", remove=names, insert_after=[(n, [S[n]]) for n in names])
print("installed")
