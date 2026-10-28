"""Audit tick 40 (2026-10-28): Day 15's trace_via_onb through JNF's column lemmas and Day 4's
mat_of_cols_dagger_mult_vec_index, trace_tensor through Day 6's sum_div_mod (no hand-built
bijection), and the two operator_tensor_iso zero lemmas by eq_matI (wip/d23/D15d.thy).
New Day 2 Tr_carrier (Tr A = sum of the diagonal for A in carrier_mat n n).  Day 15 is metis/smt-free."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D15d.thy")
edit("Day02_Trace_Projections.thy", insert_after=[("Tr", [txt(r"$\Tr(A)=\sum_iA_{ii}$ for a square matrix $A$."), S["Tr_carrier"]])])
names = ["trace_via_onb", "trace_tensor", "operator_tensor_iso_map_zero", "operator_tensor_iso_inv_zero"]
edit("Day15_Partial_Traces.thy", remove=names, insert_after=[(n, [S[n]]) for n in names])
print("installed")
