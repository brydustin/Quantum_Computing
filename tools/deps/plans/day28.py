"""Audit tick 35 (2026-10-28): Day 28's ten `metis div_less_iff_less_mult mult.commute` index bounds
(i div p < m from i < m * p) become `blast intro: less_mult_imp_div_less`, and Day 15's four block-index
bound lemmas are instances of the bundle's mult_index_lt (wip/d23/D15c.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

src = head("Day28_Entanglement_Witnesses.thy")
n0 = src.count("by (metis div_less_iff_less_mult mult.commute)")
src = src.replace("by (metis div_less_iff_less_mult mult.commute)", "by (blast intro: less_mult_imp_div_less)")
for old, new in [
    ("by (metis atLeastLessThan_iff div_less_iff_less_mult less_nat_zero_code mult.commute)",
     "by (blast intro: less_mult_imp_div_less)"),
    ("using i_lt p_pos div_less_iff_less_mult by (metis mult.commute)",
     "using i_lt by (blast intro: less_mult_imp_div_less)")]:
    assert src.count(old) == 1, old
    src = src.replace(old, new)
edit("Day28_Entanglement_Witnesses.thy", src=src)
print("installed", n0 + 2, "replacements")

S = scratch_blocks("wip/d23/D15c.thy")
names = ["operator_tensor_iso_map_row_bound", "operator_tensor_iso_map_col_bound",
         "operator_tensor_iso_inv_row_bound", "operator_tensor_iso_inv_col_bound"]
edit("Day15_Partial_Traces.thy", remove=names, insert_after=[(n, [S[n]]) for n in names])
print("installed Day 15 bounds")
