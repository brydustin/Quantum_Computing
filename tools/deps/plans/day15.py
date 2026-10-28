"""Audit tick 24 (2026-10-28): Day 15's measurement identity and the positivity of the partial trace
through a double reindexing (Day 6 sum_div_mod2) and the trace-of-product entry formula
(Day 2 Tr_mult_entry, of which Tr_cyclic becomes a corollary); wip/d23/D15.thy."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D15.thy")
edit("Day02_Trace_Projections.thy",
     remove=["Tr_cyclic"],
     insert_after=[("Tr_cyclic", [S["Tr_mult_entry"], S["Tr_cyclic"]])])
edit("Day06_Tensor_Products.thy",
     insert_after=[("sum_div_mod", [txt(r"The same for two indices at once."), S["sum_div_mod2"]])])
edit("Day15_Partial_Traces.thy",
     remove=["partial_trace_measurement", "partial_trace_B_is_density"],
     insert_after=[("partial_trace_measurement",
                    [txt(r"$\Tr((N\otimes I)\rho)=\Tr(N\,\tr_B\rho)$: reindex $r=ip+a$, $s=jp+b$ and sum out $\delta_{ab}$."),
                     S["Tr_tensor_one_partial_trace_B"], S["partial_trace_measurement"]]),
                   ("partial_trace_B_is_density",
                    [txt(r"$\braket v{\tr_B(X)v}=\sum_a\braket{v\otimes e_a}{X(v\otimes e_a)}\ge0$."),
                     S["partial_trace_B_is_density"]])])
print("installed")
