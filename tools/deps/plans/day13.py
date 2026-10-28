"""Audit tick 18 (2026-10-27): Tr_mult_outer (Tr (A |v><v|) = <v|Av>) moves from Day 26 to Day 2, where it
belongs; Day 13's pure_state_prob_trace is then three steps (wip/d23/D13.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D13.thy")
O26 = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(head("Day26_Arveson_Extension.thy")) if b["name"]}
edit("Day02_Trace_Projections.thy", insert_after=[("outer_prod_carrier",
     [txt(r"$\Tr(A\,\ketbra vv)=\braket v{Av}$."), O26["Tr_mult_outer"]])])
edit("Day26_Arveson_Extension.thy", remove=["Tr_mult_outer"])
edit("Day13_Density_Matrices.thy", remove=["pure_state_prob_trace"],
     insert_after=[("pure_state_prob_trace", [S["pure_state_prob_trace"]])])
print("installed")
