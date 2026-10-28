"""Audit tick 21 (2026-10-28): Day 8's outer-projection facts and the orthogonal-states theorem
through Day 2's outer-product toolkit (wip/d23/D08.thy); `outer_prod_dagger` moves to Day 2, and
Day 2 gains the complement-projection lemmas."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D08.thy")
H = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(head("Day08_Measurements.thy")) if b["name"]}
edit("Day02_Trace_Projections.thy",
     insert_after=[("outer_prod_carrier", [txt(r"$(vw^*)^*=wv^*$."), H["outer_prod_dagger"]]),
                   ("outer_prod_idempotent", [txt(r"$I-P$ is again a projection when $P$ is."),
                                              S["complement_projection"], S["complement_dagger"]])])
edit("Day08_Measurements.thy",
     remove=["outer_proj_self", "outer_proj_orth_zero", "outer_proj_idem", "outer_proj_hermitian",
             "orthogonal_states_distinguishable", "outer_prod_dagger"],
     insert_after=[("outer_proj_self", [S["outer_proj_self"]]),
                   ("outer_proj_orth_zero", [S["outer_proj_orth_zero"]]),
                   ("outer_proj_idem", [S["outer_proj_idem"]]),
                   ("outer_proj_hermitian", [S["outer_proj_hermitian"]]),
                   ("orthogonal_states_distinguishable", [S["orthogonal_states_distinguishable"]])])
print("installed")
