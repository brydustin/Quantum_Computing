"""Audit tick 31 (2026-10-28): Day 2's conj_outer_prod by associativity - W |phi><phi| W* =
(W|phi>)(<phi|W*) = |W phi><W phi| - with the new fact mat_mult_ket (wip/d23/D02b.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D02b.thy")
edit("Day02_Trace_Projections.thy",
     remove=["conj_outer_prod"],
     insert_after=[("conj_outer_prod", [S["mat_mult_ket"], S["conj_outer_prod"]])])
print("installed")
