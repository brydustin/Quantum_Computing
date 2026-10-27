"""Audit tick 3 (2026-10-27): Quantum_Channels rewritten around mixed unitary channels as Kraus maps
(wip/d23/Channels.thy); two general lemmas go to Days 17 and 19."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/Channels.thy")
src = open(os.path.join(P, "wip/d23/Channels.thy")).read()
assert src.startswith("theory Channels\n")
src = ("(*  Title:   Quantum_Channels.thy\n    Author:  Dustin Bryant, standard channels beyond the notes\n*)\n\n"
       "theory Quantum_Channels\n" + src[len("theory Channels\n"):])
open(os.path.join(P, "Quantum_Channels.thy"), "w").write(src)
edit("Quantum_Channels.thy", remove=["kraus_map_dim_single"], remove_with_text=["kraus_map_dim_density_matrix"],
     src=open(os.path.join(P, "Quantum_Channels.thy")).read())
edit("Day17_Quantum_Noise.thy", insert_after=[("kraus_map_dim_two", [S["kraus_map_dim_single"]])])
edit("Day19_Choi_Theorem.thy", insert_after=[("kraus_is_trace_preserving",
     [txt("So Kraus maps carry density matrices to density matrices."), S["kraus_map_dim_density_matrix"]])])
print("channels done")
