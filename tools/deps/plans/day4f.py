"""Audit tick 33 (2026-10-28): Day 4's pd_iff_spanning - <x|Px> = <y|y> for y = M* x, whose entries
are the <v_i|x> (wip/d23/D04f.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D04f.thy")
edit("Day04_Hermitian_Matrices.thy", remove=["pd_iff_spanning"],
     insert_after=[("pd_iff_spanning", [S["pd_iff_spanning"]])])
print("installed")
