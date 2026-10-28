"""Audit tick 32 (2026-10-28): Day 4's pd_iff_pos_eigenvalues through IMD's
inner_prod_with_itself_Re_non0 and the square root (wip/d23/D04e.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D04e.thy")
edit("Day04_Hermitian_Matrices.thy", remove=["pd_iff_pos_eigenvalues"],
     insert_after=[("pd_iff_pos_eigenvalues", [S["pd_iff_pos_eigenvalues"]])])
print("installed")
