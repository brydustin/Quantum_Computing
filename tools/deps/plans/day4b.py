"""Audit tick 12 (2026-10-27): the spectral theorem from the Schur form (wip/d23/D04b.thy): T = U* H U is
Hermitian and upper triangular, hence a real diagonal; the (* ... *) process comment of pd_iff_spanning
removed."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

F = "Day04_Hermitian_Matrices.thy"
S = scratch_blocks("wip/d23/D04b.thy")
src = re.sub(r"  \(\* pd P .*?\*\)\n", "", head(F), count=1, flags=re.S)
assert "(* pd P" not in src
edit(F, src=src, remove=["hermitian_spectral_decomp"],
     insert_after=[("hermitian_spectral_decomp", [S["hermitian_spectral_decomp"]])])
print("installed")
