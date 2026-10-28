"""Audit tick 17 (2026-10-27): Day 18's hermitian_decomp_psd (D = D+ - D- in the spectral form) and
matrix_decomp_psd (X = Re part + i Im part) via the Day 4 spectral lemmas (wip/d23/D18.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D18.thy")
names = ["hermitian_decomp_psd", "matrix_decomp_psd"]
edit("Day18_CP_Maps.thy", remove=names, insert_after=[(n, [S[n]]) for n in names])
print("installed")
