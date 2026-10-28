"""Audit tick 28 (2026-10-28): Day 4 bookkeeping - inner_prod_adjoint_swap is a sum swap, and
psd_MdagM, psd_conjugate, psd_smult_nonneg are one quadratic-form computation each through
psd_iff_quad_form_nonneg (wip/d23/D04c.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D04c.thy")
names = ["inner_prod_adjoint_swap", "psd_MdagM", "psd_conjugate", "psd_smult_nonneg"]
edit("Day04_Hermitian_Matrices.thy", remove=names, insert_after=[(n, [S[n]]) for n in names])
print("installed")
