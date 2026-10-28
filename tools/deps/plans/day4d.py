"""Audit tick 29 (2026-10-28): Day 4's polarization trio - polarization_helper by sesquilinearity on
unit vectors, quadratic_form_zero by four instances of it, hermitian_iff_real_quad_form through
A - A* having zero quadratic form; the indicator-sum helper sum_indicator_T_indicator is then dead
(wip/d23/D04d.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D04d.thy")
names = ["polarization_helper", "quadratic_form_zero", "hermitian_iff_real_quad_form"]
edit("Day04_Hermitian_Matrices.thy", remove=names + ["sum_indicator_T_indicator"],
     insert_after=[(n, [S[n]]) for n in names])
print("installed")
