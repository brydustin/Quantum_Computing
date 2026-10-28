"""Audit tick 27 (2026-10-28): Day 20's theorem that a positive scalar map is completely positive -
<x|P x> = phi(|cx><cx|)_{00} by Day 19's lin_expansion, so the Choi matrix is positive - with the new
Day 4 fact psd_one_by_one (a positive 1x1 matrix is a non-negative real); the tick-23 special case MdagM_psd of Day 4's
psd_MdagM goes again and Day 9 uses the general fact; wip/d23/D20.thy."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D20.thy")
edit("Day04_Hermitian_Matrices.thy",
     insert_after=[("psd_hermitian", [txt(r"A positive $1\times1$ matrix is a non-negative real number."),
                                      S["psd_one_by_one"]])])
edit("Day07_Postulates.thy", remove_with_text=["MdagM_psd"])
edit("Day09_POVMs_Entanglement.thy",
     remove=["measurement_induces_povm"],
     insert_after=[("measurement_induces_povm", [S["measurement_induces_povm"]])])
edit("Day20_Positive_Functionals.thy",
     remove=["positive_scalar_is_cp"],
     insert_after=[("positive_scalar_is_cp", [S["positive_scalar_is_cp"]])])
print("written")
