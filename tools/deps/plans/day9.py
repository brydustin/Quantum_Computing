"""Audit tick 23 (2026-10-28): Day 9's tensor action (A (x) B)(v (x) w) = Av (x) Bw through Day 6's
sum_div_mod, the measurement-to-POVM lemma through the new Day 7 fact M*M >= 0, and the Bell-state
norm through tensor_unit_vec (wip/d23/D09.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D09.thy")
edit("Day07_Postulates.thy",
     insert_after=[("meas_prob_quad_form", [txt(r"In particular $M^*M\ge0$."), S["MdagM_psd"]])])
edit("Day09_POVMs_Entanglement.thy",
     remove=["measurement_induces_povm", "tensor_mat_vec_mult", "bell_state_norm"],
     insert_after=[("measurement_induces_povm", [S["measurement_induces_povm"]]),
                   ("tensor_mat_vec_mult", [S["tensor_mat_vec_mult"]]),
                   ("bell_state_norm", [S["bell_state_norm"]])])
print("installed")
