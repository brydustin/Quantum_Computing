"""Audit tick 20 (2026-10-28): Day 7's tensor lemmas through sum_div_mod and the product-list
indexing helper (wip/d23/D07.thy), and the measurement-probability sum as one induction through
the quadratic form, which moves up to sit beside meas_prob."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D07.thy")
H = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(head("Day07_Postulates.thy")) if b["name"]}
edit("Day07_Postulates.thy",
     remove=["nth_concat_map_upt", "tensor_inner_prod", "tensor_onb", "measurement_probs_sum_one"],
     remove_with_text=["meas_prob_quad_form"],
     insert_after=[
       ("tensor_inner_prod", [S["tensor_inner_prod"],
                              txt(r"Position $p$ of the product list $[h_i\otimes k_j]_{i<n,\,j<m}$ holds $h_{p\div m}\otimes k_{p\bmod m}$.")]),
       ("nth_concat_map_upt", [S["nth_concat_map_upt"]]),
       ("tensor_onb", [S["tensor_onb"]]),
       ("meas_prob", [txt(r"$p_m(\psi)=\braket{\psi}{M_m^*M_m\psi}$, the form in which the notes state Postulate 3."),
                      H["meas_prob_quad_form"],

                      S["measurement_probs_sum_one"]])])
print("installed")
