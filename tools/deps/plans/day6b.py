"""Audit tick 30 (2026-10-28): Day 6's bilinearity of the tensor product entrywise through
tensor_vec_index, and Day 17's positivity of Kraus maps by psd_conjugate + psd_add_psd
(wip/d23/D06.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D06.thy")
edit("Day06_Tensor_Products.thy",
     remove=["tensor_vec_bilinear_left", "tensor_vec_bilinear_right"],
     insert_after=[("tensor_vec_bilinear_left", [S["tensor_vec_bilinear_left"]]),
                   ("tensor_vec_bilinear_right", [S["tensor_vec_bilinear_right"]])])
edit("Day17_Quantum_Noise.thy",
     remove=["kraus_map_dim_psd"],
     insert_after=[("kraus_map_dim_psd", [S["kraus_map_dim_psd"]])])
print("installed")
