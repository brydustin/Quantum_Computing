"""Audit tick 25 (2026-10-28): the remaining long partial-trace lemmas of Day 15 (tensor, trace,
Hermiticity) through index_tensor_mat / sum_div_mod / hermitian_index with the bundle's bound
mult_index_lt, and the projection-complement lemmas of Days 4 and 32 as corollaries of Day 2's
complement_projection / complement_dagger; wip/d23/D15b.thy."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D15b.thy")
edit("Day15_Partial_Traces.thy",
     remove=["partial_trace_B_tensor", "partial_trace_B_trace", "partial_trace_B_hermitian"],
     insert_after=[("partial_trace_B_tensor", [S["partial_trace_B_tensor"]]),
                   ("partial_trace_B_trace", [S["partial_trace_B_trace"]]),
                   ("partial_trace_B_hermitian", [S["partial_trace_B_hermitian"]])])
edit("Day04_Hermitian_Matrices.thy",
     remove=["projection_complement_idempotent"],
     insert_after=[("projection_complement_idempotent", [S["projection_complement_idempotent"]])])
edit("Day32_Phase_Flip_Code.thy",
     remove=["projection_complement"],
     insert_after=[("projection_complement", [S["projection_complement"]])])
print("installed")
