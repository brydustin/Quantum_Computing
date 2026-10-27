"""Audit tick 2 (2026-10-27): the amplification of a Kraus map through blocks and tensor products
instead of 420 lines of index bookkeeping.  Proofs developed in wip/d23/Sweep.thy."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/Sweep.thy")
edit("Essential_Functional_Analysis/Matrix_Lemmas.thy",
     insert_after=[("msum_mult_right", [S["msum_mult_left"]]), ("msum_pairs_mult_right", [S["msum_pairs_mult_left"]])])
edit("Day17_Quantum_Noise.thy",
     remove=["tensor_id_kraus_index", "sum_block_delta", "sum_block_delta_index", "tensor_id_kraus_left_mult_index",
             "tensor_id_kraus_right_mult_index", "kraus_term_index", "kraus_amplification_single",
             "amplification_zero_map", "amplification_add", "amplification_kraus_map_dim"],
     insert_after=[
       ("block_of_mat_single", [txt(r"A $pn\times pn$ matrix is the sum of its blocks in place: $x=\sum_{a,b}E_{ab}\otimes x_{ab}$."),
                                S["block_of_mat_decomposition"]]),
       ("amplification_carrier", [S["amplification_dims"]]),
       ("amplification_index", [txt(r"So $\Phi^{(p)}(x)=\sum_{a,b}E_{ab}\otimes\Phi(x_{ab})$, and $\Phi^{(p)}$ is linear in $\Phi$."),
                                S["amplification_blocks"], S["amplification_zero_map"], S["amplification_add"]]),
       ("tensor_id_kraus_list_carrier", [txt(r"""Block by block, $(I\otimes W)(E_{ab}\otimes x_{ab})(I\otimes W)^*=E_{ab}\otimes Wx_{ab}W^*$, so the
amplification of $X\mapsto WXW^*$ is conjugation by $I_p\otimes W$."""),
                                         S["tensor_unit_sandwich"], S["amplification_sandwich"], S["amplification_kraus_map_dim"]])])
print("day17 done")
