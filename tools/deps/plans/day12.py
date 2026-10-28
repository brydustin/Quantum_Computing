"""Audit tick 11 (2026-10-27): the oracle U_f as the permutation matrix of the involution
sigma(2J+i) = 2J + (i xor f J) (wip/d23/D12.thy): U e_l = e_{sigma l}, so U^2 = I and U = U*."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D12.thy")
edit("Day12_Quantum_Parallelism.thy", remove=["oracle_exists"],
     insert_after=[("oracle_unitary",
                    [txt(r"""The oracle is the permutation matrix of the involution $\sigma(2J+i)=2J+(i\oplus f(J))$ of the
computational basis of $\C^{2^N}\otimes\C^2$ (the basis vector $e_J\otimes e_i$ is $e_{2J+i}$):
$Ue_l=e_{\sigma(l)}$, so $U^2=I$ and $U=U^*$."""), S["oracle_exists"]])])
print("installed")
