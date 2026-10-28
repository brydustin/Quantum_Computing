"""Audit tick 10 (2026-10-27): Schur's theorem by induction with JNF's block-matrix lemmas
(wip/d23/D03c.thy): the block decomposition of U1* A U1 by one eq_matI, the products by
mult_four_block_mat; dagger_four_block_mat_complex, block_diag_mult, block_diag_unitary reproved in a
few lines; four_block_mat_mult_left_block_diag dropped.  Day 19's Choi sentence trimmed."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D03c.thy")
edit("Day03_Unitary_Matrices.thy",
     remove=["dagger_four_block_mat_complex", "block_diag_mult", "block_diag_unitary",
             "four_block_mat_mult_left_block_diag", "schur_induct"],
     insert_after=[("dagger_four_block_mat_complex", [S["dagger_four_block_mat_complex"]]),
                   ("block_diag_mult", [S["block_diag_mult"]]),
                   ("block_diag_unitary", [S["block_diag_unitary"]]),
                   ("schur_induct",
                    [txt(r"""Schur's theorem by induction: a unit eigenvector $v_1$ of $A$ extends to an orthonormal basis,
the columns of a unitary $U_1$; then $M=U_1^*AU_1$ has first column $\lambda e_1$, so
$M=\begin{pmatrix}\lambda&B\\0&A_3\end{pmatrix}$, and for $U_2^*A_3U_2=T_3$ by induction,
$U=U_1\begin{pmatrix}1&0\\0&U_2\end{pmatrix}$ gives $U^*AU=\begin{pmatrix}\lambda&BU_2\\0&T_3\end{pmatrix}$."""),
                     S["schur_induct"]])])
edit("Day19_Choi_Theorem.thy",
     replace=[(r"The formal text writes it \<open>choi_matrix n d \<Phi>\<close> (displayed \<open>P\<^sub>\<Phi> n d \<Phi>\<close>), with the dimensions explicit.\<close>",
               r"Formally \<open>choi_matrix n d \<Phi>\<close>, displayed \<open>P\<^sub>\<Phi> n d \<Phi>\<close>.\<close>")])
print("installed")
