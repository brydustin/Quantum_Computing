"""Audit tick 9 (2026-10-27): Schur's lemma by the phase choice <alpha y|x> <= 0 (wip/d23/D03b.thy), which
makes x - alpha y nonzero and absorbs the zero case (IMD's inner_prod_distrib_left does the scaling); and the informal-to-
formal notation sentences the user asked for (outer product, Householder, psd/pd, Choi matrix, partial
traces)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D03b.thy")
old_schur_text = r"""The formal statement writes $e^{i\theta}$ as \<^term>\<open>Complex (cos \<theta>) (sin \<theta>)\<close>; the case
$x=0$ is treated separately.\<close>"""
new_schur_text = r"""The formal statement writes $e^{i\theta}$ as \<^term>\<open>Complex (cos \<theta>) (sin \<theta>)\<close>.
For $x\ne0$ choose the phase $\alpha=e^{i\theta}$ with $\braket{\alpha y}{x}=-|\braket yx|\le0$; then
$d=x-\alpha y\ne0$, and for $w=d/\|d\|$ the reflection $U_wx=x-2\braket wx\,w=x-d=\alpha y$ because
$\braket dd=2\braket dx$.  For $x=0$ also $y=0$ and any unit $w$ serves.\<close>"""
edit("Day03_Unitary_Matrices.thy",
     remove=["schur_lemma_zero_case", "schur_lemma"],
     insert_after=[("schur_lemma", [S["schur_lemma"]]),
                   ("smult_dagger_mult",
                    [txt(r"The Householder reflection $U_w=I-2\ketbra ww$ of the notes is \<open>householder w\<close> in the formal text (displayed \<open>U\<^sub>H w\<close>).")])],
     replace=[(old_schur_text, new_schur_text)])
edit("Day02_Trace_Projections.thy",
     replace=[(r"text \<open>The outer product $\ketbra vw=v\,w^*$ of Dirac's notation.\<close>",
               r"text \<open>The outer product $\ketbra vw=v\,w^*$ of Dirac's notation; the formal text writes it \<open>v \<oslash> w\<close>.\<close>")])
edit("Day04_Hermitian_Matrices.thy",
     replace=[(r"orthogonal to every $v_i$''.\<close>",
               r"""orthogonal to every $v_i$''.  Formally $P\ge0$ and $P>0$ are \<open>psd P\<close> and \<open>pd P\<close>,
displayed \<open>P \<ge>\<^sub>M 0\<close> and \<open>P >\<^sub>M 0\<close>.\<close>""")])
edit("Day19_Choi_Theorem.thy",
     replace=[(r"text \<open>$P_\Phi\in M_n(M_d)$ is the block matrix with $(a,b)$ block $\Phi(E_{ab})$.  It is linear in $\Phi$.\<close>",
               r"""text \<open>$P_\Phi\in M_n(M_d)$ is the block matrix with $(a,b)$ block $\Phi(E_{ab})$.  It is linear in $\Phi$.
The formal text writes it \<open>choi_matrix n d \<Phi>\<close> (displayed \<open>P\<^sub>\<Phi> n d \<Phi>\<close>), with the dimensions explicit.\<close>""")])
edit("Day15_Partial_Traces.thy",
     replace=[(r"defining property on elementary tensors is proved below.\<close>",
               r"""defining property on elementary tensors is proved below.  The formal text writes $\tr_BX$ and
$\tr_AX$ for $X\in M_m\otimes M_p$ as \<open>partial_trace_B m p X\<close> and \<open>partial_trace_A m p X\<close>, and
\<open>partial_trace_on S AB X\<close> (displayed \<open>tr\<^bsub>S\<^esub>\<^bsup>AB\<^esup> X\<close>) traces out the factor $S$ of the
bipartite space $AB$.\<close>""")])
print("installed")
