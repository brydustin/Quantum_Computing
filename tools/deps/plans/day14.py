"""Audit tick 5 (2026-10-27): Day 14's spectral ensemble and the pure = idempotent theorem through
UDU* = sum_i D_i |u_i><u_i| (wip/d23/D14.thy); helpers to Days 3, 4 and Matrix_Lemmas; the
process comments of the two remaining long proofs removed."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D14.thy")
edit("Day03_Unitary_Matrices.thy", insert_after=[("unitary_conj_mult",
     [txt(r"Conjugation by a unitary is injective: $U^*(UXU^*)U=X$."), S["unitary_conj_cancel"]])])
edit("Day04_Hermitian_Matrices.thy", insert_after=[("psd_U_diag_Udag",
     [txt(r"$\Tr(UDU^*)=\sum_iD_i$."), S["Tr_unitary_diag"]])])
edit("Essential_Functional_Analysis/Matrix_Lemmas.thy", insert_after=[("sum_delta2",
     [txt(r"A list of $0$s and $1$s summing to $1$ has exactly one $1$."), S["sum_zero_one_eq_one"]])])
src = head("Day14_Pure_States.thy")
# drop the process comments inside the two proofs that stay
src = re.sub(r"\n[ \t]*\\<comment> \\<open>(Step \d|Conclusion|Basic facts|Define beta|LHS entry|RHS entry)[^\n]*\\<close>[ \t]*\n", "\n", src)
edit("Day14_Pure_States.thy", src=src,
     remove=["spectral_ensemble_exists", "pure_density_iff_idempotent", "tensor_pure_density"],
     remove_with_text=[],
     insert_after=[
       ("ensemble_density_index", [txt(r"""$UDU^*=\sum_iD_i\,\ketbra{u_i}{u_i}$ for the columns $u_i$ of $U$, which are unit vectors: the
spectral decomposition of a density matrix is the ensemble of its eigenvectors weighted by the
eigenvalues."""), S["unitary_diag_ensemble"], S["unitary_col_quantum_state"], S["spectral_ensemble_exists"]]),
       ("pure_density_is_pure_state_density", [txt(r"""A companion fact not in the notes: a density matrix is pure iff it is idempotent.  For
$\rho=UDU^*$ idempotence makes every eigenvalue $0$ or $1$, and the trace makes exactly one of them
$1$."""), S["pure_density_iff_idempotent"]]),
       ("outer_sum_tensor", [S["tensor_pure_density"]])],
     replace=[(txt(r"A companion fact not in the notes: a density matrix is pure iff it is idempotent.") + "\n\n", "")])
print("installed")
