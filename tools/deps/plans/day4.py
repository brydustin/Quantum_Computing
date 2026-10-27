"""Audit tick 7 (2026-10-27): Day 4's positive-matrix proofs through the eigenvector columns of U
(wip/d23/D04.thy).  psd_spectral_decomp_nonneg, psd_kraus_decomp, psd_sqrt_exists, psd_U_diag_Udag and
psd_iff_nonneg_eigenvalues rewritten; diag_mat_of_real_quad_Re_nonneg and diag_mat_of_real_mult_vec_index
dropped; the diag_mat_of_real facts and the spectral-decomposition corollaries moved to the subsections
they belong to; inner_unit_T_unit and mult_mat_vec_index by the sum formulas."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

F = "Day04_Hermitian_Matrices.thy"
S = scratch_blocks("wip/d23/D04.thy")
O = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(head(F)) if b["name"]}
t_dir = txt(r"""The direction $\Rightarrow$, from the spectral theorem:
$P=\sum_j\lambda_j\ketbra{u_j}{u_j}=\sum_j\ketbra{\lambda_j^{1/2}u_j}{\lambda_j^{1/2}u_j}$.""")
t_pos = txt(r"The spectral theorem for positive matrices: $P=U\,\mathrm{diag}(D)\,U^\dagger$ with $D\ge0$.")
edit(F,
     remove=["inner_unit_T_unit", "mult_mat_vec_index", "diag_mat_of_real_mult_vec_index",
             "diag_mat_of_real_hermitian", "diag_mat_of_real_sqrt_square",
             "hermitian_spectral_decomp_eq", "hermitian_spectral_decomp_right",
             "psd_spectral_decomp_nonneg", "psd_kraus_decomp", "psd_sqrt_exists"],
     remove_with_text=["diag_mat_of_real_quad_Re_nonneg", "psd_iff_nonneg_eigenvalues", "psd_U_diag_Udag",
                       "Tr_unitary_diag"],
     insert_after=[
       ("inner_T_double_sum", [S["inner_unit_T_unit"]]),
       ("quadratic_form_zero", [S["mult_mat_vec_index"], S["mult_mat_vec_unit_vec"]]),
       ("diag_mat_of_real_index", [S["col_diag_mat_of_real"], S["diag_mat_of_real_hermitian"],
                                   S["diag_mat_of_real_sqrt_square"]]),
       ("hermitian_real_eigenvalues",
        [txt(r"""The spectral decomposition as $P=UDU^*$ and $PU=UD$: the columns of $U$ are eigenvectors of
$P$ for the eigenvalues $D_i$."""),
         S["hermitian_spectral_decomp_eq"], S["hermitian_spectral_decomp_right"], S["spectral_col_eigenvector"]]),
       ("psd_conjugate",
        [txt(r"$U\,\mathrm{diag}(D)\,U^\dagger$ is positive whenever the real entries of $D$ are non-negative."),
         S["psd_diag_mat_of_real"], S["psd_U_diag_Udag"],
         txt(r"$\Tr(UDU^*)=\sum_iD_i$."), O["Tr_unitary_diag"],
         txt(r"$P\ge 0$ iff $P$ is Hermitian with non-negative eigenvalues:"), S["psd_iff_nonneg_eigenvalues"]]),
       ("outer_sum_psd",
        [txt(r"""The spectral theorem for positive matrices: $P=U\,\mathrm{diag}(D)\,U^\dagger$ with $D\ge0$, since
$D_i=\braket{u_i}{Pu_i}$ for the columns $u_i$ of $U$."""),
         S["psd_spectral_decomp_nonneg"],
         txt(r"""The direction $\Rightarrow$, from the spectral theorem:
$P=\sum_j\lambda_j\ketbra{u_j}{u_j}=\sum_j\ketbra{\lambda_j^{1/2}u_j}{\lambda_j^{1/2}u_j}$, the columns of
$U\sqrt D$."""),
         S["psd_kraus_decomp"]]),
       ("psd_sqrt", [S["psd_sqrt_exists"]])],
     replace=[(t_dir + "\n", ""), (t_pos + "\n", "")])
q = os.path.join(P, F); s = re.sub(r"\n{3,}", "\n\n", open(q).read())
open(q, "w").write(s)
print("installed")

# The new mult_mat_vec_unit_vec duplicated Day 33's mat_vec_unit_col and HHL's mult_unit_vec: keep the
# earliest, point the later uses at it.
edit("Day33_Shor_Code.thy", remove=["mat_vec_unit_col"],
     replace=[("mat_vec_unit_col[OF shor_V_carrier, of 0] mat_vec_unit_col[OF shor_V_carrier, of 1]",
               "mult_mat_vec_unit_vec[OF shor_V_carrier, of 0] mult_mat_vec_unit_vec[OF shor_V_carrier, of 1]")])
edit("Algorithms/HHL_Simulation.thy", remove=["mult_unit_vec"])
for f in ["Algorithms/HHL_Simulation.thy", "Algorithms/HHL_Sparse_Circuit.thy", "Algorithms/HHL_All_Elementary.thy"]:
    q = os.path.join(P, f); s = open(q).read()
    s2 = re.sub(r"\bmult_unit_vec\b", "mult_mat_vec_unit_vec", s)
    assert s2 != s, f
    open(q, "w").write(s2)
print("duplicates removed")
