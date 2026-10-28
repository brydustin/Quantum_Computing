"""Audit tick 44 (2026-10-28): the remaining one-line metis/smt calls of Days 4, 20, 22_UC, 29 and 31:
hermitian entries through hermitian_index, associativity through instantiated assoc_mult_mat(_vec),
dimension facts through carrier_matD, the Hilbert–Schmidt additivity through
hs_inner_prod_left_add, list and parity facts through auto/blast, and the fidelity of a pure state
with itself through cpx_vec_length_one_iff.  `python3 sweep4.py --scratch` writes one check theory
per day (wip/d23/D44_NN.thy, listed in wip/d23/ROOT) for tools/chk.sh; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

D4, D20, D22 = "Day04_Hermitian_Matrices.thy", "Day20_Positive_Functionals.thy", "Day22_UCP_Compact.thy"
D29, D31 = "Day29_Error_Correction.thy", "Day31_Bit_Flip_Channel.thy"
FILES = [D4, D20, D22, D29, D31]
SRC = {f: head(f) for f in FILES}
EXP = {}
def L(f, a, b):
    t = "\n".join(SRC[f].split("\n")[a - 1:b]); assert "metis" in t or "smt" in t, (f, a, b); EXP[t] = SRC[f].count(t); return t
def blocks(f): return {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC[f]) if b["name"]}

REPS = {
 D22: [(L(D22, 95, 95), r'''      by (rule hermitian_index[OF hx da db])'''),
       (L(D22, 136, 137), r'''        unfolding dagger_def using i_lt j_lt ji by simp'''),
       (L(D22, 194, 195), r'''        by (rule mult_mat_vec_index[OF carrier_mat_triv _ i_lt], rule carrier_vecI) (simp add: xdim)'''),
       (L(D22, 414, 419), r'''    show "Q $$ (b, a) = cnj (Q $$ (a, b))"
      using hermitian_index[OF Qherm, of b a] Qdr Qdc a b by simp'''),
       (L(D22, 592, 595), r'''  show "norm M \<le> 1"
    by (rule power2_le_imp_le) (use norm_sq_le in simp_all)''')],
 D20: [(L(D20, 151, 152), r'''    by (simp only: assoc_mult_mat[OF Ydag_c A_c X_c] assoc_mult_mat[OF Ydag_c AX_c Adag_c])'''),
       (L(D20, 159, 160), r'''    by (simp only: assoc_mult_mat[OF AdYd_c A_c X_c] assoc_mult_mat[OF Adag_c Ydag_c AX_c]
                   assoc_mult_mat[OF Ydag_c A_c X_c])'''),
       (L(D20, 163, 163), r'''    unfolding carrier_matD(2)[OF AdY_c] carrier_matD(1)[OF A_c] ..'''),
       (L(D20, 165, 165), r'''    unfolding carrier_matD(2)[OF Adag_c] carrier_matD(1)[OF Y_c] ..'''),
       (L(D20, 229, 230), r'''    by (intro hs_inner_prod_left_add) (use AdYA_c ka_c X_c in auto)''')],
 D4: [(L(D4, 33, 34), r'''  using arg_cong[OF assms[unfolded hermitian_def], of dim_row] by simp'''),
      (L(D4, 453, 456), r'''    by (rule inner_prod_with_itself_nonneg_reals_non0) (simp add: v_nonzero vdim)'''),
      (L(D4, 744, 745), r'''        by (simp only: assoc_mult_mat_vec[OF M_car dagger_carrier[OF M_car] xcar])'''),
      (L(D4, 935, 937), r'''    by (simp only: assoc_mult_mat_vec[OF M_car dagger_carrier[OF M_car] xcar])''')],
 D31: [(L(D31, 137, 137), r'''    by (rule inner_prod_cnj) (simp add: \<psi>_dim \<psi>'_dim)'''),
       (L(D31, 139, 147), r'''  have sq_real: "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = complex_of_real ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
    unfolding inner_eq conj_swap complex_norm_square ..'''),
       (L(D31, 167, 179), r'''proof -
  have "\<langle>\<psi> | \<psi>\<rangle> = 1"
    using quantum_state_norm1[OF \<psi>_qs] unfolding cpx_vec_length_one_iff .
  thus ?thesis
    unfolding fidelity_pure_states[OF \<psi>_qs \<psi>_qs] by simp''')],
 D29: [(L(D29, 175, 175), r'''    by (auto simp: in_set_conv_nth)'''),
       (L(D29, 257, 257), r'''  thus "w \<in> notes_hamming_code" unfolding notes_hamming_code_def by (blast intro: image_eqI)'''),
       (L(D29, 293, 293), r'''  by (auto simp: mod2_eq_if)''')]}
AFFECTED = {D22: ["closed_hermitian_unwrap_lmat", "closed_nonneg_quad_form_lmat", "psd_entry_bound_by_diag", "norm_lmat_le_of_psd_unit_trace"],
            D20: ["hs_inner_prod_kraus_term", "kraus_adjoint_correct"],
            D4: ["hermitian_square", "hermitian_real_eigenvalues", "outer_sum_psd", "inner_prod_outer_sum_general"],
            D31: ["fidelity_pure_states", "fidelity_self"],
            D29: ["parity_check_detects_one_error", "notes_hamming_code_iff", "mod2_eq_iff"]}

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    used = {old: 0 for reps in REPS.values() for old, _ in reps}
    names = []
    for f, lemmas in AFFECTED.items():
        bl, th = blocks(f), "D44_" + f[3:5]
        out = ["theory " + th, "  imports Quantum_Computing_by_VP." + f[:-4], "begin", ""]
        for n in lemmas:
            t = bl[n]
            for old, new in REPS[f]:
                if old in t: used[old] += t.count(old); t = t.replace(old, new)
            out += [prime(t), ""]
        out.append("end\n"); names.append(th)
        open(os.path.join(P, "wip/d23", th + ".thy"), "w").write("\n".join(out))
    assert all(v == EXP[k] for k, v in used.items()), [k[:40] for k, v in used.items() if v != EXP[k]]
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n" + "".join("    %s\n" % n for n in names))
    print("scratch written:", *names)
else:
    for f in FILES:
        s = SRC[f]
        for old, new in dict(REPS[f]).items(): assert s.count(old) == EXP[old], (f, old[:40]); s = s.replace(old, new)
        edit(f, src=s)
    print("installed")
