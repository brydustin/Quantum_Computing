"""Audit tick 47 (2026-10-28): the bundle without metis/smt.  A unitary is square because
Σ_c (A*A)_cc = Σ_r (AA*)_rr; (AB)*(AB) = B*(A*A)B; the tensor of identities and the
mixed-product property through IMD's index_tensor_mat / mult_distr_tensor (the zero-width cases
are empty sums); unitarity of A ⊗ B is one unfolding.  `python3 sweep7.py --scratch` writes one check
theory per bundle theory (wip/d23/D47_*.thy); without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

ML, UTA, LE = ("Matrix_Analysis_Prerequisites/" + t + ".thy" for t in ("Matrix_Lemmas", "Unitary_Tensor_Algebra", "Lmat_Euclidean"))
FILES = [ML, UTA, LE]
SRC = {f: head(f) for f in FILES}
BL = {f: {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(SRC[f]) if b["name"]} for f in FILES}
EXP = {}
def blk(f, n): t = BL[f][n]; EXP[t] = SRC[f].count(t); return t
def seg(f, t): assert t in SRC[f], (f, t[:50]); EXP[t] = SRC[f].count(t); return t

REPS = {
 ML: [(blk(ML, "cnj_mult_self_cmod"), r'''lemma cnj_mult_self_cmod: "cnj z * z = complex_of_real ((cmod z)\<^sup>2)"
  unfolding complex_norm_square by (rule mult.commute)''')],
 LE: [(seg(LE, '''  thus "M = N" by (metis unwrap_lm_inverse)'''), '''  thus "M = N" unfolding unwrap_lm_inject .'''),
      (seg(LE, '''  using Basis_lmat_perp_imp_zero zero_inner_Basis_lmat by metis'''),
       '''  using Basis_lmat_perp_imp_zero zero_inner_Basis_lmat by blast''')],
 UTA: [(blk(UTA, "unitary_square_dim"), r'''lemma unitary_square_dim:
  assumes uA: "unitary A"
  shows "dim_row A = dim_col A"
proof -
  let ?m = "dim_row A" and ?n = "dim_col A"
  have "of_nat ?n = (\<Sum>c<?n. ((A\<^sup>\<dagger>) * A) $$ (c, c))"
    using uA unfolding unitary_def by simp
  also have "\<dots> = (\<Sum>c<?n. \<Sum>r<?m. cnj (A $$ (r, c)) * A $$ (r, c))"
    by (intro sum.cong refl) (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>r<?m. \<Sum>c<?n. A $$ (r, c) * cnj (A $$ (r, c)))"
    by (subst sum.swap) (simp add: mult.commute)
  also have "\<dots> = (\<Sum>r<?m. (A * (A\<^sup>\<dagger>)) $$ (r, r))"
    by (intro sum.cong refl) (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = of_nat ?m"
    using uA unfolding unitary_def by simp
  finally show ?thesis by simp
qed'''),
       (blk(UTA, "unitary_dagger"), r'''lemma unitary_dagger:
  assumes uA: "unitary A"
  shows "unitary (A\<^sup>\<dagger>)"
  using uA unfolding unitary_def by (simp add: dagger_of_dagger_is_id)'''),
       (blk(UTA, "unitary_mult"), r'''lemma unitary_mult:
  assumes UA: "unitary A"
      and UB: "unitary B"
      and dimA: "A \<in> carrier_mat n n"
      and dimB: "B \<in> carrier_mat n n"
  shows "unitary (A * B)"
proof -
  have Ad: "A\<^sup>\<dagger> \<in> carrier_mat n n" and Bd: "B\<^sup>\<dagger> \<in> carrier_mat n n" using dimA dimB by auto
  have A: "(A\<^sup>\<dagger>) * A = 1\<^sub>m n" "A * (A\<^sup>\<dagger>) = 1\<^sub>m n"
    and B: "(B\<^sup>\<dagger>) * B = 1\<^sub>m n" "B * (B\<^sup>\<dagger>) = 1\<^sub>m n"
    using UA UB dimA dimB unfolding unitary_def by auto
  have AB: "(A * B)\<^sup>\<dagger> = (B\<^sup>\<dagger>) * (A\<^sup>\<dagger>)" by (rule dagger_of_prod) (use dimA dimB in simp)
  have "((A * B)\<^sup>\<dagger>) * (A * B) = (B\<^sup>\<dagger>) * (((A\<^sup>\<dagger>) * A) * B)"
    unfolding AB assoc_mult_mat[OF Bd Ad mult_carrier_mat[OF dimA dimB]] assoc_mult_mat[OF Ad dimA dimB] ..
  moreover have "(A * B) * ((A * B)\<^sup>\<dagger>) = A * ((B * (B\<^sup>\<dagger>)) * (A\<^sup>\<dagger>))"
    unfolding AB assoc_mult_mat[OF dimA dimB mult_carrier_mat[OF Bd Ad]] assoc_mult_mat[OF dimB Bd Ad] ..
  ultimately show ?thesis unfolding unitary_def using dimA dimB Ad Bd by (simp add: A B)
qed'''),
       (blk(UTA, "tensor_mat_id"), r'''lemma tensor_mat_id:
  "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) = 1\<^sub>m (n * m)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (1\<^sub>m (n * m))" "j < dim_col (1\<^sub>m (n * m))"
  hence ij: "i < n * m" "j < n * m" by simp_all
  hence "0 < n" "0 < m" by (auto intro: gr0I)
  thus "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) $$ (i, j) = 1\<^sub>m (n * m) $$ (i, j)"
    using ij by (simp add: less_mult_imp_div_less nat_eq_iff_div_mod[of i j m])
qed simp_all'''),
       (seg(UTA, "subsection \\<open> Tensor Adjoint \\<close>\n\n"), ""),
       (seg(UTA, "$(R_1\\otimes T_1)(R_2\\otimes T_2)=R_1R_2\\otimes T_1T_2$ (both from Day 9), and unitarity of"),
        "$(R_1\\otimes T_1)(R_2\\otimes T_2)=R_1R_2\\otimes T_1T_2$, and unitarity of"),
       (blk(UTA, "tensor_mat_mult"), r'''lemma tensor_mat_mult:
  assumes dimAC: "dim_col A = dim_row C"
      and dimBD: "dim_col B = dim_row D"
  shows "Tensor.tensor_mat A B * Tensor.tensor_mat C D =
         Tensor.tensor_mat (A * C) (B * D)"
proof (cases "0 < dim_col A \<and> 0 < dim_col B \<and> 0 < dim_col C \<and> 0 < dim_col D")
  case True
  thus ?thesis by (simp add: mult_distr_tensor[OF dimAC dimBD])
next
  case False
  show ?thesis
  proof (rule eq_matI)
    fix i j
    assume "i < dim_row (Tensor.tensor_mat (A * C) (B * D))" "j < dim_col (Tensor.tensor_mat (A * C) (B * D))"
    hence ij: "i < dim_row A * dim_row B" "j < dim_col C * dim_col D" by simp_all
    hence pos: "0 < dim_row B" "0 < dim_col C" "0 < dim_col D" by (auto intro: gr0I)
    with False have "dim_col A = 0 \<or> dim_col B = 0" by auto
    thus "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i, j) = Tensor.tensor_mat (A * C) (B * D) $$ (i, j)"
      using ij pos dimAC dimBD by (auto simp: scalar_prod_def less_mult_imp_div_less)
  qed (use dimAC dimBD in simp_all)
qed'''),
       (blk(UTA, "tensor_mat_unitary_carrier"), r'''lemma tensor_mat_unitary_carrier:
  assumes dimA: "A \<in> carrier_mat n n"
      and dimB: "B \<in> carrier_mat m m"
      and uA:   "unitary A"
      and uB:   "unitary B"
  shows "unitary (Tensor.tensor_mat A B)"
proof -
  have "(A\<^sup>\<dagger>) * A = 1\<^sub>m n" "A * (A\<^sup>\<dagger>) = 1\<^sub>m n" "(B\<^sup>\<dagger>) * B = 1\<^sub>m m" "B * (B\<^sup>\<dagger>) = 1\<^sub>m m"
    using uA uB dimA dimB unfolding unitary_def by auto
  thus ?thesis
    unfolding unitary_def hermite_cnj_of_tensor tensor_adjoint_mult tensor_mult_adjoint
    using dimA dimB by (simp add: tensor_mat_id)
qed''')]}

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    names = []
    for f in FILES:
        th = "D47_" + os.path.basename(f)[:-4].split("_")[0]
        out = ["theory " + th, "  imports Matrix_Analysis_Prerequisites." + os.path.basename(f)[:-4], "begin", ""]
        for n, t in BL[f].items():
            if not any(old in t for old, _ in REPS[f]): continue
            for old, new in REPS[f]: t = t.replace(old, new)
            out += [prime(t), ""]
        out.append("end\n"); names.append(th)
        open(os.path.join(P, "wip/d23", th + ".thy"), "w").write("\n".join(out))
    root = os.path.join(P, "wip/d23/ROOT"); r = open(root).read()
    open(root, "w").write(r[:r.index("  theories")] + "  theories\n" + "".join("    %s\n" % n for n in names))
    print("scratch written:", *names)
else:
    for f in FILES:
        s = SRC[f]
        for old, new in REPS[f]: assert s.count(old) == EXP[old] == 1, (f, old[:40]); s = s.replace(old, new)
        edit(f, src=s)
    print("installed")
