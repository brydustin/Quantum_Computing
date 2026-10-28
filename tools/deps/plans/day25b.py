"""Audit tick 41 (2026-10-28): Day 25_UFN's ten metis calls.  The matrix-vector algebra of
cI + eA and aY + bY* is done by unfolding the distributive and scaling rules, the Hermitian
combination by hermitian_plus/hermitian_real_scale, realness through
hermitian_iff_real_quad_form + complex_is_Real_iff, the of_real conversions by of_real_eq_iff
and the new bundle lemma Re_of_real_eq, the square root bound by power_mono.  `python3 day25b.py --scratch` writes
wip/d23/D25b.thy (primed copies inside a copy of the theory's anonymous context) for
tools/chk.sh; without the flag it installs."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

F = "Day25_Unital_Functional_Norm.thy"
NEWB = r'''lemma Re_of_real_eq: "complex_of_real r = z \<Longrightarrow> r = Re z"
  by (drule arg_cong[where f = Re]) simp'''
REPS = [
 (r'''  moreover have "A *\<^sub>v unit_vec n j = Matrix.col A j" by (rule eq_vecI) (use A j in auto)
  ultimately have "Matrix.col A j $ i = 0" by (metis i index_zero_vec(1))
  thus "A $$ (i,j) = 0\<^sub>m n n $$ (i,j)" using A i j by simp''',
  r'''  hence "(A *\<^sub>v unit_vec n j) $ i = 0" using i by simp
  thus "A $$ (i,j) = 0\<^sub>m n n $$ (i,j)" using A i j by simp'''),
 (r'''    show "hermitian (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A)"
      by (metis Ac assms(3) hermitian_identity hermitian_plus hermitian_real_scale of_real_1 
          of_real_minus one_carrier_mat smult_carrier_mat that)''',
  r'''    have eA: "hermitian (e \<cdot>\<^sub>m A)"
      using e hermitian_real_scale[OF A(2) Ac, of 1] hermitian_real_scale[OF A(2) Ac, of "-1"] by auto
    show "hermitian (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A)"
      by (rule hermitian_plus[OF hermitian_real_scale[OF hermitian_identity one_carrier_mat] eA])
         (rule smult_carrier_mat one_carrier_mat Ac)+'''),
 (r'''    have "(complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v x + e \<cdot>\<^sub>v (A *\<^sub>v x)"
      by (metis (no_types, lifting) ext Ac I TSc add_mult_distrib_mat_vec assms(3) 
          carrier_matD(2) carrier_mat_triv hermitian_square
          index_one_mat(2) index_smult_mat(2,3) one_mult_mat_vec smult_mat_mult_vec x xc)     
    hence "\<langle>x|(complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A) *\<^sub>v x\<rangle> = complex_of_real c * \<langle>x|x\<rangle> + e * \<langle>x|A *\<^sub>v x\<rangle>"
      by (metis Ac carrier_matD(1) dim_mult_mat_vec index_smult_vec(2) inner_prod_right_add' inner_prod_right_smult' x)''',
  r'''    have Mx: "(complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v x + e \<cdot>\<^sub>v (A *\<^sub>v x)"
      unfolding add_mult_distrib_mat_vec[OF smult_carrier_mat[OF one_carrier_mat] smult_carrier_mat[OF Ac] xc]
                smult_mat_mult_vec[OF one_carrier_mat xc] smult_mat_mult_vec[OF Ac xc] one_mult_mat_vec[OF xc] ..
    have dd: "dim_vec (complex_of_real c \<cdot>\<^sub>v x) = dim_vec (e \<cdot>\<^sub>v (A *\<^sub>v x))" using Ac x by simp
    have "\<langle>x|(complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A) *\<^sub>v x\<rangle> = complex_of_real c * \<langle>x|x\<rangle> + e * \<langle>x|A *\<^sub>v x\<rangle>"
      unfolding Mx inner_prod_right_add'[OF dd] inner_prod_right_smult' ..'''),
 (r'''    have "(a \<cdot>\<^sub>m Y + b \<cdot>\<^sub>m (Y\<^sup>\<dagger>)) *\<^sub>v x = a \<cdot>\<^sub>v (Y *\<^sub>v x) + b \<cdot>\<^sub>v (Y\<^sup>\<dagger> *\<^sub>v x)"
      using add_mult_distrib_mat_vec[OF smult_carrier_mat[OF Yc] smult_carrier_mat[OF Ydc] xc]
      by (simp add: smult_mat_mult_vec[OF Yc xc] smult_mat_mult_vec[OF Ydc xc])
    thus ?thesis using Yc Ydc x
      by (metis (no_types, lifting) carrier_matD(1) dim_mult_mat_vec index_smult_vec(2) 
          inner_prod_adjoint_swap inner_prod_cnj  inner_prod_right_add' inner_prod_right_smult')''',
  r'''    have Yx: "(a \<cdot>\<^sub>m Y + b \<cdot>\<^sub>m (Y\<^sup>\<dagger>)) *\<^sub>v x = a \<cdot>\<^sub>v (Y *\<^sub>v x) + b \<cdot>\<^sub>v (Y\<^sup>\<dagger> *\<^sub>v x)"
      unfolding add_mult_distrib_mat_vec[OF smult_carrier_mat[OF Yc] smult_carrier_mat[OF Ydc] xc]
                smult_mat_mult_vec[OF Yc xc] smult_mat_mult_vec[OF Ydc xc] ..
    have sw: "\<langle>x|Y\<^sup>\<dagger> *\<^sub>v x\<rangle> = cnj \<langle>x|Y *\<^sub>v x\<rangle>"
      unfolding inner_prod_adjoint_swap[OF Yc x x] by (rule inner_prod_cnj) (use Yc x in simp)
    have dd: "dim_vec (a \<cdot>\<^sub>v (Y *\<^sub>v x)) = dim_vec (b \<cdot>\<^sub>v (Y\<^sup>\<dagger> *\<^sub>v x))" using Yc Ydc by simp
    show ?thesis unfolding Yx inner_prod_right_add'[OF dd] inner_prod_right_smult' sw ..'''),
 (r'''  finally have e1: "\<parallel>P *\<^sub>v x\<parallel>\<^sup>2 = Re \<langle>?Q *\<^sub>v x|P *\<^sub>v (?Q *\<^sub>v x)\<rangle>" by (metis Re_complex_of_real)''',
  r'''  finally have e1: "\<parallel>P *\<^sub>v x\<parallel>\<^sup>2 = Re \<langle>?Q *\<^sub>v x|P *\<^sub>v (?Q *\<^sub>v x)\<rangle>" by (rule Re_of_real_eq)'''),
 (r'''    finally show ?thesis unfolding Px[symmetric] by (metis Re_complex_of_real)''',
  r'''    finally show ?thesis unfolding Px[symmetric] by (rule Re_of_real_eq)'''),
 (r'''    have "\<langle>x|P *\<^sub>v x\<rangle> = cnj \<langle>x|P *\<^sub>v x\<rangle>"
      using Pc Reals_cnj_iff hermitian_iff_real_quad_form ps psd_def x by auto   
    thus ?thesis by (metis cnj.simps(2) complex_cnj_cancel_iff neg_equal_zero)''',
  r'''    have "\<langle>x|P *\<^sub>v x\<rangle> \<in> \<real>"
      using hermitian_iff_real_quad_form[OF Pc] ps x unfolding psd_def by blast
    thus ?thesis unfolding complex_is_Real_iff .'''),
 (r'''      finally have "\<parallel>M *\<^sub>v x\<parallel>\<^sup>2 = \<parallel>P *\<^sub>v x\<parallel>\<^sup>2 - 2 * s * q + (s\<^sup>2 + t\<^sup>2) * \<parallel>x\<parallel>\<^sup>2" by (metis of_real_eq_iff)''',
  r'''      finally have "\<parallel>M *\<^sub>v x\<parallel>\<^sup>2 = \<parallel>P *\<^sub>v x\<parallel>\<^sup>2 - 2 * s * q + (s\<^sup>2 + t\<^sup>2) * \<parallel>x\<parallel>\<^sup>2" unfolding of_real_eq_iff .'''),
 (r'''    hence "(cmod (f P + ?z))\<^sup>2 \<le> s\<^sup>2 + t\<^sup>2" by (metis norm_ge_zero power_mono real_sqrt_pow2 add_nonneg_nonneg zero_le_power2)''',
  r'''    hence "(cmod (f P + ?z))\<^sup>2 \<le> s\<^sup>2 + t\<^sup>2" using power_mono[of "cmod (f P + ?z)" "sqrt (s\<^sup>2 + t\<^sup>2)" 2] by simp''')]

GLOBAL = ["op_norm_zero_imp"]
HELPERS = ["TSc", "lin2", "comb_in", "f_zero", "adjoint_inner"]
INCTX = ["herm_bound", "positive_imp_bound", "sq_le_norm_quad", "bound_imp_positive"]

def prime(t): return re.sub(r"^(lemma|theorem|corollary) (\S+?):", r"\1 \2':", t, count=1)

if "--scratch" in sys.argv:
    src = head(F)
    blocks = {b["name"]: "\n".join(b["lines"]).rstrip("\n") for b in B.split(src) if b["name"]}
    ctx = re.search(r"^context\n(?:  .*\n)*?begin\n", src, re.M).group(0).rstrip("\n")
    used = {old: 0 for old, _ in REPS}
    def fix(t):
        for old, new in REPS:
            if old in t:
                assert t.count(old) == 1; t = t.replace(old, new); used[old] += 1
        for m in INCTX:                      # copied proofs must cite the primed copies
            t = re.sub(r"(?<=[ \[(])(" + m + r")(?=[ \[)\](])", m + "'", t)
        return t
    out = ["theory D25b", "  imports Quantum_Computing_by_VP.Day25_Unital_Functional_Norm", "begin", "", NEWB, ""]
    out += [prime(fix(blocks[n])) + "\n" for n in GLOBAL]
    out += [ctx, ""] + [blocks[n] + "\n" for n in HELPERS] + [prime(fix(blocks[n])) + "\n" for n in INCTX] + ["end", "", "end", ""]
    assert all(v == 1 for v in used.values()), {k[:50]: v for k, v in used.items()}
    open(os.path.join(P, "wip/d23/D25b.thy"), "w").write("\n".join(out)); print("scratch written")
else:
    edit("Essential_Functional_Analysis/Matrix_Lemmas.thy", insert_after=[("sum_zero_one_eq_one", [NEWB])])
    edit(F, replace=REPS)
    print("installed")
