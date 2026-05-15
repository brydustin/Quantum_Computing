(*
  Title:      Essential_Functional_Analysis.thy
  Author:     Dustin Bryant

  Functional-analysis infrastructure for the Hilbert-Schmidt
  inner-product space of complex matrices, used throughout the
  Quantum_Computing development. Maintained as a separate theory
  so its proofs sit in a smaller simp environment than the main
  Quantum_Computing.thy file.

  Sections:
    1. HS inner product algebra (real-part / conj-symmetry helpers)
    2. Trace and inner-product/trace bridge
    3. HS norm helpers (sq-diff expansion, parallelogram, triangle,
       entry bound, norm-zero)
    4. Tensor product helpers (smult absorption; norm multiplicativity
       — partly sorried, structure preserved)
    5. HS Cauchy / convergence (entry-Cauchy, entry-lim, completeness)
*)

theory Essential_Functional_Analysis
  imports
    Matrix_Typed
    "Jordan_Normal_Form.Schur_Decomposition"
    "Isabelle_Marries_Dirac.Tensor"
begin


section \<open>HS inner-product algebra\<close>

lemma hs_inner_prod_self_eq_of_real:
  "\<langle>\<langle> A | A \<rangle>\<rangle> = complex_of_real (Re (\<langle>\<langle> A | A \<rangle>\<rangle>))"
  using hs_inner_prod_self_real complex_eq_iff
  by (metis Reals_cases of_real_Re)

lemma hs_inner_prod_self_zero_iff:
  fixes A :: "complex Matrix.mat"
  shows "\<langle>\<langle> A | A \<rangle>\<rangle> = 0 \<longleftrightarrow> A = 0\<^sub>m (dim_row A) (dim_col A)"
proof
  assume h: "\<langle>\<langle> A | A \<rangle>\<rangle> = 0"
  have entries_zero: "\<And>i j. i < dim_row A \<Longrightarrow> j < dim_col A
                            \<Longrightarrow> A $$ (i,j) = 0"
    using hs_inner_prod_eq_zero_imp[OF h] by simp
  show "A = 0\<^sub>m (dim_row A) (dim_col A)"
    by (intro eq_matI) (auto simp: entries_zero)
next
  assume eq: "A = 0\<^sub>m (dim_row A) (dim_col A)"
  have entries_zero:
    "\<And>i j. i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> A $$ (i,j) = 0"
  proof -
    fix i j assume i: "i < dim_row A" and j: "j < dim_col A"
    have "A $$ (i,j) = (0\<^sub>m (dim_row A) (dim_col A)) $$ (i,j)"
      using eq by simp
    also have "\<dots> = 0" using i j by simp
    finally show "A $$ (i,j) = 0" .
  qed
  show "\<langle>\<langle> A | A \<rangle>\<rangle> = 0"
    unfolding hs_inner_prod_def
    by (intro sum.neutral ballI) (simp add: entries_zero)
qed

lemma Re_hs_inner_prod_right_smult_real:
  fixes A B :: "complex Matrix.mat" and t :: real
  assumes "dim_row A = dim_row B" and "dim_col A = dim_col B"
  shows "Re (\<langle>\<langle> A | complex_of_real t \<cdot>\<^sub>m B \<rangle>\<rangle>) = t * Re (\<langle>\<langle> A | B \<rangle>\<rangle>)"
proof -
  have d1: "dim_row B = dim_row A" using assms by simp
  have d2: "dim_col B = dim_col A" using assms by simp
  have "\<langle>\<langle> A | complex_of_real t \<cdot>\<^sub>m B \<rangle>\<rangle> = complex_of_real t * \<langle>\<langle> A | B \<rangle>\<rangle>"
    by (rule hs_inner_prod_right_smult[OF d1 d2])
  thus ?thesis by simp
qed

lemma Re_hs_inner_prod_swap:
  fixes A B :: "complex Matrix.mat"
  assumes "dim_row A = dim_row B" and "dim_col A = dim_col B"
  shows "Re (\<langle>\<langle> A | B \<rangle>\<rangle>) = Re (\<langle>\<langle> B | A \<rangle>\<rangle>)"
proof -
  have "\<langle>\<langle> A | B \<rangle>\<rangle> = cnj (\<langle>\<langle> B | A \<rangle>\<rangle>)"
    by (rule hs_inner_prod_cnj[OF assms])
  thus ?thesis by simp
qed


section \<open>Trace lemmas\<close>

lemma Tr_dagger:
  fixes M :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat n n"
  shows "Tr (M\<^sup>\<dagger>) = cnj (Tr M)"
proof -
  have dr: "dim_row M = n" and dc: "dim_col M = n" using M_c by auto
  have d_dr: "dim_row (M\<^sup>\<dagger>) = n" using dc by simp
  have d_dc: "dim_col (M\<^sup>\<dagger>) = n" using dr by simp
  have "Tr (M\<^sup>\<dagger>) = (\<Sum>r<n. (M\<^sup>\<dagger>) $$ (r,r))"
    unfolding Tr_def using d_dr d_dc by simp
  also have "\<dots> = (\<Sum>r<n. cnj (M $$ (r,r)))"
    using dr dc unfolding dagger_def by simp
  also have "\<dots> = cnj (\<Sum>r<n. M $$ (r,r))" by simp
  also have "\<dots> = cnj (Tr M)"
    unfolding Tr_def using dr dc by simp
  finally show ?thesis .
qed

lemma Tr_smult_mat:
  fixes M :: "complex Matrix.mat" and c :: complex
  assumes M_c: "M \<in> carrier_mat n n"
  shows "Tr (c \<cdot>\<^sub>m M) = c * Tr M"
proof -
  have dr: "dim_row M = n" and dc: "dim_col M = n" using M_c by auto
  have "Tr (c \<cdot>\<^sub>m M) = (\<Sum>r<n. (c \<cdot>\<^sub>m M) $$ (r,r))"
    unfolding Tr_def using dr dc by simp
  also have "\<dots> = (\<Sum>r<n. c * M $$ (r,r))"
    using dr dc by (intro sum.cong refl) simp
  also have "\<dots> = c * (\<Sum>r<n. M $$ (r,r))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = c * Tr M"
    unfolding Tr_def using dr dc by simp
  finally show ?thesis .
qed

lemma Re_hs_inner_eq_Re_Tr_dagger:
  fixes A B :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat n n"
      and B_c: "B \<in> carrier_mat n n"
  shows "Re (\<langle>\<langle> A | B \<rangle>\<rangle>) = Re (Tr ((A\<^sup>\<dagger>) * B))"
  using A_c B_c hs_inner_prod_as_trace by auto


section \<open>HS norm definition and basic facts\<close>

text \<open>HS / Frobenius norm on raw complex matrices. Definition
duplicates the one in \<open>Matrix_Typed\<close> for the typed wrapper, but
here for the raw matrices.\<close>

definition hs_norm :: "complex Matrix.mat \<Rightarrow> real" where
  "hs_norm A \<equiv> sqrt (Re (\<langle>\<langle> A | A \<rangle>\<rangle>))"

lemma hs_norm_nonneg: "hs_norm A \<ge> 0"
  unfolding hs_norm_def by (rule real_sqrt_ge_zero) (rule hs_inner_prod_self_nonneg)

lemma hs_norm_sq:
  "(hs_norm A)\<^sup>2 = Re (\<langle>\<langle> A | A \<rangle>\<rangle>)"
proof -
  have nn: "Re (\<langle>\<langle> A | A \<rangle>\<rangle>) \<ge> 0" by (rule hs_inner_prod_self_nonneg)
  have "(hs_norm A)\<^sup>2 = (sqrt (Re (\<langle>\<langle> A | A \<rangle>\<rangle>)))\<^sup>2"
    by (simp add: hs_norm_def)
  also have "\<dots> = Re (\<langle>\<langle> A | A \<rangle>\<rangle>)"
    using nn by (rule real_sqrt_pow2)
  finally show ?thesis .
qed

lemma hs_norm_zero: "hs_norm (0\<^sub>m m n) = 0"
  unfolding hs_norm_def hs_inner_prod_def by simp

lemma hs_norm_smult:
  "hs_norm (c \<cdot>\<^sub>m A) = cmod c * hs_norm A"
proof -
  have eq1: "Re (\<langle>\<langle> c \<cdot>\<^sub>m A | c \<cdot>\<^sub>m A \<rangle>\<rangle>) = (cmod c)\<^sup>2 * Re (\<langle>\<langle> A | A \<rangle>\<rangle>)"
  proof -
    have "\<langle>\<langle> c \<cdot>\<^sub>m A | c \<cdot>\<^sub>m A \<rangle>\<rangle> = cnj c * \<langle>\<langle> A | c \<cdot>\<^sub>m A \<rangle>\<rangle>"
      by (simp add: hs_inner_prod_left_smult)
    also have "\<dots> = cnj c * (c * \<langle>\<langle> A | A \<rangle>\<rangle>)"
      by (simp add: hs_inner_prod_right_smult)
    also have "\<dots> = (cnj c * c) * \<langle>\<langle> A | A \<rangle>\<rangle>"
      by (simp add: ac_simps)
    also have "\<dots> = complex_of_real ((cmod c)\<^sup>2) * \<langle>\<langle> A | A \<rangle>\<rangle>"
    proof -
      have "cnj c * c = complex_of_real ((cmod c)\<^sup>2)"
        by (metis complex_norm_square mult.commute)
      thus ?thesis by simp
    qed
    finally have "\<langle>\<langle> c \<cdot>\<^sub>m A | c \<cdot>\<^sub>m A \<rangle>\<rangle>
                    = complex_of_real ((cmod c)\<^sup>2) * \<langle>\<langle> A | A \<rangle>\<rangle>" .
    thus ?thesis by simp
  qed
  have nn: "Re (\<langle>\<langle> A | A \<rangle>\<rangle>) \<ge> 0" by (rule hs_inner_prod_self_nonneg)
  have "hs_norm (c \<cdot>\<^sub>m A) = sqrt ((cmod c)\<^sup>2 * Re (\<langle>\<langle> A | A \<rangle>\<rangle>))"
    unfolding hs_norm_def using eq1 by simp
  also have "\<dots> = sqrt ((cmod c)\<^sup>2) * sqrt (Re (\<langle>\<langle> A | A \<rangle>\<rangle>))"
    using nn by (simp add: real_sqrt_mult)
  also have "\<dots> = cmod c * hs_norm A"
    unfolding hs_norm_def by simp
  finally show ?thesis .
qed

text \<open>Triangle inequality for the HS norm via Cauchy-Schwarz.\<close>

lemma hs_norm_triangle:
  fixes A B :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat n n"
      and B_c: "B \<in> carrier_mat n n"
  shows "hs_norm (A + B) \<le> hs_norm A + hs_norm B"
proof -
  have dr: "dim_row A = dim_row B" using A_c B_c by auto
  have dc: "dim_col A = dim_col B" using A_c B_c by auto
  let ?aa = "Re (\<langle>\<langle> A | A \<rangle>\<rangle>)"
  let ?bb = "Re (\<langle>\<langle> B | B \<rangle>\<rangle>)"
  let ?ab = "Re (\<langle>\<langle> A | B \<rangle>\<rangle>)"
  have aa_nn: "?aa \<ge> 0" by (rule hs_inner_prod_self_nonneg)
  have bb_nn: "?bb \<ge> 0" by (rule hs_inner_prod_self_nonneg)
  have ab_eq_ba: "?ab = Re (\<langle>\<langle> B | A \<rangle>\<rangle>)"
    by (metis cnj.sel(1) dc dr hs_inner_prod_cnj)

  have ip_sum:
    "\<langle>\<langle> A + B | A + B \<rangle>\<rangle>
       = \<langle>\<langle> A | A \<rangle>\<rangle> + \<langle>\<langle> A | B \<rangle>\<rangle> + \<langle>\<langle> B | A \<rangle>\<rangle> + \<langle>\<langle> B | B \<rangle>\<rangle>"
  proof -
    have d5: "dim_row A = dim_row A" by simp
    have d6: "dim_col A = dim_col A" by simp
    have d7: "dim_row B = dim_row A" using dr by simp
    have d8: "dim_col B = dim_col A" using dc by simp
    have step2: "\<langle>\<langle> A | A + B \<rangle>\<rangle> = \<langle>\<langle> A | A \<rangle>\<rangle> + \<langle>\<langle> A | B \<rangle>\<rangle>"
      using hs_inner_prod_right_add[OF d5 d6 d7 d8] .
    have d9: "dim_row A = dim_row B" using dr by simp
    have d10: "dim_col A = dim_col B" using dc by simp
    have d11: "dim_row B = dim_row B" by simp
    have d12: "dim_col B = dim_col B" by simp
    have step3: "\<langle>\<langle> B | A + B \<rangle>\<rangle> = \<langle>\<langle> B | A \<rangle>\<rangle> + \<langle>\<langle> B | B \<rangle>\<rangle>"
      using hs_inner_prod_right_add[OF d9 d10 d11 d12] .
    have AB_dr: "dim_row (A + B) = dim_row B" using B_c by auto
    have AB_dc: "dim_col (A + B) = dim_col B" using B_c by auto
    have h1: "dim_row A = dim_row (A + B)" using dr by simp
    have h2: "dim_col A = dim_col (A + B)" using dc by simp
    have h3: "dim_row B = dim_row (A + B)" using dr by simp
    have h4: "dim_col B = dim_col (A + B)" using dc by simp
    have step1_rev: "\<langle>\<langle> A + B | A + B \<rangle>\<rangle>
                      = \<langle>\<langle> A + B | A \<rangle>\<rangle> + \<langle>\<langle> A + B | B \<rangle>\<rangle>"
      using hs_inner_prod_right_add[OF h1 h2 h3 h4] .
    have flipA: "\<langle>\<langle> A + B | A \<rangle>\<rangle> = cnj (\<langle>\<langle> A | A + B \<rangle>\<rangle>)"
      using AB_dr AB_dc dr dc by (intro hs_inner_prod_cnj) auto
    have flipB: "\<langle>\<langle> A + B | B \<rangle>\<rangle> = cnj (\<langle>\<langle> B | A + B \<rangle>\<rangle>)"
      using AB_dr AB_dc dr dc by (intro hs_inner_prod_cnj) auto
    have flipA_eq: "cnj (\<langle>\<langle> A | A + B \<rangle>\<rangle>)
                      = cnj (\<langle>\<langle> A | A \<rangle>\<rangle>) + cnj (\<langle>\<langle> A | B \<rangle>\<rangle>)"
      using step2 by simp
    have flipB_eq: "cnj (\<langle>\<langle> B | A + B \<rangle>\<rangle>)
                      = cnj (\<langle>\<langle> B | A \<rangle>\<rangle>) + cnj (\<langle>\<langle> B | B \<rangle>\<rangle>)"
      using step3 by simp
    have AA_real: "cnj (\<langle>\<langle> A | A \<rangle>\<rangle>) = \<langle>\<langle> A | A \<rangle>\<rangle>"
      using hs_inner_prod_self_real by (metis Reals_cnj_iff)
    have BB_real: "cnj (\<langle>\<langle> B | B \<rangle>\<rangle>) = \<langle>\<langle> B | B \<rangle>\<rangle>"
      using hs_inner_prod_self_real by (metis Reals_cnj_iff)
    have cnj_AB: "cnj (\<langle>\<langle> A | B \<rangle>\<rangle>) = \<langle>\<langle> B | A \<rangle>\<rangle>"
      using hs_inner_prod_cnj[OF d9 d10] by simp
    have cnj_BA: "cnj (\<langle>\<langle> B | A \<rangle>\<rangle>) = \<langle>\<langle> A | B \<rangle>\<rangle>"
      using hs_inner_prod_cnj[OF d7 d8] by simp
    have flipA_full: "\<langle>\<langle> A + B | A \<rangle>\<rangle>
                        = \<langle>\<langle> A | A \<rangle>\<rangle> + \<langle>\<langle> B | A \<rangle>\<rangle>"
      using flipA flipA_eq AA_real cnj_AB by simp
    have flipB_full: "\<langle>\<langle> A + B | B \<rangle>\<rangle>
                        = \<langle>\<langle> A | B \<rangle>\<rangle> + \<langle>\<langle> B | B \<rangle>\<rangle>"
      using flipB flipB_eq BB_real cnj_BA by simp
    show ?thesis using step1_rev flipA_full flipB_full by (simp add: ac_simps)
  qed
  have re_sum: "Re (\<langle>\<langle> A + B | A + B \<rangle>\<rangle>) = ?aa + 2 * ?ab + ?bb"
    using ip_sum ab_eq_ba by simp

  have cs: "?ab\<^sup>2 \<le> ?aa * ?bb"
    using hs_cauchy_schwarz_re[OF dr dc] .
  have ab_le: "?ab \<le> sqrt ?aa * sqrt ?bb"
  proof -
    have "?ab \<le> \<bar>?ab\<bar>" by simp
    also have "\<bar>?ab\<bar> = sqrt (?ab\<^sup>2)" by simp
    also have "\<dots> \<le> sqrt (?aa * ?bb)"
      using cs by (rule real_sqrt_le_mono)
    also have "\<dots> = sqrt ?aa * sqrt ?bb"
      by (rule real_sqrt_mult)
    finally show ?thesis .
  qed

  have target_sq:
    "(hs_norm (A + B))\<^sup>2 \<le> (hs_norm A + hs_norm B)\<^sup>2"
  proof -
    have lhs: "(hs_norm (A + B))\<^sup>2 = ?aa + 2 * ?ab + ?bb"
      using hs_norm_sq[of "A + B"] re_sum by simp
    have hA: "hs_norm A = sqrt ?aa" by (simp add: hs_norm_def)
    have hB: "hs_norm B = sqrt ?bb" by (simp add: hs_norm_def)
    have rhs:
      "(hs_norm A + hs_norm B)\<^sup>2
         = ?aa + 2 * (sqrt ?aa * sqrt ?bb) + ?bb"
    proof -
      have "(hs_norm A + hs_norm B)\<^sup>2 = (sqrt ?aa + sqrt ?bb)\<^sup>2"
        by (simp add: hA hB)
      also have "\<dots> = (sqrt ?aa)\<^sup>2 + 2 * (sqrt ?aa * sqrt ?bb) + (sqrt ?bb)\<^sup>2"
        by (simp add: power2_sum)
      also have "\<dots> = ?aa + 2 * (sqrt ?aa * sqrt ?bb) + ?bb"
        using aa_nn bb_nn by simp
      finally show ?thesis .
    qed
    show ?thesis using lhs rhs ab_le by (simp add: algebra_simps)
  qed

  have lhs_nn: "0 \<le> hs_norm (A + B)" by (rule hs_norm_nonneg)
  have rhs_nn: "0 \<le> hs_norm A + hs_norm B"
    using hs_norm_nonneg[of A] hs_norm_nonneg[of B] by simp
  show ?thesis
    using target_sq lhs_nn rhs_nn power2_le_imp_le by blast
qed

lemma hs_norm_zero_iff:
  fixes A :: "complex Matrix.mat"
  shows "hs_norm A = 0 \<longleftrightarrow> A = 0\<^sub>m (dim_row A) (dim_col A)"
proof
  assume "hs_norm A = 0"
  hence "(hs_norm A)\<^sup>2 = 0" by simp
  hence "Re (\<langle>\<langle> A | A \<rangle>\<rangle>) = 0" by (simp add: hs_norm_sq)
  hence "\<langle>\<langle> A | A \<rangle>\<rangle> = 0"
    using hs_inner_prod_self_eq_of_real by (metis of_real_0)
  thus "A = 0\<^sub>m (dim_row A) (dim_col A)"
    by (simp add: hs_inner_prod_self_zero_iff)
next
  assume eq: "A = 0\<^sub>m (dim_row A) (dim_col A)"
  hence "\<langle>\<langle> A | A \<rangle>\<rangle> = 0" using hs_inner_prod_self_zero_iff by simp
  thus "hs_norm A = 0"
    by (simp add: hs_norm_def)
qed


section \<open>Carath\<eacute>odory's theorem for conic combinations\<close>

text \<open>Given a finite-dimensional real vector space V of dimension
d and a set S of V, every element of the conic hull of S (the set
of finite non-negative linear combinations of elements of S) admits
a representation with at most d generators.

For our application V is the real vector space of Hermitian
(m*p)x(m*p) matrices, of real dimension (m*p)^2; S is the
set of product PSD operators.  This is the bound that allows us
to extract a convergent subsequence from a sequence in the
separable cone (each rho_n decomposes with uniformly-bounded
length, Bolzano-Weierstrass on weights and factors gives a
convergent subsequence, the limit lies in the cone, hence the
cone is closed).

HOL-Analysis has a Carath\<eacute>odory theorem for euclidean_space;
reusing it directly would require establishing a euclidean_space
instance on the relevant matrix subspace.  The alternative is a
list-based proof: linear dependence of any d+1 vectors gives
a non-trivial relation; renormalising weights along this relation
kills one term while keeping all weights non-negative; iterate.\<close>

text \<open>Below is a fold-based weighted sum of the cone-style list,
suitable for stating Carath\<eacute>odory at the matrix level.\<close>

fun cone_list_sum ::
  "nat \<Rightarrow> nat \<Rightarrow>
   (real \<times> complex Matrix.mat \<times> complex Matrix.mat) list \<Rightarrow>
   complex Matrix.mat"
where
  "cone_list_sum m p [] = 0\<^sub>m (m*p) (m*p)"
| "cone_list_sum m p ((w, \<sigma>, \<tau>) # ts) =
     complex_of_real w \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>) + cone_list_sum m p ts"

lemma cone_list_sum_carrier:
  "cone_list_sum m p ts \<in> carrier_mat (m*p) (m*p)"
proof (induction ts)
  case Nil show ?case by simp
next
  case (Cons t ts)
  obtain w \<sigma> \<tau> where t_eq: "t = (w, \<sigma>, \<tau>)" by (cases t)
  show ?case using Cons.IH unfolding t_eq by (simp add: add_carrier_mat)
qed

text \<open>Statement of the matrix-space Carath\<eacute>odory result
specialised to lists of weight-\<sigma>-\<tau> triples; the full proof is
deferred (uses the linear-dependence argument above).\<close>

lemma caratheodory_matrix_cone:
  fixes m p :: nat
      and ts :: "(real \<times> complex Matrix.mat \<times> complex Matrix.mat) list"
  assumes m_pos: "0 < m" and p_pos: "0 < p"
      and ts_typing: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts.
                          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
      and ts_nn: "\<forall>(w, _, _) \<in> set ts. 0 \<le> w"
  shows "\<exists>ts'. length ts' \<le> (m*p)\<^sup>2 + 1
              \<and> (\<forall>(w, \<sigma>, \<tau>) \<in> set ts'.
                    \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
                    \<and> (w, \<sigma>, \<tau>) \<in> set ts)
              \<and> cone_list_sum m p ts = cone_list_sum m p ts'"
  sorry

text \<open>The Bolzano-Weierstrass step that follows Carath\<eacute>odory:
given a bounded HS-norm sequence in the cone, apply
caratheodory_matrix_cone to get decompositions of length at most
K = (m*p)^2 + 1; pad with zero-weight dummy entries; the weights
are bounded after unit-trace normalisation; Bolzano-Weierstrass
extracts a subsequence converging coordinatewise; tensor and
addition are HS-continuous, so the limit equals the original
limit and lies in the cone.

The compactness step requires either embedding the unit-trace
PSD slice into Euclidean space (via HS coordinates, cardinality
2(m*p)^2) and invoking HOL-Analysis compactness, or proving
  sequential compactness directly via diagonal extraction over
  finitely many entries.  The latter is what \<open>HS_Cauchy_imp_convergent\<close>
  achieves for general HS-Cauchy sequences; restricting to the
  bounded-trace PSD slice and applying it pointwise on entries is
  the concrete plan.
\<close>

end
