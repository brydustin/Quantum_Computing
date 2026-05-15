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

text \<open>HS-norm-squared of \<open>U + (-t) \<cdot> V\<close>, expanded along the
bilinear structure.  We extract this into a stand-alone lemma so
the parameter names do not clash with let-bound names in callers.\<close>

lemma hs_norm_sq_diff_expand:
  fixes U V :: "complex Matrix.mat" and t :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and V_c: "V \<in> carrier_mat n n"
  shows "(hs_norm (U + complex_of_real (-t) \<cdot>\<^sub>m V))\<^sup>2
          = Re (\<langle>\<langle> U | U \<rangle>\<rangle>) - 2 * t * Re (\<langle>\<langle> U | V \<rangle>\<rangle>)
            + t\<^sup>2 * Re (\<langle>\<langle> V | V \<rangle>\<rangle>)"
proof -
  let ?tV = "complex_of_real (-t) \<cdot>\<^sub>m V"
  let ?Z = "U + ?tV"
  have tV_c: "?tV \<in> carrier_mat n n" using V_c by auto
  have Z_c: "?Z \<in> carrier_mat n n" using U_c tV_c by auto
  have U_dr: "dim_row U = n" using U_c by auto
  have U_dc: "dim_col U = n" using U_c by auto
  have V_dr: "dim_row V = n" using V_c by auto
  have V_dc: "dim_col V = n" using V_c by auto
  have tV_dr: "dim_row ?tV = n" using tV_c by auto
  have tV_dc: "dim_col ?tV = n" using tV_c by auto
  have Z_dr: "dim_row ?Z = n" using Z_c by auto
  have Z_dc: "dim_col ?Z = n" using Z_c by auto
  have ZZ_split: "\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle> = \<langle>\<langle> U | ?Z \<rangle>\<rangle> + \<langle>\<langle> ?tV | ?Z \<rangle>\<rangle>"
  proof -
    have rhs_split: "\<langle>\<langle> ?Z | U + ?tV \<rangle>\<rangle>
                       = \<langle>\<langle> ?Z | U \<rangle>\<rangle> + \<langle>\<langle> ?Z | ?tV \<rangle>\<rangle>"
      by (rule hs_inner_prod_right_add)
         (use Z_dr Z_dc U_dr U_dc tV_dr tV_dc in auto)
    have IP1: "\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle>
                  = \<langle>\<langle> ?Z | U \<rangle>\<rangle> + \<langle>\<langle> ?Z | ?tV \<rangle>\<rangle>"
      using rhs_split by simp
    have e1: "\<langle>\<langle> ?Z | U \<rangle>\<rangle> = cnj (\<langle>\<langle> U | ?Z \<rangle>\<rangle>)"
      by (rule hs_inner_prod_cnj) (use U_dr U_dc Z_dr Z_dc in auto)
    have e2: "\<langle>\<langle> ?Z | ?tV \<rangle>\<rangle> = cnj (\<langle>\<langle> ?tV | ?Z \<rangle>\<rangle>)"
      by (rule hs_inner_prod_cnj) (use tV_dr tV_dc Z_dr Z_dc in auto)
    have ZZ_real: "\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle> = cnj (\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle>)"
      using hs_inner_prod_self_real by (metis Reals_cnj_iff)
    have "\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle> = cnj (\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle>)" by (rule ZZ_real)
    also have "cnj (\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle>)
                = cnj (\<langle>\<langle> ?Z | U \<rangle>\<rangle> + \<langle>\<langle> ?Z | ?tV \<rangle>\<rangle>)"
      using IP1 by simp
    also have "\<dots> = cnj (\<langle>\<langle> ?Z | U \<rangle>\<rangle>) + cnj (\<langle>\<langle> ?Z | ?tV \<rangle>\<rangle>)" by simp
    also have "\<dots> = cnj (cnj (\<langle>\<langle> U | ?Z \<rangle>\<rangle>))
                    + cnj (cnj (\<langle>\<langle> ?tV | ?Z \<rangle>\<rangle>))"
      using e1 e2 by simp
    also have "\<dots> = \<langle>\<langle> U | ?Z \<rangle>\<rangle> + \<langle>\<langle> ?tV | ?Z \<rangle>\<rangle>" by simp
    finally show ?thesis .
  qed
  have UZ_split: "\<langle>\<langle> U | ?Z \<rangle>\<rangle> = \<langle>\<langle> U | U \<rangle>\<rangle> + \<langle>\<langle> U | ?tV \<rangle>\<rangle>"
    by (rule hs_inner_prod_right_add)
       (use U_dr U_dc tV_dr tV_dc in auto)
  have tVZ_split: "\<langle>\<langle> ?tV | ?Z \<rangle>\<rangle>
                    = \<langle>\<langle> ?tV | U \<rangle>\<rangle> + \<langle>\<langle> ?tV | ?tV \<rangle>\<rangle>"
    by (rule hs_inner_prod_right_add)
       (use U_dr U_dc tV_dr tV_dc in auto)
  have UtV_smult: "\<langle>\<langle> U | ?tV \<rangle>\<rangle>
                    = complex_of_real (-t) * \<langle>\<langle> U | V \<rangle>\<rangle>"
    by (rule hs_inner_prod_right_smult)
       (use U_dr U_dc V_dr V_dc in auto)
  have tVU_smult: "\<langle>\<langle> ?tV | U \<rangle>\<rangle>
                    = cnj (complex_of_real (-t)) * \<langle>\<langle> V | U \<rangle>\<rangle>"
    by (rule hs_inner_prod_left_smult)
       (use U_dr U_dc V_dr V_dc in auto)
  have tVtV_smult: "\<langle>\<langle> ?tV | ?tV \<rangle>\<rangle>
                     = cnj (complex_of_real (-t)) * \<langle>\<langle> V | ?tV \<rangle>\<rangle>"
    by (rule hs_inner_prod_left_smult)
       (use V_dr V_dc tV_dr tV_dc in auto)
  have VtV_smult: "\<langle>\<langle> V | ?tV \<rangle>\<rangle>
                    = complex_of_real (-t) * \<langle>\<langle> V | V \<rangle>\<rangle>"
    by (rule hs_inner_prod_right_smult)
       (use V_dr V_dc in auto)
  have full:
    "\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle>
       = \<langle>\<langle> U | U \<rangle>\<rangle>
         + complex_of_real (-t) * \<langle>\<langle> U | V \<rangle>\<rangle>
         + (cnj (complex_of_real (-t)) * \<langle>\<langle> V | U \<rangle>\<rangle>
             + cnj (complex_of_real (-t))
                 * (complex_of_real (-t) * \<langle>\<langle> V | V \<rangle>\<rangle>))"
    using ZZ_split UZ_split tVZ_split
          UtV_smult tVU_smult tVtV_smult VtV_smult
    by simp
  have re_eq:
    "Re (\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle>)
        = Re (\<langle>\<langle> U | U \<rangle>\<rangle>)
          - t * Re (\<langle>\<langle> U | V \<rangle>\<rangle>)
          - t * Re (\<langle>\<langle> V | U \<rangle>\<rangle>)
          + t\<^sup>2 * Re (\<langle>\<langle> V | V \<rangle>\<rangle>)"
    using full by (simp add: power2_eq_square)
  have swap: "Re (\<langle>\<langle> V | U \<rangle>\<rangle>) = Re (\<langle>\<langle> U | V \<rangle>\<rangle>)"
  proof -
    have d1: "dim_row V = dim_row U" using V_dr U_dr by simp
    have d2: "dim_col V = dim_col U" using V_dc U_dc by simp
    have "\<langle>\<langle> V | U \<rangle>\<rangle> = cnj (\<langle>\<langle> U | V \<rangle>\<rangle>)"
      by (rule hs_inner_prod_cnj[OF d1 d2])
    thus ?thesis by simp
  qed
  have "(hs_norm ?Z)\<^sup>2 = Re (\<langle>\<langle> ?Z | ?Z \<rangle>\<rangle>)" by (rule hs_norm_sq)
  thus ?thesis using re_eq swap by simp
qed

text \<open>HS norm satisfies the parallelogram identity.\<close>

lemma hs_norm_parallelogram:
  fixes U V :: "complex Matrix.mat"
  assumes U_c: "U \<in> carrier_mat n n"
      and V_c: "V \<in> carrier_mat n n"
  shows "(hs_norm (U + V))\<^sup>2 + (hs_norm (U - V))\<^sup>2
          = 2 * (hs_norm U)\<^sup>2 + 2 * (hs_norm V)\<^sup>2"
proof -
  have minus_eq: "U + complex_of_real (-1) \<cdot>\<^sub>m V = U - V"
    using U_c V_c
    by (intro eq_matI) (auto simp: minus_mat_def uminus_mat_def)
  have plus_eq: "U + complex_of_real (-(-1)) \<cdot>\<^sub>m V = U + V"
    using U_c V_c by (intro eq_matI) auto
  have neg_one_expand:
    "(hs_norm (U + complex_of_real (-1) \<cdot>\<^sub>m V))\<^sup>2
       = Re (\<langle>\<langle> U | U \<rangle>\<rangle>) - 2 * 1 * Re (\<langle>\<langle> U | V \<rangle>\<rangle>)
         + 1\<^sup>2 * Re (\<langle>\<langle> V | V \<rangle>\<rangle>)"
    by (rule hs_norm_sq_diff_expand[OF U_c V_c])
  have pos_one_expand:
    "(hs_norm (U + complex_of_real (-(-1)) \<cdot>\<^sub>m V))\<^sup>2
       = Re (\<langle>\<langle> U | U \<rangle>\<rangle>) - 2 * (-1) * Re (\<langle>\<langle> U | V \<rangle>\<rangle>)
         + (-1)\<^sup>2 * Re (\<langle>\<langle> V | V \<rangle>\<rangle>)"
    by (rule hs_norm_sq_diff_expand[OF U_c V_c])
  have UU_eq: "Re (\<langle>\<langle> U | U \<rangle>\<rangle>) = (hs_norm U)\<^sup>2" by (simp add: hs_norm_sq)
  have VV_eq: "Re (\<langle>\<langle> V | V \<rangle>\<rangle>) = (hs_norm V)\<^sup>2" by (simp add: hs_norm_sq)
  have minus_norm: "(hs_norm (U - V))\<^sup>2
                      = (hs_norm U)\<^sup>2 - 2 * Re (\<langle>\<langle> U | V \<rangle>\<rangle>) + (hs_norm V)\<^sup>2"
    using neg_one_expand minus_eq UU_eq VV_eq by simp
  have plus_norm: "(hs_norm (U + V))\<^sup>2
                     = (hs_norm U)\<^sup>2 + 2 * Re (\<langle>\<langle> U | V \<rangle>\<rangle>) + (hs_norm V)\<^sup>2"
    using pos_one_expand plus_eq UU_eq VV_eq by simp
  show ?thesis using minus_norm plus_norm by simp
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

text \<open>Every entry of a matrix is bounded in modulus-squared by the HS-norm
squared.  Useful for transferring HS-norm convergence to entry-wise
convergence.\<close>

lemma cmod_entry_sq_le_hs_norm_sq:
  fixes A :: "complex Matrix.mat" and i j :: nat
  assumes A_c: "A \<in> carrier_mat n n"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "(cmod (A $$ (i,j)))\<^sup>2 \<le> (hs_norm A)\<^sup>2"
proof -
  have dr: "dim_row A = n" using A_c by auto
  have dc: "dim_col A = n" using A_c by auto
  let ?term = "\<lambda>i' j'. (cmod (A $$ (i',j')))\<^sup>2"
  have entry_re:
    "\<And>i' j'. Re (cnj (A $$ (i',j')) * A $$ (i',j')) = ?term i' j'"
  proof -
    fix i' j'
    let ?z = "A $$ (i',j')"
    have eq1: "cnj ?z * ?z = ?z * cnj ?z" by (simp add: mult.commute)
    have eq2: "?z * cnj ?z = complex_of_real ((cmod ?z)\<^sup>2)"
      using complex_norm_square[of ?z, symmetric] by simp
    have eq3: "Re (complex_of_real ((cmod ?z)\<^sup>2)) = (cmod ?z)\<^sup>2" by simp
    show "Re (cnj ?z * ?z) = (cmod ?z)\<^sup>2"
      using eq1 eq2 eq3 by simp
  qed
  have hs_eq: "(hs_norm A)\<^sup>2
                 = (\<Sum>i'\<in>{0..<n}. \<Sum>j'\<in>{0..<n}. ?term i' j')"
  proof -
    have step1: "(hs_norm A)\<^sup>2 = Re (\<langle>\<langle> A | A \<rangle>\<rangle>)" by (rule hs_norm_sq)
    have step2: "Re (\<langle>\<langle> A | A \<rangle>\<rangle>)
                  = Re (\<Sum>i'\<in>{0..<n}. \<Sum>j'\<in>{0..<n}.
                          cnj (A $$ (i',j')) * A $$ (i',j'))"
      unfolding hs_inner_prod_def using dr dc by simp
    have step3: "Re (\<Sum>i'\<in>{0..<n}. \<Sum>j'\<in>{0..<n}.
                          cnj (A $$ (i',j')) * A $$ (i',j'))
                   = (\<Sum>i'\<in>{0..<n}. \<Sum>j'\<in>{0..<n}.
                          Re (cnj (A $$ (i',j')) * A $$ (i',j')))"
      by (simp add: Re_sum)
    have step4: "(\<Sum>i'\<in>{0..<n}. \<Sum>j'\<in>{0..<n}.
                     Re (cnj (A $$ (i',j')) * A $$ (i',j')))
                   = (\<Sum>i'\<in>{0..<n}. \<Sum>j'\<in>{0..<n}. ?term i' j')"
    proof (intro sum.cong refl)
      fix i' j'
      show "Re (cnj (A $$ (i',j')) * A $$ (i',j')) = ?term i' j'"
        by (rule entry_re)
    qed
    show ?thesis using step1 step2 step3 step4 by simp
  qed
  have one_term_le_double_sum:
    "?term i j \<le> (\<Sum>i'\<in>{0..<n}. \<Sum>j'\<in>{0..<n}. ?term i' j')"
  proof -
    have inner_bd: "?term i j \<le> (\<Sum>j'\<in>{0..<n}. ?term i j')"
      using j_lt
      by (intro member_le_sum) (auto simp: zero_le_power2)
    have outer_bd:
      "(\<Sum>j'\<in>{0..<n}. ?term i j')
         \<le> (\<Sum>i'\<in>{0..<n}. \<Sum>j'\<in>{0..<n}. ?term i' j')"
      using i_lt
      by (intro member_le_sum) (auto intro: sum_nonneg simp: zero_le_power2)
    show ?thesis using inner_bd outer_bd by linarith
  qed
  show ?thesis using hs_eq one_term_le_double_sum by simp
qed

text \<open>Modulus form of the entry bound: \<open>|A\<^bsub>i,j\<^esub>| \<le> \<parallel>A\<parallel>\<^sub>HS\<close>.\<close>

lemma cmod_entry_le_hs_norm:
  fixes A :: "complex Matrix.mat" and i j :: nat
  assumes A_c: "A \<in> carrier_mat n n"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "cmod (A $$ (i,j)) \<le> hs_norm A"
proof -
  have sq_le: "(cmod (A $$ (i,j)))\<^sup>2 \<le> (hs_norm A)\<^sup>2"
    by (rule cmod_entry_sq_le_hs_norm_sq[OF A_c i_lt j_lt])
  have lhs_nn: "0 \<le> cmod (A $$ (i,j))" by simp
  have rhs_nn: "0 \<le> hs_norm A" by (rule hs_norm_nonneg)
  show ?thesis using sq_le lhs_nn rhs_nn power2_le_imp_le by blast
qed


section \<open>HS-norm convergence vs entry-wise convergence\<close>

text \<open>HS-norm convergence implies entry-wise convergence:
if \<open>(M\<^sub>n)\<close> converges to \<open>L\<close> in HS-norm then for every
\<open>(i, j)\<close> the entry sequence \<open>M\<^sub>n $$ (i, j)\<close> tends to \<open>L $$ (i, j)\<close>.\<close>

lemma HS_lim_entry_lim:
  fixes M_seq :: "nat \<Rightarrow> complex Matrix.mat" and r :: nat
      and i j :: nat and L :: "complex Matrix.mat"
  assumes carrier: "\<forall>n. M_seq n \<in> carrier_mat r r"
      and L_c: "L \<in> carrier_mat r r"
      and lim: "(\<lambda>n. hs_norm (M_seq n - L)) \<longlonglongrightarrow> 0"
      and i_lt: "i < r" and j_lt: "j < r"
  shows "(\<lambda>n. M_seq n $$ (i,j)) \<longlonglongrightarrow> L $$ (i,j)"
proof (rule metric_LIMSEQ_I)
  fix \<epsilon> :: real assume \<epsilon>_pos: "0 < \<epsilon>"
  obtain N where N_bd: "\<forall>n \<ge> N. hs_norm (M_seq n - L) < \<epsilon>"
    using lim \<epsilon>_pos
    unfolding lim_sequentially
    by (auto simp: dist_real_def hs_norm_nonneg)
  show "\<exists>N. \<forall>n \<ge> N. dist (M_seq n $$ (i,j)) (L $$ (i,j)) < \<epsilon>"
  proof (rule exI[of _ N], intro allI impI)
    fix n assume n_ge: "n \<ge> N"
    let ?D = "M_seq n - L"
    have Mn_c: "M_seq n \<in> carrier_mat r r" using carrier by simp
    have D_c: "?D \<in> carrier_mat r r" by (rule minus_carrier_mat[OF L_c])
    have entry_eq: "?D $$ (i,j) = M_seq n $$ (i,j) - L $$ (i,j)"
    proof -
      have dr: "dim_row L = r" using L_c by auto
      have dc: "dim_col L = r" using L_c by auto
      have "?D $$ (i,j)
              = Matrix.mat (dim_row L) (dim_col L)
                  (\<lambda>ij. M_seq n $$ ij - L $$ ij) $$ (i,j)"
        unfolding minus_mat_def by simp
      also have "\<dots> = M_seq n $$ (i,j) - L $$ (i,j)"
        using i_lt j_lt dr dc by simp
      finally show ?thesis .
    qed
    have cmod_le: "(cmod (?D $$ (i,j)))\<^sup>2 \<le> (hs_norm ?D)\<^sup>2"
      by (rule cmod_entry_sq_le_hs_norm_sq[OF D_c i_lt j_lt])
    have hs_lt: "hs_norm ?D < \<epsilon>" using N_bd n_ge by simp
    have hs_nn: "0 \<le> hs_norm ?D" by (rule hs_norm_nonneg)
    have eps_nn: "0 \<le> \<epsilon>" using \<epsilon>_pos by simp
    have hs_sq_lt: "(hs_norm ?D)\<^sup>2 < \<epsilon>\<^sup>2"
      using hs_lt hs_nn by (intro power_strict_mono) auto
    have cmod_sq_lt: "(cmod (?D $$ (i,j)))\<^sup>2 < \<epsilon>\<^sup>2"
      using cmod_le hs_sq_lt by linarith
    have cmod_lt: "cmod (?D $$ (i,j)) < \<epsilon>"
      by (rule power_less_imp_less_base[OF cmod_sq_lt eps_nn])
    have dist_eq: "dist (M_seq n $$ (i,j)) (L $$ (i,j))
                     = cmod (M_seq n $$ (i,j) - L $$ (i,j))"
      by (simp add: dist_complex_def)
    show "dist (M_seq n $$ (i,j)) (L $$ (i,j)) < \<epsilon>"
      using dist_eq entry_eq cmod_lt by simp
  qed
qed

text \<open>HS-Cauchy implies entry-wise Cauchy: the dual of
\<open>HS_lim_entry_lim\<close>.  Combined with the completeness of \<open>\<complex>\<close> it
yields a candidate limit for every entry.\<close>

lemma HS_Cauchy_entry_Cauchy:
  fixes M_seq :: "nat \<Rightarrow> complex Matrix.mat" and r :: nat
      and i j :: nat
  assumes carrier: "\<forall>n. M_seq n \<in> carrier_mat r r"
      and hs_cauchy: "\<forall>\<epsilon>>0. \<exists>N. \<forall>x \<ge> N. \<forall>y \<ge> N.
                                hs_norm (M_seq x - M_seq y) < \<epsilon>"
      and i_lt: "i < r" and j_lt: "j < r"
  shows "Cauchy (\<lambda>n. M_seq n $$ (i,j))"
proof (rule metric_CauchyI)
  fix \<epsilon> :: real assume \<epsilon>_pos: "0 < \<epsilon>"
  obtain N where N_bd: "\<forall>x \<ge> N. \<forall>y \<ge> N. hs_norm (M_seq x - M_seq y) < \<epsilon>"
    using hs_cauchy \<epsilon>_pos by blast
  show "\<exists>N. \<forall>x \<ge> N. \<forall>y \<ge> N.
            dist (M_seq x $$ (i, j)) (M_seq y $$ (i, j)) < \<epsilon>"
  proof (rule exI[of _ N], intro allI impI)
    fix x y assume xN: "N \<le> x" and yN: "N \<le> y"
    let ?D = "M_seq x - M_seq y"
    have Mx_c: "M_seq x \<in> carrier_mat r r" using carrier by simp
    have My_c: "M_seq y \<in> carrier_mat r r" using carrier by simp
    have D_c: "?D \<in> carrier_mat r r" by (rule minus_carrier_mat[OF My_c])
    have entry_eq: "?D $$ (i,j) = M_seq x $$ (i,j) - M_seq y $$ (i,j)"
    proof -
      have dr: "dim_row (M_seq y) = r" using My_c by auto
      have dc: "dim_col (M_seq y) = r" using My_c by auto
      have "?D $$ (i,j)
              = Matrix.mat (dim_row (M_seq y)) (dim_col (M_seq y))
                  (\<lambda>ij. M_seq x $$ ij - M_seq y $$ ij) $$ (i,j)"
        unfolding minus_mat_def by simp
      also have "\<dots> = M_seq x $$ (i,j) - M_seq y $$ (i,j)"
        using i_lt j_lt dr dc by simp
      finally show ?thesis .
    qed
    have cmod_le: "(cmod (?D $$ (i,j)))\<^sup>2 \<le> (hs_norm ?D)\<^sup>2"
      by (rule cmod_entry_sq_le_hs_norm_sq[OF D_c i_lt j_lt])
    have hs_lt_eps: "hs_norm ?D < \<epsilon>" using N_bd xN yN by simp
    have hs_nn: "0 \<le> hs_norm ?D" by (rule hs_norm_nonneg)
    have eps_nn: "0 \<le> \<epsilon>" using \<epsilon>_pos by simp
    have hs_sq_lt: "(hs_norm ?D)\<^sup>2 < \<epsilon>\<^sup>2"
      using hs_lt_eps hs_nn by (intro power_strict_mono) auto
    have cmod_sq_lt: "(cmod (?D $$ (i,j)))\<^sup>2 < \<epsilon>\<^sup>2"
      using cmod_le hs_sq_lt by linarith
    have cmod_lt: "cmod (?D $$ (i,j)) < \<epsilon>"
      by (rule power_less_imp_less_base[OF cmod_sq_lt eps_nn])
    have dist_eq: "dist (M_seq x $$ (i,j)) (M_seq y $$ (i,j))
                     = cmod (M_seq x $$ (i,j) - M_seq y $$ (i,j))"
      by (simp add: dist_complex_def)
    show "dist (M_seq x $$ (i,j)) (M_seq y $$ (i,j)) < \<epsilon>"
      using dist_eq entry_eq cmod_lt by simp
  qed
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
