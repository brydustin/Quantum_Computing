(*  Title:   Essential_Functional_Analysis.thy
    Author:  Dustin Bryant.  Infrastructure (not in the notes): the Hilbert-Schmidt norm on
             complex matrices, completeness, closedness of the Hermitian and positive
             matrices, and Caratheodory's theorem for conic combinations of product matrices.
*)

theory Essential_Functional_Analysis
  imports
    Matrix_Typed
    Day10_Quantum_Gates
    "Jordan_Normal_Form.Schur_Decomposition"
    "Jordan_Normal_Form.DL_Rank"
begin


section \<open>Overview\<close>

text \<open>The notes take the analysis of finite-dimensional spaces for granted (``it is easy to
see that it is closed'', Day 22; ``$C$ is a closed cone'', Day 28).  This theory supplies
those facts for the matrix space $M_n$ with the Hilbert--Schmidt norm $\norm A=\sqrt{\Tr(A^*A)}$:
the norm axioms, the parallelogram law, entrywise bounds, completeness, closedness of the sets
of Hermitian and of positive semidefinite matrices, and Carath\'eodory's theorem in the form
needed on Day 28: a non-negative combination of product matrices $\sigma\otimes\tau$ in
$M_{mp}$ can be rewritten using at most $2(mp)^2+1$ of them.\<close>

section \<open>HS inner-product algebra\<close>

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
    using hs_inner_prod_real_self by (metis of_real_0)
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

text \<open>HS-norm-squared as a real double sum of entry-modulus squares.
This is the entry-wise expansion of \<open>\<parallel>A\<parallel>\<^sup>2 = Re \<langle>\<langle> A | A \<rangle>\<rangle>\<close>.\<close>

lemma hs_norm_sq_as_entry_sum:
  fixes A :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat r r"
  shows "(hs_norm A)\<^sup>2
           = (\<Sum>i\<in>{0..<r}. \<Sum>j\<in>{0..<r}. (cmod (A $$ (i,j)))\<^sup>2)"
proof -
  have dr: "dim_row A = r" using A_c by auto
  have dc: "dim_col A = r" using A_c by auto
  have body_eq:
    "\<And>i j. Re (cnj (A $$ (i,j)) * A $$ (i,j)) = (cmod (A $$ (i,j)))\<^sup>2"
  proof -
    fix i j
    let ?z = "A $$ (i,j)"
    have e1: "cnj ?z * ?z = ?z * cnj ?z" by (simp add: mult.commute)
    have e2: "?z * cnj ?z = complex_of_real ((cmod ?z)\<^sup>2)"
      using complex_norm_square[of ?z, symmetric] by simp
    show "Re (cnj ?z * ?z) = (cmod ?z)\<^sup>2" using e1 e2 by simp
  qed
  have "(hs_norm A)\<^sup>2 = Re (\<langle>\<langle> A | A \<rangle>\<rangle>)" by (rule hs_norm_sq)
  also have "\<dots> = Re (\<Sum>i\<in>{0..<r}. \<Sum>j\<in>{0..<r}.
                        cnj (A $$ (i,j)) * A $$ (i,j))"
    unfolding hs_inner_prod_def using dr dc by simp
  also have "\<dots> = (\<Sum>i\<in>{0..<r}. \<Sum>j\<in>{0..<r}.
                      Re (cnj (A $$ (i,j)) * A $$ (i,j)))"
    by (simp add: Re_sum)
  also have "\<dots> = (\<Sum>i\<in>{0..<r}. \<Sum>j\<in>{0..<r}. (cmod (A $$ (i,j)))\<^sup>2)"
    by (intro sum.cong refl) (rule body_eq)
  finally show ?thesis .
qed

text \<open>Pointwise entry bounds give an HS-norm-squared bound.\<close>

lemma hs_norm_sq_le_from_entry_bounds:
  fixes A :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat r r"
      and entries: "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow> (cmod (A $$ (i,j)))\<^sup>2 \<le> M"
  shows "(hs_norm A)\<^sup>2 \<le> real r * real r * M"
proof -
  let ?term = "\<lambda>i j. (cmod (A $$ (i,j)))\<^sup>2"
  have inner_bound: "\<And>i. i < r \<Longrightarrow> (\<Sum>j\<in>{0..<r}. ?term i j) \<le> real r * M"
  proof -
    fix i assume i: "i < r"
    have "(\<Sum>j\<in>{0..<r}. ?term i j) \<le> (\<Sum>j\<in>{0..<r}. M)"
      by (intro sum_mono entries[OF i]) auto
    also have "(\<Sum>j\<in>{0..<r}. M :: real) = real r * M" by simp
    finally show "(\<Sum>j\<in>{0..<r}. ?term i j) \<le> real r * M" .
  qed
  have outer_bound:
    "(\<Sum>i\<in>{0..<r}. \<Sum>j\<in>{0..<r}. ?term i j) \<le> real r * real r * M"
  proof -
    have "(\<Sum>i\<in>{0..<r}. \<Sum>j\<in>{0..<r}. ?term i j)
            \<le> (\<Sum>i\<in>{0..<r}. real r * M)"
      by (intro sum_mono inner_bound) auto
    also have "(\<Sum>i\<in>{0..<r}. real r * M) = real r * (real r * M)"
      by simp
    also have "real r * (real r * M) = real r * real r * M"
      by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  have eq: "(hs_norm A)\<^sup>2
            = (\<Sum>i\<in>{0..<r}. \<Sum>j\<in>{0..<r}. ?term i j)"
    by (rule hs_norm_sq_as_entry_sum[OF A_c])
  show ?thesis using eq outer_bound by linarith
qed

text \<open>Entry-cmod bound gives an HS-norm bound.  Combines the
\<open>hs_norm_sq_le_from_entry_bounds\<close> bound with \<open>sqrt\<close>.\<close>

lemma hs_norm_le_from_entry_bounds:
  fixes A :: "complex Matrix.mat" and \<delta> :: real
  assumes A_c: "A \<in> carrier_mat r r"
      and \<delta>_nn: "0 \<le> \<delta>"
      and entries: "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow> cmod (A $$ (i,j)) \<le> \<delta>"
  shows "hs_norm A \<le> real r * \<delta>"
proof -
  have sq_le: "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow> (cmod (A $$ (i,j)))\<^sup>2 \<le> \<delta>\<^sup>2"
  proof -
    fix i j assume i: "i < r" and j: "j < r"
    have nn: "0 \<le> cmod (A $$ (i,j))" by simp
    have le: "cmod (A $$ (i,j)) \<le> \<delta>" by (rule entries[OF i j])
    show "(cmod (A $$ (i,j)))\<^sup>2 \<le> \<delta>\<^sup>2"
      using nn le \<delta>_nn by (intro power_mono) auto
  qed
  have hs_sq_le: "(hs_norm A)\<^sup>2 \<le> real r * real r * \<delta>\<^sup>2"
    by (rule hs_norm_sq_le_from_entry_bounds[OF A_c sq_le])
  have rd_sq_eq: "(real r * \<delta>)\<^sup>2 = real r * real r * \<delta>\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  have hs_sq_le': "(hs_norm A)\<^sup>2 \<le> (real r * \<delta>)\<^sup>2"
    using hs_sq_le rd_sq_eq by linarith
  have rd_nn: "0 \<le> real r * \<delta>" using \<delta>_nn by simp
  show ?thesis
    by (rule power2_le_imp_le[OF hs_sq_le' rd_nn])
qed

text \<open>Entry-wise convergence implies HS-norm convergence.  This is
the slow half of HS-completeness; we use the entry-bound helper to
keep it tractable.\<close>

lemma entry_lim_imp_HS_lim:
  fixes M_seq :: "nat \<Rightarrow> complex Matrix.mat" and M_lim :: "complex Matrix.mat"
      and r :: nat
  assumes carrier: "\<forall>n. M_seq n \<in> carrier_mat r r"
      and M_lim_c: "M_lim \<in> carrier_mat r r"
      and entry_lim: "\<And>i j. i < r \<Longrightarrow> j < r
                       \<Longrightarrow> (\<lambda>n. M_seq n $$ (i,j)) \<longlonglongrightarrow> M_lim $$ (i,j)"
  shows "(\<lambda>n. hs_norm (M_seq n - M_lim)) \<longlonglongrightarrow> 0"
proof (rule metric_LIMSEQ_I)
  fix \<epsilon> :: real assume \<epsilon>_pos: "0 < \<epsilon>"
  define \<delta> where "\<delta> = \<epsilon> / (real r + 1)"
  have \<delta>_pos: "0 < \<delta>"
    unfolding \<delta>_def using \<epsilon>_pos by simp
  have \<delta>_nn: "0 \<le> \<delta>" using \<delta>_pos by simp
  text \<open>Per-entry: \<open>\<exists>N_ij. \<forall>n \<ge> N_ij. cmod entry < \<delta>\<close>.\<close>
  have entry_close:
    "\<And>i j. i < r \<Longrightarrow> j < r
            \<Longrightarrow> \<exists>N. \<forall>n \<ge> N. cmod (M_seq n $$ (i,j) - M_lim $$ (i,j)) \<le> \<delta>"
  proof -
    fix i j assume i: "i < r" and j: "j < r"
    from entry_lim[OF i j] \<delta>_pos
    obtain N where N_bd:
      "\<forall>n \<ge> N. dist (M_seq n $$ (i,j)) (M_lim $$ (i,j)) < \<delta>"
      unfolding lim_sequentially by blast
    have "\<forall>n \<ge> N. cmod (M_seq n $$ (i,j) - M_lim $$ (i,j)) \<le> \<delta>"
      using N_bd by (auto simp: dist_complex_def)
    thus "\<exists>N. \<forall>n \<ge> N. cmod (M_seq n $$ (i,j) - M_lim $$ (i,j)) \<le> \<delta>"
      by blast
  qed
  text \<open>Choose \<open>N_fn (i,j)\<close> via Hilbert choice; take Max over a finite set.\<close>
  define N_pick :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "N_pick = (\<lambda>i j. SOME N. \<forall>n \<ge> N.
              cmod (M_seq n $$ (i,j) - M_lim $$ (i,j)) \<le> \<delta>)"
  have N_pick_bd:
    "\<And>i j. i < r \<Longrightarrow> j < r
           \<Longrightarrow> \<forall>n \<ge> N_pick i j.
                  cmod (M_seq n $$ (i,j) - M_lim $$ (i,j)) \<le> \<delta>"
  proof -
    fix i j assume i: "i < r" and j: "j < r"
    have ex: "\<exists>N. \<forall>n \<ge> N. cmod (M_seq n $$ (i,j) - M_lim $$ (i,j)) \<le> \<delta>"
      by (rule entry_close[OF i j])
    show "\<forall>n \<ge> N_pick i j.
            cmod (M_seq n $$ (i,j) - M_lim $$ (i,j)) \<le> \<delta>"
      unfolding N_pick_def by (rule someI_ex[OF ex])
  qed
  define N_fn :: "nat \<times> nat \<Rightarrow> nat" where
    "N_fn = (\<lambda>p. N_pick (fst p) (snd p))"
  define IdxList :: "(nat \<times> nat) list" where
    "IdxList = concat (map (\<lambda>i. map (\<lambda>j. (i,j)) [0..<r]) [0..<r])"
  have IdxList_in: "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow> (i,j) \<in> set IdxList"
  proof -
    fix i j assume i: "i < r" and j: "j < r"
    have i_in: "i \<in> set [0..<r]" using i by simp
    have j_in: "j \<in> set [0..<r]" using j by simp
    have inner: "(i,j) \<in> set (map (\<lambda>j. (i,j)) [0..<r])" using j_in by auto
    show "(i,j) \<in> set IdxList"
      unfolding IdxList_def using i_in inner by auto
  qed
  define Nbar :: nat where
    "Nbar = sum_list (map N_fn IdxList)"
  have Nbar_ge:
    "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow> N_pick i j \<le> Nbar"
  proof -
    fix i j assume i: "i < r" and j: "j < r"
    have ij_in: "(i,j) \<in> set IdxList" using IdxList_in[OF i j] .
    hence N_in: "N_fn (i,j) \<in> set (map N_fn IdxList)" by simp
    have all_le: "\<And>x :: nat. x \<in> set (map N_fn IdxList) \<Longrightarrow> x \<le> Nbar"
      unfolding Nbar_def by (rule member_le_sum_list) auto
    have eq: "N_fn (i,j) = N_pick i j" unfolding N_fn_def by simp
    show "N_pick i j \<le> Nbar"
      using all_le[OF N_in] eq by simp
  qed
  show "\<exists>N. \<forall>n \<ge> N. dist (hs_norm (M_seq n - M_lim)) 0 < \<epsilon>"
  proof (rule exI[of _ Nbar], intro allI impI)
    fix n assume n_ge: "n \<ge> Nbar"
    let ?D = "M_seq n - M_lim"
    have Mn_c: "M_seq n \<in> carrier_mat r r" using carrier by simp
    have D_c: "?D \<in> carrier_mat r r" by (rule minus_carrier_mat[OF M_lim_c])
    have entry_diff:
      "\<And>i j. i < r \<Longrightarrow> j < r
            \<Longrightarrow> ?D $$ (i,j) = M_seq n $$ (i,j) - M_lim $$ (i,j)"
    proof -
      fix i j assume i: "i < r" and j: "j < r"
      have ML_dr: "dim_row M_lim = r" using M_lim_c by auto
      have ML_dc: "dim_col M_lim = r" using M_lim_c by auto
      have "?D $$ (i,j)
              = Matrix.mat (dim_row M_lim) (dim_col M_lim)
                  (\<lambda>ij. M_seq n $$ ij - M_lim $$ ij) $$ (i,j)"
        unfolding minus_mat_def by simp
      also have "\<dots> = M_seq n $$ (i,j) - M_lim $$ (i,j)"
        using i j ML_dr ML_dc by simp
      finally show "?D $$ (i,j) = M_seq n $$ (i,j) - M_lim $$ (i,j)" .
    qed
    have entry_le: "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow> cmod (?D $$ (i,j)) \<le> \<delta>"
    proof -
      fix i j assume i: "i < r" and j: "j < r"
      have nN: "n \<ge> N_pick i j" using n_ge Nbar_ge[OF i j] by simp
      hence "cmod (M_seq n $$ (i,j) - M_lim $$ (i,j)) \<le> \<delta>"
        using N_pick_bd[OF i j] by simp
      thus "cmod (?D $$ (i,j)) \<le> \<delta>"
        using entry_diff[OF i j] by simp
    qed
    have hs_le_rd: "hs_norm ?D \<le> real r * \<delta>"
      by (rule hs_norm_le_from_entry_bounds[OF D_c \<delta>_nn entry_le])
    have rd_lt: "real r * \<delta> < \<epsilon>"
    proof -
      have "real r * \<delta> = real r * (\<epsilon> / (real r + 1))"
        unfolding \<delta>_def by simp
      also have "\<dots> = (real r / (real r + 1)) * \<epsilon>"
        by simp
      also have "\<dots> < 1 * \<epsilon>"
      proof (rule mult_strict_right_mono[OF _ \<epsilon>_pos])
        have rp1_pos: "0 < real r + 1" by simp
        have "real r < real r + 1" by simp
        thus "real r / (real r + 1) < 1"
          using rp1_pos by (simp add: divide_less_eq)
      qed
      finally show ?thesis by simp
    qed
    have hs_lt: "hs_norm ?D < \<epsilon>" using hs_le_rd rd_lt by linarith
    have hs_nn: "0 \<le> hs_norm ?D" by (rule hs_norm_nonneg)
    show "dist (hs_norm ?D) 0 < \<epsilon>" using hs_lt hs_nn by (simp add: dist_real_def)
  qed
qed

text \<open>HS-completeness of the matrix space: every HS-Cauchy sequence
in \<open>carrier_mat r r\<close> converges in HS norm to a matrix in
\<open>carrier_mat r r\<close>.  Combines \<open>HS_Cauchy_entry_Cauchy\<close> +
completeness of \<open>\<complex>\<close> + \<open>entry_lim_imp_HS_lim\<close>.\<close>

lemma HS_Cauchy_imp_convergent:
  fixes M_seq :: "nat \<Rightarrow> complex Matrix.mat" and r :: nat
  assumes carrier: "\<forall>n. M_seq n \<in> carrier_mat r r"
      and hs_cauchy: "\<forall>\<epsilon>>0. \<exists>N. \<forall>x \<ge> N. \<forall>y \<ge> N.
                                hs_norm (M_seq x - M_seq y) < \<epsilon>"
  shows "\<exists>M_lim. M_lim \<in> carrier_mat r r
              \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n \<ge> N. hs_norm (M_seq n - M_lim) < \<epsilon>)"
proof -
  have entry_cauchy:
    "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow> Cauchy (\<lambda>n. M_seq n $$ (i,j))"
    by (rule HS_Cauchy_entry_Cauchy[OF carrier hs_cauchy])
  have lim_exists:
    "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow> \<exists>L. (\<lambda>n. M_seq n $$ (i,j)) \<longlonglongrightarrow> L"
    using entry_cauchy Cauchy_convergent unfolding convergent_def by metis
  define L :: "nat \<Rightarrow> nat \<Rightarrow> complex" where
    "L i j = (SOME L. (\<lambda>n. M_seq n $$ (i,j)) \<longlonglongrightarrow> L)" for i j
  define M_lim where "M_lim = Matrix.mat r r (\<lambda>(i,j). L i j)"
  have M_lim_c: "M_lim \<in> carrier_mat r r"
    unfolding M_lim_def by simp
  have entry_lim:
    "\<And>i j. i < r \<Longrightarrow> j < r
            \<Longrightarrow> (\<lambda>n. M_seq n $$ (i,j)) \<longlonglongrightarrow> M_lim $$ (i,j)"
  proof -
    fix i j assume i: "i < r" and j: "j < r"
    have entry_eq: "M_lim $$ (i,j) = L i j"
      unfolding M_lim_def using i j by simp
    have "(\<lambda>n. M_seq n $$ (i,j)) \<longlonglongrightarrow> L i j"
      unfolding L_def by (rule someI_ex[OF lim_exists[OF i j]])
    thus "(\<lambda>n. M_seq n $$ (i,j)) \<longlonglongrightarrow> M_lim $$ (i,j)"
      using entry_eq by simp
  qed
  have hs_lim_zero: "(\<lambda>n. hs_norm (M_seq n - M_lim)) \<longlonglongrightarrow> 0"
    by (rule entry_lim_imp_HS_lim[OF carrier M_lim_c entry_lim])
  have conv: "\<forall>\<epsilon>>0. \<exists>N. \<forall>n \<ge> N. hs_norm (M_seq n - M_lim) < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real assume \<epsilon>_pos: "0 < \<epsilon>"
    from hs_lim_zero \<epsilon>_pos
    obtain N where "\<forall>n \<ge> N. dist (hs_norm (M_seq n - M_lim)) 0 < \<epsilon>"
      unfolding lim_sequentially by blast
    hence "\<forall>n \<ge> N. hs_norm (M_seq n - M_lim) < \<epsilon>"
      by (simp add: dist_real_def hs_norm_nonneg)
    thus "\<exists>N. \<forall>n \<ge> N. hs_norm (M_seq n - M_lim) < \<epsilon>" by blast
  qed
  show ?thesis using M_lim_c conv by blast
qed


text \<open>Symmetry of HS-distance: \<open>\<parallel>A - B\<parallel> = \<parallel>B - A\<parallel>\<close>.\<close>

lemma hs_norm_sub_swap:
  fixes A B :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat n n"
      and B_c: "B \<in> carrier_mat n n"
  shows "hs_norm (A - B) = hs_norm (B - A)"
proof -
  have lhs: "A - B = complex_of_real (-1) \<cdot>\<^sub>m (B - A)"
    using A_c B_c
    by (intro eq_matI) (auto simp: minus_mat_def uminus_mat_def)
  have abs_one: "cmod (complex_of_real (-1)) = 1" by simp
  have "hs_norm (A - B) = hs_norm (complex_of_real (-1) \<cdot>\<^sub>m (B - A))"
    using lhs by simp
  also have "\<dots> = cmod (complex_of_real (-1)) * hs_norm (B - A)"
    by (rule hs_norm_smult)
  also have "\<dots> = hs_norm (B - A)" using abs_one by simp
  finally show ?thesis .
qed

text \<open>HS-norm closedness of the Hermitian set.\<close>

lemma hermitian_HS_closed:
  fixes M_seq :: "nat \<Rightarrow> complex Matrix.mat" and L :: "complex Matrix.mat"
      and r :: nat
  assumes carrier: "\<forall>n. M_seq n \<in> carrier_mat r r"
      and L_c: "L \<in> carrier_mat r r"
      and herm_n: "\<forall>n. hermitian (M_seq n)"
      and lim: "(\<lambda>n. hs_norm (M_seq n - L)) \<longlonglongrightarrow> 0"
  shows "hermitian L"
  unfolding hermitian_def
proof (intro eq_matI)
  show "dim_row (L\<^sup>\<dagger>) = dim_row L" using L_c by auto
  show "dim_col (L\<^sup>\<dagger>) = dim_col L" using L_c by auto
  fix i j assume i: "i < dim_row L" and j: "j < dim_col L"
  have iN: "i < r" using i L_c by auto
  have jN: "j < r" using j L_c by auto
  have herm_entry: "\<And>n. M_seq n $$ (j,i) = cnj (M_seq n $$ (i,j))"
  proof -
    fix n
    have Mn_c: "M_seq n \<in> carrier_mat r r" using carrier by simp
    have dr: "dim_row (M_seq n) = r" using Mn_c by auto
    have dc: "dim_col (M_seq n) = r" using Mn_c by auto
    have "M_seq n $$ (j,i) = (M_seq n)\<^sup>\<dagger> $$ (j,i)"
      using herm_n unfolding hermitian_def by simp
    also have "\<dots> = cnj (M_seq n $$ (i,j))"
      using iN jN dr dc unfolding dagger_def by simp
    finally show "M_seq n $$ (j,i) = cnj (M_seq n $$ (i,j))" .
  qed
  have lim_ij: "(\<lambda>n. M_seq n $$ (i,j)) \<longlonglongrightarrow> L $$ (i,j)"
    by (rule HS_lim_entry_lim[OF carrier L_c lim iN jN])
  have lim_ji: "(\<lambda>n. M_seq n $$ (j,i)) \<longlonglongrightarrow> L $$ (j,i)"
    by (rule HS_lim_entry_lim[OF carrier L_c lim jN iN])
  have lim_cnj_ij: "(\<lambda>n. cnj (M_seq n $$ (i,j))) \<longlonglongrightarrow> cnj (L $$ (i,j))"
    using lim_ij by (rule tendsto_cnj)
  have lim_eq: "(\<lambda>n. M_seq n $$ (j,i)) = (\<lambda>n. cnj (M_seq n $$ (i,j)))"
    using herm_entry by auto
  have "L $$ (j,i) = cnj (L $$ (i,j))"
    using lim_ji lim_cnj_ij lim_eq by (metis LIMSEQ_unique)
  hence "(L\<^sup>\<dagger>) $$ (i,j) = L $$ (i,j)"
    using iN jN L_c unfolding dagger_def by simp
  thus "L\<^sup>\<dagger> $$ (i, j) = L $$ (i, j)" .
qed

text \<open>HS-norm closedness of the PSD set.  The proof combines
hermitian\_HS\_closed for the Hermitian part with continuity of the
quadratic form \<open>\<sigma> \<mapsto> \<langle>x | \<sigma> *\<^sub>v x\<rangle>\<close> (linear in the entries of
\<open>\<sigma>\<close>, hence HS-continuous via entry convergence).\<close>

lemma psd_HS_closed:
  fixes \<sigma>_n :: "nat \<Rightarrow> complex Matrix.mat" and \<sigma> :: "complex Matrix.mat"
      and r :: nat
  assumes carrier: "\<forall>n. \<sigma>_n n \<in> carrier_mat r r"
      and \<sigma>_c: "\<sigma> \<in> carrier_mat r r"
      and psd_n: "\<forall>n. psd (\<sigma>_n n)"
      and lim: "(\<lambda>n. hs_norm (\<sigma>_n n - \<sigma>)) \<longlonglongrightarrow> 0"
  shows "psd \<sigma>"
proof -
  have herm_n: "\<forall>n. hermitian (\<sigma>_n n)"
    using psd_n by (auto simp: psd_def)
  have herm: "hermitian \<sigma>"
    by (rule hermitian_HS_closed[OF carrier \<sigma>_c herm_n lim])
  have quad: "\<forall>x. dim_vec x = dim_row \<sigma>
                  \<longrightarrow> Re (\<langle>x | \<sigma> *\<^sub>v x\<rangle>) \<ge> 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim_eq: "dim_vec x = dim_row \<sigma>"
    have xdim: "dim_vec x = r" using xdim_eq \<sigma>_c by auto
    have ip_eq: "\<And>M :: complex Matrix.mat. M \<in> carrier_mat r r \<Longrightarrow>
                  \<langle>x | M *\<^sub>v x\<rangle>
                  = (\<Sum>i\<in>{..<r}. \<Sum>j\<in>{..<r}.
                       cnj (x $ i) * M $$ (i,j) * x $ j)"
    proof -
      fix M :: "complex Matrix.mat" assume M_c: "M \<in> carrier_mat r r"
      have M_dr: "dim_row M = r" using M_c by auto
      have M_dc: "dim_col M = r" using M_c by auto
      have Mxv_dim: "dim_vec (M *\<^sub>v x) = r"
        using M_c xdim by simp
      have entry_eq: "\<And>i. i < r \<Longrightarrow>
              (M *\<^sub>v x) $ i = (\<Sum>j\<in>{..<r}. M $$ (i,j) * x $ j)"
      proof -
        fix i assume i: "i < r"
        have "(M *\<^sub>v x) $ i = Matrix.row M i \<bullet> x"
          using i M_c by simp
        also have "\<dots> = (\<Sum>j<r. Matrix.row M i $ j * x $ j)"
          using xdim M_c by (simp add: scalar_prod_def lessThan_atLeast0)
        also have "\<dots> = (\<Sum>j<r. M $$ (i,j) * x $ j)"
          using i M_c by simp
        finally show "(M *\<^sub>v x) $ i = (\<Sum>j<r. M $$ (i,j) * x $ j)"
          by simp
      qed
      have "\<langle>x | M *\<^sub>v x\<rangle>
             = (\<Sum>i = 0..<r. cnj (x $ i) * (M *\<^sub>v x) $ i)"
        unfolding inner_prod_def using Mxv_dim xdim by simp
      also have "\<dots> = (\<Sum>i\<in>{..<r}. cnj (x $ i)
                                 * (\<Sum>j\<in>{..<r}. M $$ (i,j) * x $ j))"
      proof -
        have "(\<Sum>i = 0..<r. cnj (x $ i) * (M *\<^sub>v x) $ i)
              = (\<Sum>i\<in>{..<r}. cnj (x $ i) * (M *\<^sub>v x) $ i)"
          by (simp add: lessThan_atLeast0)
        also have "\<dots> = (\<Sum>i\<in>{..<r}. cnj (x $ i)
                                   * (\<Sum>j\<in>{..<r}. M $$ (i,j) * x $ j))"
        proof (intro sum.cong refl)
          fix i assume i_in: "i \<in> {..<r}"
          hence i: "i < r" by simp
          show "cnj (x $ i) * (M *\<^sub>v x) $ i
                  = cnj (x $ i) * (\<Sum>j\<in>{..<r}. M $$ (i,j) * x $ j)"
            using entry_eq[OF i] by simp
        qed
        finally show ?thesis .
      qed
      also have "\<dots> = (\<Sum>i\<in>{..<r}. \<Sum>j\<in>{..<r}.
                          cnj (x $ i) * (M $$ (i,j) * x $ j))"
        by (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>i\<in>{..<r}. \<Sum>j\<in>{..<r}.
                          cnj (x $ i) * M $$ (i,j) * x $ j)"
        by (intro sum.cong refl) (simp add: mult.assoc)
      finally show "\<langle>x | M *\<^sub>v x\<rangle>
                       = (\<Sum>i\<in>{..<r}. \<Sum>j\<in>{..<r}.
                            cnj (x $ i) * M $$ (i,j) * x $ j)" .
    qed
    have psd_form: "\<And>n. Re (\<langle>x | \<sigma>_n n *\<^sub>v x\<rangle>) \<ge> 0"
    proof -
      fix n
      have Mn_c: "\<sigma>_n n \<in> carrier_mat r r" using carrier by simp
      have xdim_n: "dim_vec x = dim_row (\<sigma>_n n)" using Mn_c xdim by auto
      show "Re (\<langle>x | \<sigma>_n n *\<^sub>v x\<rangle>) \<ge> 0"
        using psd_n[THEN spec, of n] xdim_n unfolding psd_def by blast
    qed
    have entry_lim: "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow>
                     (\<lambda>n. \<sigma>_n n $$ (i,j)) \<longlonglongrightarrow> \<sigma> $$ (i,j)"
      using HS_lim_entry_lim[OF carrier \<sigma>_c lim] by simp
    have term_lim: "\<And>i j. i < r \<Longrightarrow> j < r \<Longrightarrow>
                     (\<lambda>n. cnj (x $ i) * \<sigma>_n n $$ (i,j) * x $ j)
                     \<longlonglongrightarrow> cnj (x $ i) * \<sigma> $$ (i,j) * x $ j"
    proof -
      fix i j assume i: "i < r" and j: "j < r"
      have "(\<lambda>n. \<sigma>_n n $$ (i,j) * x $ j)
              \<longlonglongrightarrow> \<sigma> $$ (i,j) * x $ j"
        by (rule tendsto_mult_right) (rule entry_lim[OF i j])
      hence h: "(\<lambda>n. cnj (x $ i) * (\<sigma>_n n $$ (i,j) * x $ j))
              \<longlonglongrightarrow> cnj (x $ i) * (\<sigma> $$ (i,j) * x $ j)"
        by (rule tendsto_mult_left)
      have eq1: "\<And>n. cnj (x $ i) * (\<sigma>_n n $$ (i,j) * x $ j)
                     = cnj (x $ i) * \<sigma>_n n $$ (i,j) * x $ j"
        by (simp add: mult.assoc)
      have eq2: "cnj (x $ i) * (\<sigma> $$ (i,j) * x $ j)
                   = cnj (x $ i) * \<sigma> $$ (i,j) * x $ j"
        by (simp add: mult.assoc)
      show "(\<lambda>n. cnj (x $ i) * \<sigma>_n n $$ (i,j) * x $ j)
              \<longlonglongrightarrow> cnj (x $ i) * \<sigma> $$ (i,j) * x $ j"
        using h eq1 eq2 by simp
    qed
    have inner_lim: "(\<lambda>n. (\<Sum>i\<in>{..<r}. \<Sum>j\<in>{..<r}.
                              cnj (x $ i) * \<sigma>_n n $$ (i,j) * x $ j))
                       \<longlonglongrightarrow> (\<Sum>i\<in>{..<r}. \<Sum>j\<in>{..<r}.
                              cnj (x $ i) * \<sigma> $$ (i,j) * x $ j)"
      using term_lim
      by (intro tendsto_sum) auto
    have ip_n_eq: "\<And>n. \<langle>x | \<sigma>_n n *\<^sub>v x\<rangle>
                       = (\<Sum>i\<in>{..<r}. \<Sum>j\<in>{..<r}.
                            cnj (x $ i) * \<sigma>_n n $$ (i,j) * x $ j)"
      using ip_eq[OF carrier[THEN spec]] by simp
    have ip_lim_eq: "\<langle>x | \<sigma> *\<^sub>v x\<rangle>
                       = (\<Sum>i\<in>{..<r}. \<Sum>j\<in>{..<r}.
                            cnj (x $ i) * \<sigma> $$ (i,j) * x $ j)"
      using ip_eq[OF \<sigma>_c] by simp
    have inner_prod_lim: "(\<lambda>n. \<langle>x | \<sigma>_n n *\<^sub>v x\<rangle>) \<longlonglongrightarrow> \<langle>x | \<sigma> *\<^sub>v x\<rangle>"
      using inner_lim ip_n_eq ip_lim_eq by simp
    have re_lim: "(\<lambda>n. Re (\<langle>x | \<sigma>_n n *\<^sub>v x\<rangle>)) \<longlonglongrightarrow> Re (\<langle>x | \<sigma> *\<^sub>v x\<rangle>)"
      using inner_prod_lim by (rule tendsto_Re)
    have psd_form_exN: "\<exists>N. \<forall>n \<ge> N. 0 \<le> Re (\<langle>x | \<sigma>_n n *\<^sub>v x\<rangle>)"
      using psd_form by blast
    show "0 \<le> Re (\<langle>x | \<sigma> *\<^sub>v x\<rangle>)"
      using re_lim psd_form_exN by (rule LIMSEQ_le_const)
  qed
  show ?thesis unfolding psd_def using herm quad by blast
qed

text \<open>Reverse triangle inequality: \<open>\<bar>\<parallel>A\<parallel> - \<parallel>B\<parallel>\<bar> \<le> \<parallel>A - B\<parallel>\<close>.\<close>

lemma hs_norm_sub_triangle_ineq:
  fixes A B :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat n n"
      and B_c: "B \<in> carrier_mat n n"
  shows "\<bar>hs_norm A - hs_norm B\<bar> \<le> hs_norm (A - B)"
proof -
  have AB_c: "A - B \<in> carrier_mat n n" by (rule minus_carrier_mat[OF B_c])
  have BA_c: "B - A \<in> carrier_mat n n" by (rule minus_carrier_mat[OF A_c])
  text \<open>Two inequalities.\<close>
  have A_eq: "A = B + (A - B)"
    using A_c B_c by (intro eq_matI) (auto simp: minus_mat_def)
  have lhs1: "hs_norm A \<le> hs_norm B + hs_norm (A - B)"
  proof -
    have "hs_norm A = hs_norm (B + (A - B))" using A_eq by simp
    also have "\<dots> \<le> hs_norm B + hs_norm (A - B)"
      by (rule hs_norm_triangle[OF B_c AB_c])
    finally show ?thesis .
  qed
  have B_eq: "B = A + (B - A)"
    using A_c B_c by (intro eq_matI) (auto simp: minus_mat_def)
  have lhs2: "hs_norm B \<le> hs_norm A + hs_norm (B - A)"
  proof -
    have "hs_norm B = hs_norm (A + (B - A))" using B_eq by simp
    also have "\<dots> \<le> hs_norm A + hs_norm (B - A)"
      by (rule hs_norm_triangle[OF A_c BA_c])
    finally show ?thesis .
  qed
  have BA_eq_AB: "hs_norm (B - A) = hs_norm (A - B)"
    using hs_norm_sub_swap[OF B_c A_c] .
  show ?thesis using lhs1 lhs2 BA_eq_AB by linarith
qed


section \<open>Carath\'eodory's theorem for conic combinations\<close>

text \<open>Carath\'eodory's theorem for cones: in a real vector space $V$ of dimension $d$, every
element of the conic hull of a set $S$ (a finite non-negative combination of elements of
$S$) is already a non-negative combination of at most $d$ elements of $S$.  We need it for
$V$ the real space of Hermitian $(mp)\times(mp)$ matrices, of real dimension $(mp)^2$, and
$S$ the product positive matrices $\sigma\otimes\tau$: it bounds the length of the
decompositions of elements of the separable cone uniformly, which is what makes the cone
closed (Separable\_Cone).  HOL-Analysis has Carath\'eodory for \<open>euclidean_space\<close>; using it
directly would require a Euclidean-space instance on the Hermitian matrices, so the theorem is
proved here directly for lists: any $d+1$ vectors are linearly dependent, and renormalising
the weights along a dependence relation removes one term while keeping all weights
non-negative.\<close>

text \<open>Below is a fold-based weighted sum of the cone-style list,
suitable for stating Carath\'eodory at the matrix level.\<close>

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

text \<open>\<open>cone_list_sum\<close> is additive over list-append.\<close>

lemma cone_list_sum_append:
  "cone_list_sum m p (xs @ ys)
     = cone_list_sum m p xs + cone_list_sum m p ys"
proof (induction xs)
  case Nil
  have ys_c: "cone_list_sum m p ys \<in> carrier_mat (m*p) (m*p)"
    by (rule cone_list_sum_carrier)
  have "cone_list_sum m p [] + cone_list_sum m p ys
          = 0\<^sub>m (m*p) (m*p) + cone_list_sum m p ys" by simp
  also have "\<dots> = cone_list_sum m p ys" using left_add_zero_mat[OF ys_c] .
  finally show ?case by simp
next
  case (Cons x xs)
  obtain w \<sigma> \<tau> where x_eq: "x = (w, \<sigma>, \<tau>)" by (cases x)
  let ?S = "complex_of_real w \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)"
  have xs_c: "cone_list_sum m p xs \<in> carrier_mat (m*p) (m*p)"
    by (rule cone_list_sum_carrier)
  have ys_c: "cone_list_sum m p ys \<in> carrier_mat (m*p) (m*p)"
    by (rule cone_list_sum_carrier)
  have IH: "cone_list_sum m p (xs @ ys)
            = cone_list_sum m p xs + cone_list_sum m p ys" using Cons.IH .
  have "cone_list_sum m p ((x # xs) @ ys)
          = ?S + cone_list_sum m p (xs @ ys)"
    using x_eq by simp
  also have "\<dots> = ?S + (cone_list_sum m p xs + cone_list_sum m p ys)"
    using IH by simp
  also have "\<dots> = (?S + cone_list_sum m p xs) + cone_list_sum m p ys"
    using xs_c ys_c by (intro eq_matI) auto
  also have "\<dots> = cone_list_sum m p (x # xs) + cone_list_sum m p ys"
    using x_eq by simp
  finally show ?case .
qed

text \<open>A zero-weight singleton over a properly-sized matrix pair
contributes the zero matrix.\<close>

lemma cone_list_sum_zero_singleton:
  assumes \<sigma>_c: "\<sigma> \<in> carrier_mat m m" and \<tau>_c: "\<tau> \<in> carrier_mat p p"
  shows "cone_list_sum m p [(0, \<sigma>, \<tau>)] = 0\<^sub>m (m*p) (m*p)"
proof -
  have st_c: "\<sigma> \<Otimes> \<tau> \<in> carrier_mat (m*p) (m*p)" using \<sigma>_c \<tau>_c by auto
  have st_dr: "dim_row (\<sigma> \<Otimes> \<tau>) = m*p"
    using st_c by (rule carrier_matD)
  have st_dc: "dim_col (\<sigma> \<Otimes> \<tau>) = m*p"
    using st_c by (rule carrier_matD)
  have zs: "complex_of_real 0 \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>) = 0\<^sub>m (m*p) (m*p)"
  proof (intro eq_matI)
    show "dim_row (complex_of_real 0 \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)) = dim_row (0\<^sub>m (m*p) (m*p))"
      using st_dr by simp
    show "dim_col (complex_of_real 0 \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)) = dim_col (0\<^sub>m (m*p) (m*p))"
      using st_dc by simp
  next
    fix i j
    assume "i < dim_row (0\<^sub>m (m*p) (m*p))" and "j < dim_col (0\<^sub>m (m*p) (m*p))"
    hence i_lt: "i < m*p" and j_lt: "j < m*p" by auto
    have e1: "(complex_of_real 0 \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)) $$ (i, j)
                 = complex_of_real 0 * (\<sigma> \<Otimes> \<tau>) $$ (i, j)"
      using st_dr st_dc i_lt j_lt by simp
    have e2: "complex_of_real 0 = (0 :: complex)" by simp
    show "(complex_of_real 0 \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)) $$ (i, j) = 0\<^sub>m (m*p) (m*p) $$ (i, j)"
      using e1 e2 i_lt j_lt by simp
  qed
  have "cone_list_sum m p [(0, \<sigma>, \<tau>)]
          = complex_of_real 0 \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>) + 0\<^sub>m (m*p) (m*p)" by simp
  also have "\<dots> = 0\<^sub>m (m*p) (m*p) + 0\<^sub>m (m*p) (m*p)" using zs by simp
  also have "\<dots> = 0\<^sub>m (m*p) (m*p)" by (intro eq_matI) auto
  finally show ?thesis .
qed

text \<open>Dropping a zero-weight entry from a cone list (with properly
typed matrix part) preserves the cone sum.\<close>

lemma cone_list_sum_drop_zero:
  assumes i_lt: "i < length xs"
      and zero_w: "fst (xs ! i) = 0"
      and typing: "\<forall>(w, \<sigma>, \<tau>) \<in> set xs.
                       \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
  shows "cone_list_sum m p (take i xs @ drop (Suc i) xs)
            = cone_list_sum m p xs"
proof -
  obtain w \<sigma> \<tau> where xi: "xs ! i = (w, \<sigma>, \<tau>)" by (cases "xs ! i") auto
  have w_zero: "w = 0" using zero_w xi by simp
  have xi_mem: "(w, \<sigma>, \<tau>) \<in> set xs"
    using xi i_lt nth_mem by metis
  have \<sigma>_c: "\<sigma> \<in> carrier_mat m m" and \<tau>_c: "\<tau> \<in> carrier_mat p p"
    using typing xi_mem by auto
  have decomp: "xs = take i xs @ [xs ! i] @ drop (Suc i) xs"
    using i_lt by (simp add: id_take_nth_drop)
  let ?L = "take i xs"
  let ?R = "drop (Suc i) xs"
  let ?M = "[xs ! i]"
  have L_c: "cone_list_sum m p ?L \<in> carrier_mat (m*p) (m*p)"
    by (rule cone_list_sum_carrier)
  have R_c: "cone_list_sum m p ?R \<in> carrier_mat (m*p) (m*p)"
    by (rule cone_list_sum_carrier)
  have Msum_zero: "cone_list_sum m p ?M = 0\<^sub>m (m*p) (m*p)"
    using cone_list_sum_zero_singleton[OF \<sigma>_c \<tau>_c] xi w_zero by simp
  have "cone_list_sum m p xs
          = cone_list_sum m p (?L @ ?M @ ?R)" using decomp by simp
  also have "\<dots> = cone_list_sum m p ?L + cone_list_sum m p (?M @ ?R)"
    by (rule cone_list_sum_append)
  also have "cone_list_sum m p (?M @ ?R)
              = cone_list_sum m p ?M + cone_list_sum m p ?R"
    by (rule cone_list_sum_append)
  also have "cone_list_sum m p ?M + cone_list_sum m p ?R
              = 0\<^sub>m (m*p) (m*p) + cone_list_sum m p ?R" using Msum_zero by simp
  also have "\<dots> = cone_list_sum m p ?R" using left_add_zero_mat[OF R_c] .
  finally have xs_eq:
    "cone_list_sum m p xs = cone_list_sum m p ?L + cone_list_sum m p ?R" .
  have "cone_list_sum m p (?L @ ?R)
          = cone_list_sum m p ?L + cone_list_sum m p ?R"
    by (rule cone_list_sum_append)
  thus ?thesis using xs_eq by simp
qed

text \<open>Linearity of \<open>cone_list_sum\<close> in the weight.  Two lists with
matching matrix parts but weights related by
\<open>w\<^sub>k = w\<^sub>k\<^sup>1 + \<mu> * r\<^sub>k\<close> satisfy the corresponding sum-equation.\<close>

lemma cone_list_sum_weight_split:
  fixes f g h :: "nat \<Rightarrow> real"
    and \<sigma>f \<tau>f :: "nat \<Rightarrow> complex Matrix.mat"
    and \<mu> :: real and L :: nat
  assumes typing: "\<And>k. k < L \<Longrightarrow>
                        \<sigma>f k \<in> carrier_mat m m \<and> \<tau>f k \<in> carrier_mat p p"
      and split: "\<And>k. k < L \<Longrightarrow> f k = g k + \<mu> * h k"
  shows "cone_list_sum m p (map (\<lambda>k. (f k, \<sigma>f k, \<tau>f k)) [0..<L])
       = cone_list_sum m p (map (\<lambda>k. (g k, \<sigma>f k, \<tau>f k)) [0..<L])
         + complex_of_real \<mu> \<cdot>\<^sub>m
             cone_list_sum m p (map (\<lambda>k. (h k, \<sigma>f k, \<tau>f k)) [0..<L])"
  using typing split
proof (induction L)
  case 0
  have rhs: "complex_of_real \<mu> \<cdot>\<^sub>m (0\<^sub>m (m*p) (m*p) :: complex Matrix.mat)
              = 0\<^sub>m (m*p) (m*p)"
    by (intro eq_matI) auto
  show ?case using rhs by simp
next
  case (Suc L)
  have typing_L: "\<And>k. k < L \<Longrightarrow>
                       \<sigma>f k \<in> carrier_mat m m \<and> \<tau>f k \<in> carrier_mat p p"
    using Suc.prems(1) by simp
  have split_L: "\<And>k. k < L \<Longrightarrow> f k = g k + \<mu> * h k"
    using Suc.prems(2) by simp
  have IH: "cone_list_sum m p (map (\<lambda>k. (f k, \<sigma>f k, \<tau>f k)) [0..<L])
            = cone_list_sum m p (map (\<lambda>k. (g k, \<sigma>f k, \<tau>f k)) [0..<L])
              + complex_of_real \<mu> \<cdot>\<^sub>m
                  cone_list_sum m p (map (\<lambda>k. (h k, \<sigma>f k, \<tau>f k)) [0..<L])"
    using Suc.IH[OF typing_L split_L] .
  have typingL: "\<sigma>f L \<in> carrier_mat m m \<and> \<tau>f L \<in> carrier_mat p p"
    using Suc.prems(1) by simp
  have splitL: "f L = g L + \<mu> * h L" using Suc.prems(2) by simp
  let ?TL = "\<sigma>f L \<Otimes> \<tau>f L"
  have TL_c: "?TL \<in> carrier_mat (m*p) (m*p)" using typingL by auto
  let ?F = "cone_list_sum m p (map (\<lambda>k. (f k, \<sigma>f k, \<tau>f k)) [0..<L])"
  let ?G = "cone_list_sum m p (map (\<lambda>k. (g k, \<sigma>f k, \<tau>f k)) [0..<L])"
  let ?H = "cone_list_sum m p (map (\<lambda>k. (h k, \<sigma>f k, \<tau>f k)) [0..<L])"
  have F_c: "?F \<in> carrier_mat (m*p) (m*p)" by (rule cone_list_sum_carrier)
  have G_c: "?G \<in> carrier_mat (m*p) (m*p)" by (rule cone_list_sum_carrier)
  have H_c: "?H \<in> carrier_mat (m*p) (m*p)" by (rule cone_list_sum_carrier)
  have list_split_f:
    "map (\<lambda>k. (f k, \<sigma>f k, \<tau>f k)) [0..<Suc L]
      = map (\<lambda>k. (f k, \<sigma>f k, \<tau>f k)) [0..<L] @ [(f L, \<sigma>f L, \<tau>f L)]"
    by simp
  have list_split_g:
    "map (\<lambda>k. (g k, \<sigma>f k, \<tau>f k)) [0..<Suc L]
      = map (\<lambda>k. (g k, \<sigma>f k, \<tau>f k)) [0..<L] @ [(g L, \<sigma>f L, \<tau>f L)]"
    by simp
  have list_split_h:
    "map (\<lambda>k. (h k, \<sigma>f k, \<tau>f k)) [0..<Suc L]
      = map (\<lambda>k. (h k, \<sigma>f k, \<tau>f k)) [0..<L] @ [(h L, \<sigma>f L, \<tau>f L)]"
    by simp
  let ?eFL = "complex_of_real (f L) \<cdot>\<^sub>m ?TL"
  let ?eGL = "complex_of_real (g L) \<cdot>\<^sub>m ?TL"
  let ?eHL = "complex_of_real (h L) \<cdot>\<^sub>m ?TL"
  have eFL_c: "?eFL \<in> carrier_mat (m*p) (m*p)" using TL_c by auto
  have eGL_c: "?eGL \<in> carrier_mat (m*p) (m*p)" using TL_c by auto
  have eHL_c: "?eHL \<in> carrier_mat (m*p) (m*p)" using TL_c by auto
  have single_f: "cone_list_sum m p [(f L, \<sigma>f L, \<tau>f L)] = ?eFL"
    using eFL_c by (intro eq_matI) auto
  have single_g: "cone_list_sum m p [(g L, \<sigma>f L, \<tau>f L)] = ?eGL"
    using eGL_c by (intro eq_matI) auto
  have single_h: "cone_list_sum m p [(h L, \<sigma>f L, \<tau>f L)] = ?eHL"
    using eHL_c by (intro eq_matI) auto
  have F_app: "cone_list_sum m p (map (\<lambda>k. (f k, \<sigma>f k, \<tau>f k)) [0..<Suc L])
                  = ?F + ?eFL"
    using list_split_f cone_list_sum_append single_f by simp
  have G_app: "cone_list_sum m p (map (\<lambda>k. (g k, \<sigma>f k, \<tau>f k)) [0..<Suc L])
                  = ?G + ?eGL"
    using list_split_g cone_list_sum_append single_g by simp
  have H_app: "cone_list_sum m p (map (\<lambda>k. (h k, \<sigma>f k, \<tau>f k)) [0..<Suc L])
                  = ?H + ?eHL"
    using list_split_h cone_list_sum_append single_h by simp
  have scale_eq: "?eFL = ?eGL + complex_of_real \<mu> \<cdot>\<^sub>m ?eHL"
    using splitL TL_c by (intro eq_matI) (auto simp: distrib_right)
  have mu_HL_c: "complex_of_real \<mu> \<cdot>\<^sub>m ?eHL \<in> carrier_mat (m*p) (m*p)"
    using eHL_c by auto
  have mu_H_c: "complex_of_real \<mu> \<cdot>\<^sub>m ?H \<in> carrier_mat (m*p) (m*p)"
    using H_c by auto
  have scale_dist:
    "complex_of_real \<mu> \<cdot>\<^sub>m (?H + ?eHL)
       = complex_of_real \<mu> \<cdot>\<^sub>m ?H + complex_of_real \<mu> \<cdot>\<^sub>m ?eHL"
    using H_c eHL_c by (rule add_smult_distrib_left_mat)
  have rearr: "(?G + complex_of_real \<mu> \<cdot>\<^sub>m ?H) + (?eGL + complex_of_real \<mu> \<cdot>\<^sub>m ?eHL)
                = (?G + ?eGL) + (complex_of_real \<mu> \<cdot>\<^sub>m ?H + complex_of_real \<mu> \<cdot>\<^sub>m ?eHL)"
    using G_c eGL_c mu_H_c mu_HL_c by (intro eq_matI) auto
  have "?F + ?eFL = (?G + complex_of_real \<mu> \<cdot>\<^sub>m ?H)
                      + (?eGL + complex_of_real \<mu> \<cdot>\<^sub>m ?eHL)"
    using IH scale_eq by simp
  also have "\<dots> = (?G + ?eGL)
                  + (complex_of_real \<mu> \<cdot>\<^sub>m ?H + complex_of_real \<mu> \<cdot>\<^sub>m ?eHL)"
    using rearr .
  also have "complex_of_real \<mu> \<cdot>\<^sub>m ?H + complex_of_real \<mu> \<cdot>\<^sub>m ?eHL
              = complex_of_real \<mu> \<cdot>\<^sub>m (?H + ?eHL)" using scale_dist by simp
  finally have "?F + ?eFL = (?G + ?eGL) + complex_of_real \<mu> \<cdot>\<^sub>m (?H + ?eHL)" .
  thus ?case using F_app G_app H_app by simp
qed

text \<open>Entry-wise expression for \<open>cone_list_sum\<close>: each entry is a
HOL sum over the list indices of weight times tensor entry.\<close>

lemma cone_list_sum_entry:
  fixes m p :: nat
      and ts :: "(real \<times> complex Matrix.mat \<times> complex Matrix.mat) list"
  assumes typing: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts.
                       \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
      and i_lt: "i < m * p" and j_lt: "j < m * p"
  shows "cone_list_sum m p ts $$ (i, j)
           = (\<Sum>k<length ts.
                complex_of_real (fst (ts!k))
                  * (fst (snd (ts!k)) \<Otimes> snd (snd (ts!k))) $$ (i, j))"
  using typing
proof (induction ts)
  case Nil
  show ?case using i_lt j_lt by (simp add: zero_mat_def)
next
  case (Cons t ts)
  obtain w \<sigma> \<tau> where t_eq: "t = (w, \<sigma>, \<tau>)" by (cases t)
  from Cons.prems t_eq have
    \<sigma>_c: "\<sigma> \<in> carrier_mat m m" and \<tau>_c: "\<tau> \<in> carrier_mat p p" by auto
  have ts_typing: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts.
                       \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
    using Cons.prems by simp
  have st_c: "\<sigma> \<Otimes> \<tau> \<in> carrier_mat (m*p) (m*p)" using \<sigma>_c \<tau>_c by auto
  have wstm_c: "complex_of_real w \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>) \<in> carrier_mat (m*p) (m*p)"
    using st_c by auto
  have rest_c: "cone_list_sum m p ts \<in> carrier_mat (m*p) (m*p)"
    by (rule cone_list_sum_carrier)
  have dim_st_r: "dim_row (\<sigma> \<Otimes> \<tau>) = m*p" using st_c by auto
  have dim_st_c: "dim_col (\<sigma> \<Otimes> \<tau>) = m*p" using st_c by auto
  have dim_rest_r: "dim_row (cone_list_sum m p ts) = m*p" using rest_c by auto
  have dim_rest_c: "dim_col (cone_list_sum m p ts) = m*p" using rest_c by auto
  have head_entry:
    "(complex_of_real w \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)) $$ (i, j)
       = complex_of_real w * (\<sigma> \<Otimes> \<tau>) $$ (i, j)"
    using index_smult_mat(1)[of i "\<sigma> \<Otimes> \<tau>" j "complex_of_real w"]
          i_lt j_lt dim_st_r dim_st_c by simp
  have add_entry:
    "(complex_of_real w \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>) + cone_list_sum m p ts) $$ (i, j)
       = (complex_of_real w \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)) $$ (i, j)
         + cone_list_sum m p ts $$ (i, j)"
    using index_add_mat(1)[of i "complex_of_real w \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)" j "cone_list_sum m p ts"]
          i_lt j_lt wstm_c rest_c by auto
  have IH: "cone_list_sum m p ts $$ (i, j)
              = (\<Sum>k<length ts.
                   complex_of_real (fst (ts!k))
                     * (fst (snd (ts!k)) \<Otimes> snd (snd (ts!k))) $$ (i, j))"
    using Cons.IH[OF ts_typing] .
  define gf where "gf =
     (\<lambda>xs k. complex_of_real (fst ((xs::(real \<times> complex Matrix.mat \<times> complex Matrix.mat) list)!k))
              * (fst (snd (xs!k)) \<Otimes> snd (snd (xs!k))) $$ (i, j))"
  have shift_unfold:
    "(\<Sum>k<length (t # ts). gf (t#ts) k)
       = gf (t#ts) 0 + (\<Sum>k<length ts. gf (t#ts) (Suc k))"
  proof -
    have len_eq: "length (t # ts) = Suc (length ts)" by simp
    have step: "(\<Sum>k<Suc (length ts). gf (t#ts) k)
                  = gf (t#ts) 0 + (\<Sum>k<length ts. gf (t#ts) (Suc k))"
      by (rule sum.lessThan_Suc_shift)
    show ?thesis using step unfolding len_eq .
  qed
  have suc_eq: "\<And>k. k < length ts \<Longrightarrow> gf (t#ts) (Suc k) = gf ts k"
    unfolding gf_def by simp
  have head_gf: "gf (t#ts) 0 = complex_of_real (fst t) * (fst (snd t) \<Otimes> snd (snd t)) $$ (i, j)"
    unfolding gf_def by simp
  have shift:
    "(\<Sum>k<length (t # ts).
         complex_of_real (fst ((t # ts)!k))
           * (fst (snd ((t # ts)!k))
              \<Otimes> snd (snd ((t # ts)!k))) $$ (i, j))
     = complex_of_real (fst t) * (fst (snd t) \<Otimes> snd (snd t)) $$ (i, j)
       + (\<Sum>k<length ts.
            complex_of_real (fst (ts!k))
              * (fst (snd (ts!k)) \<Otimes> snd (snd (ts!k))) $$ (i, j))"
  proof -
    have L_eq: "(\<Sum>k<length (t # ts).
                  complex_of_real (fst ((t # ts)!k))
                    * (fst (snd ((t # ts)!k))
                       \<Otimes> snd (snd ((t # ts)!k))) $$ (i, j))
                = (\<Sum>k<length (t # ts). gf (t#ts) k)"
      unfolding gf_def by simp
    have R_eq: "(\<Sum>k<length ts. gf (t#ts) (Suc k))
                = (\<Sum>k<length ts. gf ts k)"
      using suc_eq by (intro sum.cong) auto
    have R_eq2: "(\<Sum>k<length ts. gf ts k)
                  = (\<Sum>k<length ts.
                       complex_of_real (fst (ts!k))
                         * (fst (snd (ts!k))
                            \<Otimes> snd (snd (ts!k))) $$ (i, j))"
      unfolding gf_def by simp
    show ?thesis
      using L_eq shift_unfold head_gf R_eq R_eq2 by simp
  qed
  have lhs_split: "cone_list_sum m p (t # ts) $$ (i, j)
          = (complex_of_real w \<cdot>\<^sub>m (\<sigma> \<Otimes> \<tau>)) $$ (i, j)
              + cone_list_sum m p ts $$ (i, j)"
    using t_eq add_entry by simp
  have step1: "cone_list_sum m p (t # ts) $$ (i, j)
                = complex_of_real w * (\<sigma> \<Otimes> \<tau>) $$ (i, j)
                  + (\<Sum>k<length ts.
                       complex_of_real (fst (ts!k))
                         * (fst (snd (ts!k)) \<Otimes> snd (snd (ts!k))) $$ (i, j))"
    using lhs_split head_entry IH by simp
  have t_proj: "fst t = w" "fst (snd t) = \<sigma>" "snd (snd t) = \<tau>"
    using t_eq by auto
  show ?case using step1 shift t_proj by simp
qed

text \<open>An entry-wise zero criterion: if every entry is 0, the matrix is \<open>0\<^sub>m\<close>.\<close>

lemma matrix_eq_zero_via_entries:
  fixes M :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat (m*p) (m*p)"
      and zero: "\<And>i j. i < m*p \<Longrightarrow> j < m*p \<Longrightarrow> M $$ (i, j) = 0"
  shows "M = 0\<^sub>m (m*p) (m*p)"
proof (intro eq_matI)
  show "dim_row M = dim_row (0\<^sub>m (m*p) (m*p))" using M_c by simp
  show "dim_col M = dim_col (0\<^sub>m (m*p) (m*p))" using M_c by simp
next
  fix i j assume "i < dim_row (0\<^sub>m (m*p) (m*p))"
             and "j < dim_col (0\<^sub>m (m*p) (m*p))"
  hence i_lt: "i < m*p" and j_lt: "j < m*p" by auto
  show "M $$ (i, j) = 0\<^sub>m (m*p) (m*p) $$ (i, j)"
    using zero[OF i_lt j_lt] i_lt j_lt by simp
qed


text \<open>Top-level linear-algebra core.  A list of more than \<open>2 (m p)\<^sup>2\<close>
complex \<open>(m p) \<times> (m p)\<close> matrix pairs admits a non-trivial real
linear combination of their tensor products that vanishes.

The proof is the standard JNF \<open>vec_space TYPE(real) (2 (m p)\<^sup>2)\<close>
\<open>li_le_dim\<close> contrapositive applied to a real-flatten of the tensor
products.  Admitted here as a single named lemma so it can be
discharged independently of the cone Carath\'eodory reduction
machinery (which is fully proved below modulo this one lemma).\<close>

lemma cone_list_real_lin_dep:
  fixes m p :: nat
      and pairs :: "(complex Matrix.mat \<times> complex Matrix.mat) list"
  assumes m_pos: "0 < m" and p_pos: "0 < p"
      and typing: "\<forall>(\<sigma>, \<tau>) \<in> set pairs.
                       \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
      and long: "length pairs > 2 * (m*p)\<^sup>2"
  shows "\<exists>r :: nat \<Rightarrow> real.
            (\<exists>k < length pairs. r k \<noteq> 0) \<and>
            (\<forall>k \<ge> length pairs. r k = 0) \<and>
            cone_list_sum m p
              (map (\<lambda>k. (r k, fst (pairs ! k), snd (pairs ! k)))
                   [0..<length pairs])
             = 0\<^sub>m (m*p) (m*p)"
proof -
  define n where "n = m * p"
  define N where "N = n * n"
  define D where "D = 2 * N"
  define L where "L = length pairs"
  have n_pos: "0 < n" using m_pos p_pos n_def by simp
  have N_pos: "0 < N" using n_pos N_def by simp
  have D_pos: "0 < D" using N_pos D_def by simp
  have L_gt_D: "L > D"
    using long unfolding L_def D_def N_def n_def power2_eq_square by simp
  have L_pos: "0 < L" using L_gt_D D_pos by linarith

  define T :: "complex Matrix.mat list" where
    "T = map (\<lambda>p. fst p \<Otimes> snd p) pairs"
  have T_len: "length T = L" unfolding T_def L_def by simp

  have T_idx_c: "\<And>k. k < L \<Longrightarrow> T ! k \<in> carrier_mat n n"
  proof -
    fix k assume k_lt: "k < L"
    obtain \<sigma> \<tau> where p_eq: "pairs ! k = (\<sigma>, \<tau>)" by (cases "pairs ! k")
    have mem_p: "pairs ! k \<in> set pairs"
      using k_lt unfolding L_def by (simp add: nth_mem)
    hence "(\<sigma>, \<tau>) \<in> set pairs" using p_eq by simp
    hence \<sigma>_c: "\<sigma> \<in> carrier_mat m m" and \<tau>_c: "\<tau> \<in> carrier_mat p p"
      using typing by auto
    have T_k: "T ! k = \<sigma> \<Otimes> \<tau>"
      using p_eq k_lt T_len unfolding T_def L_def by simp
    show "T ! k \<in> carrier_mat n n"
      using T_k \<sigma>_c \<tau>_c unfolding n_def by auto
  qed

  define A :: "real Matrix.mat" where
    "A = Matrix.mat D L (\<lambda>(k, j).
            if k < N then Re ((T!j) $$ (k div n, k mod n))
                     else Im ((T!j) $$ ((k-N) div n, (k-N) mod n)))"
  have A_c: "A \<in> carrier_mat D L" unfolding A_def by simp
  have A_dim_r: "dim_row A = D" using A_c by simp
  have A_dim_c: "dim_col A = L" using A_c by simp

  have row_lt_N: "\<And>k. k < N \<Longrightarrow> k div n < n \<and> k mod n < n"
    using n_pos N_def by (simp add: less_mult_imp_div_less)
  have row_lt_2N: "\<And>k. k < D \<Longrightarrow> \<not> k < N \<Longrightarrow>
                      (k-N) div n < n \<and> (k-N) mod n < n"
  proof -
    fix k assume k_lt: "k < D" and k_ge_N: "\<not> k < N"
    have "k - N < D - N" using k_lt k_ge_N by linarith
    also have "D - N = N" unfolding D_def by simp
    finally have kN: "k - N < N" .
    thus "(k-N) div n < n \<and> (k-N) mod n < n"
      using n_pos N_def by (simp add: less_mult_imp_div_less)
  qed

  have A_entry_Re:
    "\<And>k j. k < N \<Longrightarrow> j < L \<Longrightarrow>
        A $$ (k, j) = Re ((T!j) $$ (k div n, k mod n))"
    unfolding A_def using D_pos N_def D_def by (simp add: less_le_trans)
  have A_entry_Im:
    "\<And>k j. k < D \<Longrightarrow> \<not> k < N \<Longrightarrow> j < L \<Longrightarrow>
        A $$ (k, j) = Im ((T!j) $$ ((k-N) div n, (k-N) mod n))"
    unfolding A_def by simp

  have cols_set_c: "set (cols A) \<subseteq> carrier_vec D"
  proof
    fix x assume "x \<in> set (cols A)"
    then obtain k where k_lt: "k < length (cols A)" and x_eq: "x = cols A ! k"
      by (auto simp: in_set_conv_nth)
    have k_L: "k < L" using k_lt A_c by (simp add: cols_length)
    have "cols A ! k = Matrix.col A k"
      using k_lt A_c by (simp add: cols_nth cols_length)
    hence "x = Matrix.col A k" using x_eq by simp
    moreover have "Matrix.col A k \<in> carrier_vec D"
      using A_c k_L by auto
    ultimately show "x \<in> carrier_vec D" by simp
  qed
  have cols_len: "length (cols A) = L"
    using A_c by (simp add: cols_length)

  have unit_mult_col:
    "\<And>i. i < L \<Longrightarrow> A *\<^sub>v unit_vec L i = Matrix.col A i"
  proof -
    fix i assume i_L: "i < L"
    show "A *\<^sub>v unit_vec L i = Matrix.col A i"
    proof (rule eq_vecI)
      show "dim_vec (A *\<^sub>v unit_vec L i) = dim_vec (Matrix.col A i)"
        using A_c by auto
    next
      fix k assume k_lt: "k < dim_vec (Matrix.col A i)"
      hence k_D: "k < D" using A_c by auto
      have "(A *\<^sub>v unit_vec L i) $ k = Matrix.row A k \<bullet> unit_vec L i"
        using A_c k_D by (simp add: index_mult_mat_vec)
      also have "... = (\<Sum>j = 0..<L. Matrix.row A k $ j * unit_vec L i $ j)"
        unfolding scalar_prod_def by simp
      also have "... = (\<Sum>j = 0..<L.
                          Matrix.row A k $ j * (if j = i then 1 else 0))"
        using i_L by (intro sum.cong refl) (auto simp: index_unit_vec)
      also have "... = Matrix.row A k $ i"
        using i_L by (simp add: sum.delta if_distrib mult.commute
                              cong: if_cong)
      also have "Matrix.row A k $ i = A $$ (k, i)"
        using A_c k_D i_L by (simp add: index_row(1))
      finally have lhs: "(A *\<^sub>v unit_vec L i) $ k = A $$ (k, i)" .
      have rhs: "Matrix.col A i $ k = A $$ (k, i)"
        using A_c k_D i_L by (simp add: index_col)
      show "(A *\<^sub>v unit_vec L i) $ k = Matrix.col A i $ k"
        using lhs rhs by simp
    qed
  qed

  have ex_v: "\<exists>v :: real Matrix.vec.
                v \<in> carrier_vec L \<and> v \<noteq> 0\<^sub>v L \<and> A *\<^sub>v v = 0\<^sub>v D"
  proof (cases "distinct (cols A)")
    case True
    have cols_card: "card (set (cols A)) = L"
      using True cols_len by (simp add: distinct_card)
    interpret VS: vec_space "TYPE(real)" D .
    have not_li: "\<not> VS.lin_indpt (set (cols A))"
    proof
      assume li: "VS.lin_indpt (set (cols A))"
      have "card (set (cols A)) \<le> VS.dim"
        using VS.li_le_dim(2)[OF VS.fin_dim cols_set_c li] .
      hence card_le: "card (set (cols A)) \<le> D"
        using VS.dim_is_n by simp
      thus False using cols_card L_gt_D by linarith
    qed
    hence lin_dep_cols: "VS.lin_dep (set (cols A))" by simp
    show ?thesis
      using VS.lin_depE[OF A_c lin_dep_cols True] by blast
  next
    case False
    obtain i j where i_lt: "i < L" and j_lt: "j < L"
                 and i_neq_j: "i \<noteq> j"
                 and ij_eq: "cols A ! i = cols A ! j"
      using False cols_len by (metis distinct_conv_nth)
    define vv :: "real Matrix.vec" where
      "vv = unit_vec L i - unit_vec L j"
    have uvi_c: "unit_vec L i \<in> carrier_vec L" by simp
    have uvj_c: "unit_vec L j \<in> carrier_vec L" by simp
    have vv_c: "vv \<in> carrier_vec L"
      unfolding vv_def using uvi_c uvj_c by auto
    have vv_i: "vv $ i = (1 :: real)"
    proof -
      have ui_i: "(unit_vec L i :: real Matrix.vec) $ i = 1"
        using i_lt by (simp add: index_unit_vec)
      have uj_i: "(unit_vec L j :: real Matrix.vec) $ i = 0"
      proof -
        have "(unit_vec L j :: real Matrix.vec) $ i = (if i = j then 1 else 0)"
          using i_lt j_lt index_unit_vec(1)[of j L i] by simp
        thus ?thesis using i_neq_j by simp
      qed
      have "vv $ i = (unit_vec L i :: real Matrix.vec) $ i
                    - (unit_vec L j :: real Matrix.vec) $ i"
        unfolding vv_def using i_lt by (simp add: index_minus_vec)
      also have "... = 1 - 0" using ui_i uj_i by simp
      also have "... = (1 :: real)" by simp
      finally show "vv $ i = (1 :: real)" .
    qed
    have vv_nz: "vv \<noteq> 0\<^sub>v L"
    proof
      assume "vv = 0\<^sub>v L"
      hence "vv $ i = 0\<^sub>v L $ i" by simp
      hence "(1::real) = 0" using vv_i i_lt by simp
      thus False by simp
    qed
    have col_i: "Matrix.col A i = cols A ! i"
      using i_lt cols_len cols_nth A_c by simp
    have col_j: "Matrix.col A j = cols A ! j"
      using j_lt cols_len cols_nth A_c by simp
    have col_eq: "Matrix.col A i = Matrix.col A j"
      using col_i col_j ij_eq by simp
    have col_i_c: "Matrix.col A i \<in> carrier_vec D"
      using A_c i_lt by auto
    have "A *\<^sub>v vv = A *\<^sub>v (unit_vec L i - unit_vec L j)"
      unfolding vv_def by simp
    also have "... = A *\<^sub>v unit_vec L i - A *\<^sub>v unit_vec L j"
      using mult_minus_distrib_mat_vec[OF A_c uvi_c uvj_c] .
    also have "... = Matrix.col A i - Matrix.col A j"
      using unit_mult_col[OF i_lt] unit_mult_col[OF j_lt] by simp
    also have "... = 0\<^sub>v D"
      using col_eq col_i_c by simp
    finally have Avv: "A *\<^sub>v vv = 0\<^sub>v D" .
    show ?thesis using vv_c vv_nz Avv by blast
  qed

  obtain v :: "real Matrix.vec" where
    v_c: "v \<in> carrier_vec L"
    and v_nz: "v \<noteq> 0\<^sub>v L"
    and Av_eq: "A *\<^sub>v v = 0\<^sub>v D"
    using ex_v by blast

  define r :: "nat \<Rightarrow> real" where
    "r = (\<lambda>k. if k < L then v $ k else 0)"

  have r_witness: "\<exists>k < L. r k \<noteq> 0"
  proof (rule ccontr)
    assume neg: "\<not> (\<exists>k < L. r k \<noteq> 0)"
    hence all_zero: "\<forall>k < L. r k = 0" by auto
    have all_v_zero: "\<And>i. i < L \<Longrightarrow> v $ i = 0"
      using all_zero unfolding r_def by auto
    have v_eq: "v = 0\<^sub>v L"
    proof (rule eq_vecI)
      show "dim_vec v = dim_vec (0\<^sub>v L)" using v_c by simp
      fix i assume i_lt: "i < dim_vec (0\<^sub>v L)"
      hence "i < L" by simp
      thus "v $ i = 0\<^sub>v L $ i" using all_v_zero by simp
    qed
    show False using v_eq v_nz by simp
  qed

  have r_zero_high: "\<forall>k \<ge> L. r k = 0"
    unfolding r_def by auto

  define ts where
    "ts = map (\<lambda>k. (r k, fst (pairs ! k), snd (pairs ! k))) [0..<L]"
  have ts_len: "length ts = L" unfolding ts_def by simp

  have ts_typing: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts.
                     \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
  proof safe
    fix w \<sigma> \<tau> assume mem: "(w, \<sigma>, \<tau>) \<in> set ts"
    then obtain k where k_lt: "k < L" and ts_k: "ts ! k = (w, \<sigma>, \<tau>)"
      unfolding ts_def L_def by (auto simp: in_set_conv_nth)
    obtain pa pb where pairs_k: "pairs ! k = (pa, pb)" by (cases "pairs ! k")
    have eq: "ts ! k = (r k, pa, pb)"
      using k_lt pairs_k unfolding ts_def L_def by simp
    hence w_eq: "w = r k" and \<sigma>eq: "\<sigma> = pa" and \<tau>eq: "\<tau> = pb"
      using ts_k by auto
    have "pairs ! k \<in> set pairs"
      using k_lt unfolding L_def by (simp add: nth_mem)
    hence pa_c: "pa \<in> carrier_mat m m" and pb_c: "pb \<in> carrier_mat p p"
      using typing pairs_k by auto
    show "\<sigma> \<in> carrier_mat m m" using pa_c \<sigma>eq by simp
    show "\<tau> \<in> carrier_mat p p" using pb_c \<tau>eq by simp
  qed

  have ts_nth: "\<And>k. k < L \<Longrightarrow>
        fst (ts ! k) = r k \<and>
        fst (snd (ts ! k)) = fst (pairs ! k) \<and>
        snd (snd (ts ! k)) = snd (pairs ! k)"
    unfolding ts_def L_def by auto

  have T_nth_pairs: "\<And>k. k < L \<Longrightarrow> T ! k = fst (pairs ! k) \<Otimes> snd (pairs ! k)"
    unfolding T_def L_def by simp

  have idx_lt_N: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i * n + j < N"
  proof -
    fix i j assume i_n: "i < n" and j_n: "j < n"
    have step1: "i * n + j < i * n + n" using j_n by simp
    have step2: "i * n + n = Suc i * n" by simp
    have step3: "Suc i * n \<le> n * n"
      using i_n by (intro mult_right_mono) auto
    have "i * n + j < n * n" using step1 step2 step3 by linarith
    thus "i * n + j < N" unfolding N_def .
  qed

  have idx_div_mod: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
                       (i * n + j) div n = i \<and> (i * n + j) mod n = j"
    by auto

  define rowAv where
    "rowAv = (\<lambda>idx::nat. (\<Sum>k<L. A $$ (idx, k) * v $ k))"

  have rowAv_eq: "\<And>idx. idx < D \<Longrightarrow> (A *\<^sub>v v) $ idx = rowAv idx"
  proof -
    fix idx assume idx_D: "idx < D"
    have "(A *\<^sub>v v) $ idx = Matrix.row A idx \<bullet> v"
      using A_c idx_D index_mult_mat_vec by auto
    also have "... = (\<Sum>k = 0..<dim_vec v. Matrix.row A idx $ k * v $ k)"
      unfolding scalar_prod_def by simp
    also have "... = (\<Sum>k<L. Matrix.row A idx $ k * v $ k)"
      using v_c by (simp add: atLeast0LessThan)
    also have "... = (\<Sum>k<L. A $$ (idx, k) * v $ k)"
      using A_c idx_D by (intro sum.cong refl) (auto simp: index_row(1))
    finally show "(A *\<^sub>v v) $ idx = rowAv idx" unfolding rowAv_def .
  qed

  have rowAv_zero: "\<And>idx. idx < D \<Longrightarrow> rowAv idx = 0"
  proof -
    fix idx assume idx_D: "idx < D"
    have "rowAv idx = (A *\<^sub>v v) $ idx" using rowAv_eq idx_D by simp
    also have "... = (0\<^sub>v D) $ idx" using Av_eq by simp
    also have "... = 0" using idx_D by simp
    finally show "rowAv idx = 0" .
  qed

  have AvRe: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
              (\<Sum>k<L. v $ k * Re ((T!k) $$ (i, j))) = 0"
  proof -
    fix i j assume i_n: "i < n" and j_n: "j < n"
    define idx where "idx = i * n + j"
    have idx_N: "idx < N" using idx_lt_N[OF i_n j_n] idx_def by simp
    have idx_D: "idx < D" using idx_N D_def by simp
    have div_eq: "idx div n = i" and mod_eq: "idx mod n = j"
      using idx_div_mod[OF i_n j_n] idx_def by auto
    have rowAv_unfold:
      "rowAv idx = (\<Sum>k<L. v $ k * Re ((T!k) $$ (i, j)))"
    proof -
      have "rowAv idx = (\<Sum>k<L. A $$ (idx, k) * v $ k)"
        unfolding rowAv_def by simp
      also have "... = (\<Sum>k<L. Re ((T!k) $$ (i, j)) * v $ k)"
        using A_entry_Re[OF idx_N] div_eq mod_eq
        by (intro sum.cong refl) auto
      also have "... = (\<Sum>k<L. v $ k * Re ((T!k) $$ (i, j)))"
        by (simp add: mult.commute)
      finally show ?thesis .
    qed
    show "(\<Sum>k<L. v $ k * Re ((T!k) $$ (i, j))) = 0"
      using rowAv_zero[OF idx_D] rowAv_unfold by simp
  qed

  have AvIm: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
              (\<Sum>k<L. v $ k * Im ((T!k) $$ (i, j))) = 0"
  proof -
    fix i j assume i_n: "i < n" and j_n: "j < n"
    define idx where "idx = N + i * n + j"
    have idx_ge_N: "\<not> idx < N" unfolding idx_def by simp
    have idx_D: "idx < D"
      using idx_lt_N[OF i_n j_n] idx_def D_def by simp
    have idx_sub: "idx - N = i * n + j" unfolding idx_def by simp
    have div_eq: "(idx - N) div n = i" and mod_eq: "(idx - N) mod n = j"
      using idx_div_mod[OF i_n j_n] idx_sub by auto
    have rowAv_unfold:
      "rowAv idx = (\<Sum>k<L. v $ k * Im ((T!k) $$ (i, j)))"
    proof -
      have "rowAv idx = (\<Sum>k<L. A $$ (idx, k) * v $ k)"
        unfolding rowAv_def by simp
      also have "... = (\<Sum>k<L. Im ((T!k) $$ (i, j)) * v $ k)"
        using A_entry_Im[OF idx_D idx_ge_N] div_eq mod_eq
        by (intro sum.cong refl) auto
      also have "... = (\<Sum>k<L. v $ k * Im ((T!k) $$ (i, j)))"
        by (simp add: mult.commute)
      finally show ?thesis .
    qed
    show "(\<Sum>k<L. v $ k * Im ((T!k) $$ (i, j))) = 0"
      using rowAv_zero[OF idx_D] rowAv_unfold by simp
  qed

  have cls_zero: "cone_list_sum m p ts = 0\<^sub>m (m*p) (m*p)"
  proof (rule matrix_eq_zero_via_entries[where m=m and p=p])
    show "cone_list_sum m p ts \<in> carrier_mat (m*p) (m*p)"
      by (rule cone_list_sum_carrier)
  next
    fix i j assume i_mp: "i < m*p" and j_mp: "j < m*p"
    have i_n: "i < n" and j_n: "j < n" using i_mp j_mp n_def by auto

    have entry_ts: "cone_list_sum m p ts $$ (i, j)
                  = (\<Sum>k<length ts. complex_of_real (fst (ts!k))
                       * (fst (snd (ts!k)) \<Otimes> snd (snd (ts!k))) $$ (i, j))"
      using cone_list_sum_entry[OF ts_typing i_mp j_mp] .

    have ts_subst: "\<And>k. k < L \<Longrightarrow>
        complex_of_real (fst (ts!k))
          * (fst (snd (ts!k)) \<Otimes> snd (snd (ts!k))) $$ (i, j)
          = complex_of_real (v $ k) * (T!k) $$ (i, j)"
    proof -
      fix k assume k_lt: "k < L"
      have a: "fst (ts ! k) = r k"
        and b: "fst (snd (ts ! k)) = fst (pairs ! k)"
        and c: "snd (snd (ts ! k)) = snd (pairs ! k)"
        using ts_nth[OF k_lt] by auto
      have rk: "r k = v $ k" unfolding r_def using k_lt by simp
      have T_k: "T ! k = fst (pairs ! k) \<Otimes> snd (pairs ! k)"
        using T_nth_pairs[OF k_lt] .
      show "complex_of_real (fst (ts!k))
              * (fst (snd (ts!k)) \<Otimes> snd (snd (ts!k))) $$ (i, j)
              = complex_of_real (v $ k) * (T!k) $$ (i, j)"
        using a b c rk T_k by simp
    qed

    have entry_v: "cone_list_sum m p ts $$ (i, j)
                    = (\<Sum>k<L. complex_of_real (v $ k) * (T!k) $$ (i, j))"
    proof -
      have "cone_list_sum m p ts $$ (i, j)
              = (\<Sum>k<L. complex_of_real (fst (ts!k))
                  * (fst (snd (ts!k)) \<Otimes> snd (snd (ts!k))) $$ (i, j))"
        using entry_ts ts_len by simp
      also have "... = (\<Sum>k<L. complex_of_real (v $ k) * (T!k) $$ (i, j))"
        using ts_subst by (intro sum.cong refl) auto
      finally show ?thesis .
    qed

    have decomp: "\<And>k. k < L \<Longrightarrow>
        complex_of_real (v $ k) * (T!k) $$ (i, j)
          = Complex (v $ k * Re ((T!k) $$ (i, j)))
                     (v $ k * Im ((T!k) $$ (i, j)))"
      by (simp add: complex_eq_iff)

    have sum_to_complex:
      "(\<Sum>k<L. complex_of_real (v $ k) * (T!k) $$ (i, j))
        = Complex (\<Sum>k<L. v $ k * Re ((T!k) $$ (i, j)))
                   (\<Sum>k<L. v $ k * Im ((T!k) $$ (i, j)))"
    proof -
      have "(\<Sum>k<L. complex_of_real (v $ k) * (T!k) $$ (i, j))
              = (\<Sum>k<L. Complex (v $ k * Re ((T!k) $$ (i, j)))
                                  (v $ k * Im ((T!k) $$ (i, j))))"
        using decomp by (intro sum.cong refl) auto
      also have "... = Complex (\<Sum>k<L. v $ k * Re ((T!k) $$ (i, j)))
                                (\<Sum>k<L. v $ k * Im ((T!k) $$ (i, j)))"
        by (induction L) (auto simp: complex_eq_iff)
      finally show ?thesis .
    qed

    have Re_zero: "(\<Sum>k<L. v $ k * Re ((T!k) $$ (i, j))) = 0"
      using AvRe[OF i_n j_n] .
    have Im_zero: "(\<Sum>k<L. v $ k * Im ((T!k) $$ (i, j))) = 0"
      using AvIm[OF i_n j_n] .

    have "cone_list_sum m p ts $$ (i, j)
            = Complex 0 0"
      using entry_v sum_to_complex Re_zero Im_zero by simp
    thus "cone_list_sum m p ts $$ (i, j) = 0"
      by (simp add: complex_eq_iff)
  qed

  show ?thesis
  proof (rule exI[where x = r])
    have "(\<exists>k < length pairs. r k \<noteq> 0)
            \<and> (\<forall>k \<ge> length pairs. r k = 0)
            \<and> cone_list_sum m p
                (map (\<lambda>k. (r k, fst (pairs ! k), snd (pairs ! k)))
                     [0..<length pairs])
               = 0\<^sub>m (m*p) (m*p)"
      using r_witness r_zero_high cls_zero
      unfolding L_def[symmetric] ts_def[symmetric]
      by blast
    thus "(\<exists>k < length pairs. r k \<noteq> 0)
            \<and> (\<forall>k \<ge> length pairs. r k = 0)
            \<and> cone_list_sum m p
                (map (\<lambda>k. (r k, fst (pairs ! k), snd (pairs ! k)))
                     [0..<length pairs])
               = 0\<^sub>m (m*p) (m*p)" .
  qed
qed


text \<open>One reduction step: a length-\<open>L\<close> cone list with
\<open>L > (m p)\<^sup>2 + 1\<close> admits a length-\<open>(L-1)\<close> list with the same cone
sum, weights non-negative, and matrix pairs inherited from the
original list.

NOTE on the conclusion: the standard Carath\'eodory reduction
\<^emph>\<open>reweights\<close> rather than \<^emph>\<open>selects\<close>, so we require only that the
\<^emph>\<open>matrix pair\<close> \<open>(\<sigma>, \<tau>)\<close> of each new entry occurs in the original
list — the weight may differ.  This is what the downstream
closedness argument actually needs (typing + non-negativity
inherited from the original cone).\<close>

lemma caratheodory_matrix_cone_step:
  fixes m p :: nat
      and ts :: "(real \<times> complex Matrix.mat \<times> complex Matrix.mat) list"
  assumes m_pos: "0 < m" and p_pos: "0 < p"
      and ts_typing: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts.
                          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
      and ts_nn: "\<forall>(w, _, _) \<in> set ts. 0 \<le> w"
      and ts_long: "length ts > 2 * (m*p)\<^sup>2 + 1"
  shows "\<exists>ts'. length ts' = length ts - 1
              \<and> (\<forall>(w, \<sigma>, \<tau>) \<in> set ts'.
                    \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
                    \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts))
              \<and> cone_list_sum m p ts = cone_list_sum m p ts'"
proof -
  define K where "K = (m * p)\<^sup>2"
  define L where "L = length ts"
  have K_pos: "0 < K" unfolding K_def using m_pos p_pos by simp
  have L_gt: "L > K + 1" unfolding L_def K_def using ts_long by simp
  have L_pos: "0 < L" using L_gt by linarith

  have typing_idx:
    "\<And>k. k < L \<Longrightarrow>
        fst (snd (ts ! k)) \<in> carrier_mat m m \<and>
        snd (snd (ts ! k)) \<in> carrier_mat p p"
  proof -
    fix k assume "k < L"
    hence mem: "ts ! k \<in> set ts" unfolding L_def by (simp add: nth_mem)
    show "fst (snd (ts ! k)) \<in> carrier_mat m m \<and>
          snd (snd (ts ! k)) \<in> carrier_mat p p"
      using ts_typing mem by (cases "ts ! k") auto
  qed

  have w_nn_idx: "\<And>k. k < L \<Longrightarrow> 0 \<le> fst (ts ! k)"
  proof -
    fix k assume "k < L"
    hence mem: "ts ! k \<in> set ts" unfolding L_def by (simp add: nth_mem)
    show "0 \<le> fst (ts ! k)" using ts_nn mem by (cases "ts ! k") auto
  qed

  text \<open>The linear-algebra core: invoke \<open>cone_list_real_lin_dep\<close> on
        the pair-list extracted from \<open>ts\<close>, then sign-correct so that
        at least one coefficient is strictly positive.\<close>

  define pairs :: "(complex Matrix.mat \<times> complex Matrix.mat) list"
    where "pairs = map (\<lambda>k. (fst (snd (ts ! k)), snd (snd (ts ! k))))
                       [0..<L]"
  have pairs_length: "length pairs = L" unfolding pairs_def by simp
  have pairs_typing: "\<forall>(\<sigma>, \<tau>) \<in> set pairs.
                          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
  proof clarify
    fix \<sigma> \<tau> assume "(\<sigma>, \<tau>) \<in> set pairs"
    then obtain k where kL: "k < L"
      and pair_eq: "(\<sigma>, \<tau>) = (fst (snd (ts ! k)), snd (snd (ts ! k)))"
      unfolding pairs_def by auto
    have s_eq: "\<sigma> = fst (snd (ts ! k))"
      using pair_eq by (metis fst_conv)
    have t_eq: "\<tau> = snd (snd (ts ! k))"
      using pair_eq by (metis snd_conv)
    show "\<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
      using typing_idx[OF kL] s_eq t_eq by simp
  qed
  have pairs_long: "length pairs > 2 * (m*p)\<^sup>2"
    unfolding pairs_length L_def using ts_long by simp

  from cone_list_real_lin_dep[OF m_pos p_pos pairs_typing pairs_long]
  obtain c :: "nat \<Rightarrow> real"
    where c_nontriv: "\<exists>k<length pairs. c k \<noteq> 0"
      and c_outside: "\<forall>k\<ge>length pairs. c k = 0"
      and c_sum: "cone_list_sum m p
                    (map (\<lambda>k. (c k, fst (pairs ! k), snd (pairs ! k)))
                         [0..<length pairs])
                  = 0\<^sub>m (m*p) (m*p)"
    by blast
  have c_nontriv_L: "\<exists>k<L. c k \<noteq> 0" using c_nontriv pairs_length by simp
  have c_outside_L: "\<forall>k\<ge>L. c k = 0" using c_outside pairs_length by simp

  text \<open>Rewrite \<open>c_sum\<close> with \<open>pairs ! k\<close> unfolded.\<close>
  have pairs_nth: "\<And>k. k < L \<Longrightarrow>
                       pairs ! k = (fst (snd (ts ! k)), snd (snd (ts ! k)))"
    unfolding pairs_def by simp
  have c_sum_ts: "cone_list_sum m p
                    (map (\<lambda>k. (c k, fst (snd (ts ! k)),
                                    snd (snd (ts ! k))))
                         [0..<L])
                  = 0\<^sub>m (m*p) (m*p)"
  proof -
    have list_eq:
      "map (\<lambda>k. (c k, fst (pairs ! k), snd (pairs ! k)))
           [0..<length pairs]
       = map (\<lambda>k. (c k, fst (snd (ts ! k)), snd (snd (ts ! k)))) [0..<L]"
    proof -
      have step:
        "\<And>k. k \<in> set [0..<L]
            \<Longrightarrow> (c k, fst (pairs ! k), snd (pairs ! k))
                = (c k, fst (snd (ts ! k)), snd (snd (ts ! k)))"
        using pairs_nth by auto
      have len_eq: "[0..<length pairs] = [0..<L]" using pairs_length by simp
      show ?thesis using len_eq step by (auto cong: map_cong)
    qed
    show ?thesis using c_sum list_eq by simp
  qed

  text \<open>Sign-correct so the witness coefficient is strictly positive.\<close>
  have real_relation_exists:
    "\<exists>r :: nat \<Rightarrow> real.
        (\<exists>k<L. 0 < r k) \<and>
        (\<forall>k\<ge>L. r k = 0) \<and>
        cone_list_sum m p
          (map (\<lambda>k. (r k, fst (snd (ts ! k)), snd (snd (ts ! k))))
               [0..<L])
           = 0\<^sub>m (m*p) (m*p)"
  proof (cases "\<exists>k<L. 0 < c k")
    case True
    show ?thesis
      using True c_outside_L c_sum_ts by blast
  next
    case False
    obtain k0 where k0_L: "k0 < L" and k0_nz: "c k0 \<noteq> 0"
      using c_nontriv_L by blast
    have all_nonpos: "\<And>k. k < L \<Longrightarrow> c k \<le> 0" using False by force
    have k0_neg: "c k0 < 0" using all_nonpos[OF k0_L] k0_nz by linarith
    define rN :: "nat \<Rightarrow> real" where "rN k = - c k" for k
    have rN_pos: "0 < rN k0" using k0_neg unfolding rN_def by simp
    have rN_outside: "\<forall>k\<ge>L. rN k = 0"
      unfolding rN_def using c_outside_L by simp
    text \<open>Apply \<open>cone_list_sum_weight_split\<close> with \<open>f = c\<close>,
          \<open>g = 0\<close>, \<open>h = rN\<close>, \<open>\<mu> = -1\<close>: then \<open>c k = 0 + (-1) * rN k\<close>
          holds (since \<open>rN k = - c k\<close>).\<close>
    have c_split: "\<And>k. k < L \<Longrightarrow> c k = (0::real) + (-1) * rN k"
      unfolding rN_def by simp
    have typing_idx_pair2:
      "\<And>k. k < L \<Longrightarrow>
          fst (snd (ts ! k)) \<in> carrier_mat m m
          \<and> snd (snd (ts ! k)) \<in> carrier_mat p p"
      using typing_idx by simp
    text \<open>Step A: \<open>cone_list_sum\<close> with all-zero weights = \<open>0\<^sub>m\<close>.\<close>
    have zero_sum:
      "cone_list_sum m p
          (map (\<lambda>k. ((0::real), fst (snd (ts ! k)), snd (snd (ts ! k))))
               [0..<L])
        = 0\<^sub>m (m*p) (m*p)"
    proof -
      have step: "\<And>L'. L' \<le> L \<Longrightarrow>
            cone_list_sum m p
              (map (\<lambda>k. ((0::real), fst (snd (ts ! k)), snd (snd (ts ! k))))
                   [0..<L'])
              = 0\<^sub>m (m*p) (m*p)"
      proof -
        fix L' assume "L' \<le> L"
        thus "cone_list_sum m p
                (map (\<lambda>k. ((0::real), fst (snd (ts ! k)), snd (snd (ts ! k))))
                     [0..<L'])
              = 0\<^sub>m (m*p) (m*p)"
        proof (induction L')
          case 0 thus ?case by simp
        next
          case (Suc L'')
          have L''_lt: "L'' < L" using Suc.prems by linarith
          have L''_le: "L'' \<le> L" using L''_lt by linarith
          have IH: "cone_list_sum m p
                       (map (\<lambda>k. ((0::real), fst (snd (ts ! k)),
                                                  snd (snd (ts ! k))))
                            [0..<L''])
                       = 0\<^sub>m (m*p) (m*p)"
            using Suc.IH[OF L''_le] .
          obtain w0 \<sigma>0 \<tau>0 where ts_L: "ts ! L'' = (w0, \<sigma>0, \<tau>0)"
            by (cases "ts ! L''") auto
          have fst_eq: "fst (snd (ts ! L'')) = \<sigma>0" using ts_L by simp
          have snd_eq: "snd (snd (ts ! L'')) = \<tau>0" using ts_L by simp
          have ts_L_mem: "(w0, \<sigma>0, \<tau>0) \<in> set ts"
            using ts_L L''_lt unfolding L_def by (metis nth_mem)
          have \<sigma>0_c: "\<sigma>0 \<in> carrier_mat m m" and \<tau>0_c: "\<tau>0 \<in> carrier_mat p p"
            using ts_typing ts_L_mem by auto
          have single: "cone_list_sum m p [((0::real), \<sigma>0, \<tau>0)] = 0\<^sub>m (m*p) (m*p)"
            using cone_list_sum_zero_singleton[OF \<sigma>0_c \<tau>0_c] .
          have map_step:
            "map (\<lambda>k. ((0::real), fst (snd (ts ! k)), snd (snd (ts ! k))))
                 [0..<Suc L'']
              = map (\<lambda>k. ((0::real), fst (snd (ts ! k)), snd (snd (ts ! k))))
                    [0..<L'']
                @ [((0::real), \<sigma>0, \<tau>0)]"
            using ts_L by simp
          have z_c: "(0\<^sub>m (m*p) (m*p) :: complex Matrix.mat) \<in> carrier_mat (m*p) (m*p)"
            by simp
          show ?case
            using map_step cone_list_sum_append IH single z_c
            by (simp add: left_add_zero_mat)
        qed
      qed
      show ?thesis using step[OF le_refl] .
    qed

    text \<open>Step B: apply weight-split with \<open>f = c\<close>, \<open>g = 0\<close>, \<open>h = rN\<close>,
          \<open>\<mu> = -1\<close>; then combine with \<open>c_sum_ts = 0\<close> and \<open>zero_sum = 0\<close>.\<close>
    let ?rN_sum = "cone_list_sum m p
                     (map (\<lambda>k. (rN k, fst (snd (ts ! k)),
                                        snd (snd (ts ! k))))
                          [0..<L])"
    have rN_c: "?rN_sum \<in> carrier_mat (m*p) (m*p)"
      by (rule cone_list_sum_carrier)
    have wsplit_eq:
      "cone_list_sum m p
          (map (\<lambda>k. (c k, fst (snd (ts ! k)), snd (snd (ts ! k))))
               [0..<L])
        = cone_list_sum m p
            (map (\<lambda>k. ((0::real), fst (snd (ts ! k)),
                                          snd (snd (ts ! k))))
                 [0..<L])
          + complex_of_real (-1) \<cdot>\<^sub>m ?rN_sum"
      by (rule cone_list_sum_weight_split[OF typing_idx_pair2 c_split])
    text \<open>From \<open>c_sum_ts = 0\<close> and \<open>zero_sum = 0\<close>: \<open>(-1) \<cdot>\<^sub>m ?rN_sum = 0\<close>.\<close>
    have neg_rN_zero: "complex_of_real (-1) \<cdot>\<^sub>m ?rN_sum = 0\<^sub>m (m*p) (m*p)"
    proof -
      have h: "0\<^sub>m (m*p) (m*p)
                  = 0\<^sub>m (m*p) (m*p) + complex_of_real (-1) \<cdot>\<^sub>m ?rN_sum"
        using wsplit_eq c_sum_ts zero_sum by simp
      thus ?thesis using rN_c by (intro eq_matI) auto
    qed
    have S_zero: "?rN_sum = 0\<^sub>m (m*p) (m*p)"
    proof -
      have "?rN_sum = (-1 :: complex) \<cdot>\<^sub>m (complex_of_real (-1) \<cdot>\<^sub>m ?rN_sum)"
        using rN_c by (intro eq_matI) auto
      also have "\<dots> = (-1 :: complex) \<cdot>\<^sub>m 0\<^sub>m (m*p) (m*p)" using neg_rN_zero by simp
      also have "(-1 :: complex) \<cdot>\<^sub>m (0\<^sub>m (m*p) (m*p) :: complex Matrix.mat)
                    = 0\<^sub>m (m*p) (m*p)"
        by (intro eq_matI) auto
      finally show ?thesis .
    qed
    show ?thesis
      apply (rule exI[of _ rN])
      using rN_pos k0_L rN_outside S_zero by blast
  qed

  then obtain r :: "nat \<Rightarrow> real"
    where r_pos_some: "\<exists>k<L. 0 < r k"
      and r_zero_outside: "\<forall>k\<ge>L. r k = 0"
      and r_zero_sum:
        "cone_list_sum m p
          (map (\<lambda>k. (r k, fst (snd (ts ! k)), snd (snd (ts ! k))))
               [0..<L])
           = 0\<^sub>m (m*p) (m*p)"
    by blast

  define P where "P = {k. k < L \<and> 0 < r k}"
  have P_finite: "finite P" unfolding P_def by simp
  have P_nonempty: "P \<noteq> {}" using r_pos_some unfolding P_def by blast
  define ratios where "ratios = (\<lambda>k. fst (ts ! k) / r k)"
  define lam where "lam = Min (ratios ` P)"
  have ri_fin: "finite (ratios ` P)" using P_finite by simp
  have ri_ne: "ratios ` P \<noteq> {}" using P_nonempty by simp
  have lam_in: "lam \<in> ratios ` P"
    unfolding lam_def using ri_fin ri_ne by (rule Min_in)
  have lam_le: "\<And>k. k \<in> P \<Longrightarrow> lam \<le> ratios k"
    unfolding lam_def using ri_fin by (auto intro: Min_le)
  obtain k0 where k0_in: "k0 \<in> P" and k0_eq: "lam = ratios k0"
    using lam_in by auto
  have k0_lt: "k0 < L" and rk0_pos: "0 < r k0"
    using k0_in unfolding P_def by auto
  have wk0_nn: "0 \<le> fst (ts ! k0)" using w_nn_idx[OF k0_lt] .
  have lam_nn: "0 \<le> lam"
    using k0_eq wk0_nn rk0_pos unfolding ratios_def by simp

  define w' where "w' = (\<lambda>k. fst (ts ! k) - lam * r k)"
  have w'_nn: "\<And>k. k < L \<Longrightarrow> 0 \<le> w' k"
  proof -
    fix k assume kL: "k < L"
    show "0 \<le> w' k"
    proof (cases "0 < r k")
      case True
      hence kP: "k \<in> P" using kL unfolding P_def by simp
      have "lam \<le> fst (ts ! k) / r k"
        using lam_le[OF kP] unfolding ratios_def .
      hence "lam * r k \<le> fst (ts ! k)"
        using True by (simp add: pos_le_divide_eq mult.commute)
      thus ?thesis unfolding w'_def by linarith
    next
      case False
      hence "r k \<le> 0" by linarith
      hence "lam * r k \<le> 0"
        using lam_nn by (simp add: mult_nonneg_nonpos)
      thus ?thesis unfolding w'_def using w_nn_idx[OF kL] by linarith
    qed
  qed
  have w'_k0_zero: "w' k0 = 0"
    using k0_eq rk0_pos unfolding w'_def ratios_def by simp

  define ts1 :: "(real \<times> complex Matrix.mat \<times> complex Matrix.mat) list"
    where "ts1 = map (\<lambda>k. (w' k, fst (snd (ts ! k)), snd (snd (ts ! k))))
                     [0..<L]"
  define ts' where "ts' = take k0 ts1 @ drop (Suc k0) ts1"

  have ts1_len: "length ts1 = L" unfolding ts1_def by simp
  have ts'_len: "length ts' = L - 1"
  proof -
    have "length ts' = k0 + (L - Suc k0)"
      unfolding ts'_def using k0_lt ts1_len by simp
    also have "\<dots> = L - 1" using k0_lt by linarith
    finally show ?thesis .
  qed
  have ts'_len_orig: "length ts' = length ts - 1"
    using ts'_len unfolding L_def .

  text \<open>Typing / non-negativity / matrix-pair-inheritance for every
        triple of \<open>ts'\<close>.\<close>
  have ts'_sub_ts1: "set ts' \<subseteq> set ts1"
    unfolding ts'_def using set_take_subset set_drop_subset by fastforce
  have ts'_props:
    "\<forall>(w, \<sigma>, \<tau>) \<in> set ts'.
        \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
        \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts)"
  proof (intro ballI, clarify)
    fix w \<sigma> \<tau> assume mem: "(w, \<sigma>, \<tau>) \<in> set ts'"
    from mem ts'_sub_ts1 have mem1: "(w, \<sigma>, \<tau>) \<in> set ts1" by blast
    from mem1 obtain k where kL: "k < L"
      and triple_eq: "(w, \<sigma>, \<tau>)
                       = (w' k, fst (snd (ts ! k)), snd (snd (ts ! k)))"
      unfolding ts1_def by auto
    obtain w0 s0 t0 where tsk: "ts ! k = (w0, s0, t0)"
      by (cases "ts ! k") auto
    have decomp: "(w, \<sigma>, \<tau>) = (w' k, s0, t0)"
      using triple_eq tsk by simp
    have w_eq: "w = w' k" using decomp by simp
    have s_eq: "\<sigma> = s0" using decomp by simp
    have t_eq: "\<tau> = t0" using decomp by simp
    have tsk_mem: "(w0, s0, t0) \<in> set ts"
      using kL tsk L_def by (metis nth_mem)
    have s0_c: "s0 \<in> carrier_mat m m" and t0_c: "t0 \<in> carrier_mat p p"
      using ts_typing tsk_mem by auto
    show "\<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
          \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts)"
    proof (intro conjI)
      show "\<sigma> \<in> carrier_mat m m" using s_eq s0_c by simp
      show "\<tau> \<in> carrier_mat p p" using t_eq t0_c by simp
      show "0 \<le> w" using w'_nn[OF kL] w_eq by simp
      show "\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts"
        using tsk_mem s_eq t_eq by blast
    qed
  qed

  text \<open>Sum preservation: \<open>cone_list_sum ts = cone_list_sum ts'\<close>.
        Apply \<open>cone_list_sum_weight_split\<close> with \<open>f = fst \<circ> (ts!_)\<close>,
        \<open>g = w'\<close>, \<open>h = r\<close>, \<open>\<mu> = lam\<close>; use \<open>r_zero_sum\<close> to kill the
        \<open>lam\<close>-scaled term; then apply \<open>cone_list_sum_drop_zero\<close>
        at index \<open>k0\<close> where \<open>w' k0 = 0\<close>.\<close>
  have typing_idx_pair:
    "\<And>k. k < L \<Longrightarrow>
        fst (snd (ts ! k)) \<in> carrier_mat m m
        \<and> snd (snd (ts ! k)) \<in> carrier_mat p p"
    using typing_idx by simp
  define tsI :: "(real \<times> complex Matrix.mat \<times> complex Matrix.mat) list"
    where "tsI = map (\<lambda>k. (fst (ts ! k), fst (snd (ts ! k)),
                              snd (snd (ts ! k)))) [0..<L]"
  define tsR :: "(real \<times> complex Matrix.mat \<times> complex Matrix.mat) list"
    where "tsR = map (\<lambda>k. (r k, fst (snd (ts ! k)), snd (snd (ts ! k))))
                    [0..<L]"
  have tsI_eq_ts: "tsI = ts"
  proof (rule nth_equalityI)
    show "length tsI = length ts" unfolding tsI_def L_def by simp
  next
    fix k assume k_lt: "k < length tsI"
    hence k_L: "k < L" unfolding tsI_def by simp
    obtain w0 s0 t0 where tsk: "ts ! k = (w0, s0, t0)"
      by (cases "ts ! k") auto
    have "tsI ! k = (fst (ts ! k), fst (snd (ts ! k)), snd (snd (ts ! k)))"
      unfolding tsI_def using k_L by simp
    also have "\<dots> = (w0, s0, t0)" using tsk by simp
    finally show "tsI ! k = ts ! k" using tsk by simp
  qed
  have r_zero: "cone_list_sum m p tsR = 0\<^sub>m (m*p) (m*p)"
    using r_zero_sum unfolding tsR_def .
  have split_eq:
    "\<And>k. k < L \<Longrightarrow> fst (ts ! k) = w' k + lam * r k"
    unfolding w'_def by simp
  have ws_eq: "cone_list_sum m p tsI
                  = cone_list_sum m p ts1
                    + complex_of_real lam \<cdot>\<^sub>m cone_list_sum m p tsR"
    unfolding tsI_def ts1_def tsR_def
    by (rule cone_list_sum_weight_split[OF typing_idx_pair split_eq])
  have ts1_c: "cone_list_sum m p ts1 \<in> carrier_mat (m*p) (m*p)"
    by (rule cone_list_sum_carrier)
  have z_scale: "complex_of_real lam \<cdot>\<^sub>m (0\<^sub>m (m*p) (m*p) :: complex Matrix.mat)
                  = 0\<^sub>m (m*p) (m*p)"
    by (intro eq_matI) auto
  have ts1_sum_eq: "cone_list_sum m p ts1 = cone_list_sum m p ts"
  proof -
    have "cone_list_sum m p ts = cone_list_sum m p tsI"
      using tsI_eq_ts by simp
    also have "\<dots> = cone_list_sum m p ts1
                    + complex_of_real lam \<cdot>\<^sub>m cone_list_sum m p tsR"
      using ws_eq .
    also have "\<dots> = cone_list_sum m p ts1
                    + complex_of_real lam \<cdot>\<^sub>m 0\<^sub>m (m*p) (m*p)"
      using r_zero by simp
    also have "complex_of_real lam \<cdot>\<^sub>m 0\<^sub>m (m*p) (m*p)
                  = (0\<^sub>m (m*p) (m*p) :: complex Matrix.mat)"
      using z_scale .
    also have "cone_list_sum m p ts1 + 0\<^sub>m (m*p) (m*p)
                  = cone_list_sum m p ts1"
      using ts1_c by (intro eq_matI) auto
    finally show ?thesis by simp
  qed
  have ts1_typing_all: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts1.
                          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
  proof clarify
    fix w \<sigma> \<tau> assume "(w, \<sigma>, \<tau>) \<in> set ts1"
    then obtain k where kL: "k < L"
      and triple_eq: "(w, \<sigma>, \<tau>)
                       = (w' k, fst (snd (ts ! k)), snd (snd (ts ! k)))"
      unfolding ts1_def by auto
    obtain w0 s0 t0 where tsk: "ts ! k = (w0, s0, t0)"
      by (cases "ts ! k") auto
    have d: "(w, \<sigma>, \<tau>) = (w' k, s0, t0)"
      using triple_eq tsk by simp
    have s_eq: "\<sigma> = s0" using d by simp
    have t_eq: "\<tau> = t0" using d by simp
    have tsk_mem: "(w0, s0, t0) \<in> set ts"
      using kL tsk L_def by (metis nth_mem)
    have "s0 \<in> carrier_mat m m \<and> t0 \<in> carrier_mat p p"
      using ts_typing tsk_mem by auto
    thus "\<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
      using s_eq t_eq by simp
  qed
  have k0_in_ts1: "k0 < length ts1" using k0_lt ts1_len by simp
  have ts1_k0_zero: "fst (ts1 ! k0) = 0"
    unfolding ts1_def using k0_lt w'_k0_zero by simp
  have drop_eq: "cone_list_sum m p (take k0 ts1 @ drop (Suc k0) ts1)
                  = cone_list_sum m p ts1"
    using cone_list_sum_drop_zero[OF k0_in_ts1 ts1_k0_zero ts1_typing_all] .
  have ts'_sum_eq: "cone_list_sum m p ts' = cone_list_sum m p ts1"
    unfolding ts'_def using drop_eq .
  have sum_preserved: "cone_list_sum m p ts = cone_list_sum m p ts'"
    using ts1_sum_eq ts'_sum_eq by simp

  show ?thesis
    using ts'_len_orig ts'_props sum_preserved
    by (intro exI[of _ ts']) blast
qed

text \<open>The Carath\'eodory bound follows from the reduction step by
strong induction on \<open>length ts\<close>.  This part is now closed
unconditionally; only the two focused sub-sorries inside
\<open>caratheodory_matrix_cone_step\<close> remain.\<close>

lemma caratheodory_matrix_cone:
  fixes m p :: nat
      and ts :: "(real \<times> complex Matrix.mat \<times> complex Matrix.mat) list"
  assumes m_pos: "0 < m" and p_pos: "0 < p"
      and ts_typing: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts.
                          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
      and ts_nn: "\<forall>(w, _, _) \<in> set ts. 0 \<le> w"
  shows "\<exists>ts'. length ts' \<le> 2 * (m*p)\<^sup>2 + 1
              \<and> (\<forall>(w, \<sigma>, \<tau>) \<in> set ts'.
                    \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
                    \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts))
              \<and> cone_list_sum m p ts = cone_list_sum m p ts'"
  using ts_typing ts_nn
proof (induction "length ts" arbitrary: ts rule: less_induct)
  case less
  show ?case
  proof (cases "length ts \<le> 2 * (m*p)\<^sup>2 + 1")
    case True
    have ts_in: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts.
                    \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
                    \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts)"
      using less.prems by force
    show ?thesis
      using True ts_in by (intro exI[of _ ts]) auto
  next
    case False
    hence ts_long: "length ts > 2 * (m*p)\<^sup>2 + 1" by simp
    from caratheodory_matrix_cone_step
            [OF m_pos p_pos less.prems(1) less.prems(2) ts_long]
    obtain ts1 where ts1_len: "length ts1 = length ts - 1"
      and ts1_props: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts1.
                          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
                          \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts)"
      and ts1_sum: "cone_list_sum m p ts = cone_list_sum m p ts1"
      by blast
    have ts_pos_len: "0 < length ts" using ts_long by linarith
    have ts1_shorter: "length ts1 < length ts"
      using ts1_len ts_pos_len by linarith
    have ts1_typing: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts1.
                          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p"
      using ts1_props by force
    have ts1_nn: "\<forall>(w, _, _) \<in> set ts1. 0 \<le> w"
      using ts1_props by force
    from less.hyps[OF ts1_shorter ts1_typing ts1_nn]
    obtain ts' where ts'_len: "length ts' \<le> 2 * (m*p)\<^sup>2 + 1"
      and ts'_props: "\<forall>(w, \<sigma>, \<tau>) \<in> set ts'.
                          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
                          \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts1)"
      and ts'_sum: "cone_list_sum m p ts1 = cone_list_sum m p ts'"
      by blast
    have ts'_in_ts:
      "\<forall>(w, \<sigma>, \<tau>) \<in> set ts'.
          \<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
          \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts)"
    proof clarify
      fix w \<sigma> \<tau> assume m: "(w, \<sigma>, \<tau>) \<in> set ts'"
      from ts'_props m have \<sigma>: "\<sigma> \<in> carrier_mat m m"
        and \<tau>: "\<tau> \<in> carrier_mat p p" and wnn: "0 \<le> w"
        and ex1: "\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts1" by auto
      from ex1 obtain w1 where w1: "(w1, \<sigma>, \<tau>) \<in> set ts1" by blast
      from ts1_props w1 have "\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts" by auto
      thus "\<sigma> \<in> carrier_mat m m \<and> \<tau> \<in> carrier_mat p p \<and> 0 \<le> w
              \<and> (\<exists>w\<^sub>0. (w\<^sub>0, \<sigma>, \<tau>) \<in> set ts)"
        using \<sigma> \<tau> wnn by blast
    qed
    have sum_eq: "cone_list_sum m p ts = cone_list_sum m p ts'"
      using ts1_sum ts'_sum by simp
    show ?thesis
      using ts'_len ts'_in_ts sum_eq by (intro exI[of _ ts']) blast
  qed
qed

text \<open>How the bound is used (Separable\_Cone): a sequence in the separable cone has
decompositions of length at most $K=2(mp)^2+1$; padding with zero-weight entries and
normalising traces makes the weights bounded, so coordinatewise Bolzano--Weierstrass
extracts a convergent subsequence of weights and factors; tensoring and addition are
continuous, so the limit lies in the cone.  The compactness of the unit-trace positive
matrices is obtained from the Euclidean-space instance of Lmat\_Euclidean (real dimension
$2(mp)^2$) rather than from the sequential-compactness lemma
\<open>HS_Cauchy_imp_convergent\<close> proved above.\<close>
end
