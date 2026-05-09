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

end
