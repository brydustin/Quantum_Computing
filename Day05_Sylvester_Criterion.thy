theory Day05_Sylvester_Criterion
  imports Quantum_Computing_by_VP.Day05_Positivity_Tests Two_Hermitian_Results.Sylvester_Criterion
begin

section \<open>Day 5: Sylvester's criterion (D5-1)\<close>

text \<open>Sylvester's criterion, stated in the previous section, is proved in the AFP entry
\emph{Two Hermitian Results} (@{thm [source] Sylvester_Criterion.sylvester_criterion}), with its
own notions of Hermitian matrix (\<^const>\<open>Complex_Matrix.hermitian\<close>, from QHLProver)
and positive definiteness (\<^const>\<open>Misc_Matrix_Results.positive_definite\<close>, with the quadratic form
\<^const>\<open>quadratic_form\<close> and the order on \<^typ>\<open>complex\<close>).  It is not reproved here.  The
lemmas below show that these notions agree with \<^const>\<open>Day04_Hermitian_Matrices.hermitian\<close> and
\<^const>\<open>Day04_Hermitian_Matrices.pd\<close> of the formalised notes; the theorem is then restated in
those terms.  Names that both libraries define (\<open>hermitian\<close>, \<open>inner_prod\<close>) are written with
their theory prefix.  Formally $P_k$ is \<^term>\<open>lps P k\<close>, and $k$ ranges over $0,\dots,n$:
the case $k=0$ adds nothing, since a $0\times0$ determinant is $1$.  The entry's imports undo the
hiding of Isabelle\_Marries\_Dirac's gate names in \texttt{Day01\_Inner\_Product}, so they are
hidden again here.\<close>

hide_const (open) Quantum.X Quantum.Y Quantum.Z Quantum.H Quantum.S Quantum.T

lemma hermitian_iff_Complex_Matrix_hermitian: "Day04_Hermitian_Matrices.hermitian A \<longleftrightarrow> Complex_Matrix.hermitian A"
  by (simp add: Day04_Hermitian_Matrices.hermitian_def Complex_Matrix.hermitian_def Linear_Algebra_Complements.dagger_adjoint)

lemma quadratic_form_eq_inner_prod:
  fixes P :: "complex Matrix.mat" and x :: "complex Matrix.vec"
  assumes P: "P \<in> carrier_mat n n" and x: "dim_vec x = n"
  shows "quadratic_form P x = Quantum.inner_prod x (P *\<^sub>v x)"
  using P x by (simp add: Quantum.inner_prod_def scalar_prod_def conjugate_vec_def mult.commute)

lemma pd_iff_positive_definite:
  fixes P :: "complex Matrix.mat"
  assumes P: "P \<in> carrier_mat n n"
  shows "Day04_Hermitian_Matrices.pd P \<longleftrightarrow> positive_definite P"
proof
  assume pd: "Day04_Hermitian_Matrices.pd P"
  hence h: "Day04_Hermitian_Matrices.hermitian P" unfolding Day04_Hermitian_Matrices.pd_def by blast
  have all: "\<forall>x. dim_vec x = dim_row P \<longrightarrow> x \<noteq> 0\<^sub>v (dim_row P) \<longrightarrow> 0 < Re (Quantum.inner_prod x (P *\<^sub>v x))"
    using pd unfolding Day04_Hermitian_Matrices.pd_def by blast
  have "0 < quadratic_form P x" if x: "x \<in> carrier_vec n" "x \<noteq> 0\<^sub>v n" for x
  proof -
    have xd: "dim_vec x = n" using x(1) by (rule carrier_vecD)
    have re: "0 < Re (Quantum.inner_prod x (P *\<^sub>v x))" using all[rule_format, of x] xd x(2) carrier_matD(1)[OF P] by simp
    have "Quantum.inner_prod x (P *\<^sub>v x) \<in> \<real>"
      using Day04_Hermitian_Matrices.hermitian_iff_real_quad_form[OF P] h xd by blast
    hence im: "Im (Quantum.inner_prod x (P *\<^sub>v x)) = 0" by (simp add: complex_is_Real_iff)
    show ?thesis unfolding quadratic_form_eq_inner_prod[OF P xd] using re im by (simp add: less_complex_def)
  qed
  hence "\<forall>x \<in> carrier_vec (dim_col P). x \<noteq> 0\<^sub>v (dim_col P) \<longrightarrow> 0 < quadratic_form P x"
    using carrier_matD(2)[OF P] by simp
  moreover have "Complex_Matrix.hermitian P" using h by (simp add: hermitian_iff_Complex_Matrix_hermitian)
  ultimately show "positive_definite P" unfolding positive_definite_def by blast
next
  assume pd: "positive_definite P"
  hence "Complex_Matrix.hermitian P" unfolding positive_definite_def by blast
  hence h: "Day04_Hermitian_Matrices.hermitian P" by (simp add: hermitian_iff_Complex_Matrix_hermitian)
  have "0 < Re (Quantum.inner_prod x (P *\<^sub>v x))" if xd: "dim_vec x = n" and x0: "x \<noteq> 0\<^sub>v n" for x
  proof -
    have xc: "x \<in> carrier_vec (dim_col P)" using xd carrier_matD(2)[OF P] by (intro carrier_vecI) simp
    have x0': "x \<noteq> 0\<^sub>v (dim_col P)" using x0 carrier_matD(2)[OF P] by simp
    have "0 < quadratic_form P x" using pd xc x0' unfolding positive_definite_def by blast
    thus ?thesis unfolding quadratic_form_eq_inner_prod[OF P xd] by (simp add: less_complex_def)
  qed
  hence "\<forall>x. dim_vec x = dim_row P \<longrightarrow> x \<noteq> 0\<^sub>v (dim_row P) \<longrightarrow> 0 < Re (Quantum.inner_prod x (P *\<^sub>v x))"
    using carrier_matD(1)[OF P] by simp
  thus "Day04_Hermitian_Matrices.pd P" unfolding Day04_Hermitian_Matrices.pd_def using h by blast
qed

text \<open>Sylvester's criterion: a Hermitian $P\in M_n$ is positive definite iff
$\det P_k>0$ for every leading principal submatrix $P_k$, $k\le n$ (\<^const>\<open>lps\<close>; the order is
that of \<^typ>\<open>complex\<close>, so each minor is real and positive).\<close>

theorem pd_iff_leading_minors_pos:
  fixes P :: "complex Matrix.mat"
  assumes P: "P \<in> carrier_mat n n" and h: "Day04_Hermitian_Matrices.hermitian P"
  shows "Day04_Hermitian_Matrices.pd P \<longleftrightarrow> (\<forall>k \<le> n. 0 < Determinant.det (lps P k))"
proof -
  have "Complex_Matrix.hermitian P" using h by (simp add: hermitian_iff_Complex_Matrix_hermitian)
  hence "sylvester_criterion P \<longleftrightarrow> positive_definite P" by (rule Sylvester_Criterion.sylvester_criterion)
  thus ?thesis using P by (simp add: pd_iff_positive_definite[OF P] sylvester_criterion_def)
qed

corollary pd_iff_leading_minors_real_pos:
  fixes P :: "complex Matrix.mat"
  assumes P: "P \<in> carrier_mat n n" and h: "Day04_Hermitian_Matrices.hermitian P"
  shows "Day04_Hermitian_Matrices.pd P \<longleftrightarrow>
         (\<forall>k \<le> n. Im (Determinant.det (lps P k)) = 0 \<and> 0 < Re (Determinant.det (lps P k)))"
  using pd_iff_leading_minors_pos[OF P h] by (simp add: less_complex_def conj_commute)

end
