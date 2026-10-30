theory Notes_Library_Bridge
  imports Day10_Quantum_Gates Day13_Density_Matrices
    QHLProver.Complex_Matrix
begin

section \<open>The notes' definitions and the AFP's\<close>

text \<open>The lectures define their basic notions as Paulsen does.  Several of them are also defined in
the AFP entry \emph{Quantum Hoare Logic} (\<open>QHLProver\<close>, theory \<open>Complex_Matrix\<close>) and in
\emph{Isabelle Marries Dirac} (\<open>Quantum\<close>).  They agree: for square matrices of matching size
each notion of the notes is the library's.  The projector of the AFP entry
\emph{Projective Measurements} is \<open>Complex_Matrix.hermitian M \<and> M * M = M\<close>, the right-hand side
of \<open>projection_AFP\<close> below.\<close>

lemma dagger_adjoint_AFP: "M\<^sup>\<dagger> = Complex_Matrix.adjoint M"
  by (rule eq_matI) (simp_all add: dagger_def adjoint_eval)

lemma inner_prod_AFP: "dim_vec v = dim_vec w \<Longrightarrow> Complex_Matrix.inner_prod v w = \<langle>v | w\<rangle>"
  by (simp add: Quantum.inner_prod_def scalar_prod_def conjugate_vec_def mult.commute)

lemma hermitian_AFP: "Day04_Hermitian_Matrices.hermitian A \<longleftrightarrow> Complex_Matrix.hermitian A"
  by (simp add: Day04_Hermitian_Matrices.hermitian_def Complex_Matrix.hermitian_def dagger_adjoint_AFP)

lemma Tr_AFP:
  assumes A: "A \<in> carrier_mat n n"
  shows "Tr A = Complex_Matrix.trace A"
proof -
  have r: "dim_row A = n" using A by (rule carrier_matD(1))
  show ?thesis unfolding Tr_carrier[OF A] Complex_Matrix.trace_def r atLeast0LessThan ..
qed

lemma psd_AFP: "psd P \<longleftrightarrow> Complex_Matrix.positive P"
proof
  assume P: "psd P"
  hence h: "Day04_Hermitian_Matrices.hermitian P" by (simp add: psd_def)
  have dr: "dim_row P = dim_col P" by (rule hermitian_square[OF h])
  have sq: "P \<in> carrier_mat (dim_col P) (dim_col P)" by (rule carrier_matI) (simp_all only: dr)
  have q: "\<forall>x :: complex Matrix.vec. dim_vec x = dim_col P \<longrightarrow> \<langle>x | P *\<^sub>v x\<rangle> \<in> \<real>"
    using hermitian_iff_real_quad_form[OF sq] h by blast
  show "Complex_Matrix.positive P"
    unfolding Complex_Matrix.positive_def
  proof (intro conjI allI impI)
    show "P \<in> carrier_mat (dim_col P) (dim_col P)" by (rule sq)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = dim_col P"
    have vr: "dim_vec v = dim_row P" by (simp only: v dr)
    have e: "Complex_Matrix.inner_prod v (P *\<^sub>v v) = \<langle>v | P *\<^sub>v v\<rangle>"
      by (intro inner_prod_AFP) (simp only: vr dim_mult_mat_vec)
    have real: "\<langle>v | P *\<^sub>v v\<rangle> \<in> \<real>" using q v by blast
    have re: "Re \<langle>v | P *\<^sub>v v\<rangle> \<ge> 0" using P vr by (simp add: psd_def)
    show "Complex_Matrix.inner_prod v (P *\<^sub>v v) \<ge> 0"
      using e real re by (simp add: less_eq_complex_def complex_is_Real_iff)
  qed
next
  assume P: "Complex_Matrix.positive P"
  have h: "Day04_Hermitian_Matrices.hermitian P"
    using positive_is_hermitian[OF P] by (simp add: hermitian_AFP)
  have sq: "P \<in> carrier_mat (dim_col P) (dim_col P)" using P unfolding Complex_Matrix.positive_def by (rule conjunct1)
  have dr: "dim_row P = dim_col P" using sq by (rule carrier_matD(1))
  show "psd P"
    unfolding psd_def
  proof (intro conjI allI impI)
    show "Day04_Hermitian_Matrices.hermitian P" by (rule h)
    fix x :: "complex Matrix.vec" assume x: "dim_vec x = dim_row P"
    have xc: "dim_vec x = dim_col P" by (simp only: x dr)
    have "Complex_Matrix.inner_prod x (P *\<^sub>v x) \<ge> 0"
      using P xc unfolding Complex_Matrix.positive_def by blast
    moreover have "Complex_Matrix.inner_prod x (P *\<^sub>v x) = \<langle>x | P *\<^sub>v x\<rangle>"
      by (intro inner_prod_AFP) (simp only: x dim_mult_mat_vec)
    ultimately show "Re \<langle>x | P *\<^sub>v x\<rangle> \<ge> 0" by (simp add: less_eq_complex_def)
  qed
qed

lemma density_matrix_AFP:
  "density_matrix n \<rho> \<longleftrightarrow> \<rho> \<in> carrier_mat n n \<and> Complex_Matrix.density_operator \<rho>"
proof
  assume "density_matrix n \<rho>"
  hence c: "\<rho> \<in> carrier_mat n n" "psd \<rho>" "Tr \<rho> = 1" by (simp_all add: density_matrix_def)
  have "Complex_Matrix.positive \<rho>" using c(2) by (simp only: psd_AFP)
  moreover have "Complex_Matrix.trace \<rho> = 1" using c(3) by (simp only: Tr_AFP[OF c(1)])
  ultimately show "\<rho> \<in> carrier_mat n n \<and> Complex_Matrix.density_operator \<rho>"
    using c(1) by (simp only: Complex_Matrix.density_operator_def simp_thms)
next
  assume a: "\<rho> \<in> carrier_mat n n \<and> Complex_Matrix.density_operator \<rho>"
  hence c: "\<rho> \<in> carrier_mat n n" "Complex_Matrix.positive \<rho>" "Complex_Matrix.trace \<rho> = 1"
    by (simp_all only: Complex_Matrix.density_operator_def simp_thms)
  have "psd \<rho>" using c(2) by (simp only: psd_AFP)
  moreover have "Tr \<rho> = 1" using c(3) by (simp only: Tr_AFP[OF c(1)])
  ultimately show "density_matrix n \<rho>" using c(1) by (simp only: density_matrix_def simp_thms)
qed

lemma projection_AFP:
  "projection n P \<longleftrightarrow> P \<in> carrier_mat n n \<and> Complex_Matrix.hermitian P \<and> P * P = P"
  by (simp add: projection_def hermitian_AFP)

lemma unitary_AFP:
  assumes U: "U \<in> carrier_mat n n"
  shows "Quantum.unitary U \<longleftrightarrow> Complex_Matrix.unitary U"
proof
  assume "Quantum.unitary U"
  thus "Complex_Matrix.unitary U"
    using U unfolding Complex_Matrix.unitary_def Quantum.unitary_def inverts_mat_def dagger_adjoint_AFP
    by auto
next
  assume u: "Complex_Matrix.unitary U"
  show "Quantum.unitary U"
    using U unitary_simps[OF U u] unfolding Quantum.unitary_def dagger_adjoint_AFP by auto
qed

lemma Pauli_AFP: "Pauli_X = Quantum.X" "Pauli_Y = - Quantum.Y" "Pauli_Z = Quantum.Z"
  by (rule eq_matI; auto simp: Pauli_X_def Pauli_Y_def Pauli_Z_def Quantum.X_def Quantum.Y_def
      Quantum.Z_def less_Suc_eq numeral_2_eq_2)+

end
