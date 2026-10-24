(*  Title:   Functional_Calculus_Overview.thy
    Author:  Dustin Bryant
*)

theory Functional_Calculus_Overview
  imports
    Hermitian_Functional_Calculus
    Matrix_Sums
    Trotter_Product_Formula
    Suzuki_Order
    Suzuki_Error
begin

section \<open>Overview\<close>

text \<open>The entry has five parts.
\<^item> \texttt{Hermitian\_Functional\_Calculus}: $g(A)$ for Hermitian $A$ (\<open>mat_fun_eigen\<close>,
  \<open>mat_fun_decomp\<close>), its algebra ($g(A)h(A)=(gh)(A)$, $g(A)^*=\bar g(A)$, linearity, powers,
  composition), unitarity, time evolution, and the inverse (\<open>herm_inv\<close>).
\<^item> \texttt{Matrix\_Sums}: finite sums of matrices.
\<^item> \texttt{Trotter\_Product\_Formula}: the Lie--Trotter formula with error bound (\<open>trotter\<close>).
\<^item> \texttt{Suzuki\_Order}: Suzuki's recursion and its order conditions (\<open>suzuki_order\<close>).
\<^item> \texttt{Suzuki\_Error}: the error of a product formula (\<open>formula_product_approx\<close>,
  \<open>suzuki_error\<close>).\<close>

section \<open>Using the entry\<close>

text \<open>For a Hermitian $A\in M_n$ (\<open>A \<in> carrier_mat n n\<close> and \<open>hermitian A\<close>) and a function
$g:\R\to\C$, \<open>mat_fun g A\<close> is $g(A)$.
\<^item> Computing $g(A)$: on eigenvectors (\<open>mat_fun_eigen\<close>), from a spectral decomposition
  (\<open>spectral_decomp_exists\<close>, \<open>mat_fun_decomp\<close>), or entrywise for real diagonal matrices
  (\<open>mat_fun_diag\<close>).  To show that a given matrix is $g(A)$, use \<open>mat_fun_eqI\<close>.
\<^item> Algebra: \<open>mat_fun_add\<close>, \<open>mat_fun_smult\<close>, \<open>mat_fun_mult\<close>, \<open>mat_fun_pow\<close>,
  \<open>mat_fun_comp\<close>, \<open>mat_fun_dagger\<close>, \<open>mat_fun_hermitian\<close>, \<open>mat_fun_unitary\<close>, and
  \<open>mat_fun_cong\<close> (only the values on the spectrum matter).
\<^item> \<open>evolution A t\<close> is $e^{itA}$ and \<open>herm_inv A\<close> is $A^{-1}$.
\<^item> \<open>op_close n \<eta> U V\<close> says $\norm{Uv-Vv}\le\eta\norm v$ for all $v$; the product formulas
  (\<open>trotter\<close>, \<open>suzuki_error\<close>) are stated with it.\<close>

text \<open>Matrices are those of Jordan\_Normal\_Form, with the adjoint $M^\dagger$ and \<open>unitary\<close> of
Isabelle\_Marries\_Dirac and \<open>hermitian\<close> of QHLProver.  The theories hide Isabelle\_Marries\_Dirac's
gate constants \<open>X\<close>, \<open>Y\<close>, \<open>Z\<close>, \<open>H\<close>, \<open>S\<close>, \<open>T\<close> (still available as \<open>Quantum.X\<close> etc.), so
that these letters can name matrices.\<close>

subsection \<open>Examples\<close>

text \<open>The evolution under $Z=\diag(1,-1)$ is $e^{itZ}=\diag(e^{it},e^{-it})$:\<close>

lemma example_evolution_Z: "evolution (diag_matrix [1, -1]) t = diag_matrix [cis t, cis (- t)]"
proof -
  have "evolution (diag_matrix (map complex_of_real [1, -1])) t = diag_matrix (map (\<lambda>x. cis (t * x)) [1, -1])"
    unfolding evolution_def by (rule mat_fun_diag)
  thus ?thesis by simp
qed

text \<open>The inverse of $\diag(2,4)$ is $\diag(\tfrac12,\tfrac14)$:\<close>

lemma example_inverse: "herm_inv (diag_matrix [2, 4]) = diag_matrix [1/2, 1/4]"
proof -
  have "herm_inv (diag_matrix (map complex_of_real [2, 4])) = diag_matrix (map (\<lambda>x. complex_of_real (inverse x)) [2, 4])"
    unfolding herm_inv_def by (rule mat_fun_diag)
  thus ?thesis by (simp add: inverse_eq_divide)
qed

end
