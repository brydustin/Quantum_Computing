(*  Title:   Matrix_Analysis_Prerequisites.thy
    Author:  Dustin Bryant.  Capstone of the bundle: imports its four theories.
*)
theory Matrix_Analysis_Prerequisites
  imports
    Matrix_Lemmas
    Unitary_Tensor_Algebra
    Matrix_Typed
    Lmat_Euclidean
begin

section \<open>The bundle at a glance\<close>

text \<open>Four theories, none of which depends on the lectures.\<close>

subsection \<open>Matrix lemmas\<close>

text \<open>Sums, adjoints and index arithmetic for \<open>complex Matrix.mat\<close>: finite sums of
matrices (\<open>msum\<close>, \<open>foldr\<close>-sums), entries of products, linear maps on a set of matrices and
linear-space isomorphisms.\<close>

text \<open>
@{thm [display] dagger_mult_inner}
@{thm [display] mat_eq_of_mult_vec_eq}
@{thm [display] msum_mult_left}
@{thm [display] msum_mult_right}
@{thm [display] nat_eq_iff_div_mod}
@{thm [display] lin_on_msum_closed}\<close>

subsection \<open>Unitary and Kronecker-product algebra\<close>

text \<open>Unitary matrices are closed under products and adjoints; the Kronecker product
satisfies the mixed-product law, so tensor products of unitaries are unitary.\<close>

text \<open>
@{thm [display] unitary_dagger}
@{thm [display] unitary_mult}
@{thm [display] tensor_mat_mult}
@{thm [display] tensor_mat_unitary}
@{thm [display] mult_index_div_mod}\<close>

subsection \<open>Matrices of fixed dimension\<close>

text \<open>\<open>('a, 'm, 'n) lmat\<close> carries the dimensions in its type.  With the Hilbert--Schmidt
norm it is a normed vector space in the sense of \<open>HOL-Hahn_Banach\<close>.\<close>

text \<open>
@{thm [display] hs_norm_lmat_triangle}
@{thm [display] hs_norm_lmat_zero_iff}
@{thm [display] normed_vectorspace_UNIV_lmat}\<close>

subsection \<open>Matrices as a Euclidean space\<close>

text \<open>For \<open>'a = complex\<close> the type \<open>lmat\<close> is a \<open>euclidean_space\<close> of dimension
$2\,\mathrm{CARD}('m)\,\mathrm{CARD}('n)$, so the convexity and compactness results of
\<open>HOL-Analysis\<close> apply to matrices; entries depend continuously on the matrix.\<close>

text \<open>
@{thm [display] DIM_lmat}
@{thm [display] norm_lmat_index_le}
@{thm [display] continuous_on_lmat_entries}\<close>

end
