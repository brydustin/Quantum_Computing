theory Matrix_Sums
  imports Hermitian_Functional_Calculus QHLProver.Matrix_Limit
begin

section \<open>Finite sums of matrices\<close>

text \<open>For QHLProver's sums $\sum_{k<n}F_k$ of $K\times K$ matrices: entries are sums of entries, and a sum
of multiples of one matrix is a multiple of it,
\[ \Bigl(\sum_kF_k\Bigr)_{ij}=\sum_k(F_k)_{ij},\qquad \sum_kf_k\,B=\Bigl(\sum_kf_k\Bigr)B. \]\<close>

lemma matrix_sum_index:
  assumes f: "\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat K K" and ij: "i < K" "j < K"
  shows "matrix_sum K f n $$ (i, j) = (\<Sum>k<n. f k $$ (i, j))"
  using f
proof (induction n)
  case (Suc n)
  have c: "matrix_sum K f n \<in> carrier_mat K K" by (rule matrix_sum_dim) (use Suc.prems in auto)
  have "matrix_sum K f (Suc n) $$ (i, j) = f n $$ (i, j) + matrix_sum K f n $$ (i, j)"
    using c Suc.prems[of n] ij by simp
  thus ?case using Suc by (simp add: add_ac)
qed (use ij in simp)

lemma matrix_sum_scalar:
  assumes B: "B \<in> carrier_mat d d"
  shows "matrix_sum d (\<lambda>k. f k \<cdot>\<^sub>m B) m = (\<Sum>k<m. f k) \<cdot>\<^sub>m B"
proof (induction m)
  case 0 show ?case by (rule eq_matI) (use B in auto)
next
  case (Suc m)
  show ?case unfolding matrix_sum.simps Suc.IH using B by (intro eq_matI) (auto simp: algebra_simps)
qed

end
