theory Day05_Direct_Sum_Basis
  imports Quantum_Computing_by_VP_Basics.Day05_Positivity_Tests
begin

section \<open>Day 5: a basis of $V\oplus W$ (D5-5)\<close>

text \<open>A basis of $\C^n$ is a list of $n$ vectors whose column matrix is invertible.  The notes: if $v_1,\dots,v_n$ and $w_1,\dots,w_k$ are bases of
$V$ and $W$ then $(v_i,0)$, $(0,w_j)$ is a basis of $V\oplus W$, so
$\dim(V\oplus W)=\dim V+\dim W$.  The column matrix is block diagonal.\<close>

definition direct_sum_basis :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec list" where
  "direct_sum_basis n k vs ws = map (\<lambda>v. v \<oplus>\<^sub>v 0\<^sub>v k) vs @ map (\<lambda>w. 0\<^sub>v n \<oplus>\<^sub>v w) ws"

lemma direct_sum_basis_block:
  assumes vs: "\<forall>v \<in> set vs. dim_vec v = n" "length vs = n" and ws: "\<forall>w \<in> set ws. dim_vec w = k" "length ws = k"
  shows "mat_of_cols (n + k) (direct_sum_basis n k vs ws)
         = four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws))"
    "j < dim_col (four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws))"
  hence i: "i < n + k" and j: "j < n + k" using vs ws by simp_all
  show "mat_of_cols (n + k) (direct_sum_basis n k vs ws) $$ (i, j)
        = four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws) $$ (i, j)"
  proof (cases "j < n")
    case True
    have vj: "dim_vec (vs ! j) = n" using vs True by simp
    show ?thesis using i j True vs ws vj
      by (auto simp: mat_of_cols_def direct_sum_basis_def nth_append append_vec_def Let_def)
  next
    case False
    have wj: "dim_vec (ws ! (j - n)) = k" using ws j False by simp
    show ?thesis using i j False vs ws wj
      by (auto simp: mat_of_cols_def direct_sum_basis_def nth_append append_vec_def Let_def)
  qed
qed (use vs ws in \<open>simp_all add: direct_sum_basis_def\<close>)

lemma basis_inverse:
  fixes fs :: "complex Matrix.vec list"
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and inv: "invertible_mat (mat_of_cols m fs)"
  obtains G where "G \<in> carrier_mat m m" "G * mat_of_cols m fs = 1\<^sub>m m" "mat_of_cols m fs * G = 1\<^sub>m m"
proof -
  let ?F = "mat_of_cols m fs"
  obtain G where FG: "?F * G = 1\<^sub>m m" and GF: "G * ?F = 1\<^sub>m (dim_row G)"
    using inv unfolding invertible_mat_def inverts_mat_def by auto
  have c: "dim_col G = m" using arg_cong[OF FG, of dim_col] by simp
  have r: "dim_row G = m" using arg_cong[OF GF, of dim_col] fd by simp
  show thesis by (rule that) (use c r FG GF in \<open>auto intro: carrier_matI\<close>)
qed

theorem direct_sum_basis_is_basis:
  assumes vs: "\<forall>v \<in> set vs. dim_vec v = n" "length vs = n" and iv: "invertible_mat (mat_of_cols n vs)"
      and ws: "\<forall>w \<in> set ws. dim_vec w = k" "length ws = k" and iw: "invertible_mat (mat_of_cols k ws)"
  shows "\<forall>u \<in> set (direct_sum_basis n k vs ws). dim_vec u = n + k"
    and "length (direct_sum_basis n k vs ws) = n + k"
    and "invertible_mat (mat_of_cols (n + k) (direct_sum_basis n k vs ws))"
proof -
  show "\<forall>u \<in> set (direct_sum_basis n k vs ws). dim_vec u = n + k"
    using vs ws by (auto simp: direct_sum_basis_def)
  show "length (direct_sum_basis n k vs ws) = n + k" using vs ws by (simp add: direct_sum_basis_def)
  obtain G where G: "G \<in> carrier_mat n n" and GV: "G * mat_of_cols n vs = 1\<^sub>m n" and VG: "mat_of_cols n vs * G = 1\<^sub>m n"
    by (rule basis_inverse[OF vs iv])
  obtain H where H: "H \<in> carrier_mat k k" and HW: "H * mat_of_cols k ws = 1\<^sub>m k" and WH: "mat_of_cols k ws * H = 1\<^sub>m k"
    by (rule basis_inverse[OF ws iw])
  have V: "mat_of_cols n vs \<in> carrier_mat n n" using mat_of_cols_carrier(1)[of n vs] vs(2) by simp
  have W: "mat_of_cols k ws \<in> carrier_mat k k" using mat_of_cols_carrier(1)[of k ws] ws(2) by simp
  let ?M = "four_block_mat (mat_of_cols n vs) (0\<^sub>m n k) (0\<^sub>m k n) (mat_of_cols k ws)"
  let ?N = "four_block_mat G (0\<^sub>m n k) (0\<^sub>m k n) H"
  have MN: "?M * ?N = 1\<^sub>m (n + k)"
    using mult_four_block_mat[OF V zero_carrier_mat zero_carrier_mat W G zero_carrier_mat zero_carrier_mat H]
    using V W G H VG WH right_mult_zero_mat[OF V, of k] right_mult_zero_mat[OF W, of n] by simp
  have NM: "?N * ?M = 1\<^sub>m (n + k)"
    using mult_four_block_mat[OF G zero_carrier_mat zero_carrier_mat H V zero_carrier_mat zero_carrier_mat W]
    using V W G H GV HW right_mult_zero_mat[OF G, of k] right_mult_zero_mat[OF H, of n] vs(2) ws(2) by simp
  have Mc: "?M \<in> carrier_mat (n + k) (n + k)" using V W by simp
  have Nc: "?N \<in> carrier_mat (n + k) (n + k)" using G H by simp
  have "invertible_mat ?M"
  proof -
    have "inverts_mat ?M ?N" unfolding inverts_mat_def using MN carrier_matD[OF Mc] by simp
    moreover have "inverts_mat ?N ?M" unfolding inverts_mat_def using NM carrier_matD[OF Nc] by simp
    moreover have "square_mat ?M" using carrier_matD[OF Mc] by simp
    ultimately show ?thesis unfolding invertible_mat_def by blast
  qed
  thus "invertible_mat (mat_of_cols (n + k) (direct_sum_basis n k vs ws))"
    unfolding direct_sum_basis_block[OF vs ws] .
qed

end
