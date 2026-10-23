(*  Title:   Day06_Tensor_Products.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 9 September 2011 (Day 6)
*)

theory Day06_Tensor_Products
  imports Day05_Positivity_Tests
begin

section \<open>Day 6 (9 September 2011): tensor products\<close>

text \<open>\begin{notesdef}
$B:X\times Y\to Z$ is \emph{bilinear} if $B(x_1+x_2,y)=B(x_1,y)+B(x_2,y)$,
$B(x,y_1+y_2)=B(x,y_1)+B(x,y_2)$ and $B(\lambda x,y)=B(x,\lambda y)=\lambda B(x,y)$.
\end{notesdef}
The tensor product $X\otimes Y$ is the span of elementary tensors $x\otimes y$ with the
universal property: every bilinear $B$ factors as $B(x,y)=L_B(x\otimes y)$ for a unique
linear $L_B$.  Key relations: $(x_1+x_2)\otimes y=x_1\otimes y+x_2\otimes y$,
$x\otimes(y_1+y_2)=x\otimes y_1+x\otimes y_2$,
$\lambda(x\otimes y)=(\lambda x)\otimes y=x\otimes(\lambda y)$.
\begin{notestheorem}
If $\{e_1,\dots,e_k\}$ and $\{f_1,\dots,f_m\}$ are bases of $X$ and $Y$, then
$\{e_i\otimes f_j\}$ is a basis of $X\otimes Y$; hence $\dim(X\otimes Y)=\dim X\cdot\dim Y$.
\end{notestheorem}
\begin{notesprop}
With bases as above, every $u\in X\otimes Y$ is uniquely $u=\sum_j x_j\otimes f_j$ with
$x_j\in X$, and uniquely $u=\sum_i e_i\otimes y_i$ with $y_i\in Y$; consequently
$X\otimes Y\cong X\oplus\cdots\oplus X$ ($m$ copies).
\end{notesprop}
\begin{notesdef}
The \emph{Schmidt rank} of $u\in X\otimes Y$ is the least number of elementary tensors in an
expression for $u$.
\end{notesdef}
The formalisation uses the concrete model: $\C^n\otimes\C^m=\C^{nm}$ with
$(v\otimes w)_{im+j}=v_iw_j$ (\<open>tensor_vec v w\<close> from the library).  The three key
relations are the bilinearity lemmas below; the product basis theorem is \<open>tensor_onb\<close>
(Day 7); the unique decomposition along a basis of $Y$ is not stated for vectors (its
operator analogue is in theory Day15\_Partial\_Traces).\<close>


lemma tensor_vec_dim:
  assumes vd: "dim_vec v = n" "dim_vec w = m"
  shows "dim_vec (tensor_vec v w) = n * m"
proof -
  have len_aux: "length (mult.vec_vec_Tensor (*) xs ys) = length xs * length ys"
    for xs ys :: "complex list"
    using mult.vec_vec_Tensor_length[of "1::complex" "(*)" xs ys]
    by (simp add: mult.intro)
  have len: "length (mult.vec_vec_Tensor (*) (list_of_vec v) (list_of_vec w)) =
      length (list_of_vec v) * length (list_of_vec w)"
    by (rule len_aux)
  show ?thesis
    using assms len by (simp add: tensor_vec_def)
qed


lemma tensor_vec_index:
  assumes "dim_vec v = n" "dim_vec w = m" "i < n * m"
  shows "tensor_vec v w $ i = v $ (i div m) * w $ (i mod m)"
proof -
  have m_pos: "m > 0" using assms(3) by (cases m) auto
  have n_pos: "n > 0" using assms(3) by (cases n) auto
  have lw_nonempty: "list_of_vec w \<noteq> []"
    using assms(2) m_pos by (metis length_greater_0_conv length_list_of_vec)
  have len_v: "length (list_of_vec v) = n" using assms(1) by simp
  have len_w: "length (list_of_vec w) = m" using assms(2) by simp
  have mult_inst: "Matrix_Tensor.mult (1::complex) (*)"
    by (simp add: Matrix_Tensor.mult_def)
  have elems: "\<forall>i. i < length (list_of_vec v) * length (list_of_vec w) \<longrightarrow>
     (mult.vec_vec_Tensor (*) (list_of_vec v) (list_of_vec w)) ! i =
        ((list_of_vec v) ! (i div length (list_of_vec w))) *
        ((list_of_vec w) ! (i mod length (list_of_vec w)))"
    using mult.vec_vec_Tensor_elements[OF mult_inst lw_nonempty,
        of "(list_of_vec v)"] by simp
  have i_bound: "i < length (list_of_vec v) * length (list_of_vec w)"
    using assms(3) len_v len_w by simp
  have div_bound: "i div m < n" using assms(3) less_mult_imp_div_less by blast
  have mod_bound: "i mod m < m" using m_pos by simp
  have len_tensor: "length (mult.vec_vec_Tensor (*) (list_of_vec v) (list_of_vec w)) = n * m"
    using len_v len_w mult.vec_vec_Tensor_length[OF mult_inst] by simp
  have "tensor_vec v w $ i =
      (mult.vec_vec_Tensor (*) (list_of_vec v) (list_of_vec w)) ! i"
    unfolding tensor_vec_def using assms(3) len_tensor
    by (simp add: vec_of_list_index)
  also have "\<dots> = (list_of_vec v) ! (i div m) * (list_of_vec w) ! (i mod m)"
    using elems i_bound len_w by simp
  also have "\<dots> = v $ (i div m) * w $ (i mod m)"
    using div_bound mod_bound assms(1,2) by (simp add: list_of_vec_index)
  finally show ?thesis .
qed


text \<open>In coordinates $(v\otimes w)_{im+j}=v_i\,w_j$, the first factor giving the major index; for
$v,w\in\C^2$,
\[ v\otimes w=(v_0w_0,\;v_0w_1,\;v_1w_0,\;v_1w_1). \]
Each entry is a product of one coordinate of each factor, so $\otimes$ is bilinear:\<close>

lemma tensor_vec_bilinear_left:
  assumes vd: "dim_vec v1 = n" "dim_vec v2 = n" "dim_vec w = m"
  shows "tensor_vec (v1 + v2) w = tensor_vec v1 w + tensor_vec v2 w"
proof -
  have v1_carrier: "v1 \<in> carrier_vec n"
    using vd(1) by (rule carrier_vecI)
  have v2_carrier: "v2 \<in> carrier_vec n"
    using vd(2) by (rule carrier_vecI)
  have w_carrier: "w \<in> carrier_vec m"
    using vd(3) by (rule carrier_vecI)

  have dim_lhs: "dim_vec (tensor_vec (v1 + v2) w) = n * m"
    using vd by (simp add: tensor_vec_dim)
  have dim_rhs: "dim_vec (tensor_vec v1 w + tensor_vec v2 w) = n * m"
    using vd by (simp add: tensor_vec_dim)

  show ?thesis
  proof
    show "dim_vec (tensor_vec (v1 + v2) w) =
          dim_vec (tensor_vec v1 w + tensor_vec v2 w)"
      using dim_lhs dim_rhs by simp
  next
    fix i
    assume i: "i < dim_vec (tensor_vec v1 w + tensor_vec v2 w)"
    then have i_bound: "i < n * m"
      using dim_rhs by simp
    let ?a = "i div m"
    let ?b = "i mod m"
    have split_index: "i = ?a * m + ?b"
      by presburger
    have a_bound: "?a < n"
      using i_bound less_mult_imp_div_less by blast
    have b_bound: "?b < m"
      by (metis gr0I i_bound less_zeroE mod_less_divisor mult_not_zero)


    have dim_v12: "dim_vec (v1 + v2) = n" using vd by simp
    have lhs_i:  "tensor_vec (v1 + v2) w $ i = ((v1 + v2) $ ?a) * (w $ ?b)"
      using tensor_vec_index[OF dim_v12 vd(3) i_bound] .
    also have "\<dots> = (v1 $ ?a * w $ ?b) + (v2 $ ?a * w $ ?b)"
      using vd a_bound b_bound by (simp add: algebra_simps)
    also have "\<dots> = (tensor_vec v1 w + tensor_vec v2 w) $ i"
    proof -
      have t1: "tensor_vec v1 w $ i = v1 $ ?a * w $ ?b"
        using tensor_vec_index[OF vd(1) vd(3) i_bound] .
      have t2: "tensor_vec v2 w $ i = v2 $ ?a * w $ ?b"
        using tensor_vec_index[OF vd(2) vd(3) i_bound] .
      have di_rhs: "i < dim_vec (tensor_vec v1 w + tensor_vec v2 w)"
        using dim_rhs i_bound by simp
      have dt1: "dim_vec (tensor_vec v1 w) = n * m" using vd by (simp add: tensor_vec_dim)
      have dt2: "dim_vec (tensor_vec v2 w) = n * m" using vd by (simp add: tensor_vec_dim)
      have "(tensor_vec v1 w + tensor_vec v2 w) $ i = tensor_vec v1 w $ i + tensor_vec v2 w $ i"
        using dt1 dt2 i_bound by simp
      with t1 t2 show ?thesis by simp
    qed
    finally show "tensor_vec (v1 + v2) w $ i =
                  (tensor_vec v1 w + tensor_vec v2 w) $ i" .
  qed
qed





lemma tensor_vec_bilinear_right:
  assumes vd: "dim_vec v = n" "dim_vec w1 = m" "dim_vec w2 = m"
  shows "tensor_vec v (w1 + w2) = tensor_vec v w1 + tensor_vec v w2"
proof -
  have v_carrier: "v \<in> carrier_vec n"
    using vd(1) by (rule carrier_vecI)
  have w1_carrier: "w1 \<in> carrier_vec m"
    using vd(2) by (rule carrier_vecI)
  have w2_carrier: "w2 \<in> carrier_vec m"
    using vd(3) by (rule carrier_vecI)

  have dim_lhs: "dim_vec (tensor_vec v (w1 + w2)) = n * m"
    using vd by (simp add: tensor_vec_dim)
  have dim_rhs: "dim_vec (tensor_vec v w1 + tensor_vec v w2) = n * m"
    using vd by (simp add: tensor_vec_dim)

  show ?thesis
  proof
    show "dim_vec (tensor_vec v (w1 + w2)) =
          dim_vec (tensor_vec v w1 + tensor_vec v w2)"
      using dim_lhs dim_rhs by simp
  next
    fix i
    assume i: "i < dim_vec (tensor_vec v w1 + tensor_vec v w2)"
    then have i_bound: "i < n * m"
      using dim_rhs by simp
    let ?a = "i div m"
    let ?b = "i mod m"
    have split_index: "i = ?a * m + ?b"
      by presburger
    have a_bound: "?a < n"
      using i_bound less_mult_imp_div_less by blast
    have b_bound: "?b < m"
      by (metis i_bound mod_by_0 mod_less_divisor mod_mult_self2_is_0 not_gr0)
    have dim_w12: "dim_vec (w1 + w2) = m" using vd by simp
    have lhs_i:
      "tensor_vec v (w1 + w2) $ i = (v $ ?a) * ((w1 + w2) $ ?b)"
      using tensor_vec_index[OF vd(1) dim_w12 i_bound] .
    also have "\<dots> = (v $ ?a * w1 $ ?b) + (v $ ?a * w2 $ ?b)"
      using vd a_bound b_bound by (simp add: algebra_simps)
    also have "\<dots> = (tensor_vec v w1 + tensor_vec v w2) $ i"
    proof -
      have t1: "tensor_vec v w1 $ i = v $ ?a * w1 $ ?b"
        using tensor_vec_index[OF vd(1) vd(2) i_bound] .
      have t2: "tensor_vec v w2 $ i = v $ ?a * w2 $ ?b"
        using tensor_vec_index[OF vd(1) vd(3) i_bound] .
      have dt1: "dim_vec (tensor_vec v w1) = n * m" using vd by (simp add: tensor_vec_dim)
      have dt2: "dim_vec (tensor_vec v w2) = n * m" using vd by (simp add: tensor_vec_dim)
      have "(tensor_vec v w1 + tensor_vec v w2) $ i = tensor_vec v w1 $ i + tensor_vec v w2 $ i"
        using dt1 dt2 i_bound by simp
      with t1 t2 show ?thesis by simp
    qed
    finally show "tensor_vec v (w1 + w2) $ i =
                  (tensor_vec v w1 + tensor_vec v w2) $ i" .
  qed
qed

lemma tensor_vec_smult_left:
  assumes vd: "dim_vec v = n" "dim_vec w = m"
  shows "tensor_vec (\<alpha> \<cdot>\<^sub>v v) w = \<alpha> \<cdot>\<^sub>v tensor_vec v w"
proof
  have dim_av: "dim_vec (\<alpha> \<cdot>\<^sub>v v) = n" using vd by simp
  have dim_lhs: "dim_vec (tensor_vec (\<alpha> \<cdot>\<^sub>v v) w) = n * m"
    using dim_av vd(2) by (simp add: tensor_vec_dim)
  have dim_rhs: "dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w) = n * m"
    using vd by (simp add: tensor_vec_dim)
  show "dim_vec (tensor_vec (\<alpha> \<cdot>\<^sub>v v) w) = dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w)"
    using dim_lhs dim_rhs by simp
next
  fix i
  assume i: "i < dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w)"
  have dim_tvw: "dim_vec (tensor_vec v w) = n * m" using vd by (simp add: tensor_vec_dim)
  have i_bound: "i < n * m" using i dim_tvw by simp
  have dim_av: "dim_vec (\<alpha> \<cdot>\<^sub>v v) = n" using vd by simp
  let ?a = "i div m" let ?b = "i mod m"
  have a_bound: "?a < n" using i_bound less_mult_imp_div_less by blast
  have lhs: "tensor_vec (\<alpha> \<cdot>\<^sub>v v) w $ i = (\<alpha> \<cdot>\<^sub>v v) $ ?a * w $ ?b"
    using tensor_vec_index[OF dim_av vd(2) i_bound] .
  also have "\<dots> = \<alpha> * (v $ ?a * w $ ?b)"
    using a_bound vd by simp
  also have "\<dots> = \<alpha> * (tensor_vec v w $ i)"
    using tensor_vec_index[OF vd i_bound] by simp
  also have "\<dots> = (\<alpha> \<cdot>\<^sub>v tensor_vec v w) $ i"
    using i by simp
  finally show "tensor_vec (\<alpha> \<cdot>\<^sub>v v) w $ i = (\<alpha> \<cdot>\<^sub>v tensor_vec v w) $ i" .
qed

lemma tensor_vec_smult_right:
  assumes vd: "dim_vec v = n" "dim_vec w = m"
  shows "tensor_vec v (\<alpha> \<cdot>\<^sub>v w) = \<alpha> \<cdot>\<^sub>v tensor_vec v w"
proof
  have dim_aw: "dim_vec (\<alpha> \<cdot>\<^sub>v w) = m" using vd by simp
  have dim_lhs: "dim_vec (tensor_vec v (\<alpha> \<cdot>\<^sub>v w)) = n * m"
    using vd(1) dim_aw by (simp add: tensor_vec_dim)
  have dim_rhs: "dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w) = n * m"
    using vd by (simp add: tensor_vec_dim)
  show "dim_vec (tensor_vec v (\<alpha> \<cdot>\<^sub>v w)) = dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w)"
    using dim_lhs dim_rhs by simp
next
  fix i
  assume i: "i < dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w)"
  have dim_tvw: "dim_vec (tensor_vec v w) = n * m" using vd by (simp add: tensor_vec_dim)
  have i_bound: "i < n * m" using i dim_tvw by simp
  have dim_aw: "dim_vec (\<alpha> \<cdot>\<^sub>v w) = m" using vd by simp
  let ?a = "i div m" let ?b = "i mod m"
  have m_pos: "m > 0" using i_bound by (cases m) auto
  have b_bound: "?b < m" using m_pos by simp
  have lhs: "tensor_vec v (\<alpha> \<cdot>\<^sub>v w) $ i = v $ ?a * (\<alpha> \<cdot>\<^sub>v w) $ ?b"
    using tensor_vec_index[OF vd(1) dim_aw i_bound] .
  also have "\<dots> = \<alpha> * (v $ ?a * w $ ?b)"
    using b_bound vd by simp
  also have "\<dots> = \<alpha> * (tensor_vec v w $ i)"
    using tensor_vec_index[OF vd i_bound] by simp
  also have "\<dots> = (\<alpha> \<cdot>\<^sub>v tensor_vec v w) $ i"
    using i by simp
  finally show "tensor_vec v (\<alpha> \<cdot>\<^sub>v w) $ i = (\<alpha> \<cdot>\<^sub>v tensor_vec v w) $ i" .
qed


text \<open>The Schmidt rank, the least length of a representation by elementary tensors.  It is
\<open>LEAST\<close>, not \<open>Min\<close> of the set of lengths: that set is infinite (zero terms can be added),
and \<open>Min\<close> is unspecified on infinite sets.  Its properties (rank $1$ iff a product state) are
in theory Day06\_Schmidt\_Rank.\<close>

definition schmidt_rank :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> nat" where
  "schmidt_rank u m \<equiv>
     LEAST k. \<exists>vs :: complex Matrix.vec list. \<exists>ws :: complex Matrix.vec list.
              length vs = k \<and> length ws = k \<and>
              (\<forall>i < k. dim_vec (vs ! i) = dim_vec u div m) \<and>
              (\<forall>i < k. dim_vec (ws ! i) = m) \<and>
              u = foldr (\<lambda>(v,w) acc. tensor_vec v w + acc)
                        (zip vs ws) (0\<^sub>v (dim_vec u))"

end
