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
proved below.\<close>

definition schmidt_rank :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> nat" where
  "schmidt_rank u m \<equiv>
     LEAST k. \<exists>vs :: complex Matrix.vec list. \<exists>ws :: complex Matrix.vec list.
              length vs = k \<and> length ws = k \<and>
              (\<forall>i < k. dim_vec (vs ! i) = dim_vec u div m) \<and>
              (\<forall>i < k. dim_vec (ws ! i) = m) \<and>
              u = foldr (\<lambda>(v,w) acc. tensor_vec v w + acc)
                        (zip vs ws) (0\<^sub>v (dim_vec u))"

lemma tensor_unit_vec:
  assumes i: "i < n" and j: "j < m"
  shows "tensor_vec (unit_vec n i) (unit_vec m j) = (unit_vec (n * m) (i * m + j) :: complex Matrix.vec)"
proof (rule eq_vecI)
  have d: "dim_vec (tensor_vec (unit_vec n i) (unit_vec m j) :: complex Matrix.vec) = n * m"
    by (rule tensor_vec_dim) simp_all
  fix r assume "r < dim_vec (unit_vec (n * m) (i * m + j) :: complex Matrix.vec)"
  hence r: "r < n * m" by simp
  have m: "0 < m" using j by simp
  have rd: "r div m < n" using r by (simp add: less_mult_imp_div_less)
  have e: "(r div m = i \<and> r mod m = j) \<longleftrightarrow> r = i * m + j"
  proof
    assume "r div m = i \<and> r mod m = j" thus "r = i * m + j" using div_mult_mod_eq[of r m] by simp
  next
    assume "r = i * m + j" thus "r div m = i \<and> r mod m = j" using j m by simp
  qed
  have "tensor_vec (unit_vec n i) (unit_vec m j) $ r = unit_vec n i $ (r div m) * unit_vec m j $ (r mod m)"
    by (rule tensor_vec_index) (use r in simp_all)
  also have "\<dots> = (if r div m = i \<and> r mod m = j then 1 else 0)" using rd m by (simp add: unit_vec_def)
  also have "\<dots> = unit_vec (n * m) (i * m + j) $ r" using e r by (simp add: unit_vec_def)
  finally show "tensor_vec (unit_vec n i) (unit_vec m j) $ r = unit_vec (n * m) (i * m + j) $ r" .
qed (simp add: tensor_vec_dim)

subsection \<open>The universal properties in the Kronecker model\<close>

text \<open>D6-1: for $\C^n\otimes\C^m=\C^{nm}$ with $(v\otimes w)_{im+j}=v_iw_j$, every bilinear map
$\beta:\C^n\times\C^m\to\C^p$ factors as $\beta(v,w)=L(v\otimes w)$ for a unique linear $L$.  First
for bilinear forms ($p=1$), then coordinatewise.\<close>

definition bilinear_on :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex) \<Rightarrow> bool" where
  "bilinear_on n m \<beta> \<longleftrightarrow>
     (\<forall>v1 v2 w. dim_vec v1 = n \<longrightarrow> dim_vec v2 = n \<longrightarrow> dim_vec w = m \<longrightarrow> \<beta> (v1 + v2) w = \<beta> v1 w + \<beta> v2 w)
   \<and> (\<forall>v w1 w2. dim_vec v = n \<longrightarrow> dim_vec w1 = m \<longrightarrow> dim_vec w2 = m \<longrightarrow> \<beta> v (w1 + w2) = \<beta> v w1 + \<beta> v w2)
   \<and> (\<forall>a v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> \<beta> (a \<cdot>\<^sub>v v) w = a * \<beta> v w \<and> \<beta> v (a \<cdot>\<^sub>v w) = a * \<beta> v w)"

definition linear_on :: "nat \<Rightarrow> (complex Matrix.vec \<Rightarrow> complex) \<Rightarrow> bool" where
  "linear_on K L \<longleftrightarrow> (\<forall>x y. dim_vec x = K \<longrightarrow> dim_vec y = K \<longrightarrow> L (x + y) = L x + L y)
                     \<and> (\<forall>a x. dim_vec x = K \<longrightarrow> L (a \<cdot>\<^sub>v x) = a * L x)"

definition trunc_vec :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "trunc_vec v k = Matrix.vec (dim_vec v) (\<lambda>i. if i < k then v $ i else 0)"

lemma dim_trunc_vec [simp]: "dim_vec (trunc_vec v k) = dim_vec v" by (simp add: trunc_vec_def)

lemma trunc_vec_full: "trunc_vec v (dim_vec v) = v" by (rule eq_vecI) (simp_all add: trunc_vec_def)

lemma trunc_vec_Suc: "k < dim_vec v \<Longrightarrow> trunc_vec v (Suc k) = trunc_vec v k + v $ k \<cdot>\<^sub>v unit_vec (dim_vec v) k"
  by (rule eq_vecI) (auto simp: trunc_vec_def unit_vec_def less_Suc_eq)

lemma trunc_vec_zero: "trunc_vec v 0 = 0\<^sub>v (dim_vec v)" by (rule eq_vecI) (simp_all add: trunc_vec_def)

text \<open>A linear map is determined by its values on the unit vectors.\<close>

lemma linear_on_zero: "linear_on K L \<Longrightarrow> L (0\<^sub>v K) = 0"
proof -
  assume l: "linear_on K L"
  have "L ((0::complex) \<cdot>\<^sub>v 0\<^sub>v K) = (0::complex) * L (0\<^sub>v K)" using l unfolding linear_on_def by simp
  moreover have "(0::complex) \<cdot>\<^sub>v 0\<^sub>v K = 0\<^sub>v K" by (rule eq_vecI) simp_all
  ultimately show ?thesis by simp
qed

lemma linear_on_expand:
  assumes l: "linear_on K L" and x: "dim_vec x = K"
  shows "L x = (\<Sum>k<K. x $ k * L (unit_vec K k))"
proof -
  have "k \<le> K \<Longrightarrow> L (trunc_vec x k) = (\<Sum>i<k. x $ i * L (unit_vec K i))" for k
  proof (induction k)
    case 0 thus ?case using linear_on_zero[OF l] x by (simp add: trunc_vec_zero)
  next
    case (Suc k)
    have "L (trunc_vec x (Suc k)) = L (trunc_vec x k) + L (x $ k \<cdot>\<^sub>v unit_vec K k)"
      using trunc_vec_Suc[of k x] Suc.prems x l unfolding linear_on_def by simp
    also have "L (x $ k \<cdot>\<^sub>v unit_vec K k) = x $ k * L (unit_vec K k)" using l unfolding linear_on_def by simp
    finally show ?case using Suc by simp
  qed
  from this[of K] show ?thesis using trunc_vec_full[of x] x by simp
qed

text \<open>A bilinear map is determined by its values on pairs of unit vectors.\<close>

text \<open>A bilinear $\beta$ is determined by its values on pairs of basis vectors:
\[ \beta(v,w)=\sum_{i,j}v_iw_j\,\beta(e_i,e_j)=\sum_{i,j}(v\otimes w)_{im+j}\,\beta(e_i,e_j), \]
so $L(x)=\sum_kx_k\,\beta(e_{k\div m},e_{k\bmod m})$ is the unique linear map with $L(v\otimes w)=\beta(v,w)$.\<close>

lemma bilinear_on_expand:
  assumes b: "bilinear_on n m \<beta>" and v: "dim_vec v = n" and w: "dim_vec w = m"
  shows "\<beta> v w = (\<Sum>i<n. \<Sum>j<m. (v $ i * w $ j) * \<beta> (unit_vec n i) (unit_vec m j))"
proof -
  have lv: "linear_on n (\<lambda>x. \<beta> x w')" if w': "dim_vec w' = m" for w'
    using b w' unfolding bilinear_on_def linear_on_def by simp
  have lw: "linear_on m (\<lambda>y. \<beta> u y)" if u: "dim_vec u = n" for u
    using b u unfolding bilinear_on_def linear_on_def by simp
  have "\<beta> v w = (\<Sum>i<n. v $ i * \<beta> (unit_vec n i) w)" by (rule linear_on_expand[OF lv[OF w] v])
  also have "\<dots> = (\<Sum>i<n. v $ i * (\<Sum>j<m. w $ j * \<beta> (unit_vec n i) (unit_vec m j)))"
    by (rule sum.cong[OF refl]) (simp add: linear_on_expand[OF lw w])
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<m. (v $ i * w $ j) * \<beta> (unit_vec n i) (unit_vec m j))"
    by (simp add: sum_distrib_left Groups.mult.assoc)
  finally show ?thesis .
qed

lemma sum_div_mod:
  fixes n m :: nat and g :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>k<n * m. g (k div m) (k mod m)) = (\<Sum>i<n. \<Sum>j<m. g i j)"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  let ?f = "\<lambda>k. g (k div m) (k mod m)"
  have u: "{..<Suc n * m} = {..<n * m} \<union> {n * m..<n * m + m}" by auto
  have "(\<Sum>k<Suc n * m. ?f k) = (\<Sum>k\<in>{..<n * m} \<union> {n * m..<n * m + m}. ?f k)" unfolding u ..
  also have "\<dots> = (\<Sum>k<n * m. ?f k) + (\<Sum>k\<in>{n * m..<n * m + m}. ?f k)" by (rule sum.union_disjoint) auto
  also have "(\<Sum>k\<in>{n * m..<n * m + m}. ?f k) = (\<Sum>j<m. ?f (n * m + j))"
  proof -
    have "{n * m..<n * m + m} = (\<lambda>j. n * m + j) ` {..<m}"
    proof
      show "{n * m..<n * m + m} \<subseteq> (\<lambda>j. n * m + j) ` {..<m}"
      proof
        fix x assume x: "x \<in> {n * m..<n * m + m}"
        hence "x = n * m + (x - n * m)" "x - n * m \<in> {..<m}" by auto
        thus "x \<in> (\<lambda>j. n * m + j) ` {..<m}" by (rule image_eqI)
      qed
    qed auto
    moreover have "inj_on (\<lambda>j. n * m + j) {..<m}" by (simp add: inj_on_def)
    ultimately show ?thesis by (simp add: sum.reindex)
  qed
  also have "(\<Sum>j<m. ?f (n * m + j)) = (\<Sum>j<m. g n j)" by (rule sum.cong[OF refl]) auto
  finally show ?case using Suc by simp
qed

text \<open>The same for two indices at once.\<close>

lemma sum_div_mod2:
  fixes g :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>r<n * m. \<Sum>s<n' * m'. g (r div m) (r mod m) (s div m') (s mod m')) =
         (\<Sum>i<n. \<Sum>a<m. \<Sum>j<n'. \<Sum>b<m'. g i a j b)"
proof -
  have inner: "(\<Sum>s<n' * m'. g i a (s div m') (s mod m')) = (\<Sum>j<n'. \<Sum>b<m'. g i a j b)" for i a
    by (rule sum_div_mod)
  show ?thesis unfolding inner by (rule sum_div_mod[where g = "\<lambda>i a. \<Sum>j<n'. \<Sum>b<m'. g i a j b"])
qed

theorem tensor_universal_property:
  assumes b: "bilinear_on n m \<beta>"
  shows "\<exists>L. linear_on (n * m) L \<and> (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L (tensor_vec v w) = \<beta> v w)
           \<and> (\<forall>L'. linear_on (n * m) L' \<and> (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L' (tensor_vec v w) = \<beta> v w)
                  \<longrightarrow> (\<forall>x. dim_vec x = n * m \<longrightarrow> L' x = L x))"
proof -
  define L where "L x = (\<Sum>k<n * m. x $ k * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)))" for x
  have lin: "linear_on (n * m) L"
    unfolding linear_on_def L_def by (auto simp: distrib_right sum_distrib_left sum.distrib Groups.mult.assoc)
  have el: "L (tensor_vec v w) = \<beta> v w" if v: "dim_vec v = n" and w: "dim_vec w = m" for v w
  proof -
    have "L (tensor_vec v w) = (\<Sum>k<n * m. (v $ (k div m) * w $ (k mod m)) * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)))"
      unfolding L_def by (rule sum.cong[OF refl]) (simp add: tensor_vec_index[OF v w])
    also have "\<dots> = (\<Sum>i<n. \<Sum>j<m. (v $ i * w $ j) * \<beta> (unit_vec n i) (unit_vec m j))" by (rule sum_div_mod)
    also have "\<dots> = \<beta> v w" by (rule bilinear_on_expand[OF b v w, symmetric])
    finally show ?thesis .
  qed
  have un: "L' x = L x" if l': "linear_on (n * m) L'" and e': "\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L' (tensor_vec v w) = \<beta> v w"
    and x: "dim_vec x = n * m" for L' x
  proof -
    have "L' x = (\<Sum>k<n * m. x $ k * L' (unit_vec (n * m) k))" by (rule linear_on_expand[OF l' x])
    also have "\<dots> = L x" unfolding L_def
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {..<n * m}"
      hence k: "k < n * m" by simp
      have m0: "0 < m" using k by (cases m) auto
      have i: "k div m < n" using k by (simp add: less_mult_imp_div_less)
      have j: "k mod m < m" using m0 by simp
      have "unit_vec (n * m) k = tensor_vec (unit_vec n (k div m)) (unit_vec m (k mod m))"
        using tensor_unit_vec[OF i j] by (simp add: Groups.mult.commute)
      thus "x $ k * L' (unit_vec (n * m) k) = x $ k * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m))"
        using e' by simp
    qed
    finally show ?thesis .
  qed
  show ?thesis using lin el un by blast
qed

definition bilinear_vec_on :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec) \<Rightarrow> bool" where
  "bilinear_vec_on n m p \<beta> \<longleftrightarrow>
     (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> dim_vec (\<beta> v w) = p)
   \<and> (\<forall>v1 v2 w. dim_vec v1 = n \<longrightarrow> dim_vec v2 = n \<longrightarrow> dim_vec w = m \<longrightarrow> \<beta> (v1 + v2) w = \<beta> v1 w + \<beta> v2 w)
   \<and> (\<forall>v w1 w2. dim_vec v = n \<longrightarrow> dim_vec w1 = m \<longrightarrow> dim_vec w2 = m \<longrightarrow> \<beta> v (w1 + w2) = \<beta> v w1 + \<beta> v w2)
   \<and> (\<forall>a v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> \<beta> (a \<cdot>\<^sub>v v) w = a \<cdot>\<^sub>v \<beta> v w \<and> \<beta> v (a \<cdot>\<^sub>v w) = a \<cdot>\<^sub>v \<beta> v w)"

definition linear_vec_on :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.vec \<Rightarrow> complex Matrix.vec) \<Rightarrow> bool" where
  "linear_vec_on K p L \<longleftrightarrow> (\<forall>x. dim_vec x = K \<longrightarrow> dim_vec (L x) = p)
     \<and> (\<forall>x y. dim_vec x = K \<longrightarrow> dim_vec y = K \<longrightarrow> L (x + y) = L x + L y)
     \<and> (\<forall>a x. dim_vec x = K \<longrightarrow> L (a \<cdot>\<^sub>v x) = a \<cdot>\<^sub>v L x)"

lemma bilinear_vec_coord: "bilinear_vec_on n m p \<beta> \<Longrightarrow> r < p \<Longrightarrow> bilinear_on n m (\<lambda>v w. \<beta> v w $ r)"
  unfolding bilinear_vec_on_def bilinear_on_def by auto

lemma linear_vec_coord: "linear_vec_on K p L \<Longrightarrow> r < p \<Longrightarrow> linear_on K (\<lambda>x. L x $ r)"
  unfolding linear_vec_on_def linear_on_def by auto

theorem tensor_universal_property_vec:
  assumes b: "bilinear_vec_on n m p \<beta>"
  shows "\<exists>L. linear_vec_on (n * m) p L \<and> (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L (tensor_vec v w) = \<beta> v w)
           \<and> (\<forall>L'. linear_vec_on (n * m) p L' \<and> (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L' (tensor_vec v w) = \<beta> v w)
                  \<longrightarrow> (\<forall>x. dim_vec x = n * m \<longrightarrow> L' x = L x))"
proof -
  define L where "L x = Matrix.vec p (\<lambda>r. \<Sum>k<n * m. x $ k * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)) $ r)" for x
  have dL: "dim_vec (L x) = p" for x by (simp add: L_def)
  have lin: "linear_vec_on (n * m) p L"
    unfolding linear_vec_on_def
    by (auto simp: dL L_def distrib_right sum_distrib_left sum.distrib Groups.mult.assoc intro!: eq_vecI)
  have el: "L (tensor_vec v w) = \<beta> v w" if v: "dim_vec v = n" and w: "dim_vec w = m" for v w
  proof (rule eq_vecI)
    have db: "dim_vec (\<beta> v w) = p" using b v w unfolding bilinear_vec_on_def by simp
    show "dim_vec (L (tensor_vec v w)) = dim_vec (\<beta> v w)" using db dL by simp
    fix r assume "r < dim_vec (\<beta> v w)"
    hence r: "r < p" using db by simp
    note sc = bilinear_vec_coord[OF b r]
    have "L (tensor_vec v w) $ r = (\<Sum>k<n * m. (v $ (k div m) * w $ (k mod m)) * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)) $ r)"
      unfolding L_def using r by (simp add: tensor_vec_index[OF v w])
    also have "\<dots> = (\<Sum>i<n. \<Sum>j<m. (v $ i * w $ j) * \<beta> (unit_vec n i) (unit_vec m j) $ r)" by (rule sum_div_mod)
    also have "\<dots> = \<beta> v w $ r" by (rule bilinear_on_expand[OF sc v w, symmetric])
    finally show "L (tensor_vec v w) $ r = \<beta> v w $ r" .
  qed
  have un: "L' x = L x" if l': "linear_vec_on (n * m) p L'" and e': "\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L' (tensor_vec v w) = \<beta> v w"
    and x: "dim_vec x = n * m" for L' x
  proof (rule eq_vecI)
    show "dim_vec (L' x) = dim_vec (L x)" using l' x dL unfolding linear_vec_on_def by simp
    fix r assume "r < dim_vec (L x)"
    hence r: "r < p" using dL by simp
    have "L' x $ r = (\<Sum>k<n * m. x $ k * L' (unit_vec (n * m) k) $ r)" by (rule linear_on_expand[OF linear_vec_coord[OF l' r] x])
    also have "\<dots> = L x $ r" unfolding L_def using r
    proof (simp, intro sum.cong refl)
      fix k assume "k \<in> {..<n * m}"
      hence k: "k < n * m" by simp
      have m0: "0 < m" using k by (cases m) auto
      have i: "k div m < n" using k by (simp add: less_mult_imp_div_less)
      have j: "k mod m < m" using m0 by simp
      have "unit_vec (n * m) k = tensor_vec (unit_vec n (k div m)) (unit_vec m (k mod m))"
        using tensor_unit_vec[OF i j] by (simp add: Groups.mult.commute)
      thus "x $ k * L' (unit_vec (n * m) k) $ r = x $ k * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)) $ r"
        using e' by simp
    qed
    finally show "L' x $ r = L x $ r" .
  qed
  show ?thesis using lin el un by blast
qed

subsection \<open>Coordinates in a tensor product\<close>

text \<open>$\sum_j x_j\otimes y_j$ in $\C^N$, written as in \<^const>\<open>schmidt_rank\<close>.\<close>

definition tensor_combination :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec" where
  "tensor_combination N xs ys = foldr (\<lambda>(x,y) acc. tensor_vec x y + acc) (zip xs ys) (0\<^sub>v N)"

lemma tensor_combination_dim [simp]: "dim_vec (tensor_combination N xs ys) = N"
proof (induction xs arbitrary: ys)
  case (Cons x xs) thus ?case by (cases ys) (simp_all add: tensor_combination_def)
qed (simp add: tensor_combination_def)

lemma tensor_combination_index:
  assumes "\<forall>x \<in> set xs. dim_vec x = k" "\<forall>y \<in> set ys. dim_vec y = m" "length xs = length ys" "p < k * m"
  shows "tensor_combination (k * m) xs ys $ p = (\<Sum>j<length xs. xs ! j $ (p div m) * ys ! j $ (p mod m))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil thus ?case by (simp add: tensor_combination_def)
next
  case (Cons x xs)
  then obtain y ys' where ys: "ys = y # ys'" by (cases ys) auto
  have IH: "tensor_combination (k * m) xs ys' $ p = (\<Sum>j<length xs. xs ! j $ (p div m) * ys' ! j $ (p mod m))"
    using Cons.IH[of ys'] Cons.prems ys by simp
  have "tensor_combination (k * m) (x # xs) ys = tensor_vec x y + tensor_combination (k * m) xs ys'"
    unfolding ys tensor_combination_def by simp
  hence "tensor_combination (k * m) (x # xs) ys $ p = tensor_vec x y $ p + tensor_combination (k * m) xs ys' $ p"
    using Cons.prems by simp
  also have "tensor_vec x y $ p = x $ (p div m) * y $ (p mod m)"
    using Cons.prems ys by (simp add: tensor_vec_index)
  finally show ?case unfolding IH ys length_Cons sum.lessThan_Suc_shift by simp
qed

text \<open>A vector $u\in\C^k\otimes\C^m$ has $k\,m$ entries: the coefficient of $e_i\otimes e_l$ sits at
position $i\,m+l$.  Read row by row, $u$ is a $k\times m$ matrix; for $k=2$, $m=3$,
\[
  u=(u_0,u_1,u_2,u_3,u_4,u_5)\quad\longmapsto\quad
  \begin{pmatrix}u_0&u_1&u_2\\ u_3&u_4&u_5\end{pmatrix}.
\]
The columns are the parts of $u$ along the basis of the second factor, the rows those along the
basis of the first:
\[
  u=(u_0,u_3)\otimes e_0+(u_1,u_4)\otimes e_1+(u_2,u_5)\otimes e_2
   =e_0\otimes(u_0,u_1,u_2)+e_1\otimes(u_3,u_4,u_5).
\]\<close>

definition vec_to_mat :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "vec_to_mat k m u = Matrix.mat k m (\<lambda>(i, l). u $ (i * m + l))"

lemma vec_to_mat_carrier [simp]: "vec_to_mat k m u \<in> carrier_mat k m"
  by (simp add: vec_to_mat_def)

lemma vec_to_mat_dims [simp]: "dim_row (vec_to_mat k m u) = k" "dim_col (vec_to_mat k m u) = m"
  by (simp_all add: vec_to_mat_def)

lemma vec_to_mat_index [simp]: "i < k \<Longrightarrow> l < m \<Longrightarrow> vec_to_mat k m u $$ (i, l) = u $ (i * m + l)"
  by (simp add: vec_to_mat_def)

lemma col_vec_to_mat: "l < m \<Longrightarrow> Matrix.col (vec_to_mat k m u) l = Matrix.vec k (\<lambda>i. u $ (i * m + l))"
  by (auto simp: vec_to_mat_def)

text \<open>Conversely, reading a matrix row by row gives a vector, and \<^const>\<open>vec_to_mat\<close> undoes this:
\[
  \begin{pmatrix}a&b&c\\ d&e&f\end{pmatrix}\quad\longmapsto\quad(a,b,c,d,e,f).
\]\<close>

definition mat_to_vec :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec" where
  "mat_to_vec c = Matrix.vec (dim_row c * dim_col c) (\<lambda>k. c $$ (k div dim_col c, k mod dim_col c))"

lemma vec_to_mat_mat_to_vec: "c \<in> carrier_mat K1 K2 \<Longrightarrow> vec_to_mat K1 K2 (mat_to_vec c) = c"
proof (rule eq_matI)
  fix i j assume c: "c \<in> carrier_mat K1 K2" and ij: "i < dim_row c" "j < dim_col c"
  have j: "j < K2" using c ij by simp
  have "i * K2 + j < K1 * K2"
  proof -
    have "i * K2 + j < i * K2 + K2" using j by simp
    also have "\<dots> = Suc i * K2" by simp
    also have "\<dots> \<le> K1 * K2" using c ij by (intro mult_le_mono1) simp
    finally show ?thesis .
  qed
  thus "vec_to_mat K1 K2 (mat_to_vec c) $$ (i, j) = c $$ (i, j)" using c ij j by (simp add: vec_to_mat_def mat_to_vec_def carrier_matD[OF c])
qed (auto simp: vec_to_mat_def)

lemma dim_mat_to_vec: "c \<in> carrier_mat K1 K2 \<Longrightarrow> dim_vec (mat_to_vec c) = K1 * K2" by (simp add: mat_to_vec_def carrier_matD)

lemma mat_to_vec_index:
  assumes c: "c \<in> carrier_mat K1 K2" and i: "i < K1" and j: "j < K2"
  shows "mat_to_vec c $ (i * K2 + j) = c $$ (i, j)"
proof -
  have "i * K2 + j < K1 * K2"
  proof -
    have "i * K2 + j < Suc i * K2" using j by simp
    also have "\<dots> \<le> K1 * K2" using i by (intro mult_le_mono1) simp
    finally show ?thesis .
  qed
  thus ?thesis using j by (simp add: mat_to_vec_def carrier_matD[OF c])
qed

text \<open>For other bases the matrix is multiplied by the inverse basis matrix.  If $f_1,\dots,f_m$ is
a basis of $\C^m$ with column matrix $F$ and $G=F^{-1}$, then $u=\sum_jx_j\otimes f_j$ says $U=XF^T$,
where $U$ is the matrix of $u$ and $X$ has the columns $x_j$; so the $x_j$ are the columns of
$UG^T$.  In the first factor, with $H$ the inverse of the column matrix of $e_1,\dots,e_k$,
$u=\sum_ie_i\otimes y_i$ has $y_i$ the rows of $HU$.\<close>

lemma right_coordinates_index:
  assumes G: "G \<in> carrier_mat m m" and "i < k" "j < m"
  shows "Matrix.col (vec_to_mat k m u * G\<^sup>T) j $ i = (\<Sum>l<m. u $ (i * m + l) * G $$ (j,l))"
  using assms by (simp add: scalar_prod_def vec_to_mat_def carrier_matD[OF G] atLeast0LessThan)

lemma left_coordinates_index:
  assumes H: "H \<in> carrier_mat k k" and "i < k" "l < m"
  shows "Matrix.row (H * vec_to_mat k m u) i $ l = (\<Sum>r<k. H $$ (i,r) * u $ (r * m + l))"
  using assms by (simp add: scalar_prod_def vec_to_mat_def carrier_matD[OF H] atLeast0LessThan)

lemma inv_entry_left:
  fixes fs :: "complex Matrix.vec list"
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and G: "G \<in> carrier_mat m m"
      and GF: "G * mat_of_cols m fs = 1\<^sub>m m" and j: "j < m" and j': "j' < m"
  shows "(\<Sum>l<m. fs ! j' $ l * G $$ (j,l)) = (if j = j' then 1 else 0)"
proof -
  have "(G * mat_of_cols m fs) $$ (j,j') = (\<Sum>l<m. G $$ (j,l) * fs ! j' $ l)"
    using G j j' fd by (simp add: scalar_prod_def mat_of_cols_def atLeast0LessThan)
  moreover have "(\<Sum>l<m. fs ! j' $ l * G $$ (j,l)) = (\<Sum>l<m. G $$ (j,l) * fs ! j' $ l)"
    by (simp add: mult.commute)
  ultimately show ?thesis unfolding GF using j j' by simp
qed

lemma inv_entry_right:
  fixes fs :: "complex Matrix.vec list"
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and G: "G \<in> carrier_mat m m"
      and FG: "mat_of_cols m fs * G = 1\<^sub>m m" and r: "r < m" and l: "l < m"
  shows "(\<Sum>j<m. fs ! j $ r * G $$ (j,l)) = (if r = l then 1 else 0)"
proof -
  have "(mat_of_cols m fs * G) $$ (r,l) = (\<Sum>j<m. fs ! j $ r * G $$ (j,l))"
    using G r l fd by (simp add: scalar_prod_def mat_of_cols_def atLeast0LessThan)
  thus ?thesis unfolding FG using r l by simp
qed

lemma right_coordinates_unique:
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and G: "G \<in> carrier_mat m m"
      and GF: "G * mat_of_cols m fs = 1\<^sub>m m"
      and xs: "length xs = m" "\<forall>x \<in> set xs. dim_vec x = k" and j: "j < m"
  shows "Matrix.col (vec_to_mat k m (tensor_combination (k * m) xs fs) * G\<^sup>T) j = xs ! j"
proof (rule eq_vecI)
  have xd: "dim_vec (xs ! j) = k" using xs j by simp
  show "dim_vec (Matrix.col (vec_to_mat k m (tensor_combination (k * m) xs fs) * G\<^sup>T) j) = dim_vec (xs ! j)"
    by (simp add: xd)
  fix i assume "i < dim_vec (xs ! j)"
  hence i: "i < k" using xd by simp
  have "Matrix.col (vec_to_mat k m (tensor_combination (k * m) xs fs) * G\<^sup>T) j $ i
      = (\<Sum>l<m. (\<Sum>j'<m. xs ! j' $ i * fs ! j' $ l) * G $$ (j,l))"
    unfolding right_coordinates_index[OF G i j] using i
    by (simp add: tensor_combination_index[OF xs(2) fd(1)] xs(1) fd(2) mult_index_lt mult_index_div_mod)
  also have "\<dots> = (\<Sum>j'<m. xs ! j' $ i * (\<Sum>l<m. fs ! j' $ l * G $$ (j,l)))"
    unfolding sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>j'<m. if j' = j then xs ! j' $ i else 0)"
    by (rule sum.cong) (auto simp: inv_entry_left[OF fd G GF j])
  also have "\<dots> = xs ! j $ i" using j by simp
  finally show "Matrix.col (vec_to_mat k m (tensor_combination (k * m) xs fs) * G\<^sup>T) j $ i = xs ! j $ i" .
qed

lemma right_coordinates_exist:
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and G: "G \<in> carrier_mat m m"
      and FG: "mat_of_cols m fs * G = 1\<^sub>m m" and u: "dim_vec u = k * m"
  shows "tensor_combination (k * m) (cols (vec_to_mat k m u * G\<^sup>T)) fs = u"
proof (rule eq_vecI)
  have cd: "\<forall>x \<in> set (cols (vec_to_mat k m u * G\<^sup>T)). dim_vec x = k" by (auto simp: cols_def)
  fix p assume "p < dim_vec u"
  hence p: "p < k * m" using u by simp
  hence m0: "0 < m" by (cases m) auto
  let ?i = "p div m" and ?r = "p mod m"
  have i: "?i < k" using p by (simp add: less_mult_imp_div_less)
  have r: "?r < m" using m0 by simp
  have "tensor_combination (k * m) (cols (vec_to_mat k m u * G\<^sup>T)) fs $ p
      = (\<Sum>j<m. (\<Sum>l<m. u $ (?i * m + l) * G $$ (j,l)) * fs ! j $ ?r)"
    using tensor_combination_index[OF cd fd(1) _ p] fd(2) i by (simp add: right_coordinates_index[OF G i] carrier_matD[OF G])
  also have "\<dots> = (\<Sum>l<m. u $ (?i * m + l) * (\<Sum>j<m. fs ! j $ ?r * G $$ (j,l)))"
    unfolding sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>l<m. if l = ?r then u $ (?i * m + l) else 0)"
    by (rule sum.cong) (auto simp: inv_entry_right[OF fd G FG r])
  also have "\<dots> = u $ (?i * m + ?r)" using r by simp
  also have "?i * m + ?r = p" by (simp add: div_mult_mod_eq)
  finally show "tensor_combination (k * m) (cols (vec_to_mat k m u * G\<^sup>T)) fs $ p = u $ p" .
qed (use u in simp)

text \<open>D6-3 (i): for a basis $f_1,\dots,f_m$ of $\C^m$, every $u\in\C^k\otimes\C^m$ is
$\sum_j x_j\otimes f_j$ for unique $x_1,\dots,x_m\in\C^k$.\<close>

theorem tensor_right_coordinates:
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and inv: "invertible_mat (mat_of_cols m fs)"
      and u: "dim_vec u = k * m"
  shows "\<exists>!xs. length xs = m \<and> (\<forall>x \<in> set xs. dim_vec x = k) \<and> u = tensor_combination (k * m) xs fs"
proof -
  obtain G where G: "G \<in> carrier_mat m m" and GF: "G * mat_of_cols m fs = 1\<^sub>m m"
    and FG: "mat_of_cols m fs * G = 1\<^sub>m m" by (rule basis_inverse[OF fd inv])
  show ?thesis
  proof (rule ex1I)
    show "length (cols (vec_to_mat k m u * G\<^sup>T)) = m \<and>
          (\<forall>x \<in> set (cols (vec_to_mat k m u * G\<^sup>T)). dim_vec x = k) \<and>
          u = tensor_combination (k * m) (cols (vec_to_mat k m u * G\<^sup>T)) fs"
      using right_coordinates_exist[OF fd G FG u] by (auto simp: cols_def carrier_matD[OF G])
    fix xs assume xs: "length xs = m \<and> (\<forall>x \<in> set xs. dim_vec x = k) \<and> u = tensor_combination (k * m) xs fs"
    show "xs = cols (vec_to_mat k m u * G\<^sup>T)"
      by (rule nth_equalityI) (use xs right_coordinates_unique[OF fd G GF, of xs k] in \<open>auto simp: carrier_matD[OF G]\<close>)
  qed
qed

lemma left_coordinates_unique:
  assumes ed: "\<forall>e \<in> set es. dim_vec e = k" "length es = k" and Hm: "Hm \<in> carrier_mat k k"
      and HE: "Hm * mat_of_cols k es = 1\<^sub>m k"
      and ys: "length ys = k" "\<forall>y \<in> set ys. dim_vec y = m" and i: "i < k"
  shows "Matrix.row (Hm * vec_to_mat k m (tensor_combination (k * m) es ys)) i = ys ! i"
proof (rule eq_vecI)
  have yd: "dim_vec (ys ! i) = m" using ys i by simp
  show "dim_vec (Matrix.row (Hm * vec_to_mat k m (tensor_combination (k * m) es ys)) i) = dim_vec (ys ! i)"
    by (simp add: yd)
  fix l assume "l < dim_vec (ys ! i)"
  hence l: "l < m" using yd by simp
  have "Matrix.row (Hm * vec_to_mat k m (tensor_combination (k * m) es ys)) i $ l
      = (\<Sum>r<k. Hm $$ (i,r) * (\<Sum>i'<k. es ! i' $ r * ys ! i' $ l))"
    unfolding left_coordinates_index[OF Hm i l] using l
    by (simp add: tensor_combination_index[OF ed(1) ys(2)] ys(1) ed(2) mult_index_lt mult_index_div_mod)
  also have "\<dots> = (\<Sum>i'<k. ys ! i' $ l * (\<Sum>r<k. es ! i' $ r * Hm $$ (i,r)))"
    unfolding sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>i'<k. if i' = i then ys ! i' $ l else 0)"
    by (rule sum.cong) (auto simp: inv_entry_left[OF ed Hm HE i])
  also have "\<dots> = ys ! i $ l" using i by simp
  finally show "Matrix.row (Hm * vec_to_mat k m (tensor_combination (k * m) es ys)) i $ l = ys ! i $ l" .
qed

lemma left_coordinates_exist:
  assumes ed: "\<forall>e \<in> set es. dim_vec e = k" "length es = k" and Hm: "Hm \<in> carrier_mat k k"
      and EH: "mat_of_cols k es * Hm = 1\<^sub>m k" and u: "dim_vec u = k * m"
  shows "tensor_combination (k * m) es (rows (Hm * vec_to_mat k m u)) = u"
proof (rule eq_vecI)
  have cd: "\<forall>y \<in> set (rows (Hm * vec_to_mat k m u)). dim_vec y = m" by (auto simp: rows_def)
  fix p assume "p < dim_vec u"
  hence p: "p < k * m" using u by simp
  hence m0: "0 < m" by (cases m) auto
  let ?i = "p div m" and ?r = "p mod m"
  have i: "?i < k" using p by (simp add: less_mult_imp_div_less)
  have r: "?r < m" using m0 by simp
  have "tensor_combination (k * m) es (rows (Hm * vec_to_mat k m u)) $ p
      = (\<Sum>j<k. es ! j $ ?i * (\<Sum>r'<k. Hm $$ (j,r') * u $ (r' * m + ?r)))"
    using tensor_combination_index[OF ed(1) cd _ p] ed(2) r by (simp add: left_coordinates_index[OF Hm _ r] carrier_matD[OF Hm])
  also have "\<dots> = (\<Sum>r'<k. u $ (r' * m + ?r) * (\<Sum>j<k. es ! j $ ?i * Hm $$ (j,r')))"
    unfolding sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>r'<k. if r' = ?i then u $ (r' * m + ?r) else 0)"
    by (rule sum.cong) (auto simp: inv_entry_right[OF ed Hm EH i])
  also have "\<dots> = u $ (?i * m + ?r)" using i by simp
  also have "?i * m + ?r = p" by (simp add: div_mult_mod_eq)
  finally show "tensor_combination (k * m) es (rows (Hm * vec_to_mat k m u)) $ p = u $ p" .
qed (use u in simp)

text \<open>D6-3 (ii): likewise $u=\sum_i e_i\otimes y_i$ for unique $y_1,\dots,y_k\in\C^m$.\<close>

theorem tensor_left_coordinates:
  assumes ed: "\<forall>e \<in> set es. dim_vec e = k" "length es = k" and inv: "invertible_mat (mat_of_cols k es)"
      and u: "dim_vec u = k * m"
  shows "\<exists>!ys. length ys = k \<and> (\<forall>y \<in> set ys. dim_vec y = m) \<and> u = tensor_combination (k * m) es ys"
proof -
  obtain Hm where Hm: "Hm \<in> carrier_mat k k" and HE: "Hm * mat_of_cols k es = 1\<^sub>m k"
    and EH: "mat_of_cols k es * Hm = 1\<^sub>m k" by (rule basis_inverse[OF ed inv])
  show ?thesis
  proof (rule ex1I)
    show "length (rows (Hm * vec_to_mat k m u)) = k \<and>
          (\<forall>y \<in> set (rows (Hm * vec_to_mat k m u)). dim_vec y = m) \<and>
          u = tensor_combination (k * m) es (rows (Hm * vec_to_mat k m u))"
      using left_coordinates_exist[OF ed Hm EH u] by (auto simp: rows_def carrier_matD[OF Hm])
    fix ys assume ys: "length ys = k \<and> (\<forall>y \<in> set ys. dim_vec y = m) \<and> u = tensor_combination (k * m) es ys"
    show "ys = rows (Hm * vec_to_mat k m u)"
      by (rule nth_equalityI) (use ys left_coordinates_unique[OF ed Hm HE, of ys m] in \<open>auto simp: carrier_matD[OF Hm]\<close>)
  qed
qed

text \<open>Corollary: $\C^k\otimes\C^m\cong\C^k\oplus\cdots\oplus\C^k$ ($m$ times) by the linear bijection
$(x_1,\dots,x_m)\mapsto\sum_j x_j\otimes f_j$, and $\cong\C^m\oplus\cdots\oplus\C^m$ ($k$ times)
likewise; the identification depends on the chosen basis.\<close>

lemma tensor_combination_add_left:
  assumes l: "length xs = length fs" "length xs' = length fs"
      and d: "\<forall>x \<in> set xs. dim_vec x = k" "\<forall>x \<in> set xs'. dim_vec x = k" and fd: "\<forall>y \<in> set fs. dim_vec y = m"
  shows "tensor_combination (k * m) (map2 (+) xs xs') fs = tensor_combination (k * m) xs fs + tensor_combination (k * m) xs' fs"
proof (rule eq_vecI)
  fix p assume "p < dim_vec (tensor_combination (k * m) xs fs + tensor_combination (k * m) xs' fs)"
  hence p: "p < k * m" by simp
  have q: "p div m < k" using p by (simp add: less_mult_imp_div_less)
  have dj: "\<And>j. j < length fs \<Longrightarrow> dim_vec (xs ! j) = k \<and> dim_vec (xs' ! j) = k"
    using l d by (simp add: all_set_conv_all_nth)
  have ds: "\<forall>x \<in> set (map2 (+) xs xs'). dim_vec x = k"
    using l dj by (auto simp: set_zip)
  have "tensor_combination (k * m) (map2 (+) xs xs') fs $ p
      = (\<Sum>j<length fs. (xs ! j + xs' ! j) $ (p div m) * fs ! j $ (p mod m))"
    using tensor_combination_index[OF ds fd _ p] l by simp
  also have "\<dots> = (\<Sum>j<length fs. xs ! j $ (p div m) * fs ! j $ (p mod m))
                 + (\<Sum>j<length fs. xs' ! j $ (p div m) * fs ! j $ (p mod m))"
    unfolding sum.distrib[symmetric] by (rule sum.cong) (use dj q in \<open>auto simp: distrib_right\<close>)
  finally show "tensor_combination (k * m) (map2 (+) xs xs') fs $ p
      = (tensor_combination (k * m) xs fs + tensor_combination (k * m) xs' fs) $ p"
    using p l by (simp add: tensor_combination_index[OF d(1) fd _ p] tensor_combination_index[OF d(2) fd _ p])
qed simp

lemma tensor_combination_smult_left:
  assumes l: "length xs = length fs" and d: "\<forall>x \<in> set xs. dim_vec x = k" and fd: "\<forall>y \<in> set fs. dim_vec y = m"
  shows "tensor_combination (k * m) (map (\<lambda>x. a \<cdot>\<^sub>v x) xs) fs = a \<cdot>\<^sub>v tensor_combination (k * m) xs fs"
proof (rule eq_vecI)
  fix p assume "p < dim_vec (a \<cdot>\<^sub>v tensor_combination (k * m) xs fs)"
  hence p: "p < k * m" by simp
  have q: "p div m < k" using p by (simp add: less_mult_imp_div_less)
  have ds: "\<forall>x \<in> set (map (\<lambda>x. a \<cdot>\<^sub>v x) xs). dim_vec x = k" using d by auto
  have dj: "\<And>j. j < length fs \<Longrightarrow> dim_vec (xs ! j) = k" using l d by (simp add: all_set_conv_all_nth)
  have "tensor_combination (k * m) (map (\<lambda>x. a \<cdot>\<^sub>v x) xs) fs $ p
      = (\<Sum>j<length fs. (a \<cdot>\<^sub>v xs ! j) $ (p div m) * fs ! j $ (p mod m))"
    using tensor_combination_index[OF ds fd _ p] l by simp
  also have "\<dots> = a * (\<Sum>j<length fs. xs ! j $ (p div m) * fs ! j $ (p mod m))"
    unfolding sum_distrib_left by (rule sum.cong) (use dj q in \<open>auto simp: mult.assoc\<close>)
  finally show "tensor_combination (k * m) (map (\<lambda>x. a \<cdot>\<^sub>v x) xs) fs $ p = (a \<cdot>\<^sub>v tensor_combination (k * m) xs fs) $ p"
    using p l by (simp add: tensor_combination_index[OF d fd _ p])
qed simp

corollary tensor_iso_direct_sum:
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and inv: "invertible_mat (mat_of_cols m fs)"
  shows "bij_betw (\<lambda>xs. tensor_combination (k * m) xs fs)
           {xs. length xs = m \<and> (\<forall>x \<in> set xs. dim_vec x = k)} (carrier_vec (k * m))"
proof (rule bij_betwI')
  fix xs ys :: "complex Matrix.vec list" assume xs: "xs \<in> {xs. length xs = m \<and> (\<forall>x \<in> set xs. dim_vec x = k)}"
               and ys: "ys \<in> {xs. length xs = m \<and> (\<forall>x \<in> set xs. dim_vec x = k)}"
  let ?P = "\<lambda>zs. length zs = m \<and> (\<forall>x \<in> set zs. dim_vec x = k) \<and>
                   tensor_combination (k * m) ys fs = tensor_combination (k * m) zs fs"
  have ex: "\<exists>!zs. ?P zs" by (rule tensor_right_coordinates[OF fd inv]) simp
  from ex obtain z where "?P z" and z: "\<forall>zs. ?P zs \<longrightarrow> zs = z" by (rule ex1E)
  show "(tensor_combination (k * m) xs fs = tensor_combination (k * m) ys fs) = (xs = ys)"
  proof
    assume e: "tensor_combination (k * m) xs fs = tensor_combination (k * m) ys fs"
    have px: "?P xs" and py: "?P ys" using xs ys e by auto
    have "xs = z" by (rule z[rule_format, OF px])
    moreover have "ys = z" by (rule z[rule_format, OF py])
    ultimately
    show "xs = ys" by simp
  qed simp
next
  fix xs :: "complex Matrix.vec list" assume "xs \<in> {xs. length xs = m \<and> (\<forall>x \<in> set xs. dim_vec x = k)}"
  show "tensor_combination (k * m) xs fs \<in> carrier_vec (k * m)" by (rule carrier_vecI) simp
next
  fix u :: "complex Matrix.vec" assume "u \<in> carrier_vec (k * m)"
  hence u: "dim_vec u = k * m" by simp
  show "\<exists>xs \<in> {xs. length xs = m \<and> (\<forall>x \<in> set xs. dim_vec x = k)}. u = tensor_combination (k * m) xs fs"
    using tensor_right_coordinates[OF fd inv u] by blast
qed

subsection \<open>The Schmidt rank (D6-4)\<close>

text \<open>The notes define the Schmidt rank $\operatorname{rank}_S(u)$ of $u\in X\otimes Y$ as the least
number of elementary tensors in an expression for $u$, and use on Day 10 that a two-photon state
$\psi$ is a product $\psi_1\otimes\psi_2$ iff $\operatorname{rank}_S(\psi)=1$; otherwise it is entangled.
Here: every $u\in\C^n\otimes\C^m$ has an expression of length $n$, so the least length exists;
$\operatorname{rank}_S(u)=0$ iff $u=0$; for $u\ne0$, $\operatorname{rank}_S(u)=1$ iff $u$ is a product
and $u$ is entangled iff $\operatorname{rank}_S(u)>1$; the Bell state has Schmidt rank $2$.\<close>

text \<open>A representation of $u\in\C^n\otimes\C^m$ by $k$ elementary tensors.\<close>

definition schmidt_repr :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> nat \<Rightarrow> bool" where
  "schmidt_repr n m u k \<longleftrightarrow> (\<exists>vs ws. length vs = k \<and> length ws = k \<and>
     (\<forall>i < k. dim_vec (vs ! i) = n) \<and> (\<forall>i < k. dim_vec (ws ! i) = m) \<and>
     u = tensor_combination (n * m) vs ws)"

lemma schmidt_rank_eq:
  assumes u: "dim_vec u = n * m" and m: "0 < m"
  shows "schmidt_rank u m = (LEAST k. schmidt_repr n m u k)"
proof -
  have "dim_vec u div m = n" using u m by simp
  thus ?thesis unfolding schmidt_rank_def schmidt_repr_def tensor_combination_def using u by simp
qed

text \<open>Every $u$ is a sum of $n$ elementary tensors, $u=\sum_ie_i\otimes u_i$ with
$u_i=(u_{im+j})_j$, so the least length exists.\<close>

lemma schmidt_repr_exists:
  assumes u: "dim_vec u = n * m"
  shows "schmidt_repr n m u n"
proof -
  define vs :: "complex Matrix.vec list" where "vs = map (unit_vec n) [0..<n]"
  define ws where "ws = map (\<lambda>i. Matrix.vec m (\<lambda>j. u $ (i * m + j))) [0..<n]"
  have vsd: "\<forall>x \<in> set vs. dim_vec x = n" and wsd: "\<forall>y \<in> set ws. dim_vec y = m" by (auto simp: vs_def ws_def)
  have len: "length vs = length ws" by (simp add: vs_def ws_def)
  have "u = tensor_combination (n * m) vs ws"
  proof (rule eq_vecI)
    fix p assume "p < dim_vec (tensor_combination (n * m) vs ws)"
    hence p: "p < n * m" by simp
    have m: "0 < m" using p by (cases m) auto
    have pd: "p div m < n" using p by (simp add: less_mult_imp_div_less)
    have "tensor_combination (n * m) vs ws $ p = (\<Sum>j<n. vs ! j $ (p div m) * ws ! j $ (p mod m))"
      using tensor_combination_index[OF vsd wsd len p] by (simp add: vs_def)
    also have "\<dots> = (\<Sum>j<n. if j = p div m then u $ (j * m + p mod m) else 0)"
      by (rule sum.cong) (use m pd in \<open>auto simp: vs_def ws_def unit_vec_def\<close>)
    also have "\<dots> = u $ (p div m * m + p mod m)" using pd by simp
    also have "\<dots> = u $ p" by simp
    finally show "u $ p = tensor_combination (n * m) vs ws $ p" ..
  qed (use u in simp)
  thus ?thesis unfolding schmidt_repr_def using vsd wsd len
    by (intro exI[of _ vs] exI[of _ ws]) (auto simp: vs_def ws_def)
qed

lemma schmidt_rank_repr:
  assumes u: "dim_vec u = n * m" and m: "0 < m"
  shows "schmidt_repr n m u (schmidt_rank u m)" and "\<And>k. schmidt_repr n m u k \<Longrightarrow> schmidt_rank u m \<le> k"
proof -
  show "schmidt_repr n m u (schmidt_rank u m)"
    unfolding schmidt_rank_eq[OF u m] by (rule LeastI[where P = "schmidt_repr n m u", OF schmidt_repr_exists[OF u]])
  show "\<And>k. schmidt_repr n m u k \<Longrightarrow> schmidt_rank u m \<le> k"
    unfolding schmidt_rank_eq[OF u m] by (rule Least_le)
qed

lemma schmidt_repr_0: "schmidt_repr n m u 0 \<longleftrightarrow> u = 0\<^sub>v (n * m)"
  by (simp add: schmidt_repr_def tensor_combination_def)

lemma schmidt_repr_1:
  "schmidt_repr n m u 1 \<longleftrightarrow> (\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w)"
proof
  assume "schmidt_repr n m u 1"
  then obtain vs ws where l: "length vs = 1" "length ws = 1" and d: "dim_vec (vs ! 0) = n" "dim_vec (ws ! 0) = m"
    and u: "u = tensor_combination (n * m) vs ws" unfolding schmidt_repr_def by auto
  obtain v w where vs: "vs = [v]" and ws: "ws = [w]" using l by (cases vs; cases ws) auto
  have d': "dim_vec v = n" "dim_vec w = m" using d vs ws by simp_all
  have "u = tensor_vec v w + 0\<^sub>v (n * m)" using u by (simp add: vs ws tensor_combination_def)
  also have "\<dots> = tensor_vec v w" by (rule right_zero_vec[OF carrier_vecI[OF tensor_vec_dim[OF d']]])
  finally show "\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w" using d' by auto
next
  assume "\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w"
  then obtain v w where d: "dim_vec v = n" "dim_vec w = m" and u: "u = tensor_vec v w" by blast
  have "tensor_combination (n * m) [v] [w] = tensor_vec v w"
    using right_zero_vec[OF carrier_vecI[OF tensor_vec_dim[OF d]]] by (simp add: tensor_combination_def)
  thus "schmidt_repr n m u 1" unfolding schmidt_repr_def using d u
    by (intro exI[of _ "[v]"] exI[of _ "[w]"]) simp
qed

theorem schmidt_rank_zero_iff:
  assumes u: "dim_vec u = n * m" and m: "0 < m"
  shows "schmidt_rank u m = 0 \<longleftrightarrow> u = 0\<^sub>v (n * m)"
proof
  assume "schmidt_rank u m = 0"
  thus "u = 0\<^sub>v (n * m)" using schmidt_rank_repr(1)[OF u m] schmidt_repr_0 by simp
next
  assume "u = 0\<^sub>v (n * m)"
  hence "schmidt_repr n m u 0" using schmidt_repr_0 by simp
  thus "schmidt_rank u m = 0" using schmidt_rank_repr(2)[OF u m] by fastforce
qed

text \<open>The notes: $\psi=\psi_1\otimes\psi_2$ iff $\operatorname{rank}_S(\psi)=1$ (for $\psi\ne0$).\<close>

theorem schmidt_rank_one_iff_product:
  assumes u: "dim_vec u = n * m" and m: "0 < m" and u0: "u \<noteq> 0\<^sub>v (n * m)"
  shows "schmidt_rank u m = 1 \<longleftrightarrow> (\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w)"
proof
  assume "schmidt_rank u m = 1"
  thus "\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w"
    using schmidt_rank_repr(1)[OF u m] schmidt_repr_1 by simp
next
  assume "\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w"
  hence "schmidt_rank u m \<le> 1" using schmidt_rank_repr(2)[OF u m] schmidt_repr_1 by blast
  moreover have "schmidt_rank u m \<noteq> 0" using schmidt_rank_zero_iff[OF u m] u0 by simp
  ultimately show "schmidt_rank u m = 1" by simp
qed

end
