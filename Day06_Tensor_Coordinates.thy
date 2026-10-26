theory Day06_Tensor_Coordinates
  imports
    Day05_Direct_Sum_Basis
    Quantum_Computing_by_VP.Day06_Tensor_Products
begin

section \<open>Day 6: coordinates in a tensor product\<close>

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

end
