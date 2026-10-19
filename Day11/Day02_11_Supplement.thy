theory Day02_11_Supplement
  imports Quantum_Computing11
begin

text \<open>Supplementary results for Days 2--11 recorded as gaps by the first audit.\<close>

subsection \<open>Day 2: the projection does not depend on the orthonormal basis\<close>

definition col_span :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec set" where
  "col_span n vs = {mat_of_cols n vs *\<^sub>v c | c. dim_vec c = length vs}"

lemma outer_sum_fixes_col_span:
  assumes orth: "orthonormal_list n vs" and w: "w \<in> col_span n vs"
  shows "outer_sum n vs *\<^sub>v w = w"
proof -
  let ?k = "length vs" and ?V = "mat_of_cols n vs"
  obtain c where c: "dim_vec c = ?k" and wc: "w = ?V *\<^sub>v c" using w unfolding col_span_def by blast
  have Vc: "?V \<in> carrier_mat n ?k" by simp
  have Vdc: "?V\<^sup>\<dagger> \<in> carrier_mat ?k n" by (rule dagger_carrier[OF Vc])
  have cc: "c \<in> carrier_vec ?k" by (rule carrier_vecI[OF c])
  have VdV: "(?V\<^sup>\<dagger>) * ?V = 1\<^sub>m ?k" by (rule cols_mat_dagger_left[OF orth])
  have "outer_sum n vs *\<^sub>v w = ?V *\<^sub>v ((?V\<^sup>\<dagger>) *\<^sub>v (?V *\<^sub>v c))"
    unfolding outer_sum_def wc by (rule assoc_mult_mat_vec[OF Vc Vdc mult_mat_vec_carrier[OF Vc cc]])
  also have "(?V\<^sup>\<dagger>) *\<^sub>v (?V *\<^sub>v c) = c"
    using assoc_mult_mat_vec[OF Vdc Vc cc] unfolding VdV using cc by simp
  finally show ?thesis unfolding wc .
qed

lemma mem_col_span_self:
  assumes "\<forall>v \<in> set vs. dim_vec v = n" and j: "j < length vs"
  shows "vs ! j \<in> col_span n vs"
proof -
  have Vc: "mat_of_cols n vs \<in> carrier_mat n (length vs)" by simp
  have vj: "vs ! j \<in> carrier_vec n" using assms(1) j by (auto intro!: carrier_vecI)
  have "mat_of_cols n vs *\<^sub>v unit_vec (length vs) j = Matrix.col (mat_of_cols n vs) j"
    by (rule eq_vecI) (use Vc j in auto)
  also have "\<dots> = vs ! j" by (rule col_mat_of_cols[OF j vj])
  finally have "mat_of_cols n vs *\<^sub>v unit_vec (length vs) j = vs ! j" .
  thus ?thesis unfolding col_span_def
    by (intro CollectI exI[of _ "unit_vec (length vs) j"]) simp
qed

lemma outer_sum_absorbs:
  assumes ov: "orthonormal_list n vs" and ow: "orthonormal_list n ws"
      and sub: "set ws \<subseteq> col_span n vs"
  shows "outer_sum n vs * outer_sum n ws = outer_sum n ws"
proof -
  let ?V = "mat_of_cols n vs" and ?W = "mat_of_cols n ws" and ?P = "outer_sum n vs"
  have wd: "\<And>j. j < length ws \<Longrightarrow> ws ! j \<in> carrier_vec n"
    using ow unfolding orthonormal_list_def by (auto intro: carrier_vecI)
  have Pc: "?P \<in> carrier_mat n n" by (simp add: carrier_matI)
  have Wc: "?W \<in> carrier_mat n (length ws)" by simp
  have Wdc: "?W\<^sup>\<dagger> \<in> carrier_mat (length ws) n" by (rule dagger_carrier[OF Wc])
  have PW: "?P * ?W = ?W"
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row ?W" and j': "j < dim_col ?W"
    have j: "j < length ws" using j' by simp
    have "(?P * ?W) $$ (i,j) = (?P *\<^sub>v Matrix.col ?W j) $ i" using i j Pc by (simp add: scalar_prod_def atLeast0LessThan)
    also have "Matrix.col ?W j = ws ! j" by (rule col_mat_of_cols[OF j wd[OF j]])
    also have "?P *\<^sub>v ws ! j = ws ! j" by (rule outer_sum_fixes_col_span[OF ov subsetD[OF sub nth_mem[OF j]]])
    finally show "(?P * ?W) $$ (i,j) = ?W $$ (i,j)" using i j wd[OF j] by (simp add: mat_of_cols_def)
  qed (use Pc in simp_all)
  have "?P * outer_sum n ws = (?P * ?W) * (?W\<^sup>\<dagger>)"
    unfolding outer_sum_def[of n ws] by (rule assoc_mult_mat[OF Pc Wc Wdc, symmetric])
  thus ?thesis unfolding PW outer_sum_def[of n ws] .
qed

text \<open>D2-8: two orthonormal bases of the same subspace give the same projection.\<close>

theorem outer_sum_basis_independent:
  assumes ov: "orthonormal_list n vs" and ow: "orthonormal_list n ws"
      and span: "col_span n vs = col_span n ws"
  shows "outer_sum n vs = outer_sum n ws"
proof -
  let ?P = "outer_sum n vs" and ?Q = "outer_sum n ws"
  have vd: "\<forall>v \<in> set vs. dim_vec v = n" and wd: "\<forall>v \<in> set ws. dim_vec v = n"
    using ov ow unfolding orthonormal_list_def by auto
  have subw: "set ws \<subseteq> col_span n vs"
    using mem_col_span_self[OF wd] span by (auto simp: in_set_conv_nth)
  have subv: "set vs \<subseteq> col_span n ws"
    using mem_col_span_self[OF vd] span by (auto simp: in_set_conv_nth)
  have PQ: "?P * ?Q = ?Q" by (rule outer_sum_absorbs[OF ov ow subw])
  have QP: "?Q * ?P = ?P" by (rule outer_sum_absorbs[OF ow ov subv])
  have Pc: "?P \<in> carrier_mat n n" and Qc: "?Q \<in> carrier_mat n n" by (simp_all add: carrier_matI)
  have "?Q = (?P * ?Q)\<^sup>\<dagger>" unfolding PQ outer_sum_hermitian ..
  also have "\<dots> = (?Q\<^sup>\<dagger>) * (?P\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Pc Qc in simp)
  also have "\<dots> = ?P" unfolding outer_sum_hermitian QP ..
  finally show ?thesis ..
qed

subsection \<open>Day 6: coordinates in a tensor product\<close>

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

lemma idx_bound: "i < k \<Longrightarrow> l < (m::nat) \<Longrightarrow> i * m + l < k * m"
proof -
  assume i: "i < k" and l: "l < m"
  have "i * m + l < Suc i * m" using l by simp
  also have "Suc i * m \<le> k * m" using i by (intro mult_le_mono1) simp
  finally show ?thesis .
qed

lemma idx_div_mod: "l < (m::nat) \<Longrightarrow> (i * m + l) div m = i \<and> (i * m + l) mod m = l"
  by simp

text \<open>A basis $f_1,\dots,f_m$ of $\C^m$ is a list whose column matrix $F$ is invertible; the
coordinates use $G=F^{-1}$.\<close>

definition right_coord :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "right_coord k m G u j = Matrix.vec k (\<lambda>i. \<Sum>l<m. u $ (i * m + l) * G $$ (j,l))"

definition left_coord :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "left_coord k m Hm u i = Matrix.vec m (\<lambda>l. \<Sum>r<k. Hm $$ (i,r) * u $ (r * m + l))"

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

lemma right_coord_unique:
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and G: "G \<in> carrier_mat m m"
      and GF: "G * mat_of_cols m fs = 1\<^sub>m m"
      and xs: "length xs = m" "\<forall>x \<in> set xs. dim_vec x = k" and j: "j < m"
  shows "right_coord k m G (tensor_combination (k * m) xs fs) j = xs ! j"
proof (rule eq_vecI)
  have xd: "dim_vec (xs ! j) = k" using xs j by simp
  show "dim_vec (right_coord k m G (tensor_combination (k * m) xs fs) j) = dim_vec (xs ! j)"
    by (simp add: right_coord_def xd)
  fix i assume "i < dim_vec (xs ! j)"
  hence i: "i < k" using xd by simp
  have "right_coord k m G (tensor_combination (k * m) xs fs) j $ i
      = (\<Sum>l<m. (\<Sum>j'<m. xs ! j' $ i * fs ! j' $ l) * G $$ (j,l))"
    unfolding right_coord_def using i
    by (simp add: tensor_combination_index[OF xs(2) fd(1)] xs(1) fd(2) idx_bound idx_div_mod)
  also have "\<dots> = (\<Sum>j'<m. xs ! j' $ i * (\<Sum>l<m. fs ! j' $ l * G $$ (j,l)))"
    unfolding sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>j'<m. if j' = j then xs ! j' $ i else 0)"
    by (rule sum.cong) (auto simp: inv_entry_left[OF fd G GF j])
  also have "\<dots> = xs ! j $ i" using j by simp
  finally show "right_coord k m G (tensor_combination (k * m) xs fs) j $ i = xs ! j $ i" .
qed

lemma right_coord_exists:
  assumes fd: "\<forall>f \<in> set fs. dim_vec f = m" "length fs = m" and G: "G \<in> carrier_mat m m"
      and FG: "mat_of_cols m fs * G = 1\<^sub>m m" and u: "dim_vec u = k * m"
  shows "tensor_combination (k * m) (map (right_coord k m G u) [0..<m]) fs = u"
proof (rule eq_vecI)
  have cd: "\<forall>x \<in> set (map (right_coord k m G u) [0..<m]). dim_vec x = k" by (auto simp: right_coord_def)
  fix p assume "p < dim_vec u"
  hence p: "p < k * m" using u by simp
  hence m0: "0 < m" by (cases m) auto
  let ?i = "p div m" and ?r = "p mod m"
  have i: "?i < k" using p by (simp add: less_mult_imp_div_less)
  have r: "?r < m" using m0 by simp
  have "tensor_combination (k * m) (map (right_coord k m G u) [0..<m]) fs $ p
      = (\<Sum>j<m. (\<Sum>l<m. u $ (?i * m + l) * G $$ (j,l)) * fs ! j $ ?r)"
    using tensor_combination_index[OF cd fd(1) _ p] fd(2) i by (simp add: right_coord_def)
  also have "\<dots> = (\<Sum>l<m. u $ (?i * m + l) * (\<Sum>j<m. fs ! j $ ?r * G $$ (j,l)))"
    unfolding sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>l<m. if l = ?r then u $ (?i * m + l) else 0)"
    by (rule sum.cong) (auto simp: inv_entry_right[OF fd G FG r])
  also have "\<dots> = u $ (?i * m + ?r)" using r by simp
  also have "?i * m + ?r = p" by (simp add: div_mult_mod_eq)
  finally show "tensor_combination (k * m) (map (right_coord k m G u) [0..<m]) fs $ p = u $ p" .
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
    show "length (map (right_coord k m G u) [0..<m]) = m \<and>
          (\<forall>x \<in> set (map (right_coord k m G u) [0..<m]). dim_vec x = k) \<and>
          u = tensor_combination (k * m) (map (right_coord k m G u) [0..<m]) fs"
      using right_coord_exists[OF fd G FG u] by (auto simp: right_coord_def)
    fix xs assume xs: "length xs = m \<and> (\<forall>x \<in> set xs. dim_vec x = k) \<and> u = tensor_combination (k * m) xs fs"
    show "xs = map (right_coord k m G u) [0..<m]"
      by (rule nth_equalityI) (use xs right_coord_unique[OF fd G GF, of xs k] in auto)
  qed
qed

lemma left_coord_unique:
  assumes ed: "\<forall>e \<in> set es. dim_vec e = k" "length es = k" and Hm: "Hm \<in> carrier_mat k k"
      and HE: "Hm * mat_of_cols k es = 1\<^sub>m k"
      and ys: "length ys = k" "\<forall>y \<in> set ys. dim_vec y = m" and i: "i < k"
  shows "left_coord k m Hm (tensor_combination (k * m) es ys) i = ys ! i"
proof (rule eq_vecI)
  have yd: "dim_vec (ys ! i) = m" using ys i by simp
  show "dim_vec (left_coord k m Hm (tensor_combination (k * m) es ys) i) = dim_vec (ys ! i)"
    by (simp add: left_coord_def yd)
  fix l assume "l < dim_vec (ys ! i)"
  hence l: "l < m" using yd by simp
  have "left_coord k m Hm (tensor_combination (k * m) es ys) i $ l
      = (\<Sum>r<k. Hm $$ (i,r) * (\<Sum>i'<k. es ! i' $ r * ys ! i' $ l))"
    unfolding left_coord_def using l
    by (simp add: tensor_combination_index[OF ed(1) ys(2)] ys(1) ed(2) idx_bound idx_div_mod)
  also have "\<dots> = (\<Sum>i'<k. ys ! i' $ l * (\<Sum>r<k. es ! i' $ r * Hm $$ (i,r)))"
    unfolding sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>i'<k. if i' = i then ys ! i' $ l else 0)"
    by (rule sum.cong) (auto simp: inv_entry_left[OF ed Hm HE i])
  also have "\<dots> = ys ! i $ l" using i by simp
  finally show "left_coord k m Hm (tensor_combination (k * m) es ys) i $ l = ys ! i $ l" .
qed

lemma left_coord_exists:
  assumes ed: "\<forall>e \<in> set es. dim_vec e = k" "length es = k" and Hm: "Hm \<in> carrier_mat k k"
      and EH: "mat_of_cols k es * Hm = 1\<^sub>m k" and u: "dim_vec u = k * m"
  shows "tensor_combination (k * m) es (map (left_coord k m Hm u) [0..<k]) = u"
proof (rule eq_vecI)
  have cd: "\<forall>y \<in> set (map (left_coord k m Hm u) [0..<k]). dim_vec y = m" by (auto simp: left_coord_def)
  fix p assume "p < dim_vec u"
  hence p: "p < k * m" using u by simp
  hence m0: "0 < m" by (cases m) auto
  let ?i = "p div m" and ?r = "p mod m"
  have i: "?i < k" using p by (simp add: less_mult_imp_div_less)
  have r: "?r < m" using m0 by simp
  have "tensor_combination (k * m) es (map (left_coord k m Hm u) [0..<k]) $ p
      = (\<Sum>j<k. es ! j $ ?i * (\<Sum>r'<k. Hm $$ (j,r') * u $ (r' * m + ?r)))"
    using tensor_combination_index[OF ed(1) cd _ p] ed(2) r by (simp add: left_coord_def)
  also have "\<dots> = (\<Sum>r'<k. u $ (r' * m + ?r) * (\<Sum>j<k. es ! j $ ?i * Hm $$ (j,r')))"
    unfolding sum_distrib_left sum_distrib_right by (subst sum.swap) (simp add: mult_ac)
  also have "\<dots> = (\<Sum>r'<k. if r' = ?i then u $ (r' * m + ?r) else 0)"
    by (rule sum.cong) (auto simp: inv_entry_right[OF ed Hm EH i])
  also have "\<dots> = u $ (?i * m + ?r)" using i by simp
  also have "?i * m + ?r = p" by (simp add: div_mult_mod_eq)
  finally show "tensor_combination (k * m) es (map (left_coord k m Hm u) [0..<k]) $ p = u $ p" .
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
    show "length (map (left_coord k m Hm u) [0..<k]) = k \<and>
          (\<forall>y \<in> set (map (left_coord k m Hm u) [0..<k]). dim_vec y = m) \<and>
          u = tensor_combination (k * m) es (map (left_coord k m Hm u) [0..<k])"
      using left_coord_exists[OF ed Hm EH u] by (auto simp: left_coord_def)
    fix ys assume ys: "length ys = k \<and> (\<forall>y \<in> set ys. dim_vec y = m) \<and> u = tensor_combination (k * m) es ys"
    show "ys = map (left_coord k m Hm u) [0..<k]"
      by (rule nth_equalityI) (use ys left_coord_unique[OF ed Hm HE, of ys m] in auto)
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

subsection \<open>Day 8: non-orthogonal states cannot be distinguished\<close>

lemma meas_sum_norm:
  assumes ms: "measurement_system n Ms" and v: "dim_vec v = n"
  shows "(\<Sum>l<length Ms. \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2) = \<parallel>v\<parallel>\<^sup>2"
proof (cases "\<parallel>v\<parallel> = 0")
  case True
  hence v0: "v = 0\<^sub>v n" using v cpx_vec_length_zero_iff by fastforce
  have Mc: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have z: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l *\<^sub>v v = 0\<^sub>v n"
  proof -
    fix l assume "l < length Ms"
    hence M: "Ms ! l \<in> carrier_mat n n" by (rule Mc)
    show "Ms ! l *\<^sub>v v = 0\<^sub>v n" by (rule eq_vecI) (use M in \<open>auto simp: v0 scalar_prod_def\<close>)
  qed
  show ?thesis using True by (simp add: z cpx_vec_length_def)
next
  case False
  let ?c = "complex_of_real (1 / \<parallel>v\<parallel>)"
  have st: "quantum_state n (?c \<cdot>\<^sub>v v)"
  proof -
    have "\<parallel>v\<parallel> \<ge> 0" unfolding cpx_vec_length_def by (simp add: sum_nonneg)
    thus ?thesis unfolding quantum_state_def using v False by (simp add: cpx_vec_length_smult norm_divide)
  qed
  have Mc: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
  have tm: "\<And>l. l < length Ms \<Longrightarrow> meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v) = \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2 / \<parallel>v\<parallel>\<^sup>2"
  proof -
    fix l assume l: "l < length Ms"
    have vn: "\<parallel>v\<parallel> \<ge> 0" unfolding cpx_vec_length_def by (simp add: sum_nonneg)
    show "meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v) = \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2 / \<parallel>v\<parallel>\<^sup>2"
      unfolding meas_prob_def mult_mat_vec[OF Mc[OF l] vc]
      by (simp add: cpx_vec_length_smult norm_divide abs_of_nonneg[OF vn] power_mult_distrib power_divide)
  qed
  have "1 = (\<Sum>M \<leftarrow> Ms. meas_prob M (?c \<cdot>\<^sub>v v))" by (rule measurement_probs_sum_one[OF ms st, symmetric])
  also have "\<dots> = (\<Sum>l<length Ms. meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = (\<Sum>l<length Ms. \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2) / \<parallel>v\<parallel>\<^sup>2"
    unfolding sum_divide_distrib by (rule sum.cong[OF refl], rule tm, simp)
  finally show ?thesis using False by (simp add: field_simps)
qed

lemma inner_minus_smult:
  assumes d1: "dim_vec u = n" and d2: "dim_vec w = n"
  shows "\<langle>w - a \<cdot>\<^sub>v u | w - a \<cdot>\<^sub>v u\<rangle> = \<langle>w|w\<rangle> - a * \<langle>w|u\<rangle> - cnj a * \<langle>u|w\<rangle> + a * cnj a * \<langle>u|u\<rangle>"
  unfolding inner_prod_def using d1 d2
  by (simp add: sum.distrib sum_subtractf sum_distrib_left algebra_simps)

lemma norm_sq_minus_component:
  assumes d1: "dim_vec u = n" and d2: "dim_vec w = n" and u: "\<parallel>u\<parallel> = 1"
  shows "\<parallel>w - \<langle>u|w\<rangle> \<cdot>\<^sub>v u\<parallel>\<^sup>2 = \<parallel>w\<parallel>\<^sup>2 - (cmod \<langle>u|w\<rangle>)\<^sup>2"
proof -
  let ?a = "\<langle>u|w\<rangle>"
  have uu: "\<langle>u|u\<rangle> = 1" using u cpx_vec_length_inner_prod[of u] by simp
  have wu: "\<langle>w|u\<rangle> = cnj ?a" by (rule inner_prod_cnj) (use d1 d2 in simp)
  have e: "\<langle>w - ?a \<cdot>\<^sub>v u | w - ?a \<cdot>\<^sub>v u\<rangle> = \<langle>w|w\<rangle> - ?a * \<langle>w|u\<rangle> - cnj ?a * ?a + ?a * cnj ?a * \<langle>u|u\<rangle>"
    by (rule inner_minus_smult[OF d1 d2])
  have "complex_of_real (\<parallel>w - ?a \<cdot>\<^sub>v u\<parallel>\<^sup>2) = complex_of_real (\<parallel>w\<parallel>\<^sup>2) - ?a * cnj ?a"
    unfolding cpx_vec_length_inner_prod e wu uu by simp
  also have "?a * cnj ?a = complex_of_real ((cmod ?a)\<^sup>2)" using complex_norm_square[of ?a] by simp
  finally show ?thesis by (metis of_real_diff of_real_eq_iff)
qed

text \<open>D8-2: if outcome $i$ certainly occurs on $\psi_1$, it occurs on $\psi_2$ with probability
at least $|\langle\psi_1|\psi_2\rangle|^2$.\<close>

theorem nonorthogonal_outcome_prob:
  assumes ms: "measurement_system n Ms" and q1: "quantum_state n \<psi>1" and q2: "quantum_state n \<psi>2"
      and i: "i < length Ms" and p1: "meas_prob (Ms ! i) \<psi>1 = 1"
  shows "(cmod \<langle>\<psi>1|\<psi>2\<rangle>)\<^sup>2 \<le> meas_prob (Ms ! i) \<psi>2"
proof -
  let ?N = "length Ms" and ?a = "\<langle>\<psi>1|\<psi>2\<rangle>"
  let ?g = "\<psi>2 - ?a \<cdot>\<^sub>v \<psi>1"
  have d1: "dim_vec \<psi>1 = n" and n1: "\<parallel>\<psi>1\<parallel> = 1" and d2: "dim_vec \<psi>2 = n" and n2: "\<parallel>\<psi>2\<parallel> = 1"
    using q1 q2 unfolding quantum_state_def by auto
  have Mc: "\<And>l. l < ?N \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have rem: "\<And>f :: nat \<Rightarrow> real. (\<Sum>l<?N. f l) = f i + (\<Sum>l\<in>{..<?N} - {i}. f l)"
    by (rule sum.remove) (use i in simp_all)
  have S1: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2) = 1" using meas_sum_norm[OF ms d1] n1 by simp
  have rest0: "(\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2) = 0"
    using S1 rem[of "\<lambda>l. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2"] p1 unfolding meas_prob_def by simp
  have z: "\<And>l. l < ?N \<Longrightarrow> l \<noteq> i \<Longrightarrow> Ms ! l *\<^sub>v \<psi>1 = 0\<^sub>v n"
  proof -
    fix l assume l: "l < ?N" "l \<noteq> i"
    have "\<forall>x\<in>{..<?N} - {i}. \<parallel>Ms ! x *\<^sub>v \<psi>1\<parallel>\<^sup>2 = 0"
      using rest0 by (subst (asm) sum_nonneg_eq_0_iff) auto
    hence "\<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2 = 0" using l by auto
    hence "\<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel> = 0" by simp
    thus "Ms ! l *\<^sub>v \<psi>1 = 0\<^sub>v n" using cpx_vec_length_zero_iff Mc[OF l(1)] by fastforce
  qed
  have gd: "dim_vec ?g = n" using d1 d2 by simp
  have Mg: "\<And>l. l < ?N \<Longrightarrow> l \<noteq> i \<Longrightarrow> Ms ! l *\<^sub>v \<psi>2 = Ms ! l *\<^sub>v ?g"
  proof -
    fix l assume l: "l < ?N" "l \<noteq> i"
    have c1: "\<psi>1 \<in> carrier_vec n" by (rule carrier_vecI[OF d1])
    have c2: "\<psi>2 \<in> carrier_vec n" by (rule carrier_vecI[OF d2])
    have "Ms ! l *\<^sub>v ?g = Ms ! l *\<^sub>v \<psi>2 - ?a \<cdot>\<^sub>v (Ms ! l *\<^sub>v \<psi>1)"
      using mult_minus_distrib_mat_vec[OF Mc[OF l(1)] c2 smult_carrier_vec[THEN iffD2, OF c1]] mult_mat_vec[OF Mc[OF l(1)] c1] by simp
    thus "Ms ! l *\<^sub>v \<psi>2 = Ms ! l *\<^sub>v ?g" using z[OF l] Mc[OF l(1)] by auto
  qed
  have S2: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2) = 1" using meas_sum_norm[OF ms d2] n2 by simp
  have Sg: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2) = 1 - (cmod ?a)\<^sup>2"
    using meas_sum_norm[OF ms gd] norm_sq_minus_component[OF d1 d2 n1] n2 by simp
  have "(\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2) = (\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2)"
    by (rule sum.cong) (simp_all add: Mg)
  also have "\<dots> \<le> (\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2)" by (rule sum_mono2) auto
  finally show ?thesis using S2 Sg rem[of "\<lambda>l. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2"] unfolding meas_prob_def by linarith
qed

corollary nonorthogonal_not_distinguishable:
  assumes ms: "measurement_system n Ms" and q1: "quantum_state n \<psi>1" and q2: "quantum_state n \<psi>2"
      and no: "\<langle>\<psi>1|\<psi>2\<rangle> \<noteq> 0" and i: "i < length Ms" and p1: "meas_prob (Ms ! i) \<psi>1 = 1"
  shows "meas_prob (Ms ! i) \<psi>2 > 0"
  using nonorthogonal_outcome_prob[OF ms q1 q2 i p1] no
  by (smt (verit) zero_less_power norm_eq_zero zero_less_norm_iff)

subsection \<open>Day 9: measuring one half of a Bell pair\<close>

definition e0 :: "complex Matrix.vec" where "e0 = unit_vec 2 0"
definition e1 :: "complex Matrix.vec" where "e1 = unit_vec 2 1"
definition proj0 :: "complex Matrix.mat" where "proj0 = e0 \<oslash> e0"
definition proj1 :: "complex Matrix.mat" where "proj1 = e1 \<oslash> e1"

lemma e_dims [simp]: "dim_vec e0 = 2" "dim_vec e1 = 2"
  by (simp_all add: e0_def e1_def)

lemma e_inner [simp]: "\<langle>e0|e0\<rangle> = 1" "\<langle>e0|e1\<rangle> = 0" "\<langle>e1|e0\<rangle> = 0" "\<langle>e1|e1\<rangle> = 1"
  by (simp_all add: e0_def e1_def inner_prod_def unit_vec_def)

lemma proj_carrier [simp]: "proj0 \<in> carrier_mat 2 2" "proj1 \<in> carrier_mat 2 2"
  by (simp_all add: proj0_def proj1_def ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def carrier_matI)

lemma proj_apply [simp]:
  "proj0 *\<^sub>v e0 = e0" "proj0 *\<^sub>v e1 = 0\<^sub>v 2" "proj1 *\<^sub>v e0 = 0\<^sub>v 2" "proj1 *\<^sub>v e1 = e1"
proof -
  have z: "(0::complex) \<cdot>\<^sub>v e0 = 0\<^sub>v 2" "(0::complex) \<cdot>\<^sub>v e1 = 0\<^sub>v 2" by (auto intro!: eq_vecI)
  show "proj0 *\<^sub>v e0 = e0" "proj0 *\<^sub>v e1 = 0\<^sub>v 2" "proj1 *\<^sub>v e0 = 0\<^sub>v 2" "proj1 *\<^sub>v e1 = e1"
    by (simp_all add: proj0_def proj1_def outer_prod_mult_vec z)
qed

lemma bell_state_e: "bell_state = (1 / csqrt 2) \<cdot>\<^sub>v (tensor_vec e0 e0 + tensor_vec e1 e1)"
  unfolding bell_state_def e0_def e1_def ..

lemma tensor_zero_left: "dim_vec w = 2 \<Longrightarrow> tensor_vec (0\<^sub>v 2) w = 0\<^sub>v 4"
  by (rule eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim)

lemma tensor_zero_right: "dim_vec v = 2 \<Longrightarrow> tensor_vec v (0\<^sub>v 2) = 0\<^sub>v 4"
  by (rule eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim)

lemma A_meas_bell:
  "(proj0 \<Otimes> 1\<^sub>m 2) *\<^sub>v bell_state = (1 / csqrt 2) \<cdot>\<^sub>v tensor_vec e0 e0"
  "(proj1 \<Otimes> 1\<^sub>m 2) *\<^sub>v bell_state = (1 / csqrt 2) \<cdot>\<^sub>v tensor_vec e1 e1"
proof -
  have c: "\<And>P. P \<in> carrier_mat 2 2 \<Longrightarrow> P \<Otimes> 1\<^sub>m 2 \<in> carrier_mat 4 4" by auto
  have t: "\<And>a b. dim_vec a = 2 \<Longrightarrow> dim_vec b = 2 \<Longrightarrow> tensor_vec a b \<in> carrier_vec 4"
    by (auto intro: carrier_vecI simp: tensor_vec_dim)
  have m: "\<And>P a b. P \<in> carrier_mat 2 2 \<Longrightarrow> dim_vec a = 2 \<Longrightarrow> dim_vec b = 2 \<Longrightarrow>
              (P \<Otimes> 1\<^sub>m 2) *\<^sub>v tensor_vec a b = tensor_vec (P *\<^sub>v a) b"
    by (rule tensor_mat_vec_mult_right_id) auto
  have one: "\<And>v :: complex Matrix.vec. v \<in> carrier_vec 4 \<Longrightarrow> 0\<^sub>v 4 + v = v" "\<And>v :: complex Matrix.vec. v \<in> carrier_vec 4 \<Longrightarrow> v + 0\<^sub>v 4 = v"
    by auto
  show "(proj0 \<Otimes> 1\<^sub>m 2) *\<^sub>v bell_state = (1 / csqrt 2) \<cdot>\<^sub>v tensor_vec e0 e0"
    unfolding bell_state_e
    using mult_mat_vec[OF c[OF proj_carrier(1)] add_carrier_vec[OF t t]]
      mult_add_distrib_mat_vec[OF c[OF proj_carrier(1)] t t]
    by (simp add: m tensor_zero_left one t)
  show "(proj1 \<Otimes> 1\<^sub>m 2) *\<^sub>v bell_state = (1 / csqrt 2) \<cdot>\<^sub>v tensor_vec e1 e1"
    unfolding bell_state_e
    using mult_mat_vec[OF c[OF proj_carrier(2)] add_carrier_vec[OF t t]]
      mult_add_distrib_mat_vec[OF c[OF proj_carrier(2)] t t]
    by (simp add: m tensor_zero_left one t)
qed

lemma tensor_e_norm: "\<parallel>tensor_vec e0 e0\<parallel> = 1" "\<parallel>tensor_vec e1 e1\<parallel> = 1"
proof -
  have n1: "\<And>v. \<langle>v|v\<rangle> = 1 \<Longrightarrow> \<parallel>v\<parallel> = 1"
  proof -
    fix v assume "\<langle>v|v\<rangle> = 1"
    hence "complex_of_real (\<parallel>v\<parallel>\<^sup>2) = 1" using cpx_vec_length_inner_prod[of v] by simp
    hence "\<parallel>v\<parallel>\<^sup>2 = 1" by (metis of_real_eq_1_iff)
    moreover have "\<parallel>v\<parallel> \<ge> 0" unfolding cpx_vec_length_def by (simp add: sum_nonneg)
    ultimately show "\<parallel>v\<parallel> = 1" by (smt (verit) power2_eq_1_iff)
  qed
  have t: "\<And>a. dim_vec a = 2 \<Longrightarrow> \<langle>a|a\<rangle> = 1 \<Longrightarrow> \<langle>tensor_vec a a|tensor_vec a a\<rangle> = 1"
  proof -
    fix a :: "complex Matrix.vec" assume d: "dim_vec a = 2" and a: "\<langle>a|a\<rangle> = 1"
    have "\<langle>tensor_vec a a|tensor_vec a a\<rangle> = \<langle>a|a\<rangle> * \<langle>a|a\<rangle>" by (rule tensor_inner_prod[OF d d d d])
    thus "\<langle>tensor_vec a a|tensor_vec a a\<rangle> = 1" unfolding a by simp
  qed
  show "\<parallel>tensor_vec e0 e0\<parallel> = 1" "\<parallel>tensor_vec e1 e1\<parallel> = 1"
    by (rule n1, rule t, simp_all)+
qed

text \<open>D9-6: A measures $\ketbra00,\ketbra11$ on the shared state $\gamma$: each outcome has
probability $\tfrac12$, and $\gamma$ collapses to $e_0\otimes e_0$ resp.\ $e_1\otimes e_1$, after
which B's measurement $I\otimes M_m$ gives A's outcome with probability $1$.\<close>

theorem bell_measurement:
  "meas_prob (proj0 \<Otimes> 1\<^sub>m 2) bell_state = 1/2"
  "meas_prob (proj1 \<Otimes> 1\<^sub>m 2) bell_state = 1/2"
  "post_meas_state (proj0 \<Otimes> 1\<^sub>m 2) bell_state = tensor_vec e0 e0"
  "post_meas_state (proj1 \<Otimes> 1\<^sub>m 2) bell_state = tensor_vec e1 e1"
  "meas_prob (1\<^sub>m 2 \<Otimes> proj0) (tensor_vec e0 e0) = 1"
  "meas_prob (1\<^sub>m 2 \<Otimes> proj1) (tensor_vec e1 e1) = 1"
proof -
  have s: "cmod (1 / csqrt 2) = 1 / sqrt 2" "cmod (1 / complex_of_real (sqrt 2)) = 1 / sqrt 2"
    by (simp_all add: norm_divide)
  show "meas_prob (proj0 \<Otimes> 1\<^sub>m 2) bell_state = 1/2" "meas_prob (proj1 \<Otimes> 1\<^sub>m 2) bell_state = 1/2"
    unfolding meas_prob_def A_meas_bell by (simp_all add: cpx_vec_length_smult tensor_e_norm s power_divide)
  have r: "1 / complex_of_real (1 / sqrt 2) * (1 / csqrt 2) = 1"
          "1 / complex_of_real (1 / sqrt 2) * (1 / complex_of_real (sqrt 2)) = 1"
    by (simp_all add: field_simps)
  show "post_meas_state (proj0 \<Otimes> 1\<^sub>m 2) bell_state = tensor_vec e0 e0"
       "post_meas_state (proj1 \<Otimes> 1\<^sub>m 2) bell_state = tensor_vec e1 e1"
    unfolding post_meas_state_def A_meas_bell by (simp_all add: cpx_vec_length_smult tensor_e_norm s r smult_smult_assoc)
  have m: "\<And>P a b. P \<in> carrier_mat 2 2 \<Longrightarrow> dim_vec a = 2 \<Longrightarrow> dim_vec b = 2 \<Longrightarrow>
              (1\<^sub>m 2 \<Otimes> P) *\<^sub>v tensor_vec a b = tensor_vec a (P *\<^sub>v b)"
  proof -
    fix P :: "complex Matrix.mat" and a b :: "complex Matrix.vec" assume P: "P \<in> carrier_mat 2 2" and a: "dim_vec a = 2" and b: "dim_vec b = 2"
    have ac: "a \<in> carrier_vec 2" by (rule carrier_vecI[OF a])
    show "(1\<^sub>m 2 \<Otimes> P) *\<^sub>v tensor_vec a b = tensor_vec a (P *\<^sub>v b)"
      using tensor_mat_vec_mult[OF one_carrier_mat P a b] ac by simp
  qed
  show "meas_prob (1\<^sub>m 2 \<Otimes> proj0) (tensor_vec e0 e0) = 1" "meas_prob (1\<^sub>m 2 \<Otimes> proj1) (tensor_vec e1 e1) = 1"
    unfolding meas_prob_def by (simp_all add: m tensor_e_norm)
qed

lemma proj_explicit:
  "proj0 = Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then 1 else 0)"
  "proj1 = Matrix.mat 2 2 (\<lambda>(i,j). if i = 1 \<and> j = 1 then 1 else 0)"
  by (auto intro!: eq_matI simp: proj0_def proj1_def outer_prod_index e0_def e1_def
      ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def)

lemma proj_measurement_system: "measurement_system 2 [proj0, proj1]"
  unfolding measurement_system_def proj_explicit
  by (auto intro!: eq_matI simp: dagger_def scalar_prod_def less_2_cases_iff numeral_2_eq_2 lessThan_Suc)

subsection \<open>Day 11: SWAP from three CNOTs\<close>

lemma less4_cases: "(i::nat) < 4 \<longleftrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
  by auto

text \<open>$\mathrm{CNOT}'$ is CNOT controlled by the second qubit.\<close>

definition CNOT' :: "complex Matrix.mat" where
  "CNOT' = Matrix.mat 4 4 (\<lambda>(i,j). if (i,j) \<in> {(0,0),(1,3),(2,2),(3,1)} then 1 else 0)"

text \<open>D11-3: $\mathrm{SWAP}=\mathrm{CNOT}\cdot\mathrm{CNOT}'\cdot\mathrm{CNOT}$
(\<^const>\<open>SWAP\<close> is the AFP's).\<close>

theorem SWAP_three_CNOTs: "SWAP = CNOT * CNOT' * CNOT"
  by (rule eq_matI)
     (auto simp: SWAP_def CNOT_def CNOT'_def scalar_prod_def sum.atLeast0_lessThan_Suc
        lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq)

lemma SWAP_basis:
  assumes "a < 2" "b < 2"
  shows "SWAP *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 b) (unit_vec 2 a)"
proof -
  have "\<forall>a \<in> {0,1}. \<forall>b \<in> {0,1::nat}.
          SWAP *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 b) (unit_vec 2 a)"
    by (auto intro!: eq_vecI simp: SWAP_def tensor_vec_index tensor_vec_dim scalar_prod_def
        sum.atLeast0_lessThan_Suc lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq less4_cases)
  moreover have "a \<in> {0,1}" "b \<in> {0,1}" using assms by auto
  ultimately show ?thesis by blast
qed

lemma CNOT'_basis:
  assumes "a < 2" "b < 2"
  shows "CNOT' *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 ((a + b) mod 2)) (unit_vec 2 b)"
proof -
  have "\<forall>a \<in> {0,1}. \<forall>b \<in> {0,1::nat}.
          CNOT' *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 ((a + b) mod 2)) (unit_vec 2 b)"
    by (auto intro!: eq_vecI simp: CNOT'_def tensor_vec_index tensor_vec_dim scalar_prod_def
        sum.atLeast0_lessThan_Suc lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq less4_cases)
  moreover have "a \<in> {0,1}" "b \<in> {0,1}" using assms by auto
  ultimately show ?thesis by blast
qed

end
