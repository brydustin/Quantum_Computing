theory Day25_Arveson_Correspondence
  imports Day24_Operator_Systems
begin

text \<open>Days 24--25: Arveson's correspondence between maps $\Phi:S\to M_d$ and functionals
$S_\Phi:M_d(S)\to\C$, $S_\Phi((A_{ij}))=\frac1d\sum_{i,j}\Phi(A_{ij})_{ij}$, with inverse
$f\mapsto\Phi_f$, $\Phi_f(M)=d\,(f(E_{ij}\otimes M))_{ij}$.\<close>

subsection \<open>Finite sums of matrices\<close>

definition msum :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> complex Matrix.mat) \<Rightarrow> 'a list \<Rightarrow> complex Matrix.mat" where
  "msum r c g xs = foldr (\<lambda>x acc. g x + acc) xs (0\<^sub>m r c)"

lemma msum_Nil [simp]: "msum r c g [] = 0\<^sub>m r c"
  by (simp add: msum_def)

lemma msum_Cons [simp]: "msum r c g (x # xs) = g x + msum r c g xs"
  by (simp add: msum_def)

lemma msum_carrier: "\<forall>x \<in> set xs. g x \<in> carrier_mat r c \<Longrightarrow> msum r c g xs \<in> carrier_mat r c"
  by (induction xs) auto

lemma msum_index:
  assumes "\<forall>x \<in> set xs. g x \<in> carrier_mat r c" and "i < r" and "j < c"
  shows "msum r c g xs $$ (i,j) = (\<Sum>x\<leftarrow>xs. g x $$ (i,j))"
  unfolding msum_def by (rule foldr_add_mat_index_rect[OF assms])

lemma msum_in_os:
  assumes OS: "operator_system n OS" and g: "\<forall>x \<in> set xs. g x \<in> OS"
  shows "msum n n g xs \<in> OS"
  using g by (induction xs) (auto intro: operator_systemD(4)[OF OS] operator_system_zero[OF OS])

lemma lin_on_zero:
  assumes OS: "operator_system n OS" and L: "lin_on n d OS \<Phi>"
  shows "\<Phi> (0\<^sub>m n n) = 0\<^sub>m d d"
proof -
  have I: "1\<^sub>m n \<in> OS" by (rule operator_systemD(2)[OF OS])
  have "\<Phi> (0 \<cdot>\<^sub>m 1\<^sub>m n) = 0 \<cdot>\<^sub>m \<Phi> (1\<^sub>m n)" using L I unfolding lin_on_def by blast
  moreover have "(0 :: complex) \<cdot>\<^sub>m 1\<^sub>m n = 0\<^sub>m n n" by (rule eq_matI) simp_all
  moreover have "(0 :: complex) \<cdot>\<^sub>m \<Phi> (1\<^sub>m n) = 0\<^sub>m d d" using L I unfolding lin_on_def by (intro eq_matI) auto
  ultimately show ?thesis by simp
qed

lemma lin_on_msum:
  assumes OS: "operator_system n OS" and L: "lin_on n d OS \<Phi>" and g: "\<forall>x \<in> set xs. g x \<in> OS"
  shows "\<Phi> (msum n n g xs) = msum d d (\<lambda>x. \<Phi> (g x)) xs"
  using g
proof (induction xs)
  case Nil show ?case using lin_on_zero[OF OS L] by simp
next
  case (Cons x xs)
  have gx: "g x \<in> OS" and rest: "\<forall>x \<in> set xs. g x \<in> OS" using Cons.prems by auto
  have "\<Phi> (g x + msum n n g xs) = \<Phi> (g x) + \<Phi> (msum n n g xs)"
    using L gx msum_in_os[OF OS rest] unfolding lin_on_def by blast
  thus ?case using Cons.IH[OF rest] by simp
qed

lemma sum_list_product_upt:
  "(\<Sum>x\<leftarrow>List.product [0..<a] [0..<b]. h x) = (\<Sum>i<a. \<Sum>j<b. h (i,j))"
proof -
  have "(\<Sum>x\<leftarrow>List.product [0..<a] [0..<b]. h x) = sum h ({..<a} \<times> {..<b})"
    by (subst sum_list_distinct_conv_sum_set) (auto simp: distinct_product atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<a. \<Sum>j<b. h (i,j))" unfolding sum.cartesian_product by simp
  finally show ?thesis .
qed

lemma sum_delta2:
  fixes a d b e :: nat
  assumes a: "a < d" and b: "b < e"
  shows "(\<Sum>i<d. \<Sum>j<e. if i = a \<and> j = b then v else 0) = v"
proof -
  have "\<And>i. (\<Sum>j<e. if i = a \<and> j = b then v else 0) = (if i = a then v else 0)"
    using b by (case_tac "i = a") (simp_all add: sum.delta)
  thus ?thesis using a by (simp add: sum.delta)
qed

subsection \<open>$E_{ij}\otimes M$ and the block decomposition\<close>

definition unit_block :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "unit_block d n i j M = Matrix.mat (d * n) (d * n)
     (\<lambda>(r,c). if r div n = i \<and> c div n = j then M $$ (r mod n, c mod n) else 0)"

lemma unit_block_carrier [simp]: "unit_block d n i j M \<in> carrier_mat (d * n) (d * n)"
  by (simp add: unit_block_def)

lemma unit_block_dims [simp]: "dim_row (unit_block d n i j M) = d * n" "dim_col (unit_block d n i j M) = d * n"
  by (simp_all add: unit_block_def)

text \<open>\<open>unit_block d n i j M\<close> is $E_{ij}\otimes M$.\<close>

lemma unit_block_tensor:
  assumes M: "M \<in> carrier_mat n n" and i: "i < d" and j: "j < d"
  shows "unit_block d n i j M = Tensor.tensor_mat (Matrix.mat d d (\<lambda>(a,b). if a = i \<and> b = j then 1 else 0)) M"
proof (rule eq_matI)
  fix r c assume "r < dim_row (Tensor.tensor_mat (Matrix.mat d d (\<lambda>(a,b). if a = i \<and> b = j then 1 else 0)) M)"
    "c < dim_col (Tensor.tensor_mat (Matrix.mat d d (\<lambda>(a,b). if a = i \<and> b = j then 1 else 0)) M)"
  hence r: "r < d * n" and c: "c < d * n" using M by simp_all
  have n: "0 < n" using r by (cases n) auto
  have "r div n < d" "c div n < d" using r c by (simp_all add: less_mult_imp_div_less mult.commute)
  thus "unit_block d n i j M $$ (r,c)
        = Tensor.tensor_mat (Matrix.mat d d (\<lambda>(a,b). if a = i \<and> b = j then 1 else 0)) M $$ (r,c)"
    using r c n M i by (subst index_tensor_mat[where rA=d and cA=d and rB=n and cB=n]) (auto simp: unit_block_def)
qed (use M in simp_all)

lemma block_unit_block:
  assumes M: "M \<in> carrier_mat n n" and a: "a < d" and b: "b < d"
  shows "block_of_mat n (unit_block d n i j M) a b = (if a = i \<and> b = j then M else 0\<^sub>m n n)"
proof (rule eq_matI)
  fix r c assume "r < dim_row (if a = i \<and> b = j then M else 0\<^sub>m n n)" "c < dim_col (if a = i \<and> b = j then M else 0\<^sub>m n n)"
  hence r: "r < n" and c: "c < n" using M by (simp_all split: if_splits)
  show "block_of_mat n (unit_block d n i j M) a b $$ (r,c) = (if a = i \<and> b = j then M else 0\<^sub>m n n) $$ (r,c)"
    using mult_index_lt[OF a r] mult_index_div_mod[OF r] mult_index_lt[OF b c] mult_index_div_mod[OF c] r c M by (simp add: block_of_mat_index unit_block_def)
qed (use M in simp_all)

lemma unit_block_Mp:
  assumes OS: "operator_system n OS" and M: "M \<in> OS" and i: "i < d" and j: "j < d"
  shows "unit_block d n i j M \<in> Mp d n OS"
  unfolding Mp_def using block_unit_block operator_systemD(1)[OF OS] M operator_system_zero[OF OS] by auto

lemma block_decomposition:
  assumes A: "A \<in> carrier_mat (d * n) (d * n)"
  shows "A = msum (d * n) (d * n) (\<lambda>(i,j). unit_block d n i j (block_of_mat n A i j)) (List.product [0..<d] [0..<d])"
proof -
  have mc: "msum (d * n) (d * n) (\<lambda>(i,j). unit_block d n i j (block_of_mat n A i j)) (List.product [0..<d] [0..<d])
            \<in> carrier_mat (d * n) (d * n)" by (rule msum_carrier) (auto simp: split_beta)
  show ?thesis
  proof (rule eq_matI)
  fix r c assume "r < dim_row (msum (d * n) (d * n) (\<lambda>(i,j). unit_block d n i j (block_of_mat n A i j)) (List.product [0..<d] [0..<d]))"
    "c < dim_col (msum (d * n) (d * n) (\<lambda>(i,j). unit_block d n i j (block_of_mat n A i j)) (List.product [0..<d] [0..<d]))"
  hence r: "r < d * n" and c: "c < d * n" using mc by simp_all
  have n: "0 < n" using r by (cases n) auto
  have rd: "r div n < d" and cd: "c div n < d" using r c by (simp_all add: less_mult_imp_div_less mult.commute)
  have "msum (d * n) (d * n) (\<lambda>(i,j). unit_block d n i j (block_of_mat n A i j)) (List.product [0..<d] [0..<d]) $$ (r,c)
        = (\<Sum>i<d. \<Sum>j<d. unit_block d n i j (block_of_mat n A i j) $$ (r,c))"
    by (subst msum_index) (auto simp: r c sum_list_product_upt[of _ d d] split_beta)
  also have "\<dots> = (\<Sum>i<d. \<Sum>j<d. if i = r div n \<and> j = c div n then A $$ (r,c) else 0)"
  proof (intro sum.cong refl)
    fix i j
    have "(r div n) * n + r mod n = r" "(c div n) * n + c mod n = c" by simp_all
    thus "unit_block d n i j (block_of_mat n A i j) $$ (r,c) = (if i = r div n \<and> j = c div n then A $$ (r,c) else 0)"
      using r c n by (auto simp: unit_block_def block_of_mat_index)
  qed
  also have "\<dots> = A $$ (r,c)" by (rule sum_delta2[OF rd cd])
  finally show "A $$ (r,c) = msum (d * n) (d * n) (\<lambda>(i,j). unit_block d n i j (block_of_mat n A i j)) (List.product [0..<d] [0..<d]) $$ (r,c)" ..
  qed (use A mc in simp_all)
qed

subsection \<open>The correspondence\<close>

definition arveson_functional :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex" where
  "arveson_functional n d \<Phi> A = (\<Sum>i<d. \<Sum>j<d. \<Phi> (block_of_mat n A i j) $$ (i,j)) / of_nat d"

definition arveson_map :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "arveson_map n d f M = Matrix.mat d d (\<lambda>(i,j). of_nat d * f (unit_block d n i j M))"

definition lin_fun_on :: "complex Matrix.mat set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex) \<Rightarrow> bool" where
  "lin_fun_on TS f \<longleftrightarrow> (\<forall>A \<in> TS. \<forall>B \<in> TS. f (A + B) = f A + f B) \<and> (\<forall>A \<in> TS. \<forall>c. f (c \<cdot>\<^sub>m A) = c * f A)"

definition positive_fun_on :: "complex Matrix.mat set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex) \<Rightarrow> bool" where
  "positive_fun_on TS f \<longleftrightarrow> (\<forall>A \<in> TS. psd A \<longrightarrow> 0 \<le> f A)"

lemma amplification_idx:
  assumes r: "r < q" and s: "s < q" and i: "i < d" and j: "j < d"
  shows "amplification n d q \<Phi> A $$ (r * d + i, s * d + j) = \<Phi> (block_of_mat n A r s) $$ (i,j)"
  using mult_index_lt[OF r i] mult_index_div_mod[OF i] mult_index_lt[OF s j] mult_index_div_mod[OF j] by (simp add: amplification_def)

lemma arveson_map_index: "i < d \<Longrightarrow> j < d \<Longrightarrow> arveson_map n d f M $$ (i,j) = of_nat d * f (unit_block d n i j M)"
  by (simp add: arveson_map_def)

lemma arveson_map_carrier [simp]: "arveson_map n d f M \<in> carrier_mat d d"
  by (simp add: arveson_map_def)

lemma arveson_map_dims [simp]: "dim_row (arveson_map n d f M) = d" "dim_col (arveson_map n d f M) = d"
  by (simp_all add: arveson_map_def)

lemma lin_fun_zero:
  assumes TS: "operator_system N TS" and f: "lin_fun_on TS f"
  shows "f (0\<^sub>m N N) = 0"
proof -
  have I: "1\<^sub>m N \<in> TS" by (rule operator_systemD(2)[OF TS])
  have "f (0 \<cdot>\<^sub>m 1\<^sub>m N) = 0 * f (1\<^sub>m N)" using f I unfolding lin_fun_on_def by blast
  moreover have "(0 :: complex) \<cdot>\<^sub>m 1\<^sub>m N = 0\<^sub>m N N" by (rule eq_matI) simp_all
  ultimately show ?thesis by simp
qed

lemma lin_fun_msum:
  assumes TS: "operator_system N TS" and f: "lin_fun_on TS f" and g: "\<forall>x \<in> set xs. g x \<in> TS"
  shows "f (msum N N g xs) = (\<Sum>x\<leftarrow>xs. f (g x))"
  using g
proof (induction xs)
  case Nil show ?case using lin_fun_zero[OF TS f] by simp
next
  case (Cons x xs)
  have gx: "g x \<in> TS" and rest: "\<forall>x \<in> set xs. g x \<in> TS" using Cons.prems by auto
  have "f (g x + msum N N g xs) = f (g x) + f (msum N N g xs)"
    using f gx msum_in_os[OF TS rest] unfolding lin_fun_on_def by blast
  thus ?case using Cons.IH[OF rest] by simp
qed

text \<open>$S_{\Phi_f}=f$ on $M_d(S)$.\<close>

theorem arveson_functional_of_map:
  assumes OS: "operator_system n OS" and f: "lin_fun_on (Mp d n OS) f" and A: "A \<in> Mp d n OS" and d: "0 < d"
  shows "arveson_functional n d (arveson_map n d f) A = f A"
proof -
  have TS: "operator_system (d * n) (Mp d n OS)" by (rule Mp_operator_system[OF OS])
  have Ac: "A \<in> carrier_mat (d * n) (d * n)" and Ab: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> block_of_mat n A i j \<in> OS"
    using A unfolding Mp_def by blast+
  let ?g = "\<lambda>(i,j). unit_block d n i j (block_of_mat n A i j)"
  have g: "\<forall>x \<in> set (List.product [0..<d] [0..<d]). ?g x \<in> Mp d n OS"
    using unit_block_Mp[OF OS] Ab by auto
  have "arveson_functional n d (arveson_map n d f) A
        = (\<Sum>i<d. \<Sum>j<d. of_nat d * f (unit_block d n i j (block_of_mat n A i j))) / of_nat d"
    unfolding arveson_functional_def by (simp add: arveson_map_index)
  also have "\<dots> = (\<Sum>i<d. \<Sum>j<d. f (unit_block d n i j (block_of_mat n A i j)))"
    using d by (simp add: sum_distrib_left[symmetric])
  also have "\<dots> = (\<Sum>x\<leftarrow>List.product [0..<d] [0..<d]. f (?g x))"
    by (simp add: sum_list_product_upt split_beta)
  also have "\<dots> = f (msum (d * n) (d * n) ?g (List.product [0..<d] [0..<d]))"
    by (rule lin_fun_msum[OF TS f g, symmetric])
  also have "\<dots> = f A" using block_decomposition[OF Ac] by simp
  finally show ?thesis .
qed

text \<open>$\Phi_{S_\Phi}=\Phi$ on $S$.\<close>

theorem arveson_map_of_functional:
  assumes OS: "operator_system n OS" and L: "lin_on n d OS \<Phi>" and M: "M \<in> OS" and d: "0 < d"
  shows "arveson_map n d (arveson_functional n d \<Phi>) M = \<Phi> M"
proof (rule eq_matI)
  have Mc: "M \<in> carrier_mat n n" using operator_systemD(1)[OF OS] M by auto
  have PhiM: "\<Phi> M \<in> carrier_mat d d" using L M unfolding lin_on_def by blast
  show "dim_row (arveson_map n d (arveson_functional n d \<Phi>) M) = dim_row (\<Phi> M)"
    "dim_col (arveson_map n d (arveson_functional n d \<Phi>) M) = dim_col (\<Phi> M)" using PhiM by simp_all
  fix i j assume "i < dim_row (\<Phi> M)" "j < dim_col (\<Phi> M)"
  hence i: "i < d" and j: "j < d" using PhiM by simp_all
  have z: "\<Phi> (0\<^sub>m n n) = 0\<^sub>m d d" by (rule lin_on_zero[OF OS L])
  have "arveson_map n d (arveson_functional n d \<Phi>) M $$ (i,j)
        = (\<Sum>a<d. \<Sum>b<d. \<Phi> (block_of_mat n (unit_block d n i j M) a b) $$ (a,b))"
    using d i j by (simp add: arveson_map_index arveson_functional_def)
  also have "\<dots> = (\<Sum>a<d. \<Sum>b<d. if a = i \<and> b = j then \<Phi> M $$ (i,j) else 0)"
    by (intro sum.cong refl) (use z in \<open>auto simp: block_unit_block[OF Mc]\<close>)
  also have "\<dots> = \<Phi> M $$ (i,j)" by (rule sum_delta2[OF i j])
  finally show "arveson_map n d (arveson_functional n d \<Phi>) M $$ (i,j) = \<Phi> M $$ (i,j)" .
qed

lemma unit_block_add:
  assumes M: "M \<in> carrier_mat n n" and M': "M' \<in> carrier_mat n n"
  shows "unit_block d n i j (M + M') = unit_block d n i j M + unit_block d n i j M'"
proof (rule eq_matI)
  fix r k assume "r < dim_row (unit_block d n i j M + unit_block d n i j M')"
    "k < dim_col (unit_block d n i j M + unit_block d n i j M')"
  hence r: "r < d * n" and k: "k < d * n" by simp_all
  have n: "0 < n" using r by (cases n) auto
  show "unit_block d n i j (M + M') $$ (r,k) = (unit_block d n i j M + unit_block d n i j M') $$ (r,k)"
    using r k n M M' by (auto simp: unit_block_def)
qed simp_all

lemma unit_block_smult:
  assumes M: "M \<in> carrier_mat n n"
  shows "unit_block d n i j (c \<cdot>\<^sub>m M) = c \<cdot>\<^sub>m unit_block d n i j M"
proof (rule eq_matI)
  fix r k assume "r < dim_row (c \<cdot>\<^sub>m unit_block d n i j M)" "k < dim_col (c \<cdot>\<^sub>m unit_block d n i j M)"
  hence r: "r < d * n" and k: "k < d * n" by simp_all
  have n: "0 < n" using r by (cases n) auto
  show "unit_block d n i j (c \<cdot>\<^sub>m M) $$ (r,k) = (c \<cdot>\<^sub>m unit_block d n i j M) $$ (r,k)"
    using r k n M by (auto simp: unit_block_def)
qed simp_all

lemma arveson_map_lin:
  assumes OS: "operator_system n OS" and f: "lin_fun_on (Mp d n OS) f"
  shows "lin_on n d OS (arveson_map n d f)"
  unfolding lin_on_def
proof (intro conjI ballI allI)
  fix M assume "M \<in> OS" thus "arveson_map n d f M \<in> carrier_mat d d" by simp
next
  fix M M' assume M: "M \<in> OS" and M': "M' \<in> OS"
  have Mc: "M \<in> carrier_mat n n" and M'c: "M' \<in> carrier_mat n n" using operator_systemD(1)[OF OS] M M' by auto
  show "arveson_map n d f (M + M') = arveson_map n d f M + arveson_map n d f M'"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (arveson_map n d f M + arveson_map n d f M')" "j < dim_col (arveson_map n d f M + arveson_map n d f M')"
    hence i: "i < d" and j: "j < d" by simp_all
    have "f (unit_block d n i j (M + M')) = f (unit_block d n i j M) + f (unit_block d n i j M')"
      unfolding unit_block_add[OF Mc M'c] using f unit_block_Mp[OF OS M i j] unit_block_Mp[OF OS M' i j]
      unfolding lin_fun_on_def by blast
    thus "arveson_map n d f (M + M') $$ (i,j) = (arveson_map n d f M + arveson_map n d f M') $$ (i,j)"
      using i j by (simp add: arveson_map_index distrib_left)
  qed simp_all
next
  fix M c assume M: "M \<in> OS"
  have Mc: "M \<in> carrier_mat n n" using operator_systemD(1)[OF OS] M by auto
  show "arveson_map n d f (c \<cdot>\<^sub>m M) = c \<cdot>\<^sub>m arveson_map n d f M"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (c \<cdot>\<^sub>m arveson_map n d f M)" "j < dim_col (c \<cdot>\<^sub>m arveson_map n d f M)"
    hence i: "i < d" and j: "j < d" by simp_all
    have "f (unit_block d n i j (c \<cdot>\<^sub>m M)) = c * f (unit_block d n i j M)"
      unfolding unit_block_smult[OF Mc] using f unit_block_Mp[OF OS M i j] unfolding lin_fun_on_def by blast
    thus "arveson_map n d f (c \<cdot>\<^sub>m M) $$ (i,j) = (c \<cdot>\<^sub>m arveson_map n d f M) $$ (i,j)"
      using i j by (simp add: arveson_map_index)
  qed simp_all
qed

lemma arveson_functional_lin:
  assumes OS: "operator_system n OS" and L: "lin_on n d OS \<Phi>"
  shows "lin_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
  unfolding lin_fun_on_def
proof (intro conjI ballI allI)
  fix A B assume A: "A \<in> Mp d n OS" and B: "B \<in> Mp d n OS"
  have Ac: "A \<in> carrier_mat (d * n) (d * n)" and Bc: "B \<in> carrier_mat (d * n) (d * n)"
    and Ab: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> block_of_mat n A i j \<in> OS"
    and Bb: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> block_of_mat n B i j \<in> OS" using A B unfolding Mp_def by blast+
  have "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> \<Phi> (block_of_mat n (A + B) i j) $$ (i,j)
          = \<Phi> (block_of_mat n A i j) $$ (i,j) + \<Phi> (block_of_mat n B i j) $$ (i,j)"
  proof -
    fix i j assume i: "i < d" and j: "j < d"
    have "\<Phi> (block_of_mat n (A + B) i j) = \<Phi> (block_of_mat n A i j) + \<Phi> (block_of_mat n B i j)"
      unfolding block_of_mat_add[OF Ac Bc i j] using L Ab[OF i j] Bb[OF i j] unfolding lin_on_def by blast
    moreover have "\<Phi> (block_of_mat n A i j) \<in> carrier_mat d d" "\<Phi> (block_of_mat n B i j) \<in> carrier_mat d d"
      using L Ab[OF i j] Bb[OF i j] unfolding lin_on_def by blast+
    ultimately show "\<Phi> (block_of_mat n (A + B) i j) $$ (i,j) = \<Phi> (block_of_mat n A i j) $$ (i,j) + \<Phi> (block_of_mat n B i j) $$ (i,j)"
      using i j by simp
  qed
  thus "arveson_functional n d \<Phi> (A + B) = arveson_functional n d \<Phi> A + arveson_functional n d \<Phi> B"
    unfolding arveson_functional_def by (simp add: sum.distrib add_divide_distrib)
next
  fix A c assume A: "A \<in> Mp d n OS"
  have Ac: "A \<in> carrier_mat (d * n) (d * n)" and Ab: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> block_of_mat n A i j \<in> OS"
    using A unfolding Mp_def by blast+
  have "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> \<Phi> (block_of_mat n (c \<cdot>\<^sub>m A) i j) $$ (i,j) = c * \<Phi> (block_of_mat n A i j) $$ (i,j)"
  proof -
    fix i j assume i: "i < d" and j: "j < d"
    have "\<Phi> (block_of_mat n (c \<cdot>\<^sub>m A) i j) = c \<cdot>\<^sub>m \<Phi> (block_of_mat n A i j)"
      unfolding block_of_mat_smult[OF Ac i j] using L Ab[OF i j] unfolding lin_on_def by blast
    moreover have "\<Phi> (block_of_mat n A i j) \<in> carrier_mat d d" using L Ab[OF i j] unfolding lin_on_def by blast
    ultimately show "\<Phi> (block_of_mat n (c \<cdot>\<^sub>m A) i j) $$ (i,j) = c * \<Phi> (block_of_mat n A i j) $$ (i,j)"
      using i j by simp
  qed
  thus "arveson_functional n d \<Phi> (c \<cdot>\<^sub>m A) = c * arveson_functional n d \<Phi> A"
    unfolding arveson_functional_def by (simp add: sum_distrib_left)
qed

lemma quad_split:
  fixes M :: "complex Matrix.mat" and w :: "complex Matrix.vec"
  assumes M: "M \<in> carrier_mat (q * d) (q * d)" and w: "dim_vec w = q * d"
  shows "\<langle>w | M *\<^sub>v w\<rangle> = (\<Sum>r<q. \<Sum>i<d. \<Sum>s<q. \<Sum>j<d.
           cnj (w $ (r * d + i)) * M $$ (r * d + i, s * d + j) * w $ (s * d + j))"
proof -
  have Mw: "dim_vec (M *\<^sub>v w) = q * d" using M by simp
  have "\<langle>w | M *\<^sub>v w\<rangle> = (\<Sum>x<q * d. cnj (w $ x) * (M *\<^sub>v w) $ x)"
    unfolding inner_prod_sum[OF w Mw] atLeast0LessThan ..
  also have "\<dots> = (\<Sum>x<q * d. \<Sum>y<q * d. cnj (w $ x) * M $$ (x,y) * w $ y)"
  proof (rule sum.cong[OF refl])
    fix x assume "x \<in> {..<q * d}"
    hence x: "x < q * d" by simp
    have "(M *\<^sub>v w) $ x = (\<Sum>y<q * d. M $$ (x,y) * w $ y)"
      using M w x by (simp add: scalar_prod_def atLeast0LessThan)
    thus "cnj (w $ x) * (M *\<^sub>v w) $ x = (\<Sum>y<q * d. cnj (w $ x) * M $$ (x,y) * w $ y)"
      by (simp add: sum_distrib_left mult_ac)
  qed
  also have "\<dots> = (\<Sum>r<q. \<Sum>i<d. \<Sum>s<q. \<Sum>j<d.
           cnj (w $ (r * d + i)) * M $$ (r * d + i, s * d + j) * w $ (s * d + j))"
    by (simp only: sum_split_mp)
  finally show ?thesis .
qed

subsection \<open>Theorem (Arveson): completely positive iff $d$-positive iff $S_\Phi$ positive\<close>

lemma if_zero_mult: "(if P then x else 0) * (y::complex) = (if P then x * y else 0)"
  by simp

lemma mult_if_zero: "(y::complex) * (if P then x else 0) = (if P then y * x else 0)"
  by simp

lemma cnj_if_zero: "cnj (if P then x else 0) = (if P then cnj x else 0)"
  by simp

lemma nonneg_of_real_quad:
  fixes z :: complex
  assumes "z \<in> \<real>" and "0 \<le> Re z" and d: "0 < d"
  shows "0 \<le> z / of_nat d"
proof -
  have "Im z = 0" using assms(1) by (simp add: complex_is_Real_iff)
  thus ?thesis using assms(2) d by (simp add: less_eq_complex_def)
qed

lemma diag_quad_amplification:
  fixes d n :: nat and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" and A :: "complex Matrix.mat"
  defines "v \<equiv> Matrix.vec (d * d) (\<lambda>x. if x div d = x mod d then 1 else (0::complex))"
  shows "\<langle>v | amplification n d d \<Phi> A *\<^sub>v v\<rangle> = (\<Sum>i<d. \<Sum>j<d. \<Phi> (block_of_mat n A i j) $$ (i,j))"
proof -
  let ?M = "amplification n d d \<Phi> A"
  have Mc: "?M \<in> carrier_mat (d * d) (d * d)" by (rule amplification_carrier)
  have vd: "dim_vec v = d * d" unfolding v_def by simp
  have vidx: "\<And>r i. r < d \<Longrightarrow> i < d \<Longrightarrow> v $ (r * d + i) = (if i = r then 1 else 0)"
    unfolding v_def using mult_index_lt mult_index_div_mod by auto
  have inner: "\<And>r. r < d \<Longrightarrow> (\<Sum>i<d. \<Sum>s<d. \<Sum>j<d. cnj (v $ (r * d + i)) * ?M $$ (r * d + i, s * d + j) * v $ (s * d + j))
                 = (\<Sum>s<d. ?M $$ (r * d + r, s * d + s))"
  proof -
    fix r assume r: "r < d"
    have "(\<Sum>i<d. \<Sum>s<d. \<Sum>j<d. cnj (v $ (r * d + i)) * ?M $$ (r * d + i, s * d + j) * v $ (s * d + j))
          = (\<Sum>i<d. if i = r then (\<Sum>s<d. \<Sum>j<d. if j = s then ?M $$ (r * d + i, s * d + j) else 0) else 0)"
      using r by (intro sum.cong refl) (simp add: vidx if_zero_mult mult_if_zero cnj_if_zero)
    also have "\<dots> = (\<Sum>s<d. \<Sum>j<d. if j = s then ?M $$ (r * d + r, s * d + j) else 0)"
      using r by (simp add: sum.delta)
    also have "\<dots> = (\<Sum>s<d. ?M $$ (r * d + r, s * d + s))" by (simp add: sum.delta)
    finally show "(\<Sum>i<d. \<Sum>s<d. \<Sum>j<d. cnj (v $ (r * d + i)) * ?M $$ (r * d + i, s * d + j) * v $ (s * d + j))
                 = (\<Sum>s<d. ?M $$ (r * d + r, s * d + s))" .
  qed
  have "\<langle>v | ?M *\<^sub>v v\<rangle> = (\<Sum>r<d. \<Sum>s<d. ?M $$ (r * d + r, s * d + s))"
    unfolding quad_split[OF Mc vd] by (rule sum.cong[OF refl]) (simp add: inner)
  also have "\<dots> = (\<Sum>r<d. \<Sum>s<d. \<Phi> (block_of_mat n A r s) $$ (r,s))"
    by (intro sum.cong refl) (simp add: amplification_idx)
  finally show ?thesis .
qed

lemma dpos_imp_functional_pos:
  assumes OS: "operator_system n OS" and d: "0 < d" and P: "p_positive_on n d d OS \<Phi>"
  shows "positive_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
  unfolding positive_fun_on_def
proof (intro ballI impI)
  fix A assume A: "A \<in> Mp d n OS" and Apsd: "psd A"
  let ?M = "amplification n d d \<Phi> A"
  have Mc: "?M \<in> carrier_mat (d * d) (d * d)" by (rule amplification_carrier)
  have Mpsd: "psd ?M" using P A Apsd unfolding p_positive_on_def by blast
  define v where "v = Matrix.vec (d * d) (\<lambda>x. if x div d = x mod d then 1 else (0::complex))"
  have vd: "dim_vec v = d * d" unfolding v_def by simp
  have vidx: "\<And>r i. r < d \<Longrightarrow> i < d \<Longrightarrow> v $ (r * d + i) = (if i = r then 1 else 0)"
    unfolding v_def using mult_index_lt mult_index_div_mod by auto
  have inner: "\<And>r. r < d \<Longrightarrow> (\<Sum>i<d. \<Sum>s<d. \<Sum>j<d. cnj (v $ (r * d + i)) * ?M $$ (r * d + i, s * d + j) * v $ (s * d + j))
                 = (\<Sum>s<d. ?M $$ (r * d + r, s * d + s))"
  proof -
    fix r assume r: "r < d"
    have "(\<Sum>i<d. \<Sum>s<d. \<Sum>j<d. cnj (v $ (r * d + i)) * ?M $$ (r * d + i, s * d + j) * v $ (s * d + j))
          = (\<Sum>i<d. if i = r then (\<Sum>s<d. \<Sum>j<d. if j = s then ?M $$ (r * d + i, s * d + j) else 0) else 0)"
      using r by (intro sum.cong refl) (simp add: vidx if_zero_mult mult_if_zero cnj_if_zero)
    also have "\<dots> = (\<Sum>s<d. \<Sum>j<d. if j = s then ?M $$ (r * d + r, s * d + j) else 0)"
      using r by (simp add: sum.delta)
    also have "\<dots> = (\<Sum>s<d. ?M $$ (r * d + r, s * d + s))" by (simp add: sum.delta)
    finally show "(\<Sum>i<d. \<Sum>s<d. \<Sum>j<d. cnj (v $ (r * d + i)) * ?M $$ (r * d + i, s * d + j) * v $ (s * d + j))
                 = (\<Sum>s<d. ?M $$ (r * d + r, s * d + s))" .
  qed
  have "\<langle>v | ?M *\<^sub>v v\<rangle> = (\<Sum>r<d. \<Sum>s<d. ?M $$ (r * d + r, s * d + s))"
    unfolding quad_split[OF Mc vd] by (rule sum.cong[OF refl]) (simp add: inner)
  also have "\<dots> = (\<Sum>r<d. \<Sum>s<d. \<Phi> (block_of_mat n A r s) $$ (r,s))"
    by (intro sum.cong refl) (simp add: amplification_idx)
  finally have q: "\<langle>v | ?M *\<^sub>v v\<rangle> / of_nat d = arveson_functional n d \<Phi> A"
    unfolding arveson_functional_def by simp
  have "\<langle>v | ?M *\<^sub>v v\<rangle> \<in> \<real> \<and> 0 \<le> Re (\<langle>v | ?M *\<^sub>v v\<rangle>)"
    using Mpsd psd_iff_quad_form_nonneg[OF Mc] vd by blast
  thus "0 \<le> arveson_functional n d \<Phi> A" unfolding q[symmetric] using nonneg_of_real_quad d by blast
qed

lemma conj_tensor_index:
  fixes w :: "complex Matrix.vec"
  assumes s: "s < q" and k: "k < d" and b': "b' < n" and b: "b < n"
  defines "V \<equiv> Tensor.tensor_mat (Matrix.mat q d (\<lambda>(r,t). w $ (r * d + t))) (1\<^sub>m n)"
  shows "V $$ (s * n + b', k * n + b) = (if b' = b then w $ (s * d + k) else 0)"
proof -
  have "V $$ (s * n + b', k * n + b) = Matrix.mat q d (\<lambda>(r,t). w $ (r * d + t)) $$ ((s * n + b') div n, (k * n + b) div n)
          * 1\<^sub>m n $$ ((s * n + b') mod n, (k * n + b) mod n)"
  proof -
    have d0: "0 < d" using k by simp
    show ?thesis unfolding V_def by (rule index_tensor_mat) (use mult_index_lt[OF s b'] mult_index_div_mod[OF b'] mult_index_lt[OF k b] mult_index_div_mod[OF b] b d0 in simp_all)
  qed
  thus ?thesis using mult_index_lt[OF s b'] mult_index_div_mod[OF b'] mult_index_lt[OF k b] mult_index_div_mod[OF b] s k b b' by simp
qed

lemma conj_block:
  fixes A :: "complex Matrix.mat" and w :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat (q * n) (q * n)" and i: "i < d" and j: "j < d" and a: "a < n" and b: "b < n"
  defines "V \<equiv> Tensor.tensor_mat (Matrix.mat q d (\<lambda>(r,t). w $ (r * d + t))) (1\<^sub>m n)"
  shows "((V\<^sup>\<dagger>) * A * V) $$ (i * n + a, j * n + b)
         = (\<Sum>r<q. \<Sum>s<q. cnj (w $ (r * d + i)) * w $ (s * d + j) * A $$ (r * n + a, s * n + b))"
proof -
  have Vc: "V \<in> carrier_mat (q * n) (d * n)" unfolding V_def by simp
  have Vd: "V\<^sup>\<dagger> \<in> carrier_mat (d * n) (q * n)" by (rule dagger_carrier[OF Vc])
  have VdA: "(V\<^sup>\<dagger>) * A \<in> carrier_mat (d * n) (q * n)" using Vd A by simp
  have ia: "i * n + a < d * n" and jb: "j * n + b < d * n" using mult_index_lt[OF i a] mult_index_lt[OF j b] by simp_all
  have Vix: "\<And>s b'. s < q \<Longrightarrow> b' < n \<Longrightarrow> V $$ (s * n + b', j * n + b) = (if b' = b then w $ (s * d + j) else 0)"
    unfolding V_def by (rule conj_tensor_index[OF _ j _ b])
  have Vdix: "\<And>r a'. r < q \<Longrightarrow> a' < n \<Longrightarrow> cnj (V $$ (r * n + a', i * n + a)) = (if a' = a then cnj (w $ (r * d + i)) else 0)"
    unfolding V_def using conj_tensor_index[OF _ i _ a] by simp
  have "((V\<^sup>\<dagger>) * A * V) $$ (i * n + a, j * n + b) = (\<Sum>x<q * n. ((V\<^sup>\<dagger>) * A) $$ (i * n + a, x) * V $$ (x, j * n + b))"
    by (rule mat_mult_entry[OF VdA Vc ia jb])
  also have "\<dots> = (\<Sum>x<q * n. (\<Sum>y<q * n. cnj (V $$ (y, i * n + a)) * A $$ (y, x)) * V $$ (x, j * n + b))"
  proof (rule sum.cong[OF refl])
    fix x assume "x \<in> {..<q * n}"
    hence x: "x < q * n" by simp
    show "((V\<^sup>\<dagger>) * A) $$ (i * n + a, x) * V $$ (x, j * n + b)
          = (\<Sum>y<q * n. cnj (V $$ (y, i * n + a)) * A $$ (y, x)) * V $$ (x, j * n + b)"
      unfolding mat_mult_entry[OF Vd A ia x] using Vc ia by (simp add: dagger_def)
  qed
  also have "\<dots> = (\<Sum>s<q. \<Sum>b'<n. (\<Sum>r<q. \<Sum>a'<n. cnj (V $$ (r * n + a', i * n + a)) * A $$ (r * n + a', s * n + b'))
                    * V $$ (s * n + b', j * n + b))"
    by (simp only: sum_split_mp)
  also have "\<dots> = (\<Sum>s<q. \<Sum>b'<n. (\<Sum>r<q. \<Sum>a'<n. (if a' = a then cnj (w $ (r * d + i)) else 0) * A $$ (r * n + a', s * n + b'))
                    * (if b' = b then w $ (s * d + j) else 0))"
    by (intro sum.cong refl) (simp add: Vix Vdix)
  also have "\<dots> = (\<Sum>s<q. (\<Sum>r<q. cnj (w $ (r * d + i)) * A $$ (r * n + a, s * n + b)) * w $ (s * d + j))"
  proof (rule sum.cong[OF refl])
    fix s
    have "\<And>b'. (\<Sum>r<q. \<Sum>a'<n. (if a' = a then cnj (w $ (r * d + i)) else 0) * A $$ (r * n + a', s * n + b'))
               = (\<Sum>r<q. cnj (w $ (r * d + i)) * A $$ (r * n + a, s * n + b'))"
      by (intro sum.cong refl) (simp add: if_zero_mult a sum.delta)
    thus "(\<Sum>b'<n. (\<Sum>r<q. \<Sum>a'<n. (if a' = a then cnj (w $ (r * d + i)) else 0) * A $$ (r * n + a', s * n + b'))
                    * (if b' = b then w $ (s * d + j) else 0))
           = (\<Sum>r<q. cnj (w $ (r * d + i)) * A $$ (r * n + a, s * n + b)) * w $ (s * d + j)"
      using b by (simp add: mult_if_zero sum.delta)
  qed
  also have "\<dots> = (\<Sum>s<q. \<Sum>r<q. cnj (w $ (r * d + i)) * w $ (s * d + j) * A $$ (r * n + a, s * n + b))"
    by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  also have "\<dots> = (\<Sum>r<q. \<Sum>s<q. cnj (w $ (r * d + i)) * w $ (s * d + j) * A $$ (r * n + a, s * n + b))"
    by (rule sum.swap)
  finally show ?thesis .
qed

lemma functional_pos_imp_cp:
  assumes OS: "operator_system n OS" and L: "lin_on n d OS \<Phi>" and d: "0 < d"
      and Pos: "positive_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
  shows "cp_on n d OS \<Phi>"
  unfolding cp_on_def p_positive_on_def
proof (intro allI impI ballI)
  fix q A assume q: "0 < q" and A: "A \<in> Mp q n OS" and Apsd: "psd A"
  have Ac: "A \<in> carrier_mat (q * n) (q * n)" and Ab: "\<And>r s. r < q \<Longrightarrow> s < q \<Longrightarrow> block_of_mat n A r s \<in> OS"
    using A unfolding Mp_def by blast+
  let ?M = "amplification n d q \<Phi> A"
  have Mc: "?M \<in> carrier_mat (q * d) (q * d)" by (rule amplification_carrier)
  have PhiAc: "\<And>r s. r < q \<Longrightarrow> s < q \<Longrightarrow> \<Phi> (block_of_mat n A r s) \<in> carrier_mat d d"
    using L Ab unfolding lin_on_def by blast
  show "psd ?M"
    unfolding psd_iff_quad_form_nonneg[OF Mc]
  proof (intro allI impI)
    fix w :: "complex Matrix.vec" assume wd: "dim_vec w = q * d"
    define V where "V = Tensor.tensor_mat (Matrix.mat q d (\<lambda>(r,t). w $ (r * d + t))) (1\<^sub>m n)"
    have Vc: "V \<in> carrier_mat (q * n) (d * n)" unfolding V_def by simp
    define Ym where "Ym = (V\<^sup>\<dagger>) * A * V"
    have Yc: "Ym \<in> carrier_mat (d * n) (d * n)" unfolding Ym_def using Vc Ac by auto
    have Ypsd: "psd Ym" unfolding Ym_def by (rule psd_conjugate[OF Ac Apsd Vc])
    let ?c = "\<lambda>i j r s. cnj (w $ (r * d + i)) * w $ (s * d + j)"
    let ?g = "\<lambda>i j. \<lambda>(r,s). ?c i j r s \<cdot>\<^sub>m block_of_mat n A r s"
    have gc: "\<And>i j. \<forall>x \<in> set (List.product [0..<q] [0..<q]). ?g i j x \<in> carrier_mat n n" by auto
    have gOS: "\<And>i j. \<forall>x \<in> set (List.product [0..<q] [0..<q]). ?g i j x \<in> OS"
      using Ab operator_systemD(5)[OF OS] by auto
    have Yblk: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow>
        block_of_mat n Ym i j = msum n n (?g i j) (List.product [0..<q] [0..<q])"
    proof -
      fix i j assume i: "i < d" and j: "j < d"
      show "block_of_mat n Ym i j = msum n n (?g i j) (List.product [0..<q] [0..<q])"
      proof (rule eq_matI)
        fix a b assume "a < dim_row (msum n n (?g i j) (List.product [0..<q] [0..<q]))"
          "b < dim_col (msum n n (?g i j) (List.product [0..<q] [0..<q]))"
        hence a: "a < n" and b: "b < n" using msum_carrier[OF gc[of i j]] by simp_all
        have "block_of_mat n Ym i j $$ (a,b) = (\<Sum>r<q. \<Sum>s<q. ?c i j r s * A $$ (r * n + a, s * n + b))"
          unfolding block_of_mat_index[OF a b] Ym_def V_def by (rule conj_block[OF Ac i j a b])
        also have "\<dots> = msum n n (?g i j) (List.product [0..<q] [0..<q]) $$ (a,b)"
          unfolding msum_index[OF gc a b] sum_list_product_upt
          by (intro sum.cong refl) (simp add: block_of_mat_index[OF a b] a b)
        finally show "block_of_mat n Ym i j $$ (a,b) = msum n n (?g i j) (List.product [0..<q] [0..<q]) $$ (a,b)" .
      qed (use msum_carrier[OF gc[of i j]] in simp_all)
    qed
    have YMp: "Ym \<in> Mp d n OS" unfolding Mp_def using Yc Yblk msum_in_os[OF OS gOS] by auto
    have pos: "0 \<le> arveson_functional n d \<Phi> Ym" using Pos YMp Ypsd unfolding positive_fun_on_def by blast
    have PhiY: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> \<Phi> (block_of_mat n Ym i j) $$ (i,j)
                  = (\<Sum>r<q. \<Sum>s<q. ?c i j r s * \<Phi> (block_of_mat n A r s) $$ (i,j))"
    proof -
      fix i j assume i: "i < d" and j: "j < d"
      have gPhi: "\<forall>x \<in> set (List.product [0..<q] [0..<q]). \<Phi> (?g i j x) \<in> carrier_mat d d"
        using L gOS[of i j] unfolding lin_on_def by blast
      have "\<Phi> (block_of_mat n Ym i j) $$ (i,j) = (\<Sum>x\<leftarrow>List.product [0..<q] [0..<q]. \<Phi> (?g i j x) $$ (i,j))"
        unfolding Yblk[OF i j] lin_on_msum[OF OS L gOS] by (rule msum_index[OF gPhi i j])
      also have "\<dots> = (\<Sum>r<q. \<Sum>s<q. ?c i j r s * \<Phi> (block_of_mat n A r s) $$ (i,j))"
        unfolding sum_list_product_upt
      proof (intro sum.cong refl)
        fix r s assume "r \<in> {..<q}" "s \<in> {..<q}"
        hence r: "r < q" and s: "s < q" by simp_all
        have "\<Phi> (?c i j r s \<cdot>\<^sub>m block_of_mat n A r s) = ?c i j r s \<cdot>\<^sub>m \<Phi> (block_of_mat n A r s)"
          using L Ab[OF r s] unfolding lin_on_def by blast
        thus "\<Phi> (?g i j (r,s)) $$ (i,j) = ?c i j r s * \<Phi> (block_of_mat n A r s) $$ (i,j)"
          using PhiAc[OF r s] i j by simp
      qed
      finally show "\<Phi> (block_of_mat n Ym i j) $$ (i,j) = (\<Sum>r<q. \<Sum>s<q. ?c i j r s * \<Phi> (block_of_mat n A r s) $$ (i,j))" .
    qed
    define F where "F = (\<lambda>r i s j. cnj (w $ (r * d + i)) * \<Phi> (block_of_mat n A r s) $$ (i,j) * w $ (s * d + j))"
    have "\<langle>w | ?M *\<^sub>v w\<rangle> = (\<Sum>r<q. \<Sum>i<d. \<Sum>s<q. \<Sum>j<d. F r i s j)"
      unfolding quad_split[OF Mc wd] F_def by (intro sum.cong refl) (simp add: amplification_idx)
    also have "\<dots> = (\<Sum>i<d. \<Sum>r<q. \<Sum>s<q. \<Sum>j<d. F r i s j)" by (rule sum.swap)
    also have "\<dots> = (\<Sum>i<d. \<Sum>r<q. \<Sum>j<d. \<Sum>s<q. F r i s j)"
      by (rule sum.cong[OF refl], rule sum.cong[OF refl], rule sum.swap)
    also have "\<dots> = (\<Sum>i<d. \<Sum>j<d. \<Sum>r<q. \<Sum>s<q. F r i s j)"
      by (rule sum.cong[OF refl], rule sum.swap)
    also have "\<dots> = (\<Sum>i<d. \<Sum>j<d. \<Phi> (block_of_mat n Ym i j) $$ (i,j))"
      by (intro sum.cong refl) (simp add: PhiY F_def mult_ac)
    also have "\<dots> = of_nat d * arveson_functional n d \<Phi> Ym"
      unfolding arveson_functional_def using d by simp
    finally have e: "\<langle>w | ?M *\<^sub>v w\<rangle> = of_nat d * arveson_functional n d \<Phi> Ym" .
    have "Im (arveson_functional n d \<Phi> Ym) = 0" "0 \<le> Re (arveson_functional n d \<Phi> Ym)"
      using pos by (simp_all add: less_eq_complex_def)
    thus "\<langle>w | ?M *\<^sub>v w\<rangle> \<in> \<real> \<and> 0 \<le> Re (\<langle>w | ?M *\<^sub>v w\<rangle>)"
      unfolding e by (simp add: complex_is_Real_iff)
  qed
qed

text \<open>Theorem (Arveson, Day 24): for linear $\Phi:S\to M_d$, completely positive $\iff$
$d$-positive $\iff$ $S_\Phi$ positive.\<close>

theorem arveson_cp_iff:
  assumes OS: "operator_system n OS" and L: "lin_on n d OS \<Phi>" and d: "0 < d"
  shows "cp_on n d OS \<Phi> \<longleftrightarrow> p_positive_on n d d OS \<Phi>"
    and "p_positive_on n d d OS \<Phi> \<longleftrightarrow> positive_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
proof -
  show 2: "p_positive_on n d d OS \<Phi> \<longleftrightarrow> positive_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
  proof
    assume "p_positive_on n d d OS \<Phi>" thus "positive_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
      by (rule dpos_imp_functional_pos[OF OS d])
  next
    assume "positive_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
    hence "cp_on n d OS \<Phi>" by (rule functional_pos_imp_cp[OF OS L d])
    thus "p_positive_on n d d OS \<Phi>" using d unfolding cp_on_def by blast
  qed
  show "cp_on n d OS \<Phi> \<longleftrightarrow> p_positive_on n d d OS \<Phi>"
    using 2 functional_pos_imp_cp[OF OS L d] d unfolding cp_on_def by blast
qed

text \<open>Theorem (Arveson correspondence, Day 25): $\Phi\mapsto S_\Phi$ maps $CP(S,M_d)$ onto the
positive functionals on $M_d(S)$, with inverse $f\mapsto\Phi_f$; it is affine and sends unital
maps to states.\<close>

theorem arveson_correspondence:
  assumes OS: "operator_system n OS" and d: "0 < d"
  shows "lin_on n d OS \<Phi> \<Longrightarrow> cp_on n d OS \<Phi> \<longleftrightarrow> positive_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
    and "lin_fun_on (Mp d n OS) f \<Longrightarrow> cp_on n d OS (arveson_map n d f) \<longleftrightarrow> positive_fun_on (Mp d n OS) f"
    and "lin_on n d OS \<Phi> \<Longrightarrow> M \<in> OS \<Longrightarrow> arveson_map n d (arveson_functional n d \<Phi>) M = \<Phi> M"
    and "lin_fun_on (Mp d n OS) f \<Longrightarrow> A \<in> Mp d n OS \<Longrightarrow> arveson_functional n d (arveson_map n d f) A = f A"
proof -
  show 1: "\<And>\<Phi>. lin_on n d OS \<Phi> \<Longrightarrow> cp_on n d OS \<Phi> \<longleftrightarrow> positive_fun_on (Mp d n OS) (arveson_functional n d \<Phi>)"
    using arveson_cp_iff[OF OS _ d] by blast
  show "lin_on n d OS \<Phi> \<Longrightarrow> M \<in> OS \<Longrightarrow> arveson_map n d (arveson_functional n d \<Phi>) M = \<Phi> M"
    by (rule arveson_map_of_functional[OF OS _ _ d])
  show "lin_fun_on (Mp d n OS) f \<Longrightarrow> A \<in> Mp d n OS \<Longrightarrow> arveson_functional n d (arveson_map n d f) A = f A"
    by (rule arveson_functional_of_map[OF OS _ _ d])
  assume f: "lin_fun_on (Mp d n OS) f"
  have "positive_fun_on (Mp d n OS) (arveson_functional n d (arveson_map n d f)) \<longleftrightarrow> positive_fun_on (Mp d n OS) f"
    unfolding positive_fun_on_def using arveson_functional_of_map[OF OS f _ d] by simp
  thus "cp_on n d OS (arveson_map n d f) \<longleftrightarrow> positive_fun_on (Mp d n OS) f"
    using 1[OF arveson_map_lin[OF OS f]] by simp
qed

lemma arveson_functional_affine:
  assumes OS: "operator_system n OS" and L1: "lin_on n d OS \<Phi>" and L2: "lin_on n d OS \<Psi>" and A: "A \<in> Mp d n OS"
  shows "arveson_functional n d (\<lambda>M. t \<cdot>\<^sub>m \<Phi> M + (1 - t) \<cdot>\<^sub>m \<Psi> M) A
         = t * arveson_functional n d \<Phi> A + (1 - t) * arveson_functional n d \<Psi> A"
proof -
  have Ab: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> block_of_mat n A i j \<in> OS" using A unfolding Mp_def by blast
  have "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> (t \<cdot>\<^sub>m \<Phi> (block_of_mat n A i j) + (1 - t) \<cdot>\<^sub>m \<Psi> (block_of_mat n A i j)) $$ (i,j)
          = t * \<Phi> (block_of_mat n A i j) $$ (i,j) + (1 - t) * \<Psi> (block_of_mat n A i j) $$ (i,j)"
  proof -
    fix i j assume i: "i < d" and j: "j < d"
    have "\<Phi> (block_of_mat n A i j) \<in> carrier_mat d d" "\<Psi> (block_of_mat n A i j) \<in> carrier_mat d d"
      using L1 L2 Ab[OF i j] unfolding lin_on_def by blast+
    thus "(t \<cdot>\<^sub>m \<Phi> (block_of_mat n A i j) + (1 - t) \<cdot>\<^sub>m \<Psi> (block_of_mat n A i j)) $$ (i,j)
          = t * \<Phi> (block_of_mat n A i j) $$ (i,j) + (1 - t) * \<Psi> (block_of_mat n A i j) $$ (i,j)"
      using i j by simp
  qed
  thus ?thesis unfolding arveson_functional_def
    by (simp add: sum.distrib sum_distrib_left add_divide_distrib)
qed

lemma arveson_functional_unital:
  assumes OS: "operator_system n OS" and L: "lin_on n d OS \<Phi>" and u: "\<Phi> (1\<^sub>m n) = 1\<^sub>m d" and d: "0 < d"
  shows "arveson_functional n d \<Phi> (1\<^sub>m (d * n)) = 1"
proof -
  have z: "\<Phi> (0\<^sub>m n n) = 0\<^sub>m d d" by (rule lin_on_zero[OF OS L])
  have "(\<Sum>i<d. \<Sum>j<d. \<Phi> (block_of_mat n (1\<^sub>m (d * n)) i j) $$ (i,j)) = (\<Sum>i<d. \<Sum>j<d. if i = j then 1 else 0)"
    by (intro sum.cong refl) (simp add: block_of_mat_one u z)
  also have "\<dots> = of_nat d" by simp
  finally show ?thesis unfolding arveson_functional_def using d by simp
qed

end
