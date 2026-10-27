(*  Title:   Matrix_Lemmas.thy
    Author:  Dustin Bryant.  Facts about complex matrices and vectors (Jordan_Normal_Form,
             Isabelle_Marries_Dirac) that the lectures use throughout.
*)

theory Matrix_Lemmas
  imports Isabelle_Marries_Dirac.Quantum
begin

text \<open>The gate names of Isabelle\_Marries\_Dirac would capture the letters $X,Y,Z,H,S,T$
used as variables in the lectures.\<close>

hide_const (open) Quantum.X Quantum.Y Quantum.Z Quantum.H Quantum.S Quantum.T

section \<open>Complex numbers and scalar multiples\<close>

lemma cnj_mult_self_cmod: "cnj z * z = complex_of_real ((cmod z)\<^sup>2)"
  by (metis complex_norm_square mult.commute)

lemma Re_cnj_mult_self: "Re (cnj z * z) = (cmod z)\<^sup>2"
  by (simp add: cnj_mult_self_cmod)

lemma smult_smult_mat:
  fixes A :: "complex Matrix.mat"
  shows "a \<cdot>\<^sub>m (b \<cdot>\<^sub>m A) = (a * b) \<cdot>\<^sub>m A"
  by (rule eq_matI) (simp_all add: mult.assoc)

lemma zero_smult_mat_carrier:
  fixes A :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat m k"
  shows "0 \<cdot>\<^sub>m A = 0\<^sub>m m k"
  using assms by (intro eq_matI) auto

section \<open>The adjoint\<close>

text \<open>The adjoint of an $m\times n$ matrix is $n\times m$.\<close>

lemma dagger_carrier:
  assumes "M \<in> carrier_mat m n"
  shows "(M\<^sup>\<dagger>) \<in> carrier_mat n m"
  using assms
  by (simp add: dagger_def)

lemma dagger_mult_diag_inner:
  fixes Y :: "complex Matrix.mat"
  assumes Yc: "Y \<in> carrier_mat p q" and j: "j < q"
  shows "((Y\<^sup>\<dagger>) * Y) $$ (j,j) = \<langle>Matrix.col Y j | Matrix.col Y j\<rangle>"
proof -
  have "((Y\<^sup>\<dagger>) * Y) $$ (j,j) = (\<Sum>i<p. cnj (Y $$ (i,j)) * Y $$ (i,j))"
    using carrier_matD[OF Yc] j by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<p. cnj (Matrix.col Y j $ i) * Matrix.col Y j $ i)"
    using carrier_matD[OF Yc] by (intro sum.cong refl) (simp add: Matrix.col_def)
  also have "\<dots> = \<langle>Matrix.col Y j | Matrix.col Y j\<rangle>"
    unfolding inner_prod_def using carrier_matD[OF Yc] by (simp add: atLeast0LessThan)
  finally show ?thesis .
qed

section \<open>Sums of vectors\<close>

text \<open>Finite sums of vectors, entrywise.\<close>

definition vec_sum :: "nat \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> complex Matrix.vec) \<Rightarrow> complex Matrix.vec" where
  "vec_sum n Js w = Matrix.vec n (\<lambda>i. sum (\<lambda>J. w J $ i) Js)"

lemma vec_sum_dim [simp]: "dim_vec (vec_sum n Js w) = n"
  by (simp add: vec_sum_def)

lemma vec_sum_index [simp]: "i < n \<Longrightarrow> vec_sum n Js w $ i = sum (\<lambda>J. w J $ i) Js"
  by (simp add: vec_sum_def)

lemma vec_sum_cong:
  assumes "\<And>J. J \<in> Js \<Longrightarrow> w J = w' J"
  shows "vec_sum n Js w = vec_sum n Js w'"
  unfolding vec_sum_def using assms by (intro arg_cong[where f = "Matrix.vec n"] ext sum.cong refl) simp

lemma mult_mat_vec_vec_sum:
  assumes Ac: "A \<in> carrier_mat m n" and fin: "finite Js"
      and wd: "\<And>J. J \<in> Js \<Longrightarrow> dim_vec (w J) = n"
  shows "A *\<^sub>v vec_sum n Js w = vec_sum m Js (\<lambda>J. A *\<^sub>v w J)"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (vec_sum m Js (\<lambda>J. A *\<^sub>v w J))"
  hence i: "i < m" by simp
  have "(A *\<^sub>v vec_sum n Js w) $ i = Matrix.row A i \<bullet> vec_sum n Js w" using i Ac by simp
  also have "\<dots> = (\<Sum>k = 0..<n. Matrix.row A i $ k * vec_sum n Js w $ k)"
    unfolding scalar_prod_def by simp
  also have "\<dots> = (\<Sum>k = 0..<n. sum (\<lambda>J. Matrix.row A i $ k * w J $ k) Js)"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = sum (\<lambda>J. \<Sum>k = 0..<n. Matrix.row A i $ k * w J $ k) Js"
    by (rule sum.swap)
  also have "\<dots> = sum (\<lambda>J. (A *\<^sub>v w J) $ i) Js"
  proof (rule sum.cong[OF refl])
    fix J assume J: "J \<in> Js"
    have "(A *\<^sub>v w J) $ i = Matrix.row A i \<bullet> w J" using i Ac by simp
    also have "\<dots> = (\<Sum>k = 0..<n. Matrix.row A i $ k * w J $ k)"
      unfolding scalar_prod_def using wd[OF J] by simp
    finally show "(\<Sum>k = 0..<n. Matrix.row A i $ k * w J $ k) = (A *\<^sub>v w J) $ i" ..
  qed
  also have "\<dots> = vec_sum m Js (\<lambda>J. A *\<^sub>v w J) $ i" using i by simp
  finally show "(A *\<^sub>v vec_sum n Js w) $ i = vec_sum m Js (\<lambda>J. A *\<^sub>v w J) $ i" .
qed (simp add: Ac[THEN carrier_matD(1)])

lemma mult_mat_vec_smult_vec:
  fixes A :: "complex Matrix.mat" and v :: "complex Matrix.vec"
  assumes Ac: "A \<in> carrier_mat m n" and vd: "dim_vec v = n"
  shows "A *\<^sub>v (c \<cdot>\<^sub>v v) = c \<cdot>\<^sub>v (A *\<^sub>v v)"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (c \<cdot>\<^sub>v (A *\<^sub>v v))"
  hence i: "i < m" using Ac by simp
  have "(A *\<^sub>v (c \<cdot>\<^sub>v v)) $ i = (\<Sum>k = 0..<n. A $$ (i,k) * (c * v $ k))"
    using i Ac vd by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<n. c * (A $$ (i,k) * v $ k))"
    by (intro sum.cong refl) (simp only: mult.left_commute[of _ c])
  also have "\<dots> = c * (\<Sum>k = 0..<n. A $$ (i,k) * v $ k)" by (simp add: sum_distrib_left)
  also have "\<dots> = (c \<cdot>\<^sub>v (A *\<^sub>v v)) $ i" using i Ac vd by (simp add: scalar_prod_def)
  finally show "(A *\<^sub>v (c \<cdot>\<^sub>v v)) $ i = (c \<cdot>\<^sub>v (A *\<^sub>v v)) $ i" .
qed (use Ac in simp)

section \<open>Products and sums of matrices\<close>

lemma mat_mult_entry:
  fixes A B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat r s" "B \<in> carrier_mat s t" "k < r" "j < t"
  shows "(A * B) $$ (k,j) = (\<Sum>l<s. A $$ (k,l) * B $$ (l,j))"
  using assms by (simp add: scalar_prod_def atLeast0LessThan)

lemma foldr_add_mat_carrier_rect:
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat p q"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m p q) \<in> carrier_mat p q"
  using assms by (induction xs) auto

lemma foldr_add_mat_index_rect:
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat p q" and "i < p" and "j < q"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m p q) $$ (i,j) = (\<Sum>x\<leftarrow>xs. f x $$ (i,j))"
  using assms
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have c: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m p q) \<in> carrier_mat p q"
    using Cons.prems(1) by (intro foldr_add_mat_carrier_rect) simp
  have "foldr (\<lambda>x acc. f x + acc) (x # xs) (0\<^sub>m p q) $$ (i,j)
        = f x $$ (i,j) + foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m p q) $$ (i,j)"
    using Cons.prems(2,3) carrier_matD[OF c] by simp
  also have "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m p q) $$ (i,j) = (\<Sum>x\<leftarrow>xs. f x $$ (i,j))"
    by (rule Cons.IH) (use Cons.prems in simp_all)
  finally show ?case by simp
qed

text \<open>Carrier-preservation in a different dimension pair.\<close>

lemma foldr_add_carrier_dn:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat d n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m d n) \<in> carrier_mat d n"
  using assms by (induction xs) (auto intro!: add_carrier_mat)

lemma foldr_add_mat_cong:
  fixes f g :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows "foldr (\<lambda>x acc. f x + acc) xs z = foldr (\<lambda>x acc. g x + acc) xs z"
  using assms by (induction xs) auto

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

section \<open>Finite sums and index arithmetic\<close>

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

lemma idx8: "k < (8::nat) \<Longrightarrow> k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3 \<or> k = 4 \<or> k = 5 \<or> k = 6 \<or> k = 7"
  by auto

section \<open>Linear maps on a set of matrices\<close>

text \<open>Linearity of a map defined on a set of $n\times n$ matrices (an operator system, from
Day 24 on) with values in $M_d$.\<close>

definition lin_on :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "lin_on n d OS \<Phi> \<longleftrightarrow> (\<forall>A \<in> OS. \<Phi> A \<in> carrier_mat d d) \<and> (\<forall>A \<in> OS. \<forall>B \<in> OS. \<Phi> (A + B) = \<Phi> A + \<Phi> B)
     \<and> (\<forall>A \<in> OS. \<forall>c. \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A)"

end
