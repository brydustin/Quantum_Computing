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

text \<open>The same with the sum over $\{0..<q\}$; square matrices that agree on
every vector are equal; a non-zero matrix has a non-zero entry.\<close>

lemma mat_mult_index_sum:
  assumes A_c: "A \<in> carrier_mat p q"
      and B_c: "B \<in> carrier_mat q s"
      and r_lt: "r < p" and c_lt: "c < s"
  shows "(A * B) $$ (r, c) = (\<Sum>k = 0..<q. A $$ (r, k) * B $$ (k, c))"
  using A_c B_c r_lt c_lt
  by (simp add: times_mat_def scalar_prod_def lessThan_atLeast0)

lemma mat_eq_of_mult_vec_eq:
  fixes M N :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat k k"
      and N_c: "N \<in> carrier_mat k k"
      and eq: "\<And>x. x \<in> carrier_vec k \<Longrightarrow> M *\<^sub>v x = N *\<^sub>v x"
  shows "M = N"
proof (rule eq_matI)
  show "dim_row M = dim_row N" using M_c N_c by auto
  show "dim_col M = dim_col N" using M_c N_c by auto
  fix i j assume "i < dim_row N" and "j < dim_col N"
  hence ilt: "i < k" and jlt: "j < k" using N_c by auto
  have one_c: "1\<^sub>m k \<in> carrier_mat k k" by auto
  have e_c: "Matrix.col (1\<^sub>m k) j \<in> carrier_vec k" by (rule carrier_vecI) simp
  have "Matrix.col M j = Matrix.col (M * 1\<^sub>m k) j"
    using right_mult_one_mat[OF M_c] by simp
  also have "\<dots> = M *\<^sub>v Matrix.col (1\<^sub>m k) j"
    by (rule col_mult2[OF M_c one_c jlt])
  also have "\<dots> = N *\<^sub>v Matrix.col (1\<^sub>m k) j"
    by (rule eq[OF e_c])
  also have "\<dots> = Matrix.col (N * 1\<^sub>m k) j"
    by (rule col_mult2[OF N_c one_c jlt, symmetric])
  also have "\<dots> = Matrix.col N j"
    using right_mult_one_mat[OF N_c] by simp
  finally have cols: "Matrix.col M j = Matrix.col N j" .
  have "M $$ (i, j) = Matrix.col M j $ i" using ilt jlt M_c by auto
  also have "\<dots> = Matrix.col N j $ i" using cols by simp
  also have "\<dots> = N $$ (i, j)" using ilt jlt N_c by auto
  finally show "M $$ (i, j) = N $$ (i, j)" .
qed

lemma nonzero_entry:
  fixes A :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat m k" and nz: "A \<noteq> 0\<^sub>m m k"
  obtains r s where "r < m" "s < k" "A $$ (r,s) \<noteq> 0"
proof -
  have "\<exists>r < m. \<exists>s < k. A $$ (r,s) \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>r < m. \<exists>s < k. A $$ (r,s) \<noteq> 0)"
    hence "A = 0\<^sub>m m k" using A by (intro eq_matI) auto
    thus False using nz by simp
  qed
  thus thesis using that by blast
qed

text \<open>An independent frame cancels: if $M^*M$ is invertible, $MAM^*=0$ forces $A=0$.\<close>

lemma frame_cancel:
  fixes M A B :: "complex Matrix.mat"
  assumes M: "M \<in> carrier_mat m k" and A: "A \<in> carrier_mat k k" and B: "B \<in> carrier_mat k k"
      and BG: "B * (M\<^sup>\<dagger> * M) = 1\<^sub>m k" and GB: "(M\<^sup>\<dagger> * M) * B = 1\<^sub>m k"
      and z: "M * A * (M\<^sup>\<dagger>) = 0\<^sub>m m m"
  shows "A = 0\<^sub>m k k"
proof -
  have Md: "M\<^sup>\<dagger> \<in> carrier_mat k m" by (rule dagger_carrier[OF M])
  have G: "M\<^sup>\<dagger> * M \<in> carrier_mat k k" using Md M by simp
  have MA: "M * A \<in> carrier_mat m k" using M A by simp
  have GA: "(M\<^sup>\<dagger> * M) * A \<in> carrier_mat k k" using G A by simp
  have "(M\<^sup>\<dagger> * M) * A * (M\<^sup>\<dagger> * M) = M\<^sup>\<dagger> * (M * A * (M\<^sup>\<dagger>)) * M"
    by (simp only: assoc_mult_mat[OF Md MA Md, symmetric] assoc_mult_mat[OF Md M A, symmetric]
                   assoc_mult_mat[OF GA Md M])
  also have "\<dots> = 0\<^sub>m k k" using z Md M by simp
  finally have GAG: "(M\<^sup>\<dagger> * M) * A * (M\<^sup>\<dagger> * M) = 0\<^sub>m k k" .
  have "A * (M\<^sup>\<dagger> * M) = B * (M\<^sup>\<dagger> * M) * A * (M\<^sup>\<dagger> * M)" using BG A by simp
  also have "\<dots> = B * ((M\<^sup>\<dagger> * M) * A * (M\<^sup>\<dagger> * M))"
    by (simp only: assoc_mult_mat[OF B G A] assoc_mult_mat[OF B GA G])
  also have "\<dots> = 0\<^sub>m k k" using GAG B by simp
  finally have AG: "A * (M\<^sup>\<dagger> * M) = 0\<^sub>m k k" .
  have "A = A * ((M\<^sup>\<dagger> * M) * B)" using GB A by simp
  also have "\<dots> = A * (M\<^sup>\<dagger> * M) * B" by (simp only: assoc_mult_mat[OF A G B])
  also have "\<dots> = 0\<^sub>m k k" using AG B by simp
  finally show ?thesis .
qed

lemma foldr_add_mat_carrier:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat n n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n"
  using assms by (induction xs) auto

lemma foldr_add_mat_index:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat n n" and "i < n" and "j < n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) $$ (i, j) = sum_list (map (\<lambda>x. f x $$ (i, j)) xs)"
  using assms
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat n n" and rest: "\<forall>y \<in> set xs. f y \<in> carrier_mat n n" using Cons.prems by auto
  have rc: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n" by (rule foldr_add_mat_carrier[OF rest])
  show ?case using Cons.IH[OF rest] Cons.prems fx rc by simp
qed

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

text \<open>Sums over $[0..<N]$, and their entries.\<close>

lemma foldr_upt_add_acc_index:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat"
  assumes carr: "\<forall>k < N. f k \<in> carrier_mat d d"
      and z_c:  "z \<in> carrier_mat d d"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "foldr (\<lambda>k acc. f k + acc) [0..<N] z $$ (r, c)
           = (\<Sum>k = 0..<N. f k $$ (r, c)) + z $$ (r, c)"
  using carr z_c
proof (induction N arbitrary: z)
  case 0
  show ?case by simp
next
  case (Suc N)
  have hd_c:   "f N \<in> carrier_mat d d" using Suc.prems(1) by simp
  have rest_c: "\<forall>k < N. f k \<in> carrier_mat d d" using Suc.prems(1) by simp
  have fNz_c:  "f N + z \<in> carrier_mat d d"
    using hd_c Suc.prems(2) by auto
  have dec: "[0..<Suc N] = [0..<N] @ [N]" by simp
  have step: "foldr (\<lambda>k acc. f k + acc) [0..<Suc N] z
                = foldr (\<lambda>k acc. f k + acc) [0..<N] (f N + z)"
    using dec by (simp add: foldr_append)
  have IH: "foldr (\<lambda>k acc. f k + acc) [0..<N] (f N + z) $$ (r,c)
              = (\<Sum>k = 0..<N. f k $$ (r,c)) + (f N + z) $$ (r,c)"
    using Suc.IH[OF rest_c fNz_c] .
  have idx_split: "(f N + z) $$ (r,c) = f N $$ (r,c) + z $$ (r,c)"
    using hd_c Suc.prems(2) r_lt c_lt by simp
  have "foldr (\<lambda>k acc. f k + acc) [0..<Suc N] z $$ (r,c)
          = (\<Sum>k = 0..<N. f k $$ (r,c)) + (f N $$ (r,c) + z $$ (r,c))"
    using step IH idx_split by simp
  also have "\<dots> = ((\<Sum>k = 0..<N. f k $$ (r,c)) + f N $$ (r,c)) + z $$ (r,c)"
    by (simp add: add.assoc)
  also have "\<dots> = (\<Sum>k = 0..<Suc N. f k $$ (r,c)) + z $$ (r,c)"
    by simp
  finally show ?case .
qed

lemma foldr_upt_add_index:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat"
  assumes carr: "\<forall>k < N. f k \<in> carrier_mat d d"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "foldr (\<lambda>k acc. f k + acc) [0..<N] (0\<^sub>m d d) $$ (r, c)
           = (\<Sum>k = 0..<N. f k $$ (r, c))"
proof -
  have z_c: "(0\<^sub>m d d :: complex Matrix.mat) \<in> carrier_mat d d" by simp
  have z_idx: "(0\<^sub>m d d :: complex Matrix.mat) $$ (r,c) = 0"
    using r_lt c_lt by simp
  show ?thesis
    using foldr_upt_add_acc_index[OF carr z_c r_lt c_lt] z_idx by simp
qed

lemma foldr_smult_index:
  assumes Bs: "\<forall>B \<in> set Bs. B \<in> carrier_mat n m" and r: "r < n" and s: "s < m"
  shows "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n m) $$ (r,s)
       = (\<Sum>k<length Bs. c k * Bs ! k $$ (r,s))"
proof -
  have "\<forall>k \<in> set [0..<length Bs]. c k \<cdot>\<^sub>m (Bs ! k) \<in> carrier_mat n m" using Bs by auto
  from foldr_add_mat_index_rect[OF this r s]
  have "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n m) $$ (r,s)
      = (\<Sum>k<length Bs. (c k \<cdot>\<^sub>m (Bs ! k)) $$ (r,s))"
    by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<length Bs. c k * Bs ! k $$ (r,s))"
  proof (intro sum.cong refl)
    fix k assume "k \<in> {..<length Bs}"
    hence "Bs ! k \<in> carrier_mat n m" using Bs by simp
    thus "(c k \<cdot>\<^sub>m (Bs ! k)) $$ (r,s) = c k * Bs ! k $$ (r,s)" using r s by simp
  qed
  finally show ?thesis .
qed

subsection \<open>Algebra of \<open>foldr\<close>-sums of matrices\<close>

lemma foldr_add_mat_mult_left:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes Ac: "A \<in> carrier_mat m n" and fc: "\<forall>x \<in> set xs. f x \<in> carrier_mat n p"
  shows "A * foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n p) = foldr (\<lambda>x acc. A * f x + acc) xs (0\<^sub>m m p)"
  using fc
proof (induction xs)
  case Nil show ?case using Ac by simp
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat n p" and rest: "\<forall>y \<in> set xs. f y \<in> carrier_mat n p" using Cons.prems by auto
  have rc: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n p) \<in> carrier_mat n p"
    using rest by (induction xs) auto
  show ?case using Ac fx rc Cons.IH[OF rest] by (simp add: mult_add_distrib_mat)
qed

lemma foldr_add_mat_mult_right:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes Bc: "B \<in> carrier_mat n p" and fc: "\<forall>x \<in> set xs. f x \<in> carrier_mat m n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m m n) * B = foldr (\<lambda>x acc. f x * B + acc) xs (0\<^sub>m m p)"
  using fc
proof (induction xs)
  case Nil show ?case using Bc by simp
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat m n" and rest: "\<forall>y \<in> set xs. f y \<in> carrier_mat m n" using Cons.prems by auto
  have rc: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m m n) \<in> carrier_mat m n"
    using rest by (induction xs) auto
  show ?case using Bc fx rc Cons.IH[OF rest] by (simp add: add_mult_distrib_mat)
qed

lemma foldr_add_mat_dagger:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat m n"
  shows "(foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m m n))\<^sup>\<dagger> = foldr (\<lambda>x acc. (f x)\<^sup>\<dagger> + acc) xs (0\<^sub>m n m)"
  using assms
proof (induction xs)
  case Nil show ?case by (rule eq_matI) (auto simp: dagger_def)
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat m n" and rest: "\<forall>y \<in> set xs. f y \<in> carrier_mat m n" using Cons.prems by auto
  have rc: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m m n) \<in> carrier_mat m n" by (rule foldr_add_carrier_dn[OF rest])
  have "(f x + foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m m n))\<^sup>\<dagger>
        = (f x)\<^sup>\<dagger> + ((foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m m n))\<^sup>\<dagger>)"
    using fx rc by (intro eq_matI) (auto simp: dagger_def)
  thus ?case using Cons.IH[OF rest] by simp
qed

lemma foldr_add_mat_zero:
  "foldr (\<lambda>x acc. (0\<^sub>m m n :: complex Matrix.mat) + acc) xs (0\<^sub>m m n) = 0\<^sub>m m n"
  by (induction xs) auto

lemma foldr_add_mat_delta:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat"
  assumes fc: "\<forall>x \<in> set xs. f x \<in> carrier_mat m n" and d: "distinct xs" and i: "i \<in> set xs"
  shows "foldr (\<lambda>x acc. (if x = i then f x else 0\<^sub>m m n) + acc) xs (0\<^sub>m m n) = f i"
  using fc d i
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x = i")
    case True
    hence "i \<notin> set xs" using Cons.prems by simp
    hence "foldr (\<lambda>x acc. (if x = i then f x else 0\<^sub>m m n) + acc) xs (0\<^sub>m m n) = 0\<^sub>m m n"
      by (subst foldr_add_mat_cong[where g = "\<lambda>_. 0\<^sub>m m n"]) (auto simp: foldr_add_mat_zero)
    thus ?thesis using True Cons.prems by simp
  next
    case False
    thus ?thesis using Cons by simp
  qed
qed

lemma foldr_add_mat_smult_pull:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat" and c :: "'a \<Rightarrow> complex"
  assumes fc: "\<forall>x \<in> set xs. f x = c x \<cdot>\<^sub>m M" and Mc: "M \<in> carrier_mat m n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m m n) = sum_list (map c xs) \<cdot>\<^sub>m M"
  using fc
proof (induction xs)
  case Nil show ?case using Mc by (intro eq_matI) auto
next
  case (Cons x xs)
  have "foldr (\<lambda>x acc. f x + acc) (x # xs) (0\<^sub>m m n) = c x \<cdot>\<^sub>m M + sum_list (map c xs) \<cdot>\<^sub>m M"
    using Cons by simp
  also have "\<dots> = (c x + sum_list (map c xs)) \<cdot>\<^sub>m M" using Mc by (intro eq_matI) (auto simp: algebra_simps)
  finally show ?case by simp
qed

lemma foldr_list_as_index:
  fixes g :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  shows "foldr (\<lambda>A acc. g A + acc) As z = foldr (\<lambda>l acc. g (As ! l) + acc) [0..<length As] z"
proof -
  have "foldr (\<lambda>l acc. g (As ! l) + acc) [0..<length As] z = foldr (\<lambda>A acc. g A + acc) (map (nth As) [0..<length As]) z"
    by (simp add: foldr_map comp_def)
  also have "map (nth As) [0..<length As] = As" by (rule map_nth)
  finally show ?thesis ..
qed

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

text \<open>Every \<open>msum\<close> has its stated dimensions; multiplying a sum on the right.\<close>

lemma msum_dims [simp]: "dim_row (msum r c g xs) = r" "dim_col (msum r c g xs) = c"
  by (induction xs) simp_all

lemma msum_mult_right:
  assumes "\<forall>x \<in> set xs. g x \<in> carrier_mat r c" and "B \<in> carrier_mat c p"
  shows "msum r c g xs * B = msum r p (\<lambda>x. g x * B) xs"
  unfolding msum_def by (rule foldr_add_mat_mult_right[OF assms(2,1)])

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

text \<open>Concatenating rows of equal length, and the reindexing
$\kappa=ik+j$.\<close>

lemma concat_uniform_length:
  assumes "\<forall>xs \<in> set L. length xs = m"
  shows "length (concat L) = length L * m"
  using assms by (induct L) auto

lemma concat_uniform_nth:
  assumes uniform: "\<forall>xs \<in> set L. length xs = m"
      and i_lt: "i < length L"
      and j_lt: "j < m"
  shows "concat L ! (i * m + j) = L ! i ! j"
  using uniform i_lt
proof (induction L arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons l L)
  hence l_len: "length l = m" and rest_uniform: "\<forall>xs \<in> set L. length xs = m"
    by simp_all
  show ?case
  proof (cases i)
    case 0
    show ?thesis using 0 l_len j_lt by (simp add: nth_append)
  next
    case (Suc i')
    hence i'_lt: "i' < length L" using Cons.prems by simp
    have idx_shift: "i * m + j = m + (i' * m + j)"
      using Suc by (simp add: algebra_simps)
    have lhs_split: "concat (l # L) ! (i * m + j)
                       = concat L ! (i' * m + j)"
      using l_len idx_shift j_lt by (simp add: nth_append)
    have rhs: "(l # L) ! i ! j = L ! i' ! j"
      using Suc by simp
    show ?thesis using lhs_split rhs Cons.IH[OF rest_uniform i'_lt] by simp
  qed
qed

lemma sum_split_prod_atLeastLessThan:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>\<kappa> = 0..<N * k. f \<kappa>) = (\<Sum>i = 0..<N. \<Sum>j = 0..<k. f (i * k + j))"
proof -
  have step1: "(\<Sum>\<kappa> < N * k. f \<kappa>) = (\<Sum>i < N. \<Sum>\<kappa> \<in> {i*k..<i*k + k}. f \<kappa>)"
    by (rule sum.nat_group[symmetric])
  have step2: "\<And>i. (\<Sum>\<kappa> \<in> {i*k..<i*k + k}. f \<kappa>) = (\<Sum>j = 0..<k. f (j + i*k))"
  proof -
    fix i
    have "(\<Sum>\<kappa> \<in> {0 + i*k..<k + i*k}. f \<kappa>) = (\<Sum>j = 0..<k. f (j + i*k))"
      by (rule sum.shift_bounds_nat_ivl)
    thus "(\<Sum>\<kappa> \<in> {i*k..<i*k + k}. f \<kappa>) = (\<Sum>j = 0..<k. f (j + i*k))"
      by (simp add: add.commute)
  qed
  have step3: "\<And>i j. f (j + i * k) = f (i * k + j)"
    by (simp add: add.commute)
  have "(\<Sum>\<kappa> < N * k. f \<kappa>) = (\<Sum>i < N. \<Sum>j = 0..<k. f (i * k + j))"
    using step1 step2 step3 by (simp cong: sum.cong)
  thus ?thesis by (simp add: atLeast0LessThan)
qed

text \<open>Sums over pairs of indices $(i,j)$ with $i,j<k$.\<close>

lemma msum_pairs_carrier:
  assumes "\<And>i j. i < k \<Longrightarrow> j < k \<Longrightarrow> g i j \<in> carrier_mat r c"
  shows "msum r c (\<lambda>(i, j). g i j) (List.product [0..<k] [0..<k]) \<in> carrier_mat r c"
  by (rule msum_carrier) (use assms in auto)

lemma msum_pairs_index:
  assumes g: "\<And>i j. i < k \<Longrightarrow> j < k \<Longrightarrow> g i j \<in> carrier_mat r c" and a: "a < r" and b: "b < c"
  shows "msum r c (\<lambda>(i, j). g i j) (List.product [0..<k] [0..<k]) $$ (a, b)
       = (\<Sum>i<k. \<Sum>j<k. g i j $$ (a, b))"
proof -
  have "\<forall>x \<in> set (List.product [0..<k] [0..<k]). (case x of (i, j) \<Rightarrow> g i j) \<in> carrier_mat r c"
    using g by auto
  from msum_index[OF this a b] show ?thesis by (simp add: sum_list_product_upt)
qed

lemma msum_pairs_mult_right:
  assumes g: "\<And>i j. i < k \<Longrightarrow> j < k \<Longrightarrow> g i j \<in> carrier_mat r c" and B: "B \<in> carrier_mat c p"
  shows "msum r c (\<lambda>(i, j). g i j) (List.product [0..<k] [0..<k]) * B
       = msum r p (\<lambda>(i, j). g i j * B) (List.product [0..<k] [0..<k])"
proof -
  have "msum r c (\<lambda>(i, j). g i j) (List.product [0..<k] [0..<k]) * B
      = msum r p (\<lambda>x. (case x of (i, j) \<Rightarrow> g i j) * B) (List.product [0..<k] [0..<k])"
    by (rule msum_mult_right[OF _ B]) (use g in auto)
  also have "(\<lambda>x. (case x of (i, j) \<Rightarrow> g i j) * B) = (\<lambda>(i, j). g i j * B)"
    by (rule ext) (simp split: prod.split)
  finally show ?thesis .
qed

lemma msum_upt_index:
  assumes "\<And>x. x < m \<Longrightarrow> g x \<in> carrier_mat r c" and "a < r" and "b < c"
  shows "msum r c g [0..<m] $$ (a, b) = (\<Sum>x<m. g x $$ (a, b))"
  using assms by (simp add: msum_index interv_sum_list_conv_sum_set_nat atLeast0LessThan)

lemma idx8: "k < (8::nat) \<Longrightarrow> k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3 \<or> k = 4 \<or> k = 5 \<or> k = 6 \<or> k = 7"
  by auto

section \<open>Linear maps on a set of matrices\<close>

text \<open>Linearity of a map defined on a set of $n\times n$ matrices (an operator system, from
Day 24 on) with values in $M_d$.\<close>

definition lin_on :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "lin_on n d OS \<Phi> \<longleftrightarrow> (\<forall>A \<in> OS. \<Phi> A \<in> carrier_mat d d) \<and> (\<forall>A \<in> OS. \<forall>B \<in> OS. \<Phi> (A + B) = \<Phi> A + \<Phi> B)
     \<and> (\<forall>A \<in> OS. \<forall>c. \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A)"

text \<open>On a set closed under sums and containing $0$, such a map commutes with finite sums.\<close>

lemma msum_closed:
  assumes S0: "0\<^sub>m n n \<in> S" and S: "\<And>A B. A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> A + B \<in> S"
    and g: "\<forall>x \<in> set xs. g x \<in> S"
  shows "msum n n g xs \<in> S"
  using g by (induction xs) (auto intro: S simp: S0)

lemma lin_on_msum_closed:
  assumes L: "lin_on n d S \<Phi>" and S0: "0\<^sub>m n n \<in> S" and S: "\<And>A B. A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> A + B \<in> S"
    and g: "\<forall>x \<in> set xs. g x \<in> S"
  shows "\<Phi> (msum n n g xs) = msum d d (\<lambda>x. \<Phi> (g x)) xs"
  using g
proof (induction xs)
  case Nil
  have "\<Phi> (0 \<cdot>\<^sub>m 0\<^sub>m n n) = 0 \<cdot>\<^sub>m \<Phi> (0\<^sub>m n n)" and c: "\<Phi> (0\<^sub>m n n) \<in> carrier_mat d d"
    using L S0 unfolding lin_on_def by blast+
  moreover have "(0 :: complex) \<cdot>\<^sub>m 0\<^sub>m n n = 0\<^sub>m n n" by (rule eq_matI) simp_all
  moreover have "(0 :: complex) \<cdot>\<^sub>m \<Phi> (0\<^sub>m n n) = 0\<^sub>m d d" using c by (intro eq_matI) auto
  ultimately show ?case by simp
next
  case (Cons x xs)
  hence gx: "g x \<in> S" and rest: "\<forall>x \<in> set xs. g x \<in> S" by auto
  have "\<Phi> (g x + msum n n g xs) = \<Phi> (g x) + \<Phi> (msum n n g xs)"
    using L gx msum_closed[OF S0 S rest] unfolding lin_on_def by blast
  thus ?case using Cons.IH[OF rest] by simp
qed

lemma lin_on_smult:
  assumes "lin_on n d S F"
  shows "lin_on n d S (\<lambda>X. a \<cdot>\<^sub>m F X)"
  using assms unfolding lin_on_def
  by (auto simp: add_smult_distrib_left_mat[of _ d d] smult_smult_mat mult.commute)

section \<open>Linear-space isomorphisms\<close>

text \<open>Matrix spaces are represented by carrier predicates on the single type
\<^typ>\<open>complex Matrix.mat\<close>.  The record below packages a carrier with its zero,
addition and scalar multiplication, so that statements such as
$L(\Hil_A)\otimes L(\Hil_B)\cong L(\Hil_A\otimes\Hil_B)$ (Day 15) can be made as explicit
linear isomorphisms with explicit inverses.\<close>

record ('a, 'v) linear_structure =
  ls_carrier :: "'v set"
  ls_zero :: "'v"
  ls_add :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"
  ls_smul :: "'a \<Rightarrow> 'v \<Rightarrow> 'v"

definition linear_structure_map ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "linear_structure_map V W f \<equiv>
     f (ls_zero V) = ls_zero W \<and>
     (\<forall>x \<in> ls_carrier V. f x \<in> ls_carrier W) \<and>
     (\<forall>x \<in> ls_carrier V. \<forall>y \<in> ls_carrier V.
        f (ls_add V x y) = ls_add W (f x) (f y)) \<and>
     (\<forall>c x. x \<in> ls_carrier V \<longrightarrow>
        f (ls_smul V c x) = ls_smul W c (f x))"

definition is_isomorphism_between ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "is_isomorphism_between V W f \<equiv>
     linear_structure_map V W f \<and>
     (\<exists>g. linear_structure_map W V g \<and>
          (\<forall>x \<in> ls_carrier V. g (f x) = x) \<and>
          (\<forall>y \<in> ls_carrier W. f (g y) = y))"

definition is_isomorphic_to ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> bool" where
  "is_isomorphic_to V W \<equiv> \<exists>f. is_isomorphism_between V W f"

lemma is_isomorphism_betweenD_map:
  assumes "is_isomorphism_between V W f"
  shows "linear_structure_map V W f"
  using assms by (simp add: is_isomorphism_between_def)

lemma is_isomorphism_betweenD_inverse:
  assumes "is_isomorphism_between V W f"
  obtains g where "linear_structure_map W V g"
    and "\<And>x. x \<in> ls_carrier V \<Longrightarrow> g (f x) = x"
    and "\<And>y. y \<in> ls_carrier W \<Longrightarrow> f (g y) = y"
  using assms by (auto simp: is_isomorphism_between_def)

text \<open>The example used throughout: $M_{m,n}$ with entrywise addition and scaling.\<close>

definition mat_linear_structure :: "nat \<Rightarrow> nat \<Rightarrow> (complex, complex Matrix.mat) linear_structure" where
  "mat_linear_structure m n \<equiv>
     \<lparr> ls_carrier = carrier_mat m n,
       ls_zero = 0\<^sub>m m n,
       ls_add = (\<lambda>x y. x + y),
       ls_smul = (\<lambda>c x. c \<cdot>\<^sub>m x) \<rparr>"

end
