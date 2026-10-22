theory Day32_Recovery_Proposition
  imports Day21_Unitary_Freedom
begin

section \<open>Days 32--33: composition of Kraus maps and the general recovery proposition (D32-4, D33-2)\<close>

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

lemma foldr_add_mat_cong:
  fixes f g :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows "foldr (\<lambda>x acc. f x + acc) xs z = foldr (\<lambda>x acc. g x + acc) xs z"
  using assms by (induction xs) auto

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

subsection \<open>Composition of Kraus maps\<close>

definition kraus_compose :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "kraus_compose As Es = concat (map (\<lambda>E. map (\<lambda>A. A * E) As) Es)"

lemma kraus_compose_Nil [simp]: "kraus_compose As [] = []"
  by (simp add: kraus_compose_def)

lemma kraus_compose_Cons: "kraus_compose As (E # Es) = map (\<lambda>A. A * E) As @ kraus_compose As Es"
  by (simp add: kraus_compose_def)

lemma length_kraus_compose [simp]: "length (kraus_compose As Es) = length Es * length As"
  by (induction Es) (simp_all add: kraus_compose_Cons)

lemma kraus_compose_nth:
  assumes i: "i < length Es" and l: "l < length As"
  shows "kraus_compose As Es ! (i * length As + l) = As ! l * Es ! i"
  using i
proof (induction Es arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons E Es)
  show ?case
  proof (cases i)
    case 0 thus ?thesis using l by (simp add: kraus_compose_Cons nth_append)
  next
    case (Suc i')
    hence "i * length As + l = length As + (i' * length As + l)" by simp
    thus ?thesis using Suc Cons by (simp add: kraus_compose_Cons nth_append)
  qed
qed

lemma kraus_compose_carrier:
  assumes "\<forall>A \<in> set As. A \<in> carrier_mat m d" and "\<forall>E \<in> set Es. E \<in> carrier_mat d n"
  shows "\<forall>W \<in> set (kraus_compose As Es). W \<in> carrier_mat m n"
  using assms by (auto simp: kraus_compose_def)

lemma kraus_map_dim_map_mult_right:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and Ec: "E \<in> carrier_mat d n" and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim m (map (\<lambda>A. A * E) As) M = kraus_map_dim m As (E * M * (E\<^sup>\<dagger>))"
  using As_c
proof (induction As)
  case Nil show ?case by simp
next
  case (Cons A As)
  have Ac: "A \<in> carrier_mat m d" using Cons.prems by simp
  have Adc: "A\<^sup>\<dagger> \<in> carrier_mat d m" and Edc: "E\<^sup>\<dagger> \<in> carrier_mat n d"
    by (rule dagger_carrier[OF Ac]) (rule dagger_carrier[OF Ec])
  have dag: "(A * E)\<^sup>\<dagger> = (E\<^sup>\<dagger>) * (A\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp only: carrier_matD[OF Ac] carrier_matD[OF Ec])
  have "(A * E) * M * ((A * E)\<^sup>\<dagger>) = ((A * E) * M) * ((E\<^sup>\<dagger>) * (A\<^sup>\<dagger>))" by (simp only: dag)
  also have "\<dots> = (A * (E * M)) * ((E\<^sup>\<dagger>) * (A\<^sup>\<dagger>))" by (simp only: assoc_mult_mat[OF Ac Ec Xc])
  also have "\<dots> = A * ((E * M) * ((E\<^sup>\<dagger>) * (A\<^sup>\<dagger>)))"
    by (rule assoc_mult_mat[OF Ac mult_carrier_mat[OF Ec Xc] mult_carrier_mat[OF Edc Adc]])
  also have "\<dots> = A * (((E * M) * (E\<^sup>\<dagger>)) * (A\<^sup>\<dagger>))"
    by (simp only: assoc_mult_mat[OF mult_carrier_mat[OF Ec Xc] Edc Adc, symmetric])
  also have "\<dots> = A * (E * M * (E\<^sup>\<dagger>)) * (A\<^sup>\<dagger>)"
    by (rule assoc_mult_mat[OF Ac mult_carrier_mat[OF mult_carrier_mat[OF Ec Xc] Edc] Adc, symmetric])
  finally have "(A * E) * M * ((A * E)\<^sup>\<dagger>) = A * (E * M * (E\<^sup>\<dagger>)) * (A\<^sup>\<dagger>)" .
  thus ?case using Cons by simp
qed

lemma kraus_map_dim_compose:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat d n"
      and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim m (kraus_compose As Es) M = kraus_map_dim m As (kraus_map_dim d Es M)"
  using Es_c
proof (induction Es)
  case Nil show ?case using As_c by (simp add: kraus_map_dim_zero)
next
  case (Cons E Es)
  have Ec: "E \<in> carrier_mat d n" and Es_c': "\<forall>E \<in> set Es. E \<in> carrier_mat d n" using Cons.prems by auto
  have c1: "\<forall>W \<in> set (map (\<lambda>A. A * E) As). W \<in> carrier_mat m n" using As_c Ec by auto
  have c2: "\<forall>W \<in> set (kraus_compose As Es). W \<in> carrier_mat m n" by (rule kraus_compose_carrier[OF As_c Es_c'])
  have EXE: "E * M * (E\<^sup>\<dagger>) \<in> carrier_mat d d" using Ec Xc dagger_carrier[OF Ec] by auto
  have kc: "kraus_map_dim d Es M \<in> carrier_mat d d" by (rule kraus_map_dim_carrier[OF Es_c' Xc])
  have "kraus_map_dim m (kraus_compose As (E # Es)) M
        = kraus_map_dim m As (E * M * (E\<^sup>\<dagger>)) + kraus_map_dim m As (kraus_map_dim d Es M)"
    unfolding kraus_compose_Cons kraus_map_dim_append[OF c1 c2 Xc]
    using kraus_map_dim_map_mult_right[OF As_c Ec Xc] Cons.IH[OF Es_c'] by simp
  also have "\<dots> = kraus_map_dim m As (E * M * (E\<^sup>\<dagger>) + kraus_map_dim d Es M)"
    by (rule kraus_map_dim_add[OF EXE kc As_c, symmetric])
  finally show ?case by simp
qed

lemma sum_wdag_w_map_mult_right:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and Ec: "E \<in> carrier_mat d n"
  shows "sum_wdag_w n (map (\<lambda>A. A * E) As) = (E\<^sup>\<dagger>) * sum_wdag_w d As * E"
  using As_c
proof (induction As)
  case Nil show ?case using Ec dagger_carrier[OF Ec] by simp
next
  case (Cons A As)
  have Ac: "A \<in> carrier_mat m d" and As_c': "\<forall>A \<in> set As. A \<in> carrier_mat m d" using Cons.prems by auto
  have sc: "sum_wdag_w d As \<in> carrier_mat d d" by (rule sum_wdag_w_carrier[OF As_c'])
  have AA: "(A\<^sup>\<dagger>) * A \<in> carrier_mat d d" using Ac dagger_carrier[OF Ac] by auto
  have Adc: "A\<^sup>\<dagger> \<in> carrier_mat d m" and Edc: "E\<^sup>\<dagger> \<in> carrier_mat n d"
    by (rule dagger_carrier[OF Ac]) (rule dagger_carrier[OF Ec])
  have dag: "(A * E)\<^sup>\<dagger> = (E\<^sup>\<dagger>) * (A\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp only: carrier_matD[OF Ac] carrier_matD[OF Ec])
  have "((A * E)\<^sup>\<dagger>) * (A * E) = ((E\<^sup>\<dagger>) * (A\<^sup>\<dagger>)) * (A * E)" by (simp only: dag)
  also have "\<dots> = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * (A * E))" by (rule assoc_mult_mat[OF Edc Adc mult_carrier_mat[OF Ac Ec]])
  also have "\<dots> = (E\<^sup>\<dagger>) * (((A\<^sup>\<dagger>) * A) * E)" by (simp only: assoc_mult_mat[OF Adc Ac Ec, symmetric])
  also have "\<dots> = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) * E"
    by (rule assoc_mult_mat[OF Edc mult_carrier_mat[OF Adc Ac] Ec, symmetric])
  finally have key: "((A * E)\<^sup>\<dagger>) * (A * E) = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) * E" .
  have "((A * E)\<^sup>\<dagger>) * (A * E) + (E\<^sup>\<dagger>) * sum_wdag_w d As * E
        = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) * E + (E\<^sup>\<dagger>) * sum_wdag_w d As * E" by (simp only: key)
  also have "\<dots> = ((E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) + (E\<^sup>\<dagger>) * sum_wdag_w d As) * E"
    by (rule add_mult_distrib_mat[OF mult_carrier_mat[OF Edc AA] mult_carrier_mat[OF Edc sc] Ec, symmetric])
  also have "(E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) + (E\<^sup>\<dagger>) * sum_wdag_w d As = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A + sum_wdag_w d As)"
    by (rule mult_add_distrib_mat[OF Edc AA sc, symmetric])
  finally show ?case unfolding list.map sum_wdag_w_Cons Cons.IH[OF As_c'] .
qed

lemma sum_wdag_w_compose:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat d n"
      and As_tp: "sum_wdag_w d As = 1\<^sub>m d"
  shows "sum_wdag_w n (kraus_compose As Es) = sum_wdag_w n Es"
  using Es_c
proof (induction Es)
  case Nil show ?case by simp
next
  case (Cons E Es)
  have Ec: "E \<in> carrier_mat d n" and Es_c': "\<forall>E \<in> set Es. E \<in> carrier_mat d n" using Cons.prems by auto
  have c1: "\<forall>W \<in> set (map (\<lambda>A. A * E) As). W \<in> carrier_mat m n" using As_c Ec by auto
  have c2: "\<forall>W \<in> set (kraus_compose As Es). W \<in> carrier_mat m n" by (rule kraus_compose_carrier[OF As_c Es_c'])
  have "sum_wdag_w n (kraus_compose As (E # Es)) = (E\<^sup>\<dagger>) * E + sum_wdag_w n (kraus_compose As Es)"
    unfolding kraus_compose_Cons sum_wdag_w_append[OF c1 c2] sum_wdag_w_map_mult_right[OF As_c Ec] As_tp
    using Ec dagger_carrier[OF Ec] by simp
  thus ?case using Cons.IH[OF Es_c'] by (simp add: sum_wdag_w_Cons)
qed

lemma kraus_operators_compose:
  assumes As: "kraus_operators d m As" and Es: "kraus_operators n d Es"
  shows "kraus_operators n m (kraus_compose As Es)"
proof -
  have As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and As_tp: "sum_wdag_w d As = 1\<^sub>m d"
    using As by (auto simp: kraus_operators_altdef)
  have Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat d n" and Es_tp: "sum_wdag_w n Es = 1\<^sub>m n"
    using Es by (auto simp: kraus_operators_altdef)
  show ?thesis
    unfolding kraus_operators_altdef
    using kraus_compose_carrier[OF As_c Es_c] sum_wdag_w_compose[OF As_c Es_c As_tp] Es_tp by simp
qed

subsection \<open>The general recovery proposition (D32-4) and its linear-combination form (D33-2)\<close>

subsection \<open>Matrix sums acting on vectors\<close>

lemma smult_zero_vec [simp]: "(c :: complex) \<cdot>\<^sub>v 0\<^sub>v n = 0\<^sub>v n"
  by (intro eq_vecI) auto

lemma zero_mat_mult_vec:
  assumes "dim_vec w = n" shows "(0\<^sub>m m n :: complex Matrix.mat) *\<^sub>v w = 0\<^sub>v m"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (0\<^sub>v m :: complex Matrix.vec)"
  hence i: "i < m" by simp
  have "((0\<^sub>m m n :: complex Matrix.mat) *\<^sub>v w) $ i = (0\<^sub>v n :: complex Matrix.vec) \<bullet> w" using i by simp
  also have "\<dots> = 0" by (rule scalar_prod_left_zero[OF carrier_vecI[OF assms]])
  finally show "((0\<^sub>m m n :: complex Matrix.mat) *\<^sub>v w) $ i = (0\<^sub>v m :: complex Matrix.vec) $ i" using i by simp
qed simp

lemma mult_mat_vec_zero_vec:
  assumes Ac: "A \<in> carrier_mat m n" shows "A *\<^sub>v (0\<^sub>v n :: complex Matrix.vec) = 0\<^sub>v m"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (0\<^sub>v m :: complex Matrix.vec)"
  hence i: "i < m" by simp
  have rc: "Matrix.row A i \<in> carrier_vec n" by (rule row_carrier_vec[OF i Ac])
  have "(A *\<^sub>v 0\<^sub>v n) $ i = Matrix.row A i \<bullet> 0\<^sub>v n" using i carrier_matD[OF Ac] by simp
  also have "\<dots> = 0" by (rule scalar_prod_right_zero[OF rc])
  finally show "(A *\<^sub>v 0\<^sub>v n) $ i = (0\<^sub>v m :: complex Matrix.vec) $ i" using i by simp
qed (simp add: carrier_matD[OF Ac])

lemma foldr_add_mat_mult_vec_zero:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes fc: "\<forall>x \<in> set xs. f x \<in> carrier_mat n n" and wd: "dim_vec w = n"
      and z: "\<And>x. x \<in> set xs \<Longrightarrow> f x *\<^sub>v w = 0\<^sub>v n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) *\<^sub>v w = 0\<^sub>v n"
  using fc z
proof (induction xs)
  case Nil show ?case by (simp add: zero_mat_mult_vec[OF wd])
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat n n" and rest: "\<forall>y \<in> set xs. f y \<in> carrier_mat n n" using Cons.prems(1) by auto
  have Fc: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n" by (rule foldr_add_carrier_dn[OF rest])
  have "foldr (\<lambda>x acc. f x + acc) (x # xs) (0\<^sub>m n n) *\<^sub>v w = f x *\<^sub>v w + foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) *\<^sub>v w"
    by (simp only: foldr.simps o_apply add_mult_distrib_mat_vec[OF fx Fc carrier_vecI[OF wd]])
  also have "\<dots> = 0\<^sub>v n + 0\<^sub>v n" using Cons.prems(2) Cons.IH[OF rest] by simp
  also have "\<dots> = 0\<^sub>v n" by (intro eq_vecI) auto
  finally show ?case .
qed

lemma foldr_add_mat_mult_vec_delta:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat"
  assumes fc: "\<forall>x \<in> set xs. f x \<in> carrier_mat n n" and wd: "dim_vec w = n"
      and d: "distinct xs" and j: "j \<in> set xs"
      and del: "\<And>x. x \<in> set xs \<Longrightarrow> f x *\<^sub>v w = (if x = j then w else 0\<^sub>v n)"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) *\<^sub>v w = w"
  using fc d j del
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat n n" and rest: "\<forall>y \<in> set xs. f y \<in> carrier_mat n n" using Cons.prems(1) by auto
  have Fc: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n" by (rule foldr_add_carrier_dn[OF rest])
  have unf: "foldr (\<lambda>x acc. f x + acc) (x # xs) (0\<^sub>m n n) *\<^sub>v w = f x *\<^sub>v w + foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) *\<^sub>v w"
    by (simp only: foldr.simps o_apply add_mult_distrib_mat_vec[OF fx Fc carrier_vecI[OF wd]])
  show ?case
  proof (cases "x = j")
    case True
    have nj: "j \<notin> set xs" using True Cons.prems(2) by simp
    have "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) *\<^sub>v w = 0\<^sub>v n"
    proof (rule foldr_add_mat_mult_vec_zero[OF rest wd])
      fix y assume y: "y \<in> set xs"
      hence "y \<noteq> j" using nj by auto
      thus "f y *\<^sub>v w = 0\<^sub>v n" using Cons.prems(4)[of y] y by simp
    qed
    moreover have "f x *\<^sub>v w = w" using Cons.prems(4)[of x] True by simp
    ultimately have "f x *\<^sub>v w + foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) *\<^sub>v w = w + 0\<^sub>v n" by simp
    also have "\<dots> = w" using wd by (intro eq_vecI) auto
    finally show ?thesis unfolding unf .
  next
    case False
    have "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) *\<^sub>v w = w"
    proof (rule Cons.IH[OF rest])
      show "distinct xs" using Cons.prems(2) by simp
      show "j \<in> set xs" using Cons.prems(3) False by simp
      fix y assume "y \<in> set xs" thus "f y *\<^sub>v w = (if y = j then w else 0\<^sub>v n)" using Cons.prems(4)[of y] by simp
    qed
    moreover have "f x *\<^sub>v w = 0\<^sub>v n" using Cons.prems(4)[of x] False by simp
    ultimately have "f x *\<^sub>v w + foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) *\<^sub>v w = 0\<^sub>v n + w" by simp
    also have "\<dots> = w" using wd by (intro eq_vecI) auto
    finally show ?thesis unfolding unf .
  qed
qed

lemma vec_sum_delta:
  assumes fin: "finite Js" and j: "j \<in> Js" and wd: "\<And>i. i \<in> Js \<Longrightarrow> dim_vec (w i) = n"
  shows "vec_sum n Js (\<lambda>i. if i = j then w i else 0\<^sub>v n) = w j"
proof (rule eq_vecI)
  fix k assume "k < dim_vec (w j)"
  hence k: "k < n" using wd[OF j] by simp
  have "vec_sum n Js (\<lambda>i. if i = j then w i else 0\<^sub>v n) $ k = (\<Sum>i\<in>Js. (if i = j then w i else 0\<^sub>v n) $ k)"
    using k by (simp only: vec_sum_index)
  also have "\<dots> = (\<Sum>i\<in>Js. if i = j then w j $ k else 0)"
  proof (intro sum.cong refl)
    fix i assume "i \<in> Js"
    show "(if i = j then w i else 0\<^sub>v n) $ k = (if i = j then w j $ k else 0)" using k by (cases "i = j") simp_all
  qed
  also have "\<dots> = w j $ k" by (simp only: sum.delta[OF fin]) (simp add: j)
  finally show "vec_sum n Js (\<lambda>i. if i = j then w i else 0\<^sub>v n) $ k = w j $ k" .
qed (simp add: wd[OF j])

text \<open>Let $V=\operatorname{ran}P$ for a projection $P$ and let $U_0,\dots,U_{t-1}$ be unitaries with
$U_iV\perp U_jV$ for $i\ne j$, i.e.\ $PU_i^*U_jP=0$.  With $P_i=U_iPU_i^*$, $Q=I-\sum_iP_i$ and the
Kraus operators $PU_i^*$ (the notes write $U_i^*P_i=PU_i^*$) the map
$R(X)=QXQ+\sum_iPU_i^*XU_iP$ is CPTP and recovers every $\psi\in V$ from any
$\varphi=\sum_ia_iU_i\psi$: $R(|\varphi\rangle\langle\varphi|)=(\sum_i|a_i|^2)|\psi\rangle\langle\psi|$.\<close>

definition image_proj_sum :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "image_proj_sum n P Us = foldr (\<lambda>i acc. Us ! i * P * ((Us ! i)\<^sup>\<dagger>) + acc) [0..<length Us] (0\<^sub>m n n)"

definition recovery_ops :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "recovery_ops n P Us = (1\<^sub>m n - image_proj_sum n P Us) # map (\<lambda>i. P * ((Us ! i)\<^sup>\<dagger>)) [0..<length Us]"

text \<open>The hypotheses of the proposition, bundled: $P$ a projection and $PU_i^*U_jP=\delta_{ij}P$.
For unitaries $U_i$ the case $i=j$ is automatic (\<open>recovery_setting_unitaries\<close>); the weaker form
also covers the rescaled errors of the Knill--Laflamme theorem.\<close>

definition recovery_setting :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "recovery_setting n P Us \<longleftrightarrow> projection n P \<and> (\<forall>U \<in> set Us. U \<in> carrier_mat n n)
     \<and> (\<forall>i < length Us. \<forall>j < length Us. P * (((Us ! i)\<^sup>\<dagger>) * Us ! j) * P = (if i = j then P else 0\<^sub>m n n))"

lemma recovery_settingD:
  assumes "recovery_setting n P Us"
  shows "projection n P" "\<forall>U \<in> set Us. U \<in> carrier_mat n n"
    "\<forall>i < length Us. \<forall>j < length Us. i \<noteq> j \<longrightarrow> P * (((Us ! i)\<^sup>\<dagger>) * Us ! j) * P = 0\<^sub>m n n"
    "\<forall>i < length Us. P * (((Us ! i)\<^sup>\<dagger>) * Us ! i) * P = P"
  using assms unfolding recovery_setting_def by auto

lemma recovery_setting_unitaries:
  assumes P: "projection n P" and Us: "\<forall>U \<in> set Us. U \<in> carrier_mat n n \<and> unitary U"
      and orth: "\<forall>i < length Us. \<forall>j < length Us. i \<noteq> j \<longrightarrow> P * (((Us ! i)\<^sup>\<dagger>) * Us ! j) * P = 0\<^sub>m n n"
  shows "recovery_setting n P Us"
  unfolding recovery_setting_def
proof (intro conjI ballI allI impI)
  show "projection n P" by (rule P)
  fix U assume "U \<in> set Us" thus "U \<in> carrier_mat n n" using Us by blast
next
  fix i j assume i: "i < length Us" and j: "j < length Us"
  have Pc: "P \<in> carrier_mat n n" and PP: "P * P = P" using P by (auto simp: projection_def)
  have "((Us ! i)\<^sup>\<dagger>) * Us ! i = 1\<^sub>m n" using Us nth_mem[OF i] by (auto simp: unitary_def)
  hence "P * (((Us ! i)\<^sup>\<dagger>) * Us ! i) * P = P" by (simp only: right_mult_one_mat[OF Pc] PP)
  thus "P * (((Us ! i)\<^sup>\<dagger>) * Us ! j) * P = (if i = j then P else 0\<^sub>m n n)" using orth i j by auto
qed

lemma
  assumes S: "recovery_setting n P Us"
  shows rec_Pc: "P \<in> carrier_mat n n" and rec_Ph: "P\<^sup>\<dagger> = P" and rec_PP: "P * P = P"
  using recovery_settingD(1)[OF S] by (auto simp: projection_def hermitian_def)

lemma
  assumes S: "recovery_setting n P Us"
  shows rec_Uc: "i < length Us \<Longrightarrow> Us ! i \<in> carrier_mat n n"
    and rec_PUUP: "i < length Us \<Longrightarrow> P * (((Us ! i)\<^sup>\<dagger>) * Us ! i) * P = P"
  using recovery_settingD(2,4)[OF S] by auto

lemma rec_Pi_c:
  assumes S: "recovery_setting n P Us" and i: "i < length Us"
  shows "Us ! i * P * ((Us ! i)\<^sup>\<dagger>) \<in> carrier_mat n n"
  by (rule mult_carrier_mat[OF mult_carrier_mat[OF rec_Uc[OF S i] rec_Pc[OF S]] dagger_carrier[OF rec_Uc[OF S i]]])

lemma rec_Pi_mult:
  assumes S: "recovery_setting n P Us" and i: "i < length Us" and j: "j < length Us"
  shows "(Us ! i * P * ((Us ! i)\<^sup>\<dagger>)) * (Us ! j * P * ((Us ! j)\<^sup>\<dagger>))
         = (if i = j then Us ! i * P * ((Us ! i)\<^sup>\<dagger>) else 0\<^sub>m n n)"
proof -
  let ?Ui = "Us ! i" and ?Uj = "Us ! j" and ?Uid = "(Us ! i)\<^sup>\<dagger>" and ?Ujd = "(Us ! j)\<^sup>\<dagger>"
  have Pc: "P \<in> carrier_mat n n" by (rule rec_Pc[OF S])
  have Uic: "?Ui \<in> carrier_mat n n" and Ujc: "?Uj \<in> carrier_mat n n"
    by (rule rec_Uc[OF S i]) (rule rec_Uc[OF S j])
  have Uidc: "?Uid \<in> carrier_mat n n" and Ujdc: "?Ujd \<in> carrier_mat n n"
    by (rule dagger_carrier[OF Uic]) (rule dagger_carrier[OF Ujc])
  have "(?Ui * P * ?Uid) * (?Uj * P * ?Ujd) = (?Ui * P) * (?Uid * (?Uj * P * ?Ujd))"
    by (rule assoc_mult_mat[OF mult_carrier_mat[OF Uic Pc] Uidc
          mult_carrier_mat[OF mult_carrier_mat[OF Ujc Pc] Ujdc]])
  also have "\<dots> = ?Ui * (P * (?Uid * (?Uj * P * ?Ujd)))"
    by (rule assoc_mult_mat[OF Uic Pc mult_carrier_mat[OF Uidc mult_carrier_mat[OF mult_carrier_mat[OF Ujc Pc] Ujdc]]])
  also have "\<dots> = ?Ui * (P * ((?Uid * (?Uj * P)) * ?Ujd))"
    by (simp only: assoc_mult_mat[OF Uidc mult_carrier_mat[OF Ujc Pc] Ujdc, symmetric])
  also have "\<dots> = ?Ui * (P * (((?Uid * ?Uj) * P) * ?Ujd))"
    by (simp only: assoc_mult_mat[OF Uidc Ujc Pc, symmetric])
  also have "\<dots> = ?Ui * ((P * ((?Uid * ?Uj) * P)) * ?Ujd)"
    by (simp only: assoc_mult_mat[OF Pc mult_carrier_mat[OF mult_carrier_mat[OF Uidc Ujc] Pc] Ujdc, symmetric])
  also have "\<dots> = ?Ui * (((P * (?Uid * ?Uj)) * P) * ?Ujd)"
    by (simp only: assoc_mult_mat[OF Pc mult_carrier_mat[OF Uidc Ujc] Pc, symmetric])
  also have "\<dots> = (?Ui * ((P * (?Uid * ?Uj)) * P)) * ?Ujd"
    by (rule assoc_mult_mat[OF Uic mult_carrier_mat[OF mult_carrier_mat[OF Pc mult_carrier_mat[OF Uidc Ujc]] Pc] Ujdc, symmetric])
  finally have key: "(?Ui * P * ?Uid) * (?Uj * P * ?Ujd) = ?Ui * (P * (?Uid * ?Uj) * P) * ?Ujd" .
  show ?thesis
  proof (cases "i = j")
    case True
    have PP: "P * (?Uid * ?Ui) * P = P"
      by (rule rec_PUUP[OF S i])
    show ?thesis unfolding True[symmetric] key[unfolded True[symmetric]] PP by simp
  next
    case False
    have z: "P * (?Uid * ?Uj) * P = 0\<^sub>m n n" using recovery_settingD(3)[OF S] i j False by blast
    show ?thesis unfolding key z using False
      by (simp add: right_mult_zero_mat[OF Uic] left_mult_zero_mat[OF Ujdc])
  qed
qed

lemma image_proj_sum_carrier:
  assumes S: "recovery_setting n P Us"
  shows "image_proj_sum n P Us \<in> carrier_mat n n"
  unfolding image_proj_sum_def by (rule foldr_add_carrier_dn) (simp add: rec_Pi_c[OF S])

lemma image_proj_sum_hermitian:
  assumes S: "recovery_setting n P Us"
  shows "(image_proj_sum n P Us)\<^sup>\<dagger> = image_proj_sum n P Us"
proof -
  have Pc: "P \<in> carrier_mat n n" by (rule rec_Pc[OF S])
  have h: "\<And>i. i < length Us \<Longrightarrow> (Us ! i * P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger> = Us ! i * P * ((Us ! i)\<^sup>\<dagger>)"
  proof -
    fix i assume i: "i < length Us"
    have Uic: "Us ! i \<in> carrier_mat n n" by (rule rec_Uc[OF S i])
    have Uidc: "(Us ! i)\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Uic])
    have "(Us ! i * P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger> = (((Us ! i)\<^sup>\<dagger>)\<^sup>\<dagger>) * ((Us ! i * P)\<^sup>\<dagger>)"
      by (rule dagger_of_prod) (simp only: carrier_matD[OF mult_carrier_mat[OF Uic Pc]] carrier_matD[OF Uidc])
    also have "(Us ! i * P)\<^sup>\<dagger> = (P\<^sup>\<dagger>) * ((Us ! i)\<^sup>\<dagger>)"
      by (rule dagger_of_prod) (simp only: carrier_matD[OF Uic] carrier_matD[OF Pc])
    also have "(((Us ! i)\<^sup>\<dagger>)\<^sup>\<dagger>) * ((P\<^sup>\<dagger>) * ((Us ! i)\<^sup>\<dagger>)) = Us ! i * (P * ((Us ! i)\<^sup>\<dagger>))"
      by (simp add: dagger_of_dagger_is_id rec_Ph[OF S])
    also have "\<dots> = Us ! i * P * ((Us ! i)\<^sup>\<dagger>)" by (rule assoc_mult_mat[OF Uic Pc Uidc, symmetric])
    finally show "(Us ! i * P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger> = Us ! i * P * ((Us ! i)\<^sup>\<dagger>)" .
  qed
  have "(image_proj_sum n P Us)\<^sup>\<dagger>
        = foldr (\<lambda>i acc. (Us ! i * P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger> + acc) [0..<length Us] (0\<^sub>m n n)"
    unfolding image_proj_sum_def by (rule foldr_add_mat_dagger) (simp add: rec_Pi_c[OF S])
  also have "\<dots> = foldr (\<lambda>i acc. Us ! i * P * ((Us ! i)\<^sup>\<dagger>) + acc) [0..<length Us] (0\<^sub>m n n)"
    by (rule foldr_add_mat_cong) (simp add: h)
  finally show ?thesis unfolding image_proj_sum_def .
qed

lemma image_proj_sum_idem:
  assumes S: "recovery_setting n P Us"
  shows "image_proj_sum n P Us * image_proj_sum n P Us = image_proj_sum n P Us"
proof -
  let ?Pi = "\<lambda>i. Us ! i * P * ((Us ! i)\<^sup>\<dagger>)"
  let ?S = "image_proj_sum n P Us"
  have Pic: "\<forall>i \<in> set [0..<length Us]. ?Pi i \<in> carrier_mat n n" using rec_Pi_c[OF S] by simp
  have "?S * ?S = foldr (\<lambda>i acc. ?Pi i * ?S + acc) [0..<length Us] (0\<^sub>m n n)"
    unfolding image_proj_sum_def
    by (rule foldr_add_mat_mult_right[OF image_proj_sum_carrier[OF S, unfolded image_proj_sum_def] Pic])
  also have "\<dots> = foldr (\<lambda>i acc. ?Pi i + acc) [0..<length Us] (0\<^sub>m n n)"
  proof (rule foldr_add_mat_cong)
    fix i assume "i \<in> set [0..<length Us]"
    hence i: "i < length Us" by simp
    have "?Pi i * ?S = foldr (\<lambda>j acc. ?Pi i * ?Pi j + acc) [0..<length Us] (0\<^sub>m n n)"
      unfolding image_proj_sum_def by (rule foldr_add_mat_mult_left[OF rec_Pi_c[OF S i] Pic])
    also have "\<dots> = foldr (\<lambda>j acc. (if j = i then ?Pi j else 0\<^sub>m n n) + acc) [0..<length Us] (0\<^sub>m n n)"
    proof (rule foldr_add_mat_cong)
      fix j assume "j \<in> set [0..<length Us]"
      hence j: "j < length Us" by simp
      show "?Pi i * ?Pi j = (if j = i then ?Pi j else 0\<^sub>m n n)"
        unfolding rec_Pi_mult[OF S i j] by (cases "i = j") simp_all
    qed
    also have "\<dots> = ?Pi i" by (rule foldr_add_mat_delta[OF Pic]) (simp_all add: i)
    finally show "?Pi i * ?S = ?Pi i" .
  qed
  finally show ?thesis unfolding image_proj_sum_def .
qed

lemma image_proj_sum_projection:
  assumes S: "recovery_setting n P Us"
  shows "projection n (image_proj_sum n P Us)"
  unfolding projection_def hermitian_def
  using image_proj_sum_carrier[OF S] image_proj_sum_hermitian[OF S] image_proj_sum_idem[OF S] by simp

lemma dagger_one_minus:
  assumes Sc: "M \<in> carrier_mat n n" and Sh: "M\<^sup>\<dagger> = M"
  shows "(1\<^sub>m n - M)\<^sup>\<dagger> = 1\<^sub>m n - M"
proof (rule eq_matI)
  fix i j assume "i < dim_row (1\<^sub>m n - M)" "j < dim_col (1\<^sub>m n - M)"
  hence i: "i < n" and j: "j < n" using carrier_matD[OF Sc] by auto
  have "(M\<^sup>\<dagger>) $$ (i,j) = M $$ (i,j)" unfolding Sh ..
  hence c: "cnj (M $$ (j,i)) = M $$ (i,j)" using i j carrier_matD[OF Sc] by (simp add: dagger_def)
  show "((1\<^sub>m n - M)\<^sup>\<dagger>) $$ (i,j) = (1\<^sub>m n - M) $$ (i,j)"
    using i j carrier_matD[OF Sc] c by (simp add: dagger_def)
qed (use carrier_matD[OF Sc] in \<open>auto simp: dagger_def\<close>)

lemma recovery_ops_carrier:
  assumes S: "recovery_setting n P Us"
  shows "\<forall>W \<in> set (recovery_ops n P Us). W \<in> carrier_mat n n"
proof (unfold recovery_ops_def, intro ballI)
  fix W assume "W \<in> set ((1\<^sub>m n - image_proj_sum n P Us) # map (\<lambda>i. P * ((Us ! i)\<^sup>\<dagger>)) [0..<length Us])"
  hence "W = 1\<^sub>m n - image_proj_sum n P Us \<or> (\<exists>i < length Us. W = P * ((Us ! i)\<^sup>\<dagger>))" by auto
  thus "W \<in> carrier_mat n n"
  proof
    assume W: "W = 1\<^sub>m n - image_proj_sum n P Us"
    show ?thesis unfolding W by (intro minus_carrier_mat one_carrier_mat image_proj_sum_carrier[OF S])
  next
    assume "\<exists>i < length Us. W = P * ((Us ! i)\<^sup>\<dagger>)"
    then obtain i where i: "i < length Us" and W: "W = P * ((Us ! i)\<^sup>\<dagger>)" by blast
    show ?thesis unfolding W by (rule mult_carrier_mat[OF rec_Pc[OF S] dagger_carrier[OF rec_Uc[OF S i]]])
  qed
qed

theorem recovery_ops_kraus_operators:
  assumes S: "recovery_setting n P Us"
  shows "kraus_operators n n (recovery_ops n P Us)"
proof -
  let ?Q = "1\<^sub>m n - image_proj_sum n P Us"
  have Pc: "P \<in> carrier_mat n n" by (rule rec_Pc[OF S])
  have Sc: "image_proj_sum n P Us \<in> carrier_mat n n" by (rule image_proj_sum_carrier[OF S])
  have Qh: "?Q\<^sup>\<dagger> = ?Q" by (rule dagger_one_minus[OF Sc image_proj_sum_hermitian[OF S]])
  have QQ: "?Q * ?Q = ?Q" by (rule projection_complement_idempotent[OF image_proj_sum_projection[OF S]])
  have kterm: "\<And>i. i < length Us \<Longrightarrow>
      ((P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger>) * (P * ((Us ! i)\<^sup>\<dagger>)) = Us ! i * P * ((Us ! i)\<^sup>\<dagger>)"
  proof -
    fix i assume i: "i < length Us"
    have Uic: "Us ! i \<in> carrier_mat n n" by (rule rec_Uc[OF S i])
    have Uidc: "(Us ! i)\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Uic])
    have "(P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger> = (((Us ! i)\<^sup>\<dagger>)\<^sup>\<dagger>) * (P\<^sup>\<dagger>)"
      by (rule dagger_of_prod) (simp only: carrier_matD[OF Pc] carrier_matD[OF Uidc])
    also have "\<dots> = Us ! i * P" by (simp add: dagger_of_dagger_is_id rec_Ph[OF S])
    finally have d: "(P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger> = Us ! i * P" .
    have "((P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger>) * (P * ((Us ! i)\<^sup>\<dagger>)) = (Us ! i * P) * (P * ((Us ! i)\<^sup>\<dagger>))"
      by (simp only: d)
    also have "\<dots> = ((Us ! i * P) * P) * ((Us ! i)\<^sup>\<dagger>)"
      by (rule assoc_mult_mat[OF mult_carrier_mat[OF Uic Pc] Pc Uidc, symmetric])
    also have "\<dots> = (Us ! i * (P * P)) * ((Us ! i)\<^sup>\<dagger>)" by (simp only: assoc_mult_mat[OF Uic Pc Pc])
    also have "\<dots> = Us ! i * P * ((Us ! i)\<^sup>\<dagger>)" by (simp only: rec_PP[OF S])
    finally show "((P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger>) * (P * ((Us ! i)\<^sup>\<dagger>)) = Us ! i * P * ((Us ! i)\<^sup>\<dagger>)" .
  qed
  have "sum_wdag_w n (recovery_ops n P Us)
        = (?Q\<^sup>\<dagger>) * ?Q + foldr (\<lambda>i acc. ((P * ((Us ! i)\<^sup>\<dagger>))\<^sup>\<dagger>) * (P * ((Us ! i)\<^sup>\<dagger>)) + acc) [0..<length Us] (0\<^sub>m n n)"
    unfolding recovery_ops_def sum_wdag_w_Cons sum_wdag_w_def by (simp add: foldr_map comp_def)
  also have "\<dots> = ?Q + foldr (\<lambda>i acc. Us ! i * P * ((Us ! i)\<^sup>\<dagger>) + acc) [0..<length Us] (0\<^sub>m n n)"
    unfolding Qh QQ by (rule arg_cong[where f = "\<lambda>M. ?Q + M"]) (rule foldr_add_mat_cong, simp add: kterm)
  also have "\<dots> = ?Q + image_proj_sum n P Us" unfolding image_proj_sum_def ..
  also have "\<dots> = 1\<^sub>m n" using carrier_matD[OF Sc] by (intro eq_matI) auto
  finally show ?thesis unfolding kraus_operators_altdef using recovery_ops_carrier[OF S] by simp
qed

corollary recovery_map_CPTP':
  assumes S: "recovery_setting n P Us" and npos: "0 < n"
  shows "kraus_map_dim n (recovery_ops n P Us) \<in> CPTP n n"
  using kraus_is_cptp[OF recovery_ops_kraus_operators[OF S] npos npos] .

text \<open>Action of the Kraus operators on $\varphi=\sum_ia_iU_i\psi$, $\psi\in V$.\<close>

lemma rec_kraus_on_image:
  assumes S: "recovery_setting n P Us"
      and \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>" and i: "i < length Us" and j: "j < length Us"
  shows "(P * ((Us ! i)\<^sup>\<dagger>)) *\<^sub>v (Us ! j *\<^sub>v \<psi>) = (if i = j then \<psi> else 0\<^sub>v n)"
proof -
  let ?Uid = "(Us ! i)\<^sup>\<dagger>" and ?Uj = "Us ! j"
  have Pc: "P \<in> carrier_mat n n" by (rule rec_Pc[OF S])
  have Uic: "Us ! i \<in> carrier_mat n n" and Ujc: "?Uj \<in> carrier_mat n n"
    by (rule rec_Uc[OF S i]) (rule rec_Uc[OF S j])
  have Uidc: "?Uid \<in> carrier_mat n n" by (rule dagger_carrier[OF Uic])
  have \<psi>c: "\<psi> \<in> carrier_vec n" by (rule carrier_vecI[OF \<psi>d])
  have "(P * ?Uid) *\<^sub>v (?Uj *\<^sub>v \<psi>) = ((P * ?Uid) * ?Uj) *\<^sub>v \<psi>"
    by (rule assoc_mult_mat_vec[OF mult_carrier_mat[OF Pc Uidc] Ujc \<psi>c, symmetric])
  also have "\<dots> = (P * (?Uid * ?Uj)) *\<^sub>v \<psi>" by (simp only: assoc_mult_mat[OF Pc Uidc Ujc])
  also have "\<dots> = (P * (?Uid * ?Uj) * P) *\<^sub>v \<psi>"
    by (simp only: assoc_mult_mat_vec[OF mult_carrier_mat[OF Pc mult_carrier_mat[OF Uidc Ujc]] Pc \<psi>c] \<psi>V)
  also have "\<dots> = (if i = j then \<psi> else 0\<^sub>v n)"
  proof (cases "i = j")
    case True
    have "P * (?Uid * ?Uj) * P = P"
      unfolding True[symmetric] by (rule rec_PUUP[OF S i])
    thus ?thesis using True \<psi>V by simp
  next
    case False
    have "P * (?Uid * ?Uj) * P = 0\<^sub>m n n" using recovery_settingD(3)[OF S] i j False by blast
    thus ?thesis using False by (simp add: zero_mat_mult_vec[OF \<psi>d])
  qed
  finally show ?thesis .
qed

lemma rec_Q_on_image:
  assumes S: "recovery_setting n P Us"
      and \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>" and j: "j < length Us"
  shows "(1\<^sub>m n - image_proj_sum n P Us) *\<^sub>v (Us ! j *\<^sub>v \<psi>) = 0\<^sub>v n"
proof -
  let ?Pi = "\<lambda>i. Us ! i * P * ((Us ! i)\<^sup>\<dagger>)" and ?w = "Us ! j *\<^sub>v \<psi>"
  have Pc: "P \<in> carrier_mat n n" by (rule rec_Pc[OF S])
  have Ujc: "Us ! j \<in> carrier_mat n n" by (rule rec_Uc[OF S j])
  have wd: "dim_vec ?w = n" using carrier_matD(1)[OF Ujc] by simp
  have Pic: "\<forall>i \<in> set [0..<length Us]. ?Pi i \<in> carrier_mat n n" using rec_Pi_c[OF S] by simp
  have del: "\<And>i. i \<in> set [0..<length Us] \<Longrightarrow> ?Pi i *\<^sub>v ?w = (if i = j then ?w else 0\<^sub>v n)"
  proof -
    fix i assume "i \<in> set [0..<length Us]"
    hence i: "i < length Us" by simp
    have Uic: "Us ! i \<in> carrier_mat n n" by (rule rec_Uc[OF S i])
    have Uidc: "(Us ! i)\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Uic])
    have "?Pi i *\<^sub>v ?w = (Us ! i * (P * ((Us ! i)\<^sup>\<dagger>))) *\<^sub>v ?w" by (simp only: assoc_mult_mat[OF Uic Pc Uidc])
    also have "\<dots> = Us ! i *\<^sub>v ((P * ((Us ! i)\<^sup>\<dagger>)) *\<^sub>v ?w)"
      by (rule assoc_mult_mat_vec[OF Uic mult_carrier_mat[OF Pc Uidc] carrier_vecI[OF wd]])
    also have "\<dots> = Us ! i *\<^sub>v (if i = j then \<psi> else 0\<^sub>v n)" unfolding rec_kraus_on_image[OF S \<psi>d \<psi>V i j] ..
    also have "\<dots> = (if i = j then ?w else 0\<^sub>v n)" by (cases "i = j") (simp_all add: mult_mat_vec_zero_vec[OF Uic])
    finally show "?Pi i *\<^sub>v ?w = (if i = j then ?w else 0\<^sub>v n)" .
  qed
  have "image_proj_sum n P Us *\<^sub>v ?w = ?w"
    unfolding image_proj_sum_def by (rule foldr_add_mat_mult_vec_delta[OF Pic wd _ _ del]) (simp_all add: j)
  thus ?thesis
    unfolding minus_mult_distrib_mat_vec[OF one_carrier_mat image_proj_sum_carrier[OF S] carrier_vecI[OF wd]]
              one_mult_mat_vec[OF carrier_vecI[OF wd]]
    using wd by (intro eq_vecI) auto
qed

theorem recovery_linear_combination:
  fixes a :: "nat \<Rightarrow> complex"
  assumes S: "recovery_setting n P Us" and \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>"
  defines "\<phi> \<equiv> vec_sum n {i. i < length Us} (\<lambda>i. a i \<cdot>\<^sub>v (Us ! i *\<^sub>v \<psi>))"
  shows "kraus_map_dim n (recovery_ops n P Us) (\<phi> \<oslash> \<phi>)
         = complex_of_real (\<Sum>i < length Us. (cmod (a i))\<^sup>2) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
proof -
  let ?t = "length Us"
  let ?Q = "1\<^sub>m n - image_proj_sum n P Us"
  let ?W = "\<lambda>i. P * ((Us ! i)\<^sup>\<dagger>)"
  have Pc: "P \<in> carrier_mat n n" by (rule rec_Pc[OF S])
  have fin: "finite {i. i < ?t}" by simp
  have \<phi>d: "dim_vec \<phi> = n" by (simp add: \<phi>_def)
  have Ujd: "\<And>j. j < ?t \<Longrightarrow> dim_vec (Us ! j *\<^sub>v \<psi>) = n"
  proof -
    fix j assume "j < ?t"
    show "dim_vec (Us ! j *\<^sub>v \<psi>) = n" using carrier_matD(1)[OF rec_Uc[OF S \<open>j < ?t\<close>]] by simp
  qed
  have Uj\<psi>d: "\<And>j. j < ?t \<Longrightarrow> dim_vec (a j \<cdot>\<^sub>v (Us ! j *\<^sub>v \<psi>)) = n" using Ujd by simp
  have Qc: "?Q \<in> carrier_mat n n" by (intro minus_carrier_mat one_carrier_mat image_proj_sum_carrier[OF S])
  have Wc: "\<And>i. i < ?t \<Longrightarrow> ?W i \<in> carrier_mat n n"
  proof -
    fix i assume i: "i < ?t"
    show "?W i \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Pc dagger_carrier[OF rec_Uc[OF S i]]])
  qed
  \<comment> \<open>\<open>Q \<phi> = 0\<close> and \<open>W\<^sub>i \<phi> = a\<^sub>i \<psi>\<close>.\<close>
  have Q\<phi>: "?Q *\<^sub>v \<phi> = 0\<^sub>v n"
  proof -
    have "?Q *\<^sub>v \<phi> = vec_sum n {i. i < ?t} (\<lambda>j. ?Q *\<^sub>v (a j \<cdot>\<^sub>v (Us ! j *\<^sub>v \<psi>)))"
      unfolding \<phi>_def by (rule mult_mat_vec_vec_sum[OF Qc fin]) (simp add: carrier_matD(1)[OF rec_Uc[OF S]])
    also have "\<dots> = vec_sum n {i. i < ?t} (\<lambda>j. 0\<^sub>v n)"
    proof (rule vec_sum_cong)
      fix j assume "j \<in> {i. i < ?t}"
      hence j: "j < ?t" by simp
      have "?Q *\<^sub>v (a j \<cdot>\<^sub>v (Us ! j *\<^sub>v \<psi>)) = a j \<cdot>\<^sub>v (?Q *\<^sub>v (Us ! j *\<^sub>v \<psi>))"
        by (rule mult_mat_vec_smult_vec[OF Qc Ujd[OF j]])
      thus "?Q *\<^sub>v (a j \<cdot>\<^sub>v (Us ! j *\<^sub>v \<psi>)) = 0\<^sub>v n" unfolding rec_Q_on_image[OF S \<psi>d \<psi>V j] by simp
    qed
    also have "\<dots> = 0\<^sub>v n" by (intro eq_vecI) auto
    finally show ?thesis .
  qed
  have W\<phi>: "\<And>i. i < ?t \<Longrightarrow> ?W i *\<^sub>v \<phi> = a i \<cdot>\<^sub>v \<psi>"
  proof -
    fix i assume i: "i < ?t"
    have "?W i *\<^sub>v \<phi> = vec_sum n {i. i < ?t} (\<lambda>j. ?W i *\<^sub>v (a j \<cdot>\<^sub>v (Us ! j *\<^sub>v \<psi>)))"
      unfolding \<phi>_def by (rule mult_mat_vec_vec_sum[OF Wc[OF i] fin]) (simp add: carrier_matD(1)[OF rec_Uc[OF S]])
    also have "\<dots> = vec_sum n {i. i < ?t} (\<lambda>j. if j = i then a i \<cdot>\<^sub>v \<psi> else 0\<^sub>v n)"
    proof (rule vec_sum_cong)
      fix j assume "j \<in> {i. i < ?t}"
      hence j: "j < ?t" by simp
      have "?W i *\<^sub>v (a j \<cdot>\<^sub>v (Us ! j *\<^sub>v \<psi>)) = a j \<cdot>\<^sub>v (?W i *\<^sub>v (Us ! j *\<^sub>v \<psi>))"
        by (rule mult_mat_vec_smult_vec[OF Wc[OF i] Ujd[OF j]])
      also have "\<dots> = a j \<cdot>\<^sub>v (if i = j then \<psi> else 0\<^sub>v n)" unfolding rec_kraus_on_image[OF S \<psi>d \<psi>V i j] ..
      also have "\<dots> = (if j = i then a i \<cdot>\<^sub>v \<psi> else 0\<^sub>v n)" by (cases "i = j") simp_all
      finally show "?W i *\<^sub>v (a j \<cdot>\<^sub>v (Us ! j *\<^sub>v \<psi>)) = (if j = i then a i \<cdot>\<^sub>v \<psi> else 0\<^sub>v n)" .
    qed
    also have "\<dots> = a i \<cdot>\<^sub>v \<psi>" by (rule vec_sum_delta[OF fin]) (simp_all add: i \<psi>d)
    finally show "?W i *\<^sub>v \<phi> = a i \<cdot>\<^sub>v \<psi>" .
  qed
  \<comment> \<open>Assemble: each Kraus term is \<open>|W \<phi>\<rangle>\<langle>W \<phi>|\<close>.\<close>
  have gen: "\<And>is. (\<forall>i \<in> set is. i < ?t) \<Longrightarrow>
      kraus_map_dim n (map ?W is) (\<phi> \<oslash> \<phi>) = foldr (\<lambda>i acc. (?W i *\<^sub>v \<phi>) \<oslash> (?W i *\<^sub>v \<phi>) + acc) is (0\<^sub>m n n)"
  proof -
    fix "is" :: "nat list"
    show "(\<forall>i \<in> set is. i < ?t) \<Longrightarrow>
      kraus_map_dim n (map ?W is) (\<phi> \<oslash> \<phi>) = foldr (\<lambda>i acc. (?W i *\<^sub>v \<phi>) \<oslash> (?W i *\<^sub>v \<phi>) + acc) is (0\<^sub>m n n)"
    proof (induction "is")
      case Nil show ?case by simp
    next
      case (Cons i "is")
      have i: "i < ?t" and rest: "\<forall>i \<in> set is. i < ?t" using Cons.prems by auto
      show ?case
        by (simp only: list.map kraus_map_dim_Cons foldr.simps o_apply conj_outer_prod[OF Wc[OF i] \<phi>d] Cons.IH[OF rest])
    qed
  qed
  have terms: "kraus_map_dim n (recovery_ops n P Us) (\<phi> \<oslash> \<phi>)
        = (?Q *\<^sub>v \<phi>) \<oslash> (?Q *\<^sub>v \<phi>)
          + foldr (\<lambda>i acc. (?W i *\<^sub>v \<phi>) \<oslash> (?W i *\<^sub>v \<phi>) + acc) [0..<?t] (0\<^sub>m n n)"
    unfolding recovery_ops_def kraus_map_dim_Cons conj_outer_prod[OF Qc \<phi>d] using gen[of "[0..<?t]"] by simp
  have "foldr (\<lambda>i acc. (?W i *\<^sub>v \<phi>) \<oslash> (?W i *\<^sub>v \<phi>) + acc) [0..<?t] (0\<^sub>m n n)
        = foldr (\<lambda>i acc. (cnj (a i) * a i) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + acc) [0..<?t] (0\<^sub>m n n)"
  proof (rule foldr_add_mat_cong)
    fix i assume "i \<in> set [0..<?t]"
    hence i: "i < ?t" by simp
    have c2: "\<psi> \<oslash> \<psi> \<in> carrier_mat n n" by (rule outer_prod_carrier[OF \<psi>d \<psi>d])
    have "(?W i *\<^sub>v \<phi>) \<oslash> (?W i *\<^sub>v \<phi>) = (a i \<cdot>\<^sub>v \<psi>) \<oslash> (a i \<cdot>\<^sub>v \<psi>)" unfolding W\<phi>[OF i] ..
    also have "\<dots> = (cnj (a i) * a i) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
    proof (rule eq_matI)
      fix k l assume "k < dim_row ((cnj (a i) * a i) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>))" "l < dim_col ((cnj (a i) * a i) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>))"
      hence k: "k < n" and l: "l < n" using carrier_matD[OF c2] by auto
      have d: "dim_vec (a i \<cdot>\<^sub>v \<psi>) = n" using \<psi>d by simp
      have e1: "((a i \<cdot>\<^sub>v \<psi>) \<oslash> (a i \<cdot>\<^sub>v \<psi>)) $$ (k,l) = (a i \<cdot>\<^sub>v \<psi>) $ k * cnj ((a i \<cdot>\<^sub>v \<psi>) $ l)"
        by (rule outer_prod_index) (simp_all add: \<psi>d k l)
      have e2: "(\<psi> \<oslash> \<psi>) $$ (k,l) = \<psi> $ k * cnj (\<psi> $ l)" by (rule outer_prod_index) (simp_all add: \<psi>d k l)
      have "((cnj (a i) * a i) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)) $$ (k,l) = (cnj (a i) * a i) * (\<psi> \<oslash> \<psi>) $$ (k,l)"
        by (rule index_smult_mat(1)) (simp_all only: carrier_matD[OF c2] k l)
      also have "\<dots> = (cnj (a i) * a i) * (\<psi> $ k * cnj (\<psi> $ l))" unfolding e2 ..
      also have "\<dots> = (a i * \<psi> $ k) * cnj (a i * \<psi> $ l)" by (simp add: algebra_simps)
      also have "\<dots> = (a i \<cdot>\<^sub>v \<psi>) $ k * cnj ((a i \<cdot>\<^sub>v \<psi>) $ l)" using k l \<psi>d by simp
      also have "\<dots> = ((a i \<cdot>\<^sub>v \<psi>) \<oslash> (a i \<cdot>\<^sub>v \<psi>)) $$ (k,l)" by (rule e1[symmetric])
      finally show "((a i \<cdot>\<^sub>v \<psi>) \<oslash> (a i \<cdot>\<^sub>v \<psi>)) $$ (k,l) = ((cnj (a i) * a i) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)) $$ (k,l)" ..
    qed (use \<psi>d carrier_matD[OF c2] carrier_matD[OF outer_prod_carrier[of "a i \<cdot>\<^sub>v \<psi>" n "a i \<cdot>\<^sub>v \<psi>" n]] in auto)
    finally show "(?W i *\<^sub>v \<phi>) \<oslash> (?W i *\<^sub>v \<phi>) = (cnj (a i) * a i) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)" .
  qed
  also have "\<dots> = sum_list (map (\<lambda>i. cnj (a i) * a i) [0..<?t]) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
    by (rule foldr_add_mat_smult_pull) (simp_all add: outer_prod_carrier[OF \<psi>d \<psi>d])
  also have "sum_list (map (\<lambda>i. cnj (a i) * a i) [0..<?t]) = complex_of_real (\<Sum>i < ?t. (cmod (a i))\<^sup>2)"
    by (simp add: sum_list_sum_nth atLeast0LessThan cnj_mult_self_cmod)
  finally show ?thesis
    unfolding terms Q\<phi> outer_prod_zero_vec
    using smult_carrier_mat[OF outer_prod_carrier[OF \<psi>d \<psi>d]] by simp
qed

corollary recovery_single_error:
  assumes S: "recovery_setting n P Us"
      and \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>" and j: "j < length Us"
  shows "kraus_map_dim n (recovery_ops n P Us) ((Us ! j *\<^sub>v \<psi>) \<oslash> (Us ! j *\<^sub>v \<psi>)) = \<psi> \<oslash> \<psi>"
proof -
  let ?t = "length Us"
  let ?a = "\<lambda>i. if i = j then 1 else (0::complex)"
  have Ujd: "\<And>i. i < ?t \<Longrightarrow> dim_vec (Us ! i *\<^sub>v \<psi>) = n"
  proof -
    fix i assume "i < ?t"
    show "dim_vec (Us ! i *\<^sub>v \<psi>) = n" using carrier_matD(1)[OF rec_Uc[OF S \<open>i < ?t\<close>]] by simp
  qed
  have "vec_sum n {i. i < ?t} (\<lambda>i. ?a i \<cdot>\<^sub>v (Us ! i *\<^sub>v \<psi>))
        = vec_sum n {i. i < ?t} (\<lambda>i. if i = j then Us ! i *\<^sub>v \<psi> else 0\<^sub>v n)"
  proof (rule vec_sum_cong)
    fix i assume "i \<in> {i. i < ?t}"
    hence i: "i < ?t" by simp
    show "?a i \<cdot>\<^sub>v (Us ! i *\<^sub>v \<psi>) = (if i = j then Us ! i *\<^sub>v \<psi> else 0\<^sub>v n)"
      using Ujd[OF i] by (cases "i = j") (auto intro!: eq_vecI)
  qed
  also have "\<dots> = Us ! j *\<^sub>v \<psi>" by (rule vec_sum_delta) (simp_all add: j carrier_matD(1)[OF rec_Uc[OF S]])
  finally have \<phi>: "vec_sum n {i. i < ?t} (\<lambda>i. ?a i \<cdot>\<^sub>v (Us ! i *\<^sub>v \<psi>)) = Us ! j *\<^sub>v \<psi>" .
  have c: "(\<Sum>i < ?t. (cmod (?a i))\<^sup>2) = 1"
  proof -
    have "(\<Sum>i < ?t. (cmod (?a i))\<^sup>2) = (\<Sum>i < ?t. if i = j then 1 else (0::real))" by (intro sum.cong refl) simp
    also have "\<dots> = 1" using j by (simp add: sum.delta)
    finally show ?thesis .
  qed
  have "kraus_map_dim n (recovery_ops n P Us) ((Us ! j *\<^sub>v \<psi>) \<oslash> (Us ! j *\<^sub>v \<psi>))
        = complex_of_real (\<Sum>i < ?t. (cmod (?a i))\<^sup>2) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
    using recovery_linear_combination[OF S \<psi>d \<psi>V, where a = ?a] unfolding \<phi> .
  also have "\<dots> = \<psi> \<oslash> \<psi>" unfolding c by (intro eq_matI) auto
  finally show ?thesis .
qed


end
