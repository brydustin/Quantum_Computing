theory QC_Prelims
  imports Day23_ChoiExtremeUCP
begin

section \<open>Small matrix and vector lemmas shared by the gap-closure theories\<close>

text \<open>Index case splits, trace facts, entrywise vector sums, rank-one identities and
rectangular \<open>foldr\<close> sums.  Nothing here is specific to a lecture; the theories
\<open>Day12_Counting_Probability\<close>, \<open>Day18_Positive_Maps\<close>, \<open>Day22_Kraus_Independence\<close>,
\<open>Day28_Horodecki_Peres\<close>, \<open>Day30_BitFlip_Code\<close> and \<open>Day32_Pauli_Expansion\<close> build on it.\<close>

lemma cnj_mult_self_cmod: "cnj z * z = complex_of_real ((cmod z)\<^sup>2)"
  by (metis complex_norm_square mult.commute)

lemma Re_cnj_mult_self: "Re (cnj z * z) = (cmod z)\<^sup>2"
  by (simp add: cnj_mult_self_cmod)

lemma idx4: "k < (4::nat) \<Longrightarrow> k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3"
  by auto

lemma mult_index_lt:
  fixes i j n m :: nat
  assumes "i < n" and "j < m"
  shows "i * m + j < n * m"
proof -
  have "i * m + j < (i + 1) * m" using assms(2) by simp
  also have "\<dots> \<le> n * m" using assms(1) by (intro mult_le_mono1) simp
  finally show ?thesis .
qed

lemma Tr_hermitian_Im_zero:
  assumes Pc: "P \<in> carrier_mat n n" and herm: "hermitian P"
  shows "Im (Tr P) = 0"
proof -
  have "Tr P = (\<Sum>r<n. P $$ (r,r))" using Pc by (simp add: Tr_def)
  moreover have "\<And>r. r < n \<Longrightarrow> Im (P $$ (r,r)) = 0"
  proof -
    fix r assume r: "r < n"
    have eq: "P $$ (r,r) = cnj (P $$ (r,r))"
      using hermitian_index[OF herm, of r r] r Pc by auto
    have "Im (P $$ (r,r)) = Im (cnj (P $$ (r,r)))" using eq by (rule arg_cong)
    also have "\<dots> = - Im (P $$ (r,r))" by simp
    finally show "Im (P $$ (r,r)) = 0" by simp
  qed
  ultimately show ?thesis by simp
qed

lemma Tr_hermitian_real:
  assumes Pc: "P \<in> carrier_mat n n" and herm: "hermitian P"
  shows "Tr P = complex_of_real (Re (Tr P))"
  using Tr_hermitian_Im_zero[OF assms] by (simp add: complex_eq_iff)

lemma Tr_minus:
  fixes x y :: "complex Matrix.mat"
  assumes "dim_row x = dim_row y" and "dim_col x = dim_col y"
  shows "Tr (x - y) = Tr x - Tr y"
proof -
  have "x - y = x + (-1) \<cdot>\<^sub>m y" using assms by (intro eq_matI) auto
  thus ?thesis using Tr_add[of x "(-1) \<cdot>\<^sub>m y"] assms by (simp add: Tr_smult)
qed

text \<open>A positive semidefinite matrix of trace zero is zero (the notes: ``given a non-zero
$P\ge0$, $\Tr(P)\ne0$'').\<close>

lemma psd_Tr_zero_imp_zero:
  assumes Pc: "P \<in> carrier_mat n n" and pos: "psd P" and tr0: "Tr P = 0"
  shows "P = 0\<^sub>m n n"
proof -
  obtain U :: "complex Matrix.mat" and D :: "real list"
    where Uc: "U \<in> carrier_mat n n" and UU: "unitary U" and Dlen: "length D = n"
      and Dnn: "\<forall>i < n. 0 \<le> D ! i"
      and PUD: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF Pc pos] by blast
  let ?D = "diag_mat_of_real D"
  have Dc: "?D \<in> carrier_mat n n" by (rule diag_mat_of_real_carrier[of D, unfolded Dlen])
  have Udc: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by (rule dagger_carrier)
  have UdU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n" using UU Uc by (simp add: unitary_def)
  have UDc: "U * ?D \<in> carrier_mat n n" using Uc Dc by simp
  have "Tr P = Tr ((U * ?D) * (U\<^sup>\<dagger>))" using PUD by simp
  also have "\<dots> = Tr ((U\<^sup>\<dagger>) * (U * ?D))"
    using UDc Udc Dlen Uc by (intro Tr_cyclic) auto
  also have "\<dots> = Tr (((U\<^sup>\<dagger>) * U) * ?D)"
    using assoc_mult_mat[OF Udc Uc Dc] by simp
  also have "\<dots> = Tr ?D" unfolding UdU left_mult_one_mat[OF Dc] ..
  also have "\<dots> = (\<Sum>i<n. complex_of_real (D ! i))"
    using Dlen by (simp add: Tr_def)
  finally have "(\<Sum>i<n. D ! i) = 0" using tr0 by (simp flip: of_real_sum)
  hence D0: "\<And>i. i < n \<Longrightarrow> D ! i = 0"
    using Dnn sum_nonneg_eq_0_iff[of "{..<n}" "\<lambda>i. D ! i"] by auto
  have Dz: "?D = 0\<^sub>m n n"
    by (rule eq_matI) (use Dlen D0 in auto)
  have "P = U * 0\<^sub>m n n * (U\<^sup>\<dagger>)" using PUD Dz by simp
  also have "\<dots> = 0\<^sub>m n n" using Uc Udc by simp
  finally show ?thesis .
qed

lemma smult_smult_mat:
  fixes A :: "complex Matrix.mat"
  shows "a \<cdot>\<^sub>m (b \<cdot>\<^sub>m A) = (a * b) \<cdot>\<^sub>m A"
  by (rule eq_matI) (simp_all add: mult.assoc)

lemma zero_smult_mat_carrier:
  fixes A :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat m k"
  shows "0 \<cdot>\<^sub>m A = 0\<^sub>m m k"
  using assms by (intro eq_matI) auto

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

lemma inner_prod_vec_sum_right:
  assumes ud: "dim_vec u = n"
      and wd: "\<And>J. J \<in> Js \<Longrightarrow> dim_vec (w J) = n"
  shows "\<langle>u | vec_sum n Js w\<rangle> = sum (\<lambda>J. \<langle>u | w J\<rangle>) Js"
proof -
  have "\<langle>u | vec_sum n Js w\<rangle> = (\<Sum>i = 0..<n. cnj (u $ i) * vec_sum n Js w $ i)"
    using inner_prod_expand[OF ud, of "vec_sum n Js w"] by simp
  also have "\<dots> = (\<Sum>i = 0..<n. sum (\<lambda>J. cnj (u $ i) * w J $ i) Js)"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = sum (\<lambda>J. \<Sum>i = 0..<n. cnj (u $ i) * w J $ i) Js"
    by (rule sum.swap)
  also have "\<dots> = sum (\<lambda>J. \<langle>u | w J\<rangle>) Js"
  proof (rule sum.cong[OF refl])
    fix J assume J: "J \<in> Js"
    show "(\<Sum>i = 0..<n. cnj (u $ i) * w J $ i) = \<langle>u | w J\<rangle>"
      using inner_prod_expand[OF ud wd[OF J]] by simp
  qed
  finally show ?thesis .
qed

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

lemma inner_prod_unit_vec_right:
  assumes ud: "dim_vec u = n" and j: "j < n"
  shows "\<langle>u | unit_vec n j\<rangle> = cnj (u $ j)"
proof -
  have "\<langle>u | unit_vec n j\<rangle> = (\<Sum>i = 0..<n. cnj (u $ i) * unit_vec n j $ i)"
    using inner_prod_expand[OF ud, of "unit_vec n j"] by simp
  also have "\<dots> = (\<Sum>i = 0..<n. if i = j then cnj (u $ i) else 0)"
    using j by (intro sum.cong refl) simp
  also have "\<dots> = cnj (u $ j)" using j by simp
  finally show ?thesis .
qed

lemma outer_prod_self_psd:
  assumes "dim_vec v = n"
  shows "psd (v \<oslash> v)"
proof -
  have c: "v \<oslash> v \<in> carrier_mat n n" by (rule outer_prod_carrier[OF assms assms])
  have "v \<oslash> v = outer_sum n [v]"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (outer_sum n [v])" "j < dim_col (outer_sum n [v])"
    hence i: "i < n" and j: "j < n" by simp_all
    show "(v \<oslash> v) $$ (i,j) = outer_sum n [v] $$ (i,j)"
      unfolding outer_sum_singleton_index[OF i j] using i j assms by (simp add: outer_prod_index)
  qed (use carrier_matD[OF c] in auto)
  thus ?thesis using outer_sum_psd[of "[v]" 1 n] assms by simp
qed

text \<open>Conjugating a rank-one matrix: $W|\varphi\rangle\langle\varphi|W^*=|W\varphi\rangle\langle W\varphi|$.\<close>

lemma conj_outer_prod:
  fixes W :: "complex Matrix.mat" and \<phi> :: "complex Matrix.vec"
  assumes Wc: "W \<in> carrier_mat m n" and \<phi>d: "dim_vec \<phi> = n"
  shows "W * (\<phi> \<oslash> \<phi>) * (W\<^sup>\<dagger>) = (W *\<^sub>v \<phi>) \<oslash> (W *\<^sub>v \<phi>)"
proof -
  define M where "M = \<phi> \<oslash> \<phi>"
  define R where "R = (W *\<^sub>v \<phi>) \<oslash> (W *\<^sub>v \<phi>)"
  have Mc: "M \<in> carrier_mat n n" unfolding M_def by (rule outer_prod_carrier[OF \<phi>d \<phi>d])
  have Me: "\<And>k l. k < n \<Longrightarrow> l < n \<Longrightarrow> M $$ (k,l) = \<phi> $ k * cnj (\<phi> $ l)"
    unfolding M_def using \<phi>d by (intro outer_prod_index) auto
  have Wdc: "W\<^sup>\<dagger> \<in> carrier_mat n m" by (rule dagger_carrier[OF Wc])
  have W\<phi>d: "dim_vec (W *\<^sub>v \<phi>) = m" using Wc by simp
  have Rc: "R \<in> carrier_mat m m" unfolding R_def by (rule outer_prod_carrier[OF W\<phi>d W\<phi>d])
  have Re: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> R $$ (i,j) = (W *\<^sub>v \<phi>) $ i * cnj ((W *\<^sub>v \<phi>) $ j)"
    unfolding R_def using W\<phi>d by (intro outer_prod_index) auto
  have WMc: "W * M \<in> carrier_mat m n" using Wc Mc by simp
  have "W * M * (W\<^sup>\<dagger>) = R"
  proof (rule eq_matI)
    fix i j assume "i < dim_row R" "j < dim_col R"
    hence i: "i < m" and j: "j < m" using carrier_matD[OF Rc] by auto
    have inner: "\<And>l. l < n \<Longrightarrow> (W * M) $$ (i,l) = (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * cnj (\<phi> $ l)"
    proof -
      fix l assume l: "l < n"
      have "(W * M) $$ (i,l) = (\<Sum>k<n. W $$ (i,k) * M $$ (k,l))"
        using i l carrier_matD[OF Wc] carrier_matD[OF Mc] by (simp add: scalar_prod_def atLeast0LessThan)
      also have "\<dots> = (\<Sum>k<n. W $$ (i,k) * (\<phi> $ k * cnj (\<phi> $ l)))"
        using l by (intro sum.cong refl) (simp add: Me)
      also have "\<dots> = (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * cnj (\<phi> $ l)"
        by (simp add: sum_distrib_right mult_ac(1))
      finally show "(W * M) $$ (i,l) = (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * cnj (\<phi> $ l)" .
    qed
    have "(W * M * (W\<^sup>\<dagger>)) $$ (i,j) = (\<Sum>l<n. (W * M) $$ (i,l) * cnj (W $$ (j,l)))"
      using i j carrier_matD[OF WMc] carrier_matD[OF Wdc] carrier_matD[OF Wc]
      by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>l<n. (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * (cnj (\<phi> $ l) * cnj (W $$ (j,l))))"
      by (intro sum.cong refl) (simp add: inner mult_ac(1))
    also have "\<dots> = (\<Sum>k<n. W $$ (i,k) * \<phi> $ k) * (\<Sum>l<n. cnj (W $$ (j,l) * \<phi> $ l))"
      by (simp add: sum_distrib_left mult.commute)
    also have "\<dots> = (W *\<^sub>v \<phi>) $ i * cnj ((W *\<^sub>v \<phi>) $ j)"
      using i j carrier_matD[OF Wc] \<phi>d by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = R $$ (i,j)" by (rule Re[OF i j, symmetric])
    finally show "(W * M * (W\<^sup>\<dagger>)) $$ (i,j) = R $$ (i,j)" .
  next
    show "dim_row (W * M * (W\<^sup>\<dagger>)) = dim_row R" using carrier_matD[OF Wc] carrier_matD[OF Rc] by simp
    show "dim_col (W * M * (W\<^sup>\<dagger>)) = dim_col R" using carrier_matD[OF Wdc] carrier_matD[OF Rc] by simp
  qed
  thus ?thesis unfolding M_def R_def .
qed

lemma outer_prod_zero_vec: "(0\<^sub>v n :: complex Matrix.vec) \<oslash> (0\<^sub>v n) = 0\<^sub>m n n"
proof (rule eq_matI)
  have c: "(0\<^sub>v n :: complex Matrix.vec) \<oslash> (0\<^sub>v n) \<in> carrier_mat n n" by (rule outer_prod_carrier) simp_all
  fix i j assume "i < dim_row (0\<^sub>m n n :: complex Matrix.mat)" "j < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
  hence "i < n" "j < n" by simp_all
  thus "((0\<^sub>v n :: complex Matrix.vec) \<oslash> (0\<^sub>v n)) $$ (i,j) = (0\<^sub>m n n :: complex Matrix.mat) $$ (i,j)"
    by (simp add: outer_prod_index)
qed (use carrier_matD[OF outer_prod_carrier[of "0\<^sub>v n :: complex Matrix.vec" n "0\<^sub>v n" n]] in auto)

lemma idx8: "k < (8::nat) \<Longrightarrow> k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3 \<or> k = 4 \<or> k = 5 \<or> k = 6 \<or> k = 7"
  by auto

lemma s8: "{0..<(8::nat)} = {0,1,2,3,4,5,6,7}" by auto

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

end
