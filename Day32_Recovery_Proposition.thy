(*  Title:   Day32_Recovery_Proposition.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 14 November 2011 (Day 32)
*)

theory Day32_Recovery_Proposition
  imports
    Day09_POVMs_Entanglement
    Day22_Minimal_Kraus
    Day32_Phase_Flip_Code
begin

subsection \<open>The general recovery proposition (D32-4, D33-2)\<close>

subsubsection \<open>Matrix sums acting on vectors\<close>

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

text \<open>Under $PU_i^*U_jP=\delta_{ij}P$ the images $P_i=U_iPU_i^*$ of the code projection are mutually
orthogonal projections,
\[ P_iP_j=U_i\,(PU_i^*U_jP)\,U_j^*=\delta_{ij}\,U_iPU_i^*, \]
so $Q=\sum_iP_i$ is a projection.  The recovery operators $I-Q$ and $PU_i^*$ then satisfy
$(I-Q)^*(I-Q)+\sum_i(PU_i^*)^*(PU_i^*)=(I-Q)+Q=I$.\<close>

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


subsection \<open>The code for $Y$ flips\<close>

definition block_op :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "block_op s U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m (2^s)) U) (1\<^sub>m (2^(2-s)))"

lemma block_op_cases:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat 2 2"
  shows "block_op 0 U = Tensor.tensor_mat (Tensor.tensor_mat U (1\<^sub>m 2)) (1\<^sub>m 2)"
    and "block_op 1 U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) U) (1\<^sub>m 2)"
    and "block_op 2 U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) U"
proof -
  have i4: "1\<^sub>m 4 = Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)" by (simp add: tensor_mat_id)
  show "block_op 0 U = Tensor.tensor_mat (Tensor.tensor_mat U (1\<^sub>m 2)) (1\<^sub>m 2)"
    unfolding block_op_def using tensor_one_left[OF U] by (simp add: i4 tensor_mat_is_assoc)
  show "block_op 1 U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) U) (1\<^sub>m 2)" unfolding block_op_def by simp
  have c: "Tensor.tensor_mat (1\<^sub>m 4) U \<in> carrier_mat 8 8" using U by auto
  show "block_op 2 U = Tensor.tensor_mat (Tensor.tensor_mat (1\<^sub>m 2) (1\<^sub>m 2)) U"
    unfolding block_op_def using tensor_one_right[OF c] by (simp add: i4)
qed

lemma block_op_carrier:
  assumes U: "U \<in> carrier_mat 2 2" and s: "s < 3"
  shows "block_op s U \<in> carrier_mat 8 8"
proof -
  have "s = 0 \<or> s = 1 \<or> s = 2" using s by auto
  thus ?thesis using U by (elim disjE) (auto simp: block_op_def)
qed

lemma gram_entry:
  fixes A B :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n k" and B: "B \<in> carrier_mat n k" and a: "a < k" and b: "b < k"
  shows "((A\<^sup>\<dagger>) * B) $$ (a,b) = \<langle>Matrix.col A a | Matrix.col B b\<rangle>"
proof -
  have "((A\<^sup>\<dagger>) * B) $$ (a,b) = (\<Sum>i<n. cnj (A $$ (i,a)) * B $$ (i,b))"
    using A B a b by (simp add: scalar_prod_def dagger_def)
  also have "\<dots> = \<langle>Matrix.col A a | Matrix.col B b\<rangle>"
  proof -
    have dA: "dim_vec (Matrix.col A a) = n" and dB: "dim_vec (Matrix.col B b) = n" using A B by simp_all
    show ?thesis unfolding inner_prod_sum[OF dA dB] atLeast0LessThan
      by (rule sum.cong) (use A B a b in auto)
  qed
  finally show ?thesis .
qed

lemma sandwich_VVd:
  fixes V W :: "complex Matrix.mat"
  assumes V: "V \<in> carrier_mat n k" and W: "W \<in> carrier_mat n n"
  shows "(V * (V\<^sup>\<dagger>)) * W * (V * (V\<^sup>\<dagger>)) = V * ((V\<^sup>\<dagger>) * W * V) * (V\<^sup>\<dagger>)"
proof -
  have Vd: "V\<^sup>\<dagger> \<in> carrier_mat k n" by (rule dagger_carrier[OF V])
  have VdW: "(V\<^sup>\<dagger>) * W \<in> carrier_mat k n" by (rule mult_carrier_mat[OF Vd W])
  have "(V * (V\<^sup>\<dagger>)) * W * (V * (V\<^sup>\<dagger>)) = V * ((V\<^sup>\<dagger>) * W) * (V * (V\<^sup>\<dagger>))"
    by (simp only: assoc_mult_mat[OF V Vd W])
  also have "\<dots> = V * (((V\<^sup>\<dagger>) * W) * (V * (V\<^sup>\<dagger>)))"
    by (rule assoc_mult_mat[OF V VdW mult_carrier_mat[OF V Vd]])
  also have "((V\<^sup>\<dagger>) * W) * (V * (V\<^sup>\<dagger>)) = (((V\<^sup>\<dagger>) * W) * V) * (V\<^sup>\<dagger>)"
    by (rule assoc_mult_mat[OF VdW V Vd, symmetric])
  also have "V * ((((V\<^sup>\<dagger>) * W) * V) * (V\<^sup>\<dagger>)) = (V * (((V\<^sup>\<dagger>) * W) * V)) * (V\<^sup>\<dagger>)"
    by (rule assoc_mult_mat[OF V mult_carrier_mat[OF VdW V] Vd, symmetric])
  finally show ?thesis .
qed

text \<open>Day 32: the code for $Y$ flips.  With $\beta=Y\ket+$ one has $\ket+\perp\beta$,
$Y\ket+=\beta$, $Y\beta=\ket+$, and the code $\ket0\mapsto\ket{+++}$, $\ket1\mapsto\ket{\beta\beta\beta}$
corrects one $Y$ flip exactly as the bit-flip code corrects one $X$ flip.\<close>

definition ket_beta :: "complex Matrix.vec" where "ket_beta = \<i> \<cdot>\<^sub>v ket_minus"

definition y_basis :: "bool \<Rightarrow> complex Matrix.vec" where "y_basis s = (if s then ket_plus else ket_beta)"

lemma ket_beta_dim [simp]: "dim_vec ket_beta = 2" by (simp add: ket_beta_def ket_minus_def)
lemma y_basis_dim [simp]: "dim_vec (y_basis s) = 2" by (simp add: y_basis_def)

lemma ket_beta_index: "ket_beta $ 0 = \<i> / sqrt 2" "ket_beta $ 1 = - \<i> / sqrt 2"
  by (simp_all add: ket_beta_def ket_minus_def)

lemma Y_plus: "Pauli_Y *\<^sub>v ket_plus = ket_beta"
  by (rule eq_vecI) (auto simp: Pauli_Y_def ket_plus_def ket_beta_def ket_minus_def scalar_prod_def less_2_cases_iff)

lemma Y_beta: "Pauli_Y *\<^sub>v ket_beta = ket_plus"
  by (rule eq_vecI) (auto simp: Pauli_Y_def ket_plus_def ket_beta_def ket_minus_def scalar_prod_def less_2_cases_iff)

lemma Y_ub: "Pauli_Y *\<^sub>v y_basis s = y_basis (\<not> s)"
  by (cases s) (simp_all add: y_basis_def Y_plus Y_beta)

lemma inner2: "dim_vec u = 2 \<Longrightarrow> dim_vec v = 2 \<Longrightarrow> \<langle>u|v\<rangle> = cnj (u $ 0) * v $ 0 + cnj (u $ 1) * v $ 1"
  by (subst inner_prod_sum[of _ 2]) (simp_all add: numeral_2_eq_2)

text \<open>\[ \beta=Y\ket+=\frac{i}{\sqrt2}\begin{pmatrix}1\\-1\end{pmatrix},\qquad Y\beta=\ket+,\qquad
   \braket{+}{\beta}=0, \]
so $\{\ket+,\beta\}$ is an orthonormal basis that $Y$ swaps, as $X$ swaps $\ket0$ and $\ket1$.\<close>

lemma y_basis_inner: "\<langle>y_basis s | y_basis t\<rangle> = (if s = t then 1 else 0)"
proof -
  have r: "cnj (complex_of_real (sqrt 2)) = complex_of_real (sqrt 2)" by simp
  have s2: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
    by (simp only: of_real_mult[symmetric]) simp
  show ?thesis unfolding inner2[OF y_basis_dim y_basis_dim]
    by (cases s; cases t) (simp_all add: y_basis_def ket_plus_index_0 ket_plus_index_1 ket_beta_index ket_plus_index_1[unfolded One_nat_def] ket_beta_index(2)[unfolded One_nat_def] field_simps s2)
qed

theorem ket_plus_beta_orth: "\<langle>ket_plus | ket_beta\<rangle> = 0"
  using y_basis_inner[of True False] by (simp add: y_basis_def)

subsubsection \<open>Codes with orthogonal error images\<close>

text \<open>For a code with orthonormal basis $v_1,\dots,v_k$ (the columns of $V$, projection $VV^*$)
and unitary errors whose images of the basis are mutually orthogonal, the recovery proposition
gives one CPTP map correcting each error on every code state $Vc$.\<close>

lemma proj_of_orthonormal:
  assumes orth: "orthonormal_list n vs"
  defines "V \<equiv> mat_of_cols n vs"
  shows "projection n (V * (V\<^sup>\<dagger>))"
proof -
  let ?k = "length vs"
  have Vc: "V \<in> carrier_mat n ?k" unfolding V_def by simp
  have Vdc: "V\<^sup>\<dagger> \<in> carrier_mat ?k n" by (rule dagger_carrier[OF Vc])
  have VdV: "(V\<^sup>\<dagger>) * V = 1\<^sub>m ?k" unfolding V_def by (rule cols_mat_dagger_left[OF orth])
  have Pc: "V * (V\<^sup>\<dagger>) \<in> carrier_mat n n" using Vc Vdc by simp
  have "(V * (V\<^sup>\<dagger>))\<^sup>\<dagger> = ((V\<^sup>\<dagger>)\<^sup>\<dagger>) * (V\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Vc Vdc in simp)
  hence h: "(V * (V\<^sup>\<dagger>))\<^sup>\<dagger> = V * (V\<^sup>\<dagger>)" unfolding dagger_of_dagger_is_id .
  have "V * (V\<^sup>\<dagger>) * (V * (V\<^sup>\<dagger>)) = V * (((V\<^sup>\<dagger>) * V) * (V\<^sup>\<dagger>))"
    by (simp only: assoc_mult_mat[OF Vc Vdc mult_carrier_mat[OF Vc Vdc]] assoc_mult_mat[OF Vdc Vc Vdc])
  also have "\<dots> = V * (V\<^sup>\<dagger>)" unfolding VdV by (simp only: left_mult_one_mat[OF Vdc])
  finally show ?thesis unfolding projection_def hermitian_def using Pc h by simp
qed

lemma proj_fixes_code:
  assumes orth: "orthonormal_list n vs" and c: "dim_vec c = length vs"
  defines "V \<equiv> mat_of_cols n vs"
  shows "(V * (V\<^sup>\<dagger>)) *\<^sub>v (V *\<^sub>v c) = V *\<^sub>v c"
proof -
  let ?k = "length vs"
  have Vc: "V \<in> carrier_mat n ?k" unfolding V_def by simp
  have Vdc: "V\<^sup>\<dagger> \<in> carrier_mat ?k n" by (rule dagger_carrier[OF Vc])
  have VdV: "(V\<^sup>\<dagger>) * V = 1\<^sub>m ?k" unfolding V_def by (rule cols_mat_dagger_left[OF orth])
  have cc: "c \<in> carrier_vec ?k" by (rule carrier_vecI[OF c])
  have "(V * (V\<^sup>\<dagger>)) *\<^sub>v (V *\<^sub>v c) = V *\<^sub>v ((V\<^sup>\<dagger>) *\<^sub>v (V *\<^sub>v c))"
    by (rule assoc_mult_mat_vec[OF Vc Vdc mult_mat_vec_carrier[OF Vc cc]])
  also have "(V\<^sup>\<dagger>) *\<^sub>v (V *\<^sub>v c) = c"
    using assoc_mult_mat_vec[OF Vdc Vc cc] unfolding VdV using cc by simp
  finally show ?thesis .
qed

theorem orthogonal_images_recovery:
  assumes orth: "orthonormal_list n vs"
      and Us: "\<forall>U \<in> set Us. U \<in> carrier_mat n n \<and> unitary U"
      and img: "\<forall>i < length Us. \<forall>j < length Us. i \<noteq> j \<longrightarrow>
                  (\<forall>a < length vs. \<forall>b < length vs. \<langle>Us ! i *\<^sub>v vs ! a | Us ! j *\<^sub>v vs ! b\<rangle> = 0)"
  defines "V \<equiv> mat_of_cols n vs"
  shows "recovery_setting n (V * (V\<^sup>\<dagger>)) Us"
proof (rule recovery_setting_unitaries[OF _ Us])
  let ?k = "length vs" and ?P = "V * (V\<^sup>\<dagger>)"
  show "projection n ?P" unfolding V_def by (rule proj_of_orthonormal[OF orth])
  have Vc: "V \<in> carrier_mat n ?k" unfolding V_def by simp
  have Vdc: "V\<^sup>\<dagger> \<in> carrier_mat ?k n" by (rule dagger_carrier[OF Vc])
  have vsd: "\<And>a. a < ?k \<Longrightarrow> vs ! a \<in> carrier_vec n"
    using orth unfolding orthonormal_list_def by (auto intro: carrier_vecI)
  show "\<forall>i < length Us. \<forall>j < length Us. i \<noteq> j \<longrightarrow> ?P * (((Us ! i)\<^sup>\<dagger>) * Us ! j) * ?P = 0\<^sub>m n n"
  proof (intro allI impI)
    fix i j assume i: "i < length Us" and j: "j < length Us" and ij: "i \<noteq> j"
    have Uic: "Us ! i \<in> carrier_mat n n" and Ujc: "Us ! j \<in> carrier_mat n n" using Us i j nth_mem by blast+
    have Uidc: "(Us ! i)\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Uic])
    have UVi: "Us ! i * V \<in> carrier_mat n ?k" and UVj: "Us ! j * V \<in> carrier_mat n ?k" using Uic Ujc Vc by auto
    have G0: "((Us ! i * V)\<^sup>\<dagger>) * (Us ! j * V) = 0\<^sub>m ?k ?k"
    proof (rule eq_matI)
      fix a b assume "a < dim_row (0\<^sub>m ?k ?k :: complex Matrix.mat)" "b < dim_col (0\<^sub>m ?k ?k :: complex Matrix.mat)"
      hence a: "a < ?k" and b: "b < ?k" by simp_all
      have ca: "Matrix.col (Us ! i * V) a = Us ! i *\<^sub>v vs ! a"
        using col_mult2[OF Uic Vc a] col_mat_of_cols[OF a vsd[OF a]] unfolding V_def by simp
      have cb: "Matrix.col (Us ! j * V) b = Us ! j *\<^sub>v vs ! b"
        using col_mult2[OF Ujc Vc b] col_mat_of_cols[OF b vsd[OF b]] unfolding V_def by simp
      show "(((Us ! i * V)\<^sup>\<dagger>) * (Us ! j * V)) $$ (a,b) = (0\<^sub>m ?k ?k :: complex Matrix.mat) $$ (a,b)"
        unfolding gram_entry[OF UVi UVj a b] ca cb using img i j ij a b by simp
    qed (use UVi UVj in \<open>simp_all add: V_def\<close>)
    have "(V\<^sup>\<dagger>) * ((Us ! i)\<^sup>\<dagger> * Us ! j) * V = ((Us ! i * V)\<^sup>\<dagger>) * (Us ! j * V)"
    proof -
      have "(Us ! i * V)\<^sup>\<dagger> = (V\<^sup>\<dagger>) * ((Us ! i)\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Uic Vc in simp)
      thus ?thesis
        by (simp add: assoc_mult_mat[OF Vdc Uidc mult_carrier_mat[OF Ujc Vc]]
            assoc_mult_mat[OF Vdc mult_carrier_mat[OF Uidc Ujc] Vc] assoc_mult_mat[OF Uidc Ujc Vc])
    qed
    hence inner0: "(V\<^sup>\<dagger>) * ((Us ! i)\<^sup>\<dagger> * Us ! j) * V = 0\<^sub>m ?k ?k" unfolding G0 .
    have W: "(Us ! i)\<^sup>\<dagger> * Us ! j \<in> carrier_mat n n" using Uidc Ujc by simp
    have "?P * ((Us ! i)\<^sup>\<dagger> * Us ! j) * ?P = V * ((V\<^sup>\<dagger>) * ((Us ! i)\<^sup>\<dagger> * Us ! j) * V) * (V\<^sup>\<dagger>)"
      by (rule sandwich_VVd[OF Vc W])
    also have "\<dots> = 0\<^sub>m n n" unfolding inner0 using Vc Vdc by simp
    finally show "?P * (((Us ! i)\<^sup>\<dagger>) * Us ! j) * ?P = 0\<^sub>m n n" .
  qed
qed

corollary orthogonal_images_correct:
  assumes orth: "orthonormal_list n vs"
      and Us: "\<forall>U \<in> set Us. U \<in> carrier_mat n n \<and> unitary U"
      and img: "\<forall>i < length Us. \<forall>j < length Us. i \<noteq> j \<longrightarrow>
                  (\<forall>a < length vs. \<forall>b < length vs. \<langle>Us ! i *\<^sub>v vs ! a | Us ! j *\<^sub>v vs ! b\<rangle> = 0)"
  shows "\<exists>Rs. kraus_operators n n Rs \<and>
           (\<forall>(c :: complex Matrix.vec) j. dim_vec c = length vs \<longrightarrow> j < length Us \<longrightarrow>
              kraus_map_dim n Rs (Us ! j * ((mat_of_cols n vs *\<^sub>v c) \<oslash> (mat_of_cols n vs *\<^sub>v c)) * ((Us ! j)\<^sup>\<dagger>))
              = (mat_of_cols n vs *\<^sub>v c) \<oslash> (mat_of_cols n vs *\<^sub>v c))"
proof -
  let ?V = "mat_of_cols n vs"
  have S: "recovery_setting n (?V * (?V\<^sup>\<dagger>)) Us" by (rule orthogonal_images_recovery[OF orth Us img])
  show ?thesis
  proof (intro exI conjI allI impI)
    show "kraus_operators n n (Day32_Recovery_Proposition.recovery_ops n (?V * (?V\<^sup>\<dagger>)) Us)"
      by (rule recovery_ops_kraus_operators[OF S])
    fix c :: "complex Matrix.vec" and j assume c: "dim_vec c = length vs" and j: "j < length Us"
    have \<psi>d: "dim_vec (?V *\<^sub>v c) = n" by simp
    have Ujc: "Us ! j \<in> carrier_mat n n" using Us j nth_mem by blast
    show "kraus_map_dim n (Day32_Recovery_Proposition.recovery_ops n (?V * (?V\<^sup>\<dagger>)) Us)
            (Us ! j * ((?V *\<^sub>v c) \<oslash> (?V *\<^sub>v c)) * ((Us ! j)\<^sup>\<dagger>)) = (?V *\<^sub>v c) \<oslash> (?V *\<^sub>v c)"
      unfolding conj_outer_prod[OF Ujc \<psi>d]
      by (rule recovery_single_error[OF S \<psi>d proj_fixes_code[OF orth c] j])
  qed
qed

subsubsection \<open>The $Y$-flip code\<close>

definition y_word :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> complex Matrix.vec" where
  "y_word a b c = tensor_vec (tensor_vec (y_basis a) (y_basis b)) (y_basis c)"

definition y_errors :: "complex Matrix.mat list" where
  "y_errors = [1\<^sub>m 8, block_op 0 Pauli_Y, block_op 1 Pauli_Y, block_op 2 Pauli_Y]"

definition y_codewords :: "complex Matrix.vec list" where
  "y_codewords = [y_word True True True, y_word False False False]"

lemma y_word_dim [simp]: "dim_vec (y_word a b c) = 8"
  unfolding y_word_def by (simp add: tensor_vec_dim)

text \<open>The code $\ket0\mapsto\ket{{+}{+}{+}}$, $\ket1\mapsto\ket{\beta\beta\beta}$ is the bit-flip code in the basis
$\{\ket+,\beta\}$.  The eight products of $\ket+$ and $\beta$ are orthonormal and $Y$ on qubit $s$
swaps the factor $s$, so the images of the code under $I,Y_0,Y_1,Y_2$ are mutually orthogonal.\<close>

lemma y_word_inner: "\<langle>y_word a b c | y_word a' b' c'\<rangle> = (if a = a' \<and> b = b' \<and> c = c' then 1 else 0)"
proof -
  have "\<langle>y_word a b c | y_word a' b' c'\<rangle> = \<langle>tensor_vec (y_basis a) (y_basis b) | tensor_vec (y_basis a') (y_basis b')\<rangle> * \<langle>y_basis c | y_basis c'\<rangle>"
    unfolding y_word_def by (rule tensor_inner_prod) (simp_all add: tensor_vec_dim)
  also have "\<langle>tensor_vec (y_basis a) (y_basis b) | tensor_vec (y_basis a') (y_basis b')\<rangle> = \<langle>y_basis a | y_basis a'\<rangle> * \<langle>y_basis b | y_basis b'\<rangle>"
    by (rule tensor_inner_prod) simp_all
  finally show ?thesis by (simp add: y_basis_inner)
qed

lemma y_actions:
  "block_op 0 Pauli_Y *\<^sub>v y_word a b c = y_word (\<not> a) b c"
  "block_op 1 Pauli_Y *\<^sub>v y_word a b c = y_word a (\<not> b) c"
  "block_op 2 Pauli_Y *\<^sub>v y_word a b c = y_word a b (\<not> c)"
proof -
  have Y: "Pauli_Y \<in> carrier_mat 2 2" by simp
  have I: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp
  have ab: "dim_vec (tensor_vec (y_basis a) (y_basis b)) = 4" by (simp add: tensor_vec_dim)
  have c4: "\<And>A B. A \<in> carrier_mat 2 2 \<Longrightarrow> B \<in> carrier_mat 2 2 \<Longrightarrow> Tensor.tensor_mat A B \<in> carrier_mat 4 4"
    by auto
  have one: "\<And>v :: complex Matrix.vec. dim_vec v = 2 \<Longrightarrow> 1\<^sub>m 2 *\<^sub>v v = v" by (rule one_mult_mat_vec, rule carrier_vecI)
  show "block_op 0 Pauli_Y *\<^sub>v y_word a b c = y_word (\<not> a) b c"
    unfolding block_op_cases[OF Y] y_word_def tensor_mat_vec_mult[OF c4[OF Y I] I ab y_basis_dim]
      tensor_mat_vec_mult[OF Y I y_basis_dim y_basis_dim] by (simp add: one Y_ub)
  show "block_op 1 Pauli_Y *\<^sub>v y_word a b c = y_word a (\<not> b) c"
    unfolding block_op_cases[OF Y] y_word_def tensor_mat_vec_mult[OF c4[OF I Y] I ab y_basis_dim]
      tensor_mat_vec_mult[OF I Y y_basis_dim y_basis_dim] by (simp add: one Y_ub)
  show "block_op 2 Pauli_Y *\<^sub>v y_word a b c = y_word a b (\<not> c)"
    unfolding block_op_cases[OF Y] y_word_def tensor_mat_vec_mult[OF c4[OF I I] Y ab y_basis_dim]
      tensor_mat_vec_mult[OF I I y_basis_dim y_basis_dim] by (simp add: one Y_ub)
qed

lemma y_codewords_orthonormal: "orthonormal_list 8 y_codewords"
  unfolding orthonormal_list_def y_codewords_def
  by (auto simp: y_word_inner less_Suc_eq)

lemma y_errors_unitary: "\<forall>U \<in> set y_errors. U \<in> carrier_mat 8 8 \<and> unitary U"
  unfolding y_errors_def using block_op_carrier[OF Pauli_Y_carrier, of 0] block_op_carrier[OF Pauli_Y_carrier, of 1]
    block_op_carrier[OF Pauli_Y_carrier, of 2]
  by (auto simp: block_op_def Pauli_Y_unitary simp del: One_nat_def)

lemma y_images_orthogonal:
  "\<forall>i < length y_errors. \<forall>j < length y_errors. i \<noteq> j \<longrightarrow>
     (\<forall>a < length y_codewords. \<forall>b < length y_codewords.
        \<langle>y_errors ! i *\<^sub>v y_codewords ! a | y_errors ! j *\<^sub>v y_codewords ! b\<rangle> = 0)"
proof -
  have I: "\<And>a b c. 1\<^sub>m 8 *\<^sub>v y_word a b c = y_word a b c" by (rule one_mult_mat_vec, rule carrier_vecI, simp)
  show ?thesis unfolding y_errors_def y_codewords_def
    by (auto simp: less_Suc_eq I y_actions y_actions(2)[unfolded One_nat_def] y_word_inner)
qed

text \<open>D32-2: one CPTP map corrects every single $Y$ flip on every state $a\ket{+++}+b\ket{\beta\beta\beta}$.\<close>

theorem y_code_corrects:
  "\<exists>Rs. kraus_operators 8 8 Rs \<and>
     (\<forall>c j. dim_vec c = 2 \<longrightarrow> j < 4 \<longrightarrow>
        kraus_map_dim 8 Rs (y_errors ! j * ((mat_of_cols 8 y_codewords *\<^sub>v c) \<oslash> (mat_of_cols 8 y_codewords *\<^sub>v c)) * ((y_errors ! j)\<^sup>\<dagger>))
        = (mat_of_cols 8 y_codewords *\<^sub>v c) \<oslash> (mat_of_cols 8 y_codewords *\<^sub>v c))"
proof -
  have l: "length y_codewords = 2" "length y_errors = 4" by (simp_all add: y_codewords_def y_errors_def)
  show ?thesis using orthogonal_images_correct[OF y_codewords_orthonormal y_errors_unitary y_images_orthogonal]
    unfolding l .
qed

end
