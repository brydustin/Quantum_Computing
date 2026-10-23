theory Day32_Y_Code
  imports Day33_Shor_Code
begin

section \<open>Day 32: the code for $Y$ flips\<close>

text \<open>Day 32: the code for $Y$ flips.  With $\beta=Y\ket+$ one has $\ket+\perp\beta$,
$Y\ket+=\beta$, $Y\beta=\ket+$, and the code $\ket0\mapsto\ket{+++}$, $\ket1\mapsto\ket{\beta\beta\beta}$
corrects one $Y$ flip exactly as the bit-flip code corrects one $X$ flip.\<close>

definition ket_beta :: "complex Matrix.vec" where "ket_beta = \<i> \<cdot>\<^sub>v ket_minus"

definition ub :: "bool \<Rightarrow> complex Matrix.vec" where "ub s = (if s then ket_plus else ket_beta)"

lemma ket_beta_dim [simp]: "dim_vec ket_beta = 2" by (simp add: ket_beta_def ket_minus_def)
lemma ub_dim [simp]: "dim_vec (ub s) = 2" by (simp add: ub_def)

lemma ket_beta_index: "ket_beta $ 0 = \<i> / sqrt 2" "ket_beta $ 1 = - \<i> / sqrt 2"
  by (simp_all add: ket_beta_def ket_minus_def)

lemma Y_plus: "Pauli_Y *\<^sub>v ket_plus = ket_beta"
  by (rule eq_vecI) (auto simp: Pauli_Y_def ket_plus_def ket_beta_def ket_minus_def scalar_prod_def less_2_cases_iff)

lemma Y_beta: "Pauli_Y *\<^sub>v ket_beta = ket_plus"
  by (rule eq_vecI) (auto simp: Pauli_Y_def ket_plus_def ket_beta_def ket_minus_def scalar_prod_def less_2_cases_iff)

lemma Y_ub: "Pauli_Y *\<^sub>v ub s = ub (\<not> s)"
  by (cases s) (simp_all add: ub_def Y_plus Y_beta)

lemma inner2: "dim_vec u = 2 \<Longrightarrow> dim_vec v = 2 \<Longrightarrow> \<langle>u|v\<rangle> = cnj (u $ 0) * v $ 0 + cnj (u $ 1) * v $ 1"
  by (subst inner_prod_sum[of _ 2]) (simp_all add: numeral_2_eq_2)

text \<open>\[ \beta=Y\ket+=\frac{i}{\sqrt2}\begin{pmatrix}1\\-1\end{pmatrix},\qquad Y\beta=\ket+,\qquad
   \braket{+}{\beta}=0, \]
so $\{\ket+,\beta\}$ is an orthonormal basis that $Y$ swaps, as $X$ swaps $\ket0$ and $\ket1$.\<close>

lemma ub_inner: "\<langle>ub s | ub t\<rangle> = (if s = t then 1 else 0)"
proof -
  have r: "cnj (complex_of_real (sqrt 2)) = complex_of_real (sqrt 2)" by simp
  have s2: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
    by (simp only: of_real_mult[symmetric]) simp
  show ?thesis unfolding inner2[OF ub_dim ub_dim]
    by (cases s; cases t) (simp_all add: ub_def ket_plus_index_0 ket_plus_index_1 ket_beta_index ket_plus_index_1[unfolded One_nat_def] ket_beta_index(2)[unfolded One_nat_def] field_simps s2)
qed

theorem ket_plus_beta_orth: "\<langle>ket_plus | ket_beta\<rangle> = 0"
  using ub_inner[of True False] by (simp add: ub_def)

subsection \<open>Codes with orthogonal error images\<close>

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

subsection \<open>The $Y$-flip code\<close>

definition tv2 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> complex Matrix.vec" where
  "tv2 a b c = tensor_vec (tensor_vec (ub a) (ub b)) (ub c)"

definition y_errors :: "complex Matrix.mat list" where
  "y_errors = [1\<^sub>m 8, bop 0 Pauli_Y, bop 1 Pauli_Y, bop 2 Pauli_Y]"

definition y_codewords :: "complex Matrix.vec list" where
  "y_codewords = [tv2 True True True, tv2 False False False]"

lemma tv2_dim [simp]: "dim_vec (tv2 a b c) = 8"
  unfolding tv2_def by (simp add: tensor_vec_dim)

text \<open>The code $\ket0\mapsto\ket{{+}{+}{+}}$, $\ket1\mapsto\ket{\beta\beta\beta}$ is the bit-flip code in the basis
$\{\ket+,\beta\}$.  The eight products of $\ket+$ and $\beta$ are orthonormal and $Y$ on qubit $s$
swaps the factor $s$, so the images of the code under $I,Y_0,Y_1,Y_2$ are mutually orthogonal.\<close>

lemma tv2_inner: "\<langle>tv2 a b c | tv2 a' b' c'\<rangle> = (if a = a' \<and> b = b' \<and> c = c' then 1 else 0)"
proof -
  have "\<langle>tv2 a b c | tv2 a' b' c'\<rangle> = \<langle>tensor_vec (ub a) (ub b) | tensor_vec (ub a') (ub b')\<rangle> * \<langle>ub c | ub c'\<rangle>"
    unfolding tv2_def by (rule tensor_inner_prod) (simp_all add: tensor_vec_dim)
  also have "\<langle>tensor_vec (ub a) (ub b) | tensor_vec (ub a') (ub b')\<rangle> = \<langle>ub a | ub a'\<rangle> * \<langle>ub b | ub b'\<rangle>"
    by (rule tensor_inner_prod) simp_all
  finally show ?thesis by (simp add: ub_inner)
qed

lemma y_actions:
  "bop 0 Pauli_Y *\<^sub>v tv2 a b c = tv2 (\<not> a) b c"
  "bop 1 Pauli_Y *\<^sub>v tv2 a b c = tv2 a (\<not> b) c"
  "bop 2 Pauli_Y *\<^sub>v tv2 a b c = tv2 a b (\<not> c)"
proof -
  have Y: "Pauli_Y \<in> carrier_mat 2 2" by simp
  have I: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp
  have ab: "dim_vec (tensor_vec (ub a) (ub b)) = 4" by (simp add: tensor_vec_dim)
  have c4: "\<And>A B. A \<in> carrier_mat 2 2 \<Longrightarrow> B \<in> carrier_mat 2 2 \<Longrightarrow> Tensor.tensor_mat A B \<in> carrier_mat 4 4"
    by auto
  have one: "\<And>v :: complex Matrix.vec. dim_vec v = 2 \<Longrightarrow> 1\<^sub>m 2 *\<^sub>v v = v" by (rule one_mult_mat_vec, rule carrier_vecI)
  show "bop 0 Pauli_Y *\<^sub>v tv2 a b c = tv2 (\<not> a) b c"
    unfolding bop_cases[OF Y] tv2_def tensor_mat_vec_mult[OF c4[OF Y I] I ab ub_dim]
      tensor_mat_vec_mult[OF Y I ub_dim ub_dim] by (simp add: one Y_ub)
  show "bop 1 Pauli_Y *\<^sub>v tv2 a b c = tv2 a (\<not> b) c"
    unfolding bop_cases[OF Y] tv2_def tensor_mat_vec_mult[OF c4[OF I Y] I ab ub_dim]
      tensor_mat_vec_mult[OF I Y ub_dim ub_dim] by (simp add: one Y_ub)
  show "bop 2 Pauli_Y *\<^sub>v tv2 a b c = tv2 a b (\<not> c)"
    unfolding bop_cases[OF Y] tv2_def tensor_mat_vec_mult[OF c4[OF I I] Y ab ub_dim]
      tensor_mat_vec_mult[OF I I ub_dim ub_dim] by (simp add: one Y_ub)
qed

lemma y_codewords_orthonormal: "orthonormal_list 8 y_codewords"
  unfolding orthonormal_list_def y_codewords_def
  by (auto simp: tv2_inner less_Suc_eq)

lemma y_errors_unitary: "\<forall>U \<in> set y_errors. U \<in> carrier_mat 8 8 \<and> unitary U"
  unfolding y_errors_def using bop_carrier[OF Pauli_Y_carrier, of 0] bop_carrier[OF Pauli_Y_carrier, of 1]
    bop_carrier[OF Pauli_Y_carrier, of 2]
  by (auto simp: bop_def Pauli_Y_unitary simp del: One_nat_def)

lemma y_images_orthogonal:
  "\<forall>i < length y_errors. \<forall>j < length y_errors. i \<noteq> j \<longrightarrow>
     (\<forall>a < length y_codewords. \<forall>b < length y_codewords.
        \<langle>y_errors ! i *\<^sub>v y_codewords ! a | y_errors ! j *\<^sub>v y_codewords ! b\<rangle> = 0)"
proof -
  have I: "\<And>a b c. 1\<^sub>m 8 *\<^sub>v tv2 a b c = tv2 a b c" by (rule one_mult_mat_vec, rule carrier_vecI, simp)
  show ?thesis unfolding y_errors_def y_codewords_def
    by (auto simp: less_Suc_eq I y_actions y_actions(2)[unfolded One_nat_def] tv2_inner)
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
