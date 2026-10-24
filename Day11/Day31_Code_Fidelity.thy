theory Day31_Code_Fidelity
  imports Day30_BitFlip_Code
begin

section \<open>Day 31: the three-qubit code against independent bit flips\<close>

text \<open>Day 31: the three-qubit code against independent bit flips.  Each qubit flips with
probability $p$, so $E(Y)=(1-p)^3Y+p(1-p)^2\sum_iX_iYX_i+p^2(1-p)\sum_{i<j}X_iX_jYX_jX_i+p^3\,X_1X_2X_3YX_3X_2X_1$.
On an encoded state the recovery $R$ leaves
$((1-p)^3+3p(1-p)^2)\ketbra{\tilde\psi}{\tilde\psi}+(3p^2(1-p)+p^3)\ketbra{X_1X_2X_3\tilde\psi}{X_1X_2X_3\tilde\psi}$.
The notes state this formula for a general $Y$; it holds for $Y$ supported on the code space
(for $Y=\ketbra{100}{100}$ and $p=0$ one gets $R(Y)=\ketbra{000}{000}\neq Y$).\<close>

definition three_bit_channel :: "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "three_bit_channel p M =
     complex_of_real ((1 - p)^3) \<cdot>\<^sub>m M
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m (X\<^sub>1 * M * (X\<^sub>1\<^sup>\<dagger>))
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m (X\<^sub>2 * M * (X\<^sub>2\<^sup>\<dagger>))
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m (X\<^sub>3 * M * (X\<^sub>3\<^sup>\<dagger>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>2 * X\<^sub>3) * M * ((X\<^sub>2 * X\<^sub>3)\<^sup>\<dagger>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>1 * X\<^sub>3) * M * ((X\<^sub>1 * X\<^sub>3)\<^sup>\<dagger>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>1 * X\<^sub>2) * M * ((X\<^sub>1 * X\<^sub>2)\<^sup>\<dagger>))
     + complex_of_real (p^3) \<cdot>\<^sub>m ((X\<^sub>1 * X\<^sub>2 * X\<^sub>3) * M * ((X\<^sub>1 * X\<^sub>2 * X\<^sub>3)\<^sup>\<dagger>))"

definition swap2 :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "swap2 x = Matrix.vec 2 (\<lambda>i. x $ (1 - i))"

lemma swap2_dim [simp]: "dim_vec (swap2 x) = 2" by (simp add: swap2_def)

lemma flips_on_codeword:
  assumes x: "dim_vec x = 2"
  defines "\<psi> \<equiv> encode_mat *\<^sub>v x" and "\<phi> \<equiv> encode_mat *\<^sub>v swap2 x"
  shows "(X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = \<phi>"
    and "(X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v \<phi>"
    and "(X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>2 *\<^sub>v \<phi>"
    and "(X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi> = X\<^sub>3 *\<^sub>v \<phi>"
proof -
  have \<psi>c: "\<psi> \<in> carrier_vec 8" unfolding \<psi>_def by (rule carrier_vecI) simp
  have c: "\<And>b. flip_bit_mat b \<in> carrier_mat 8 8" by simp
  have ev: "\<And>u. dim_vec u = 2 \<Longrightarrow> \<forall>i < 8. (encode_mat *\<^sub>v u) $ i = (if i = 0 then u $ 0 else if i = 7 then u $ 1 else 0)"
    using encode_mat_mult_vec by blast
  have fl: "\<And>b v i. b < 3 \<Longrightarrow> dim_vec v = 8 \<Longrightarrow> i < 8 \<Longrightarrow>
      (flip_bit_mat b *\<^sub>v v) $ i = v $ (if i div 2^b mod 2 = 0 then i + 2^b else i - 2^b)"
    by (rule flip_bit_mat_mult_vec)
  have sw: "swap2 x $ 0 = x $ 1" "swap2 x $ 1 = x $ 0" "swap2 x $ Suc 0 = x $ 0" by (simp_all add: swap2_def)
  show "(X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = \<phi>"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec \<phi>" hence i: "i < 8" unfolding \<phi>_def by simp
    have "(X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>))"
      by (simp only: assoc_mult_mat_vec[OF mult_carrier_mat[OF c c] c \<psi>c] assoc_mult_mat_vec[OF c c mult_mat_vec_carrier[OF c \<psi>c]])
    hence "((X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>))) $ i" by simp
    thus "((X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi>) $ i = \<phi> $ i"
      using idx8[OF i] x unfolding \<psi>_def \<phi>_def
      by (elim disjE) (simp_all add: fl ev sw del: index_mult_mat_vec)
  qed (simp add: \<phi>_def)
  show "(X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v \<phi>"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (X\<^sub>1 *\<^sub>v \<phi>)" hence i: "i < 8" by simp
    have "(X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>)" by (rule assoc_mult_mat_vec[OF c c \<psi>c])
    hence "((X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>)) $ i" by simp
    thus "((X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>1 *\<^sub>v \<phi>) $ i"
      using idx8[OF i] x unfolding \<psi>_def \<phi>_def by (elim disjE) (simp_all add: fl ev sw del: index_mult_mat_vec)
  qed simp
  show "(X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>2 *\<^sub>v \<phi>"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (X\<^sub>2 *\<^sub>v \<phi>)" hence i: "i < 8" by simp
    have "(X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>)" by (rule assoc_mult_mat_vec[OF c c \<psi>c])
    hence "((X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>1 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>)) $ i" by simp
    thus "((X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>2 *\<^sub>v \<phi>) $ i"
      using idx8[OF i] x unfolding \<psi>_def \<phi>_def by (elim disjE) (simp_all add: fl ev sw del: index_mult_mat_vec)
  qed simp
  show "(X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi> = X\<^sub>3 *\<^sub>v \<phi>"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (X\<^sub>3 *\<^sub>v \<phi>)" hence i: "i < 8" by simp
    have "(X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>)" by (rule assoc_mult_mat_vec[OF c c \<psi>c])
    hence "((X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi>) $ i = (X\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>)) $ i" by simp
    thus "((X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi>) $ i = (X\<^sub>3 *\<^sub>v \<phi>) $ i"
      using idx8[OF i] x unfolding \<psi>_def \<phi>_def by (elim disjE) (simp_all add: fl ev sw del: index_mult_mat_vec)
  qed simp
qed

subsection \<open>Errors followed by recovery\<close>

lemma bitflip_recovery_ops_carrier': "\<forall>W \<in> set bitflip_recovery_ops. W \<in> carrier_mat 8 8"
  using bitflip_recovery_ops_kraus by (simp add: kraus_operators_altdef)

lemma bitflip_recovery_map_add: "A \<in> carrier_mat 8 8 \<Longrightarrow> B \<in> carrier_mat 8 8 \<Longrightarrow> bitflip_recovery_map (A + B) = bitflip_recovery_map A + bitflip_recovery_map B"
  unfolding bitflip_recovery_map_def by (rule kraus_map_dim_add[OF _ _ bitflip_recovery_ops_carrier'])

lemma bitflip_recovery_map_smult: "A \<in> carrier_mat 8 8 \<Longrightarrow> bitflip_recovery_map (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m bitflip_recovery_map A"
  unfolding bitflip_recovery_map_def by (rule kraus_map_dim_smult[OF _ bitflip_recovery_ops_carrier'])

lemma comb8:
  fixes A B :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  shows "complex_of_real a \<cdot>\<^sub>m A + complex_of_real b \<cdot>\<^sub>m A + complex_of_real b \<cdot>\<^sub>m A + complex_of_real b \<cdot>\<^sub>m A
         + complex_of_real c \<cdot>\<^sub>m B + complex_of_real c \<cdot>\<^sub>m B + complex_of_real c \<cdot>\<^sub>m B + complex_of_real d \<cdot>\<^sub>m B
         = complex_of_real (a + 3 * b) \<cdot>\<^sub>m A + complex_of_real (3 * c + d) \<cdot>\<^sub>m B"
  using A B by (intro eq_matI) (simp_all add: algebra_simps)

lemma outer8: "dim_vec v = 8 \<Longrightarrow> v \<oslash> v \<in> carrier_mat 8 8"
  by (rule outer_prod_carrier) simp_all

text \<open>D31-2: errors followed by recovery on an encoded state.\<close>

theorem three_bit_code_recovery:
  assumes x: "dim_vec x = 2"
  defines "\<psi> \<equiv> encode_mat *\<^sub>v x" and "\<phi> \<equiv> encode_mat *\<^sub>v swap2 x"
  shows "bitflip_recovery_map (three_bit_channel p (\<psi> \<oslash> \<psi>))
         = complex_of_real ((1 - p)^3 + 3 * p * (1 - p)^2) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)
           + complex_of_real (3 * p^2 * (1 - p) + p^3) \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)"
proof -
  have \<psi>d: "dim_vec \<psi> = 8" and \<phi>d: "dim_vec \<phi> = 8" unfolding \<psi>_def \<phi>_def by simp_all
  have c: "\<And>b. flip_bit_mat b \<in> carrier_mat 8 8" by simp
  have co: "\<And>M. M \<in> carrier_mat 8 8 \<Longrightarrow> M * (\<psi> \<oslash> \<psi>) * (M\<^sup>\<dagger>) = (M *\<^sub>v \<psi>) \<oslash> (M *\<^sub>v \<psi>)"
    by (rule conj_outer_prod[OF _ \<psi>d])
  have fl: "(X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = \<phi>" "(X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v \<phi>"
    "(X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>2 *\<^sub>v \<phi>" "(X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi> = X\<^sub>3 *\<^sub>v \<phi>"
    using flips_on_codeword[OF x] unfolding \<psi>_def \<phi>_def by blast+
  let ?P = "\<psi> \<oslash> \<psi>" and ?Q = "\<phi> \<oslash> \<phi>"
  have E: "three_bit_channel p ?P =
     complex_of_real ((1 - p)^3) \<cdot>\<^sub>m ?P
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ((X\<^sub>1 *\<^sub>v \<psi>) \<oslash> (X\<^sub>1 *\<^sub>v \<psi>))
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ((X\<^sub>2 *\<^sub>v \<psi>) \<oslash> (X\<^sub>2 *\<^sub>v \<psi>))
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ((X\<^sub>3 *\<^sub>v \<psi>) \<oslash> (X\<^sub>3 *\<^sub>v \<psi>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>1 *\<^sub>v \<phi>) \<oslash> (X\<^sub>1 *\<^sub>v \<phi>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>2 *\<^sub>v \<phi>) \<oslash> (X\<^sub>2 *\<^sub>v \<phi>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>3 *\<^sub>v \<phi>) \<oslash> (X\<^sub>3 *\<^sub>v \<phi>))
     + complex_of_real (p^3) \<cdot>\<^sub>m ?Q"
    unfolding three_bit_channel_def
    by (simp only: co c mult_carrier_mat[OF c c] mult_carrier_mat[OF mult_carrier_mat[OF c c] c] fl)
  have r\<psi>: "bitflip_recovery_map ?P = ?P" "bitflip_recovery_map ((X\<^sub>1 *\<^sub>v \<psi>) \<oslash> (X\<^sub>1 *\<^sub>v \<psi>)) = ?P"
    "bitflip_recovery_map ((X\<^sub>2 *\<^sub>v \<psi>) \<oslash> (X\<^sub>2 *\<^sub>v \<psi>)) = ?P" "bitflip_recovery_map ((X\<^sub>3 *\<^sub>v \<psi>) \<oslash> (X\<^sub>3 *\<^sub>v \<psi>)) = ?P"
    unfolding \<psi>_def using bit_flip_code_recovery[OF x] by blast+
  have r\<phi>: "bitflip_recovery_map ?Q = ?Q" "bitflip_recovery_map ((X\<^sub>1 *\<^sub>v \<phi>) \<oslash> (X\<^sub>1 *\<^sub>v \<phi>)) = ?Q"
    "bitflip_recovery_map ((X\<^sub>2 *\<^sub>v \<phi>) \<oslash> (X\<^sub>2 *\<^sub>v \<phi>)) = ?Q" "bitflip_recovery_map ((X\<^sub>3 *\<^sub>v \<phi>) \<oslash> (X\<^sub>3 *\<^sub>v \<phi>)) = ?Q"
    unfolding \<phi>_def using bit_flip_code_recovery[OF swap2_dim] by blast+
  have oc: "\<And>M. M \<in> carrier_mat 8 8 \<Longrightarrow> (M *\<^sub>v \<psi>) \<oslash> (M *\<^sub>v \<psi>) \<in> carrier_mat 8 8"
       "\<And>M. M \<in> carrier_mat 8 8 \<Longrightarrow> (M *\<^sub>v \<phi>) \<oslash> (M *\<^sub>v \<phi>) \<in> carrier_mat 8 8"
    by (rule outer8, simp)+
  have Pc: "?P \<in> carrier_mat 8 8" and Qc: "?Q \<in> carrier_mat 8 8" by (rule outer8[OF \<psi>d], rule outer8[OF \<phi>d])
  have "bitflip_recovery_map (three_bit_channel p ?P)
        = complex_of_real ((1 - p)^3) \<cdot>\<^sub>m ?P + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ?P
          + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ?P + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ?P
          + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ?Q + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ?Q
          + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ?Q + complex_of_real (p^3) \<cdot>\<^sub>m ?Q"
    unfolding E using Pc Qc oc[OF c] r\<psi>[unfolded One_nat_def] r\<phi>[unfolded One_nat_def]
    by (simp add: bitflip_recovery_map_add bitflip_recovery_map_smult r\<psi> r\<phi>)
  also have "\<dots> = complex_of_real ((1 - p)^3 + 3 * p * (1 - p)^2) \<cdot>\<^sub>m ?P
           + complex_of_real (3 * p^2 * (1 - p) + p^3) \<cdot>\<^sub>m ?Q"
    by (subst comb8[OF Pc Qc]) (simp add: mult_ac)
  finally show ?thesis .
qed

text \<open>The code is better than doing nothing iff $(1-p)^3+3p(1-p)^2\ge1-p$ iff $p\le\frac12$.\<close>

theorem three_bit_code_better_iff:
  assumes p0: "0 \<le> p" and p1: "p < 1"
  shows "(1 - p) \<le> (1 - p)^3 + 3 * p * (1 - p)^2 \<longleftrightarrow> p \<le> (1/2 :: real)"
proof -
  have e: "(1 - p)^3 + 3 * p * (1 - p)^2 - (1 - p) = (1 - p) * (p * (1 - 2 * p))"
    by (simp add: eval_nat_numeral algebra_simps)
  have q: "0 < 1 - p" using p1 by simp
  have "(1 - p) \<le> (1 - p)^3 + 3 * p * (1 - p)^2 \<longleftrightarrow> 0 \<le> (1 - p) * (p * (1 - 2 * p))" using e by linarith
  also have "\<dots> \<longleftrightarrow> 0 \<le> p * (1 - 2 * p)" using q by (simp add: zero_le_mult_iff)
  also have "\<dots> \<longleftrightarrow> p \<le> 1/2" using p0 by (cases "p = 0") (auto simp: zero_le_mult_iff)
  finally show ?thesis .
qed

subsection \<open>Minimum fidelities (D31-4)\<close>

lemma quad_two_outer:
  fixes \<psi> \<phi> :: "complex Matrix.vec"
  assumes \<psi>d: "dim_vec \<psi> = n" and \<phi>d: "dim_vec \<phi> = n"
  shows "\<langle>\<psi> | (a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi>\<rangle>
         = a * (\<langle>\<psi>|\<psi>\<rangle> * \<langle>\<psi>|\<psi>\<rangle>) + b * (\<langle>\<phi>|\<psi>\<rangle> * \<langle>\<psi>|\<phi>\<rangle>)"
proof -
  have Pc: "\<psi> \<oslash> \<psi> \<in> carrier_mat n n" and Qc: "\<phi> \<oslash> \<phi> \<in> carrier_mat n n"
    by (rule outer_prod_carrier[OF \<psi>d \<psi>d], rule outer_prod_carrier[OF \<phi>d \<phi>d])
  have \<psi>c: "\<psi> \<in> carrier_vec n" by (rule carrier_vecI[OF \<psi>d])
  have "(a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi> = (a * \<langle>\<psi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<psi> + (b * \<langle>\<phi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<phi>"
  proof -
    have "(a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi> = (a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)) *\<^sub>v \<psi> + (b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi>"
      by (rule add_mult_distrib_mat_vec[OF smult_carrier_mat[OF Pc] smult_carrier_mat[OF Qc] \<psi>c])
    also have "\<dots> = a \<cdot>\<^sub>v (\<langle>\<psi>|\<psi>\<rangle> \<cdot>\<^sub>v \<psi>) + b \<cdot>\<^sub>v (\<langle>\<phi>|\<psi>\<rangle> \<cdot>\<^sub>v \<phi>)"
    proof -
      have d1: "dim_col (\<psi> \<oslash> \<psi>) = dim_vec \<psi>" and d2: "dim_col (\<phi> \<oslash> \<phi>) = dim_vec \<psi>"
        using carrier_matD(2)[OF Pc] carrier_matD(2)[OF Qc] \<psi>d by simp_all
      have e2: "dim_vec \<psi> = dim_vec \<phi>" using \<psi>d \<phi>d by simp
      show ?thesis by (simp only: smult_mat_mult_vec[OF carrier_matI[OF refl refl] carrier_vecI[OF d1[symmetric]]] smult_mat_mult_vec[OF carrier_matI[OF refl refl] carrier_vecI[OF d2[symmetric]]]
          outer_prod_mult_vec[of \<psi> \<psi> \<psi>, OF refl] outer_prod_mult_vec[of \<psi> \<phi> \<phi>, OF e2])
    qed
    finally show ?thesis by (simp only: smult_smult_assoc)
  qed
  hence "\<langle>\<psi> | (a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | (a * \<langle>\<psi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<psi> + (b * \<langle>\<phi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<phi>\<rangle>" by simp
  also have "\<dots> = (a * \<langle>\<psi>|\<psi>\<rangle>) * \<langle>\<psi>|\<psi>\<rangle> + (b * \<langle>\<phi>|\<psi>\<rangle>) * \<langle>\<psi>|\<phi>\<rangle>"
  proof -
    have e: "dim_vec ((a * \<langle>\<psi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<psi>) = dim_vec ((b * \<langle>\<phi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<phi>)" using \<psi>d \<phi>d by simp
    show ?thesis by (simp only: inner_prod_right_add'[OF e] inner_prod_right_smult')
  qed
  finally show ?thesis by (simp add: mult_ac)
qed

lemma encode_inner:
  assumes u: "dim_vec u = 2" and v: "dim_vec v = 2"
  shows "\<langle>encode_mat *\<^sub>v u | encode_mat *\<^sub>v v\<rangle> = \<langle>u|v\<rangle>"
proof -
  have "\<langle>encode_mat *\<^sub>v u | encode_mat *\<^sub>v v\<rangle> = (\<Sum>i \<in> {0..<8}. cnj ((encode_mat *\<^sub>v u) $ i) * (encode_mat *\<^sub>v v) $ i)"
    by (rule inner_prod_sum) simp_all
  also have "\<dots> = cnj (u $ 0) * v $ 0 + cnj (u $ 1) * v $ 1" unfolding set_8_atLeast0 using u v by (simp add: encode_mat_mult_vec del: index_mult_mat_vec)
  also have "\<dots> = \<langle>u|v\<rangle>" unfolding inner_prod_sum[OF u v] using u v by (simp add: numeral_2_eq_2)
  finally show ?thesis .
qed

theorem code_min_fidelity:
  assumes p0: "0 \<le> p" and p1: "p \<le> 1"
  defines "c1 \<equiv> (1 - p)^3 + 3 * p * (1 - p)^2"
  shows "\<forall>x. dim_vec x = 2 \<longrightarrow> \<langle>x|x\<rangle> = 1 \<longrightarrow>
           sqrt c1 \<le> fidelity (encode_mat *\<^sub>v x) (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v x) \<oslash> (encode_mat *\<^sub>v x))))"
    and "fidelity (encode_mat *\<^sub>v unit_vec 2 0)
           (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v unit_vec 2 0) \<oslash> (encode_mat *\<^sub>v unit_vec 2 0)))) = sqrt c1"
proof -
  define c2 where "c2 = 3 * p^2 * (1 - p) + p^3"
  have c2: "0 \<le> c2" unfolding c2_def using p0 p1 by simp
  have val: "\<And>x. dim_vec x = 2 \<Longrightarrow> \<langle>x|x\<rangle> = 1 \<Longrightarrow>
      fidelity (encode_mat *\<^sub>v x) (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v x) \<oslash> (encode_mat *\<^sub>v x))))
      = sqrt (c1 + c2 * (cmod \<langle>x | swap2 x\<rangle>)^2)"
  proof -
    fix x :: "complex Matrix.vec" assume x: "dim_vec x = 2" and n: "\<langle>x|x\<rangle> = 1"
    let ?\<psi> = "encode_mat *\<^sub>v x" and ?\<phi> = "encode_mat *\<^sub>v swap2 x"
    have q: "\<langle>?\<psi> | (complex_of_real c1 \<cdot>\<^sub>m (?\<psi> \<oslash> ?\<psi>) + complex_of_real c2 \<cdot>\<^sub>m (?\<phi> \<oslash> ?\<phi>)) *\<^sub>v ?\<psi>\<rangle>
             = complex_of_real c1 * (\<langle>?\<psi>|?\<psi>\<rangle> * \<langle>?\<psi>|?\<psi>\<rangle>) + complex_of_real c2 * (\<langle>?\<phi>|?\<psi>\<rangle> * \<langle>?\<psi>|?\<phi>\<rangle>)"
      by (rule quad_two_outer) simp_all
    have ip: "\<langle>?\<psi>|?\<psi>\<rangle> = 1" "\<langle>?\<psi>|?\<phi>\<rangle> = \<langle>x | swap2 x\<rangle>" "\<langle>?\<phi>|?\<psi>\<rangle> = cnj \<langle>x | swap2 x\<rangle>"
      using encode_inner[OF x x] encode_inner[OF x swap2_dim] encode_inner[OF swap2_dim x] n
        inner_prod_cnj[of "swap2 x" x] x by simp_all
    show "fidelity ?\<psi> (bitflip_recovery_map (three_bit_channel p (?\<psi> \<oslash> ?\<psi>))) = sqrt (c1 + c2 * (cmod \<langle>x | swap2 x\<rangle>)^2)"
      unfolding fidelity_def_eq three_bit_code_recovery[OF x] c1_def[symmetric] c2_def[symmetric] q ip
      by (simp add: cnj_mult_self_cmod)
  qed
  show "\<forall>x. dim_vec x = 2 \<longrightarrow> \<langle>x|x\<rangle> = 1 \<longrightarrow>
           sqrt c1 \<le> fidelity (encode_mat *\<^sub>v x) (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v x) \<oslash> (encode_mat *\<^sub>v x))))"
    using val c2 by simp
  have e0: "dim_vec (unit_vec 2 0 :: complex Matrix.vec) = 2" "\<langle>unit_vec 2 0 | unit_vec 2 (0::nat)\<rangle> = (1::complex)"
    "\<langle>unit_vec 2 0 | swap2 (unit_vec 2 0)\<rangle> = (0::complex)"
  proof -
    show "dim_vec (unit_vec 2 0 :: complex Matrix.vec) = 2" by simp
    show "\<langle>unit_vec 2 0 | unit_vec 2 (0::nat)\<rangle> = (1::complex)"
      by (subst inner_prod_unit_vec_right) simp_all
    have "swap2 (unit_vec 2 0) = unit_vec 2 1" by (rule eq_vecI) (auto simp: swap2_def less_2_cases_iff)
    thus "\<langle>unit_vec 2 0 | swap2 (unit_vec 2 0)\<rangle> = (0::complex)"
      by (simp only:) (subst inner_prod_unit_vec_right, simp_all)
  qed
  show "fidelity (encode_mat *\<^sub>v unit_vec 2 0)
           (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v unit_vec 2 0) \<oslash> (encode_mat *\<^sub>v unit_vec 2 0)))) = sqrt c1"
    unfolding val[OF e0(1,2)] e0(3) by simp
qed

theorem nothing_min_fidelity:
  assumes p0: "0 \<le> p" and p1: "p \<le> 1"
  shows "\<forall>\<psi>. dim_vec \<psi> = 2 \<longrightarrow> \<langle>\<psi>|\<psi>\<rangle> = 1 \<longrightarrow> sqrt (1 - p) \<le> fidelity \<psi> (bit_flip_channel p (\<psi> \<oslash> \<psi>))"
    and "fidelity (unit_vec 2 0) (bit_flip_channel p (unit_vec 2 0 \<oslash> unit_vec 2 0)) = sqrt (1 - p)"
proof -
  have val: "\<And>\<psi>. dim_vec \<psi> = 2 \<Longrightarrow> \<langle>\<psi>|\<psi>\<rangle> = 1 \<Longrightarrow>
      fidelity \<psi> (bit_flip_channel p (\<psi> \<oslash> \<psi>)) = sqrt ((1 - p) + p * (cmod \<langle>\<psi> | Pauli_X *\<^sub>v \<psi>\<rangle>)^2)"
  proof -
    fix \<psi> :: "complex Matrix.vec" assume \<psi>d: "dim_vec \<psi> = 2" and n: "\<langle>\<psi>|\<psi>\<rangle> = 1"
    have Xd: "dim_vec (Pauli_X *\<^sub>v \<psi>) = 2" by (simp add: Pauli_X_def)
    have "bit_flip_channel p (\<psi> \<oslash> \<psi>) = complex_of_real (1 - p) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)
          + complex_of_real p \<cdot>\<^sub>m ((Pauli_X *\<^sub>v \<psi>) \<oslash> (Pauli_X *\<^sub>v \<psi>))"
      unfolding bit_flip_channel_def using conj_outer_prod[OF Pauli_X_carrier \<psi>d] by simp
    moreover have "\<langle>\<psi> | (complex_of_real (1 - p) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + complex_of_real p \<cdot>\<^sub>m ((Pauli_X *\<^sub>v \<psi>) \<oslash> (Pauli_X *\<^sub>v \<psi>))) *\<^sub>v \<psi>\<rangle>
          = complex_of_real (1 - p) * (\<langle>\<psi>|\<psi>\<rangle> * \<langle>\<psi>|\<psi>\<rangle>)
            + complex_of_real p * (\<langle>Pauli_X *\<^sub>v \<psi>|\<psi>\<rangle> * \<langle>\<psi>|Pauli_X *\<^sub>v \<psi>\<rangle>)"
      by (rule quad_two_outer[OF \<psi>d Xd])
    moreover have "\<langle>Pauli_X *\<^sub>v \<psi>|\<psi>\<rangle> = cnj \<langle>\<psi>|Pauli_X *\<^sub>v \<psi>\<rangle>" by (rule inner_prod_cnj) (use \<psi>d Xd in simp)
    ultimately show "fidelity \<psi> (bit_flip_channel p (\<psi> \<oslash> \<psi>)) = sqrt ((1 - p) + p * (cmod \<langle>\<psi> | Pauli_X *\<^sub>v \<psi>\<rangle>)^2)"
      unfolding fidelity_def_eq n by (simp add: cnj_mult_self_cmod)
  qed
  show "\<forall>\<psi>. dim_vec \<psi> = 2 \<longrightarrow> \<langle>\<psi>|\<psi>\<rangle> = 1 \<longrightarrow> sqrt (1 - p) \<le> fidelity \<psi> (bit_flip_channel p (\<psi> \<oslash> \<psi>))"
    using val p0 by simp
  have Xe: "Pauli_X *\<^sub>v unit_vec 2 0 = unit_vec 2 1"
    by (rule eq_vecI) (auto simp: Pauli_X_def less_2_cases_iff scalar_prod_def)
  have e: "\<langle>unit_vec 2 0 | unit_vec 2 (0::nat)\<rangle> = (1::complex)" by (subst inner_prod_unit_vec_right) simp_all
  have z: "\<langle>unit_vec 2 0 | unit_vec 2 (1::nat)\<rangle> = (0::complex)" by (subst inner_prod_unit_vec_right) simp_all
  show "fidelity (unit_vec 2 0) (bit_flip_channel p (unit_vec 2 0 \<oslash> unit_vec 2 0)) = sqrt (1 - p)"
  proof -
    have d: "dim_vec (unit_vec 2 0 :: complex Matrix.vec) = 2" by simp
    show ?thesis unfolding val[OF d e] Xe z by simp
  qed
qed

end
