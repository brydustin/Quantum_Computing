(*
  Title:    Matrix_Typed.thy
  Purpose:  Typed-dimension wrapper around Jordan_Normal_Form matrices, with
            real-vector-space typeclass instances, an overloading of HOL's
            Hahn-Banach scalar-multiplication constant, and a real-vectorspace
            locale instantiation.  Used by Quantum_Computing.thy to apply
            HOL/Hahn_Banach's norm_Hahn_Banach to matrix subspaces.
*)

theory Matrix_Typed
  imports
    "HOL-Hahn_Banach.Hahn_Banach"
    "Jordan_Normal_Form.Matrix"
    "HOL-Library.Cardinality"
    "Vern_Paulsen_QC_3_10.Basic_Math"
begin

section \<open>Typed-dimension matrix wrapper\<close>

text \<open>The type \<open>('a, 'm :: finite, 'n :: finite) lmat\<close> represents matrices of size
\<open>CARD('m) \<times> CARD('n)\<close> with entries in \<open>'a\<close>, by typedef of the
JNF matrix type at the appropriate dimension.\<close>

typedef (overloaded) ('a, 'm :: finite, 'n :: finite) lmat =
  "{M :: 'a Matrix.mat. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
  morphisms unwrap_lm wrap_lm
proof
  let ?M = "Matrix.mat (CARD('m)) (CARD('n)) (\<lambda>_. undefined :: 'a)"
  show "?M \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
    by simp
qed

setup_lifting type_definition_lmat

lemma unwrap_lm_dim_row [simp]:
  "dim_row (unwrap_lm (M :: ('a, 'm :: finite, 'n :: finite) lmat)) = CARD('m)"
  using unwrap_lm by auto

lemma unwrap_lm_dim_col [simp]:
  "dim_col (unwrap_lm (M :: ('a, 'm :: finite, 'n :: finite) lmat)) = CARD('n)"
  using unwrap_lm by auto

lemma unwrap_lm_carrier [simp]:
  "unwrap_lm (M :: ('a, 'm :: finite, 'n :: finite) lmat)
     \<in> carrier_mat (CARD('m)) (CARD('n))"
  using unwrap_lm by auto


section \<open>Typeclass instances\<close>

text \<open>The unique zero matrix of the right shape.\<close>

instantiation lmat :: (zero, finite, finite) zero
begin
lift_definition zero_lmat :: "('a, 'm :: finite, 'n :: finite) lmat"
  is "0\<^sub>m (CARD('m)) (CARD('n))" by simp
instance ..
end

lemma unwrap_lm_zero [simp]:
  "unwrap_lm (0 :: ('a :: zero, 'm :: finite, 'n :: finite) lmat)
     = 0\<^sub>m (CARD('m)) (CARD('n))"
  by transfer simp

instantiation lmat :: (plus, finite, finite) plus
begin
lift_definition plus_lmat ::
  "('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat"
  is "(+)" by (simp add: plus_mat_def)
instance ..
end

lemma unwrap_lm_plus [simp]:
  "unwrap_lm ((A :: ('a :: plus, 'm :: finite, 'n :: finite) lmat) + B)
     = unwrap_lm A + unwrap_lm B"
  by transfer simp

instantiation lmat :: (uminus, finite, finite) uminus
begin
lift_definition uminus_lmat ::
  "('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat"
  is "uminus" by (simp add: uminus_mat_def)
instance ..
end

lemma unwrap_lm_uminus [simp]:
  "unwrap_lm (- (A :: ('a :: uminus, 'm :: finite, 'n :: finite) lmat))
     = - unwrap_lm A"
  by transfer simp

instantiation lmat :: (minus, finite, finite) minus
begin
lift_definition minus_lmat ::
  "('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat"
  is "(-)" by (simp add: minus_mat_def)
instance ..
end

lemma unwrap_lm_minus [simp]:
  "unwrap_lm ((A :: ('a :: minus, 'm :: finite, 'n :: finite) lmat) - B)
     = unwrap_lm A - unwrap_lm B"
  by transfer simp

text \<open>Lift the additive structure laws via @{thm eq_matI} on the
underlying JNF matrices.\<close>

instance lmat :: (semigroup_add, finite, finite) semigroup_add
proof
  fix a b c :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "a + b + c = a + (b + c)"
  proof (transfer)
    fix A B C :: "'a Matrix.mat"
    assume da: "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
      and  db: "dim_row B = CARD('m) \<and> dim_col B = CARD('n)"
      and  dc: "dim_row C = CARD('m) \<and> dim_col C = CARD('n)"
    show "A + B + C = A + (B + C)"
      using da db dc by (intro eq_matI) (auto simp: ac_simps)
  qed
qed

instance lmat :: (ab_semigroup_add, finite, finite) ab_semigroup_add
proof
  fix a b :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "a + b = b + a"
  proof (transfer)
    fix A B :: "'a Matrix.mat"
    assume da: "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
      and  db: "dim_row B = CARD('m) \<and> dim_col B = CARD('n)"
    show "A + B = B + A"
      using da db by (intro eq_matI) (auto simp: ac_simps)
  qed
qed

instance lmat :: (monoid_add, finite, finite) monoid_add
proof
  fix a :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "0 + a = a"
  proof (transfer)
    fix A :: "'a Matrix.mat"
    assume A: "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
    show "0\<^sub>m (CARD('m)) (CARD('n)) + A = A"
      using A by auto
  qed
  show "a + 0 = a"
  proof (transfer)
    fix A :: "'a Matrix.mat"
    assume A: "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
    show "A + 0\<^sub>m (CARD('m)) (CARD('n)) = A"
      using A by auto
  qed
qed

instance lmat :: (comm_monoid_add, finite, finite) comm_monoid_add
  by standard simp

instance lmat :: (group_add, finite, finite) group_add
proof
  fix a b :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "- a + a = 0"
  proof (transfer)
    fix A :: "'a Matrix.mat"
    assume da: "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
    show "- A + A = 0\<^sub>m (CARD('m)) (CARD('n))"
      using da by (intro eq_matI) (auto simp: minus_mat_def uminus_mat_def)
  qed
  show "a + - b = a - b"
  proof (transfer)
    fix A B :: "'a Matrix.mat"
    assume da: "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
      and  db: "dim_row B = CARD('m) \<and> dim_col B = CARD('n)"
    show "A + - B = A - B"
      using da db by (intro eq_matI) (auto simp: minus_mat_def uminus_mat_def plus_mat_def)
  qed
qed

instance lmat :: (ab_group_add, finite, finite) ab_group_add
  by standard (rule left_minus, rule diff_conv_add_uminus)


section \<open>Real scalar multiplication and Hahn-Banach overloading\<close>

text \<open>HOL's @{const Vector_Space.prod} is the abstract real-scalar
multiplication used by the Hahn-Banach locales.  We overload it on
the type \<open>(complex, 'm, 'n) lmat\<close> as multiplication by the
embedded real, lifted from JNF's \<open>(\<cdot>\<^sub>m)\<close>.\<close>

overloading
  prod_lmat \<equiv>
    "Vector_Space.prod ::
       real \<Rightarrow> (complex, 'm :: finite, 'n :: finite) lmat
              \<Rightarrow> (complex, 'm, 'n) lmat"
begin
definition prod_lmat ::
  "real \<Rightarrow> (complex, 'm :: finite, 'n :: finite) lmat
         \<Rightarrow> (complex, 'm, 'n) lmat"
where
  "prod_lmat r M = wrap_lm (complex_of_real r \<cdot>\<^sub>m unwrap_lm M)"
end

lemma unwrap_lm_prod [simp]:
  "unwrap_lm (Vector_Space.prod r (M :: (complex, 'm :: finite, 'n :: finite) lmat))
     = complex_of_real r \<cdot>\<^sub>m unwrap_lm M"
  unfolding prod_lmat_def
  by (subst wrap_lm_inverse) simp_all


section \<open>Real-vectorspace locale on the full type\<close>

text \<open>Every \<open>(complex, 'm, 'n) lmat\<close> with the universe set is a real
vector space in HOL/Hahn_Banach's sense.\<close>

lemma vectorspace_UNIV_lmat:
  "Vector_Space.vectorspace (UNIV :: (complex, 'm :: finite, 'n :: finite) lmat set)"
proof (unfold_locales)
  fix x y z :: "(complex, 'm, 'n) lmat" and a b :: real
  show "(UNIV :: (complex, 'm, 'n) lmat set) \<noteq> {}" by simp
  show "x + y \<in> UNIV" by simp
  show "Vector_Space.prod a x \<in> UNIV" by simp
  show "x + y + z = x + (y + z)" by (simp only: ac_simps)
  show "x + y = y + x" by (simp only: ac_simps)
  show "x - x = 0" by simp
  show "0 + x = x" by simp
  show "Vector_Space.prod a (x + y) = Vector_Space.prod a x + Vector_Space.prod a y"
  proof -
    have c1: "unwrap_lm x \<in> carrier_mat (CARD('m)) (CARD('n))" by simp
    have c2: "unwrap_lm y \<in> carrier_mat (CARD('m)) (CARD('n))" by simp
    have mat_eq:
      "complex_of_real a \<cdot>\<^sub>m (unwrap_lm x + unwrap_lm y)
         = complex_of_real a \<cdot>\<^sub>m unwrap_lm x + complex_of_real a \<cdot>\<^sub>m unwrap_lm y"
      by (rule add_smult_distrib_left_mat[OF c1 c2])
    have unwrap_eq:
      "unwrap_lm (Vector_Space.prod a (x + y))
         = unwrap_lm (Vector_Space.prod a x + Vector_Space.prod a y)"
      using mat_eq by simp
    show ?thesis
      by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
  qed
  show "Vector_Space.prod (a + b) x = Vector_Space.prod a x + Vector_Space.prod b x"
  proof -
    have cx: "unwrap_lm x \<in> carrier_mat (CARD('m)) (CARD('n))" by simp
    have mat_eq:
      "(complex_of_real a + complex_of_real b) \<cdot>\<^sub>m unwrap_lm x
         = complex_of_real a \<cdot>\<^sub>m unwrap_lm x + complex_of_real b \<cdot>\<^sub>m unwrap_lm x"
      by (rule add_smult_distrib_right_mat[OF cx])
    have unwrap_eq:
      "unwrap_lm (Vector_Space.prod (a + b) x)
         = unwrap_lm (Vector_Space.prod a x + Vector_Space.prod b x)"
      using mat_eq by (simp add: of_real_add)
    show ?thesis
      by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
  qed
  show "Vector_Space.prod (a * b) x = Vector_Space.prod a (Vector_Space.prod b x)"
  proof -
    have mat_eq:
      "(complex_of_real a * complex_of_real b) \<cdot>\<^sub>m unwrap_lm x
         = complex_of_real a \<cdot>\<^sub>m (complex_of_real b \<cdot>\<^sub>m unwrap_lm x)"
      by (intro eq_matI) (auto simp: mult.assoc)
    have unwrap_eq:
      "unwrap_lm (Vector_Space.prod (a * b) x)
         = unwrap_lm (Vector_Space.prod a (Vector_Space.prod b x))"
      using mat_eq by simp
    show ?thesis
      by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
  qed
  show "Vector_Space.prod 1 x = x"
  proof -
    have one_smult: "(1 :: complex) \<cdot>\<^sub>m unwrap_lm x = unwrap_lm x"
      by (intro eq_matI) auto
    have unwrap_eq:
      "unwrap_lm (Vector_Space.prod 1 x) = unwrap_lm x"
      using one_smult by simp
    show ?thesis
      by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
  qed
  show "- x = Vector_Space.prod (- 1) x"
  proof -
    have cx: "unwrap_lm x \<in> carrier_mat (CARD('m)) (CARD('n))" by simp
    have m1_eq: "(- 1 :: complex) \<cdot>\<^sub>m unwrap_lm x = - unwrap_lm x"
      using cx by (intro eq_matI) (auto simp: uminus_mat_def)
    have unwrap_eq:
      "unwrap_lm (- x) = unwrap_lm (Vector_Space.prod (- 1) x)"
      using m1_eq by simp
    show ?thesis
      by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
  qed
  show "x - y = x + - y"
    by (simp only: diff_conv_add_uminus)
qed


section \<open>The Hilbert-Schmidt norm on \<open>(complex, 'm, 'n) lmat\<close>\<close>

text \<open>The HS / Frobenius norm: \<open>\<parallel>M\<parallel>\<^sub>HS = sqrt (Re \<langle>\<langle>M | M\<rangle>\<rangle>)\<close>.
We define it on \<open>(complex, 'm, 'n) lmat\<close> using the underlying matrix's
HS inner product from \<open>Basic_Math\<close>.\<close>

definition hs_norm_lmat ::
    "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
where
  "hs_norm_lmat M = sqrt (Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>))"

lemma hs_norm_lmat_nonneg: "0 \<le> hs_norm_lmat M"
  unfolding hs_norm_lmat_def
  by (rule real_sqrt_ge_zero) (rule hs_inner_prod_self_nonneg)

lemma hs_norm_lmat_sq:
  "(hs_norm_lmat M)\<^sup>2 = Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>)"
proof -
  have nn: "Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>) \<ge> 0"
    by (rule hs_inner_prod_self_nonneg)
  have "(hs_norm_lmat M)\<^sup>2
        = (sqrt (Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>)))\<^sup>2"
    by (simp add: hs_norm_lmat_def)
  also have "\<dots> = Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>)"
    using nn by (rule real_sqrt_pow2)
  finally show ?thesis .
qed

lemma hs_norm_lmat_smult:
  "hs_norm_lmat (Vector_Space.prod a M) = \<bar>a\<bar> * hs_norm_lmat M"
proof -
  let ?ca = "complex_of_real a"
  have hs_smult:
    "\<langle>\<langle> ?ca \<cdot>\<^sub>m unwrap_lm M | ?ca \<cdot>\<^sub>m unwrap_lm M \<rangle>\<rangle>
     = (cnj ?ca * ?ca) * \<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>"
    by (simp add: hs_inner_prod_left_smult hs_inner_prod_right_smult ac_simps)
  have cnj_real: "cnj ?ca * ?ca = complex_of_real (a\<^sup>2)"
    by (simp add: complex_eq_iff power2_eq_square)
  have re_mul:
    "Re (complex_of_real (a\<^sup>2) * \<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>)
     = a\<^sup>2 * Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>)"
    by simp
  have nn: "Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>) \<ge> 0"
    by (rule hs_inner_prod_self_nonneg)
  have a2_nn: "0 \<le> a\<^sup>2" by simp
  have "hs_norm_lmat (Vector_Space.prod a M)
        = sqrt (Re (\<langle>\<langle> ?ca \<cdot>\<^sub>m unwrap_lm M | ?ca \<cdot>\<^sub>m unwrap_lm M \<rangle>\<rangle>))"
    by (simp add: hs_norm_lmat_def)
  also have "\<dots> = sqrt (a\<^sup>2 * Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>))"
    using hs_smult cnj_real re_mul by simp
  also have "\<dots> = sqrt (a\<^sup>2) * sqrt (Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>))"
    by (rule real_sqrt_mult)
  also have "\<dots> = \<bar>a\<bar> * hs_norm_lmat M"
    by (simp only: hs_norm_lmat_def real_sqrt_abs)
  finally show ?thesis .
qed


section \<open>Triangle inequality for the HS norm\<close>

text \<open>Cauchy-Schwarz on the HS inner product (real form), used in
the triangle inequality proof.\<close>

lemma hs_inner_prod_real_self:
  "\<langle>\<langle> A | A \<rangle>\<rangle> = complex_of_real (Re (\<langle>\<langle> A | A \<rangle>\<rangle>))"
  using hs_inner_prod_self_real
  by (metis Reals_cases of_real_Re)

lemma hs_inner_prod_left_add:
  assumes "dim_row A1 = dim_row B" and "dim_col A1 = dim_col B"
      and "dim_row A2 = dim_row B" and "dim_col A2 = dim_col B"
  shows "\<langle>\<langle> A1 + A2 | B \<rangle>\<rangle> = \<langle>\<langle> A1 | B \<rangle>\<rangle> + \<langle>\<langle> A2 | B \<rangle>\<rangle>"
proof -
  have dims:
    "dim_row (A1 + A2) = dim_row B" "dim_col (A1 + A2) = dim_col B"
    using assms by auto
  have "\<langle>\<langle> A1 + A2 | B \<rangle>\<rangle> = cnj (\<langle>\<langle> B | A1 + A2 \<rangle>\<rangle>)"
    using dims by (intro hs_inner_prod_cnj) auto
  also have "\<dots> = cnj (\<langle>\<langle> B | A1 \<rangle>\<rangle> + \<langle>\<langle> B | A2 \<rangle>\<rangle>)"
    using assms by (simp add: hs_inner_prod_right_add)
  also have "\<dots> = cnj (\<langle>\<langle> B | A1 \<rangle>\<rangle>) + cnj (\<langle>\<langle> B | A2 \<rangle>\<rangle>)"
    by simp
  also have "\<dots> = \<langle>\<langle> A1 | B \<rangle>\<rangle> + \<langle>\<langle> A2 | B \<rangle>\<rangle>"
    by (metis assms(1,2,3,4) hs_inner_prod_cnj)    
  finally show ?thesis.
qed

lemma hs_cauchy_schwarz_re:
  fixes A B :: "complex Matrix.mat"
  assumes dr: "dim_row A = dim_row B" and dc: "dim_col A = dim_col B"
  shows "(Re (\<langle>\<langle> A | B \<rangle>\<rangle>))\<^sup>2 \<le> Re (\<langle>\<langle> A | A \<rangle>\<rangle>) * Re (\<langle>\<langle> B | B \<rangle>\<rangle>)"
proof -
  let ?aa = "Re (\<langle>\<langle> A | A \<rangle>\<rangle>)"
  let ?bb = "Re (\<langle>\<langle> B | B \<rangle>\<rangle>)"
  let ?ab = "Re (\<langle>\<langle> A | B \<rangle>\<rangle>)"
  let ?ba = "Re (\<langle>\<langle> B | A \<rangle>\<rangle>)"
  have aa_nn: "?aa \<ge> 0" by (rule hs_inner_prod_self_nonneg)
  have bb_nn: "?bb \<ge> 0" by (rule hs_inner_prod_self_nonneg)
  have ab_eq_ba: "?ab = ?ba"
    by (metis cnj.sel(1) dc dr hs_inner_prod_cnj)

  have quad_nn:
    "\<And>t :: real. 0 \<le> ?aa + 2 * t * ?ab + t\<^sup>2 * ?bb"
  proof -
    fix t :: real
    let ?CR = "complex_of_real"
    have dim_tB_row: "dim_row (?CR t \<cdot>\<^sub>m B) = dim_row B" by simp
    have dim_tB_col: "dim_col (?CR t \<cdot>\<^sub>m B) = dim_col B" by simp
    have dim_AtB_row: "dim_row (A + ?CR t \<cdot>\<^sub>m B) = dim_row B" using dr by simp
    have dim_AtB_col: "dim_col (A + ?CR t \<cdot>\<^sub>m B) = dim_col B" using dc by simp

    have ip_self_nn:
      "0 \<le> Re (\<langle>\<langle> A + ?CR t \<cdot>\<^sub>m B | A + ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>)"
      by (rule hs_inner_prod_self_nonneg)

    have left_split:
      "\<langle>\<langle> A + ?CR t \<cdot>\<^sub>m B | A + ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>
       = \<langle>\<langle> A | A + ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>
         + \<langle>\<langle> ?CR t \<cdot>\<^sub>m B | A + ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>"
      using dr dc by (intro hs_inner_prod_left_add) auto
    have AaB:
      "\<langle>\<langle> A | A + ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>
       = \<langle>\<langle> A | A \<rangle>\<rangle> + \<langle>\<langle> A | ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>"
      using dr dc by (intro hs_inner_prod_right_add) auto
    have tBaB:
      "\<langle>\<langle> ?CR t \<cdot>\<^sub>m B | A + ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>
       = \<langle>\<langle> ?CR t \<cdot>\<^sub>m B | A \<rangle>\<rangle> + \<langle>\<langle> ?CR t \<cdot>\<^sub>m B | ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>"
      using dr dc by (intro hs_inner_prod_right_add) auto
    have AtB: "\<langle>\<langle> A | ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle> = ?CR t * \<langle>\<langle> A | B \<rangle>\<rangle>"
      using dc dr hs_inner_prod_right_smult by presburger
    have tBA: "\<langle>\<langle> ?CR t \<cdot>\<^sub>m B | A \<rangle>\<rangle> = cnj (?CR t) * \<langle>\<langle> B | A \<rangle>\<rangle>"
      using dc dr hs_inner_prod_left_smult by blast
    have tBtB:
      "\<langle>\<langle> ?CR t \<cdot>\<^sub>m B | ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle> = cnj (?CR t) * (?CR t * \<langle>\<langle> B | B \<rangle>\<rangle>)"
      by (simp add: hs_inner_prod_left_smult hs_inner_prod_right_smult)

    have expand:
      "\<langle>\<langle> A + ?CR t \<cdot>\<^sub>m B | A + ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>
       = \<langle>\<langle> A | A \<rangle>\<rangle>
         + ?CR t * \<langle>\<langle> A | B \<rangle>\<rangle>
         + ?CR t * \<langle>\<langle> B | A \<rangle>\<rangle>
         + ?CR (t\<^sup>2) * \<langle>\<langle> B | B \<rangle>\<rangle>"
      using left_split AaB tBaB AtB tBA tBtB
      by (simp add: power2_eq_square)

    have re_expand:
      "Re (\<langle>\<langle> A + ?CR t \<cdot>\<^sub>m B | A + ?CR t \<cdot>\<^sub>m B \<rangle>\<rangle>)
       = ?aa + t * ?ab + t * ?ba + t\<^sup>2 * ?bb"
      using expand by simp
    also have "\<dots> = ?aa + 2 * t * ?ab + t\<^sup>2 * ?bb"
      using ab_eq_ba by (simp add: algebra_simps)
    finally show "0 \<le> ?aa + 2 * t * ?ab + t\<^sup>2 * ?bb"
      using ip_self_nn by simp
  qed

  show ?thesis
  proof (cases "?bb = 0")
    case True
    then have bb0: "?bb = 0" .
    have "?ab = 0"
    proof (rule ccontr)
      assume "?ab \<noteq> 0"
      then obtain s where s_def: "s = - (?aa + 1) / (2 * ?ab)" and s_nz: "True"
        by simp
      have "?aa + 2 * s * ?ab + s\<^sup>2 * ?bb = ?aa + 2 * s * ?ab"
        using bb0 by simp
      also have "\<dots> = ?aa - (?aa + 1)"
        using \<open>?ab \<noteq> 0\<close> by (simp add: s_def field_simps)
      also have "\<dots> = - 1" by simp
      finally have "?aa + 2 * s * ?ab + s\<^sup>2 * ?bb = - 1" .
      with quad_nn[of s] show False by simp
    qed
    thus ?thesis using bb0 by simp
  next
    case False
    hence bb_pos: "?bb > 0" using bb_nn by simp
    let ?t = "- ?ab / ?bb"
    have ineq: "0 \<le> ?aa + 2 * ?t * ?ab + ?t\<^sup>2 * ?bb"
      by (rule quad_nn)
    have "?aa + 2 * ?t * ?ab + ?t\<^sup>2 * ?bb
          = ?aa - 2 * ?ab\<^sup>2 / ?bb + ?ab\<^sup>2 / ?bb"
      using bb_pos by (simp add: field_simps power2_eq_square)
    also have "\<dots> = ?aa - ?ab\<^sup>2 / ?bb"
      by (simp add: field_simps)
    finally have "0 \<le> ?aa - ?ab\<^sup>2 / ?bb" using ineq by simp
    hence "?ab\<^sup>2 / ?bb \<le> ?aa" by simp
    hence "?ab\<^sup>2 \<le> ?aa * ?bb"
      using bb_pos by (simp add: field_simps)
    thus ?thesis by simp
  qed
qed

lemma hs_norm_lmat_triangle:
  fixes M N :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "hs_norm_lmat (M + N) \<le> hs_norm_lmat M + hs_norm_lmat N"
proof -
  let ?A = "unwrap_lm M"
  let ?B = "unwrap_lm N"
  have dr: "dim_row ?A = dim_row ?B" by simp
  have dc: "dim_col ?A = dim_col ?B" by simp
  let ?aa = "Re (\<langle>\<langle> ?A | ?A \<rangle>\<rangle>)"
  let ?bb = "Re (\<langle>\<langle> ?B | ?B \<rangle>\<rangle>)"
  let ?ab = "Re (\<langle>\<langle> ?A | ?B \<rangle>\<rangle>)"
  have aa_nn: "?aa \<ge> 0" by (rule hs_inner_prod_self_nonneg)
  have bb_nn: "?bb \<ge> 0" by (rule hs_inner_prod_self_nonneg)

  have ab_eq_ba: "?ab = Re (\<langle>\<langle> ?B | ?A \<rangle>\<rangle>)"
    by (metis cnj.sel(1) dc dr hs_inner_prod_cnj)
  have unwrap_sum: "unwrap_lm (M + N) = ?A + ?B" by simp
  have ip_sum:
    "\<langle>\<langle> ?A + ?B | ?A + ?B \<rangle>\<rangle>
     = \<langle>\<langle> ?A | ?A \<rangle>\<rangle> + \<langle>\<langle> ?A | ?B \<rangle>\<rangle> + \<langle>\<langle> ?B | ?A \<rangle>\<rangle> + \<langle>\<langle> ?B | ?B \<rangle>\<rangle>"
  proof -
    have "\<langle>\<langle> ?A + ?B | ?A + ?B \<rangle>\<rangle>
          = \<langle>\<langle> ?A | ?A + ?B \<rangle>\<rangle> + \<langle>\<langle> ?B | ?A + ?B \<rangle>\<rangle>"
      using dr dc by (intro hs_inner_prod_left_add) auto
    also have "\<langle>\<langle> ?A | ?A + ?B \<rangle>\<rangle> = \<langle>\<langle> ?A | ?A \<rangle>\<rangle> + \<langle>\<langle> ?A | ?B \<rangle>\<rangle>"
      using dr dc by (intro hs_inner_prod_right_add) auto
    moreover have "\<langle>\<langle> ?B | ?A + ?B \<rangle>\<rangle> = \<langle>\<langle> ?B | ?A \<rangle>\<rangle> + \<langle>\<langle> ?B | ?B \<rangle>\<rangle>"
      using dr dc by (intro hs_inner_prod_right_add) auto
    ultimately show ?thesis by (simp add: ac_simps)
  qed
  have re_sum:
    "Re (\<langle>\<langle> ?A + ?B | ?A + ?B \<rangle>\<rangle>) = ?aa + 2 * ?ab + ?bb"
    using ip_sum ab_eq_ba by simp

  have cs: "?ab\<^sup>2 \<le> ?aa * ?bb"
    using hs_cauchy_schwarz_re[OF dr dc] .
  have ab_le: "?ab \<le> sqrt ?aa * sqrt ?bb"
  proof -
    have aa_bb_nn: "0 \<le> ?aa * ?bb" using aa_nn bb_nn by simp
    have "?ab \<le> \<bar>?ab\<bar>" by simp
    also have "\<bar>?ab\<bar> = sqrt (?ab\<^sup>2)" by simp
    also have "\<dots> \<le> sqrt (?aa * ?bb)"
      using cs by (rule real_sqrt_le_mono)
    also have "\<dots> = sqrt ?aa * sqrt ?bb"
      by (rule real_sqrt_mult)
    finally show ?thesis.
  qed

  have target_sq:
    "(hs_norm_lmat (M + N))\<^sup>2 \<le> (hs_norm_lmat M + hs_norm_lmat N)\<^sup>2"
  proof -
    have lhs: "(hs_norm_lmat (M + N))\<^sup>2 = ?aa + 2 * ?ab + ?bb"
      using hs_norm_lmat_sq[of "M + N"] re_sum unwrap_sum by simp
    have rhs:
      "(hs_norm_lmat M + hs_norm_lmat N)\<^sup>2
       = ?aa + 2 * (sqrt ?aa * sqrt ?bb) + ?bb"
    proof -
      have eA: "(hs_norm_lmat M)\<^sup>2 = ?aa"
        by (rule hs_norm_lmat_sq)
      have eB: "(hs_norm_lmat N)\<^sup>2 = ?bb"
        by (rule hs_norm_lmat_sq)
      have hA: "hs_norm_lmat M = sqrt ?aa"
        by (simp add: hs_norm_lmat_def)
      have hB: "hs_norm_lmat N = sqrt ?bb"
        by (simp add: hs_norm_lmat_def)
      have "(hs_norm_lmat M + hs_norm_lmat N)\<^sup>2
            = (sqrt ?aa + sqrt ?bb)\<^sup>2"
        by (simp add: hA hB)
      also have "\<dots> = (sqrt ?aa)\<^sup>2 + 2 * (sqrt ?aa * sqrt ?bb) + (sqrt ?bb)\<^sup>2"
        by (simp add: power2_sum)
      also have "\<dots> = ?aa + 2 * (sqrt ?aa * sqrt ?bb) + ?bb"
        using aa_nn bb_nn by simp
      finally show ?thesis .
    qed
    show ?thesis
      using lhs rhs ab_le by (simp add: algebra_simps)
  qed

  have lhs_nn: "0 \<le> hs_norm_lmat (M + N)" by (rule hs_norm_lmat_nonneg)
  have rhs_nn: "0 \<le> hs_norm_lmat M + hs_norm_lmat N"
    using hs_norm_lmat_nonneg[of M] hs_norm_lmat_nonneg[of N] by simp
  show ?thesis
    using target_sq lhs_nn rhs_nn power2_le_imp_le by blast
qed


section \<open>Subspace, seminorm, normed-vectorspace instances\<close>

text \<open>HS norm is a seminorm on the whole real vector space of
\<open>(complex, 'm, 'n) lmat\<close>.\<close>

lemma seminorm_UNIV_hs_norm_lmat:
  "seminorm (UNIV :: (complex, 'm :: finite, 'n :: finite) lmat set) hs_norm_lmat"
proof
  fix x y :: "(complex, 'm, 'n) lmat" and a :: real
  show "0 \<le> hs_norm_lmat x" by (rule hs_norm_lmat_nonneg)
  show "hs_norm_lmat (Vector_Space.prod a x) = \<bar>a\<bar> * hs_norm_lmat x"
    by (rule hs_norm_lmat_smult)
  show "hs_norm_lmat (x + y) \<le> hs_norm_lmat x + hs_norm_lmat y"
    by (rule hs_norm_lmat_triangle)
qed

text \<open>HS norm is a (real) norm: it vanishes only on the zero matrix.\<close>

lemma hs_norm_lmat_zero_iff:
  fixes M :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "(hs_norm_lmat M = 0) \<longleftrightarrow> (M = 0)"
proof
  assume "hs_norm_lmat M = 0"
  hence sq_zero: "Re (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>) = 0"
    using hs_norm_lmat_sq[of M] by simp
  have re_in_R: "\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle> \<in> \<real>"
    by (rule hs_inner_prod_self_real)
  hence im_zero: "Im (\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle>) = 0"
    by (simp add: complex_is_Real_iff)
  have ip_zero: "\<langle>\<langle> unwrap_lm M | unwrap_lm M \<rangle>\<rangle> = 0"
    using sq_zero im_zero by (simp add: complex_eq_iff)
  have entries:
    "\<And>i j. i < CARD('m) \<Longrightarrow> j < CARD('n) \<Longrightarrow> (unwrap_lm M) $$ (i, j) = 0"
    using ip_zero hs_inner_prod_eq_zero_imp by force
  have unwrap_zero: "unwrap_lm M = 0\<^sub>m (CARD('m)) (CARD('n))"
    by (intro eq_matI) (auto simp: zero_mat_def entries)
  have "unwrap_lm M = unwrap_lm (0 :: (complex, 'm, 'n) lmat)"
    using unwrap_zero by simp
  thus "M = 0" by (simp only: unwrap_lm_inject)
next
  assume "M = 0"
  thus "hs_norm_lmat M = 0"
    by (simp add: hs_norm_lmat_def hs_inner_prod_def zero_mat_def)
qed

lemma norm_UNIV_hs_norm_lmat:
  "Normed_Space.norm
     (UNIV :: (complex, 'm :: finite, 'n :: finite) lmat set) hs_norm_lmat"
  using seminorm_UNIV_hs_norm_lmat hs_norm_lmat_zero_iff
  by (auto simp: Normed_Space.norm_def Normed_Space.norm_axioms_def)

lemma normed_vectorspace_UNIV_lmat:
  "normed_vectorspace
     (UNIV :: (complex, 'm :: finite, 'n :: finite) lmat set) hs_norm_lmat"
  using vectorspace_UNIV_lmat norm_UNIV_hs_norm_lmat
  by (rule normed_vectorspace.intro)

text \<open>A complex-linear subspace V of \<open>(complex, 'm, 'n) lmat\<close>
(i.e.\ nonempty, closed under addition and complex-scalar
multiplication) is in particular a real-linear subspace, hence a
\<open>subspace\<close> of \<open>UNIV\<close> in HOL/Hahn_Banach's sense.\<close>

definition cmat_subspace_lmat ::
    "(complex, 'm :: finite, 'n :: finite) lmat set \<Rightarrow> bool"
where
  "cmat_subspace_lmat V \<equiv>
     V \<noteq> {} \<and>
     (\<forall>x \<in> V. \<forall>y \<in> V. x + y \<in> V) \<and>
     (\<forall>x \<in> V. \<forall>c :: complex.
        wrap_lm (c \<cdot>\<^sub>m unwrap_lm x) \<in> V)"

lemma subspace_of_cmat_subspace_lmat:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
  assumes "cmat_subspace_lmat V"
  shows "Subspace.subspace V (UNIV :: (complex, 'm, 'n) lmat set)"
proof
  show "V \<noteq> {}"
    using assms unfolding cmat_subspace_lmat_def by simp
  show "V \<subseteq> UNIV" by simp
  fix x y :: "(complex, 'm, 'n) lmat" and a :: real
  assume xV: "x \<in> V" and yV: "y \<in> V"
  show "x + y \<in> V"
    using assms xV yV unfolding cmat_subspace_lmat_def by blast
  have "Vector_Space.prod a x = wrap_lm (complex_of_real a \<cdot>\<^sub>m unwrap_lm x)"
    by (simp add: prod_lmat_def)
  thus "Vector_Space.prod a x \<in> V"
    using assms xV unfolding cmat_subspace_lmat_def by simp
qed


section \<open>Complex scalar multiplication on lmat\<close>

text \<open>Complex scalar multiplication on \<open>(complex, 'm, 'n) lmat\<close>,
extending the \<open>Vector_Space.prod\<close> overload (which is only by reals).\<close>

definition cmult_lmat ::
    "complex \<Rightarrow> (complex, 'm :: finite, 'n :: finite) lmat
              \<Rightarrow> (complex, 'm, 'n) lmat"
where
  "cmult_lmat c M = wrap_lm (c \<cdot>\<^sub>m unwrap_lm M)"

lemma unwrap_lm_cmult [simp]:
  "unwrap_lm (cmult_lmat c (M :: (complex, 'm :: finite, 'n :: finite) lmat))
     = c \<cdot>\<^sub>m unwrap_lm M"
  unfolding cmult_lmat_def
  by (subst wrap_lm_inverse) simp_all

lemma cmult_lmat_real:
  "cmult_lmat (complex_of_real a) M = Vector_Space.prod a M"
  by (simp add: cmult_lmat_def prod_lmat_def)


section \<open>Bounded complex-linear functionals on lmat\<close>

definition clinear_functional_on ::
    "(complex, 'm :: finite, 'n :: finite) lmat set
     \<Rightarrow> ((complex, 'm, 'n) lmat \<Rightarrow> complex) \<Rightarrow> bool"
where
  "clinear_functional_on V g \<equiv>
     (\<forall>x \<in> V. \<forall>y \<in> V. g (x + y) = g x + g y) \<and>
     (\<forall>x \<in> V. \<forall>c. g (cmult_lmat c x) = c * g x)"

definition bounded_clinear_functional_on ::
    "(complex, 'm :: finite, 'n :: finite) lmat set
     \<Rightarrow> ((complex, 'm, 'n) lmat \<Rightarrow> complex) \<Rightarrow> bool"
where
  "bounded_clinear_functional_on V g \<equiv>
     clinear_functional_on V g \<and>
     (\<exists>C \<ge> 0. \<forall>x \<in> V. cmod (g x) \<le> C * hs_norm_lmat x)"


section \<open>Real-part functional and linearform/continuous instances\<close>

definition re_part_lmat ::
    "((complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> complex)
     \<Rightarrow> ((complex, 'm, 'n) lmat \<Rightarrow> real)"
where
  "re_part_lmat g x = Re (g x)"

lemma linearform_re_part_lmat:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
  assumes V_sub: "Subspace.subspace V UNIV"
      and g_clin: "clinear_functional_on V g"
  shows "linearform V (re_part_lmat g)"
proof
  fix x y :: "(complex, 'm, 'n) lmat" and a :: real
  assume xV: "x \<in> V" and yV: "y \<in> V"
  show "re_part_lmat g (x + y) = re_part_lmat g x + re_part_lmat g y"
    using g_clin xV yV
    unfolding clinear_functional_on_def re_part_lmat_def
    by simp
next
  fix x :: "(complex, 'm, 'n) lmat" and a :: real
  assume xV: "x \<in> V"
  have prod_as_cmult: "Vector_Space.prod a x = cmult_lmat (complex_of_real a) x"
    by (simp add: cmult_lmat_real)
  have "g (Vector_Space.prod a x) = complex_of_real a * g x"
    using g_clin xV prod_as_cmult
    unfolding clinear_functional_on_def by simp
  thus "re_part_lmat g (Vector_Space.prod a x) = a * re_part_lmat g x"
    unfolding re_part_lmat_def by simp
qed

lemma continuous_re_part_lmat:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
  assumes V_sub: "Subspace.subspace V UNIV"
      and g_bnd: "bounded_clinear_functional_on V g"
  shows "continuous V (re_part_lmat g) hs_norm_lmat"
proof -
  have lin: "linearform V (re_part_lmat g)"
    using V_sub g_bnd
    unfolding bounded_clinear_functional_on_def
    by (intro linearform_re_part_lmat) auto
  obtain C where C_nn: "C \<ge> 0"
            and C_bnd: "\<forall>x \<in> V. cmod (g x) \<le> C * hs_norm_lmat x"
    using g_bnd unfolding bounded_clinear_functional_on_def by blast
  have re_bnd: "\<And>x. x \<in> V \<Longrightarrow> \<bar>re_part_lmat g x\<bar> \<le> C * hs_norm_lmat x"
  proof -
    fix x assume xV: "x \<in> V"
    have "\<bar>re_part_lmat g x\<bar> = \<bar>Re (g x)\<bar>"
      unfolding re_part_lmat_def by simp
    also have "\<dots> \<le> cmod (g x)"
      by (rule abs_Re_le_cmod)
    also have "\<dots> \<le> C * hs_norm_lmat x"
      using C_bnd xV by simp
    finally show "\<bar>re_part_lmat g x\<bar> \<le> C * hs_norm_lmat x" .
  qed
  show ?thesis using lin re_bnd by (rule continuousI)
qed


section \<open>Application of HOL/Hahn_Banach (norm-preserving extension)\<close>

text \<open>Apply HOL/Hahn_Banach to extend the real-linearform
\<open>re_part_lmat g\<close> to all of UNIV preserving the function norm.\<close>

theorem hahn_banach_re_part_lmat:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
  assumes V_sub: "Subspace.subspace V (UNIV :: (complex, 'm, 'n) lmat set)"
      and g_bnd: "bounded_clinear_functional_on V g"
  shows
    "\<exists>F :: (complex, 'm, 'n) lmat \<Rightarrow> real.
        linearform UNIV F
      \<and> continuous UNIV F hs_norm_lmat
      \<and> (\<forall>x \<in> V. F x = re_part_lmat g x)"
proof -
  have nv: "normed_vectorspace UNIV hs_norm_lmat"
    by (rule normed_vectorspace_UNIV_lmat)
  have lin: "linearform V (re_part_lmat g)"
    using V_sub g_bnd
    unfolding bounded_clinear_functional_on_def
    by (intro linearform_re_part_lmat) auto
  have cont: "continuous V (re_part_lmat g) hs_norm_lmat"
    by (rule continuous_re_part_lmat[OF V_sub g_bnd])
  obtain F where
      F_lin: "linearform UNIV F"
    and F_cont: "continuous UNIV F hs_norm_lmat"
    and F_ext: "\<forall>x \<in> V. F x = re_part_lmat g x"
    using norm_Hahn_Banach[OF nv V_sub lin cont] by blast
  show ?thesis using F_lin F_cont F_ext by blast
qed


section \<open>Bohnenblust-Sobczyk: complex extension from real extension\<close>

text \<open>Given a real-linear extension \<open>F\<close> of \<open>re_part_lmat g\<close> on
all of UNIV, define the complex-linear extension
\<open>f x = F x - i \<cdot> F (i \<cdot> x)\<close>.\<close>

definition bs_complex_extension ::
    "((complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real)
     \<Rightarrow> ((complex, 'm, 'n) lmat \<Rightarrow> complex)"
where
  "bs_complex_extension F x =
     complex_of_real (F x) - \<i> * complex_of_real (F (cmult_lmat \<i> x))"

end