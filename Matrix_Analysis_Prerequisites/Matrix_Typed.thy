(*  Title:   Matrix_Typed.thy
    Author:  Dustin Bryant.  Typed-dimension matrices with the Hilbert-Schmidt norm: the
             setting of the Hahn-Banach theorem of Day 25 (Day25_Hahn_Banach).
*)

theory Matrix_Typed
  imports
    "HOL-Hahn_Banach.Hahn_Banach"
    "Jordan_Normal_Form.Matrix"
    "HOL-Library.Cardinality"
    "HOL-Analysis.L2_Norm"
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
vector space in HOL/Hahn\_Banach's sense.\<close>

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

text \<open>The Hilbert--Schmidt (Frobenius) norm $\|M\|=(\sum_{i,j}|M_{ij}|^2)^{1/2}$, the Euclidean
norm of the entries.\<close>

definition hs_norm_lmat ::
    "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
where
  "hs_norm_lmat M =
     L2_set (\<lambda>(i, j). cmod (unwrap_lm M $$ (i, j))) ({0..<CARD('m)} \<times> {0..<CARD('n)})"

lemma hs_norm_lmat_nonneg: "0 \<le> hs_norm_lmat M"
  unfolding hs_norm_lmat_def by (rule L2_set_nonneg)

text \<open>Scaling every entry in modulus by $r\ge0$ scales the norm by $r$.\<close>

lemma hs_norm_lmat_scale:
  fixes M N :: "(complex, 'm :: finite, 'n :: finite) lmat"
  assumes "\<And>i j. i < CARD('m) \<Longrightarrow> j < CARD('n) \<Longrightarrow>
             cmod (unwrap_lm N $$ (i, j)) = r * cmod (unwrap_lm M $$ (i, j))"
      and "0 \<le> r"
  shows "hs_norm_lmat N = r * hs_norm_lmat M"
proof -
  have "hs_norm_lmat N
        = L2_set (\<lambda>x. r * (\<lambda>(i, j). cmod (unwrap_lm M $$ (i, j))) x) ({0..<CARD('m)} \<times> {0..<CARD('n)})"
    unfolding hs_norm_lmat_def using assms(1) by (intro L2_set_cong) auto
  also have "\<dots> = r * hs_norm_lmat M"
    unfolding hs_norm_lmat_def using assms(2) by (simp add: L2_set_right_distrib)
  finally show ?thesis .
qed

lemma hs_norm_lmat_smult:
  "hs_norm_lmat (Vector_Space.prod a M) = \<bar>a\<bar> * hs_norm_lmat M"
  by (rule hs_norm_lmat_scale) (simp_all add: norm_mult)

lemma hs_norm_lmat_triangle:
  fixes M N :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "hs_norm_lmat (M + N) \<le> hs_norm_lmat M + hs_norm_lmat N"
proof -
  let ?I = "{0..<CARD('m)} \<times> {0..<CARD('n)}"
  let ?f = "\<lambda>(i, j). cmod (unwrap_lm M $$ (i, j))"
  let ?g = "\<lambda>(i, j). cmod (unwrap_lm N $$ (i, j))"
  have "hs_norm_lmat (M + N) \<le> L2_set (\<lambda>x. ?f x + ?g x) ?I"
    unfolding hs_norm_lmat_def by (rule L2_set_mono) (auto simp: norm_triangle_ineq)
  also have "\<dots> \<le> L2_set ?f ?I + L2_set ?g ?I"
    by (rule L2_set_triangle_ineq)
  finally show ?thesis unfolding hs_norm_lmat_def .
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
  hence entries: "\<And>i j. i < CARD('m) \<Longrightarrow> j < CARD('n) \<Longrightarrow> unwrap_lm M $$ (i, j) = 0"
    unfolding hs_norm_lmat_def by (auto simp: L2_set_eq_0_iff)
  have "unwrap_lm M = unwrap_lm (0 :: (complex, 'm, 'n) lmat)"
    by (intro eq_matI) (auto simp: entries)
  thus "M = 0" by (simp only: unwrap_lm_inject)
next
  assume "M = 0"
  thus "hs_norm_lmat M = 0"
    by (auto simp: hs_norm_lmat_def L2_set_eq_0_iff)
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
\<open>subspace\<close> of \<open>UNIV\<close> in HOL/Hahn\_Banach's sense.\<close>

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

lemma cmult_lmat_add:
  fixes x y :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "cmult_lmat c (x + y) = cmult_lmat c x + cmult_lmat c y"
proof -
  have c1: "unwrap_lm x \<in> carrier_mat (CARD('m)) (CARD('n))" by simp
  have c2: "unwrap_lm y \<in> carrier_mat (CARD('m)) (CARD('n))" by simp
  have unwrap_eq:
    "unwrap_lm (cmult_lmat c (x + y))
       = unwrap_lm (cmult_lmat c x + cmult_lmat c y)"
    using add_smult_distrib_left_mat[OF c1 c2] by simp
  show ?thesis
    by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
qed

lemma cmult_lmat_scalar_add:
  fixes x :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "cmult_lmat (c + d) x = cmult_lmat c x + cmult_lmat d x"
proof -
  have cx: "unwrap_lm x \<in> carrier_mat (CARD('m)) (CARD('n))" by simp
  have unwrap_eq:
    "unwrap_lm (cmult_lmat (c + d) x)
       = unwrap_lm (cmult_lmat c x + cmult_lmat d x)"
    using add_smult_distrib_right_mat[OF cx] by simp
  show ?thesis
    by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
qed

lemma cmult_lmat_scalar_mult:
  fixes x :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "cmult_lmat (c * d) x = cmult_lmat c (cmult_lmat d x)"
proof -
  have mat_eq: "(c * d) \<cdot>\<^sub>m unwrap_lm x = c \<cdot>\<^sub>m (d \<cdot>\<^sub>m unwrap_lm x)"
    by (intro eq_matI) (auto simp: ac_simps)
  have unwrap_eq:
    "unwrap_lm (cmult_lmat (c * d) x)
       = unwrap_lm (cmult_lmat c (cmult_lmat d x))"
    using mat_eq by simp
  show ?thesis
    by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
qed

lemma cmult_lmat_uminus_one:
  fixes x :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "cmult_lmat (- 1) x = - x"
proof -
  have cx: "unwrap_lm x \<in> carrier_mat (CARD('m)) (CARD('n))" by simp
  have m1_eq: "(- 1 :: complex) \<cdot>\<^sub>m unwrap_lm x = - unwrap_lm x"
    using cx by (intro eq_matI) (auto simp: uminus_mat_def)
  have unwrap_eq: "unwrap_lm (cmult_lmat (- 1) x) = unwrap_lm (- x)"
    using m1_eq by simp
  show ?thesis
    by (rule iffD1[OF unwrap_lm_inject unwrap_eq])
qed

lemma cmult_lmat_i_sq:
  fixes x :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "cmult_lmat \<i> (cmult_lmat \<i> x) = - x"
  using cmult_lmat_scalar_mult[symmetric, of \<i> \<i> x] cmult_lmat_uminus_one[of x]
  by (simp add: i_squared)

lemma hs_norm_lmat_cmult:
  fixes M :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "hs_norm_lmat (cmult_lmat c M) = cmod c * hs_norm_lmat M"
  by (rule hs_norm_lmat_scale) (simp_all add: norm_mult)

end
