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
  is "(+)" by (auto simp: plus_mat_def)
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
  is "uminus" by (auto simp: uminus_mat_def)
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
  is "(-)" by (auto simp: minus_mat_def)
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
    assume "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
      and  "dim_row B = CARD('m) \<and> dim_col B = CARD('n)"
      and  "dim_row C = CARD('m) \<and> dim_col C = CARD('n)"
    then have A: "A \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
       and B: "B \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
       and C: "C \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
      by simp_all
    have Ac: "A \<in> carrier_mat (CARD('m)) (CARD('n))"
      using A by blast 
    have Bc: "B \<in> carrier_mat (CARD('m)) (CARD('n))"
      using B by blast
    have Cc: "C \<in> carrier_mat (CARD('m)) (CARD('n))"
      using C by blast
    show "A + B + C = A + (B + C)"
      using Ac Bc Cc by (intro eq_matI) (auto simp: ac_simps)
  qed
qed

instance lmat :: (ab_semigroup_add, finite, finite) ab_semigroup_add
proof
  fix a b :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "a + b = b + a"
  proof (transfer)
    fix A B :: "'a Matrix.mat"
    assume "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
       and "dim_row B = CARD('m) \<and> dim_col B = CARD('n)"
    then have "A \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
       and "B \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
      by simp_all
    hence "A \<in> carrier_mat (CARD('m)) (CARD('n))"
          "B \<in> carrier_mat (CARD('m)) (CARD('n))"
      by auto 
    thus "A + B = B + A" by (intro eq_matI) (auto simp: ac_simps)
  qed
qed

instance lmat :: (monoid_add, finite, finite) monoid_add
proof
  fix a :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "0 + a = a"
  proof (transfer)
    fix A :: "'a Matrix.mat"
    assume "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
    then have "A \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
      by simp
    hence Ac: "A \<in> carrier_mat (CARD('m)) (CARD('n))" by auto
    show "0\<^sub>m (CARD('m)) (CARD('n)) + A = A"
      using Ac by simp
  qed
  show "a + 0 = a"
  proof (transfer)
    fix A :: "'a Matrix.mat"
    assume "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
    then have "A \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
      by simp
    hence Ac: "A \<in> carrier_mat (CARD('m)) (CARD('n))" by auto
    show "A + 0\<^sub>m (CARD('m)) (CARD('n)) = A"
      using Ac by simp
  qed
qed

instance lmat :: (comm_monoid_add, finite, finite) comm_monoid_add
proof
  fix a :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "0 + a = a" by simp
qed

instance lmat :: (group_add, finite, finite) group_add
proof
  fix a b :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "- a + a = 0"
  proof (transfer)
    fix A :: "'a Matrix.mat"
    assume "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
    then have "A \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
      by simp
    hence Ac: "A \<in> carrier_mat (CARD('m)) (CARD('n))" by auto
    show "- A + A = 0\<^sub>m (CARD('m)) (CARD('n))"
      using Ac by (intro eq_matI) (auto simp: minus_mat_def uminus_mat_def)
  qed
  show "a + - b = a - b"
  proof (transfer)
    fix A B :: "'a Matrix.mat"
    assume "dim_row A = CARD('m) \<and> dim_col A = CARD('n)"
       and "dim_row B = CARD('m) \<and> dim_col B = CARD('n)"
    then have "A \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
       and "B \<in> {M. dim_row M = CARD('m) \<and> dim_col M = CARD('n)}"
      by simp_all
    hence Ac: "A \<in> carrier_mat (CARD('m)) (CARD('n))"
          and Bc: "B \<in> carrier_mat (CARD('m)) (CARD('n))" by auto
    show "A + - B = A - B"
      using Ac Bc by (intro eq_matI) (auto simp: minus_mat_def uminus_mat_def plus_mat_def)
  qed
qed

instance lmat :: (ab_group_add, finite, finite) ab_group_add
proof
  fix a b :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "- a + a = 0" by (rule left_minus)
  show "a - b = a + - b" by (rule diff_conv_add_uminus)
qed


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
  "vectorspace (UNIV :: (complex, 'm :: finite, 'n :: finite) lmat set)"
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

end