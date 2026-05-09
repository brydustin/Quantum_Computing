(*
  Title:    Lmat_Euclidean.thy
  Purpose:  Equip the typed-dimension matrix wrapper lmat with the
            HOL-Analysis typeclass tower:
              real_vector \<subseteq> real_normed_vector \<subseteq> real_inner
              \<subseteq> euclidean_space \<subseteq> heine_borel.

  Status:   Stage 1 (real_vector) is complete and verified to build.
            The remaining instances (real_normed_vector, real_inner,
            euclidean_space, heine_borel) are work-in-progress; they
            will be added in subsequent commits, each independently
            verified to build clean before being committed.
*)

theory Lmat_Euclidean
  imports
    Matrix_Typed
    "HOL-Analysis.Euclidean_Space"
    "HOL-Analysis.L2_Norm"
    "HOL-Analysis.Elementary_Metric_Spaces"
    "HOL-Analysis.Topology_Euclidean_Space"
begin

text \<open>The HOL/Hahn_Banach development imports a locale also called \<open>norm\<close>
under the qualifier \<open>Normed_Space\<close>.  Hide its short names so that, inside
our instantiation blocks, \<open>norm\<close> resolves to the class method from
\<^theory>\<open>HOL.Real_Vector_Spaces\<close>.\<close>

hide_const (open) Normed_Space.norm
hide_const (open) Normed_Space.seminorm


section \<open>Real scalar multiplication and \<open>real_vector\<close> instance\<close>

text \<open>For \<open>'a :: real_vector\<close>, lift element-wise scalar multiplication
via \<open>map_mat (scaleR a)\<close>.\<close>

instantiation lmat :: (real_vector, finite, finite) scaleR
begin

lift_definition scaleR_lmat ::
  "real \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat"
  is "\<lambda>r M. map_mat (\<lambda>x. r *\<^sub>R x) M" by simp

instance ..

end

lemma unwrap_lm_scaleR [simp]:
  "unwrap_lm ((r :: real) *\<^sub>R (M :: ('a :: real_vector, 'm :: finite, 'n :: finite) lmat))
     = map_mat (\<lambda>x. r *\<^sub>R x) (unwrap_lm M)"
  by transfer simp

lemma unwrap_lm_scaleR_index [simp]:
  fixes M :: "('a :: real_vector, 'm :: finite, 'n :: finite) lmat"
  assumes "i < CARD('m)" "j < CARD('n)"
  shows "unwrap_lm (r *\<^sub>R M) $$ (i, j) = r *\<^sub>R (unwrap_lm M $$ (i, j))"
  using assms by (simp add: index_map_mat)

instance lmat :: (real_vector, finite, finite) real_vector
proof
  fix a b :: real
  fix x y :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y"
    apply transfer
    apply (rule eq_matI)
       apply (auto simp: scaleR_right_distrib)
    done
  show "(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x"
    apply transfer
    apply (rule eq_matI)
       apply (auto simp: scaleR_left_distrib)
    done
  show "a *\<^sub>R (b *\<^sub>R x) = (a * b) *\<^sub>R x"
    apply transfer
    apply (rule eq_matI)
       apply auto
    done
  show "1 *\<^sub>R x = x"
    apply transfer
    apply (rule eq_matI)
       apply auto
    done
qed


section \<open>Auxiliary: pointwise unwrapping (used by later instances)\<close>

lemma unwrap_lm_plus_index [simp]:
  fixes M N :: "('a :: plus, 'm :: finite, 'n :: finite) lmat"
  assumes "i < CARD('m)" "j < CARD('n)"
  shows "unwrap_lm (M + N) $$ (i, j) = unwrap_lm M $$ (i, j) + unwrap_lm N $$ (i, j)"
  using assms by (simp add: index_add_mat)

lemma unwrap_lm_minus_index [simp]:
  fixes M N :: "('a :: ab_group_add, 'm :: finite, 'n :: finite) lmat"
  assumes "i < CARD('m)" "j < CARD('n)"
  shows "unwrap_lm (M - N) $$ (i, j) = unwrap_lm M $$ (i, j) - unwrap_lm N $$ (i, j)"
  using assms by (simp add: index_minus_mat)

lemma unwrap_lm_zero_index [simp]:
  fixes i j :: nat
  assumes "i < CARD('m :: finite)" "j < CARD('n :: finite)"
  shows "unwrap_lm (0 :: ('a :: zero, 'm, 'n) lmat) $$ (i, j) = 0"
  using assms by simp

lemma lmat_eq_iff_entries:
  fixes M N :: "('a, 'm :: finite, 'n :: finite) lmat"
  shows "M = N \<longleftrightarrow>
         (\<forall>i j. i < CARD('m) \<longrightarrow> j < CARD('n)
                 \<longrightarrow> unwrap_lm M $$ (i, j) = unwrap_lm N $$ (i, j))"
proof
  assume "M = N" thus "\<forall>i j. i < CARD('m) \<longrightarrow> j < CARD('n)
            \<longrightarrow> unwrap_lm M $$ (i, j) = unwrap_lm N $$ (i, j)" by simp
next
  assume *: "\<forall>i j. i < CARD('m) \<longrightarrow> j < CARD('n)
              \<longrightarrow> unwrap_lm M $$ (i, j) = unwrap_lm N $$ (i, j)"
  have "unwrap_lm M = unwrap_lm N"
    by (rule eq_matI) (use * in auto)
  thus "M = N" by (metis unwrap_lm_inverse)
qed


section \<open>Distance, uniformity, open: \<open>metric_space\<close> instance\<close>

text \<open>Distance is the L2 sum of entry-wise distances, indexed by
\<open>{0..<CARD('m)} \<times> {0..<CARD('n)}\<close>.  Uniformity and \<open>open\<close> are
defined via the standard metric-induced filter so that the
\<open>open_uniformity\<close> axiom is discharged by reflexivity.\<close>

instantiation lmat :: (metric_space, finite, finite) dist
begin

definition dist_lmat :: "('a, 'm :: finite, 'n :: finite) lmat
                      \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real" where
  "dist_lmat M N = L2_set (\<lambda>(i, j). dist (unwrap_lm M $$ (i, j)) (unwrap_lm N $$ (i, j)))
                          ({0..<CARD('m)} \<times> {0..<CARD('n)})"

instance ..

end

instantiation lmat :: (metric_space, finite, finite) uniformity_dist
begin

definition uniformity_lmat ::
  "(('a, 'm :: finite, 'n :: finite) lmat \<times> ('a, 'm, 'n) lmat) filter" where
  "(uniformity_lmat :: (('a, 'm, 'n) lmat \<times> ('a, 'm, 'n) lmat) filter)
     = (INF e \<in> {0<..}. principal {(x, y). dist x y < e})"

instance by standard (rule uniformity_lmat_def)

end

instantiation lmat :: (metric_space, finite, finite) metric_space
begin

definition open_lmat :: "('a, 'm :: finite, 'n :: finite) lmat set \<Rightarrow> bool" where
  "open_lmat U = (\<forall>x \<in> U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"

instance proof
  fix x y :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "(dist x y = 0) = (x = y)"
    unfolding dist_lmat_def
    by (auto simp: L2_set_eq_0_iff lmat_eq_iff_entries split: prod.split)
next
  fix x y z :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_lmat_def
    apply (rule order_trans [OF _ L2_set_triangle_ineq])
    apply (rule L2_set_mono)
     apply (auto simp: dist_triangle2)
    done
next
  fix S :: "('a, 'm :: finite, 'n :: finite) lmat set"
  show "open S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"
    by (rule open_lmat_def)
qed

end


section \<open>Norm and \<open>real_normed_vector\<close> instance\<close>

instantiation lmat :: (real_normed_vector, finite, finite) real_normed_vector
begin

definition norm_lmat :: "('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real" where
  "norm_lmat M = L2_set (\<lambda>(i, j). norm (unwrap_lm M $$ (i, j)))
                        ({0..<CARD('m)} \<times> {0..<CARD('n)})"

definition sgn_lmat ::
  "('a, 'm :: finite, 'n :: finite) lmat \<Rightarrow> ('a, 'm, 'n) lmat" where
  "sgn_lmat (M :: ('a, 'm, 'n) lmat) = scaleR (inverse (norm M)) M"

instance proof
  fix a :: real
  fix x y :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_lmat_def
    by (auto simp: L2_set_eq_0_iff lmat_eq_iff_entries split: prod.split)
  show "norm (x + y) \<le> norm x + norm y"
    unfolding norm_lmat_def
    apply (rule order_trans [OF _ L2_set_triangle_ineq])
    apply (rule L2_set_mono)
     apply (auto simp: norm_triangle_ineq)
    done
  show "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x"
  proof -
    have eq1: "L2_set (\<lambda>(i, j). norm (unwrap_lm (a *\<^sub>R x) $$ (i, j)))
                      ({0..<CARD('m)} \<times> {0..<CARD('n)})
             = L2_set (\<lambda>(i, j). \<bar>a\<bar> * norm (unwrap_lm x $$ (i, j)))
                      ({0..<CARD('m)} \<times> {0..<CARD('n)})"
    proof (rule L2_set_cong [OF refl])
      fix p :: "nat \<times> nat"
      assume p_in: "p \<in> {0..<CARD('m)} \<times> {0..<CARD('n)}"
      obtain i j where p_eq: "p = (i, j)" by (cases p)
      from p_in p_eq have ij: "i < CARD('m)" "j < CARD('n)" by auto
      show "(case p of (i, j) \<Rightarrow> norm (unwrap_lm (a *\<^sub>R x) $$ (i, j)))
            = (case p of (i, j) \<Rightarrow> \<bar>a\<bar> * norm (unwrap_lm x $$ (i, j)))"
        unfolding p_eq prod.case
        by (simp add: ij)
    qed
    have eq2: "L2_set (\<lambda>(i, j). \<bar>a\<bar> * norm (unwrap_lm x $$ (i, j)))
                      ({0..<CARD('m)} \<times> {0..<CARD('n)})
             = \<bar>a\<bar> * L2_set (\<lambda>(i, j). norm (unwrap_lm x $$ (i, j)))
                            ({0..<CARD('m)} \<times> {0..<CARD('n)})"
    proof -
      have "L2_set (\<lambda>(i, j). \<bar>a\<bar> * norm (unwrap_lm x $$ (i, j)))
                   ({0..<CARD('m)} \<times> {0..<CARD('n)})
          = L2_set (\<lambda>p. \<bar>a\<bar> * (\<lambda>(i, j). norm (unwrap_lm x $$ (i, j))) p)
                   ({0..<CARD('m)} \<times> {0..<CARD('n)})"
        by (rule L2_set_cong [OF refl]) (auto split: prod.split)
      also have "\<dots> = \<bar>a\<bar> * L2_set (\<lambda>(i, j). norm (unwrap_lm x $$ (i, j)))
                                   ({0..<CARD('m)} \<times> {0..<CARD('n)})"
        by (subst L2_set_right_distrib[symmetric]) auto
      finally show ?thesis .
    qed
    show ?thesis using eq1 eq2 unfolding norm_lmat_def by simp
  qed
  show "sgn x = scaleR (inverse (norm x)) x"
    by (rule sgn_lmat_def)
  show "dist x y = norm (x - y)"
    unfolding dist_lmat_def norm_lmat_def
    by (rule L2_set_cong) (auto simp: dist_norm split: prod.split)
qed

end


section \<open>Real inner product\<close>

text \<open>For \<open>'a :: real_inner\<close>, the lmat inner product is the entry-wise
sum of inner products.  When \<open>'a = complex\<close> with the standard real-inner
instance \<open>inner z w = Re (cnj z * w)\<close>, this is the real part of the
Hilbert-Schmidt inner product.\<close>

instantiation lmat :: (real_inner, finite, finite) real_inner
begin

definition inner_lmat :: "('a, 'm :: finite, 'n :: finite) lmat
                        \<Rightarrow> ('a, 'm, 'n) lmat \<Rightarrow> real" where
  "inner_lmat M N = (\<Sum>(i, j) \<in> {0..<CARD('m)} \<times> {0..<CARD('n)}.
                       inner (unwrap_lm M $$ (i, j)) (unwrap_lm N $$ (i, j)))"

instance proof
  fix r :: real
  fix x y z :: "('a, 'm :: finite, 'n :: finite) lmat"
  show "inner x y = inner y x"
    unfolding inner_lmat_def by (simp add: inner_commute split: prod.split)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_lmat_def
    apply (subst sum.distrib[symmetric])
    apply (rule sum.cong, simp)
    apply (auto simp: inner_add_left split: prod.split)
    done
  show "inner (r *\<^sub>R x) y = r * inner x y"
    unfolding inner_lmat_def
    apply (subst sum_distrib_left)
    apply (rule sum.cong, simp)
    apply (auto split: prod.split)
    done
  show "0 \<le> inner x x"
    unfolding inner_lmat_def
    by (auto intro!: sum_nonneg split: prod.split)
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_lmat_def
    by (auto simp: sum_nonneg_eq_0_iff lmat_eq_iff_entries split: prod.split)
  show "norm x = sqrt (inner x x)"
    unfolding inner_lmat_def norm_lmat_def L2_set_def
    by (simp add: power2_norm_eq_inner split: prod.split)
qed

end


section \<open>Basis: matrix units carrying a basis vector\<close>

definition lmat_axis :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: zero
                       \<Rightarrow> ('a, 'm :: finite, 'n :: finite) lmat" where
  "lmat_axis i j u = wrap_lm (Matrix.mat (CARD('m)) (CARD('n))
                              (\<lambda>(r, s). if r = i \<and> s = j then u else 0))"

lemma unwrap_lmat_axis [simp]:
  "unwrap_lm (lmat_axis i j u :: ('a :: zero, 'm :: finite, 'n :: finite) lmat)
     = Matrix.mat (CARD('m)) (CARD('n))
                   (\<lambda>(r, s). if r = i \<and> s = j then u else 0)"
  unfolding lmat_axis_def by (subst wrap_lm_inverse) auto

lemma lmat_axis_index [simp]:
  fixes u :: "'a :: zero"
  assumes "r < CARD('m :: finite)" "s < CARD('n :: finite)"
  shows "unwrap_lm (lmat_axis i j u :: ('a, 'm, 'n) lmat) $$ (r, s)
           = (if r = i \<and> s = j then u else 0)"
  using assms by simp


text \<open>Inner product against a single matrix-unit basis vector picks out
one matrix entry.\<close>

lemma inner_lmat_axis:
  fixes u :: "'a :: real_inner"
    and M :: "('a, 'm :: finite, 'n :: finite) lmat"
  assumes ij: "i < CARD('m)" "j < CARD('n)"
  shows "inner M (lmat_axis i j u :: ('a, 'm, 'n) lmat)
           = inner (unwrap_lm M $$ (i, j)) u"
proof -
  let ?S = "{0..<CARD('m)} \<times> {0..<CARD('n)}"
  have ij_mem: "(i, j) \<in> ?S" using ij by auto
  have step: "inner M (lmat_axis i j u :: ('a, 'm, 'n) lmat)
            = (\<Sum>p \<in> ?S. (if p = (i, j) then inner (unwrap_lm M $$ (i, j)) u else 0))"
    unfolding inner_lmat_def
  proof (rule sum.cong, simp)
    fix p assume p_in: "p \<in> ?S"
    obtain r s where p_eq: "p = (r, s)" by (cases p)
    from p_in p_eq have rs: "r < CARD('m)" "s < CARD('n)" by auto
    show "(case p of (k, l) \<Rightarrow> inner (unwrap_lm M $$ (k, l))
                          (unwrap_lm (lmat_axis i j u :: ('a, 'm, 'n) lmat) $$ (k, l)))
        = (if p = (i, j) then inner (unwrap_lm M $$ (i, j)) u else 0)"
    proof (cases "(r, s) = (i, j)")
      case True
      hence r_eq: "r = i" and s_eq: "s = j" by auto
      show ?thesis
        unfolding p_eq prod.case r_eq s_eq
        using ij by simp
    next
      case False
      hence cond: "\<not> (r = i \<and> s = j)" by auto
      have ax_form: "unwrap_lm (lmat_axis i j u :: ('a, 'm, 'n) lmat) $$ (r, s)
                   = (if r = i \<and> s = j then u else 0)"
        using rs by simp
      have ax0: "unwrap_lm (lmat_axis i j u :: ('a, 'm, 'n) lmat) $$ (r, s) = 0"
        using ax_form cond by simp
      show ?thesis unfolding p_eq prod.case
        using ax0 False cond by force
    qed
  qed
  also have "\<dots> = inner (unwrap_lm M $$ (i, j)) u"
    using ij_mem by (subst sum.delta) auto
  finally show ?thesis .
qed


text \<open>Two matrix-unit basis vectors are equal iff their entries and
positions match (or both vectors are zero).\<close>

lemma lmat_axis_eq_iff:
  fixes u v :: "'a :: zero"
  assumes "i < CARD('m :: finite)" "j < CARD('n :: finite)"
      and "i' < CARD('m)" "j' < CARD('n)"
  shows "(lmat_axis i j u :: ('a, 'm, 'n) lmat) = lmat_axis i' j' v
           \<longleftrightarrow> (u = v \<and> i = i' \<and> j = j') \<or> (u = 0 \<and> v = 0)"
proof
  assume eq: "(lmat_axis i j u :: ('a, 'm, 'n) lmat) = lmat_axis i' j' v"
  show "(u = v \<and> i = i' \<and> j = j') \<or> (u = 0 \<and> v = 0)"
  proof (cases "u = 0 \<and> v = 0")
    case True thus ?thesis by simp
  next
    case False
    have h1: "unwrap_lm (lmat_axis i j u :: ('a, 'm, 'n) lmat) $$ (i, j)
            = unwrap_lm (lmat_axis i' j' v :: ('a, 'm, 'n) lmat) $$ (i, j)"
      using eq by simp
    have h2: "unwrap_lm (lmat_axis i j u :: ('a, 'm, 'n) lmat) $$ (i', j')
            = unwrap_lm (lmat_axis i' j' v :: ('a, 'm, 'n) lmat) $$ (i', j')"
      using eq by simp
    show ?thesis using h1 h2 assms False
      by (auto split: if_split_asm)
  qed
next
  assume "(u = v \<and> i = i' \<and> j = j') \<or> (u = 0 \<and> v = 0)"
  thus "(lmat_axis i j u :: ('a, 'm, 'n) lmat) = lmat_axis i' j' v"
    apply (elim disjE)
     apply simp
    apply (subst lmat_eq_iff_entries)
    apply auto
    done
qed


text \<open>Inner product between two matrix-unit basis vectors: 1 if same
position and basis component, 0 otherwise.\<close>

lemma inner_lmat_axis_axis:
  fixes u v :: "'a :: real_inner"
  assumes ij: "i < CARD('m :: finite)" "j < CARD('n :: finite)"
      and ij': "i' < CARD('m)" "j' < CARD('n)"
  shows "inner (lmat_axis i j u :: ('a, 'm, 'n) lmat) (lmat_axis i' j' v)
           = (if i = i' \<and> j = j' then inner u v else 0)"
proof -
  have "inner (lmat_axis i j u :: ('a, 'm, 'n) lmat) (lmat_axis i' j' v)
      = inner (unwrap_lm (lmat_axis i j u :: ('a, 'm, 'n) lmat) $$ (i', j')) v"
    using inner_lmat_axis[OF ij'] .
  also have "\<dots> = inner (if i' = i \<and> j' = j then u else 0) v"
    using ij' by simp
  also have "\<dots> = (if i' = i \<and> j' = j then inner u v else 0)"
    by (cases "i' = i \<and> j' = j") auto
  also have "\<dots> = (if i = i' \<and> j = j' then inner u v else 0)"
    by (cases "i = i' \<and> j = j'") auto
  finally show ?thesis .
qed


section \<open>Basis set\<close>

definition Basis_lmat_set :: "('a :: euclidean_space, 'm :: finite, 'n :: finite) lmat set"
  where "Basis_lmat_set = (\<Union>i \<in> {0..<CARD('m)}.
                            \<Union>j \<in> {0..<CARD('n)}.
                              \<Union>u \<in> Basis. {lmat_axis i j u :: ('a, 'm, 'n) lmat})"

lemma Basis_lmat_set_finite:
  "finite (Basis_lmat_set :: ('a :: euclidean_space, 'm :: finite, 'n :: finite) lmat set)"
  unfolding Basis_lmat_set_def by simp

lemma Basis_lmat_set_nonempty:
  "Basis_lmat_set \<noteq> ({} :: ('a :: euclidean_space, 'm :: finite, 'n :: finite) lmat set)"
proof -
  obtain u :: 'a where uB: "u \<in> Basis"
    using nonempty_Basis[where 'a = 'a] by blast
  have m_pos: "(0 :: nat) < CARD('m)" by simp
  have n_pos: "(0 :: nat) < CARD('n)" by simp
  have mem: "(0 :: nat) \<in> {0..<CARD('m)}" using m_pos by simp
  have nmem: "(0 :: nat) \<in> {0..<CARD('n)}" using n_pos by simp
  have step1: "(lmat_axis 0 0 u :: ('a, 'm, 'n) lmat)
              \<in> (\<Union>u' \<in> Basis. {lmat_axis (0 :: nat) (0 :: nat) u' :: ('a, 'm, 'n) lmat})"
    using uB by blast
  have step2: "(lmat_axis 0 0 u :: ('a, 'm, 'n) lmat)
              \<in> (\<Union>j \<in> {0..<CARD('n)}. \<Union>u' \<in> Basis. {lmat_axis (0 :: nat) j u' :: ('a, 'm, 'n) lmat})"
    using step1 nmem by blast
  have step3: "(lmat_axis 0 0 u :: ('a, 'm, 'n) lmat) \<in> Basis_lmat_set"
    using step2 mem unfolding Basis_lmat_set_def by blast
  thus ?thesis by blast
qed

lemma Basis_lmat_orthonormal:
  fixes u v :: "('a :: euclidean_space, 'm :: finite, 'n :: finite) lmat"
  assumes uB: "u \<in> Basis_lmat_set" and vB: "v \<in> Basis_lmat_set"
  shows "inner u v = (if u = v then 1 else 0)"
proof -
  from uB obtain i j a where u_eq: "u = lmat_axis i j a"
                       and ij: "i < CARD('m)" "j < CARD('n)"
                       and aB: "a \<in> Basis"
    unfolding Basis_lmat_set_def by auto
  from vB obtain i' j' b where v_eq: "v = lmat_axis i' j' b"
                       and ij': "i' < CARD('m)" "j' < CARD('n)"
                       and bB: "b \<in> Basis"
    unfolding Basis_lmat_set_def by auto
  have a0: "a \<noteq> 0" using aB by (rule nonzero_Basis)
  have b0: "b \<noteq> 0" using bB by (rule nonzero_Basis)
  have eq_iff: "(lmat_axis i j a :: ('a, 'm, 'n) lmat) = lmat_axis i' j' b
              \<longleftrightarrow> (a = b \<and> i = i' \<and> j = j')"
    using lmat_axis_eq_iff[OF ij ij'] a0 b0 by auto
  have axx: "inner (lmat_axis i j a :: ('a, 'm, 'n) lmat) (lmat_axis i' j' b)
           = (if i = i' \<and> j = j' then inner a b else 0)"
    using inner_lmat_axis_axis[OF ij ij'] .
  show ?thesis
    unfolding u_eq v_eq
  proof (cases "i = i' \<and> j = j'")
    case True
    have lhs: "inner (lmat_axis i j a :: ('a, 'm, 'n) lmat) (lmat_axis i' j' b)
             = (if a = b then 1 else 0)"
      using axx inner_Basis[OF aB bB] True by simp
    have rhs: "(if (lmat_axis i j a :: ('a, 'm, 'n) lmat) = lmat_axis i' j' b
                then (1 :: real) else 0) = (if a = b then 1 else 0)"
      using eq_iff True by simp
    show "inner (lmat_axis i j a :: ('a, 'm, 'n) lmat) (lmat_axis i' j' b)
        = (if (lmat_axis i j a :: ('a, 'm, 'n) lmat) = lmat_axis i' j' b
           then 1 else 0)"
      using lhs rhs by simp
  next
    case False
    hence lhs: "inner (lmat_axis i j a :: ('a, 'm, 'n) lmat) (lmat_axis i' j' b) = 0"
      using axx by force
    have ne: "(lmat_axis i j a :: ('a, 'm, 'n) lmat) \<noteq> lmat_axis i' j' b"
      using False eq_iff by auto
    show "inner (lmat_axis i j a :: ('a, 'm, 'n) lmat) (lmat_axis i' j' b)
        = (if (lmat_axis i j a :: ('a, 'm, 'n) lmat) = lmat_axis i' j' b
           then 1 else 0)"
      using lhs ne by simp
  qed
qed

lemma axis_mem_Basis_lmat_set:
  fixes u :: "'a :: euclidean_space"
  assumes i_lt: "i < CARD('m :: finite)"
      and j_lt: "j < CARD('n :: finite)"
      and uB: "u \<in> Basis"
  shows "(lmat_axis i j u :: ('a, 'm, 'n) lmat) \<in> Basis_lmat_set"
proof -
  have mem_i: "i \<in> {0..<CARD('m)}" using i_lt by simp
  have mem_j: "j \<in> {0..<CARD('n)}" using j_lt by simp
  have step1: "(lmat_axis i j u :: ('a, 'm, 'n) lmat)
              \<in> (\<Union>u' \<in> Basis. {lmat_axis i j u' :: ('a, 'm, 'n) lmat})"
    using uB by blast
  have step2: "(lmat_axis i j u :: ('a, 'm, 'n) lmat)
              \<in> (\<Union>j' \<in> {0..<CARD('n)}.
                    \<Union>u' \<in> Basis. {lmat_axis i j' u' :: ('a, 'm, 'n) lmat})"
    using step1 mem_j by blast
  show ?thesis
    using step2 mem_i unfolding Basis_lmat_set_def by blast
qed


end
