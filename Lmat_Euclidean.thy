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


end
