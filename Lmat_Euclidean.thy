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


end
