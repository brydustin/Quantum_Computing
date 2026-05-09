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

end
