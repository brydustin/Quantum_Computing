theory Topology_Bridge
  imports
    "HOL-Analysis.Analysis"
    Munkres_Topology_Local.Munkres_Topology
begin

section \<open>Bridge to the Munkres-Style Topology API\<close>

text \<open>
  This theory keeps the topology-language mismatch local.

  The applied-math development is written in the standard HOL-Analysis style,
  while the vendored Munkres formalization uses explicit carriers and families
  of open sets. The lemmas below are the small translation layer needed for the
  Baire-category closeout.
\<close>

lemma munkres_subspace_open_iff:
  fixes S U :: "'a::topological_space set"
  shows "U \<in> subspace_topology UNIV top1_open_sets S \<longleftrightarrow> openin (top_of_set S) U"
  by (auto simp: subspace_topology_def top1_open_sets_def openin_subtopology)

lemma openin_top_of_set_imp_open:
  fixes S U :: "'a::topological_space set"
  assumes "open S" and "openin (top_of_set S) U"
  shows "open U"
  using assms by (auto simp: openin_subtopology)

lemma top1_densein_on_UNIV_top1_open_sets_imp_subset_closure:
  fixes A :: "'a::topological_space set"
  assumes hD: "top1_densein_on UNIV top1_open_sets A"
  shows "UNIV \<subseteq> closure A"
proof
  fix x :: 'a
  have hTop: "is_topology_on (UNIV::'a set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hInt:
    "\<forall>U. neighborhood_of x UNIV top1_open_sets U \<longrightarrow> intersects U A"
    using hD by (simp add: Theorem_17_5a[OF hTop, of x A] top1_densein_on_def,
                 metis Theorem_17_5a UNIV_I hTop top_greatest)
  show "x \<in> closure A"
  proof (rule ccontr)
    assume hx: "x \<notin> closure A"
    have hOpen: "open (UNIV - closure A)"
      by blast

    have hN: "neighborhood_of x UNIV top1_open_sets (UNIV - closure A)"
      unfolding neighborhood_of_def top1_open_sets_def
      using hOpen hx by auto
    have "intersects (UNIV - closure A) A"
      using hInt hN by blast
    then show False
      unfolding intersects_def
      by (metis Diff_disjoint hOpen inf_commute open_Int_closure_eq_empty) 
  qed
qed

lemma top1_baire_on_UNIV_top1_open_sets:
  fixes T :: "'a::{real_normed_vector,heine_borel} set"
  shows "top1_baire_on (UNIV::'a set) top1_open_sets"
proof -
  have hTop: "is_topology_on (UNIV::'a set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  show ?thesis
    unfolding top1_baire_on_def
  proof (intro allI impI)
    fix U :: "nat \<Rightarrow> 'a set"
    assume hU: "\<forall>n. U n \<in> top1_open_sets \<and> top1_densein_on UNIV top1_open_sets (U n)"

    have hU_open: "\<forall>n. open (U n)"
      using hU by (auto simp: top1_open_sets_def)
    have hU_dense: "\<forall>n. UNIV \<subseteq> closure (U n)"
      using hU top1_densein_on_UNIV_top1_open_sets_imp_subset_closure by blast

    let ?G = "range U"

    have hBaire_std: "UNIV \<subseteq> closure (\<Inter>n. U n)"
    proof -
      have hG_countable: "countable ?G"
        by (meson Top1_Ch3.countable_def dual_order.refl inj_on_inv_into)

      have hG_props:
        "\<And>T. T \<in> ?G \<Longrightarrow> openin (top_of_set (UNIV::'a set)) T \<and> UNIV \<subseteq> closure T"
      proof -
        fix T assume "T \<in> ?G"
        then obtain n where "T = U n"
          by blast
        then show "openin (top_of_set (UNIV::'a set)) T \<and> UNIV \<subseteq> closure T"
          using hU_open hU_dense by simp
      qed

      have hBaire_range:
        "(UNIV::'a set) \<subseteq> closure (Inter ?G)"
      proof (rule Baire)
        show "closed (UNIV::'a set)"
          by simp
        show "Countable_Set.countable (range U)"
          by blast
        show "\<And>T. T \<in> ?G \<Longrightarrow>
          openin (top_of_set (UNIV::'a set)) T \<and>
          (UNIV::'a set) \<subseteq> closure T"
          using hG_props by blast
      qed

      have "Inter ?G = (\<Inter>n. U n)"
        by auto
      then show ?thesis
        using hBaire_range by simp
    qed

    have hInter_dense:
      "top1_densein_on UNIV top1_open_sets (\<Inter>n. U n)"
    proof (rule iffD2[OF top1_densein_on_iff_intersects_nonempty_open[OF hTop]])
      show "(\<Inter>n. U n) \<subseteq> (UNIV::'a set)"
        by simp
      show "\<forall>V. V \<in> top1_open_sets \<and> V \<subseteq> UNIV \<and> V \<noteq> {}
          \<longrightarrow> intersects V (\<Inter>n. U n)"
      proof (intro allI impI)
        fix V :: "'a set"
        assume hV: "V \<in> top1_open_sets \<and> V \<subseteq> UNIV \<and> V \<noteq> {}"
        have hV_open: "open V"
          using hV by (simp add: top1_open_sets_def)
        obtain x where hxV: "x \<in> V"
          using hV by blast
        have hxcl: "x \<in> closure (\<Inter>n. U n)"
          using hBaire_std by blast
        have "V \<inter> (\<Inter>n. U n) \<noteq> {}"
        proof
          assume hEmpty: "V \<inter> (\<Inter>n. U n) = {}"
          then have "V \<inter> closure (\<Inter>n. U n) = {}"
            using open_Int_closure_eq_empty[OF hV_open, of "\<Inter>n. U n"] by simp
          then show False
            using hxV hxcl by blast
        qed
        then show "intersects V (\<Inter>n. U n)"
          unfolding intersects_def by blast
      qed
    qed

    show "top1_densein_on UNIV top1_open_sets (\<Inter>n. U n)"
      by (rule hInter_dense)
  qed
qed

lemma top1_baire_on_open_subspace:
  fixes U :: "'a::{real_normed_vector,heine_borel} set"
  assumes "open U"
  shows "top1_baire_on U (subspace_topology UNIV top1_open_sets U)"
proof -
  have hTop: "is_topology_on (UNIV::'a set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hB: "top1_baire_on (UNIV::'a set) top1_open_sets"
    by (rule top1_baire_on_UNIV_top1_open_sets)
  have hU_mem: "U \<in> top1_open_sets"
    using assms by (simp add: top1_open_sets_def)
  show ?thesis
    by (rule Lemma_48_4[OF hTop hB]) (use hU_mem in auto)
qed

lemma top1_baire_dense_open_intersects_nonempty_open:
  fixes S W :: "'a set"
    and TS :: "'a set set"
    and D :: "nat \<Rightarrow> 'a set"
  assumes hTop: "is_topology_on S TS"
    and hB: "top1_baire_on S TS"
    and hW: "W \<in> TS" "W \<subseteq> S" "W \<noteq> {}"
    and hD: "\<forall>n. D n \<in> TS \<and> D n \<subseteq> S \<and> top1_densein_on S TS (D n)"
  shows "intersects W (\<Inter>n. D n)"
proof -
  have hInter_dense: "top1_densein_on S TS (\<Inter>n. D n)"
    using hB hD unfolding top1_baire_on_def by blast
  have hInter_sub: "(\<Inter>n. D n) \<subseteq> S"
    using hD by auto
  show ?thesis
    using hW hInter_dense
    using hTop top1_densein_on_intersects_nonempty_open by blast
qed

end
