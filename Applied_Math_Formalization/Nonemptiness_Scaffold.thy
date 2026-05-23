theory Nonemptiness_Scaffold
  imports Topology_Bridge Nonemptiness_Array_Factor
begin

section \<open>Topological Closeout for the Nonemptiness Proof\<close>

text \<open>
  This theory formalizes the topological backbone of the proof in
   \<open>Applied Math/nonemptiness_unified_singlefile_complete.tex\<close>.

  It is now \<^emph>\<open>locale-free and \<^theory_text>\<open>sorry\<close>-free\<close>: the configuration sets are ordinary
  function arguments rather than abstract locale parameters, and every lemma here
  is a genuine theorem. Concretely it provides:

  1. a self-contained \<open>meager\<close> / \<open>nowhere_dense\<close> API and the Baire fact that a
     nonempty open subset of a Euclidean space is not meager;
  2. the closeout lemma \<open>final_nonemptiness_from_bad_union\<close> and its end-to-end
     corollary \<open>nonemptiness_from_branches\<close>, which assemble the four meager bad
     strata into nonemptiness of a robust feasible set.

  The deep, branch-specific meagerness results remain to be proved against the
  \<^emph>\<open>concrete\<close> bad sets built from \<^const>\<open>array_factor\<close>; they are the explicit
  hypotheses of \<open>nonemptiness_from_branches\<close>, not hidden assumptions. The
  repository's existing quantum-computing sessions still contain active
  @{command sorry}s, so this development intentionally avoids importing that
  stack.
\<close>


section \<open>Basic Topological Infrastructure\<close>

definition nowhere_dense :: "'a::topological_space set \<Rightarrow> bool" where
  "nowhere_dense A \<longleftrightarrow> interior (closure A) = {}"

definition meager :: "'a::topological_space set \<Rightarrow> bool" where
  "meager A \<longleftrightarrow>
     (\<exists>E :: nat \<Rightarrow> 'a set. A \<subseteq> (\<Union>n. E n) \<and> (\<forall>n. nowhere_dense (E n)))"

lemma nowhere_dense_empty [simp]: "nowhere_dense ({} :: 'a::topological_space set)"
  by (simp add: nowhere_dense_def)

lemma meager_empty [simp]: "meager ({} :: 'a::topological_space set)"
  unfolding meager_def
  by (meson empty_subsetI nowhere_dense_empty) 

lemma meager_subset:
  fixes A B :: "'a::topological_space set"
  assumes "A \<subseteq> B" and "meager B"
  shows "meager A"
  using assms unfolding meager_def by blast

lemma nowhere_dense_Un:
  fixes A B :: "'a::topological_space set"
  assumes "nowhere_dense A" and "nowhere_dense B"
  shows "nowhere_dense (A \<union> B)"
  using assms
  by (simp add: interior_closed_Un_empty_interior nowhere_dense_def)

lemma meager_Un:
  fixes A B :: "'a::topological_space set"
  assumes "meager A" and "meager B"
  shows "meager (A \<union> B)"
proof -
  obtain E :: "nat \<Rightarrow> 'a set"
    where hE: "A \<subseteq> (\<Union>n. E n)" and hEn: "\<forall>n. nowhere_dense (E n)"
    using assms(1) unfolding meager_def by blast
  obtain F :: "nat \<Rightarrow> 'a set"
    where hF: "B \<subseteq> (\<Union>n. F n)" and hFn: "\<forall>n. nowhere_dense (F n)"
    using assms(2) unfolding meager_def by blast
  define G :: "nat \<Rightarrow> 'a set" where
    "G n = (if even n then E (n div 2) else F (n div 2))" for n
  have "(A \<union> B) \<subseteq> (\<Union>n. G n)"
  proof
    fix x assume "x \<in> A \<union> B"
    then show "x \<in> (\<Union>n. G n)"
    proof
      assume "x \<in> A"
      then obtain n where "x \<in> E n"
        using hE by blast
      then have "x \<in> G (2 * n)"
        by (simp add: G_def)
      then show "x \<in> (\<Union>n. G n)"
        by blast
    next
      assume "x \<in> B"
      then obtain n where "x \<in> F n"
        using hF by blast
      then have "x \<in> G (Suc (2 * n))"
        by (simp add: G_def)
      then show "x \<in> (\<Union>n. G n)"
        by blast
    qed
  qed
  moreover have "\<forall>n. nowhere_dense (G n)"
    using hEn hFn by (simp add: G_def)
  ultimately show ?thesis
    unfolding meager_def by blast
qed

lemma meager_Union_nat:
  fixes A :: "nat \<Rightarrow> 'a::topological_space set"
  assumes "\<And>n. meager (A n)"
  shows "meager (\<Union>n. A n)"
proof -
  have "\<forall>n. \<exists>E :: nat \<Rightarrow> 'a set.
      A n \<subseteq> (\<Union>m. E m) \<and> (\<forall>m. nowhere_dense (E m))"
    using assms unfolding meager_def by blast
  then obtain E :: "nat \<Rightarrow> nat \<Rightarrow> 'a set"
    where hE: "\<forall>n. A n \<subseteq> (\<Union>m. E n m) \<and> (\<forall>m. nowhere_dense (E n m))"
    by metis
  define F :: "nat \<Rightarrow> 'a set" where
    "F k = (case prod_decode k of (n, m) \<Rightarrow> E n m)" for k
  have "(\<Union>n. A n) \<subseteq> (\<Union>k. F k)"
  proof
    fix x assume "x \<in> (\<Union>n. A n)"
    then obtain n where hx: "x \<in> A n"
      by blast
    then obtain m where "x \<in> E n m"
      using hE by blast
    then have "x \<in> F (prod_encode (n, m))"
      by (simp add: F_def)
    then show "x \<in> (\<Union>k. F k)"
      by blast
  qed
  moreover have "\<forall>k. nowhere_dense (F k)"
    using hE by (auto simp: F_def split: prod.splits)
  ultimately show ?thesis
    unfolding meager_def by blast
qed

lemma open_nonempty_not_meager:
  fixes U :: "'a::{real_normed_vector,heine_borel} set"
  assumes "open U" and "U \<noteq> {}"
  shows "\<not> meager U"
proof
  assume hU_meager: "meager U"
  obtain E :: "nat \<Rightarrow> 'a set"
    where hCover: "U \<subseteq> (\<Union>n. E n)" and hND: "\<forall>n. nowhere_dense (E n)"
    using hU_meager unfolding meager_def by blast

  define D :: "nat \<Rightarrow> 'a set" where
    "D n = U - closure (E n)" for n

  have hTopU: "is_topology_on U (subspace_topology UNIV top1_open_sets U)"
    by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) simp
  have hBaireU: "top1_baire_on U (subspace_topology UNIV top1_open_sets U)"
    by (rule top1_baire_on_open_subspace[OF assms(1)])

  have hD_props:
    "\<forall>n. D n \<in> subspace_topology UNIV top1_open_sets U \<and>
         D n \<subseteq> U \<and>
         top1_densein_on U (subspace_topology UNIV top1_open_sets U) (D n)"
  proof
    fix n
    have hDn_open_sub:
      "D n \<in> subspace_topology UNIV top1_open_sets U"
      unfolding D_def
      by (auto simp: subspace_topology_def top1_open_sets_def)
    have hDn_sub: "D n \<subseteq> U"
      by (simp add: D_def)
    have hDn_dense:
      "top1_densein_on U (subspace_topology UNIV top1_open_sets U) (D n)"
    proof (rule iffD2[OF top1_densein_on_iff_intersects_nonempty_open[OF hTopU hDn_sub]])
      show "\<forall>W. W \<in> subspace_topology UNIV top1_open_sets U \<and> W \<subseteq> U \<and> W \<noteq> {}
          \<longrightarrow> intersects W (D n)"
      proof (intro allI impI)
        fix W
        assume hW: "W \<in> subspace_topology UNIV top1_open_sets U \<and> W \<subseteq> U \<and> W \<noteq> {}"
        have hW_openin: "openin (top_of_set U) W"
          using hW by (simp add: munkres_subspace_open_iff)
        have hW_open: "open W"
          by (rule openin_top_of_set_imp_open[OF assms(1) hW_openin])
        have hW_nonempty: "W \<noteq> {}"
          using hW by blast
        have hW_sub: "W \<subseteq> U"
          using hW by blast
        show "intersects W (D n)"
        proof (rule ccontr)
          assume "\<not> intersects W (D n)"
          then have hDisj: "W \<inter> D n = {}"
            unfolding intersects_def by blast
          have hW_closure: "W \<subseteq> closure (E n)"
            using hDisj hW_sub by (auto simp: D_def)
          then have "W \<subseteq> interior (closure (E n))"
            by (rule interior_maximal[OF _ hW_open])
          with hND hW_nonempty show False
            by (auto simp: nowhere_dense_def)
        qed
      qed
    qed
    show "D n \<in> subspace_topology UNIV top1_open_sets U \<and>
          D n \<subseteq> U \<and>
          top1_densein_on U (subspace_topology UNIV top1_open_sets U) (D n)"
      using hDn_open_sub hDn_sub hDn_dense by blast
  qed

  have "intersects U (\<Inter>n. D n)"
  proof (rule top1_baire_dense_open_intersects_nonempty_open[OF hTopU hBaireU])
    show "U \<in> subspace_topology UNIV top1_open_sets U"
      by (simp add: munkres_subspace_open_iff)
    show "U \<subseteq> U"
      by simp
    show "U \<noteq> {}"
      by (rule assms(2))
    show "\<forall>n. D n \<in> subspace_topology UNIV top1_open_sets U \<and>
          D n \<subseteq> U \<and> top1_densein_on U (subspace_topology UNIV top1_open_sets U) (D n)"
      by (rule hD_props)
  qed
  then obtain x where hxU: "x \<in> U" and hxD: "x \<in> (\<Inter>n. D n)"
    unfolding intersects_def by blast
  obtain n where hxEn: "x \<in> E n"
    using hCover hxU by blast
  have "x \<in> D n"
    using hxD by blast
  then have "x \<notin> closure (E n)"
    by (simp add: D_def)
  then show False
    using hxEn closure_subset by blast
qed


section \<open>Array-Factor Primitives\<close>

text \<open>
  The concrete radiation-pattern functions \<^const>\<open>array_factor\<close> and
  \<^const>\<open>power_pattern\<close>, together with the odd-\<open>N\<close> zero geometry, now live in
  \<^theory>\<open>Applied_Math_Nonemptiness.Nonemptiness_Array_Factor\<close>. The concrete
  configuration space used in the final proof should later be a finite-dimensional
  chart type, not a list type. Lists are convenient for the raw array-factor
  formulas, while the closeout below is kept abstract over a Baire-space
  configuration type.
\<close>


section \<open>Closeout Layer (locale-free)\<close>

text \<open>
  These objects used to live inside a locale. They are now plain definitions and
  lemmas: the configuration variables are ordinary function arguments, and every
  hypothesis is written out explicitly. Nothing here is a hidden assumption.

  \<^item> \<open>Fzero\<close> is the robust feasible set \<open>Fset \<inter> X0 \<xi>\<close>.
  \<^item> \<open>bad_union\<close> bundles the four bad strata.
  \<^item> \<open>final_nonemptiness_from_bad_union\<close> is the Baire closeout: if the bad
    union is meager inside a non-meager working set \<open>V \<subseteq> Fset\<close>, and every good
    point lies in some \<open>X0 \<xi>\<close>, then some \<open>Fzero \<xi>\<close> is nonempty.
\<close>

definition Fzero :: "'cfg set \<Rightarrow> (real \<Rightarrow> 'cfg set) \<Rightarrow> real \<Rightarrow> 'cfg set" where
  "Fzero Fset X0 \<xi> = Fset \<inter> X0 \<xi>"

definition bad_union ::
  "'cfg set \<Rightarrow> 'cfg set \<Rightarrow> 'cfg set \<Rightarrow> 'cfg set \<Rightarrow> 'cfg set" where
  "bad_union B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4 = B\<^sub>1 \<union> B\<^sub>2 \<union> B\<^sub>3 \<union> B\<^sub>4"

theorem final_nonemptiness_from_bad_union:
  fixes V Fset :: "'cfg::topological_space set"
    and X0 :: "real \<Rightarrow> 'cfg set"
    and B :: "'cfg set"
  assumes V_subset_Fset: "V \<subseteq> Fset"
    and V_not_meager: "\<not> meager V"
    and bad_meager: "meager (B \<inter> V)"
    and X0_sound: "\<And>x. x \<in> V - B \<Longrightarrow> \<exists>\<xi>>0. x \<in> X0 \<xi>"
  shows "\<exists>\<xi>>0. Fzero Fset X0 \<xi> \<noteq> {}"
proof -
  have "V - B \<noteq> {}"
  proof
    assume hEmpty: "V - B = {}"
    then have hSub: "V \<subseteq> B \<inter> V"
      by auto
    have "meager V"
      by (rule meager_subset[OF hSub bad_meager])
    with V_not_meager show False
      by contradiction
  qed
  then obtain x where hx: "x \<in> V - B"
    by blast
  then obtain \<xi> where hxi: "\<xi> > 0" and hxX0: "x \<in> X0 \<xi>"
    using X0_sound by blast
  have "x \<in> Fzero Fset X0 \<xi>"
    using hx hxX0 V_subset_Fset unfolding Fzero_def by blast
  then show ?thesis
    using hxi by blast
qed

text \<open>
  Meagerness of the bundled bad set follows from meagerness of the four branches
  by set algebra and \<open>meager_Un\<close>. This is now a genuine theorem with no
  \<^theory_text>\<open>sorry\<close>: it takes the four branch facts as explicit hypotheses.
\<close>

theorem bad_union_meagerness:
  fixes V B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4 :: "'cfg::topological_space set"
  assumes "meager (B\<^sub>1 \<inter> V)" and "meager (B\<^sub>2 \<inter> V)"
    and "meager (B\<^sub>3 \<inter> V)" and "meager (B\<^sub>4 \<inter> V)"
  shows "meager (bad_union B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4 \<inter> V)"
proof -
  have eq: "bad_union B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4 \<inter> V =
              ((B\<^sub>1 \<inter> V) \<union> (B\<^sub>2 \<inter> V)) \<union> ((B\<^sub>3 \<inter> V) \<union> (B\<^sub>4 \<inter> V))"
    by (auto simp: bad_union_def)
  have "meager (((B\<^sub>1 \<inter> V) \<union> (B\<^sub>2 \<inter> V)) \<union> ((B\<^sub>3 \<inter> V) \<union> (B\<^sub>4 \<inter> V)))"
    by (rule meager_Un[OF meager_Un[OF assms(1) assms(2)]
                          meager_Un[OF assms(3) assms(4)]])
  then show ?thesis
    by (simp add: eq)
qed

text \<open>
  The end-to-end closeout: a nonempty open working set \<open>V \<subseteq> Fset\<close> is not meager
  (Baire), so once all four bad branches are meager in \<open>V\<close> and the soundness
  hypothesis holds, some robust feasible set is nonempty.
\<close>

theorem nonemptiness_from_branches:
  fixes V Fset :: "'cfg::{real_normed_vector,heine_borel} set"
    and X0 :: "real \<Rightarrow> 'cfg set"
    and B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4 :: "'cfg set"
  assumes V_open: "open V" and V_nonempty: "V \<noteq> {}"
    and V_subset_Fset: "V \<subseteq> Fset"
    and m\<^sub>1: "meager (B\<^sub>1 \<inter> V)" and m\<^sub>2: "meager (B\<^sub>2 \<inter> V)"
    and m\<^sub>3: "meager (B\<^sub>3 \<inter> V)" and m\<^sub>4: "meager (B\<^sub>4 \<inter> V)"
    and X0_sound:
      "\<And>x. x \<in> V - bad_union B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4 \<Longrightarrow> \<exists>\<xi>>0. x \<in> X0 \<xi>"
  shows "\<exists>\<xi>>0. Fzero Fset X0 \<xi> \<noteq> {}"
proof -
  have hV: "\<not> meager V"
    by (rule open_nonempty_not_meager[OF V_open V_nonempty])
  have hB: "meager (bad_union B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4 \<inter> V)"
    by (rule bad_union_meagerness[OF m\<^sub>1 m\<^sub>2 m\<^sub>3 m\<^sub>4])
  show ?thesis
    by (rule final_nonemptiness_from_bad_union[OF V_subset_Fset hV hB X0_sound])
qed


section \<open>Main Theorem Inventory from the TeX Note\<close>

text \<open>
  The deep branch results are not stated here as abstract \<^theory_text>\<open>sorry\<close> lemmas,
  because they are false for arbitrary sets: they only become genuine theorems once
  \<open>Fset\<close>, \<open>X0\<close>, the working set \<open>V\<close>, and the four bad strata are given concrete
  definitions in terms of \<^const>\<open>array_factor\<close>. They are the hypotheses of
  \<open>nonemptiness_from_branches\<close>, and the future concrete lemmas are:

  \<^enum> \<open>open_feasible_family\<close> / \<open>two_triple_cover\<close> --- construction of a nonempty open
     \<open>V \<subseteq> Fset\<close> with two noncollinear triples (TeX Prop 2.1, Lem 2.2);
  \<^enum> \<open>regular_stratum_zero_meagerness\<close> --- \<open>meager (B\<^sub>1 \<inter> V)\<close>, via the odd-\<open>N\<close>
     transversality core already proved in
     \<open>array_factor_zero_odd_not_collinear\<close> (TeX Prop 3.1);
  \<^enum> \<open>fold_zero_meagerness\<close> / \<open>fold_nonzero_meagerness\<close> --- the fold-curve branches
     (TeX Prop 4.1, 4.3);
  \<^enum> \<open>regular_stratum_nonzero_meagerness\<close> --- the moment-map / 12x12 determinant
     branch (TeX Section 5).

  When each is proved for the concrete sets, feeding them to
  \<open>nonemptiness_from_branches\<close> yields the final odd-\<open>N\<close> nonemptiness theorem
  with no remaining \<^theory_text>\<open>sorry\<close>.
\<close>


section \<open>Roadmap Markers\<close>

text \<open>
  The largest future proof blocks, corresponding to the TeX appendices, are:

  1. a specialized transversality package for the regular-stratum zero branch;
  2. the fold-geometry closure and the finite exceptional-set argument;
  3. the moment-map surjectivity witness, including the explicit 12x12
     determinant computation;
  4. the Hessian-zero residual closure; and
  5. the direct configuration-space closure of Case B.

  These are described operationally in
  \<open>Applied_Math_Formalization/ROADMAP.md\<close>.
\<close>

end
