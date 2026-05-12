(*
  Title:      Day24_Separability.thy
  Author:     Dustin Bryant (based on lectures of Vern Paulsen)

  Days 24-28 of the Paulsen QC lectures (24 Oct - 4 Nov 2011),
  topic: Separability and Entanglement Witnesses.

  Originally skipped in Quantum_Computing11.thy with the comment:
    "Day 24-28 require partial-isometry / Hahn-Banach machinery that
     lies beyond the matrix infrastructure currently set up."
  The infrastructure was subsequently developed in
  Vern_Paulsen_QC_3_10_Lmat.Separable_Cone using the HOL-Analysis
  real_inner / euclidean_space / heine_borel typeclass instances on
  the typed-dimension matrix wrapper \<open>lmat\<close>.  This file imports those
  results and presents them in the day-by-day lecture form.

  The contents map to the proven theorems as follows:

    Day 24 (separability defined, sanity facts on the cone):
      separable_cone_lmat (definition)
      separable_cone_lmat_convex_cone
      zero_in_separable_cone_lmat
      separable_cone_lmat_hermitian

    Day 25 (the textbook convex-hull characterisation):
      separable_density_iff_in_convex_hull_Sprime

    Day 26 (topology: separable set is compact, closed, bounded):
      compact_convex_hull_Sprime
      closed_convex_hull_Sprime
      bounded_convex_hull_Sprime
      separable_cone_lmat_closed

    Day 27 (Hahn-Banach separating hyperplane):
      separable_cone_lmat_separating_hyperplane
      separable_density_separating_hyperplane

    Day 28 (entanglement witnesses):
      entanglement_witness_re_tr
      entanglement_witness_hermitian
      entanglement_witness_hermitian'
      separable_iff_witness
      entanglement_witness_for_density
      entanglement_witness_for_density_on_Sprime
      entanglement_witness_strict
      separable_density_iff_witness
*)

theory Day24_Separability
  imports
    Quantum_Computing11
    Vern_Paulsen_QC_3_10_Lmat.Separable_Cone
begin


(* ============================================================================
   DAY 24 \<mdash> 24 / Oct / 11
   Topic: Separability of bipartite states; the separable cone.
   ============================================================================ *)

text \<open>A bipartite mixed state \<open>\<rho>\<close> on \<open>\<complex>\<^sup>m \<otimes> \<complex>\<^sup>p\<close> is
\<^emph>\<open>separable\<close> if it admits a representation as a finite nonneg
combination of product states \<open>\<sigma> \<otimes> \<tau>\<close> with \<open>\<sigma>, \<tau>\<close> PSD.  Equivalently,
the set of separable states is the convex conic hull of pure-PSD
tensor products.  This is the formalisation we use throughout.

The typed-dimension formalisation lives in
\<^theory>\<open>Vern_Paulsen_QC_3_10_Lmat.Separable_Cone\<close>.  We re-export the
basic definitions and sanity facts under Day 24 names.\<close>

text \<open>The separable cone is convex, conic, and contains the zero
matrix.  Every separable state has hermitian unwrap (it is in fact
PSD by construction of the generators).  Throughout this file we
write \<open>\<rho> \<in> separable_cone_lmat\<close> for ``\<open>\<rho>\<close> is separable''.\<close>

theorem D24_separable_cone_convex_cone:
  "convex_cone (separable_cone_lmat
                  :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set)"
  by (rule separable_cone_lmat_convex_cone)

theorem D24_zero_separable:
  "(0 :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat)
     \<in> separable_cone_lmat"
  by (rule zero_in_separable_cone_lmat)

theorem D24_separable_state_hermitian:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes "\<rho> \<in> separable_cone_lmat"
  shows "hermitian (unwrap_lm \<rho>)"
  using assms by (rule separable_cone_lmat_hermitian)


(* ============================================================================
   DAY 25 \<mdash> 26 / Oct / 11
   Topic: Density-matrix separability is exactly a convex
   combination of product states.
   ============================================================================ *)

text \<open>This is the standard textbook definition: a density matrix
\<open>\<rho>\<close> (PSD with \<open>Tr \<rho> = 1\<close>) is separable iff it can be written as a
convex combination of product states \<open>\<sigma>\<^sub>i \<otimes> \<tau>\<^sub>i\<close> with each \<open>\<sigma>\<^sub>i,
\<tau>\<^sub>i\<close> a density matrix.\<close>

theorem D25_separable_density_iff_convex_combination:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
  shows "\<rho> \<in> separable_cone_lmat \<longleftrightarrow> \<rho> \<in> convex hull Sprime"
  using separable_density_iff_in_convex_hull_Sprime [OF \<rho>_psd \<rho>_tr] .


(* ============================================================================
   DAY 26 \<mdash> 28 / Oct / 11
   Topic: Topology of the separable set; closedness in HS norm.
   ============================================================================ *)

text \<open>The separable cone is HS-norm-closed; the separable
density-matrix set (\<open>convex hull Sprime\<close>) is compact, closed, and
bounded.  Closedness is the geometric prerequisite for the
Hahn-Banach separation argument of Day 27.\<close>

theorem D26_separable_cone_closed:
  "closed (separable_cone_lmat
             :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set)"
  by (rule separable_cone_lmat_closed)

theorem D26_separable_density_compact:
  "compact (convex hull
              (Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set))"
  by (rule compact_convex_hull_Sprime)

theorem D26_separable_density_closed:
  "closed (convex hull
              (Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set))"
  by (rule closed_convex_hull_Sprime)

theorem D26_separable_density_bounded:
  "bounded (convex hull
              (Sprime :: (complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat set))"
  by (rule bounded_convex_hull_Sprime)


(* ============================================================================
   DAY 27 \<mdash> 31 / Oct / 11
   Topic: Hahn-Banach for the separable cone; strict separation.
   ============================================================================ *)

text \<open>The geometric Hahn-Banach theorem applied to a non-separable
state \<open>\<rho>\<close> and the separable cone yields a real-linear functional
that is strictly negative on \<open>\<rho>\<close> and nonneg on the cone.  For
density matrices we get a stronger, strict, two-sided margin
because the separable density set is compact.\<close>

theorem D27_separating_hyperplane_cone:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>a :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
           inner a \<rho> < 0
         \<and> (\<forall>\<sigma> \<in> separable_cone_lmat. 0 \<le> inner a \<sigma>)"
  using assms by (rule separable_cone_lmat_separating_hyperplane)

theorem D27_strict_hyperplane_density:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
      and \<rho>_not_sep: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>a b.
           inner a \<rho> < b
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> convex hull Sprime \<longrightarrow> b < inner a \<sigma>)"
  using separable_density_separating_hyperplane [OF \<rho>_psd \<rho>_tr \<rho>_not_sep] .


(* ============================================================================
   DAY 28 \<mdash> 4 / Nov / 11
   Topic: Entanglement witnesses and the Horodecki characterisation.
   ============================================================================ *)

text \<open>An \<^emph>\<open>entanglement witness\<close> for \<open>\<rho>\<close> is a hermitian \<open>W\<close>
that is nonneg-trace on every separable state and strictly
negative-trace on \<open>\<rho>\<close>.  Three central facts:

  (i)   Existence: for every non-separable hermitian \<open>\<rho>\<close>, an
        entanglement witness exists.

  (ii)  For density matrices, a strict-margin entanglement witness
        exists.

  (iii) Horodecki characterisation: \<open>\<rho>\<close> is separable iff every
        hermitian witness which is nonneg-trace on the cone is also
        nonneg-trace on \<open>\<rho>\<close>.

We state each of these in their natural forms.\<close>

theorem D28_witness_exists_hermitian:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes notin: "\<rho> \<notin> separable_cone_lmat"
      and \<rho>_herm: "hermitian (unwrap_lm \<rho>)"
  shows "\<exists>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> hermitian W
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < 0
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> separable_cone_lmat
                \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))"
  using entanglement_witness_hermitian' [OF notin \<rho>_herm] .

theorem D28_witness_for_density:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
      and \<rho>_not_sep: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> hermitian W
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < 0
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> separable_cone_lmat
                \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))"
  using entanglement_witness_for_density [OF \<rho>_psd \<rho>_tr \<rho>_not_sep] .

theorem D28_witness_strict_density:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
      and \<rho>_not_sep: "\<rho> \<notin> separable_cone_lmat"
  shows "\<exists>(W :: complex Matrix.mat) c.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
         \<and> hermitian W
         \<and> Re (Tr (W * unwrap_lm \<rho>)) < c
         \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
              \<sigma> \<in> convex hull Sprime
                \<longrightarrow> c < Re (Tr (W * unwrap_lm \<sigma>)))"
  using entanglement_witness_strict [OF \<rho>_psd \<rho>_tr \<rho>_not_sep] .

theorem D28_separable_iff_witness:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_herm: "hermitian (unwrap_lm \<rho>)"
  shows "\<rho> \<in> separable_cone_lmat
       \<longleftrightarrow>
        (\<forall>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
           \<and> hermitian W
           \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                \<sigma> \<in> separable_cone_lmat
                  \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))
             \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<rho>)))"
  using separable_iff_witness [OF \<rho>_herm] .

theorem D28_separable_density_iff_witness:
  fixes \<rho> :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes \<rho>_psd: "psd_lmat \<rho>"
      and \<rho>_tr: "Tr_lmat \<rho> = 1"
  shows "\<rho> \<in> separable_cone_lmat
       \<longleftrightarrow>
        (\<forall>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('m \<times> 'p)) (CARD('m \<times> 'p))
           \<and> hermitian W
           \<and> (\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat.
                \<sigma> \<in> separable_cone_lmat
                  \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>)))
             \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<rho>)))"
  using separable_density_iff_witness [OF \<rho>_psd \<rho>_tr] .


text \<open>This closes the entanglement-witness chapter that motivated
the detour into typed-dimension matrices and Hahn-Banach.  Day 29
resumes the lecture stream with classical error correction.\<close>


end
