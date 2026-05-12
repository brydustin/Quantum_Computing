(*
  Title:      Day23_ChoiExtremeUCP.thy
  Author:     Dustin Bryant (based on lectures of Vern Paulsen)

  Day 23 (~ 20 Oct 2011): Extreme points of the UCP cone /
  Choi's Theorem 3.

  The main classical result of Day 23 is:

     CHOI'S THEOREM 3.  A UCP map \<Phi> : M_n \<rightarrow> M_d is an
     extreme point of the convex set UCP(n,d) if and only if
     for any (and hence every) Kraus representation
        \<Phi>(X) = \<Sum>_i V_i X V_i\<^sup>\<dagger>,
     the set {V_j\<^sup>\<dagger> V_i : i, j} is linearly independent
     in M_n.

  A full formalisation requires explicit Kraus-list infrastructure
  (representation theorem, uniqueness up to unitary, linear
  independence of matrix sets, perturbation construction) that we
  do not yet have.  This file fills in the part of Day 23 that is
  reachable today: the natural specialisation of \<open>extreme_point_mat\<close>
  to \<open>UCP n d\<close>, and the connection to the Day-22 / Day-19 Choi
  infrastructure.  The full theorem statement is recorded as a
  guiding north star in the documentation block below.
*)

theory Day23_ChoiExtremeUCP
  imports
    Quantum_Computing11
begin


(* ============================================================================
   DAY 23 \<mdash> 20 / Oct / 11
   Topic: Extreme points of UCP; Choi's Theorem 3.
   ============================================================================ *)

text \<open>The extreme points of UCP(n,d) are exactly those maps whose
Kraus operators give a linearly independent system.  The day-22
infrastructure already provides:

  \<^item> \<open>UCP n d\<close>            (Day 22)
  \<^item> \<open>extreme_point_mat\<close>  (Day 22, abstract)
  \<^item> \<open>UCP_convex\<close>         (Day 22)
  \<^item> \<open>choi_matrix\<close>        (Day 19)

We collect the Day-23-specific specialisations here.\<close>


subsection \<open>Extreme UCP maps\<close>

text \<open>An \<^emph>\<open>extreme UCP map\<close> is one that cannot be written as a
proper convex combination of two distinct UCP maps.  Following
Day-22's \<open>extreme_point_mat\<close>, we use the half-half mid-point
formulation; this is equivalent to the standard definition for
convex sets.\<close>

definition extreme_UCP ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool"
where
  "extreme_UCP n d \<Phi> \<equiv>
     \<Phi> \<in> UCP n d \<and>
     \<not> (\<exists>\<Phi>\<^sub>1 \<in> UCP n d. \<exists>\<Phi>\<^sub>2 \<in> UCP n d.
           \<Phi>\<^sub>1 \<noteq> \<Phi> \<and> \<Phi> \<noteq> \<Phi>\<^sub>2 \<and>
           (\<forall>X. X \<in> carrier_mat n n
                  \<longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X
                            + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X))"

lemma extreme_UCP_member:
  assumes "extreme_UCP n d \<Phi>"
  shows "\<Phi> \<in> UCP n d"
  using assms unfolding extreme_UCP_def by simp

text \<open>Trivial unfolding: an extreme UCP map satisfies no non-trivial
mid-point decomposition.\<close>

lemma extreme_UCP_no_split:
  assumes ext: "extreme_UCP n d \<Phi>"
      and \<Phi>1_in: "\<Phi>\<^sub>1 \<in> UCP n d"
      and \<Phi>2_in: "\<Phi>\<^sub>2 \<in> UCP n d"
      and \<Phi>1_neq: "\<Phi>\<^sub>1 \<noteq> \<Phi>"
      and \<Phi>2_neq: "\<Phi> \<noteq> \<Phi>\<^sub>2"
  shows "\<exists>X \<in> carrier_mat n n.
            \<Phi> X \<noteq> (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X
                  + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X"
  using ext \<Phi>1_in \<Phi>2_in \<Phi>1_neq \<Phi>2_neq
  unfolding extreme_UCP_def by blast


subsection \<open>Choi's Theorem 3 (statement only)\<close>

text \<open>Choi (1975) Theorem 3 states: a UCP map \<open>\<Phi>\<close> with Kraus
representation \<open>\<Phi>(X) = sum (V_i X V_i^dag) over i\<close> is an extreme
point of UCP(n,d) iff the set of n-by-n matrices
\<open>{V_j^dag V_i : i, j over the Kraus index}\<close> is linearly independent.

Forward direction (linearly indep => extreme): a perturbation
argument starting from any non-trivial mid-point splitting.
Reverse direction (extreme => linearly indep): the
constructive direction; a linear dependence among the
products yields a non-trivial splitting.

A full proof requires a Kraus-list infrastructure that packages
the operators V_i together with the trace-preserving normalisation
sum (V_i^dag V_i) = I_n.  Day 19 already provides choi_matrix and
the PSD-Kraus decomposition; the missing piece is the linear
independence wrapper.  Pending.\<close>


subsection \<open>Sanity / easy facts about extreme UCP\<close>

text \<open>If a UCP map has a non-trivial mid-point representation by two
distinct UCP maps, it is not extreme \<^emph>\<open>by definition\<close>.\<close>

lemma not_extreme_UCP_if_midpoint:
  assumes "\<Phi>\<^sub>1 \<in> UCP n d" "\<Phi>\<^sub>2 \<in> UCP n d"
      and "\<Phi>\<^sub>1 \<noteq> \<Phi>" and "\<Phi> \<noteq> \<Phi>\<^sub>2"
      and "\<Phi> \<in> UCP n d"
      and "\<And>X. X \<in> carrier_mat n n
                \<Longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X
                          + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X"
  shows "\<not> extreme_UCP n d \<Phi>"
  using assms unfolding extreme_UCP_def by blast

text \<open>The contrapositive: every extreme UCP map, when written as a
mid-point of two UCP maps, must have those maps coincide with itself
on every \<open>X \<in> carrier_mat n n\<close>.\<close>

lemma extreme_UCP_midpoint_collapses:
  assumes ext: "extreme_UCP n d \<Phi>"
      and \<Phi>1_in: "\<Phi>\<^sub>1 \<in> UCP n d"
      and \<Phi>2_in: "\<Phi>\<^sub>2 \<in> UCP n d"
      and mid: "\<And>X. X \<in> carrier_mat n n
                       \<Longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X
                                 + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X"
  shows "\<Phi>\<^sub>1 = \<Phi> \<or> \<Phi> = \<Phi>\<^sub>2"
proof (rule ccontr)
  assume neq: "\<not> (\<Phi>\<^sub>1 = \<Phi> \<or> \<Phi> = \<Phi>\<^sub>2)"
  hence neq1: "\<Phi>\<^sub>1 \<noteq> \<Phi>" and neq2: "\<Phi> \<noteq> \<Phi>\<^sub>2" by simp_all
  have "\<not> extreme_UCP n d \<Phi>"
    using \<Phi>1_in \<Phi>2_in neq1 neq2
          extreme_UCP_member [OF ext] mid
    by (rule not_extreme_UCP_if_midpoint)
  thus False using ext by simp
qed


text \<open>This closes the Day-23 stub.  The full content of Choi's
Theorem 3 awaits a Kraus-list formalisation; the definitions
collected above will plug into that proof once available.\<close>


end
