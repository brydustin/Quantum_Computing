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


subsection \<open>UCP-Kraus representation\<close>

text \<open>A \<^emph>\<open>UCP Kraus representation\<close> for a map \<open>\<Phi> : M\<^sub>n \<rightarrow> M\<^sub>d\<close> is a
list \<open>Vs\<close> of \<open>d \<times> n\<close> matrices such that
  \<^item> each \<open>V \<in> Vs\<close> is \<open>d \<times> n\<close>;
  \<^item> the unitality identity \<open>\<Sum>\<^sub>i V\<^sub>i V\<^sub>i\<^sup>\<dagger> = I\<^sub>d\<close> holds;
  \<^item> \<open>\<Phi> X = \<Sum>\<^sub>i V\<^sub>i X V\<^sub>i\<^sup>\<dagger>\<close> for every \<open>X \<in> M\<^sub>n\<close>.

Note that the standard \<open>kraus_operators\<close> predicate of Day 17 uses
the \<^emph>\<open>trace-preserving\<close> identity \<open>\<Sum> V\<^sub>i\<^sup>\<dagger> V\<^sub>i = I\<^sub>n\<close>; the
\<^emph>\<open>unital\<close> form \<open>\<Sum> V\<^sub>i V\<^sub>i\<^sup>\<dagger> = I\<^sub>d\<close> is the Heisenberg-dual
condition appropriate for \<open>UCP\<close>.\<close>

definition ucp_kraus_rep ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow>
       complex Matrix.mat list \<Rightarrow> bool"
where
  "ucp_kraus_rep n d \<Phi> Vs \<equiv>
     (\<forall>V \<in> set Vs. V \<in> carrier_mat d n) \<and>
     foldr (\<lambda>V acc. V * (V\<^sup>\<dagger>) + acc) Vs (0\<^sub>m d d) = 1\<^sub>m d \<and>
     (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Vs X)"

text \<open>The \<^emph>\<open>products set\<close> of a Kraus list \<open>Vs\<close> is the list of
\<open>n \<times> n\<close> matrices \<open>V\<^sub>j\<^sup>\<dagger> V\<^sub>i\<close> for all pairs of indices \<open>(i,j)\<close>.\<close>

definition kraus_products ::
  "complex Matrix.mat list \<Rightarrow> complex Matrix.mat list"
where
  "kraus_products Vs \<equiv>
     concat (map (\<lambda>i. map (\<lambda>j. (Vs!j)\<^sup>\<dagger> * Vs!i) [0..<length Vs])
                 [0..<length Vs])"

text \<open>Real linear independence for a list of complex matrices.
A list \<open>Bs\<close> is independent over \<open>\<real>\<close> iff the only \<open>\<real>\<close>-coefficients
making \<open>\<Sum>\<^sub>k c\<^sub>k B\<^sub>k = 0\<close> are all zero.  We use the real-coefficient
form because Choi's perturbation argument constructs real
combinations of hermitian generators.\<close>

definition mat_lin_indep_real ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool"
where
  "mat_lin_indep_real n Bs \<equiv>
     (\<forall>B \<in> set Bs. B \<in> carrier_mat n n) \<and>
     (\<forall>c :: nat \<Rightarrow> real.
        foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (Bs!k) + acc)
              [0..<length Bs] (0\<^sub>m n n)
          = 0\<^sub>m n n
        \<longrightarrow> (\<forall>k < length Bs. c k = 0))"


subsection \<open>Unital condition from the Kraus list\<close>

text \<open>If \<open>Ws\<close> is a list of \<open>d \<times> n\<close> matrices, then evaluating the
Kraus map at the identity \<open>1\<^sub>m n\<close> gives exactly the sum
\<open>\<Sum> W W\<^sup>\<dagger>\<close>.  Combined with unitality, this gives the
\<open>\<Sum> W W\<^sup>\<dagger> = 1\<^sub>m d\<close> identity that distinguishes UCP from
plain CP.\<close>

lemma kraus_map_dim_one:
  assumes "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (1\<^sub>m n)
           = foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d)"
  using assms
proof (induction Ws)
  case Nil
  show ?case by simp
next
  case (Cons W Ws)
  have W_c: "W \<in> carrier_mat d n" using Cons.prems by simp
  have Wd_c: "W\<^sup>\<dagger> \<in> carrier_mat n d" using W_c by auto
  have I_n_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by auto
  have step_W: "W * 1\<^sub>m n * (W\<^sup>\<dagger>) = W * (W\<^sup>\<dagger>)"
    using W_c by simp
  have rest_c: "\<forall>W' \<in> set Ws. W' \<in> carrier_mat d n"
    using Cons.prems by simp
  have IH: "kraus_map_dim d Ws (1\<^sub>m n)
              = foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d)"
    using Cons.IH[OF rest_c] .
  have "kraus_map_dim d (W # Ws) (1\<^sub>m n)
          = W * 1\<^sub>m n * (W\<^sup>\<dagger>) + kraus_map_dim d Ws (1\<^sub>m n)"
    by simp
  also have "... = W * (W\<^sup>\<dagger>) + kraus_map_dim d Ws (1\<^sub>m n)"
    using step_W by simp
  also have "... = W * (W\<^sup>\<dagger>) + foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d)"
    using IH by simp
  also have "... = foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) (W # Ws) (0\<^sub>m d d)"
    by simp
  finally show ?case .
qed


subsection \<open>UCP-Kraus existence\<close>

text \<open>Every linear UCP map admits a UCP Kraus representation
of length \<open>n d\<close>.  Linearity, scalar-multiplication and range
hypotheses match those of \<open>kraus_rep_of_psd_choi\<close>; the unital
condition \<open>\<Sum> V V\<^sup>\<dagger> = 1\<^sub>m d\<close> is supplied by
\<open>\<Phi> (1\<^sub>m n) = 1\<^sub>m d\<close> + \<open>kraus_map_dim_one\<close>.\<close>

lemma ucp_has_kraus_rep:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "0 < n" and dpos: "0 < d"
      and ucp: "\<Phi> \<in> UCP n d"
  shows "\<exists>Vs :: complex Matrix.mat list.
           ucp_kraus_rep n d \<Phi> Vs \<and> length Vs = n * d"
proof -
  have cp: "completely_positive n d \<Phi>"
    using ucp unfolding UCP_def by auto
  have unital: "\<Phi> (1\<^sub>m n) = 1\<^sub>m d"
    using ucp unfolding UCP_def unital_map_def by auto
  have psd_choi: "psd (choi_matrix n d \<Phi>)"
    using choi_psd_if_cp[OF npos dpos cp] .
  obtain Ws :: "complex Matrix.mat list"
    where Ws_len: "length Ws = n * d"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Ws_eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos psd_choi]
    by blast
  have I_n_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by auto
  have phi_I: "\<Phi> (1\<^sub>m n) = kraus_map_dim d Ws (1\<^sub>m n)"
    using Ws_eq I_n_c by blast
  have sum_WWdag: "foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d) = 1\<^sub>m d"
  proof -
    have "1\<^sub>m d = \<Phi> (1\<^sub>m n)" using unital by simp
    also have "... = kraus_map_dim d Ws (1\<^sub>m n)" using phi_I .
    also have "... = foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d)"
      using kraus_map_dim_one[OF Ws_c] .
    finally show ?thesis by simp
  qed
  have rep: "ucp_kraus_rep n d \<Phi> Ws"
    unfolding ucp_kraus_rep_def
    using Ws_c sum_WWdag Ws_eq by blast
  show ?thesis using rep Ws_len by blast
qed


subsection \<open>Sanity facts about \<open>kraus_products\<close>\<close>

lemma kraus_products_carrier:
  assumes "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "\<forall>B \<in> set (kraus_products Vs). B \<in> carrier_mat n n"
proof
  fix B assume "B \<in> set (kraus_products Vs)"
  then obtain i j where
    i_lt: "i < length Vs" and j_lt: "j < length Vs"
    and B_eq: "B = (Vs!j)\<^sup>\<dagger> * Vs!i"
    unfolding kraus_products_def by auto
  have Vi_c: "Vs!i \<in> carrier_mat d n"
    using assms i_lt by (simp add: nth_mem)
  have Vj_c: "Vs!j \<in> carrier_mat d n"
    using assms j_lt by (simp add: nth_mem)
  have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by auto
  show "B \<in> carrier_mat n n" using B_eq Vi_c Vjd_c by auto
qed


subsection \<open>Choi's Theorem 3 (statement)\<close>

text \<open>Choi (1975), Theorem 3: a UCP map \<open>\<Phi> : M\<^sub>n \<rightarrow> M\<^sub>d\<close> is an
extreme point of \<open>UCP(n,d)\<close> if and only if, for any (equivalently:
every) Kraus representation \<open>\<Phi>(X) = \<Sum>\<^sub>i V\<^sub>i X V\<^sub>i\<^sup>\<dagger>\<close>, the
matrices \<open>{V\<^sub>j\<^sup>\<dagger> V\<^sub>i : 1 \<le> i,j \<le> length Vs}\<close> are linearly
independent in \<open>M\<^sub>n\<close>.

We state it as a single theorem parametrised by a fixed Kraus
representation; the "any/every" character follows from the
unitary-freedom of Kraus reps (Day 22 / "Kraus uniqueness"),
which is not yet formalised in this development.

\<^bold>\<open>Forward (lin. indep. \<Rightarrow> extreme)\<close>: given any UCP midpoint
splitting \<open>\<Phi> = \<onehalf>\<Phi>\<^sub>1 + \<onehalf>\<Phi>\<^sub>2\<close>, both \<open>\<Phi>\<^sub>i\<close>
admit Kraus reps that factor through \<open>Vs\<close> (Radon-Nikodym for
CP maps); unitality + lin. indep. of the products forces the
factoring matrix to be a multiple of the identity, hence
\<open>\<Phi>\<^sub>1 = \<Phi>\<^sub>2 = \<Phi>\<close>.

\<^bold>\<open>Reverse (extreme \<Rightarrow> lin. indep.)\<close>: contrapositive.  If
\<open>\<Sum>\<^sub>{i,j} a\<^sub>{ij} V\<^sub>j\<^sup>\<dagger> V\<^sub>i = 0\<close> non-trivially, define
\<open>\<Phi>\<^sub>\<epsilon>(X) = \<Phi>(X) + \<epsilon> \<Sum>\<^sub>{i,j} a\<^sub>{ij} V\<^sub>i X V\<^sub>j\<^sup>\<dagger>\<close>; for small
hermitian \<open>a\<close>, both \<open>\<Phi>\<^sub>\<plusminus>\<epsilon>\<close> are UCP and distinct, yielding
a non-trivial midpoint of \<open>\<Phi>\<close>.\<close>

theorem choi_theorem_3:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> UCP n d"
      and rep:  "ucp_kraus_rep n d \<Phi> Vs"
  shows "extreme_UCP n d \<Phi> \<longleftrightarrow>
           mat_lin_indep_real n (kraus_products Vs)"
  sorry


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
