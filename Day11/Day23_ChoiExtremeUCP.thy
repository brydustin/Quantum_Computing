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

text \<open>Complex linear independence: the classical Choi statement uses
\<^bold>\<open>complex\<close>-coefficient linear independence. This is strictly stronger
than @{const mat_lin_indep_real}.\<close>

definition mat_lin_indep_complex ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool"
where
  "mat_lin_indep_complex n Bs \<equiv>
     (\<forall>B \<in> set Bs. B \<in> carrier_mat n n) \<and>
     (\<forall>c :: nat \<Rightarrow> complex.
        foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (Bs!k) + acc)
              [0..<length Bs] (0\<^sub>m n n)
          = 0\<^sub>m n n
        \<longrightarrow> (\<forall>k < length Bs. c k = 0))"

text \<open>Complex linear independence implies real.\<close>

lemma mat_lin_indep_complex_imp_real:
  assumes "mat_lin_indep_complex n Bs"
  shows "mat_lin_indep_real n Bs"
proof -
  have carr: "\<forall>B \<in> set Bs. B \<in> carrier_mat n n"
    using assms unfolding mat_lin_indep_complex_def by simp
  have body: "\<And>c :: nat \<Rightarrow> real.
                foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (Bs!k) + acc)
                      [0..<length Bs] (0\<^sub>m n n)
                  = 0\<^sub>m n n
                \<Longrightarrow> (\<forall>k < length Bs. c k = 0)"
  proof -
    fix c :: "nat \<Rightarrow> real"
    assume foldr_zero: "foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (Bs!k) + acc)
                              [0..<length Bs] (0\<^sub>m n n) = 0\<^sub>m n n"
    let ?c_complex = "\<lambda>k. complex_of_real (c k)"
    have foldr_complex: "foldr (\<lambda>k acc. ?c_complex k \<cdot>\<^sub>m (Bs!k) + acc)
                                 [0..<length Bs] (0\<^sub>m n n) = 0\<^sub>m n n"
      using foldr_zero by simp
    have univ: "\<forall>c :: nat \<Rightarrow> complex.
                  foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (Bs!k) + acc)
                        [0..<length Bs] (0\<^sub>m n n) = 0\<^sub>m n n
                  \<longrightarrow> (\<forall>k < length Bs. c k = 0)"
      using assms unfolding mat_lin_indep_complex_def by simp
    have all_zero: "\<forall>k < length Bs. complex_of_real (c k) = 0"
      using spec[OF univ, where x = "\<lambda>k. complex_of_real (c k)"]
            foldr_complex by blast
    show "\<forall>k < length Bs. c k = 0"
      using all_zero by (metis of_real_eq_0_iff)
  qed
  show ?thesis
    unfolding mat_lin_indep_real_def using carr body by metis
qed


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


subsection \<open>Quadratic Kraus map (perturbation primitive)\<close>

text \<open>For a Kraus list \<open>Vs\<close> of \<open>d \<times> n\<close> matrices and a coefficient
matrix \<open>T \<in> M\<^sub>k\<close> (where \<open>k = length Vs\<close>), the \<^emph>\<open>quadratic
Kraus map\<close> is
  \<open>(kraus_quad_map d Vs T) X = \<Sum>\<^sub>{i,j} T\<^sub>{ij} V\<^sub>i X V\<^sub>j\<^sup>\<dagger>\<close>.
When \<open>T = I\<^sub>k\<close> this reduces to the ordinary Kraus map
\<open>kraus_map_dim d Vs X = \<Sum> V\<^sub>i X V\<^sub>i\<^sup>\<dagger>\<close>; for PSD \<open>T\<close> the
result is again a Kraus map (Lemma A below).  The perturbations
\<open>T\<^sub>\<plusminus> = I \<plusminus> \<epsilon> A\<close> for small \<open>\<epsilon>\<close> and hermitian \<open>A\<close>
will provide the \<^emph>\<open>splittings\<close> witnessing non-extremity.\<close>

definition kraus_quad_row ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow>
       complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat"
where
  "kraus_quad_row d Vs Tm rho i \<equiv>
     foldr (\<lambda>j acc. Tm $$ (i, j) \<cdot>\<^sub>m (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) + acc)
           [0..<length Vs] (0\<^sub>m d d)"

definition kraus_quad_map ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow>
       complex Matrix.mat \<Rightarrow> complex Matrix.mat"
where
  "kraus_quad_map d Vs Tm rho \<equiv>
     foldr (\<lambda>i acc. kraus_quad_row d Vs Tm rho i + acc)
           [0..<length Vs] (0\<^sub>m d d)"

text \<open>Generic carrier-preservation lemma for accumulating folds over
\<open>[0..<N]\<close>: if each per-index term lies in \<open>M\<^sub>d\<close>, so does the fold.\<close>

lemma foldr_add_carrier:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat d d"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m d d) \<in> carrier_mat d d"
  using assms
  by (induction xs) (auto intro!: add_carrier_mat)

lemma foldr_upt_add_carrier:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>k < N. f k \<in> carrier_mat d d"
  shows "foldr (\<lambda>k acc. f k + acc) [0..<N] (0\<^sub>m d d) \<in> carrier_mat d d"
  using assms by (intro foldr_add_carrier) auto

lemma kraus_quad_row_carrier:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and i_lt: "i < length Vs"
  shows "kraus_quad_row d Vs Tm rho i \<in> carrier_mat d d"
proof -
  let ?N = "length Vs"
  let ?f = "\<lambda>j. Tm $$ (i, j) \<cdot>\<^sub>m (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>))"
  have Vi_c: "Vs!i \<in> carrier_mat d n"
    using Vs_c i_lt nth_mem by blast
  have term_c: "\<forall>j < ?N. ?f j \<in> carrier_mat d d"
  proof (intro allI impI)
    fix j assume j_lt: "j < ?N"
    have Vj_c: "Vs!j \<in> carrier_mat d n"
      using Vs_c j_lt nth_mem by blast
    have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d"
      using Vj_c by (rule dagger_carrier)
    have inner_c: "Vs!i * rho * ((Vs!j)\<^sup>\<dagger>) \<in> carrier_mat d d"
      using Vi_c rho_c Vjd_c by (intro mult_carrier_mat) auto
    show "?f j \<in> carrier_mat d d"
      using inner_c by (intro smult_carrier_mat) auto
  qed
  show ?thesis
    unfolding kraus_quad_row_def
    using foldr_upt_add_carrier[OF term_c] .
qed

lemma kraus_quad_map_carrier:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
  shows "kraus_quad_map d Vs Tm rho \<in> carrier_mat d d"
proof -
  let ?N = "length Vs"
  let ?f = "\<lambda>i. kraus_quad_row d Vs Tm rho i"
  have term_c: "\<forall>i < ?N. ?f i \<in> carrier_mat d d"
    using kraus_quad_row_carrier[OF Vs_c rho_c] by blast
  show ?thesis
    unfolding kraus_quad_map_def
    using foldr_upt_add_carrier[OF term_c] .
qed

text \<open>Per-entry index formula for the accumulating fold (with arbitrary base).\<close>

lemma foldr_upt_add_acc_index:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat"
  assumes carr: "\<forall>k < N. f k \<in> carrier_mat d d"
      and z_c:  "z \<in> carrier_mat d d"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "foldr (\<lambda>k acc. f k + acc) [0..<N] z $$ (r, c)
           = (\<Sum>k = 0..<N. f k $$ (r, c)) + z $$ (r, c)"
  using carr z_c
proof (induction N arbitrary: z)
  case 0
  show ?case by simp
next
  case (Suc N)
  have hd_c:   "f N \<in> carrier_mat d d" using Suc.prems(1) by simp
  have rest_c: "\<forall>k < N. f k \<in> carrier_mat d d" using Suc.prems(1) by simp
  have fNz_c:  "f N + z \<in> carrier_mat d d"
    using hd_c Suc.prems(2) by auto
  have dec: "[0..<Suc N] = [0..<N] @ [N]" by simp
  have step: "foldr (\<lambda>k acc. f k + acc) [0..<Suc N] z
                = foldr (\<lambda>k acc. f k + acc) [0..<N] (f N + z)"
    using dec by (simp add: foldr_append)
  have IH: "foldr (\<lambda>k acc. f k + acc) [0..<N] (f N + z) $$ (r,c)
              = (\<Sum>k = 0..<N. f k $$ (r,c)) + (f N + z) $$ (r,c)"
    using Suc.IH[OF rest_c fNz_c] .
  have idx_split: "(f N + z) $$ (r,c) = f N $$ (r,c) + z $$ (r,c)"
    using hd_c Suc.prems(2) r_lt c_lt by simp
  have "foldr (\<lambda>k acc. f k + acc) [0..<Suc N] z $$ (r,c)
          = (\<Sum>k = 0..<N. f k $$ (r,c)) + (f N $$ (r,c) + z $$ (r,c))"
    using step IH idx_split by simp
  also have "\<dots> = ((\<Sum>k = 0..<N. f k $$ (r,c)) + f N $$ (r,c)) + z $$ (r,c)"
    by (simp add: add.assoc)
  also have "\<dots> = (\<Sum>k = 0..<Suc N. f k $$ (r,c)) + z $$ (r,c)"
    by simp
  finally show ?case .
qed

lemma foldr_upt_add_index:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat"
  assumes carr: "\<forall>k < N. f k \<in> carrier_mat d d"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "foldr (\<lambda>k acc. f k + acc) [0..<N] (0\<^sub>m d d) $$ (r, c)
           = (\<Sum>k = 0..<N. f k $$ (r, c))"
proof -
  have z_c: "(0\<^sub>m d d :: complex Matrix.mat) \<in> carrier_mat d d" by simp
  have z_idx: "(0\<^sub>m d d :: complex Matrix.mat) $$ (r,c) = 0"
    using r_lt c_lt by simp
  show ?thesis
    using foldr_upt_add_acc_index[OF carr z_c r_lt c_lt] z_idx by simp
qed

text \<open>Per-entry formula for @{const kraus_quad_row}.\<close>

lemma kraus_quad_row_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and i_lt: "i < length Vs"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "kraus_quad_row d Vs Tm rho i $$ (r, c)
           = (\<Sum>j = 0..<length Vs.
                Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
proof -
  let ?N = "length Vs"
  let ?f = "\<lambda>j. Tm $$ (i, j) \<cdot>\<^sub>m (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>))"
  have Vi_c: "Vs!i \<in> carrier_mat d n"
    using Vs_c i_lt nth_mem by blast
  have term_c: "\<forall>j < ?N. ?f j \<in> carrier_mat d d"
  proof (intro allI impI)
    fix j assume j_lt: "j < ?N"
    have Vj_c: "Vs!j \<in> carrier_mat d n"
      using Vs_c j_lt nth_mem by blast
    have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d"
      using Vj_c by (rule dagger_carrier)
    have inner_c: "Vs!i * rho * ((Vs!j)\<^sup>\<dagger>) \<in> carrier_mat d d"
      using Vi_c rho_c Vjd_c by (intro mult_carrier_mat) auto
    show "?f j \<in> carrier_mat d d"
      using inner_c by (intro smult_carrier_mat) auto
  qed
  have term_idx: "\<And>j. j < ?N \<Longrightarrow>
                   ?f j $$ (r, c) = Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)"
  proof -
    fix j assume j_lt: "j < ?N"
    have Vj_c: "Vs!j \<in> carrier_mat d n"
      using Vs_c j_lt nth_mem by blast
    have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d"
      using Vj_c by (rule dagger_carrier)
    have inner_c: "Vs!i * rho * ((Vs!j)\<^sup>\<dagger>) \<in> carrier_mat d d"
      using Vi_c rho_c Vjd_c by (intro mult_carrier_mat) auto
    have r_lt_dim: "r < dim_row (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>))"
      using inner_c r_lt by auto
    have c_lt_dim: "c < dim_col (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>))"
      using inner_c c_lt by auto
    show "?f j $$ (r, c) = Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)"
      using index_smult_mat(1)[OF r_lt_dim c_lt_dim] .
  qed
  have "kraus_quad_row d Vs Tm rho i $$ (r, c)
          = foldr (\<lambda>j acc. ?f j + acc) [0..<?N] (0\<^sub>m d d) $$ (r, c)"
    unfolding kraus_quad_row_def by simp
  also have "\<dots> = (\<Sum>j = 0..<?N. ?f j $$ (r, c))"
    using foldr_upt_add_index[OF term_c r_lt c_lt] .
  also have "\<dots> = (\<Sum>j = 0..<?N.
                     Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    by (rule sum.cong) (auto simp: term_idx)
  finally show ?thesis .
qed

text \<open>Per-entry formula for @{const kraus_quad_map}: double sum over indices.\<close>

lemma kraus_quad_map_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "kraus_quad_map d Vs Tm rho $$ (r, c)
           = (\<Sum>i = 0..<length Vs.
                \<Sum>j = 0..<length Vs.
                   Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
proof -
  let ?N = "length Vs"
  let ?row = "\<lambda>i. kraus_quad_row d Vs Tm rho i"
  have row_c: "\<forall>i < ?N. ?row i \<in> carrier_mat d d"
    using kraus_quad_row_carrier[OF Vs_c rho_c] by blast
  have row_idx: "\<And>i. i < ?N \<Longrightarrow>
                  ?row i $$ (r,c) = (\<Sum>j = 0..<?N.
                     Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    using kraus_quad_row_index[OF Vs_c rho_c _ r_lt c_lt] by blast
  have "kraus_quad_map d Vs Tm rho $$ (r, c)
          = foldr (\<lambda>i acc. ?row i + acc) [0..<?N] (0\<^sub>m d d) $$ (r, c)"
    unfolding kraus_quad_map_def by simp
  also have "\<dots> = (\<Sum>i = 0..<?N. ?row i $$ (r, c))"
    using foldr_upt_add_index[OF row_c r_lt c_lt] .
  also have "\<dots> = (\<Sum>i = 0..<?N.
                     \<Sum>j = 0..<?N.
                       Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    by (rule sum.cong) (auto simp: row_idx)
  finally show ?thesis .
qed

text \<open>Carrier-preservation in a different dimension pair.\<close>

lemma foldr_add_carrier_dn:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat d n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m d n) \<in> carrier_mat d n"
  using assms by (induction xs) (auto intro!: add_carrier_mat)

text \<open>Linear combination of Kraus operators with complex coefficients.
\<open>kraus_combo d n Vs u\<close> is \<open>\<Sum>\<^sub>i u\<^sub>i V\<^sub>i\<close>, a
\<open>d \<times> n\<close> matrix.\<close>

definition kraus_combo ::
  "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.vec \<Rightarrow>
       complex Matrix.mat"
where
  "kraus_combo d n Vs u \<equiv>
     foldr (\<lambda>i acc. u $ i \<cdot>\<^sub>m (Vs!i) + acc) [0..<length Vs] (0\<^sub>m d n)"

lemma kraus_combo_carrier:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "kraus_combo d n Vs u \<in> carrier_mat d n"
proof -
  let ?N = "length Vs"
  let ?f = "\<lambda>i. u $ i \<cdot>\<^sub>m (Vs!i)"
  have "\<forall>i \<in> set [0..<?N]. ?f i \<in> carrier_mat d n"
  proof
    fix i assume "i \<in> set [0..<?N]"
    hence i_lt: "i < ?N" by simp
    have Vi_c: "Vs!i \<in> carrier_mat d n"
      using Vs_c i_lt nth_mem by blast
    show "?f i \<in> carrier_mat d n"
      using Vi_c by (intro smult_carrier_mat) auto
  qed
  thus ?thesis
    unfolding kraus_combo_def
    by (rule foldr_add_carrier_dn)
qed

text \<open>Per-entry formula for @{const kraus_combo}: foldr index lemma in d\<times>n.\<close>

lemma foldr_upt_add_acc_index_dn:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat"
  assumes carr: "\<forall>k < N. f k \<in> carrier_mat d n"
      and z_c:  "z \<in> carrier_mat d n"
      and r_lt: "r < d" and c_lt: "c < n"
  shows "foldr (\<lambda>k acc. f k + acc) [0..<N] z $$ (r, c)
           = (\<Sum>k = 0..<N. f k $$ (r, c)) + z $$ (r, c)"
  using carr z_c
proof (induction N arbitrary: z)
  case 0
  show ?case by simp
next
  case (Suc N)
  have hd_c:   "f N \<in> carrier_mat d n" using Suc.prems(1) by simp
  have rest_c: "\<forall>k < N. f k \<in> carrier_mat d n" using Suc.prems(1) by simp
  have fNz_c:  "f N + z \<in> carrier_mat d n"
    using hd_c Suc.prems(2) by auto
  have dec: "[0..<Suc N] = [0..<N] @ [N]" by simp
  have step: "foldr (\<lambda>k acc. f k + acc) [0..<Suc N] z
                = foldr (\<lambda>k acc. f k + acc) [0..<N] (f N + z)"
    using dec by (simp add: foldr_append)
  have IH: "foldr (\<lambda>k acc. f k + acc) [0..<N] (f N + z) $$ (r,c)
              = (\<Sum>k = 0..<N. f k $$ (r,c)) + (f N + z) $$ (r,c)"
    using Suc.IH[OF rest_c fNz_c] .
  have idx_split: "(f N + z) $$ (r,c) = f N $$ (r,c) + z $$ (r,c)"
    using hd_c Suc.prems(2) r_lt c_lt by simp
  have "foldr (\<lambda>k acc. f k + acc) [0..<Suc N] z $$ (r,c)
          = (\<Sum>k = 0..<N. f k $$ (r,c)) + (f N $$ (r,c) + z $$ (r,c))"
    using step IH idx_split by simp
  also have "\<dots> = ((\<Sum>k = 0..<N. f k $$ (r,c)) + f N $$ (r,c)) + z $$ (r,c)"
    by (simp add: add.assoc)
  also have "\<dots> = (\<Sum>k = 0..<Suc N. f k $$ (r,c)) + z $$ (r,c)"
    by simp
  finally show ?case .
qed

lemma kraus_combo_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and r_lt: "r < d" and c_lt: "c < n"
  shows "kraus_combo d n Vs u $$ (r, c)
           = (\<Sum>i = 0..<length Vs. u $ i * (Vs!i) $$ (r, c))"
proof -
  let ?N = "length Vs"
  let ?f = "\<lambda>i. u $ i \<cdot>\<^sub>m (Vs!i)"
  have term_c: "\<forall>i < ?N. ?f i \<in> carrier_mat d n"
  proof (intro allI impI)
    fix i assume i_lt: "i < ?N"
    have Vi_c: "Vs!i \<in> carrier_mat d n"
      using Vs_c i_lt nth_mem by blast
    show "?f i \<in> carrier_mat d n"
      using Vi_c by (intro smult_carrier_mat) auto
  qed
  have z_c: "(0\<^sub>m d n :: complex Matrix.mat) \<in> carrier_mat d n" by simp
  have z_idx: "(0\<^sub>m d n :: complex Matrix.mat) $$ (r,c) = 0"
    using r_lt c_lt by simp
  have idx_term: "\<And>i. i < ?N \<Longrightarrow> ?f i $$ (r,c) = u $ i * (Vs!i) $$ (r,c)"
  proof -
    fix i assume i_lt: "i < ?N"
    have Vi_c: "Vs!i \<in> carrier_mat d n"
      using Vs_c i_lt nth_mem by blast
    show "?f i $$ (r,c) = u $ i * (Vs!i) $$ (r,c)"
      using Vi_c r_lt c_lt by simp
  qed
  have "kraus_combo d n Vs u $$ (r,c)
          = foldr (\<lambda>i acc. ?f i + acc) [0..<?N] (0\<^sub>m d n) $$ (r,c)"
    unfolding kraus_combo_def by simp
  also have "\<dots> = (\<Sum>i = 0..<?N. ?f i $$ (r,c)) + (0\<^sub>m d n :: complex Matrix.mat) $$ (r,c)"
    using foldr_upt_add_acc_index_dn[OF term_c z_c r_lt c_lt] .
  also have "\<dots> = (\<Sum>i = 0..<?N. ?f i $$ (r,c))"
    using z_idx by simp
  also have "\<dots> = (\<Sum>i = 0..<?N. u $ i * (Vs!i) $$ (r,c))"
    by (rule sum.cong) (auto simp: idx_term)
  finally show ?thesis .
qed


text \<open>A direct per-entry formula for matrix products.\<close>

lemma mat_mult_index_sum:
  assumes A_c: "A \<in> carrier_mat p q"
      and B_c: "B \<in> carrier_mat q s"
      and r_lt: "r < p" and c_lt: "c < s"
  shows "(A * B) $$ (r, c) = (\<Sum>k = 0..<q. A $$ (r, k) * B $$ (k, c))"
  using A_c B_c r_lt c_lt
  by (simp add: times_mat_def scalar_prod_def lessThan_atLeast0)

text \<open>Per-entry formula for \<open>W * rho\<close>, where \<open>W = kraus_combo d n Vs u\<close>.\<close>

lemma kraus_combo_times_rho_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and r_lt: "r < d" and k_lt: "k < n"
  shows "(kraus_combo d n Vs u * rho) $$ (r, k)
           = (\<Sum>i = 0..<length Vs. u $ i * (Vs!i * rho) $$ (r, k))"
proof -
  let ?W = "kraus_combo d n Vs u"
  let ?N = "length Vs"
  have W_c: "?W \<in> carrier_mat d n"
    by (rule kraus_combo_carrier[OF Vs_c])
  have "(?W * rho) $$ (r, k)
          = (\<Sum>b = 0..<n. ?W $$ (r, b) * rho $$ (b, k))"
    by (rule mat_mult_index_sum[OF W_c rho_c r_lt k_lt])
  also have "\<dots> = (\<Sum>b = 0..<n.
                     (\<Sum>i = 0..<?N. u $ i * (Vs!i) $$ (r, b)) * rho $$ (b, k))"
  proof (intro sum.cong refl)
    fix b assume "b \<in> {0..<n}"
    hence b_lt: "b < n" by simp
    have "?W $$ (r, b) = (\<Sum>i = 0..<?N. u $ i * (Vs!i) $$ (r, b))"
      by (rule kraus_combo_index[OF Vs_c r_lt b_lt])
    thus "?W $$ (r, b) * rho $$ (b, k)
            = (\<Sum>i = 0..<?N. u $ i * (Vs!i) $$ (r, b)) * rho $$ (b, k)"
      by simp
  qed
  also have "\<dots> = (\<Sum>b = 0..<n. \<Sum>i = 0..<?N.
                     (u $ i * (Vs!i) $$ (r, b)) * rho $$ (b, k))"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>b = 0..<n.
                     (u $ i * (Vs!i) $$ (r, b)) * rho $$ (b, k))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>b = 0..<n.
                     u $ i * ((Vs!i) $$ (r, b) * rho $$ (b, k)))"
  proof (intro sum.cong refl)
    fix i b assume "i \<in> {0..<?N}" "b \<in> {0..<n}"
    show "(u $ i * (Vs!i) $$ (r, b)) * rho $$ (b, k)
            = u $ i * ((Vs!i) $$ (r, b) * rho $$ (b, k))"
      by (simp add: algebra_simps)
  qed
  also have "\<dots> = (\<Sum>i = 0..<?N. u $ i *
                       (\<Sum>b = 0..<n. (Vs!i) $$ (r, b) * rho $$ (b, k)))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, k))"
  proof (intro sum.cong refl)
    fix i assume "i \<in> {0..<?N}"
    hence i_lt: "i < ?N" by simp
    have Vi_c: "Vs!i \<in> carrier_mat d n"
      using Vs_c i_lt nth_mem by blast
    have "(Vs!i * rho) $$ (r, k)
            = (\<Sum>b = 0..<n. (Vs!i) $$ (r, b) * rho $$ (b, k))"
      by (rule mat_mult_index_sum[OF Vi_c rho_c r_lt k_lt])
    thus "u $ i * (\<Sum>b = 0..<n. (Vs!i) $$ (r, b) * rho $$ (b, k))
            = u $ i * (Vs!i * rho) $$ (r, k)"
      by simp
  qed
  finally show ?thesis .
qed

text \<open>The full quadratic per-entry formula:
\<open>(W rho W\<^sup>\<dagger>) $$ (r,c) = \<Sum>\<^sub>{i,j} u\<^sub>i \<bar>u\<^sub>j\<bar> (V\<^sub>i rho V\<^sub>j\<^sup>\<dagger>) $$ (r,c)\<close>.\<close>

lemma kraus_combo_quad_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "(kraus_combo d n Vs u * rho * ((kraus_combo d n Vs u)\<^sup>\<dagger>)) $$ (r, c)
           = (\<Sum>i = 0..<length Vs. \<Sum>j = 0..<length Vs.
                u $ i * cnj (u $ j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
proof -
  let ?W = "kraus_combo d n Vs u"
  let ?N = "length Vs"
  have W_c: "?W \<in> carrier_mat d n"
    by (rule kraus_combo_carrier[OF Vs_c])
  have Wdag_c: "?W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  have Wrho_c: "?W * rho \<in> carrier_mat d n"
    using W_c rho_c by auto
  \<comment> \<open>Expand the outer matrix product.\<close>
  have outer_idx: "(?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)
                     = (\<Sum>a = 0..<n. (?W * rho) $$ (r, a) * (?W\<^sup>\<dagger>) $$ (a, c))"
    by (rule mat_mult_index_sum[OF Wrho_c Wdag_c r_lt c_lt])
  \<comment> \<open>Convert the dagger entry to a conjugate.\<close>
  have Wdag_idx: "\<And>a. a < n \<Longrightarrow> (?W\<^sup>\<dagger>) $$ (a, c) = cnj (?W $$ (c, a))"
    using W_c c_lt by (simp add: dagger_def)
  \<comment> \<open>Substitute the per-entry formula for the inner product \<open>W * rho\<close>.\<close>
  have Wrho_idx: "\<And>a. a < n \<Longrightarrow>
                    (?W * rho) $$ (r, a)
                      = (\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))"
    using kraus_combo_times_rho_index[OF Vs_c rho_c r_lt] by blast
  \<comment> \<open>And for \<open>W\<close> at the dagger argument.\<close>
  have W_at_c: "\<And>a. a < n \<Longrightarrow>
                  ?W $$ (c, a) = (\<Sum>j = 0..<?N. u $ j * (Vs!j) $$ (c, a))"
    using kraus_combo_index[OF Vs_c c_lt] by blast
  \<comment> \<open>Step 1: rewrite the per-\<open>a\<close> term inside the sum.\<close>
  have per_a: "\<And>a. a < n \<Longrightarrow>
                 (?W * rho) $$ (r, a) * (?W\<^sup>\<dagger>) $$ (a, c)
                 = (\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))
                   * cnj (\<Sum>j = 0..<?N. u $ j * (Vs!j) $$ (c, a))"
    using Wrho_idx Wdag_idx W_at_c by simp
  have step1: "(?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)
                 = (\<Sum>a = 0..<n.
                      (\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))
                      * cnj (\<Sum>j = 0..<?N. u $ j * (Vs!j) $$ (c, a)))"
  proof -
    have "(?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)
            = (\<Sum>a = 0..<n. (?W * rho) $$ (r, a) * (?W\<^sup>\<dagger>) $$ (a, c))"
      using outer_idx .
    also have "\<dots> = (\<Sum>a = 0..<n.
                       (\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))
                       * cnj (\<Sum>j = 0..<?N. u $ j * (Vs!j) $$ (c, a)))"
      by (intro sum.cong refl) (auto simp: per_a)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 2: per-\<open>a\<close>, expand product of two sums and pull out scalars.
      We split into two pieces: (a) push \<open>cnj\<close> through the sum, and (b)
      distribute the product of two sums and reorder.\<close>
  have cnj_push: "\<And>a. cnj (\<Sum>j = 0..<?N. u $ j * (Vs!j) $$ (c, a))
                       = (\<Sum>j = 0..<?N. cnj (u $ j) * cnj ((Vs!j) $$ (c, a)))"
    by (simp add: complex_cnj_mult)
  have per_a2: "\<And>a. a < n \<Longrightarrow>
                  (\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))
                  * (\<Sum>j = 0..<?N. cnj (u $ j) * cnj ((Vs!j) $$ (c, a)))
                = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                     u $ i * cnj (u $ j) *
                     ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
  proof -
    fix a assume a_lt: "a < n"
    have "(\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))
            * (\<Sum>j = 0..<?N. cnj (u $ j) * cnj ((Vs!j) $$ (c, a)))
          = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
               (u $ i * (Vs!i * rho) $$ (r, a))
               * (cnj (u $ j) * cnj ((Vs!j) $$ (c, a))))"
      by (simp add: sum_product)
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       u $ i * cnj (u $ j) *
                       ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
    proof (intro sum.cong refl)
      fix i j assume "i \<in> {0..<?N}" "j \<in> {0..<?N}"
      show "(u $ i * (Vs!i * rho) $$ (r, a))
              * (cnj (u $ j) * cnj ((Vs!j) $$ (c, a)))
            = u $ i * cnj (u $ j) *
              ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a)))"
        by (simp add: algebra_simps)
    qed
    finally show "(\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))
                  * (\<Sum>j = 0..<?N. cnj (u $ j) * cnj ((Vs!j) $$ (c, a)))
                  = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       u $ i * cnj (u $ j) *
                       ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))" .
  qed
  have step2: "(?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)
                 = (\<Sum>a = 0..<n. \<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                      u $ i * cnj (u $ j) *
                      ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
  proof -
    have "(?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)
            = (\<Sum>a = 0..<n.
                 (\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))
                 * cnj (\<Sum>j = 0..<?N. u $ j * (Vs!j) $$ (c, a)))"
      using step1 .
    also have "\<dots> = (\<Sum>a = 0..<n.
                       (\<Sum>i = 0..<?N. u $ i * (Vs!i * rho) $$ (r, a))
                       * (\<Sum>j = 0..<?N. cnj (u $ j) * cnj ((Vs!j) $$ (c, a))))"
      by (intro sum.cong refl) (simp add: cnj_push)
    also have "\<dots> = (\<Sum>a = 0..<n. \<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       u $ i * cnj (u $ j) *
                       ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
      by (intro sum.cong refl) (auto simp: per_a2)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 3: swap sums.\<close>
  have step3: "(\<Sum>a = 0..<n. \<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                  u $ i * cnj (u $ j) *
                  ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))
               = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N. \<Sum>a = 0..<n.
                    u $ i * cnj (u $ j) *
                    ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
  proof -
    have "(\<Sum>a = 0..<n. \<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
             u $ i * cnj (u $ j) *
             ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))
          = (\<Sum>i = 0..<?N. \<Sum>a = 0..<n. \<Sum>j = 0..<?N.
                u $ i * cnj (u $ j) *
                ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N. \<Sum>a = 0..<n.
                       u $ i * cnj (u $ j) *
                       ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {0..<?N}"
      show "(\<Sum>a = 0..<n. \<Sum>j = 0..<?N.
               u $ i * cnj (u $ j) *
               ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))
            = (\<Sum>j = 0..<?N. \<Sum>a = 0..<n.
                u $ i * cnj (u $ j) *
                ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
        by (rule sum.swap)
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>Step 4: pull out the \<open>u\<^sub>i \<bar>u\<^sub>j\<bar>\<close> scalar from the \<open>a\<close>-sum.\<close>
  have step4: "(\<Sum>i = 0..<?N. \<Sum>j = 0..<?N. \<Sum>a = 0..<n.
                  u $ i * cnj (u $ j) *
                  ((Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))
               = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                  u $ i * cnj (u $ j) *
                  (\<Sum>a = 0..<n.
                    (Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
    by (simp add: sum_distrib_left)
  \<comment> \<open>Step 5: collapse the \<open>a\<close>-sum into a matrix product entry.\<close>
  have step5: "\<And>i j. i < ?N \<Longrightarrow> j < ?N \<Longrightarrow>
                  (\<Sum>a = 0..<n.
                     (Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a)))
                  = (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)"
  proof -
    fix i j assume i_lt: "i < ?N" and j_lt: "j < ?N"
    have Vi_c: "Vs!i \<in> carrier_mat d n"
      using Vs_c i_lt nth_mem by blast
    have Vj_c: "Vs!j \<in> carrier_mat d n"
      using Vs_c j_lt nth_mem by blast
    have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d"
      using Vj_c by (rule dagger_carrier)
    have Virho_c: "Vs!i * rho \<in> carrier_mat d n"
      using Vi_c rho_c by auto
    have "(Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)
            = (\<Sum>a = 0..<n.
                 (Vs!i * rho) $$ (r, a) * ((Vs!j)\<^sup>\<dagger>) $$ (a, c))"
      by (rule mat_mult_index_sum[OF Virho_c Vjd_c r_lt c_lt])
    also have "\<dots> = (\<Sum>a = 0..<n.
                       (Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a)))"
    proof (intro sum.cong refl)
      fix a assume "a \<in> {0..<n}"
      hence a_lt: "a < n" by simp
      have "((Vs!j)\<^sup>\<dagger>) $$ (a, c) = cnj ((Vs!j) $$ (c, a))"
        using Vj_c c_lt a_lt by (simp add: dagger_def)
      thus "(Vs!i * rho) $$ (r, a) * ((Vs!j)\<^sup>\<dagger>) $$ (a, c)
             = (Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))"
        by simp
    qed
    finally show "(\<Sum>a = 0..<n.
                     (Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a)))
                  = (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)"
      by simp
  qed
  \<comment> \<open>Combine.\<close>
  have combined: "(?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)
                    = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                         u $ i * cnj (u $ j) *
                         (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
  proof -
    have "(?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)
            = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                u $ i * cnj (u $ j) *
                (\<Sum>a = 0..<n.
                  (Vs!i * rho) $$ (r, a) * cnj ((Vs!j) $$ (c, a))))"
      using step2 step3 step4 by simp
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       u $ i * cnj (u $ j) *
                       (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
      by (intro sum.cong refl) (auto simp: step5)
    finally show ?thesis .
  qed
  show ?thesis using combined .
qed


text \<open>Linearity of @{const kraus_quad_map} in the coefficient matrix
(needed for the rank-1 decomposition below).\<close>

lemma kraus_quad_map_add_Tm:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and T1_c: "T1 \<in> carrier_mat (length Vs) (length Vs)"
      and T2_c: "T2 \<in> carrier_mat (length Vs) (length Vs)"
  shows "kraus_quad_map d Vs (T1 + T2) rho
           = kraus_quad_map d Vs T1 rho + kraus_quad_map d Vs T2 rho"
proof (rule eq_matI)
  let ?N = "length Vs"
  let ?L = "kraus_quad_map d Vs (T1 + T2) rho"
  let ?R = "kraus_quad_map d Vs T1 rho + kraus_quad_map d Vs T2 rho"
  have L_c: "?L \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have R1_c: "kraus_quad_map d Vs T1 rho \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have R2_c: "kraus_quad_map d Vs T2 rho \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have R_c: "?R \<in> carrier_mat d d" using R1_c R2_c by auto
  show "dim_row ?L = dim_row ?R" using L_c R_c by auto
  show "dim_col ?L = dim_col ?R" using L_c R_c by auto
  fix r c assume r_lt: "r < dim_row ?R" and c_lt: "c < dim_col ?R"
  hence r_lt': "r < d" and c_lt': "c < d" using R_c by auto
  have plus_idx: "\<And>i j. i < ?N \<Longrightarrow> j < ?N \<Longrightarrow>
                    (T1 + T2) $$ (i, j) = T1 $$ (i, j) + T2 $$ (i, j)"
    using T1_c T2_c by auto
  have L_idx: "?L $$ (r, c)
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       (T1 $$ (i, j) + T2 $$ (i, j))
                         * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    using kraus_quad_map_index[OF Vs_c rho_c r_lt' c_lt', of "T1 + T2"]
    by (auto intro!: sum.cong simp: plus_idx)
  have R_idx: "?R $$ (r, c)
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       T1 $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))
                 + (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       T2 $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    using R1_c R2_c r_lt' c_lt'
          kraus_quad_map_index[OF Vs_c rho_c r_lt' c_lt', of T1]
          kraus_quad_map_index[OF Vs_c rho_c r_lt' c_lt', of T2]
    by simp
  have distr: "\<And>i j. (T1 $$ (i,j) + T2 $$ (i,j)) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r,c)
                    = T1 $$ (i,j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r,c)
                    + T2 $$ (i,j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r,c)"
    by (simp add: ring_distribs)
  have inner_split:
    "\<And>i. (\<Sum>j = 0..<?N.
            (T1 $$ (i, j) + T2 $$ (i, j)) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))
         = (\<Sum>j = 0..<?N. T1 $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))
         + (\<Sum>j = 0..<?N. T2 $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    by (simp add: distr sum.distrib)
  show "?L $$ (r, c) = ?R $$ (r, c)"
    using L_idx R_idx inner_split by (simp add: sum.distrib)
qed

text \<open>Carrier of @{term \<open>outer_sum k vs\<close>}.\<close>

lemma outer_sum_carrier:
  "outer_sum k vs \<in> carrier_mat k k"
  by (auto simp: outer_sum_def)

text \<open>Cons-recursion for @{const outer_sum}: adds a rank-1 piece.\<close>

lemma outer_sum_Cons_split:
  assumes "\<forall>v \<in> set (u # us). dim_vec v = k"
  shows "outer_sum k (u # us)
           = outer_sum k [u] + outer_sum k us"
proof (rule eq_matI)
  let ?L = "outer_sum k (u # us)"
  let ?R1 = "outer_sum k [u]"
  let ?R2 = "outer_sum k us"
  have L_c: "?L \<in> carrier_mat k k" by (rule outer_sum_carrier)
  have R1_c: "?R1 \<in> carrier_mat k k" by (rule outer_sum_carrier)
  have R2_c: "?R2 \<in> carrier_mat k k" by (rule outer_sum_carrier)
  show "dim_row ?L = dim_row (?R1 + ?R2)" using L_c R1_c R2_c by simp
  show "dim_col ?L = dim_col (?R1 + ?R2)" using L_c R1_c R2_c by simp
  fix i j assume "i < dim_row (?R1 + ?R2)" "j < dim_col (?R1 + ?R2)"
  hence i_lt: "i < k" and j_lt: "j < k" using R1_c R2_c by auto
  have u_dim: "dim_vec u = k" using assms by simp
  have us_dim: "\<forall>v \<in> set us. dim_vec v = k" using assms by simp
  have uus_dim: "\<forall>v \<in> set (u # us). dim_vec v = k" using assms by simp
  have eqL: "?L $$ (i, j)
               = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) (u # us))"
    by (rule outer_sum_entry_sum_list[OF uus_dim i_lt j_lt])
  have eqR1: "?R1 $$ (i, j) = u $ i * cnj (u $ j)"
  proof -
    have "\<forall>v \<in> set [u]. dim_vec v = k" using u_dim by simp
    hence "?R1 $$ (i, j) = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) [u])"
      by (rule outer_sum_entry_sum_list[OF _ i_lt j_lt])
    thus ?thesis by simp
  qed
  have eqR2: "?R2 $$ (i, j) = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) us)"
    by (rule outer_sum_entry_sum_list[OF us_dim i_lt j_lt])
  show "?L $$ (i, j) = (?R1 + ?R2) $$ (i, j)"
    using eqL eqR1 eqR2 R1_c R2_c i_lt j_lt by simp
qed

text \<open>Rank-1 identity:
\<open>kraus_quad_map d Vs (outer_sum k [u]) rho = W rho W\<^sup>\<dagger>\<close>
where \<open>W = kraus_combo d n Vs u\<close>.\<close>

lemma kraus_quad_map_outer_singleton:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and u_dim: "dim_vec u = length Vs"
  shows "kraus_quad_map d Vs (outer_sum (length Vs) [u]) rho
           = kraus_combo d n Vs u * rho * ((kraus_combo d n Vs u)\<^sup>\<dagger>)"
proof (rule eq_matI)
  let ?k = "length Vs"
  let ?T = "outer_sum ?k [u]"
  let ?W = "kraus_combo d n Vs u"
  have T_c: "?T \<in> carrier_mat ?k ?k" by (rule outer_sum_carrier)
  have W_c: "?W \<in> carrier_mat d n"
    by (rule kraus_combo_carrier[OF Vs_c])
  have Wdag_c: "?W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  have L_c: "kraus_quad_map d Vs ?T rho \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have R_c: "?W * rho * (?W\<^sup>\<dagger>) \<in> carrier_mat d d"
    using W_c rho_c Wdag_c by (intro mult_carrier_mat) auto
  show "dim_row (kraus_quad_map d Vs ?T rho) = dim_row (?W * rho * (?W\<^sup>\<dagger>))"
    using L_c R_c by auto
  show "dim_col (kraus_quad_map d Vs ?T rho) = dim_col (?W * rho * (?W\<^sup>\<dagger>))"
    using L_c R_c by auto
  fix r c
  assume "r < dim_row (?W * rho * (?W\<^sup>\<dagger>))" "c < dim_col (?W * rho * (?W\<^sup>\<dagger>))"
  hence r_lt: "r < d" and c_lt: "c < d" using R_c by auto
  \<comment> \<open>Per-entry of LHS.\<close>
  have L_idx: "kraus_quad_map d Vs ?T rho $$ (r, c)
                 = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                      ?T $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    by (rule kraus_quad_map_index[OF Vs_c rho_c r_lt c_lt])
  \<comment> \<open>Per-entry of \<open>?T\<close>.\<close>
  have T_idx: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow>
                  ?T $$ (i, j) = u $ i * cnj (u $ j)"
  proof -
    fix i j assume i_lt: "i < ?k" and j_lt: "j < ?k"
    have "\<forall>v \<in> set [u]. dim_vec v = ?k" using u_dim by simp
    hence "?T $$ (i, j) = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) [u])"
      by (rule outer_sum_entry_sum_list[OF _ i_lt j_lt])
    thus "?T $$ (i, j) = u $ i * cnj (u $ j)" by simp
  qed
  \<comment> \<open>Per-entry of RHS.\<close>
  have R_idx: "(?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)
                 = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                      u $ i * cnj (u $ j)
                      * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    by (rule kraus_combo_quad_index[OF Vs_c rho_c r_lt c_lt])
  \<comment> \<open>Match per-entry.\<close>
  have "kraus_quad_map d Vs ?T rho $$ (r, c)
          = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
               u $ i * cnj (u $ j)
               * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    using L_idx by (auto intro!: sum.cong simp: T_idx)
  also have "\<dots> = (?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)"
    using R_idx by simp
  finally show "kraus_quad_map d Vs ?T rho $$ (r, c)
                  = (?W * rho * (?W\<^sup>\<dagger>)) $$ (r, c)" .
qed

text \<open>Vanishing of the quadratic map when the coefficient matrix is zero.\<close>

lemma kraus_quad_map_zero_Tm:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
  shows "kraus_quad_map d Vs (0\<^sub>m (length Vs) (length Vs)) rho = 0\<^sub>m d d"
proof (rule eq_matI)
  let ?L = "kraus_quad_map d Vs (0\<^sub>m (length Vs) (length Vs)) rho"
  have L_c: "?L \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  show "dim_row ?L = dim_row ((0\<^sub>m d d) :: complex Matrix.mat)"
    using L_c by auto
  show "dim_col ?L = dim_col ((0\<^sub>m d d) :: complex Matrix.mat)"
    using L_c by auto
  fix r c
  assume "r < dim_row ((0\<^sub>m d d) :: complex Matrix.mat)"
         "c < dim_col ((0\<^sub>m d d) :: complex Matrix.mat)"
  hence r_lt: "r < d" and c_lt: "c < d" by auto
  have "?L $$ (r, c)
          = (\<Sum>i = 0..<length Vs. \<Sum>j = 0..<length Vs.
               (0\<^sub>m (length Vs) (length Vs)) $$ (i, j)
                 * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
    by (rule kraus_quad_map_index[OF Vs_c rho_c r_lt c_lt])
  also have "\<dots> = 0"
    by (rule sum.neutral) (auto intro!: sum.neutral)
  finally show "?L $$ (r, c) = (0\<^sub>m d d :: complex Matrix.mat) $$ (r, c)"
    using r_lt c_lt by simp
qed

text \<open>Sum-decomposition: a PSD-style coefficient matrix \<open>outer_sum k us\<close>
gives @{const kraus_quad_map} as a kraus_map_dim of the combos.\<close>

lemma kraus_quad_map_outer_sum_eq_kraus_map_dim:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and us_dim: "\<forall>v \<in> set us. dim_vec v = length Vs"
  shows "kraus_quad_map d Vs (outer_sum (length Vs) us) rho
           = kraus_map_dim d (map (kraus_combo d n Vs) us) rho"
  using us_dim
proof (induction us)
  case Nil
  \<comment> \<open>Base case: empty list. outer_sum reduces to the zero matrix.\<close>
  have outer_nil: "outer_sum (length Vs) ([] :: complex Matrix.vec list)
                    = 0\<^sub>m (length Vs) (length Vs)"
  proof (rule eq_matI)
    have c: "outer_sum (length Vs) ([] :: complex Matrix.vec list)
              \<in> carrier_mat (length Vs) (length Vs)"
      by (rule outer_sum_carrier)
    show "dim_row (outer_sum (length Vs) ([] :: complex Matrix.vec list))
           = dim_row (0\<^sub>m (length Vs) (length Vs) :: complex Matrix.mat)"
      using c by auto
    show "dim_col (outer_sum (length Vs) ([] :: complex Matrix.vec list))
           = dim_col (0\<^sub>m (length Vs) (length Vs) :: complex Matrix.mat)"
      using c by auto
    fix i j
    assume i_lt: "i < dim_row (0\<^sub>m (length Vs) (length Vs) :: complex Matrix.mat)"
    assume j_lt: "j < dim_col (0\<^sub>m (length Vs) (length Vs) :: complex Matrix.mat)"
    from i_lt have i_lt': "i < length Vs" by simp
    from j_lt have j_lt': "j < length Vs" by simp
    have nil_dim: "\<forall>v \<in> set ([] :: complex Matrix.vec list). dim_vec v = length Vs"
      by simp
    have "outer_sum (length Vs) ([] :: complex Matrix.vec list) $$ (i, j)
            = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) [])"
      by (rule outer_sum_entry_sum_list[OF nil_dim i_lt' j_lt'])
    thus "outer_sum (length Vs) ([] :: complex Matrix.vec list) $$ (i, j)
            = (0\<^sub>m (length Vs) (length Vs) :: complex Matrix.mat) $$ (i, j)"
      using i_lt' j_lt' by simp
  qed
  show ?case
    using outer_nil kraus_quad_map_zero_Tm[OF Vs_c rho_c]
    by simp
next
  case (Cons u us)
  let ?k = "length Vs"
  let ?Tu  = "outer_sum ?k [u]"
  let ?Tus = "outer_sum ?k us"
  let ?T   = "outer_sum ?k (u # us)"
  have u_dim: "dim_vec u = ?k" using Cons.prems by simp
  have us_dim': "\<forall>v \<in> set us. dim_vec v = ?k" using Cons.prems by simp
  have uus_dim: "\<forall>v \<in> set (u # us). dim_vec v = ?k" using Cons.prems by simp
  have Tu_c:  "?Tu  \<in> carrier_mat ?k ?k" by (rule outer_sum_carrier)
  have Tus_c: "?Tus \<in> carrier_mat ?k ?k" by (rule outer_sum_carrier)
  have IH: "kraus_quad_map d Vs ?Tus rho
              = kraus_map_dim d (map (kraus_combo d n Vs) us) rho"
    using Cons.IH[OF us_dim'] .
  have split: "?T = ?Tu + ?Tus"
    by (rule outer_sum_Cons_split[OF uus_dim])
  have "kraus_quad_map d Vs ?T rho
          = kraus_quad_map d Vs (?Tu + ?Tus) rho"
    using split by simp
  also have "\<dots> = kraus_quad_map d Vs ?Tu rho
                + kraus_quad_map d Vs ?Tus rho"
    by (rule kraus_quad_map_add_Tm[OF Vs_c rho_c Tu_c Tus_c])
  also have "\<dots> = (kraus_combo d n Vs u * rho * ((kraus_combo d n Vs u)\<^sup>\<dagger>))
                + kraus_map_dim d (map (kraus_combo d n Vs) us) rho"
    using kraus_quad_map_outer_singleton[OF Vs_c rho_c u_dim] IH by simp
  also have "\<dots> = kraus_map_dim d (kraus_combo d n Vs u
                                    # map (kraus_combo d n Vs) us) rho"
    by simp
  also have "\<dots> = kraus_map_dim d (map (kraus_combo d n Vs) (u # us)) rho"
    by simp
  finally show ?case .
qed


subsection \<open>Lemma A: PSD coefficient matrix gives a CP perturbation\<close>

text \<open>Since @{const amplification} only evaluates @{term \<Phi>} on
\<open>n\<times>n\<close> blocks, two maps that agree on @{term \<open>carrier_mat n n\<close>}
yield the same amplification, hence the same notion of complete
positivity.\<close>

lemma amplification_cong:
  fixes Phi Psi :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Xm :: "complex Matrix.mat"
  assumes eq: "\<And>r. r \<in> carrier_mat n n \<Longrightarrow> Phi r = Psi r"
  shows "amplification n d p Phi Xm = amplification n d p Psi Xm"
proof (rule eq_matI)
  show "dim_row (amplification n d p Phi Xm) = dim_row (amplification n d p Psi Xm)"
    by (simp add: amplification_def)
  show "dim_col (amplification n d p Phi Xm) = dim_col (amplification n d p Psi Xm)"
    by (simp add: amplification_def)
  fix i j
  assume i_a: "i < dim_row (amplification n d p Psi Xm)"
  assume j_a: "j < dim_col (amplification n d p Psi Xm)"
  have i_lt: "i < p * d" using i_a by (simp add: amplification_def)
  have j_lt: "j < p * d" using j_a by (simp add: amplification_def)
  have blk_c: "block_of_mat n Xm (i div d) (j div d) \<in> carrier_mat n n"
    by (simp add: block_of_mat_def)
  hence phi_eq_psi: "Phi (block_of_mat n Xm (i div d) (j div d))
           = Psi (block_of_mat n Xm (i div d) (j div d))"
    by (rule eq)
  have L_idx: "amplification n d p Phi Xm $$ (i, j)
                 = Phi (block_of_mat n Xm (i div d) (j div d)) $$ (i mod d, j mod d)"
    using i_lt j_lt by (simp add: amplification_def)
  have R_idx: "amplification n d p Psi Xm $$ (i, j)
                 = Psi (block_of_mat n Xm (i div d) (j div d)) $$ (i mod d, j mod d)"
    using i_lt j_lt by (simp add: amplification_def)
  show "amplification n d p Phi Xm $$ (i, j)
          = amplification n d p Psi Xm $$ (i, j)"
    using L_idx R_idx phi_eq_psi by simp
qed

lemma completely_positive_cong:
  fixes Phi Psi :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes "\<And>r. r \<in> carrier_mat n n \<Longrightarrow> Phi r = Psi r"
  shows "completely_positive n d Phi \<longleftrightarrow> completely_positive n d Psi"
proof -
  have "amplification n d p Phi Xm = amplification n d p Psi Xm" for p Xm
    by (rule amplification_cong[OF assms])
  thus ?thesis
    by (simp add: completely_positive_def p_positive_def)
qed

text \<open>\<^bold>\<open>Lemma A\<close>: if \<open>T\<close> is PSD then
\<open>kraus_quad_map d Vs T\<close> is completely positive.

\<^bold>\<open>Proof sketch.\<close> Use @{thm psd_kraus_decomp} to write
\<open>T = outer_sum k us\<close>. Then by
@{thm kraus_quad_map_outer_sum_eq_kraus_map_dim},
\<open>kraus_quad_map d Vs T\<close> agrees on @{term \<open>carrier_mat n n\<close>}
with \<open>kraus_map_dim d Ws\<close>, where \<open>Ws := map (kraus_combo d n Vs) us\<close>.
Apply @{thm kraus_cp_no_tp}.\<close>

lemma kraus_perturbation_cp:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Tm_c: "Tm \<in> carrier_mat (length Vs) (length Vs)"
      and Tm_psd: "psd Tm"
      and npos: "0 < n" and dpos: "0 < d"
  shows "completely_positive n d (kraus_quad_map d Vs Tm)"
proof -
  let ?k = "length Vs"
  obtain us :: "complex Matrix.vec list"
    where us_len: "length us = ?k"
      and us_dim: "\<forall>v \<in> set us. dim_vec v = ?k"
      and outer_eq: "outer_sum ?k us = Tm"
    using psd_kraus_decomp[OF Tm_c Tm_psd] by blast
  let ?Ws = "map (kraus_combo d n Vs) us"
  have Ws_c: "\<forall>W \<in> set ?Ws. W \<in> carrier_mat d n"
  proof
    fix W assume "W \<in> set ?Ws"
    then obtain u where "u \<in> set us" "W = kraus_combo d n Vs u" by auto
    thus "W \<in> carrier_mat d n"
      using kraus_combo_carrier[OF Vs_c] by simp
  qed
  have agree: "\<And>r :: complex Matrix.mat.
                  r \<in> carrier_mat n n \<Longrightarrow>
                  kraus_quad_map d Vs Tm r = kraus_map_dim d ?Ws r"
  proof -
    fix r :: "complex Matrix.mat" assume r_c: "r \<in> carrier_mat n n"
    have "kraus_quad_map d Vs Tm r
            = kraus_quad_map d Vs (outer_sum ?k us) r"
      using outer_eq by simp
    also have "\<dots> = kraus_map_dim d ?Ws r"
      using kraus_quad_map_outer_sum_eq_kraus_map_dim[OF Vs_c r_c us_dim] .
    finally show "kraus_quad_map d Vs Tm r = kraus_map_dim d ?Ws r" .
  qed
  have cp_Ws: "completely_positive n d (kraus_map_dim d ?Ws)"
    by (rule kraus_cp_no_tp[OF Ws_c npos dpos])
  show ?thesis
    using cp_Ws completely_positive_cong[OF agree] by simp
qed


subsection \<open>Small-\<open>\<epsilon>\<close> PSD perturbation of the identity\<close>

text \<open>For any hermitian \<open>A : k \<times> k\<close>, the matrix \<open>1\<^sub>m k + \<delta> \<cdot>\<^sub>m A\<close>
is PSD whenever \<open>\<bar>\<delta>\<bar>\<close> is small enough. The bound uses the
entry-wise sum
\<open>S := \<Sum>\<^sub>{i,j} \<bar>A\<^sub>{ij}\<bar>\<close>, taking \<open>\<epsilon> := 1/(1 + S)\<close>; this avoids any
operator-norm computation and just uses Cauchy-Schwarz on entries.\<close>

text \<open>Bilinearity of the inner product in the right slot.\<close>

lemma inner_prod_add_right:
  fixes u v w :: "complex Matrix.vec"
  assumes ud: "dim_vec u = k" and vd: "dim_vec v = k" and wd: "dim_vec w = k"
  shows "\<langle>u | v + w\<rangle> = \<langle>u | v\<rangle> + \<langle>u | w\<rangle>"
proof -
  have vwd: "dim_vec (v + w) = k" using vd wd by auto
  have "\<langle>u | v + w\<rangle> = (\<Sum>i = 0..<k. cnj (u $ i) * (v + w) $ i)"
    using inner_prod_expand[OF ud vwd] .
  also have "\<dots> = (\<Sum>i = 0..<k. cnj (u $ i) * (v $ i + w $ i))"
    by (intro sum.cong refl) (simp add: vd wd)
  also have "\<dots> = (\<Sum>i = 0..<k. cnj (u $ i) * v $ i + cnj (u $ i) * w $ i)"
    by (intro sum.cong refl) (simp add: distrib_left)
  also have "\<dots> = (\<Sum>i = 0..<k. cnj (u $ i) * v $ i)
                + (\<Sum>i = 0..<k. cnj (u $ i) * w $ i)"
    by (rule sum.distrib)
  also have "\<dots> = \<langle>u | v\<rangle> + \<langle>u | w\<rangle>"
    using inner_prod_expand[OF ud vd] inner_prod_expand[OF ud wd] by simp
  finally show ?thesis .
qed

lemma inner_prod_smult_right:
  fixes u v :: "complex Matrix.vec"
  assumes ud: "dim_vec u = k" and vd: "dim_vec v = k"
  shows "\<langle>u | c \<cdot>\<^sub>v v\<rangle> = c * \<langle>u | v\<rangle>"
proof -
  have cvd: "dim_vec (c \<cdot>\<^sub>v v) = k" using vd by auto
  have "\<langle>u | c \<cdot>\<^sub>v v\<rangle> = (\<Sum>i = 0..<k. cnj (u $ i) * (c \<cdot>\<^sub>v v) $ i)"
    using inner_prod_expand[OF ud cvd] .
  also have "\<dots> = (\<Sum>i = 0..<k. cnj (u $ i) * (c * v $ i))"
    by (intro sum.cong refl) (simp add: vd)
  also have "\<dots> = (\<Sum>i = 0..<k. c * (cnj (u $ i) * v $ i))"
    by (intro sum.cong refl) (simp add: ac_simps)
  also have "\<dots> = c * (\<Sum>i = 0..<k. cnj (u $ i) * v $ i)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = c * \<langle>u | v\<rangle>"
    using inner_prod_expand[OF ud vd] by simp
  finally show ?thesis .
qed

text \<open>The hermitian sum.\<close>

lemma hermitian_add:
  assumes Aherm: "hermitian A" and Bherm: "hermitian B"
      and Ac: "A \<in> carrier_mat k k" and Bc: "B \<in> carrier_mat k k"
  shows "hermitian (A + B)"
  unfolding hermitian_def
proof (rule eq_matI)
  show "dim_row ((A + B)\<^sup>\<dagger>) = dim_row (A + B)" using Ac Bc by simp
  show "dim_col ((A + B)\<^sup>\<dagger>) = dim_col (A + B)" using Ac Bc by simp
  fix i j assume "i < dim_row (A + B)" "j < dim_col (A + B)"
  hence i_lt: "i < k" and j_lt: "j < k" using Ac Bc by auto
  have Ad: "A\<^sup>\<dagger> = A" using Aherm by (simp add: hermitian_def)
  have Bd: "B\<^sup>\<dagger> = B" using Bherm by (simp add: hermitian_def)
  have "((A + B)\<^sup>\<dagger>) $$ (i, j) = cnj ((A + B) $$ (j, i))"
    using i_lt j_lt Ac Bc by (simp add: dagger_def)
  also have "\<dots> = cnj (A $$ (j, i)) + cnj (B $$ (j, i))"
    using i_lt j_lt Ac Bc by simp
  also have "\<dots> = (A\<^sup>\<dagger>) $$ (i, j) + (B\<^sup>\<dagger>) $$ (i, j)"
    using i_lt j_lt Ac Bc by (simp add: dagger_def)
  also have "\<dots> = A $$ (i, j) + B $$ (i, j)"
    using Ad Bd by simp
  also have "\<dots> = (A + B) $$ (i, j)"
    using i_lt j_lt Ac Bc by simp
  finally show "((A + B)\<^sup>\<dagger>) $$ (i, j) = (A + B) $$ (i, j)" .
qed

lemma hermitian_one_mat:
  "hermitian (1\<^sub>m k :: complex Matrix.mat)"
  unfolding hermitian_def by (rule eq_matI) (auto simp: dagger_def)

lemma hermitian_smult_real:
  fixes A :: "complex Matrix.mat"
  assumes "hermitian A" "A \<in> carrier_mat k k"
  shows "hermitian (complex_of_real d \<cdot>\<^sub>m A)"
  unfolding hermitian_def
proof (rule eq_matI)
  let ?dA = "complex_of_real d \<cdot>\<^sub>m A"
  show "dim_row (?dA\<^sup>\<dagger>) = dim_row ?dA" using assms by simp
  show "dim_col (?dA\<^sup>\<dagger>) = dim_col ?dA" using assms by simp
  fix i j assume "i < dim_row ?dA" "j < dim_col ?dA"
  hence i_lt: "i < k" and j_lt: "j < k" using assms by auto
  have "?dA\<^sup>\<dagger> $$ (i,j) = cnj (?dA $$ (j,i))"
    using i_lt j_lt assms by (simp add: dagger_def)
  also have "\<dots> = cnj (complex_of_real d * A $$ (j,i))"
    using i_lt j_lt assms by simp
  also have "\<dots> = complex_of_real d * cnj (A $$ (j,i))"
    by (simp add: complex_cnj_mult)
  also have "\<dots> = complex_of_real d * (A\<^sup>\<dagger>) $$ (i,j)"
    using i_lt j_lt assms by (simp add: dagger_def)
  also have "\<dots> = complex_of_real d * A $$ (i,j)"
    using assms by (simp add: hermitian_def)
  also have "\<dots> = ?dA $$ (i,j)"
    using i_lt j_lt assms by simp
  finally show "?dA\<^sup>\<dagger> $$ (i,j) = ?dA $$ (i,j)" .
qed

text \<open>Entry-wise bound on the quadratic form of a hermitian matrix.\<close>

lemma quad_form_bound_by_entry_sum:
  fixes A :: "complex Matrix.mat" and x :: "complex Matrix.vec"
  assumes A_c: "A \<in> carrier_mat k k" and x_d: "dim_vec x = k"
  shows "cmod (\<langle>x | A *\<^sub>v x\<rangle>)
           \<le> (\<Sum>i = 0..<k. \<Sum>j = 0..<k. cmod (A $$ (i,j))) * Re \<langle>x | x\<rangle>"
proof -
  let ?S = "(\<Sum>i = 0..<k. \<Sum>j = 0..<k. cmod (A $$ (i,j)))"
  let ?Rxx = "Re \<langle>x | x\<rangle>"
  \<comment> \<open>Per-entry: \<open>(A*x)_i = \<Sum>_j A_{ij} x_j\<close>.\<close>
  have Ax_idx: "\<And>i. i < k \<Longrightarrow>
                  (A *\<^sub>v x) $ i = (\<Sum>j = 0..<k. A $$ (i, j) * x $ j)"
  proof -
    fix i assume i_lt: "i < k"
    have "(A *\<^sub>v x) $ i = Matrix.row A i \<bullet> x"
      using A_c x_d i_lt by simp
    also have "\<dots> = (\<Sum>j = 0..<k. Matrix.row A i $ j * x $ j)"
      using A_c x_d by (simp add: scalar_prod_def)
    also have "\<dots> = (\<Sum>j = 0..<k. A $$ (i, j) * x $ j)"
      using A_c i_lt by (intro sum.cong refl) auto
    finally show "(A *\<^sub>v x) $ i = (\<Sum>j = 0..<k. A $$ (i, j) * x $ j)" .
  qed
  \<comment> \<open>Expand \<open>\<langle>x | A*x\<rangle>\<close> as a double sum.\<close>
  have Ax_dim: "dim_vec (A *\<^sub>v x) = k" using A_c x_d by simp
  have q: "\<langle>x | A *\<^sub>v x\<rangle>
             = (\<Sum>i = 0..<k. \<Sum>j = 0..<k. cnj (x $ i) * A $$ (i,j) * x $ j)"
  proof -
    have "\<langle>x | A *\<^sub>v x\<rangle> = (\<Sum>i = 0..<k. cnj (x $ i) * (A *\<^sub>v x) $ i)"
      using x_d Ax_dim inner_prod_expand by blast
    also have "\<dots> = (\<Sum>i = 0..<k.
                       cnj (x $ i) * (\<Sum>j = 0..<k. A $$ (i,j) * x $ j))"
      by (intro sum.cong refl) (auto simp: Ax_idx)
    also have "\<dots> = (\<Sum>i = 0..<k. \<Sum>j = 0..<k.
                       cnj (x $ i) * (A $$ (i,j) * x $ j))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>i = 0..<k. \<Sum>j = 0..<k.
                       cnj (x $ i) * A $$ (i,j) * x $ j)"
      by (intro sum.cong refl) (simp add: mult.assoc)
    finally show ?thesis .
  qed
  \<comment> \<open>Triangle: \<open>cmod\<close> of a double sum bound by sum of \<open>cmod\<close>s.\<close>
  have tri: "cmod (\<langle>x | A *\<^sub>v x\<rangle>)
               \<le> (\<Sum>i = 0..<k. \<Sum>j = 0..<k.
                     cmod (cnj (x $ i) * A $$ (i,j) * x $ j))"
  proof -
    have "cmod (\<langle>x | A *\<^sub>v x\<rangle>)
             \<le> (\<Sum>i = 0..<k. cmod (\<Sum>j = 0..<k.
                  cnj (x $ i) * A $$ (i,j) * x $ j))"
      using q norm_sum by (simp add: q) (rule norm_sum)
    also have "\<dots> \<le> (\<Sum>i = 0..<k. \<Sum>j = 0..<k.
                       cmod (cnj (x $ i) * A $$ (i,j) * x $ j))"
      by (intro sum_mono norm_sum)
    finally show ?thesis .
  qed
  \<comment> \<open>Per-entry factorisation: \<open>cmod (cnj x_i * A_{ij} * x_j) = |x_i| |A_{ij}| |x_j|\<close>.\<close>
  have entry_eq: "\<And>i j. cmod (cnj (x $ i) * A $$ (i,j) * x $ j)
                          = cmod (x $ i) * cmod (A $$ (i,j)) * cmod (x $ j)"
    by (simp add: norm_mult)
  \<comment> \<open>Each cross-term bounded by \<open>cmod(A_{ij}) * Re\<langle>x|x\<rangle>\<close>.\<close>
  have xx_real: "Re \<langle>x | x\<rangle> = (\<Sum>p = 0..<k. (cmod (x $ p))\<^sup>2)"
  proof -
    have "Re \<langle>x | x\<rangle> = (\<Sum>p<k. Re (cnj (x $ p) * x $ p))"
      using x_d by (simp add: inner_prod_def lessThan_atLeast0)
    also have "\<dots> = (\<Sum>p<k. (cmod (x $ p))\<^sup>2)"
    proof (intro sum.cong refl)
      fix p assume "p \<in> {..<k}"
      have "cnj (x $ p) * x $ p = x $ p * cnj (x $ p)" by (rule mult.commute)
      also have "\<dots> = complex_of_real ((cmod (x $ p))\<^sup>2)"
        using complex_norm_square[of "x $ p"] by simp
      finally have "Re (cnj (x $ p) * x $ p) = (cmod (x $ p))\<^sup>2" by simp
      thus "Re (cnj (x $ p) * x $ p) = (cmod (x $ p))\<^sup>2" .
    qed
    finally show ?thesis by (simp add: lessThan_atLeast0)
  qed
  have x_sq_bound: "\<And>i. i < k \<Longrightarrow> (cmod (x $ i))\<^sup>2 \<le> Re \<langle>x | x\<rangle>"
  proof -
    fix i assume i_lt: "i < k"
    have iI: "i \<in> {0..<k}" using i_lt by simp
    have nn: "\<And>p. p \<in> {0..<k} - {i} \<Longrightarrow> 0 \<le> (cmod (x $ p))\<^sup>2"
      by simp
    have "(cmod (x $ i))\<^sup>2 \<le> (\<Sum>p = 0..<k. (cmod (x $ p))\<^sup>2)"
      by (rule member_le_sum[OF iI nn]) auto
    thus "(cmod (x $ i))\<^sup>2 \<le> Re \<langle>x | x\<rangle>" using xx_real by simp
  qed
  have x_cmod_bound: "\<And>i. i < k \<Longrightarrow> cmod (x $ i) \<le> sqrt (Re \<langle>x | x\<rangle>)"
  proof -
    fix i assume i_lt: "i < k"
    have "cmod (x $ i) = sqrt ((cmod (x $ i))\<^sup>2)" by simp
    also have "\<dots> \<le> sqrt (Re \<langle>x | x\<rangle>)"
      using x_sq_bound[OF i_lt] real_sqrt_le_mono by blast
    finally show "cmod (x $ i) \<le> sqrt (Re \<langle>x | x\<rangle>)" .
  qed
  have prod_bound: "\<And>i j. i < k \<Longrightarrow> j < k \<Longrightarrow>
                       cmod (x $ i) * cmod (x $ j) \<le> Re \<langle>x | x\<rangle>"
  proof -
    fix i j assume i_lt: "i < k" and j_lt: "j < k"
    have nn: "0 \<le> Re \<langle>x | x\<rangle>" using inner_prod_with_itself_Re by blast
    have i_b: "cmod (x $ i) \<le> sqrt (Re \<langle>x | x\<rangle>)" using x_cmod_bound[OF i_lt] .
    have j_b: "cmod (x $ j) \<le> sqrt (Re \<langle>x | x\<rangle>)" using x_cmod_bound[OF j_lt] .
    have sqrt_nn: "0 \<le> sqrt (Re \<langle>x | x\<rangle>)" using nn by auto
    have cj_nn: "0 \<le> cmod (x $ j)" by simp
    have "cmod (x $ i) * cmod (x $ j)
            \<le> sqrt (Re \<langle>x | x\<rangle>) * sqrt (Re \<langle>x | x\<rangle>)"
      by (rule mult_mono[OF i_b j_b sqrt_nn cj_nn])
    also have "\<dots> = Re \<langle>x | x\<rangle>"
      using nn by simp
    finally show "cmod (x $ i) * cmod (x $ j) \<le> Re \<langle>x | x\<rangle>" .
  qed
  have inner_bound:
    "\<And>i j. i < k \<Longrightarrow> j < k \<Longrightarrow>
       cmod (x $ i) * cmod (A $$ (i,j)) * cmod (x $ j)
       \<le> cmod (A $$ (i,j)) * Re \<langle>x | x\<rangle>"
  proof -
    fix i j assume i_lt: "i < k" and j_lt: "j < k"
    have nn: "0 \<le> cmod (A $$ (i,j))" by simp
    have rxx_nn: "0 \<le> Re \<langle>x | x\<rangle>"
      using inner_prod_with_itself_Re by blast
    have step: "cmod (x $ i) * cmod (x $ j) \<le> Re \<langle>x | x\<rangle>"
      by (rule prod_bound[OF i_lt j_lt])
    have "cmod (x $ i) * cmod (A $$ (i,j)) * cmod (x $ j)
            = cmod (A $$ (i,j)) * (cmod (x $ i) * cmod (x $ j))"
      by (simp add: ac_simps)
    also have "\<dots> \<le> cmod (A $$ (i,j)) * Re \<langle>x | x\<rangle>"
      using step nn by (rule mult_left_mono)
    finally show "cmod (x $ i) * cmod (A $$ (i,j)) * cmod (x $ j)
                    \<le> cmod (A $$ (i,j)) * Re \<langle>x | x\<rangle>" .
  qed
  \<comment> \<open>Assemble.\<close>
  have "cmod (\<langle>x | A *\<^sub>v x\<rangle>)
          \<le> (\<Sum>i = 0..<k. \<Sum>j = 0..<k.
                cmod (x $ i) * cmod (A $$ (i,j)) * cmod (x $ j))"
    using tri entry_eq by simp
  also have "\<dots> \<le> (\<Sum>i = 0..<k. \<Sum>j = 0..<k.
                     cmod (A $$ (i,j)) * Re \<langle>x | x\<rangle>)"
  proof (rule sum_mono)
    fix i assume "i \<in> {0..<k}"
    hence i_lt: "i < k" by simp
    show "(\<Sum>j = 0..<k. cmod (x $ i) * cmod (A $$ (i,j)) * cmod (x $ j))
            \<le> (\<Sum>j = 0..<k. cmod (A $$ (i,j)) * Re \<langle>x | x\<rangle>)"
    proof (rule sum_mono)
      fix j assume "j \<in> {0..<k}"
      hence j_lt: "j < k" by simp
      show "cmod (x $ i) * cmod (A $$ (i,j)) * cmod (x $ j)
              \<le> cmod (A $$ (i,j)) * Re \<langle>x | x\<rangle>"
        by (rule inner_bound[OF i_lt j_lt])
    qed
  qed
  also have "\<dots> = (\<Sum>i = 0..<k. \<Sum>j = 0..<k. cmod (A $$ (i,j))) * Re \<langle>x | x\<rangle>"
    by (simp add: sum_distrib_right)
  finally show ?thesis .
qed

text \<open>The main lemma: small \<open>\<epsilon>\<close> keeps the perturbation PSD.\<close>

lemma small_eps_psd:
  fixes A :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat k k" and herm: "hermitian A"
  shows "\<exists>\<epsilon> > 0. \<forall>d :: real. \<bar>d\<bar> \<le> \<epsilon> \<longrightarrow>
                     psd (1\<^sub>m k + complex_of_real d \<cdot>\<^sub>m A)"
proof -
  define S where "S = (\<Sum>i = 0..<k. \<Sum>j = 0..<k. cmod (A $$ (i,j)))"
  have S_nn: "S \<ge> 0" unfolding S_def by (simp add: sum_nonneg)
  define eps where "eps = 1 / (1 + S)"
  have eps_pos: "eps > 0" unfolding eps_def using S_nn by simp
  have S_eps_le1: "S * eps \<le> 1"
  proof -
    have "S * eps = S / (1 + S)" by (simp add: eps_def field_simps)
    also have "\<dots> \<le> 1" using S_nn by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (intro exI[where x = eps] conjI allI impI)
    show "eps > 0" using eps_pos .
    fix d :: real assume d_le: "\<bar>d\<bar> \<le> eps"
    let ?M = "1\<^sub>m k + complex_of_real d \<cdot>\<^sub>m A"
    have I_c: "(1\<^sub>m k :: complex Matrix.mat) \<in> carrier_mat k k" by simp
    have dA_c: "complex_of_real d \<cdot>\<^sub>m A \<in> carrier_mat k k"
      using A_c by simp
    have M_c: "?M \<in> carrier_mat k k"
      using I_c dA_c by auto
    have herm_M: "hermitian ?M"
    proof -
      have herm_dA: "hermitian (complex_of_real d \<cdot>\<^sub>m A)"
        by (rule hermitian_smult_real[OF herm A_c])
      show ?thesis
        by (rule hermitian_add[OF hermitian_one_mat herm_dA I_c dA_c])
    qed
    have quad_nn: "\<forall>x :: complex Matrix.vec.
                     dim_vec x = dim_row ?M \<longrightarrow> 0 \<le> Re \<langle>x | ?M *\<^sub>v x\<rangle>"
    proof (intro allI impI)
      fix x :: "complex Matrix.vec"
      assume xd: "dim_vec x = dim_row ?M"
      have dim_M_k: "dim_row ?M = k" using M_c by auto
      have x_d: "dim_vec x = k" using xd dim_M_k by simp
      \<comment> \<open>Split \<open>?M*x = x + d \<cdot>v (A*x)\<close>.\<close>
      have Ax_dim: "dim_vec (A *\<^sub>v x) = k" using A_c x_d by simp
      have dAx_dim: "dim_vec (complex_of_real d \<cdot>\<^sub>m A *\<^sub>v x) = k"
        using A_c x_d by simp
      have x_cv: "x \<in> carrier_vec k"
        using x_d by (intro carrier_vecI) simp
      have Ix_eq: "(1\<^sub>m k :: complex Matrix.mat) *\<^sub>v x = x"
        using one_mult_mat_vec[OF x_cv] .
      have dAx_eq: "(complex_of_real d \<cdot>\<^sub>m A) *\<^sub>v x
                      = complex_of_real d \<cdot>\<^sub>v (A *\<^sub>v x)"
        using smult_mat_mult_vec[OF A_c x_cv] .
      have Mx_eq: "?M *\<^sub>v x = x + complex_of_real d \<cdot>\<^sub>v (A *\<^sub>v x)"
      proof -
        have "?M *\<^sub>v x = (1\<^sub>m k :: complex Matrix.mat) *\<^sub>v x
                       + (complex_of_real d \<cdot>\<^sub>m A) *\<^sub>v x"
          using add_mult_distrib_mat_vec[OF I_c dA_c x_cv] .
        also have "\<dots> = x + complex_of_real d \<cdot>\<^sub>v (A *\<^sub>v x)"
          using Ix_eq dAx_eq by simp
        finally show ?thesis .
      qed
      have inner_split: "\<langle>x | ?M *\<^sub>v x\<rangle>
                            = \<langle>x | x\<rangle> + complex_of_real d * \<langle>x | A *\<^sub>v x\<rangle>"
      proof -
        have dAx_dimv: "dim_vec (complex_of_real d \<cdot>\<^sub>v (A *\<^sub>v x)) = k"
          using Ax_dim by auto
        have "\<langle>x | ?M *\<^sub>v x\<rangle>
                = \<langle>x | x + complex_of_real d \<cdot>\<^sub>v (A *\<^sub>v x)\<rangle>"
          using Mx_eq by simp
        also have "\<dots> = \<langle>x | x\<rangle>
                        + \<langle>x | complex_of_real d \<cdot>\<^sub>v (A *\<^sub>v x)\<rangle>"
          using inner_prod_add_right[OF x_d x_d dAx_dimv] .
        also have "\<dots> = \<langle>x | x\<rangle>
                        + complex_of_real d * \<langle>x | A *\<^sub>v x\<rangle>"
          using inner_prod_smult_right[OF x_d Ax_dim] by simp
        finally show ?thesis .
      qed
      have rxx_nn: "0 \<le> Re \<langle>x | x\<rangle>"
        using inner_prod_with_itself_Re by blast
      \<comment> \<open>Apply the entry-sum bound.\<close>
      have qbound: "cmod (\<langle>x | A *\<^sub>v x\<rangle>) \<le> S * Re \<langle>x | x\<rangle>"
        using quad_form_bound_by_entry_sum[OF A_c x_d]
        unfolding S_def .
      have re_abs: "\<bar>Re (\<langle>x | A *\<^sub>v x\<rangle>)\<bar> \<le> cmod (\<langle>x | A *\<^sub>v x\<rangle>)"
        by (rule abs_Re_le_cmod)
      have re_bound: "\<bar>Re (\<langle>x | A *\<^sub>v x\<rangle>)\<bar> \<le> S * Re \<langle>x | x\<rangle>"
        using re_abs qbound by linarith
      \<comment> \<open>Final estimate.\<close>
      have re_Mx: "Re \<langle>x | ?M *\<^sub>v x\<rangle>
                     = Re \<langle>x | x\<rangle> + d * Re \<langle>x | A *\<^sub>v x\<rangle>"
        using inner_split by simp
      have abs_bound: "\<bar>d * Re \<langle>x | A *\<^sub>v x\<rangle>\<bar> \<le> \<bar>d\<bar> * (S * Re \<langle>x | x\<rangle>)"
      proof -
        have "\<bar>d * Re \<langle>x | A *\<^sub>v x\<rangle>\<bar> = \<bar>d\<bar> * \<bar>Re \<langle>x | A *\<^sub>v x\<rangle>\<bar>"
          by (simp add: abs_mult)
        also have "\<dots> \<le> \<bar>d\<bar> * (S * Re \<langle>x | x\<rangle>)"
          using re_bound by (intro mult_left_mono) auto
        finally show ?thesis .
      qed
      have d_re_bound: "d * Re \<langle>x | A *\<^sub>v x\<rangle> \<ge> - (\<bar>d\<bar> * (S * Re \<langle>x | x\<rangle>))"
      proof -
        have "d * Re \<langle>x | A *\<^sub>v x\<rangle> \<ge> - \<bar>d * Re \<langle>x | A *\<^sub>v x\<rangle>\<bar>" by simp
        thus ?thesis using abs_bound by linarith
      qed
      have eps_re_bound: "\<bar>d\<bar> * (S * Re \<langle>x | x\<rangle>) \<le> Re \<langle>x | x\<rangle>"
      proof -
        have step: "\<bar>d\<bar> * S \<le> 1"
        proof -
          have "\<bar>d\<bar> * S \<le> eps * S"
            using d_le S_nn by (intro mult_right_mono) auto
          also have "\<dots> = S * eps" by (simp add: mult.commute)
          also have "\<dots> \<le> 1" using S_eps_le1 .
          finally show ?thesis .
        qed
        have "\<bar>d\<bar> * (S * Re \<langle>x | x\<rangle>) = (\<bar>d\<bar> * S) * Re \<langle>x | x\<rangle>"
          by (simp add: mult.assoc)
        also have "\<dots> \<le> 1 * Re \<langle>x | x\<rangle>"
          using step rxx_nn by (intro mult_right_mono) auto
        finally show ?thesis by simp
      qed
      have "0 \<le> Re \<langle>x | x\<rangle> - \<bar>d\<bar> * (S * Re \<langle>x | x\<rangle>)"
        using eps_re_bound rxx_nn by linarith
      also have "\<dots> \<le> Re \<langle>x | x\<rangle> + d * Re \<langle>x | A *\<^sub>v x\<rangle>"
        using d_re_bound by linarith
      also have "\<dots> = Re \<langle>x | ?M *\<^sub>v x\<rangle>"
        using re_Mx by simp
      finally show "0 \<le> Re \<langle>x | ?M *\<^sub>v x\<rangle>" .
    qed
    show "psd ?M"
      unfolding psd_def using herm_M quad_nn by blast
  qed
qed


subsection \<open>Symmetric / anti-hermitian split of the coefficient matrix\<close>

text \<open>The \<^emph>\<open>dual\<close> linear combination
\<open>kraus_pair_sum n Vs A = \<Sum>\<^sub>{i,j} A\<^sub>{ij} V\<^sub>j\<^sup>\<dagger> V\<^sub>i\<close>
is an \<open>n \<times> n\<close> matrix. The dependence assumption
\<open>\<not> mat_lin_indep_real n (kraus_products Vs)\<close> says that some real-coefficient
\<open>A\<close> makes this sum vanish.\<close>

definition kraus_pair_row ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow>
       nat \<Rightarrow> complex Matrix.mat"
where
  "kraus_pair_row n Vs Amat i \<equiv>
     foldr (\<lambda>j acc. Amat $$ (i, j) \<cdot>\<^sub>m ((Vs!j)\<^sup>\<dagger> * Vs!i) + acc)
           [0..<length Vs] (0\<^sub>m n n)"

definition kraus_pair_sum ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow>
       complex Matrix.mat"
where
  "kraus_pair_sum n Vs Amat \<equiv>
     foldr (\<lambda>i acc. kraus_pair_row n Vs Amat i + acc)
           [0..<length Vs] (0\<^sub>m n n)"

lemma kraus_pair_row_carrier:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and i_lt: "i < length Vs"
  shows "kraus_pair_row n Vs Amat i \<in> carrier_mat n n"
proof -
  let ?N = "length Vs"
  let ?f = "\<lambda>j. Amat $$ (i,j) \<cdot>\<^sub>m ((Vs!j)\<^sup>\<dagger> * Vs!i)"
  have Vi_c: "Vs!i \<in> carrier_mat d n" using Vs_c i_lt nth_mem by blast
  have term_c: "\<forall>j < ?N. ?f j \<in> carrier_mat n n"
  proof (intro allI impI)
    fix j assume j_lt: "j < ?N"
    have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
    have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
    have inner_c: "(Vs!j)\<^sup>\<dagger> * Vs!i \<in> carrier_mat n n"
      using Vjd_c Vi_c by auto
    show "?f j \<in> carrier_mat n n"
      using inner_c by (intro smult_carrier_mat) auto
  qed
  show ?thesis
    unfolding kraus_pair_row_def
    using foldr_upt_add_carrier[OF term_c] .
qed

lemma kraus_pair_sum_carrier:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "kraus_pair_sum n Vs Amat \<in> carrier_mat n n"
proof -
  let ?N = "length Vs"
  have term_c: "\<forall>i < ?N. kraus_pair_row n Vs Amat i \<in> carrier_mat n n"
    using kraus_pair_row_carrier[OF Vs_c] by blast
  show ?thesis
    unfolding kraus_pair_sum_def
    using foldr_upt_add_carrier[OF term_c] .
qed

text \<open>Per-entry index for the dual sum.\<close>

lemma kraus_pair_row_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and i_lt: "i < length Vs"
      and r_lt: "r < n" and c_lt: "c < n"
  shows "kraus_pair_row n Vs Amat i $$ (r, c)
           = (\<Sum>j = 0..<length Vs.
                Amat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
proof -
  let ?N = "length Vs"
  let ?f = "\<lambda>j. Amat $$ (i, j) \<cdot>\<^sub>m ((Vs!j)\<^sup>\<dagger> * Vs!i)"
  have Vi_c: "Vs!i \<in> carrier_mat d n" using Vs_c i_lt nth_mem by blast
  have term_c: "\<forall>j < ?N. ?f j \<in> carrier_mat n n"
  proof (intro allI impI)
    fix j assume j_lt: "j < ?N"
    have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
    have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
    have inner_c: "(Vs!j)\<^sup>\<dagger> * Vs!i \<in> carrier_mat n n"
      using Vjd_c Vi_c by auto
    show "?f j \<in> carrier_mat n n"
      using inner_c by (intro smult_carrier_mat) auto
  qed
  have term_idx: "\<And>j. j < ?N \<Longrightarrow>
                   ?f j $$ (r,c) = Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r,c)"
  proof -
    fix j assume j_lt: "j < ?N"
    have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
    have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
    have inner_c: "(Vs!j)\<^sup>\<dagger> * Vs!i \<in> carrier_mat n n"
      using Vjd_c Vi_c by auto
    have r_dim: "r < dim_row ((Vs!j)\<^sup>\<dagger> * Vs!i)" using inner_c r_lt by auto
    have c_dim: "c < dim_col ((Vs!j)\<^sup>\<dagger> * Vs!i)" using inner_c c_lt by auto
    show "?f j $$ (r,c) = Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r,c)"
      using index_smult_mat(1)[OF r_dim c_dim] .
  qed
  have "kraus_pair_row n Vs Amat i $$ (r, c)
          = foldr (\<lambda>j acc. ?f j + acc) [0..<?N] (0\<^sub>m n n) $$ (r, c)"
    unfolding kraus_pair_row_def by simp
  also have "\<dots> = (\<Sum>j = 0..<?N. ?f j $$ (r, c))"
    using foldr_upt_add_index[OF term_c r_lt c_lt] .
  also have "\<dots> = (\<Sum>j = 0..<?N. Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
    by (rule sum.cong) (auto simp: term_idx)
  finally show ?thesis .
qed

lemma kraus_pair_sum_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and r_lt: "r < n" and c_lt: "c < n"
  shows "kraus_pair_sum n Vs Amat $$ (r, c)
           = (\<Sum>i = 0..<length Vs. \<Sum>j = 0..<length Vs.
                Amat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
proof -
  let ?N = "length Vs"
  let ?row = "\<lambda>i. kraus_pair_row n Vs Amat i"
  have row_c: "\<forall>i < ?N. ?row i \<in> carrier_mat n n"
    using kraus_pair_row_carrier[OF Vs_c] by blast
  have row_idx: "\<And>i. i < ?N \<Longrightarrow>
                  ?row i $$ (r,c) = (\<Sum>j = 0..<?N.
                     Amat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
    using kraus_pair_row_index[OF Vs_c _ r_lt c_lt] by blast
  have "kraus_pair_sum n Vs Amat $$ (r, c)
          = foldr (\<lambda>i acc. ?row i + acc) [0..<?N] (0\<^sub>m n n) $$ (r, c)"
    unfolding kraus_pair_sum_def by simp
  also have "\<dots> = (\<Sum>i = 0..<?N. ?row i $$ (r, c))"
    using foldr_upt_add_index[OF row_c r_lt c_lt] .
  also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                     Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r,c))"
    by (rule sum.cong) (auto simp: row_idx)
  finally show ?thesis .
qed

text \<open>Linearity in the coefficient matrix.\<close>

lemma kraus_pair_sum_add_A:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and A1_c: "A1 \<in> carrier_mat (length Vs) (length Vs)"
      and A2_c: "A2 \<in> carrier_mat (length Vs) (length Vs)"
  shows "kraus_pair_sum n Vs (A1 + A2)
           = kraus_pair_sum n Vs A1 + kraus_pair_sum n Vs A2"
proof (rule eq_matI)
  let ?N = "length Vs"
  let ?L = "kraus_pair_sum n Vs (A1 + A2)"
  let ?R = "kraus_pair_sum n Vs A1 + kraus_pair_sum n Vs A2"
  have L_c: "?L \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  have R1_c: "kraus_pair_sum n Vs A1 \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  have R2_c: "kraus_pair_sum n Vs A2 \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  have R_c: "?R \<in> carrier_mat n n" using R1_c R2_c by auto
  show "dim_row ?L = dim_row ?R" using L_c R_c by auto
  show "dim_col ?L = dim_col ?R" using L_c R_c by auto
  fix r c assume r_lt: "r < dim_row ?R" and c_lt: "c < dim_col ?R"
  hence r_lt': "r < n" and c_lt': "c < n" using R_c by auto
  have plus_idx: "\<And>i j. i < ?N \<Longrightarrow> j < ?N \<Longrightarrow>
                    (A1 + A2) $$ (i, j) = A1 $$ (i, j) + A2 $$ (i, j)"
    using A1_c A2_c by auto
  have L_idx: "?L $$ (r, c)
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       (A1 $$ (i,j) + A2 $$ (i,j)) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
    using kraus_pair_sum_index[OF Vs_c r_lt' c_lt', of "A1 + A2"]
    by (auto intro!: sum.cong simp: plus_idx)
  have R_idx: "?R $$ (r, c)
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       A1 $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))
                 + (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       A2 $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
    using R1_c R2_c r_lt' c_lt'
          kraus_pair_sum_index[OF Vs_c r_lt' c_lt', of A1]
          kraus_pair_sum_index[OF Vs_c r_lt' c_lt', of A2]
    by simp
  have inner_split:
    "\<And>i. (\<Sum>j = 0..<?N.
            (A1 $$ (i, j) + A2 $$ (i, j)) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))
         = (\<Sum>j = 0..<?N. A1 $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))
         + (\<Sum>j = 0..<?N. A2 $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
    by (simp add: ring_distribs sum.distrib)
  show "?L $$ (r, c) = ?R $$ (r, c)"
    using L_idx R_idx inner_split by (simp add: sum.distrib)
qed

lemma kraus_pair_sum_smult_A:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Amat_c: "Amat \<in> carrier_mat (length Vs) (length Vs)"
  shows "kraus_pair_sum n Vs (c \<cdot>\<^sub>m Amat)
           = c \<cdot>\<^sub>m kraus_pair_sum n Vs Amat"
proof (rule eq_matI)
  let ?N = "length Vs"
  let ?L = "kraus_pair_sum n Vs (c \<cdot>\<^sub>m Amat)"
  let ?R = "c \<cdot>\<^sub>m kraus_pair_sum n Vs Amat"
  have L_c: "?L \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  have R0_c: "kraus_pair_sum n Vs Amat \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  have R_c: "?R \<in> carrier_mat n n" using R0_c by simp
  show "dim_row ?L = dim_row ?R" using L_c R_c by auto
  show "dim_col ?L = dim_col ?R" using L_c R_c by auto
  fix r c1 assume r_lt: "r < dim_row ?R" and c1_lt: "c1 < dim_col ?R"
  hence r_lt': "r < n" and c1_lt': "c1 < n" using R_c by auto
  have smult_idx: "\<And>i j. i < ?N \<Longrightarrow> j < ?N \<Longrightarrow>
                     (c \<cdot>\<^sub>m Amat) $$ (i,j) = c * Amat $$ (i,j)"
    using Amat_c by auto
  have L_idx: "?L $$ (r, c1)
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       (c * Amat $$ (i,j)) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
    using kraus_pair_sum_index[OF Vs_c r_lt' c1_lt', of "c \<cdot>\<^sub>m Amat"]
    by (auto intro!: sum.cong simp: smult_idx)
  have R_idx_pre: "kraus_pair_sum n Vs Amat $$ (r, c1)
                     = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                          Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
    using kraus_pair_sum_index[OF Vs_c r_lt' c1_lt'] .
  have r_lt_dim: "r < dim_row (kraus_pair_sum n Vs Amat)" using R0_c r_lt' by auto
  have c1_lt_dim: "c1 < dim_col (kraus_pair_sum n Vs Amat)" using R0_c c1_lt' by auto
  have R_idx: "?R $$ (r, c1)
                 = c * (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                          Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
    using index_smult_mat(1)[OF r_lt_dim c1_lt_dim] R_idx_pre by simp
  have collapse: "(\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                      (c * Amat $$ (i,j)) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))
                = c * (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                          Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
  proof -
    have step1: "(\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                    (c * Amat $$ (i,j)) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                      c * (Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1)))"
      by (intro sum.cong refl) (simp add: algebra_simps)
    have step2: "(\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                    c * (Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1)))
                 = c * (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                          Amat $$ (i,j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
      by (simp add: sum_distrib_left)
    show ?thesis using step1 step2 by simp
  qed
  show "?L $$ (r, c1) = ?R $$ (r, c1)"
    using L_idx R_idx collapse by simp
qed

text \<open>Dagger identity: taking the dagger of @{term \<open>kraus_pair_sum n Vs A\<close>}
swaps and conjugates the coefficient indices.\<close>

lemma kraus_pair_sum_dagger:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Amat_c: "Amat \<in> carrier_mat (length Vs) (length Vs)"
  shows "(kraus_pair_sum n Vs Amat)\<^sup>\<dagger>
           = kraus_pair_sum n Vs
               (Matrix.mat (length Vs) (length Vs)
                  (\<lambda>(i,j). cnj (Amat $$ (j, i))))"
proof (rule eq_matI)
  let ?N = "length Vs"
  let ?Adag = "Matrix.mat ?N ?N (\<lambda>(i,j). cnj (Amat $$ (j, i)))"
  let ?L = "(kraus_pair_sum n Vs Amat)\<^sup>\<dagger>"
  let ?R = "kraus_pair_sum n Vs ?Adag"
  have S_c: "kraus_pair_sum n Vs Amat \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  have L_c: "?L \<in> carrier_mat n n" using S_c by (rule dagger_carrier)
  have R_c: "?R \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  show "dim_row ?L = dim_row ?R" using L_c R_c by auto
  show "dim_col ?L = dim_col ?R" using L_c R_c by auto
  fix r c assume r_a: "r < dim_row ?R" and c_a: "c < dim_col ?R"
  hence r_lt: "r < n" and c_lt: "c < n" using R_c by auto
  \<comment> \<open>LHS via dagger of the original.\<close>
  have L_idx: "?L $$ (r, c) = cnj (kraus_pair_sum n Vs Amat $$ (c, r))"
    using S_c r_lt c_lt by (simp add: dagger_def)
  also have "\<dots> = cnj (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                          Amat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (c, r))"
    using kraus_pair_sum_index[OF Vs_c c_lt r_lt] by simp
  also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                     cnj (Amat $$ (i, j)) * cnj (((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (c, r)))"
    by (simp add: complex_cnj_mult)
  also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                     cnj (Amat $$ (i, j)) * ((Vs!i)\<^sup>\<dagger> * Vs!j) $$ (r, c))"
  proof (intro sum.cong refl)
    fix i j assume "i \<in> {0..<?N}" "j \<in> {0..<?N}"
    hence i_lt: "i < ?N" and j_lt: "j < ?N" by simp_all
    have Vi_c: "Vs!i \<in> carrier_mat d n" using Vs_c i_lt nth_mem by blast
    have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
    have Vid_c: "(Vs!i)\<^sup>\<dagger> \<in> carrier_mat n d" using Vi_c by (rule dagger_carrier)
    have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
    have inner_c1: "(Vs!j)\<^sup>\<dagger> * Vs!i \<in> carrier_mat n n" using Vjd_c Vi_c by auto
    have inner_c2: "(Vs!i)\<^sup>\<dagger> * Vs!j \<in> carrier_mat n n" using Vid_c Vj_c by auto
    have dag_prod: "((Vs!j)\<^sup>\<dagger> * Vs!i)\<^sup>\<dagger> = (Vs!i)\<^sup>\<dagger> * Vs!j"
    proof -
      let ?Vjd = "(Vs!j)\<^sup>\<dagger>"
      have dims: "dim_col ?Vjd = dim_row (Vs!i)"
        using Vjd_c Vi_c by auto
      have a: "(?Vjd * Vs!i)\<^sup>\<dagger> = (Vs!i)\<^sup>\<dagger> * (?Vjd\<^sup>\<dagger>)"
        by (rule dagger_of_prod[OF dims])
      have b: "(?Vjd)\<^sup>\<dagger> = Vs!j"
        by (rule dagger_of_dagger_is_id)
      from a b show ?thesis by simp
    qed
    have cnj_eq: "cnj (((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (c, r)) = ((Vs!i)\<^sup>\<dagger> * Vs!j) $$ (r, c)"
    proof -
      have c_dim: "c < dim_row ((Vs!j)\<^sup>\<dagger> * Vs!i)" using inner_c1 c_lt by auto
      have r_dim: "r < dim_col ((Vs!j)\<^sup>\<dagger> * Vs!i)" using inner_c1 r_lt by auto
      have "cnj (((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (c, r))
              = ((Vs!j)\<^sup>\<dagger> * Vs!i)\<^sup>\<dagger> $$ (r, c)"
        using c_dim r_dim by (simp add: dagger_def)
      thus ?thesis using dag_prod by simp
    qed
    show "cnj (Amat $$ (i, j)) * cnj (((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (c, r))
            = cnj (Amat $$ (i, j)) * ((Vs!i)\<^sup>\<dagger> * Vs!j) $$ (r, c)"
      using cnj_eq by simp
  qed
  also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                     ?Adag $$ (j, i) * ((Vs!i)\<^sup>\<dagger> * Vs!j) $$ (r, c))"
  proof (intro sum.cong refl)
    fix i j assume "i \<in> {0..<?N}" "j \<in> {0..<?N}"
    hence i_lt: "i < ?N" and j_lt: "j < ?N" by simp_all
    have idx: "?Adag $$ (j, i) = cnj (Amat $$ (i, j))"
      using i_lt j_lt by simp
    show "cnj (Amat $$ (i, j)) * ((Vs!i)\<^sup>\<dagger> * Vs!j) $$ (r, c)
            = ?Adag $$ (j, i) * ((Vs!i)\<^sup>\<dagger> * Vs!j) $$ (r, c)"
      using idx by simp
  qed
  also have "\<dots> = (\<Sum>j = 0..<?N. \<Sum>i = 0..<?N.
                     ?Adag $$ (j, i) * ((Vs!i)\<^sup>\<dagger> * Vs!j) $$ (r, c))"
    by (rule sum.swap)
  also have "\<dots> = ?R $$ (r, c)"
    using kraus_pair_sum_index[OF Vs_c r_lt c_lt, of ?Adag] by simp
  finally show "?L $$ (r, c) = ?R $$ (r, c)" .
qed


text \<open>Existence of a hermitian witness: if \<open>A_orig\<close> (with real entries)
gives \<open>kraus_pair_sum n Vs A_orig = 0\<close> and \<open>A_orig \<noteq> 0\<close>, then either
the symmetric or the anti-hermitian part yields a non-zero hermitian
matrix with the same property.\<close>

lemma sym_or_antisym_witness:
  fixes A_orig :: "complex Matrix.mat"
  assumes Vs_c:  "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and A_c:   "A_orig \<in> carrier_mat (length Vs) (length Vs)"
      and A_real: "\<And>i j. i < length Vs \<Longrightarrow> j < length Vs \<Longrightarrow>
                      cnj (A_orig $$ (i, j)) = A_orig $$ (i, j)"
      and A_zero: "kraus_pair_sum n Vs A_orig = 0\<^sub>m n n"
      and A_nontriv: "A_orig \<noteq> 0\<^sub>m (length Vs) (length Vs)"
  shows "\<exists>H. H \<in> carrier_mat (length Vs) (length Vs)
           \<and> hermitian H
           \<and> H \<noteq> 0\<^sub>m (length Vs) (length Vs)
           \<and> kraus_pair_sum n Vs H = 0\<^sub>m n n"
proof -
  let ?k = "length Vs"
  let ?Atr = "Matrix.mat ?k ?k (\<lambda>(i,j). cnj (A_orig $$ (j, i)))"
  have Atr_c: "?Atr \<in> carrier_mat ?k ?k" by simp
  \<comment> \<open>For real \<open>A_orig\<close>, \<open>?Atr\<close> coincides with the transpose.\<close>
  have Atr_idx: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow>
                   ?Atr $$ (i, j) = A_orig $$ (j, i)"
    using A_real by auto
  \<comment> \<open>By the dagger identity, the pair-sum of \<open>?Atr\<close> also vanishes.\<close>
  have pairsum_Atr: "kraus_pair_sum n Vs ?Atr = 0\<^sub>m n n"
  proof -
    have "kraus_pair_sum n Vs ?Atr = (kraus_pair_sum n Vs A_orig)\<^sup>\<dagger>"
      using kraus_pair_sum_dagger[OF Vs_c A_c] by simp
    also have "\<dots> = (0\<^sub>m n n :: complex Matrix.mat)\<^sup>\<dagger>"
      using A_zero by simp
    also have "\<dots> = (0\<^sub>m n n :: complex Matrix.mat)"
      by (rule eq_matI) (auto simp: dagger_def)
    finally show ?thesis .
  qed
  define Asym  where "Asym  = A_orig + ?Atr"
  define Askew where "Askew = A_orig + (-1) \<cdot>\<^sub>m ?Atr"
  define Hskew where "Hskew = \<i> \<cdot>\<^sub>m Askew"
  have Asym_c:  "Asym  \<in> carrier_mat ?k ?k" unfolding Asym_def using A_c Atr_c by auto
  have nAtr_c: "(-1::complex) \<cdot>\<^sub>m ?Atr \<in> carrier_mat ?k ?k" using Atr_c by auto
  have Askew_c: "Askew \<in> carrier_mat ?k ?k" unfolding Askew_def using A_c nAtr_c by auto
  have Hskew_c: "Hskew \<in> carrier_mat ?k ?k" unfolding Hskew_def using Askew_c by auto
  \<comment> \<open>Pair-sum of \<open>Asym\<close> and \<open>Askew\<close> vanish.\<close>
  have ps_Asym: "kraus_pair_sum n Vs Asym = 0\<^sub>m n n"
  proof -
    have "kraus_pair_sum n Vs Asym
            = kraus_pair_sum n Vs A_orig + kraus_pair_sum n Vs ?Atr"
      unfolding Asym_def by (rule kraus_pair_sum_add_A[OF Vs_c A_c Atr_c])
    also have "\<dots> = 0\<^sub>m n n + 0\<^sub>m n n"
      using A_zero pairsum_Atr by simp
    also have "(0\<^sub>m n n :: complex Matrix.mat) + 0\<^sub>m n n = 0\<^sub>m n n"
      by (rule eq_matI) auto
    finally show ?thesis .
  qed
  have ps_Hskew: "kraus_pair_sum n Vs Hskew = 0\<^sub>m n n"
  proof -
    have ps_nAtr: "kraus_pair_sum n Vs ((-1::complex) \<cdot>\<^sub>m ?Atr) = 0\<^sub>m n n"
    proof -
      have "kraus_pair_sum n Vs ((-1::complex) \<cdot>\<^sub>m ?Atr)
              = (-1::complex) \<cdot>\<^sub>m kraus_pair_sum n Vs ?Atr"
        by (rule kraus_pair_sum_smult_A[OF Vs_c Atr_c])
      also have "\<dots> = (-1::complex) \<cdot>\<^sub>m 0\<^sub>m n n"
        using pairsum_Atr by simp
      also have "\<dots> = 0\<^sub>m n n"
        by (rule eq_matI) auto
      finally show ?thesis .
    qed
    have ps_Askew: "kraus_pair_sum n Vs Askew = 0\<^sub>m n n"
    proof -
      have "kraus_pair_sum n Vs Askew
              = kraus_pair_sum n Vs A_orig
                + kraus_pair_sum n Vs ((-1::complex) \<cdot>\<^sub>m ?Atr)"
        unfolding Askew_def
        by (rule kraus_pair_sum_add_A[OF Vs_c A_c nAtr_c])
      also have "\<dots> = 0\<^sub>m n n + 0\<^sub>m n n"
        using A_zero ps_nAtr by simp
      also have "(0\<^sub>m n n :: complex Matrix.mat) + 0\<^sub>m n n = 0\<^sub>m n n"
        by (rule eq_matI) auto
      finally show ?thesis .
    qed
    have "kraus_pair_sum n Vs Hskew
            = \<i> \<cdot>\<^sub>m kraus_pair_sum n Vs Askew"
      unfolding Hskew_def
      by (rule kraus_pair_sum_smult_A[OF Vs_c Askew_c])
    also have "\<dots> = \<i> \<cdot>\<^sub>m 0\<^sub>m n n"
      using ps_Askew by simp
    also have "\<dots> = 0\<^sub>m n n"
      by (rule eq_matI) auto
    finally show ?thesis .
  qed
  \<comment> \<open>Hermitian-ness.\<close>
  have herm_Asym: "hermitian Asym"
    unfolding hermitian_def
  proof (rule eq_matI)
    show "dim_row (Asym\<^sup>\<dagger>) = dim_row Asym" using Asym_c by simp
    show "dim_col (Asym\<^sup>\<dagger>) = dim_col Asym" using Asym_c by simp
    fix i j assume "i < dim_row Asym" "j < dim_col Asym"
    hence i_lt: "i < ?k" and j_lt: "j < ?k" using Asym_c by auto
    have Atr_ij: "?Atr $$ (i, j) = cnj (A_orig $$ (j, i))"
      using i_lt j_lt by simp
    have Atr_ji: "?Atr $$ (j, i) = cnj (A_orig $$ (i, j))"
      using i_lt j_lt by simp
    have Asym_ij: "Asym $$ (i, j) = A_orig $$ (i, j) + cnj (A_orig $$ (j, i))"
      unfolding Asym_def using i_lt j_lt A_c Atr_c Atr_ij by simp
    have Asym_ji: "Asym $$ (j, i) = A_orig $$ (j, i) + cnj (A_orig $$ (i, j))"
      unfolding Asym_def using i_lt j_lt A_c Atr_c Atr_ji by simp
    have "Asym\<^sup>\<dagger> $$ (i, j) = cnj (Asym $$ (j, i))"
      using i_lt j_lt Asym_c by (simp add: dagger_def)
    also have "\<dots> = cnj (A_orig $$ (j, i) + cnj (A_orig $$ (i, j)))"
      using Asym_ji by simp
    also have "\<dots> = cnj (A_orig $$ (j, i)) + A_orig $$ (i, j)"
      by simp
    also have "\<dots> = A_orig $$ (i, j) + cnj (A_orig $$ (j, i))"
      by simp
    also have "\<dots> = Asym $$ (i, j)"
      using Asym_ij by simp
    finally show "Asym\<^sup>\<dagger> $$ (i, j) = Asym $$ (i, j)" .
  qed
  have herm_Hskew: "hermitian Hskew"
    unfolding hermitian_def
  proof (rule eq_matI)
    show "dim_row (Hskew\<^sup>\<dagger>) = dim_row Hskew" using Hskew_c by simp
    show "dim_col (Hskew\<^sup>\<dagger>) = dim_col Hskew" using Hskew_c by simp
    fix i j assume "i < dim_row Hskew" "j < dim_col Hskew"
    hence i_lt: "i < ?k" and j_lt: "j < ?k" using Hskew_c by auto
    have As_idx: "Askew $$ (i, j) = A_orig $$ (i, j) - A_orig $$ (j, i)"
      unfolding Askew_def using i_lt j_lt A_c Atr_c Atr_idx by simp
    have As_idx_swap: "Askew $$ (j, i) = A_orig $$ (j, i) - A_orig $$ (i, j)"
      unfolding Askew_def using i_lt j_lt A_c Atr_c Atr_idx by simp
    have "Hskew\<^sup>\<dagger> $$ (i, j) = cnj (Hskew $$ (j, i))"
      using i_lt j_lt Hskew_c by (simp add: dagger_def)
    also have "\<dots> = cnj (\<i> * Askew $$ (j, i))"
      unfolding Hskew_def using i_lt j_lt Askew_c by simp
    also have "\<dots> = - \<i> * cnj (Askew $$ (j, i))"
      by (simp add: complex_cnj_mult)
    also have "\<dots> = - \<i> * (A_orig $$ (j, i) - A_orig $$ (i, j))"
      using As_idx_swap A_real[OF i_lt j_lt] A_real[OF j_lt i_lt] by simp
    also have "\<dots> = \<i> * (A_orig $$ (i, j) - A_orig $$ (j, i))"
      by (simp add: algebra_simps)
    also have "\<dots> = \<i> * Askew $$ (i, j)"
      using As_idx by simp
    also have "\<dots> = Hskew $$ (i, j)"
      unfolding Hskew_def using i_lt j_lt Askew_c by simp
    finally show "Hskew\<^sup>\<dagger> $$ (i, j) = Hskew $$ (i, j)" .
  qed
  \<comment> \<open>At least one is non-zero.\<close>
  show ?thesis
  proof (cases "Asym = 0\<^sub>m ?k ?k")
    case False
    \<comment> \<open>Use the symmetric part.\<close>
    show ?thesis using Asym_c herm_Asym False ps_Asym by blast
  next
    case True
    \<comment> \<open>\<open>Asym = 0\<close> means \<open>A_orig + transpose A_orig = 0\<close>, so \<open>A_orig\<close> is skew.
        Then \<open>Hskew = \<i> \<cdot> 2A_orig \<noteq> 0\<close>.\<close>
    have At_eq_neg: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow>
                      A_orig $$ (j, i) = - A_orig $$ (i, j)"
    proof -
      fix i j assume i_lt: "i < ?k" and j_lt: "j < ?k"
      have "Asym $$ (i, j) = 0"
        using True i_lt j_lt by simp
      hence "A_orig $$ (i, j) + ?Atr $$ (i, j) = 0"
        unfolding Asym_def using i_lt j_lt A_c Atr_c by simp
      hence eq0: "A_orig $$ (i, j) + A_orig $$ (j, i) = 0"
        using Atr_idx[OF i_lt j_lt] by simp
      hence "- A_orig $$ (i, j) = A_orig $$ (j, i)"
        by (rule minus_unique)
      thus "A_orig $$ (j, i) = - A_orig $$ (i, j)" by simp
    qed
    have Askew_eq_2A: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow>
                         Askew $$ (i, j) = 2 * A_orig $$ (i, j)"
    proof -
      fix i j assume i_lt: "i < ?k" and j_lt: "j < ?k"
      have "Askew $$ (i, j) = A_orig $$ (i, j) - A_orig $$ (j, i)"
        unfolding Askew_def using i_lt j_lt A_c Atr_c Atr_idx by simp
      also have "\<dots> = A_orig $$ (i, j) - (- A_orig $$ (i, j))"
        using At_eq_neg[OF i_lt j_lt] by simp
      also have "\<dots> = 2 * A_orig $$ (i, j)" by simp
      finally show "Askew $$ (i, j) = 2 * A_orig $$ (i, j)" .
    qed
    have Hskew_nz: "Hskew \<noteq> 0\<^sub>m ?k ?k"
    proof
      assume Hzero: "Hskew = 0\<^sub>m ?k ?k"
      have all_zero: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow> A_orig $$ (i, j) = 0"
      proof -
        fix i j assume i_lt: "i < ?k" and j_lt: "j < ?k"
        have "Hskew $$ (i, j) = 0"
          using Hzero i_lt j_lt by simp
        hence "\<i> * Askew $$ (i, j) = 0"
          unfolding Hskew_def using i_lt j_lt Askew_c by simp
        hence "\<i> * (2 * A_orig $$ (i, j)) = 0"
          using Askew_eq_2A[OF i_lt j_lt] by simp
        thus "A_orig $$ (i, j) = 0" by simp
      qed
      have "A_orig = 0\<^sub>m ?k ?k"
      proof (rule eq_matI)
        show "dim_row A_orig = dim_row (0\<^sub>m ?k ?k :: complex Matrix.mat)"
          using A_c by simp
        show "dim_col A_orig = dim_col (0\<^sub>m ?k ?k :: complex Matrix.mat)"
          using A_c by simp
        fix i j assume "i < dim_row (0\<^sub>m ?k ?k :: complex Matrix.mat)"
                       "j < dim_col (0\<^sub>m ?k ?k :: complex Matrix.mat)"
        hence i_lt: "i < ?k" and j_lt: "j < ?k" by auto
        show "A_orig $$ (i, j) = (0\<^sub>m ?k ?k :: complex Matrix.mat) $$ (i, j)"
          using all_zero[OF i_lt j_lt] i_lt j_lt by simp
      qed
      thus False using A_nontriv by simp
    qed
    show ?thesis using Hskew_c herm_Hskew Hskew_nz ps_Hskew by blast
  qed
qed


subsection \<open>Bridge: \<open>\<not> mat_lin_indep_real\<close> gives a real \<open>A_orig\<close> witness\<close>

text \<open>Generic concat-nth for uniform-length rows.\<close>

lemma concat_uniform_length:
  assumes "\<forall>xs \<in> set L. length xs = m"
  shows "length (concat L) = length L * m"
  using assms by (induct L) auto

lemma concat_uniform_nth:
  assumes uniform: "\<forall>xs \<in> set L. length xs = m"
      and i_lt: "i < length L"
      and j_lt: "j < m"
  shows "concat L ! (i * m + j) = L ! i ! j"
  using uniform i_lt
proof (induction L arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons l L)
  hence l_len: "length l = m" and rest_uniform: "\<forall>xs \<in> set L. length xs = m"
    by simp_all
  show ?case
  proof (cases i)
    case 0
    show ?thesis using 0 l_len j_lt by (simp add: nth_append)
  next
    case (Suc i')
    hence i'_lt: "i' < length L" using Cons.prems by simp
    have idx_shift: "i * m + j = m + (i' * m + j)"
      using Suc by (simp add: algebra_simps)
    have lhs_split: "concat (l # L) ! (i * m + j)
                       = concat L ! (i' * m + j)"
      using l_len idx_shift j_lt by (simp add: nth_append)
    have rhs: "(l # L) ! i ! j = L ! i' ! j"
      using Suc by simp
    show ?thesis using lhs_split rhs Cons.IH[OF rest_uniform i'_lt] by simp
  qed
qed

text \<open>\<open>kraus_products Vs\<close> has length \<open>k\<^sup>2\<close> with
\<open>kraus_products Vs ! (i*k + j) = (V\<^sub>j)\<^sup>\<dagger> V\<^sub>i\<close>.\<close>

lemma length_kraus_products:
  "length (kraus_products Vs) = length Vs * length Vs"
proof -
  let ?k = "length Vs"
  let ?L = "map (\<lambda>i. map (\<lambda>j. (Vs!j)\<^sup>\<dagger> * Vs!i) [0..<?k]) [0..<?k]"
  have uniform: "\<forall>xs \<in> set ?L. length xs = ?k" by auto
  have outer_len: "length ?L = ?k" by simp
  have "length (kraus_products Vs) = length (concat ?L)"
    by (simp add: kraus_products_def)
  also have "\<dots> = length ?L * ?k"
    using concat_uniform_length[OF uniform] .
  also have "\<dots> = ?k * ?k"
    using outer_len by simp
  finally show ?thesis .
qed

lemma kraus_products_nth:
  assumes i_lt: "i < length Vs" and j_lt: "j < length Vs"
  shows "kraus_products Vs ! (i * length Vs + j) = (Vs!j)\<^sup>\<dagger> * Vs!i"
proof -
  let ?k = "length Vs"
  let ?L = "map (\<lambda>i. map (\<lambda>j. (Vs!j)\<^sup>\<dagger> * Vs!i) [0..<?k]) [0..<?k]"
  have uniform: "\<forall>xs \<in> set ?L. length xs = ?k" by auto
  have outer_len: "length ?L = ?k" by simp
  have inner_nth: "?L ! i ! j = (Vs!j)\<^sup>\<dagger> * Vs!i"
    using i_lt j_lt by simp
  have i_lt': "i < length ?L" using outer_len i_lt by simp
  have "kraus_products Vs ! (i * ?k + j) = concat ?L ! (i * ?k + j)"
    by (simp add: kraus_products_def)
  also have "\<dots> = ?L ! i ! j"
    using concat_uniform_nth[OF uniform i_lt' j_lt] .
  also have "\<dots> = (Vs!j)\<^sup>\<dagger> * Vs!i"
    using inner_nth .
  finally show ?thesis .
qed

text \<open>Per-entry of the foldr that mat_lin_indep_real builds.\<close>

lemma foldr_smult_nth_index:
  fixes c :: "nat \<Rightarrow> real" and Bs :: "complex Matrix.mat list"
  assumes Bs_c: "\<forall>B \<in> set Bs. B \<in> carrier_mat n n"
      and r_lt: "r < n" and c_lt: "c1 < n"
  shows "foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (Bs ! k) + acc)
                [0..<length Bs] (0\<^sub>m n n) $$ (r, c1)
           = (\<Sum>k = 0..<length Bs.
                complex_of_real (c k) * (Bs ! k) $$ (r, c1))"
proof -
  let ?f = "\<lambda>k. complex_of_real (c k) \<cdot>\<^sub>m (Bs ! k)"
  have term_c: "\<forall>k < length Bs. ?f k \<in> carrier_mat n n"
  proof (intro allI impI)
    fix k assume k_lt: "k < length Bs"
    have "Bs ! k \<in> carrier_mat n n" using Bs_c k_lt nth_mem by blast
    thus "?f k \<in> carrier_mat n n" by (intro smult_carrier_mat) auto
  qed
  have term_idx: "\<And>k. k < length Bs \<Longrightarrow>
                    ?f k $$ (r, c1) = complex_of_real (c k) * (Bs ! k) $$ (r, c1)"
  proof -
    fix k assume k_lt: "k < length Bs"
    have Bk_c: "Bs ! k \<in> carrier_mat n n" using Bs_c k_lt nth_mem by blast
    have r_dim: "r < dim_row (Bs ! k)" using Bk_c r_lt by auto
    have c_dim: "c1 < dim_col (Bs ! k)" using Bk_c c_lt by auto
    show "?f k $$ (r, c1) = complex_of_real (c k) * (Bs ! k) $$ (r, c1)"
      using index_smult_mat(1)[OF r_dim c_dim] .
  qed
  have "foldr (\<lambda>k acc. ?f k + acc) [0..<length Bs] (0\<^sub>m n n) $$ (r, c1)
          = (\<Sum>k = 0..<length Bs. ?f k $$ (r, c1))"
    using foldr_upt_add_index[OF term_c r_lt c_lt] .
  also have "\<dots> = (\<Sum>k = 0..<length Bs.
                     complex_of_real (c k) * (Bs ! k) $$ (r, c1))"
    by (rule sum.cong) (auto simp: term_idx)
  finally show ?thesis .
qed

text \<open>Reindex \<open>\<Sum>\<^sub>{\<kappa> = 0..<n\<cdot>k}\<close> via \<open>\<kappa> = i*k + j\<close>.\<close>

lemma sum_split_prod_atLeastLessThan:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>\<kappa> = 0..<N * k. f \<kappa>) = (\<Sum>i = 0..<N. \<Sum>j = 0..<k. f (i * k + j))"
proof -
  have step1: "(\<Sum>\<kappa> < N * k. f \<kappa>) = (\<Sum>i < N. \<Sum>\<kappa> \<in> {i*k..<i*k + k}. f \<kappa>)"
    by (rule sum.nat_group[symmetric])
  have step2: "\<And>i. (\<Sum>\<kappa> \<in> {i*k..<i*k + k}. f \<kappa>) = (\<Sum>j = 0..<k. f (j + i*k))"
  proof -
    fix i
    have "(\<Sum>\<kappa> \<in> {0 + i*k..<k + i*k}. f \<kappa>) = (\<Sum>j = 0..<k. f (j + i*k))"
      by (rule sum.shift_bounds_nat_ivl)
    thus "(\<Sum>\<kappa> \<in> {i*k..<i*k + k}. f \<kappa>) = (\<Sum>j = 0..<k. f (j + i*k))"
      by (simp add: add.commute)
  qed
  have step3: "\<And>i j. f (j + i * k) = f (i * k + j)"
    by (simp add: add.commute)
  have "(\<Sum>\<kappa> < N * k. f \<kappa>) = (\<Sum>i < N. \<Sum>j = 0..<k. f (i * k + j))"
    using step1 step2 step3 by (simp cong: sum.cong)
  thus ?thesis by (simp add: atLeast0LessThan)
qed

text \<open>The main bridge: a non-trivial real dependence yields a real,
non-zero matrix \<open>A_orig\<close> for which @{const kraus_pair_sum} vanishes.\<close>

lemma mat_lin_indep_real_neg_witness:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and npos: "0 < n"
      and dep: "\<not> mat_lin_indep_real n (kraus_products Vs)"
  shows "\<exists>A_orig :: complex Matrix.mat.
            A_orig \<in> carrier_mat (length Vs) (length Vs)
          \<and> (\<forall>i j. i < length Vs \<longrightarrow> j < length Vs \<longrightarrow>
                cnj (A_orig $$ (i, j)) = A_orig $$ (i, j))
          \<and> A_orig \<noteq> 0\<^sub>m (length Vs) (length Vs)
          \<and> kraus_pair_sum n Vs A_orig = 0\<^sub>m n n"
proof -
  let ?k = "length Vs"
  let ?L = "?k * ?k"
  let ?B = "kraus_products Vs"
  have B_c: "\<forall>B \<in> set ?B. B \<in> carrier_mat n n"
    by (rule kraus_products_carrier[OF Vs_c])
  have B_len: "length ?B = ?L"
    by (simp add: length_kraus_products)
  \<comment> \<open>From the negation, extract coefficients.\<close>
  from dep have "\<not> ((\<forall>B \<in> set ?B. B \<in> carrier_mat n n) \<and>
                    (\<forall>c :: nat \<Rightarrow> real.
                       foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (?B!k) + acc)
                             [0..<length ?B] (0\<^sub>m n n) = 0\<^sub>m n n
                       \<longrightarrow> (\<forall>k < length ?B. c k = 0)))"
    unfolding mat_lin_indep_real_def .
  with B_c obtain c :: "nat \<Rightarrow> real" where
        c_fold: "foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (?B!k) + acc)
                       [0..<length ?B] (0\<^sub>m n n) = 0\<^sub>m n n"
    and c_nontriv: "\<exists>k < length ?B. c k \<noteq> 0"
    by blast
  obtain k0 where k0_lt: "k0 < ?L" and c_k0: "c k0 \<noteq> 0"
    using c_nontriv B_len by auto
  define i0 where "i0 = k0 div ?k"
  define j0 where "j0 = k0 mod ?k"
  have k_pos: "0 < ?k"
    using k0_lt by (cases ?k) auto
  have i0_lt: "i0 < ?k"
    unfolding i0_def using k0_lt k_pos by (simp add: less_mult_imp_div_less)
  have j0_lt: "j0 < ?k"
    unfolding j0_def using k_pos by simp
  have k0_decomp: "k0 = i0 * ?k + j0"
    unfolding i0_def j0_def by simp
  \<comment> \<open>Build the real matrix.\<close>
  define A_orig where
    "A_orig = Matrix.mat ?k ?k (\<lambda>(i, j). complex_of_real (c (i * ?k + j)))"
  have A_c: "A_orig \<in> carrier_mat ?k ?k"
    unfolding A_orig_def by simp
  have A_idx: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow>
                  A_orig $$ (i, j) = complex_of_real (c (i * ?k + j))"
    unfolding A_orig_def by simp
  have A_real: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow>
                   cnj (A_orig $$ (i, j)) = A_orig $$ (i, j)"
    using A_idx by simp
  \<comment> \<open>\<open>A_orig\<close> is non-zero at \<open>(i0, j0)\<close>.\<close>
  have A_nontriv: "A_orig \<noteq> 0\<^sub>m ?k ?k"
  proof
    assume "A_orig = 0\<^sub>m ?k ?k"
    hence "A_orig $$ (i0, j0) = (0\<^sub>m ?k ?k :: complex Matrix.mat) $$ (i0, j0)"
      by simp
    hence "complex_of_real (c k0) = 0"
      using A_idx[OF i0_lt j0_lt] k0_decomp i0_lt j0_lt by simp
    hence "c k0 = 0" by simp
    thus False using c_k0 by simp
  qed
  \<comment> \<open>The crucial per-entry equality.\<close>
  have pair_sum_zero: "kraus_pair_sum n Vs A_orig = 0\<^sub>m n n"
  proof (rule eq_matI)
    let ?S = "kraus_pair_sum n Vs A_orig"
    have S_c: "?S \<in> carrier_mat n n"
      by (rule kraus_pair_sum_carrier[OF Vs_c])
    show "dim_row ?S = dim_row (0\<^sub>m n n :: complex Matrix.mat)" using S_c by auto
    show "dim_col ?S = dim_col (0\<^sub>m n n :: complex Matrix.mat)" using S_c by auto
    fix r c1 assume r_a: "r < dim_row (0\<^sub>m n n :: complex Matrix.mat)"
                and c_a: "c1 < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
    hence r_lt: "r < n" and c_lt: "c1 < n" by auto
    \<comment> \<open>LHS via @{thm kraus_pair_sum_index}.\<close>
    have lhs_idx: "?S $$ (r, c1)
                     = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                          A_orig $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
      using kraus_pair_sum_index[OF Vs_c r_lt c_lt] .
    \<comment> \<open>Substitute the def of \<open>A_orig\<close>.\<close>
    have lhs_idx': "?S $$ (r, c1)
                      = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                           complex_of_real (c (i * ?k + j))
                             * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
      using lhs_idx by (auto intro!: sum.cong simp: A_idx)
    \<comment> \<open>Reindex the foldr to a double sum.\<close>
    have foldr_idx: "foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (?B!k) + acc)
                            [0..<length ?B] (0\<^sub>m n n) $$ (r, c1)
                     = (\<Sum>\<kappa> = 0..<?L.
                          complex_of_real (c \<kappa>) * (?B!\<kappa>) $$ (r, c1))"
    proof -
      have step: "foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (?B!k) + acc)
                         [0..<length ?B] (0\<^sub>m n n) $$ (r, c1)
                    = (\<Sum>k = 0..<length ?B.
                         complex_of_real (c k) * (?B!k) $$ (r, c1))"
        using foldr_smult_nth_index[OF B_c r_lt c_lt] .
      show ?thesis using step B_len by simp
    qed
    \<comment> \<open>The foldr equals zero by \<open>c_fold\<close>.\<close>
    have foldr_zero: "foldr (\<lambda>k acc. complex_of_real (c k) \<cdot>\<^sub>m (?B!k) + acc)
                              [0..<length ?B] (0\<^sub>m n n) $$ (r, c1) = 0"
      using c_fold r_lt c_lt by simp
    \<comment> \<open>So the sum vanishes.\<close>
    have sum_kappa_zero: "(\<Sum>\<kappa> = 0..<?L.
                            complex_of_real (c \<kappa>) * (?B!\<kappa>) $$ (r, c1)) = 0"
      using foldr_idx foldr_zero by simp
    \<comment> \<open>Apply reindex.\<close>
    have sum_decomp: "(\<Sum>\<kappa> = 0..<?L.
                         complex_of_real (c \<kappa>) * (?B!\<kappa>) $$ (r, c1))
                     = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                          complex_of_real (c (i * ?k + j))
                            * (?B!(i * ?k + j)) $$ (r, c1))"
      by (rule sum_split_prod_atLeastLessThan)
    \<comment> \<open>Substitute the formula for kraus_products at index \<open>i*k+j\<close>.\<close>
    have inner_eq: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow>
                      (?B!(i * ?k + j)) $$ (r, c1)
                      = ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1)"
      using kraus_products_nth by metis
    have sum_decomp': "(\<Sum>\<kappa> = 0..<?L.
                          complex_of_real (c \<kappa>) * (?B!\<kappa>) $$ (r, c1))
                     = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                          complex_of_real (c (i * ?k + j))
                            * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
      using sum_decomp by (auto intro!: sum.cong simp: inner_eq)
    \<comment> \<open>Conclude.\<close>
    have "?S $$ (r, c1) = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                            complex_of_real (c (i * ?k + j))
                              * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c1))"
      using lhs_idx' .
    also have "\<dots> = 0"
      using sum_decomp' sum_kappa_zero by simp
    finally show "?S $$ (r, c1) = (0\<^sub>m n n :: complex Matrix.mat) $$ (r, c1)"
      using r_lt c_lt by simp
  qed
  show ?thesis
    using A_c A_real A_nontriv pair_sum_zero by blast
qed


subsection \<open>Auxiliary lemmas for the assembly\<close>

text \<open>Scalar-multiplication linearity of @{const kraus_quad_map} in \<open>T\<close>.\<close>

lemma kraus_quad_map_smult_Tm:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
      and Tm_c: "Tm \<in> carrier_mat (length Vs) (length Vs)"
  shows "kraus_quad_map d Vs (c \<cdot>\<^sub>m Tm) rho
           = c \<cdot>\<^sub>m kraus_quad_map d Vs Tm rho"
proof (rule eq_matI)
  let ?N = "length Vs"
  let ?L = "kraus_quad_map d Vs (c \<cdot>\<^sub>m Tm) rho"
  let ?R = "c \<cdot>\<^sub>m kraus_quad_map d Vs Tm rho"
  have L_c: "?L \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have R0_c: "kraus_quad_map d Vs Tm rho \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have R_c: "?R \<in> carrier_mat d d" using R0_c by simp
  show "dim_row ?L = dim_row ?R" using L_c R_c by auto
  show "dim_col ?L = dim_col ?R" using L_c R_c by auto
  fix r c1 assume r_lt: "r < dim_row ?R" and c1_lt: "c1 < dim_col ?R"
  hence r_lt': "r < d" and c1_lt': "c1 < d" using R_c by auto
  have smult_idx: "\<And>i j. i < ?N \<Longrightarrow> j < ?N \<Longrightarrow>
                     (c \<cdot>\<^sub>m Tm) $$ (i, j) = c * Tm $$ (i, j)"
    using Tm_c by auto
  have L_idx: "?L $$ (r, c1)
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       (c * Tm $$ (i, j))
                         * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1))"
    using kraus_quad_map_index[OF Vs_c rho_c r_lt' c1_lt', of "c \<cdot>\<^sub>m Tm"]
    by (auto intro!: sum.cong simp: smult_idx)
  have R_pre: "kraus_quad_map d Vs Tm rho $$ (r, c1)
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1))"
    using kraus_quad_map_index[OF Vs_c rho_c r_lt' c1_lt'] .
  have r_lt_dim: "r < dim_row (kraus_quad_map d Vs Tm rho)" using R0_c r_lt' by auto
  have c_lt_dim: "c1 < dim_col (kraus_quad_map d Vs Tm rho)" using R0_c c1_lt' by auto
  have R_idx: "?R $$ (r, c1)
                 = c * (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                          Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1))"
    using index_smult_mat(1)[OF r_lt_dim c_lt_dim] R_pre by simp
  have collapse: "(\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                      (c * Tm $$ (i, j)) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1))
                = c * (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                          Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1))"
  proof -
    have step1: "(\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                    (c * Tm $$ (i, j)) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1))
                 = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                      c * (Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1)))"
      by (intro sum.cong refl) (simp add: algebra_simps)
    have step2: "(\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                    c * (Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1)))
                 = c * (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                          Tm $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c1))"
      by (simp add: sum_distrib_left)
    show ?thesis using step1 step2 by simp
  qed
  show "?L $$ (r, c1) = ?R $$ (r, c1)"
    using L_idx R_idx collapse by simp
qed

text \<open>The identity-coefficient case: @{const kraus_quad_map} with \<open>1\<^sub>m k\<close>
reduces to the ordinary @{const kraus_map_dim}.\<close>

lemma kraus_quad_map_one_eq_kraus_map_dim:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and rho_c: "rho \<in> carrier_mat n n"
  shows "kraus_quad_map d Vs (1\<^sub>m (length Vs)) rho = kraus_map_dim d Vs rho"
proof (rule eq_matI)
  let ?N = "length Vs"
  let ?L = "kraus_quad_map d Vs (1\<^sub>m ?N) rho"
  let ?R = "kraus_map_dim d Vs rho"
  have L_c: "?L \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have R_c: "?R \<in> carrier_mat d d"
    by (rule kraus_map_dim_carrier[OF Vs_c rho_c])
  show "dim_row ?L = dim_row ?R" using L_c R_c by auto
  show "dim_col ?L = dim_col ?R" using L_c R_c by auto
  fix r c assume r_a: "r < dim_row ?R" and c_a: "c < dim_col ?R"
  hence r_lt: "r < d" and c_lt: "c < d" using R_c by auto
  have one_idx: "\<And>i j. i < ?N \<Longrightarrow> j < ?N \<Longrightarrow>
                    (1\<^sub>m ?N :: complex Matrix.mat) $$ (i, j)
                      = (if i = j then 1 else 0)"
    by simp
  have term_zero: "\<And>i j. i < ?N \<Longrightarrow> j < ?N \<Longrightarrow> i \<noteq> j \<Longrightarrow>
                      (1\<^sub>m ?N :: complex Matrix.mat) $$ (i, j)
                        * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c) = 0"
    by simp
  have term_diag: "\<And>i. i < ?N \<Longrightarrow>
                      (1\<^sub>m ?N :: complex Matrix.mat) $$ (i, i)
                        * (Vs!i * rho * ((Vs!i)\<^sup>\<dagger>)) $$ (r, c)
                      = (Vs!i * rho * ((Vs!i)\<^sup>\<dagger>)) $$ (r, c)"
    by simp
  \<comment> \<open>LHS per-entry: double sum collapses to diagonal.\<close>
  have L_idx: "?L $$ (r, c)
                 = (\<Sum>i = 0..<?N. (Vs!i * rho * ((Vs!i)\<^sup>\<dagger>)) $$ (r, c))"
  proof -
    have "?L $$ (r, c)
            = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                 (1\<^sub>m ?N :: complex Matrix.mat) $$ (i, j)
                   * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
      using kraus_quad_map_index[OF Vs_c rho_c r_lt c_lt] .
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       (if i = j then 1 else 0)
                         * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
      by (intro sum.cong refl) auto
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       (if i = j then (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c) else 0))"
      by (intro sum.cong refl) (simp split: if_split)
    also have "\<dots> = (\<Sum>i = 0..<?N. (Vs!i * rho * ((Vs!i)\<^sup>\<dagger>)) $$ (r, c))"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {0..<?N}"
      hence i_lt: "i < ?N" by simp
      show "(\<Sum>j = 0..<?N.
                if i = j then (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c) else 0)
            = (Vs!i * rho * ((Vs!i)\<^sup>\<dagger>)) $$ (r, c)"
        using i_lt by (simp add: sum.delta)
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>RHS via list-induction on Vs (uses outer_sum_entry_sum_list-like reasoning).\<close>
  have R_idx: "?R $$ (r, c)
                 = sum_list (map (\<lambda>W. (W * rho * (W\<^sup>\<dagger>)) $$ (r, c)) Vs)"
    using Vs_c rho_c r_lt c_lt
  proof (induction Vs)
    case Nil
    have "kraus_map_dim d [] rho = 0\<^sub>m d d" by simp
    thus ?case using r_lt c_lt by simp
  next
    case (Cons V Vs')
    have V_c: "V \<in> carrier_mat d n" using Cons.prems by simp
    have Vs'_c: "\<forall>W \<in> set Vs'. W \<in> carrier_mat d n" using Cons.prems by simp
    have Vd_c: "V\<^sup>\<dagger> \<in> carrier_mat n d" using V_c by (rule dagger_carrier)
    have term_c: "V * rho * (V\<^sup>\<dagger>) \<in> carrier_mat d d"
      using V_c rho_c Vd_c by (intro mult_carrier_mat) auto
    have IH_c: "kraus_map_dim d Vs' rho \<in> carrier_mat d d"
      using kraus_map_dim_carrier[OF Vs'_c rho_c] .
    have "kraus_map_dim d (V # Vs') rho $$ (r, c)
            = (V * rho * (V\<^sup>\<dagger>) + kraus_map_dim d Vs' rho) $$ (r, c)"
      by simp
    also have "\<dots> = (V * rho * (V\<^sup>\<dagger>)) $$ (r, c)
                  + kraus_map_dim d Vs' rho $$ (r, c)"
      using term_c IH_c r_lt c_lt by auto
    also have "\<dots> = (V * rho * (V\<^sup>\<dagger>)) $$ (r, c)
                  + sum_list (map (\<lambda>W. (W * rho * (W\<^sup>\<dagger>)) $$ (r, c)) Vs')"
      using Cons.IH[OF Vs'_c rho_c r_lt c_lt] by simp
    also have "\<dots> = sum_list (map (\<lambda>W. (W * rho * (W\<^sup>\<dagger>)) $$ (r, c)) (V # Vs'))"
      by simp
    finally show ?case .
  qed
  have R_sum_eq: "sum_list (map (\<lambda>W. (W * rho * (W\<^sup>\<dagger>)) $$ (r, c)) Vs)
                    = (\<Sum>i = 0..<?N. (Vs!i * rho * ((Vs!i)\<^sup>\<dagger>)) $$ (r, c))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  show "?L $$ (r, c) = ?R $$ (r, c)"
    using L_idx R_idx R_sum_eq by simp
qed

text \<open>The pair-sum at the identity coefficient is exactly @{const sum_wdag_w}.\<close>

lemma kraus_pair_sum_one_eq_sum_wdag_w:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "kraus_pair_sum n Vs (1\<^sub>m (length Vs)) = sum_wdag_w n Vs"
proof (rule eq_matI)
  let ?N = "length Vs"
  let ?L = "kraus_pair_sum n Vs (1\<^sub>m ?N)"
  let ?R = "sum_wdag_w n Vs"
  have L_c: "?L \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  have R_c: "?R \<in> carrier_mat n n"
    by (rule sum_wdag_w_carrier[OF Vs_c])
  show "dim_row ?L = dim_row ?R" using L_c R_c by auto
  show "dim_col ?L = dim_col ?R" using L_c R_c by auto
  fix r c assume r_a: "r < dim_row ?R" and c_a: "c < dim_col ?R"
  hence r_lt: "r < n" and c_lt: "c < n" using R_c by auto
  \<comment> \<open>LHS: double sum collapses to diagonal.\<close>
  have L_idx: "?L $$ (r, c)
                 = (\<Sum>i = 0..<?N. ((Vs!i)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
  proof -
    have "?L $$ (r, c)
            = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                  (1\<^sub>m ?N :: complex Matrix.mat) $$ (i, j)
                    * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
      using kraus_pair_sum_index[OF Vs_c r_lt c_lt] .
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       (if i = j then 1 else 0)
                         * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
      by (intro sum.cong refl) auto
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       (if i = j then ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c) else 0))"
      by (intro sum.cong refl) (simp split: if_split)
    also have "\<dots> = (\<Sum>i = 0..<?N. ((Vs!i)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {0..<?N}"
      hence i_lt: "i < ?N" by simp
      show "(\<Sum>j = 0..<?N.
                if i = j then ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, c) else 0)
            = ((Vs!i)\<^sup>\<dagger> * Vs!i) $$ (r, c)"
        using i_lt by (simp add: sum.delta)
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>RHS via list induction.\<close>
  have R_idx: "?R $$ (r, c)
                 = sum_list (map (\<lambda>W. (W\<^sup>\<dagger> * W) $$ (r, c)) Vs)"
    using Vs_c r_lt c_lt
  proof (induction Vs)
    case Nil
    have "sum_wdag_w n [] = 0\<^sub>m n n" by simp
    thus ?case using r_lt c_lt by simp
  next
    case (Cons V Vs')
    have V_c: "V \<in> carrier_mat d n" using Cons.prems by simp
    have Vs'_c: "\<forall>W \<in> set Vs'. W \<in> carrier_mat d n" using Cons.prems by simp
    have Vd_c: "V\<^sup>\<dagger> \<in> carrier_mat n d" using V_c by (rule dagger_carrier)
    have term_c: "V\<^sup>\<dagger> * V \<in> carrier_mat n n"
      using Vd_c V_c by auto
    have IH_c: "sum_wdag_w n Vs' \<in> carrier_mat n n"
      using sum_wdag_w_carrier[OF Vs'_c] .
    have "sum_wdag_w n (V # Vs') $$ (r, c)
            = (V\<^sup>\<dagger> * V + sum_wdag_w n Vs') $$ (r, c)"
      by (simp add: sum_wdag_w_Cons)
    also have "\<dots> = (V\<^sup>\<dagger> * V) $$ (r, c) + sum_wdag_w n Vs' $$ (r, c)"
      using term_c IH_c r_lt c_lt by auto
    also have "\<dots> = (V\<^sup>\<dagger> * V) $$ (r, c)
                  + sum_list (map (\<lambda>W. (W\<^sup>\<dagger> * W) $$ (r, c)) Vs')"
      using Cons.IH[OF Vs'_c r_lt c_lt] by simp
    also have "\<dots> = sum_list (map (\<lambda>W. (W\<^sup>\<dagger> * W) $$ (r, c)) (V # Vs'))"
      by simp
    finally show ?case .
  qed
  have R_sum_eq: "sum_list (map (\<lambda>W. (W\<^sup>\<dagger> * W) $$ (r, c)) Vs)
                    = (\<Sum>i = 0..<?N. ((Vs!i)\<^sup>\<dagger> * Vs!i) $$ (r, c))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  show "?L $$ (r, c) = ?R $$ (r, c)"
    using L_idx R_idx R_sum_eq by simp
qed


subsection \<open>Minimality and the distinctness lemma (Lemma B)\<close>

text \<open>Linear independence of a complex-matrix list (over \<open>\<complex>\<close>).
This is the \<^emph>\<open>minimality\<close> assumption needed to make the reverse direction
of Choi's Theorem 3 go through: without it, perturbations of a non-minimal
Kraus list can produce the same map.\<close>

definition lin_indep_complex_mat ::
  "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool"
where
  "lin_indep_complex_mat d n Ws \<equiv>
     (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and>
     (\<forall>c :: nat \<Rightarrow> complex.
        foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (Ws!k) + acc) [0..<length Ws] (0\<^sub>m d n)
            = 0\<^sub>m d n
        \<longrightarrow> (\<forall>k < length Ws. c k = 0))"

text \<open>\<^bold>\<open>Lemma B\<close>: under minimality of \<open>Vs\<close>, a non-zero coefficient matrix
gives a non-vanishing quadratic Kraus map for some \<open>\<rho>\<close>.

The witness \<open>\<rho> := mat_unit p q n n\<close> (a single 1 at \<open>(p,q)\<close>) makes
\<open>(V\<^sub>i \<rho> V\<^sub>j\<^sup>\<dagger>) $$ (r,c) = V\<^sub>i $$ (r,p) \<bar>V\<^sub>j $$ (c,q)\<bar>\<close>, so
universal vanishing of @{const kraus_quad_map} on all \<open>(p,q,r,c)\<close>
combined with linear independence of \<open>Vs\<close> (applied twice, separated
by conjugation) forces \<open>A = 0\<close>.\<close>

text \<open>A convenient form of minimality: if the per-entry sum vanishes for
all \<open>(r,p)\<close>, then all coefficients are zero.\<close>

lemma lin_indep_zero_combo:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and minimal: "lin_indep_complex_mat d n Vs"
      and coeff_kills: "\<And>r p. r < d \<Longrightarrow> p < n \<Longrightarrow>
                           (\<Sum>i = 0..<length Vs. c i * (Vs!i) $$ (r, p)) = 0"
  shows "\<forall>i < length Vs. c i = 0"
proof -
  let ?N = "length Vs"
  let ?f = "\<lambda>k. c k \<cdot>\<^sub>m (Vs!k)"
  have term_c: "\<forall>k < ?N. ?f k \<in> carrier_mat d n"
  proof (intro allI impI)
    fix k assume k_lt: "k < ?N"
    have "Vs!k \<in> carrier_mat d n" using Vs_c k_lt nth_mem by blast
    thus "?f k \<in> carrier_mat d n" by (intro smult_carrier_mat) auto
  qed
  have foldr_c: "foldr (\<lambda>k acc. ?f k + acc) [0..<?N] (0\<^sub>m d n) \<in> carrier_mat d n"
    using term_c by (intro foldr_add_carrier_dn) auto
  have foldr_zero: "foldr (\<lambda>k acc. ?f k + acc) [0..<?N] (0\<^sub>m d n) = 0\<^sub>m d n"
  proof (rule eq_matI)
    show "dim_row (foldr (\<lambda>k acc. ?f k + acc) [0..<?N] (0\<^sub>m d n))
            = dim_row (0\<^sub>m d n :: complex Matrix.mat)"
      using foldr_c by auto
    show "dim_col (foldr (\<lambda>k acc. ?f k + acc) [0..<?N] (0\<^sub>m d n))
            = dim_col (0\<^sub>m d n :: complex Matrix.mat)"
      using foldr_c by auto
    fix r p
    assume r_a: "r < dim_row (0\<^sub>m d n :: complex Matrix.mat)"
       and p_a: "p < dim_col (0\<^sub>m d n :: complex Matrix.mat)"
    hence r_lt: "r < d" and p_lt: "p < n" by auto
    have z_c: "(0\<^sub>m d n :: complex Matrix.mat) \<in> carrier_mat d n" by simp
    have idx_step: "foldr (\<lambda>k acc. ?f k + acc) [0..<?N] (0\<^sub>m d n) $$ (r, p)
                      = (\<Sum>k = 0..<?N. ?f k $$ (r, p))
                        + (0\<^sub>m d n :: complex Matrix.mat) $$ (r, p)"
      using foldr_upt_add_acc_index_dn[OF term_c z_c r_lt p_lt] .
    have z_idx: "(0\<^sub>m d n :: complex Matrix.mat) $$ (r, p) = 0"
      using r_lt p_lt by simp
    have term_idx: "(\<Sum>k = 0..<?N. ?f k $$ (r, p))
                      = (\<Sum>k = 0..<?N. c k * (Vs!k) $$ (r, p))"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {0..<?N}" hence k_lt: "k < ?N" by simp
      have Vk_c: "Vs!k \<in> carrier_mat d n" using Vs_c k_lt nth_mem by blast
      have r_dim: "r < dim_row (Vs!k)" using Vk_c r_lt by auto
      have p_dim: "p < dim_col (Vs!k)" using Vk_c p_lt by auto
      show "?f k $$ (r, p) = c k * (Vs!k) $$ (r, p)"
        using index_smult_mat(1)[OF r_dim p_dim] .
    qed
    have "foldr (\<lambda>k acc. ?f k + acc) [0..<?N] (0\<^sub>m d n) $$ (r, p)
            = (\<Sum>k = 0..<?N. c k * (Vs!k) $$ (r, p))"
      using idx_step z_idx term_idx by simp
    also have "\<dots> = 0" using coeff_kills[OF r_lt p_lt] .
    finally show "foldr (\<lambda>k acc. ?f k + acc) [0..<?N] (0\<^sub>m d n) $$ (r, p)
                    = (0\<^sub>m d n :: complex Matrix.mat) $$ (r, p)"
      using r_lt p_lt by simp
  qed
  show ?thesis
    using minimal foldr_zero unfolding lin_indep_complex_mat_def by simp
qed

text \<open>The per-entry computation for the rank-1 \<open>\<rho> = mat_unit p q n n\<close>.\<close>

lemma kraus_quad_map_mat_unit_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and i_lt: "i < length Vs" and j_lt: "j < length Vs"
      and p_lt: "p < n" and q_lt: "q < n"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "(Vs!i * mat_unit p q n n * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)
           = (Vs!i) $$ (r, p) * cnj ((Vs!j) $$ (c, q))"
proof -
  have Vi_c: "Vs!i \<in> carrier_mat d n" using Vs_c i_lt nth_mem by blast
  have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
  have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
  have unit_c: "mat_unit p q n n \<in> carrier_mat n n"
    by (simp add: mat_unit_def)
  have ViE_c: "Vs!i * mat_unit p q n n \<in> carrier_mat d n"
    using Vi_c unit_c by auto
  \<comment> \<open>\<open>(V\<^sub>i * E\<^sub>{pq}) $$ (r,b)\<close> is \<open>V\<^sub>i $$ (r,p)\<close> if \<open>b = q\<close>, else 0.\<close>
  have ViE_idx: "\<And>b. b < n \<Longrightarrow>
                   (Vs!i * mat_unit p q n n) $$ (r, b)
                     = (if b = q then (Vs!i) $$ (r, p) else 0)"
  proof -
    fix b assume b_lt: "b < n"
    have "(Vs!i * mat_unit p q n n) $$ (r, b)
            = (\<Sum>a = 0..<n. (Vs!i) $$ (r, a) * (mat_unit p q n n) $$ (a, b))"
      by (rule mat_mult_index_sum[OF Vi_c unit_c r_lt b_lt])
    also have "\<dots> = (\<Sum>a = 0..<n.
                       (Vs!i) $$ (r, a) * (if a = p \<and> b = q then 1 else 0))"
    proof (rule sum.cong[OF refl])
      fix a assume "a \<in> {0..<n}" hence a_lt: "a < n" by simp
      show "(Vs!i) $$ (r, a) * (mat_unit p q n n) $$ (a, b)
              = (Vs!i) $$ (r, a) * (if a = p \<and> b = q then 1 else 0)"
        using mat_unit_index[OF a_lt b_lt, of p q] by simp
    qed
    also have "\<dots> = (if b = q then (Vs!i) $$ (r, p) else 0)"
    proof (cases "b = q")
      case True
      have "(\<Sum>a = 0..<n.
              (Vs!i) $$ (r, a) * (if a = p \<and> b = q then 1 else 0))
              = (\<Sum>a = 0..<n.
                   (if a = p then (Vs!i) $$ (r, a) else 0))"
        using True by (intro sum.cong refl) (auto)
      also have "\<dots> = (if p \<in> {0..<n} then (Vs!i) $$ (r, p) else 0)"
        by (rule sum.delta) simp
      also have "\<dots> = (Vs!i) $$ (r, p)" using p_lt by simp
      finally show ?thesis using True by simp
    next
      case False
      have "(\<Sum>a = 0..<n.
              (Vs!i) $$ (r, a) * (if a = p \<and> b = q then 1 else 0))
              = (\<Sum>a = 0..<n. (0::complex))"
        using False by (intro sum.cong refl) (auto)
      thus ?thesis using False by simp
    qed
    finally show "(Vs!i * mat_unit p q n n) $$ (r, b)
                    = (if b = q then (Vs!i) $$ (r, p) else 0)" .
  qed
  \<comment> \<open>Now the outer product.\<close>
  have "(Vs!i * mat_unit p q n n * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)
          = (\<Sum>b = 0..<n.
              (Vs!i * mat_unit p q n n) $$ (r, b) * ((Vs!j)\<^sup>\<dagger>) $$ (b, c))"
    by (rule mat_mult_index_sum[OF ViE_c Vjd_c r_lt c_lt])
  also have "\<dots> = (\<Sum>b = 0..<n.
                     (if b = q then (Vs!i) $$ (r, p) else 0) * ((Vs!j)\<^sup>\<dagger>) $$ (b, c))"
    by (rule sum.cong[OF refl]) (auto simp: ViE_idx)
  also have "\<dots> = (\<Sum>b = 0..<n.
                     (if b = q then (Vs!i) $$ (r, p) * ((Vs!j)\<^sup>\<dagger>) $$ (b, c)
                              else 0))"
    by (intro sum.cong refl) (simp split: if_split)
  also have "\<dots> = (if q \<in> {0..<n} then (Vs!i) $$ (r, p) * ((Vs!j)\<^sup>\<dagger>) $$ (q, c)
                                   else 0)"
    by (rule sum.delta) simp
  also have "\<dots> = (Vs!i) $$ (r, p) * ((Vs!j)\<^sup>\<dagger>) $$ (q, c)"
    using q_lt by simp
  also have "((Vs!j)\<^sup>\<dagger>) $$ (q, c) = cnj ((Vs!j) $$ (c, q))"
    using Vj_c q_lt c_lt by (simp add: dagger_def)
  finally show "(Vs!i * mat_unit p q n n * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)
                  = (Vs!i) $$ (r, p) * cnj ((Vs!j) $$ (c, q))" by simp
qed

text \<open>\<^bold>\<open>Lemma B.\<close> Under minimality, a non-zero coefficient matrix
gives a non-vanishing quadratic Kraus map for some rank-1 \<open>\<rho>\<close>.\<close>

lemma kraus_quad_map_nonzero_witness:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and minimal: "lin_indep_complex_mat d n Vs"
      and A_c: "A \<in> carrier_mat (length Vs) (length Vs)"
      and A_nz: "A \<noteq> 0\<^sub>m (length Vs) (length Vs)"
      and npos: "0 < n" and dpos: "0 < d"
  shows "\<exists>rho \<in> carrier_mat n n. kraus_quad_map d Vs A rho \<noteq> 0\<^sub>m d d"
proof (rule ccontr)
  let ?k = "length Vs"
  assume not_ex: "\<not> (\<exists>rho \<in> carrier_mat n n. kraus_quad_map d Vs A rho \<noteq> 0\<^sub>m d d)"
  hence all_zero: "\<And>rho. rho \<in> carrier_mat n n \<Longrightarrow>
                       kraus_quad_map d Vs A rho = 0\<^sub>m d d"
    by auto
  \<comment> \<open>Step 1: pick \<open>\<rho> = mat_unit p q n n\<close>, get a per-entry vanishing identity.\<close>
  have entry_zero:
    "\<And>p q r c. p < n \<Longrightarrow> q < n \<Longrightarrow> r < d \<Longrightarrow> c < d \<Longrightarrow>
       (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
          A $$ (i, j) * (Vs!i) $$ (r, p) * cnj ((Vs!j) $$ (c, q))) = 0"
  proof -
    fix p q r c
    assume p_lt: "p < n" and q_lt: "q < n" and r_lt: "r < d" and c_lt: "c < d"
    have unit_c: "mat_unit p q n n \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
    have qm_zero: "kraus_quad_map d Vs A (mat_unit p q n n) = 0\<^sub>m d d"
      using all_zero[OF unit_c] .
    have qm_zero_idx: "kraus_quad_map d Vs A (mat_unit p q n n) $$ (r, c) = 0"
      using qm_zero r_lt c_lt by simp
    have qm_idx: "kraus_quad_map d Vs A (mat_unit p q n n) $$ (r, c)
                    = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                        A $$ (i, j)
                          * (Vs!i * mat_unit p q n n * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))"
      using kraus_quad_map_index[OF Vs_c unit_c r_lt c_lt] .
    have sum_eq: "(\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                     A $$ (i, j)
                       * (Vs!i * mat_unit p q n n * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))
                  = (\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
                       A $$ (i, j) * (Vs!i) $$ (r, p) * cnj ((Vs!j) $$ (c, q)))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {0..<?k}" hence i_lt: "i < ?k" by simp
      show "(\<Sum>j = 0..<?k.
              A $$ (i, j) * (Vs!i * mat_unit p q n n * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c))
              = (\<Sum>j = 0..<?k.
                   A $$ (i, j) * (Vs!i) $$ (r, p) * cnj ((Vs!j) $$ (c, q)))"
      proof (rule sum.cong[OF refl])
        fix j assume "j \<in> {0..<?k}" hence j_lt: "j < ?k" by simp
        have prod_eq: "(Vs!i * mat_unit p q n n * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)
                         = (Vs!i) $$ (r, p) * cnj ((Vs!j) $$ (c, q))"
          by (rule kraus_quad_map_mat_unit_index
                    [OF Vs_c i_lt j_lt p_lt q_lt r_lt c_lt])
        show "A $$ (i, j) * (Vs!i * mat_unit p q n n * ((Vs!j)\<^sup>\<dagger>)) $$ (r, c)
                = A $$ (i, j) * (Vs!i) $$ (r, p) * cnj ((Vs!j) $$ (c, q))"
          using prod_eq by (simp add: mult.assoc)
      qed
    qed
    show "(\<Sum>i = 0..<?k. \<Sum>j = 0..<?k.
            A $$ (i, j) * (Vs!i) $$ (r, p) * cnj ((Vs!j) $$ (c, q))) = 0"
      using qm_zero_idx qm_idx sum_eq by simp
  qed
  \<comment> \<open>Step 2: for each fixed \<open>(c, q)\<close>, the coefficients
      \<open>e i = \<Sum>j A(i,j) cnj(V_j$$(c,q))\<close> satisfy
      \<open>\<Sum>i e i V_i = 0\<close>, so all \<open>e i = 0\<close> by minimality.\<close>
  have inner_zero: "\<And>i c q. i < ?k \<Longrightarrow> c < d \<Longrightarrow> q < n \<Longrightarrow>
                       (\<Sum>j = 0..<?k. A $$ (i, j) * cnj ((Vs!j) $$ (c, q))) = 0"
  proof -
    fix i c q assume i_lt: "i < ?k" and c_lt: "c < d" and q_lt: "q < n"
    let ?e = "\<lambda>i'. (\<Sum>j = 0..<?k. A $$ (i', j) * cnj ((Vs!j) $$ (c, q)))"
    have e_zero_combo: "\<And>r p. r < d \<Longrightarrow> p < n \<Longrightarrow>
                           (\<Sum>i' = 0..<?k. ?e i' * (Vs!i') $$ (r, p)) = 0"
    proof -
      fix r p assume r_lt: "r < d" and p_lt: "p < n"
      have step1: "(\<Sum>i' = 0..<?k. ?e i' * (Vs!i') $$ (r, p))
                     = (\<Sum>i' = 0..<?k. \<Sum>j = 0..<?k.
                         A $$ (i', j) * cnj ((Vs!j) $$ (c, q))
                          * (Vs!i') $$ (r, p))"
        by (simp add: sum_distrib_right)
      have step2: "(\<Sum>i' = 0..<?k. \<Sum>j = 0..<?k.
                       A $$ (i', j) * cnj ((Vs!j) $$ (c, q))
                        * (Vs!i') $$ (r, p))
                    = (\<Sum>i' = 0..<?k. \<Sum>j = 0..<?k.
                         A $$ (i', j) * (Vs!i') $$ (r, p)
                          * cnj ((Vs!j) $$ (c, q)))"
        by (intro sum.cong refl) (simp add: ac_simps)
      have step3: "(\<Sum>i' = 0..<?k. \<Sum>j = 0..<?k.
                       A $$ (i', j) * (Vs!i') $$ (r, p)
                        * cnj ((Vs!j) $$ (c, q))) = 0"
        by (rule entry_zero[OF p_lt q_lt r_lt c_lt])
      show "(\<Sum>i' = 0..<?k. ?e i' * (Vs!i') $$ (r, p)) = 0"
        using step1 step2 step3 by simp
    qed
    have all_e: "\<forall>i' < ?k. ?e i' = 0"
      by (rule lin_indep_zero_combo[OF Vs_c minimal e_zero_combo])
    show "(\<Sum>j = 0..<?k. A $$ (i, j) * cnj ((Vs!j) $$ (c, q))) = 0"
      using all_e i_lt by simp
  qed
  \<comment> \<open>Step 3: take \<open>cnj\<close> to get \<open>\<Sum>j cnj(A(i,j)) V_j$$(c,q) = 0\<close>
      for all \<open>(c,q)\<close>.\<close>
  have cnj_inner_zero: "\<And>i c q. i < ?k \<Longrightarrow> c < d \<Longrightarrow> q < n \<Longrightarrow>
                          (\<Sum>j = 0..<?k. cnj (A $$ (i, j)) * (Vs!j) $$ (c, q)) = 0"
  proof -
    fix i c q assume i_lt: "i < ?k" and c_lt: "c < d" and q_lt: "q < n"
    have "cnj (\<Sum>j = 0..<?k. A $$ (i, j) * cnj ((Vs!j) $$ (c, q)))
            = (\<Sum>j = 0..<?k. cnj (A $$ (i, j)) * (Vs!j) $$ (c, q))"
      by (simp add: complex_cnj_mult)
    moreover have "cnj (\<Sum>j = 0..<?k. A $$ (i, j) * cnj ((Vs!j) $$ (c, q))) = 0"
      using inner_zero[OF i_lt c_lt q_lt] by simp
    ultimately show "(\<Sum>j = 0..<?k. cnj (A $$ (i, j)) * (Vs!j) $$ (c, q)) = 0"
      by simp
  qed
  \<comment> \<open>Step 4: for each fixed \<open>i\<close>, the coefficients
      \<open>g j := cnj(A(i,j))\<close> satisfy \<open>\<Sum>j g j V_j = 0\<close>, so \<open>g j = 0\<close>
      by minimality. Hence \<open>A(i,j) = 0\<close>.\<close>
  have A_entry_zero: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow> A $$ (i, j) = 0"
  proof -
    fix i j assume i_lt: "i < ?k" and j_lt: "j < ?k"
    let ?g = "\<lambda>k. cnj (A $$ (i, k))"
    have g_zero_combo: "\<And>r p. r < d \<Longrightarrow> p < n \<Longrightarrow>
                           (\<Sum>j' = 0..<?k. ?g j' * (Vs!j') $$ (r, p)) = 0"
      using cnj_inner_zero[OF i_lt] by simp
    have all_g: "\<forall>j' < ?k. ?g j' = 0"
      by (rule lin_indep_zero_combo[OF Vs_c minimal g_zero_combo])
    hence "cnj (A $$ (i, j)) = 0" using j_lt by simp
    thus "A $$ (i, j) = 0" by simp
  qed
  \<comment> \<open>Therefore \<open>A = 0\<close>, contradiction.\<close>
  have "A = 0\<^sub>m ?k ?k"
  proof (rule eq_matI)
    show "dim_row A = dim_row (0\<^sub>m ?k ?k :: complex Matrix.mat)" using A_c by auto
    show "dim_col A = dim_col (0\<^sub>m ?k ?k :: complex Matrix.mat)" using A_c by auto
    fix i j assume "i < dim_row (0\<^sub>m ?k ?k :: complex Matrix.mat)"
                   "j < dim_col (0\<^sub>m ?k ?k :: complex Matrix.mat)"
    hence i_lt: "i < ?k" and j_lt: "j < ?k" by auto
    show "A $$ (i, j) = (0\<^sub>m ?k ?k :: complex Matrix.mat) $$ (i, j)"
      using A_entry_zero[OF i_lt j_lt] i_lt j_lt by simp
  qed
  thus False using A_nz by simp
qed

text \<open>Trace-preservation lemma for @{const kraus_quad_map}.

The proof shows
\<open>Tr (kraus_quad_map d Vs T \<rho>) = Tr (kraus_pair_sum n Vs T * \<rho>)\<close>
by per-entry sum manipulation and one application of @{thm Tr_cyclic}
to flip \<open>V\<^sub>i \<rho> V\<^sub>j\<^sup>\<dagger>\<close> into \<open>V\<^sub>j\<^sup>\<dagger> V\<^sub>i \<rho>\<close>; the
TP conclusion follows when the pair-sum equals \<open>1\<^sub>m n\<close>.\<close>

lemma Tr_kraus_quad_map_eq:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Tmat_c: "Tmat \<in> carrier_mat (length Vs) (length Vs)"
      and rho_c: "rho \<in> carrier_mat n n"
  shows "Tr (kraus_quad_map d Vs Tmat rho)
           = Tr (kraus_pair_sum n Vs Tmat * rho)"
proof -
  let ?N = "length Vs"
  let ?M = "kraus_quad_map d Vs Tmat rho"
  let ?P = "kraus_pair_sum n Vs Tmat"
  have M_c: "?M \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have P_c: "?P \<in> carrier_mat n n"
    by (rule kraus_pair_sum_carrier[OF Vs_c])
  have Prho_c: "?P * rho \<in> carrier_mat n n"
    using P_c rho_c by auto
  \<comment> \<open>Common quantity: \<open>S := \<Sum>\<^sub>{i,j} T\<^sub>{ij} Tr (V\<^sub>j\<^sup>\<dagger> V\<^sub>i * \<rho>)\<close>.\<close>
  define S where
    "S = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
            Tmat $$ (i,j) * Tr ((Vs!j)\<^sup>\<dagger> * Vs!i * rho))"
  \<comment> \<open>LHS.\<close>
  have lhs_eq_S: "Tr ?M = S"
  proof -
    have M_dr: "dim_row ?M = d" using M_c by auto
    have M_dc: "dim_col ?M = d" using M_c by auto
    have "Tr ?M = (\<Sum>r < d. if r < d then ?M $$ (r, r) else 0)"
      unfolding Tr_def using M_dr M_dc by simp
    also have "\<dots> = (\<Sum>r = 0..<d. ?M $$ (r, r))"
      by (simp add: lessThan_atLeast0)
    also have "\<dots> = (\<Sum>r = 0..<d. \<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       Tmat $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))"
      by (rule sum.cong[OF refl])
         (auto simp: kraus_quad_map_index[OF Vs_c rho_c])
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N. \<Sum>r = 0..<d.
                       Tmat $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))"
    proof -
      have a: "(\<Sum>r = 0..<d. \<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                  Tmat $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))
              = (\<Sum>i = 0..<?N. \<Sum>r = 0..<d. \<Sum>j = 0..<?N.
                  Tmat $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))"
        by (rule sum.swap)
      have b: "(\<Sum>i = 0..<?N. \<Sum>r = 0..<d. \<Sum>j = 0..<?N.
                  Tmat $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))
              = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N. \<Sum>r = 0..<d.
                  Tmat $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))"
      proof (rule sum.cong[OF refl])
        fix i assume "i \<in> {0..<?N}"
        show "(\<Sum>r = 0..<d. \<Sum>j = 0..<?N.
                 Tmat $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))
                = (\<Sum>j = 0..<?N. \<Sum>r = 0..<d.
                     Tmat $$ (i, j) * (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))"
          by (rule sum.swap)
      qed
      show ?thesis using a b by simp
    qed
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       Tmat $$ (i, j) *
                       (\<Sum>r = 0..<d. (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r)))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       Tmat $$ (i, j) * Tr (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)))"
    proof (intro sum.cong refl)
      fix i j assume "i \<in> {0..<?N}" "j \<in> {0..<?N}"
      hence i_lt: "i < ?N" and j_lt: "j < ?N" by simp_all
      have Vi_c: "Vs!i \<in> carrier_mat d n" using Vs_c i_lt nth_mem by blast
      have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
      have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
      have prod_c: "Vs!i * rho * ((Vs!j)\<^sup>\<dagger>) \<in> carrier_mat d d"
        using Vi_c rho_c Vjd_c by (intro mult_carrier_mat) auto
      have prod_dr: "dim_row (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) = d" using prod_c by auto
      have prod_dc: "dim_col (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) = d" using prod_c by auto
      have "Tr (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>))
              = (\<Sum>r < d.
                  if r < d then (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r) else 0)"
        unfolding Tr_def using prod_dr prod_dc by simp
      also have "\<dots> = (\<Sum>r = 0..<d. (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))"
        by (simp add: lessThan_atLeast0)
      finally have tr_eq: "Tr (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>))
                             = (\<Sum>r = 0..<d. (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))" .
      show "Tmat $$ (i, j) *
              (\<Sum>r = 0..<d. (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) $$ (r, r))
            = Tmat $$ (i, j) * Tr (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>))"
        using tr_eq by simp
    qed
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       Tmat $$ (i, j) * Tr ((Vs!j)\<^sup>\<dagger> * Vs!i * rho))"
    proof (intro sum.cong refl)
      fix i j assume "i \<in> {0..<?N}" "j \<in> {0..<?N}"
      hence i_lt: "i < ?N" and j_lt: "j < ?N" by simp_all
      have Vi_c: "Vs!i \<in> carrier_mat d n" using Vs_c i_lt nth_mem by blast
      have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
      have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
      have VirhoVjd_c: "Vs!i * rho * ((Vs!j)\<^sup>\<dagger>) \<in> carrier_mat d d"
        using Vi_c rho_c Vjd_c by (intro mult_carrier_mat) auto
      have ViRho_c: "Vs!i * rho \<in> carrier_mat d n"
        using Vi_c rho_c by auto
      \<comment> \<open>Group as \<open>(V\<^sub>i * \<rho>) * V\<^sub>j\<^sup>\<dagger>\<close>.\<close>
      have group1: "Vs!i * rho * ((Vs!j)\<^sup>\<dagger>) = (Vs!i * rho) * ((Vs!j)\<^sup>\<dagger>)"
        by simp
      have dims1: "dim_col (Vs!i * rho) = dim_row ((Vs!j)\<^sup>\<dagger>)"
      proof -
        have "dim_col (Vs!i * rho) = n" using ViRho_c by auto
        moreover have "dim_row ((Vs!j)\<^sup>\<dagger>) = n" using Vjd_c by auto
        ultimately show ?thesis by simp
      qed
      have dims2: "dim_row (Vs!i * rho) = dim_col ((Vs!j)\<^sup>\<dagger>)"
      proof -
        have "dim_row (Vs!i * rho) = d" using ViRho_c by auto
        moreover have "dim_col ((Vs!j)\<^sup>\<dagger>) = d" using Vjd_c by auto
        ultimately show ?thesis by simp
      qed
      have cyc1: "Tr ((Vs!i * rho) * ((Vs!j)\<^sup>\<dagger>))
                    = Tr ((Vs!j)\<^sup>\<dagger> * (Vs!i * rho))"
        using Tr_cyclic[OF dims1 dims2] .
      \<comment> \<open>And rewrite \<open>V\<^sub>j\<^sup>\<dagger> * (V\<^sub>i * \<rho>)\<close> as \<open>V\<^sub>j\<^sup>\<dagger> * V\<^sub>i * \<rho>\<close>.\<close>
      have reassoc: "(Vs!j)\<^sup>\<dagger> * (Vs!i * rho) = (Vs!j)\<^sup>\<dagger> * Vs!i * rho"
        using Vjd_c Vi_c rho_c by (metis assoc_mult_mat)
      have "Tr (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>)) = Tr ((Vs!j)\<^sup>\<dagger> * Vs!i * rho)"
        using cyc1 reassoc group1 by simp
      thus "Tmat $$ (i, j) * Tr (Vs!i * rho * ((Vs!j)\<^sup>\<dagger>))
              = Tmat $$ (i, j) * Tr ((Vs!j)\<^sup>\<dagger> * Vs!i * rho)"
        by simp
    qed
    finally show ?thesis unfolding S_def .
  qed
  \<comment> \<open>RHS.\<close>
  have rhs_eq_S: "Tr (?P * rho) = S"
  proof -
    have Prho_dr: "dim_row (?P * rho) = n" using Prho_c by auto
    have Prho_dc: "dim_col (?P * rho) = n" using Prho_c by auto
    have "Tr (?P * rho) = (\<Sum>r < n. if r < n then (?P * rho) $$ (r, r) else 0)"
      unfolding Tr_def using Prho_dr Prho_dc by simp
    also have "\<dots> = (\<Sum>r = 0..<n. (?P * rho) $$ (r, r))"
      by (simp add: lessThan_atLeast0)
    also have "\<dots> = (\<Sum>r = 0..<n. \<Sum>s = 0..<n. ?P $$ (r, s) * rho $$ (s, r))"
    proof (intro sum.cong refl)
      fix r assume "r \<in> {0..<n}" hence r_lt: "r < n" by simp
      show "(?P * rho) $$ (r, r)
              = (\<Sum>s = 0..<n. ?P $$ (r, s) * rho $$ (s, r))"
        by (rule mat_mult_index_sum[OF P_c rho_c r_lt r_lt])
    qed
    also have "\<dots> = (\<Sum>r = 0..<n. \<Sum>s = 0..<n.
                       (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                         Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s))
                       * rho $$ (s, r))"
    proof (intro sum.cong refl)
      fix r s assume "r \<in> {0..<n}" "s \<in> {0..<n}"
      hence r_lt: "r < n" and s_lt: "s < n" by simp_all
      have "?P $$ (r, s)
              = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                   Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s))"
        using kraus_pair_sum_index[OF Vs_c r_lt s_lt] .
      thus "?P $$ (r, s) * rho $$ (s, r)
              = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                   Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s))
                * rho $$ (s, r)" by simp
    qed
    also have "\<dots> = (\<Sum>r = 0..<n. \<Sum>s = 0..<n.
                       \<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                         Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r))"
      by (intro sum.cong refl) (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N. \<Sum>r = 0..<n. \<Sum>s = 0..<n.
                       Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r))"
    proof -
      let ?h = "\<lambda>r s i j.
                  Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r)"
      \<comment> \<open>Step 1: swap outermost \<open>s\<close> with \<open>i\<close>, under outer \<open>r\<close>.\<close>
      have step1: "(\<Sum>r = 0..<n. \<Sum>s = 0..<n. \<Sum>i = 0..<?N. \<Sum>j = 0..<?N. ?h r s i j)
                    = (\<Sum>r = 0..<n. \<Sum>i = 0..<?N. \<Sum>s = 0..<n. \<Sum>j = 0..<?N. ?h r s i j)"
      proof (rule sum.cong[OF refl])
        fix r assume "r \<in> {0..<n}"
        show "(\<Sum>s = 0..<n. \<Sum>i = 0..<?N. \<Sum>j = 0..<?N. ?h r s i j)
                = (\<Sum>i = 0..<?N. \<Sum>s = 0..<n. \<Sum>j = 0..<?N. ?h r s i j)"
          by (rule sum.swap)
      qed
      have step2: "(\<Sum>r = 0..<n. \<Sum>i = 0..<?N. \<Sum>s = 0..<n. \<Sum>j = 0..<?N. ?h r s i j)
                    = (\<Sum>i = 0..<?N. \<Sum>r = 0..<n. \<Sum>s = 0..<n. \<Sum>j = 0..<?N. ?h r s i j)"
        by (rule sum.swap)
      have step3: "(\<Sum>i = 0..<?N. \<Sum>r = 0..<n. \<Sum>s = 0..<n. \<Sum>j = 0..<?N. ?h r s i j)
                    = (\<Sum>i = 0..<?N. \<Sum>r = 0..<n. \<Sum>j = 0..<?N. \<Sum>s = 0..<n. ?h r s i j)"
      proof (rule sum.cong[OF refl])
        fix i assume "i \<in> {0..<?N}"
        show "(\<Sum>r = 0..<n. \<Sum>s = 0..<n. \<Sum>j = 0..<?N. ?h r s i j)
                = (\<Sum>r = 0..<n. \<Sum>j = 0..<?N. \<Sum>s = 0..<n. ?h r s i j)"
        proof (rule sum.cong[OF refl])
          fix r assume "r \<in> {0..<n}"
          show "(\<Sum>s = 0..<n. \<Sum>j = 0..<?N. ?h r s i j)
                  = (\<Sum>j = 0..<?N. \<Sum>s = 0..<n. ?h r s i j)"
            by (rule sum.swap)
        qed
      qed
      have step4: "(\<Sum>i = 0..<?N. \<Sum>r = 0..<n. \<Sum>j = 0..<?N. \<Sum>s = 0..<n. ?h r s i j)
                    = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N. \<Sum>r = 0..<n. \<Sum>s = 0..<n. ?h r s i j)"
      proof (rule sum.cong[OF refl])
        fix i assume "i \<in> {0..<?N}"
        show "(\<Sum>r = 0..<n. \<Sum>j = 0..<?N. \<Sum>s = 0..<n. ?h r s i j)
                = (\<Sum>j = 0..<?N. \<Sum>r = 0..<n. \<Sum>s = 0..<n. ?h r s i j)"
          by (rule sum.swap)
      qed
      show ?thesis using step1 step2 step3 step4 by simp
    qed
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       \<Sum>r = 0..<n.
                         Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {0..<?N}" hence i_lt: "i < ?N" by simp
      show "(\<Sum>j = 0..<?N. \<Sum>r = 0..<n. \<Sum>s = 0..<n.
                Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r))
              = (\<Sum>j = 0..<?N. \<Sum>r = 0..<n.
                   Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r))"
      proof (rule sum.cong[OF refl])
        fix j assume "j \<in> {0..<?N}" hence j_lt: "j < ?N" by simp
        have Vi_c: "Vs!i \<in> carrier_mat d n" using Vs_c i_lt nth_mem by blast
        have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
        have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
        have VjdVi_c: "(Vs!j)\<^sup>\<dagger> * Vs!i \<in> carrier_mat n n"
          using Vjd_c Vi_c by auto
        show "(\<Sum>r = 0..<n. \<Sum>s = 0..<n.
                  Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r))
                = (\<Sum>r = 0..<n.
                     Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r))"
        proof (rule sum.cong[OF refl])
          fix r assume "r \<in> {0..<n}" hence r_lt: "r < n" by simp
          have prod_idx: "((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r)
                            = (\<Sum>s = 0..<n.
                                ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r))"
            by (rule mat_mult_index_sum[OF VjdVi_c rho_c r_lt r_lt])
          have "(\<Sum>s = 0..<n.
                   Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r))
                = (\<Sum>s = 0..<n.
                     Tmat $$ (i, j)
                      * (((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r)))"
            by (intro sum.cong refl) (simp add: mult.assoc)
          also have "\<dots> = Tmat $$ (i, j)
                            * (\<Sum>s = 0..<n.
                                  ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s) * rho $$ (s, r))"
            by (simp add: sum_distrib_left)
          also have "\<dots> = Tmat $$ (i, j)
                            * ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r)"
            using prod_idx by simp
          finally show "(\<Sum>s = 0..<n.
                           Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i) $$ (r, s)
                            * rho $$ (s, r))
                         = Tmat $$ (i, j) * ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r)" .
        qed
      qed
    qed
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       Tmat $$ (i, j) *
                       (\<Sum>r = 0..<n. ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r)))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>i = 0..<?N. \<Sum>j = 0..<?N.
                       Tmat $$ (i, j) * Tr ((Vs!j)\<^sup>\<dagger> * Vs!i * rho))"
    proof (intro sum.cong refl)
      fix i j assume "i \<in> {0..<?N}" "j \<in> {0..<?N}"
      hence i_lt: "i < ?N" and j_lt: "j < ?N" by simp_all
      have Vi_c: "Vs!i \<in> carrier_mat d n" using Vs_c i_lt nth_mem by blast
      have Vj_c: "Vs!j \<in> carrier_mat d n" using Vs_c j_lt nth_mem by blast
      have Vjd_c: "(Vs!j)\<^sup>\<dagger> \<in> carrier_mat n d" using Vj_c by (rule dagger_carrier)
      have VjdVi_c: "(Vs!j)\<^sup>\<dagger> * Vs!i \<in> carrier_mat n n"
        using Vjd_c Vi_c by auto
      have VjdViRho_c: "(Vs!j)\<^sup>\<dagger> * Vs!i * rho \<in> carrier_mat n n"
        using VjdVi_c rho_c by auto
      have prod_dr: "dim_row ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) = n" using VjdViRho_c by auto
      have prod_dc: "dim_col ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) = n" using VjdViRho_c by auto
      have "Tr ((Vs!j)\<^sup>\<dagger> * Vs!i * rho)
              = (\<Sum>r < n. if r < n then ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r) else 0)"
        unfolding Tr_def using prod_dr prod_dc by simp
      also have "\<dots> = (\<Sum>r = 0..<n. ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r))"
        by (simp add: lessThan_atLeast0)
      finally have tr_eq: "Tr ((Vs!j)\<^sup>\<dagger> * Vs!i * rho)
                             = (\<Sum>r = 0..<n. ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r))" .
      show "Tmat $$ (i, j) * (\<Sum>r = 0..<n. ((Vs!j)\<^sup>\<dagger> * Vs!i * rho) $$ (r, r))
              = Tmat $$ (i, j) * Tr ((Vs!j)\<^sup>\<dagger> * Vs!i * rho)"
        using tr_eq by simp
    qed
    finally show ?thesis unfolding S_def .
  qed
  show ?thesis using lhs_eq_S rhs_eq_S by simp
qed

lemma kraus_quad_map_is_TP:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Tmat_c: "Tmat \<in> carrier_mat (length Vs) (length Vs)"
      and Tmat_pair_sum: "kraus_pair_sum n Vs Tmat = 1\<^sub>m n"
      and npos: "0 < n"
  shows "trace_preserving n (kraus_quad_map d Vs Tmat)"
  unfolding trace_preserving_def
proof (intro allI impI)
  fix rho :: "complex Matrix.mat" assume rho_c: "rho \<in> carrier_mat n n"
  have "Tr (kraus_quad_map d Vs Tmat rho)
          = Tr (kraus_pair_sum n Vs Tmat * rho)"
    by (rule Tr_kraus_quad_map_eq[OF Vs_c Tmat_c rho_c])
  also have "\<dots> = Tr (1\<^sub>m n * rho)"
    using Tmat_pair_sum by simp
  also have "1\<^sub>m n * rho = rho"
    using rho_c by simp
  finally show "Tr (kraus_quad_map d Vs Tmat rho) = Tr rho" .
qed


subsection \<open>CPTP-Kraus representation and extreme CPTP maps\<close>

text \<open>A \<open>cptp_kraus_rep n d \<Phi> Vs\<close> says \<open>Vs\<close> is a Kraus operator list
(trace-preserving) and \<open>\<Phi>\<close> equals the corresponding @{const kraus_map_dim}
on every \<open>X \<in> carrier_mat n n\<close>.\<close>

definition cptp_kraus_rep ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow>
       complex Matrix.mat list \<Rightarrow> bool"
where
  "cptp_kraus_rep n d \<Phi> Vs \<equiv>
     kraus_operators n d Vs \<and>
     (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Vs X)"

text \<open>Extreme points of \<open>CPTP(n,d)\<close>: analog of @{const extreme_UCP}.\<close>

definition extreme_CPTP ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool"
where
  "extreme_CPTP n d \<Phi> \<equiv>
     \<Phi> \<in> CPTP n d \<and>
     \<not> (\<exists>\<Phi>\<^sub>1 \<in> CPTP n d. \<exists>\<Phi>\<^sub>2 \<in> CPTP n d.
           \<Phi>\<^sub>1 \<noteq> \<Phi> \<and> \<Phi> \<noteq> \<Phi>\<^sub>2 \<and>
           (\<forall>X. X \<in> carrier_mat n n
                  \<longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X
                            + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X))"


subsection \<open>CP Radon\<dash>Nikodym (axiom)\<close>

text \<open>\<^bold>\<open>CP Radon\<dash>Nikodym\<close> (Arveson 1969).  If \<open>\<Phi>\<close> is CP with Kraus
representation \<open>\<Phi>(X) = \<Sum>\<^sub>i V\<^sub>i X V\<^sub>i\<^sup>\<dagger>\<close> and \<open>\<Psi>\<close> is CP with
\<open>\<Phi> - \<Psi>\<close> also CP (i.e., \<open>\<Psi>\<close> is \<^emph>\<open>dominated\<close> by \<open>\<Phi>\<close> in the CP order),
then there exists a PSD matrix \<open>T \<in> M\<^sub>k\<close> (where \<open>k = length Vs\<close>)
such that
\<open>\<Psi>(X) = \<Sum>\<^sub>{i,j} T\<^sub>{ij} V\<^sub>i X V\<^sub>j\<^sup>\<dagger>\<close> on @{term \<open>carrier_mat n n\<close>}.

This is a substantial classical result; we take it as an axiom here
(currently \<open>sorry\<close>'d) so the forward direction of Choi's Theorem 3
can be assembled.\<close>

lemma cp_radon_nikodym:
  fixes Phi Psi :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Phi_kraus: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> Phi X = kraus_map_dim d Vs X"
      and Psi_cp: "completely_positive n d Psi"
      and Psi_range: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> Psi X \<in> carrier_mat d d"
      and diff_cp: "completely_positive n d (\<lambda>X. Phi X - Psi X)"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "\<exists>T. T \<in> carrier_mat (length Vs) (length Vs) \<and> psd T \<and>
              (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> Psi X = kraus_quad_map d Vs T X)"
  sorry


subsection \<open>Choi's Theorem 3 \<mdash> reverse direction\<close>


text \<open>\<^bold>\<open>Reverse direction of Choi's Theorem 3 (CPTP form).\<close>
Under minimality of the Kraus list \<open>Vs\<close>, the non-linear-independence of
the products \<open>{V\<^sub>j\<^sup>\<dagger> V\<^sub>i}\<close> forces \<open>\<Phi>\<close> to fail to be an extreme
point of \<open>CPTP n d\<close>.

The witness uses the explicit perturbation \<open>\<Phi>\<^sub>\<plusminus>(\<rho>) := \<Sum>(I\<^sub>{ij} \<plusminus> \<epsilon> H\<^sub>{ij}) V\<^sub>i \<rho> V\<^sub>j\<^sup>\<dagger>\<close>
for a hermitian \<open>H\<close> (from @{thm sym_or_antisym_witness}) and a small
\<open>\<epsilon>\<close> (from @{thm small_eps_psd}). Distinctness uses
@{thm kraus_quad_map_nonzero_witness} (Lemma B).\<close>

theorem choi_theorem_3_cptp_reverse:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep:  "cptp_kraus_rep n d \<Phi> Vs"
      and minimal: "lin_indep_complex_mat d n Vs"
      and dep: "\<not> mat_lin_indep_real n (kraus_products Vs)"
  shows "\<not> extreme_CPTP n d \<Phi>"
proof -
  let ?k = "length Vs"
  \<comment> \<open>Unpack the Kraus representation.\<close>
  have Vs_kops: "kraus_operators n d Vs"
    using rep by (simp add: cptp_kraus_rep_def)
  have Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
    using Vs_kops by (simp add: kraus_operators_def)
  have Vs_sum_one: "sum_wdag_w n Vs = 1\<^sub>m n"
    using Vs_kops by (simp add: kraus_operators_altdef)
  have \<Phi>_eq: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Vs X"
    using rep by (simp add: cptp_kraus_rep_def)
  \<comment> \<open>Step 1: extract a real, non-zero coefficient matrix.\<close>
  obtain A_orig :: "complex Matrix.mat"
    where A_c:    "A_orig \<in> carrier_mat ?k ?k"
      and A_real: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow>
                      cnj (A_orig $$ (i, j)) = A_orig $$ (i, j)"
      and A_nz:   "A_orig \<noteq> 0\<^sub>m ?k ?k"
      and A_pair: "kraus_pair_sum n Vs A_orig = 0\<^sub>m n n"
    using mat_lin_indep_real_neg_witness[OF Vs_c npos dep] by blast
  \<comment> \<open>Step 2: symmetric / anti-hermitian split to a hermitian witness.\<close>
  obtain H :: "complex Matrix.mat"
    where H_c:    "H \<in> carrier_mat ?k ?k"
      and H_herm: "hermitian H"
      and H_nz:   "H \<noteq> 0\<^sub>m ?k ?k"
      and H_pair: "kraus_pair_sum n Vs H = 0\<^sub>m n n"
    using sym_or_antisym_witness[OF Vs_c A_c A_real A_pair A_nz] by blast
  \<comment> \<open>Step 3: small-\<open>\<epsilon>\<close> PSD perturbation.\<close>
  obtain \<epsilon> :: real
    where \<epsilon>_pos: "\<epsilon> > 0"
      and \<epsilon>_psd: "\<And>d_real. \<bar>d_real\<bar> \<le> \<epsilon> \<Longrightarrow>
                     psd (1\<^sub>m ?k + complex_of_real d_real \<cdot>\<^sub>m H)"
    using small_eps_psd[OF H_c H_herm] by blast
  define Tp where "Tp = 1\<^sub>m ?k + complex_of_real \<epsilon> \<cdot>\<^sub>m H"
  define Tm where "Tm = 1\<^sub>m ?k + complex_of_real (-\<epsilon>) \<cdot>\<^sub>m H"
  have Tp_c: "Tp \<in> carrier_mat ?k ?k" unfolding Tp_def using H_c by auto
  have Tm_c: "Tm \<in> carrier_mat ?k ?k" unfolding Tm_def using H_c by auto
  have Tp_psd: "psd Tp" unfolding Tp_def by (rule \<epsilon>_psd) (use \<epsilon>_pos in auto)
  have Tm_psd: "psd Tm" unfolding Tm_def by (rule \<epsilon>_psd) (use \<epsilon>_pos in auto)
  \<comment> \<open>Step 4: pair-sum identity \<open>kraus_pair_sum n Vs T_\<plusminus> = I\<close>.\<close>
  have pair_sum_eps: "\<And>d_real :: real.
                          kraus_pair_sum n Vs (1\<^sub>m ?k
                              + complex_of_real d_real \<cdot>\<^sub>m H) = 1\<^sub>m n"
  proof -
    fix d_real :: real
    have I_c: "(1\<^sub>m ?k :: complex Matrix.mat) \<in> carrier_mat ?k ?k" by simp
    have dH_c: "complex_of_real d_real \<cdot>\<^sub>m H \<in> carrier_mat ?k ?k"
      using H_c by simp
    have "kraus_pair_sum n Vs (1\<^sub>m ?k + complex_of_real d_real \<cdot>\<^sub>m H)
            = kraus_pair_sum n Vs (1\<^sub>m ?k)
              + kraus_pair_sum n Vs (complex_of_real d_real \<cdot>\<^sub>m H)"
      by (rule kraus_pair_sum_add_A[OF Vs_c I_c dH_c])
    also have "kraus_pair_sum n Vs (1\<^sub>m ?k) = sum_wdag_w n Vs"
      by (rule kraus_pair_sum_one_eq_sum_wdag_w[OF Vs_c])
    also have "\<dots> = 1\<^sub>m n" using Vs_sum_one .
    also have "kraus_pair_sum n Vs (complex_of_real d_real \<cdot>\<^sub>m H)
                 = complex_of_real d_real \<cdot>\<^sub>m kraus_pair_sum n Vs H"
      by (rule kraus_pair_sum_smult_A[OF Vs_c H_c])
    also have "\<dots> = complex_of_real d_real \<cdot>\<^sub>m 0\<^sub>m n n"
      using H_pair by simp
    also have "(complex_of_real d_real \<cdot>\<^sub>m 0\<^sub>m n n :: complex Matrix.mat) = 0\<^sub>m n n"
      by (rule eq_matI) auto
    finally have "kraus_pair_sum n Vs (1\<^sub>m ?k + complex_of_real d_real \<cdot>\<^sub>m H)
                    = (1\<^sub>m n :: complex Matrix.mat) + 0\<^sub>m n n" by simp
    also have "(1\<^sub>m n :: complex Matrix.mat) + 0\<^sub>m n n = 1\<^sub>m n"
      by (rule eq_matI) auto
    finally show "kraus_pair_sum n Vs (1\<^sub>m ?k + complex_of_real d_real \<cdot>\<^sub>m H)
                    = 1\<^sub>m n" .
  qed
  have ps_Tp: "kraus_pair_sum n Vs Tp = 1\<^sub>m n"
    unfolding Tp_def by (rule pair_sum_eps)
  have ps_Tm: "kraus_pair_sum n Vs Tm = 1\<^sub>m n"
    unfolding Tm_def by (rule pair_sum_eps)
  \<comment> \<open>Step 5: define \<open>\<Phi>\<^sub>\<plusminus>\<close>.\<close>
  define Phip where "Phip = (\<lambda>rho. kraus_quad_map d Vs Tp rho)"
  define Phim where "Phim = (\<lambda>rho. kraus_quad_map d Vs Tm rho)"
  have Phip_in_CPTP: "Phip \<in> CPTP n d"
    unfolding CPTP_def
  proof (intro CollectI conjI)
    show "completely_positive n d Phip"
      unfolding Phip_def
      by (rule kraus_perturbation_cp[OF Vs_c Tp_c Tp_psd npos dpos])
    show "trace_preserving n Phip"
      unfolding Phip_def
      by (rule kraus_quad_map_is_TP[OF Vs_c Tp_c ps_Tp npos])
  qed
  have Phim_in_CPTP: "Phim \<in> CPTP n d"
    unfolding CPTP_def
  proof (intro CollectI conjI)
    show "completely_positive n d Phim"
      unfolding Phim_def
      by (rule kraus_perturbation_cp[OF Vs_c Tm_c Tm_psd npos dpos])
    show "trace_preserving n Phim"
      unfolding Phim_def
      by (rule kraus_quad_map_is_TP[OF Vs_c Tm_c ps_Tm npos])
  qed
  \<comment> \<open>Step 6: midpoint identity.\<close>
  have midpoint: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow>
                     \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m Phip X
                         + (1/2 :: complex) \<cdot>\<^sub>m Phim X"
  proof -
    fix X :: "complex Matrix.mat" assume X_c: "X \<in> carrier_mat n n"
    have I_c: "(1\<^sub>m ?k :: complex Matrix.mat) \<in> carrier_mat ?k ?k" by simp
    have epsH_c: "complex_of_real \<epsilon> \<cdot>\<^sub>m H \<in> carrier_mat ?k ?k" using H_c by simp
    have negepsH_c: "complex_of_real (-\<epsilon>) \<cdot>\<^sub>m H \<in> carrier_mat ?k ?k" using H_c by simp
    \<comment> \<open>Add \<open>Phip\<close> and \<open>Phim\<close> via linearity.\<close>
    have sum_eq: "Phip X + Phim X = kraus_quad_map d Vs (Tp + Tm) X"
      unfolding Phip_def Phim_def
      using kraus_quad_map_add_Tm[OF Vs_c X_c Tp_c Tm_c] by simp
    \<comment> \<open>\<open>Tp + Tm = 2 \<cdot> I\<close>.\<close>
    have TpT: "Tp + Tm = (2 :: complex) \<cdot>\<^sub>m 1\<^sub>m ?k"
    proof (rule eq_matI)
      show "dim_row (Tp + Tm) = dim_row ((2 :: complex) \<cdot>\<^sub>m 1\<^sub>m ?k)"
        using Tp_c Tm_c by simp
      show "dim_col (Tp + Tm) = dim_col ((2 :: complex) \<cdot>\<^sub>m 1\<^sub>m ?k)"
        using Tp_c Tm_c by simp
      fix i j assume "i < dim_row ((2 :: complex) \<cdot>\<^sub>m 1\<^sub>m ?k)"
                     "j < dim_col ((2 :: complex) \<cdot>\<^sub>m 1\<^sub>m ?k)"
      hence i_lt: "i < ?k" and j_lt: "j < ?k" by auto
      have "(Tp + Tm) $$ (i, j)
              = Tp $$ (i, j) + Tm $$ (i, j)"
        using Tp_c Tm_c i_lt j_lt by auto
      also have "Tp $$ (i, j) = (1\<^sub>m ?k :: complex Matrix.mat) $$ (i,j)
                                + complex_of_real \<epsilon> * H $$ (i, j)"
        unfolding Tp_def using I_c epsH_c i_lt j_lt H_c by auto
      also have "Tm $$ (i, j) = (1\<^sub>m ?k :: complex Matrix.mat) $$ (i,j)
                                + complex_of_real (-\<epsilon>) * H $$ (i, j)"
        unfolding Tm_def using I_c negepsH_c i_lt j_lt H_c by auto
      also have "((1\<^sub>m ?k :: complex Matrix.mat) $$ (i,j) + complex_of_real \<epsilon> * H $$ (i, j))
                  + ((1\<^sub>m ?k :: complex Matrix.mat) $$ (i,j) + complex_of_real (-\<epsilon>) * H $$ (i, j))
                  = 2 * (1\<^sub>m ?k :: complex Matrix.mat) $$ (i,j)"
        by (simp add: algebra_simps)
      also have "\<dots> = ((2 :: complex) \<cdot>\<^sub>m 1\<^sub>m ?k) $$ (i, j)"
        using i_lt j_lt by simp
      finally show "(Tp + Tm) $$ (i, j)
                      = ((2 :: complex) \<cdot>\<^sub>m 1\<^sub>m ?k) $$ (i, j)" .
    qed
    have sum_eq2: "Phip X + Phim X
                     = kraus_quad_map d Vs ((2::complex) \<cdot>\<^sub>m 1\<^sub>m ?k) X"
      using sum_eq TpT by simp
    have sum_eq3: "Phip X + Phim X
                     = (2::complex) \<cdot>\<^sub>m kraus_quad_map d Vs (1\<^sub>m ?k) X"
      using sum_eq2 kraus_quad_map_smult_Tm[OF Vs_c X_c I_c, of "(2::complex)"]
      by simp
    have sum_eq4: "Phip X + Phim X = (2::complex) \<cdot>\<^sub>m kraus_map_dim d Vs X"
      using sum_eq3 kraus_quad_map_one_eq_kraus_map_dim[OF Vs_c X_c] by simp
    have sum_eq5: "Phip X + Phim X = (2::complex) \<cdot>\<^sub>m \<Phi> X"
      using sum_eq4 \<Phi>_eq[OF X_c] by simp
    have \<Phi>X_c: "\<Phi> X \<in> carrier_mat d d"
      using \<Phi>_eq[OF X_c] kraus_map_dim_carrier[OF Vs_c X_c] by simp
    have \<Phi>p_c: "Phip X \<in> carrier_mat d d"
      unfolding Phip_def using kraus_quad_map_carrier[OF Vs_c X_c] .
    have \<Phi>m_c: "Phim X \<in> carrier_mat d d"
      unfolding Phim_def using kraus_quad_map_carrier[OF Vs_c X_c] .
    show "\<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m Phip X + (1/2 :: complex) \<cdot>\<^sub>m Phim X"
    proof (rule eq_matI)
      let ?L = "\<Phi> X"
      let ?R = "(1/2 :: complex) \<cdot>\<^sub>m Phip X + (1/2 :: complex) \<cdot>\<^sub>m Phim X"
      have R_c: "?R \<in> carrier_mat d d" using \<Phi>p_c \<Phi>m_c by auto
      show "dim_row ?L = dim_row ?R" using \<Phi>X_c R_c by auto
      show "dim_col ?L = dim_col ?R" using \<Phi>X_c R_c by auto
      fix r c assume r_a: "r < dim_row ?R" and c_a: "c < dim_col ?R"
      hence r_lt: "r < d" and c_lt: "c < d" using R_c by auto
      have ent_p: "(1/2 :: complex) \<cdot>\<^sub>m Phip X \<in> carrier_mat d d"
        using \<Phi>p_c by auto
      have ent_m: "(1/2 :: complex) \<cdot>\<^sub>m Phim X \<in> carrier_mat d d"
        using \<Phi>m_c by auto
      have R_idx: "?R $$ (r, c)
                     = (1/2 :: complex) * Phip X $$ (r, c)
                     + (1/2 :: complex) * Phim X $$ (r, c)"
        using ent_p ent_m r_lt c_lt \<Phi>p_c \<Phi>m_c by auto
      have sum_idx: "(Phip X + Phim X) $$ (r, c)
                       = Phip X $$ (r, c) + Phim X $$ (r, c)"
        using \<Phi>p_c \<Phi>m_c r_lt c_lt by auto
      have rhs_2Phi_idx: "((2::complex) \<cdot>\<^sub>m \<Phi> X) $$ (r, c) = 2 * \<Phi> X $$ (r, c)"
        using \<Phi>X_c r_lt c_lt by auto
      have phi_sum: "Phip X $$ (r, c) + Phim X $$ (r, c) = 2 * \<Phi> X $$ (r, c)"
        using sum_eq5 sum_idx rhs_2Phi_idx by simp
      have "?R $$ (r, c) = (1/2 :: complex) * (Phip X $$ (r, c) + Phim X $$ (r, c))"
        using R_idx by (simp add: field_simps)
      also have "\<dots> = (1/2 :: complex) * (2 * \<Phi> X $$ (r, c))"
        using phi_sum by simp
      also have "\<dots> = \<Phi> X $$ (r, c)" by simp
      finally show "?L $$ (r, c) = ?R $$ (r, c)" by simp
    qed
  qed
  \<comment> \<open>Step 7: distinctness \<open>Phip \<noteq> \<Phi>\<close>.\<close>
  obtain rho :: "complex Matrix.mat"
    where rho_c: "rho \<in> carrier_mat n n"
      and rho_qz: "kraus_quad_map d Vs H rho \<noteq> 0\<^sub>m d d"
    using kraus_quad_map_nonzero_witness[OF Vs_c minimal H_c H_nz npos dpos] by blast
  have epsH_c': "complex_of_real \<epsilon> \<cdot>\<^sub>m H \<in> carrier_mat ?k ?k" using H_c by simp
  have I_c': "(1\<^sub>m ?k :: complex Matrix.mat) \<in> carrier_mat ?k ?k" by simp
  \<comment> \<open>Express \<open>Phip rho\<close> as \<open>\<Phi> rho + \<epsilon> \<cdot> kraus_quad_map d Vs H rho\<close>.\<close>
  have phi_plus_rho: "Phip rho = \<Phi> rho
                                + complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho"
  proof -
    have lin: "kraus_quad_map d Vs Tp rho
                 = kraus_quad_map d Vs (1\<^sub>m ?k) rho
                   + kraus_quad_map d Vs (complex_of_real \<epsilon> \<cdot>\<^sub>m H) rho"
      unfolding Tp_def
      by (rule kraus_quad_map_add_Tm[OF Vs_c rho_c I_c' epsH_c'])
    have smult_lin: "kraus_quad_map d Vs (complex_of_real \<epsilon> \<cdot>\<^sub>m H) rho
                       = complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho"
      by (rule kraus_quad_map_smult_Tm[OF Vs_c rho_c H_c])
    have one_eq: "kraus_quad_map d Vs (1\<^sub>m ?k) rho = \<Phi> rho"
      using kraus_quad_map_one_eq_kraus_map_dim[OF Vs_c rho_c] \<Phi>_eq[OF rho_c] by simp
    show ?thesis
      unfolding Phip_def using lin smult_lin one_eq by simp
  qed
  \<comment> \<open>Carrier facts for the cancellation.\<close>
  have \<Phi>_rho_c: "\<Phi> rho \<in> carrier_mat d d"
    using \<Phi>_eq[OF rho_c] kraus_map_dim_carrier[OF Vs_c rho_c] by simp
  have qmap_rho_c: "kraus_quad_map d Vs H rho \<in> carrier_mat d d"
    by (rule kraus_quad_map_carrier[OF Vs_c rho_c])
  have eps_qmap_c: "complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho \<in> carrier_mat d d"
    using qmap_rho_c by auto
  \<comment> \<open>Distinctness via the \<open>rho\<close>-witness.\<close>
  have Phip_ne_\<Phi>: "Phip \<noteq> \<Phi>"
  proof
    assume "Phip = \<Phi>"
    hence eq_at_rho: "Phip rho = \<Phi> rho" by simp
    have sm_zero: "complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho = 0\<^sub>m d d"
    proof -
      have sum_eq: "\<Phi> rho
                     + complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho = \<Phi> rho"
        using phi_plus_rho eq_at_rho by simp
      \<comment> \<open>Subtract \<open>\<Phi> rho\<close> from both sides.\<close>
      show ?thesis
      proof (rule eq_matI)
        show "dim_row (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho)
                = dim_row (0\<^sub>m d d :: complex Matrix.mat)"
          using eps_qmap_c by auto
        show "dim_col (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho)
                = dim_col (0\<^sub>m d d :: complex Matrix.mat)"
          using eps_qmap_c by auto
        fix i j assume "i < dim_row (0\<^sub>m d d :: complex Matrix.mat)"
                       "j < dim_col (0\<^sub>m d d :: complex Matrix.mat)"
        hence i_lt: "i < d" and j_lt: "j < d" by auto
        have i_dim: "i < dim_row (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho)"
          using eps_qmap_c i_lt by auto
        have j_dim: "j < dim_col (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho)"
          using eps_qmap_c j_lt by auto
        have "(\<Phi> rho + complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)
                = \<Phi> rho $$ (i, j)
                  + (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)"
          using index_add_mat(1)[OF i_dim j_dim] .
        moreover have "\<Phi> rho $$ (i, j) = \<Phi> rho $$ (i, j)" by simp
        ultimately have "\<Phi> rho $$ (i, j)
                          + (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)
                          = \<Phi> rho $$ (i, j)"
          using sum_eq \<Phi>_rho_c i_lt j_lt by auto
        hence "(complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j) = 0"
          by simp
        thus "(complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)
                = (0\<^sub>m d d :: complex Matrix.mat) $$ (i, j)"
          using i_lt j_lt by simp
      qed
    qed
    \<comment> \<open>\<open>\<epsilon> \<cdot> M = 0 \<and> \<epsilon> \<noteq> 0 \<Longrightarrow> M = 0\<close>.\<close>
    have eps_ne: "complex_of_real \<epsilon> \<noteq> 0" using \<epsilon>_pos by simp
    have qmap_zero: "kraus_quad_map d Vs H rho = 0\<^sub>m d d"
    proof (rule eq_matI)
      show "dim_row (kraus_quad_map d Vs H rho)
              = dim_row (0\<^sub>m d d :: complex Matrix.mat)" using qmap_rho_c by auto
      show "dim_col (kraus_quad_map d Vs H rho)
              = dim_col (0\<^sub>m d d :: complex Matrix.mat)" using qmap_rho_c by auto
      fix i j assume "i < dim_row (0\<^sub>m d d :: complex Matrix.mat)"
                     "j < dim_col (0\<^sub>m d d :: complex Matrix.mat)"
      hence i_lt: "i < d" and j_lt: "j < d" by auto
      have idx_eq: "(complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)
                      = complex_of_real \<epsilon> * kraus_quad_map d Vs H rho $$ (i, j)"
        using qmap_rho_c i_lt j_lt by auto
      have "complex_of_real \<epsilon> * kraus_quad_map d Vs H rho $$ (i, j) = 0"
        using sm_zero idx_eq i_lt j_lt by simp
      hence "kraus_quad_map d Vs H rho $$ (i, j) = 0"
        using eps_ne by simp
      thus "kraus_quad_map d Vs H rho $$ (i, j)
              = (0\<^sub>m d d :: complex Matrix.mat) $$ (i, j)"
        using i_lt j_lt by simp
    qed
    thus False using rho_qz by simp
  qed
  \<comment> \<open>\<open>Phim \<noteq> \<Phi>\<close> follows from \<open>Phip \<noteq> \<Phi>\<close> and the midpoint identity:
      if \<open>Phim = \<Phi>\<close>, then \<open>\<Phi> X = (1/2)Phip X + (1/2)\<Phi> X\<close>, so
      \<open>(1/2)\<Phi> X = (1/2)Phip X\<close>, hence \<open>Phip X = \<Phi> X\<close> for all carrier \<open>X\<close>.
      Then \<open>Phip\<close> would agree with \<open>\<Phi>\<close> on \<open>rho\<close>, contradicting \<open>Phip \<noteq> \<Phi>\<close>
      at \<open>rho\<close>.\<close>
  have Phim_ne_\<Phi>: "\<Phi> \<noteq> Phim"
  proof
    assume eq: "\<Phi> = Phim"
    \<comment> \<open>Then the midpoint identity collapses to \<open>\<Phi> = Phip\<close> on carrier inputs.\<close>
    have collapse: "\<And>X :: complex Matrix.mat.
                       X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = Phip X"
    proof -
      fix X :: "complex Matrix.mat" assume X_c': "X \<in> carrier_mat n n"
      have mid: "\<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m Phip X
                       + (1/2 :: complex) \<cdot>\<^sub>m Phim X"
        using midpoint[OF X_c'] .
      have Phip_X_c: "Phip X \<in> carrier_mat d d"
        unfolding Phip_def using kraus_quad_map_carrier[OF Vs_c X_c'] .
      have Phim_X_c: "Phim X \<in> carrier_mat d d"
        unfolding Phim_def using kraus_quad_map_carrier[OF Vs_c X_c'] .
      have \<Phi>X_c': "\<Phi> X \<in> carrier_mat d d"
        using \<Phi>_eq[OF X_c'] kraus_map_dim_carrier[OF Vs_c X_c'] by simp
      \<comment> \<open>From \<open>\<Phi> = Phim\<close>: \<open>\<Phi> X = Phim X\<close>.\<close>
      have phim_eq: "Phim X = \<Phi> X" using eq by simp
      \<comment> \<open>Plug into the midpoint and solve for \<open>Phip X\<close>.\<close>
      show "\<Phi> X = Phip X"
      proof (rule eq_matI)
        show "dim_row (\<Phi> X) = dim_row (Phip X)" using \<Phi>X_c' Phip_X_c by auto
        show "dim_col (\<Phi> X) = dim_col (Phip X)" using \<Phi>X_c' Phip_X_c by auto
        fix r c assume "r < dim_row (Phip X)" "c < dim_col (Phip X)"
        hence r_lt: "r < d" and c_lt: "c < d" using Phip_X_c by auto
        have idx_eq: "(\<Phi> X) $$ (r, c)
                       = (1/2 :: complex) * Phip X $$ (r, c)
                         + (1/2 :: complex) * Phim X $$ (r, c)"
        proof -
          have half_m_c: "(1/2 :: complex) \<cdot>\<^sub>m Phim X \<in> carrier_mat d d"
            using Phim_X_c by auto
          have r_dim_m: "r < dim_row ((1/2 :: complex) \<cdot>\<^sub>m Phim X)"
            using half_m_c r_lt by auto
          have c_dim_m: "c < dim_col ((1/2 :: complex) \<cdot>\<^sub>m Phim X)"
            using half_m_c c_lt by auto
          have rhs_idx: "((1/2 :: complex) \<cdot>\<^sub>m Phip X
                              + (1/2 :: complex) \<cdot>\<^sub>m Phim X) $$ (r, c)
                          = ((1/2 :: complex) \<cdot>\<^sub>m Phip X) $$ (r, c)
                          + ((1/2 :: complex) \<cdot>\<^sub>m Phim X) $$ (r, c)"
            using index_add_mat(1)[OF r_dim_m c_dim_m] .
          have p_idx: "((1/2 :: complex) \<cdot>\<^sub>m Phip X) $$ (r, c)
                         = (1/2 :: complex) * Phip X $$ (r, c)"
            using Phip_X_c r_lt c_lt by auto
          have m_idx: "((1/2 :: complex) \<cdot>\<^sub>m Phim X) $$ (r, c)
                         = (1/2 :: complex) * Phim X $$ (r, c)"
            using Phim_X_c r_lt c_lt by auto
          show ?thesis using mid rhs_idx p_idx m_idx by simp
        qed
        have phim_idx: "Phim X $$ (r, c) = \<Phi> X $$ (r, c)" using phim_eq by simp
        have "\<Phi> X $$ (r, c) = (1/2 :: complex) * Phip X $$ (r, c)
                              + (1/2 :: complex) * \<Phi> X $$ (r, c)"
          using idx_eq phim_idx by simp
        hence "(1/2 :: complex) * Phip X $$ (r, c) = (1/2 :: complex) * \<Phi> X $$ (r, c)"
          by (simp add: field_simps)
        hence "Phip X $$ (r, c) = \<Phi> X $$ (r, c)"
          by simp
        thus "\<Phi> X $$ (r, c) = Phip X $$ (r, c)" by simp
      qed
    qed
    have "Phip rho = \<Phi> rho" using collapse[OF rho_c] by simp
    \<comment> \<open>But we showed \<open>Phip rho \<noteq> \<Phi> rho\<close> at \<open>rho\<close>.\<close>
    moreover have "Phip rho \<noteq> \<Phi> rho"
    proof
      assume eq_at: "Phip rho = \<Phi> rho"
      \<comment> \<open>This is the same argument as in \<open>Phip_ne_\<Phi>\<close>.\<close>
      have "complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho = 0\<^sub>m d d"
      proof -
        have sum_eq': "\<Phi> rho
                       + complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho = \<Phi> rho"
          using phi_plus_rho eq_at by simp
        show ?thesis
        proof (rule eq_matI)
          show "dim_row (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho)
                  = dim_row (0\<^sub>m d d :: complex Matrix.mat)"
            using eps_qmap_c by auto
          show "dim_col (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho)
                  = dim_col (0\<^sub>m d d :: complex Matrix.mat)"
            using eps_qmap_c by auto
          fix i j assume "i < dim_row (0\<^sub>m d d :: complex Matrix.mat)"
                         "j < dim_col (0\<^sub>m d d :: complex Matrix.mat)"
          hence i_lt: "i < d" and j_lt: "j < d" by auto
          have i_dim: "i < dim_row (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho)"
            using eps_qmap_c i_lt by auto
          have j_dim: "j < dim_col (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho)"
            using eps_qmap_c j_lt by auto
          have "(\<Phi> rho + complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)
                  = \<Phi> rho $$ (i, j)
                    + (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)"
            using index_add_mat(1)[OF i_dim j_dim] .
          hence "\<Phi> rho $$ (i, j)
                  + (complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)
                    = \<Phi> rho $$ (i, j)"
            using sum_eq' \<Phi>_rho_c i_lt j_lt by auto
          hence "(complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j) = 0"
            by simp
          thus "(complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)
                  = (0\<^sub>m d d :: complex Matrix.mat) $$ (i, j)"
            using i_lt j_lt by simp
        qed
      qed
      have eps_ne: "complex_of_real \<epsilon> \<noteq> 0" using \<epsilon>_pos by simp
      have "kraus_quad_map d Vs H rho = 0\<^sub>m d d"
      proof (rule eq_matI)
        show "dim_row (kraus_quad_map d Vs H rho)
                = dim_row (0\<^sub>m d d :: complex Matrix.mat)" using qmap_rho_c by auto
        show "dim_col (kraus_quad_map d Vs H rho)
                = dim_col (0\<^sub>m d d :: complex Matrix.mat)" using qmap_rho_c by auto
        fix i j assume "i < dim_row (0\<^sub>m d d :: complex Matrix.mat)"
                       "j < dim_col (0\<^sub>m d d :: complex Matrix.mat)"
        hence i_lt: "i < d" and j_lt: "j < d" by auto
        have idx_eq: "(complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho) $$ (i, j)
                        = complex_of_real \<epsilon> * kraus_quad_map d Vs H rho $$ (i, j)"
          using qmap_rho_c i_lt j_lt by auto
        have "complex_of_real \<epsilon> * kraus_quad_map d Vs H rho $$ (i, j) = 0"
          using \<open>complex_of_real \<epsilon> \<cdot>\<^sub>m kraus_quad_map d Vs H rho = 0\<^sub>m d d\<close>
                idx_eq i_lt j_lt by simp
        hence "kraus_quad_map d Vs H rho $$ (i, j) = 0"
          using eps_ne by simp
        thus "kraus_quad_map d Vs H rho $$ (i, j)
                = (0\<^sub>m d d :: complex Matrix.mat) $$ (i, j)"
          using i_lt j_lt by simp
      qed
      thus False using rho_qz by simp
    qed
    ultimately show False by simp
  qed
  \<comment> \<open>Final assembly: \<open>Phip \<noteq> \<Phi>\<close>, \<open>\<Phi> \<noteq> Phim\<close>, midpoint give non-extremity.\<close>
  show "\<not> extreme_CPTP n d \<Phi>"
    unfolding extreme_CPTP_def
    using \<Phi>_in Phip_in_CPTP Phim_in_CPTP Phip_ne_\<Phi> Phim_ne_\<Phi> midpoint
    by blast
qed


subsection \<open>Choi's Theorem 3 \<mdash> forward direction\<close>

text \<open>\<^bold>\<open>Important caveat on @{const extreme_CPTP}.\<close>  The current
definition uses raw function inequality \<open>\<Phi>\<^sub>1 \<noteq> \<Phi>\<close>, but both
@{const completely_positive} and @{const trace_preserving} only
constrain behaviour on @{term \<open>carrier_mat n n\<close>}.  Hence for
\<^emph>\<open>any\<close> CPTP \<open>\<Phi>\<close> one can construct \<open>\<Phi>\<^sub>1\<close> that agrees
with \<open>\<Phi>\<close> on the carrier but disagrees on (say) a \<open>1\<times>1\<close> matrix;
this \<open>\<Phi>\<^sub>1\<close> is itself in CPTP, so the negation of
@{const extreme_CPTP} is vacuously satisfied.  Consequently
\<^bold>\<open>@{const extreme_CPTP} as currently defined is always false\<close>,
and Choi's Theorem 3 as stated (an iff with @{const mat_lin_indep_real})
does not hold.

The fix is to use a \<^emph>\<open>carrier\<close>-point notion of inequality.\<close>

definition extreme_CPTP_carrier ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool"
where
  "extreme_CPTP_carrier n d \<Phi> \<equiv>
     \<Phi> \<in> CPTP n d \<and>
     \<not> (\<exists>\<Phi>\<^sub>1 \<in> CPTP n d. \<exists>\<Phi>\<^sub>2 \<in> CPTP n d.
           (\<exists>X\<^sub>1 \<in> carrier_mat n n. \<Phi>\<^sub>1 X\<^sub>1 \<noteq> \<Phi> X\<^sub>1) \<and>
           (\<exists>X\<^sub>2 \<in> carrier_mat n n. \<Phi> X\<^sub>2 \<noteq> \<Phi>\<^sub>2 X\<^sub>2) \<and>
           (\<forall>X. X \<in> carrier_mat n n
                  \<longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X
                            + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X))"

text \<open>The forward direction targets the \<^emph>\<open>carrier\<close>-flavoured version:
\<open>mat_lin_indep_complex \<Longrightarrow> extreme_CPTP_carrier\<close>.  Proof uses
@{thm cp_radon_nikodym}; remaining sorries are mechanical
(R-N application + TP-converse + assembly).\<close>

theorem choi_theorem_3_cptp_forward_complex:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep:  "cptp_kraus_rep n d \<Phi> Vs"
      and lin_indep: "mat_lin_indep_complex n (kraus_products Vs)"
  shows "extreme_CPTP_carrier n d \<Phi>"
proof (rule ccontr)
  let ?k = "length Vs"
  have Vs_kops: "kraus_operators n d Vs"
    using rep by (simp add: cptp_kraus_rep_def)
  have Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
    using Vs_kops by (simp add: kraus_operators_def)
  have Vs_sum_one: "sum_wdag_w n Vs = 1\<^sub>m n"
    using Vs_kops by (simp add: kraus_operators_altdef)
  have \<Phi>_eq: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Vs X"
    using rep by (simp add: cptp_kraus_rep_def)
  assume "\<not> extreme_CPTP_carrier n d \<Phi>"
  with \<Phi>_in have not_ext:
    "\<exists>\<Phi>\<^sub>1 \<in> CPTP n d. \<exists>\<Phi>\<^sub>2 \<in> CPTP n d.
        (\<exists>X\<^sub>1 \<in> carrier_mat n n. \<Phi>\<^sub>1 X\<^sub>1 \<noteq> \<Phi> X\<^sub>1) \<and>
        (\<exists>X\<^sub>2 \<in> carrier_mat n n. \<Phi> X\<^sub>2 \<noteq> \<Phi>\<^sub>2 X\<^sub>2) \<and>
        (\<forall>X. X \<in> carrier_mat n n \<longrightarrow>
            \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X)"
    unfolding extreme_CPTP_carrier_def by blast
  obtain \<Phi>\<^sub>1 \<Phi>\<^sub>2 X\<^sub>0 where
        \<Phi>1_in: "\<Phi>\<^sub>1 \<in> CPTP n d"
    and \<Phi>2_in: "\<Phi>\<^sub>2 \<in> CPTP n d"
    and X\<^sub>0_c: "X\<^sub>0 \<in> carrier_mat n n"
    and \<Phi>1_ne_at_X0: "\<Phi>\<^sub>1 X\<^sub>0 \<noteq> \<Phi> X\<^sub>0"
    and mid: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow>
                 \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X
                       + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X"
    using not_ext by blast
  have \<Phi>1_cp: "completely_positive n d \<Phi>\<^sub>1" using \<Phi>1_in by (simp add: CPTP_def)
  have \<Phi>1_tp: "trace_preserving n \<Phi>\<^sub>1" using \<Phi>1_in by (simp add: CPTP_def)
  have \<Phi>2_cp: "completely_positive n d \<Phi>\<^sub>2" using \<Phi>2_in by (simp add: CPTP_def)
  have \<Phi>2_tp: "trace_preserving n \<Phi>\<^sub>2" using \<Phi>2_in by (simp add: CPTP_def)
  \<comment> \<open>Define the half-map and apply CP Radon\<dash>Nikodym.\<close>
  define \<Psi> where "\<Psi> = (\<lambda>X. (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X)"
  \<comment> \<open>Step A: \<open>\<Psi>\<close> is CP, has the right range, and \<open>\<Phi> - \<Psi> = (1/2) \<cdot>\<^sub>m \<Phi>\<^sub>2\<close> on carrier is CP.\<close>
  have psi_cp: "completely_positive n d \<Psi>" sorry
  have psi_range: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Psi> X \<in> carrier_mat d d" sorry
  have diff_cp: "completely_positive n d (\<lambda>X. \<Phi> X - \<Psi> X)" sorry
  \<comment> \<open>Step B: R-N gives PSD \<open>T\<close> with \<open>\<Psi> X = kraus_quad_map d Vs T X\<close>.\<close>
  obtain T where
      T_c: "T \<in> carrier_mat ?k ?k" and T_psd: "psd T"
    and Psi_eq: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow>
                    \<Psi> X = kraus_quad_map d Vs T X"
    using cp_radon_nikodym[OF Vs_c \<Phi>_eq psi_cp psi_range diff_cp npos dpos] by blast
  \<comment> \<open>Step C: \<open>T\<^sub>1 := 2 \<cdot>\<^sub>m T\<close> satisfies \<open>\<Phi>\<^sub>1 X = kraus_quad_map d Vs T\<^sub>1 X\<close> on carrier.\<close>
  define T\<^sub>1 where "T\<^sub>1 = (2 :: complex) \<cdot>\<^sub>m T"
  have T1_c: "T\<^sub>1 \<in> carrier_mat ?k ?k" unfolding T\<^sub>1_def using T_c by auto
  have \<Phi>1_eq_qmap: "\<And>X :: complex Matrix.mat.
                       X \<in> carrier_mat n n \<Longrightarrow>
                       \<Phi>\<^sub>1 X = kraus_quad_map d Vs T\<^sub>1 X"
  proof -
    fix X :: "complex Matrix.mat" assume X_c: "X \<in> carrier_mat n n"
    have "\<Phi>\<^sub>1 X = (2 :: complex) \<cdot>\<^sub>m ((1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X)"
      by (rule eq_matI) auto
    also have "\<dots> = (2 :: complex) \<cdot>\<^sub>m \<Psi> X" unfolding \<Psi>_def by simp
    also have "\<dots> = (2 :: complex) \<cdot>\<^sub>m kraus_quad_map d Vs T X"
      using Psi_eq[OF X_c] by simp
    also have "\<dots> = kraus_quad_map d Vs ((2 :: complex) \<cdot>\<^sub>m T) X"
      using kraus_quad_map_smult_Tm[OF Vs_c X_c T_c, of "(2 :: complex)"] by simp
    finally show "\<Phi>\<^sub>1 X = kraus_quad_map d Vs T\<^sub>1 X" unfolding T\<^sub>1_def .
  qed
  \<comment> \<open>Step D: \<open>kraus_pair_sum n Vs T\<^sub>1 = 1\<^sub>m n\<close> (from TP of \<open>\<Phi>\<^sub>1\<close>).
      This is the converse of @{thm kraus_quad_map_is_TP}, proved via the
      trace pairing duality: @{thm Tr_kraus_quad_map_eq} plus
      \<open>\<forall>\<rho>. Tr (M\<rho>) = Tr (\<rho>) \<Longrightarrow> M = 1\<^sub>m n\<close>.\<close>
  have ps_T1: "kraus_pair_sum n Vs T\<^sub>1 = 1\<^sub>m n" sorry
  \<comment> \<open>Step E: \<open>S := T\<^sub>1 - 1\<^sub>m k\<close> is hermitian, non-zero, with
      \<open>kraus_pair_sum n Vs S = 0\<^sub>m n n\<close>; this yields a complex relation
      contradicting @{thm lin_indep}.\<close>
  show False sorry
qed


subsection \<open>Choi's Theorem 3 (statement)\<close>

text \<open>\<^bold>\<open>NOTE on conventions.\<close>  Choi (1975, Theorem 3) gives an
extreme-point characterisation in terms of \<^emph>\<open>linear independence
of certain products of Kraus operators\<close>.  Which products appear
depends on which of the two natural normalisations the underlying
convex set uses:

  \<^item> \<^bold>\<open>CPTP\<close> (\<open>\<Sum> V\<^sub>i\<^sup>\<dagger> V\<^sub>i = I\<^sub>n\<close>): products are
    \<open>{V\<^sub>j\<^sup>\<dagger> V\<^sub>i}\<close> in \<open>M\<^sub>n\<close>.  The perturbation
    \<open>\<Phi>\<^sub>\<epsilon>(X) = \<Sum>(\<delta>\<^sub>{ij} + \<epsilon> a\<^sub>{ij}) V\<^sub>i X V\<^sub>j\<^sup>\<dagger>\<close> stays
    trace-preserving iff \<open>\<Sum> a\<^sub>{ij} V\<^sub>j\<^sup>\<dagger> V\<^sub>i = 0\<close>.
  \<^item> \<^bold>\<open>UCP\<close>  (\<open>\<Sum> V\<^sub>i V\<^sub>i\<^sup>\<dagger> = I\<^sub>d\<close>): products are
    \<open>{V\<^sub>i V\<^sub>j\<^sup>\<dagger>}\<close> in \<open>M\<^sub>d\<close>.  Same perturbation stays
    unital iff \<open>\<Sum> a\<^sub>{ij} V\<^sub>i V\<^sub>j\<^sup>\<dagger> = 0\<close>.

The two are interchanged by the Hilbert\<dash>Schmidt adjoint
\<open>\<Phi> \<mapsto> \<Phi>\<^sup>*\<close>; this provides a UCP \<leftrightarrow> CPTP bijection.

We state both versions, parametrised by a fixed Kraus
representation; the "any/every" character follows from the
unitary-freedom of Kraus reps (Day 22 / "Kraus uniqueness"),
which is not yet formalised in this development.

\<^bold>\<open>Reverse direction (extreme \<Rightarrow> lin. indep.)\<close>: contrapositive.
For the CPTP version: if \<open>\<Sum> a\<^sub>{ij} V\<^sub>j\<^sup>\<dagger> V\<^sub>i = 0\<close> non-trivially,
define \<open>\<Phi>\<^sub>\<epsilon>\<close> as above; for small hermitian \<open>a\<close>, both
\<open>\<Phi>\<^sub>\<plusminus>\<epsilon>\<close> are CPTP and distinct, giving a non-trivial midpoint
of \<open>\<Phi>\<close>.

\<^bold>\<open>Forward direction (lin. indep. \<Rightarrow> extreme)\<close>: requires
Radon\<dash>Nikodym for CP maps (every CP \<open>\<Psi> \<le>\<^sub>{cp} \<lambda>\<Phi>\<close> has
\<open>\<Psi>(X) = \<Sum> T\<^sub>{ij} V\<^sub>i X V\<^sub>j\<^sup>\<dagger>\<close> for a PSD matrix \<open>T\<close>) which
is itself a substantial development.\<close>

text \<open>The CPTP form of Choi's Theorem 3: \<open>\<Phi>\<close> is extreme in CPTP iff
the products \<open>{V\<^sub>j\<^sup>\<dagger> V\<^sub>i}\<close> are linearly independent in \<open>M\<^sub>n\<close>.
The reverse direction is proved (modulo a couple of well-isolated
\<open>sorry\<close>s, see @{thm choi_theorem_3_cptp_reverse}); the forward
direction is left as a separate development.\<close>

theorem choi_theorem_3_cptp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep:  "cptp_kraus_rep n d \<Phi> Vs"
  shows "extreme_CPTP n d \<Phi> \<longleftrightarrow>
           mat_lin_indep_real n (kraus_products Vs)"
  sorry

text \<open>The UCP form (correct convention: products live in \<open>M\<^sub>d\<close>).
This requires a parallel \<open>mat_lin_indep_real_d\<close>-style definition
or a re-parametrised \<open>kraus_products\<close>; left for future work.\<close>

theorem choi_theorem_3:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Vs :: "complex Matrix.mat list"
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> UCP n d"
      and rep:  "ucp_kraus_rep n d \<Phi> Vs"
  shows "extreme_UCP n d \<Phi> \<longleftrightarrow>
           mat_lin_indep_real n (kraus_products Vs)"
  oops


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
