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

text \<open>The Heisenberg-dual definitions for the CPTP / Heisenberg
side: a \<open>cptp_kraus_rep n d \<Phi> Vs\<close> is the trace-preserving
Kraus condition, using the existing \<open>kraus_operators\<close> predicate
from Day 17.\<close>

definition cptp_kraus_rep ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow>
       complex Matrix.mat list \<Rightarrow> bool"
where
  "cptp_kraus_rep n d \<Phi> Vs \<equiv>
     kraus_operators n d Vs \<and>
     (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Vs X)"

text \<open>Extreme points of \<open>CPTP(n,d)\<close>: analog of \<open>extreme_UCP\<close>.\<close>

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

text \<open>The CPTP form of Choi's Theorem 3: \<open>\<Phi>\<close> is extreme in CPTP iff
the products \<open>{V\<^sub>j\<^sup>\<dagger> V\<^sub>i}\<close> are linearly independent in \<open>M\<^sub>n\<close>.\<close>

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
