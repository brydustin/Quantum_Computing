(*  Title:   Day22_Convex_Sets.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 17 October 2011 (Day 22)
*)

theory Day22_Convex_Sets
  imports Day21_Kraus_Rank
begin

section \<open>Day 22 (17 October 2011): minimal Kraus representations, convex sets, UCP and CPTP\<close>

text \<open>\begin{notesprop}
If $\Phi$ is completely positive, $\crk(\Phi)=r$ and $\Phi(X)=\sum_{i=1}^rV_i^*XV_i$, then
$V_1,\dots,V_r$ are linearly independent.
\end{notesprop}
(Not formalised: on Day 23 linear independence of the Kraus operators is a hypothesis.)
\begin{notesdef}
$C\subseteq V$ is \emph{convex} if $tv_1+(1-t)v_2\in C$ for $v_1,v_2\in C$, $0\le t\le1$;
$v\in C$ is \emph{extreme} if $v=\tfrac12(v_1+v_2)$ with $v_1,v_2\in C$ forces $v=v_1=v_2$.
The \emph{convex hull} of $E$ is the set of convex combinations of points of $E$; a map
between convex sets is \emph{affine} if it preserves convex combinations.
\end{notesdef}
\begin{notestheorem}[Krein--Milman]
A compact convex subset of a finite-dimensional real vector space is the convex hull of its
extreme points.
\end{notestheorem}
Examples: $UCP(M_n,M_d)$, the unital completely positive maps, is convex ($P_{t\Phi_1+(1-t)\Phi_2}
=tP_{\Phi_1}+(1-t)P_{\Phi_2}\ge0$) and compact (closed; bounded because $0\le\Phi(E_{ii})\le I$ gives
$|r_{ij}|\le1$ for the entries of $P_\Phi$); $CPTP(M_d,M_n)$ is convex and compact, being the
image of $UCP(M_n,M_d)$ under the affine bijection $\Gamma(\Phi)=\Phi^*$.
\begin{notestheorem}[Choi 3]
If $\Phi:M_n\to M_d$ is unital and completely positive, $\Phi(X)=\sum_{i=1}^rV_i^*XV_i$ with
$r=\crk(\Phi)$, then $\Phi$ is an extreme point of $UCP(M_n,M_d)$ iff
$\{V_i^*V_j:1\le i,j\le r\}$ is linearly independent in $M_d$.
\end{notestheorem}
\begin{notescor}
If $\Phi$ is extreme then $\crk(\Phi)\le d$.  If $\Phi:M_d\to M_n$ is CPTP with
$\Phi(X)=\sum_{i=1}^rV_iXV_i^*$, $r=\crk(\Phi)$, then $\Phi$ is extreme in $CPTP(M_d,M_n)$ iff
$\{V_i^*V_j\}$ is linearly independent.
\end{notescor}
Convexity of UCP and CPTP is proved below; compactness and the affine bijection are not
formalised; the corollary $\crk(\Phi)\le d$ is \<open>extreme_CPTP_choi_rank_le\<close> in
\<open>Day22_Kraus_Independence\<close>, and Choi's Theorem 3 is proved in theory Day23 in its CPTP form.  Krein--Milman is available in HOL-Analysis (\<open>Krein_Milman_Minkowski\<close>).\<close>

subsection \<open>Convex sets and extreme points\<close>

definition convex_set_mat :: "complex Matrix.mat set \<Rightarrow> bool" where
  "convex_set_mat C \<equiv>
     \<forall>A \<in> C. \<forall>B \<in> C. \<forall>t :: real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
       complex_of_real t \<cdot>\<^sub>m A
       + (1 - complex_of_real t) \<cdot>\<^sub>m B \<in> C"

definition extreme_point_mat ::
  "complex Matrix.mat set \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "extreme_point_mat C v \<equiv>
     v \<in> C \<and>
     \<not> (\<exists>v1 \<in> C. \<exists>v2 \<in> C. v1 \<noteq> v \<and> v \<noteq> v2 \<and>
           v = (1/2 :: complex) \<cdot>\<^sub>m v1 + (1/2 :: complex) \<cdot>\<^sub>m v2)"

definition affine_map_mat ::
  "(complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "affine_map_mat tmap \<equiv>
     \<forall>A B. \<forall>t :: real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
       tmap (complex_of_real t \<cdot>\<^sub>m A
             + (1 - complex_of_real t) \<cdot>\<^sub>m B) =
       complex_of_real t \<cdot>\<^sub>m tmap A
       + (1 - complex_of_real t) \<cdot>\<^sub>m tmap B"


subsection \<open>The convex sets UCP and CPTP\<close>

definition UCP ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) set" where
  "UCP n d \<equiv> {\<Phi>. completely_positive n d \<Phi> \<and> unital_map n d \<Phi>}"

definition CPTP ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) set" where
  "CPTP n d \<equiv> {\<Phi>. completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>}"



lemma amplification_smult:
  assumes dpos: "0 < d"
      and F_block: "\<And>a b. F (block_of_mat n x a b) \<in> carrier_mat d d"
  shows "amplification n d p (\<lambda>\<rho>. c \<cdot>\<^sub>m F \<rho>) x
         = c \<cdot>\<^sub>m amplification n d p F x"
proof (rule eq_matI)
  show "dim_row (amplification n d p (\<lambda>\<rho>. c \<cdot>\<^sub>m F \<rho>) x) =
        dim_row (c \<cdot>\<^sub>m amplification n d p F x)"
    by (simp add: amplification_def)
  show "dim_col (amplification n d p (\<lambda>\<rho>. c \<cdot>\<^sub>m F \<rho>) x) =
        dim_col (c \<cdot>\<^sub>m amplification n d p F x)"
    by (simp add: amplification_def)
next
  fix i j
  assume i: "i < dim_row (c \<cdot>\<^sub>m amplification n d p F x)"
     and j: "j < dim_col (c \<cdot>\<^sub>m amplification n d p F x)"
  have ipd: "i < p*d" and jpd: "j < p*d"
    using i j by (simp_all add: amplification_def)
  have imodd: "i mod d < d" and jmodd: "j mod d < d"
    using dpos by simp_all
  let ?B = "block_of_mat n x (i div d) (j div d)"
  have FB: "F ?B \<in> carrier_mat d d"
    by (rule F_block)
  show "amplification n d p (\<lambda>\<rho>. c \<cdot>\<^sub>m F \<rho>) x $$ (i,j) =
        (c \<cdot>\<^sub>m amplification n d p F x) $$ (i,j)"
    using ipd jpd imodd jmodd FB
    by (simp add: amplification_def)
qed


text \<open>UCP is convex.  The range hypotheses are explicit because \<open>completely_positive\<close> does
not constrain the values of $\Phi_i$ off the carrier.\<close>

lemma UCP_convex:
  fixes t :: real
  assumes t_nn:   "0 \<le> t"
      and t_le:   "t \<le> 1"
      and \<Phi>1_in:  "\<Phi>1 \<in> UCP n d"
      and \<Phi>2_in:  "\<Phi>2 \<in> UCP n d"
      and r1: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>1 X \<in> carrier_mat d d"
      and r2: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>2 X \<in> carrier_mat d d"
      and dpos: "0 < d"
  shows "(\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X
              + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X) \<in> UCP n d"
proof -
  let ?\<Psi> = "\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X
                + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X"
  have cp1: "completely_positive n d \<Phi>1"
    using \<Phi>1_in by (simp add: UCP_def)
  have cp2: "completely_positive n d \<Phi>2"
    using \<Phi>2_in by (simp add: UCP_def)
  have un1: "unital_map n d \<Phi>1"
    using \<Phi>1_in by (simp add: UCP_def)
  have un2: "unital_map n d \<Phi>2"
    using \<Phi>2_in by (simp add: UCP_def)
  have one_minus_nn: "0 \<le> 1 - t" using t_le by simp
  have one_minus_eq: "(1 - complex_of_real t) = complex_of_real (1 - t)"
    by simp

  (* Unitality. *)
  have \<Psi>_unital: "unital_map n d ?\<Psi>"
  proof -
    have \<Phi>1_one: "\<Phi>1 (1\<^sub>m n) = 1\<^sub>m d" using un1 by (simp add: unital_map_def)
    have \<Phi>2_one: "\<Phi>2 (1\<^sub>m n) = 1\<^sub>m d" using un2 by (simp add: unital_map_def)
    have "?\<Psi> (1\<^sub>m n) = complex_of_real t \<cdot>\<^sub>m (1\<^sub>m d :: complex Matrix.mat)
                       + (1 - complex_of_real t) \<cdot>\<^sub>m (1\<^sub>m d)"
      using \<Phi>1_one \<Phi>2_one by simp
    also have "\<dots> = (complex_of_real t + (1 - complex_of_real t))
                     \<cdot>\<^sub>m (1\<^sub>m d :: complex Matrix.mat)"
      by (rule add_smult_distrib_right_mat[symmetric]) auto
    also have "\<dots> = (1 :: complex) \<cdot>\<^sub>m (1\<^sub>m d :: complex Matrix.mat)"
      by simp
    also have "\<dots> = 1\<^sub>m d"
      by (intro eq_matI) auto
    finally show ?thesis unfolding unital_map_def .
  qed

  (* Complete positivity. *)
  have \<Psi>_cp: "completely_positive n d ?\<Psi>"
    unfolding completely_positive_def p_positive_def
  proof (intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and X_c: "X \<in> carrier_mat (p*n) (p*n)"
       and X_psd: "psd X"
    have block_c: "\<And>a b. block_of_mat n X a b \<in> carrier_mat n n"
      by (simp add: block_of_mat_def)
    have F1_block: "\<And>a b. \<Phi>1 (block_of_mat n X a b) \<in> carrier_mat d d"
      using r1 block_c by blast
    have F2_block: "\<And>a b. \<Phi>2 (block_of_mat n X a b) \<in> carrier_mat d d"
      using r2 block_c by blast
    let ?F1 = "\<lambda>\<rho>. complex_of_real t \<cdot>\<^sub>m \<Phi>1 \<rho>"
    let ?F2 = "\<lambda>\<rho>. (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 \<rho>"
    have F1'_block: "\<And>a b. ?F1 (block_of_mat n X a b) \<in> carrier_mat d d"
      using F1_block by simp
    have F2'_block: "\<And>a b. ?F2 (block_of_mat n X a b) \<in> carrier_mat d d"
      using F2_block by simp

    (* amplification distributes over the convex combination *)
    have amp_eq:
      "amplification n d p ?\<Psi> X
         = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
           + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
    proof -
      have step_add:
        "amplification n d p (\<lambda>\<rho>. ?F1 \<rho> + ?F2 \<rho>) X
           = amplification n d p ?F1 X + amplification n d p ?F2 X"
        using amplification_add[where F = ?F1 and G = ?F2
                                 and n = n and d = d and p = p and x = X,
                                OF dpos F1'_block F2'_block] .
      have step_s1:
        "amplification n d p ?F1 X
           = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X"
        using amplification_smult[where F = \<Phi>1 and c = "complex_of_real t"
                                   and n = n and d = d and p = p and x = X,
                                  OF dpos F1_block] .
      have step_s2:
        "amplification n d p ?F2 X
           = (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
        using amplification_smult[where F = \<Phi>2 and c = "1 - complex_of_real t"
                                   and n = n and d = d and p = p and x = X,
                                  OF dpos F2_block] .
      show ?thesis using step_add step_s1 step_s2 by simp
    qed

    have amp1_psd: "psd (amplification n d p \<Phi>1 X)"
      using cp1 ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    have amp2_psd: "psd (amplification n d p \<Phi>2 X)"
      using cp2 ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    have amp1_c: "amplification n d p \<Phi>1 X \<in> carrier_mat (p*d) (p*d)"
      by (simp add: amplification_def)
    have amp2_c: "amplification n d p \<Phi>2 X \<in> carrier_mat (p*d) (p*d)"
      by (simp add: amplification_def)

    have term1_psd:
      "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X)"
      using t_nn amp1_psd amp1_c by (rule psd_smult_nonneg)
    have term2_psd:
      "psd ((1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
    proof -
      have prev: "psd (complex_of_real (1 - t)
                          \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
        using one_minus_nn amp2_psd amp2_c by (rule psd_smult_nonneg)
      have rew: "complex_of_real (1 - t) = 1 - complex_of_real t"
        by simp
      show ?thesis using prev rew by metis
    qed
    have term1_c:
      "complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
        \<in> carrier_mat (p*d) (p*d)"
      using amp1_c by simp
    have term2_c:
      "(1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X
        \<in> carrier_mat (p*d) (p*d)"
      using amp2_c by simp

    have psum_psd:
      "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
            + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
      using term1_psd term2_psd term1_c term2_c
      by (rule psd_add_psd)

    show "psd (amplification n d p ?\<Psi> X)"
      using amp_eq psum_psd by simp
  qed

  show ?thesis using \<Psi>_cp \<Psi>_unital by (simp add: UCP_def)
qed


text \<open>CPTP is convex.\<close>

lemma CPTP_convex:
  fixes t :: real
  assumes t_nn:   "0 \<le> t"
      and t_le:   "t \<le> 1"
      and \<Phi>1_in:  "\<Phi>1 \<in> CPTP n d"
      and \<Phi>2_in:  "\<Phi>2 \<in> CPTP n d"
      and r1: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>1 X \<in> carrier_mat d d"
      and r2: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>2 X \<in> carrier_mat d d"
      and dpos: "0 < d"
  shows "(\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X
              + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X) \<in> CPTP n d"
proof -
  let ?\<Psi> = "\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X
                + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X"
  have cp1: "completely_positive n d \<Phi>1"
    using \<Phi>1_in by (simp add: CPTP_def)
  have cp2: "completely_positive n d \<Phi>2"
    using \<Phi>2_in by (simp add: CPTP_def)
  have tp1: "trace_preserving n \<Phi>1"
    using \<Phi>1_in by (simp add: CPTP_def)
  have tp2: "trace_preserving n \<Phi>2"
    using \<Phi>2_in by (simp add: CPTP_def)

  have one_minus_nn: "0 \<le> 1 - t" using t_le by simp

  (* CP: copy of UCP_convex's CP half. *)
  have \<Psi>_cp: "completely_positive n d ?\<Psi>"
    unfolding completely_positive_def p_positive_def
  proof (intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and X_c: "X \<in> carrier_mat (p*n) (p*n)"
       and X_psd: "psd X"
    have block_c: "\<And>a b. block_of_mat n X a b \<in> carrier_mat n n"
      by (simp add: block_of_mat_def)
    have F1_block: "\<And>a b. \<Phi>1 (block_of_mat n X a b) \<in> carrier_mat d d"
      using r1 block_c by blast
    have F2_block: "\<And>a b. \<Phi>2 (block_of_mat n X a b) \<in> carrier_mat d d"
      using r2 block_c by blast
    let ?F1 = "\<lambda>\<rho>. complex_of_real t \<cdot>\<^sub>m \<Phi>1 \<rho>"
    let ?F2 = "\<lambda>\<rho>. (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 \<rho>"
    have F1'_block: "\<And>a b. ?F1 (block_of_mat n X a b) \<in> carrier_mat d d"
      using F1_block by simp
    have F2'_block: "\<And>a b. ?F2 (block_of_mat n X a b) \<in> carrier_mat d d"
      using F2_block by simp
    have amp_eq:
      "amplification n d p ?\<Psi> X
         = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
           + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
    proof -
      have step_add:
        "amplification n d p (\<lambda>\<rho>. ?F1 \<rho> + ?F2 \<rho>) X
           = amplification n d p ?F1 X + amplification n d p ?F2 X"
        using amplification_add[where F = ?F1 and G = ?F2
                                 and n = n and d = d and p = p and x = X,
                                OF dpos F1'_block F2'_block] .
      have step_s1:
        "amplification n d p ?F1 X
           = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X"
        using amplification_smult[where F = \<Phi>1 and c = "complex_of_real t"
                                   and n = n and d = d and p = p and x = X,
                                  OF dpos F1_block] .
      have step_s2:
        "amplification n d p ?F2 X
           = (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
        using amplification_smult[where F = \<Phi>2 and c = "1 - complex_of_real t"
                                   and n = n and d = d and p = p and x = X,
                                  OF dpos F2_block] .
      show ?thesis using step_add step_s1 step_s2 by simp
    qed
    have amp1_psd: "psd (amplification n d p \<Phi>1 X)"
      using cp1 ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    have amp2_psd: "psd (amplification n d p \<Phi>2 X)"
      using cp2 ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    have amp1_c: "amplification n d p \<Phi>1 X \<in> carrier_mat (p*d) (p*d)"
      by (simp add: amplification_def)
    have amp2_c: "amplification n d p \<Phi>2 X \<in> carrier_mat (p*d) (p*d)"
      by (simp add: amplification_def)
    have term1_psd:
      "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X)"
      using t_nn amp1_psd amp1_c by (rule psd_smult_nonneg)
    have term2_psd:
      "psd ((1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
    proof -
      have prev: "psd (complex_of_real (1 - t)
                          \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
        using one_minus_nn amp2_psd amp2_c by (rule psd_smult_nonneg)
      have rew: "complex_of_real (1 - t) = 1 - complex_of_real t" by simp
      show ?thesis using prev rew by metis
    qed
    have term1_c:
      "complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
        \<in> carrier_mat (p*d) (p*d)"
      using amp1_c by simp
    have term2_c:
      "(1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X
        \<in> carrier_mat (p*d) (p*d)"
      using amp2_c by simp
    have psum_psd:
      "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
            + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
      using term1_psd term2_psd term1_c term2_c by (rule psd_add_psd)
    show "psd (amplification n d p ?\<Psi> X)"
      using amp_eq psum_psd by simp
  qed

  (* Trace preservation: Tr(t Phi1 X + (1-t) Phi2 X) = Tr X. *)
  have \<Psi>_tp: "trace_preserving n ?\<Psi>"
  proof (unfold trace_preserving_def, intro allI impI)
    fix X :: "complex Matrix.mat"
    assume X_c: "X \<in> carrier_mat n n"
    have \<Phi>1X_c: "\<Phi>1 X \<in> carrier_mat d d" using r1 X_c by blast
    have \<Phi>2X_c: "\<Phi>2 X \<in> carrier_mat d d" using r2 X_c by blast
    have Tr1: "Tr (\<Phi>1 X) = Tr X"
      using tp1 X_c by (simp add: trace_preserving_def)
    have Tr2: "Tr (\<Phi>2 X) = Tr X"
      using tp2 X_c by (simp add: trace_preserving_def)
    have row_eq:
      "dim_row (complex_of_real t \<cdot>\<^sub>m \<Phi>1 X)
       = dim_row ((1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
      using \<Phi>1X_c \<Phi>2X_c by simp
    have col_eq:
      "dim_col (complex_of_real t \<cdot>\<^sub>m \<Phi>1 X)
       = dim_col ((1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
      using \<Phi>1X_c \<Phi>2X_c by simp
    have "Tr (?\<Psi> X) = Tr (complex_of_real t \<cdot>\<^sub>m \<Phi>1 X)
                       + Tr ((1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
      using row_eq col_eq by (rule Tr_add)
    also have "\<dots> = complex_of_real t * Tr (\<Phi>1 X)
                    + (1 - complex_of_real t) * Tr (\<Phi>2 X)"
      by (simp add: Tr_smult)
    also have "\<dots> = complex_of_real t * Tr X
                    + (1 - complex_of_real t) * Tr X"
      using Tr1 Tr2 by simp
    also have "\<dots> = (complex_of_real t + (1 - complex_of_real t)) * Tr X"
      by (simp add: ring_distribs)
    also have "\<dots> = 1 * Tr X" by simp
    also have "\<dots> = Tr X" by simp
    finally show "Tr (?\<Psi> X) = Tr X" .
  qed

  show ?thesis using \<Psi>_cp \<Psi>_tp by (simp add: CPTP_def)
qed

lemma kraus_is_cptp:
  fixes Ws :: "complex Matrix.mat list"
  assumes Ws: "kraus_operators n d Ws"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "kraus_map_dim d Ws \<in> CPTP n d"
  unfolding CPTP_def
  using kraus_is_cp[OF Ws npos dpos] kraus_is_trace_preserving[OF Ws]
  by simp

end
