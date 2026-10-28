(*  Title:   Day22_Minimal_Kraus.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 17 October 2011 (Day 22)
*)

theory Day22_Minimal_Kraus
  imports Day21_Unitary_Freedom Jordan_Normal_Form.DL_Rank
begin

section \<open>Day 22 (17 October 2011): minimal Kraus representations, convex sets, UCP and CPTP\<close>

text \<open>\begin{notesprop}
If $\Phi$ is completely positive, $\crk(\Phi)=r$ and $\Phi(X)=\sum_{i=1}^rV_i^*XV_i$, then
$V_1,\dots,V_r$ are linearly independent.
\end{notesprop}
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
Below: convexity of UCP and CPTP, the proposition (\<open>minimal_kraus_rep_lin_indep\<close>), with it
Choi's rank theorem of Day 20, and the affine bijection $\Gamma$; compactness is the next
theory.  Choi's Theorem 3 and its corollary $\crk(\Phi)\le d$ (\<open>extreme_CPTP_choi_rank_le\<close>)
are proved on Day 23, in the CPTP form.  Krein--Milman is available in HOL-Analysis
(\<open>Krein_Milman_Minkowski\<close>).\<close>

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

text \<open>Convex combinations: the amplification is linear in the map, and positive matrices are closed
under non-negative combinations, so $t\Phi_1+(1-t)\Phi_2$ is completely positive; it is unital, resp.
trace preserving, when $\Phi_1$ and $\Phi_2$ are.\<close>

lemma completely_positive_convex:
  fixes t :: real
  assumes t_nn: "0 \<le> t" and t_le: "t \<le> 1"
      and cp1: "completely_positive n d \<Phi>1" and cp2: "completely_positive n d \<Phi>2"
      and r1: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>1 X \<in> carrier_mat d d"
      and r2: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>2 X \<in> carrier_mat d d"
      and dpos: "0 < d"
  shows "completely_positive n d (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
  unfolding completely_positive_def p_positive_def
proof (intro allI impI)
  fix p :: nat and X :: "complex Matrix.mat"
  assume ppos: "0 < p" and X: "X \<in> carrier_mat (p*n) (p*n)" and Xpsd: "psd X"
  have blk: "\<And>a b. block_of_mat n X a b \<in> carrier_mat n n" by (simp add: block_of_mat_def)
  have b1: "\<And>a b. \<Phi>1 (block_of_mat n X a b) \<in> carrier_mat d d" using r1 blk by blast
  have b2: "\<And>a b. \<Phi>2 (block_of_mat n X a b) \<in> carrier_mat d d" using r2 blk by blast
  have b1': "\<And>a b. complex_of_real t \<cdot>\<^sub>m \<Phi>1 (block_of_mat n X a b) \<in> carrier_mat d d" using b1 by simp
  have b2': "\<And>a b. (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 (block_of_mat n X a b) \<in> carrier_mat d d" using b2 by simp
  have amp: "amplification n d p (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X) X
             = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
    unfolding amplification_add[where F = "\<lambda>\<rho>. complex_of_real t \<cdot>\<^sub>m \<Phi>1 \<rho>"
                                and G = "\<lambda>\<rho>. (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 \<rho>", OF dpos b1' b2']
              amplification_smult[where F = \<Phi>1 and c = "complex_of_real t", OF dpos b1]
              amplification_smult[where F = \<Phi>2 and c = "1 - complex_of_real t", OF dpos b2] ..
  have A1: "psd (amplification n d p \<Phi>1 X)" and A2: "psd (amplification n d p \<Phi>2 X)"
    using cp1 cp2 ppos X Xpsd by (auto simp: completely_positive_def p_positive_def)
  have C1: "amplification n d p \<Phi>1 X \<in> carrier_mat (p*d) (p*d)"
   and C2: "amplification n d p \<Phi>2 X \<in> carrier_mat (p*d) (p*d)" by (simp_all add: amplification_def)
  have P1: "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X)" by (rule psd_smult_nonneg[OF t_nn A1 C1])
  have P2: "psd ((1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
    using psd_smult_nonneg[OF _ A2 C2, of "1 - t"] t_le by simp
  show "psd (amplification n d p (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X) X)"
    unfolding amp by (rule psd_add_psd[OF P1 P2 smult_carrier_mat[OF C1] smult_carrier_mat[OF C2]])
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
  have "\<Phi>1 (1\<^sub>m n) = 1\<^sub>m d" "\<Phi>2 (1\<^sub>m n) = 1\<^sub>m d" using \<Phi>1_in \<Phi>2_in by (simp_all add: UCP_def unital_map_def)
  hence "unital_map n d (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
    unfolding unital_map_def by (intro eq_matI) auto
  thus ?thesis using completely_positive_convex[OF t_nn t_le _ _ r1 r2 dpos] \<Phi>1_in \<Phi>2_in by (simp add: UCP_def)
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
  have "trace_preserving n (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
    unfolding trace_preserving_def
  proof (intro allI impI)
    fix X :: "complex Matrix.mat" assume X: "X \<in> carrier_mat n n"
    have c: "\<Phi>1 X \<in> carrier_mat d d" "\<Phi>2 X \<in> carrier_mat d d" using r1 r2 X by blast+
    have "Tr (complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)
          = complex_of_real t * Tr (\<Phi>1 X) + (1 - complex_of_real t) * Tr (\<Phi>2 X)"
      using c by (subst Tr_add) (simp_all add: Tr_smult)
    thus "Tr (complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X) = Tr X"
      using \<Phi>1_in \<Phi>2_in X by (simp add: CPTP_def trace_preserving_def algebra_simps)
  qed
  thus ?thesis using completely_positive_convex[OF t_nn t_le _ _ r1 r2 dpos] \<Phi>1_in \<Phi>2_in by (simp add: CPTP_def)
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

subsection \<open>A minimal Kraus representation is linearly independent (D22-1)\<close>

subsubsection \<open>Mixing a Kraus list by an isometry does not change the map\<close>

definition kraus_mix :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "kraus_mix d n U Vs =
     map (\<lambda>l. foldr (\<lambda>j acc. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<length Vs] (0\<^sub>m d n)) [0..<dim_row U]"

lemma kraus_mix_length [simp]: "length (kraus_mix d n U Vs) = dim_row U"
  by (simp add: kraus_mix_def)

lemma kraus_mix_nth:
  assumes "l < dim_row U"
  shows "kraus_mix d n U Vs ! l = foldr (\<lambda>j acc. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<length Vs] (0\<^sub>m d n)"
  using assms by (simp add: kraus_mix_def)

lemma kraus_mix_carrier:
  assumes "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "\<forall>W \<in> set (kraus_mix d n U Vs). W \<in> carrier_mat d n"
proof
  fix W assume "W \<in> set (kraus_mix d n U Vs)"
  then obtain l where "W = foldr (\<lambda>j acc. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<length Vs] (0\<^sub>m d n)"
    by (auto simp: kraus_mix_def)
  thus "W \<in> carrier_mat d n" using assms by (auto intro!: foldr_add_carrier_dn)
qed

text \<open>Mixing a Kraus list by a matrix $U=(u_{lj})$ gives $W_l=\sum_ju_{lj}V_j$.  When $U^*U=I$ the two lists
define the same map:
\[ \sum_lW_lXW_l^*=\sum_{j,j'}\Bigl(\sum_l\overline{u_{lj'}}\,u_{lj}\Bigr)V_jXV_{j'}^*=\sum_jV_jXV_j^*. \]\<close>

lemma kraus_mix_entry:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and l: "l < dim_row U" and i: "i < d" and a: "a < n"
  shows "kraus_mix d n U Vs ! l $$ (i,a) = (\<Sum>j = 0..<length Vs. U $$ (l,j) * Vs ! j $$ (i,a))"
proof -
  have fc: "\<forall>j \<in> set [0..<length Vs]. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) \<in> carrier_mat d n" using Vs_c by auto
  show ?thesis
    unfolding kraus_mix_nth[OF l] foldr_add_mat_index_rect[OF fc i a]
  proof -
    have "(\<Sum>j\<leftarrow>[0..<length Vs]. (U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)) $$ (i,a)) = (\<Sum>j<length Vs. (U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)) $$ (i,a))"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>j<length Vs. U $$ (l,j) * Vs ! j $$ (i,a))"
    proof (intro sum.cong refl)
      fix j assume "j \<in> {..<length Vs}"
      hence Vj: "Vs ! j \<in> carrier_mat d n" using Vs_c nth_mem[of j Vs] by auto
      show "(U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)) $$ (i,a) = U $$ (l,j) * Vs ! j $$ (i,a)" using carrier_matD[OF Vj] i a by simp
    qed
    finally show "(\<Sum>j\<leftarrow>[0..<length Vs]. (U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)) $$ (i,a)) = (\<Sum>j = 0..<length Vs. U $$ (l,j) * Vs ! j $$ (i,a))"
      by (simp add: atLeast0LessThan)
  qed
qed

lemma kraus_mix_mat_of_cols:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and Uc: "U \<in> carrier_mat m (length Vs)" and dpos: "0 < d"
  shows "mat_of_cols (n*d) (map (vec_of_kraus d n) (kraus_mix d n U Vs))
         = mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U"
proof (rule eq_matI)
  let ?Ws = "kraus_mix d n U Vs"
  have Ws_c: "\<forall>W \<in> set ?Ws. W \<in> carrier_mat d n" by (rule kraus_mix_carrier[OF Vs_c])
  have dimU: "dim_row U = m" using Uc by simp
  fix r l assume "r < dim_row (mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U)"
             and "l < dim_col (mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U)"
  hence r: "r < n*d" and l: "l < m" using Uc by auto
  define a where "a = r div d"
  define i where "i = r mod d"
  have a: "a < n" using r dpos by (simp add: a_def less_mult_imp_div_less)
  have i: "i < d" using dpos by (simp add: i_def)
  have r_eq: "r = a*d + i" unfolding a_def i_def by simp
  have "mat_of_cols (n*d) (map (vec_of_kraus d n) ?Ws) $$ (r, l) = ?Ws ! l $$ (i,a)"
    unfolding r_eq using vec_of_kraus_mat_of_cols_index[OF Ws_c dpos i a] l dimU by simp
  also have "\<dots> = (\<Sum>j = 0..<length Vs. U $$ (l,j) * Vs ! j $$ (i,a))"
    using kraus_mix_entry[OF Vs_c _ i a] l dimU by simp
  also have "\<dots> = (\<Sum>j = 0..<length Vs. mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) $$ (r, j) * transpose_mat U $$ (j, l))"
    unfolding r_eq
  proof (intro sum.cong refl)
    fix j assume "j \<in> {0..<length Vs}"
    hence j: "j < length Vs" by simp
    show "U $$ (l,j) * Vs ! j $$ (i,a) = mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) $$ (a*d + i, j) * transpose_mat U $$ (j, l)"
      unfolding vec_of_kraus_mat_of_cols_index[OF Vs_c dpos i a j] using l j carrier_matD[OF Uc] by (simp add: mult.commute)
  qed
  also have "\<dots> = (mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U) $$ (r, l)"
    using r l carrier_matD[OF Uc] by (simp add: scalar_prod_def atLeast0LessThan)
  finally show "mat_of_cols (n*d) (map (vec_of_kraus d n) ?Ws) $$ (r, l)
                = (mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U) $$ (r, l)" .
qed (use Uc in auto)

lemma kraus_mix_same_map:
  assumes npos: "0 < n" and dpos: "0 < d"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Uc: "U \<in> carrier_mat m (length Vs)" and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m (length Vs)"
      and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim d (kraus_mix d n U Vs) M = kraus_map_dim d Vs M"
proof -
  let ?Ws = "kraus_mix d n U Vs"
  let ?V = "mat_of_cols (n*d) (map (vec_of_kraus d n) Vs)"
  have Ws_c: "\<forall>W \<in> set ?Ws. W \<in> carrier_mat d n" by (rule kraus_mix_carrier[OF Vs_c])
  have Vc: "?V \<in> carrier_mat (n*d) (length Vs)" using mat_of_cols_carrier[of "n*d" "map (vec_of_kraus d n) Vs"] by simp
  have "choi_matrix n d (kraus_map_dim d ?Ws) = outer_sum (n*d) (map (vec_of_kraus d n) ?Ws)"
    by (rule choi_matrix_kraus_eq[OF Ws_c npos dpos])
  also have "\<dots> = (?V * transpose_mat U) * ((?V * transpose_mat U)\<^sup>\<dagger>)"
    unfolding outer_sum_def kraus_mix_mat_of_cols[OF Vs_c Uc dpos] ..
  also have "\<dots> = ?V * (?V\<^sup>\<dagger>)" by (rule isometry_mix_outer[OF Vc Uc UU])
  also have "\<dots> = outer_sum (n*d) (map (vec_of_kraus d n) Vs)" unfolding outer_sum_def ..
  also have "\<dots> = choi_matrix n d (kraus_map_dim d Vs)" by (rule choi_matrix_kraus_eq[OF Vs_c npos dpos, symmetric])
  finally have choi: "choi_matrix n d (kraus_map_dim d ?Ws) = choi_matrix n d (kraus_map_dim d Vs)" .
  show ?thesis
    by (rule map_eq_from_choi_when_linear[OF kraus_lin_on[OF Ws_c] kraus_lin_on[OF Vs_c] choi Xc])
qed

subsubsection \<open>A unitary with a prescribed first row\<close>

lemma transpose_unitary_isometry:
  assumes Mc: "M \<in> carrier_mat r r" and MM: "M * (M\<^sup>\<dagger>) = 1\<^sub>m r"
  shows "((transpose_mat M)\<^sup>\<dagger>) * transpose_mat M = 1\<^sub>m r"
proof (rule eq_matI)
  let ?T = "transpose_mat M"
  have Tc: "?T \<in> carrier_mat r r" using Mc by simp
  have Tdc: "?T\<^sup>\<dagger> \<in> carrier_mat r r" by (rule dagger_carrier[OF Tc])
  have Mdc: "M\<^sup>\<dagger> \<in> carrier_mat r r" by (rule dagger_carrier[OF Mc])
  fix j k assume "j < dim_row (1\<^sub>m r :: complex Matrix.mat)" "k < dim_col (1\<^sub>m r :: complex Matrix.mat)"
  hence j: "j < r" and k: "k < r" by simp_all
  have "((?T\<^sup>\<dagger>) * ?T) $$ (j,k) = (\<Sum>l<r. (?T\<^sup>\<dagger>) $$ (j,l) * ?T $$ (l,k))"
    by (rule mat_mult_entry[OF Tdc Tc j k])
  also have "\<dots> = (\<Sum>l<r. M $$ (k,l) * (M\<^sup>\<dagger>) $$ (l,j))"
    using j k carrier_matD[OF Mc] by (intro sum.cong refl) (simp add: dagger_def)
  also have "\<dots> = (M * (M\<^sup>\<dagger>)) $$ (k,j)" by (rule mat_mult_entry[OF Mc Mdc k j, symmetric])
  also have "\<dots> = (1\<^sub>m r :: complex Matrix.mat) $$ (k,j)" unfolding MM ..
  also have "\<dots> = (1\<^sub>m r :: complex Matrix.mat) $$ (j,k)" using j k by auto
  finally show "((?T\<^sup>\<dagger>) * ?T) $$ (j,k) = (1\<^sub>m r :: complex Matrix.mat) $$ (j,k)" .
qed (use Mc in \<open>auto simp: dagger_def\<close>)

lemma isometry_with_first_row:
  assumes ud: "dim_vec u = r" and un: "\<parallel>u\<parallel> = 1"
  shows "\<exists>U :: complex Matrix.mat. U \<in> carrier_mat r r \<and> (U\<^sup>\<dagger>) * U = 1\<^sub>m r \<and> (\<forall>j < r. U $$ (0,j) = u $ j)"
proof -
  obtain us where orth: "orthonormal_list r us" and len: "length us = r" and us0: "us ! 0 = u"
    using unit_vec_extends_to_onb[of u r] ud un by auto
  let ?M = "mat_of_cols r us"
  have Mc: "?M \<in> carrier_mat r r" using mat_of_cols_carrier[of r us] len by simp
  have Mu: "unitary ?M" by (rule orthonormal_mat_unitary[OF orth len])
  have MM: "?M * (?M\<^sup>\<dagger>) = 1\<^sub>m r" using Mu Mc by (simp add: unitary_def)
  have rpos: "0 < r" using ud un by (cases r) (auto simp: cpx_vec_length_def)
  have row0: "\<And>j. j < r \<Longrightarrow> transpose_mat ?M $$ (0,j) = u $ j"
    using rpos len us0 by (simp add: mat_of_cols_index)
  show ?thesis
    using Mc transpose_unitary_isometry[OF Mc MM] row0 by (intro exI[of _ "transpose_mat ?M"]) auto
qed

subsubsection \<open>D22-1\<close>

lemma kraus_map_dim_zero_head:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim d (0\<^sub>m d n # Ws) M = kraus_map_dim d Ws M"
  using kraus_map_dim_carrier[OF Ws_c Xc] Xc by simp

text \<open>If $\Phi(X)=\sum_{j<r}V_jXV_j^*$ with $r=\mathrm{cr}(\Phi)$, then $V_0,\dots,V_{r-1}$ are linearly
independent: a dependency $\sum_jc_jV_j=0$ would allow a unitary change of representation whose first
Kraus operator is $0$, giving a representation with $r-1$ terms.\<close>

theorem minimal_kraus_rep_lin_indep:
  assumes npos: "0 < n" and dpos: "0 < d"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and minimal: "choi_rank n d (kraus_map_dim d Vs) = length Vs"
  shows "lin_indep_complex_mat d n Vs"
proof (unfold lin_indep_complex_mat_def, intro conjI allI impI)
  show "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" by (rule Vs_c)
next
  fix c :: "nat \<Rightarrow> complex"
  let ?r = "length Vs"
  let ?\<Phi> = "kraus_map_dim d Vs"
  assume dep: "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (Vs ! k) + acc) [0..<?r] (0\<^sub>m d n) = 0\<^sub>m d n"
  fix k0 assume k0: "k0 < ?r"
  show "c k0 = 0"
  proof (rule ccontr)
    assume ck0: "c k0 \<noteq> 0"
    have rpos: "0 < ?r" using k0 by (cases Vs) auto
    define cv :: "complex Matrix.vec" where "cv = Matrix.vec ?r c"
    have cvd: "dim_vec cv = ?r" by (simp add: cv_def)
    have cvnz: "cv \<noteq> 0\<^sub>v ?r" using k0 ck0 by (auto simp: cv_def dest: arg_cong[where f = "\<lambda>v. v $ k0"])
    define N where "N = \<parallel>cv\<parallel>"
    have Nnz: "N \<noteq> 0" unfolding N_def using cpx_vec_length_zero_iff[of cv] cvnz cvd by simp
    have Nnn: "0 \<le> N" unfolding N_def cpx_vec_length_def by (simp add: sum_nonneg)
    have Npos: "0 < N" using Nnz Nnn by simp
    define u where "u = complex_of_real (1 / N) \<cdot>\<^sub>v cv"
    have ud: "dim_vec u = ?r" by (simp add: u_def cvd)
    have un: "\<parallel>u\<parallel> = 1" unfolding u_def cpx_vec_length_smult N_def[symmetric] using Npos by (simp add: norm_divide)
    obtain U :: "complex Matrix.mat" where Uc: "U \<in> carrier_mat ?r ?r" and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m ?r"
      and U0: "\<forall>j < ?r. U $$ (0,j) = u $ j"
      using isometry_with_first_row[OF ud un] by blast
    let ?Ws = "kraus_mix d n U Vs"
    have Ws_c: "\<forall>W \<in> set ?Ws. W \<in> carrier_mat d n" by (rule kraus_mix_carrier[OF Vs_c])
    have Ws_len: "length ?Ws = ?r" using Uc by simp
    have same: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> kraus_map_dim d ?Ws X = ?\<Phi> X"
      by (rule kraus_mix_same_map[OF npos dpos Vs_c Uc UU])
    \<comment> \<open>The first mixed operator vanishes.\<close>
    have W0: "?Ws ! 0 = 0\<^sub>m d n"
    proof -
      have fc: "\<forall>j \<in> set [0..<?r]. U $$ (0,j) \<cdot>\<^sub>m (Vs ! j) \<in> carrier_mat d n" using Vs_c by auto
      have "?Ws ! 0 = foldr (\<lambda>j acc. U $$ (0,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<?r] (0\<^sub>m d n)"
        using kraus_mix_nth[of 0 U d n Vs] Uc rpos by simp
      also have "\<dots> = foldr (\<lambda>j acc. complex_of_real (1 / N) \<cdot>\<^sub>m (c j \<cdot>\<^sub>m (Vs ! j)) + acc) [0..<?r] (0\<^sub>m d n)"
        by (rule foldr_add_mat_cong) (simp add: U0 u_def cv_def smult_smult_mat)
      also have "\<dots> = complex_of_real (1 / N) \<cdot>\<^sub>m foldr (\<lambda>j acc. c j \<cdot>\<^sub>m (Vs ! j) + acc) [0..<?r] (0\<^sub>m d n)"
      proof -
        have gen: "\<And>js. (\<forall>j \<in> set js. j < ?r) \<Longrightarrow>
            foldr (\<lambda>j acc. complex_of_real (1 / N) \<cdot>\<^sub>m (c j \<cdot>\<^sub>m (Vs ! j)) + acc) js (0\<^sub>m d n)
            = complex_of_real (1 / N) \<cdot>\<^sub>m foldr (\<lambda>j acc. c j \<cdot>\<^sub>m (Vs ! j) + acc) js (0\<^sub>m d n)"
        proof -
          fix js :: "nat list" assume "\<forall>j \<in> set js. j < ?r"
          thus "foldr (\<lambda>j acc. complex_of_real (1 / N) \<cdot>\<^sub>m (c j \<cdot>\<^sub>m (Vs ! j)) + acc) js (0\<^sub>m d n)
                = complex_of_real (1 / N) \<cdot>\<^sub>m foldr (\<lambda>j acc. c j \<cdot>\<^sub>m (Vs ! j) + acc) js (0\<^sub>m d n)"
          proof (induction js)
            case Nil show ?case by (intro eq_matI) auto
          next
            case (Cons j js)
            have jc: "c j \<cdot>\<^sub>m (Vs ! j) \<in> carrier_mat d n" using Cons.prems Vs_c by auto
            have rc: "foldr (\<lambda>j acc. c j \<cdot>\<^sub>m (Vs ! j) + acc) js (0\<^sub>m d n) \<in> carrier_mat d n"
              using Cons.prems Vs_c by (intro foldr_add_carrier_dn) auto
            show ?case using Cons jc rc by (simp add: add_smult_distrib_left_mat)
          qed
        qed
        show ?thesis by (rule gen) simp
      qed
      also have "\<dots> = 0\<^sub>m d n" unfolding dep by (intro eq_matI) auto
      finally show ?thesis .
    qed
    \<comment> \<open>Dropping it gives a representation with \<open>r - 1\<close> operators.\<close>
    obtain W0 Ws' where Ws_eq: "?Ws = W0 # Ws'" using Ws_len rpos by (cases ?Ws) auto
    have W0z: "W0 = 0\<^sub>m d n" using W0 Ws_eq by simp
    have Ws'_c: "\<forall>W \<in> set Ws'. W \<in> carrier_mat d n" using Ws_c Ws_eq by simp
    have Ws'_len: "length Ws' = ?r - 1" using Ws_len Ws_eq by simp
    have rep': "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> ?\<Phi> X = kraus_map_dim d Ws' X"
    proof (intro allI impI)
      fix X :: "complex Matrix.mat" assume Xc: "X \<in> carrier_mat n n"
      have "?\<Phi> X = kraus_map_dim d (W0 # Ws') X" using same[OF Xc] Ws_eq by simp
      also have "\<dots> = kraus_map_dim d Ws' X" unfolding W0z by (rule kraus_map_dim_zero_head[OF Ws'_c Xc])
      finally show "?\<Phi> X = kraus_map_dim d Ws' X" .
    qed
    have "choi_rank n d ?\<Phi> \<le> length Ws'"
      unfolding choi_rank_def using Ws'_c rep' by (intro cInf_lower) (auto intro: bdd_belowI[of _ 0])
    thus False using minimal Ws'_len rpos by (cases "length Vs") simp_all
  qed
qed

subsection \<open>Choi's rank theorem $\mathrm{cr}(\Phi)=\operatorname{rank}P_\Phi$ (D20-4)\<close>

text \<open>A linearly independent list of vectors in $\mathbb C^n$ has at most $n$ members.
The bridge is to JNF's @{locale vec_space}: kernel-triviality of \<open>mat_of_cols\<close> is
JNF's \<open>lin_indpt\<close> (via \<open>vec_space.lin_depE\<close>), and \<open>li_le_dim\<close> bounds the cardinality.\<close>

lemma lin_indep_vecs_distinct:
  assumes li: "lin_indep_vecs n vs"
  shows "distinct vs"
proof (rule ccontr)
  assume "\<not> distinct vs"
  then obtain i j where i: "i < length vs" and j: "j < length vs" and ij: "i \<noteq> j"
    and eq: "vs ! i = vs ! j" by (auto simp: distinct_conv_nth)
  have vsd: "\<forall>v \<in> set vs. dim_vec v = n" using li by (simp add: lin_indep_vecs_def)
  let ?m = "length vs"
  define x :: "complex Matrix.vec" where
    "x = Matrix.vec ?m (\<lambda>k. if k = i then 1 else if k = j then -1 else 0)"
  have xc: "x \<in> carrier_vec ?m" by (simp add: x_def)
  have xi: "x $ i = 1" using i ij by (simp add: x_def)
  have xnz: "x \<noteq> 0\<^sub>v ?m" using xi i by auto
  have "mat_of_cols n vs *\<^sub>v x = 0\<^sub>v n"
  proof (rule eq_vecI)
    fix r assume "r < dim_vec (0\<^sub>v n :: complex Matrix.vec)"
    hence r: "r < n" by simp
    have "(mat_of_cols n vs *\<^sub>v x) $ r = (\<Sum>k = 0..<?m. mat_of_cols n vs $$ (r,k) * x $ k)"
      using r carrier_vecD[OF xc] by (simp add: scalar_prod_def)
    also have "\<dots> = (\<Sum>k = 0..<?m. (if k = i then vs ! i $ r else 0) - (if k = j then vs ! j $ r else 0))"
      using r ij by (intro sum.cong refl) (simp add: x_def mat_of_cols_index)
    also have "\<dots> = vs ! i $ r - vs ! j $ r"
      using i j by (simp add: sum_subtractf)
    also have "\<dots> = 0" using eq by simp
    finally show "(mat_of_cols n vs *\<^sub>v x) $ r = (0\<^sub>v n :: complex Matrix.vec) $ r" using r by simp
  qed simp
  hence "x = 0\<^sub>v ?m" using li xc by (simp add: lin_indep_vecs_def)
  thus False using xnz by simp
qed

lemma lin_indep_vecs_length_le:
  assumes li: "lin_indep_vecs n vs"
  shows "length vs \<le> n"
proof -
  interpret V: vec_space "TYPE(complex)" n .
  have vsd: "\<forall>v \<in> set vs. dim_vec v = n" using li by (simp add: lin_indep_vecs_def)
  have vsc: "set vs \<subseteq> carrier_vec n" using vsd by auto
  have dist: "distinct vs" by (rule lin_indep_vecs_distinct[OF li])
  let ?A = "mat_of_cols n vs"
  have Ac: "?A \<in> carrier_mat n (length vs)" by simp
  have cols: "cols ?A = vs" using vsc by simp
  have indpt: "V.lin_indpt (set vs)"
  proof
    assume dep: "V.lin_dep (set vs)"
    obtain x where xc: "x \<in> carrier_vec (length vs)" and xnz: "x \<noteq> 0\<^sub>v (length vs)"
      and Ax: "?A *\<^sub>v x = 0\<^sub>v n"
      using V.lin_depE[OF Ac, of thesis] dep dist cols by auto
    have "x = 0\<^sub>v (length vs)" using li xc Ax by (simp add: lin_indep_vecs_def)
    thus False using xnz by simp
  qed
  have "card (set vs) \<le> V.dim"
    using V.li_le_dim(2)[OF V.fin_dim _ indpt] vsc by simp
  thus ?thesis using V.dim_is_n distinct_card[OF dist] by simp
qed

text \<open>Flattening a matrix into a vector carries linear independence of matrices to
\<open>lin_indep_vecs\<close>, so a linearly independent family in $M_n$ has at most $n^2$ members.\<close>

lemma lin_indep_mats_vecs:
  assumes li: "lin_indep_complex_mat n n Bs"
  shows "lin_indep_vecs (n*n) (map mat_to_vec Bs)"
proof (unfold lin_indep_vecs_def, intro conjI allI impI)
  show "\<forall>v \<in> set (map mat_to_vec Bs). dim_vec v = n*n"
    using li by (auto simp: lin_indep_complex_mat_def intro: dim_mat_to_vec)
next
  fix x :: "complex Matrix.vec"
  let ?m = "length (map mat_to_vec Bs)"
  let ?A = "mat_of_cols (n*n) (map mat_to_vec Bs)"
  assume xc: "x \<in> carrier_vec ?m" and Ax: "?A *\<^sub>v x = 0\<^sub>v (n*n)"
  have Bc: "\<forall>B \<in> set Bs. B \<in> carrier_mat n n" using li by (simp add: lin_indep_complex_mat_def)
  have len: "?m = length Bs" by simp
  let ?f = "\<lambda>k. x $ k \<cdot>\<^sub>m (Bs!k)"
  have fc: "\<forall>k \<in> set [0..<length Bs]. ?f k \<in> carrier_mat n n" using Bc by auto
  have comb0: "foldr (\<lambda>k acc. x $ k \<cdot>\<^sub>m (Bs!k) + acc) [0..<length Bs] (0\<^sub>m n n) = 0\<^sub>m n n"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (0\<^sub>m n n :: complex Matrix.mat)" "j < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
    hence i: "i < n" and j: "j < n" by simp_all
    have "foldr (\<lambda>k acc. ?f k + acc) [0..<length Bs] (0\<^sub>m n n) $$ (i,j)
            = sum_list (map (\<lambda>k. ?f k $$ (i,j)) [0..<length Bs])"
      by (rule foldr_add_mat_index[OF fc i j])
    also have "\<dots> = (\<Sum>k = 0..<length Bs. (x $ k \<cdot>\<^sub>m (Bs!k)) $$ (i,j))"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>k = 0..<length Bs. x $ k * Bs!k $$ (i,j))"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {0..<length Bs}"
      hence "Bs ! k \<in> carrier_mat n n" using Bc by (auto dest: nth_mem)
      thus "(x $ k \<cdot>\<^sub>m (Bs!k)) $$ (i,j) = x $ k * Bs!k $$ (i,j)" using i j by simp
    qed
    also have "\<dots> = (\<Sum>k = 0..<length Bs. ?A $$ (i*n + j, k) * x $ k)"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {0..<length Bs}"
      hence k: "k < length Bs" by simp
      have "?A $$ (i*n + j, k) = mat_to_vec (Bs ! k) $ (i*n + j)"
        using mult_index_lt[OF i j] k by (simp add: mat_of_cols_index)
      also have "\<dots> = Bs ! k $$ (i,j)" by (rule mat_to_vec_index[OF _ i j]) (use Bc k in auto)
      finally show "x $ k * Bs ! k $$ (i,j) = ?A $$ (i*n + j, k) * x $ k" by (simp add: mult.commute)
    qed
    also have "\<dots> = (?A *\<^sub>v x) $ (i*n + j)"
    proof -
      have lt: "i*n + j < n*n" using i j by (rule mult_index_lt)
      show ?thesis using lt xc by (simp add: scalar_prod_def)
    qed
    also have "\<dots> = 0" using Ax mult_index_lt[OF i j] by simp
    finally show "foldr (\<lambda>k acc. ?f k + acc) [0..<length Bs] (0\<^sub>m n n) $$ (i,j) = (0\<^sub>m n n :: complex Matrix.mat) $$ (i,j)"
      using i j by simp
  qed (use foldr_add_mat_carrier[OF fc] in auto)
  have "\<forall>k < length Bs. x $ k = 0" using li comb0 by (simp add: lin_indep_complex_mat_def)
  thus "x = 0\<^sub>v ?m" using xc by (intro eq_vecI) auto
qed

lemma lin_indep_mats_length_le:
  assumes "lin_indep_complex_mat n n Bs"
  shows "length Bs \<le> n*n"
  using lin_indep_vecs_length_le[OF lin_indep_mats_vecs[OF assms]] by simp

text \<open>Rank is JNF's \<open>vec_space.rank\<close>, the dimension of the column space.\<close>

abbreviation mat_rank :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat" where
  "mat_rank m A \<equiv> vec_space.rank m A"

subsubsection \<open>$\operatorname{rank}(\sum_{l<L}w_lw_l^*)\le L$\<close>

lemma rank_outer_prod_le_1:
  assumes vd: "dim_vec v = m"
  shows "mat_rank m (v \<oslash> v) \<le> 1"
proof -
  interpret V: vec_space "TYPE(complex)" m .
  have c: "v \<oslash> v \<in> carrier_mat m m" by (rule outer_prod_carrier[OF vd vd])
  show ?thesis
  proof (rule V.rank_le_1_product_entries[OF c, of "\<lambda>r. v $ r" "\<lambda>c. cnj (v $ c)"])
    fix r c assume "r < dim_row (v \<oslash> v)" "c < dim_col (v \<oslash> v)"
    hence r: "r < m" and cc: "c < m" using carrier_matD[OF c] by auto
    have "r < dim_vec v" and "c < dim_vec v" using r cc vd by simp_all
    thus "(v \<oslash> v) $$ (r, c) = v $ r * cnj (v $ c)" by (rule outer_prod_index)
  qed
qed

lemma rank_foldr_outer_le:
  assumes vsd: "\<forall>v \<in> set vs. dim_vec v = m"
  shows "mat_rank m (foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m m m)) \<le> length vs"
  using vsd
proof (induction vs)
  case Nil
  interpret V: vec_space "TYPE(complex)" m .
  show ?case using V.rank_0I by simp
next
  case (Cons v vs)
  interpret V: vec_space "TYPE(complex)" m .
  have vd: "dim_vec v = m" and rest: "\<forall>v \<in> set vs. dim_vec v = m" using Cons.prems by auto
  have rc: "foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m m m) \<in> carrier_mat m m"
    using rest by (induction vs) (auto simp: outer_prod_carrier)
  have "mat_rank m (v \<oslash> v + foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m m m))
        \<le> mat_rank m (v \<oslash> v) + mat_rank m (foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m m m))"
    by (rule V.rank_subadditive[OF outer_prod_carrier[OF vd vd] rc])
  also have "\<dots> \<le> 1 + length vs" using rank_outer_prod_le_1[OF vd] Cons.IH[OF rest] by simp
  finally show ?case by simp
qed

lemma rank_outer_sum_le:
  assumes vsd: "\<forall>v \<in> set vs. dim_vec v = m"
  shows "mat_rank m (outer_sum m vs) \<le> length vs"
  unfolding outer_sum_as_foldr[OF vsd] by (rule rank_foldr_outer_le[OF vsd])

subsubsection \<open>Independent vectors inside the column space bound the rank from below\<close>

lemma mult_mat_vec_in_span:
  assumes Ac: "A \<in> carrier_mat m k" and xc: "x \<in> carrier_vec k"
  shows "A *\<^sub>v x \<in> module.span class_ring (module_vec TYPE(complex) m) (set (cols A))"
proof -
  interpret V: vec_space "TYPE(complex)" m .
  have cd: "\<forall>w \<in> set (cols A). dim_vec w = m" using Ac by (auto simp: cols_def)
  have cc: "set (cols A) \<subseteq> carrier_vec m" using cd by auto
  have A_eq: "mat_of_cols m (cols A) = A" using mat_of_cols_cols[of A] Ac by simp
  have x_eq: "Matrix.vec (length (cols A)) (\<lambda>i. (x :: complex Matrix.vec) $ i) = x" using Ac xc by (intro eq_vecI) auto
  have "A *\<^sub>v x = V.lincomb_list (\<lambda>i. x $ i) (cols A)"
    unfolding V.lincomb_list_as_mat_mult[OF cd] A_eq x_eq ..
  also have "\<dots> \<in> V.span_list (cols A)" by (rule V.in_span_listI) auto
  also have "V.span_list (cols A) = V.span (set (cols A))" by (rule V.span_list_as_span[OF cc])
  finally show ?thesis .
qed

lemma rank_ge_indep_in_colspace:
  assumes Ac: "A \<in> carrier_mat m k" and li: "lin_indep_vecs m ws"
      and insp: "\<And>w. w \<in> set ws \<Longrightarrow> w \<in> module.span class_ring (module_vec TYPE(complex) m) (set (cols A))"
  shows "length ws \<le> mat_rank m A"
proof -
  interpret V: vec_space "TYPE(complex)" m .
  define SS where "SS = set (cols A)"
  have Sc: "SS \<subseteq> carrier_vec m" unfolding SS_def using Ac by (auto simp: cols_def)
  have finS: "finite SS" by (simp add: SS_def)
  have wsc: "set ws \<subseteq> carrier_vec m" using li by (auto simp: lin_indep_vecs_def)
  have dist: "distinct ws" by (rule lin_indep_vecs_distinct[OF li])
  \<comment> \<open>independence in \<open>V\<close>, as in \<open>lin_indep_vecs_length_le\<close>\<close>
  have indpt: "V.lin_indpt (set ws)"
  proof
    assume dep: "V.lin_dep (set ws)"
    have Wc: "mat_of_cols m ws \<in> carrier_mat m (length ws)" by simp
    have cols: "cols (mat_of_cols m ws) = ws" using wsc by simp
    obtain x where xc: "x \<in> carrier_vec (length ws)" and xnz: "x \<noteq> 0\<^sub>v (length ws)"
      and Ax: "mat_of_cols m ws *\<^sub>v x = 0\<^sub>v m"
      using V.lin_depE[OF Wc, of thesis] dep dist cols by auto
    have "x = 0\<^sub>v (length ws)" using li xc Ax by (simp add: lin_indep_vecs_def)
    thus False using xnz by simp
  qed
  \<comment> \<open>pass to the subspace \<open>span S\<close>\<close>
  have sub: "VectorSpace.subspace class_ring (V.span SS) V.V" by (rule V.span_is_subspace[OF Sc])
  interpret Sp: VectorSpace.vectorspace class_ring "V.vs (V.span SS)" by (rule V.subspace_is_vs[OF sub])
  have sub_md: "submodule class_ring (V.span SS) V.V" using sub by (simp add: VectorSpace.subspace_def)
  have wsS: "set ws \<subseteq> V.span SS" unfolding SS_def using insp by auto
  have indpt_S: "Sp.lin_indpt (set ws)"
    using V.span_li_not_depend(2)[OF wsS sub_md] indpt by simp
  have Sc': "SS \<subseteq> carrier V.V" using Sc by (simp add: module_vec_simps)
  have fd: "Sp.fin_dim" using V.fin_dim_span[OF finS Sc'] by simp
  have "card (set ws) \<le> Sp.dim" using Sp.li_le_dim(2)[OF fd _ indpt_S] wsS by simp
  thus ?thesis using distinct_card[OF dist] unfolding V.rank_def by (simp add: SS_def)
qed

subsubsection \<open>The theorem\<close>

lemma choi_rank_attained:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp:     "completely_positive n d \<Phi>"
      and npos:   "0 < n" and dpos: "0 < d"
  shows "\<exists>As :: complex Matrix.mat list. length As = choi_rank n d \<Phi> \<and>
           (\<forall>A \<in> set As. A \<in> carrier_mat d n) \<and>
           (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X)"
proof -
  let ?K = "{ length As | As :: complex Matrix.mat list.
             (\<forall>A \<in> set As. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X) }"
  have "?K \<noteq> {}" using kraus_rank_bound[OF linear smult range cp npos dpos] by blast
  hence "Inf ?K \<in> ?K" by (rule Inf_nat_def1)
  then obtain As :: "complex Matrix.mat list" where e: "Inf ?K = length As"
    and c: "\<forall>A \<in> set As. A \<in> carrier_mat d n" and eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X"
    unfolding mem_Collect_eq by blast
  show ?thesis unfolding choi_rank_def by (intro exI[of _ As] conjI, rule e[symmetric], rule c, rule eq)
qed

theorem choi_rank_eq_rank:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp:     "completely_positive n d \<Phi>"
      and npos:   "0 < n" and dpos: "0 < d"
  shows "choi_rank n d \<Phi> = mat_rank (n*d) (choi_matrix n d \<Phi>)"
proof -
  obtain As :: "complex Matrix.mat list" where len: "length As = choi_rank n d \<Phi>"
    and As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
    and rep: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X"
    using choi_rank_attained[OF assms] by blast
  let ?ws = "map (vec_of_kraus d n) As"
  have wsd: "\<forall>w \<in> set ?ws. dim_vec w = n*d" by simp
  have choi: "choi_matrix n d \<Phi> = outer_sum (n*d) ?ws"
    using choi_matrix_cong[of n \<Phi> "kraus_map_dim d As" d] rep choi_matrix_kraus_eq[OF As_c npos dpos] by simp
  \<comment> \<open>\<open>rank P\<^sub>\<Phi> \<le> cr \<Phi>\<close>\<close>
  have le1: "mat_rank (n*d) (choi_matrix n d \<Phi>) \<le> choi_rank n d \<Phi>"
    unfolding choi using rank_outer_sum_le[OF wsd] len by simp
  \<comment> \<open>\<open>cr \<Phi> \<le> rank P\<^sub>\<Phi>\<close>: the minimal representation is independent (D22-1), so its Kraus vectors are
      independent vectors in the column space of \<open>P\<^sub>\<Phi> = W W\<^sup>\<dagger>\<close>.\<close>
  have minimal: "choi_rank n d (kraus_map_dim d As) = length As"
  proof -
    have "\<And>Bs :: complex Matrix.mat list.
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim d As X = kraus_map_dim d Bs X)
            \<longleftrightarrow> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Bs X)"
      using rep by simp
    hence "{length Bs | Bs :: complex Matrix.mat list. (\<forall>A \<in> set Bs. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim d As X = kraus_map_dim d Bs X)}
           = {length Bs | Bs :: complex Matrix.mat list. (\<forall>A \<in> set Bs. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Bs X)}" by simp
    thus ?thesis unfolding choi_rank_def using len unfolding choi_rank_def by simp
  qed
  have liA: "lin_indep_complex_mat d n As" by (rule minimal_kraus_rep_lin_indep[OF npos dpos As_c minimal])
  have liw: "lin_indep_vecs (n*d) ?ws" by (rule lin_indep_complex_mat_vec_of_kraus[OF liA dpos])
  let ?W = "mat_of_cols (n*d) ?ws"
  have Wc: "?W \<in> carrier_mat (n*d) (length As)" using mat_of_cols_carrier[of "n*d" ?ws] by simp
  have Wdc: "?W\<^sup>\<dagger> \<in> carrier_mat (length As) (n*d)" using dagger_carrier[OF Wc] .
  have Pc: "choi_matrix n d \<Phi> \<in> carrier_mat (n*d) (n*d)" unfolding choi outer_sum_def using Wc Wdc by auto
  obtain B where Bc: "B \<in> carrier_mat (length As) (length As)"
    and GB: "((?W\<^sup>\<dagger>) * ?W) * B = 1\<^sub>m (length As)" using gram_inverse[OF liw] by auto
  have insp: "\<And>w. w \<in> set ?ws \<Longrightarrow> w \<in> module.span class_ring (module_vec TYPE(complex) (n*d)) (set (cols (choi_matrix n d \<Phi>)))"
  proof -
    fix w assume "w \<in> set ?ws"
    then obtain l where l: "l < length As" and wl: "w = ?ws ! l" by (auto simp: in_set_conv_nth)
    have wc: "w \<in> carrier_vec (n*d)" unfolding wl using l by (intro carrier_vecI) simp
    \<comment> \<open>\<open>w = col W l = (W W\<^sup>\<dagger>) (W B e\<^sub>l)\<close>\<close>
    let ?x = "?W *\<^sub>v (B *\<^sub>v unit_vec (length As) l)"
    have xc: "?x \<in> carrier_vec (n*d)" using Wc Bc by simp
    let ?e = "unit_vec (length As) l"
    have ec: "?e \<in> carrier_vec (length As)" by simp
    have Bec: "B *\<^sub>v ?e \<in> carrier_vec (length As)" using Bc by simp
    have "choi_matrix n d \<Phi> *\<^sub>v ?x = (?W * (?W\<^sup>\<dagger>)) *\<^sub>v (?W *\<^sub>v (B *\<^sub>v ?e))" unfolding choi outer_sum_def ..
    also have "\<dots> = ((?W * (?W\<^sup>\<dagger>)) * ?W) *\<^sub>v (B *\<^sub>v ?e)"
      by (rule assoc_mult_mat_vec[OF mult_carrier_mat[OF Wc Wdc] Wc Bec, symmetric])
    also have "\<dots> = (((?W * (?W\<^sup>\<dagger>)) * ?W) * B) *\<^sub>v ?e"
      by (rule assoc_mult_mat_vec[OF mult_carrier_mat[OF mult_carrier_mat[OF Wc Wdc] Wc] Bc ec, symmetric])
    also have "((?W * (?W\<^sup>\<dagger>)) * ?W) * B = ?W * ((?W\<^sup>\<dagger>) * ?W * B)"
      by (simp only: assoc_mult_mat[OF Wc Wdc Wc] assoc_mult_mat[OF Wc mult_carrier_mat[OF Wdc Wc] Bc])
    also have "?W * ((?W\<^sup>\<dagger>) * ?W * B) = ?W" by (simp only: GB right_mult_one_mat[OF Wc])
    also have "?W *\<^sub>v ?e = Matrix.col ?W l"
    proof (rule eq_vecI)
      fix i assume "i < dim_vec (Matrix.col ?W l)"
      hence i: "i < n*d" using carrier_matD[OF Wc] by simp
      have "(?W *\<^sub>v ?e) $ i = (\<Sum>j<length As. ?W $$ (i,j) * ?e $ j)"
        using i carrier_matD[OF Wc] by (simp add: scalar_prod_def atLeast0LessThan)
      also have "\<dots> = (\<Sum>j<length As. if j = l then ?W $$ (i,j) else 0)"
        by (intro sum.cong refl) (simp add: unit_vec_def)
      also have "\<dots> = ?W $$ (i,l)" by (simp only: sum.delta[OF finite_lessThan]) (simp add: l)
      also have "\<dots> = Matrix.col ?W l $ i" using i carrier_matD[OF Wc] by (simp add: Matrix.col_def)
      finally show "(?W *\<^sub>v ?e) $ i = Matrix.col ?W l $ i" .
    qed (simp add: carrier_matD[OF Wc])
    also have "Matrix.col ?W l = ?ws ! l" using l wc[unfolded wl] by (intro col_mat_of_cols) simp_all
    finally have "choi_matrix n d \<Phi> *\<^sub>v ?x = w" unfolding wl .
    thus "w \<in> module.span class_ring (module_vec TYPE(complex) (n*d)) (set (cols (choi_matrix n d \<Phi>)))"
      using mult_mat_vec_in_span[OF Pc xc] by simp
  qed
  have ge1: "choi_rank n d \<Phi> \<le> mat_rank (n*d) (choi_matrix n d \<Phi>)"
    using rank_ge_indep_in_colspace[OF Pc liw insp] len by simp
  show ?thesis using le1 ge1 by simp
qed

subsection \<open>The adjoint map, an affine bijection from UCP onto CPTP (D22-5)\<close>

text \<open>The notes: $\mathrm{UCP}(M_n,M_d)$ and $\mathrm{CPTP}(M_d,M_n)$ are convex, and
$\Gamma(\Phi)=\Phi^*$ is an affine bijection between them with affine inverse, so the two
convex sets are affinely isomorphic.  The adjoint was available only for Kraus maps
(\<^const>\<open>kraus_adjoint_dim\<close>); here it is defined for every linear $\Phi$.  Maps are total
functions on matrices, so $\Gamma$ is a bijection up to agreement on $M_n$, resp.\ $M_d$:
$\Gamma$ sends linear UCP maps to linear CPTP maps and back, and $\Gamma(\Gamma(\Phi))=\Phi$ on
$M_n$.  The set \<^const>\<open>UCP\<close> does not record linearity, which the notes' maps have, so it is
assumed.\<close>

text \<open>For linear $\Phi:M_n\to M_d$, $\Phi^*:M_d\to M_n$ is determined by
$\langle Y|\Phi(X)\rangle=\langle\Phi^*(Y)|X\rangle$; taking $X=E_{ij}$ gives
$\Phi^*(Y)_{ij}=\langle\Phi(E_{ij})|Y\rangle$.\<close>

definition map_adjoint :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "map_adjoint n d \<Phi> Y = Matrix.mat n n (\<lambda>(i, j). \<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>)"

text \<open>$\Phi^*:M_d\to M_n$ is determined by $\langle\Phi^*(Y)|X\rangle=\langle Y|\Phi(X)\rangle$.  Since
$\Phi(X)=\sum_{i,j}x_{ij}\Phi(E_{ij})$ for linear $\Phi$, it suffices that
\[ \Phi^*(Y)_{ij}=\langle\Phi(E_{ij})|Y\rangle, \]
which is the definition.\<close>

lemma map_adjoint_carrier [simp]: "map_adjoint n d \<Phi> Y \<in> carrier_mat n n"
  by (simp add: map_adjoint_def)

lemma map_adjoint_dims [simp]: "dim_row (map_adjoint n d \<Phi> Y) = n" "dim_col (map_adjoint n d \<Phi> Y) = n"
  by (simp_all add: map_adjoint_def)

lemma lin_entry:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and X: "X \<in> carrier_mat n n" and a: "a < d" and b: "b < d"
  shows "\<Phi> X $$ (a, b) = (\<Sum>i<n. \<Sum>j<n. X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b))"
proof -
  have Ec: "\<And>i j. \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d" using L unfolding lin_on_def by simp
  have "\<Phi> X $$ (a, b) = msum d d (\<lambda>(i,j). X $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) (List.product [0..<n] [0..<n]) $$ (a, b)"
    by (simp add: lin_expansion[OF L X])
  also have "\<dots> = (\<Sum>x\<leftarrow>List.product [0..<n] [0..<n]. ((\<lambda>(i,j). X $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) x) $$ (a, b))"
    by (rule msum_index) (use Ec a b in auto)
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b))"
    unfolding sum_list_product_upt using Ec a b carrier_matD[OF Ec] by simp
  finally show ?thesis .
qed

theorem map_adjoint_correct:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and X: "X \<in> carrier_mat n n" and Y: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> Y | \<Phi> X \<rangle>\<rangle> = \<langle>\<langle> map_adjoint n d \<Phi> Y | X \<rangle>\<rangle>"
proof -
  have Ec: "\<And>i j. \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d" using L unfolding lin_on_def by simp
  have PX: "\<Phi> X \<in> carrier_mat d d" using L X unfolding lin_on_def by simp
  have "\<langle>\<langle> Y | \<Phi> X \<rangle>\<rangle> = (\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * \<Phi> X $$ (a, b))"
    using PX by (simp add: hs_inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>a<d. \<Sum>b<d. \<Sum>i<n. \<Sum>j<n. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (simp add: lin_entry[OF L X] sum_distrib_left)
  also have "\<dots> = (\<Sum>a<d. \<Sum>i<n. \<Sum>b<d. \<Sum>j<n. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. \<Sum>a<d. \<Sum>b<d. \<Sum>j<n. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. \<Sum>a<d. \<Sum>j<n. \<Sum>b<d. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (rule sum.cong[OF refl], rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. \<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. cnj (\<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>) * X $$ (i, j))"
  proof (intro sum.cong refl)
    fix i j
    have "cnj (\<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>) = \<langle>\<langle> Y | \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<rangle>\<rangle>"
      using hs_inner_prod_cnj[of Y "\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)"] carrier_matD[OF Y] carrier_matD[OF Ec[of i j]] by simp
    also have "\<dots> = (\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b))"
      using carrier_matD[OF Ec[of i j]] by (simp add: hs_inner_prod_def atLeast0LessThan)
    finally have c: "cnj (\<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>) = (\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b))" .
    have "(\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))
          = (\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)) * X $$ (i, j)"
      by (simp add: sum_distrib_left sum_distrib_right mult_ac)
    thus "(\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))
                  = cnj (\<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>) * X $$ (i, j)" unfolding c .
  qed
  also have "\<dots> = \<langle>\<langle> map_adjoint n d \<Phi> Y | X \<rangle>\<rangle>"
    using X by (simp add: hs_inner_prod_def map_adjoint_def atLeast0LessThan)
  finally show ?thesis .
qed

lemma hs_inner_prod_mat_unit:
  assumes A: "A \<in> carrier_mat n n" and i: "i < n" and j: "j < n"
  shows "\<langle>\<langle> A | E\<lbrakk>i,j ; n,n\<rbrakk> \<rangle>\<rangle> = cnj (A $$ (i, j))"
proof -
  have "\<langle>\<langle> A | E\<lbrakk>i,j ; n,n\<rbrakk> \<rangle>\<rangle> = (\<Sum>a<n. \<Sum>b<n. cnj (A $$ (a, b)) * (if a = i \<and> b = j then 1 else 0))"
    by (simp add: hs_inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>a<n. if a = i then cnj (A $$ (a, j)) else 0)"
    by (rule sum.cong[OF refl]) (use j in \<open>auto simp: if_distrib cong: if_cong\<close>)
  also have "\<dots> = cnj (A $$ (i, j))" using i by simp
  finally show ?thesis .
qed

lemma hs_inner_prod_ext:
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
      and eq: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<langle>\<langle> A | X \<rangle>\<rangle> = \<langle>\<langle> B | X \<rangle>\<rangle>"
  shows "A = B"
proof (rule eq_matI)
  fix i j assume "i < dim_row B" "j < dim_col B"
  hence i: "i < n" and j: "j < n" using B by auto
  have "cnj (A $$ (i, j)) = cnj (B $$ (i, j))"
    using eq[of "E\<lbrakk>i,j ; n,n\<rbrakk>"] hs_inner_prod_mat_unit[OF A i j] hs_inner_prod_mat_unit[OF B i j] by simp
  thus "A $$ (i, j) = B $$ (i, j)" by simp
qed (use A B in auto)

lemma map_adjoint_lin: "lin_on d n (carrier_mat d d) (map_adjoint n d \<Phi>)"
  unfolding lin_on_def
proof (intro conjI ballI allI)
  fix A B :: "complex Matrix.mat" assume A: "A \<in> carrier_mat d d" and B: "B \<in> carrier_mat d d"
  show "map_adjoint n d \<Phi> (A + B) = map_adjoint n d \<Phi> A + map_adjoint n d \<Phi> B"
    by (rule eq_matI) (use A B in \<open>auto simp: map_adjoint_def hs_inner_prod_def sum.distrib distrib_left\<close>)
next
  fix A :: "complex Matrix.mat" and c :: complex assume A: "A \<in> carrier_mat d d"
  show "map_adjoint n d \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m map_adjoint n d \<Phi> A"
    by (rule eq_matI) (use A in \<open>auto simp: map_adjoint_def hs_inner_prod_def sum_distrib_left mult_ac\<close>)
qed simp

lemma map_adjoint_cong:
  assumes "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = \<Psi> X"
  shows "map_adjoint n d \<Phi> = map_adjoint n d \<Psi>"
  unfolding map_adjoint_def using assms by (intro ext) (simp add: mat_unit_def)

text \<open>For a Kraus map the adjoint is \<^const>\<open>kraus_adjoint_dim\<close>.\<close>

lemma map_adjoint_kraus:
  assumes As: "\<forall>A \<in> set As. A \<in> carrier_mat d n" and Y: "Y \<in> carrier_mat d d"
  shows "map_adjoint n d (kraus_map_dim d As) Y = kraus_adjoint_dim n As Y"
proof (rule hs_inner_prod_ext[OF map_adjoint_carrier kraus_adjoint_dim_carrier[OF As Y]])
  fix X :: "complex Matrix.mat" assume X: "X \<in> carrier_mat n n"
  have L: "lin_on n d (carrier_mat n n) (kraus_map_dim d As)" by (rule kraus_lin_on[OF As])
  show "\<langle>\<langle> map_adjoint n d (kraus_map_dim d As) Y | X \<rangle>\<rangle> = \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using map_adjoint_correct[OF L X Y] kraus_adjoint_correct[OF As X Y] by simp
qed

text \<open>$\Phi^{**}=\Phi$.\<close>

theorem map_adjoint_adjoint:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and X: "X \<in> carrier_mat n n"
  shows "map_adjoint d n (map_adjoint n d \<Phi>) X = \<Phi> X"
proof -
  have PX: "\<Phi> X \<in> carrier_mat d d" using L X unfolding lin_on_def by simp
  have "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> \<langle>\<langle> map_adjoint d n (map_adjoint n d \<Phi>) X | Y \<rangle>\<rangle> = \<langle>\<langle> \<Phi> X | Y \<rangle>\<rangle>"
  proof -
    fix Y :: "complex Matrix.mat" assume Y: "Y \<in> carrier_mat d d"
    have Ac: "map_adjoint d n (map_adjoint n d \<Phi>) X \<in> carrier_mat d d" by simp
    have "\<langle>\<langle> map_adjoint d n (map_adjoint n d \<Phi>) X | Y \<rangle>\<rangle> = \<langle>\<langle> X | map_adjoint n d \<Phi> Y \<rangle>\<rangle>"
      using map_adjoint_correct[OF map_adjoint_lin Y X] by simp
    also have "\<dots> = cnj \<langle>\<langle> map_adjoint n d \<Phi> Y | X \<rangle>\<rangle>"
      using hs_inner_prod_cnj[of X "map_adjoint n d \<Phi> Y"] carrier_matD[OF X] by simp
    also have "\<dots> = cnj \<langle>\<langle> Y | \<Phi> X \<rangle>\<rangle>" using map_adjoint_correct[OF L X Y] by simp
    also have "\<dots> = \<langle>\<langle> \<Phi> X | Y \<rangle>\<rangle>"
      using hs_inner_prod_cnj[of "\<Phi> X" Y] carrier_matD[OF PX] carrier_matD[OF Y] by simp
    finally show "\<langle>\<langle> map_adjoint d n (map_adjoint n d \<Phi>) X | Y \<rangle>\<rangle> = \<langle>\<langle> \<Phi> X | Y \<rangle>\<rangle>" .
  qed
  moreover have "\<And>A B. A \<in> carrier_mat d d \<Longrightarrow> B \<in> carrier_mat d d \<Longrightarrow> (\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> \<langle>\<langle> A | Y \<rangle>\<rangle> = \<langle>\<langle> B | Y \<rangle>\<rangle>) \<Longrightarrow> A = B"
    by (rule hs_inner_prod_ext)
  ultimately show ?thesis using PX by force
qed

lemma cp_kraus_form:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and cp: "completely_positive n d \<Phi>" and n: "0 < n" and d: "0 < d"
  shows "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
  using choi_four_conditions[OF lin_on_choi_hyps[OF L] n d] cp by blast

lemma trace_preserving_cong:
  assumes "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = \<Psi> X"
  shows "trace_preserving n \<Phi> \<longleftrightarrow> trace_preserving n \<Psi>"
  using assms unfolding trace_preserving_def by auto

text \<open>$\Gamma(\Phi)=\Phi^*$ maps the unital CP maps $M_n\to M_d$ to the CPTP maps $M_d\to M_n$ and
back.\<close>

theorem adjoint_ucp_imp_cptp:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and U: "\<Phi> \<in> UCP n d" and n: "0 < n" and d: "0 < d"
  shows "map_adjoint n d \<Phi> \<in> CPTP d n"
proof -
  have cp: "completely_positive n d \<Phi>" and un: "\<Phi> (1\<^sub>m n) = 1\<^sub>m d" using U by (auto simp: UCP_def unital_map_def)
  obtain Ws where Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and W: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Ws X"
    using cp_kraus_form[OF L cp n d] by blast
  have eq: "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> map_adjoint n d \<Phi> Y = kraus_adjoint_dim n Ws Y"
    using map_adjoint_cong[of n \<Phi> "kraus_map_dim d Ws" d] W map_adjoint_kraus[OF Wc] by simp
  have "completely_positive d n (kraus_adjoint_dim n Ws)" by (rule adjoint_cp_from_kraus[OF Wc n d])
  hence "completely_positive d n (map_adjoint n d \<Phi>)" using completely_positive_cong[of d "map_adjoint n d \<Phi>" "kraus_adjoint_dim n Ws" n] eq by blast
  moreover have "unital_map n d (kraus_map_dim d Ws)" using un W[of "1\<^sub>m n"] by (simp add: unital_map_def)
  hence "trace_preserving d (kraus_adjoint_dim n Ws)" using cp_unital_iff_adjoint_tp[OF Wc n d] by simp
  hence "trace_preserving d (map_adjoint n d \<Phi>)" using trace_preserving_cong[of d "map_adjoint n d \<Phi>" "kraus_adjoint_dim n Ws"] eq by blast
  ultimately show ?thesis by (simp add: CPTP_def)
qed

theorem adjoint_cptp_imp_ucp:
  assumes L: "lin_on d n (carrier_mat d d) \<Psi>" and C: "\<Psi> \<in> CPTP d n" and n: "0 < n" and d: "0 < d"
  shows "map_adjoint d n \<Psi> \<in> UCP n d"
proof -
  have cp: "completely_positive d n \<Psi>" and tp: "trace_preserving d \<Psi>" using C by (auto simp: CPTP_def)
  obtain Bs where Bc: "\<forall>B \<in> set Bs. B \<in> carrier_mat n d" and B: "\<And>X. X \<in> carrier_mat d d \<Longrightarrow> \<Psi> X = kraus_map_dim n Bs X"
    using cp_kraus_form[OF L cp d n] by blast
  define As where "As = map (\<lambda>B. B\<^sup>\<dagger>) Bs"
  have Ac: "\<forall>A \<in> set As. A \<in> carrier_mat d n" using Bc by (auto simp: As_def intro: dagger_carrier)
  have BsAs: "map (\<lambda>A. A\<^sup>\<dagger>) As = Bs" by (simp add: As_def comp_def dagger_of_dagger_is_id)
  have eq: "\<And>Y. Y \<in> carrier_mat n n \<Longrightarrow> map_adjoint d n \<Psi> Y = kraus_map_dim d As Y"
  proof -
    fix Y :: "complex Matrix.mat" assume Y: "Y \<in> carrier_mat n n"
    have "map_adjoint d n \<Psi> Y = kraus_adjoint_dim d Bs Y"
      using map_adjoint_cong[of d \<Psi> "kraus_map_dim n Bs" n] B map_adjoint_kraus[OF Bc Y] by simp
    also have "\<dots> = kraus_map_dim d As Y" unfolding As_def by (rule kraus_adjoint_dim_as_kraus_map_dim[OF Bc Y])
    finally show "map_adjoint d n \<Psi> Y = kraus_map_dim d As Y" .
  qed
  have "completely_positive n d (kraus_map_dim d As)" by (rule kraus_cp_no_tp[OF Ac n d])
  hence "completely_positive n d (map_adjoint d n \<Psi>)" using completely_positive_cong[of n "map_adjoint d n \<Psi>" "kraus_map_dim d As" d] eq by blast
  moreover have "\<And>X. X \<in> carrier_mat d d \<Longrightarrow> kraus_adjoint_dim n As X = \<Psi> X"
    using kraus_adjoint_dim_as_kraus_map_dim[OF Ac] B unfolding BsAs by simp
  hence "trace_preserving d (kraus_adjoint_dim n As)" using tp trace_preserving_cong[of d "kraus_adjoint_dim n As" \<Psi>] by blast
  hence "unital_map n d (kraus_map_dim d As)" using cp_unital_iff_adjoint_tp[OF Ac n d] by simp
  hence "unital_map n d (map_adjoint d n \<Psi>)" using eq[of "1\<^sub>m n"] by (simp add: unital_map_def)
  ultimately show ?thesis by (simp add: UCP_def)
qed

text \<open>$\Gamma$ is affine (for real weights), and $\Gamma^{-1}=\Gamma$ by
@{thm [source] map_adjoint_adjoint}.\<close>

lemma hs_inner_prod_left_real_comb:
  fixes t s :: real
  assumes A: "A \<in> carrier_mat d d" and B: "B \<in> carrier_mat d d" and Y: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> complex_of_real t \<cdot>\<^sub>m A + complex_of_real s \<cdot>\<^sub>m B | Y \<rangle>\<rangle>
         = complex_of_real t * \<langle>\<langle> A | Y \<rangle>\<rangle> + complex_of_real s * \<langle>\<langle> B | Y \<rangle>\<rangle>"
proof -
  have "\<langle>\<langle> complex_of_real t \<cdot>\<^sub>m A + complex_of_real s \<cdot>\<^sub>m B | Y \<rangle>\<rangle>
        = (\<Sum>i<d. \<Sum>j<d. complex_of_real t * (cnj (A $$ (i, j)) * Y $$ (i, j)) + complex_of_real s * (cnj (B $$ (i, j)) * Y $$ (i, j)))"
  proof -
    have e: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> cnj ((complex_of_real t \<cdot>\<^sub>m A + complex_of_real s \<cdot>\<^sub>m B) $$ (i, j)) * Y $$ (i, j)
        = complex_of_real t * (cnj (A $$ (i, j)) * Y $$ (i, j)) + complex_of_real s * (cnj (B $$ (i, j)) * Y $$ (i, j))"
      using A B by (simp add: algebra_simps)
    show ?thesis unfolding hs_inner_prod_def carrier_matD(1,2)[OF Y] atLeast0LessThan
      by (intro sum.cong refl) (simp add: e)
  qed
  also have "\<dots> = complex_of_real t * \<langle>\<langle> A | Y \<rangle>\<rangle> + complex_of_real s * \<langle>\<langle> B | Y \<rangle>\<rangle>"
    using carrier_matD[OF Y] by (simp add: hs_inner_prod_def atLeast0LessThan sum.distrib sum_distrib_left)
  finally show ?thesis .
qed

theorem map_adjoint_affine:
  fixes t :: real
  assumes L1: "lin_on n d (carrier_mat n n) \<Phi>1" and L2: "lin_on n d (carrier_mat n n) \<Phi>2" and Y: "Y \<in> carrier_mat d d"
  shows "map_adjoint n d (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + complex_of_real (1 - t) \<cdot>\<^sub>m \<Phi>2 X) Y
         = complex_of_real t \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + complex_of_real (1 - t) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y"
proof (rule eq_matI)
  fix i j assume "i < dim_row (complex_of_real t \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + complex_of_real (1 - t) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y)"
    "j < dim_col (complex_of_real t \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + complex_of_real (1 - t) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y)"
  hence i: "i < n" and j: "j < n" by simp_all
  have c1: "\<Phi>1 (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d" and c2: "\<Phi>2 (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d"
    using L1 L2 unfolding lin_on_def by simp_all
  show "map_adjoint n d (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + complex_of_real (1 - t) \<cdot>\<^sub>m \<Phi>2 X) Y $$ (i, j)
        = (complex_of_real t \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + complex_of_real (1 - t) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y) $$ (i, j)"
    using i j hs_inner_prod_left_real_comb[OF c1 c2 Y, of t "1 - t"] by (simp add: map_adjoint_def)
qed simp_all

end
