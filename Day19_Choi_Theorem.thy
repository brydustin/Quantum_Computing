(*  Title:   Day19_Choi_Theorem.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 10 October 2011 (Day 19)
*)

theory Day19_Choi_Theorem
  imports Day18_CP_Maps
begin

section \<open>Day 19 (10 October 2011): Choi's theorem\<close>

text \<open>\begin{notestheorem}[Choi, 1975]
For linear $\Phi:M_n\to M_d$ the following are equivalent: (1) $\Phi$ is completely positive;
(2) $\Phi$ is $n$-positive; (3) $P_\Phi=(\Phi(E_{ij}))_{i,j}\ge0$ in $M_n(M_d)$; (4) there are
$d\times n$ matrices $B_1,\dots,B_K$ with $\Phi(X)=\sum_kB_kXB_k^*$.
\end{notestheorem}
Notes: (1) $\sum_kB_kXB_k^*$ is a \emph{Choi--Kraus representation}; (2) $P_\Phi$ is the
\emph{Choi--Jamio{\l}kowski matrix}; (3) $CP(M_n,M_d)\leftrightarrow M_n(M_d)^+$ via
$\Phi\leftrightarrow P_\Phi$; (4) $\Phi$ is trace preserving iff $\tr(\Phi(E_{ij}))=\delta_{ij}$;
(5) $\Phi$ is unital iff $\sum_i\Phi(E_{ii})=I_d$.

Formally $P_\Phi$ is \<open>choi_matrix n d \<Phi>\<close> (an $nd\times nd$ matrix built from the
blocks $\Phi(E_{ij})$); \<open>choi_theorem\<close> is (1)$\Leftrightarrow$(3),
\<open>kraus_rep_of_psd_choi\<close> is (3)$\Rightarrow$(4), and \<open>kraus_is_cp\<close> is (4)$\Rightarrow$(1).
The step (2)$\Rightarrow$(3) is the observation that $P_\Phi=\Phi^{(n)}((E_{ij}))$ with
$(E_{ij})\ge0$ (\<open>choi_matrix_as_amplification\<close>).  Linearity of $\Phi$ is assumed on the
carrier $M_n$ (additivity and homogeneity hypotheses).  The trace-preserving case is
\<open>choi_kraus_cptp\<close>; notes (4) and (5) in Choi-matrix form are \<open>choi_trace_preserving_iff\<close>
and \<open>choi_unital_iff\<close> in theory Day19\_Choi\_TP\_Unital.\<close>

definition choi_matrix :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "choi_matrix n d \<Phi> \<equiv>
     Matrix.mat (n*d) (n*d)
       (\<lambda>(r,c). \<Phi> (mat_unit (r div d) (c div d) n n) $$ (r mod d, c mod d))"

notation choi_matrix ("P\<^sub>\<Phi>")

definition choi_seed :: "nat \<Rightarrow> complex Matrix.mat" where
  "choi_seed n \<equiv>
     Matrix.mat (n*n) (n*n)
       (\<lambda>(r,c). mat_unit (r div n) (c div n) n n $$ (r mod n, c mod n))"

lemma choi_seed_carrier [simp]:
  "choi_seed n \<in> carrier_mat (n*n) (n*n)"
  by (simp add: choi_seed_def)

text \<open>The seed $\sum_{a,b}E_{ab}\otimes E_{ab}\in M_n(M_n)$ has the matrix unit $E_{ab}$ as its $(a,b)$
block, so the Choi matrix is the amplification of $\Phi$ applied to it:
\[ P_\Phi=\bigl(\Phi(E_{ab})\bigr)_{a,b}=\Phi^{(n)}\Bigl(\sum_{a,b}E_{ab}\otimes E_{ab}\Bigr). \]
The seed is $\ketbra\xi\xi$ with $\xi=\sum_ae_a\otimes e_a$, hence positive; so $P_\Phi\ge0$ when
$\Phi$ is completely positive.\<close>

lemma choi_seed_block:
  assumes npos: "n > 0"
      and a: "a < n"
      and b: "b < n"
  shows "block_of_mat n (choi_seed n) a b = mat_unit a b n n"
proof (rule eq_matI)
  show "dim_row (block_of_mat n (choi_seed n) a b) = dim_row (mat_unit a b n n)"
    by (simp add: block_of_mat_def)
  show "dim_col (block_of_mat n (choi_seed n) a b) = dim_col (mat_unit a b n n)"
    by (simp add: block_of_mat_def)
next
  fix r c
  assume r: "r < dim_row (mat_unit a b n n)"
     and c: "c < dim_col (mat_unit a b n n)"
  then have rn: "r < n" and cn: "c < n" by simp_all
  have row_lt: "a * n + r < n * n"
  proof -
    have "a * n + r < a * n + n"
      using rn by simp
    also have "\<dots> = Suc a * n"
      by simp
    also have "\<dots> \<le> n * n"
    proof -
      have "Suc a \<le> n"
        using a by simp
      thus "Suc a * n \<le> n * n"
        by (metis mult.commute mult_le_mono2)
    qed
    finally show ?thesis .
  qed
  have col_lt: "b * n + c < n * n"
  proof -
    have "b * n + c < b * n + n"
      using cn by simp
    also have "\<dots> = Suc b * n"
      by simp
    also have "\<dots> \<le> n * n"
    proof -
      have "Suc b \<le> n"
        using b by simp
      thus "Suc b * n \<le> n * n"
        by (metis mult.commute mult_le_mono2)
    qed
    finally show ?thesis .
  qed
  have div_row: "(a*n + r) div n = a"
    using npos rn by simp
  have div_col: "(b*n + c) div n = b"
    using npos cn by simp
  have mod_row: "(a*n + r) mod n = r"
    using npos rn by simp
  have mod_col: "(b*n + c) mod n = c"
    using npos cn by simp
  have "block_of_mat n (choi_seed n) a b $$ (r,c)
      = choi_seed n $$ (a*n + r, b*n + c)"
    using rn cn by (simp add: block_of_mat_def)
  also have "\<dots> =
      mat_unit ((a*n + r) div n) ((b*n + c) div n) n n $$
        ((a*n + r) mod n, (b*n + c) mod n)"
    using row_lt col_lt by (simp add: choi_seed_def)
  also have "\<dots> = mat_unit a b n n $$ (r,c)"
    using div_row div_col mod_row mod_col by simp
  finally show "block_of_mat n (choi_seed n) a b $$ (r,c) = mat_unit a b n n $$ (r,c)".
qed

lemma choi_matrix_as_amplification:
  assumes npos: "n > 0"
      and dpos: "d > 0"
  shows "choi_matrix n d \<Phi> = amplification n d n \<Phi> (choi_seed n)"
proof (rule eq_matI)
  show "dim_row (choi_matrix n d \<Phi>) = dim_row (amplification n d n \<Phi> (choi_seed n))"
    by (simp add: choi_matrix_def amplification_def)
  show "dim_col (choi_matrix n d \<Phi>) = dim_col (amplification n d n \<Phi> (choi_seed n))"
    by (simp add: choi_matrix_def amplification_def)
next
  fix i j
  assume i: "i < dim_row (amplification n d n \<Phi> (choi_seed n))"
     and j: "j < dim_col (amplification n d n \<Phi> (choi_seed n))"
  then have id: "i < n*d" and jd: "j < n*d"
    by (simp_all add: amplification_def)
  have a_lt: "i div d < n"
    using id dpos by (simp add: div_less_iff_less_mult)
  have b_lt: "j div d < n"
    using jd dpos by (simp add: div_less_iff_less_mult)
  have "choi_matrix n d \<Phi> $$ (i,j)
      = \<Phi> (mat_unit (i div d) (j div d) n n) $$ (i mod d, j mod d)"
    using id jd by (simp add: choi_matrix_def)
  also have "\<dots> =
      \<Phi> (block_of_mat n (choi_seed n) (i div d) (j div d)) $$ (i mod d, j mod d)"
    using choi_seed_block[OF npos a_lt b_lt] by simp
  also have "\<dots> = amplification n d n \<Phi> (choi_seed n) $$ (i,j)"
    using id jd by (simp add: amplification_def)
  finally show "choi_matrix n d \<Phi> $$ (i,j) =
      amplification n d n \<Phi> (choi_seed n) $$ (i,j)".
qed

lemma choi_psd_if_cp:
  assumes npos: "n > 0"
      and dpos: "d > 0"
      and cp: "completely_positive n d \<Phi>"
  shows "psd (choi_matrix n d \<Phi>)"
proof -
  have pp: "p_positive n d n \<Phi>"
    using cp npos by (simp add: completely_positive_def)
  \<comment> \<open>The seed is the rank-one matrix \<open>v v\<^sup>\<dagger>\<close> for the (unnormalized) maximally
     entangled vector \<open>v = \<Sum>\<^sub>i e\<^sub>i \<otimes> e\<^sub>i\<close>, i.e. the \<open>n*n\<close>-vector that is 1 at
     position \<open>i*(n+1)\<close> for \<open>i < n\<close> and 0 elsewhere.\<close>
  define v :: "complex Matrix.vec" where
    "v = Matrix.vec (n*n) (\<lambda>r. if r div n = r mod n then 1 else 0)"
  have v_dim: "dim_vec v = n*n" by (simp add: v_def)
  let ?V = "mat_of_cols (n*n) [v]"
  have V_car: "?V \<in> carrier_mat (n*n) 1"
    by (simp add: mat_of_cols_def)
  have Vdag_car: "?V\<^sup>\<dagger> \<in> carrier_mat 1 (n*n)"
    using V_car by (simp add: dagger_def)
  have V_idx: "\<And>i. i < n*n \<Longrightarrow> ?V $$ (i,0) = v $ i"
    by (simp add: mat_of_cols_def)
  have Vdag_idx: "\<And>j. j < n*n \<Longrightarrow> (?V\<^sup>\<dagger>) $$ (0,j) = cnj (v $ j)"
    by (simp add: dagger_def mat_of_cols_def)
  have os_psd: "psd (outer_sum (n*n) [v])"
    using v_dim by (intro outer_sum_psd) auto
  have seed_eq: "choi_seed n = outer_sum (n*n) [v]"
  proof (rule eq_matI)
    show "dim_row (choi_seed n) = dim_row (outer_sum (n*n) [v])"
      by (simp add: choi_seed_def)
    show "dim_col (choi_seed n) = dim_col (outer_sum (n*n) [v])"
      by (simp add: choi_seed_def)
  next
    fix r c
    assume r_lt: "r < dim_row (outer_sum (n*n) [v])"
       and c_lt: "c < dim_col (outer_sum (n*n) [v])"
    hence rnn: "r < n*n" and cnn: "c < n*n" by simp_all
    have rdn: "r div n < n"
      using rnn npos by (simp add: div_less_iff_less_mult)
    have cdn: "c div n < n"
      using cnn npos by (simp add: div_less_iff_less_mult)
    have rmn: "r mod n < n" using npos by simp
    have cmn: "c mod n < n" using npos by simp
    have "choi_seed n $$ (r,c) =
          mat_unit (r div n) (c div n) n n $$ (r mod n, c mod n)"
      using rnn cnn by (simp add: choi_seed_def)
    also have "\<dots> = (if r mod n = r div n \<and> c mod n = c div n then 1 else 0)"
      using rmn cmn by simp
    also have "\<dots> = v $ r * cnj (v $ c)"
      using rnn cnn by (auto simp: v_def)
    also have "\<dots> = ?V $$ (r,0) * (?V\<^sup>\<dagger>) $$ (0,c)"
      using V_idx[OF rnn] Vdag_idx[OF cnn] by simp
    also have "\<dots> = (\<Sum>l<1. ?V $$ (r,l) * (?V\<^sup>\<dagger>) $$ (l,c))"
      by simp
    also have "\<dots> = (?V * (?V\<^sup>\<dagger>)) $$ (r,c)"
      using rnn cnn V_car Vdag_car
      by simp
    also have "\<dots> = outer_sum (n*n) [v] $$ (r,c)"
      by (simp add: outer_sum_def)
    finally show "choi_seed n $$ (r,c) = outer_sum (n*n) [v] $$ (r,c)" .
  qed
  have seed_psd: "psd (choi_seed n)"
    using os_psd seed_eq by simp
  have "psd (amplification n d n \<Phi> (choi_seed n))"
    using pp seed_psd by (simp add: p_positive_def)
  thus ?thesis
    using choi_matrix_as_amplification[OF npos dpos, of \<Phi>] by simp
qed

lemma kraus_cp_no_tp:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (kraus_map_dim d Ws)"
proof (unfold completely_positive_def p_positive_def, intro allI impI)
  fix p :: nat and X :: "complex Matrix.mat"
  assume ppos: "0 < p"
     and X_c: "X \<in> carrier_mat (p*n) (p*n)"
     and X_psd: "psd X"
  have lifted_c: "\<forall>L \<in> set (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws).
      L \<in> carrier_mat (p*d) (p*n)"
    using tensor_id_kraus_list_carrier[OF Ws_c] .
  have amp_eq: "amplification n d p (kraus_map_dim d Ws) X =
      kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) X"
    using amplification_kraus_map_dim[OF Ws_c X_c dpos npos] .
  show "psd (amplification n d p (kraus_map_dim d Ws) X)"
    using kraus_map_dim_psd[OF lifted_c X_c X_psd] amp_eq by simp
qed

subsection \<open>From a positive Choi matrix to a Kraus representation\<close>

text \<open>The notes' proof of (3)$\Rightarrow$(4): write $P_\Phi=\sum_kv_kv_k^*$ with
$v_k\in\C^{nd}$, cut each $v_k$ into $n$ blocks $w^k_1,\dots,w^k_n\in\C^d$, and let
$B_k=[w^k_1|\cdots|w^k_n]$; then $B_kE_{ij}B_k^*=w^k_i(w^k_j)^*$ and
$\Phi(X)=\sum_{ij}x_{ij}\Phi(E_{ij})=\sum_kB_kXB_k^*$ by linearity.\<close>

text \<open>
  Complete positivity from a Kraus list without the trace-preservation
  constraint: the argument is the same as @{thm kraus_is_cp}, which only uses
  the carrier hypothesis.
\<close>
text \<open>Linearity of the Kraus-sum map in its matrix argument.\<close>

lemma kraus_map_dim_add:
  assumes A_c: "A \<in> carrier_mat n n" and B_c: "B \<in> carrier_mat n n"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (A + B) =
         kraus_map_dim d Ws A + kraus_map_dim d Ws B"
  using Ws_c
proof (induction Ws)
  case Nil
  have "kraus_map_dim d [] (A + B) = 0\<^sub>m d d" by simp
  also have "\<dots> = (0\<^sub>m d d :: complex Matrix.mat) + 0\<^sub>m d d"
    by (intro eq_matI) auto
  also have "\<dots> = kraus_map_dim d [] A + kraus_map_dim d [] B"
    by simp
  finally show ?case .
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have WA_c: "W * A \<in> carrier_mat d n" using Wc A_c by auto
  have WB_c: "W * B \<in> carrier_mat d n" using Wc B_c by auto
  have WAD_c: "W * A * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using WA_c Wdag by auto
  have WBD_c: "W * B * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using WB_c Wdag by auto
  have rec_cA: "kraus_map_dim d Ws A \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' A_c] .
  have rec_cB: "kraus_map_dim d Ws B \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' B_c] .

  have sum_c: "A + B \<in> carrier_mat n n" using A_c B_c by auto
  have W_sum: "W * (A + B) = W * A + W * B"
    using Wc A_c B_c by (simp add: mult_add_distrib_mat)
  have "W * (A + B) * (W\<^sup>\<dagger>) = (W * A + W * B) * (W\<^sup>\<dagger>)"
    using W_sum by simp
  also have "\<dots> = W * A * (W\<^sup>\<dagger>) + W * B * (W\<^sup>\<dagger>)"
    using WA_c WB_c Wdag by (simp add: add_mult_distrib_mat)
  finally have term_split:
    "W * (A + B) * (W\<^sup>\<dagger>) = W * A * (W\<^sup>\<dagger>) + W * B * (W\<^sup>\<dagger>)" .

  have IH: "kraus_map_dim d Ws (A + B) =
            kraus_map_dim d Ws A + kraus_map_dim d Ws B"
    using Cons.IH[OF Ws_c'] .

  have "kraus_map_dim d (W # Ws) (A + B) =
        W * (A + B) * (W\<^sup>\<dagger>) + kraus_map_dim d Ws (A + B)"
    by simp
  also have "\<dots> = (W * A * (W\<^sup>\<dagger>) + W * B * (W\<^sup>\<dagger>))
                + (kraus_map_dim d Ws A + kraus_map_dim d Ws B)"
    using term_split IH by simp
  also have "\<dots> = (W * A * (W\<^sup>\<dagger>) + kraus_map_dim d Ws A)
                + (W * B * (W\<^sup>\<dagger>) + kraus_map_dim d Ws B)"
    using WAD_c WBD_c rec_cA rec_cB
    by (intro eq_matI) (auto simp: add.commute add.assoc)
  also have "\<dots> = kraus_map_dim d (W # Ws) A + kraus_map_dim d (W # Ws) B"
    by simp
  finally show ?case .
qed

lemma kraus_map_dim_smult:
  assumes A_c: "A \<in> carrier_mat n n"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m kraus_map_dim d Ws A"
  using Ws_c
proof (induction Ws)
  case Nil
  have "(c \<cdot>\<^sub>m 0\<^sub>m d d :: complex Matrix.mat) = 0\<^sub>m d d"
    by (intro eq_matI) auto
  thus ?case by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have WA_c: "W * A \<in> carrier_mat d n" using Wc A_c by auto
  have WAD_c: "W * A * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using WA_c Wdag by auto
  have rec_c: "kraus_map_dim d Ws A \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' A_c] .

  have W_scale: "W * (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m (W * A)"
    using Wc A_c by (simp add: mult_smult_distrib)
  have "W * (c \<cdot>\<^sub>m A) * (W\<^sup>\<dagger>) = (c \<cdot>\<^sub>m (W * A)) * (W\<^sup>\<dagger>)"
    using W_scale by simp
  also have "\<dots> = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>))"
    using WA_c Wdag by (simp add: mult_smult_assoc_mat)
  finally have term_eq:
    "W * (c \<cdot>\<^sub>m A) * (W\<^sup>\<dagger>) = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>))" .

  have IH: "kraus_map_dim d Ws (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m kraus_map_dim d Ws A"
    using Cons.IH[OF Ws_c'] .

  have "kraus_map_dim d (W # Ws) (c \<cdot>\<^sub>m A) =
        W * (c \<cdot>\<^sub>m A) * (W\<^sup>\<dagger>) + kraus_map_dim d Ws (c \<cdot>\<^sub>m A)"
    by simp
  also have "\<dots> = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>)) + c \<cdot>\<^sub>m kraus_map_dim d Ws A"
    using term_eq IH by simp
  also have "\<dots> = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>) + kraus_map_dim d Ws A)"
    using WAD_c rec_c by (simp add: add_smult_distrib_left_mat)
  also have "\<dots> = c \<cdot>\<^sub>m kraus_map_dim d (W # Ws) A"
    by simp
  finally show ?case .
qed

lemma kraus_map_dim_zero [simp]:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (0\<^sub>m n n) = 0\<^sub>m d d"
  using Ws_c
proof (induction Ws)
  case Nil show ?case by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have W0: "W * (0\<^sub>m n n) = 0\<^sub>m d n"
    using Wc by (metis right_mult_zero_mat)
  have term_zero: "W * (0\<^sub>m n n) * (W\<^sup>\<dagger>) = 0\<^sub>m d d"
    using W0 Wdag by (metis left_mult_zero_mat)
  have IH: "kraus_map_dim d Ws (0\<^sub>m n n) = 0\<^sub>m d d" using Cons.IH[OF Ws_c'] .
  have "kraus_map_dim d (W # Ws) (0\<^sub>m n n) =
        W * (0\<^sub>m n n) * (W\<^sup>\<dagger>) + kraus_map_dim d Ws (0\<^sub>m n n)"
    by simp
  also have "\<dots> = 0\<^sub>m d d + 0\<^sub>m d d"
    using term_zero IH by simp
  also have "\<dots> = 0\<^sub>m d d"
    by (intro eq_matI) auto
  finally show ?case .
qed

text \<open>Enumeration of \<open>[0..<n] \<times> [0..<n]\<close> as a list of pairs.\<close>

definition mat_unit_pairs :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "mat_unit_pairs n \<equiv>
     concat (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"

lemma mat_unit_pairs_set:
  "set (mat_unit_pairs n) = {p. fst p < n \<and> snd p < n}"
  unfolding mat_unit_pairs_def by auto

lemma mat_unit_pairs_distinct: "distinct (mat_unit_pairs n)"
  unfolding mat_unit_pairs_def
proof (intro distinct_concat)
  have inj: "inj_on (\<lambda>a. map (Pair a) [0..<n]) (set [0..<n])"
  proof (rule inj_onI)
    fix a1 a2
    assume a1_in: "a1 \<in> set [0..<n]" and a2_in: "a2 \<in> set [0..<n]"
       and eq: "map (Pair a1) [0..<n] = map (Pair a2) [0..<n]"
    have npos: "0 < n" using a1_in by simp
    from eq show "a1 = a2" using npos by auto
  qed
  show "distinct (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"
    using inj by (simp add: distinct_map)
next
  fix ys
  assume "ys \<in> set (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"
  thus "distinct ys"
    by (auto simp: distinct_map inj_on_def)
next
  fix ys zs
  assume "ys \<in> set (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"
     and "zs \<in> set (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"
     and "ys \<noteq> zs"
  thus "set ys \<inter> set zs = {}"
    by auto
qed

text \<open>The combination $\sum_{a,b}A_{ab}\,f(E_{ab})$.\<close>

primrec pair_comb ::
  "(complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> complex Matrix.mat" where
  "pair_comb f A n d [] = 0\<^sub>m d d" |
  "pair_comb f A n d (p # ps) =
     A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n) + pair_comb f A n d ps"

lemma pair_comb_carrier:
  assumes f_car: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> f (mat_unit a b n n) \<in> carrier_mat d d"
      and ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
  shows "pair_comb f A n d ps \<in> carrier_mat d d"
  using ps_valid
proof (induction ps)
  case Nil show ?case by simp
next
  case (Cons p ps)
  obtain a b where p_eq: "p = (a,b)" by (cases p)
  hence a_lt: "a < n" and b_lt: "b < n"
    using Cons.prems by auto
  have fE_car: "f (mat_unit a b n n) \<in> carrier_mat d d"
    using f_car[OF a_lt b_lt] .
  have smult_c: "A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n) \<in> carrier_mat d d"
    using fE_car p_eq by simp
  have rec_c: "pair_comb f A n d ps \<in> carrier_mat d d"
    using Cons by auto
  show ?case using smult_c rec_c by simp
qed

lemma pair_comb_entry:
  assumes f_car: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> f (mat_unit a b n n) \<in> carrier_mat d d"
      and ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "pair_comb f A n d ps $$ (r,c) =
         (\<Sum>p \<leftarrow> ps. A $$ p * f (mat_unit (fst p) (snd p) n n) $$ (r,c))"
  using ps_valid
proof (induction ps)
  case Nil
  show ?case using r_lt c_lt by simp
next
  case (Cons p ps)
  obtain a b where p_eq: "p = (a,b)" by (cases p)
  hence a_lt: "a < n" and b_lt: "b < n"
    using Cons.prems by auto
  have fE_car: "f (mat_unit a b n n) \<in> carrier_mat d d"
    using f_car[OF a_lt b_lt] .
  have smult_c: "A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n) \<in> carrier_mat d d"
    using fE_car p_eq by simp
  have rec_c: "pair_comb f A n d ps \<in> carrier_mat d d"
    using Cons.prems f_car pair_comb_carrier[where f=f] by auto
  have IH: "pair_comb f A n d ps $$ (r,c) =
            (\<Sum>q \<leftarrow> ps. A $$ q * f (mat_unit (fst q) (snd q) n n) $$ (r,c))"
    using Cons by auto
  have "pair_comb f A n d (p # ps) $$ (r,c) =
        (A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n) + pair_comb f A n d ps) $$ (r,c)"
    by simp
  also have "\<dots> = (A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)) $$ (r,c)
                + pair_comb f A n d ps $$ (r,c)"
    using smult_c rec_c r_lt c_lt by simp
  also have "(A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)) $$ (r,c)
           = A $$ p * f (mat_unit (fst p) (snd p) n n) $$ (r,c)"
    using fE_car r_lt c_lt p_eq by simp
  finally show ?case using IH by simp
qed

text \<open>For the identity-like choice \<open>f = id\<close>, the pair combination reconstructs
  \<open>A\<close> when \<open>ps\<close> enumerates all basis positions.\<close>

lemma pair_comb_id_reconstructs:
  assumes A_car: "A \<in> carrier_mat n n"
  shows "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) = A"
proof (rule eq_matI)
  have ps_valid: "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
    using mat_unit_pairs_set by auto
  have comb_car: "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) \<in> carrier_mat n n"
  proof (rule pair_comb_carrier)
    fix a b :: nat
    assume "a < n" "b < n"
    show "(\<lambda>X. X) (mat_unit a b n n) \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
  qed (use ps_valid in auto)
  show "dim_row (pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n)) = dim_row A"
    using comb_car A_car by auto
  show "dim_col (pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n)) = dim_col A"
    using comb_car A_car by auto
next
  fix r c
  assume "r < dim_row A" "c < dim_col A"
  hence r_lt: "r < n" and c_lt: "c < n"
    using A_car by auto
  have ps_valid: "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
    using mat_unit_pairs_set by auto
  have pc_entry:
    "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) $$ (r,c) =
     (\<Sum>p \<leftarrow> mat_unit_pairs n. A $$ p * (\<lambda>X. X) (mat_unit (fst p) (snd p) n n) $$ (r,c))"
  proof (rule pair_comb_entry)
    fix a b :: nat
    assume "a < n" "b < n"
    show "(\<lambda>X. X) (mat_unit a b n n) \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
  qed (use ps_valid r_lt c_lt in auto)
  have "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) $$ (r,c) =
        (\<Sum>p \<leftarrow> mat_unit_pairs n. A $$ p * mat_unit (fst p) (snd p) n n $$ (r,c))"
    using pc_entry by simp
  also have "\<dots> = (\<Sum>p \<leftarrow> mat_unit_pairs n.
                    A $$ p * (if fst p = r \<and> snd p = c then 1 else 0))"
    using r_lt c_lt
    by (intro arg_cong[where f=sum_list] list.map_cong refl)
       (auto simp: case_prod_beta)
  also have "\<dots> = (\<Sum>p \<leftarrow> mat_unit_pairs n.
                    (if p = (r,c) then A $$ (r,c) else 0))"
    by (intro arg_cong[where f=sum_list] list.map_cong refl)
       (auto simp: prod_eq_iff)
  also have "\<dots> = A $$ (r,c)"
  proof -
    have rc_in: "(r,c) \<in> set (mat_unit_pairs n)"
      using r_lt c_lt by (simp add: mat_unit_pairs_set)
    have dist: "distinct (mat_unit_pairs n)"
      by (rule mat_unit_pairs_distinct)
    have "(\<Sum>p \<leftarrow> mat_unit_pairs n.
             (if p = (r,c) then A $$ (r,c) else 0))
          = (\<Sum>p \<in> set (mat_unit_pairs n).
               (if p = (r,c) then A $$ (r,c) else 0))"
      using dist by (rule sum_list_distinct_conv_sum_set)
    also have "\<dots> = A $$ (r,c)"
      using rc_in by (subst sum.delta_remove) auto
    finally show ?thesis .
  qed
  finally show "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) $$ (r,c) = A $$ (r,c)"
    by simp
qed

text \<open>For linear $f:M_n\to M_d$, $f(A)=\sum_{a,b}A_{ab}\,f(E_{ab})$.\<close>

lemma linear_eq_pair_comb:
  fixes f :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes f_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n \<Longrightarrow>
                   f (X + Y) = f X + f Y"
      and f_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow> f (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m f X"
      and f_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> f X \<in> carrier_mat d d"
      and A_car: "A \<in> carrier_mat n n"
      and npos: "n > 0" and dpos: "d > 0"
  shows "f A = pair_comb f A n d (mat_unit_pairs n)"
proof -
  have Eab_car: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> mat_unit a b n n \<in> carrier_mat n n"
    by (simp add: mat_unit_def)
  have fEab_car: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> f (mat_unit a b n n) \<in> carrier_mat d d"
    using f_car Eab_car by blast
  have f_zero: "f (0\<^sub>m n n) = 0\<^sub>m d d"
  proof -
    have zc: "0\<^sub>m n n \<in> carrier_mat n n" by auto
    have "f (0\<^sub>m n n) = f (0 \<cdot>\<^sub>m 0\<^sub>m n n)"
      by (intro arg_cong[where f=f]) (rule eq_matI, auto)
    also have "\<dots> = 0 \<cdot>\<^sub>m f (0\<^sub>m n n)"
      using f_smult[OF zc] by simp
    also have "\<dots> = 0\<^sub>m d d"
      using f_car[OF zc] by (intro eq_matI) auto
    finally show ?thesis.
  qed
  \<comment> \<open>Key induction: for any list \<open>ps\<close> of valid pairs, \<open>f\<close> applied to the
     \<open>\<lambda>X. X\<close> pair-combination equals the \<open>f\<close> pair-combination.\<close>
  have gen: "\<And>ps. (\<forall>p \<in> set ps. fst p < n \<and> snd p < n) \<Longrightarrow>
              f (pair_comb (\<lambda>X. X) A n n ps) = pair_comb f A n d ps"
  proof -
    fix ps :: "(nat \<times> nat) list"
    assume ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
    show "f (pair_comb (\<lambda>X. X) A n n ps) = pair_comb f A n d ps"
      using ps_valid
    proof (induction ps)
      case Nil
      show ?case using f_zero by simp
    next
      case (Cons p ps)
      obtain a b where p_eq: "p = (a,b)" by (cases p)
      hence a_lt: "a < n" and b_lt: "b < n"
        using Cons.prems by auto
      have Eab_c: "mat_unit a b n n \<in> carrier_mat n n"
        using a_lt b_lt Eab_car by simp
      have smult_Eab_c: "A $$ p \<cdot>\<^sub>m mat_unit (fst p) (snd p) n n \<in> carrier_mat n n"
        using Eab_c p_eq by simp
      have ps_valid': "\<forall>q \<in> set ps. fst q < n \<and> snd q < n"
        using Cons.prems by simp
      have rec_c: "pair_comb (\<lambda>X. X) A n n ps \<in> carrier_mat n n"
      proof (rule pair_comb_carrier)
        fix a b :: nat
        assume "a < n" "b < n"
        show "(\<lambda>X. X) (mat_unit a b n n) \<in> carrier_mat n n"
          by (simp add: mat_unit_def)
      qed (use ps_valid' in auto)
      have "f (pair_comb (\<lambda>X. X) A n n (p # ps)) =
            f (A $$ p \<cdot>\<^sub>m mat_unit (fst p) (snd p) n n + pair_comb (\<lambda>X. X) A n n ps)"
        by simp
      also have "\<dots> = f (A $$ p \<cdot>\<^sub>m mat_unit (fst p) (snd p) n n)
                    + f (pair_comb (\<lambda>X. X) A n n ps)"
        using f_add[OF smult_Eab_c rec_c] by simp
      also have "\<dots> = A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)
                    + f (pair_comb (\<lambda>X. X) A n n ps)"
      proof -
        have "f (A $$ p \<cdot>\<^sub>m mat_unit (fst p) (snd p) n n)
              = A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)"
          using f_smult[OF Eab_c] p_eq by simp
        thus ?thesis by simp
      qed
      also have "\<dots> = A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)
                    + pair_comb f A n d ps"
        using Cons.IH[OF ps_valid'] by simp
      also have "\<dots> = pair_comb f A n d (p # ps)"
        by simp
      finally show ?case.
    qed
  qed
  have ps_valid_full: "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
    using mat_unit_pairs_set by auto
  have "f A = f (pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n))"
    using pair_comb_id_reconstructs[OF A_car] by simp
  also have "\<dots> = pair_comb f A n d (mat_unit_pairs n)"
    using gen[OF ps_valid_full].
  finally show ?thesis.
qed

text \<open>$(WE_{ab}W^*)_{ij}=W_{ia}\,\overline{W_{jb}}$.\<close>

lemma conjugation_mat_unit_entry:
  assumes Wc: "W \<in> carrier_mat d n"
      and a_lt: "a < n" and b_lt: "b < n"
      and i_lt: "i < d" and j_lt: "j < d"
  shows "(W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
         W $$ (i, a) * cnj (W $$ (j, b))"
proof -
  have Eab_c: "mat_unit a b n n \<in> carrier_mat n n"
    by (simp add: mat_unit_def)
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have WE_c: "W * mat_unit a b n n \<in> carrier_mat d n"
    using Wc Eab_c by auto
  have dim_WE: "dim_col (W * mat_unit a b n n) = n"
    using WE_c by auto
  have dim_W: "dim_col W = n" using Wc by auto
  have i_WE: "i < dim_row (W * mat_unit a b n n)"
    using WE_c i_lt by auto
  have j_Wdag: "j < dim_col (W\<^sup>\<dagger>)"
    using Wdag_c j_lt by auto
  have "(W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)
      = Matrix.row (W * mat_unit a b n n) i \<bullet> Matrix.col (W\<^sup>\<dagger>) j"
    using index_mult_mat(1)[OF i_WE j_Wdag].
  also have "\<dots> = (\<Sum>p<n.
        Matrix.row (W * mat_unit a b n n) i $ p * Matrix.col (W\<^sup>\<dagger>) j $ p)"
    unfolding scalar_prod_def using dim_WE dim_W Wdag_c
    by (simp add: atLeast0LessThan)
  also have "\<dots> = (\<Sum>p<n.
        (W * mat_unit a b n n) $$ (i, p) * (W\<^sup>\<dagger>) $$ (p, j))"
  proof (intro sum.cong refl)
    fix p assume "p \<in> {..<n}"
    hence p_lt: "p < n" by simp
    have "Matrix.row (W * mat_unit a b n n) i $ p = (W * mat_unit a b n n) $$ (i, p)"
      using i_WE p_lt dim_WE by simp
    moreover have "Matrix.col (W\<^sup>\<dagger>) j $ p = (W\<^sup>\<dagger>) $$ (p, j)"
      using Wdag_c j_lt p_lt
      by (metis carrier_matD(1) carrier_matD(2) index_col)
    ultimately show "Matrix.row (W * mat_unit a b n n) i $ p *
                     Matrix.col (W\<^sup>\<dagger>) j $ p
                   = (W * mat_unit a b n n) $$ (i, p) * (W\<^sup>\<dagger>) $$ (p, j)"
      by simp
  qed
  also have "\<dots> = (\<Sum>p<n.
        (\<Sum>q<n. W $$ (i, q) * mat_unit a b n n $$ (q, p)) * (W\<^sup>\<dagger>) $$ (p, j))"
  proof (intro sum.cong refl)
    fix p assume "p \<in> {..<n}"
    hence p_lt: "p < n" by simp
    have i_W: "i < dim_row W" using Wc i_lt by auto
    have p_E: "p < dim_col (mat_unit a b n n)" using Eab_c p_lt by simp
    have "(W * mat_unit a b n n) $$ (i, p) =
          Matrix.row W i \<bullet> Matrix.col (mat_unit a b n n) p"
      using index_mult_mat(1)[OF i_W p_E] .
    also have "\<dots> = (\<Sum>q<n. Matrix.row W i $ q *
                           Matrix.col (mat_unit a b n n) p $ q)"
      unfolding scalar_prod_def using dim_W
      by (simp add: atLeast0LessThan)
    also have "\<dots> = (\<Sum>q<n. W $$ (i, q) * mat_unit a b n n $$ (q, p))"
    proof (intro sum.cong refl)
      fix q assume "q \<in> {..<n}"
      hence q_lt: "q < n" by simp
      have "Matrix.row W i $ q = W $$ (i, q)"
        using i_W q_lt dim_W by simp
      moreover have
        "Matrix.col (mat_unit a b n n) p $ q = mat_unit a b n n $$ (q, p)"
        using Eab_c p_lt q_lt by simp
      ultimately show "Matrix.row W i $ q * Matrix.col (mat_unit a b n n) p $ q
                     = W $$ (i, q) * mat_unit a b n n $$ (q, p)"
        by simp
    qed
    finally show
      "(W * mat_unit a b n n) $$ (i, p) * (W\<^sup>\<dagger>) $$ (p, j) =
       (\<Sum>q<n. W $$ (i, q) * mat_unit a b n n $$ (q, p)) * (W\<^sup>\<dagger>) $$ (p, j)"
      by simp
  qed
  also have "\<dots> = (\<Sum>p<n.
        (\<Sum>q<n. W $$ (i, q) * (if q = a \<and> p = b then 1 else 0))
           * (W\<^sup>\<dagger>) $$ (p, j))"
    by (intro sum.cong refl) (simp)
  also have "\<dots> = (\<Sum>p<n.
        (if p = b then W $$ (i, a) else 0) * (W\<^sup>\<dagger>) $$ (p, j))"
  proof (intro sum.cong refl)
    fix p assume "p \<in> {..<n}"
    hence p_lt: "p < n" by simp
    have "(\<Sum>q<n. W $$ (i, q) * (if q = a \<and> p = b then 1 else 0))
        = (\<Sum>q<n. if q = a \<and> p = b then W $$ (i, q) else 0)"
      by (intro sum.cong refl) simp
    also have "\<dots> = (if p = b then W $$ (i, a) else 0)"
      using a_lt by simp
    finally show "(\<Sum>q<n. W $$ (i, q) * (if q = a \<and> p = b then 1 else 0))
               * (W\<^sup>\<dagger>) $$ (p, j)
               = (if p = b then W $$ (i, a) else 0) * (W\<^sup>\<dagger>) $$ (p, j)"
      by simp
  qed
  also have "\<dots> = (\<Sum>p<n. if p = b then W $$ (i, a) * (W\<^sup>\<dagger>) $$ (p, j) else 0)"
    by (intro sum.cong refl) simp
  also have "\<dots> = W $$ (i, a) * (W\<^sup>\<dagger>) $$ (b, j)"
    using b_lt by simp
  also have "(W\<^sup>\<dagger>) $$ (b, j) = cnj (W $$ (j, b))"
    using Wc b_lt j_lt by (simp add: dagger_def)
  finally show ?thesis.
qed

text \<open>Entry-wise formula for @{const kraus_map_dim} as a sum over the list.\<close>

lemma kraus_map_dim_entry_sum_list:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and rho_c: "\<rho> \<in> carrier_mat n n"
      and i_lt: "i < d" and j_lt: "j < d"
  shows "kraus_map_dim d Ws \<rho> $$ (i, j) =
         sum_list (map (\<lambda>W. (W * \<rho> * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
  using Ws_c
proof (induction Ws)
  case Nil
  show ?case using i_lt j_lt by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n" and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have Wr_c: "W * \<rho> \<in> carrier_mat d n" using Wc rho_c by auto
  have WrW_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using Wr_c Wdag_c by auto
  have rec_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' rho_c] .
  have IH: "kraus_map_dim d Ws \<rho> $$ (i, j) =
            sum_list (map (\<lambda>W. (W * \<rho> * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
    using Cons.IH[OF Ws_c'] .
  show "kraus_map_dim d (W # Ws) \<rho> $$ (i, j)
      = sum_list (map (\<lambda>W. (W * \<rho> * (W\<^sup>\<dagger>)) $$ (i, j)) (W # Ws))"
    using IH WrW_c rec_c i_lt j_lt by simp
qed

text \<open>From a positive Choi matrix to Kraus operators: factor $P_\Phi=VV^*$ and reshape each column of
$V$ into a $d\times n$ matrix $W_k$; then $\Phi(X)=\sum_kW_kXW_k^*$ on all of $M_n$.\<close>

lemma kraus_rep_of_psd_choi:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
      and psdP: "psd (choi_matrix n d \<Phi>)"
  shows "\<exists>Ws :: complex Matrix.mat list.
           length Ws = n * d \<and>
           (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and>
           (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
proof -
  have P_car: "choi_matrix n d \<Phi> \<in> carrier_mat (n*d) (n*d)"
    by (simp add: choi_matrix_def)
  (* Extract a length-aware psd factorisation of the Choi matrix.  We
     spell out the existential elimination explicitly: obtain a
     witness \<open>vs\<^sub>0\<close> from \<open>psd_kraus_decomp\<close>, decompose its
     conjunctive predicate, and re-introduce \<open>vs\<close> with the three
     named facts. *)
  obtain vs :: "complex Matrix.vec list"
    where vs_len: "length vs = n*d"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n*d"
      and vs_sum: "outer_sum (n*d) vs = choi_matrix n d \<Phi>"
  proof -
    have ex_decomp:
      "\<exists>vs :: complex Matrix.vec list.
          length vs = n*d
          \<and> (\<forall>v \<in> set vs. dim_vec v = n*d)
          \<and> outer_sum (n*d) vs = choi_matrix n d \<Phi>"
      using psd_kraus_decomp[OF P_car psdP] .
    obtain vs\<^sub>0 :: "complex Matrix.vec list"
      where vs\<^sub>0_props:
        "length vs\<^sub>0 = n*d
         \<and> (\<forall>v \<in> set vs\<^sub>0. dim_vec v = n*d)
         \<and> outer_sum (n*d) vs\<^sub>0 = choi_matrix n d \<Phi>"
      using ex_decomp by (elim exE)
    from vs\<^sub>0_props
    have len: "length vs\<^sub>0 = n*d"
      and dim: "\<forall>v \<in> set vs\<^sub>0. dim_vec v = n*d"
      and sum: "outer_sum (n*d) vs\<^sub>0 = choi_matrix n d \<Phi>"
      by (rule conjunct1, rule conjunct1[OF conjunct2],
          rule conjunct2[OF conjunct2])
    show thesis using that[OF len dim sum] .
  qed
  define Ws :: "complex Matrix.mat list" where
    "Ws = map (\<lambda>v. Matrix.mat d n (\<lambda>(i, a). v $ (a*d + i))) vs"
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    by (auto simp: Ws_def)
  have len_Ws: "length Ws = length vs"
    by (simp add: Ws_def)

  have match_unit:
    "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow>
       \<Phi> (mat_unit a b n n) = kraus_map_dim d Ws (mat_unit a b n n)"
  proof -
    fix a b assume a_lt: "a < n" and b_lt: "b < n"
    have Eab_c: "mat_unit a b n n \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
    have \<Phi>Eab_c: "\<Phi> (mat_unit a b n n) \<in> carrier_mat d d"
      using range Eab_c by blast
    have kmd_c: "kraus_map_dim d Ws (mat_unit a b n n) \<in> carrier_mat d d"
      using kraus_map_dim_carrier[OF Ws_c Eab_c] .
    show "\<Phi> (mat_unit a b n n) = kraus_map_dim d Ws (mat_unit a b n n)"
    proof (rule eq_matI)
      show "dim_row (\<Phi> (mat_unit a b n n)) =
            dim_row (kraus_map_dim d Ws (mat_unit a b n n))"
        using \<Phi>Eab_c kmd_c by auto
      show "dim_col (\<Phi> (mat_unit a b n n)) =
            dim_col (kraus_map_dim d Ws (mat_unit a b n n))"
        using \<Phi>Eab_c kmd_c by auto
    next
      fix i j
      assume "i < dim_row (kraus_map_dim d Ws (mat_unit a b n n))"
             "j < dim_col (kraus_map_dim d Ws (mat_unit a b n n))"
      hence i_lt: "i < d" and j_lt: "j < d"
        using kmd_c by auto
      have adi_lt: "a*d + i < n*d"
        using a_lt i_lt
        by (metis Nat.add_0_right div_less div_less_iff_less_mult div_mult_self3 dpos not_less0)
      have bdj_lt: "b*d + j < n*d"
        using b_lt j_lt
        by (metis Nat.add_0_right div_less div_less_iff_less_mult div_mult_self3 dpos not_less0)
      have adi_div: "(a*d + i) div d = a" using i_lt dpos by simp
      have bdj_div: "(b*d + j) div d = b" using j_lt dpos by simp
      have adi_mod: "(a*d + i) mod d = i" using i_lt dpos by simp
      have bdj_mod: "(b*d + j) mod d = j" using j_lt dpos by simp
      have "\<Phi> (mat_unit a b n n) $$ (i, j)
          = choi_matrix n d \<Phi> $$ (a*d + i, b*d + j)"
        using adi_lt bdj_lt adi_div bdj_div adi_mod bdj_mod
        by (simp add: choi_matrix_def)
      also have "\<dots> = outer_sum (n*d) vs $$ (a*d + i, b*d + j)"
        using vs_sum by simp
      also have "\<dots> = sum_list (map (\<lambda>v. v $ (a*d + i) * cnj (v $ (b*d + j))) vs)"
        using outer_sum_entry_sum_list[OF vs_dim adi_lt bdj_lt] .
      also have "\<dots> = sum_list (map (\<lambda>W. (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
      proof -
        have point_eq:
          "\<And>W. W \<in> set Ws \<Longrightarrow>
              (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
              W $$ (i, a) * cnj (W $$ (j, b))"
        proof -
          fix W assume W_in: "W \<in> set Ws"
          have Wc_k: "W \<in> carrier_mat d n" using Ws_c W_in by simp
          show "(W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
                W $$ (i, a) * cnj (W $$ (j, b))"
            using conjugation_mat_unit_entry[OF Wc_k a_lt b_lt i_lt j_lt] .
        qed
        have "sum_list (map (\<lambda>v. v $ (a*d + i) * cnj (v $ (b*d + j))) vs) =
              sum_list (map (\<lambda>W. W $$ (i, a) * cnj (W $$ (j, b))) Ws)"
          unfolding Ws_def
          using i_lt a_lt j_lt b_lt
          by (induction vs) simp_all
        also have "\<dots> = sum_list (map (\<lambda>W. (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
          using point_eq
          by (intro arg_cong[where f=sum_list] map_cong refl) (metis)
        finally show ?thesis.
      qed
      also have "\<dots> = kraus_map_dim d Ws (mat_unit a b n n) $$ (i, j)"
        using kraus_map_dim_entry_sum_list[OF Ws_c Eab_c i_lt j_lt] by simp
      finally show "\<Phi> (mat_unit a b n n) $$ (i, j) =
                    kraus_map_dim d Ws (mat_unit a b n n) $$ (i, j)".
    qed
  qed

  have kmd_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws (X + Y) = kraus_map_dim d Ws X + kraus_map_dim d Ws Y"
    using kraus_map_dim_add Ws_c by blast
  have kmd_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m kraus_map_dim d Ws X"
    using kraus_map_dim_smult Ws_c by blast
  have kmd_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws X \<in> carrier_mat d d"
    using kraus_map_dim_carrier Ws_c by blast
  have \<Phi>_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X \<in> carrier_mat d d"
    using range by blast

  have phi_eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
  proof (intro allI impI)
    fix A :: "complex Matrix.mat" assume Ac: "A \<in> carrier_mat n n"
    have lhs: "\<Phi> A = pair_comb \<Phi> A n d (mat_unit_pairs n)"
      using linear_eq_pair_comb[OF linear smult \<Phi>_car Ac npos dpos] .
    have rhs: "kraus_map_dim d Ws A =
               pair_comb (kraus_map_dim d Ws) A n d (mat_unit_pairs n)"
      using linear_eq_pair_comb[OF kmd_add kmd_smult kmd_car Ac npos dpos] .
    have comb_eq:
      "pair_comb \<Phi> A n d (mat_unit_pairs n) =
       pair_comb (kraus_map_dim d Ws) A n d (mat_unit_pairs n)"
    proof -
      have "\<And>ps. (\<forall>p \<in> set ps. fst p < n \<and> snd p < n) \<Longrightarrow>
          pair_comb \<Phi> A n d ps = pair_comb (kraus_map_dim d Ws) A n d ps"
      proof -
        fix ps :: "(nat \<times> nat) list"
        assume ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
        show "pair_comb \<Phi> A n d ps =
              pair_comb (kraus_map_dim d Ws) A n d ps"
          using ps_valid
        proof (induction ps)
          case Nil show ?case by simp
        next
          case (Cons p ps)
          obtain a b where p_eq: "p = (a, b)" by (cases p)
          hence a_lt: "a < n" and b_lt: "b < n"
            using Cons.prems by auto
          have basis_eq: "\<Phi> (mat_unit (fst p) (snd p) n n) =
                          kraus_map_dim d Ws (mat_unit (fst p) (snd p) n n)"
            using match_unit[OF a_lt b_lt] p_eq by simp
          have IH: "pair_comb \<Phi> A n d ps =
                    pair_comb (kraus_map_dim d Ws) A n d ps"
            using Cons by auto
          show ?case using basis_eq IH by simp
        qed
      qed
      moreover have "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
        using mat_unit_pairs_set by auto
      ultimately show ?thesis by blast
    qed
    show "\<Phi> A = kraus_map_dim d Ws A"
      using lhs rhs comb_eq by simp
  qed

  have Ws_len: "length Ws = n * d"
    using vs_len len_Ws by simp
  show ?thesis using Ws_len Ws_c phi_eq by blast
qed

theorem choi_theorem:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
  shows "completely_positive n d \<Phi> \<longleftrightarrow>
         psd (choi_matrix n d \<Phi>)"
proof
  assume "completely_positive n d \<Phi>"
  thus "psd (choi_matrix n d \<Phi>)"
    using choi_psd_if_cp[OF npos dpos] by simp
next
  assume psdP: "psd (choi_matrix n d \<Phi>)"
  \<comment> \<open>Factor \<open>P\<^sub>\<Phi> = \<Sum>\<^sub>k v\<^sub>k v\<^sub>k\<^sup>\<dagger>\<close> and reshape each \<open>v\<^sub>k \<in> \<complex>\<^bsup>nd\<^esup>\<close> into a
     \<open>d \<times> n\<close> Kraus operator \<open>W\<^sub>k\<close>.  Each \<open>W\<^sub>k\<close> is given by
     \<open>(W\<^sub>k)\<^sub>i\<^sub>a = v\<^sub>k $ (a*d + i)\<close>, matching the Choi-index convention.\<close>
  have P_car: "choi_matrix n d \<Phi> \<in> carrier_mat (n*d) (n*d)"
    by (simp add: choi_matrix_def)
  obtain vs :: "complex Matrix.vec list"
    where vs_len: "length vs = n*d"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n*d"
      and vs_sum: "outer_sum (n*d) vs = choi_matrix n d \<Phi>"
    using psd_kraus_decomp[OF P_car psdP] by blast
  define Ws :: "complex Matrix.mat list" where
    "Ws = map (\<lambda>v. Matrix.mat d n (\<lambda>(i, a). v $ (a*d + i))) vs"
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    by (auto simp: Ws_def)
  have len_Ws: "length Ws = length vs"
    by (simp add: Ws_def)

  \<comment> \<open>Step 1: \<open>\<Phi>(E\<^sub>a\<^sub>b) = kraus_map_dim d Ws E\<^sub>a\<^sub>b\<close> for \<open>a, b < n\<close>.\<close>
  have match_unit:
    "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow>
       \<Phi> (mat_unit a b n n) = kraus_map_dim d Ws (mat_unit a b n n)"
  proof -
    fix a b assume a_lt: "a < n" and b_lt: "b < n"
    have Eab_c: "mat_unit a b n n \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
    have \<Phi>Eab_c: "\<Phi> (mat_unit a b n n) \<in> carrier_mat d d"
      using range Eab_c by blast
    have kmd_c: "kraus_map_dim d Ws (mat_unit a b n n) \<in> carrier_mat d d"
      using kraus_map_dim_carrier[OF Ws_c Eab_c] .
    show "\<Phi> (mat_unit a b n n) = kraus_map_dim d Ws (mat_unit a b n n)"
    proof (rule eq_matI)
      show "dim_row (\<Phi> (mat_unit a b n n)) =
            dim_row (kraus_map_dim d Ws (mat_unit a b n n))"
        using \<Phi>Eab_c kmd_c by auto
      show "dim_col (\<Phi> (mat_unit a b n n)) =
            dim_col (kraus_map_dim d Ws (mat_unit a b n n))"
        using \<Phi>Eab_c kmd_c by auto
    next
      fix i j
      assume "i < dim_row (kraus_map_dim d Ws (mat_unit a b n n))"
             "j < dim_col (kraus_map_dim d Ws (mat_unit a b n n))"
      hence i_lt: "i < d" and j_lt: "j < d"
        using kmd_c by auto
      have adi_lt: "a*d + i < n*d"
        using a_lt i_lt
        by (metis Nat.add_0_right div_less div_less_iff_less_mult div_mult_self3 dpos not_less0)
      
      have bdj_lt: "b*d + j < n*d"
        using b_lt j_lt
        by (metis Nat.add_0_right div_less div_less_iff_less_mult div_mult_self3 dpos not_less0)

      have adi_div: "(a*d + i) div d = a" using i_lt dpos by simp
      have bdj_div: "(b*d + j) div d = b" using j_lt dpos by simp
      have adi_mod: "(a*d + i) mod d = i" using i_lt dpos by simp
      have bdj_mod: "(b*d + j) mod d = j" using j_lt dpos by simp
      \<comment> \<open>LHS via the Choi matrix.\<close>
      have "\<Phi> (mat_unit a b n n) $$ (i, j)
          = choi_matrix n d \<Phi> $$ (a*d + i, b*d + j)"
        using adi_lt bdj_lt adi_div bdj_div adi_mod bdj_mod
        by (simp add: choi_matrix_def)
      also have "\<dots> = outer_sum (n*d) vs $$ (a*d + i, b*d + j)"
        using vs_sum by simp
      also have "\<dots> = sum_list (map (\<lambda>v. v $ (a*d + i) * cnj (v $ (b*d + j))) vs)"
        using outer_sum_entry_sum_list[OF vs_dim adi_lt bdj_lt] .
      \<comment> \<open>RHS via the reshape identity.\<close>
      also have "\<dots> = sum_list (map (\<lambda>W. (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
      proof -
        have "\<And>v. v \<in> set vs \<Longrightarrow>
              (Matrix.mat d n (\<lambda>(i, a). v $ (a*d + i))) $$ (i, a)
              = v $ (a*d + i)"
          using i_lt a_lt by simp
        have Ws_nth: "\<And>k. k < length vs \<Longrightarrow>
              Ws ! k = Matrix.mat d n (\<lambda>(i, a). (vs ! k) $ (a*d + i))"
          by (simp add: Ws_def)
        have Ws_c_idx: "\<And>k. k < length vs \<Longrightarrow> Ws ! k \<in> carrier_mat d n"
          using Ws_c len_Ws by (auto simp: set_conv_nth)
        have point_eq:
          "\<And>W. W \<in> set Ws \<Longrightarrow>
              (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
              W $$ (i, a) * cnj (W $$ (j, b))"
        proof -
          fix W assume "W \<in> set Ws"
          then obtain k where k_lt: "k < length Ws" and W_eq: "W = Ws ! k"
            by (metis in_set_conv_nth)
          have Wc_k: "W \<in> carrier_mat d n"
            using W_eq Ws_c \<open>W \<in> set Ws\<close> by simp
          show "(W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
                W $$ (i, a) * cnj (W $$ (j, b))"
            using conjugation_mat_unit_entry[OF Wc_k a_lt b_lt i_lt j_lt].
        qed
        have "sum_list (map (\<lambda>v. v $ (a*d + i) * cnj (v $ (b*d + j))) vs) =
              sum_list (map (\<lambda>W. W $$ (i, a) * cnj (W $$ (j, b))) Ws)"
          unfolding Ws_def
          using i_lt a_lt j_lt b_lt
          by (induction vs) simp_all
        also have "\<dots> = sum_list (map (\<lambda>W. (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
          using point_eq
          by (intro arg_cong[where f=sum_list] map_cong refl) (metis)
        finally show ?thesis.
      qed
      also have "\<dots> = kraus_map_dim d Ws (mat_unit a b n n) $$ (i, j)"
        using kraus_map_dim_entry_sum_list[OF Ws_c Eab_c i_lt j_lt] by simp
      finally show "\<Phi> (mat_unit a b n n) $$ (i, j) =
                    kraus_map_dim d Ws (mat_unit a b n n) $$ (i, j)" .
    qed
  qed

  \<comment> \<open>Step 2: Extend to all \<open>A \<in> M\<^sub>n\<close> by linearity.\<close>
  have kmd_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws (X + Y) = kraus_map_dim d Ws X + kraus_map_dim d Ws Y"
    using kraus_map_dim_add Ws_c by blast
  have kmd_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m kraus_map_dim d Ws X"
    using kraus_map_dim_smult Ws_c by blast
  have kmd_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws X \<in> carrier_mat d d"
    using kraus_map_dim_carrier Ws_c by blast
  have \<Phi>_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X \<in> carrier_mat d d"
    using range by blast

  have phi_eq: "\<And>A. A \<in> carrier_mat n n \<Longrightarrow>
                \<Phi> A = kraus_map_dim d Ws A"
  proof -
    fix A :: "complex Matrix.mat" assume Ac: "A \<in> carrier_mat n n"
    have lhs: "\<Phi> A = pair_comb \<Phi> A n d (mat_unit_pairs n)"
      using linear_eq_pair_comb[OF linear smult \<Phi>_car Ac npos dpos] .
    have rhs: "kraus_map_dim d Ws A =
               pair_comb (kraus_map_dim d Ws) A n d (mat_unit_pairs n)"
      using linear_eq_pair_comb[OF kmd_add kmd_smult kmd_car Ac npos dpos] .
    \<comment> \<open>Both pair combinations are equal because the basis values agree.\<close>
    have comb_eq:
      "pair_comb \<Phi> A n d (mat_unit_pairs n) =
       pair_comb (kraus_map_dim d Ws) A n d (mat_unit_pairs n)"
    proof -
      have "\<And>ps. (\<forall>p \<in> set ps. fst p < n \<and> snd p < n) \<Longrightarrow>
          pair_comb \<Phi> A n d ps = pair_comb (kraus_map_dim d Ws) A n d ps"
      proof -
        fix ps :: "(nat \<times> nat) list"
        assume ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
        show "pair_comb \<Phi> A n d ps =
              pair_comb (kraus_map_dim d Ws) A n d ps"
          using ps_valid
        proof (induction ps)
          case Nil show ?case by simp
        next
          case (Cons p ps)
          obtain a b where p_eq: "p = (a, b)" by (cases p)
          hence a_lt: "a < n" and b_lt: "b < n"
            using Cons.prems by auto
          have basis_eq: "\<Phi> (mat_unit (fst p) (snd p) n n) =
                          kraus_map_dim d Ws (mat_unit (fst p) (snd p) n n)"
            using match_unit[OF a_lt b_lt] p_eq by simp
          have IH: "pair_comb \<Phi> A n d ps =
                    pair_comb (kraus_map_dim d Ws) A n d ps"
            using Cons by auto
          show ?case using basis_eq IH by simp
        qed
      qed
      moreover have "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
        using mat_unit_pairs_set by auto
      ultimately show ?thesis by blast
    qed
    show "\<Phi> A = kraus_map_dim d Ws A"
      using lhs rhs comb_eq by simp
  qed

  \<comment> \<open>Step 3: Transport CP from the Kraus representation back to \<open>\<Phi>\<close>.\<close>
  have kmd_cp: "completely_positive n d (kraus_map_dim d Ws)"
    using kraus_cp_no_tp[OF Ws_c npos dpos].
  show "completely_positive n d \<Phi>"
    unfolding completely_positive_def p_positive_def
  proof (intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and Xc: "X \<in> carrier_mat (p*n) (p*n)"
       and Xpsd: "psd X"
    have psd_kmd: "psd (amplification n d p (kraus_map_dim d Ws) X)"
      using kmd_cp ppos Xc Xpsd
      by (auto simp: completely_positive_def p_positive_def)
    have amp_eq:
      "amplification n d p \<Phi> X = amplification n d p (kraus_map_dim d Ws) X"
    proof (rule eq_matI)
      show "dim_row (amplification n d p \<Phi> X) =
            dim_row (amplification n d p (kraus_map_dim d Ws) X)"
        by (simp add: amplification_def)
      show "dim_col (amplification n d p \<Phi> X) =
            dim_col (amplification n d p (kraus_map_dim d Ws) X)"
        by (simp add: amplification_def)
    next
      fix i j
      assume "i < dim_row (amplification n d p (kraus_map_dim d Ws) X)"
             "j < dim_col (amplification n d p (kraus_map_dim d Ws) X)"
      hence i_lt: "i < p*d" and j_lt: "j < p*d"
        by (simp_all add: amplification_def)
      have block_c: "block_of_mat n X (i div d) (j div d) \<in> carrier_mat n n"
        by (simp add: block_of_mat_def)
      have phi_kmd:
        "\<Phi> (block_of_mat n X (i div d) (j div d))
         = kraus_map_dim d Ws (block_of_mat n X (i div d) (j div d))"
        using phi_eq[OF block_c].
      show "amplification n d p \<Phi> X $$ (i, j) =
            amplification n d p (kraus_map_dim d Ws) X $$ (i, j)"
        using i_lt j_lt phi_kmd
        by (simp add: amplification_def)
    qed
    show "psd (amplification n d p \<Phi> X)"
      using psd_kmd amp_eq by simp
  qed
qed

text \<open>The sum $\sum_iW_i^*W_i$ over a Kraus list.\<close>

definition sum_wdag_w :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "sum_wdag_w n Ws \<equiv>
     foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Ws (0\<^sub>m n n)"

lemma sum_wdag_w_Nil [simp]: "sum_wdag_w n [] = 0\<^sub>m n n"
  by (simp add: sum_wdag_w_def)

lemma sum_wdag_w_Cons:
  "sum_wdag_w n (W # Ws) = (W\<^sup>\<dagger>) * W + sum_wdag_w n Ws"
  by (simp add: sum_wdag_w_def)

lemma sum_wdag_w_carrier:
  assumes "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "sum_wdag_w n Ws \<in> carrier_mat n n"
  using assms
proof (induction Ws)
  case Nil show ?case by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n" by simp
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have WdW_c: "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n" using Wdag_c Wc by auto
  show ?case
    using WdW_c Cons by (simp add: sum_wdag_w_Cons)
qed

lemma kraus_operators_altdef:
  "kraus_operators n d Ws \<longleftrightarrow>
     (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> sum_wdag_w n Ws = 1\<^sub>m n"
  by (simp add: kraus_operators_def sum_wdag_w_def)

lemma Tr_kraus_map_dim_as_wdagw:
  fixes \<rho> :: "complex Matrix.mat"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and X_c: "\<rho> \<in> carrier_mat n n"
  shows "Tr (kraus_map_dim d Ws \<rho>) = Tr (sum_wdag_w n Ws * \<rho>)"
  using Ws_c
proof (induction Ws)
  case Nil
  have "kraus_map_dim d [] \<rho> = 0\<^sub>m d d" by simp
  hence lhs: "Tr (kraus_map_dim d [] \<rho>) = 0" by simp
  have "sum_wdag_w n [] * \<rho> = 0\<^sub>m n n * \<rho>" by simp
  also have "\<dots> = 0\<^sub>m n n"
    using X_c by (metis left_mult_zero_mat)
  finally have "Tr (sum_wdag_w n [] * \<rho>) = 0" by simp
  thus ?case using lhs by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>Y \<in> set Ws. Y \<in> carrier_mat d n" by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d" using Wc by (rule dagger_carrier)
  have WX_c: "W * \<rho> \<in> carrier_mat d n" using Wc X_c by auto
  have WXWd_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using WX_c Wdag_c by auto
  have km_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' X_c].
  have WdW_c: "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n" using Wdag_c Wc by auto
  have sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Ws_c'].
  have sum_X_c: "sum_wdag_w n Ws * \<rho> \<in> carrier_mat n n"
    using sum_c X_c by auto
  have WdWX_c: "(W\<^sup>\<dagger>) * W * \<rho> \<in> carrier_mat n n"
    using WdW_c X_c by auto

  have tr_cyc:
    "Tr (W * \<rho> * (W\<^sup>\<dagger>)) = Tr ((W\<^sup>\<dagger>) * W * \<rho>)"
  proof -
    have "Tr (W * \<rho> * (W\<^sup>\<dagger>)) = Tr ((W\<^sup>\<dagger>) * (W * \<rho>))"
      using WX_c Wdag_c Wc X_c by (intro Tr_cyclic) auto
    also have "\<dots> = Tr ((W\<^sup>\<dagger>) * W * \<rho>)"
      using Wdag_c Wc X_c by simp
    finally show ?thesis.
  qed

  have IH: "Tr (kraus_map_dim d Ws \<rho>) = Tr (sum_wdag_w n Ws * \<rho>)"
    using Cons.IH[OF Ws_c'].

  have "Tr (kraus_map_dim d (W # Ws) \<rho>)
      = Tr (W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>)"
    by simp
  also have "\<dots> = Tr (W * \<rho> * (W\<^sup>\<dagger>)) + Tr (kraus_map_dim d Ws \<rho>)"
    using WXWd_c km_c by (intro Tr_add) auto
  also have "\<dots> = Tr ((W\<^sup>\<dagger>) * W * \<rho>) + Tr (sum_wdag_w n Ws * \<rho>)"
    using tr_cyc IH by simp
  also have "\<dots> = Tr ((W\<^sup>\<dagger>) * W * \<rho> + sum_wdag_w n Ws * \<rho>)"
    using WdWX_c sum_X_c
    by (metis Tr_add carrier_matD(1) carrier_matD(2))
  also have "(W\<^sup>\<dagger>) * W * \<rho> + sum_wdag_w n Ws * \<rho>
           = ((W\<^sup>\<dagger>) * W + sum_wdag_w n Ws) * \<rho>"
    using WdW_c sum_c X_c by (simp add: add_mult_distrib_mat)
  also have "(W\<^sup>\<dagger>) * W + sum_wdag_w n Ws = sum_wdag_w n (W # Ws)"
    by (simp add: sum_wdag_w_Cons)
  finally show ?case .
qed

text \<open>Its entries are $\bigl(\sum_iW_i^*W_i\bigr)_{ab}=\sum_i\sum_k\overline{(W_i)_{ka}}\,(W_i)_{kb}$; trace
preservation then gives $\sum_iW_i^*W_i=I_n$.\<close>

lemma sum_wdag_w_entry:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and a_lt: "a < n" and b_lt: "b < n"
  shows "sum_wdag_w n Ws $$ (a, b) =
         sum_list (map (\<lambda>W. ((W\<^sup>\<dagger>) * W) $$ (a, b)) Ws)"
  using Ws_c
proof (induction Ws)
  case Nil show ?case using a_lt b_lt by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>Y \<in> set Ws. Y \<in> carrier_mat d n" by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d" using Wc by (rule dagger_carrier)
  have WdW_c: "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n" using Wdag_c Wc by auto
  have sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Ws_c'].
  have IH: "sum_wdag_w n Ws $$ (a, b) =
            sum_list (map (\<lambda>W. ((W\<^sup>\<dagger>) * W) $$ (a, b)) Ws)"
    using Cons.IH[OF Ws_c'].
  have "sum_wdag_w n (W # Ws) $$ (a, b)
      = ((W\<^sup>\<dagger>) * W + sum_wdag_w n Ws) $$ (a, b)"
    by (simp add: sum_wdag_w_Cons)
  also have "\<dots> = ((W\<^sup>\<dagger>) * W) $$ (a, b) + sum_wdag_w n Ws $$ (a, b)"
    using WdW_c sum_c a_lt b_lt by simp
  also have "\<dots> = ((W\<^sup>\<dagger>) * W) $$ (a, b)
               + sum_list (map (\<lambda>W. ((W\<^sup>\<dagger>) * W) $$ (a, b)) Ws)"
    using IH by simp
  finally show ?case by simp
qed

text \<open>Pairing with a matrix unit picks out an entry: $\Tr(XE_{ab})=x_{ba}$.\<close>

lemma Tr_mult_mat_unit:
  assumes M_c: "M \<in> carrier_mat n n"
      and a_lt: "a < n" and b_lt: "b < n"
  shows "Tr (M * mat_unit a b n n) = M $$ (b, a)"
proof -
  let ?E = "mat_unit a b n n"
  have E_c: "?E \<in> carrier_mat n n" by (simp add: mat_unit_def)
  have ME_c: "M * ?E \<in> carrier_mat n n" using M_c E_c by auto
  have "Tr (M * ?E) = (\<Sum>i<n. (M * ?E) $$ (i, i))"
    using ME_c by (auto simp: Tr_def)
  also have "\<dots> = (\<Sum>i<n.
        (\<Sum>k<n. M $$ (i, k) * ?E $$ (k, i)))"
  proof (intro sum.cong refl)
    fix i assume "i \<in> {..<n}"
    hence i_lt: "i < n" by simp
    have i_M: "i < dim_row M" using M_c i_lt by auto
    have i_E: "i < dim_col ?E" using E_c i_lt by auto
    have "(M * ?E) $$ (i, i) = Matrix.row M i \<bullet> Matrix.col ?E i"
      using index_mult_mat(1)[OF i_M i_E] .
    also have "\<dots> = (\<Sum>k<n. Matrix.row M i $ k * Matrix.col ?E i $ k)"
      unfolding scalar_prod_def using M_c
      by (simp add: atLeast0LessThan)
    also have "\<dots> = (\<Sum>k<n. M $$ (i, k) * ?E $$ (k, i))"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {..<n}"
      hence k_lt: "k < n" by simp
      have row: "Matrix.row M i $ k = M $$ (i, k)"
        using i_M k_lt M_c by simp
      have col: "Matrix.col ?E i $ k = ?E $$ (k, i)"
        using E_c k_lt i_lt by simp
      show "Matrix.row M i $ k * Matrix.col ?E i $ k = M $$ (i, k) * ?E $$ (k, i)"
        using row col by simp
    qed
    finally show "(M * ?E) $$ (i, i) = (\<Sum>k<n. M $$ (i, k) * ?E $$ (k, i))".
  qed
  also have "\<dots> = (\<Sum>i<n.
        (\<Sum>k<n. M $$ (i, k) * (if k = a \<and> i = b then 1 else 0)))"
    by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>i<n.
        (if i = b then M $$ (i, a) else 0))"
  proof (intro sum.cong refl)
    fix i assume "i \<in> {..<n}"
    hence i_lt: "i < n" by simp
    show "(\<Sum>k<n. M $$ (i, k) * (if k = a \<and> i = b then 1 else 0))
        = (if i = b then M $$ (i, a) else 0)"
    proof (cases "i = b")
      case True
      have "(\<Sum>k<n. M $$ (i, k) * (if k = a \<and> i = b then 1 else 0))
          = (\<Sum>k<n. if k = a then M $$ (i, k) else 0)"
        using True by (intro sum.cong refl, simp)
      also have "\<dots> = M $$ (i, a)"
        using a_lt by simp
      finally show ?thesis using True by simp
    next
      case False
      thus ?thesis by (simp cong: sum.cong)
    qed
  qed
  also have "\<dots> = M $$ (b, a)"
    using b_lt by simp
  finally show ?thesis.
qed

theorem choi_kraus_cptp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
  shows "(completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>) \<longleftrightarrow>
         (\<exists>Ws :: complex Matrix.mat list.
            kraus_operators n d Ws \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X))"
proof
  \<comment> \<open>Direction \<open>\<Longleftarrow>\<close>: a Kraus representation yields a CP trace-preserving map.\<close>
  assume "\<exists>Ws :: complex Matrix.mat list.
            kraus_operators n d Ws \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
  then obtain Ws where
        Ws_kraus: "kraus_operators n d Ws"
    and phi_eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X"
    by blast
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    using Ws_kraus by (simp add: kraus_operators_def)
  have Ws_sum: "sum_wdag_w n Ws = 1\<^sub>m n"
    using Ws_kraus by (simp add: kraus_operators_altdef)

  \<comment> \<open>CP: transport from \<open>kraus_is_cp\<close> through the agreement on \<open>M\<^sub>n\<close>.\<close>
  have kmd_cp: "completely_positive n d (kraus_map_dim d Ws)"
    using kraus_is_cp[OF Ws_kraus npos dpos] .
  have cp_\<Phi>: "completely_positive n d \<Phi>"
    unfolding completely_positive_def p_positive_def
  proof (intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and Xc: "X \<in> carrier_mat (p*n) (p*n)"
       and Xpsd: "psd X"
    have psd_kmd: "psd (amplification n d p (kraus_map_dim d Ws) X)"
      using kmd_cp ppos Xc Xpsd
      by (auto simp: completely_positive_def p_positive_def)
    have amp_eq:
      "amplification n d p \<Phi> X = amplification n d p (kraus_map_dim d Ws) X"
    proof (rule eq_matI)
      show "dim_row (amplification n d p \<Phi> X) =
            dim_row (amplification n d p (kraus_map_dim d Ws) X)"
        by (simp add: amplification_def)
      show "dim_col (amplification n d p \<Phi> X) =
            dim_col (amplification n d p (kraus_map_dim d Ws) X)"
        by (simp add: amplification_def)
    next
      fix i j
      assume "i < dim_row (amplification n d p (kraus_map_dim d Ws) X)"
             "j < dim_col (amplification n d p (kraus_map_dim d Ws) X)"
      hence i_lt: "i < p*d" and j_lt: "j < p*d"
        by (simp_all add: amplification_def)
      have block_c: "block_of_mat n X (i div d) (j div d) \<in> carrier_mat n n"
        by (simp add: block_of_mat_def)
      have "\<Phi> (block_of_mat n X (i div d) (j div d))
          = kraus_map_dim d Ws (block_of_mat n X (i div d) (j div d))"
        using phi_eq block_c by simp
      thus "amplification n d p \<Phi> X $$ (i, j) =
            amplification n d p (kraus_map_dim d Ws) X $$ (i, j)"
        using i_lt j_lt by (simp add: amplification_def)
    qed
    show "psd (amplification n d p \<Phi> X)"
      using psd_kmd amp_eq by simp
  qed

  \<comment> \<open>TP: use \<open>Tr (\<Phi> X) = Tr(\<Sum>W\<^sup>\<dagger>W \<cdot> X) = Tr (1\<^sub>n \<cdot> X) = Tr X\<close>.\<close>
  have tp_\<Phi>: "trace_preserving n \<Phi>"
    unfolding trace_preserving_def
  proof (intro allI impI)
    fix A :: "complex Matrix.mat" assume Ac: "A \<in> carrier_mat n n"
    have "Tr (\<Phi> A) = Tr (kraus_map_dim d Ws A)"
      using phi_eq Ac by simp
    also have "\<dots> = Tr (sum_wdag_w n Ws * A)"
      using Tr_kraus_map_dim_as_wdagw[OF Ws_c Ac].
    also have "\<dots> = Tr (1\<^sub>m n * A)"
      using Ws_sum by simp
    also have "\<dots> = Tr A"
      using Ac by simp
    finally show "Tr (\<Phi> A) = Tr A".
  qed

  show "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>"
    using cp_\<Phi> tp_\<Phi> by simp
next
  \<comment> \<open>Direction \<open>\<Longrightarrow>\<close>: a CP trace-preserving map admits a Kraus form.\<close>
  assume "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>"
  hence cp: "completely_positive n d \<Phi>"
    and tp: "trace_preserving n \<Phi>" by auto
  \<comment> \<open>Step 1: CP implies the Choi matrix is psd.\<close>
  have psdP: "psd (choi_matrix n d \<Phi>)"
    using choi_theorem[OF linear smult range npos dpos] cp by blast
  \<comment> \<open>Step 2: reshape a decomposition of the Choi matrix into a Kraus list.\<close>
  obtain Ws :: "complex Matrix.mat list"
    where Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and phi_eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos psdP]
    by blast
  \<comment> \<open>Step 3: trace preservation forces \<open>sum_wdag_w\<close> n Ws = \<open>1_n\<close>.\<close>
  have sum_is_one: "sum_wdag_w n Ws = 1\<^sub>m n"
  proof (rule eq_matI)
    have sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
      using sum_wdag_w_carrier[OF Ws_c].
    show "dim_row (sum_wdag_w n Ws) = dim_row (1\<^sub>m n)"
      using sum_c by auto
    show "dim_col (sum_wdag_w n Ws) = dim_col (1\<^sub>m n)"
      using sum_c by auto
  next
    fix a b
    assume a_in: "a < dim_row (1\<^sub>m n)"
       and b_in: "b < dim_col (1\<^sub>m n)"
    hence a_lt: "a < n" and b_lt: "b < n" by auto
    let ?E = "mat_unit b a n n"
    have E_c: "?E \<in> carrier_mat n n" by (simp add: mat_unit_def)
    have sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
      using sum_wdag_w_carrier[OF Ws_c].
    have one_c: "1\<^sub>m n \<in> carrier_mat n n" by simp
    \<comment> \<open>Pair both sides with the \<open>mat_unit\<close> (b,a) and compare through Tr.\<close>
    have lhs: "sum_wdag_w n Ws $$ (a, b) = Tr (sum_wdag_w n Ws * ?E)"
      using Tr_mult_mat_unit[OF sum_c b_lt a_lt] by simp
    have rhs: "1\<^sub>m n $$ (a, b) = Tr (1\<^sub>m n * ?E)"
      using Tr_mult_mat_unit[OF one_c b_lt a_lt] by simp
    have "Tr (sum_wdag_w n Ws * ?E) = Tr (kraus_map_dim d Ws ?E)"
      using Tr_kraus_map_dim_as_wdagw[OF Ws_c E_c] by simp
    also have "\<dots> = Tr (\<Phi> ?E)"
      using phi_eq E_c by simp
    also have "\<dots> = Tr ?E"
      using tp E_c by (simp add: trace_preserving_def)
    also have "\<dots> = Tr (1\<^sub>m n * ?E)"
      using E_c by simp
    finally have "Tr (sum_wdag_w n Ws * ?E) = Tr (1\<^sub>m n * ?E)" .
    thus "sum_wdag_w n Ws $$ (a, b) = 1\<^sub>m n $$ (a, b)"
      using lhs rhs by simp
  qed
  \<comment> \<open>Step 4: package the Kraus list.\<close>
  have kraus: "kraus_operators n d Ws"
    unfolding kraus_operators_altdef using Ws_c sum_is_one by simp
  show "\<exists>Ws :: complex Matrix.mat list.
          kraus_operators n d Ws \<and>
          (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
    using kraus phi_eq by blast
qed

lemma kraus_lin_on:
  assumes "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "lin_on n d (carrier_mat n n) (kraus_map_dim d Ws)"
  unfolding lin_on_def using assms
  by (auto intro: kraus_map_dim_carrier kraus_map_dim_add kraus_map_dim_smult)

lemma sum_wdag_w_append:
  fixes Ws Vs :: "complex Matrix.mat list"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "sum_wdag_w n (Ws @ Vs)
         = sum_wdag_w n Ws + sum_wdag_w n Vs"
  using Ws_c
proof (induction Ws)
  case Nil
  have Vs_sum_c: "sum_wdag_w n Vs \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Vs_c] .
  show ?case
    using Vs_sum_c
    by (intro eq_matI) (auto simp: sum_wdag_w_def)
next
  case (Cons W Ws)
  hence W_c: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n" by auto
  have Wd_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  have WdW_c: "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n"
    using Wd_c W_c by (rule mult_carrier_mat)
  have Ws_sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Ws_c'] .
  have Vs_sum_c: "sum_wdag_w n Vs \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Vs_c] .
  have IH: "sum_wdag_w n (Ws @ Vs)
              = sum_wdag_w n Ws + sum_wdag_w n Vs"
    using Cons.IH Ws_c' by simp

  have "sum_wdag_w n ((W # Ws) @ Vs)
          = (W\<^sup>\<dagger>) * W + sum_wdag_w n (Ws @ Vs)"
    by (simp add: sum_wdag_w_Cons)
  also have "\<dots> = (W\<^sup>\<dagger>) * W + (sum_wdag_w n Ws + sum_wdag_w n Vs)"
    using IH by simp
  also have "\<dots> = ((W\<^sup>\<dagger>) * W + sum_wdag_w n Ws) + sum_wdag_w n Vs"
    using WdW_c Ws_sum_c Vs_sum_c
    by simp
  also have "\<dots> = sum_wdag_w n (W # Ws) + sum_wdag_w n Vs"
    by (simp add: sum_wdag_w_Cons)
  finally show ?case.
qed

lemma kraus_is_trace_preserving:
  fixes Ws :: "complex Matrix.mat list"
  assumes Ws: "kraus_operators n d Ws"
  shows "trace_preserving n (kraus_map_dim d Ws)"
proof (unfold trace_preserving_def, intro allI impI)
  fix \<rho> :: "complex Matrix.mat"
  assume \<rho>_c: "\<rho> \<in> carrier_mat n n"
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    using Ws by (simp add: kraus_operators_def)
  have sum_eq: "sum_wdag_w n Ws = 1\<^sub>m n"
    using Ws by (simp add: kraus_operators_altdef)
  have "Tr (kraus_map_dim d Ws \<rho>) = Tr (sum_wdag_w n Ws * \<rho>)"
    using Tr_kraus_map_dim_as_wdagw[OF Ws_c \<rho>_c] .
  also have "\<dots> = Tr ((1\<^sub>m n) * \<rho>)" using sum_eq by simp
  also have "\<dots> = Tr \<rho>" using \<rho>_c by simp
  finally show "Tr (kraus_map_dim d Ws \<rho>) = Tr \<rho>" .
qed

end
