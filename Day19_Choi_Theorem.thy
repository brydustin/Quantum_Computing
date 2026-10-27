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
and \<open>choi_unital_iff\<close> below.\<close>

definition choi_matrix :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "choi_matrix n d \<Phi> \<equiv>
     Matrix.mat (n*d) (n*d)
       (\<lambda>(r,c). \<Phi> (mat_unit (r div d) (c div d) n n) $$ (r mod d, c mod d))"

notation choi_matrix ("P\<^sub>\<Phi>")

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

subsection \<open>Composition of Kraus maps\<close>

definition kraus_compose :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "kraus_compose As Es = concat (map (\<lambda>E. map (\<lambda>A. A * E) As) Es)"

lemma kraus_compose_Nil [simp]: "kraus_compose As [] = []"
  by (simp add: kraus_compose_def)

lemma kraus_compose_Cons: "kraus_compose As (E # Es) = map (\<lambda>A. A * E) As @ kraus_compose As Es"
  by (simp add: kraus_compose_def)

lemma length_kraus_compose [simp]: "length (kraus_compose As Es) = length Es * length As"
  by (induction Es) (simp_all add: kraus_compose_Cons)

text \<open>Composing Kraus maps multiplies their operators: for $\mathcal E(X)=\sum_iE_iXE_i^*$ and
$\mathcal A(Y)=\sum_lA_lYA_l^*$,
\[ (\mathcal A\circ\mathcal E)(X)=\sum_{i,l}(A_lE_i)\,X\,(A_lE_i)^*, \]
and if both are trace preserving then
$\sum_{i,l}(A_lE_i)^*(A_lE_i)=\sum_iE_i^*\bigl(\sum_lA_l^*A_l\bigr)E_i=\sum_iE_i^*E_i=I$.\<close>

lemma kraus_compose_nth:
  assumes i: "i < length Es" and l: "l < length As"
  shows "kraus_compose As Es ! (i * length As + l) = As ! l * Es ! i"
  using i
proof (induction Es arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons E Es)
  show ?case
  proof (cases i)
    case 0 thus ?thesis using l by (simp add: kraus_compose_Cons nth_append)
  next
    case (Suc i')
    hence "i * length As + l = length As + (i' * length As + l)" by simp
    thus ?thesis using Suc Cons by (simp add: kraus_compose_Cons nth_append)
  qed
qed

lemma kraus_compose_carrier:
  assumes "\<forall>A \<in> set As. A \<in> carrier_mat m d" and "\<forall>E \<in> set Es. E \<in> carrier_mat d n"
  shows "\<forall>W \<in> set (kraus_compose As Es). W \<in> carrier_mat m n"
  using assms by (auto simp: kraus_compose_def)

lemma kraus_map_dim_map_mult_right:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and Ec: "E \<in> carrier_mat d n" and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim m (map (\<lambda>A. A * E) As) M = kraus_map_dim m As (E * M * (E\<^sup>\<dagger>))"
  using As_c
proof (induction As)
  case Nil show ?case by simp
next
  case (Cons A As)
  have Ac: "A \<in> carrier_mat m d" using Cons.prems by simp
  have Adc: "A\<^sup>\<dagger> \<in> carrier_mat d m" and Edc: "E\<^sup>\<dagger> \<in> carrier_mat n d"
    by (rule dagger_carrier[OF Ac]) (rule dagger_carrier[OF Ec])
  have dag: "(A * E)\<^sup>\<dagger> = (E\<^sup>\<dagger>) * (A\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp only: carrier_matD[OF Ac] carrier_matD[OF Ec])
  have "(A * E) * M * ((A * E)\<^sup>\<dagger>) = ((A * E) * M) * ((E\<^sup>\<dagger>) * (A\<^sup>\<dagger>))" by (simp only: dag)
  also have "\<dots> = (A * (E * M)) * ((E\<^sup>\<dagger>) * (A\<^sup>\<dagger>))" by (simp only: assoc_mult_mat[OF Ac Ec Xc])
  also have "\<dots> = A * ((E * M) * ((E\<^sup>\<dagger>) * (A\<^sup>\<dagger>)))"
    by (rule assoc_mult_mat[OF Ac mult_carrier_mat[OF Ec Xc] mult_carrier_mat[OF Edc Adc]])
  also have "\<dots> = A * (((E * M) * (E\<^sup>\<dagger>)) * (A\<^sup>\<dagger>))"
    by (simp only: assoc_mult_mat[OF mult_carrier_mat[OF Ec Xc] Edc Adc, symmetric])
  also have "\<dots> = A * (E * M * (E\<^sup>\<dagger>)) * (A\<^sup>\<dagger>)"
    by (rule assoc_mult_mat[OF Ac mult_carrier_mat[OF mult_carrier_mat[OF Ec Xc] Edc] Adc, symmetric])
  finally have "(A * E) * M * ((A * E)\<^sup>\<dagger>) = A * (E * M * (E\<^sup>\<dagger>)) * (A\<^sup>\<dagger>)" .
  thus ?case using Cons by simp
qed

lemma kraus_map_dim_compose:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat d n"
      and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim m (kraus_compose As Es) M = kraus_map_dim m As (kraus_map_dim d Es M)"
  using Es_c
proof (induction Es)
  case Nil show ?case using As_c by (simp add: kraus_map_dim_zero)
next
  case (Cons E Es)
  have Ec: "E \<in> carrier_mat d n" and Es_c': "\<forall>E \<in> set Es. E \<in> carrier_mat d n" using Cons.prems by auto
  have c1: "\<forall>W \<in> set (map (\<lambda>A. A * E) As). W \<in> carrier_mat m n" using As_c Ec by auto
  have c2: "\<forall>W \<in> set (kraus_compose As Es). W \<in> carrier_mat m n" by (rule kraus_compose_carrier[OF As_c Es_c'])
  have EXE: "E * M * (E\<^sup>\<dagger>) \<in> carrier_mat d d" using Ec Xc dagger_carrier[OF Ec] by auto
  have kc: "kraus_map_dim d Es M \<in> carrier_mat d d" by (rule kraus_map_dim_carrier[OF Es_c' Xc])
  have "kraus_map_dim m (kraus_compose As (E # Es)) M
        = kraus_map_dim m As (E * M * (E\<^sup>\<dagger>)) + kraus_map_dim m As (kraus_map_dim d Es M)"
    unfolding kraus_compose_Cons kraus_map_dim_append[OF c1 c2 Xc]
    using kraus_map_dim_map_mult_right[OF As_c Ec Xc] Cons.IH[OF Es_c'] by simp
  also have "\<dots> = kraus_map_dim m As (E * M * (E\<^sup>\<dagger>) + kraus_map_dim d Es M)"
    by (rule kraus_map_dim_add[OF EXE kc As_c, symmetric])
  finally show ?case by simp
qed

lemma sum_wdag_w_map_mult_right:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and Ec: "E \<in> carrier_mat d n"
  shows "sum_wdag_w n (map (\<lambda>A. A * E) As) = (E\<^sup>\<dagger>) * sum_wdag_w d As * E"
  using As_c
proof (induction As)
  case Nil show ?case using Ec dagger_carrier[OF Ec] by simp
next
  case (Cons A As)
  have Ac: "A \<in> carrier_mat m d" and As_c': "\<forall>A \<in> set As. A \<in> carrier_mat m d" using Cons.prems by auto
  have sc: "sum_wdag_w d As \<in> carrier_mat d d" by (rule sum_wdag_w_carrier[OF As_c'])
  have AA: "(A\<^sup>\<dagger>) * A \<in> carrier_mat d d" using Ac dagger_carrier[OF Ac] by auto
  have Adc: "A\<^sup>\<dagger> \<in> carrier_mat d m" and Edc: "E\<^sup>\<dagger> \<in> carrier_mat n d"
    by (rule dagger_carrier[OF Ac]) (rule dagger_carrier[OF Ec])
  have dag: "(A * E)\<^sup>\<dagger> = (E\<^sup>\<dagger>) * (A\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp only: carrier_matD[OF Ac] carrier_matD[OF Ec])
  have "((A * E)\<^sup>\<dagger>) * (A * E) = ((E\<^sup>\<dagger>) * (A\<^sup>\<dagger>)) * (A * E)" by (simp only: dag)
  also have "\<dots> = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * (A * E))" by (rule assoc_mult_mat[OF Edc Adc mult_carrier_mat[OF Ac Ec]])
  also have "\<dots> = (E\<^sup>\<dagger>) * (((A\<^sup>\<dagger>) * A) * E)" by (simp only: assoc_mult_mat[OF Adc Ac Ec, symmetric])
  also have "\<dots> = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) * E"
    by (rule assoc_mult_mat[OF Edc mult_carrier_mat[OF Adc Ac] Ec, symmetric])
  finally have key: "((A * E)\<^sup>\<dagger>) * (A * E) = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) * E" .
  have "((A * E)\<^sup>\<dagger>) * (A * E) + (E\<^sup>\<dagger>) * sum_wdag_w d As * E
        = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) * E + (E\<^sup>\<dagger>) * sum_wdag_w d As * E" by (simp only: key)
  also have "\<dots> = ((E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) + (E\<^sup>\<dagger>) * sum_wdag_w d As) * E"
    by (rule add_mult_distrib_mat[OF mult_carrier_mat[OF Edc AA] mult_carrier_mat[OF Edc sc] Ec, symmetric])
  also have "(E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) + (E\<^sup>\<dagger>) * sum_wdag_w d As = (E\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A + sum_wdag_w d As)"
    by (rule mult_add_distrib_mat[OF Edc AA sc, symmetric])
  finally show ?case unfolding list.map sum_wdag_w_Cons Cons.IH[OF As_c'] .
qed

lemma sum_wdag_w_compose:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat d n"
      and As_tp: "sum_wdag_w d As = 1\<^sub>m d"
  shows "sum_wdag_w n (kraus_compose As Es) = sum_wdag_w n Es"
  using Es_c
proof (induction Es)
  case Nil show ?case by simp
next
  case (Cons E Es)
  have Ec: "E \<in> carrier_mat d n" and Es_c': "\<forall>E \<in> set Es. E \<in> carrier_mat d n" using Cons.prems by auto
  have c1: "\<forall>W \<in> set (map (\<lambda>A. A * E) As). W \<in> carrier_mat m n" using As_c Ec by auto
  have c2: "\<forall>W \<in> set (kraus_compose As Es). W \<in> carrier_mat m n" by (rule kraus_compose_carrier[OF As_c Es_c'])
  have "sum_wdag_w n (kraus_compose As (E # Es)) = (E\<^sup>\<dagger>) * E + sum_wdag_w n (kraus_compose As Es)"
    unfolding kraus_compose_Cons sum_wdag_w_append[OF c1 c2] sum_wdag_w_map_mult_right[OF As_c Ec] As_tp
    using Ec dagger_carrier[OF Ec] by simp
  thus ?case using Cons.IH[OF Es_c'] by (simp add: sum_wdag_w_Cons)
qed

lemma kraus_operators_compose:
  assumes As: "kraus_operators d m As" and Es: "kraus_operators n d Es"
  shows "kraus_operators n m (kraus_compose As Es)"
proof -
  have As_c: "\<forall>A \<in> set As. A \<in> carrier_mat m d" and As_tp: "sum_wdag_w d As = 1\<^sub>m d"
    using As by (auto simp: kraus_operators_altdef)
  have Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat d n" and Es_tp: "sum_wdag_w n Es = 1\<^sub>m n"
    using Es by (auto simp: kraus_operators_altdef)
  show ?thesis
    unfolding kraus_operators_altdef
    using kraus_compose_carrier[OF As_c Es_c] sum_wdag_w_compose[OF As_c Es_c As_tp] Es_tp by simp
qed

subsection \<open>Vectorisation of Kraus operators\<close>

text \<open>The vectorisation of $V\in M_{d,n}$ stacks its columns: the vector in $\C^{nd}$ with entry
$V_{r\bmod d,\;r\div d}$ at position $r$.\<close>

definition vec_of_kraus :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec"
  where
  "vec_of_kraus d n V = Matrix.vec (n*d) (\<lambda>r. V $$ (r mod d, r div d))"

lemma vec_of_kraus_dim [simp]: "dim_vec (vec_of_kraus d n V) = n*d"
  by (simp add: vec_of_kraus_def)

lemma vec_of_kraus_index:
  assumes r_lt: "r < n*d"
  shows "vec_of_kraus d n V $ r = V $$ (r mod d, r div d)"
  using r_lt by (simp add: vec_of_kraus_def)

text \<open>At position $ad+i$ it holds $V_{ia}$.\<close>

lemma vec_of_kraus_combined_index:
  assumes V_c: "V \<in> carrier_mat d n"
      and a_lt: "a < n" and i_lt: "i < d" and dpos: "0 < d"
  shows "vec_of_kraus d n V $ (a*d + i) = V $$ (i, a)"
proof -
  have lt: "a*d + i < n*d"
  proof -
    have "a*d + i < a*d + d" using i_lt by simp
    also have "\<dots> = Suc a * d" by simp
    also have "\<dots> \<le> n * d"
      using a_lt by (intro mult_le_mono1) simp
    finally show ?thesis .
  qed
  have d_div: "(a*d + i) div d = a" using i_lt dpos by simp
  have d_mod: "(a*d + i) mod d = i" using i_lt dpos by simp
  show ?thesis using lt d_div d_mod by (simp add: vec_of_kraus_def)
qed


subsection \<open>Choi matrix of a Kraus map\<close>

text \<open>The Choi matrix of a Kraus map is the outer sum of the vectorised Kraus operators:
\[ \Phi(X)=\sum_iV_iXV_i^*\quad\Longrightarrow\quad P_\Phi=\sum_iv_iv_i^*,\qquad v_i=\mathrm{vec}(V_i), \]
so its range is spanned by the $v_i$.\<close>

lemma kraus_map_dim_mat_unit_entry:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and a_lt: "a < n" and b_lt: "b < n"
      and i_lt: "i < d" and j_lt: "j < d"
  shows "(kraus_map_dim d Vs (mat_unit a b n n)) $$ (i, j)
           = (\<Sum>k<length Vs. Vs!k $$ (i, a) * cnj (Vs!k $$ (j, b)))"
  using Vs_c
proof (induction Vs)
  case Nil
  show ?case using i_lt j_lt by simp
next
  case (Cons V Vs)
  from Cons.prems have V_c: "V \<in> carrier_mat d n" by simp
  from Cons.prems have rest_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" by simp
  have IH: "(kraus_map_dim d Vs (mat_unit a b n n)) $$ (i, j)
              = (\<Sum>k<length Vs. Vs!k $$ (i, a) * cnj (Vs!k $$ (j, b)))"
    by (rule Cons.IH[OF rest_c])
  have rest_c': "kraus_map_dim d Vs (mat_unit a b n n) \<in> carrier_mat d d"
    by (rule kraus_map_dim_carrier[OF rest_c]) (simp add: mat_unit_def)
  have term_c: "V * mat_unit a b n n * (V\<^sup>\<dagger>) \<in> carrier_mat d d"
    using V_c by (auto simp: mat_unit_def)
  have i_dim: "i < dim_row (V * mat_unit a b n n * (V\<^sup>\<dagger>))"
    using term_c i_lt by auto
  have j_dim: "j < dim_col (V * mat_unit a b n n * (V\<^sup>\<dagger>))"
    using term_c j_lt by auto
  have "(kraus_map_dim d (V # Vs) (mat_unit a b n n)) $$ (i, j)
          = (V * mat_unit a b n n * (V\<^sup>\<dagger>) + kraus_map_dim d Vs (mat_unit a b n n))
              $$ (i, j)" by simp
  also have "\<dots> = (V * mat_unit a b n n * (V\<^sup>\<dagger>)) $$ (i, j)
                   + (kraus_map_dim d Vs (mat_unit a b n n)) $$ (i, j)"
    using index_add_mat(1)[OF i_dim j_dim] term_c rest_c' i_lt j_lt by auto
  also have "(V * mat_unit a b n n * (V\<^sup>\<dagger>)) $$ (i, j) = V $$ (i, a) * cnj (V $$ (j, b))"
    by (rule conjugation_mat_unit_entry[OF V_c a_lt b_lt i_lt j_lt])
  also have "V $$ (i, a) * cnj (V $$ (j, b))
               + (kraus_map_dim d Vs (mat_unit a b n n)) $$ (i, j)
              = V $$ (i, a) * cnj (V $$ (j, b))
                + (\<Sum>k<length Vs. Vs!k $$ (i, a) * cnj (Vs!k $$ (j, b)))"
    using IH by simp
  also have "\<dots> = (\<Sum>k<length (V # Vs).
                     (V # Vs)!k $$ (i, a) * cnj ((V # Vs)!k $$ (j, b)))"
  proof -
    have len: "length (V # Vs) = Suc (length Vs)" by simp
    have "(\<Sum>k<length (V # Vs).
              (V # Vs)!k $$ (i, a) * cnj ((V # Vs)!k $$ (j, b)))
            = (\<Sum>k<Suc (length Vs).
                  (V # Vs)!k $$ (i, a) * cnj ((V # Vs)!k $$ (j, b)))"
      using len by simp
    also have "\<dots> = (V # Vs)!0 $$ (i, a) * cnj ((V # Vs)!0 $$ (j, b))
                    + (\<Sum>k<length Vs.
                          (V # Vs)!(Suc k) $$ (i, a)
                            * cnj ((V # Vs)!(Suc k) $$ (j, b)))"
      by (rule sum.lessThan_Suc_shift)
    also have "\<dots> = V $$ (i, a) * cnj (V $$ (j, b))
                    + (\<Sum>k<length Vs. Vs!k $$ (i, a) * cnj (Vs!k $$ (j, b)))"
      by simp
    finally show ?thesis by simp
  qed
  finally show ?case .
qed

lemma choi_matrix_kraus_eq:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and npos: "0 < n" and dpos: "0 < d"
  shows "choi_matrix n d (kraus_map_dim d Vs)
           = outer_sum (n*d) (map (vec_of_kraus d n) Vs)"
proof (rule eq_matI)
  let ?vs = "map (vec_of_kraus d n) Vs"
  let ?V = "mat_of_cols (n*d) ?vs"
  have V_c: "?V \<in> carrier_mat (n*d) (length Vs)"
    by (simp add: mat_of_cols_def)
  have Vdag_c: "?V\<^sup>\<dagger> \<in> carrier_mat (length Vs) (n*d)"
    using V_c by (rule dagger_carrier)
  have out_c: "outer_sum (n*d) ?vs \<in> carrier_mat (n*d) (n*d)"
    unfolding outer_sum_def using V_c Vdag_c by auto
  show "dim_row (choi_matrix n d (kraus_map_dim d Vs))
          = dim_row (outer_sum (n*d) ?vs)"
    by (simp add: choi_matrix_def)
  show "dim_col (choi_matrix n d (kraus_map_dim d Vs))
          = dim_col (outer_sum (n*d) ?vs)"
    by (simp add: choi_matrix_def)
next
  let ?vs = "map (vec_of_kraus d n) Vs"
  let ?V = "mat_of_cols (n*d) ?vs"
  fix r c
  assume r_a: "r < dim_row (outer_sum (n*d) ?vs)"
     and c_a: "c < dim_col (outer_sum (n*d) ?vs)"
  hence r_lt: "r < n*d" and c_lt: "c < n*d" by auto
  have a_lt: "r div d < n" using r_lt dpos by (simp add: div_less_iff_less_mult)
  have b_lt: "c div d < n" using c_lt dpos by (simp add: div_less_iff_less_mult)
  have i_lt: "r mod d < d" using dpos by simp
  have j_lt: "c mod d < d" using dpos by simp
  have V_c: "?V \<in> carrier_mat (n*d) (length Vs)"
    by (simp add: mat_of_cols_def)
  have Vdag_c: "?V\<^sup>\<dagger> \<in> carrier_mat (length Vs) (n*d)"
    using V_c by (rule dagger_carrier)
  have rrow: "r < dim_row ?V" using V_c r_lt by auto
  have ccol: "c < dim_col (?V\<^sup>\<dagger>)" using Vdag_c c_lt by auto
  have "choi_matrix n d (kraus_map_dim d Vs) $$ (r, c)
          = kraus_map_dim d Vs (mat_unit (r div d) (c div d) n n)
              $$ (r mod d, c mod d)"
    using r_lt c_lt by (simp add: choi_matrix_def)
  also have "\<dots> = (\<Sum>k<length Vs.
                    Vs!k $$ (r mod d, r div d) * cnj (Vs!k $$ (c mod d, c div d)))"
    by (rule kraus_map_dim_mat_unit_entry[OF Vs_c a_lt b_lt i_lt j_lt])
  also have "\<dots> = (\<Sum>k<length Vs.
                    vec_of_kraus d n (Vs!k) $ r * cnj (vec_of_kraus d n (Vs!k) $ c))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<length Vs}"
    hence k_lt: "k < length Vs" by simp
    have Vk_c: "Vs!k \<in> carrier_mat d n" using Vs_c k_lt by simp
    have "vec_of_kraus d n (Vs!k) $ r = Vs!k $$ (r mod d, r div d)"
      using r_lt by (simp add: vec_of_kraus_def)
    moreover have "vec_of_kraus d n (Vs!k) $ c = Vs!k $$ (c mod d, c div d)"
      using c_lt by (simp add: vec_of_kraus_def)
    ultimately show
      "Vs!k $$ (r mod d, r div d) * cnj (Vs!k $$ (c mod d, c div d))
        = vec_of_kraus d n (Vs!k) $ r * cnj (vec_of_kraus d n (Vs!k) $ c)"
      by simp
  qed
  also have "\<dots> = (\<Sum>k<length Vs.
                    ?vs!k $ r * cnj (?vs!k $ c))"
    by (rule sum.cong[OF refl]) simp
  also have "\<dots> = outer_sum (n*d) ?vs $$ (r, c)"
  proof -
    have mul_entry: "(?V * (?V\<^sup>\<dagger>)) $$ (r, c)
                       = (\<Sum>k<length Vs.
                            ?V $$ (r, k) * (?V\<^sup>\<dagger>) $$ (k, c))"
    proof -
      have "(?V * (?V\<^sup>\<dagger>)) $$ (r, c)
              = Matrix.row ?V r \<bullet> Matrix.col (?V\<^sup>\<dagger>) c"
        using rrow ccol by (subst index_mult_mat) auto
      also have "\<dots> = (\<Sum>k\<in>{0..<length Vs}.
                          Matrix.row ?V r $ k * Matrix.col (?V\<^sup>\<dagger>) c $ k)"
        unfolding scalar_prod_def using V_c Vdag_c by simp
      also have "\<dots> = (\<Sum>k\<in>{0..<length Vs}.
                          ?V $$ (r, k) * (?V\<^sup>\<dagger>) $$ (k, c))"
      proof (rule sum.cong[OF refl])
        fix k assume "k \<in> {0..<length Vs}"
        hence k_lt: "k < length Vs" by simp
        have rr: "Matrix.row ?V r $ k = ?V $$ (r, k)"
          using rrow V_c k_lt by auto
        have cc: "Matrix.col (?V\<^sup>\<dagger>) c $ k = (?V\<^sup>\<dagger>) $$ (k, c)"
          using ccol Vdag_c k_lt by (simp add: dagger_def mat_of_cols_def)
        show "Matrix.row ?V r $ k * Matrix.col (?V\<^sup>\<dagger>) c $ k
                = ?V $$ (r, k) * (?V\<^sup>\<dagger>) $$ (k, c)"
          using rr cc by simp
      qed
      finally show ?thesis by (simp add: lessThan_atLeast0)
    qed
    have entry_eq: "\<And>k. k < length Vs \<Longrightarrow>
                       ?V $$ (r, k) * (?V\<^sup>\<dagger>) $$ (k, c)
                         = ?vs!k $ r * cnj (?vs!k $ c)"
    proof -
      fix k assume k_lt: "k < length Vs"
      have V_idx: "?V $$ (r, k) = ?vs!k $ r"
        using r_lt k_lt by (simp add: mat_of_cols_def)
      have Vdag_idx: "(?V\<^sup>\<dagger>) $$ (k, c) = cnj (?V $$ (c, k))"
        using V_c c_lt k_lt by (simp add: dagger_def)
      have Vc_idx: "?V $$ (c, k) = ?vs!k $ c"
        using c_lt k_lt by (simp add: mat_of_cols_def)
      show "?V $$ (r, k) * (?V\<^sup>\<dagger>) $$ (k, c)
              = ?vs!k $ r * cnj (?vs!k $ c)"
        using V_idx Vdag_idx Vc_idx by simp
    qed
    have "(\<Sum>k<length Vs. ?vs!k $ r * cnj (?vs!k $ c))
            = (\<Sum>k<length Vs. ?V $$ (r, k) * (?V\<^sup>\<dagger>) $$ (k, c))"
      by (rule sum.cong[OF refl]) (simp add: entry_eq)
    also have "\<dots> = (?V * (?V\<^sup>\<dagger>)) $$ (r, c)"
      using mul_entry by simp
    also have "\<dots> = outer_sum (n*d) ?vs $$ (r, c)"
      by (simp add: outer_sum_def)
    finally show ?thesis .
  qed
  finally show "choi_matrix n d (kraus_map_dim d Vs) $$ (r, c)
                  = outer_sum (n*d) ?vs $$ (r, c)" .
qed


subsection \<open>Choi matrix is linear in the map\<close>

text \<open>The Choi matrix depends linearly on the map: $P_{\Phi-\Psi}=P_\Phi-P_\Psi$.\<close>

lemma choi_matrix_carrier [simp]:
  "choi_matrix n d \<Phi> \<in> carrier_mat (n*d) (n*d)"
  by (simp add: choi_matrix_def)

lemma choi_matrix_diff:
  fixes Phi Psi :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes Phi_range: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> Phi X \<in> carrier_mat d d"
      and Psi_range: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> Psi X \<in> carrier_mat d d"
      and npos: "0 < n" and dpos: "0 < d"
  shows "choi_matrix n d (\<lambda>X. Phi X - Psi X)
           = choi_matrix n d Phi - choi_matrix n d Psi"
proof (rule eq_matI)
  show "dim_row (choi_matrix n d (\<lambda>X. Phi X - Psi X))
          = dim_row (choi_matrix n d Phi - choi_matrix n d Psi)"
    by (simp add: choi_matrix_def)
  show "dim_col (choi_matrix n d (\<lambda>X. Phi X - Psi X))
          = dim_col (choi_matrix n d Phi - choi_matrix n d Psi)"
    by (simp add: choi_matrix_def)
next
  fix r c
  assume r_a: "r < dim_row (choi_matrix n d Phi - choi_matrix n d Psi)"
     and c_a: "c < dim_col (choi_matrix n d Phi - choi_matrix n d Psi)"
  have r_lt: "r < n*d"
    using r_a by (simp add: choi_matrix_def)
  have c_lt: "c < n*d"
    using c_a by (simp add: choi_matrix_def)
  have a_lt: "r div d < n" using r_lt dpos by (simp add: div_less_iff_less_mult)
  have b_lt: "c div d < n" using c_lt dpos by (simp add: div_less_iff_less_mult)
  have i_lt: "r mod d < d" using dpos by simp
  have j_lt: "c mod d < d" using dpos by simp
  let ?E = "mat_unit (r div d) (c div d) n n"
  have E_c: "?E \<in> carrier_mat n n" by (simp add: mat_unit_def)
  have phi_E_c: "Phi ?E \<in> carrier_mat d d" by (rule Phi_range[OF E_c])
  have psi_E_c: "Psi ?E \<in> carrier_mat d d" by (rule Psi_range[OF E_c])
  have "choi_matrix n d (\<lambda>X. Phi X - Psi X) $$ (r, c)
          = (Phi ?E - Psi ?E) $$ (r mod d, c mod d)"
    using r_lt c_lt by (simp add: choi_matrix_def)
  also have "\<dots> = Phi ?E $$ (r mod d, c mod d) - Psi ?E $$ (r mod d, c mod d)"
    using phi_E_c psi_E_c i_lt j_lt by auto
  also have "\<dots> = choi_matrix n d Phi $$ (r, c) - choi_matrix n d Psi $$ (r, c)"
    using r_lt c_lt by (simp add: choi_matrix_def)
  also have "\<dots> = (choi_matrix n d Phi - choi_matrix n d Psi) $$ (r, c)"
    using r_lt c_lt by (simp add: choi_matrix_def)
  finally show "choi_matrix n d (\<lambda>X. Phi X - Psi X) $$ (r, c)
                  = (choi_matrix n d Phi - choi_matrix n d Psi) $$ (r, c)" .
qed

text \<open>The Choi matrix agrees on maps that agree on the carrier.\<close>

lemma choi_matrix_cong:
  assumes agree: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> Phi X = Psi X"
  shows "choi_matrix n d Phi = choi_matrix n d Psi"
proof (rule eq_matI)
  show "dim_row (choi_matrix n d Phi) = dim_row (choi_matrix n d Psi)"
    by (simp add: choi_matrix_def)
  show "dim_col (choi_matrix n d Phi) = dim_col (choi_matrix n d Psi)"
    by (simp add: choi_matrix_def)
next
  fix r c
  assume r_a: "r < dim_row (choi_matrix n d Psi)"
     and c_a: "c < dim_col (choi_matrix n d Psi)"
  have r_lt: "r < n*d" using r_a by (simp add: choi_matrix_def)
  have c_lt: "c < n*d" using c_a by (simp add: choi_matrix_def)
  let ?E = "mat_unit (r div d) (c div d) n n"
  have E_c: "?E \<in> carrier_mat n n" by (simp add: mat_unit_def)
  have "choi_matrix n d Phi $$ (r, c)
          = Phi ?E $$ (r mod d, c mod d)"
    using r_lt c_lt by (simp add: choi_matrix_def)
  also have "\<dots> = Psi ?E $$ (r mod d, c mod d)"
    using agree[OF E_c] by simp
  also have "\<dots> = choi_matrix n d Psi $$ (r, c)"
    using r_lt c_lt by (simp add: choi_matrix_def)
  finally show "choi_matrix n d Phi $$ (r, c) = choi_matrix n d Psi $$ (r, c)" .
qed

subsection \<open>Choi matrix determines a linear CP map on carrier\<close>

text \<open>If two maps that are linear on carrier have the same Choi matrix
and the same target carrier, they agree pointwise on carrier.\<close>

lemma map_eq_from_choi_when_linear:
  fixes Phi Psi :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes Phi_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n
                          \<Longrightarrow> Phi (X + Y) = Phi X + Phi Y"
      and Phi_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow> Phi (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m Phi X"
      and Phi_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> Phi X \<in> carrier_mat d d"
      and Psi_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n
                          \<Longrightarrow> Psi (X + Y) = Psi X + Psi Y"
      and Psi_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow> Psi (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m Psi X"
      and Psi_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> Psi X \<in> carrier_mat d d"
      and choi_eq: "choi_matrix n d Phi = choi_matrix n d Psi"
      and npos: "n > 0" and dpos: "d > 0"
      and A_c: "A \<in> carrier_mat n n"
  shows "Phi A = Psi A"
proof -
  let ?ps = "mat_unit_pairs n"
  \<comment> \<open>Step 1: \<open>Phi(E_{a,b}) = Psi(E_{a,b})\<close> as full matrices via Choi entries.\<close>
  have basis_eq:
    "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> Phi (mat_unit a b n n) = Psi (mat_unit a b n n)"
  proof -
    fix a b assume a_lt: "a < n" and b_lt: "b < n"
    have E_c: "mat_unit a b n n \<in> carrier_mat n n" by (simp add: mat_unit_def)
    have phiE_c: "Phi (mat_unit a b n n) \<in> carrier_mat d d"
      by (rule Phi_car[OF E_c])
    have psiE_c: "Psi (mat_unit a b n n) \<in> carrier_mat d d"
      by (rule Psi_car[OF E_c])
    show "Phi (mat_unit a b n n) = Psi (mat_unit a b n n)"
    proof (rule eq_matI)
      show "dim_row (Phi (mat_unit a b n n)) = dim_row (Psi (mat_unit a b n n))"
        using phiE_c psiE_c by auto
      show "dim_col (Phi (mat_unit a b n n)) = dim_col (Psi (mat_unit a b n n))"
        using phiE_c psiE_c by auto
      fix i j assume i_a: "i < dim_row (Psi (mat_unit a b n n))"
                   and j_a: "j < dim_col (Psi (mat_unit a b n n))"
      have i_lt: "i < d" using i_a psiE_c by auto
      have j_lt: "j < d" using j_a psiE_c by auto
      have idx: "a*d + i < n*d \<and> b*d + j < n*d"
      proof -
        have "a*d + i < a*d + d" using i_lt by simp
        also have "\<dots> = Suc a * d" by simp
        also have "\<dots> \<le> n * d" using a_lt by (intro mult_le_mono1) simp
        finally have "a*d + i < n*d" .
        moreover have "b*d + j < b*d + d" using j_lt by simp
        moreover have "b*d + d = Suc b * d" by simp
        moreover have "Suc b * d \<le> n * d" using b_lt by (intro mult_le_mono1) simp
        ultimately show ?thesis by simp
      qed
      have r_lt: "a*d + i < n*d" using idx by simp
      have c_lt: "b*d + j < n*d" using idx by simp
      have r_div: "(a*d + i) div d = a" using i_lt dpos by simp
      have r_mod: "(a*d + i) mod d = i" using i_lt dpos by simp
      have c_div: "(b*d + j) div d = b" using j_lt dpos by simp
      have c_mod: "(b*d + j) mod d = j" using j_lt dpos by simp
      have "Phi (mat_unit a b n n) $$ (i, j)
              = choi_matrix n d Phi $$ (a*d + i, b*d + j)"
        unfolding choi_matrix_def
        using r_lt c_lt r_div r_mod c_div c_mod by simp
      also have "\<dots> = choi_matrix n d Psi $$ (a*d + i, b*d + j)"
        using choi_eq by simp
      also have "\<dots> = Psi (mat_unit a b n n) $$ (i, j)"
        unfolding choi_matrix_def
        using r_lt c_lt r_div r_mod c_div c_mod by simp
      finally show "Phi (mat_unit a b n n) $$ (i, j)
                       = Psi (mat_unit a b n n) $$ (i, j)" .
    qed
  qed
  have phi_pair: "Phi A = pair_comb Phi A n d ?ps"
    by (rule linear_eq_pair_comb[OF Phi_add Phi_smult Phi_car A_c npos dpos])
  have psi_pair: "Psi A = pair_comb Psi A n d ?ps"
    by (rule linear_eq_pair_comb[OF Psi_add Psi_smult Psi_car A_c npos dpos])
  have pc_eq: "pair_comb Phi A n d ?ps = pair_comb Psi A n d ?ps"
  proof -
    have valid: "\<forall>p \<in> set ?ps. fst p < n \<and> snd p < n"
      using mat_unit_pairs_set by auto
    have aux: "\<And>ps. \<forall>p \<in> set ps. fst p < n \<and> snd p < n
                  \<Longrightarrow> pair_comb Phi A n d ps = pair_comb Psi A n d ps"
    proof -
      fix ps :: "(nat \<times> nat) list"
      assume "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
      thus "pair_comb Phi A n d ps = pair_comb Psi A n d ps"
      proof (induction ps)
        case Nil
        show ?case by simp
      next
        case (Cons p ps')
        obtain a b where p_eq: "p = (a, b)" by (cases p)
        hence a_lt: "a < n" and b_lt: "b < n" using Cons.prems by auto
        have IH: "pair_comb Phi A n d ps' = pair_comb Psi A n d ps'"
          using Cons by simp
        have eq_at_p: "Phi (mat_unit (fst p) (snd p) n n)
                         = Psi (mat_unit (fst p) (snd p) n n)"
          using basis_eq[OF a_lt b_lt] p_eq by simp
        show ?case by (simp add: eq_at_p IH)
      qed
    qed
    show ?thesis using aux[OF valid] .
  qed
  show ?thesis using phi_pair psi_pair pc_eq by simp
qed


subsection \<open>Choi's theorem with (2) isolated (D19-1)\<close>

text \<open>For $f:\{0,\dots,r-1\}\to\{0,\dots,n-1\}$ the block matrix $(E_{f(a)f(b)})_{a,b}\in M_r(M_n)$.
The notes' examples are $f=(i,j)$ with $r=2$, giving $\begin{pmatrix}E_{ii}&E_{ij}\\E_{ji}&E_{jj}\end{pmatrix}$,
and $f=\mathrm{id}$ with $r=n$, giving $(E_{ij})$.\<close>

definition unit_blocks :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "unit_blocks r n f = Matrix.mat (r * n) (r * n)
     (\<lambda>(x, y). if x mod n = f (x div n) \<and> y mod n = f (y div n) then 1 else 0)"

lemma unit_blocks_carrier [simp]: "unit_blocks r n f \<in> carrier_mat (r * n) (r * n)"
  by (simp add: unit_blocks_def)

lemma unit_blocks_block:
  assumes "a < r" "b < r" "f a < n" "f b < n"
  shows "block_of_mat n (unit_blocks r n f) a b = mat_unit (f a) (f b) n n"
proof (rule eq_matI)
  fix k l assume "k < dim_row (mat_unit (f a) (f b) n n)" "l < dim_col (mat_unit (f a) (f b) n n)"
  hence k: "k < n" and l: "l < n" by (simp_all add: mat_unit_def)
  have x: "a * n + k < r * n" and y: "b * n + l < r * n"
    using mult_index_lt assms k l by simp_all
  show "block_of_mat n (unit_blocks r n f) a b $$ (k, l) = mat_unit (f a) (f b) n n $$ (k, l)"
    using k l x y by (auto simp: block_of_mat_def unit_blocks_def mat_unit_def)
qed (simp_all add: block_of_mat_def mat_unit_def)

definition unit_blocks_vec :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.vec" where
  "unit_blocks_vec r n f = Matrix.vec (r * n) (\<lambda>x. if x mod n = f (x div n) then 1 else 0)"

text \<open>The matrix with blocks $E_{f(a)f(b)}$ is $\ketbra uu$ for $u=\sum_ae_a\otimes e_{f(a)}$, hence positive.\<close>

lemma unit_blocks_outer: "unit_blocks r n f = unit_blocks_vec r n f \<oslash> unit_blocks_vec r n f"
proof (rule eq_matI)
  let ?v = "unit_blocks_vec r n f"
  have vd: "dim_vec ?v = r * n" by (simp add: unit_blocks_vec_def)
  fix x y assume "x < dim_row (?v \<oslash> ?v)" "y < dim_col (?v \<oslash> ?v)"
  hence x: "x < r * n" and y: "y < r * n" using carrier_matD[OF outer_prod_carrier[OF vd vd]] by auto
  show "unit_blocks r n f $$ (x, y) = (?v \<oslash> ?v) $$ (x, y)"
    using outer_prod_index[of x ?v y ?v] x y vd by (simp add: unit_blocks_def unit_blocks_vec_def)
qed (use carrier_matD[OF outer_prod_carrier[of "unit_blocks_vec r n f" "r * n" "unit_blocks_vec r n f" "r * n"]]
     in \<open>simp_all add: unit_blocks_def unit_blocks_vec_def\<close>)

lemma unit_blocks_psd: "psd (unit_blocks r n f)"
  unfolding unit_blocks_outer by (rule outer_prod_self_psd) (simp add: unit_blocks_vec_def)

lemma choi_seed_unit_blocks: "choi_seed n = unit_blocks n n id"
proof (rule eq_matI)
  fix x y assume "x < dim_row (unit_blocks n n id)" "y < dim_col (unit_blocks n n id)"
  hence x: "x < n * n" and y: "y < n * n" by (simp_all add: unit_blocks_def)
  have "x div n < n" "y div n < n" "x mod n < n" "y mod n < n"
    using x y by (simp_all add: less_mult_imp_div_less) (cases n; simp)+
  thus "choi_seed n $$ (x, y) = unit_blocks n n id $$ (x, y)"
    using x y by (simp add: choi_seed_def unit_blocks_def)
qed (simp_all add: choi_seed_def unit_blocks_def)

lemma choi_seed_psd: "psd (choi_seed n)"
  unfolding choi_seed_unit_blocks by (rule unit_blocks_psd)

lemma choi_psd_if_n_positive:
  assumes n: "0 < n" and d: "0 < d" and pp: "p_positive n d n \<Phi>"
  shows "psd (choi_matrix n d \<Phi>)"
proof -
  have "choi_seed n \<in> carrier_mat (n * n) (n * n)" by (rule choi_seed_carrier)
  hence "psd (amplification n d n \<Phi> (choi_seed n))" using pp choi_seed_psd by (simp add: p_positive_def)
  thus ?thesis by (simp add: choi_matrix_as_amplification[OF n d])
qed

theorem choi_four_conditions:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult: "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and n: "0 < n" and d: "0 < d"
  shows "(completely_positive n d \<Phi> \<longleftrightarrow> p_positive n d n \<Phi>)
       \<and> (p_positive n d n \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>))
       \<and> (psd (choi_matrix n d \<Phi>) \<longleftrightarrow>
           (\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)))"
proof -
  have cp_choi: "completely_positive n d \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>)"
    by (rule choi_theorem[OF linear smult range n d])
  have np: "p_positive n d n \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>)"
  proof
    assume "p_positive n d n \<Phi>" thus "psd (choi_matrix n d \<Phi>)" by (rule choi_psd_if_n_positive[OF n d])
  next
    assume "psd (choi_matrix n d \<Phi>)"
    hence "completely_positive n d \<Phi>" using cp_choi by simp
    thus "p_positive n d n \<Phi>" using n by (simp add: completely_positive_def)
  qed
  have kraus: "psd (choi_matrix n d \<Phi>) \<longleftrightarrow>
           (\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A))"
  proof
    assume "psd (choi_matrix n d \<Phi>)"
    thus "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
      using kraus_rep_of_psd_choi[OF linear smult range n d] by blast
  next
    assume "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
    then obtain Ws where Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Wk: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A" by blast
    have "completely_positive n d (kraus_map_dim d Ws)" by (rule kraus_cp_no_tp[OF Wc n d])
    hence "completely_positive n d \<Phi>" using completely_positive_cong[of n \<Phi> "kraus_map_dim d Ws" d] Wk by blast
    thus "psd (choi_matrix n d \<Phi>)" using cp_choi by simp
  qed
  have "completely_positive n d \<Phi> \<longleftrightarrow> p_positive n d n \<Phi>" using cp_choi np by simp
  thus ?thesis using np kraus by blast
qed

subsection \<open>Trace preservation and unitality in Choi-matrix form (D19-3)\<close>

text \<open>Day 19, notes (4) and (5) after Choi's theorem: write $P_\Phi=(R_{ij})$ with
$R_{ij}=\Phi(E_{ij})\in M_d$.  Then $\Phi$ is trace preserving iff $\Tr R_{ij}=\delta_{ij}$, and
unital iff $\sum_iR_{ii}=I_d$; with \<open>choi_theorem\<close> this characterises CPTP and UCP maps by
their Choi matrix.  Linearity on $M_n$ is \<^term>\<open>lin_on n d (carrier_mat n n) \<Phi>\<close>.\<close>

lemma choi_block:
  assumes range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d" and i: "i < n" and j: "j < n"
  shows "block_of_mat d (choi_matrix n d \<Phi>) i j = \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)"
proof -
  have c: "\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d" using range by simp
  show ?thesis
  proof (rule eq_matI)
    fix r s assume "r < dim_row (\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>))" "s < dim_col (\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>))"
    hence r: "r < d" and s: "s < d" using c by auto
    have "i * d + r < n * d" "j * d + s < n * d" using mult_index_lt i j r s by auto
    thus "block_of_mat d (choi_matrix n d \<Phi>) i j $$ (r,s) = \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (r,s)"
      using r s by (simp add: block_of_mat_def choi_matrix_def mult.commute[of n d])
  qed (use c in \<open>auto simp: block_of_mat_def\<close>)
qed

lemma msum_cong: "(\<And>x. x \<in> set xs \<Longrightarrow> g x = h x) \<Longrightarrow> msum r c g xs = msum r c h xs"
  by (induction xs) auto

lemma Tr_msum:
  assumes "\<forall>x \<in> set xs. g x \<in> carrier_mat d d"
  shows "Tr (msum d d g xs) = (\<Sum>x\<leftarrow>xs. Tr (g x))"
  using assms
proof (induction xs)
  case Nil show ?case by (simp add: Tr_def)
next
  case (Cons x xs)
  have gx: "g x \<in> carrier_mat d d" and rest: "\<forall>x \<in> set xs. g x \<in> carrier_mat d d" using Cons.prems by auto
  have "Tr (g x + msum d d g xs) = Tr (g x) + Tr (msum d d g xs)"
    by (rule Tr_add) (use gx msum_carrier[OF rest] in auto)
  thus ?case using Cons.IH[OF rest] by simp
qed

text \<open>In matrix units $A=\sum_{i,j}a_{ij}E_{ij}$ and $I=\sum_iE_{ii}$, so a linear $\Phi$ satisfies
$\Phi(A)=\sum_{i,j}a_{ij}\,\Phi(E_{ij})=\sum_{i,j}a_{ij}R_{ij}$, the $R_{ij}$ being the blocks of $P_\Phi$.\<close>

lemma unit_expansion:
  assumes A: "A \<in> carrier_mat n n"
  shows "A = msum n n (\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m E\<lbrakk>i,j ; n,n\<rbrakk>) (List.product [0..<n] [0..<n])"
proof -
  let ?g = "\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m E\<lbrakk>i,j ; n,n\<rbrakk>"
  have g: "\<forall>x \<in> set (List.product [0..<n] [0..<n]). ?g x \<in> carrier_mat n n" by auto
  show ?thesis
  proof (rule eq_matI)
    fix r c assume "r < dim_row (msum n n ?g (List.product [0..<n] [0..<n]))"
                   "c < dim_col (msum n n ?g (List.product [0..<n] [0..<n]))"
    hence r: "r < n" and c: "c < n" using msum_carrier[OF g] by auto
    have "msum n n ?g (List.product [0..<n] [0..<n]) $$ (r,c)
        = (\<Sum>i<n. \<Sum>j<n. if i = r \<and> j = c then A $$ (r,c) else 0)"
      unfolding msum_index[OF g r c] sum_list_product_upt using r c
      by (intro sum.cong refl) auto
    also have "\<dots> = A $$ (r,c)" by (rule sum_delta2[OF r c])
    finally show "A $$ (r,c) = msum n n ?g (List.product [0..<n] [0..<n]) $$ (r,c)" by simp
  qed (use A msum_carrier[OF g] in auto)
qed

lemma id_expansion: "1\<^sub>m n = msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n]"
proof -
  have g: "\<forall>x \<in> set [0..<n]. E\<lbrakk>x,x ; n,n\<rbrakk> \<in> carrier_mat n n" by simp
  show ?thesis
  proof (rule eq_matI)
    fix r c assume "r < dim_row (msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n])"
                   "c < dim_col (msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n])"
    hence r: "r < n" and c: "c < n" using msum_carrier[OF g] by auto
    have "msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n] $$ (r,c) = (\<Sum>i<n. if i = r \<and> r = c then 1 else 0)"
      unfolding msum_index[OF g r c] interv_sum_list_conv_sum_set_nat set_upt atLeast0LessThan
      using r c by (intro sum.cong refl) auto
    also have "\<dots> = (if r = c then 1 else 0)" using r by (simp add: sum.delta)
    finally show "1\<^sub>m n $$ (r,c) = msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n] $$ (r,c)" using r c by simp
  qed (use msum_carrier[OF g] in auto)
qed

lemma lin_expansion:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and A: "A \<in> carrier_mat n n"
  shows "\<Phi> A = msum d d (\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) (List.product [0..<n] [0..<n])"
proof -
  let ?xs = "List.product [0..<n] [0..<n]" and ?g = "\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m E\<lbrakk>i,j ; n,n\<rbrakk>"
  have "\<Phi> A = \<Phi> (msum n n ?g ?xs)" by (rule arg_cong[OF unit_expansion[OF A]])
  also have "\<dots> = msum d d (\<lambda>x. \<Phi> (?g x)) ?xs"
    by (rule lin_on_msum_closed[OF L zero_carrier_mat add_carrier_mat]) auto
  also have "\<dots> = msum d d (\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) ?xs"
    by (rule msum_cong) (use L in \<open>auto simp: lin_on_def\<close>)
  finally show ?thesis .
qed

text \<open>D19-3, note (4): trace preservation in Choi-matrix form.\<close>

theorem choi_trace_preserving_iff:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>"
  shows "trace_preserving n \<Phi> \<longleftrightarrow>
         (\<forall>i < n. \<forall>j < n. Tr (block_of_mat d (choi_matrix n d \<Phi>) i j) = (if i = j then 1 else 0))"
proof -
  have range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d" using L unfolding lin_on_def by auto
  have R: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> block_of_mat d (choi_matrix n d \<Phi>) i j = \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)"
    by (rule choi_block[OF range])
  show ?thesis
  proof
    assume "trace_preserving n \<Phi>"
    thus "\<forall>i < n. \<forall>j < n. Tr (block_of_mat d (choi_matrix n d \<Phi>) i j) = (if i = j then 1 else 0)"
      using R by (simp add: trace_preserving_def Tr_mat_unit)
  next
    assume "\<forall>i < n. \<forall>j < n. Tr (block_of_mat d (choi_matrix n d \<Phi>) i j) = (if i = j then 1 else 0)"
    hence h: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> Tr (\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) = (if i = j then 1 else 0)"
      using R by simp
    show "trace_preserving n \<Phi>" unfolding trace_preserving_def
    proof (intro allI impI)
      fix X :: "complex Matrix.mat" assume X: "X \<in> carrier_mat n n"
      let ?xs = "List.product [0..<n] [0..<n]"
      have gc: "\<forall>x \<in> set ?xs. (\<lambda>(i,j). X $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) x \<in> carrier_mat d d"
        using range by auto
      have "Tr (\<Phi> X) = (\<Sum>x\<leftarrow>?xs. Tr ((\<lambda>(i,j). X $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) x))"
        unfolding lin_expansion[OF L X] by (rule Tr_msum[OF gc])
      also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. X $$ (i,j) * Tr (\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)))"
        by (simp add: sum_list_product_upt Tr_smult)
      also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. if j = i then X $$ (i,i) else 0)"
        by (intro sum.cong refl) (simp add: h)
      also have "\<dots> = (\<Sum>i<n. X $$ (i,i))" by simp
      also have "\<dots> = Tr X" using X by (simp add: Tr_def)
      finally show "Tr (\<Phi> X) = Tr X" .
    qed
  qed
qed

text \<open>D19-3, note (5): unitality in Choi-matrix form, $\sum_iR_{ii}=I_d$.\<close>

theorem choi_unital_iff:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>"
  shows "unital_map n d \<Phi> \<longleftrightarrow> msum d d (\<lambda>i. block_of_mat d (choi_matrix n d \<Phi>) i i) [0..<n] = 1\<^sub>m d"
proof -
  have range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d" using L unfolding lin_on_def by auto
  have "\<Phi> (1\<^sub>m n) = \<Phi> (msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n])" by (rule arg_cong[OF id_expansion])
  also have "\<dots> = msum d d (\<lambda>i. \<Phi> (E\<lbrakk>i,i ; n,n\<rbrakk>)) [0..<n]"
    by (rule lin_on_msum_closed[OF L zero_carrier_mat add_carrier_mat]) auto
  also have "\<dots> = msum d d (\<lambda>i. block_of_mat d (choi_matrix n d \<Phi>) i i) [0..<n]"
    by (rule msum_cong) (simp add: choi_block[OF range])
  finally show ?thesis unfolding unital_map_def by simp
qed

lemma lin_on_choi_hyps:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>"
  shows "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
    and "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
    and "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
  using L unfolding lin_on_def by auto

text \<open>Notes (4) and (5) with Choi's theorem: CPTP iff $P_\Phi\ge0$ and $\Tr R_{ij}=\delta_{ij}$;
UCP iff $P_\Phi\ge0$ and $\sum_iR_{ii}=I_d$.\<close>

corollary choi_cptp_iff:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and n: "n > 0" and d: "d > 0"
  shows "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi> \<longleftrightarrow>
         psd (choi_matrix n d \<Phi>) \<and>
         (\<forall>i < n. \<forall>j < n. Tr (block_of_mat d (choi_matrix n d \<Phi>) i j) = (if i = j then 1 else 0))"
  using choi_theorem[OF lin_on_choi_hyps[OF L] n d] choi_trace_preserving_iff[OF L] by simp

corollary choi_ucp_iff:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and n: "n > 0" and d: "d > 0"
  shows "completely_positive n d \<Phi> \<and> unital_map n d \<Phi> \<longleftrightarrow>
         psd (choi_matrix n d \<Phi>) \<and> msum d d (\<lambda>i. block_of_mat d (choi_matrix n d \<Phi>) i i) [0..<n] = 1\<^sub>m d"
  using choi_theorem[OF lin_on_choi_hyps[OF L] n d] choi_unital_iff[OF L] by simp

end
