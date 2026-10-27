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
$(E_{ij})\ge0$ (\<open>choi_matrix_as_amplification\<close>); (3)$\Rightarrow$(4) is the notes' proof,
through the vectorisation of Kraus operators (\<open>choi_matrix_kraus_eq\<close>: the Choi matrix of a
Kraus map is $\sum_k v_kv_k^*$, $v_k=\mathrm{vec}(V_k)$).  Linearity of $\Phi$ is assumed on the
carrier $M_n$ (additivity and homogeneity hypotheses).  The trace-preserving case is
\<open>choi_kraus_cptp\<close>; notes (4) and (5) in Choi-matrix form are \<open>choi_trace_preserving_iff\<close>
and \<open>choi_unital_iff\<close> below.\<close>

subsection \<open>The Choi matrix\<close>

text \<open>$P_\Phi\in M_n(M_d)$ is the block matrix with $(a,b)$ block $\Phi(E_{ab})$.  It is linear in $\Phi$.\<close>

definition choi_matrix :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "choi_matrix n d \<Phi> \<equiv>
     Matrix.mat (n*d) (n*d)
       (\<lambda>(r,c). \<Phi> (mat_unit (r div d) (c div d) n n) $$ (r mod d, c mod d))"

notation choi_matrix ("P\<^sub>\<Phi>")

lemma choi_matrix_carrier [simp]:
  "choi_matrix n d \<Phi> \<in> carrier_mat (n*d) (n*d)"
  by (simp add: choi_matrix_def)

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

lemma choi_matrix_smult:
  assumes F: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> F X \<in> carrier_mat d d" and d: "0 < d"
  shows "choi_matrix n d (\<lambda>X. a \<cdot>\<^sub>m F X) = a \<cdot>\<^sub>m choi_matrix n d F"
proof (rule eq_matI)
  fix r c assume "r < dim_row (a \<cdot>\<^sub>m choi_matrix n d F)" "c < dim_col (a \<cdot>\<^sub>m choi_matrix n d F)"
  hence r: "r < n*d" and c: "c < n*d" by (simp_all add: choi_matrix_def)
  have E: "mat_unit (r div d) (c div d) n n \<in> carrier_mat n n" by simp
  have "r mod d < d" "c mod d < d" using d by simp_all
  thus "choi_matrix n d (\<lambda>X. a \<cdot>\<^sub>m F X) $$ (r, c) = (a \<cdot>\<^sub>m choi_matrix n d F) $$ (r, c)"
    using r c F[OF E] by (simp add: choi_matrix_def)
qed (simp_all add: choi_matrix_def)

lemma choi_matrix_lincomb:
  assumes F: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> F X \<in> carrier_mat d d"
      and G: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> G X \<in> carrier_mat d d" and d: "0 < d"
  shows "choi_matrix n d (\<lambda>X. a \<cdot>\<^sub>m F X + b \<cdot>\<^sub>m G X) = a \<cdot>\<^sub>m choi_matrix n d F + b \<cdot>\<^sub>m choi_matrix n d G"
proof (rule eq_matI)
  fix r c assume "r < dim_row (a \<cdot>\<^sub>m choi_matrix n d F + b \<cdot>\<^sub>m choi_matrix n d G)"
    "c < dim_col (a \<cdot>\<^sub>m choi_matrix n d F + b \<cdot>\<^sub>m choi_matrix n d G)"
  hence r: "r < n*d" and c: "c < n*d" by (simp_all add: choi_matrix_def)
  have E: "mat_unit (r div d) (c div d) n n \<in> carrier_mat n n" by simp
  have "r mod d < d" "c mod d < d" using d by simp_all
  thus "choi_matrix n d (\<lambda>X. a \<cdot>\<^sub>m F X + b \<cdot>\<^sub>m G X) $$ (r, c)
      = (a \<cdot>\<^sub>m choi_matrix n d F + b \<cdot>\<^sub>m choi_matrix n d G) $$ (r, c)"
    using r c F[OF E] G[OF E] by (simp add: choi_matrix_def)
qed (simp_all add: choi_matrix_def)

subsection \<open>A linear map is its values on the matrix units\<close>

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

text \<open>So two linear maps with the same Choi matrix agree on $M_n$.\<close>

lemma map_eq_from_choi_when_linear:
  assumes L: "lin_on n d (carrier_mat n n) Phi" and L': "lin_on n d (carrier_mat n n) Psi"
      and choi_eq: "choi_matrix n d Phi = choi_matrix n d Psi" and A: "A \<in> carrier_mat n n"
  shows "Phi A = Psi A"
proof -
  have "Phi (E\<lbrakk>i,j ; n,n\<rbrakk>) = Psi (E\<lbrakk>i,j ; n,n\<rbrakk>)" if "i < n" "j < n" for i j
    using choi_block[OF _ that, of Phi d] choi_block[OF _ that, of Psi d] L L' choi_eq
    unfolding lin_on_def by simp
  thus ?thesis unfolding lin_expansion[OF L A] lin_expansion[OF L' A] by (intro msum_cong) auto
qed

subsection \<open>The Choi matrix as an amplification\<close>

text \<open>For $f:\{0,\dots,r-1\}\to\{0,\dots,n-1\}$ the block matrix $(E_{f(a)f(b)})_{a,b}\in M_r(M_n)$.
The notes' examples are $f=(i,j)$ with $r=2$, giving $\begin{pmatrix}E_{ii}&E_{ij}\\E_{ji}&E_{jj}\end{pmatrix}$,
and $f=\mathrm{id}$ with $r=n$, giving $(E_{ij})$.\<close>

definition unit_blocks :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "unit_blocks r n f = Matrix.mat (r * n) (r * n)
     (\<lambda>(x, y). if x mod n = f (x div n) \<and> y mod n = f (y div n) then 1 else 0)"

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

lemma choi_seed_block:
  assumes a: "a < n" and b: "b < n"
  shows "block_of_mat n (choi_seed n) a b = mat_unit a b n n"
  using unit_blocks_block[OF a b, of id] a b by (simp add: choi_seed_unit_blocks)

text \<open>The seed $\sum_{a,b}E_{ab}\otimes E_{ab}\in M_n(M_n)$ has the matrix unit $E_{ab}$ as its $(a,b)$
block, so the Choi matrix is the amplification of $\Phi$ applied to it:
\[ P_\Phi=\bigl(\Phi(E_{ab})\bigr)_{a,b}=\Phi^{(n)}\Bigl(\sum_{a,b}E_{ab}\otimes E_{ab}\Bigr). \]
The seed is $\ketbra\xi\xi$ with $\xi=\sum_ae_a\otimes e_a$, hence positive; so $P_\Phi\ge0$ when
$\Phi$ is completely positive.\<close>

lemma choi_matrix_as_amplification:
  assumes npos: "n > 0"
      and dpos: "d > 0"
  shows "choi_matrix n d \<Phi> = amplification n d n \<Phi> (choi_seed n)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (amplification n d n \<Phi> (choi_seed n))" "j < dim_col (amplification n d n \<Phi> (choi_seed n))"
  hence "i < n*d" "j < n*d" by simp_all
  hence "i div d < n" "j div d < n" by (simp_all add: less_mult_imp_div_less)
  thus "choi_matrix n d \<Phi> $$ (i, j) = amplification n d n \<Phi> (choi_seed n) $$ (i, j)"
    using \<open>i < n*d\<close> \<open>j < n*d\<close> by (simp add: choi_matrix_def amplification_index choi_seed_block)
qed (simp_all add: choi_matrix_def)

lemma choi_psd_if_n_positive:
  assumes n: "0 < n" and d: "0 < d" and pp: "p_positive n d n \<Phi>"
  shows "psd (choi_matrix n d \<Phi>)"
proof -
  have "choi_seed n \<in> carrier_mat (n * n) (n * n)" by (rule choi_seed_carrier)
  hence "psd (amplification n d n \<Phi> (choi_seed n))" using pp choi_seed_psd by (simp add: p_positive_def)
  thus ?thesis by (simp add: choi_matrix_as_amplification[OF n d])
qed

lemma choi_psd_if_cp:
  assumes npos: "n > 0"
      and dpos: "d > 0"
      and cp: "completely_positive n d \<Phi>"
  shows "psd (choi_matrix n d \<Phi>)"
  using cp npos by (simp add: completely_positive_def choi_psd_if_n_positive[OF npos dpos])

subsection \<open>Kraus maps\<close>

text \<open>A Kraus map is linear in its argument, completely positive, and trace preserving when its operators are Kraus operators.\<close>

lemma kraus_map_dim_add:
  assumes A_c: "A \<in> carrier_mat n n" and B_c: "B \<in> carrier_mat n n"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (A + B) =
         kraus_map_dim d Ws A + kraus_map_dim d Ws B"
proof -
  have "W * (A + B) * (W\<^sup>\<dagger>) = W * A * (W\<^sup>\<dagger>) + W * B * (W\<^sup>\<dagger>)" if "W \<in> set Ws" for W
  proof -
    have W: "W \<in> carrier_mat d n" using Ws_c that by blast
    show ?thesis
      by (simp add: mult_add_distrib_mat[OF W A_c B_c]
                    add_mult_distrib_mat[OF mult_carrier_mat[OF W A_c] mult_carrier_mat[OF W B_c] dagger_carrier[OF W]])
  qed
  thus ?thesis unfolding kraus_map_dim_msum
    by (subst msum_add[symmetric]) (use Ws_c A_c B_c in \<open>auto intro!: msum_cong mult_carrier_mat dagger_carrier\<close>)
qed

lemma kraus_map_dim_smult:
  assumes A_c: "A \<in> carrier_mat n n"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m kraus_map_dim d Ws A"
proof -
  have "W * (c \<cdot>\<^sub>m A) * (W\<^sup>\<dagger>) = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>))" if "W \<in> set Ws" for W
  proof -
    have W: "W \<in> carrier_mat d n" using Ws_c that by blast
    show ?thesis
      by (simp add: mult_smult_distrib[OF W A_c] mult_smult_assoc_mat[OF mult_carrier_mat[OF W A_c] dagger_carrier[OF W]])
  qed
  thus ?thesis unfolding kraus_map_dim_msum
    by (subst msum_smult[symmetric]) (use Ws_c A_c in \<open>auto intro!: msum_cong mult_carrier_mat dagger_carrier\<close>)
qed

lemma kraus_map_dim_zero [simp]:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (0\<^sub>m n n) = 0\<^sub>m d d"
proof -
  have "W * 0\<^sub>m n n * (W\<^sup>\<dagger>) = 0\<^sub>m d d" if "W \<in> set Ws" for W
  proof -
    have W: "W \<in> carrier_mat d n" using Ws_c that by blast
    show ?thesis by (simp add: right_mult_zero_mat[OF W] left_mult_zero_mat[OF dagger_carrier[OF W]])
  qed
  thus ?thesis unfolding kraus_map_dim_msum
    by (subst msum_cong[of Ws _ "\<lambda>_. 0\<^sub>m d d"]) (simp_all add: msum_def foldr_add_mat_zero)
qed

lemma kraus_lin_on:
  assumes "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "lin_on n d (carrier_mat n n) (kraus_map_dim d Ws)"
  unfolding lin_on_def using assms
  by (auto intro: kraus_map_dim_carrier kraus_map_dim_add kraus_map_dim_smult)

text \<open>
  Complete positivity from a Kraus list without the trace-preservation
  constraint: the argument is the same as @{thm kraus_is_cp}, which only uses
  the carrier hypothesis.
\<close>

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

lemma sum_wdag_w_append:
  fixes Ws Vs :: "complex Matrix.mat list"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "sum_wdag_w n (Ws @ Vs)
         = sum_wdag_w n Ws + sum_wdag_w n Vs"
  unfolding sum_wdag_w_msum
  by (rule msum_append) (use Ws_c Vs_c in \<open>auto intro!: mult_carrier_mat dagger_carrier\<close>)

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

text \<open>So Kraus maps carry density matrices to density matrices.\<close>

lemma kraus_map_dim_density_matrix:
  assumes Ws: "kraus_operators n d Ws" and \<rho>: "density_matrix n \<rho>"
  shows "density_matrix d (kraus_map_dim d Ws \<rho>)"
  using Ws \<rho> kraus_is_trace_preserving[OF Ws]
  unfolding density_matrix_def kraus_operators_def trace_preserving_def
  by (auto intro: kraus_map_dim_carrier kraus_map_dim_psd)

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

text \<open>Conversely a vector in $\C^{nd}$ folds into a $d\times n$ matrix.\<close>

definition kraus_of_vec :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "kraus_of_vec d n v = Matrix.mat d n (\<lambda>(i, a). v $ (a * d + i))"

lemma kraus_of_vec_carrier [simp]: "kraus_of_vec d n v \<in> carrier_mat d n"
  by (simp add: kraus_of_vec_def)

lemma vec_of_kraus_of_vec:
  assumes v: "dim_vec v = n * d" and d: "0 < d"
  shows "vec_of_kraus d n (kraus_of_vec d n v) = v"
proof (rule eq_vecI)
  fix r assume "r < dim_vec v"
  hence r: "r < n * d" using v by simp
  hence "r div d < n" "r mod d < d" using d by (simp_all add: less_mult_imp_div_less)
  thus "vec_of_kraus d n (kraus_of_vec d n v) $ r = v $ r"
    using r by (simp add: vec_of_kraus_index kraus_of_vec_def div_mult_mod_eq)
qed (use v in simp)

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
proof -
  have "(\<Sum>V\<leftarrow>Vs. (V * mat_unit a b n n * (V\<^sup>\<dagger>)) $$ (i, j)) = (\<Sum>V\<leftarrow>Vs. V $$ (i, a) * cnj (V $$ (j, b)))"
    by (rule arg_cong[where f = sum_list, OF map_cong[OF refl]])
       (use Vs_c in \<open>simp add: sandwich_mat_unit_entry[OF _ _ a_lt b_lt i_lt j_lt]\<close>)
  thus ?thesis
    by (simp add: kraus_map_dim_entry_sum_list[OF Vs_c mat_unit_carrier i_lt j_lt] sum_list_sum_nth atLeast0LessThan)
qed

lemma choi_matrix_kraus_eq:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and npos: "0 < n" and dpos: "0 < d"
  shows "choi_matrix n d (kraus_map_dim d Vs)
           = outer_sum (n*d) (map (vec_of_kraus d n) Vs)"
proof (rule eq_matI)
  let ?M = "mat_of_cols (n*d) (map (vec_of_kraus d n) Vs)"
  fix r c assume "r < dim_row (outer_sum (n*d) (map (vec_of_kraus d n) Vs))"
    "c < dim_col (outer_sum (n*d) (map (vec_of_kraus d n) Vs))"
  hence r: "r < n*d" and c: "c < n*d" by simp_all
  have rd: "r div d < n" "r mod d < d" and cd: "c div d < n" "c mod d < d"
    using r c dpos by (simp_all add: less_mult_imp_div_less)
  have "choi_matrix n d (kraus_map_dim d Vs) $$ (r, c)
      = (\<Sum>k<length Vs. Vs!k $$ (r mod d, r div d) * cnj (Vs!k $$ (c mod d, c div d)))"
    using r c by (simp add: choi_matrix_def kraus_map_dim_mat_unit_entry[OF Vs_c rd(1) cd(1) rd(2) cd(2)])
  also have "\<dots> = (?M * (?M\<^sup>\<dagger>)) $$ (r, c)"
    using r c
    by (simp add: mat_mult_entry[OF mat_of_cols_carrier(1) dagger_carrier[OF mat_of_cols_carrier(1)] r c]
                  dagger_def mat_of_cols_index vec_of_kraus_index)
  finally show "choi_matrix n d (kraus_map_dim d Vs) $$ (r, c) = outer_sum (n*d) (map (vec_of_kraus d n) Vs) $$ (r, c)"
    by (simp add: outer_sum_def)
qed (simp_all add: choi_matrix_def outer_sum_def)

subsection \<open>Choi's theorem\<close>

text \<open>The notes' proof of (3)$\Rightarrow$(4): write $P_\Phi=\sum_kv_kv_k^*$ with
$v_k\in\C^{nd}$, cut each $v_k$ into $n$ blocks $w^k_1,\dots,w^k_n\in\C^d$, and let
$B_k=[w^k_1|\cdots|w^k_n]$; then $B_kE_{ij}B_k^*=w^k_i(w^k_j)^*$ and
$\Phi(X)=\sum_{ij}x_{ij}\Phi(E_{ij})=\sum_kB_kXB_k^*$ by linearity.\<close>

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
  have L: "lin_on n d (carrier_mat n n) \<Phi>" unfolding lin_on_def using linear smult range by auto
  obtain vs :: "complex Matrix.vec list" where len: "length vs = n * d"
    and dim: "\<forall>v \<in> set vs. dim_vec v = n * d" and P: "outer_sum (n * d) vs = choi_matrix n d \<Phi>"
    using psd_kraus_decomp[OF choi_matrix_carrier psdP] by blast
  define Ws where "Ws = map (kraus_of_vec d n) vs"
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" by (simp add: Ws_def)
  have "map (vec_of_kraus d n) Ws = vs"
    unfolding Ws_def map_map using dim dpos by (intro map_idI) (simp add: vec_of_kraus_of_vec)
  hence "choi_matrix n d (kraus_map_dim d Ws) = choi_matrix n d \<Phi>"
    by (simp add: choi_matrix_kraus_eq[OF Ws_c npos dpos] P)
  hence eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using map_eq_from_choi_when_linear[OF L kraus_lin_on[OF Ws_c]] by simp
  show ?thesis using len Ws_c eq by (intro exI[of _ Ws]) (simp add: Ws_def)
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
  thus "psd (choi_matrix n d \<Phi>)" by (rule choi_psd_if_cp[OF npos dpos])
next
  assume "psd (choi_matrix n d \<Phi>)"
  then obtain Ws where Ws: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    and eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos] by blast
  thus "completely_positive n d \<Phi>"
    using kraus_cp_no_tp[OF Ws npos dpos] completely_positive_cong[of n \<Phi> "kraus_map_dim d Ws" d] by simp
qed

text \<open>The trace-preserving case: CPTP maps are exactly the Kraus maps of Kraus operators.\<close>

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
  assume "\<exists>Ws :: complex Matrix.mat list. kraus_operators n d Ws \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
  then obtain Ws where K: "kraus_operators n d Ws"
    and eq: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Ws X" by blast
  have "completely_positive n d \<Phi> = completely_positive n d (kraus_map_dim d Ws)"
    by (rule completely_positive_cong) (rule eq)
  thus "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>"
    using kraus_is_cp[OF K npos dpos] kraus_is_trace_preserving[OF K] by (simp add: trace_preserving_def eq)
next
  assume "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>"
  hence cp: "completely_positive n d \<Phi>" and tp: "trace_preserving n \<Phi>" by auto
  obtain Ws where Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    and eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos choi_psd_if_cp[OF npos dpos cp]] by blast
  have "sum_wdag_w n Ws = 1\<^sub>m n"
  proof (rule mat_trace_pairing_unique[OF sum_wdag_w_carrier[OF Ws_c] one_carrier_mat])
    fix \<rho> :: "complex Matrix.mat" assume \<rho>: "\<rho> \<in> carrier_mat n n"
    have "Tr (sum_wdag_w n Ws * \<rho>) = Tr (kraus_map_dim d Ws \<rho>)"
      by (rule Tr_kraus_map_dim_as_wdagw[OF Ws_c \<rho>, symmetric])
    also have "\<dots> = Tr \<rho>" using eq tp \<rho> by (simp add: trace_preserving_def)
    finally show "Tr (sum_wdag_w n Ws * \<rho>) = Tr (1\<^sub>m n * \<rho>)" using \<rho> by simp
  qed
  thus "\<exists>Ws :: complex Matrix.mat list. kraus_operators n d Ws \<and>
          (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
    using Ws_c eq by (auto simp: kraus_operators_altdef)
qed

text \<open>Condition (2), $n$-positivity, isolated (D19-1).\<close>

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

subsection \<open>Trace preservation and unitality in Choi-matrix form (D19-3)\<close>

text \<open>Day 19, notes (4) and (5) after Choi's theorem: write $P_\Phi=(R_{ij})$ with
$R_{ij}=\Phi(E_{ij})\in M_d$.  Then $\Phi$ is trace preserving iff $\Tr R_{ij}=\delta_{ij}$, and
unital iff $\sum_iR_{ii}=I_d$; with \<open>choi_theorem\<close> this characterises CPTP and UCP maps by
their Choi matrix.  Linearity on $M_n$ is \<^term>\<open>lin_on n d (carrier_mat n n) \<Phi>\<close>.\<close>

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

lemma Tr_msum_pairs:
  assumes "\<And>i j. i < k \<Longrightarrow> j < k \<Longrightarrow> g i j \<in> carrier_mat r r"
  shows "Tr (msum r r (\<lambda>(i, j). g i j) (List.product [0..<k] [0..<k])) = (\<Sum>i<k. \<Sum>j<k. Tr (g i j))"
proof -
  have "\<forall>x \<in> set (List.product [0..<k] [0..<k]). (case x of (i, j) \<Rightarrow> g i j) \<in> carrier_mat r r"
    using assms by auto
  from Tr_msum[OF this] show ?thesis by (simp add: sum_list_product_upt)
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
