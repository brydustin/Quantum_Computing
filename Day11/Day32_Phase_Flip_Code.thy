(*  Title:   Day32_Phase_Flip_Code.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 14 November 2011 (Day 32)
*)

theory Day32_Phase_Flip_Code
  imports Day31_Bit_Flip_Channel
begin

section \<open>Day 32 (14 November 2011): the phase-flip code, the Shor code, Pauli magic\<close>

subsection \<open>The phase-flip code\<close>

text \<open>With $Z\ket0=\ket0$, $Z\ket1=-\ket1$ and $\ket\pm=(\ket0\pm\ket1)/\sqrt2$ one has
$\ket+\perp\ket-$, $Z\ket+=\ket-$, $Z\ket-=\ket+$: $Z$ acts on $\{\ket+,\ket-\}$ as the bit flip
acts on $\{\ket0,\ket1\}$.  Encoding $\ket0\mapsto\ket{+++}$, $\ket1\mapsto\ket{---}$ gives the
three-qubit \emph{phase-flip code}, which detects and corrects phase flips exactly as the
bit-flip code corrects bit flips; with $\beta=Y\ket+$ (orthogonal to $\ket+$, $Y\beta=\ket+$) the
same works for $Y$.

The \emph{Shor code} encodes $\ket0\mapsto\ket{0_L}=2^{-3/2}(\ket{000}+\ket{111})^{\otimes3}$ and
$\ket1\mapsto\ket{1_L}=2^{-3/2}(\ket{000}-\ket{111})^{\otimes3}$ in $\C^{2^9}$.
\begin{notestheorem}[Shor]
There is a completely positive trace-preserving $R:M_{2^9}\to M_{2^9}$ such that for every
$2\times2$ unitary $U$, every position $j$, $\tilde U=I\otimes\cdots\otimes U\otimes\cdots\otimes I$,
and every $\psi=a\ket{0_L}+b\ket{1_L}$, $R(\tilde U\ketbra\psi\psi\tilde U^*)=\ketbra\psi\psi$.
\end{notestheorem}
\begin{notesprop}
If $V\subseteq\C^n$ is a subspace and $U_1,\dots,U_t$ are unitaries with $U_iV\perp U_jV$ for
$i\neq j$, then there is a CPTP $R$ with $R(U_i\ketbra\psi\psi U_i^*)=\ketbra\psi\psi$ for all
$\psi\in V$ and all $i$ (take $R(X)=\sum_iU_i^*P_iXP_iU_i$ with $P_i$ the projection onto
$U_iV$, $P_0=I-\sum P_i$, $U_0=I$).
\end{notesprop}
The $3\cdot9+1$ \emph{1-Pauli} operators $I\otimes\cdots\otimes U\otimes\cdots\otimes I$ ($U$ a
Pauli matrix) map $V=\operatorname{span}\{\ket{0_L},\ket{1_L}\}$ to mutually orthogonal subspaces
(up to the coincidences $Z_1v=Z_2v=Z_3v$ etc.).  The proposition is \<open>recovery_single_error\<close>
in \<open>Day32_Recovery_Proposition\<close>, together with its linear-combination form
\<open>recovery_linear_combination\<close> (Day 33); the Pauli expansion identity is
\<open>pauli_expansion_unitary\<close> in \<open>Day32_Pauli_Expansion\<close>.  The Shor code and Shor's theorem
are \<open>Day33_Shor_Code\<close> (\<open>shor_code_theorem\<close>).  As first stated, the orthogonality claim is false
($Z_1\ne Z_2$ but $Z_1\ket{0_L}=Z_2\ket{0_L}$, \<open>shor_notes_Z1_Z2\<close>); Day 33 corrects it.\<close>

definition ket_plus :: "complex Matrix.vec" where
  "ket_plus \<equiv> (1 / sqrt 2 :: complex) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"

definition ket_minus :: "complex Matrix.vec" where
  "ket_minus \<equiv> (1 / sqrt 2 :: complex) \<cdot>\<^sub>v (unit_vec 2 0 - unit_vec 2 1)"

lemma ket_plus_carrier [simp]: "ket_plus \<in> carrier_vec 2"
  by (simp add: ket_plus_def)

lemma ket_minus_carrier [simp]: "ket_minus \<in> carrier_vec 2"
  by (simp add: ket_minus_def)

lemma ket_plus_dim [simp]: "dim_vec ket_plus = 2"
  by (simp add: ket_plus_def)

lemma ket_minus_dim [simp]: "dim_vec ket_minus = 2"
  by (simp add: ket_minus_def)

lemma ket_plus_index_0: "ket_plus $ 0 = 1 / sqrt 2"
  by (simp add: ket_plus_def)

lemma ket_plus_index_1: "ket_plus $ 1 = 1 / sqrt 2"
  by (simp add: ket_plus_def)

lemma ket_minus_index_0: "ket_minus $ 0 = 1 / sqrt 2"
  by (simp add: ket_minus_def)

lemma ket_minus_index_1: "ket_minus $ 1 = - 1 / sqrt 2"
  by (simp add: ket_minus_def)

lemma ket_plus_unit: "\<parallel>ket_plus\<parallel> = 1"
proof -
  have inner: "\<langle>ket_plus | ket_plus\<rangle> = 1"
  proof -
    have "\<langle>ket_plus | ket_plus\<rangle>
            = (\<Sum>i = 0..<2. cnj (ket_plus $ i) * (ket_plus $ i))"
      unfolding inner_prod_def by simp
    also have "\<dots> = cnj (ket_plus $ 0) * (ket_plus $ 0)
                    + cnj (ket_plus $ 1) * (ket_plus $ 1)"
      by (simp add: numeral_2_eq_2)
    also have "\<dots> = 1"
      unfolding ket_plus_def by (simp add: of_real_mult [symmetric])
    finally show ?thesis .
  qed
  have "(\<parallel>ket_plus\<parallel>)\<^sup>2 = 1"
    using inner by (metis cpx_vec_length_inner_prod of_real_1 of_real_eq_iff)
  thus ?thesis
    by (metis cpx_vec_length_inner_prod cpx_vec_length_zero_iff
        inner_prod_csqrt ket_plus_carrier ket_plus_dim norm_eq_zero
        norm_of_real normalized_vec_norm of_real_eq_0_iff of_real_eq_1_iff
        power2_eq_1_iff real_sqrt_abs)
qed

lemma ket_minus_unit: "\<parallel>ket_minus\<parallel> = 1"
proof -
  have inner: "\<langle>ket_minus | ket_minus\<rangle> = 1"
  proof -
    have "\<langle>ket_minus | ket_minus\<rangle>
            = (\<Sum>i = 0..<2. cnj (ket_minus $ i) * (ket_minus $ i))"
      unfolding inner_prod_def by simp
    also have "\<dots> = cnj (ket_minus $ 0) * (ket_minus $ 0)
                    + cnj (ket_minus $ 1) * (ket_minus $ 1)"
      by (simp add: numeral_2_eq_2)
    also have "\<dots> = 1"
      unfolding ket_minus_def by (simp add: of_real_mult [symmetric])
    finally show ?thesis .
  qed
  have "(\<parallel>ket_minus\<parallel>)\<^sup>2 = 1"
    using inner by (metis cpx_vec_length_inner_prod of_real_1 of_real_eq_iff)
  thus ?thesis
    by (metis cpx_vec_length_inner_prod inner_prod_csqrt ket_plus_unit
        of_real_eq_1_iff power_one)
qed

lemma ket_plus_minus_orthog: "\<langle>ket_plus | ket_minus\<rangle> = 0"
proof -
  have "\<langle>ket_plus | ket_minus\<rangle>
          = (\<Sum>i = 0..<2. cnj (ket_plus $ i) * (ket_minus $ i))"
    unfolding inner_prod_def by simp
  also have "\<dots> = cnj (ket_plus $ 0) * (ket_minus $ 0)
                  + cnj (ket_plus $ 1) * (ket_minus $ 1)"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = 0"
    unfolding ket_plus_def ket_minus_def by simp
  finally show ?thesis .
qed


lemma Pauli_Z_ket_plus: "Pauli_Z *\<^sub>v ket_plus = ket_minus"
proof (rule eq_vecI)
  show "dim_vec (Pauli_Z *\<^sub>v ket_plus) = dim_vec ket_minus"
    by (simp add: Pauli_Z_def)
next
  fix i assume "i < dim_vec ket_minus"
  hence i_lt: "i < 2" by simp
  have "(Pauli_Z *\<^sub>v ket_plus) $ i =
        (\<Sum>k = 0..<2. Pauli_Z $$ (i, k) * ket_plus $ k)"
    using i_lt by (simp add: scalar_prod_def Pauli_Z_def)
  also have "\<dots> = Pauli_Z $$ (i, 0) * ket_plus $ 0
                  + Pauli_Z $$ (i, 1) * ket_plus $ 1"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = ket_minus $ i"
    using i_lt
    by (cases "i = 0";
        simp add: Pauli_Z_def ket_plus_def ket_minus_def)
  finally show "(Pauli_Z *\<^sub>v ket_plus) $ i = ket_minus $ i" .
qed

lemma Pauli_Z_ket_minus: "Pauli_Z *\<^sub>v ket_minus = ket_plus"
proof -
  have "Pauli_Z *\<^sub>v ket_minus = Pauli_Z *\<^sub>v (Pauli_Z *\<^sub>v ket_plus)"
    using Pauli_Z_ket_plus by simp
  also have "\<dots> = (Pauli_Z * Pauli_Z) *\<^sub>v ket_plus"
    by (metis assoc_mult_mat_vec Pauli_Z_carrier ket_plus_carrier)
  also have "\<dots> = (1\<^sub>m 2) *\<^sub>v ket_plus"
    using Pauli_Z_squared by simp
  also have "\<dots> = ket_plus" by simp
  finally show ?thesis .
qed


lemma Pauli_X_ket_plus: "Pauli_X *\<^sub>v ket_plus = ket_plus"
proof (rule eq_vecI)
  show "dim_vec (Pauli_X *\<^sub>v ket_plus) = dim_vec ket_plus"
    by (simp add: Pauli_X_def)
next
  fix i assume "i < dim_vec ket_plus"
  hence i_lt: "i < 2" by simp
  have "(Pauli_X *\<^sub>v ket_plus) $ i =
        (\<Sum>k = 0..<2. Pauli_X $$ (i, k) * ket_plus $ k)"
    using i_lt by (simp add: scalar_prod_def Pauli_X_def)
  also have "\<dots> = Pauli_X $$ (i, 0) * ket_plus $ 0
                  + Pauli_X $$ (i, 1) * ket_plus $ 1"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = ket_plus $ i"
    using i_lt
    by (cases "i = 0";
        simp add: Pauli_X_def ket_plus_def)
  finally show "(Pauli_X *\<^sub>v ket_plus) $ i = ket_plus $ i" .
qed

lemma Pauli_X_ket_minus: "Pauli_X *\<^sub>v ket_minus = - ket_minus"
proof (rule eq_vecI)
  show "dim_vec (Pauli_X *\<^sub>v ket_minus) = dim_vec (- ket_minus)"
    by (simp add: Pauli_X_def)
next
  fix i assume "i < dim_vec (- ket_minus)"
  hence i_lt: "i < 2" by simp
  have "(Pauli_X *\<^sub>v ket_minus) $ i =
        (\<Sum>k = 0..<2. Pauli_X $$ (i, k) * ket_minus $ k)"
    using i_lt by (simp add: scalar_prod_def Pauli_X_def)
  also have "\<dots> = Pauli_X $$ (i, 0) * ket_minus $ 0
                  + Pauli_X $$ (i, 1) * ket_minus $ 1"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = (- ket_minus) $ i"
    using i_lt
    by (cases "i = 0";
        simp add: Pauli_X_def ket_minus_def)
  finally show "(Pauli_X *\<^sub>v ket_minus) $ i = (- ket_minus) $ i" .
qed


text \<open>The code words $\ket{+++}$ and $\ket{---}$ of the three-qubit phase-flip code (an
earlier version of this file called them \<open>phase_code_zero\<close>/\<open>phase_code_one\<close>; the nine-qubit Shor
code words are not defined).\<close>

definition phase_code_zero :: "complex Matrix.vec" where
  "phase_code_zero \<equiv>
     let v = unit_vec 2 0 + unit_vec 2 1 in
     (1 / (2 * sqrt 2) :: complex)
       \<cdot>\<^sub>v tensor_vec (tensor_vec v v) v"

definition phase_code_one :: "complex Matrix.vec" where
  "phase_code_one \<equiv>
     let v = unit_vec 2 0 - unit_vec 2 1 in
     (1 / (2 * sqrt 2) :: complex)
       \<cdot>\<^sub>v tensor_vec (tensor_vec v v) v"

lemma phase_code_zero_dim [simp]: "dim_vec phase_code_zero = 8"
  by (simp add: phase_code_zero_def Let_def, simp add: tensor_vec_dim)

lemma phase_code_one_dim [simp]: "dim_vec phase_code_one = 8"
  by (smt (verit, best) index_minus_vec(2) index_smult_vec(2) index_unit_vec(3) 
      mult_2 mult_commute_abs numeral_Bit0 phase_code_one_def tensor_vec_dim)

lemma phase_code_zero_carrier [simp]: "phase_code_zero \<in> carrier_vec 8"
  by (simp add: carrier_dim_vec)

lemma phase_code_one_carrier [simp]: "phase_code_one \<in> carrier_vec 8"
  by (simp add: carrier_dim_vec)


subsection \<open>Projections\<close>

text \<open>A \emph{projection} on $\C^n$ is a Hermitian idempotent, the notion of Day 2; projections
are the building blocks of syndrome measurements and recovery maps (Days 30--34).  Day 2's
theorem that such a $P$ is the orthogonal projection onto its range follows the basic facts.\<close>

definition projection :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "projection n P \<equiv>
     P \<in> carrier_mat n n \<and> hermitian P \<and> P * P = P"

lemma projection_carrier:
  "projection n P \<Longrightarrow> P \<in> carrier_mat n n"
  by (simp add: projection_def)

lemma projection_hermitian:
  "projection n P \<Longrightarrow> hermitian P"
  by (simp add: projection_def)

lemma projection_idempotent:
  "projection n P \<Longrightarrow> P * P = P"
  by (simp add: projection_def)

lemma projection_zero: "projection n (0\<^sub>m n n)"
  by (auto simp: projection_def hermitian_def dagger_def)

lemma projection_one: "projection n (1\<^sub>m n)"
  by (auto simp: projection_def hermitian_def dagger_def)


lemma projection_psd:
  assumes "projection n P"
  shows "psd P"
proof -
  have P_c: "P \<in> carrier_mat n n" using assms by (rule projection_carrier)
  have P_h: "hermitian P" using assms by (rule projection_hermitian)
  have P_idem: "P * P = P" using assms by (rule projection_idempotent)
  have P_dag: "P\<^sup>\<dagger> = P" using P_h by (simp add: hermitian_def)
  have eq: "P = (P\<^sup>\<dagger>) * P" using P_dag P_idem by simp
  have psd_PdP: "psd (P\<^sup>\<dagger> * P)"
    using P_c by (rule psd_MdagM)
  show ?thesis using eq psd_PdP by simp
qed


text \<open>The theorem of Day 2: a Hermitian idempotent $P$ is the orthogonal projection onto its
range, i.e. $Pv=v$ for $v$ in the range and $Pw=0$ for $w$ orthogonal to the range.\<close>

lemma projection_fixes_range:
  fixes P :: "complex Matrix.mat" and x :: "complex Matrix.vec"
  assumes P: "projection n P" and x: "dim_vec x = n"
  shows "P *\<^sub>v (P *\<^sub>v x) = P *\<^sub>v x"
proof -
  have Pc: "P \<in> carrier_mat n n" and idem: "P * P = P" using P by (auto simp: projection_def)
  have xc: "x \<in> carrier_vec n" using x by auto
  have "P *\<^sub>v (P *\<^sub>v x) = (P * P) *\<^sub>v x" using assoc_mult_mat_vec[OF Pc Pc xc] by simp
  thus ?thesis using idem by simp
qed

lemma projection_annihilates_orthogonal:
  fixes P :: "complex Matrix.mat" and w :: "complex Matrix.vec"
  assumes P: "projection n P" and w: "dim_vec w = n"
      and orth: "\<And>x :: complex Matrix.vec. dim_vec x = n \<Longrightarrow> \<langle>P *\<^sub>v x | w\<rangle> = 0"
  shows "P *\<^sub>v w = 0\<^sub>v n"
proof -
  have Pc: "P \<in> carrier_mat n n" and herm: "hermitian P" and idem: "P * P = P"
    using P by (auto simp: projection_def)
  have Ph: "P\<^sup>\<dagger> = P" using herm by (simp add: hermitian_def)
  have Pw: "dim_vec (P *\<^sub>v w) = n" using Pc w by auto
  have "\<langle>P *\<^sub>v w | P *\<^sub>v w\<rangle> = \<langle>P\<^sup>\<dagger> *\<^sub>v w | P *\<^sub>v w\<rangle>" using Ph by simp
  also have "\<dots> = \<langle>w | P *\<^sub>v (P *\<^sub>v w)\<rangle>"
    using inner_prod_adjoint_swap[OF Pc w Pw] by simp
  also have "\<dots> = \<langle>w | P *\<^sub>v w\<rangle>" using projection_fixes_range[OF P w] by simp
  also have "\<dots> = cnj \<langle>P *\<^sub>v w | w\<rangle>"
  proof -
    have dims: "dim_vec (P *\<^sub>v w) = dim_vec w" using Pw w by simp
    show ?thesis using inner_prod_cnj[OF dims] .
  qed
  also have "\<dots> = 0" using orth[OF w] by simp
  finally have "\<langle>P *\<^sub>v w | P *\<^sub>v w\<rangle> = 0" .
  thus ?thesis using inner_prod_self_eq_zero_iff[of "P *\<^sub>v w"] Pw by simp
qed

lemma projection_complement_idempotent:
  assumes "projection n P"
  shows "(1\<^sub>m n - P) * (1\<^sub>m n - P) = 1\<^sub>m n - P"
proof -
  have P_c: "P \<in> carrier_mat n n"
    using assms by (rule projection_carrier)

  have P_idem: "P * P = P"
    using assms by (rule projection_idempotent)

  have P_one_l: "1\<^sub>m n * P = P"
    using P_c by simp

  have P_one_r: "P * 1\<^sub>m n = P"
    using P_c by simp

  have I_one: "(1\<^sub>m n :: complex Matrix.mat) * 1\<^sub>m n = 1\<^sub>m n"
    by simp

  have "(1\<^sub>m n - P) * (1\<^sub>m n - P) = (1\<^sub>m n) * (1\<^sub>m n - P) - P * (1\<^sub>m n - P)"
    by (meson P_c minus_carrier_mat minus_mult_distrib_mat one_carrier_mat)
  also have "... = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * P) - (P * (1\<^sub>m n) - P * P)"
    by (metis P_c mult_minus_distrib_mat one_carrier_mat)
  also have "... = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * P) - (P * (1\<^sub>m n)) + P * P"
    using P_c by (simp add: algebra_simps, auto)
  also have "... = (1\<^sub>m n - P) - P + P * P"
    by (simp add: P_one_l P_one_r)
  also have "... = (1\<^sub>m n - P) - P + P"
    using P_idem by simp
  also have "... = 1\<^sub>m n - P"
    by auto
  finally show ?thesis.
qed


subsection \<open>More on the repetition code\<close>

lemma hamming_weight_append:
  "hamming_weight (xs @ ys) = hamming_weight xs + hamming_weight ys"
  by (simp add: hamming_weight_def)

lemma hamming_weight_repetition_encode:
  "hamming_weight (repetition_encode v) = 2 * hamming_weight v"
  by (simp add: repetition_encode_def hamming_weight_append)

lemma repetition_encode_binary:
  assumes "\<forall>x \<in> set v. x < 2"
  shows "\<forall>x \<in> set (repetition_encode v). x < 2"
  using assms by (auto simp: repetition_encode_def)


subsection \<open>Algebra of projections; towards Days 33 and 34\<close>

text \<open>Day 33 constructs the Shor recovery map from the projections onto the $22$ orthogonal
subspaces $V,X_1V,\dots,X_9V,Y_1V,\dots,Y_9V,Z_1V,Z_4V,Z_7V$ and proves, using
$U=a_0I+a_1X+a_2Y+a_3Z$ with $\sum|a_k|^2=1$ for unitary $U$ (Pauli magic), that it corrects
every single-qubit unitary error.  Day 34 gives the general theory:
\begin{notesprop}
For $V\subseteq\C^n$ with projection $P$ and CPTP maps $E$ (errors) and $R$ (recovery),
$R\circ E(\ketbra\psi\psi)=\ketbra\psi\psi$ for all $\psi\in V$ iff $R\circ E(PXP)=PXP$ for all $X$.
\end{notesprop}
\begin{notestheorem}[1]
Let $E(X)=\sum_{i=1}^rE_iXE_i^*$ be CPTP.  There is a CPTP $R$ with $R\circ E(PXP)=PXP$ for all $X$
iff $PE_i^*E_jP=\alpha_{ij}P$ for some scalars $\alpha_{ij}$.
\end{notestheorem}
\begin{notestheorem}[2]
If $R$ corrects $E$ as in Theorem 1 and $G_i\in\operatorname{span}\{E_j\}$ with $\sum G_i^*G_i=I$,
then $R$ also corrects $G(X)=\sum_iG_iXG_i^*$.
\end{notestheorem}
Of the Knill--Laflamme results, the equivalence of Theorem 1's two readings
(\<open>recovery_states_iff_PXP\<close>), the necessity of $PE_i^*E_jP=\alpha_{ij}P$
(\<open>knill_laflamme_necessity\<close>) and Theorem 2 (\<open>knill_laflamme_closure\<close>) are proved in
\<open>Day34_Knill_Laflamme\<close>; the converse, the construction of $R$ from the conditions, and
the equivalence itself (\<open>knill_laflamme\<close>) are in \<open>Day34_KL_Sufficiency\<close>.  The elementary algebra of orthogonal
projections used by the proofs follows.\<close>


lemma projection_complement:
  assumes "projection n P"
  shows "projection n (1\<^sub>m n - P)"
proof -
  have P_c: "P \<in> carrier_mat n n" using assms by (rule projection_carrier)
  have P_h: "hermitian P" using assms by (rule projection_hermitian)
  have P_dag: "P\<^sup>\<dagger> = P" using P_h by (simp add: hermitian_def)
  have I_dag: "(1\<^sub>m n :: complex Matrix.mat)\<^sup>\<dagger> = 1\<^sub>m n"
    by (intro eq_matI) (auto simp: dagger_def)
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have IP_c: "(1\<^sub>m n - P) \<in> carrier_mat n n"
    using P_c by (rule minus_carrier_mat)
  have IP_dag: "(1\<^sub>m n - P)\<^sup>\<dagger> = 1\<^sub>m n - P"
  proof (rule eq_matI)
    show "dim_row ((1\<^sub>m n - P)\<^sup>\<dagger>) = dim_row (1\<^sub>m n - P)"
      using P_c by simp
    show "dim_col ((1\<^sub>m n - P)\<^sup>\<dagger>) = dim_col (1\<^sub>m n - P)"
      using P_c by simp
  next
    fix i j
    assume i: "i < dim_row (1\<^sub>m n - P)"
       and j: "j < dim_col (1\<^sub>m n - P)"
    hence ij: "i < n" "j < n" using P_c by simp_all
    have P_swap: "P $$ (j, i) = cnj (P $$ (i, j))"
    proof -
      have "(P\<^sup>\<dagger>) $$ (i, j) = cnj (P $$ (j, i))"
        using ij P_c by (simp add: dagger_def)
      hence "P $$ (i, j) = cnj (P $$ (j, i))"
        using P_dag by simp
      thus ?thesis by simp
    qed
    have one_entry_self_cnj:
      "(1\<^sub>m n :: complex Matrix.mat) $$ (j, i)
        = cnj ((1\<^sub>m n :: complex Matrix.mat) $$ (i, j))"
      using ij by auto
    show "((1\<^sub>m n - P)\<^sup>\<dagger>) $$ (i, j) = (1\<^sub>m n - P) $$ (i, j)"
      using ij P_c P_swap one_entry_self_cnj
      by (simp add: dagger_def)
  qed
  have IP_h: "hermitian (1\<^sub>m n - P)" using IP_dag by (simp add: hermitian_def)
  have IP_idem: "(1\<^sub>m n - P) * (1\<^sub>m n - P) = 1\<^sub>m n - P"
    using assms by (rule projection_complement_idempotent)
  show ?thesis
    unfolding projection_def using IP_c IP_h IP_idem by blast
qed

text \<open>Two projections are orthogonal if their products in both orders vanish.\<close>

definition orthogonal_projections ::
  "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "orthogonal_projections n P Q \<equiv>
     projection n P \<and> projection n Q \<and>
     P * Q = 0\<^sub>m n n \<and> Q * P = 0\<^sub>m n n"

lemma orthogonal_projections_carrier_left:
  "orthogonal_projections n P Q \<Longrightarrow> P \<in> carrier_mat n n"
  by (simp add: orthogonal_projections_def projection_def)

lemma orthogonal_projections_carrier_right:
  "orthogonal_projections n P Q \<Longrightarrow> Q \<in> carrier_mat n n"
  by (simp add: orthogonal_projections_def projection_def)

lemma orthogonal_projections_symm:
  "orthogonal_projections n P Q \<longleftrightarrow> orthogonal_projections n Q P"
  by (auto simp: orthogonal_projections_def)


lemma orthogonal_projections_sum:
  assumes opq: "orthogonal_projections n P Q"
  shows "projection n (P + Q)"
proof -
  have P_proj: "projection n P"
    using opq by (simp add: orthogonal_projections_def)
  have Q_proj: "projection n Q"
    using opq by (simp add: orthogonal_projections_def)
  have PQ_zero: "P * Q = 0\<^sub>m n n"
    using opq by (simp add: orthogonal_projections_def)
  have QP_zero: "Q * P = 0\<^sub>m n n"
    using opq by (simp add: orthogonal_projections_def)
  have P_c: "P \<in> carrier_mat n n" using P_proj by (rule projection_carrier)
  have Q_c: "Q \<in> carrier_mat n n" using Q_proj by (rule projection_carrier)
  have P_idem: "P * P = P" using P_proj by (rule projection_idempotent)
  have Q_idem: "Q * Q = Q" using Q_proj by (rule projection_idempotent)
  have P_h: "hermitian P" using P_proj by (rule projection_hermitian)
  have Q_h: "hermitian Q" using Q_proj by (rule projection_hermitian)
  have P_dag: "P\<^sup>\<dagger> = P" using P_h by (simp add: hermitian_def)
  have Q_dag: "Q\<^sup>\<dagger> = Q" using Q_h by (simp add: hermitian_def)

  have PQ_c: "P + Q \<in> carrier_mat n n" using P_c Q_c by simp

  have PQ_dag: "(P + Q)\<^sup>\<dagger> = P + Q"
  proof -
    have "(P + Q)\<^sup>\<dagger> = (P\<^sup>\<dagger>) + (Q\<^sup>\<dagger>)"
      using P_c Q_c
      by (intro eq_matI, auto simp: dagger_def)
    also have "\<dots> = P + Q" using P_dag Q_dag by simp
    finally show ?thesis.
  qed
  have PQ_h: "hermitian (P + Q)" using PQ_dag by (simp add: hermitian_def)

  have PQ_idem: "(P + Q) * (P + Q) = P + Q"
  proof -
    have expand:
      "(P + Q) * (P + Q) = P * P + P * Q + (Q * P + Q * Q)"
      using P_c Q_c
      by (smt (verit) add_carrier_mat add_mult_distrib_mat
          mult_add_distrib_mat assoc_add_mat)
    have "P * P + P * Q + (Q * P + Q * Q)
            = P + 0\<^sub>m n n + (0\<^sub>m n n + Q)"
      using P_idem Q_idem PQ_zero QP_zero by simp
    also have "\<dots> = P + Q"
      using P_c Q_c by (intro eq_matI, auto)
    finally show ?thesis using expand by simp
  qed
  show ?thesis unfolding projection_def using PQ_c PQ_h PQ_idem by blast
qed


lemma orthogonal_projections_decomp_id:
  assumes "orthogonal_projections n P Q"
  shows "P + Q + (1\<^sub>m n - P - Q) = 1\<^sub>m n"
proof -
  have P_c: "P \<in> carrier_mat n n"
    using assms by (rule orthogonal_projections_carrier_left)
  have Q_c: "Q \<in> carrier_mat n n"
    using assms by (rule orthogonal_projections_carrier_right)
  show ?thesis using P_c Q_c by (intro eq_matI) auto
qed

end
