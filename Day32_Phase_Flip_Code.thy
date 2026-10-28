(*  Title:   Day32_Phase_Flip_Code.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 14 November 2011 (Day 32)
*)

theory Day32_Phase_Flip_Code
  imports Day10_Quantum_Gates
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
\<open>pauli_expansion_unitary\<close> below.  The Shor code and Shor's theorem
are \<open>Day33_Shor_Code\<close> (\<open>shor_code_theorem\<close>).  As first stated, the orthogonality claim is false
($Z_1\ne Z_2$ but $Z_1\ket{0_L}=Z_2\ket{0_L}$, \<open>shor_notes_Z1_Z2\<close>); Day 33 corrects it.\<close>

definition ket_plus :: "complex Matrix.vec" where
  "ket_plus \<equiv> (1 / sqrt 2 :: complex) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"

definition ket_minus :: "complex Matrix.vec" where
  "ket_minus \<equiv> (1 / sqrt 2 :: complex) \<cdot>\<^sub>v (unit_vec 2 0 - unit_vec 2 1)"

lemma ket_plus_carrier [simp]: "ket_plus \<in> carrier_vec 2"
  by (simp add: ket_plus_def)

lemma ket_plus_dim [simp]: "dim_vec ket_plus = 2"
  by (simp add: ket_plus_def)

lemma ket_minus_dim [simp]: "dim_vec ket_minus = 2"
  by (simp add: ket_minus_def)

lemma ket_plus_index_0: "ket_plus $ 0 = 1 / sqrt 2"
  by (simp add: ket_plus_def)

lemma ket_plus_index_1: "ket_plus $ 1 = 1 / sqrt 2"
  by (simp add: ket_plus_def)

text \<open>$\ket\pm=\tfrac1{\sqrt2}(\ket0\pm\ket1)$ is an orthonormal basis in which $X$ and $Z$ exchange roles:
\[ Z\ket+=\ket-,\quad Z\ket-=\ket+,\qquad X\ket+=\ket+,\quad X\ket-=-\ket-. \]
A phase flip acts on $\ket\pm$ as a bit flip acts on $\ket0,\ket1$, so the phase-flip code is
the bit-flip code in the basis $\ket\pm$.\<close>

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
(\<open>knill_laflamme_necessity\<close>) and Theorem 2 (\<open>knill_laflamme_closure\<close>) are proved on
Day 34, with the converse, the construction of $R$ from the conditions, and the equivalence
itself (\<open>knill_laflamme\<close>).  The elementary algebra of orthogonal
projections used by the proofs follows.\<close>

lemma projection_complement:
  assumes "projection n P"
  shows "projection n (1\<^sub>m n - P)"
  using assms unfolding projection_def hermitian_def
  by (auto simp: complement_dagger complement_projection intro: minus_carrier_mat)

text \<open>Two projections are orthogonal if their products in both orders vanish.\<close>

definition orthogonal_projections ::
  "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "orthogonal_projections n P Q \<equiv>
     projection n P \<and> projection n Q \<and>
     P * Q = 0\<^sub>m n n \<and> Q * P = 0\<^sub>m n n"

subsection \<open>Pauli magic (D32-6)\<close>

text \<open>\begin{notesprop}
$I,X,Y,Z$ are orthogonal in $M_2$ and all have $2$-norm $\sqrt2$.
\end{notesprop}\<close>

proposition pauli_orthogonal:
  shows "\<langle>\<langle> 1\<^sub>m 2 | Pauli_X \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> 1\<^sub>m 2 | Pauli_Y \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> 1\<^sub>m 2 | Pauli_Z \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> Pauli_X | Pauli_Y \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> Pauli_X | Pauli_Z \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> Pauli_Y | Pauli_Z \<rangle>\<rangle> = 0"
proof -
  show "\<langle>\<langle> 1\<^sub>m 2 | Pauli_X \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def Pauli_X_def numeral_2_eq_2)
  show "\<langle>\<langle> 1\<^sub>m 2 | Pauli_Y \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def Pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle> 1\<^sub>m 2 | Pauli_Z \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def Pauli_Z_def numeral_2_eq_2)
  show "\<langle>\<langle> Pauli_X | Pauli_Y \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def Pauli_X_def Pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle> Pauli_X | Pauli_Z \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def Pauli_X_def Pauli_Z_def numeral_2_eq_2)
  show "\<langle>\<langle> Pauli_Y | Pauli_Z \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def Pauli_Y_def Pauli_Z_def numeral_2_eq_2)
qed

proposition pauli_norm:
  shows "\<langle>\<langle> 1\<^sub>m 2 | (1\<^sub>m 2 :: complex Matrix.mat) \<rangle>\<rangle> = 2"
    and "\<langle>\<langle> Pauli_X | Pauli_X \<rangle>\<rangle> = 2"
    and "\<langle>\<langle> Pauli_Y | Pauli_Y \<rangle>\<rangle> = 2"
    and "\<langle>\<langle> Pauli_Z | Pauli_Z \<rangle>\<rangle> = 2"
proof -
  show "\<langle>\<langle> 1\<^sub>m 2 | (1\<^sub>m 2 :: complex Matrix.mat) \<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def numeral_2_eq_2)
  show "\<langle>\<langle> Pauli_X | Pauli_X \<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def Pauli_X_def numeral_2_eq_2)
  show "\<langle>\<langle> Pauli_Y | Pauli_Y \<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def Pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle> Pauli_Z | Pauli_Z \<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def Pauli_Z_def numeral_2_eq_2)
qed

subsection \<open>The Pauli expansion identity for unitaries (D32-7)\<close>

lemma cmod_parallelogram:
  fixes a b :: complex
  shows "(cmod (a + b))\<^sup>2 + (cmod (a - b))\<^sup>2 = 2 * (cmod a)\<^sup>2 + 2 * (cmod b)\<^sup>2"
  unfolding cmod_power2 by (simp add: power2_eq_square algebra_simps)

proposition pauli_expansion_unitary:
  fixes U :: "complex Matrix.mat" and a0 a1 a2 a3 :: complex
  assumes Uu: "unitary U"
      and U_eq: "U = a0 \<cdot>\<^sub>m 1\<^sub>m 2 + a1 \<cdot>\<^sub>m Pauli_X + a2 \<cdot>\<^sub>m Pauli_Y + a3 \<cdot>\<^sub>m Pauli_Z"
  shows "(cmod a0)\<^sup>2 + (cmod a1)\<^sup>2 + (cmod a2)\<^sup>2 + (cmod a3)\<^sup>2 = 1"
proof -
  have Uc: "U \<in> carrier_mat 2 2"
    unfolding U_eq by (simp add: Pauli_X_def Pauli_Y_def Pauli_Z_def)
  have dr: "dim_row U = 2" and dc: "dim_col U = 2" using Uc by auto
  have e00: "U $$ (0,0) = a0 + a3"
    by (simp add: U_eq Pauli_X_def Pauli_Y_def Pauli_Z_def)
  have e01: "U $$ (0,1) = a1 + \<i> * a2"
    by (simp add: U_eq Pauli_X_def Pauli_Y_def Pauli_Z_def)
  have e10: "U $$ (1,0) = a1 - \<i> * a2"
    by (simp add: U_eq Pauli_X_def Pauli_Y_def Pauli_Z_def)
  have e11: "U $$ (1,1) = a0 - a3"
    by (simp add: U_eq Pauli_X_def Pauli_Y_def Pauli_Z_def)
  have UdU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m 2" using Uu dc by (simp add: unitary_def)
  have tr2: "Tr ((U\<^sup>\<dagger>) * U) = 2" unfolding UdU by (simp add: Tr_one_mat)
  have hs: "\<langle>\<langle> U | U \<rangle>\<rangle> = Tr ((U\<^sup>\<dagger>) * U)"
    by (rule hs_inner_prod_as_trace) simp_all
  have expand: "\<langle>\<langle> U | U \<rangle>\<rangle> =
      cnj (U $$ (0,0)) * U $$ (0,0) + cnj (U $$ (0,1)) * U $$ (0,1)
    + cnj (U $$ (1,0)) * U $$ (1,0) + cnj (U $$ (1,1)) * U $$ (1,1)"
    unfolding hs_inner_prod_def dr dc by (simp add: numeral_2_eq_2)
  have "2 = Re (\<langle>\<langle> U | U \<rangle>\<rangle>)" using hs tr2 by simp
  also have "\<dots> = (cmod (a0 + a3))\<^sup>2 + (cmod (a1 + \<i> * a2))\<^sup>2
                 + (cmod (a1 - \<i> * a2))\<^sup>2 + (cmod (a0 - a3))\<^sup>2"
    unfolding expand e00 e01 e10 e11 cnj_mult_self_cmod by simp
  also have "\<dots> = 2 * ((cmod a0)\<^sup>2 + (cmod a1)\<^sup>2 + (cmod a2)\<^sup>2 + (cmod a3)\<^sup>2)"
  proof -
    have p1: "(cmod (a0 + a3))\<^sup>2 + (cmod (a0 - a3))\<^sup>2 = 2 * (cmod a0)\<^sup>2 + 2 * (cmod a3)\<^sup>2"
      by (rule cmod_parallelogram)
    have p2: "(cmod (a1 + \<i> * a2))\<^sup>2 + (cmod (a1 - \<i> * a2))\<^sup>2 = 2 * (cmod a1)\<^sup>2 + 2 * (cmod a2)\<^sup>2"
      using cmod_parallelogram[of a1 "\<i> * a2"] by (simp add: norm_mult)
    have "(cmod (a0 + a3))\<^sup>2 + (cmod (a1 + \<i> * a2))\<^sup>2 + (cmod (a1 - \<i> * a2))\<^sup>2 + (cmod (a0 - a3))\<^sup>2
          = ((cmod (a0 + a3))\<^sup>2 + (cmod (a0 - a3))\<^sup>2) + ((cmod (a1 + \<i> * a2))\<^sup>2 + (cmod (a1 - \<i> * a2))\<^sup>2)"
      by (simp add: algebra_simps)
    also have "\<dots> = (2 * (cmod a0)\<^sup>2 + 2 * (cmod a3)\<^sup>2) + (2 * (cmod a1)\<^sup>2 + 2 * (cmod a2)\<^sup>2)"
      unfolding p1 p2 ..
    also have "\<dots> = 2 * ((cmod a0)\<^sup>2 + (cmod a1)\<^sup>2 + (cmod a2)\<^sup>2 + (cmod a3)\<^sup>2)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  finally show ?thesis by simp
qed

end
