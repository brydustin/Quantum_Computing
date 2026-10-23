(*  Title:   Day30_Error_Probabilities.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 9 November 2011 (Day 30)
*)

theory Day30_Error_Probabilities
  imports Day29_Error_Correction
begin

section \<open>Day 30 (9 November 2011): error probabilities; the three-qubit bit-flip code\<close>

text \<open>If a bit flips with probability $p$ (independently), the repetition code on three bits
leaves an error undetected with probability $3p^2(1-p)^4+3p^4(1-p)^2+p^6$, the parity code with
probability $\binom42p^2(1-p)^2+p^4$ (the former is smaller for $p<\tfrac12$), and the
majority-rule code $0\mapsto000$, $1\mapsto111$ decodes wrongly with probability $3p^2(1-p)+p^3$
(theory Day29\_Classical\_Codes; the comparison holds for all $0<p<1$).

Quantum error correction: one cannot clone, but basis vectors can be copied and measurements
can decode.  With $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ the allowed errors are qubit flips
$X\otimes I\otimes I$, $I\otimes X\otimes I$, \dots.  The \emph{three-qubit bit-flip code} encodes
$a\ket0+b\ket1\mapsto a\ket{000}+b\ket{111}$ (two CNOTs).  Decoding: (1) syndrome measurement with
$P_0=\ketbra{000}{000}+\ketbra{111}{111}$, $P_1=\ketbra{100}{100}+\ketbra{011}{011}$,
$P_2=\ketbra{010}{010}+\ketbra{101}{101}$, $P_3=\ketbra{001}{001}+\ketbra{110}{110}$,
$\sum P_i^2=I$, which leaves a state with at most one flip unchanged and reveals where the flip
occurred; (2) recovery
$R(Y)=P_0YP_0+(X\otimes I\otimes I)P_1YP_1(X\otimes I\otimes I)+\cdots$, a completely positive
trace-preserving map with $R(\ketbra{\psi_i}{\psi_i})=\ketbra\psi\psi$ after zero or one error.
The code's recovery theorem is \<open>bit_flip_code_recovery\<close> in \<open>Day30_BitFlip_Code\<close>
(syndrome projections, $\sum P_i=I$, $R$ CPTP); the Pauli matrices and the bit-flip channel
are below.\<close>

subsection \<open>The Pauli matrices\<close>

text \<open>The notes use two sign conventions for $Y$: $\begin{pmatrix}0&-i\\i&0\end{pmatrix}$ on
Day 10 (the library's \<open>Y\<close>) and $\begin{pmatrix}0&i\\-i&0\end{pmatrix}$ on Day 32.
\<open>Pauli_Y\<close> follows Day 32; both are Hermitian unitary involutions, and the Pauli
identities below carry the corresponding signs.  \<open>Pauli_X\<close> and \<open>Pauli_Z\<close> are the
library's \<open>Quantum.X\<close> and \<open>Quantum.Z\<close>.\<close>

definition Pauli_X :: "complex Matrix.mat" where
  "Pauli_X \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if (i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0) then 1 else 0)"

definition Pauli_Y :: "complex Matrix.mat" where
  "Pauli_Y \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if i = 0 \<and> j = 1 then \<i>
                else if i = 1 \<and> j = 0 then -\<i> else 0)"

definition Pauli_Z :: "complex Matrix.mat" where
  "Pauli_Z \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if i = 0 \<and> j = 0 then 1
                else if i = 1 \<and> j = 1 then -1 else 0)"

lemma Pauli_X_carrier [simp]: "Pauli_X \<in> carrier_mat 2 2"
  by (auto simp: Pauli_X_def)

lemma Pauli_Y_carrier [simp]: "Pauli_Y \<in> carrier_mat 2 2"
  by (auto simp: Pauli_Y_def)

lemma Pauli_Z_carrier [simp]: "Pauli_Z \<in> carrier_mat 2 2"
  by (auto simp: Pauli_Z_def)

lemma Pauli_X_dagger: "Pauli_X\<^sup>\<dagger> = Pauli_X"
proof (rule eq_matI)
  show "dim_row (Pauli_X\<^sup>\<dagger>) = dim_row Pauli_X" by (simp add: Pauli_X_def)
  show "dim_col (Pauli_X\<^sup>\<dagger>) = dim_col Pauli_X" by (simp add: Pauli_X_def)
next
  fix i j assume "i < dim_row Pauli_X" "j < dim_col Pauli_X"
  thus "(Pauli_X\<^sup>\<dagger>) $$ (i, j) = Pauli_X $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: Pauli_X_def dagger_def)
qed

lemma Pauli_X_squared: "Pauli_X * Pauli_X = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (Pauli_X * Pauli_X) = dim_row (1\<^sub>m 2)"
    by (simp add: Pauli_X_def)
  show "dim_col (Pauli_X * Pauli_X) = dim_col (1\<^sub>m 2)"
    by (simp add: Pauli_X_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(Pauli_X * Pauli_X) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding Pauli_X_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

lemma Pauli_X_unitary: "unitary Pauli_X"
  unfolding unitary_def
  using Pauli_X_dagger Pauli_X_squared by (simp add: Pauli_X_def)

lemma Pauli_Y_dagger: "Pauli_Y\<^sup>\<dagger> = Pauli_Y"
proof (rule eq_matI)
  show "dim_row (Pauli_Y\<^sup>\<dagger>) = dim_row Pauli_Y" by (simp add: Pauli_Y_def)
  show "dim_col (Pauli_Y\<^sup>\<dagger>) = dim_col Pauli_Y" by (simp add: Pauli_Y_def)
next
  fix i j assume "i < dim_row Pauli_Y" "j < dim_col Pauli_Y"
  thus "(Pauli_Y\<^sup>\<dagger>) $$ (i, j) = Pauli_Y $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: Pauli_Y_def dagger_def)
qed

lemma Pauli_Y_squared: "Pauli_Y * Pauli_Y = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (Pauli_Y * Pauli_Y) = dim_row (1\<^sub>m 2)"
    by (simp add: Pauli_Y_def)
  show "dim_col (Pauli_Y * Pauli_Y) = dim_col (1\<^sub>m 2)"
    by (simp add: Pauli_Y_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(Pauli_Y * Pauli_Y) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding Pauli_Y_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

lemma Pauli_Y_unitary: "unitary Pauli_Y"
  unfolding unitary_def
  using Pauli_Y_dagger Pauli_Y_squared by (simp add: Pauli_Y_def)

lemma Pauli_Z_dagger: "Pauli_Z\<^sup>\<dagger> = Pauli_Z"
proof (rule eq_matI)
  show "dim_row (Pauli_Z\<^sup>\<dagger>) = dim_row Pauli_Z" by (simp add: Pauli_Z_def)
  show "dim_col (Pauli_Z\<^sup>\<dagger>) = dim_col Pauli_Z" by (simp add: Pauli_Z_def)
next
  fix i j assume "i < dim_row Pauli_Z" "j < dim_col Pauli_Z"
  thus "(Pauli_Z\<^sup>\<dagger>) $$ (i, j) = Pauli_Z $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: Pauli_Z_def dagger_def)
qed

lemma Pauli_Z_squared: "Pauli_Z * Pauli_Z = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (Pauli_Z * Pauli_Z) = dim_row (1\<^sub>m 2)"
    by (simp add: Pauli_Z_def)
  show "dim_col (Pauli_Z * Pauli_Z) = dim_col (1\<^sub>m 2)"
    by (simp add: Pauli_Z_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(Pauli_Z * Pauli_Z) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding Pauli_Z_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

lemma Pauli_Z_unitary: "unitary Pauli_Z"
  unfolding unitary_def
  using Pauli_Z_dagger Pauli_Z_squared by (simp add: Pauli_Z_def)


subsection \<open>Pauli magic (Day 32)\<close>

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


subsection \<open>The bit-flip channel (Day 31)\<close>

text \<open>Doing nothing to $\psi$ while a flip occurs with probability $p$ produces the ensemble
$\{1-p,\psi\},\{p,X\psi\}$, i.e. the error map $E(Y)=(1-p)Y+pXYX^*$, which is completely
positive and trace preserving.\<close>

definition bit_flip_channel ::
  "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "bit_flip_channel p \<rho> \<equiv>
     complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
     + complex_of_real p \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>))"

lemma bit_flip_channel_carrier:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "bit_flip_channel p \<rho> \<in> carrier_mat 2 2"
proof -
  have x_c: "Pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "Pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "Pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c assms by (rule mult_carrier_mat)
  have x\<rho>xd_c: "Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)
  show ?thesis
    using assms x\<rho>xd_c by (auto simp: bit_flip_channel_def)
qed


lemma bit_flip_channel_trace_preserving:
  fixes p :: real
  assumes \<rho>_c: "\<rho> \<in> carrier_mat 2 2"
  shows "Tr (bit_flip_channel p \<rho>) = Tr \<rho>"
proof -
  have x_c: "Pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "Pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "Pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c \<rho>_c by (rule mult_carrier_mat)
  have x\<rho>xd_c: "Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)
  have xdx_eq: "(Pauli_X\<^sup>\<dagger>) * Pauli_X = 1\<^sub>m 2"
    using Pauli_X_dagger Pauli_X_squared by simp

  (* Tr(X \<rho> X^dagger) = Tr(X^dagger X \<rho>) = Tr(I \<rho>) = Tr \<rho>, by cyclicity. *)
  have tr_conj: "Tr (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)) = Tr \<rho>"
  proof -
    have "Tr (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)) = Tr (Pauli_X\<^sup>\<dagger> * (Pauli_X * \<rho>))"
    proof (rule Tr_cyclic)
      show "dim_col (Pauli_X * \<rho>) = dim_row (Pauli_X\<^sup>\<dagger>)"
        using x\<rho>_c xd_c by (metis carrier_matD)
      show "dim_row (Pauli_X * \<rho>) = dim_col (Pauli_X\<^sup>\<dagger>)"
        using x\<rho>_c xd_c by (metis carrier_matD)
    qed
    also have "\<dots> = Tr ((Pauli_X\<^sup>\<dagger> * Pauli_X) * \<rho>)"
      by (metis xd_c x_c \<rho>_c assoc_mult_mat)
    also have "\<dots> = Tr ((1\<^sub>m 2) * \<rho>)" using xdx_eq by simp
    also have "\<dots> = Tr \<rho>" using \<rho>_c by simp
    finally show ?thesis .
  qed

  have row_eq: "dim_row (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_row (complex_of_real p \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)))"
    using \<rho>_c x\<rho>xd_c by (metis carrier_matD(1) index_smult_mat(2))
  have col_eq: "dim_col (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_col (complex_of_real p \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)))"
    using \<rho>_c x\<rho>xd_c by (metis carrier_matD(2) index_smult_mat(3))
  have "Tr (bit_flip_channel p \<rho>)
          = Tr (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
            + Tr (complex_of_real p \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)))"
    unfolding bit_flip_channel_def
    using row_eq col_eq by (rule Tr_add)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>))"
    by (simp add: Tr_smult)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr \<rho>"
    using tr_conj by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) * Tr \<rho>"
    by (simp add: ring_distribs)
  also have "\<dots> = 1 * Tr \<rho>"
    by simp
  also have "\<dots> = Tr \<rho>" by simp
  finally show ?thesis.
qed


lemma bit_flip_channel_psd:
  fixes p :: real
  assumes p_nn:    "0 \<le> p"
      and p_le_1:  "p \<le> 1"
      and \<rho>_c:    "\<rho> \<in> carrier_mat 2 2"
      and \<rho>_psd:  "psd \<rho>"
  shows "psd (bit_flip_channel p \<rho>)"
proof -
  have x_c: "Pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "Pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "Pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c \<rho>_c by (rule mult_carrier_mat)
  have x\<rho>xd_c: "Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)

  have one_minus_nn: "0 \<le> 1 - p" using p_le_1 by simp

  (* X . \<rho> . X^dagger is PSD: factor \<rho> = Q*Q via the psd-sqrt, then
     X . Q*Q . X^dagger = (X Q) (X Q)^dagger which is psd by psd_MdagM. *)
  have conj_psd: "psd (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>))"
  proof -
    obtain Q where Q_c:    "Q \<in> carrier_mat 2 2"
               and Q_psd:  "psd Q"
               and Q_sq:   "Q * Q = \<rho>"
      using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
    have Q_dagger: "Q\<^sup>\<dagger> = Q"
      using Q_psd by (simp add: psd_def hermitian_def)
    have XQ_c: "Pauli_X * Q \<in> carrier_mat 2 2"
      using x_c Q_c by (rule mult_carrier_mat)
    have XQd_c: "(Pauli_X * Q)\<^sup>\<dagger> \<in> carrier_mat 2 2"
      using XQ_c by (rule dagger_carrier)
    have eq: "Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>) = (Pauli_X * Q) * ((Pauli_X * Q)\<^sup>\<dagger>)"
    proof -
      have dim_eq: "dim_col Pauli_X = dim_row Q"
        using x_c Q_c by (metis carrier_matD)
      have dagprod: "(Pauli_X * Q)\<^sup>\<dagger> = (Q\<^sup>\<dagger>) * (Pauli_X\<^sup>\<dagger>)"
        using dim_eq by (rule dagger_of_prod)
      hence dagprod': "(Pauli_X * Q)\<^sup>\<dagger> = Q * (Pauli_X\<^sup>\<dagger>)"
        using Q_dagger by simp
      have "(Pauli_X * Q) * ((Pauli_X * Q)\<^sup>\<dagger>)
              = (Pauli_X * Q) * (Q * (Pauli_X\<^sup>\<dagger>))"
        using dagprod' by simp
      also have "\<dots> = Pauli_X * Q * Q * (Pauli_X\<^sup>\<dagger>)"
        using x_c Q_c xd_c by (metis assoc_mult_mat mult_carrier_mat)
      also have "\<dots> = Pauli_X * (Q * Q) * (Pauli_X\<^sup>\<dagger>)"
        using x_c Q_c by (metis assoc_mult_mat)
      also have "\<dots> = Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)"
        using Q_sq by simp
      finally show ?thesis by simp
    qed
    have psd_dd: "psd (((Pauli_X * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((Pauli_X * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF XQd_c] .
    have dd_eq: "(Pauli_X * Q)\<^sup>\<dagger>\<^sup>\<dagger> = Pauli_X * Q"
      using XQ_c by (simp add: dagger_of_dagger_is_id)
    have "psd ((Pauli_X * Q) * ((Pauli_X * Q)\<^sup>\<dagger>))"
      using psd_dd dd_eq by simp
    thus ?thesis using eq by simp
  qed

  have term1_psd: "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)"
    using one_minus_nn \<rho>_psd \<rho>_c by (rule psd_smult_nonneg)
  have term2_psd: "psd (complex_of_real p \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)))"
    using p_nn conj_psd x\<rho>xd_c by (rule psd_smult_nonneg)

  have term1_c: "complex_of_real (1 - p) \<cdot>\<^sub>m \<rho> \<in> carrier_mat 2 2"
    using \<rho>_c by simp
  have term2_c: "complex_of_real p \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>))
                   \<in> carrier_mat 2 2"
    using x\<rho>xd_c by simp

  have "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
              + complex_of_real p \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)))"
    using term1_psd term2_psd term1_c term2_c by (rule psd_add_psd)
  thus ?thesis by (simp add: bit_flip_channel_def)
qed

end
