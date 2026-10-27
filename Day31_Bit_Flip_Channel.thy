(*  Title:   Day31_Bit_Flip_Channel.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 11 November 2011 (Day 31)
*)

theory Day31_Bit_Flip_Channel
  imports Day14_Pure_States Day30_Bit_Flip_Code
begin

section \<open>Day 31 (11 November 2011): the bit-flip code as a channel; fidelity\<close>

text \<open>Encoding $\tilde\psi=a\ket{000}+b\ket{111}$ and flipping each qubit independently with
probability $p$ gives the error map
$E(Y)=(1-p)^3Y+p(1-p)^2\sum_j(X_j)Y(X_j)^*+\cdots+p^3(X\otimes X\otimes X)Y(X\otimes X\otimes X)^*$,
and with the recovery $R$ of Day 30,
\[ R\circ E(Y)=\bigl((1-p)^3+3p(1-p)^2\bigr)Y+\bigl(3p^2(1-p)+p^3\bigr)(X\otimes X\otimes X)Y(X\otimes X\otimes X). \]
The code helps iff $(1-p)^3+3p(1-p)^2\ge1-p$ iff $p\le\tfrac12$ (below, where the formula for $R\circ E$ holds for $Y$ supported on
the code space).
Below: the encoding isometry.\<close>

subsection \<open>The bit-flip channel\<close>

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

subsection \<open>Fidelity\<close>

text \<open>A state $\psi$ perturbed to $\psi'=a\psi+b\psi^\perp$ is close to $\psi$ when $|a|$ is
close to $1$, so the \emph{fidelity} of states is $F=|\braket{\psi'}\psi|$; for the density
matrices $\rho=\ketbra\psi\psi$, $\rho'=\ketbra{\psi'}{\psi'}$ one has
$\langle\rho|\rho'\rangle=\Tr(\rho\rho')=|\braket{\psi'}\psi|^2$, so $F=\sqrt{\Tr(\rho\rho')}$.
Error correction is compared by $F=\sqrt{\braket\psi{R\circ E(\ketbra\psi\psi)\psi}}$, minimised
or averaged over $\psi$: doing nothing gives $\min F=\sqrt{1-p}$, the bit-flip code gives
$\min F=\sqrt{(1-p)^3+3p(1-p)^2}$ (below).  Formally
\<open>fidelity \<psi> \<rho>\<close> is $\sqrt{\Re\braket\psi{\rho\psi}}$.\<close>

definition fidelity ::
  "complex Matrix.vec \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where
  "fidelity \<psi> \<rho> \<equiv> sqrt (Re (\<langle>\<psi> | \<rho> *\<^sub>v \<psi>\<rangle>))"

lemma fidelity_def_eq:
  "fidelity \<psi> \<rho> = sqrt (Re (\<langle>\<psi> | \<rho> *\<^sub>v \<psi>\<rangle>))"
  by (simp add: fidelity_def)


lemma fidelity_pure_states:
  fixes \<psi> \<psi>' :: "complex Matrix.vec"
  assumes \<psi>_qs:  "quantum_state n \<psi>"
      and \<psi>'_qs: "quantum_state n \<psi>'"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>))
           = cmod (\<langle>\<psi> | \<psi>'\<rangle>)"
proof -
  let ?\<rho> = "(mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>)"
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have \<psi>'_dim: "dim_vec \<psi>' = n" using \<psi>'_qs by (simp add: quantum_state_def)

  have rho_eq: "?\<rho> = outer_sum n [\<psi>']"
    by (simp add: outer_sum_def)

  (* ?\<rho> *_v \<psi> = \<langle>\<psi>'|\<psi>\<rangle> \<cdot>\<^sub>v \<psi>' *)
  have \<rho>\<psi>: "?\<rho> *\<^sub>v \<psi> = \<langle>\<psi>' | \<psi>\<rangle> \<cdot>\<^sub>v \<psi>'"
    using outer_sum_singleton_mult_vec[OF \<psi>'_dim \<psi>_dim] rho_eq by simp

  (* \<langle>\<psi> | ?\<rho> *_v \<psi>\<rangle> = \<langle>\<psi>|\<psi>'\<rangle> * \<langle>\<psi>'|\<psi>\<rangle> = (cmod \<langle>\<psi>|\<psi>'\<rangle>)^2 *)
  have inner_eq: "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<psi>'\<rangle> * \<langle>\<psi>' | \<psi>\<rangle>"
  proof -
    have "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<langle>\<psi>'|\<psi>\<rangle> \<cdot>\<^sub>v \<psi>'\<rangle>"
      using \<rho>\<psi> by simp
    also have "\<dots> = \<langle>\<psi>'|\<psi>\<rangle> * \<langle>\<psi> | \<psi>'\<rangle>"
      by (rule inner_prod_right_smult')
    finally show ?thesis by (simp add: mult.commute)
  qed

  have conj_swap: "\<langle>\<psi>' | \<psi>\<rangle> = cnj (\<langle>\<psi> | \<psi>'\<rangle>)"
    by (metis \<psi>_dim \<psi>'_dim inner_prod_cnj)

  have sq_real:
    "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = complex_of_real ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
  proof -
    have "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<psi>'\<rangle> * cnj (\<langle>\<psi> | \<psi>'\<rangle>)"
      using inner_eq conj_swap by simp
    also have "\<dots> = complex_of_real ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
      by (simp add: complex_norm_square mult.commute, metis complex_norm_square of_real_power)
    finally show ?thesis.
  qed

  have re_eq: "Re (\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle>) = (cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2"
    using sq_real by simp

  have nn: "0 \<le> cmod (\<langle>\<psi> | \<psi>'\<rangle>)" by simp

  have "fidelity \<psi> ?\<rho> = sqrt (Re (\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle>))"
    by (simp add: fidelity_def)
  also have "\<dots> = sqrt ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
    using re_eq by simp
  also have "\<dots> = cmod (\<langle>\<psi> | \<psi>'\<rangle>)"
    using nn by simp
  finally show ?thesis.
qed


lemma fidelity_self:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>]) * ((mat_of_cols n [\<psi>])\<^sup>\<dagger>)) = 1"
proof -
  have norm1: "\<parallel>\<psi>\<parallel> = 1"
    using \<psi>_qs by (simp add: quantum_state_def)
  have "fidelity \<psi> ((mat_of_cols n [\<psi>]) * ((mat_of_cols n [\<psi>])\<^sup>\<dagger>))
          = cmod (\<langle>\<psi> | \<psi>\<rangle>)"
    using fidelity_pure_states[OF \<psi>_qs \<psi>_qs] .
  also have "\<dots> = cmod (complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2))"
    by (metis cpx_vec_length_inner_prod)
  also have "\<dots> = cmod (complex_of_real (1\<^sup>2))"
    using norm1 by simp
  also have "\<dots> = 1"
    by simp
  finally show ?thesis .
qed


lemma fidelity_orthogonal:
  fixes \<psi> \<psi>' :: "complex Matrix.vec"
  assumes \<psi>_qs:  "quantum_state n \<psi>"
      and \<psi>'_qs: "quantum_state n \<psi>'"
      and ortho: "\<langle>\<psi> | \<psi>'\<rangle> = 0"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>)) = 0"
  using fidelity_pure_states[OF \<psi>_qs \<psi>'_qs] ortho by simp

subsection \<open>The three-qubit code against independent bit flips\<close>

text \<open>Day 31: the three-qubit code against independent bit flips.  Each qubit flips with
probability $p$, so $E(Y)=(1-p)^3Y+p(1-p)^2\sum_iX_iYX_i+p^2(1-p)\sum_{i<j}X_iX_jYX_jX_i+p^3\,X_1X_2X_3YX_3X_2X_1$.
On an encoded state the recovery $R$ leaves
$((1-p)^3+3p(1-p)^2)\ketbra{\tilde\psi}{\tilde\psi}+(3p^2(1-p)+p^3)\ketbra{X_1X_2X_3\tilde\psi}{X_1X_2X_3\tilde\psi}$.
The notes state this formula for a general $Y$; it holds for $Y$ supported on the code space
(for $Y=\ketbra{100}{100}$ and $p=0$ one gets $R(Y)=\ketbra{000}{000}\neq Y$).\<close>

definition three_bit_channel :: "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "three_bit_channel p M =
     complex_of_real ((1 - p)^3) \<cdot>\<^sub>m M
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m (X\<^sub>1 * M * (X\<^sub>1\<^sup>\<dagger>))
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m (X\<^sub>2 * M * (X\<^sub>2\<^sup>\<dagger>))
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m (X\<^sub>3 * M * (X\<^sub>3\<^sup>\<dagger>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>2 * X\<^sub>3) * M * ((X\<^sub>2 * X\<^sub>3)\<^sup>\<dagger>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>1 * X\<^sub>3) * M * ((X\<^sub>1 * X\<^sub>3)\<^sup>\<dagger>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>1 * X\<^sub>2) * M * ((X\<^sub>1 * X\<^sub>2)\<^sup>\<dagger>))
     + complex_of_real (p^3) \<cdot>\<^sub>m ((X\<^sub>1 * X\<^sub>2 * X\<^sub>3) * M * ((X\<^sub>1 * X\<^sub>2 * X\<^sub>3)\<^sup>\<dagger>))"

definition swap2 :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "swap2 x = Matrix.vec 2 (\<lambda>i. x $ (1 - i))"

lemma swap2_dim [simp]: "dim_vec (swap2 x) = 2" by (simp add: swap2_def)

lemma flips_on_codeword:
  assumes x: "dim_vec x = 2"
  defines "\<psi> \<equiv> encode_mat *\<^sub>v x" and "\<phi> \<equiv> encode_mat *\<^sub>v swap2 x"
  shows "(X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = \<phi>"
    and "(X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v \<phi>"
    and "(X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>2 *\<^sub>v \<phi>"
    and "(X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi> = X\<^sub>3 *\<^sub>v \<phi>"
proof -
  have \<psi>c: "\<psi> \<in> carrier_vec 8" unfolding \<psi>_def by (rule carrier_vecI) simp
  have c: "\<And>b. flip_bit_mat b \<in> carrier_mat 8 8" by simp
  have ev: "\<And>u. dim_vec u = 2 \<Longrightarrow> \<forall>i < 8. (encode_mat *\<^sub>v u) $ i = (if i = 0 then u $ 0 else if i = 7 then u $ 1 else 0)"
    using encode_mat_mult_vec by blast
  have fl: "\<And>b v i. b < 3 \<Longrightarrow> dim_vec v = 8 \<Longrightarrow> i < 8 \<Longrightarrow>
      (flip_bit_mat b *\<^sub>v v) $ i = v $ (if i div 2^b mod 2 = 0 then i + 2^b else i - 2^b)"
    by (rule flip_bit_mat_mult_vec)
  have sw: "swap2 x $ 0 = x $ 1" "swap2 x $ 1 = x $ 0" "swap2 x $ Suc 0 = x $ 0" by (simp_all add: swap2_def)
  show "(X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = \<phi>"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec \<phi>" hence i: "i < 8" unfolding \<phi>_def by simp
    have "(X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>))"
      by (simp only: assoc_mult_mat_vec[OF mult_carrier_mat[OF c c] c \<psi>c] assoc_mult_mat_vec[OF c c mult_mat_vec_carrier[OF c \<psi>c]])
    hence "((X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>))) $ i" by simp
    thus "((X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi>) $ i = \<phi> $ i"
      using idx8[OF i] x unfolding \<psi>_def \<phi>_def
      by (elim disjE) (simp_all add: fl ev sw del: index_mult_mat_vec)
  qed (simp add: \<phi>_def)
  show "(X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v \<phi>"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (X\<^sub>1 *\<^sub>v \<phi>)" hence i: "i < 8" by simp
    have "(X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>)" by (rule assoc_mult_mat_vec[OF c c \<psi>c])
    hence "((X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>2 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>)) $ i" by simp
    thus "((X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>1 *\<^sub>v \<phi>) $ i"
      using idx8[OF i] x unfolding \<psi>_def \<phi>_def by (elim disjE) (simp_all add: fl ev sw del: index_mult_mat_vec)
  qed simp
  show "(X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>2 *\<^sub>v \<phi>"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (X\<^sub>2 *\<^sub>v \<phi>)" hence i: "i < 8" by simp
    have "(X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>)" by (rule assoc_mult_mat_vec[OF c c \<psi>c])
    hence "((X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>1 *\<^sub>v (X\<^sub>3 *\<^sub>v \<psi>)) $ i" by simp
    thus "((X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi>) $ i = (X\<^sub>2 *\<^sub>v \<phi>) $ i"
      using idx8[OF i] x unfolding \<psi>_def \<phi>_def by (elim disjE) (simp_all add: fl ev sw del: index_mult_mat_vec)
  qed simp
  show "(X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi> = X\<^sub>3 *\<^sub>v \<phi>"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (X\<^sub>3 *\<^sub>v \<phi>)" hence i: "i < 8" by simp
    have "(X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>)" by (rule assoc_mult_mat_vec[OF c c \<psi>c])
    hence "((X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi>) $ i = (X\<^sub>1 *\<^sub>v (X\<^sub>2 *\<^sub>v \<psi>)) $ i" by simp
    thus "((X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi>) $ i = (X\<^sub>3 *\<^sub>v \<phi>) $ i"
      using idx8[OF i] x unfolding \<psi>_def \<phi>_def by (elim disjE) (simp_all add: fl ev sw del: index_mult_mat_vec)
  qed simp
qed

subsubsection \<open>Errors followed by recovery\<close>

lemma bitflip_recovery_ops_carrier': "\<forall>W \<in> set bitflip_recovery_ops. W \<in> carrier_mat 8 8"
  using bitflip_recovery_ops_kraus by (simp add: kraus_operators_altdef)

lemma bitflip_recovery_map_add: "A \<in> carrier_mat 8 8 \<Longrightarrow> B \<in> carrier_mat 8 8 \<Longrightarrow> bitflip_recovery_map (A + B) = bitflip_recovery_map A + bitflip_recovery_map B"
  unfolding bitflip_recovery_map_def by (rule kraus_map_dim_add[OF _ _ bitflip_recovery_ops_carrier'])

lemma bitflip_recovery_map_smult: "A \<in> carrier_mat 8 8 \<Longrightarrow> bitflip_recovery_map (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m bitflip_recovery_map A"
  unfolding bitflip_recovery_map_def by (rule kraus_map_dim_smult[OF _ bitflip_recovery_ops_carrier'])

lemma comb8:
  fixes A B :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  shows "complex_of_real a \<cdot>\<^sub>m A + complex_of_real b \<cdot>\<^sub>m A + complex_of_real b \<cdot>\<^sub>m A + complex_of_real b \<cdot>\<^sub>m A
         + complex_of_real c \<cdot>\<^sub>m B + complex_of_real c \<cdot>\<^sub>m B + complex_of_real c \<cdot>\<^sub>m B + complex_of_real d \<cdot>\<^sub>m B
         = complex_of_real (a + 3 * b) \<cdot>\<^sub>m A + complex_of_real (3 * c + d) \<cdot>\<^sub>m B"
  using A B by (intro eq_matI) (simp_all add: algebra_simps)

lemma outer8: "dim_vec v = 8 \<Longrightarrow> v \<oslash> v \<in> carrier_mat 8 8"
  by (rule outer_prod_carrier) simp_all

text \<open>D31-2: errors followed by recovery on an encoded state.\<close>

theorem three_bit_code_recovery:
  assumes x: "dim_vec x = 2"
  defines "\<psi> \<equiv> encode_mat *\<^sub>v x" and "\<phi> \<equiv> encode_mat *\<^sub>v swap2 x"
  shows "bitflip_recovery_map (three_bit_channel p (\<psi> \<oslash> \<psi>))
         = complex_of_real ((1 - p)^3 + 3 * p * (1 - p)^2) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)
           + complex_of_real (3 * p^2 * (1 - p) + p^3) \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)"
proof -
  have \<psi>d: "dim_vec \<psi> = 8" and \<phi>d: "dim_vec \<phi> = 8" unfolding \<psi>_def \<phi>_def by simp_all
  have c: "\<And>b. flip_bit_mat b \<in> carrier_mat 8 8" by simp
  have co: "\<And>M. M \<in> carrier_mat 8 8 \<Longrightarrow> M * (\<psi> \<oslash> \<psi>) * (M\<^sup>\<dagger>) = (M *\<^sub>v \<psi>) \<oslash> (M *\<^sub>v \<psi>)"
    by (rule conj_outer_prod[OF _ \<psi>d])
  have fl: "(X\<^sub>1 * X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = \<phi>" "(X\<^sub>2 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>1 *\<^sub>v \<phi>"
    "(X\<^sub>1 * X\<^sub>3) *\<^sub>v \<psi> = X\<^sub>2 *\<^sub>v \<phi>" "(X\<^sub>1 * X\<^sub>2) *\<^sub>v \<psi> = X\<^sub>3 *\<^sub>v \<phi>"
    using flips_on_codeword[OF x] unfolding \<psi>_def \<phi>_def by blast+
  let ?P = "\<psi> \<oslash> \<psi>" and ?Q = "\<phi> \<oslash> \<phi>"
  have E: "three_bit_channel p ?P =
     complex_of_real ((1 - p)^3) \<cdot>\<^sub>m ?P
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ((X\<^sub>1 *\<^sub>v \<psi>) \<oslash> (X\<^sub>1 *\<^sub>v \<psi>))
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ((X\<^sub>2 *\<^sub>v \<psi>) \<oslash> (X\<^sub>2 *\<^sub>v \<psi>))
     + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ((X\<^sub>3 *\<^sub>v \<psi>) \<oslash> (X\<^sub>3 *\<^sub>v \<psi>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>1 *\<^sub>v \<phi>) \<oslash> (X\<^sub>1 *\<^sub>v \<phi>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>2 *\<^sub>v \<phi>) \<oslash> (X\<^sub>2 *\<^sub>v \<phi>))
     + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ((X\<^sub>3 *\<^sub>v \<phi>) \<oslash> (X\<^sub>3 *\<^sub>v \<phi>))
     + complex_of_real (p^3) \<cdot>\<^sub>m ?Q"
    unfolding three_bit_channel_def
    by (simp only: co c mult_carrier_mat[OF c c] mult_carrier_mat[OF mult_carrier_mat[OF c c] c] fl)
  have r\<psi>: "bitflip_recovery_map ?P = ?P" "bitflip_recovery_map ((X\<^sub>1 *\<^sub>v \<psi>) \<oslash> (X\<^sub>1 *\<^sub>v \<psi>)) = ?P"
    "bitflip_recovery_map ((X\<^sub>2 *\<^sub>v \<psi>) \<oslash> (X\<^sub>2 *\<^sub>v \<psi>)) = ?P" "bitflip_recovery_map ((X\<^sub>3 *\<^sub>v \<psi>) \<oslash> (X\<^sub>3 *\<^sub>v \<psi>)) = ?P"
    unfolding \<psi>_def using bit_flip_code_recovery[OF x] by blast+
  have r\<phi>: "bitflip_recovery_map ?Q = ?Q" "bitflip_recovery_map ((X\<^sub>1 *\<^sub>v \<phi>) \<oslash> (X\<^sub>1 *\<^sub>v \<phi>)) = ?Q"
    "bitflip_recovery_map ((X\<^sub>2 *\<^sub>v \<phi>) \<oslash> (X\<^sub>2 *\<^sub>v \<phi>)) = ?Q" "bitflip_recovery_map ((X\<^sub>3 *\<^sub>v \<phi>) \<oslash> (X\<^sub>3 *\<^sub>v \<phi>)) = ?Q"
    unfolding \<phi>_def using bit_flip_code_recovery[OF swap2_dim] by blast+
  have oc: "\<And>M. M \<in> carrier_mat 8 8 \<Longrightarrow> (M *\<^sub>v \<psi>) \<oslash> (M *\<^sub>v \<psi>) \<in> carrier_mat 8 8"
       "\<And>M. M \<in> carrier_mat 8 8 \<Longrightarrow> (M *\<^sub>v \<phi>) \<oslash> (M *\<^sub>v \<phi>) \<in> carrier_mat 8 8"
    by (rule outer8, simp)+
  have Pc: "?P \<in> carrier_mat 8 8" and Qc: "?Q \<in> carrier_mat 8 8" by (rule outer8[OF \<psi>d], rule outer8[OF \<phi>d])
  have "bitflip_recovery_map (three_bit_channel p ?P)
        = complex_of_real ((1 - p)^3) \<cdot>\<^sub>m ?P + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ?P
          + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ?P + complex_of_real (p * (1 - p)^2) \<cdot>\<^sub>m ?P
          + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ?Q + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ?Q
          + complex_of_real (p^2 * (1 - p)) \<cdot>\<^sub>m ?Q + complex_of_real (p^3) \<cdot>\<^sub>m ?Q"
    unfolding E using Pc Qc oc[OF c] r\<psi>[unfolded One_nat_def] r\<phi>[unfolded One_nat_def]
    by (simp add: bitflip_recovery_map_add bitflip_recovery_map_smult r\<psi> r\<phi>)
  also have "\<dots> = complex_of_real ((1 - p)^3 + 3 * p * (1 - p)^2) \<cdot>\<^sub>m ?P
           + complex_of_real (3 * p^2 * (1 - p) + p^3) \<cdot>\<^sub>m ?Q"
    by (subst comb8[OF Pc Qc]) (simp add: mult_ac)
  finally show ?thesis .
qed

text \<open>The code is better than doing nothing iff $(1-p)^3+3p(1-p)^2\ge1-p$ iff $p\le\frac12$.\<close>

theorem three_bit_code_better_iff:
  assumes p0: "0 \<le> p" and p1: "p < 1"
  shows "(1 - p) \<le> (1 - p)^3 + 3 * p * (1 - p)^2 \<longleftrightarrow> p \<le> (1/2 :: real)"
proof -
  have e: "(1 - p)^3 + 3 * p * (1 - p)^2 - (1 - p) = (1 - p) * (p * (1 - 2 * p))"
    by (simp add: eval_nat_numeral algebra_simps)
  have q: "0 < 1 - p" using p1 by simp
  have "(1 - p) \<le> (1 - p)^3 + 3 * p * (1 - p)^2 \<longleftrightarrow> 0 \<le> (1 - p) * (p * (1 - 2 * p))" using e by linarith
  also have "\<dots> \<longleftrightarrow> 0 \<le> p * (1 - 2 * p)" using q by (simp add: zero_le_mult_iff)
  also have "\<dots> \<longleftrightarrow> p \<le> 1/2" using p0 by (cases "p = 0") (auto simp: zero_le_mult_iff)
  finally show ?thesis .
qed

subsubsection \<open>Minimum fidelities (D31-4)\<close>

lemma quad_two_outer:
  fixes \<psi> \<phi> :: "complex Matrix.vec"
  assumes \<psi>d: "dim_vec \<psi> = n" and \<phi>d: "dim_vec \<phi> = n"
  shows "\<langle>\<psi> | (a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi>\<rangle>
         = a * (\<langle>\<psi>|\<psi>\<rangle> * \<langle>\<psi>|\<psi>\<rangle>) + b * (\<langle>\<phi>|\<psi>\<rangle> * \<langle>\<psi>|\<phi>\<rangle>)"
proof -
  have Pc: "\<psi> \<oslash> \<psi> \<in> carrier_mat n n" and Qc: "\<phi> \<oslash> \<phi> \<in> carrier_mat n n"
    by (rule outer_prod_carrier[OF \<psi>d \<psi>d], rule outer_prod_carrier[OF \<phi>d \<phi>d])
  have \<psi>c: "\<psi> \<in> carrier_vec n" by (rule carrier_vecI[OF \<psi>d])
  have "(a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi> = (a * \<langle>\<psi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<psi> + (b * \<langle>\<phi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<phi>"
  proof -
    have "(a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi> = (a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)) *\<^sub>v \<psi> + (b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi>"
      by (rule add_mult_distrib_mat_vec[OF smult_carrier_mat[OF Pc] smult_carrier_mat[OF Qc] \<psi>c])
    also have "\<dots> = a \<cdot>\<^sub>v (\<langle>\<psi>|\<psi>\<rangle> \<cdot>\<^sub>v \<psi>) + b \<cdot>\<^sub>v (\<langle>\<phi>|\<psi>\<rangle> \<cdot>\<^sub>v \<phi>)"
    proof -
      have d1: "dim_col (\<psi> \<oslash> \<psi>) = dim_vec \<psi>" and d2: "dim_col (\<phi> \<oslash> \<phi>) = dim_vec \<psi>"
        using carrier_matD(2)[OF Pc] carrier_matD(2)[OF Qc] \<psi>d by simp_all
      have e2: "dim_vec \<psi> = dim_vec \<phi>" using \<psi>d \<phi>d by simp
      show ?thesis by (simp only: smult_mat_mult_vec[OF carrier_matI[OF refl refl] carrier_vecI[OF d1[symmetric]]] smult_mat_mult_vec[OF carrier_matI[OF refl refl] carrier_vecI[OF d2[symmetric]]]
          outer_prod_mult_vec[of \<psi> \<psi> \<psi>, OF refl] outer_prod_mult_vec[of \<psi> \<phi> \<phi>, OF e2])
    qed
    finally show ?thesis by (simp only: smult_smult_assoc)
  qed
  hence "\<langle>\<psi> | (a \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + b \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | (a * \<langle>\<psi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<psi> + (b * \<langle>\<phi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<phi>\<rangle>" by simp
  also have "\<dots> = (a * \<langle>\<psi>|\<psi>\<rangle>) * \<langle>\<psi>|\<psi>\<rangle> + (b * \<langle>\<phi>|\<psi>\<rangle>) * \<langle>\<psi>|\<phi>\<rangle>"
  proof -
    have e: "dim_vec ((a * \<langle>\<psi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<psi>) = dim_vec ((b * \<langle>\<phi>|\<psi>\<rangle>) \<cdot>\<^sub>v \<phi>)" using \<psi>d \<phi>d by simp
    show ?thesis by (simp only: inner_prod_right_add'[OF e] inner_prod_right_smult')
  qed
  finally show ?thesis by (simp add: mult_ac)
qed

lemma encode_inner:
  assumes u: "dim_vec u = 2" and v: "dim_vec v = 2"
  shows "\<langle>encode_mat *\<^sub>v u | encode_mat *\<^sub>v v\<rangle> = \<langle>u|v\<rangle>"
proof -
  have "\<langle>encode_mat *\<^sub>v u | encode_mat *\<^sub>v v\<rangle> = (\<Sum>i \<in> {0..<8}. cnj ((encode_mat *\<^sub>v u) $ i) * (encode_mat *\<^sub>v v) $ i)"
    by (rule inner_prod_sum) simp_all
  also have "\<dots> = cnj (u $ 0) * v $ 0 + cnj (u $ 1) * v $ 1" unfolding set_8_atLeast0 using u v by (simp add: encode_mat_mult_vec del: index_mult_mat_vec)
  also have "\<dots> = \<langle>u|v\<rangle>" unfolding inner_prod_sum[OF u v] using u v by (simp add: numeral_2_eq_2)
  finally show ?thesis .
qed

theorem code_min_fidelity:
  assumes p0: "0 \<le> p" and p1: "p \<le> 1"
  defines "c1 \<equiv> (1 - p)^3 + 3 * p * (1 - p)^2"
  shows "\<forall>x. dim_vec x = 2 \<longrightarrow> \<langle>x|x\<rangle> = 1 \<longrightarrow>
           sqrt c1 \<le> fidelity (encode_mat *\<^sub>v x) (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v x) \<oslash> (encode_mat *\<^sub>v x))))"
    and "fidelity (encode_mat *\<^sub>v unit_vec 2 0)
           (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v unit_vec 2 0) \<oslash> (encode_mat *\<^sub>v unit_vec 2 0)))) = sqrt c1"
proof -
  define c2 where "c2 = 3 * p^2 * (1 - p) + p^3"
  have c2: "0 \<le> c2" unfolding c2_def using p0 p1 by simp
  have val: "\<And>x. dim_vec x = 2 \<Longrightarrow> \<langle>x|x\<rangle> = 1 \<Longrightarrow>
      fidelity (encode_mat *\<^sub>v x) (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v x) \<oslash> (encode_mat *\<^sub>v x))))
      = sqrt (c1 + c2 * (cmod \<langle>x | swap2 x\<rangle>)^2)"
  proof -
    fix x :: "complex Matrix.vec" assume x: "dim_vec x = 2" and n: "\<langle>x|x\<rangle> = 1"
    let ?\<psi> = "encode_mat *\<^sub>v x" and ?\<phi> = "encode_mat *\<^sub>v swap2 x"
    have q: "\<langle>?\<psi> | (complex_of_real c1 \<cdot>\<^sub>m (?\<psi> \<oslash> ?\<psi>) + complex_of_real c2 \<cdot>\<^sub>m (?\<phi> \<oslash> ?\<phi>)) *\<^sub>v ?\<psi>\<rangle>
             = complex_of_real c1 * (\<langle>?\<psi>|?\<psi>\<rangle> * \<langle>?\<psi>|?\<psi>\<rangle>) + complex_of_real c2 * (\<langle>?\<phi>|?\<psi>\<rangle> * \<langle>?\<psi>|?\<phi>\<rangle>)"
      by (rule quad_two_outer) simp_all
    have ip: "\<langle>?\<psi>|?\<psi>\<rangle> = 1" "\<langle>?\<psi>|?\<phi>\<rangle> = \<langle>x | swap2 x\<rangle>" "\<langle>?\<phi>|?\<psi>\<rangle> = cnj \<langle>x | swap2 x\<rangle>"
      using encode_inner[OF x x] encode_inner[OF x swap2_dim] encode_inner[OF swap2_dim x] n
        inner_prod_cnj[of "swap2 x" x] x by simp_all
    show "fidelity ?\<psi> (bitflip_recovery_map (three_bit_channel p (?\<psi> \<oslash> ?\<psi>))) = sqrt (c1 + c2 * (cmod \<langle>x | swap2 x\<rangle>)^2)"
      unfolding fidelity_def_eq three_bit_code_recovery[OF x] c1_def[symmetric] c2_def[symmetric] q ip
      by (simp add: cnj_mult_self_cmod)
  qed
  show "\<forall>x. dim_vec x = 2 \<longrightarrow> \<langle>x|x\<rangle> = 1 \<longrightarrow>
           sqrt c1 \<le> fidelity (encode_mat *\<^sub>v x) (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v x) \<oslash> (encode_mat *\<^sub>v x))))"
    using val c2 by simp
  have e0: "dim_vec (unit_vec 2 0 :: complex Matrix.vec) = 2" "\<langle>unit_vec 2 0 | unit_vec 2 (0::nat)\<rangle> = (1::complex)"
    "\<langle>unit_vec 2 0 | swap2 (unit_vec 2 0)\<rangle> = (0::complex)"
  proof -
    show "dim_vec (unit_vec 2 0 :: complex Matrix.vec) = 2" by simp
    show "\<langle>unit_vec 2 0 | unit_vec 2 (0::nat)\<rangle> = (1::complex)"
      by (subst inner_prod_unit_vec_right) simp_all
    have "swap2 (unit_vec 2 0) = unit_vec 2 1" by (rule eq_vecI) (auto simp: swap2_def less_2_cases_iff)
    thus "\<langle>unit_vec 2 0 | swap2 (unit_vec 2 0)\<rangle> = (0::complex)"
      by (simp only:) (subst inner_prod_unit_vec_right, simp_all)
  qed
  show "fidelity (encode_mat *\<^sub>v unit_vec 2 0)
           (bitflip_recovery_map (three_bit_channel p ((encode_mat *\<^sub>v unit_vec 2 0) \<oslash> (encode_mat *\<^sub>v unit_vec 2 0)))) = sqrt c1"
    unfolding val[OF e0(1,2)] e0(3) by simp
qed

theorem nothing_min_fidelity:
  assumes p0: "0 \<le> p" and p1: "p \<le> 1"
  shows "\<forall>\<psi>. dim_vec \<psi> = 2 \<longrightarrow> \<langle>\<psi>|\<psi>\<rangle> = 1 \<longrightarrow> sqrt (1 - p) \<le> fidelity \<psi> (bit_flip_channel p (\<psi> \<oslash> \<psi>))"
    and "fidelity (unit_vec 2 0) (bit_flip_channel p (unit_vec 2 0 \<oslash> unit_vec 2 0)) = sqrt (1 - p)"
proof -
  have val: "\<And>\<psi>. dim_vec \<psi> = 2 \<Longrightarrow> \<langle>\<psi>|\<psi>\<rangle> = 1 \<Longrightarrow>
      fidelity \<psi> (bit_flip_channel p (\<psi> \<oslash> \<psi>)) = sqrt ((1 - p) + p * (cmod \<langle>\<psi> | Pauli_X *\<^sub>v \<psi>\<rangle>)^2)"
  proof -
    fix \<psi> :: "complex Matrix.vec" assume \<psi>d: "dim_vec \<psi> = 2" and n: "\<langle>\<psi>|\<psi>\<rangle> = 1"
    have Xd: "dim_vec (Pauli_X *\<^sub>v \<psi>) = 2" by (simp add: Pauli_X_def)
    have "bit_flip_channel p (\<psi> \<oslash> \<psi>) = complex_of_real (1 - p) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)
          + complex_of_real p \<cdot>\<^sub>m ((Pauli_X *\<^sub>v \<psi>) \<oslash> (Pauli_X *\<^sub>v \<psi>))"
      unfolding bit_flip_channel_def using conj_outer_prod[OF Pauli_X_carrier \<psi>d] by simp
    moreover have "\<langle>\<psi> | (complex_of_real (1 - p) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>) + complex_of_real p \<cdot>\<^sub>m ((Pauli_X *\<^sub>v \<psi>) \<oslash> (Pauli_X *\<^sub>v \<psi>))) *\<^sub>v \<psi>\<rangle>
          = complex_of_real (1 - p) * (\<langle>\<psi>|\<psi>\<rangle> * \<langle>\<psi>|\<psi>\<rangle>)
            + complex_of_real p * (\<langle>Pauli_X *\<^sub>v \<psi>|\<psi>\<rangle> * \<langle>\<psi>|Pauli_X *\<^sub>v \<psi>\<rangle>)"
      by (rule quad_two_outer[OF \<psi>d Xd])
    moreover have "\<langle>Pauli_X *\<^sub>v \<psi>|\<psi>\<rangle> = cnj \<langle>\<psi>|Pauli_X *\<^sub>v \<psi>\<rangle>" by (rule inner_prod_cnj) (use \<psi>d Xd in simp)
    ultimately show "fidelity \<psi> (bit_flip_channel p (\<psi> \<oslash> \<psi>)) = sqrt ((1 - p) + p * (cmod \<langle>\<psi> | Pauli_X *\<^sub>v \<psi>\<rangle>)^2)"
      unfolding fidelity_def_eq n by (simp add: cnj_mult_self_cmod)
  qed
  show "\<forall>\<psi>. dim_vec \<psi> = 2 \<longrightarrow> \<langle>\<psi>|\<psi>\<rangle> = 1 \<longrightarrow> sqrt (1 - p) \<le> fidelity \<psi> (bit_flip_channel p (\<psi> \<oslash> \<psi>))"
    using val p0 by simp
  have Xe: "Pauli_X *\<^sub>v unit_vec 2 0 = unit_vec 2 1"
    by (rule eq_vecI) (auto simp: Pauli_X_def less_2_cases_iff scalar_prod_def)
  have e: "\<langle>unit_vec 2 0 | unit_vec 2 (0::nat)\<rangle> = (1::complex)" by (subst inner_prod_unit_vec_right) simp_all
  have z: "\<langle>unit_vec 2 0 | unit_vec 2 (1::nat)\<rangle> = (0::complex)" by (subst inner_prod_unit_vec_right) simp_all
  show "fidelity (unit_vec 2 0) (bit_flip_channel p (unit_vec 2 0 \<oslash> unit_vec 2 0)) = sqrt (1 - p)"
  proof -
    have d: "dim_vec (unit_vec 2 0 :: complex Matrix.vec) = 2" by simp
    show ?thesis unfolding val[OF d e] Xe z by simp
  qed
qed

end
