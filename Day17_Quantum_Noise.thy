(*  Title:   Day17_Quantum_Noise.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 5 October 2011 (Day 17)
*)

theory Day17_Quantum_Noise
  imports Day15_Partial_Traces
begin

section \<open>Day 17 (5 October 2011): measurement maps, quantum noise, completely positive maps\<close>

subsection \<open>Measurement maps\<close>

text \<open>Measuring $\psi$ with $\{M_\alpha\}$ and keeping the outcome as an ensemble gives the density
matrix $\sum_\alpha p_\alpha(\psi)\ketbra{M_\alpha\psi/\norm{M_\alpha\psi}}{M_\alpha\psi/\norm{M_\alpha\psi}}
=\sum_\alpha M_\alpha(\psi\psi^*)M_\alpha^*$; for an ensemble with density $\rho_1$ one obtains
$M(\rho_1)=\sum_\alpha M_\alpha\rho_1M_\alpha^*$: a linear map on $L(\Hil_A)$ sending density
matrices to density matrices.

Classical noise flips a bit with some probability; probability vectors evolve by stochastic
matrices (non-negative entries, columns summing to one; doubly stochastic if rows do too).
Quantum noise: with an environment $\Hil_E$ in state $\ket\phi$, the system
$\rho\otimes\ketbra\phi\phi$ evolves by a unitary $U=(U_{ij})$ on $\Hil_A\otimes\Hil_E$ and lab A sees
\[ \tr_E\bigl(U(\rho\otimes\ketbra\phi\phi)U^*\bigr)=\sum_iW_i\rho W_i^*,\qquad
   W_i=\sum_kU_{ik}\alpha_k,\qquad \sum_iW_i^*W_i=I. \]
Measurement by an intruder and environmental noise are maps of the same form
$\rho\mapsto\sum_\alpha X_\alpha\rho X_\alpha^*$ with $\sum X_\alpha^*X_\alpha=I$.  The environment
computation is \<open>environment_model\<close> below.

Third way, axiomatic: a quantum event is a linear $\Phi:L(\Hil_A)\to L(\Hil_A)$.
\begin{notesprop}
$\Phi$ maps density matrices to density matrices iff $\Phi$ is positive ($\rho\ge0\Rightarrow\Phi(\rho)\ge0$)
and trace preserving ($\tr\Phi(X)=\tr X$); then $\Phi\otimes I_{L(\Hil_B)}$ also maps density
matrices to density matrices for every $\Hil_B$.
\end{notesprop}
\begin{notesdef}
$\Phi$ is \emph{completely positive} if $\Phi\otimes I_{L(\Hil_B)}$ is positive for every
finite-dimensional $\Hil_B$.
\end{notesdef}
\begin{notestheorem}[Choi--Kraus]
$\Phi:L(\Hil_A)\to L(\Hil_A)$ is completely positive and trace preserving iff
$\Phi(X)=\sum_iE_iXE_i^*$ for matrices $E_i$ with $\sum_iE_i^*E_i=I$.
\end{notestheorem}
The proposition is \<open>density_preserving_iff_positive_tp\<close> on Day 18, whose decomposition
into positives it uses;
complete positivity is defined below and the Choi--Kraus theorem is \<open>choi_kraus_cptp\<close> on
Day 19.\<close>

definition meas_map :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "meas_map Ms \<rho> \<equiv>
     foldr (\<lambda>M acc. M * \<rho> * (M\<^sup>\<dagger>) + acc) Ms (0\<^sub>m (dim_row \<rho>) (dim_col \<rho>))"

lemma meas_map_Nil [simp]:
  "meas_map [] \<rho> = 0\<^sub>m (dim_row \<rho>) (dim_col \<rho>)"
  by (simp add: meas_map_def)

lemma meas_map_Cons [simp]:
  "meas_map (M # Ms) \<rho> = M * \<rho> * (M\<^sup>\<dagger>) + meas_map Ms \<rho>"
  by (simp add: meas_map_def)

lemma meas_map_carrier:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "meas_map Ms \<rho> \<in> carrier_mat n n"
  using Ms_c
proof (induction Ms)
  case Nil
  show ?case using \<rho>_c by simp
next
  case (Cons M Ms)
  hence M_c: "M \<in> carrier_mat n n" and Ms_c': "\<forall>X \<in> set Ms. X \<in> carrier_mat n n"
    by auto
  have Mdag_c: "M\<^sup>\<dagger> \<in> carrier_mat n n"
    using M_c
    by (simp add: dagger_def) 
  have term_c: "M * \<rho> * (M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c \<rho>_c Mdag_c by simp
  have rec_c: "meas_map Ms \<rho> \<in> carrier_mat n n"
    using Cons.IH Ms_c' by blast
  show ?case
    using term_c rec_c by simp
qed

text \<open>If the outcome of a measurement is not recorded, $\rho\mapsto\sum_iM_i\rho M_i^*$.  Each term is
positive, $\braket x{M\rho M^*x}=\braket{M^*x}{\rho\,M^*x}\ge0$, and cyclicity of the trace gives
\[ \Tr\sum_iM_i\rho M_i^*=\Tr\Bigl(\bigl(\sum_iM_i^*M_i\bigr)\rho\Bigr)=\Tr\rho, \]
so densities go to densities.\<close>

lemma meas_map_psd:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
      and \<rho>_psd: "psd \<rho>"
  shows "psd (meas_map Ms \<rho>)"
  using Ms_c
proof (induction Ms)
  case Nil
  have "meas_map [] \<rho> = 0\<^sub>m n n" using \<rho>_c by simp
  thus ?case using psd_zero_mat by simp
next
  case (Cons M Ms)
  hence M_c: "M \<in> carrier_mat n n" and Ms_c': "\<forall>X \<in> set Ms. X \<in> carrier_mat n n"
    by auto
  have Mdag_c: "(M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c by (rule dagger_carrier)
  obtain Q where Qc: "Q \<in> carrier_mat n n" and Qpsd: "psd Q" and QQ: "Q * Q = \<rho>"
    using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
  have Qdag: "(Q\<^sup>\<dagger>) = Q" using Qpsd by (simp add: psd_def hermitian_def)
  have MQ_c: "M * Q \<in> carrier_mat n n"
    using M_c Qc by (intro mult_carrier_mat) auto
  have MQdag_c: "((M * Q)\<^sup>\<dagger>) \<in> carrier_mat n n"
    using MQ_c by (rule dagger_carrier)

  have term_eq: "M * \<rho> * (M\<^sup>\<dagger>) = (M * Q) * ((M * Q)\<^sup>\<dagger>)"
  proof -
    have dagprod: "((M * Q)\<^sup>\<dagger>) = (Q\<^sup>\<dagger>) * (M\<^sup>\<dagger>)"
      using M_c Qc by (simp add: dagger_of_prod)
    have dagprod': "((M * Q)\<^sup>\<dagger>) = Q * (M\<^sup>\<dagger>)"
      using dagprod Qdag by simp
    have a1: "(M * Q) * ((M * Q)\<^sup>\<dagger>) = (M * Q) * (Q * (M\<^sup>\<dagger>))"
      using dagprod' by simp
    have a2: "(M * Q) * (Q * (M\<^sup>\<dagger>)) = M * Q * Q * (M\<^sup>\<dagger>)"
      using M_c Qc Mdag_c
      by (metis assoc_mult_mat mult_carrier_mat)
    have a3: "M * Q * Q * (M\<^sup>\<dagger>) = M * (Q * Q) * (M\<^sup>\<dagger>)"
      using M_c Qc by (metis assoc_mult_mat)
    have a4: "M * (Q * Q) * (M\<^sup>\<dagger>) = M * \<rho> * (M\<^sup>\<dagger>)" using QQ by simp
    show ?thesis using a1 a2 a3 a4 by simp
  qed

  have term_psd: "psd (M * \<rho> * (M\<^sup>\<dagger>))"
  proof -
    have psd_dd: "psd (((M * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((M * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF MQdag_c] .
    have dd_eq: "((M * Q)\<^sup>\<dagger>\<^sup>\<dagger>) = M * Q"
      using MQ_c by (simp add: dagger_of_dagger_is_id)
    from psd_dd dd_eq have "psd ((M * Q) * ((M * Q)\<^sup>\<dagger>))" by simp
    thus ?thesis using term_eq by simp
  qed
  have term_c: "M * \<rho> * (M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c \<rho>_c Mdag_c by (intro mult_carrier_mat) auto
  have IH_c: "meas_map Ms \<rho> \<in> carrier_mat n n"
    using meas_map_carrier[OF Ms_c' \<rho>_c] .
  have IH_psd: "psd (meas_map Ms \<rho>)"
    using Cons.IH Ms_c' by blast
  have "psd (M * \<rho> * (M\<^sup>\<dagger>) + meas_map Ms \<rho>)"
    using term_psd IH_psd term_c IH_c by (rule psd_add_psd)
  thus ?case by simp
qed

lemma foldr_MdagM_carrier:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
  shows "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) \<in> carrier_mat n n"
  using Ms_c
proof (induction Ms)
  case Nil
  show ?case by simp
next
  case (Cons K Ks)
  hence K_c: "K \<in> carrier_mat n n" and Ks_c: "\<forall>X \<in> set Ks. X \<in> carrier_mat n n"
    by auto
  have Kdag_c: "(K\<^sup>\<dagger>) \<in> carrier_mat n n" using K_c by (rule dagger_carrier)
  have KdK_c: "(K\<^sup>\<dagger>) * K \<in> carrier_mat n n"
    using Kdag_c K_c by (intro mult_carrier_mat) auto
  have rec_c: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ks (0\<^sub>m n n) \<in> carrier_mat n n"
    using Cons.IH Ks_c by blast
  show ?case using KdK_c rec_c by simp
qed

lemma meas_map_trace_aux:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "Tr (meas_map Ms \<rho>) =
         Tr (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) * \<rho>)"
  using Ms_c
proof (induction Ms)
  case Nil
  have lhs: "Tr (meas_map [] \<rho>) = 0"
    using \<rho>_c by (simp add: Tr_def)
  have "(0\<^sub>m n n :: complex Matrix.mat) * \<rho> = 0\<^sub>m n n"
    using \<rho>_c by simp
  hence rhs: "Tr ((0\<^sub>m n n :: complex Matrix.mat) * \<rho>) = 0"
    by (simp add: Tr_def)
  show ?case using lhs rhs by simp
next
  case (Cons M Ms)
  hence M_c: "M \<in> carrier_mat n n" and Ms_c': "\<forall>X \<in> set Ms. X \<in> carrier_mat n n"
    by auto
  have Mdag_c: "(M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c by (rule dagger_carrier)
  have MdM_c: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n"
    using Mdag_c M_c by (intro mult_carrier_mat) auto
  have MrM_c: "M * \<rho> * (M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c \<rho>_c Mdag_c by (intro mult_carrier_mat) auto
  have IH_carr: "meas_map Ms \<rho> \<in> carrier_mat n n"
    using meas_map_carrier[OF Ms_c' \<rho>_c] .
  define S where S_def:
    "S = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)"
  have S_carr: "S \<in> carrier_mat n n"
    unfolding S_def using foldr_MdagM_carrier[OF Ms_c'].

  have IH: "Tr (meas_map Ms \<rho>) = Tr (S * \<rho>)"
    using Cons.IH[OF Ms_c'] by (simp add: S_def)

  have step_a: "Tr (M * \<rho> * (M\<^sup>\<dagger>)) = Tr ((M\<^sup>\<dagger>) * M * \<rho>)"
  proof -
    have "Tr (M * \<rho> * (M\<^sup>\<dagger>)) = Tr ((M\<^sup>\<dagger>) * (M * \<rho>))"
      using M_c \<rho>_c Mdag_c by (intro Tr_cyclic) auto
    also have "\<dots> = Tr ((M\<^sup>\<dagger>) * M * \<rho>)"
      using Mdag_c M_c \<rho>_c by (metis assoc_mult_mat)
    finally show ?thesis .
  qed

  have "Tr (meas_map (M # Ms) \<rho>) = Tr (M * \<rho> * (M\<^sup>\<dagger>) + meas_map Ms \<rho>)"
    by simp
  also have "\<dots> = Tr (M * \<rho> * (M\<^sup>\<dagger>)) + Tr (meas_map Ms \<rho>)"
    using MrM_c IH_carr by (intro Tr_add) auto
  also have "\<dots> = Tr ((M\<^sup>\<dagger>) * M * \<rho>) + Tr (S * \<rho>)"
    using step_a IH by simp
  also have "\<dots> = Tr (((M\<^sup>\<dagger>) * M) * \<rho> + S * \<rho>)"
    using MdM_c S_carr \<rho>_c by (intro Tr_add[symmetric]) auto
  also have "\<dots> = Tr (((M\<^sup>\<dagger>) * M + S) * \<rho>)"
    using MdM_c S_carr \<rho>_c by (simp add: add_mult_distrib_mat)
  also have "\<dots> = Tr (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (M # Ms) (0\<^sub>m n n) * \<rho>)"
    by (simp add: S_def)
  finally show ?case.
qed

lemma meas_map_density:
  assumes ms: "measurement_system n Ms"
      and dm: "density_matrix n \<rho>"
  shows "density_matrix n (meas_map Ms \<rho>)"
proof -
  have rho_carr: "\<rho> \<in> carrier_mat n n"
    using dm by (auto simp: density_matrix_def)
  have rho_psd: "psd \<rho>"
    using dm by (auto simp: density_matrix_def)
  have rho_tr: "Tr \<rho> = 1"
    using dm by (auto simp: density_matrix_def)
  have Ms_carr: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    using ms by (simp add: measurement_system_def)
  have id_eq: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n"
    using ms by (simp add: measurement_system_def)

  have map_carr: "meas_map Ms \<rho> \<in> carrier_mat n n"
    using meas_map_carrier[OF Ms_carr rho_carr] .

  have map_psd: "psd (meas_map Ms \<rho>)"
    using meas_map_psd[OF Ms_carr rho_carr rho_psd] .

  have "Tr (meas_map Ms \<rho>) = Tr (1\<^sub>m n * \<rho>)"
    using meas_map_trace_aux[OF Ms_carr rho_carr] id_eq by simp
  also have "\<dots> = Tr \<rho>"
    using rho_carr by simp
  finally have map_tr: "Tr (meas_map Ms \<rho>) = 1"
    using rho_tr by simp

  show ?thesis
    unfolding density_matrix_def using map_carr map_psd map_tr by simp
qed

subsection \<open>Kraus maps, positive maps, complete positivity\<close>

text \<open>A \emph{Kraus map} $\rho\mapsto\sum_iW_i\rho W_i^\dagger$ is \<open>kraus_map_dim d Ws\<close>; the list
\<open>Ws\<close> is a list of \emph{Kraus operators} (\<open>kraus_operators n d Ws\<close>) when
$\sum_iW_i^\dagger W_i=I_n$.  Positive, trace-preserving and unital maps are defined on the
carrier $M_n$.  The amplification $\Phi^{(p)}=\Phi\otimes\mathrm{id}_p$ acts on block matrices by
$(X_{ab})\mapsto(\Phi(X_{ab}))$ (\<open>amplification n d p \<Phi>\<close>), and $\Phi$ is $p$-positive when
$\Phi^{(p)}$ is positive, completely positive when it is $p$-positive for all $p$.  The main result
of the subsection: Kraus maps are completely positive.\<close>

definition kraus_map_dim :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "kraus_map_dim d Ws \<rho> \<equiv>
     foldr (\<lambda>W acc. W * \<rho> * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d)"

definition kraus_map :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "kraus_map Ws \<rho> \<equiv> kraus_map_dim (dim_row \<rho>) Ws \<rho>"

definition kraus_operators :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "kraus_operators n d Ws \<equiv>
     (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and>
     foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Ws (0\<^sub>m n n) = 1\<^sub>m n"

lemma kraus_map_dim_Nil [simp]:
  "kraus_map_dim d [] \<rho> = 0\<^sub>m d d"
  by (simp add: kraus_map_dim_def)

lemma kraus_map_dim_Cons [simp]:
  "kraus_map_dim d (W # Ws) \<rho> =
     W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>"
  by (simp add: kraus_map_dim_def)

lemma kraus_map_dim_two:
  assumes V: "V \<in> carrier_mat d n" and W: "W \<in> carrier_mat d n" and \<rho>: "\<rho> \<in> carrier_mat n n"
  shows "kraus_map_dim d [V, W] \<rho> = V * \<rho> * (V\<^sup>\<dagger>) + W * \<rho> * (W\<^sup>\<dagger>)"
  using mult_carrier_mat[OF mult_carrier_mat[OF W \<rho>] dagger_carrier[OF W]] by simp

lemma kraus_map_dim_single:
  assumes W: "W \<in> carrier_mat d n" and \<rho>: "\<rho> \<in> carrier_mat n n"
  shows "kraus_map_dim d [W] \<rho> = W * \<rho> * (W\<^sup>\<dagger>)"
  using mult_carrier_mat[OF mult_carrier_mat[OF W \<rho>] dagger_carrier[OF W]] by simp

lemma kraus_map_dim_carrier:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
  using Ws_c
proof (induction Ws)
  case Nil
  show ?case by simp
next
  case (Cons W Ws)
  hence W_c: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  have term_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
    using W_c \<rho>_c Wdag_c by (intro mult_carrier_mat) auto
  have rec_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using Cons.IH Ws_c' by blast
  show ?case
    using term_c rec_c by simp
qed

text \<open>At the identity a Kraus map gives $\sum_iW_iW_i^*$; so it is unital iff
$\sum_iW_iW_i^*=I_d$.\<close>

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

text \<open>The same computation shows that every Kraus map $\Phi(\rho)=\sum_iW_i\rho W_i^*$, with
$W_i\in M_{d,n}$, sends positive matrices to positive matrices.\<close>

lemma kraus_map_dim_psd:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
      and \<rho>_psd: "psd \<rho>"
  shows "psd (kraus_map_dim d Ws \<rho>)"
  using Ws_c
proof (induction Ws)
  case Nil
  show ?case by simp
next
  case (Cons W Ws)
  hence W_c: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  obtain Q where Qc: "Q \<in> carrier_mat n n" and Qpsd: "psd Q" and QQ: "Q * Q = \<rho>"
    using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
  have Qdag: "Q\<^sup>\<dagger> = Q"
    using Qpsd by (simp add: psd_def hermitian_def)
  have WQ_c: "W * Q \<in> carrier_mat d n"
    using W_c Qc by (intro mult_carrier_mat) auto
  have WQdag_c: "(W * Q)\<^sup>\<dagger> \<in> carrier_mat n d"
    using WQ_c by (rule dagger_carrier)

  have term_eq: "W * \<rho> * (W\<^sup>\<dagger>) = (W * Q) * ((W * Q)\<^sup>\<dagger>)"
  proof -
    have dagprod: "(W * Q)\<^sup>\<dagger> = (Q\<^sup>\<dagger>) * (W\<^sup>\<dagger>)"
      using W_c Qc by (simp add: dagger_of_prod)
    have dagprod': "(W * Q)\<^sup>\<dagger> = Q * (W\<^sup>\<dagger>)"
      using dagprod Qdag by simp
    have "(W * Q) * ((W * Q)\<^sup>\<dagger>) = (W * Q) * (Q * (W\<^sup>\<dagger>))"
      using dagprod' by simp
    also have "\<dots> = W * Q * Q * (W\<^sup>\<dagger>)"
      using W_c Qc Wdag_c by (metis assoc_mult_mat mult_carrier_mat)
    also have "\<dots> = W * (Q * Q) * (W\<^sup>\<dagger>)"
      using W_c Qc by (metis assoc_mult_mat)
    also have "\<dots> = W * \<rho> * (W\<^sup>\<dagger>)"
      using QQ by simp
    finally show ?thesis by simp
  qed

  have term_psd: "psd (W * \<rho> * (W\<^sup>\<dagger>))"
  proof -
    have psd_dd: "psd (((W * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((W * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF WQdag_c] .
    have dd_eq: "((W * Q)\<^sup>\<dagger>\<^sup>\<dagger>) = W * Q"
      using WQ_c by (simp add: dagger_of_dagger_is_id)
    from psd_dd dd_eq have "psd ((W * Q) * ((W * Q)\<^sup>\<dagger>))"
      by simp
    thus ?thesis
      using term_eq by simp
  qed
  have term_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
    using W_c \<rho>_c Wdag_c by (intro mult_carrier_mat) auto
  have IH_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' \<rho>_c] .
  have IH_psd: "psd (kraus_map_dim d Ws \<rho>)"
    using Cons.IH Ws_c' by blast
  have "psd (W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>)"
    using term_psd IH_psd term_c IH_c by (rule psd_add_psd)
  thus ?case by simp
qed

definition positive_map :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "positive_map n d \<Phi> \<equiv>
     (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d) \<and>
     (\<forall>P. P \<in> carrier_mat n n \<longrightarrow> psd P \<longrightarrow> psd (\<Phi> P))"

lemma kraus_map_dim_positive_map:
  assumes Ws: "kraus_operators n d Ws"
  shows "positive_map n d (kraus_map_dim d Ws)"
proof -
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    using Ws by (simp add: kraus_operators_def)
  show ?thesis
    unfolding positive_map_def
    using kraus_map_dim_carrier[OF Ws_c]
          kraus_map_dim_psd[OF Ws_c]
    by blast
qed

definition trace_preserving :: "nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "trace_preserving n \<Phi> \<equiv>
     \<forall>X. X \<in> carrier_mat n n \<longrightarrow> Tr (\<Phi> X) = Tr X"

definition unital_map :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "unital_map n d \<Phi> \<equiv> \<Phi> (1\<^sub>m n) = 1\<^sub>m d"

text \<open>A $pn\times pn$ matrix is a $p\times p$ matrix of $n\times n$ blocks, $(X_{ab})_{rc}=X_{an+r,\,bn+c}$:
\[ X=\begin{pmatrix}X_{00}&\cdots&X_{0,p-1}\\ \vdots&&\vdots\\ X_{p-1,0}&\cdots&X_{p-1,p-1}\end{pmatrix}. \]
These blocks are contiguous; the blocks of Day 16 (\<open>block\<close>) are interleaved.\<close>

definition block_of_mat :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "block_of_mat n x a b \<equiv>
     Matrix.mat n n (\<lambda>(r,c). x $$ (a*n + r, b*n + c))"

lemma block_of_mat_carrier [simp]:
  "block_of_mat n X a b \<in> carrier_mat n n"
  by (simp add: block_of_mat_def)

lemma block_of_mat_index:
  assumes "r < n" and "c < n"
  shows "block_of_mat n X a b $$ (r,c) = X $$ (a*n + r, b*n + c)"
  using assms by (simp add: block_of_mat_def)

lemma block_of_mat_single:
  assumes X: "X \<in> carrier_mat n n"
  shows "block_of_mat n X 0 0 = X"
proof (rule eq_matI)
  show "dim_row (block_of_mat n X 0 0) = dim_row X"
    using X by (simp add: block_of_mat_def)
  show "dim_col (block_of_mat n X 0 0) = dim_col X"
    using X by (simp add: block_of_mat_def)
next
  fix i j
  assume "i < dim_row X" and "j < dim_col X"
  then have "i < n" and "j < n"
    using X by auto
  thus "block_of_mat n X 0 0 $$ (i,j) = X $$ (i,j)"
    by (simp add: block_of_mat_index)
qed

text \<open>A $pn\times pn$ matrix is the sum of its blocks in place: $x=\sum_{a,b}E_{ab}\otimes x_{ab}$.\<close>

lemma block_of_mat_decomposition:
  assumes x: "x \<in> carrier_mat (p*n) (p*n)" and n: "0 < n"
  shows "x = msum (p*n) (p*n) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) (List.product [0..<p] [0..<p])"
proof (rule eq_matI)
  fix i j assume "i < dim_row (msum (p*n) (p*n) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) (List.product [0..<p] [0..<p]))"
    "j < dim_col (msum (p*n) (p*n) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) (List.product [0..<p] [0..<p]))"
  hence i: "i < p*n" and j: "j < p*n" by simp_all
  have p: "0 < p" using i by (cases p) auto
  have e: "(E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) $$ (i, j)
         = (if b = j div n then if a = i div n then x $$ (i, j) else 0 else 0)"
    if "a < p" "b < p" for a b
    using index_tensor_mat[where rA = p and cA = p and rB = n and cB = n, OF _ _ _ _ i j p n] that
          less_mult_imp_div_less[OF i] less_mult_imp_div_less[OF j] mod_less_divisor[OF n]
    by (auto simp: block_of_mat_def div_mult_mod_eq)
  have "msum (p*n) (p*n) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) (List.product [0..<p] [0..<p]) $$ (i, j)
      = (\<Sum>a<p. \<Sum>b<p. if b = j div n then if a = i div n then x $$ (i, j) else 0 else 0)"
    by (subst msum_pairs_index) (use i j in \<open>auto simp: e intro!: sum.cong\<close>)
  also have "\<dots> = x $$ (i, j)"
    using less_mult_imp_div_less[OF i] less_mult_imp_div_less[OF j] by (simp add: sum.delta)
  finally show "x $$ (i, j) = msum (p*n) (p*n) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) (List.product [0..<p] [0..<p]) $$ (i, j)" ..
qed (use x in auto)

text \<open>The amplification $\Phi^{(p)}=\mathrm{id}_p\otimes\Phi$ applies $\Phi$ block by block,
$\Phi^{(p)}\bigl((X_{ab})\bigr)=\bigl(\Phi(X_{ab})\bigr)$.  $\Phi$ is \emph{$p$-positive} if $\Phi^{(p)}$ is
positive, and \emph{completely positive} if it is $p$-positive for every $p$.\<close>

definition amplification :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "amplification n d p \<Phi> x \<equiv>
     Matrix.mat (p*d) (p*d)
       (\<lambda>(i,j). \<Phi> (block_of_mat n x (i div d) (j div d)) $$
             (i mod d, j mod d))"

lemma amplification_carrier [simp]:
  "amplification n d p \<Phi> X \<in> carrier_mat (p*d) (p*d)"
  by (simp add: amplification_def)

lemma amplification_dims [simp]:
  "dim_row (amplification n d p \<Phi> x) = p*d" "dim_col (amplification n d p \<Phi> x) = p*d"
  by (simp_all add: amplification_def)

lemma amplification_index:
  assumes "i < p*d" and "j < p*d"
  shows "amplification n d p \<Phi> X $$ (i,j) =
         \<Phi> (block_of_mat n X (i div d) (j div d)) $$
             (i mod d, j mod d)"
  using assms by (simp add: amplification_def)

text \<open>So $\Phi^{(p)}(x)=\sum_{a,b}E_{ab}\otimes\Phi(x_{ab})$, and $\Phi^{(p)}$ is linear in $\Phi$.\<close>

lemma amplification_blocks:
  assumes \<Phi>: "\<And>a b. a < p \<Longrightarrow> b < p \<Longrightarrow> \<Phi> (block_of_mat n x a b) \<in> carrier_mat d d" and d: "0 < d"
  shows "amplification n d p \<Phi> x
       = msum (p*d) (p*d) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> \<Phi> (block_of_mat n x a b)) (List.product [0..<p] [0..<p])"
proof (rule eq_matI)
  fix i j assume "i < dim_row (msum (p*d) (p*d) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> \<Phi> (block_of_mat n x a b)) (List.product [0..<p] [0..<p]))"
    "j < dim_col (msum (p*d) (p*d) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> \<Phi> (block_of_mat n x a b)) (List.product [0..<p] [0..<p]))"
  hence i: "i < p*d" and j: "j < p*d" by simp_all
  have p: "0 < p" using i by (cases p) auto
  have e: "(E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> \<Phi> (block_of_mat n x a b)) $$ (i, j)
         = (if b = j div d then if a = i div d then \<Phi> (block_of_mat n x a b) $$ (i mod d, j mod d) else 0 else 0)"
    if "a < p" "b < p" for a b
    using index_tensor_mat[where rA = p and cA = p and rB = d and cB = d, OF _ _ _ _ i j p d] that
          carrier_matD[OF \<Phi>[OF that]] less_mult_imp_div_less[OF i] less_mult_imp_div_less[OF j] by auto
  have "msum (p*d) (p*d) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> \<Phi> (block_of_mat n x a b)) (List.product [0..<p] [0..<p]) $$ (i, j)
      = (\<Sum>a<p. \<Sum>b<p. if b = j div d then if a = i div d then \<Phi> (block_of_mat n x a b) $$ (i mod d, j mod d) else 0 else 0)"
    by (subst msum_pairs_index) (use i j in \<open>auto simp: e \<Phi> intro!: sum.cong\<close>)
  also have "\<dots> = amplification n d p \<Phi> x $$ (i, j)"
    using less_mult_imp_div_less[OF i] less_mult_imp_div_less[OF j] i j
    by (simp add: sum.delta amplification_index)
  finally show "amplification n d p \<Phi> x $$ (i, j)
      = msum (p*d) (p*d) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> \<Phi> (block_of_mat n x a b)) (List.product [0..<p] [0..<p]) $$ (i, j)" ..
qed auto

lemma amplification_zero_map:
  assumes dpos: "0 < d"
  shows "amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x = 0\<^sub>m (p*d) (p*d)"
  using dpos by (intro eq_matI) (auto simp: amplification_def)

lemma amplification_add:
  assumes dpos: "0 < d"
      and F: "\<And>a b. F (block_of_mat n x a b) \<in> carrier_mat d d"
      and G: "\<And>a b. G (block_of_mat n x a b) \<in> carrier_mat d d"
  shows "amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x = amplification n d p F x + amplification n d p G x"
  using dpos by (intro eq_matI) (auto simp: amplification_index carrier_matD[OF F] carrier_matD[OF G])

text \<open>The amplification of a Kraus map is a Kraus map, with operators $I_p\otimes W_i$:
\[ \Phi^{(p)}(X)=\sum_i(I_p\otimes W_i)\,X\,(I_p\otimes W_i)^*, \]
since $(I_p\otimes W)X(I_p\otimes W)^*$ has the blocks $WX_{ab}W^*$.  The index computations below
check this entry by entry.\<close>

lemma tensor_id_kraus_carrier:
  assumes W: "W \<in> carrier_mat d n"
  shows "(1\<^sub>m p \<Otimes> W) \<in> carrier_mat (p*d) (p*n)"
  using W by simp

lemma tensor_id_kraus_list_carrier:
  assumes Ws: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "\<forall>L \<in> set (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws).
           L \<in> carrier_mat (p*d) (p*n)"
  using Ws tensor_id_kraus_carrier by auto

text \<open>Block by block, $(I\otimes W)(E_{ab}\otimes x_{ab})(I\otimes W)^*=E_{ab}\otimes Wx_{ab}W^*$, so the
amplification of $X\mapsto WXW^*$ is conjugation by $I_p\otimes W$.\<close>

lemma tensor_unit_sandwich:
  assumes W: "W \<in> carrier_mat d n" and B: "B \<in> carrier_mat n n"
  shows "(1\<^sub>m p \<Otimes> W) * (E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> B) * ((1\<^sub>m p \<Otimes> W)\<^sup>\<dagger>) = E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> (W * B * (W\<^sup>\<dagger>))"
proof -
  have "(1\<^sub>m p \<Otimes> W)\<^sup>\<dagger> = 1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)" by (simp add: hermite_cnj_of_tensor)
  thus ?thesis using carrier_matD[OF W] carrier_matD[OF B] carrier_matD[OF dagger_carrier[OF W]]
    by (simp add: tensor_mat_mult)
qed

lemma amplification_sandwich:
  assumes W: "W \<in> carrier_mat d n" and x: "x \<in> carrier_mat (p*n) (p*n)" and n: "0 < n" and d: "0 < d"
  shows "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x = (1\<^sub>m p \<Otimes> W) * x * ((1\<^sub>m p \<Otimes> W)\<^sup>\<dagger>)"
proof -
  let ?P = "List.product [0..<p] [0..<p]" and ?I = "1\<^sub>m p \<Otimes> W"
  have Ic: "?I \<in> carrier_mat (p*d) (p*n)" using W by simp
  have Id: "?I\<^sup>\<dagger> \<in> carrier_mat (p*n) (p*d)" by (rule dagger_carrier[OF Ic])
  have t: "\<And>a b. E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b \<in> carrier_mat (p*n) (p*n)" by simp
  have "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x
      = msum (p*d) (p*d) (\<lambda>(a, b). ?I * (E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) * (?I\<^sup>\<dagger>)) ?P"
    by (subst amplification_blocks[OF _ d])
       (use W in \<open>auto simp: tensor_unit_sandwich[OF W block_of_mat_carrier] intro!: mult_carrier_mat dagger_carrier\<close>)
  also have "\<dots> = ?I * msum (p*n) (p*n) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) ?P * (?I\<^sup>\<dagger>)"
    by (simp only: msum_pairs_mult_left[OF t Ic] msum_pairs_mult_right[OF _ Id] mult_carrier_mat[OF Ic t])
  also have "msum (p*n) (p*n) (\<lambda>(a, b). E\<lbrakk>a,b ; p,p\<rbrakk> \<Otimes> block_of_mat n x a b) ?P = x"
    by (rule block_of_mat_decomposition[OF x n, symmetric])
  finally show ?thesis .
qed

lemma amplification_kraus_map_dim:
  assumes Ws: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and x: "x \<in> carrier_mat (p*n) (p*n)"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "amplification n d p (kraus_map_dim d Ws) x =
         kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) x"
  using Ws
proof (induction Ws)
  case Nil
  have "kraus_map_dim d [] = (\<lambda>\<rho>. 0\<^sub>m d d)" by (rule ext) simp
  thus ?case by (simp add: amplification_zero_map[OF dpos])
next
  case (Cons W Ws)
  have W: "W \<in> carrier_mat d n" and Ws: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" using Cons.prems by auto
  have "kraus_map_dim d (W # Ws) = (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>)" by (rule ext) simp
  hence "amplification n d p (kraus_map_dim d (W # Ws)) x
       = amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x + amplification n d p (kraus_map_dim d Ws) x"
    using amplification_add[OF dpos, of "\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)" n x "kraus_map_dim d Ws" p]
          mult_carrier_mat[OF mult_carrier_mat[OF W block_of_mat_carrier] dagger_carrier[OF W]]
          kraus_map_dim_carrier[OF Ws block_of_mat_carrier] by simp
  also have "\<dots> = (1\<^sub>m p \<Otimes> W) * x * ((1\<^sub>m p \<Otimes> W)\<^sup>\<dagger>) + kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) x"
    by (simp only: amplification_sandwich[OF W x npos dpos] Cons.IH[OF Ws])
  also have "\<dots> = kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) (W # Ws)) x" by simp
  finally show ?case .
qed

definition p_positive :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "p_positive n d p \<Phi> \<equiv>
     \<forall>X :: complex Matrix.mat. X \<in> carrier_mat (p*n) (p*n) \<longrightarrow> psd X \<longrightarrow>
       psd (amplification n d p \<Phi> X)"

definition completely_positive :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "completely_positive n d \<Phi> \<equiv> \<forall>p > 0. p_positive n d p \<Phi>"

text \<open>So every $\Phi^{(p)}$ is a Kraus map, hence positive: Kraus maps are completely positive.\<close>

theorem kraus_is_cp:
  assumes Ws: "kraus_operators n d Ws"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (kraus_map_dim d Ws)"
proof -
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    using Ws by (simp add: kraus_operators_def)
  show ?thesis
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
qed

lemma kraus_map_dim_append:
  fixes Ws Vs :: "complex Matrix.mat list"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "kraus_map_dim d (Ws @ Vs) \<rho>
         = kraus_map_dim d Ws \<rho> + kraus_map_dim d Vs \<rho>"
  using Ws_c
proof (induction Ws)
  case Nil
  have Vs_km_c: "kraus_map_dim d Vs \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Vs_c \<rho>_c] .
  show ?case
    using Vs_km_c by (intro eq_matI) auto
next
  case (Cons W Ws)
  hence W_c: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n" by auto
  have Wd_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  have W\<rho>_c: "W * \<rho> \<in> carrier_mat d n"
    using W_c \<rho>_c by (rule mult_carrier_mat)
  have W\<rho>Wd_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
    using W\<rho>_c Wd_c by (rule mult_carrier_mat)
  have Ws_km_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' \<rho>_c] .
  have Vs_km_c: "kraus_map_dim d Vs \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Vs_c \<rho>_c] .
  have IH: "kraus_map_dim d (Ws @ Vs) \<rho>
              = kraus_map_dim d Ws \<rho> + kraus_map_dim d Vs \<rho>"
    using Cons.IH Ws_c' by simp

  have "kraus_map_dim d ((W # Ws) @ Vs) \<rho>
          = W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d (Ws @ Vs) \<rho>"
    by simp
  also have "\<dots> = W * \<rho> * (W\<^sup>\<dagger>)
                  + (kraus_map_dim d Ws \<rho> + kraus_map_dim d Vs \<rho>)"
    using IH by simp
  also have "\<dots> = (W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>)
                  + kraus_map_dim d Vs \<rho>"
    using W\<rho>Wd_c Ws_km_c Vs_km_c by simp
  also have "\<dots> = kraus_map_dim d (W # Ws) \<rho> + kraus_map_dim d Vs \<rho>"
    by simp
  finally show ?case.
qed

text \<open>Since @{const amplification} only evaluates @{term \<Phi>} on
\<open>n\<times>n\<close> blocks, two maps that agree on @{term \<open>carrier_mat n n\<close>}
yield the same amplification, hence the same notion of complete
positivity.\<close>

lemma amplification_cong:
  fixes Phi Psi :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and Xm :: "complex Matrix.mat"
  assumes eq: "\<And>r. r \<in> carrier_mat n n \<Longrightarrow> Phi r = Psi r"
  shows "amplification n d p Phi Xm = amplification n d p Psi Xm"
proof (rule eq_matI)
  show "dim_row (amplification n d p Phi Xm) = dim_row (amplification n d p Psi Xm)"
    by (simp add: amplification_def)
  show "dim_col (amplification n d p Phi Xm) = dim_col (amplification n d p Psi Xm)"
    by (simp add: amplification_def)
  fix i j
  assume i_a: "i < dim_row (amplification n d p Psi Xm)"
  assume j_a: "j < dim_col (amplification n d p Psi Xm)"
  have i_lt: "i < p * d" using i_a by (simp add: amplification_def)
  have j_lt: "j < p * d" using j_a by (simp add: amplification_def)
  have blk_c: "block_of_mat n Xm (i div d) (j div d) \<in> carrier_mat n n"
    by (simp add: block_of_mat_def)
  hence phi_eq_psi: "Phi (block_of_mat n Xm (i div d) (j div d))
           = Psi (block_of_mat n Xm (i div d) (j div d))"
    by (rule eq)
  have L_idx: "amplification n d p Phi Xm $$ (i, j)
                 = Phi (block_of_mat n Xm (i div d) (j div d)) $$ (i mod d, j mod d)"
    using i_lt j_lt by (simp add: amplification_def)
  have R_idx: "amplification n d p Psi Xm $$ (i, j)
                 = Psi (block_of_mat n Xm (i div d) (j div d)) $$ (i mod d, j mod d)"
    using i_lt j_lt by (simp add: amplification_def)
  show "amplification n d p Phi Xm $$ (i, j)
          = amplification n d p Psi Xm $$ (i, j)"
    using L_idx R_idx phi_eq_psi by simp
qed

lemma completely_positive_cong:
  fixes Phi Psi :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes "\<And>r. r \<in> carrier_mat n n \<Longrightarrow> Phi r = Psi r"
  shows "completely_positive n d Phi \<longleftrightarrow> completely_positive n d Psi"
proof -
  have "amplification n d p Phi Xm = amplification n d p Psi Xm" for p Xm
    by (rule amplification_cong[OF assms])
  thus ?thesis
    by (simp add: completely_positive_def p_positive_def)
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

text \<open>The sum $\sum_iW_i^*W_i$ over a Kraus list.\<close>

definition sum_wdag_w :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "sum_wdag_w n Ws \<equiv>
     foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Ws (0\<^sub>m n n)"

lemma sum_wdag_w_Nil [simp]: "sum_wdag_w n [] = 0\<^sub>m n n"
  by (simp add: sum_wdag_w_def)

lemma sum_wdag_w_Cons:
  "sum_wdag_w n (W # Ws) = (W\<^sup>\<dagger>) * W + sum_wdag_w n Ws"
  by (simp add: sum_wdag_w_def)

lemma sum_wdag_w_two:
  assumes V: "V \<in> carrier_mat d n" and W: "W \<in> carrier_mat d n"
  shows "sum_wdag_w n [V, W] = (V\<^sup>\<dagger>) * V + (W\<^sup>\<dagger>) * W"
  using mult_carrier_mat[OF dagger_carrier[OF W] W] by (simp add: sum_wdag_w_Cons)

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

lemma sum_wdag_w_dims [simp]: "dim_row (sum_wdag_w n Ws) = n" "dim_col (sum_wdag_w n Ws) = n"
  by (induction Ws) (simp_all add: sum_wdag_w_def)

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

subsection \<open>The environment model of noise\<close>

text \<open>Day 17, the environment model of noise: a state $\rho$ of lab $A$ meets an environment in
the state $\ket\varphi$, the pair evolves by a unitary $U$ on $\C^m\otimes\C^p$, and lab $A$ sees
$\operatorname{tr}_E(U(\rho\otimes\ketbra\varphi\varphi)U^*)=\sum_iW_i\rho W_i^*$ with
$\sum_iW_i^*W_i=I$.  The index of $\C^m\otimes\C^p$ is $a\,p+i$ (lab index $a$, environment
index $i$), and $W_i$ is the matrix with entries $\sum_kU_{(a,i),(c,k)}\varphi_k$, i.e.\ the
notes' $W_i=\sum_kU_{ik}\alpha_k$ for the blocks $U_{ik}$ of $U$.\<close>

definition env_kraus :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "env_kraus m p U \<phi> i = Matrix.mat m m (\<lambda>(a,c). \<Sum>k<p. U $$ (a * p + i, c * p + k) * \<phi> $ k)"

text \<open>The Kraus operators of the environment model are $W_i=(I\otimes\bra{e_i})\,U\,(I\otimes\ket\varphi)$,
entrywise $(W_i)_{ac}=\sum_kU_{ap+i,\,cp+k}\,\varphi_k$, and
\[ \tr_E\bigl(U(\rho\otimes\ketbra\varphi\varphi)U^*\bigr)=\sum_iW_i\rho W_i^*. \]\<close>

lemma env_kraus_carrier [simp]: "env_kraus m p U \<phi> i \<in> carrier_mat m m"
  by (simp add: env_kraus_def)

lemma env_kraus_dims [simp]: "dim_row (env_kraus m p U \<phi> i) = m" "dim_col (env_kraus m p U \<phi> i) = m"
  by (simp_all add: env_kraus_def)

lemma env_kraus_index: "a < m \<Longrightarrow> c < m \<Longrightarrow> env_kraus m p U \<phi> i $$ (a,c) = (\<Sum>k<p. U $$ (a * p + i, c * p + k) * \<phi> $ k)"
  by (simp add: env_kraus_def)

lemma sum_split_mp:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>x < m * p. f x) = (\<Sum>c<m. \<Sum>k<p. f (c * p + k))"
proof -
  have "(\<Sum>x < m * p. f x) = (\<Sum>c<m. sum f {c * p..<c * p + p})" by (rule sum.nat_group[symmetric])
  also have "\<dots> = (\<Sum>c<m. \<Sum>k<p. f (c * p + k))"
  proof (rule sum.cong[OF refl])
    fix c :: nat
    show "sum f {c * p..<c * p + p} = (\<Sum>k<p. f (c * p + k))"
      by (rule sum.reindex_bij_witness[where i="\<lambda>k. c * p + k" and j="\<lambda>x. x - c * p"]) auto
  qed
  finally show ?thesis .
qed

lemma tensor_outer_index:
  fixes \<rho> :: "complex Matrix.mat" and \<phi> :: "complex Matrix.vec"
  assumes \<rho>: "\<rho> \<in> carrier_mat m m" and \<phi>: "dim_vec \<phi> = p"
      and c: "c < m" and d: "d < m" and k: "k < p" and l: "l < p"
  shows "Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) $$ (c * p + k, d * p + l) = \<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))"
proof -
  have oc: "\<phi> \<oslash> \<phi> \<in> carrier_mat p p" by (rule outer_prod_carrier[OF \<phi> \<phi>])
  have mp: "0 < m" "0 < p" using c k by simp_all
  have "Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) $$ (c * p + k, d * p + l)
        = \<rho> $$ ((c * p + k) div p, (d * p + l) div p) * (\<phi> \<oslash> \<phi>) $$ ((c * p + k) mod p, (d * p + l) mod p)"
    by (rule index_tensor_mat) (use carrier_matD[OF \<rho>] carrier_matD[OF oc] mult_index_lt[OF c k] mult_index_div_mod[OF k] mult_index_lt[OF d l] mult_index_div_mod[OF l] mp in simp_all)
  also have "\<dots> = \<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))"
    unfolding mult_index_div_mod[OF k] mult_index_div_mod[OF l] using outer_prod_index[of k \<phi> l \<phi>] \<phi> k l by simp
  finally show ?thesis .
qed

text \<open>The entries of $U(\rho\otimes\ketbra\varphi\varphi)U^*$.\<close>

lemma env_entry:
  fixes U \<rho> :: "complex Matrix.mat" and \<phi> :: "complex Matrix.vec"
  assumes U: "U \<in> carrier_mat (m * p) (m * p)" and \<rho>: "\<rho> \<in> carrier_mat m m" and \<phi>: "dim_vec \<phi> = p"
      and x: "x < m * p" and y: "y < m * p"
  shows "(U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (x,y)
         = (\<Sum>d<m. \<Sum>c<m. (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (y, d * p + l) * \<phi> $ l))"
proof -
  let ?T = "Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>)"
  have Tc: "?T \<in> carrier_mat (m * p) (m * p)" using \<rho> outer_prod_carrier[OF \<phi> \<phi>] by auto
  have UT: "U * ?T \<in> carrier_mat (m * p) (m * p)" using U Tc by auto
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat (m * p) (m * p)" by (rule dagger_carrier[OF U])
  have "(U * ?T * (U\<^sup>\<dagger>)) $$ (x,y) = (\<Sum>w < m * p. (U * ?T) $$ (x,w) * (U\<^sup>\<dagger>) $$ (w,y))"
    by (rule mat_mult_entry[OF UT Ud x y])
  also have "\<dots> = (\<Sum>w < m * p. (\<Sum>z < m * p. U $$ (x,z) * ?T $$ (z,w)) * cnj (U $$ (y,w)))"
  proof (rule sum.cong[OF refl])
    fix w assume "w \<in> {..< m * p}"
    hence w: "w < m * p" by simp
    show "(U * ?T) $$ (x,w) * (U\<^sup>\<dagger>) $$ (w,y) = (\<Sum>z < m * p. U $$ (x,z) * ?T $$ (z,w)) * cnj (U $$ (y,w))"
      using mat_mult_entry[OF U Tc x w] U w y by (simp add: dagger_def)
  qed
  also have "\<dots> = (\<Sum>d<m. \<Sum>l<p. (\<Sum>c<m. \<Sum>k<p. U $$ (x, c * p + k) * ?T $$ (c * p + k, d * p + l))
                    * cnj (U $$ (y, d * p + l)))"
    by (simp only: sum_split_mp)
  also have "\<dots> = (\<Sum>d<m. \<Sum>l<p. (\<Sum>c<m. \<Sum>k<p. U $$ (x, c * p + k) * (\<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))))
                    * cnj (U $$ (y, d * p + l)))"
    by (intro sum.cong refl) (simp add: tensor_outer_index[OF \<rho> \<phi>])
  also have "\<dots> = (\<Sum>d<m. \<Sum>c<m. (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (y, d * p + l) * \<phi> $ l))"
  proof (rule sum.cong[OF refl])
    fix d
    define F where "F = (\<lambda>c k l. U $$ (x, c * p + k) * \<phi> $ k * \<rho> $$ (c,d) * cnj (\<phi> $ l) * cnj (U $$ (y, d * p + l)))"
    have "(\<Sum>l<p. (\<Sum>c<m. \<Sum>k<p. U $$ (x, c * p + k) * (\<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))))
              * cnj (U $$ (y, d * p + l))) = (\<Sum>l<p. \<Sum>c<m. \<Sum>k<p. F c k l)"
      unfolding F_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)
    also have "\<dots> = (\<Sum>c<m. \<Sum>l<p. \<Sum>k<p. F c k l)" by (rule sum.swap)
    also have "\<dots> = (\<Sum>c<m. \<Sum>k<p. \<Sum>l<p. F c k l)" by (rule sum.cong[OF refl]) (rule sum.swap)
    also have "\<dots> = (\<Sum>c<m. (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (y, d * p + l) * \<phi> $ l))"
      unfolding F_def by (simp add: sum_distrib_left sum_distrib_right mult_ac)
    finally show "(\<Sum>l<p. (\<Sum>c<m. \<Sum>k<p. U $$ (x, c * p + k) * (\<rho> $$ (c,d) * (\<phi> $ k * cnj (\<phi> $ l))))
              * cnj (U $$ (y, d * p + l)))
        = (\<Sum>c<m. (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (y, d * p + l) * \<phi> $ l))" .
  qed
  finally show ?thesis .
qed

theorem environment_model:
  fixes U \<rho> :: "complex Matrix.mat" and \<phi> :: "complex Matrix.vec"
  assumes U: "U \<in> carrier_mat (m * p) (m * p)" and Uu: "unitary U"
      and \<phi>: "dim_vec \<phi> = p" and \<phi>1: "\<langle>\<phi>|\<phi>\<rangle> = 1" and \<rho>: "\<rho> \<in> carrier_mat m m"
  defines "Ws \<equiv> map (env_kraus m p U \<phi>) [0..<p]"
  shows "partial_trace_B m p (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) = kraus_map_dim m Ws \<rho>"
    and "kraus_operators m m Ws"
proof -
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat m m" unfolding Ws_def by auto
  let ?W = "env_kraus m p U \<phi>"
  show "partial_trace_B m p (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) = kraus_map_dim m Ws \<rho>"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (kraus_map_dim m Ws \<rho>)" "b < dim_col (kraus_map_dim m Ws \<rho>)"
    hence a: "a < m" and b: "b < m" using kraus_map_dim_carrier[OF Ws_c \<rho>] by simp_all
    have "partial_trace_B m p (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (a,b)
          = (\<Sum>i<p. (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (a * p + i, b * p + i))"
      using a b by (simp add: partial_trace_B_def)
    also have "\<dots> = (\<Sum>i<p. (?W i * \<rho> * ((?W i)\<^sup>\<dagger>)) $$ (a,b))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..<p}"
      hence i: "i < p" by simp
      have W: "?W i \<in> carrier_mat m m" by simp
      have WR: "?W i * \<rho> \<in> carrier_mat m m" by (rule mult_carrier_mat[OF W \<rho>])
      have Wd: "(?W i)\<^sup>\<dagger> \<in> carrier_mat m m" by (rule dagger_carrier[OF W])
      have "(?W i * \<rho> * ((?W i)\<^sup>\<dagger>)) $$ (a,b) = (\<Sum>d<m. (?W i * \<rho>) $$ (a,d) * ((?W i)\<^sup>\<dagger>) $$ (d,b))"
        by (rule mat_mult_entry[OF WR Wd a b])
      also have "\<dots> = (\<Sum>d<m. \<Sum>c<m. (\<Sum>k<p. U $$ (a * p + i, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (b * p + i, d * p + l) * \<phi> $ l))"
      proof (rule sum.cong[OF refl])
        fix d assume "d \<in> {..<m}"
        hence d: "d < m" by simp
        show "(?W i * \<rho>) $$ (a,d) * ((?W i)\<^sup>\<dagger>) $$ (d,b) = (\<Sum>c<m. (\<Sum>k<p. U $$ (a * p + i, c * p + k) * \<phi> $ k) * \<rho> $$ (c,d)
              * cnj (\<Sum>l<p. U $$ (b * p + i, d * p + l) * \<phi> $ l))"
          unfolding mat_mult_entry[OF W \<rho> a d] using a b d
          by (simp add: dagger_def env_kraus_index sum_distrib_right)
      qed
      finally show "(U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (a * p + i, b * p + i)
                    = (?W i * \<rho> * ((?W i)\<^sup>\<dagger>)) $$ (a,b)"
        using env_entry[OF U \<rho> \<phi> mult_index_lt[OF a i] mult_index_lt[OF b i]] by simp
    qed
    also have "\<dots> = kraus_map_dim m Ws \<rho> $$ (a,b)"
      unfolding kraus_map_dim_entry_sum_list[OF Ws_c \<rho> a b] unfolding Ws_def
      by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
    finally show "partial_trace_B m p (U * Tensor.tensor_mat \<rho> (\<phi> \<oslash> \<phi>) * (U\<^sup>\<dagger>)) $$ (a,b) = kraus_map_dim m Ws \<rho> $$ (a,b)" .
  qed (use kraus_map_dim_carrier[OF Ws_c \<rho>] in simp_all)
  have UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m (m * p)" using Uu U unfolding unitary_def by simp
  have tp: "sum_wdag_w m Ws = 1\<^sub>m m"
  proof (rule eq_matI)
    fix c d assume "c < dim_row (1\<^sub>m m :: complex Matrix.mat)" "d < dim_col (1\<^sub>m m :: complex Matrix.mat)"
    hence c: "c < m" and d: "d < m" by simp_all
    define G where "G = (\<lambda>x. cnj (\<Sum>k<p. U $$ (x, c * p + k) * \<phi> $ k) * (\<Sum>l<p. U $$ (x, d * p + l) * \<phi> $ l))"
    have "sum_wdag_w m Ws $$ (c,d) = (\<Sum>i<p. (((?W i)\<^sup>\<dagger>) * ?W i) $$ (c,d))"
      unfolding sum_wdag_w_entry[OF Ws_c c d] unfolding Ws_def
      by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
    also have "\<dots> = (\<Sum>i<p. \<Sum>a<m. G (a * p + i))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..<p}"
      have W: "?W i \<in> carrier_mat m m" by simp
      show "(((?W i)\<^sup>\<dagger>) * ?W i) $$ (c,d) = (\<Sum>a<m. G (a * p + i))"
        unfolding mat_mult_entry[OF dagger_carrier[OF W] W c d] G_def
        by (rule sum.cong[OF refl]) (use c d in \<open>simp add: dagger_def env_kraus_index\<close>)
    qed
    also have "\<dots> = (\<Sum>a<m. \<Sum>i<p. G (a * p + i))" by (rule sum.swap)
    also have "\<dots> = (\<Sum>x < m * p. G x)" by (rule sum_split_mp[symmetric])
    also have "\<dots> = (\<Sum>k<p. \<Sum>l<p. cnj (\<phi> $ k) * \<phi> $ l * (\<Sum>x < m * p. cnj (U $$ (x, c * p + k)) * U $$ (x, d * p + l)))"
      unfolding G_def by (simp add: sum_distrib_left sum_distrib_right mult_ac sum.swap[of _ "{..<m*p}"])
    also have "\<dots> = (\<Sum>k<p. \<Sum>l<p. cnj (\<phi> $ k) * \<phi> $ l * (if c = d \<and> k = l then 1 else 0))"
    proof (intro sum.cong refl)
      fix k l assume "k \<in> {..<p}" "l \<in> {..<p}"
      hence k: "k < p" and l: "l < p" by simp_all
      have "(\<Sum>x < m * p. cnj (U $$ (x, c * p + k)) * U $$ (x, d * p + l)) = ((U\<^sup>\<dagger>) * U) $$ (c * p + k, d * p + l)"
        unfolding mat_mult_entry[OF dagger_carrier[OF U] U mult_index_lt[OF c k] mult_index_lt[OF d l]]
        by (rule sum.cong[OF refl]) (use U mult_index_lt[OF c k] in \<open>simp add: dagger_def\<close>)
      also have "\<dots> = (if c = d \<and> k = l then 1 else 0)"
      proof -
        have "c * p + k = d * p + l \<longleftrightarrow> c = d \<and> k = l"
          using mult_index_div_mod[OF k] mult_index_div_mod[OF l] by metis
        thus ?thesis unfolding UU using mult_index_lt[OF c k] mult_index_lt[OF d l] by simp
      qed
      finally show "cnj (\<phi> $ k) * \<phi> $ l * (\<Sum>x < m * p. cnj (U $$ (x, c * p + k)) * U $$ (x, d * p + l))
                    = cnj (\<phi> $ k) * \<phi> $ l * (if c = d \<and> k = l then 1 else 0)" by simp
    qed
    also have "\<dots> = (if c = d then \<langle>\<phi>|\<phi>\<rangle> else 0)"
    proof (cases "c = d")
      case True
      have "(\<Sum>k<p. \<Sum>l<p. cnj (\<phi> $ k) * \<phi> $ l * (if c = d \<and> k = l then 1 else 0)) = (\<Sum>k<p. cnj (\<phi> $ k) * \<phi> $ k)"
        using True by (simp add: if_distrib cong: if_cong)
      also have "\<dots> = \<langle>\<phi>|\<phi>\<rangle>" unfolding inner_prod_sum[OF \<phi> \<phi>] atLeast0LessThan ..
      finally show ?thesis using True by simp
    qed simp
    also have "\<dots> = 1\<^sub>m m $$ (c,d)" using c d \<phi>1 by simp
    finally show "sum_wdag_w m Ws $$ (c,d) = 1\<^sub>m m $$ (c,d)" .
  qed (use sum_wdag_w_carrier Ws_c in auto)
  show "kraus_operators m m Ws" unfolding kraus_operators_altdef using Ws_c tp by simp
qed

end
