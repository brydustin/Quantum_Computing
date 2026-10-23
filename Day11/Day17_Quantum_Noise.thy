(*  Title:   Day17_Quantum_Noise.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 5 October 2011 (Day 17)
*)

theory Day17_Quantum_Noise
  imports Day16_Density_Postulates
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
computation is \<open>environment_model\<close> in \<open>Day17_Environment_Model\<close>.

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
The proposition is \<open>density_preserving_iff_positive_tp\<close> in \<open>Day18_Positive_Maps\<close>;
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

lemma amplification_index:
  assumes "i < p*d" and "j < p*d"
  shows "amplification n d p \<Phi> X $$ (i,j) =
         \<Phi> (block_of_mat n X (i div d) (j div d)) $$
             (i mod d, j mod d)"
  using assms by (simp add: amplification_def)

lemma amplification_one:
  assumes X: "X \<in> carrier_mat n n"
      and range: "\<Phi> X \<in> carrier_mat d d"
  shows "amplification n d 1 \<Phi> X = \<Phi> X"
proof (rule eq_matI)
  show "dim_row (amplification n d 1 \<Phi> X) = dim_row (\<Phi> X)"
    using range by (simp add: amplification_def)
  show "dim_col (amplification n d 1 \<Phi> X) = dim_col (\<Phi> X)"
    using range by (simp add: amplification_def)
next
  fix i j
  assume i: "i < dim_row (\<Phi> X)" and j: "j < dim_col (\<Phi> X)"
  then have id: "i < d" and jd: "j < d"
    using range by auto
  have div_i: "i div d = 0"
    using id by simp
  have div_j: "j div d = 0"
    using jd by simp
  have mod_i: "i mod d = i"
    using id by simp
  have mod_j: "j mod d = j"
    using jd by simp
  have "amplification n d 1 \<Phi> X $$ (i,j)
      = \<Phi> (block_of_mat n X (i div d) (j div d)) $$ (i mod d, j mod d)"
    using id jd by (simp add: amplification_index)
  also have "\<dots> = \<Phi> (block_of_mat n X 0 0) $$ (i,j)"
    using div_i div_j mod_i mod_j by simp
  also have "\<dots> = \<Phi> X $$ (i,j)"
    using block_of_mat_single[OF X] by simp
  finally show "amplification n d 1 \<Phi> X $$ (i,j) = \<Phi> X $$ (i,j)".
qed

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

lemma tensor_id_kraus_index:
  assumes W: "W \<in> carrier_mat d n"
      and r: "r < p*d"
      and c: "c < p*n"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "(1\<^sub>m p \<Otimes> W) $$ (r,c) =
         (if r div d = c div n then W $$ (r mod d, c mod n) else 0)"
proof -
  have rowW: "dim_row W = d" and colW: "dim_col W = n"
    using W by auto
  have rd: "r div d < p"
    using r dpos by (simp add: less_mult_imp_div_less)
  have cn: "c div n < p"
    using c npos by (simp add: less_mult_imp_div_less)
  have ppos: "0 < p"
    using r dpos by (cases p) auto
  have "(1\<^sub>m p \<Otimes> W) $$ (r,c) =
        (1\<^sub>m p :: complex Matrix.mat) $$ (r div d, c div n) *
        W $$ (r mod d, c mod n)"
    using index_tensor_mat[OF _ _ rowW colW r c _ npos, of "1\<^sub>m p"]
    using ppos by simp
  also have "\<dots> =
        (if r div d = c div n then W $$ (r mod d, c mod n) else 0)"
    using rd cn by simp
  finally show ?thesis .
qed

lemma sum_block_delta:
  fixes f :: "nat \<Rightarrow> complex"
  assumes a: "a < p"
      and npos: "0 < n"
  shows "(\<Sum>t < p*n. if a = t div n then f (t mod n) else 0) =
         (\<Sum>r < n. f r)"
proof -
  have bij: "bij_betw (\<lambda>(q, r). q * n + r) ({..<p} \<times> {..<n}) {..<p*n}"
  proof (rule bij_betwI[where g = "\<lambda>t. (t div n, t mod n)"])
    show "(\<lambda>(q, r). q * n + r) \<in> {..<p} \<times> {..<n} \<rightarrow> {..<p*n}"
    proof
      fix z assume "z \<in> {..<p} \<times> {..<n}"
      then obtain q r where z: "z = (q, r)" and q: "q < p" and r: "r < n"
        by blast
      have "q * n + r < (q + 1) * n"
        using r by simp
      also have "\<dots> \<le> p * n"
      proof -
        have "q + 1 \<le> p"
          using q by simp
        thus "(q + 1) * n \<le> p * n"
          by (rule mult_le_mono1)
      qed
      finally show "(case z of (q, r) \<Rightarrow> q * n + r) \<in> {..<p*n}"
        using z by simp
    qed
  next
    show "(\<lambda>t. (t div n, t mod n)) \<in> {..<p*n} \<rightarrow> {..<p} \<times> {..<n}"
      using npos by (auto simp: less_mult_imp_div_less)
  next
    fix z assume "z \<in> {..<p} \<times> {..<n}"
    then obtain q r where z: "z = (q, r)" and r: "r < n"
      by blast
    show "(\<lambda>t. (t div n, t mod n)) ((\<lambda>(q, r). q * n + r) z) = z"
      using z r by simp
  next
    fix t assume "t \<in> {..<p*n}"
    show "(\<lambda>(q, r). q * n + r) ((\<lambda>t. (t div n, t mod n)) t) = t"
      by simp
  qed

  have "(\<Sum>t < p*n. if a = t div n then f (t mod n) else 0) =
        (\<Sum>(q, r) \<in> {..<p} \<times> {..<n}. if a = q then f r else 0)"
    using sum.reindex_bij_betw[OF bij, symmetric,
        of "\<lambda>t. if a = t div n then f (t mod n) else 0"]
  proof -
    have "(\<Sum>t < p*n. if a = t div n then f (t mod n) else 0) =
          (\<Sum>x \<in> {..<p} \<times> {..<n}.
             if a = ((case x of (q, r) \<Rightarrow> q * n + r) div n)
             then f (((case x of (q, r) \<Rightarrow> q * n + r) mod n)) else 0)"
      using sum.reindex_bij_betw[OF bij, symmetric,
          of "\<lambda>t. if a = t div n then f (t mod n) else 0"]
      by (simp add: case_prod_beta)
    also have "\<dots> = (\<Sum>(q, r) \<in> {..<p} \<times> {..<n}. if a = q then f r else 0)"
    proof (intro sum.cong refl)
      fix x assume x: "x \<in> {..<p} \<times> {..<n}"
      then obtain q r where xr: "x = (q, r)" and r: "r < n"
        by blast
      show "(if a = ((case x of (q, r) \<Rightarrow> q * n + r) div n)
             then f (((case x of (q, r) \<Rightarrow> q * n + r) mod n)) else 0) =
            (case x of (q, r) \<Rightarrow> if a = q then f r else 0)"
        using xr r npos by simp
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = (\<Sum>q < p. \<Sum>r < n. if a = q then f r else 0)"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>q < p. if a = q then (\<Sum>r < n. f r) else 0)"
    by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>r < n. f r)"
    using a by simp
  finally show ?thesis .
qed

lemma sum_block_delta_index:
  fixes h :: "nat \<Rightarrow> complex"
  assumes a: "a < p"
      and npos: "0 < n"
  shows "(\<Sum>t < p*n. if a = t div n then h t else 0) =
         (\<Sum>r < n. h (a*n + r))"
proof -
  have eq: "\<And>t. t < p*n \<Longrightarrow>
      (if a = t div n then h t else 0) =
      (if a = t div n then h (a*n + t mod n) else 0)"
  proof -
    fix t assume t: "t < p*n"
    show "(if a = t div n then h t else 0) =
          (if a = t div n then h (a*n + t mod n) else 0)"
    proof (cases "a = t div n")
      case True
      have "t = (t div n) * n + t mod n"
        by simp
      also have "\<dots> = a * n + t mod n"
        using True by simp
      finally show ?thesis
        using True by simp
    next
      case False
      thus ?thesis by simp
    qed
  qed
  have "(\<Sum>t < p*n. if a = t div n then h t else 0) =
        (\<Sum>t < p*n. if a = t div n then h (a*n + t mod n) else 0)"
    by (intro sum.cong refl eq) simp
  also have "\<dots> = (\<Sum>r < n. h (a*n + r))"
    using sum_block_delta[OF a npos, of "\<lambda>r. h (a*n + r)"] .
  finally show ?thesis .
qed

lemma tensor_id_kraus_left_mult_index:
  assumes W: "W \<in> carrier_mat d n"
      and x: "x \<in> carrier_mat (p*n) q"
      and i: "i < p*d"
      and s: "s < q"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "((1\<^sub>m p \<Otimes> W) * x) $$ (i,s) =
         (\<Sum>t < n. W $$ (i mod d, t) * x $$ ((i div d) * n + t, s))"
proof -
  have a: "i div d < p"
    using i dpos by (simp add: less_mult_imp_div_less)
  have L: "(1\<^sub>m p \<Otimes> W) \<in> carrier_mat (p*d) (p*n)"
    using W by (rule tensor_id_kraus_carrier)
  have iL: "i < dim_row (1\<^sub>m p \<Otimes> W)"
    using W i by auto
  have sx: "s < dim_col x"
    using x s by auto
  have "((1\<^sub>m p \<Otimes> W) * x) $$ (i,s) =
        Matrix.row (1\<^sub>m p \<Otimes> W) i \<bullet> Matrix.col x s"
    using index_mult_mat(1)[OF iL sx] .
  also have "\<dots> =
        (\<Sum>r = 0..<p*n. (1\<^sub>m p \<Otimes> W) $$ (i,r) * x $$ (r,s))"
  proof -
    have "Matrix.row (1\<^sub>m p \<Otimes> W) i \<bullet> Matrix.col x s =
          (\<Sum>r = 0..<p*n.
             Matrix.row (1\<^sub>m p \<Otimes> W) i $ r * Matrix.col x s $ r)"
      unfolding scalar_prod_def using x by simp
    also have "\<dots> =
          (\<Sum>r = 0..<p*n. (1\<^sub>m p \<Otimes> W) $$ (i,r) * x $$ (r,s))"
      using W x i s by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  also have "\<dots> =
        (\<Sum>r < p*n. (1\<^sub>m p \<Otimes> W) $$ (i,r) * x $$ (r,s))"
    by (simp add: lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>r < p*n. if i div d = r div n
             then W $$ (i mod d, r mod n) * x $$ (r,s) else 0)"
    using W i dpos npos
    by (intro sum.cong refl) (simp add: tensor_id_kraus_index)
  also have "\<dots> =
        (\<Sum>t < n. W $$ (i mod d, t) * x $$ ((i div d) * n + t, s))"
    using sum_block_delta_index[OF a npos,
        of "\<lambda>r. W $$ (i mod d, r mod n) * x $$ (r,s)"]
    by simp
  finally show ?thesis .
qed

lemma tensor_id_kraus_right_mult_index:
  assumes W: "W \<in> carrier_mat d n"
      and y: "y \<in> carrier_mat q (p*n)"
      and i: "i < q"
      and j: "j < p*d"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "(y * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j) =
         (\<Sum>s < n. y $$ (i, (j div d) * n + s) * (W\<^sup>\<dagger>) $$ (s, j mod d))"
proof -
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W by (rule dagger_carrier)
  have b: "j div d < p"
    using j dpos by (simp add: less_mult_imp_div_less)
  have R: "(1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*n) (p*d)"
    using Wdag by (rule tensor_id_kraus_carrier)
  have iy: "i < dim_row y"
    using y i by auto
  have jR: "j < dim_col (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))"
    using W j by auto
  have "(y * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j) =
        Matrix.row y i \<bullet> Matrix.col (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) j"
    using index_mult_mat(1)[OF iy jR] .
  also have "\<dots> =
        (\<Sum>r = 0..<p*n. y $$ (i,r) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) $$ (r,j))"
  proof -
    have "Matrix.row y i \<bullet> Matrix.col (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) j =
          (\<Sum>r = 0..<p*n.
             Matrix.row y i $ r * Matrix.col (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) j $ r)"
      unfolding scalar_prod_def using W y by simp
    also have "\<dots> =
          (\<Sum>r = 0..<p*n. y $$ (i,r) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) $$ (r,j))"
      using W y i j by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  also have "\<dots> =
        (\<Sum>r < p*n. y $$ (i,r) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) $$ (r,j))"
    by (simp add: lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>r < p*n. if j div d = r div n
             then y $$ (i,r) * (W\<^sup>\<dagger>) $$ (r mod n, j mod d) else 0)"
    using Wdag j dpos npos
    by (intro sum.cong refl) (simp add: tensor_id_kraus_index mult.commute)
  also have "\<dots> =
        (\<Sum>s < n. y $$ (i, (j div d) * n + s) * (W\<^sup>\<dagger>) $$ (s, j mod d))"
    using sum_block_delta_index[OF b npos,
        of "\<lambda>r. y $$ (i,r) * (W\<^sup>\<dagger>) $$ (r mod n, j mod d)"]
    by simp
  finally show ?thesis .
qed

lemma kraus_term_index:
  assumes W: "W \<in> carrier_mat d n"
      and B: "B \<in> carrier_mat n n"
      and i: "i < d"
      and j: "j < d"
  shows "(W * B * (W\<^sup>\<dagger>)) $$ (i,j) =
         (\<Sum>s < n. (\<Sum>t < n. W $$ (i,t) * B $$ (t,s)) * (W\<^sup>\<dagger>) $$ (s,j))"
proof -
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W by (rule dagger_carrier)
  have WB: "W * B \<in> carrier_mat d n"
    using W B by (intro mult_carrier_mat) auto
  have iWB: "i < dim_row (W * B)"
    using WB i by auto
  have jWdag: "j < dim_col (W\<^sup>\<dagger>)"
    using Wdag j by auto
  have "(W * B * (W\<^sup>\<dagger>)) $$ (i,j) =
        Matrix.row (W * B) i \<bullet> Matrix.col (W\<^sup>\<dagger>) j"
    using index_mult_mat(1)[OF iWB jWdag] .
  also have "\<dots> = (\<Sum>s = 0..<n. (W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j))"
  proof -
    have "Matrix.row (W * B) i \<bullet> Matrix.col (W\<^sup>\<dagger>) j =
          (\<Sum>s = 0..<n. Matrix.row (W * B) i $ s * Matrix.col (W\<^sup>\<dagger>) j $ s)"
      unfolding scalar_prod_def using W WB by simp
    also have "\<dots> = (\<Sum>s = 0..<n. (W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j))"
    proof (intro sum.cong refl)
      fix s assume s: "s \<in> {0..<n}"
      hence sn: "s < n" by simp
      have "Matrix.row (W * B) i $ s = (W * B) $$ (i,s)"
        using B WB i sn by (simp add: Matrix.row_def)
      moreover have "Matrix.col (W\<^sup>\<dagger>) j $ s = (W\<^sup>\<dagger>) $$ (s,j)"
        using W Wdag j sn by (simp add: Matrix.col_def)
      ultimately show "Matrix.row (W * B) i $ s * Matrix.col (W\<^sup>\<dagger>) j $ s =
        (W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j)"
        by simp
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = (\<Sum>s < n. (W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j))"
    by (simp add: lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>s < n. (\<Sum>t < n. W $$ (i,t) * B $$ (t,s)) * (W\<^sup>\<dagger>) $$ (s,j))"
  proof (intro sum.cong refl)
    fix s assume s: "s \<in> {..<n}"
    hence sn: "s < n" by simp
    have iW: "i < dim_row W"
      using W i by auto
    have sB: "s < dim_col B"
      using B sn by auto
    have "(W * B) $$ (i,s) = Matrix.row W i \<bullet> Matrix.col B s"
      using index_mult_mat(1)[OF iW sB] .
    also have "\<dots> = (\<Sum>t = 0..<n. W $$ (i,t) * B $$ (t,s))"
    proof -
      have "Matrix.row W i \<bullet> Matrix.col B s =
            (\<Sum>t = 0..<n. Matrix.row W i $ t * Matrix.col B s $ t)"
        unfolding scalar_prod_def using W B by simp
      also have "\<dots> = (\<Sum>t = 0..<n. W $$ (i,t) * B $$ (t,s))"
        using W B i sn by (intro sum.cong refl) simp
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>t < n. W $$ (i,t) * B $$ (t,s))"
      by (simp add: lessThan_atLeast0)
    finally show "(W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j) =
        (\<Sum>t<n. W $$ (i,t) * B $$ (t,s)) * (W\<^sup>\<dagger>) $$ (s,j)"
      by simp
  qed
  finally show ?thesis .
qed

lemma kraus_amplification_single:
  assumes W: "W \<in> carrier_mat d n"
      and x: "x \<in> carrier_mat (p*n) (p*n)"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x =
         ((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))"
proof (rule eq_matI)
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W by (rule dagger_carrier)
  have L: "(1\<^sub>m p \<Otimes> W) \<in> carrier_mat (p*d) (p*n)"
    using W by (rule tensor_id_kraus_carrier)
  have R: "(1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*n) (p*d)"
    using Wdag by (rule tensor_id_kraus_carrier)
  have LX: "(1\<^sub>m p \<Otimes> W) * x \<in> carrier_mat (p*d) (p*n)"
    using L x by (intro mult_carrier_mat) auto
  have RHS_c: "((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*d) (p*d)"
    using mult_carrier_mat[OF LX R] by simp
  show "dim_row (amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x) =
        dim_row (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)))"
    using W RHS_c by (simp add: amplification_def)
  show "dim_col (amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x) =
        dim_col (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)))"
    using W RHS_c by (simp add: amplification_def)
next
  fix i j
  assume ij: "i < dim_row (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)))"
             "j < dim_col (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)))"
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W by (rule dagger_carrier)
  have L: "(1\<^sub>m p \<Otimes> W) \<in> carrier_mat (p*d) (p*n)"
    using W by (rule tensor_id_kraus_carrier)
  have R: "(1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*n) (p*d)"
    using Wdag by (rule tensor_id_kraus_carrier)
  have LX: "(1\<^sub>m p \<Otimes> W) * x \<in> carrier_mat (p*d) (p*n)"
    using L x by (intro mult_carrier_mat) auto
  have RHS_c: "((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*d) (p*d)"
    using mult_carrier_mat[OF LX R] by simp
  have i_pd: "i < p*d" and j_pd: "j < p*d"
    using W ij RHS_c by auto
  have imodd: "i mod d < d" and jmodd: "j mod d < d"
    using dpos by simp_all
  have idiv: "i div d < p" and jdiv: "j div d < p"
    using i_pd j_pd dpos by (simp_all add: less_mult_imp_div_less)
  have lhs:
    "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x $$ (i,j) =
     (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
        x $$ ((i div d) * n + t, (j div d) * n + s)) *
        (W\<^sup>\<dagger>) $$ (s, j mod d))"
  proof -
    have "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x $$ (i,j) =
          (W * block_of_mat n x (i div d) (j div d) * (W\<^sup>\<dagger>)) $$ (i mod d, j mod d)"
      using i_pd j_pd by (simp add: amplification_def)
    also have "\<dots> =
       (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
          block_of_mat n x (i div d) (j div d) $$ (t,s)) *
          (W\<^sup>\<dagger>) $$ (s, j mod d))"
    proof -
      have Bc: "block_of_mat n x (i div d) (j div d) \<in> carrier_mat n n"
        by (simp add: block_of_mat_def)
      show ?thesis
        using kraus_term_index[OF W Bc imodd jmodd] .
    qed
    also have "\<dots> =
       (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
          x $$ ((i div d) * n + t, (j div d) * n + s)) *
          (W\<^sup>\<dagger>) $$ (s, j mod d))"
      by (intro sum.cong refl arg_cong2[where f="(*)"] sum.cong) (simp_all add: block_of_mat_def)
    finally show ?thesis .
  qed
  have rhs:
    "(((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j) =
     (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
        x $$ ((i div d) * n + t, (j div d) * n + s)) *
        (W\<^sup>\<dagger>) $$ (s, j mod d))"
  proof -
    have "(((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j) =
          (\<Sum>s < n. ((1\<^sub>m p \<Otimes> W) * x) $$ (i, (j div d) * n + s) *
             (W\<^sup>\<dagger>) $$ (s, j mod d))"
      by (rule tensor_id_kraus_right_mult_index[where W=W and d=d and n=n and p=p and q="p*d"])
         (use W LX i_pd j_pd dpos npos in auto)
    also have "\<dots> =
       (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
          x $$ ((i div d) * n + t, (j div d) * n + s)) *
          (W\<^sup>\<dagger>) $$ (s, j mod d))"
    proof (intro sum.cong refl)
      fix s assume s: "s \<in> {..<n}"
      hence sn: "s < n" by simp
      have col: "(j div d) * n + s < p*n"
      proof -
        have "(j div d) * n + s < (j div d + 1) * n"
          using sn by simp
        also have "\<dots> \<le> p * n"
        proof -
          have "j div d + 1 \<le> p"
            using jdiv by simp
          thus "(j div d + 1) * n \<le> p * n"
            by (rule mult_le_mono1)
        qed
        finally show ?thesis .
      qed
      show "((1\<^sub>m p \<Otimes> W) * x) $$ (i, (j div d) * n + s) *
             (W\<^sup>\<dagger>) $$ (s, j mod d) =
            (\<Sum>t<n. W $$ (i mod d, t) *
                x $$ (i div d * n + t, j div d * n + s)) *
             (W\<^sup>\<dagger>) $$ (s, j mod d)"
        using tensor_id_kraus_left_mult_index[OF W x i_pd col dpos npos]
        by simp
    qed
    finally show ?thesis .
  qed
  show "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x $$ (i,j) =
        (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j)"
    using lhs rhs by simp
qed

lemma amplification_zero_map:
  assumes dpos: "0 < d"
  shows "amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x = 0\<^sub>m (p*d) (p*d)"
proof (rule eq_matI)
  show "dim_row (amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x) = dim_row (0\<^sub>m (p*d) (p*d))"
    by (simp add: amplification_def)
  show "dim_col (amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x) = dim_col (0\<^sub>m (p*d) (p*d))"
    by (simp add: amplification_def)
next
  fix i j
  assume i: "i < dim_row (0\<^sub>m (p*d) (p*d))"
     and j: "j < dim_col (0\<^sub>m (p*d) (p*d))"
  show "amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x $$ (i,j) =
        (0\<^sub>m (p*d) (p*d)) $$ (i,j)"
    using i j dpos by (simp add: amplification_def)
qed

lemma amplification_add:
  assumes dpos: "0 < d"
      and F: "\<And>a b. F (block_of_mat n x a b) \<in> carrier_mat d d"
      and G: "\<And>a b. G (block_of_mat n x a b) \<in> carrier_mat d d"
  shows "amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x =
         amplification n d p F x + amplification n d p G x"
proof (rule eq_matI)
  show "dim_row (amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x) =
        dim_row (amplification n d p F x + amplification n d p G x)"
    by (simp add: amplification_def)
  show "dim_col (amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x) =
        dim_col (amplification n d p F x + amplification n d p G x)"
    by (simp add: amplification_def)
next
  fix i j
  assume i: "i < dim_row (amplification n d p F x + amplification n d p G x)"
     and j: "j < dim_col (amplification n d p F x + amplification n d p G x)"
  have ipd: "i < p*d" and jpd: "j < p*d"
    using i j by (simp_all add: amplification_def)
  have imodd: "i mod d < d" and jmodd: "j mod d < d"
    using dpos by simp_all
  let ?B = "block_of_mat n x (i div d) (j div d)"
  have FB: "F ?B \<in> carrier_mat d d"
    by (rule F)
  have GB: "G ?B \<in> carrier_mat d d"
    by (rule G)
  show "amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x $$ (i,j) =
        (amplification n d p F x + amplification n d p G x) $$ (i,j)"
    using ipd jpd imodd jmodd FB GB
    by (simp add: amplification_def)
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
  show ?case
    by (simp add: amplification_zero_map[OF dpos])
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Wsc: "\<forall>W\<in>set Ws. W \<in> carrier_mat d n"
    by auto
  have term_c: "\<And>a b. W * block_of_mat n x a b * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
  proof -
    fix a b
    have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
      using Wc by (rule dagger_carrier)
    have Bc: "block_of_mat n x a b \<in> carrier_mat n n"
      by (simp add: block_of_mat_def)
    have WB: "W * block_of_mat n x a b \<in> carrier_mat d n"
      using mult_carrier_mat[OF Wc Bc] by simp
    show "W * block_of_mat n x a b * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
      using mult_carrier_mat[OF WB Wdag] by simp
  qed
  have rest_c: "\<And>a b. kraus_map_dim d Ws (block_of_mat n x a b) \<in> carrier_mat d d"
  proof -
    fix a b
    have Bc: "block_of_mat n x a b \<in> carrier_mat n n"
      by (simp add: block_of_mat_def)
    show "kraus_map_dim d Ws (block_of_mat n x a b) \<in> carrier_mat d d"
      using kraus_map_dim_carrier[OF Wsc Bc] .
  qed
  have cons_fun:
    "kraus_map_dim d (W # Ws) = (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>)"
    by (rule ext) simp
  have "amplification n d p (kraus_map_dim d (W # Ws)) x =
        amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x +
        amplification n d p (kraus_map_dim d Ws) x"
    using amplification_add[
        where F="\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)" and G="kraus_map_dim d Ws"
          and n=n and d=d and p=p and x=x,
        OF dpos term_c rest_c]
    by (simp add: cons_fun)
  also have "\<dots> =
        ((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) +
        kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) x"
    using kraus_amplification_single[OF Wc x dpos npos] Cons.IH[OF Wsc] by simp
  also have "\<dots> = kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) (W # Ws)) x"
    using Wc by (simp add: hermite_cnj_of_tensor)
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

end
