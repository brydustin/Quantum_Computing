(*  Title:   Day13_Density_Matrices.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 26 September 2011 (Day 13)
*)

theory Day13_Density_Matrices
  imports Day07_Postulates
begin

section \<open>Day 13 (26 September 2011): ensembles and density matrices\<close>

subsection \<open>Ensembles\<close>

text \<open>Motivation: measuring $\psi=a\ket0+b\ket1$ with $M_0=\ketbra00$, $M_1=\ketbra11$ leaves
the state $\tfrac a{|a|}\ket0$ with probability $|a|^2$ and $\tfrac b{|b|}\ket1$ with
probability $|b|^2$; a later measurement $\{\tilde M_\alpha\}$ then has outcome probabilities
$p_\alpha=|a|^2\norm{\tilde M_\alpha\tfrac a{|a|}\ket0}^2+|b|^2\norm{\tilde M_\alpha\tfrac b{|b|}\ket1}^2$.
\begin{notesdef}
An \emph{ensemble} $\{p_i,\psi_i\}_{i=1}^L$ is a set of states with probabilities $p_i\ge0$,
$\sum_ip_i=1$.  For a measurement system $\{M_\alpha\}$ the probability of outcome $\alpha$ is
$p_\alpha(\{p_i,\psi_i\})=\sum_ip_i\norm{M_\alpha\psi_i}^2$.
\end{notesdef}
A second source of ensembles: a unit vector $\psi=\sum_l\phi_l\otimes f_l\in\Hil_A\otimes\Hil_E$
(environment $\Hil_E$ with orthonormal basis $f_l$) behaves, for measurements $M_\alpha\otimes I$,
exactly like the ensemble $\{\norm{\phi_l}^2,\phi_l/\norm{\phi_l}\}$.\<close>

definition ensemble :: "nat \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> bool" where
  "ensemble n E \<equiv>
     (\<forall>(p, \<psi>) \<in> set E. p \<ge> 0 \<and> quantum_state n \<psi>) \<and>
     (\<Sum>(p, _) \<leftarrow> E. p) = 1"

subsection \<open>Von Neumann's density matrix\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{tikzpicture}[st/.style={draw, rounded corners, fill=blue!6, inner sep=4pt, font=\small}, ar/.style={-{Stealth}, thick}]
\node[st] (e1) {$\{(\tfrac12,\ket0),\ (\tfrac12,\ket1)\}$};
\node[st, below=0.6cm of e1] (e2) {$\{(\tfrac12,\ket+),\ (\tfrac12,\ket-)\}$};
\node[st, right=2.2cm of $(e1)!0.5!(e2)$] (r) {$\rho=\sum_ip_i\psi_i\psi_i^* = \tfrac12 I$};
\draw[ar] (e1.east) -- (r.west); \draw[ar] (e2.east) -- (r.west);
\end{tikzpicture}\\[0.2em]
{\small Two ensembles, one density matrix: every measurement gives them the same outcome probabilities $\tr(M_\alpha^*M_\alpha\rho)$.}
\end{center}
\<close>

text \<open>Measurements cannot distinguish $\psi$ from $e^{i\theta}\psi$, and
$\ketbra{e^{i\theta}\psi}{e^{i\theta}\psi}=\ketbra\psi\psi=(\alpha_i\overline{\alpha_j})$: the
object attached to a state is the projection, not the vector.  For any $\gamma$,
$\norm\gamma^2=\Tr\ketbra\gamma\gamma$, and
\[ p_\alpha(\psi)=\norm{M_\alpha\psi}^2=\Tr\bigl((M_\alpha^*M_\alpha)(\psi\psi^*)\bigr),\qquad
   p_\alpha(\{p_l,\psi_l\})=\Tr\Bigl((M_\alpha^*M_\alpha)\sum_lp_l\psi_l\psi_l^*\Bigr). \]
\begin{notesdef}
$P=\sum_lp_l\ketbra{\psi_l}{\psi_l}$ is the \emph{density matrix} of the ensemble.
\end{notesdef}
Formally \<open>pure_density \<psi>\<close> is $\ketbra\psi\psi$, \<open>ensemble_density n E\<close> is $P$, and
\<open>density_matrix n \<rho>\<close> is the Day 14 characterisation ($\rho\ge0$, $\Tr\rho=1$).\<close>

definition density_matrix :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "density_matrix n \<rho> \<equiv> \<rho> \<in> carrier_mat n n \<and> psd \<rho> \<and> Tr \<rho> = 1"

definition pure_density :: "complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "pure_density \<psi> \<equiv>
     let n = dim_vec \<psi> in
     outer_sum n [\<psi>]"

text \<open>$\Tr\ketbra\psi\psi=\sum_i\psi_i\overline{\psi_i}=\norm\psi^2$, so a unit vector gives a
density matrix.\<close>

lemma Tr_outer_sum_single:
  assumes dim: "dim_vec \<psi> = n"
  shows "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
proof -
  have "Tr (outer_sum n [\<psi>]) = (\<Sum>r<n. \<psi> $ r * cnj (\<psi> $ r))"
    using dim
    by (simp add: Tr_def outer_sum_def mat_of_cols_def dagger_def scalar_prod_def)
  also have "\<dots> = (\<Sum>r<n. cnj (\<psi> $ r) * \<psi> $ r)"
    by (simp add: mult.commute)
  also have "\<dots> = \<langle>\<psi> | \<psi>\<rangle>"
    using dim by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma pure_density_is_density_matrix:
  assumes "quantum_state n \<psi>"
  shows "density_matrix n (pure_density \<psi>)"
proof -
  have dim: "dim_vec \<psi> = n" using assms by (auto simp: quantum_state_def)
  have norm: "\<parallel>\<psi>\<parallel> = 1" using assms by (auto simp: quantum_state_def)
  have psd: "psd (outer_sum n [\<psi>])"
    using dim by (intro outer_sum_psd) auto
  have tr: "Tr (outer_sum n [\<psi>]) = 1"
  proof -
    have "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
      by (rule Tr_outer_sum_single[OF dim])
    also have "\<dots> = 1"
      using norm cpx_vec_length_inner_prod[of \<psi>] by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding density_matrix_def pure_density_def Let_def
    using dim psd tr by fastforce
qed

text \<open>An ensemble $\{p_i,\psi_i\}$ has $\rho=\sum_ip_i\ketbra{\psi_i}{\psi_i}$.  It is positive, as a
non-negative combination of the positive $\ketbra{\psi_i}{\psi_i}$, and
$\Tr\rho=\sum_ip_i\norm{\psi_i}^2=\sum_ip_i=1$.\<close>

definition ensemble_density :: "nat \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> complex Matrix.mat" where
  "ensemble_density n E \<equiv>
     foldr (\<lambda>(p,\<psi>) acc. complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + acc)
           E (0\<^sub>m n n)"

lemma psd_zero_mat [simp]:
  "psd (0\<^sub>m n n)"
proof -
  have herm: "((0\<^sub>m n n)\<^sup>\<dagger>) = 0\<^sub>m n n"
    unfolding dagger_def by (rule eq_matI) simp_all
  have quad: "\<And>x::complex Matrix.vec.
        dim_vec x = n \<Longrightarrow> Re (\<langle>x | (0\<^sub>m n n) *\<^sub>v x\<rangle>) \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec" assume dx: "dim_vec x = n"
    have "(0\<^sub>m n n) *\<^sub>v x = 0\<^sub>v n"
      using dx by (intro eq_vecI) (simp_all add: scalar_prod_def)
    hence "\<langle>x | (0\<^sub>m n n) *\<^sub>v x\<rangle> = 0"
      using dx by (simp add: inner_prod_def)
    thus "Re (\<langle>x | (0\<^sub>m n n) *\<^sub>v x\<rangle>) \<ge> 0" by simp
  qed
  show ?thesis
    unfolding psd_def hermitian_def
    using herm quad by simp
qed

lemma ensemble_density_Nil [simp]:
  "ensemble_density n [] = 0\<^sub>m n n"
  by (simp add: ensemble_density_def)

lemma ensemble_density_Cons:
  "ensemble_density n ((p, \<psi>) # E) =
     complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + ensemble_density n E"
  by (simp add: ensemble_density_def)

lemma ensemble_density_carrier:
  assumes "\<forall>(p, \<psi>) \<in> set E. quantum_state n \<psi>"
  shows "ensemble_density n E \<in> carrier_mat n n"
  using assms
proof (induct E)
  case Nil
  show ?case by simp
next
  case (Cons a E)
  obtain p \<psi> where a_eq: "a = (p, \<psi>)" by (cases a) auto
  have q: "quantum_state n \<psi>" using Cons.prems a_eq by auto
  have os_car: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have sm_car: "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n"
    using os_car by auto
  have IH: "ensemble_density n E \<in> carrier_mat n n"
    using Cons.hyps Cons.prems by auto
  show ?case
    unfolding a_eq ensemble_density_Cons
    using IH by (rule add_carrier_mat)
qed

lemma ensemble_density_psd_aux:
  assumes "\<forall>(p, \<psi>) \<in> set E. p \<ge> 0 \<and> quantum_state n \<psi>"
  shows "psd (ensemble_density n E)"
  using assms
proof (induct E)
  case Nil
  show ?case by simp
next
  case (Cons a E)
  obtain p \<psi> where a_eq: "a = (p, \<psi>)" by (cases a) auto
  have p_nn: "0 \<le> p" using Cons.prems a_eq by auto
  have q: "quantum_state n \<psi>" using Cons.prems a_eq by auto
  have d\<psi>: "dim_vec \<psi> = n" using q by (simp add: quantum_state_def)

  have os_car: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have os_psd: "psd (outer_sum n [\<psi>])"
    using d\<psi> by (intro outer_sum_psd) auto
  have sm_psd: "psd (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>])"
    using p_nn os_psd os_car by (rule psd_smult_nonneg)
  have sm_car: "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n"
    using os_car by auto

  have IH_psd: "psd (ensemble_density n E)"
    using Cons.hyps Cons.prems by auto
  have IH_car: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier) (use Cons.prems in auto)

  show ?case
    unfolding a_eq ensemble_density_Cons
    using sm_psd IH_psd sm_car IH_car by (rule psd_add_psd)
qed

lemma Tr_zero_mat' [simp]:
  "Tr (0\<^sub>m n n) = 0"
  by (simp add: Tr_def zero_mat_def)

lemma ensemble_density_Tr:
  assumes "\<forall>(p, \<psi>) \<in> set E. quantum_state n \<psi>"
  shows "Tr (ensemble_density n E) = complex_of_real (\<Sum>(p, _) \<leftarrow> E. p)"
  using assms
proof (induct E)
  case Nil
  show ?case by simp
next
  case (Cons a E)
  obtain p \<psi> where a_eq: "a = (p, \<psi>)" by (cases a) auto
  have q: "quantum_state n \<psi>" using Cons.prems a_eq by auto
  have d\<psi>: "dim_vec \<psi> = n" using q by (simp add: quantum_state_def)

  have os_car: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have sm_car: "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n"
    using os_car by auto
  have IH_car: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier) (use Cons.prems in auto)

  have Tr_os: "Tr (outer_sum n [\<psi>]) = 1"
    using quantum_state_norm1[OF q] unfolding Tr_outer_sum_single[OF d\<psi>] cpx_vec_length_one_iff .

  have "Tr (ensemble_density n ((p, \<psi>) # E))
        = Tr (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + ensemble_density n E)"
    by (simp add: ensemble_density_Cons)
  also have "\<dots> = Tr (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>]) + Tr (ensemble_density n E)"
  proof (rule Tr_add)
    show "dim_row (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>]) = dim_row (ensemble_density n E)"
      using sm_car IH_car by auto
    show "dim_col (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>]) = dim_col (ensemble_density n E)"
      using sm_car IH_car by auto
  qed
  also have "\<dots> = complex_of_real p * Tr (outer_sum n [\<psi>]) + Tr (ensemble_density n E)"
    by (simp add: Tr_smult)
  also have "\<dots> = complex_of_real p + Tr (ensemble_density n E)"
    using Tr_os by simp
  also have "\<dots> = complex_of_real p + complex_of_real (\<Sum>(p, _) \<leftarrow> E. p)"
    using Cons.hyps Cons.prems by auto
  also have "\<dots> = complex_of_real (p + (\<Sum>(p, _) \<leftarrow> E. p))"
    by simp
  also have "\<dots> = complex_of_real (\<Sum>(p, _) \<leftarrow> ((p, \<psi>) # E). p)"
    by simp
  finally show ?case unfolding a_eq .
qed

theorem ensemble_density_is_dm:
  assumes E: "ensemble n E"
  shows "density_matrix n (ensemble_density n E)"
proof -
  from E have states_q: "\<forall>(p, \<psi>) \<in> set E. quantum_state n \<psi>"
    and states_pq: "\<forall>(p, \<psi>) \<in> set E. p \<ge> 0 \<and> quantum_state n \<psi>"
    and probs: "(\<Sum>(p, _) \<leftarrow> E. p) = 1"
    unfolding ensemble_def by auto

  have carr: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier[OF states_q])
  have psd_ed: "psd (ensemble_density n E)"
    by (rule ensemble_density_psd_aux[OF states_pq])
  have tr_ed: "Tr (ensemble_density n E) = 1"
    using ensemble_density_Tr[OF states_q] probs by simp

  show ?thesis
    unfolding density_matrix_def
    using carr psd_ed tr_ed by blast
qed

subsection \<open>Probabilities via the trace\<close>

text \<open>$p_\alpha(\psi)=\norm{M_\alpha\psi}^2=\Tr(M_\alpha^*M_\alpha\ketbra\psi\psi)$.  For an
ensemble with density matrix $\rho$, $p_\alpha=\Tr(M_\alpha^*M_\alpha\rho)
=\langle M_\alpha^*M_\alpha|\rho\rangle$ (\<open>ensemble_prob_trace_eq\<close> below).\<close>

lemma pure_state_prob_trace:
  fixes M :: "complex Matrix.mat" and \<psi> :: "complex Matrix.vec"
  assumes st: "quantum_state n \<psi>"
      and Msq: "M \<in> carrier_mat n n"
  shows "meas_prob M \<psi> = Re (Tr ((M\<^sup>\<dagger>) * M * outer_sum n [\<psi>]))"
proof -
  have d: "dim_vec \<psi> = n" using st by (simp add: quantum_state_def)
  have Md: "M\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Msq])
  have "Tr ((M\<^sup>\<dagger>) * M * outer_sum n [\<psi>]) = \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>"
    unfolding outer_sum_singleton_eq[OF d] by (rule Tr_mult_outer[OF mult_carrier_mat[OF Md Msq] d])
  also have "\<dots> = \<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
    unfolding assoc_mult_mat_vec[OF Md Msq carrier_vecI[OF d]]
    using Msq by (subst inner_prod_adjoint_swap[OF Md d]) (simp_all add: d dagger_of_dagger_is_id)
  finally show ?thesis unfolding meas_prob_def
    using arg_cong[OF cpx_vec_length_inner_prod[of "M *\<^sub>v \<psi>"], of Re] by simp
qed

text \<open>For an ensemble: $p_\alpha(\{p_i,\psi_i\})=\sum_ip_i\norm{M_\alpha\psi_i}^2=\Tr(M_\alpha^*M_\alpha\rho)$.\<close>

lemma ensemble_prob_trace_eq:
  fixes M :: "complex Matrix.mat"
  assumes M: "M \<in> carrier_mat n n"
      and E: "\<forall>(p, \<psi>) \<in> set E. quantum_state n \<psi>"
  shows "(\<Sum>(p, \<psi>) \<leftarrow> E. p * meas_prob M \<psi>)
           = Re (Tr (((M\<^sup>\<dagger>) * M) * ensemble_density n E))"
  using E
proof (induction E)
  case Nil
  have "((M\<^sup>\<dagger>) * M) * ensemble_density n [] = 0\<^sub>m n n" using M by auto
  thus ?case by simp
next
  case (Cons pe E)
  obtain p \<psi> where pe: "pe = (p, \<psi>)" by (cases pe)
  have qs: "quantum_state n \<psi>" using Cons.prems pe by auto
  have \<psi>d: "dim_vec \<psi> = n" using qs by (simp add: quantum_state_def)
  have rest: "\<forall>(p, \<psi>) \<in> set E. quantum_state n \<psi>" using Cons.prems by auto
  have MM: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n" using M by auto
  have os: "outer_sum n [\<psi>] \<in> carrier_mat n n" by (intro carrier_matI) auto
  have ed: "ensemble_density n E \<in> carrier_mat n n" by (rule ensemble_density_carrier[OF rest])
  have pos_c: "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n" using os by auto
  have "((M\<^sup>\<dagger>) * M) * ensemble_density n (pe # E)
          = ((M\<^sup>\<dagger>) * M) * (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>])
            + ((M\<^sup>\<dagger>) * M) * ensemble_density n E"
    unfolding pe ensemble_density_Cons by (rule mult_add_distrib_mat[OF MM pos_c ed])
  also have "((M\<^sup>\<dagger>) * M) * (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>])
               = complex_of_real p \<cdot>\<^sub>m (((M\<^sup>\<dagger>) * M) * outer_sum n [\<psi>])"
    by (rule mult_smult_distrib[OF MM os])
  finally have "((M\<^sup>\<dagger>) * M) * ensemble_density n (pe # E)
          = complex_of_real p \<cdot>\<^sub>m (((M\<^sup>\<dagger>) * M) * outer_sum n [\<psi>])
            + ((M\<^sup>\<dagger>) * M) * ensemble_density n E" .
  hence "Tr (((M\<^sup>\<dagger>) * M) * ensemble_density n (pe # E))
          = complex_of_real p * Tr (((M\<^sup>\<dagger>) * M) * outer_sum n [\<psi>])
            + Tr (((M\<^sup>\<dagger>) * M) * ensemble_density n E)"
    using MM os ed by (simp add: Tr_add Tr_smult)
  hence "Re (Tr (((M\<^sup>\<dagger>) * M) * ensemble_density n (pe # E)))
          = p * Re (Tr (((M\<^sup>\<dagger>) * M) * outer_sum n [\<psi>]))
            + Re (Tr (((M\<^sup>\<dagger>) * M) * ensemble_density n E))"
    by simp
  also have "Re (Tr (((M\<^sup>\<dagger>) * M) * outer_sum n [\<psi>])) = meas_prob M \<psi>"
    using pure_state_prob_trace[OF qs M] by simp
  finally show ?case
    using Cons.IH[OF rest] pe by simp
qed

lemma Tr_psd_Re_nonneg:
  assumes P: "psd P" and Pc: "P \<in> carrier_mat n n"
  shows "0 \<le> Re (Tr P)"
proof -
  have Pii: "0 \<le> Re (P $$ (i, i))" if "i < n" for i
    using P[unfolded psd_iff_quad_form_nonneg[OF Pc], rule_format, of "unit_vec n i"]
    unfolding inner_unit_T_unit[OF Pc that that] by simp
  show ?thesis unfolding Tr_carrier[OF Pc] Re_sum by (rule sum_nonneg) (simp add: Pii)
qed

lemma ensemble_prob_trace:
  fixes Ms :: "complex Matrix.mat list"
  assumes ms: "measurement_system n Ms"
      and dm: "density_matrix n \<rho>"
      and Min: "M \<in> set Ms"
  shows "Re (Tr ((M\<^sup>\<dagger>) * M * \<rho>)) \<ge> 0"
proof -
  have M: "M \<in> carrier_mat n n" using ms Min by (auto simp: measurement_system_def)
  have \<rho>: "\<rho> \<in> carrier_mat n n" "psd \<rho>" using dm by (auto simp: density_matrix_def)
  have Md: "M\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF M])
  have "Tr ((M\<^sup>\<dagger>) * M * \<rho>) = Tr ((M * \<rho>) * (M\<^sup>\<dagger>))"
    unfolding assoc_mult_mat[OF Md M \<rho>(1)] by (rule Tr_cyclic) (use M \<rho>(1) in simp_all)
  moreover have "psd (M * \<rho> * (M\<^sup>\<dagger>))"
    using psd_conjugate[OF \<rho> Md] by (simp add: dagger_of_dagger_is_id)
  ultimately show ?thesis
    using Tr_psd_Re_nonneg[OF _ mult_carrier_mat[OF mult_carrier_mat[OF M \<rho>(1)] Md]] by simp
qed

text \<open>Day 13: $\ketbra{e^{i\theta}\psi}{e^{i\theta}\psi}=\ketbra\psi\psi$; the density matrix forgets the phase.\<close>

lemma pure_density_smult_unit:
  fixes \<psi> :: "complex Matrix.vec" and c :: complex
  assumes c: "cmod c = 1"
  shows "pure_density (c \<cdot>\<^sub>v \<psi>) = pure_density \<psi>"
proof -
  let ?n = "dim_vec \<psi>"
  have cc: "c * cnj c = 1"
    unfolding complex_norm_square[symmetric] c by simp
  show ?thesis
    unfolding pure_density_def Let_def
  proof (rule eq_matI)
    show "dim_row (outer_sum (dim_vec (c \<cdot>\<^sub>v \<psi>)) [c \<cdot>\<^sub>v \<psi>]) = dim_row (outer_sum ?n [\<psi>])" by simp
    show "dim_col (outer_sum (dim_vec (c \<cdot>\<^sub>v \<psi>)) [c \<cdot>\<^sub>v \<psi>]) = dim_col (outer_sum ?n [\<psi>])" by simp
    fix i j assume "i < dim_row (outer_sum ?n [\<psi>])" "j < dim_col (outer_sum ?n [\<psi>])"
    hence ij: "i < ?n" "j < ?n" by auto
    have "outer_sum (dim_vec (c \<cdot>\<^sub>v \<psi>)) [c \<cdot>\<^sub>v \<psi>] $$ (i, j) = (c * \<psi> $ i) * cnj (c * \<psi> $ j)"
      using outer_sum_singleton_index[of i ?n j "c \<cdot>\<^sub>v \<psi>"] ij by simp
    also have "\<dots> = (c * cnj c) * (\<psi> $ i * cnj (\<psi> $ j))" by (simp add: algebra_simps)
    also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j)" using cc by simp
    also have "\<dots> = outer_sum ?n [\<psi>] $$ (i, j)"
      using outer_sum_singleton_index[OF ij] by simp
    finally show "outer_sum (dim_vec (c \<cdot>\<^sub>v \<psi>)) [c \<cdot>\<^sub>v \<psi>] $$ (i, j) = outer_sum ?n [\<psi>] $$ (i, j)" .
  qed
qed

end
