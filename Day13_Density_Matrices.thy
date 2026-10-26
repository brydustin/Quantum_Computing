(*  Title:   Day13_Density_Matrices.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 26 September 2011 (Day 13)
*)

theory Day13_Density_Matrices
  imports Day12_Quantum_Parallelism
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
  (* pure_density \<psi> = |\<psi>\<rangle>\<langle>\<psi>|.  Hermitian: outer_sum_hermitian.
     PSD: outer_sum_psd.  Tr = \<langle>\<psi>|\<psi>\<rangle> = \<parallel>\<psi>\<parallel>\<^sup>2 = 1. *)
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

lemma psd_add_psd:
  assumes A: "psd A" and B: "psd B"
      and Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n"
  shows "psd (A + B)"
proof -
  have A_dagger: "(A\<^sup>\<dagger>) = A" using A by (simp add: psd_def hermitian_def)
  have B_dagger: "(B\<^sup>\<dagger>) = B" using B by (simp add: psd_def hermitian_def)
  have A_quad: "\<And>x. dim_vec x = n \<Longrightarrow> Re (\<langle>x | A *\<^sub>v x\<rangle>) \<ge> 0"
    using A Ac by (simp add: psd_def)
  have B_quad: "\<And>x. dim_vec x = n \<Longrightarrow> Re (\<langle>x | B *\<^sub>v x\<rangle>) \<ge> 0"
    using B Bc by (simp add: psd_def)

  have herm_AB: "((A + B)\<^sup>\<dagger>) = A + B"
  proof (rule eq_matI)
    show "dim_row ((A + B)\<^sup>\<dagger>) = dim_row (A + B)"
      using Ac Bc by simp
    show "dim_col ((A + B)\<^sup>\<dagger>) = dim_col (A + B)"
      using Ac Bc by simp
  next
    fix i j
    assume "i < dim_row (A + B)" and "j < dim_col (A + B)"
    then have i: "i < n" and j: "j < n" using Ac Bc by auto
    have "((A + B)\<^sup>\<dagger>) $$ (i, j) = cnj ((A + B) $$ (j, i))"
      using i j Ac Bc by (simp add: dagger_def)
    also have "\<dots> = cnj (A $$ (j, i)) + cnj (B $$ (j, i))"
      using i j Ac Bc by simp
    also have "\<dots> = (A\<^sup>\<dagger>) $$ (i, j) + (B\<^sup>\<dagger>) $$ (i, j)"
      using i j Ac Bc by (simp add: dagger_def)
    also have "\<dots> = A $$ (i, j) + B $$ (i, j)"
      using A_dagger B_dagger by simp
    also have "\<dots> = (A + B) $$ (i, j)"
      using i j Ac Bc by simp
    finally show "((A + B)\<^sup>\<dagger>) $$ (i, j) = (A + B) $$ (i, j)" .
  qed

  have quad: "\<And>x. dim_vec x = dim_row (A + B) \<Longrightarrow>
                Re (\<langle>x | (A + B) *\<^sub>v x\<rangle>) \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec"
    assume dx: "dim_vec x = dim_row (A + B)"
    hence dx': "dim_vec x = n" using Ac Bc by simp
    have x_car: "x \<in> carrier_vec n" using dx' by auto
    have Ax_car: "A *\<^sub>v x \<in> carrier_vec n" using Ac x_car by auto
    have Bx_car: "B *\<^sub>v x \<in> carrier_vec n" using Bc x_car by auto
    have dim_eq: "dim_vec (A *\<^sub>v x) = dim_vec (B *\<^sub>v x)"
      using Ac Bc by simp

    have "\<langle>x | (A + B) *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x + B *\<^sub>v x\<rangle>"
      using add_mult_distrib_mat_vec[OF Ac Bc x_car] by simp
    also have "\<dots> = \<langle>x | A *\<^sub>v x\<rangle> + \<langle>x | B *\<^sub>v x\<rangle>"
      by (rule inner_prod_right_add'[OF dim_eq])
    finally have eq: "\<langle>x | (A + B) *\<^sub>v x\<rangle>
                    = \<langle>x | A *\<^sub>v x\<rangle> + \<langle>x | B *\<^sub>v x\<rangle>" .

    have "0 \<le> Re (\<langle>x | A *\<^sub>v x\<rangle>) + Re (\<langle>x | B *\<^sub>v x\<rangle>)"
      using A_quad[OF dx'] B_quad[OF dx'] by simp
    thus "0 \<le> Re (\<langle>x | (A + B) *\<^sub>v x\<rangle>)"
      using eq by simp
  qed

  show ?thesis
    unfolding psd_def hermitian_def
    using herm_AB quad by blast
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
  proof -
    have "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
      by (rule Tr_outer_sum_single[OF d\<psi>])
    also have "\<dots> = 1"
      using q by (metis cpx_vec_length_inner_prod of_real_1 one_power2 quantum_state_norm1)
    finally show ?thesis .
  qed

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
  let ?A = "(M\<^sup>\<dagger>) * M"
  have Ac: "?A \<in> carrier_mat n n" using Msq by auto
  have dpsi: "dim_vec \<psi> = n" using st by (simp add: quantum_state_def)
  have psi_car: "\<psi> \<in> carrier_vec n" using dpsi by auto
  have Mpsi_car: "M *\<^sub>v \<psi> \<in> carrier_vec n" using Msq psi_car by auto

  \<comment> \<open>Entry formula for \<open>outer_sum n [\<psi>]\<close>.\<close>
  have OS_entry: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
                 outer_sum n [\<psi>] $$ (i, j) = \<psi> $ i * cnj (\<psi> $ j)"
  proof -
    fix i j :: nat assume i: "i < n" and j: "j < n"
    let ?V = "mat_of_cols n [\<psi>]"
    have dVr: "dim_row ?V = n" by simp
    have dVc: "dim_col ?V = 1" by simp
    have Vc: "?V \<in> carrier_mat n 1" by auto
    have dVdr: "dim_row (?V\<^sup>\<dagger>) = 1" by simp
    have dVdc: "dim_col (?V\<^sup>\<dagger>) = n" by simp
    have Vdc: "(?V\<^sup>\<dagger>) \<in> carrier_mat 1 n"
      using dVdr dVdc by auto

    have Vi0: "?V $$ (i, 0) = \<psi> $ i"
      using i by (simp add: mat_of_cols_index)
    have Vj0: "?V $$ (j, 0) = \<psi> $ j"
      using j by (simp add: mat_of_cols_index)
    have Vd_0j: "(?V\<^sup>\<dagger>) $$ (0, j) = cnj (\<psi> $ j)"
    proof -
      have "(?V\<^sup>\<dagger>) $$ (0, j) = cnj (?V $$ (j, 0))"
        using j dVr dVc by (simp add: dagger_def)
      with Vj0 show ?thesis by simp
    qed

    have "outer_sum n [\<psi>] $$ (i, j) = (?V * (?V\<^sup>\<dagger>)) $$ (i, j)"
      by (simp add: outer_sum_def)
    also have "\<dots> = Matrix.row ?V i \<bullet> Matrix.col (?V\<^sup>\<dagger>) j"
    proof -
      have "i < dim_row ?V" using i dVr by simp
      moreover have "j < dim_col (?V\<^sup>\<dagger>)" using j dVdc by simp
      ultimately show ?thesis by (simp add: times_mat_def)
    qed
    also have "\<dots> = (\<Sum>k = 0..<1. Matrix.row ?V i $ k * Matrix.col (?V\<^sup>\<dagger>) j $ k)"
      using dVdr by (simp add: scalar_prod_def)
    also have "\<dots> = Matrix.row ?V i $ 0 * Matrix.col (?V\<^sup>\<dagger>) j $ 0" by simp
    also have "Matrix.row ?V i $ 0 = ?V $$ (i, 0)"
      using i dVc by auto
    also have "Matrix.col (?V\<^sup>\<dagger>) j $ 0 = (?V\<^sup>\<dagger>) $$ (0, j)"
    proof -
      have h1: "0 < dim_row (?V\<^sup>\<dagger>)" using dVdr by simp
      have h2: "j < dim_col (?V\<^sup>\<dagger>)" using j dVdc by simp
      show ?thesis by (rule index_col[OF h1 h2])
    qed
    finally show "outer_sum n [\<psi>] $$ (i, j) = \<psi> $ i * cnj (\<psi> $ j)"
      using Vi0 Vd_0j by simp
  qed

  \<comment> \<open>Cyclic identity: \<open>Tr (A \<cdot> |\<psi>\<rangle>\<langle>\<psi>|) = \<langle>\<psi> | A \<psi>\<rangle>\<close>.\<close>
  have Tr_id: "Tr (?A * outer_sum n [\<psi>]) = \<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>"
  proof -
    have OSc: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
    have prodc: "?A * outer_sum n [\<psi>] \<in> carrier_mat n n" using Ac OSc by auto
    have "Tr (?A * outer_sum n [\<psi>])
           = (\<Sum>i<n. (?A * outer_sum n [\<psi>]) $$ (i, i))"
    proof -
      have dr: "dim_row (?A * outer_sum n [\<psi>]) = n" using prodc by auto
      have dc: "dim_col (?A * outer_sum n [\<psi>]) = n" using prodc by auto
      show ?thesis using dr dc by (simp add: Tr_def)
    qed
    also have "\<dots> = (\<Sum>i<n. \<Sum>k = 0..<n. ?A $$ (i, k) * outer_sum n [\<psi>] $$ (k, i))"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {..<n}"
      hence i: "i < n" by simp
      have iA: "i < dim_row ?A" using i Ac by auto
      have iOS: "i < dim_col (outer_sum n [\<psi>])" using i OSc by auto
      have dOS: "dim_row (outer_sum n [\<psi>]) = n" using OSc by auto
      have "(?A * outer_sum n [\<psi>]) $$ (i, i)
            = Matrix.row ?A i \<bullet> Matrix.col (outer_sum n [\<psi>]) i"
        using iA iOS by (simp add: times_mat_def)
      also have "\<dots> = (\<Sum>k = 0..<n.
           Matrix.row ?A i $ k * Matrix.col (outer_sum n [\<psi>]) i $ k)"
        using dOS by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>k = 0..<n. ?A $$ (i, k) * outer_sum n [\<psi>] $$ (k, i))"
      proof (intro sum.cong refl)
        fix k assume "k \<in> {0..<n}"
        hence k: "k < n" by simp
        have "Matrix.row ?A i $ k = ?A $$ (i, k)"
          using i k Ac by auto
        moreover have "Matrix.col (outer_sum n [\<psi>]) i $ k
                     = outer_sum n [\<psi>] $$ (k, i)"
          using k i OSc by auto
        ultimately show
          "Matrix.row ?A i $ k * Matrix.col (outer_sum n [\<psi>]) i $ k
             = ?A $$ (i, k) * outer_sum n [\<psi>] $$ (k, i)"
          by simp
      qed
      finally show "(?A * outer_sum n [\<psi>]) $$ (i, i)
                  = (\<Sum>k = 0..<n. ?A $$ (i, k) * outer_sum n [\<psi>] $$ (k, i))" .
    qed
    also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i)))"
    proof -
      have entry:
        "\<And>i j. i \<in> {..<n} \<Longrightarrow> j \<in> {..<n} \<Longrightarrow>
            ?A $$ (i, j) * outer_sum n [\<psi>] $$ (j, i)
             = ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i))"
      proof -
        fix i j
        assume "i \<in> {..<n}"
        assume "j \<in> {..<n}"
        hence i: "i < n" and j: "j < n"
          using \<open>i \<in> {..<n}\<close> by auto 
        from OS_entry[OF j i]
        show "?A $$ (i, j) * outer_sum n [\<psi>] $$ (j, i)
             = ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i))"
          by simp
      qed
      have "(\<Sum>i<n. \<Sum>j = 0..<n. ?A $$ (i, j) * outer_sum n [\<psi>] $$ (j, i))
           = (\<Sum>i<n. \<Sum>j<n. ?A $$ (i, j) * outer_sum n [\<psi>] $$ (j, i))"
        by (simp add: lessThan_atLeast0)
      also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i)))"
        using entry by (intro sum.cong refl) simp
      finally show ?thesis.
    qed
    also have "\<dots> = (\<Sum>i<n. cnj (\<psi> $ i) * (\<Sum>k = 0..<n. ?A $$ (i, k) * \<psi> $ k))"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {..<n}"
      have "(\<Sum>j<n. ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i)))
           = (\<Sum>j<n. cnj (\<psi> $ i) * (?A $$ (i, j) * \<psi> $ j))"
        by (intro sum.cong refl) (simp add: ac_simps)
      also have "\<dots> = cnj (\<psi> $ i) * (\<Sum>j<n. ?A $$ (i, j) * \<psi> $ j)"
        by (simp add: sum_distrib_left)
      also have "\<dots> = cnj (\<psi> $ i) * (\<Sum>k = 0..<n. ?A $$ (i, k) * \<psi> $ k)"
        by (simp add: lessThan_atLeast0)
      finally show "(\<Sum>j<n. ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i)))
                  = cnj (\<psi> $ i) * (\<Sum>k = 0..<n. ?A $$ (i, k) * \<psi> $ k)" .
    qed
    also have "\<dots> = (\<Sum>i<n. cnj (\<psi> $ i) * (?A *\<^sub>v \<psi>) $ i)"
      using Ac dpsi
      by (intro sum.cong refl, simp add: mult_mat_vec_index psi_car)
    also have "\<dots> = \<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>"
      using Msq atLeast0LessThan inner_prod_def by auto 
    finally show ?thesis.
  qed

  \<comment> \<open>Bridge \<open>\<parallel>M\<psi>\<parallel>\<^sup>2 = Re \<langle>\<psi> | M\<^sup>\<dagger> M \<psi>\<rangle>\<close> via adjoint swap.\<close>
  have inner_eq: "\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle> = cnj (\<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>)"
  proof -
    have "\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle> = \<langle>(M\<^sup>\<dagger>) *\<^sub>v (M *\<^sub>v \<psi>) | \<psi>\<rangle>"
    proof -
      have dim_Mpsi: "dim_vec (M *\<^sub>v \<psi>) = n" using Mpsi_car carrier_vecD by blast 
      show ?thesis by (rule inner_prod_adjoint_swap[OF Msq dim_Mpsi dpsi])
    qed
    also have "(M\<^sup>\<dagger>) *\<^sub>v (M *\<^sub>v \<psi>) = ?A *\<^sub>v \<psi>"
      using Msq psi_car
      by (metis assoc_mult_mat_vec carrier_matD(1) carrier_matI dim_col_of_dagger)
    finally have "\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle> = \<langle>?A *\<^sub>v \<psi> | \<psi>\<rangle>".
    also have "\<dots> = cnj (\<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>)"
      using Msq dpsi inner_prod_cnj by force          
    finally show ?thesis.
  qed

  have norm_sq: "\<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2 = Re (\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>)"
    by (metis Re_complex_of_real cpx_vec_length_inner_prod)
  have "meas_prob M \<psi> = \<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2" by (simp add: meas_prob_def)
  also have "\<dots> = Re (\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>)" by (rule norm_sq)
  also have "\<dots> = Re (cnj (\<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>))" using inner_eq by simp
  also have "\<dots> = Re (\<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>)" by simp
  also have "\<dots> = Re (Tr (?A * outer_sum n [\<psi>]))" using Tr_id by simp
  finally show ?thesis.
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
  have dr: "dim_row P = n" and dc: "dim_col P = n" using Pc by auto

  \<comment> \<open>Diagonal entries are inner products with unit vectors.\<close>
  have diag_entry:
    "\<And>i. i < n \<Longrightarrow> P $$ (i, i) = \<langle>unit_vec n i | P *\<^sub>v unit_vec n i\<rangle>"
  proof -
    fix i assume i: "i < n"
    let ?e = "unit_vec n i"
    have de: "dim_vec ?e = n" by simp
    have Pe_idx: "\<And>k. k < n \<Longrightarrow> (P *\<^sub>v ?e) $ k = P $$ (k, i)"
    proof -
      fix k assume k: "k < n"
      have "(P *\<^sub>v ?e) $ k = Matrix.row P k \<bullet> ?e"
        using k Pc by auto
      also have "\<dots> = (\<Sum>m = 0..<n. Matrix.row P k $ m * ?e $ m)"
        using k Pc by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>m = 0..<n. if m = i then Matrix.row P k $ m else 0)"
        using i by (intro sum.cong refl) simp
      also have "\<dots> = Matrix.row P k $ i"
        using i by simp
      also have "\<dots> = P $$ (k, i)"
        using k i Pc by auto
      finally show "(P *\<^sub>v ?e) $ k = P $$ (k, i)".
    qed
    have "\<langle>?e | P *\<^sub>v ?e\<rangle> = (\<Sum>k = 0..<n. cnj (?e $ k) * (P *\<^sub>v ?e) $ k)"
      using Pc by (simp add: inner_prod_def)
    also have "\<dots> = (\<Sum>k = 0..<n. if k = i then (P *\<^sub>v ?e) $ k else 0)"
      using i by (intro sum.cong refl) simp
    also have "\<dots> = (P *\<^sub>v ?e) $ i"
      using i by simp
    also have "\<dots> = P $$ (i, i)"
      using Pe_idx[OF i] by simp
    finally show "P $$ (i, i) = \<langle>?e | P *\<^sub>v ?e\<rangle>" by simp
  qed

  \<comment> \<open>Each diagonal entry has non-negative real part, so the trace does.\<close>
  have Re_diag_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> Re (P $$ (i, i))"
  proof -
    fix i assume i: "i < n"
    have "Re (P $$ (i, i)) = Re (\<langle>unit_vec n i | P *\<^sub>v unit_vec n i\<rangle>)"
      using diag_entry[OF i] by simp
    moreover have "0 \<le> Re (\<langle>unit_vec n i | P *\<^sub>v unit_vec n i\<rangle>)"
      using P Pc by (simp add: psd_def)
    ultimately show "0 \<le> Re (P $$ (i, i))" by simp
  qed

  have "Re (Tr P) = Re (\<Sum>r<n. if r < n then P $$ (r, r) else 0)"
    using dr dc by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>r<n. Re (P $$ (r, r)))" by simp
  finally have "Re (Tr P) = (\<Sum>r<n. Re (P $$ (r, r)))".
  moreover have "0 \<le> (\<Sum>r<n. Re (P $$ (r, r)))"
    using Re_diag_nn by (intro sum_nonneg) auto
  ultimately show ?thesis by simp
qed

lemma ensemble_prob_trace:
  fixes Ms :: "complex Matrix.mat list"
  assumes ms: "measurement_system n Ms"
      and dm: "density_matrix n \<rho>"
      and Min: "M \<in> set Ms"
  shows "Re (Tr ((M\<^sup>\<dagger>) * M * \<rho>)) \<ge> 0"
proof -
  have M_carr: "M \<in> carrier_mat n n"
    using ms Min by (auto simp: measurement_system_def)
  have rho_carr: "\<rho> \<in> carrier_mat n n" using dm by (auto simp: density_matrix_def)
  have rho_psd: "psd \<rho>" using dm by (auto simp: density_matrix_def)

  \<comment> \<open>Take a PSD square root of \<open>\<rho>\<close>.\<close>
  obtain Q where Qc: "Q \<in> carrier_mat n n" and Qpsd: "psd Q" and QQ: "Q * Q = \<rho>"
    using psd_sqrt_exists[OF rho_carr rho_psd] by blast
  have Qdag: "(Q\<^sup>\<dagger>) = Q" using Qpsd by (simp add: psd_def hermitian_def)
  have Md_c: "(M\<^sup>\<dagger>) \<in> carrier_mat n n" using M_carr by auto
  have MdM_c: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n" using Md_c M_carr by auto
  have MQ_c: "M * Q \<in> carrier_mat n n" using M_carr Qc by auto
  have MQd_c: "((M * Q)\<^sup>\<dagger>) \<in> carrier_mat n n"
  proof -
    have dr: "dim_row ((M * Q)\<^sup>\<dagger>) = dim_col (M * Q)" by simp
    have dc: "dim_col ((M * Q)\<^sup>\<dagger>) = dim_row (M * Q)" by simp
    have "dim_col (M * Q) = n" using MQ_c by auto
    moreover have "dim_row (M * Q) = n" using MQ_c by auto
    ultimately show ?thesis using dr dc by auto
  qed

  \<comment> \<open>Key identity: \<open>(M*Q)\<^sup>\<dagger> * (M*Q) = Q * (M\<^sup>\<dagger>) * M * Q\<close>.\<close>
  have expand: "((M * Q)\<^sup>\<dagger>) * (M * Q) = Q * ((M\<^sup>\<dagger>) * M) * Q"
  proof -
    have "((M * Q)\<^sup>\<dagger>) * (M * Q) = ((Q\<^sup>\<dagger>) * (M\<^sup>\<dagger>)) * (M * Q)"
      using M_carr Qc by (simp add: dagger_of_prod)
    also have "\<dots> = (Q * (M\<^sup>\<dagger>)) * (M * Q)" using Qdag by simp
    also have "\<dots> = Q * ((M\<^sup>\<dagger>) * (M * Q))"
      using assoc_mult_mat[OF Qc Md_c MQ_c] by simp
    also have "\<dots> = Q * (((M\<^sup>\<dagger>) * M) * Q)"
      using assoc_mult_mat[OF Md_c M_carr Qc, symmetric] by simp
    also have "\<dots> = (Q * ((M\<^sup>\<dagger>) * M)) * Q"
      using assoc_mult_mat[OF Qc MdM_c Qc, symmetric] by simp
    finally show ?thesis by simp
  qed

  \<comment> \<open>Key identity 2: \<open>Tr (A*Q*Q) = Tr (Q * A * Q)\<close> for \<open>A = M\<^sup>\<dagger>*M\<close>.\<close>
  have Tr_eq: "Tr ((M\<^sup>\<dagger>) * M * \<rho>) = Tr (((M * Q)\<^sup>\<dagger>) * (M * Q))"
  proof -
    have "Tr ((M\<^sup>\<dagger>) * M * \<rho>) = Tr ((M\<^sup>\<dagger>) * M * (Q * Q))"
      using QQ by simp
    also have "\<dots> = Tr (((M\<^sup>\<dagger>) * M * Q) * Q)"
      using MdM_c Qc by simp
    also have "\<dots> = Tr (Q * ((M\<^sup>\<dagger>) * M * Q))"
    proof (rule Tr_cyclic)
      show "dim_col ((M\<^sup>\<dagger>) * M * Q) = dim_row Q" using MdM_c Qc by auto
      show "dim_row ((M\<^sup>\<dagger>) * M * Q) = dim_col Q" using MdM_c Qc by auto
    qed
    also have "\<dots> = Tr (Q * ((M\<^sup>\<dagger>) * M) * Q)"
      using Qc MdM_c by simp
    also have "\<dots> = Tr (((M * Q)\<^sup>\<dagger>) * (M * Q))"
      using expand by simp
    finally show ?thesis.
  qed

  \<comment> \<open>\<open>(MQ)\<^sup>\<dagger>(MQ)\<close> is PSD, so its trace has non-negative real part.\<close>
  have MQd_MQ_psd: "psd (((M * Q)\<^sup>\<dagger>) * (M * Q))"
    using psd_MdagM[OF MQ_c] by simp
  have MQd_MQ_c: "((M * Q)\<^sup>\<dagger>) * (M * Q) \<in> carrier_mat n n"
    using MQ_c MQd_c by auto

  have "0 \<le> Re (Tr (((M * Q)\<^sup>\<dagger>) * (M * Q)))"
    using Tr_psd_Re_nonneg[OF MQd_MQ_psd MQd_MQ_c].
  thus ?thesis using Tr_eq by simp
qed

end
