theory HHL_Paper_Program
  imports HHL_Termination HHL_Preconditioned
begin

section \<open>HHL in the paper's regime as a program\<close>

text \<open>The programs of \<open>HHL_Program\<close> assume that every eigenvalue of $A$ is a register value.
Here the circuits of the paper's regime run as QHLProver programs: the window-state clock
register, eigenvalues anywhere in the spectral window, an $\eta$-accurate evolution oracle, the
filtered rotation (\<open>hhl_complete\<close>) and the three-level flag version in the run-time normalisation
(\<open>hhl_paper_runtime\<close>).  The circuits of \<open>HHL_Simulation\<close> become gate lists (\<open>qgates_sem\<close>).
For a target $\ket t$ the postcondition $\ket t\bra t$ measures fidelity: $\{q\,I\}\ S\ \{\ket t\bra t\}$
says that the output passes the test ``is it $\ket t$'' with probability at least $q$.  Generic
rules: one run and a measurement give $q=|\langle t|\psi\rangle|^2$ (\<open>hoare_prog_overlap\<close>);
repeating until outcome 1 gives $|\langle t|\psi\rangle|^2/p$, with termination
(\<open>hoare_rus_overlap\<close>).  A post-selected state within $e$ of $\ket t$ has fidelity at least $1-e^2$
(\<open>fidelity_from_close\<close>).  Amplitude amplification is a program too (\<open>hhl_apx_amplified\<close>,
\<open>hhl_flag_amplified\<close>).\<close>


subsection \<open>Circuits of \<open>HHL_Simulation\<close> as gate lists\<close>

primrec qgates :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> qcirc \<Rightarrow> complex Matrix.mat list" where
  "qgates N m Oc (Gate G) = [G]"
| "qgates N m Oc (Call Pr dg) = [call_mat N m Oc Pr dg]"
| "qgates N m Oc (QSeq a b) = qgates N m Oc a @ qgates N m Oc b"

lemma qgates_ok:
  assumes Oc: "Oc \<in> carrier_mat m m" "Quantum.unitary Oc" and g: "gates_ok (N * m) c"
    and U: "U \<in> set (qgates N m Oc c)"
  shows "U \<in> carrier_mat (N * m) (N * m) \<and> Complex_Matrix.unitary U"
  using g U
proof (induction c)
  case (Gate G)
  thus ?case by (auto simp: unitary_bridge)
next
  case (Call Pr dg)
  have c: "call_mat N m Oc Pr dg \<in> carrier_mat (N * m) (N * m)" by (simp add: call_mat_def)
  have u: "Quantum.unitary (call_mat N m Oc Pr dg)"
    unfolding call_mat_def by (rule ctrl_blocks_unitary) (rule call_blocks[OF Oc])+
  have "U = call_mat N m Oc Pr dg" using Call.prems by simp
  thus ?case using c unitary_bridge[OF c u] by simp
qed auto

lemma qgates_sem:
  assumes Oc: "Oc \<in> carrier_mat m m" "Quantum.unitary Oc" and g: "gates_ok (N * m) c"
  shows "circuit_mat (N * m) (qgates N m Oc c) = sem N m Oc c"
  using g
proof (induction c)
  case (Gate G) thus ?case by (auto simp: left_mult_one_mat)
next
  case (Call Pr dg) thus ?case by (simp add: call_mat_def left_mult_one_mat[OF ctrl_blocks_carrier])
next
  case (QSeq a b)
  have ga: "gates_ok (N * m) a" and gb: "gates_ok (N * m) b" using QSeq.prems by simp_all
  have ca: "\<And>U. U \<in> set (qgates N m Oc a) \<Longrightarrow> U \<in> carrier_mat (N * m) (N * m)" using qgates_ok[OF Oc ga] by blast
  have cb: "\<And>U. U \<in> set (qgates N m Oc b) \<Longrightarrow> U \<in> carrier_mat (N * m) (N * m)" using qgates_ok[OF Oc gb] by blast
  have app: "circuit_mat (N * m) (qgates N m Oc a @ qgates N m Oc b)
             = circuit_mat (N * m) (qgates N m Oc b) * circuit_mat (N * m) (qgates N m Oc a)"
    by (rule circuit_mat_append[where K = "N * m"]) (use ca cb in auto)
  show ?case unfolding qgates.simps sem.simps app QSeq.IH(1)[OF ga] QSeq.IH(2)[OF gb] ..
qed

subsection \<open>Programs with a two-outcome measurement, and the overlap with a target state\<close>

lemma inner_prod_zero_left:
  assumes w: "w \<in> carrier_vec n"
  shows "Complex_Matrix.inner_prod (0\<^sub>v n) w = (0 :: complex)"
proof -
  have "Complex_Matrix.inner_prod w (0\<^sub>v n) = 0" by (rule scalar_prod_left_zero[OF carrier_vecI]) (use w in simp)
  thus ?thesis using inner_prod_swap[OF zero_carrier_vec w] by simp
qed

lemma inner_prod_abs_sq:
  assumes "t \<in> carrier_vec n" "w \<in> carrier_vec n"
  shows "Complex_Matrix.inner_prod t w * Complex_Matrix.inner_prod w t = complex_of_real ((cmod (Complex_Matrix.inner_prod t w))\<^sup>2)"
  using inner_prod_swap[OF assms] complex_norm_square[of "Complex_Matrix.inner_prod t w"] by simp

context state_sig
begin

text \<open>Running a circuit from $\ket0$ and measuring: the output carries the predicate $\ket t\bra t$ with
weight $|\langle t|\psi\rangle|^2$ whenever $t$ lies in the range of the second measurement operator.\<close>

lemma trace_target_branch:
  assumes t: "t \<in> carrier_vec d" and w: "w \<in> carrier_vec d" and Mc: "Mj \<in> carrier_mat d d"
  shows "trace (outer_prod t t * (Mj * (complex_of_real c \<cdot>\<^sub>m outer_prod w w) * adjoint Mj))
         = complex_of_real (c * (cmod (inner_prod (adjoint Mj *\<^sub>v t) w))\<^sup>2)"
proof -
  have e: "Mj * (complex_of_real c \<cdot>\<^sub>m outer_prod w w) * adjoint Mj = complex_of_real c \<cdot>\<^sub>m outer_prod (Mj *\<^sub>v w) (Mj *\<^sub>v w)"
    by (simp only: mult_smult_distrib[OF Mc outer_prod_dim[OF w w]]
          mult_smult_assoc_mat[OF mult_carrier_mat[OF Mc outer_prod_dim[OF w w]] adjoint_dim[OF Mc]]
          outer_prod_left_right_mat[OF w w Mc adjoint_dim[OF Mc]] adjoint_adjoint)
  have Mw: "Mj *\<^sub>v w \<in> carrier_vec d" by (rule mult_mat_vec_carrier[OF Mc w])
  have "trace (outer_prod t t * (complex_of_real c \<cdot>\<^sub>m outer_prod (Mj *\<^sub>v w) (Mj *\<^sub>v w)))
        = complex_of_real c * trace (outer_prod t t * outer_prod (Mj *\<^sub>v w) (Mj *\<^sub>v w))"
    unfolding mult_smult_distrib[OF outer_prod_dim[OF t t] outer_prod_dim[OF Mw Mw]]
    by (rule trace_smult[OF mult_carrier_mat[OF outer_prod_dim[OF t t] outer_prod_dim[OF Mw Mw]]])
  also have "trace (outer_prod t t * outer_prod (Mj *\<^sub>v w) (Mj *\<^sub>v w)) = inner_prod t (Mj *\<^sub>v w) * trace (outer_prod t (Mj *\<^sub>v w))"
    unfolding outer_prod_mult_outer_prod[OF t t Mw Mw] by (rule trace_smult[OF outer_prod_dim[OF t Mw]])
  also have "\<dots> = inner_prod t (Mj *\<^sub>v w) * inner_prod (Mj *\<^sub>v w) t" unfolding trace_outer_prod[OF t Mw] ..
  also have "\<dots> = complex_of_real ((cmod (inner_prod t (Mj *\<^sub>v w)))\<^sup>2)" by (rule inner_prod_abs_sq[OF t Mw])
  also have "inner_prod t (Mj *\<^sub>v w) = inner_prod (adjoint Mj *\<^sub>v t) w" by (rule adjoint_def_alter[OF t w Mc])
  finally show ?thesis unfolding e by simp
qed

theorem hoare_prog_overlap:
  assumes d0: "0 < d" and Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and M: "measurement d 2 M" and t: "t \<in> carrier_vec d"
    and M1t: "adjoint (M 1) *\<^sub>v t = t" and M0t: "adjoint (M 0) *\<^sub>v t = 0\<^sub>v d"
    and q: "q \<le> (cmod (inner_prod t (circuit_mat d Us *\<^sub>v unit_vec d 0)))\<^sup>2"
  shows "\<Turnstile>\<^sub>t {complex_of_real q \<cdot>\<^sub>m 1\<^sub>m d} prog_meas d M Us {outer_prod t t}"
  unfolding hoare_total_correct_def
proof
  let ?\<psi> = "circuit_mat d Us *\<^sub>v unit_vec d 0" and ?T = "outer_prod t t" and ?Me = "Measure 2 M [SKIP, SKIP]"
  have cc: "circuit_mat d Us \<in> carrier_mat d d" by (rule circuit_mat_carrier) (use Us in auto)
  have \<psi>c: "?\<psi> \<in> carrier_vec d" by (rule mult_mat_vec_carrier[OF cc unit_vec_carrier])
  have M0: "M 0 \<in> carrier_mat d d" and M1: "M 1 \<in> carrier_mat d d" by (rule measurement_dim[OF M], simp)+
  have wc: "well_com ?Me" using M by simp
  fix \<rho> assume r: "\<rho> \<in> density_states"
  have rc: "\<rho> \<in> carrier_mat d d" and pd: "partial_density_operator \<rho>" using r by (auto simp: density_states_def)
  have tr0: "0 \<le> trace \<rho>" using positive_trace[OF rc] pd unfolding partial_density_operator_def by simp
  define c where "c = Re (trace \<rho>)"
  have tr: "trace \<rho> = complex_of_real c" using tr0 unfolding c_def less_eq_complex_def by (simp add: complex_eq_iff)
  have c0: "0 \<le> c" using tr0 unfolding c_def less_eq_complex_def by simp
  let ?\<sigma> = "complex_of_real c \<cdot>\<^sub>m outer_prod ?\<psi> ?\<psi>"
  have \<sigma>c: "?\<sigma> \<in> carrier_mat d d" using outer_prod_dim[OF \<psi>c \<psi>c] by simp
  have B1: "M 1 * ?\<sigma> * adjoint (M 1) \<in> carrier_mat d d" and B0: "M 0 * ?\<sigma> * adjoint (M 0) \<in> carrier_mat d d"
    using M0 M1 \<sigma>c by (auto intro: mult_carrier_mat adjoint_dim)
  have "denote (prog_meas d M Us) \<rho> = denote ?Me (denote (init_com d ;; utrans_seq Us) \<rho>)"
    unfolding prog_meas_def by (rule denote.simps(3))
  also have "denote (init_com d ;; utrans_seq Us) \<rho> = trace \<rho> \<cdot>\<^sub>m outer_prod ?\<psi> ?\<psi>" by (rule denote_init_circuit[OF d0 Us rc])
  also have "trace \<rho> = complex_of_real c" by (rule tr)
  also have "denote ?Me ?\<sigma> = M 1 * ?\<sigma> * adjoint (M 1) + (M 0 * ?\<sigma> * adjoint (M 0) + 0\<^sub>m d d)"
    unfolding denote_measure_expand[OF le_refl wc] by (simp add: numeral_2_eq_2)
  also have "\<dots> = M 1 * ?\<sigma> * adjoint (M 1) + M 0 * ?\<sigma> * adjoint (M 0)" unfolding right_add_zero_mat[OF B0] ..
  finally have den: "denote (prog_meas d M Us) \<rho> = M 1 * ?\<sigma> * adjoint (M 1) + M 0 * ?\<sigma> * adjoint (M 0)" .
  have "trace (?T * denote (prog_meas d M Us) \<rho>)
        = trace (?T * (M 1 * ?\<sigma> * adjoint (M 1))) + trace (?T * (M 0 * ?\<sigma> * adjoint (M 0)))"
    unfolding den mult_add_distrib_mat[OF outer_prod_dim[OF t t] B1 B0]
    by (rule trace_add_linear[OF mult_carrier_mat[OF outer_prod_dim[OF t t] B1] mult_carrier_mat[OF outer_prod_dim[OF t t] B0]])
  also have "\<dots> = complex_of_real (c * (cmod (inner_prod t ?\<psi>))\<^sup>2)"
    unfolding trace_target_branch[OF t \<psi>c M1] trace_target_branch[OF t \<psi>c M0] M1t M0t inner_prod_zero_left[OF \<psi>c] by simp
  finally have val: "trace (?T * denote (prog_meas d M Us) \<rho>) = complex_of_real (c * (cmod (inner_prod t ?\<psi>))\<^sup>2)" .
  have pre: "trace (complex_of_real q \<cdot>\<^sub>m 1\<^sub>m d * \<rho>) = complex_of_real (q * c)"
    unfolding mult_smult_assoc_mat[OF one_carrier_mat rc] left_mult_one_mat[OF rc] trace_smult[OF rc] tr by simp
  have "q * c \<le> (cmod (inner_prod t ?\<psi>))\<^sup>2 * c" by (rule mult_right_mono[OF q c0])
  thus "trace (complex_of_real q \<cdot>\<^sub>m 1\<^sub>m d * \<rho>) \<le> trace (?T * denote (prog_meas d M Us) \<rho>)"
    unfolding val pre less_eq_complex_def by (simp add: Groups.mult.commute)
qed


lemma inner_prod_unit_vec_self: "0 < n \<Longrightarrow> inner_prod (unit_vec n 0 :: complex Matrix.vec) (unit_vec n 0) = 1"
proof -
  assume n: "0 < n"
  have "inner_prod (unit_vec n 0 :: complex Matrix.vec) (unit_vec n 0) = \<langle>unit_vec n 0|unit_vec n 0\<rangle>" by (rule inner_bridge) simp
  also have "\<dots> = complex_of_real (\<parallel>unit_vec n 0\<parallel>\<^sup>2)" by (rule cpx_vec_length_inner_prod[symmetric])
  also have "\<dots> = 1" using n by simp
  finally show ?thesis .
qed

lemma measurement_swap:
  assumes M: "measurement d 2 M"
  shows "measurement d 2 (\<lambda>j. M (1 - j))"
proof -
  have c: "\<And>j. j < 2 \<Longrightarrow> M j \<in> carrier_mat d d" using M unfolding measurement_def by simp
  have c0: "M 0 \<in> carrier_mat d d" and c1: "M 1 \<in> carrier_mat d d" by (rule c, simp)+
  have c': "adjoint (M 1) * M 1 \<in> carrier_mat d d" "adjoint (M 0) * M 0 \<in> carrier_mat d d"
    by (rule mult_carrier_mat[OF adjoint_dim[OF c1] c1], rule mult_carrier_mat[OF adjoint_dim[OF c0] c0])
  have "matrix_sum d (\<lambda>j. adjoint (M (1 - j)) * M (1 - j)) 2 = adjoint (M 0) * M 0 + (adjoint (M 1) * M 1 + 0\<^sub>m d d)"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = adjoint (M 1) * M 1 + (adjoint (M 0) * M 0 + 0\<^sub>m d d)"
    unfolding right_add_zero_mat[OF c'(1)] right_add_zero_mat[OF c'(2)] by (rule comm_add_mat[OF c'(2) c'(1)])
  also have "\<dots> = 1\<^sub>m d" using M unfolding measurement_def by (simp add: numeral_2_eq_2)
  finally show ?thesis unfolding measurement_def using c by auto
qed

text \<open>The two branch weights of a unit vector add up to one.\<close>

lemma measurement_weights:
  assumes M: "measurement d 2 M" and \<psi>: "\<psi> \<in> carrier_vec d" "inner_prod \<psi> \<psi> = 1"
  shows "inner_prod (M 0 *\<^sub>v \<psi>) (M 0 *\<^sub>v \<psi>) + inner_prod (M 1 *\<^sub>v \<psi>) (M 1 *\<^sub>v \<psi>) = 1"
proof -
  have M0: "M 0 \<in> carrier_mat d d" and M1: "M 1 \<in> carrier_mat d d" by (rule measurement_dim[OF M], simp)+
  have e: "inner_prod (Mj *\<^sub>v \<psi>) (Mj *\<^sub>v \<psi>) = inner_prod ((adjoint Mj * Mj) *\<^sub>v \<psi>) \<psi>" if Mj: "Mj \<in> carrier_mat d d" for Mj
    by (simp only: adjoint_def_alter[OF mult_mat_vec_carrier[OF Mj \<psi>(1)] \<psi>(1) Mj]
          assoc_mult_mat_vec[OF adjoint_dim[OF Mj] Mj \<psi>(1), symmetric])
  have c: "adjoint (M 1) * M 1 \<in> carrier_mat d d" "adjoint (M 0) * M 0 \<in> carrier_mat d d"
    using M0 M1 by (auto intro: mult_carrier_mat adjoint_dim)
  have s: "matrix_sum d (\<lambda>j. adjoint (M j) * M j) 2 = 1\<^sub>m d" using M unfolding measurement_def by simp
  have "adjoint (M 1) * M 1 + (adjoint (M 0) * M 0 + 0\<^sub>m d d) = 1\<^sub>m d" using s by (simp add: numeral_2_eq_2)
  hence s3: "adjoint (M 0) * M 0 + adjoint (M 1) * M 1 = 1\<^sub>m d"
    unfolding right_add_zero_mat[OF c(2)] comm_add_mat[OF c(1) c(2)] .
  have sum: "(adjoint (M 0) * M 0) *\<^sub>v \<psi> + (adjoint (M 1) * M 1) *\<^sub>v \<psi> = \<psi>"
    using arg_cong[OF s3, of "\<lambda>X. X *\<^sub>v \<psi>"]
    unfolding add_mult_distrib_mat_vec[OF c(2) c(1) \<psi>(1)] one_mult_mat_vec[OF \<psi>(1)] .
  have P0: "(adjoint (M 0) * M 0) *\<^sub>v \<psi> \<in> carrier_vec d" by (rule mult_mat_vec_carrier[OF c(2) \<psi>(1)])
  have P1: "(adjoint (M 1) * M 1) *\<^sub>v \<psi> \<in> carrier_vec d" by (rule mult_mat_vec_carrier[OF c(1) \<psi>(1)])
  show ?thesis unfolding e[OF M0] e[OF M1] inner_prod_distrib_left[OF \<psi>(1) P0 P1, symmetric] sum \<psi>(2) ..
qed

text \<open>Repeat until the second outcome: the output carries $\ket t\bra t$ with weight
$|\langle t|\psi\rangle|^2/p$, where $p$ is the probability of that outcome.\<close>

theorem hoare_rus_overlap:
  assumes d0: "0 < d" and Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and M: "measurement d 2 M" and t: "t \<in> carrier_vec d" "inner_prod t t = 1"
    and M1t: "adjoint (M 1) *\<^sub>v t = t" and M0t: "adjoint (M 0) *\<^sub>v t = 0\<^sub>v d"
  defines "\<psi> \<equiv> circuit_mat d Us *\<^sub>v unit_vec d 0"
  assumes p0: "0 < Re (inner_prod (M 1 *\<^sub>v \<psi>) (M 1 *\<^sub>v \<psi>))"
  shows "\<Turnstile>\<^sub>t {complex_of_real ((cmod (inner_prod t \<psi>))\<^sup>2 / Re (inner_prod (M 1 *\<^sub>v \<psi>) (M 1 *\<^sub>v \<psi>))) \<cdot>\<^sub>m 1\<^sub>m d}
           rus_meas d M Us {outer_prod t t}"
  unfolding hoare_total_correct_def
proof
  let ?T = "outer_prod t t" and ?M = "\<lambda>j. M (1 - j)" and ?Sc = "init_com d ;; utrans_seq Us" and ?\<sigma> = "outer_prod \<psi> \<psi>"
  let ?v = "(cmod (inner_prod t \<psi>))\<^sup>2"
  define p where "p = Re (inner_prod (M 1 *\<^sub>v \<psi>) (M 1 *\<^sub>v \<psi>))"
  have p0: "0 < p" using p0 unfolding p_def .
  have cc: "circuit_mat d Us \<in> carrier_mat d d" by (rule circuit_mat_carrier) (use Us in auto)
  have cu: "Complex_Matrix.unitary (circuit_mat d Us)" by (rule circuit_mat_unitary[OF Us])
  have \<psi>c: "\<psi> \<in> carrier_vec d" unfolding \<psi>_def by (rule mult_mat_vec_carrier[OF cc unit_vec_carrier])
  have \<psi>1: "inner_prod \<psi> \<psi> = 1" unfolding \<psi>_def
    using unitary_inner_keep[OF cc cu, of "unit_vec d 0"] inner_prod_unit_vec_self[OF d0] by simp
  have M0: "M 0 \<in> carrier_mat d d" and M1: "M 1 \<in> carrier_mat d d" by (rule measurement_dim[OF M], simp)+
  have M': "measurement d 2 ?M" by (rule measurement_swap[OF M])
  have Sc: "well_com ?Sc" using well_com_init[OF d0] well_com_utrans_seq[OF Us] by simp
  have \<sigma>c: "?\<sigma> \<in> carrier_mat d d" by (rule outer_prod_dim[OF \<psi>c \<psi>c])
  have \<sigma>t: "trace ?\<sigma> = 1" unfolding trace_outer_prod[OF \<psi>c \<psi>c] \<psi>1 ..
  have \<sigma>p: "partial_density_operator ?\<sigma>"
    unfolding partial_density_operator_def \<sigma>t using positive_same_outer_prod[OF \<psi>c] by simp
  have reset: "\<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> denote ?Sc \<rho> = trace \<rho> \<cdot>\<^sub>m ?\<sigma>" for \<rho>
    unfolding \<psi>_def by (rule denote_init_circuit[OF d0 Us])
  have ge: "0 \<le> inner_prod (Mj *\<^sub>v \<psi>) (Mj *\<^sub>v \<psi>)" if Mj: "Mj \<in> carrier_mat d d" for Mj
  proof -
    have w: "Mj *\<^sub>v \<psi> \<in> carrier_vec d" by (rule mult_mat_vec_carrier[OF Mj \<psi>c])
    show ?thesis using positive_trace[OF outer_prod_dim[OF w w] positive_same_outer_prod[OF w]] unfolding trace_outer_prod[OF w w] .
  qed
  have w1: "inner_prod (M 1 *\<^sub>v \<psi>) (M 1 *\<^sub>v \<psi>) = complex_of_real p"
    using ge[OF M1] unfolding p_def less_eq_complex_def by (simp add: complex_eq_iff)
  have w0: "inner_prod (M 0 *\<^sub>v \<psi>) (M 0 *\<^sub>v \<psi>) = complex_of_real (1 - p)"
    using measurement_weights[OF M \<psi>c \<psi>1] unfolding w1 by (simp add: algebra_simps)
  have ple: "p \<le> 1" using ge[OF M0] unfolding w0 less_eq_complex_def by simp
  have p1: "trace (?M 1 * ?\<sigma> * adjoint (?M 1)) = complex_of_real (1 - p)"
  proof -
    have e0: "?M 1 * ?\<sigma> * adjoint (?M 1) = outer_prod (M 0 *\<^sub>v \<psi>) (M 0 *\<^sub>v \<psi>)"
      by (simp only: diff_self_eq_0 outer_prod_left_right_mat[OF \<psi>c \<psi>c M0 adjoint_dim[OF M0]] adjoint_adjoint)
    show ?thesis unfolding e0 trace_outer_prod[OF mult_mat_vec_carrier[OF M0 \<psi>c] mult_mat_vec_carrier[OF M0 \<psi>c]] w0 ..
  qed
  have v: "trace (?T * (?M 0 * ?\<sigma> * adjoint (?M 0))) = complex_of_real ?v"
  proof -
    have one: "complex_of_real 1 \<cdot>\<^sub>m ?\<sigma> = ?\<sigma>" by (rule eq_matI) auto
    have m0: "?M 0 = M 1" by simp
    have "trace (?T * (?M 0 * ?\<sigma> * adjoint (?M 0))) = trace (?T * (M 1 * (complex_of_real 1 \<cdot>\<^sub>m ?\<sigma>) * adjoint (M 1)))"
      unfolding m0 one ..
    also have "\<dots> = complex_of_real (1 * (cmod (inner_prod (adjoint (M 1) *\<^sub>v t) \<psi>))\<^sup>2)"
      by (rule trace_target_branch[OF t(1) \<psi>c M1])
    finally show ?thesis unfolding M1t by simp
  qed
  have Q: "is_quantum_predicate ?T" by (rule qp_pure) (use t in auto)
  fix \<rho> assume r: "\<rho> \<in> density_states"
  have rc: "\<rho> \<in> carrier_mat d d" and pd: "partial_density_operator \<rho>" using r by (auto simp: density_states_def)
  have tr0: "0 \<le> trace \<rho>" using positive_trace[OF rc] pd unfolding partial_density_operator_def by simp
  have tr1: "trace \<rho> \<le> 1" using pd unfolding partial_density_operator_def by simp
  define c where "c = Re (trace \<rho>)"
  have tr: "trace \<rho> = complex_of_real c" using tr0 unfolding c_def less_eq_complex_def by (simp add: complex_eq_iff)
  have c: "0 \<le> c" "c \<le> 1" using tr0 tr1 unfolding c_def less_eq_complex_def by simp_all
  have "denote (rus_meas d M Us) \<rho> = denote (While ?M ?Sc) (denote ?Sc \<rho>)" unfolding rus_meas_def by (rule denote.simps(3))
  also have "denote ?Sc \<rho> = trace \<rho> \<cdot>\<^sub>m ?\<sigma>" by (rule reset[OF rc pd])
  also have "trace \<rho> = complex_of_real c" by (rule tr)
  finally have e: "denote (rus_meas d M Us) \<rho> = denote (While ?M ?Sc) (complex_of_real c \<cdot>\<^sub>m ?\<sigma>)" .
  have "complex_of_real (c * ?v / p) \<le> trace (?T * denote (While ?M ?Sc) (complex_of_real c \<cdot>\<^sub>m ?\<sigma>))"
    by (rule while_reset_total[OF M' Sc \<sigma>c \<sigma>p \<sigma>t reset p1 p0 ple Q v c])
  moreover have "trace (complex_of_real (?v / p) \<cdot>\<^sub>m 1\<^sub>m d * \<rho>) = complex_of_real (c * ?v / p)"
    unfolding mult_smult_assoc_mat[OF one_carrier_mat rc] left_mult_one_mat[OF rc] trace_smult[OF rc] tr by simp
  ultimately show "trace (complex_of_real (?v / Re (inner_prod (M 1 *\<^sub>v \<psi>) (M 1 *\<^sub>v \<psi>))) \<cdot>\<^sub>m 1\<^sub>m d * \<rho>)
                   \<le> trace (?T * denote (rus_meas d M Us) \<rho>)"
    unfolding p_def[symmetric] e by simp
qed

end


subsection \<open>From closeness of the post-selected state to fidelity\<close>

lemma fidelity_from_close:
  assumes t: "dim_vec t = K" "\<parallel>t\<parallel> = 1" and y: "dim_vec y = K" "0 < \<parallel>y\<parallel>"
    and D: "\<parallel>complex_of_real (1 / \<parallel>y\<parallel>) \<cdot>\<^sub>v y - t\<parallel> \<le> e"
  shows "\<parallel>y\<parallel>\<^sup>2 * (1 - e\<^sup>2) \<le> (cmod \<langle>t|y\<rangle>)\<^sup>2"
proof -
  let ?h = "complex_of_real (1 / \<parallel>y\<parallel>) \<cdot>\<^sub>v y"
  have hd: "dim_vec ?h = K" using y by simp
  have hn: "\<parallel>?h\<parallel> = 1" unfolding cpx_vec_length_smult norm_of_real using y(2) by simp
  have ud: "\<parallel>?h - t\<parallel> = sqrt (2 * (1 - Re \<langle>?h|t\<rangle>))" by (rule unit_dist[OF hd hn t])
  have e0: "0 \<le> e" using D vnorm_ge0[of "?h - t"] by linarith
  have x: "2 * (1 - Re \<langle>?h|t\<rangle>) \<le> e\<^sup>2"
  proof (cases "0 \<le> 2 * (1 - Re \<langle>?h|t\<rangle>)")
    case True
    have "sqrt (2 * (1 - Re \<langle>?h|t\<rangle>)) \<le> e" using D ud by simp
    hence "(sqrt (2 * (1 - Re \<langle>?h|t\<rangle>)))\<^sup>2 \<le> e\<^sup>2" by (rule power_mono) (rule real_sqrt_ge_zero[OF True])
    thus ?thesis using True by simp
  qed (use e0 in \<open>auto intro: order_trans[OF _ zero_le_power2]\<close>)
  have cj: "\<langle>t|?h\<rangle> = cnj \<langle>?h|t\<rangle>" using inner_prod_cnj[of ?h t] hd t(1) by simp
  have r: "1 - e\<^sup>2 / 2 \<le> Re \<langle>t|?h\<rangle>" using x unfolding cj by simp
  have th: "\<langle>t|?h\<rangle> = complex_of_real (1 / \<parallel>y\<parallel>) * \<langle>t|y\<rangle>" by (rule inner_prod_right_smult')
  have cm: "cmod \<langle>t|y\<rangle> = \<parallel>y\<parallel> * cmod \<langle>t|?h\<rangle>" unfolding th norm_mult norm_of_real using y(2) by simp
  have f: "1 - e\<^sup>2 \<le> (cmod \<langle>t|?h\<rangle>)\<^sup>2"
  proof (cases "0 \<le> 1 - e\<^sup>2 / 2")
    case True
    have "(1 - e\<^sup>2 / 2)\<^sup>2 \<le> (Re \<langle>t|?h\<rangle>)\<^sup>2" by (rule power_mono[OF r True])
    also have "\<dots> = \<bar>Re \<langle>t|?h\<rangle>\<bar>\<^sup>2" by simp
    also have "\<dots> \<le> (cmod \<langle>t|?h\<rangle>)\<^sup>2" by (rule power_mono[OF abs_Re_le_cmod]) simp
    finally have "(1 - e\<^sup>2 / 2)\<^sup>2 \<le> (cmod \<langle>t|?h\<rangle>)\<^sup>2" .
    moreover have "1 - e\<^sup>2 \<le> (1 - e\<^sup>2 / 2)\<^sup>2"
    proof -
      have "(1 - e\<^sup>2 / 2)\<^sup>2 = 1 - e\<^sup>2 + (e\<^sup>2 / 2)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
      thus ?thesis using zero_le_power2[of "e\<^sup>2 / 2"] by linarith
    qed
    ultimately show ?thesis by linarith
  next
    case False
    hence "1 - e\<^sup>2 \<le> 0" by simp
    thus ?thesis using zero_le_power2[of "cmod \<langle>t|?h\<rangle>"] by linarith
  qed
  have "\<parallel>y\<parallel>\<^sup>2 * (1 - e\<^sup>2) \<le> \<parallel>y\<parallel>\<^sup>2 * (cmod \<langle>t|?h\<rangle>)\<^sup>2" by (rule mult_left_mono[OF f]) simp
  thus ?thesis unfolding cm by (simp add: power_mult_distrib)
qed

lemma post1_anc_proj: "dim_vec v = K \<Longrightarrow> post1 v = anc_proj K 1 *\<^sub>v v"
  by (rule pflag_mat_mult[symmetric])

lemma inner_anc_post1:
  assumes t: "t \<in> carrier_vec K" "anc_proj K 1 *\<^sub>v t = t" and v: "v \<in> carrier_vec K"
  shows "Complex_Matrix.inner_prod t (post1 v) = Complex_Matrix.inner_prod t v"
proof -
  have "Complex_Matrix.inner_prod t (anc_proj K 1 *\<^sub>v v) = Complex_Matrix.inner_prod (adjoint (anc_proj K 1) *\<^sub>v t) v"
    by (rule adjoint_def_alter[OF t(1) v proj_set_carrier])
  thus ?thesis unfolding post1_anc_proj[OF carrier_vecD[OF v]] proj_set_adjoint t(2) .
qed

subsection \<open>HHL in the paper's regime as a program\<close>

text \<open>The circuit of \<open>hhl_complete\<close>: window-state clock register, eigenvalues anywhere in the
spectral window (not only on the grid), an $\eta$-accurate evolution oracle $V$, filtered rotation.
Run as a QHLProver program, measured on the ancilla; the target is
$\ket t = \ket{\Psi_0}\otimes\hat x\otimes\ket1$.\<close>

context
  fixes A V Prep :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n N :: nat and t0 C \<theta> lmin \<epsilon> \<eta> :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real N"
      and V: "V \<in> carrier_mat n n" "Quantum.unitary V" and Vc: "op_close n \<eta> V (evolution A t0)" and eta: "0 \<le> \<eta>"
      and Prep: "Prep \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" "Quantum.unitary Prep"
        "Prep *\<^sub>v unit_vec (N * (n * 2)) 0 = tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0))"
      and small: "\<epsilon> + 2 * real (N - 1) * \<eta> \<le> C * t0 / pi"
begin

abbreviation (input) "apx_K \<equiv> N * (n * 2)"
abbreviation (input) "apx_O \<equiv> V \<Otimes> 1\<^sub>m 2"
abbreviation (input) "apx_x \<equiv> herm_inv A *\<^sub>v b"
abbreviation (input) "apx_t \<equiv> tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>apx_x\<parallel>) \<cdot>\<^sub>v apx_x) (unit_vec 2 1))"
abbreviation (input) "apx_e \<equiv> 2 * (\<epsilon> + 2 * real (N - 1) * \<eta>) / (C * \<parallel>apx_x\<parallel>)"
abbreviation (input) "apx_out c \<equiv> sem N (n * 2) apx_O c *\<^sub>v unit_vec apx_K 0"

lemma apx_basics:
  shows "0 < apx_K" "apx_O \<in> carrier_mat (n * 2) (n * 2)" "Quantum.unitary apx_O"
    and "gates_ok apx_K (hhl_full_prog A t0 N C Prep)"
    and "0 < \<parallel>apx_x\<parallel>" "apx_t \<in> carrier_vec apx_K" "\<parallel>apx_t\<parallel> = 1"
    and "anc_proj apx_K 1 *\<^sub>v apx_t = apx_t" "anc_proj apx_K 0 *\<^sub>v apx_t = 0\<^sub>v apx_K"
proof -
  have N0: "0 < N" using N by simp
  have nA: "dim_row A = n" using A(1) by simp
  have n0: "n \<noteq> 0"
  proof
    assume "n = 0"
    hence "\<parallel>b\<parallel> = 0" using b(1) by (simp add: cpx_vec_length_def)
    thus False using b(2) by simp
  qed
  show "0 < apx_K" using N0 n0 by simp
  show O: "apx_O \<in> carrier_mat (n * 2) (n * 2)" "Quantum.unitary apx_O" using V by (auto intro!: carrier_matI tensor_mat_unitary_one_right)
  show "gates_ok apx_K (hhl_full_prog A t0 N C Prep)"
    using gates_ok_pe_prog[OF N0, of "n * 2"] gates_ok_adj[OF gates_ok_pe_prog[OF N0, of "n * 2"]] hhl_rot_stage_ok[of A t0 N C] Prep(1,2)
    unfolding hhl_full_prog_def HHL_Simulation.hhl_prog_def nA by simp
  have z: "0 \<notin> herm_spectrum A"
  proof
    assume "0 \<in> herm_spectrum A"
    hence "lmin \<le> 0" using spec by blast
    moreover have "0 < 2 * C / \<theta>" using C th by simp
    ultimately show False using lmin by linarith
  qed
  have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
  show xp: "0 < \<parallel>apx_x\<parallel>" by (rule herm_inv_sol_pos[OF A z b])
  have Hr: "dim_row (herm_inv A) = n" using Hc by simp
  have dx: "dim_vec (complex_of_real (1 / \<parallel>apx_x\<parallel>) \<cdot>\<^sub>v apx_x) = n" using Hc by simp
  show tc: "apx_t \<in> carrier_vec apx_K" by (rule carrier_vecI) (simp add: tensor_vec_dim dx Hr)
  show "\<parallel>apx_t\<parallel> = 1" using win_state_norm[OF N] xp dx Hr by (simp add: vnorm_tensor tensor_vec_dim cpx_vec_length_smult norm_divide)
  show "anc_proj apx_K 1 *\<^sub>v apx_t = apx_t" using anc_proj_tensor[of "win_state N" N _ n 1 1] dx Hr by simp
  show "anc_proj apx_K 0 *\<^sub>v apx_t = 0\<^sub>v apx_K" using anc_proj_tensor[of "win_state N" N _ n 1 0] dx Hr by simp
qed

text \<open>The fidelity of any run whose post-selected state satisfies the \<open>hhl_complete\<close> bound.\<close>

lemma apx_fidelity:
  assumes g: "gates_ok apx_K c" and y0: "0 < \<parallel>post1 (apx_out c)\<parallel>"
    and D: "\<parallel>complex_of_real (1 / \<parallel>post1 (apx_out c)\<parallel>) \<cdot>\<^sub>v post1 (apx_out c) - apx_t\<parallel> \<le> apx_e"
  shows "\<parallel>post1 (apx_out c)\<parallel>\<^sup>2 * (1 - apx_e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2"
proof -
  note ab = apx_basics
  have Sc: "sem N (n * 2) apx_O c \<in> carrier_mat apx_K apx_K" by (rule sem_carrier[OF ab(2,3) g])
  have oc: "apx_out c \<in> carrier_vec apx_K" by (rule mult_mat_vec_carrier[OF Sc unit_vec_carrier])
  have \<psi>: "circuit_mat apx_K (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec apx_K 0 = apx_out c" unfolding qgates_sem[OF ab(2,3) g] ..
  have "Complex_Matrix.inner_prod apx_t (apx_out c) = Complex_Matrix.inner_prod apx_t (post1 (apx_out c))"
    by (rule inner_anc_post1[symmetric, OF ab(6,8) oc])
  also have "\<dots> = \<langle>apx_t|post1 (apx_out c)\<rangle>" by (rule inner_bridge) (use carrier_vecD[OF ab(6)] carrier_vecD[OF oc] in simp)
  finally have i: "Complex_Matrix.inner_prod apx_t (apx_out c) = \<langle>apx_t|post1 (apx_out c)\<rangle>" .
  show ?thesis unfolding \<psi> i
    by (rule fidelity_from_close[OF _ ab(7) _ y0 D]) (use carrier_vecD[OF ab(6)] carrier_vecD[OF oc] in simp_all)
qed

lemma apx_triples:
  assumes g: "gates_ok apx_K c"
  shows "q \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2 \<Longrightarrow>
         state_sig.hoare_total_correct [N, n, 2] (complex_of_real q \<cdot>\<^sub>m 1\<^sub>m apx_K)
           (prog_meas apx_K (anc_proj apx_K) (qgates N (n * 2) apx_O c)) (outer_prod apx_t apx_t)"
    and "0 < \<parallel>post1 (apx_out c)\<parallel> \<Longrightarrow>
         state_sig.hoare_total_correct [N, n, 2]
           (complex_of_real ((cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2
              / \<parallel>post1 (apx_out c)\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m apx_K)
           (rus_meas apx_K (anc_proj apx_K) (qgates N (n * 2) apx_O c)) (outer_prod apx_t apx_t)"
proof -
  interpret state_sig "[N, n, 2]" .
  note ab = apx_basics
  have dd: "d = apx_K" by (simp add: d_def)
  have d0: "0 < d" using ab(1) dd by simp
  have Us: "\<And>U. U \<in> set (qgates N (n * 2) apx_O c) \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    using qgates_ok[OF ab(2,3) g] dd by simp
  have Mm: "measurement d 2 (anc_proj d)" by (rule anc_proj_measurement)
  have tc: "apx_t \<in> carrier_vec d" using ab(6) dd by simp
  have t1: "Complex_Matrix.inner_prod apx_t apx_t = 1"
    using inner_bridge[of apx_t apx_t] ab(7) cpx_vec_length_inner_prod[of apx_t] by simp
  have m1: "adjoint (anc_proj d 1) *\<^sub>v apx_t = apx_t" unfolding proj_set_adjoint dd by (rule ab(8))
  have m0: "adjoint (anc_proj d 0) *\<^sub>v apx_t = 0\<^sub>v d" unfolding proj_set_adjoint dd by (rule ab(9))
  have \<psi>: "circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0 = apx_out c" unfolding dd qgates_sem[OF ab(2,3) g] ..
  have Sc: "sem N (n * 2) apx_O c \<in> carrier_mat apx_K apx_K" by (rule sem_carrier[OF ab(2,3) g])
  have oc: "apx_out c \<in> carrier_vec apx_K" by (rule mult_mat_vec_carrier[OF Sc unit_vec_carrier])
  show "hoare_total_correct (complex_of_real q \<cdot>\<^sub>m 1\<^sub>m apx_K) (prog_meas apx_K (anc_proj apx_K) (qgates N (n * 2) apx_O c)) (outer_prod apx_t apx_t)"
    if q: "q \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2"
  proof -
    have q': "q \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0)))\<^sup>2"
      unfolding dd by (rule q)
    show ?thesis unfolding dd[symmetric] by (rule hoare_prog_overlap[where Us = "qgates N (n * 2) apx_O c", OF d0 Us Mm tc m1 m0 q'])
  qed
  show "hoare_total_correct
           (complex_of_real ((cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2
              / \<parallel>post1 (apx_out c)\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m apx_K)
           (rus_meas apx_K (anc_proj apx_K) (qgates N (n * 2) apx_O c)) (outer_prod apx_t apx_t)"
    if y0: "0 < \<parallel>post1 (apx_out c)\<parallel>"
  proof -
    have pe: "Complex_Matrix.inner_prod (anc_proj d 1 *\<^sub>v apx_out c) (anc_proj d 1 *\<^sub>v apx_out c) = complex_of_real (\<parallel>post1 (apx_out c)\<parallel>\<^sup>2)"
    proof -
      have "anc_proj d 1 *\<^sub>v apx_out c = post1 (apx_out c)" unfolding dd by (rule post1_anc_proj[symmetric, OF carrier_vecD[OF oc]])
      moreover have "Complex_Matrix.inner_prod (post1 (apx_out c)) (post1 (apx_out c)) = \<langle>post1 (apx_out c)|post1 (apx_out c)\<rangle>"
        by (rule inner_bridge) simp
      ultimately show ?thesis using cpx_vec_length_inner_prod[of "post1 (apx_out c)"] by simp
    qed
    have p0: "0 < Re (Complex_Matrix.inner_prod (anc_proj d 1 *\<^sub>v (circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0))
                     (anc_proj d 1 *\<^sub>v (circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0)))"
      unfolding \<psi> pe using y0 by simp
    have h: "hoare_total_correct (complex_of_real ((cmod (Complex_Matrix.inner_prod apx_t (circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0)))\<^sup>2
               / Re (Complex_Matrix.inner_prod (anc_proj d 1 *\<^sub>v (circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0))
                     (anc_proj d 1 *\<^sub>v (circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0)))) \<cdot>\<^sub>m 1\<^sub>m d)
             (rus_meas d (anc_proj d) (qgates N (n * 2) apx_O c)) (outer_prod apx_t apx_t)"
      by (rule hoare_rus_overlap[where Us = "qgates N (n * 2) apx_O c", OF d0 Us Mm tc t1 m1 m0 p0])
    have pr: "Re (Complex_Matrix.inner_prod (anc_proj d 1 *\<^sub>v (circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0))
                     (anc_proj d 1 *\<^sub>v (circuit_mat d (qgates N (n * 2) apx_O c) *\<^sub>v unit_vec d 0))) = \<parallel>post1 (apx_out c)\<parallel>\<^sup>2"
      unfolding \<psi> pe by simp
    show ?thesis using h unfolding dd pr[unfolded dd] .
  qed
qed

theorem hhl_apx_program:
  "state_sig.hoare_total_correct [N, n, 2] (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - apx_e\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m apx_K)
     (prog_meas apx_K (anc_proj apx_K) (qgates N (n * 2) apx_O (hhl_full_prog A t0 N C Prep))) (outer_prod apx_t apx_t)"
proof -
  note ab = apx_basics
  let ?c = "hhl_full_prog A t0 N C Prep" and ?y = "post1 (apx_out (hhl_full_prog A t0 N C Prep))"
  note hc = hhl_complete[OF A t0 N C th lmin spec b e NQ V Vc eta Prep small]
  have y1: "C * t0 / pi \<le> \<parallel>?y\<parallel>" by (rule hc(1))
  have y0: "0 < \<parallel>?y\<parallel>" using y1 C t0 by (smt (verit) divide_pos_pos mult_pos_pos pi_gt_zero)
  have F: "\<parallel>?y\<parallel>\<^sup>2 * (1 - apx_e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O ?c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2"
    by (rule apx_fidelity[OF ab(4) y0 hc(2)])
  show ?thesis
  proof (rule apx_triples(1)[OF ab(4)], cases "0 \<le> 1 - apx_e\<^sup>2")
    case True
    have "(C * t0 / pi)\<^sup>2 \<le> \<parallel>?y\<parallel>\<^sup>2" by (rule power_mono[OF y1]) (use C t0 in simp)
    hence "(C * t0 / pi)\<^sup>2 * (1 - apx_e\<^sup>2) \<le> \<parallel>?y\<parallel>\<^sup>2 * (1 - apx_e\<^sup>2)" by (rule mult_right_mono[OF _ True])
    thus "(C * t0 / pi)\<^sup>2 * (1 - apx_e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O ?c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2"
      using F by linarith
  next
    case False
    hence "(C * t0 / pi)\<^sup>2 * (1 - apx_e\<^sup>2) \<le> 0" by (simp add: mult_nonneg_nonpos)
    thus "(C * t0 / pi)\<^sup>2 * (1 - apx_e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O ?c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2"
      using zero_le_power2 by (rule order_trans)
  qed
qed

text \<open>Repeat until the ancilla reads 1: the loop terminates, and its output has fidelity at least
$1-e^2$ with the target, where $e$ is the \<open>hhl_complete\<close> error bound.\<close>

theorem hhl_apx_rus:
  "state_sig.hoare_total_correct [N, n, 2] (complex_of_real (1 - apx_e\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m apx_K)
     (rus_meas apx_K (anc_proj apx_K) (qgates N (n * 2) apx_O (hhl_full_prog A t0 N C Prep))) (outer_prod apx_t apx_t)"
proof -
  interpret state_sig "[N, n, 2]" .
  note ab = apx_basics
  have dd: "d = apx_K" by (simp add: d_def)
  let ?c = "hhl_full_prog A t0 N C Prep" and ?y = "post1 (apx_out (hhl_full_prog A t0 N C Prep))"
  note hc = hhl_complete[OF A t0 N C th lmin spec b e NQ V Vc eta Prep small]
  have y0: "0 < \<parallel>?y\<parallel>" using hc(1) C t0 by (smt (verit) divide_pos_pos mult_pos_pos pi_gt_zero)
  have F: "\<parallel>?y\<parallel>\<^sup>2 * (1 - apx_e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O ?c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2"
    by (rule apx_fidelity[OF ab(4) y0 hc(2)])
  have le: "1 - apx_e\<^sup>2 \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O ?c) *\<^sub>v unit_vec apx_K 0)))\<^sup>2 / \<parallel>?y\<parallel>\<^sup>2"
    using F y0 by (simp add: field_simps)
  show ?thesis using total_scalar_weaken[OF apx_triples(2)[OF ab(4) y0, folded dd] le[folded dd]] unfolding dd .
qed

text \<open>Amplitude amplification as a program: after $k\le\pi^2/(4Ct_0)$ rounds, with
$(2k+1)\cdot2(N-1)$ oracle calls, the ancilla reads 1 with probability at least $1-p$ (where $p$
is the single-run success probability), and the post-selected state is unchanged.\<close>

theorem hhl_apx_amplified:
  assumes y1: "\<parallel>post1 (apx_out (hhl_full_prog A t0 N C Prep))\<parallel> < 1"
  obtains k where "calls (aa_prog apx_K 2 (\<lambda>c. c = 1) (hhl_full_prog A t0 N C Prep) k) = (2 * k + 1) * (2 * (N - 1))"
    and "real k \<le> pi\<^sup>2 / (4 * C * t0)"
    and "state_sig.hoare_total_correct [N, n, 2]
           (complex_of_real ((1 - \<parallel>post1 (apx_out (hhl_full_prog A t0 N C Prep))\<parallel>\<^sup>2) * (1 - apx_e\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m apx_K)
           (prog_meas apx_K (anc_proj apx_K) (qgates N (n * 2) apx_O (aa_prog apx_K 2 (\<lambda>c. c = 1) (hhl_full_prog A t0 N C Prep) k)))
           (outer_prod apx_t apx_t)"
proof -
  note ab = apx_basics
  let ?c = "hhl_full_prog A t0 N C Prep" and ?y = "post1 (apx_out (hhl_full_prog A t0 N C Prep))"
  note hc = hhl_complete[OF A t0 N C th lmin spec b e NQ V Vc eta Prep small]
  obtain k where k1: "1 - \<parallel>?y\<parallel>\<^sup>2 \<le> \<parallel>post1 (apx_out (aa_prog apx_K 2 (\<lambda>c. c = 1) ?c k))\<parallel>\<^sup>2"
    and k2: "complex_of_real (1 / \<parallel>post1 (apx_out (aa_prog apx_K 2 (\<lambda>c. c = 1) ?c k))\<parallel>) \<cdot>\<^sub>v post1 (apx_out (aa_prog apx_K 2 (\<lambda>c. c = 1) ?c k))
             = complex_of_real (1 / \<parallel>?y\<parallel>) \<cdot>\<^sub>v ?y"
    and k3: "calls (aa_prog apx_K 2 (\<lambda>c. c = 1) ?c k) = (2 * k + 1) * (2 * (N - 1))" and k4: "real k \<le> pi\<^sup>2 / (4 * C * t0)"
    using hc(3)[OF _ y1] by blast
  let ?z = "post1 (apx_out (aa_prog apx_K 2 (\<lambda>c. c = 1) ?c k))"
  have g: "gates_ok apx_K (aa_prog apx_K 2 (\<lambda>c. c = 1) ?c k)" by (rule gates_ok_aa_prog[OF ab(4)])
  have "0 < 1 - \<parallel>?y\<parallel>\<^sup>2" using y1 vnorm_ge0[of ?y] by (simp add: power_less_one_iff abs_square_less_1)
  hence z0: "0 < \<parallel>?z\<parallel>" using k1 by (smt (verit) power2_eq_square vnorm_ge0 mult_nonneg_nonneg zero_less_mult_iff)
  have D: "\<parallel>complex_of_real (1 / \<parallel>?z\<parallel>) \<cdot>\<^sub>v ?z - apx_t\<parallel> \<le> apx_e" unfolding k2 by (rule hc(2))
  have F: "\<parallel>?z\<parallel>\<^sup>2 * (1 - apx_e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O (aa_prog apx_K 2 (\<lambda>c. c = 1) ?c k)) *\<^sub>v unit_vec apx_K 0)))\<^sup>2"
    by (rule apx_fidelity[OF g z0 D])
  have q: "(1 - \<parallel>?y\<parallel>\<^sup>2) * (1 - apx_e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod apx_t (circuit_mat apx_K (qgates N (n * 2) apx_O (aa_prog apx_K 2 (\<lambda>c. c = 1) ?c k)) *\<^sub>v unit_vec apx_K 0)))\<^sup>2"
  proof (cases "0 \<le> 1 - apx_e\<^sup>2")
    case True
    thus ?thesis using F mult_right_mono[OF k1 True] by linarith
  next
    case False
    have "0 \<le> 1 - \<parallel>?y\<parallel>\<^sup>2" using y1 vnorm_ge0[of ?y] by (simp add: abs_square_le_1)
    hence "(1 - \<parallel>?y\<parallel>\<^sup>2) * (1 - apx_e\<^sup>2) \<le> 0" using False by (simp add: mult_nonneg_nonpos)
    thus ?thesis using zero_le_power2 by (rule order_trans)
  qed
  show ?thesis by (rule that[OF k3 k4 apx_triples(1)[OF g q]])
qed

end


subsection \<open>The filtered algorithm of the HHL paper as a program\<close>

text \<open>Measurement of a flag register of $d$ levels: outcome 1 when the flag satisfies $P$.\<close>

definition flag_meas :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "flag_meas K dd P j = pflag_mat K dd (\<lambda>c. P c = (j = 1))"

lemma flag_meas_measurement: "measurement K 2 (flag_meas K dd P)"
proof -
  have "matrix_sum K (\<lambda>j. adjoint (flag_meas K dd P j) * flag_meas K dd P j) 2
        = pflag_mat K dd P + (pflag_mat K dd (\<lambda>c. \<not> P c) + 0\<^sub>m K K)"
    by (simp add: numeral_2_eq_2 flag_meas_def proj_set_adjoint proj_set_idem)
  also have "\<dots> = 1\<^sub>m K" by (rule eq_matI) (auto simp: proj_set_def mat_diag_def)
  finally show ?thesis unfolding measurement_def by (simp add: flag_meas_def)
qed

lemma tensor_zero_right: "0 < m \<Longrightarrow> tensor_vec u (0\<^sub>v m :: complex Matrix.vec) = 0\<^sub>v (dim_vec u * m)"
proof (rule eq_vecI)
  assume m: "0 < m"
  have d: "dim_vec (tensor_vec u (0\<^sub>v m :: complex Matrix.vec)) = dim_vec u * m" by (rule tensor_vec_dim) simp_all
  show "dim_vec (tensor_vec u (0\<^sub>v m :: complex Matrix.vec)) = dim_vec (0\<^sub>v (dim_vec u * m) :: complex Matrix.vec)" using d by simp
  fix i assume "i < dim_vec (0\<^sub>v (dim_vec u * m) :: complex Matrix.vec)"
  hence i: "i < dim_vec u * m" by simp
  have "i mod m < m" using m by simp
  thus "tensor_vec u (0\<^sub>v m) $ i = 0\<^sub>v (dim_vec u * m) $ i" using tensor_vec_index[OF refl _ i, of "0\<^sub>v m"] i by simp
qed

lemma pflag_unit3: "pflag 3 P (unit_vec 3 1) = (if P 1 then unit_vec 3 1 else 0\<^sub>v 3)"
  by (rule eq_vecI) (auto simp: pflag_def unit_vec_def)

context
  fixes A Prep :: "complex Matrix.mat" and G :: "nat \<Rightarrow> complex Matrix.mat" and b :: "complex Matrix.vec"
    and n N :: nat and \<kappa> t0 \<epsilon> :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and k1: "1 \<le> \<kappa>"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> 1 / \<kappa> \<le> l \<and> l \<le> 1"
      and t0: "0 < t0" "t0 \<le> pi / 2" and N: "2 \<le> N"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3 \<and> Quantum.unitary (G k)"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1"
      and Prep: "Prep \<in> carrier_mat (N * (n * 3)) (N * (n * 3))" "Quantum.unitary Prep"
        "Prep *\<^sub>v unit_vec (N * (n * 3)) 0 = tensor_vec (win_state N) (tensor_vec b (unit_vec 3 0))"
      and e: "0 < \<epsilon>" "\<epsilon> * \<kappa> \<le> 1"
      and big: "12 * pi\<^sup>2 * sqrt (4 + 2 * pi\<^sup>2) * \<kappa> / \<epsilon> \<le> real N * t0"
begin

abbreviation (input) "flg_K \<equiv> N * (n * 3)"
abbreviation (input) "flg_O \<equiv> evolution A t0 \<Otimes> 1\<^sub>m 3"
abbreviation (input) "flg_c \<equiv> flag_full_prog N n G Prep"
abbreviation (input) "flg_x \<equiv> herm_inv A *\<^sub>v b"
abbreviation (input) "flg_t \<equiv> tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>flg_x\<parallel>) \<cdot>\<^sub>v flg_x) (unit_vec 3 1))"
abbreviation (input) "flg_M \<equiv> flag_meas flg_K 3 (\<lambda>c. c = 1)"
abbreviation (input) "flg_y c \<equiv> pflag 3 (\<lambda>c. c = 1) (sem N (n * 3) flg_O c *\<^sub>v unit_vec flg_K 0)"

lemma flg_basics:
  shows "0 < flg_K" "flg_O \<in> carrier_mat (n * 3) (n * 3)" "Quantum.unitary flg_O" "gates_ok flg_K flg_c"
    and "0 < \<parallel>flg_x\<parallel>" "flg_t \<in> carrier_vec flg_K" "\<parallel>flg_t\<parallel> = 1"
    and "pflag_mat flg_K 3 (\<lambda>c. c = 1) *\<^sub>v flg_t = flg_t" "pflag_mat flg_K 3 (\<lambda>c. c \<noteq> 1) *\<^sub>v flg_t = 0\<^sub>v flg_K"
proof -
  have N0: "0 < N" using N by simp
  show "0 < flg_K" using N0 n0 by simp
  have E0: "evolution A t0 \<in> carrier_mat n n" using A by (rule evolution_carrier)
  show "flg_O \<in> carrier_mat (n * 3) (n * 3)" using E0 by (intro carrier_matI) simp_all
  show "Quantum.unitary flg_O" by (rule tensor_mat_unitary_one_right[OF evolution_unitary[OF A]])
  show "gates_ok flg_K flg_c" by (rule gates_ok_flag_full_prog[OF N0 G Prep(1,2)])
  have k0: "0 < \<kappa>" using k1 by simp
  have z: "0 \<notin> herm_spectrum A"
  proof
    assume "0 \<in> herm_spectrum A"
    hence "1 / \<kappa> \<le> 0" using spec by blast
    thus False using k0 by simp
  qed
  have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
  have Hr: "dim_row (herm_inv A) = n" using Hc by simp
  show xp: "0 < \<parallel>flg_x\<parallel>" by (rule herm_inv_sol_pos[OF A z b])
  have dx: "dim_vec (complex_of_real (1 / \<parallel>flg_x\<parallel>) \<cdot>\<^sub>v flg_x) = n" using Hc by simp
  show tc: "flg_t \<in> carrier_vec flg_K" by (rule carrier_vecI) (simp add: tensor_vec_dim dx Hr)
  show "\<parallel>flg_t\<parallel> = 1" using win_state_norm[OF N] xp dx Hr by (simp add: vnorm_tensor tensor_vec_dim cpx_vec_length_smult norm_divide)
  have pt: "pflag 3 P flg_t = tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>flg_x\<parallel>) \<cdot>\<^sub>v flg_x) (pflag 3 P (unit_vec 3 1)))" for P
    using pflag_tensor_left[of "win_state N" N _ n 3 P] pflag_tensor[OF dx, of "unit_vec 3 1" 3 P] dx Hr by (simp add: tensor_vec_dim)
  show "pflag_mat flg_K 3 (\<lambda>c. c = 1) *\<^sub>v flg_t = flg_t"
    unfolding pflag_mat_mult[OF carrier_vecD[OF tc], where P = "\<lambda>c. c = 1" and d = 3] pt pflag_unit3 by simp
  show "pflag_mat flg_K 3 (\<lambda>c. c \<noteq> 1) *\<^sub>v flg_t = 0\<^sub>v flg_K"
    unfolding pflag_mat_mult[OF carrier_vecD[OF tc], where P = "\<lambda>c. c \<noteq> 1" and d = 3] pt pflag_unit3 using dx Hr n0 tensor_zero_right[of "n * 3" "win_state N"]
    by (simp add: tensor_zero_right)
qed


lemma flg_M1: "flg_M 1 = pflag_mat flg_K 3 (\<lambda>c. c = 1)" and flg_M0: "flg_M 0 = pflag_mat flg_K 3 (\<lambda>c. c \<noteq> 1)"
  by (simp_all add: flag_meas_def)

lemma flg_triples:
  assumes g: "gates_ok flg_K c"
  shows "\<And>e. 0 < \<parallel>flg_y c\<parallel> \<Longrightarrow> \<parallel>complex_of_real (1 / \<parallel>flg_y c\<parallel>) \<cdot>\<^sub>v flg_y c - flg_t\<parallel> \<le> e \<Longrightarrow>
           \<parallel>flg_y c\<parallel>\<^sup>2 * (1 - e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
    and "q \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2 \<Longrightarrow>
         state_sig.hoare_total_correct [N, n, 3] (complex_of_real q \<cdot>\<^sub>m 1\<^sub>m flg_K)
           (prog_meas flg_K flg_M (qgates N (n * 3) flg_O c)) (outer_prod flg_t flg_t)"
    and "0 < \<parallel>flg_y c\<parallel> \<Longrightarrow>
         state_sig.hoare_total_correct [N, n, 3]
           (complex_of_real ((cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2
              / \<parallel>flg_y c\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m flg_K)
           (rus_meas flg_K flg_M (qgates N (n * 3) flg_O c)) (outer_prod flg_t flg_t)"
proof -
  interpret state_sig "[N, n, 3]" .
  note fb = flg_basics
  have dd: "d = flg_K" by (simp add: d_def)
  have d0: "0 < d" using fb(1) dd by simp
  have Us: "\<And>U. U \<in> set (qgates N (n * 3) flg_O c) \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    using qgates_ok[OF fb(2,3) g] dd by simp
  have Mm: "measurement d 2 (flag_meas d 3 (\<lambda>c. c = 1))" by (rule flag_meas_measurement)
  have tc: "flg_t \<in> carrier_vec d" using fb(6) dd by simp
  have t1: "Complex_Matrix.inner_prod flg_t flg_t = 1"
    using inner_bridge[of flg_t flg_t] fb(7) cpx_vec_length_inner_prod[of flg_t] by simp
  have m1: "adjoint (flag_meas d 3 (\<lambda>c. c = 1) 1) *\<^sub>v flg_t = flg_t" unfolding dd flg_M1 proj_set_adjoint by (rule fb(8))
  have m0: "adjoint (flag_meas d 3 (\<lambda>c. c = 1) 0) *\<^sub>v flg_t = 0\<^sub>v d" unfolding dd flg_M0 proj_set_adjoint by (rule fb(9))
  have Sc: "sem N (n * 3) flg_O c \<in> carrier_mat flg_K flg_K" by (rule sem_carrier[OF fb(2,3) g])
  have oc: "sem N (n * 3) flg_O c *\<^sub>v unit_vec flg_K 0 \<in> carrier_vec flg_K" by (rule mult_mat_vec_carrier[OF Sc unit_vec_carrier])
  have \<psi>: "circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0 = sem N (n * 3) flg_O c *\<^sub>v unit_vec flg_K 0"
    unfolding dd qgates_sem[OF fb(2,3) g] ..
  have yP: "flg_y c = flg_M 1 *\<^sub>v (sem N (n * 3) flg_O c *\<^sub>v unit_vec flg_K 0)"
    unfolding flg_M1 by (rule pflag_mat_mult[symmetric, OF carrier_vecD[OF oc]])
  have inn: "Complex_Matrix.inner_prod flg_t (sem N (n * 3) flg_O c *\<^sub>v unit_vec flg_K 0) = \<langle>flg_t|flg_y c\<rangle>"
  proof -
    have "Complex_Matrix.inner_prod flg_t (flg_M 1 *\<^sub>v (sem N (n * 3) flg_O c *\<^sub>v unit_vec flg_K 0))
          = Complex_Matrix.inner_prod (adjoint (flg_M 1) *\<^sub>v flg_t) (sem N (n * 3) flg_O c *\<^sub>v unit_vec flg_K 0)"
      by (rule adjoint_def_alter[OF fb(6) oc]) (simp add: flag_meas_def)
    also have "adjoint (flg_M 1) *\<^sub>v flg_t = flg_t" unfolding flg_M1 proj_set_adjoint by (rule fb(8))
    finally have "Complex_Matrix.inner_prod flg_t (flg_y c) = Complex_Matrix.inner_prod flg_t (sem N (n * 3) flg_O c *\<^sub>v unit_vec flg_K 0)"
      unfolding yP .
    moreover have "Complex_Matrix.inner_prod flg_t (flg_y c) = \<langle>flg_t|flg_y c\<rangle>"
      by (rule inner_bridge) (use carrier_vecD[OF fb(6)] carrier_vecD[OF oc] in simp)
    ultimately show ?thesis by simp
  qed
  show "\<parallel>flg_y c\<parallel>\<^sup>2 * (1 - e\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
    if y0: "0 < \<parallel>flg_y c\<parallel>" and D: "\<parallel>complex_of_real (1 / \<parallel>flg_y c\<parallel>) \<cdot>\<^sub>v flg_y c - flg_t\<parallel> \<le> e" for e
    using fidelity_from_close[OF _ fb(7) _ y0 D] \<psi>[unfolded dd] inn carrier_vecD[OF fb(6)] carrier_vecD[OF oc] by simp
  show "hoare_total_correct (complex_of_real q \<cdot>\<^sub>m 1\<^sub>m flg_K) (prog_meas flg_K flg_M (qgates N (n * 3) flg_O c)) (outer_prod flg_t flg_t)"
    if q: "q \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
  proof -
    have q': "q \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0)))\<^sup>2"
      unfolding dd by (rule q)
    show ?thesis unfolding dd[symmetric] by (rule hoare_prog_overlap[where Us = "qgates N (n * 3) flg_O c", OF d0 Us Mm tc m1 m0 q'])
  qed
  show "hoare_total_correct
           (complex_of_real ((cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2
              / \<parallel>flg_y c\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m flg_K)
           (rus_meas flg_K flg_M (qgates N (n * 3) flg_O c)) (outer_prod flg_t flg_t)"
    if y0: "0 < \<parallel>flg_y c\<parallel>"
  proof -
    have pe: "Complex_Matrix.inner_prod (flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0))
                (flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0)) = complex_of_real (\<parallel>flg_y c\<parallel>\<^sup>2)"
    proof -
      have "flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0) = flg_y c"
        unfolding dd \<psi>[unfolded dd] yP ..
      moreover have "Complex_Matrix.inner_prod (flg_y c) (flg_y c) = \<langle>flg_y c|flg_y c\<rangle>" by (rule inner_bridge) simp
      ultimately show ?thesis using cpx_vec_length_inner_prod[of "flg_y c"] by simp
    qed
    have p0: "0 < Re (Complex_Matrix.inner_prod (flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0))
                (flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0)))"
      unfolding pe using y0 by simp
    have h: "hoare_total_correct (complex_of_real ((cmod (Complex_Matrix.inner_prod flg_t (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0)))\<^sup>2
               / Re (Complex_Matrix.inner_prod (flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0))
                (flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0)))) \<cdot>\<^sub>m 1\<^sub>m d)
             (rus_meas d (flag_meas d 3 (\<lambda>c. c = 1)) (qgates N (n * 3) flg_O c)) (outer_prod flg_t flg_t)"
      by (rule hoare_rus_overlap[where Us = "qgates N (n * 3) flg_O c", OF d0 Us Mm tc t1 m1 m0 p0])
    have pr: "Re (Complex_Matrix.inner_prod (flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0))
                (flag_meas d 3 (\<lambda>c. c = 1) 1 *\<^sub>v (circuit_mat d (qgates N (n * 3) flg_O c) *\<^sub>v unit_vec d 0))) = \<parallel>flg_y c\<parallel>\<^sup>2"
      unfolding pe by simp
    show ?thesis using h unfolding dd pr[unfolded dd] .
  qed
qed

theorem hhl_flag_program:
  "state_sig.hoare_total_correct [N, n, 3] (complex_of_real ((1 / (4 * \<kappa>))\<^sup>2 * (1 - \<epsilon>\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m flg_K)
     (prog_meas flg_K flg_M (qgates N (n * 3) flg_O flg_c)) (outer_prod flg_t flg_t)"
proof -
  note fb = flg_basics
  note hr = hhl_paper_runtime[OF A n0 k1 spec t0 N G Gh b Prep e big]
  have k0: "0 < \<kappa>" using k1 by simp
  have y1: "1 / (4 * \<kappa>) \<le> \<parallel>flg_y flg_c\<parallel>" by (rule hr(2))
  have y0: "0 < \<parallel>flg_y flg_c\<parallel>" using y1 k0 by (smt (verit) divide_pos_pos)
  have F: "\<parallel>flg_y flg_c\<parallel>\<^sup>2 * (1 - \<epsilon>\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O flg_c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
    by (rule flg_triples(1)[OF fb(4) y0 hr(1)])
  show ?thesis
  proof (rule flg_triples(2)[OF fb(4)], cases "0 \<le> 1 - \<epsilon>\<^sup>2")
    case True
    have "(1 / (4 * \<kappa>))\<^sup>2 \<le> \<parallel>flg_y flg_c\<parallel>\<^sup>2" by (rule power_mono[OF y1]) (use k0 in simp)
    hence "(1 / (4 * \<kappa>))\<^sup>2 * (1 - \<epsilon>\<^sup>2) \<le> \<parallel>flg_y flg_c\<parallel>\<^sup>2 * (1 - \<epsilon>\<^sup>2)" by (rule mult_right_mono[OF _ True])
    thus "(1 / (4 * \<kappa>))\<^sup>2 * (1 - \<epsilon>\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O flg_c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
      using F by linarith
  next
    case False
    hence "(1 / (4 * \<kappa>))\<^sup>2 * (1 - \<epsilon>\<^sup>2) \<le> 0" by (simp add: mult_nonneg_nonpos)
    thus "(1 / (4 * \<kappa>))\<^sup>2 * (1 - \<epsilon>\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O flg_c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
      using zero_le_power2 by (rule order_trans)
  qed
qed

theorem hhl_flag_rus:
  "state_sig.hoare_total_correct [N, n, 3] (complex_of_real (1 - \<epsilon>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m flg_K)
     (rus_meas flg_K flg_M (qgates N (n * 3) flg_O flg_c)) (outer_prod flg_t flg_t)"
proof -
  interpret state_sig "[N, n, 3]" .
  note fb = flg_basics
  note hr = hhl_paper_runtime[OF A n0 k1 spec t0 N G Gh b Prep e big]
  have dd: "d = flg_K" by (simp add: d_def)
  have k0: "0 < \<kappa>" using k1 by simp
  have y0: "0 < \<parallel>flg_y flg_c\<parallel>" using hr(2) k0 by (smt (verit) divide_pos_pos)
  have F: "\<parallel>flg_y flg_c\<parallel>\<^sup>2 * (1 - \<epsilon>\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O flg_c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
    by (rule flg_triples(1)[OF fb(4) y0 hr(1)])
  have le: "1 - \<epsilon>\<^sup>2 \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O flg_c) *\<^sub>v unit_vec flg_K 0)))\<^sup>2 / \<parallel>flg_y flg_c\<parallel>\<^sup>2"
    using F y0 by (simp add: field_simps)
  show ?thesis using total_scalar_weaken[OF flg_triples(3)[OF fb(4) y0, folded dd] le[folded dd]] unfolding dd .
qed

text \<open>Amplitude amplification of the filtered algorithm, as a program: at most $\pi\kappa$ rounds.\<close>

theorem hhl_flag_amplified:
  assumes y1: "\<parallel>flg_y flg_c\<parallel> < 1"
  obtains k where "calls (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k) = (2 * k + 1) * (2 * (N - 1))"
    and "real k \<le> pi * \<kappa>"
    and "state_sig.hoare_total_correct [N, n, 3]
           (complex_of_real ((1 - \<parallel>flg_y flg_c\<parallel>\<^sup>2) * (1 - \<epsilon>\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m flg_K)
           (prog_meas flg_K flg_M (qgates N (n * 3) flg_O (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k)))
           (outer_prod flg_t flg_t)"
proof -
  note fb = flg_basics
  note hr = hhl_paper_runtime[OF A n0 k1 spec t0 N G Gh b Prep e big]
  have k0: "0 < \<kappa>" using k1 by simp
  have ylo: "1 / (4 * \<kappa>) \<le> \<parallel>flg_y flg_c\<parallel>" by (rule hr(2))
  have y0: "0 < \<parallel>flg_y flg_c\<parallel>" using ylo k0 by (smt (verit) divide_pos_pos)
  obtain k where k1': "1 - \<parallel>flg_y flg_c\<parallel>\<^sup>2 \<le> \<parallel>flg_y (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k)\<parallel>\<^sup>2"
    and k2: "complex_of_real (1 / \<parallel>flg_y (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k)\<parallel>) \<cdot>\<^sub>v flg_y (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k)
             = complex_of_real (1 / \<parallel>flg_y flg_c\<parallel>) \<cdot>\<^sub>v flg_y flg_c"
    and k3: "calls (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k) = (2 * k + 1) * calls flg_c"
    and k4: "real k \<le> pi / (4 * \<parallel>flg_y flg_c\<parallel>)"
    by (rule circuit_amplification[OF fb(2,3,4,1) y0 y1])
  have k5: "real k \<le> pi * \<kappa>"
  proof -
    have "pi / (4 * \<parallel>flg_y flg_c\<parallel>) \<le> pi / (4 * (1 / (4 * \<kappa>)))"
      using ylo k0 y0 by (intro divide_left_mono mult_left_mono) simp_all
    thus ?thesis using k4 k0 by simp
  qed
  let ?z = "flg_y (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k)"
  have g: "gates_ok flg_K (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k)" by (rule gates_ok_aa_prog[OF fb(4)])
  have "0 < 1 - \<parallel>flg_y flg_c\<parallel>\<^sup>2" using y1 vnorm_ge0[of "flg_y flg_c"] by (simp add: power_less_one_iff abs_square_less_1)
  hence z0: "0 < \<parallel>?z\<parallel>" using k1' by (smt (verit) power2_eq_square vnorm_ge0 mult_nonneg_nonneg zero_less_mult_iff)
  have D: "\<parallel>complex_of_real (1 / \<parallel>?z\<parallel>) \<cdot>\<^sub>v ?z - flg_t\<parallel> \<le> \<epsilon>" unfolding k2 by (rule hr(1))
  have F: "\<parallel>?z\<parallel>\<^sup>2 * (1 - \<epsilon>\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k)) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
    by (rule flg_triples(1)[OF g z0 D])
  have q: "(1 - \<parallel>flg_y flg_c\<parallel>\<^sup>2) * (1 - \<epsilon>\<^sup>2) \<le> (cmod (Complex_Matrix.inner_prod flg_t (circuit_mat flg_K (qgates N (n * 3) flg_O (aa_prog flg_K 3 (\<lambda>c. c = 1) flg_c k)) *\<^sub>v unit_vec flg_K 0)))\<^sup>2"
  proof (cases "0 \<le> 1 - \<epsilon>\<^sup>2")
    case True
    thus ?thesis using F mult_right_mono[OF k1' True] by linarith
  next
    case False
    have "0 \<le> 1 - \<parallel>flg_y flg_c\<parallel>\<^sup>2" using y1 vnorm_ge0[of "flg_y flg_c"] by (simp add: abs_square_le_1)
    hence "(1 - \<parallel>flg_y flg_c\<parallel>\<^sup>2) * (1 - \<epsilon>\<^sup>2) \<le> 0" using False by (simp add: mult_nonneg_nonpos)
    thus ?thesis using zero_le_power2 by (rule order_trans)
  qed
  show ?thesis by (rule that[OF k3[unfolded calls_flag_full_prog] k5 flg_triples(2)[OF g q]])
qed

end

end
