theory QPE_Program
  imports QPE_Precision HHL_Termination HHL_Preconditioned
begin

section \<open>Phase estimation as a program\<close>

text \<open>Registers: clock $\C^N$, $N=2^k$, and system $\C^m$.  The program initialises the state,
prepares the eigenvector $u=U_u\ket0$, and applies $H^{\otimes k}$, the controlled powers of $U$
and $F_N^\dagger$.  The predicate $\Pi_J$ says that the clock holds a value in $Js$.\<close>

abbreviation clock_proj :: "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> complex Matrix.mat" where
  "clock_proj N m Js \<equiv> proj_set (N * m) {r. r div m \<in> Js}"

definition qpe_gates :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "qpe_gates k U Uu = [1\<^sub>m (2 ^ k) \<Otimes> Uu, (Hadamard \<otimes>\<^bsup>k\<^esup>) \<Otimes> 1\<^sub>m (dim_row U), ctrl_pow (2 ^ k) (dim_row U) U,
     (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (dim_row U)]"

definition qpe_program :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> com" where
  "qpe_program k U Uu = init_com (2 ^ k * dim_row U) ;; utrans_seq (qpe_gates k U Uu)"

text \<open>The same circuit in elementary gates: $k$ Hadamards, one $\mathrm C_jU^{2^j}$ per clock
qubit, and the inverse of the Fourier circuit of the AFP.\<close>

definition qpe_elem_gates :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "qpe_elem_gates k U Uu = (1\<^sub>m (2 ^ k) \<Otimes> Uu) # map (\<lambda>G. G \<Otimes> 1\<^sub>m (dim_row U)) (had_gates k)
     @ map (\<lambda>j. ctrl_bit (2 ^ k) (dim_row U) j (U ^\<^sub>m 2 ^ j)) [0..<k]
     @ map (\<lambda>G. G \<Otimes> 1\<^sub>m (dim_row U)) (rev (map dagger (qft_circuit k)))"

definition qpe_elem_program :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> com" where
  "qpe_elem_program k U Uu = init_com (2 ^ k * dim_row U) ;; utrans_seq (qpe_elem_gates k U Uu)"

text \<open>On $a\otimes u$ with $u$ a unit vector, $\Pi_J$ has the value $\sum_{j\in Js}|a_j|^2$.\<close>

lemma clock_proj_value:
  assumes a: "dim_vec a = N" and u: "dim_vec u = m" and unit: "(\<Sum>i<m. (cmod (u $ i))\<^sup>2) = 1"
  shows "inner_prod (tensor_vec a u) (clock_proj N m Js *\<^sub>v tensor_vec a u)
         = complex_of_real (\<Sum>j | j < N \<and> j \<in> Js. (cmod (a $ j))\<^sup>2)"
proof -
  let ?\<psi> = "tensor_vec a u"
  have d\<psi>: "dim_vec ?\<psi> = N * m" by (rule tensor_vec_dim[OF a u])
  have "inner_prod ?\<psi> (clock_proj N m Js *\<^sub>v ?\<psi>) = (\<Sum>r<N * m. (if r div m \<in> Js then ?\<psi> $ r else 0) * cnj (?\<psi> $ r))"
    unfolding proj_set_mult_vec[OF d\<psi>] using d\<psi> by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<N. \<Sum>i<m. (if k \<in> Js then complex_of_real ((cmod (a $ k))\<^sup>2) else 0) * complex_of_real ((cmod (u $ i))\<^sup>2))"
    unfolding sum_split_mp
  proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
    fix k i assume "k \<in> {..<N}" "i \<in> {..<m}"
    hence k: "k < N" and i: "i < m" by simp_all
    have e: "?\<psi> $ (k * m + i) = a $ k * u $ i" using tensor_vec_index[OF a u mult_index_lt[OF k i]] mult_index_div_mod[OF i] by simp
    have "a $ k * u $ i * cnj (a $ k * u $ i) = complex_of_real ((cmod (a $ k))\<^sup>2) * complex_of_real ((cmod (u $ i))\<^sup>2)"
      by (simp only: complex_norm_square complex_cnj_mult mult_ac)
    thus "(if (k * m + i) div m \<in> Js then ?\<psi> $ (k * m + i) else 0) * cnj (?\<psi> $ (k * m + i))
          = (if k \<in> Js then complex_of_real ((cmod (a $ k))\<^sup>2) else 0) * complex_of_real ((cmod (u $ i))\<^sup>2)"
      unfolding e mult_index_div_mod(1)[OF i] by simp
  qed
  also have "\<dots> = (\<Sum>k<N. if k \<in> Js then complex_of_real ((cmod (a $ k))\<^sup>2) else 0)"
  proof (rule sum.cong[OF refl])
    fix k
    have s1: "(\<Sum>i<m. complex_of_real ((cmod (u $ i))\<^sup>2)) = 1" unfolding of_real_sum[symmetric] unit by simp
    show "(\<Sum>i<m. (if k \<in> Js then complex_of_real ((cmod (a $ k))\<^sup>2) else 0) * complex_of_real ((cmod (u $ i))\<^sup>2))
          = (if k \<in> Js then complex_of_real ((cmod (a $ k))\<^sup>2) else 0)"
      by (simp only: sum_distrib_left[symmetric] s1 mult_1_right)
  qed
  also have "\<dots> = complex_of_real (\<Sum>j | j < N \<and> j \<in> Js. (cmod (a $ j))\<^sup>2)"
  proof -
    have "{j. j < N \<and> j \<in> Js} = {j \<in> {..<N}. j \<in> Js}" by auto
    hence "(\<Sum>j | j < N \<and> j \<in> Js. complex_of_real ((cmod (a $ j))\<^sup>2))
           = (\<Sum>k<N. if k \<in> Js then complex_of_real ((cmod (a $ k))\<^sup>2) else 0)"
      by (simp only: sum.inter_filter[OF finite_lessThan])
    thus ?thesis unfolding of_real_sum by (rule sym)
  qed
  finally show ?thesis .
qed

context state_sig
begin

text \<open>Triples of an initialised circuit depend only on its matrix.\<close>

lemma init_circuit_transfer:
  assumes d0: "0 < d" and Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and Us': "\<And>U. U \<in> set Us' \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and circ: "circuit_mat d Us' = circuit_mat d Us"
    and h: "\<Turnstile>\<^sub>t {P} init_com d ;; utrans_seq Us {Q}"
  shows "\<Turnstile>\<^sub>t {P} init_com d ;; utrans_seq Us' {Q}"
  using h denote_init_circuit[OF d0 Us] denote_init_circuit[OF d0 Us'] circ
  unfolding hoare_total_correct_def density_states_def partial_density_operator_def by auto

end

lemma qpe_while_free: "while_free (qpe_program k U Uu)"
proof -
  have "while_free (utrans_seq Us)" for Us by (induction Us) auto
  thus ?thesis by (simp add: qpe_program_def init_com_def list_all_iff)
qed

context
  fixes U Uu :: "complex Matrix.mat" and u :: "complex Matrix.vec" and m k :: nat and \<phi> :: real
  assumes U: "U \<in> carrier_mat m m" "Quantum.unitary U" and m0: "0 < m" and k: "1 \<le> k"
    and Uu: "Uu \<in> carrier_mat m m" "Quantum.unitary Uu" "Uu *\<^sub>v unit_vec m 0 = u"
    and ev: "U *\<^sub>v u = cis (2 * pi * \<phi>) \<cdot>\<^sub>v u"
begin

lemma qpe_dim: "dim_row U = m" using U(1) by simp

lemma qpe_u: "dim_vec u = m" using Uu by auto

lemma qpe_unit: "(\<Sum>i<m. (cmod (u $ i))\<^sup>2) = 1"
proof -
  have "\<parallel>u\<parallel> = \<parallel>unit_vec m 0\<parallel>" using unitary_vnorm[OF Uu(1,2), of "unit_vec m 0"] Uu(3) by simp
  also have "\<dots> = 1" using m0 by (simp add: cpx_vec_length_def lessThan_atLeast0 sum.atLeast_Suc_lessThan unit_vec_def)
  finally have "sqrt (\<Sum>i<m. (cmod (u $ i))\<^sup>2) = 1" unfolding cpx_vec_length_def qpe_u .
  thus ?thesis by simp
qed

lemma qpe_gates_ok:
  "G \<in> set (qpe_gates k U Uu) \<Longrightarrow> G \<in> carrier_mat (2 ^ k * m) (2 ^ k * m) \<and> Complex_Matrix.unitary G"
proof -
  assume G: "G \<in> set (qpe_gates k U Uu)"
  have N: "0 < (2::nat) ^ k" by simp
  have P: "1\<^sub>m (2 ^ k) \<Otimes> Uu \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)" by (rule tensor_carrier[OF one_carrier_mat Uu(1)])
  have Pu: "Quantum.unitary (1\<^sub>m (2 ^ k) \<Otimes> Uu)" by (rule tensor_mat_unitary[OF id_is_unitary Uu(2)])
  have H: "Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m m \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)"
    by (rule tensor_carrier[OF hadamard_layer_carrier[OF k] one_carrier_mat])
  have Hu: "Quantum.unitary (Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m m)" by (rule tensor_mat_unitary_one_right[OF hadamard_layer_unitary[OF k]])
  have C: "ctrl_pow (2 ^ k) m U \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)" by simp
  have Cu: "Quantum.unitary (ctrl_pow (2 ^ k) m U)"
    by (rule ctrl_blocks_unitary) (simp_all add: U(1) unitary_pow[OF U])
  have F: "(fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)"
    by (rule tensor_carrier[OF dagger_carrier[OF fourier_carrier] one_carrier_mat])
  have Fu: "Quantum.unitary ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)"
    by (rule tensor_mat_unitary_one_right[OF unitary_dagger[OF fourier_unitary[OF N]]])
  have ok: "X \<in> carrier_mat (2 ^ k * m) (2 ^ k * m) \<and> Complex_Matrix.unitary X"
    if "X \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)" "Quantum.unitary X" for X using unitary_bridge[OF that] that(1) by simp
  from G consider "G = 1\<^sub>m (2 ^ k) \<Otimes> Uu" | "G = Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m m" | "G = ctrl_pow (2 ^ k) m U"
    | "G = (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m" unfolding qpe_gates_def qpe_dim by auto
  thus ?thesis using ok[OF P Pu] ok[OF H Hu] ok[OF C Cu] ok[OF F Fu] by cases simp_all
qed

text \<open>The circuit leaves $(\sum_j\alpha_j\ket j)\otimes u$.\<close>

lemma qpe_out:
  "circuit_mat (2 ^ k * m) (qpe_gates k U Uu) *\<^sub>v unit_vec (2 ^ k * m) 0 = tensor_vec (Matrix.vec (2 ^ k) (pe_amp (2 ^ k) \<phi>)) u"
proof -
  let ?N = "2 ^ k :: nat"
  have e0: "dim_vec (unit_vec m 0) = m" by simp
  have s1: "(1\<^sub>m ?N \<Otimes> Uu) *\<^sub>v unit_vec (?N * m) 0 = tensor_vec (unit_vec ?N 0) u"
  proof -
    have "(1\<^sub>m ?N \<Otimes> Uu) *\<^sub>v tensor_vec (unit_vec ?N 0) (unit_vec m 0) = tensor_vec (1\<^sub>m ?N *\<^sub>v unit_vec ?N 0) (Uu *\<^sub>v unit_vec m 0)"
      by (rule tensor_mat_vec_mult[OF one_carrier_mat Uu(1)]) simp_all
    thus ?thesis unfolding unit_vec_tensor using Uu(3) by simp
  qed
  have s2: "(Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec (unit_vec ?N 0) u = tensor_vec (uniform_state ?N) u"
  proof -
    have "(Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec (unit_vec ?N 0) u = tensor_vec ((Hadamard \<otimes>\<^bsup>k\<^esup>) *\<^sub>v unit_vec ?N 0) (1\<^sub>m m *\<^sub>v u)"
      by (rule tensor_mat_vec_mult[OF hadamard_layer_carrier[OF k] one_carrier_mat]) (simp_all add: qpe_u)
    thus ?thesis using hadamard_layer_zero[OF k] carrier_vecI[OF qpe_u] by simp
  qed
  have "circuit_mat (2 ^ k * m) (qpe_gates k U Uu) *\<^sub>v unit_vec (2 ^ k * m) 0 = run_gates (unit_vec (2 ^ k * m) 0) (qpe_gates k U Uu)"
    by (rule circuit_mat_run) (use qpe_gates_ok in auto)
  also have "\<dots> = ((fourier ?N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow ?N m U *\<^sub>v tensor_vec (uniform_state ?N) u)"
    unfolding qpe_gates_def qpe_dim by (simp add: s1 s2)
  also have "\<dots> = tensor_vec (Matrix.vec ?N (pe_amp ?N \<phi>)) u" by (rule phase_estimation[OF U(1) qpe_u ev])
  finally show ?thesis .
qed

lemma qpe_well_com: "state_sig.well_com [2 ^ k, m] (qpe_program k U Uu)"
proof -
  interpret state_sig "[2 ^ k, m]" .
  have dd: "d = 2 ^ k * m" by (simp add: d_def)
  show ?thesis unfolding qpe_program_def qpe_dim dd[symmetric]
    using well_com_init well_com_utrans_seq[of "qpe_gates k U Uu"] qpe_gates_ok m0 by (auto simp: dd)
qed

text \<open>The weakest precondition of $\Pi_J$: the clock reads a value in $J$ with probability
$\sum_{j\in J}|\alpha_j|^2$.\<close>

theorem qpe_total:
  "state_sig.hoare_total_correct [2 ^ k, m]
     (complex_of_real (\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * m))
     (qpe_program k U Uu) (clock_proj (2 ^ k) m Js)"
proof -
  interpret state_sig "[2 ^ k, m]" .
  have dd: "d = 2 ^ k * m" by (simp add: d_def)
  have d0: "0 < d" using m0 by (simp add: dd)
  have h: "hoare_partial (inner_prod (circuit_mat d (qpe_gates k U Uu) *\<^sub>v unit_vec d 0)
              (clock_proj (2 ^ k) m Js *\<^sub>v (circuit_mat d (qpe_gates k U Uu) *\<^sub>v unit_vec d 0)) \<cdot>\<^sub>m 1\<^sub>m d)
             (init_com d ;; utrans_seq (qpe_gates k U Uu)) (clock_proj (2 ^ k) m Js)"
    by (rule hoare_init_circuit[OF qp_proj_set[unfolded dd] d0]) (use qpe_gates_ok dd in auto)
  have v: "inner_prod (circuit_mat d (qpe_gates k U Uu) *\<^sub>v unit_vec d 0)
              (clock_proj (2 ^ k) m Js *\<^sub>v (circuit_mat d (qpe_gates k U Uu) *\<^sub>v unit_vec d 0))
           = complex_of_real (\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2)"
  proof -
    have "(\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (Matrix.vec (2 ^ k) (pe_amp (2 ^ k) \<phi>) $ j))\<^sup>2)
          = (\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2)" by (rule sum.cong) auto
    thus ?thesis unfolding dd qpe_out
      using clock_proj_value[of "Matrix.vec (2 ^ k) (pe_amp (2 ^ k) \<phi>)" "2 ^ k" u m Js] qpe_u qpe_unit by simp
  qed
  have hp: "hoare_partial (complex_of_real (\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m d)
             (qpe_program k U Uu) (clock_proj (2 ^ k) m Js)"
    using h[unfolded v] unfolding qpe_program_def qpe_dim dd .
  show ?thesis using partial_to_total[OF hoare_partial_sound[OF hp qpe_well_com] qpe_while_free qpe_well_com] unfolding dd .
qed


text \<open>The precondition is exact: on every input $\rho$ the clock reads a value in $J$ with
probability $\sum_{j\in J}|\alpha_j|^2\,\mathrm{tr}\,\rho$.\<close>

theorem qpe_prob:
  assumes r: "\<rho> \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)"
  shows "trace (clock_proj (2 ^ k) m Js * state_sig.denote [2 ^ k, m] (qpe_program k U Uu) \<rho>)
         = complex_of_real (\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2) * trace \<rho>"
proof -
  interpret state_sig "[2 ^ k, m]" .
  have dd: "d = 2 ^ k * m" by (simp add: d_def)
  let ?\<psi> = "tensor_vec (Matrix.vec (2 ^ k) (pe_amp (2 ^ k) \<phi>)) u"
  let ?P = "clock_proj (2 ^ k) m Js"
  have \<psi>c: "?\<psi> \<in> carrier_vec (2 ^ k * m)" by (rule carrier_vecI) (simp add: tensor_vec_dim qpe_u)
  have den: "denote (qpe_program k U Uu) \<rho> = trace \<rho> \<cdot>\<^sub>m outer_prod ?\<psi> ?\<psi>"
    using denote_init_circuit[of "qpe_gates k U Uu" \<rho>] qpe_gates_ok qpe_out r m0
    unfolding qpe_program_def qpe_dim dd by simp
  have O: "outer_prod ?\<psi> ?\<psi> \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)" by (rule outer_prod_dim[OF \<psi>c \<psi>c])
  have "trace (?P * denote (qpe_program k U Uu) \<rho>) = trace \<rho> * trace (?P * outer_prod ?\<psi> ?\<psi>)"
    unfolding den by (simp add: mult_smult_distrib[OF proj_set_carrier O] trace_smult[OF mult_carrier_mat[OF proj_set_carrier O]])
  also have "trace (?P * outer_prod ?\<psi> ?\<psi>) = inner_prod ?\<psi> (?P *\<^sub>v ?\<psi>)" by (rule trace_outer_prod_right[OF proj_set_carrier \<psi>c \<psi>c])
  also have "\<dots> = complex_of_real (\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2)"
  proof -
    have "(\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (Matrix.vec (2 ^ k) (pe_amp (2 ^ k) \<phi>) $ j))\<^sup>2)
          = (\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2)" by (rule sum.cong) auto
    thus ?thesis using clock_proj_value[of "Matrix.vec (2 ^ k) (pe_amp (2 ^ k) \<phi>)" "2 ^ k" u m Js] qpe_u qpe_unit by simp
  qed
  finally show ?thesis by (simp add: mult.commute)
qed

text \<open>The textbook guarantees as triples: an exact phase is read with certainty, the nearest
grid value with probability at least $4/\pi^2$, values within $e/N$ with probability at least
$1-1/(2(e-1))$, and with $k=n+\lceil\log_2(2+1/(2\varepsilon))\rceil$ clock qubits the
estimate is within $2^{-n}$ with probability at least $1-\varepsilon$.\<close>

corollary qpe_exact_total:
  assumes j0: "j0 < 2 ^ k" and \<phi>: "\<phi> = real j0 / 2 ^ k"
  shows "state_sig.hoare_total_correct [2 ^ k, m] (1\<^sub>m (2 ^ k * m)) (qpe_program k U Uu) (clock_proj (2 ^ k) m {j0})"
proof -
  have "pe_amp (2 ^ k) \<phi> j0 = 1"
    using arg_cong[OF phase_estimation_exact[of "2 ^ k" j0], of "\<lambda>v. v $ j0"] j0 \<phi> by simp
  moreover have "{j. j < 2 ^ k \<and> j \<in> {j0}} = {j0}" using j0 by auto
  moreover have "1 \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * m) = (1\<^sub>m (2 ^ k * m) :: complex Matrix.mat)" by (rule eq_matI) auto
  ultimately show ?thesis using qpe_total[of "{j0}"] by simp
qed

lemma qpe_d: "state_sig.d [2 ^ k, m] = 2 ^ k * m" by (simp add: state_sig.d_def)

corollary qpe_nearest_total:
  "state_sig.hoare_total_correct [2 ^ k, m] (complex_of_real (4 / pi\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * m))
     (qpe_program k U Uu) (clock_proj (2 ^ k) m {pe_round (2 ^ k) \<phi>})"
proof -
  let ?j = "pe_round (2 ^ k) \<phi>"
  have j: "?j < 2 ^ k" by (rule pe_round_lt) simp
  have s: "{j. j < 2 ^ k \<and> j \<in> {?j}} = {?j}" using j by auto
  have "4 / pi\<^sup>2 \<le> (cmod (pe_amp (2 ^ k) \<phi> ?j))\<^sup>2" by (rule pe_amp_near[OF _ pe_round_dist]) simp_all
  hence le: "4 / pi\<^sup>2 \<le> (\<Sum>j | j < 2 ^ k \<and> j \<in> {?j}. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2)" unfolding s by simp
  show ?thesis using state_sig.total_scalar_weaken[OF qpe_total[of "{?j}", folded qpe_d] le] unfolding qpe_d .
qed

corollary qpe_tail_total:
  assumes e: "1 < e"
  shows "state_sig.hoare_total_correct [2 ^ k, m] (complex_of_real (1 - 1 / (2 * (e - 1))) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * m))
     (qpe_program k U Uu) (clock_proj (2 ^ k) m {j. 2 ^ k * circ_dist \<phi> (real j / 2 ^ k) \<le> e})"
proof -
  have le: "1 - 1 / (2 * (e - 1)) \<le> (\<Sum>j | j < 2 ^ k \<and> j \<in> {j. 2 ^ k * circ_dist \<phi> (real j / 2 ^ k) \<le> e}. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2)"
    using pe_tail_good[of "2 ^ k" e \<phi>] e by simp
  show ?thesis using state_sig.total_scalar_weaken[OF qpe_total[folded qpe_d] le] unfolding qpe_d .
qed

corollary qpe_precision_total:
  assumes eps: "0 < \<epsilon>" and t: "k = n + nat \<lceil>log 2 (2 + 1 / (2 * \<epsilon>))\<rceil>"
  shows "state_sig.hoare_total_correct [2 ^ k, m] (complex_of_real (1 - \<epsilon>) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * m))
     (qpe_program k U Uu) (clock_proj (2 ^ k) m {j. circ_dist \<phi> (real j / 2 ^ k) \<le> 1 / 2 ^ n})"
proof -
  have le: "1 - \<epsilon> \<le> (\<Sum>j | j < 2 ^ k \<and> j \<in> {j. circ_dist \<phi> (real j / 2 ^ k) \<le> 1 / 2 ^ n}. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2)"
    using pe_precision[OF eps t, of \<phi>] by simp
  show ?thesis using state_sig.total_scalar_weaken[OF qpe_total[folded qpe_d] le] unfolding qpe_d .
qed


lemma qpe_elem_kinds:
  "G \<in> set (qpe_elem_gates k U Uu) \<Longrightarrow>
     G = 1\<^sub>m (2 ^ k) \<Otimes> Uu \<or> elementary (2 ^ k * m) G \<or> (\<exists>j<k. G = ctrl_bit (2 ^ k) m j (U ^\<^sub>m 2 ^ j))"
proof -
  assume G: "G \<in> set (qpe_elem_gates k U Uu)"
  have h: "\<forall>V \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (had_gates k)). elementary (2 ^ k * m) V"
    by (rule elementary_map_right) (use had_gates[OF k] m0 in auto)
  have f: "\<forall>V \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k)))). elementary (2 ^ k * m) V"
    by (rule elementary_map_right[OF qft_inv_circuit(2) m0])
  show ?thesis using G h f unfolding qpe_elem_gates_def qpe_dim by auto
qed

lemma qpe_elem_ok:
  "G \<in> set (qpe_elem_gates k U Uu) \<Longrightarrow> G \<in> carrier_mat (2 ^ k * m) (2 ^ k * m) \<and> Complex_Matrix.unitary G"
proof -
  assume G: "G \<in> set (qpe_elem_gates k U Uu)"
  have ok: "X \<in> carrier_mat (2 ^ k * m) (2 ^ k * m) \<and> Complex_Matrix.unitary X"
    if "X \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)" "Quantum.unitary X" for X using unitary_bridge[OF that] that(1) by simp
  from qpe_elem_kinds[OF G] show ?thesis
  proof (elim disjE exE conjE)
    assume "G = 1\<^sub>m (2 ^ k) \<Otimes> Uu"
    thus ?thesis using ok[OF tensor_carrier[OF one_carrier_mat Uu(1)] tensor_mat_unitary[OF id_is_unitary Uu(2)]] by simp
  next
    assume "elementary (2 ^ k * m) G"
    thus ?thesis using ok elementary_unitary by blast
  next
    fix j assume "j < k" "G = ctrl_bit (2 ^ k) m j (U ^\<^sub>m 2 ^ j)"
    thus ?thesis using ok[OF ctrl_bit_carrier ctrl_bit_unitary[OF pow_carrier_mat[OF U(1)] unitary_pow[OF U]]] by simp
  qed
qed

lemma qpe_elem_circuit: "circuit_mat (2 ^ k * m) (qpe_elem_gates k U Uu) = circuit_mat (2 ^ k * m) (qpe_gates k U Uu)"
proof -
  let ?K = "2 ^ k * m" and ?P = "1\<^sub>m (2 ^ k) \<Otimes> Uu"
  let ?Hs = "map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (had_gates k)" and ?Cs = "map (\<lambda>j. ctrl_bit (2 ^ k) m j (U ^\<^sub>m 2 ^ j)) [0..<k]"
  let ?Fs = "map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k)))"
  have cH: "V \<in> carrier_mat ?K ?K" if "V \<in> set ?Hs" for V using that qpe_elem_ok unfolding qpe_elem_gates_def qpe_dim by auto
  have cC: "V \<in> carrier_mat ?K ?K" if "V \<in> set ?Cs" for V using that qpe_elem_ok unfolding qpe_elem_gates_def qpe_dim by auto
  have cF: "V \<in> carrier_mat ?K ?K" if "V \<in> set ?Fs" for V using that qpe_elem_ok unfolding qpe_elem_gates_def qpe_dim by auto
  have H: "circuit_mat ?K ?Hs = Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m m"
    using circuit_mat_tensor_right[of "had_gates k" "2 ^ k" m] had_gates[OF k] elementary_carriers m0 by auto
  have C: "circuit_mat ?K ?Cs = ctrl_pow (2 ^ k) m U" by (rule ctrl_pow_qubits[OF U(1)])
  have Fc0: "V \<in> carrier_mat (2 ^ k) (2 ^ k)" if "V \<in> set (rev (map dagger (qft_circuit k)))" for V
    using qft_inv_circuit(2) elementary_unitary(1) that by blast
  have F: "circuit_mat ?K ?Fs = (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m"
    using circuit_mat_tensor_right[of "rev (map dagger (qft_circuit k))" "2 ^ k" m, OF Fc0 _ m0] qft_inv_circuit(1) by simp
  have "circuit_mat ?K (qpe_elem_gates k U Uu) = circuit_mat ?K (?Hs @ ?Cs @ ?Fs) * ?P"
    unfolding qpe_elem_gates_def qpe_dim by simp
  also have "circuit_mat ?K (?Hs @ ?Cs @ ?Fs) = (circuit_mat ?K ?Fs * circuit_mat ?K ?Cs) * circuit_mat ?K ?Hs"
  proof -
    have a1: "circuit_mat ?K (?Cs @ ?Fs) = circuit_mat ?K ?Fs * circuit_mat ?K ?Cs" by (rule circuit_mat_append) (use cC cF in auto)
    have "circuit_mat ?K (?Hs @ ?Cs @ ?Fs) = circuit_mat ?K (?Cs @ ?Fs) * circuit_mat ?K ?Hs"
      by (rule circuit_mat_append) (use cH cC cF in auto)
    thus ?thesis unfolding a1 .
  qed
  also have "\<dots> = ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m) * ctrl_pow (2 ^ k) m U * (Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m m)" unfolding H C F ..
  also have "\<dots> * ?P = circuit_mat ?K (qpe_gates k U Uu)"
  proof -
    have Fc: "(fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m \<in> carrier_mat ?K ?K" by (rule tensor_carrier[OF dagger_carrier[OF fourier_carrier] one_carrier_mat])
    show ?thesis unfolding qpe_gates_def qpe_dim using Fc by simp
  qed
  finally show ?thesis .
qed

theorem qpe_elem_total:
  "state_sig.hoare_total_correct [2 ^ k, m]
     (complex_of_real (\<Sum>j | j < 2 ^ k \<and> j \<in> Js. (cmod (pe_amp (2 ^ k) \<phi> j))\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * m))
     (qpe_elem_program k U Uu) (clock_proj (2 ^ k) m Js)"
proof -
  interpret state_sig "[2 ^ k, m]" .
  have dd: "d = 2 ^ k * m" by (simp add: d_def)
  show ?thesis using init_circuit_transfer[of "qpe_gates k U Uu" "qpe_elem_gates k U Uu", folded dd] qpe_gates_ok qpe_elem_ok
      qpe_elem_circuit qpe_total[of Js, unfolded qpe_program_def qpe_dim] m0
    unfolding qpe_elem_program_def qpe_dim dd by simp
qed

end

end
