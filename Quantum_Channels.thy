(*  Title:   Quantum_Channels.thy
    Author:  Dustin Bryant, standard channels beyond the notes
*)

theory Quantum_Channels
  imports Quantum_Computing_by_VP.Day31_Bit_Flip_Channel
begin

section \<open>Extensions beyond the notes\<close>

text \<open>Nothing from here on is in Paulsen's notes.  These are standard facts proved with the
machinery above: rank-one projections; the mixed unitary channels $\rho\mapsto(1-p)\rho+pU\rho U^*$,
which are Kraus maps and so completely positive, trace preserving and unital at once; the
bit-flip, phase-flip and bit-phase-flip channels as the cases $U=X,Z,Y$; the maximally mixed
state as their common fixed point; conjugation by a unitary, the identity channel and
composition; and the Pauli product identities.\<close>

subsection \<open>Rank-one projections\<close>

text \<open>For a unit vector $\psi$ the matrix $\ketbra\psi\psi$ is a projection: Day 13 makes it a density
matrix and Day 14 shows that pure densities are idempotent.\<close>

lemma rank1_projection:
  assumes \<psi>: "quantum_state n \<psi>"
  shows "projection n (outer_sum n [\<psi>])"
proof -
  have eq: "pure_density \<psi> = outer_sum n [\<psi>]" using \<psi> by (simp add: pure_density_def quantum_state_def)
  have dm: "density_matrix n (outer_sum n [\<psi>])" using pure_density_is_density_matrix[OF \<psi>] eq by simp
  have "outer_sum n [\<psi>] * outer_sum n [\<psi>] = outer_sum n [\<psi>]"
    using pure_density_iff_idempotent[OF dm] pure_density_is_pure_state_density[OF \<psi>] eq by simp
  thus ?thesis using dm unfolding projection_def density_matrix_def hermitian_def by (simp add: outer_sum_hermitian)
qed

lemma rank1_projection_mult_vec:
  assumes \<psi>: "quantum_state n \<psi>"
  shows "outer_sum n [\<psi>] *\<^sub>v \<psi> = \<psi>"
proof -
  have "\<langle>\<psi>|\<psi>\<rangle> = 1" using \<psi> by (simp add: quantum_state_def flip: cpx_vec_length_inner_prod)
  thus ?thesis using \<psi> by (simp add: quantum_state_def outer_sum_singleton_mult_vec)
qed

lemma rank1_projection_trace:
  assumes \<psi>: "quantum_state n \<psi>"
  shows "Tr (outer_sum n [\<psi>]) = 1"
  using \<psi> by (simp add: quantum_state_def Tr_outer_sum_single flip: cpx_vec_length_inner_prod)

subsection \<open>Mixed unitary channels\<close>

text \<open>For $U\in M_n$ and $0\le p\le1$ the channel $\rho\mapsto(1-p)\rho+pU\rho U^*$ is the Kraus map
of $\sqrt{1-p}\,I$ and $\sqrt p\,U$.  For unitary $U$ these are Kraus operators, and
$(1-p)I+pUU^*=I$ makes the channel unital as well.\<close>

definition mixed_unitary_channel :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "mixed_unitary_channel U p \<rho> = complex_of_real (1 - p) \<cdot>\<^sub>m \<rho> + complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>))"

definition mixed_unitary_kraus :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "mixed_unitary_kraus n U p = [complex_of_real (sqrt (1 - p)) \<cdot>\<^sub>m 1\<^sub>m n, complex_of_real (sqrt p) \<cdot>\<^sub>m U]"

lemma mixed_unitary_channel_kraus:
  assumes p: "0 \<le> p" "p \<le> 1" and U: "U \<in> carrier_mat n n" and \<rho>: "\<rho> \<in> carrier_mat n n"
  shows "mixed_unitary_channel U p \<rho> = kraus_map_dim n (mixed_unitary_kraus n U p) \<rho>"
proof -
  have s: "complex_of_real (sqrt (1 - p)) * cnj (complex_of_real (sqrt (1 - p))) = complex_of_real (1 - p)"
    "complex_of_real (sqrt p) * cnj (complex_of_real (sqrt p)) = complex_of_real p"
    using p by (simp_all flip: of_real_mult)
  show ?thesis
    unfolding mixed_unitary_kraus_def mixed_unitary_channel_def
    by (simp only: kraus_map_dim_two[OF smult_carrier_mat[OF one_carrier_mat] smult_carrier_mat[OF U] \<rho>]
                   smult_sandwich[OF one_carrier_mat \<rho>] smult_sandwich[OF U \<rho>] s
                   dagger_of_id_is_id left_mult_one_mat[OF \<rho>] right_mult_one_mat[OF \<rho>])
qed

lemma mixed_unitary_kraus_operators:
  assumes p: "0 \<le> p" "p \<le> 1" and U: "U \<in> carrier_mat n n" and Uu: "unitary U"
  shows "kraus_operators n n (mixed_unitary_kraus n U p)"
proof -
  have s: "cnj (complex_of_real (sqrt (1 - p))) * complex_of_real (sqrt (1 - p)) = complex_of_real (1 - p)"
    "cnj (complex_of_real (sqrt p)) * complex_of_real (sqrt p) = complex_of_real p"
    using p by (simp_all flip: of_real_mult)
  have UdU: "U\<^sup>\<dagger> * U = 1\<^sub>m n" using Uu U by (simp add: unitary_def)
  have "sum_wdag_w n (mixed_unitary_kraus n U p) = complex_of_real (1 - p) \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real p \<cdot>\<^sub>m 1\<^sub>m n"
    unfolding mixed_unitary_kraus_def
    by (simp only: sum_wdag_w_two[OF smult_carrier_mat[OF one_carrier_mat] smult_carrier_mat[OF U]]
                   smult_dagger_mult[OF one_carrier_mat] smult_dagger_mult[OF U] s
                   dagger_of_id_is_id UdU right_mult_one_mat[OF one_carrier_mat])
  also have "\<dots> = 1\<^sub>m n" by (rule eq_matI) (auto simp: algebra_simps)
  finally show ?thesis
    unfolding kraus_operators_altdef using U by (auto simp: mixed_unitary_kraus_def)
qed

lemma mixed_unitary_channel_CPTP:
  assumes p: "0 \<le> p" "p \<le> 1" and U: "U \<in> carrier_mat n n" and Uu: "unitary U" and n: "0 < n"
  shows "mixed_unitary_channel U p \<in> CPTP n n"
  using kraus_is_cptp[OF mixed_unitary_kraus_operators[OF p U Uu] n n] mixed_unitary_channel_kraus[OF p U]
        completely_positive_cong[of n "mixed_unitary_channel U p" "kraus_map_dim n (mixed_unitary_kraus n U p)" n]
        trace_preserving_cong[of n "mixed_unitary_channel U p" "kraus_map_dim n (mixed_unitary_kraus n U p)"]
  by (simp add: CPTP_def)

lemma mixed_unitary_channel_UCP:
  assumes p: "0 \<le> p" "p \<le> 1" and U: "U \<in> carrier_mat n n" and Uu: "unitary U" and n: "0 < n"
  shows "mixed_unitary_channel U p \<in> UCP n n"
proof -
  have "U * 1\<^sub>m n * (U\<^sup>\<dagger>) = 1\<^sub>m n" using Uu U by (simp add: unitary_def)
  hence "mixed_unitary_channel U p (1\<^sub>m n) = 1\<^sub>m n"
    unfolding mixed_unitary_channel_def by (intro eq_matI) (auto simp: algebra_simps)
  thus ?thesis
    using kraus_is_cptp[OF mixed_unitary_kraus_operators[OF p U Uu] n n] mixed_unitary_channel_kraus[OF p U]
          completely_positive_cong[of n "mixed_unitary_channel U p" "kraus_map_dim n (mixed_unitary_kraus n U p)" n]
    by (simp add: CPTP_def UCP_def unital_map_def)
qed

lemma mixed_unitary_channel_density_matrix:
  assumes p: "0 \<le> p" "p \<le> 1" and U: "U \<in> carrier_mat n n" and Uu: "unitary U" and \<rho>: "density_matrix n \<rho>"
  shows "density_matrix n (mixed_unitary_channel U p \<rho>)"
  using \<rho> kraus_map_dim_density_matrix[OF mixed_unitary_kraus_operators[OF p U Uu] \<rho>]
  by (simp add: mixed_unitary_channel_kraus[OF p U] density_matrix_def)

text \<open>The ends $p=0$ and $p=1$, and the fixed points: everything commuting with $U$.\<close>

lemma mixed_unitary_channel_zero:
  assumes U: "U \<in> carrier_mat n n" and \<rho>: "\<rho> \<in> carrier_mat n n"
  shows "mixed_unitary_channel U 0 \<rho> = \<rho>"
  unfolding mixed_unitary_channel_def
  using mult_carrier_mat[OF mult_carrier_mat[OF U \<rho>] dagger_carrier[OF U]] \<rho> by (intro eq_matI) auto

lemma mixed_unitary_channel_one:
  assumes U: "U \<in> carrier_mat n n" and \<rho>: "\<rho> \<in> carrier_mat n n"
  shows "mixed_unitary_channel U 1 \<rho> = U * \<rho> * (U\<^sup>\<dagger>)"
  unfolding mixed_unitary_channel_def
  using mult_carrier_mat[OF mult_carrier_mat[OF U \<rho>] dagger_carrier[OF U]] \<rho> by (intro eq_matI) auto

lemma mixed_unitary_channel_fixed_point:
  assumes U: "U \<in> carrier_mat n n" and Uu: "unitary U" and M: "M \<in> carrier_mat n n" and comm: "U * M = M * U"
  shows "mixed_unitary_channel U p M = M"
proof -
  have "U * M * (U\<^sup>\<dagger>) = M * (U * (U\<^sup>\<dagger>))" by (simp only: comm assoc_mult_mat[OF M U dagger_carrier[OF U]])
  also have "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using Uu U by (simp add: unitary_def)
  finally have "U * M * (U\<^sup>\<dagger>) = M" using M by simp
  thus ?thesis unfolding mixed_unitary_channel_def using M by (intro eq_matI) (auto simp: algebra_simps)
qed

subsection \<open>The maximally mixed state\<close>

definition maximally_mixed_state :: "nat \<Rightarrow> complex Matrix.mat" where
  "maximally_mixed_state n = complex_of_real (1 / real n) \<cdot>\<^sub>m 1\<^sub>m n"

lemma maximally_mixed_state_carrier [simp]: "maximally_mixed_state n \<in> carrier_mat n n"
  by (simp add: maximally_mixed_state_def)

lemma maximally_mixed_state_density_matrix:
  assumes n: "0 < n"
  shows "density_matrix n (maximally_mixed_state n)"
proof -
  have "psd (maximally_mixed_state n)"
    unfolding maximally_mixed_state_def
    by (rule psd_smult_nonneg[OF _ projection_psd[OF projection_one] one_carrier_mat]) simp
  moreover have "Tr (maximally_mixed_state n) = 1"
    using n by (simp add: maximally_mixed_state_def Tr_smult Tr_one_mat)
  ultimately show ?thesis by (simp add: density_matrix_def)
qed

text \<open>It commutes with everything, so every mixed unitary channel fixes it.\<close>

lemma maximally_mixed_state_commutes:
  assumes U: "U \<in> carrier_mat n n"
  shows "U * maximally_mixed_state n = maximally_mixed_state n * U"
  unfolding maximally_mixed_state_def
  by (simp add: mult_smult_distrib[OF U one_carrier_mat] mult_smult_assoc_mat[OF one_carrier_mat U] carrier_matD[OF U])

lemma mixed_unitary_channel_fixes_max_mixed:
  assumes U: "U \<in> carrier_mat n n" and Uu: "unitary U"
  shows "mixed_unitary_channel U p (maximally_mixed_state n) = maximally_mixed_state n"
  by (rule mixed_unitary_channel_fixed_point[OF U Uu maximally_mixed_state_carrier maximally_mixed_state_commutes[OF U]])

subsection \<open>The Pauli channels\<close>

text \<open>The bit-flip channel of Day 31 and the phase-flip and bit-phase-flip channels are the mixed
unitary channels of $X$, $Z$ and $Y$; Day 31 already has \<open>bit_flip_channel_CPTP\<close> and
\<open>bit_flip_channel_UCP\<close>.\<close>

lemma bit_flip_channel_eq: "bit_flip_channel p = mixed_unitary_channel Pauli_X p"
  by (rule ext) (simp add: bit_flip_channel_def mixed_unitary_channel_def)

definition phase_flip_channel :: "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "phase_flip_channel p = mixed_unitary_channel Pauli_Z p"

definition bit_phase_flip_channel :: "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "bit_phase_flip_channel p = mixed_unitary_channel Pauli_Y p"

lemma pauli_channels_CPTP:
  assumes p: "0 \<le> p" "p \<le> 1"
  shows "phase_flip_channel p \<in> CPTP 2 2" "bit_phase_flip_channel p \<in> CPTP 2 2"
  unfolding phase_flip_channel_def bit_phase_flip_channel_def
  by (rule mixed_unitary_channel_CPTP[OF p]; simp add: Pauli_Z_unitary Pauli_Y_unitary)+

lemma pauli_channels_UCP:
  assumes p: "0 \<le> p" "p \<le> 1"
  shows "phase_flip_channel p \<in> UCP 2 2" "bit_phase_flip_channel p \<in> UCP 2 2"
  unfolding phase_flip_channel_def bit_phase_flip_channel_def
  by (rule mixed_unitary_channel_UCP[OF p]; simp add: Pauli_Z_unitary Pauli_Y_unitary)+

lemma pauli_channels_density_matrix:
  assumes p: "0 \<le> p" "p \<le> 1" and \<rho>: "density_matrix 2 \<rho>"
  shows "density_matrix 2 (bit_flip_channel p \<rho>)" "density_matrix 2 (phase_flip_channel p \<rho>)"
    "density_matrix 2 (bit_phase_flip_channel p \<rho>)"
  unfolding bit_flip_channel_eq phase_flip_channel_def bit_phase_flip_channel_def
  by (rule mixed_unitary_channel_density_matrix[OF p _ _ \<rho>]; simp add: Pauli_X_unitary Pauli_Z_unitary Pauli_Y_unitary)+

lemma pauli_channels_fix_max_mixed:
  "bit_flip_channel p (maximally_mixed_state 2) = maximally_mixed_state 2"
  "phase_flip_channel p (maximally_mixed_state 2) = maximally_mixed_state 2"
  "bit_phase_flip_channel p (maximally_mixed_state 2) = maximally_mixed_state 2"
  unfolding bit_flip_channel_eq phase_flip_channel_def bit_phase_flip_channel_def
  by (rule mixed_unitary_channel_fixes_max_mixed; simp add: Pauli_X_unitary Pauli_Z_unitary Pauli_Y_unitary)+

text \<open>A matrix commuting with $X$ (resp.\ $Z$) is fixed by every bit-flip (phase-flip) channel.\<close>

lemma bit_flip_channel_fixed_point:
  assumes M: "M \<in> carrier_mat 2 2" and comm: "Pauli_X * M = M * Pauli_X"
  shows "bit_flip_channel p M = M"
  unfolding bit_flip_channel_eq by (rule mixed_unitary_channel_fixed_point[OF Pauli_X_carrier Pauli_X_unitary M comm])

lemma phase_flip_channel_fixed_point:
  assumes M: "M \<in> carrier_mat 2 2" and comm: "Pauli_Z * M = M * Pauli_Z"
  shows "phase_flip_channel p M = M"
  unfolding phase_flip_channel_def by (rule mixed_unitary_channel_fixed_point[OF Pauli_Z_carrier Pauli_Z_unitary M comm])

subsection \<open>Conjugation, the identity channel, composition\<close>

text \<open>$\rho\mapsto U\rho U^*$ is the Kraus map of the single operator $U$: completely positive for any
$U\in M_{d,n}$, and a unital channel for unitary $U$.  The identity channel is the case $U=I$.\<close>

lemma conjugation_completely_positive:
  assumes U: "U \<in> carrier_mat d n" and n: "0 < n" and d: "0 < d"
  shows "completely_positive n d (\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>))"
  by (subst completely_positive_cong[of n _ "kraus_map_dim d [U]" d])
     (simp_all add: kraus_map_dim_single[OF U] kraus_cp_no_tp[of "[U]" d n] U n d del: kraus_map_dim_Cons)

lemma unitary_kraus_operators:
  assumes U: "U \<in> carrier_mat n n" and Uu: "unitary U"
  shows "kraus_operators n n [U]"
  using Uu U mult_carrier_mat[OF dagger_carrier[OF U] U]
  by (simp add: kraus_operators_altdef sum_wdag_w_Cons unitary_def)

lemma unitary_conjugation_CPTP:
  assumes U: "U \<in> carrier_mat n n" and Uu: "unitary U" and n: "0 < n"
  shows "(\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)) \<in> CPTP n n"
  using kraus_is_cptp[OF unitary_kraus_operators[OF U Uu] n n] kraus_map_dim_single[OF U]
        completely_positive_cong[of n "\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)" "kraus_map_dim n [U]" n]
        trace_preserving_cong[of n "\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)" "kraus_map_dim n [U]"]
  by (simp add: CPTP_def)

lemma unitary_conjugation_UCP:
  assumes U: "U \<in> carrier_mat n n" and Uu: "unitary U" and n: "0 < n"
  shows "(\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)) \<in> UCP n n"
  using unitary_conjugation_CPTP[OF U Uu n] Uu U by (simp add: CPTP_def UCP_def unital_map_def unitary_def)

lemma pauli_kraus_operators:
  "kraus_operators 2 2 [Pauli_X]" "kraus_operators 2 2 [Pauli_Y]" "kraus_operators 2 2 [Pauli_Z]"
  by (rule unitary_kraus_operators; simp add: Pauli_X_unitary Pauli_Y_unitary Pauli_Z_unitary)+

definition identity_channel :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "identity_channel \<rho> = \<rho>"

lemma identity_channel_CPTP:
  assumes n: "0 < n"
  shows "identity_channel \<in> CPTP n n"
  using unitary_conjugation_CPTP[of "1\<^sub>m n" n] n
        completely_positive_cong[of n identity_channel "\<lambda>\<rho>. 1\<^sub>m n * \<rho> * ((1\<^sub>m n)\<^sup>\<dagger>)" n]
        trace_preserving_cong[of n identity_channel "\<lambda>\<rho>. 1\<^sub>m n * \<rho> * ((1\<^sub>m n)\<^sup>\<dagger>)"]
  by (simp add: CPTP_def identity_channel_def unitary_def)

lemma identity_channel_UCP:
  assumes n: "0 < n"
  shows "identity_channel \<in> UCP n n"
  using identity_channel_CPTP[OF n] by (simp add: CPTP_def UCP_def unital_map_def identity_channel_def)

lemma compose_trace_preserving:
  assumes F: "trace_preserving n F" and G: "trace_preserving n G"
      and range: "\<And>\<rho>. \<rho> \<in> carrier_mat n n \<Longrightarrow> F \<rho> \<in> carrier_mat n n"
  shows "trace_preserving n (\<lambda>\<rho>. G (F \<rho>))"
  using F G range unfolding trace_preserving_def by simp

lemma compose_unital_map:
  assumes "unital_map n n F" and "unital_map n n G"
  shows "unital_map n n (\<lambda>\<rho>. F (G \<rho>))"
  using assms unfolding unital_map_def by simp

subsection \<open>Pauli product identities\<close>

text \<open>With the Day 32 convention for $Y$: $XY=-iZ$, $YZ=-iX$, $ZX=-iY$.\<close>

lemma Pauli_X_times_Pauli_Y: "Pauli_X * Pauli_Y = -\<i> \<cdot>\<^sub>m Pauli_Z"
  by (rule eq_matI) (auto simp: Pauli_X_def Pauli_Y_def Pauli_Z_def scalar_prod_def sumof2 less_2_cases_iff)

lemma Pauli_Y_times_Pauli_Z: "Pauli_Y * Pauli_Z = -\<i> \<cdot>\<^sub>m Pauli_X"
  by (rule eq_matI) (auto simp: Pauli_X_def Pauli_Y_def Pauli_Z_def scalar_prod_def sumof2 less_2_cases_iff)

lemma Pauli_Z_times_Pauli_X: "Pauli_Z * Pauli_X = -\<i> \<cdot>\<^sub>m Pauli_Y"
  by (rule eq_matI) (auto simp: Pauli_X_def Pauli_Y_def Pauli_Z_def scalar_prod_def sumof2 less_2_cases_iff)

end
