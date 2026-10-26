(*  Title:   Quantum_Channels.thy
    Author:  Dustin Bryant, standard channels beyond the notes
*)

theory Quantum_Channels
  imports Day32_Phase_Flip_Code
begin

section \<open>Extensions beyond the notes\<close>

text \<open>Nothing from here on is in Paulsen's notes.  These are standard quantum-information
facts proved with the machinery above: rank-one projections, the bit-flip, phase-flip,
bit-phase-flip and unitary-conjugation channels and their membership in UCP and CPTP,
composition of channels, Kraus lists, the maximally mixed state, and the Pauli product
identities.\<close>

subsection \<open>Rank-one projections\<close>

lemma outer_sum_singleton_hermitian:
  fixes \<psi> :: "complex Matrix.vec"
  shows "(outer_sum n [\<psi>])\<^sup>\<dagger> = outer_sum n [\<psi>]"
proof (rule eq_matI)
  show "dim_row ((outer_sum n [\<psi>])\<^sup>\<dagger>) = dim_row (outer_sum n [\<psi>])"
    by simp
  show "dim_col ((outer_sum n [\<psi>])\<^sup>\<dagger>) = dim_col (outer_sum n [\<psi>])"
    by simp
next
  fix i j
  assume i: "i < dim_row (outer_sum n [\<psi>])"
     and j: "j < dim_col (outer_sum n [\<psi>])"
  hence ij: "i < n" "j < n" by simp_all
  have e1: "(outer_sum n [\<psi>])\<^sup>\<dagger> $$ (i, j)
              = cnj ((outer_sum n [\<psi>]) $$ (j, i))"
    using ij by (simp add: dagger_def)
  also have "\<dots> = cnj (\<psi> $ j * cnj (\<psi> $ i))"
    using outer_sum_singleton_index[OF ij(2) ij(1)] by simp
  also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j)"
    by simp
  also have "\<dots> = (outer_sum n [\<psi>]) $$ (i, j)"
    using outer_sum_singleton_index[OF ij(1) ij(2)] by simp
  finally show "(outer_sum n [\<psi>])\<^sup>\<dagger> $$ (i, j)
                  = (outer_sum n [\<psi>]) $$ (i, j)".
qed

lemma outer_sum_singleton_idempotent:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "outer_sum n [\<psi>] * outer_sum n [\<psi>] = outer_sum n [\<psi>]"
proof -
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have norm1: "\<parallel>\<psi>\<parallel> = 1" using \<psi>_qs by (simp add: quantum_state_def)
  have inner_self: "\<langle>\<psi> | \<psi>\<rangle> = 1"
  proof -
    have "\<langle>\<psi> | \<psi>\<rangle> = complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2)"
      by (metis cpx_vec_length_inner_prod)
    also have "\<dots> = complex_of_real (1\<^sup>2)" using norm1 by simp
    also have "\<dots> = 1" by simp
    finally show ?thesis .
  qed
  let ?M = "outer_sum n [\<psi>]"
  have M_c: "?M \<in> carrier_mat n n" by auto
  show "?M * ?M = ?M"
  proof (rule eq_matI)
    show "dim_row (?M * ?M) = dim_row ?M" using M_c by simp
    show "dim_col (?M * ?M) = dim_col ?M" using M_c by simp
  next
    fix i j
    assume i: "i < dim_row ?M" and j: "j < dim_col ?M"
    hence ij: "i < n" "j < n" by simp_all
    have step1: "(?M * ?M) $$ (i, j)
                   = (\<Sum>k = 0..<n. ?M $$ (i, k) * ?M $$ (k, j))"
      using ij M_c
      by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>k = 0..<n.
                       \<psi> $ i * cnj (\<psi> $ k) * (\<psi> $ k * cnj (\<psi> $ j)))"
      using ij
      by (intro sum.cong refl)
         (simp add: outer_sum_singleton_index)
    also have "\<dots> = (\<Sum>k = 0..<n.
                      \<psi> $ i * cnj (\<psi> $ j) * (cnj (\<psi> $ k) * \<psi> $ k))"
      by (intro sum.cong refl) (simp add: ac_simps)
    also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j)
                    * (\<Sum>k = 0..<n. cnj (\<psi> $ k) * \<psi> $ k)"
      by (simp add: sum_distrib_left)
    also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j) * \<langle>\<psi> | \<psi>\<rangle>"
      using \<psi>_dim
      by (simp add: inner_prod_def lessThan_atLeast0)
    also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j)"
      using inner_self by simp
    also have "\<dots> = ?M $$ (i, j)"
      using outer_sum_singleton_index[OF ij(1) ij(2)] by simp
    finally show "(?M * ?M) $$ (i, j) = ?M $$ (i, j)" .
  qed
qed

lemma rank1_projection:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "projection n (outer_sum n [\<psi>])"
proof -
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have c: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have h: "hermitian (outer_sum n [\<psi>])"
    using outer_sum_singleton_hermitian
    by (simp add: hermitian_def)
  have idem: "outer_sum n [\<psi>] * outer_sum n [\<psi>] = outer_sum n [\<psi>]"
    using outer_sum_singleton_idempotent[OF \<psi>_qs] .
  show ?thesis unfolding projection_def using c h idem by blast
qed



lemma rank1_projection_acts_identity:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "outer_sum n [\<psi>] *\<^sub>v \<psi> = \<psi>"
proof -
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have norm1: "\<parallel>\<psi>\<parallel> = 1" using \<psi>_qs by (simp add: quantum_state_def)
  have inner_self: "\<langle>\<psi> | \<psi>\<rangle> = 1"
  proof -
    have "\<langle>\<psi> | \<psi>\<rangle> = complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2)"
      by (metis cpx_vec_length_inner_prod)
    also have "\<dots> = complex_of_real (1\<^sup>2)" using norm1 by simp
    also have "\<dots> = 1" by simp
    finally show ?thesis .
  qed
  have act: "outer_sum n [\<psi>] *\<^sub>v \<psi> = \<langle>\<psi> | \<psi>\<rangle> \<cdot>\<^sub>v \<psi>"
    using outer_sum_singleton_mult_vec[OF \<psi>_dim \<psi>_dim] .
  also have "\<dots> = (1 :: complex) \<cdot>\<^sub>v \<psi>" using inner_self by simp
  also have "\<dots> = \<psi>" by (intro eq_vecI) auto
  finally show ?thesis .
qed

lemma rank1_projection_trace_one:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "Tr (outer_sum n [\<psi>]) = 1"
proof -
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have norm1: "\<parallel>\<psi>\<parallel> = 1" using \<psi>_qs by (simp add: quantum_state_def)
  have "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
    using Tr_outer_sum_single[OF \<psi>_dim] .
  also have "\<dots> = complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2)"
    by (metis cpx_vec_length_inner_prod)
  also have "\<dots> = complex_of_real (1\<^sup>2)" using norm1 by simp
  also have "\<dots> = 1" by simp
  finally show ?thesis .
qed


subsection \<open>The bit-flip channel at $p=0$ and $p=1$\<close>

lemma bit_flip_channel_zero:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "bit_flip_channel 0 \<rho> = \<rho>"
proof -
  have x_c: "Pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "Pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "Pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c assms by (rule mult_carrier_mat)
  have x\<rho>xd_c: "Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)
  have one_smul: "(1 :: complex) \<cdot>\<^sub>m \<rho> = \<rho>"
    by (intro eq_matI) auto
  have zero_smul: "(0 :: complex) \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>))
                    = 0\<^sub>m 2 2"
    using x\<rho>xd_c by (intro eq_matI) auto
  have rho_zero: "\<rho> + 0\<^sub>m 2 2 = \<rho>"
    using assms by (intro eq_matI) auto
  have "bit_flip_channel 0 \<rho>
          = (1 :: complex) \<cdot>\<^sub>m \<rho>
            + (0 :: complex) \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>))"
    by (simp add: bit_flip_channel_def)
  also have "\<dots> = \<rho> + 0\<^sub>m 2 2"
    using one_smul zero_smul by simp
  also have "\<dots> = \<rho>" using rho_zero .
  finally show ?thesis .
qed

lemma bit_flip_channel_one:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "bit_flip_channel 1 \<rho> = Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)"
proof -
  have x_c: "Pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "Pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "Pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c assms by (rule mult_carrier_mat)
  have x\<rho>xd_c: "Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)
  have one_smul: "(1 :: complex) \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>))
                    = Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)"
    by (intro eq_matI) auto
  have zero_smul: "(0 :: complex) \<cdot>\<^sub>m \<rho> = 0\<^sub>m 2 2"
    using assms by (intro eq_matI) auto
  have zero_plus: "0\<^sub>m 2 2 + Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)
                    = Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)"
    using x\<rho>xd_c by (intro eq_matI) auto
  have "bit_flip_channel 1 \<rho>
          = (0 :: complex) \<cdot>\<^sub>m \<rho>
            + (1 :: complex) \<cdot>\<^sub>m (Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>))"
    by (simp add: bit_flip_channel_def)
  also have "\<dots> = 0\<^sub>m 2 2 + Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)"
    using zero_smul one_smul by simp
  also have "\<dots> = Pauli_X * \<rho> * (Pauli_X\<^sup>\<dagger>)"
    using zero_plus .
  finally show ?thesis .
qed


subsection \<open>The phase-flip channel\<close>

definition phase_flip_channel ::
  "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "phase_flip_channel p \<rho> \<equiv>
     complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
     + complex_of_real p \<cdot>\<^sub>m (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>))"

lemma phase_flip_channel_carrier:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "phase_flip_channel p \<rho> \<in> carrier_mat 2 2"
proof -
  have z_c: "Pauli_Z \<in> carrier_mat 2 2" by simp
  have zd_c: "Pauli_Z\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using z_c by (rule dagger_carrier)
  have z\<rho>_c: "Pauli_Z * \<rho> \<in> carrier_mat 2 2"
    using z_c assms by (rule mult_carrier_mat)
  have z\<rho>zd_c: "Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using z\<rho>_c zd_c by (rule mult_carrier_mat)
  show ?thesis
    using assms z\<rho>zd_c by (auto simp: phase_flip_channel_def)
qed

lemma phase_flip_channel_trace_preserving:
  fixes p :: real
  assumes \<rho>_c: "\<rho> \<in> carrier_mat 2 2"
  shows "Tr (phase_flip_channel p \<rho>) = Tr \<rho>"
proof -
  have z_c: "Pauli_Z \<in> carrier_mat 2 2" by simp
  have zd_c: "Pauli_Z\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using z_c by (rule dagger_carrier)
  have z\<rho>_c: "Pauli_Z * \<rho> \<in> carrier_mat 2 2"
    using z_c \<rho>_c by (rule mult_carrier_mat)
  have z\<rho>zd_c: "Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using z\<rho>_c zd_c by (rule mult_carrier_mat)
  have zdz_eq: "(Pauli_Z\<^sup>\<dagger>) * Pauli_Z = 1\<^sub>m 2"
    using Pauli_Z_dagger Pauli_Z_squared by simp

  have tr_conj: "Tr (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>)) = Tr \<rho>"
  proof -
    have "Tr (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>)) = Tr (Pauli_Z\<^sup>\<dagger> * (Pauli_Z * \<rho>))"
    proof (rule Tr_cyclic)
      show "dim_col (Pauli_Z * \<rho>) = dim_row (Pauli_Z\<^sup>\<dagger>)"
        using z\<rho>_c zd_c by (metis carrier_matD)
      show "dim_row (Pauli_Z * \<rho>) = dim_col (Pauli_Z\<^sup>\<dagger>)"
        using z\<rho>_c zd_c by (metis carrier_matD)
    qed
    also have "\<dots> = Tr ((Pauli_Z\<^sup>\<dagger> * Pauli_Z) * \<rho>)"
      by (metis zd_c z_c \<rho>_c assoc_mult_mat)
    also have "\<dots> = Tr ((1\<^sub>m 2) * \<rho>)" using zdz_eq by simp
    also have "\<dots> = Tr \<rho>" using \<rho>_c by simp
    finally show ?thesis .
  qed

  have row_eq: "dim_row (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_row (complex_of_real p
                              \<cdot>\<^sub>m (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>)))"
    using \<rho>_c z\<rho>zd_c by (metis carrier_matD(1) index_smult_mat(2))
  have col_eq: "dim_col (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_col (complex_of_real p
                              \<cdot>\<^sub>m (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>)))"
    using \<rho>_c z\<rho>zd_c by (metis carrier_matD(2) index_smult_mat(3))
  have "Tr (phase_flip_channel p \<rho>)
          = Tr (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
            + Tr (complex_of_real p \<cdot>\<^sub>m (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>)))"
    unfolding phase_flip_channel_def
    using row_eq col_eq by (rule Tr_add)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>))"
    by (simp add: Tr_smult)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr \<rho>"
    using tr_conj by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) * Tr \<rho>"
    by (simp add: ring_distribs)
  also have "\<dots> = 1 * Tr \<rho>" by simp
  also have "\<dots> = Tr \<rho>" by simp
  finally show ?thesis .
qed

lemma phase_flip_channel_psd:
  fixes p :: real
  assumes p_nn:    "0 \<le> p"
      and p_le_1:  "p \<le> 1"
      and \<rho>_c:    "\<rho> \<in> carrier_mat 2 2"
      and \<rho>_psd:  "psd \<rho>"
  shows "psd (phase_flip_channel p \<rho>)"
proof -
  have z_c: "Pauli_Z \<in> carrier_mat 2 2" by simp
  have zd_c: "Pauli_Z\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using z_c by (rule dagger_carrier)
  have z\<rho>_c: "Pauli_Z * \<rho> \<in> carrier_mat 2 2"
    using z_c \<rho>_c by (rule mult_carrier_mat)
  have z\<rho>zd_c: "Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using z\<rho>_c zd_c by (rule mult_carrier_mat)
  have one_minus_nn: "0 \<le> 1 - p" using p_le_1 by simp

  have conj_psd: "psd (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>))"
  proof -
    obtain Q where Q_c:    "Q \<in> carrier_mat 2 2"
               and Q_psd:  "psd Q"
               and Q_sq:   "Q * Q = \<rho>"
      using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
    have Q_dagger: "Q\<^sup>\<dagger> = Q"
      using Q_psd by (simp add: psd_def hermitian_def)
    have ZQ_c: "Pauli_Z * Q \<in> carrier_mat 2 2"
      using z_c Q_c by (rule mult_carrier_mat)
    have ZQd_c: "(Pauli_Z * Q)\<^sup>\<dagger> \<in> carrier_mat 2 2"
      using ZQ_c by (rule dagger_carrier)
    have eq: "Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>) = (Pauli_Z * Q) * ((Pauli_Z * Q)\<^sup>\<dagger>)"
    proof -
      have dim_eq: "dim_col Pauli_Z = dim_row Q"
        using z_c Q_c by (metis carrier_matD)
      have dagprod: "(Pauli_Z * Q)\<^sup>\<dagger> = (Q\<^sup>\<dagger>) * (Pauli_Z\<^sup>\<dagger>)"
        using dim_eq by (rule dagger_of_prod)
      hence dagprod': "(Pauli_Z * Q)\<^sup>\<dagger> = Q * (Pauli_Z\<^sup>\<dagger>)"
        using Q_dagger by simp
      have "(Pauli_Z * Q) * ((Pauli_Z * Q)\<^sup>\<dagger>)
              = (Pauli_Z * Q) * (Q * (Pauli_Z\<^sup>\<dagger>))"
        using dagprod' by simp
      also have "\<dots> = Pauli_Z * Q * Q * (Pauli_Z\<^sup>\<dagger>)"
        using z_c Q_c zd_c by (metis assoc_mult_mat mult_carrier_mat)
      also have "\<dots> = Pauli_Z * (Q * Q) * (Pauli_Z\<^sup>\<dagger>)"
        using z_c Q_c by (metis assoc_mult_mat)
      also have "\<dots> = Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>)"
        using Q_sq by simp
      finally show ?thesis by simp
    qed
    have psd_dd: "psd (((Pauli_Z * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((Pauli_Z * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF ZQd_c] .
    have dd_eq: "(Pauli_Z * Q)\<^sup>\<dagger>\<^sup>\<dagger> = Pauli_Z * Q"
      using ZQ_c by (simp add: dagger_of_dagger_is_id)
    have "psd ((Pauli_Z * Q) * ((Pauli_Z * Q)\<^sup>\<dagger>))"
      using psd_dd dd_eq by simp
    thus ?thesis using eq by simp
  qed

  have term1_psd: "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)"
    using one_minus_nn \<rho>_psd \<rho>_c by (rule psd_smult_nonneg)
  have term2_psd: "psd (complex_of_real p \<cdot>\<^sub>m (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>)))"
    using p_nn conj_psd z\<rho>zd_c by (rule psd_smult_nonneg)

  have term1_c: "complex_of_real (1 - p) \<cdot>\<^sub>m \<rho> \<in> carrier_mat 2 2"
    using \<rho>_c by simp
  have term2_c: "complex_of_real p \<cdot>\<^sub>m (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>))
                   \<in> carrier_mat 2 2"
    using z\<rho>zd_c by simp

  have "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
              + complex_of_real p \<cdot>\<^sub>m (Pauli_Z * \<rho> * (Pauli_Z\<^sup>\<dagger>)))"
    using term1_psd term2_psd term1_c term2_c by (rule psd_add_psd)
  thus ?thesis by (simp add: phase_flip_channel_def)
qed


subsection \<open>Unitary-conjugation channels\<close>

text \<open>For a unitary $U\in M_n$ and $0\le p\le1$, $\rho\mapsto(1-p)\rho+pU\rho U^\dagger$ is trace
preserving and positive; the bit-flip and phase-flip channels are the instances $U=X$, $U=Z$.\<close>

definition unitary_conj_channel ::
  "complex Matrix.mat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "unitary_conj_channel U p \<rho> \<equiv>
     complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
     + complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>))"

lemma unitary_conj_channel_carrier:
  assumes U_c: "U \<in> carrier_mat n n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "unitary_conj_channel U p \<rho> \<in> carrier_mat n n"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have U\<rho>_c: "U * \<rho> \<in> carrier_mat n n"
    using U_c \<rho>_c by (rule mult_carrier_mat)
  have U\<rho>Ud_c: "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  show ?thesis
    using \<rho>_c U\<rho>Ud_c by (auto simp: unitary_conj_channel_def)
qed

lemma unitary_conj_channel_trace_preserving:
  fixes p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "Tr (unitary_conj_channel U p \<rho>) = Tr \<rho>"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have U\<rho>_c: "U * \<rho> \<in> carrier_mat n n"
    using U_c \<rho>_c by (rule mult_carrier_mat)
  have U\<rho>Ud_c: "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  have UdU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n"
    using U_unit U_c by (auto simp: unitary_def)

  have tr_conj: "Tr (U * \<rho> * (U\<^sup>\<dagger>)) = Tr \<rho>"
  proof -
    have "Tr (U * \<rho> * (U\<^sup>\<dagger>)) = Tr (U\<^sup>\<dagger> * (U * \<rho>))"
    proof (rule Tr_cyclic)
      show "dim_col (U * \<rho>) = dim_row (U\<^sup>\<dagger>)"
        using U\<rho>_c Ud_c by (metis carrier_matD)
      show "dim_row (U * \<rho>) = dim_col (U\<^sup>\<dagger>)"
        using U\<rho>_c Ud_c by (metis carrier_matD)
    qed
    also have "\<dots> = Tr ((U\<^sup>\<dagger> * U) * \<rho>)"
      by (metis Ud_c U_c \<rho>_c assoc_mult_mat)
    also have "\<dots> = Tr ((1\<^sub>m n) * \<rho>)" using UdU by simp
    also have "\<dots> = Tr \<rho>" using \<rho>_c by simp
    finally show ?thesis.
  qed

  have row_eq: "dim_row (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_row (complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    using \<rho>_c U\<rho>Ud_c by (metis carrier_matD(1) index_smult_mat(2))
  have col_eq: "dim_col (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_col (complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    using \<rho>_c U\<rho>Ud_c by (metis carrier_matD(2) index_smult_mat(3))
  have "Tr (unitary_conj_channel U p \<rho>)
          = Tr (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
            + Tr (complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    unfolding unitary_conj_channel_def
    using row_eq col_eq by (rule Tr_add)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr (U * \<rho> * (U\<^sup>\<dagger>))"
    by (simp add: Tr_smult)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr \<rho>"
    using tr_conj by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) * Tr \<rho>"
    by (simp add: ring_distribs)
  also have "\<dots> = 1 * Tr \<rho>" by simp
  also have "\<dots> = Tr \<rho>" by simp
  finally show ?thesis.
qed

lemma unitary_conj_channel_psd:
  fixes p :: real
  assumes p_nn:    "0 \<le> p"
      and p_le_1:  "p \<le> 1"
      and U_c:    "U \<in> carrier_mat n n"
      and \<rho>_c:    "\<rho> \<in> carrier_mat n n"
      and \<rho>_psd:  "psd \<rho>"
  shows "psd (unitary_conj_channel U p \<rho>)"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have U\<rho>_c: "U * \<rho> \<in> carrier_mat n n"
    using U_c \<rho>_c by (rule mult_carrier_mat)
  have U\<rho>Ud_c: "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  have one_minus_nn: "0 \<le> 1 - p" using p_le_1 by simp

  have conj_psd: "psd (U * \<rho> * (U\<^sup>\<dagger>))"
  proof -
    obtain Q where Q_c:    "Q \<in> carrier_mat n n"
               and Q_psd:  "psd Q"
               and Q_sq:   "Q * Q = \<rho>"
      using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
    have Q_dagger: "Q\<^sup>\<dagger> = Q"
      using Q_psd by (simp add: psd_def hermitian_def)
    have UQ_c: "U * Q \<in> carrier_mat n n"
      using U_c Q_c by (rule mult_carrier_mat)
    have UQd_c: "(U * Q)\<^sup>\<dagger> \<in> carrier_mat n n"
      using UQ_c by (rule dagger_carrier)
    have eq: "U * \<rho> * (U\<^sup>\<dagger>) = (U * Q) * ((U * Q)\<^sup>\<dagger>)"
    proof -
      have dim_eq: "dim_col U = dim_row Q"
        using U_c Q_c by (metis carrier_matD)
      have dagprod: "(U * Q)\<^sup>\<dagger> = (Q\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
        using dim_eq by (rule dagger_of_prod)
      hence dagprod': "(U * Q)\<^sup>\<dagger> = Q * (U\<^sup>\<dagger>)"
        using Q_dagger by simp
      have "(U * Q) * ((U * Q)\<^sup>\<dagger>) = (U * Q) * (Q * (U\<^sup>\<dagger>))"
        using dagprod' by simp
      also have "\<dots> = U * Q * Q * (U\<^sup>\<dagger>)"
        using U_c Q_c Ud_c by (metis assoc_mult_mat mult_carrier_mat)
      also have "\<dots> = U * (Q * Q) * (U\<^sup>\<dagger>)"
        using U_c Q_c by (metis assoc_mult_mat)
      also have "\<dots> = U * \<rho> * (U\<^sup>\<dagger>)" using Q_sq by simp
      finally show ?thesis by simp
    qed
    have psd_dd: "psd (((U * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((U * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF UQd_c] .
    have dd_eq: "(U * Q)\<^sup>\<dagger>\<^sup>\<dagger> = U * Q"
      using UQ_c by (simp add: dagger_of_dagger_is_id)
    have "psd ((U * Q) * ((U * Q)\<^sup>\<dagger>))"
      using psd_dd dd_eq by simp
    thus ?thesis using eq by simp
  qed

  have term1_psd: "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)"
    using one_minus_nn \<rho>_psd \<rho>_c by (rule psd_smult_nonneg)
  have term2_psd: "psd (complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    using p_nn conj_psd U\<rho>Ud_c by (rule psd_smult_nonneg)
  have term1_c: "complex_of_real (1 - p) \<cdot>\<^sub>m \<rho> \<in> carrier_mat n n"
    using \<rho>_c by simp
  have term2_c: "complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)) \<in> carrier_mat n n"
    using U\<rho>Ud_c by simp
  have "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
              + complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    using term1_psd term2_psd term1_c term2_c by (rule psd_add_psd)
  thus ?thesis by (simp add: unitary_conj_channel_def)
qed


lemma bit_flip_eq_unitary_conj:
  "bit_flip_channel p \<rho> = unitary_conj_channel Pauli_X p \<rho>"
  by (simp add: bit_flip_channel_def unitary_conj_channel_def)

lemma phase_flip_eq_unitary_conj:
  "phase_flip_channel p \<rho> = unitary_conj_channel Pauli_Z p \<rho>"
  by (simp add: phase_flip_channel_def unitary_conj_channel_def)


subsection \<open>The bit-phase-flip channel and the identity channel\<close>

definition bit_phase_flip_channel ::
  "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "bit_phase_flip_channel p \<rho> \<equiv> unitary_conj_channel Pauli_Y p \<rho>"

lemma bit_phase_flip_channel_carrier:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "bit_phase_flip_channel p \<rho> \<in> carrier_mat 2 2"
  unfolding bit_phase_flip_channel_def
  using Pauli_Y_carrier assms
  by (rule unitary_conj_channel_carrier)

lemma bit_phase_flip_channel_trace_preserving:
  fixes p :: real
  assumes \<rho>_c: "\<rho> \<in> carrier_mat 2 2"
  shows "Tr (bit_phase_flip_channel p \<rho>) = Tr \<rho>"
  unfolding bit_phase_flip_channel_def
  using Pauli_Y_carrier Pauli_Y_unitary \<rho>_c
  by (rule unitary_conj_channel_trace_preserving)

lemma bit_phase_flip_channel_psd:
  fixes p :: real
  assumes p_nn:    "0 \<le> p"
      and p_le_1:  "p \<le> 1"
      and \<rho>_c:    "\<rho> \<in> carrier_mat 2 2"
      and \<rho>_psd:  "psd \<rho>"
  shows "psd (bit_phase_flip_channel p \<rho>)"
  unfolding bit_phase_flip_channel_def
  using p_nn p_le_1 Pauli_Y_carrier \<rho>_c \<rho>_psd
  by (rule unitary_conj_channel_psd)



definition identity_channel ::
  "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "identity_channel \<rho> \<equiv> \<rho>"

lemma identity_channel_carrier:
  "\<rho> \<in> carrier_mat n n \<Longrightarrow> identity_channel \<rho> \<in> carrier_mat n n"
  by (simp add: identity_channel_def)

lemma identity_channel_trace_preserving:
  "\<rho> \<in> carrier_mat n n \<Longrightarrow> Tr (identity_channel \<rho>) = Tr \<rho>"
  by (simp add: identity_channel_def)

lemma identity_channel_psd:
  "\<rho> \<in> carrier_mat n n \<Longrightarrow> psd \<rho> \<Longrightarrow> psd (identity_channel \<rho>)"
  by (simp add: identity_channel_def)


lemma identity_channel_eq_unitary_conj_zero:
  assumes \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "identity_channel \<rho> = unitary_conj_channel (1\<^sub>m n) 0 \<rho>"
proof -
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have Id_c: "(1\<^sub>m n :: complex Matrix.mat)\<^sup>\<dagger> \<in> carrier_mat n n"
    using I_c by (rule dagger_carrier)
  have I\<rho>_c: "(1\<^sub>m n :: complex Matrix.mat) * \<rho> \<in> carrier_mat n n"
    using I_c \<rho>_c by (rule mult_carrier_mat)
  have I\<rho>Id_c: "(1\<^sub>m n :: complex Matrix.mat) * \<rho> * ((1\<^sub>m n)\<^sup>\<dagger>)
                  \<in> carrier_mat n n"
    using I\<rho>_c Id_c by (rule mult_carrier_mat)
  have one_smul: "(1 :: complex) \<cdot>\<^sub>m \<rho> = \<rho>"
    using \<rho>_c by (intro eq_matI) auto
  have zero_smul: "(0 :: complex) \<cdot>\<^sub>m
                     ((1\<^sub>m n :: complex Matrix.mat) * \<rho>
                      * ((1\<^sub>m n)\<^sup>\<dagger>))
                    = 0\<^sub>m n n"
    using I\<rho>Id_c by (intro eq_matI) auto
  have rho_zero: "\<rho> + 0\<^sub>m n n = \<rho>"
    using \<rho>_c by (intro eq_matI) auto
  have "unitary_conj_channel (1\<^sub>m n) 0 \<rho>
          = (1 :: complex) \<cdot>\<^sub>m \<rho>
            + (0 :: complex) \<cdot>\<^sub>m
                ((1\<^sub>m n :: complex Matrix.mat) * \<rho> * ((1\<^sub>m n)\<^sup>\<dagger>))"
    by (simp add: unitary_conj_channel_def)
  also have "\<dots> = \<rho> + 0\<^sub>m n n" using one_smul zero_smul by simp
  also have "\<dots> = \<rho>" using rho_zero .
  finally show ?thesis by (simp add: identity_channel_def)
qed


subsection \<open>Composition of channels\<close>

lemma compose_trace_preserving:
  assumes F_tp:    "trace_preserving n F"
      and G_tp:    "trace_preserving n G"
      and F_range: "\<forall>\<rho>. \<rho> \<in> carrier_mat n n \<longrightarrow> F \<rho> \<in> carrier_mat n n"
  shows "trace_preserving n (\<lambda>\<rho>. G (F \<rho>))"
proof (unfold trace_preserving_def, intro allI impI)
  fix \<rho> :: "complex Matrix.mat"
  assume \<rho>_c: "\<rho> \<in> carrier_mat n n"
  have F\<rho>_c: "F \<rho> \<in> carrier_mat n n" using F_range \<rho>_c by blast
  have "Tr (G (F \<rho>)) = Tr (F \<rho>)"
    using G_tp F\<rho>_c by (simp add: trace_preserving_def)
  also have "\<dots> = Tr \<rho>"
    using F_tp \<rho>_c by (simp add: trace_preserving_def)
  finally show "Tr (G (F \<rho>)) = Tr \<rho>" .
qed


lemma identity_channel_compose_left:
  "(\<lambda>\<rho>. identity_channel (F \<rho>)) = F"
  by (simp add: identity_channel_def)

lemma identity_channel_compose_right:
  "(\<lambda>\<rho>. F (identity_channel \<rho>)) = F"
  by (simp add: identity_channel_def)



lemma compose_unital_map:
  assumes F_un: "unital_map n n F"
      and G_un: "unital_map n n G"
  shows "unital_map n n (\<lambda>\<rho>. F (G \<rho>))"
proof -
  have G_one: "G (1\<^sub>m n) = 1\<^sub>m n"
    using G_un by (simp add: unital_map_def)
  have F_one: "F (1\<^sub>m n) = 1\<^sub>m n"
    using F_un by (simp add: unital_map_def)
  have "F (G (1\<^sub>m n)) = F (1\<^sub>m n)" using G_one by simp
  also have "\<dots> = 1\<^sub>m n" using F_one by simp
  finally show ?thesis by (simp add: unital_map_def)
qed


lemma identity_channel_unital: "unital_map n n identity_channel"
  by (simp add: unital_map_def identity_channel_def)

lemma identity_channel_trace_preserving_full:
  "trace_preserving n identity_channel"
  by (simp add: trace_preserving_def identity_channel_def)


lemma identity_channel_completely_positive:
  assumes "0 < n"
  shows "completely_positive n n identity_channel"
proof -
  have amp_eq:
    "\<And>p X. 0 < p \<Longrightarrow> X \<in> carrier_mat (p*n) (p*n)
      \<Longrightarrow> amplification n n p identity_channel X = X"
  proof -
    fix p :: nat and X :: "complex Matrix.mat"
    assume p_pos: "0 < p" and X_c: "X \<in> carrier_mat (p*n) (p*n)"
    show "amplification n n p identity_channel X = X"
    proof (rule eq_matI)
      show "dim_row (amplification n n p identity_channel X) = dim_row X"
        using X_c by (simp add: amplification_def)
      show "dim_col (amplification n n p identity_channel X) = dim_col X"
        using X_c by (simp add: amplification_def)
    next
      fix i j
      assume i: "i < dim_row X" and j: "j < dim_col X"
      hence ij: "i < p*n" "j < p*n" using X_c by simp_all
      have imodn: "i mod n < n" and jmodn: "j mod n < n"
        using assms by simp_all
      have iqn: "i div n < p" using ij(1) assms
        by (simp add: less_mult_imp_div_less)
      have jqn: "j div n < p" using ij(2) assms
        by (simp add: less_mult_imp_div_less)
      have idn: "i div n * n + i mod n = i" by simp
      have jdn: "j div n * n + j mod n = j" by simp
      have block_idx:
        "block_of_mat n X (i div n) (j div n) $$ (i mod n, j mod n)
         = X $$ (i, j)"
        using imodn jmodn iqn jqn ij X_c
        by (simp add: block_of_mat_def idn jdn)
      show "amplification n n p identity_channel X $$ (i, j)
              = X $$ (i, j)"
        using ij block_idx
        by (simp add: amplification_def identity_channel_def)
    qed
  qed
  show ?thesis
    unfolding completely_positive_def p_positive_def
    using amp_eq by auto
qed


subsection \<open>Conjugation channels are completely positive\<close>

definition conjugation_channel ::
  "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "conjugation_channel U \<rho> \<equiv> U * \<rho> * (U\<^sup>\<dagger>)"

lemma conjugation_channel_eq_kraus:
  assumes U_c: "U \<in> carrier_mat d n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "conjugation_channel U \<rho> = kraus_map_dim d [U] \<rho>"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n d"
    using U_c by (rule dagger_carrier)
  have U\<rho>_c: "U * \<rho> \<in> carrier_mat d n"
    using U_c \<rho>_c by (rule mult_carrier_mat)
  have U\<rho>Ud_c: "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat d d"
    using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  have add_zero: "U * \<rho> * (U\<^sup>\<dagger>) + 0\<^sub>m d d = U * \<rho> * (U\<^sup>\<dagger>)"
    using U\<rho>Ud_c by (intro eq_matI) auto
  show ?thesis
    unfolding conjugation_channel_def
    by (simp add: add_zero)
qed

lemma conjugation_channel_cp:
  assumes U_c: "U \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (kraus_map_dim d [U])"
proof -
  have Ws_c: "\<forall>W \<in> set [U]. W \<in> carrier_mat d n" using U_c by simp
  show ?thesis using kraus_cp_no_tp[OF Ws_c npos dpos] .
qed



lemma identity_channel_UCP:
  assumes "0 < n"
  shows "identity_channel \<in> UCP n n"
  unfolding UCP_def
  using identity_channel_completely_positive[OF assms]
        identity_channel_unital
  by simp

lemma identity_channel_CPTP:
  assumes "0 < n"
  shows "identity_channel \<in> CPTP n n"
  unfolding CPTP_def
  using identity_channel_completely_positive[OF assms]
        identity_channel_trace_preserving_full
  by simp




lemma map_conj_cp:
  assumes U_c: "U \<in> carrier_mat d n"
      and U_range: "\<forall>\<rho>. \<rho> \<in> carrier_mat n n
                       \<longrightarrow> U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat d d"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>))"
proof -
  have Ws_c: "\<forall>W \<in> set [U]. W \<in> carrier_mat d n" using U_c by simp
  let ?F = "\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)"
  let ?G = "kraus_map_dim d [U]"
  have agree:
    "\<And>\<rho>. \<rho> \<in> carrier_mat n n \<Longrightarrow> ?F \<rho> = ?G \<rho>"
    using conjugation_channel_eq_kraus[OF U_c]
    by (simp add: conjugation_channel_def)
  have G_cp: "completely_positive n d ?G"
    using kraus_cp_no_tp[OF Ws_c npos dpos] .
  show ?thesis
  proof (unfold completely_positive_def p_positive_def, intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and X_c: "X \<in> carrier_mat (p*n) (p*n)"
       and X_psd: "psd X"
    have amp_eq:
      "amplification n d p ?F X = amplification n d p ?G X"
    proof (rule eq_matI)
      show "dim_row (amplification n d p ?F X)
              = dim_row (amplification n d p ?G X)"
        by (simp add: amplification_def)
      show "dim_col (amplification n d p ?F X)
              = dim_col (amplification n d p ?G X)"
        by (simp add: amplification_def)
    next
      fix i j
      assume "i < dim_row (amplification n d p ?G X)"
             "j < dim_col (amplification n d p ?G X)"
      hence ij: "i < p*d" "j < p*d"
        by (simp_all add: amplification_def)
      have B_c: "block_of_mat n X (i div d) (j div d) \<in> carrier_mat n n"
        by (simp add: block_of_mat_def)
      have eq: "?F (block_of_mat n X (i div d) (j div d))
                = ?G (block_of_mat n X (i div d) (j div d))"
        using agree[OF B_c] .
      show "amplification n d p ?F X $$ (i, j)
              = amplification n d p ?G X $$ (i, j)"
        using ij eq by (simp add: amplification_def)
    qed
    have psd_G: "psd (amplification n d p ?G X)"
      using G_cp ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    show "psd (amplification n d p ?F X)"
      using amp_eq psd_G by simp
  qed
qed


lemma map_conj_unital:
  fixes U :: "complex Matrix.mat"
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
  shows "U * (1\<^sub>m n) * (U\<^sup>\<dagger>) = 1\<^sub>m n"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have UI: "U * (1\<^sub>m n) = U" using U_c by simp
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using U_unit U_c by (auto simp: unitary_def)
  have "U * (1\<^sub>m n) * (U\<^sup>\<dagger>) = U * (U\<^sup>\<dagger>)" using UI by simp
  also have "\<dots> = 1\<^sub>m n" using UUd .
  finally show ?thesis .
qed


subsection \<open>Unitary-conjugation channels are UCP and CPTP\<close>

lemma map_conj_in_UCP:
  fixes U :: "complex Matrix.mat"
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and npos: "0 < n"
  shows "(\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)) \<in> UCP n n"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have range_full:
    "\<forall>\<rho>. \<rho> \<in> carrier_mat n n \<longrightarrow> U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
  proof (intro allI impI)
    fix \<rho> :: "complex Matrix.mat" assume \<rho>_c: "\<rho> \<in> carrier_mat n n"
    have U\<rho>_c: "U * \<rho> \<in> carrier_mat n n"
      using U_c \<rho>_c by (rule mult_carrier_mat)
    show "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
      using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  qed
  have cp: "completely_positive n n (\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>))"
    using map_conj_cp[OF U_c range_full npos npos] .
  have un: "unital_map n n (\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>))"
    using map_conj_unital[OF U_c U_unit]
    by (simp add: unital_map_def)
  show ?thesis using cp un by (simp add: UCP_def)
qed

lemma unitary_conj_channel_in_UCP:
  fixes U :: "complex Matrix.mat" and p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and p_nn: "0 \<le> p"
      and p_le: "p \<le> 1"
      and npos: "0 < n"
  shows "unitary_conj_channel U p \<in> UCP n n"
proof -
  let ?Phi1 = "identity_channel :: complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  let ?Phi2 = "\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)"
  let ?t = "1 - p"
  have t_nn: "0 \<le> ?t" using p_le by simp
  have t_le: "?t \<le> 1" using p_nn by simp
  have Phi1_in: "?Phi1 \<in> UCP n n" using identity_channel_UCP[OF npos] .
  have Phi2_in: "?Phi2 \<in> UCP n n"
    using map_conj_in_UCP[OF U_c U_unit npos] .
  have r1: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> ?Phi1 X \<in> carrier_mat n n"
    by (simp add: identity_channel_def)
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have r2: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> ?Phi2 X \<in> carrier_mat n n"
  proof (intro allI impI)
    fix X :: "complex Matrix.mat" assume X_c: "X \<in> carrier_mat n n"
    have UX_c: "U * X \<in> carrier_mat n n"
      using U_c X_c by (rule mult_carrier_mat)
    show "U * X * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
      using UX_c Ud_c by (rule mult_carrier_mat)
  qed
  have convex_ucp:
    "(\<lambda>X. complex_of_real ?t \<cdot>\<^sub>m ?Phi1 X
          + (1 - complex_of_real ?t) \<cdot>\<^sub>m ?Phi2 X) \<in> UCP n n"
    using UCP_convex[OF t_nn t_le Phi1_in Phi2_in r1 r2 npos] .
  (* Match the convex form to unitary_conj_channel. *)
  have shift: "(1 :: complex) - complex_of_real (1 - p) = complex_of_real p"
    by simp
  have id_eq: "\<And>X. ?Phi1 X = X" by (simp add: identity_channel_def)
  have func_eq:
    "(\<lambda>X. complex_of_real ?t \<cdot>\<^sub>m ?Phi1 X
          + (1 - complex_of_real ?t) \<cdot>\<^sub>m ?Phi2 X)
       = unitary_conj_channel U p"
  proof (rule ext)
    fix X :: "complex Matrix.mat"
    have "complex_of_real ?t \<cdot>\<^sub>m ?Phi1 X
            + (1 - complex_of_real ?t) \<cdot>\<^sub>m ?Phi2 X
          = complex_of_real (1 - p) \<cdot>\<^sub>m X
            + complex_of_real p \<cdot>\<^sub>m (U * X * (U\<^sup>\<dagger>))"
      using shift id_eq by simp
    also have "\<dots> = unitary_conj_channel U p X"
      by (simp add: unitary_conj_channel_def)
    finally show "complex_of_real ?t \<cdot>\<^sub>m ?Phi1 X
                    + (1 - complex_of_real ?t) \<cdot>\<^sub>m ?Phi2 X
                  = unitary_conj_channel U p X" .
  qed
  show ?thesis using convex_ucp func_eq by simp
qed


lemma unitary_conj_channel_in_CPTP:
  fixes U :: "complex Matrix.mat" and p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and p_nn: "0 \<le> p"
      and p_le: "p \<le> 1"
      and npos: "0 < n"
  shows "unitary_conj_channel U p \<in> CPTP n n"
proof -
  have ucp: "unitary_conj_channel U p \<in> UCP n n"
    using unitary_conj_channel_in_UCP[OF U_c U_unit p_nn p_le npos] .
  have cp: "completely_positive n n (unitary_conj_channel U p)"
    using ucp by (simp add: UCP_def)
  have tp: "trace_preserving n (unitary_conj_channel U p)"
    unfolding trace_preserving_def
    by (intro allI impI;
        rule unitary_conj_channel_trace_preserving[OF U_c U_unit])
  show ?thesis using cp tp by (simp add: CPTP_def)
qed


subsection \<open>The Pauli channels are UCP and CPTP\<close>

lemma bit_flip_channel_eq:
  "bit_flip_channel p = unitary_conj_channel Pauli_X p"
  by (rule ext) (simp add: bit_flip_eq_unitary_conj)

lemma phase_flip_channel_eq:
  "phase_flip_channel p = unitary_conj_channel Pauli_Z p"
  by (rule ext) (simp add: phase_flip_eq_unitary_conj)

lemma bit_phase_flip_channel_eq:
  "bit_phase_flip_channel p = unitary_conj_channel Pauli_Y p"
  by (rule ext) (simp add: bit_phase_flip_channel_def)

text \<open>All three are unitary-conjugation channels $\rho\mapsto(1-p)\rho+pU\rho U^*$ with $U=X,Z,Y$, whose
Kraus operators $\sqrt{1-p}\,I$, $\sqrt p\,U$ satisfy
\[ (1-p)I+p\,U^*U=I=(1-p)I+p\,UU^*, \]
so each is both unital and trace preserving.\<close>

lemma bit_flip_channel_UCP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "bit_flip_channel p \<in> UCP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_UCP[OF Pauli_X_carrier Pauli_X_unitary
                                         p_nn p_le npos]
    by (simp add: bit_flip_channel_eq)
qed

lemma bit_flip_channel_CPTP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "bit_flip_channel p \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_CPTP[OF Pauli_X_carrier Pauli_X_unitary
                                          p_nn p_le npos]
    by (simp add: bit_flip_channel_eq)
qed

lemma phase_flip_channel_UCP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "phase_flip_channel p \<in> UCP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_UCP[OF Pauli_Z_carrier Pauli_Z_unitary
                                         p_nn p_le npos]
    by (simp add: phase_flip_channel_eq)
qed

lemma phase_flip_channel_CPTP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "phase_flip_channel p \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_CPTP[OF Pauli_Z_carrier Pauli_Z_unitary
                                          p_nn p_le npos]
    by (simp add: phase_flip_channel_eq)
qed

lemma bit_phase_flip_channel_UCP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "bit_phase_flip_channel p \<in> UCP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_UCP[OF Pauli_Y_carrier Pauli_Y_unitary
                                         p_nn p_le npos]
    by (simp add: bit_phase_flip_channel_eq)
qed

lemma bit_phase_flip_channel_CPTP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "bit_phase_flip_channel p \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_CPTP[OF Pauli_Y_carrier Pauli_Y_unitary
                                          p_nn p_le npos]
    by (simp add: bit_phase_flip_channel_eq)
qed


subsection \<open>Pauli matrices as Kraus operators\<close>

lemma Pauli_X_kraus_operators:
  "kraus_operators 2 2 [Pauli_X]"
proof -
  have X_c: "Pauli_X \<in> carrier_mat 2 2" by simp
  have X_dag: "Pauli_X\<^sup>\<dagger> = Pauli_X" by (rule Pauli_X_dagger)
  have X_sq: "Pauli_X * Pauli_X = 1\<^sub>m 2" by (rule Pauli_X_squared)
  have I_c: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp
  have all_in: "\<forall>W \<in> set [Pauli_X]. W \<in> carrier_mat 2 2"
    using X_c by simp
  have step:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [Pauli_X] (0\<^sub>m 2 2)
       = Pauli_X * Pauli_X + 0\<^sub>m 2 2"
    using X_dag by simp
  also have "\<dots> = 1\<^sub>m 2 + 0\<^sub>m 2 2" using X_sq by simp
  also have "\<dots> = 1\<^sub>m 2"
    using I_c by (intro eq_matI) auto
  finally have sum_eq:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [Pauli_X] (0\<^sub>m 2 2) = 1\<^sub>m 2" .
  show ?thesis
    unfolding kraus_operators_def
    using all_in sum_eq by blast
qed

lemma Pauli_Y_kraus_operators:
  "kraus_operators 2 2 [Pauli_Y]"
proof -
  have Y_c: "Pauli_Y \<in> carrier_mat 2 2" by simp
  have Y_dag: "Pauli_Y\<^sup>\<dagger> = Pauli_Y" by (rule Pauli_Y_dagger)
  have Y_sq: "Pauli_Y * Pauli_Y = 1\<^sub>m 2" by (rule Pauli_Y_squared)
  have I_c: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp
  have all_in: "\<forall>W \<in> set [Pauli_Y]. W \<in> carrier_mat 2 2"
    using Y_c by simp
  have step:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [Pauli_Y] (0\<^sub>m 2 2)
       = Pauli_Y * Pauli_Y + 0\<^sub>m 2 2"
    using Y_dag by simp
  also have "\<dots> = 1\<^sub>m 2 + 0\<^sub>m 2 2" using Y_sq by simp
  also have "\<dots> = 1\<^sub>m 2"
    using I_c by (intro eq_matI) auto
  finally have sum_eq:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [Pauli_Y] (0\<^sub>m 2 2) = 1\<^sub>m 2" .
  show ?thesis
    unfolding kraus_operators_def
    using all_in sum_eq by blast
qed

lemma Pauli_Z_kraus_operators:
  "kraus_operators 2 2 [Pauli_Z]"
proof -
  have Z_c: "Pauli_Z \<in> carrier_mat 2 2" by simp
  have Z_dag: "Pauli_Z\<^sup>\<dagger> = Pauli_Z" by (rule Pauli_Z_dagger)
  have Z_sq: "Pauli_Z * Pauli_Z = 1\<^sub>m 2" by (rule Pauli_Z_squared)
  have I_c: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp
  have all_in: "\<forall>W \<in> set [Pauli_Z]. W \<in> carrier_mat 2 2"
    using Z_c by simp
  have step:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [Pauli_Z] (0\<^sub>m 2 2)
       = Pauli_Z * Pauli_Z + 0\<^sub>m 2 2"
    using Z_dag by simp
  also have "\<dots> = 1\<^sub>m 2 + 0\<^sub>m 2 2" using Z_sq by simp
  also have "\<dots> = 1\<^sub>m 2"
    using I_c by (intro eq_matI) auto
  finally have sum_eq:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [Pauli_Z] (0\<^sub>m 2 2) = 1\<^sub>m 2" .
  show ?thesis
    unfolding kraus_operators_def
    using all_in sum_eq by blast
qed


subsection \<open>Kraus maps of Kraus-operator lists are CPTP\<close>

lemma kraus_is_trace_preserving:
  fixes Ws :: "complex Matrix.mat list"
  assumes Ws: "kraus_operators n d Ws"
  shows "trace_preserving n (kraus_map_dim d Ws)"
proof (unfold trace_preserving_def, intro allI impI)
  fix \<rho> :: "complex Matrix.mat"
  assume \<rho>_c: "\<rho> \<in> carrier_mat n n"
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    using Ws by (simp add: kraus_operators_def)
  have sum_eq: "sum_wdag_w n Ws = 1\<^sub>m n"
    using Ws by (simp add: kraus_operators_altdef)
  have "Tr (kraus_map_dim d Ws \<rho>) = Tr (sum_wdag_w n Ws * \<rho>)"
    using Tr_kraus_map_dim_as_wdagw[OF Ws_c \<rho>_c] .
  also have "\<dots> = Tr ((1\<^sub>m n) * \<rho>)" using sum_eq by simp
  also have "\<dots> = Tr \<rho>" using \<rho>_c by simp
  finally show "Tr (kraus_map_dim d Ws \<rho>) = Tr \<rho>" .
qed

lemma kraus_is_cptp:
  fixes Ws :: "complex Matrix.mat list"
  assumes Ws: "kraus_operators n d Ws"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "kraus_map_dim d Ws \<in> CPTP n d"
  unfolding CPTP_def
  using kraus_is_cp[OF Ws npos dpos] kraus_is_trace_preserving[OF Ws]
  by simp



lemma Pauli_X_kraus_map_CPTP:
  "kraus_map_dim 2 [Pauli_X] \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using kraus_is_cptp[OF Pauli_X_kraus_operators npos npos] .
qed

lemma Pauli_Y_kraus_map_CPTP:
  "kraus_map_dim 2 [Pauli_Y] \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using kraus_is_cptp[OF Pauli_Y_kraus_operators npos npos] .
qed

lemma Pauli_Z_kraus_map_CPTP:
  "kraus_map_dim 2 [Pauli_Z] \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using kraus_is_cptp[OF Pauli_Z_kraus_operators npos npos] .
qed



lemma identity_kraus_operators:
  "kraus_operators n n [1\<^sub>m n]"
proof -
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have I_dag: "(1\<^sub>m n :: complex Matrix.mat)\<^sup>\<dagger> = 1\<^sub>m n"
    by (intro eq_matI) (auto simp: dagger_def)
  have II: "(1\<^sub>m n :: complex Matrix.mat) * 1\<^sub>m n = 1\<^sub>m n"
    by (intro eq_matI) auto
  have all_in: "\<forall>W \<in> set [1\<^sub>m n :: complex Matrix.mat]. W \<in> carrier_mat n n"
    using I_c by simp
  have step:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [1\<^sub>m n :: complex Matrix.mat] (0\<^sub>m n n)
       = (1\<^sub>m n) * (1\<^sub>m n) + 0\<^sub>m n n"
    using I_dag by simp
  also have "\<dots> = 1\<^sub>m n + 0\<^sub>m n n" using II by simp
  also have "\<dots> = 1\<^sub>m n"
    using I_c by (intro eq_matI) auto
  finally have sum_eq:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [1\<^sub>m n :: complex Matrix.mat] (0\<^sub>m n n)
       = 1\<^sub>m n" .
  show ?thesis
    unfolding kraus_operators_def
    using all_in sum_eq by blast
qed

lemma identity_channel_eq_kraus_map_dim:
  fixes n :: nat
  assumes \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "identity_channel \<rho> = kraus_map_dim n [1\<^sub>m n] \<rho>"
proof -
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have I_dag: "(1\<^sub>m n :: complex Matrix.mat)\<^sup>\<dagger> = 1\<^sub>m n"
    by (intro eq_matI) (auto simp: dagger_def)
  have I\<rho>: "(1\<^sub>m n :: complex Matrix.mat) * \<rho> = \<rho>" using \<rho>_c by simp
  have I\<rho>I: "((1\<^sub>m n :: complex Matrix.mat) * \<rho>) * (1\<^sub>m n) = \<rho>"
    using \<rho>_c I\<rho> by simp
  have rho_zero: "\<rho> + 0\<^sub>m n n = \<rho>" using \<rho>_c by (intro eq_matI) auto
  have "kraus_map_dim n [1\<^sub>m n] \<rho>
          = (1\<^sub>m n) * \<rho> * ((1\<^sub>m n)\<^sup>\<dagger>) + 0\<^sub>m n n" by simp
  also have "\<dots> = (1\<^sub>m n) * \<rho> * (1\<^sub>m n) + 0\<^sub>m n n" using I_dag by simp
  also have "\<dots> = \<rho> + 0\<^sub>m n n" using I\<rho>I by simp
  also have "\<dots> = \<rho>" using rho_zero .
  finally show ?thesis
    by (simp add: identity_channel_def)
qed


subsection \<open>Concatenation of Kraus lists\<close>

lemma sum_wdag_w_append:
  fixes Ws Vs :: "complex Matrix.mat list"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "sum_wdag_w n (Ws @ Vs)
         = sum_wdag_w n Ws + sum_wdag_w n Vs"
  using Ws_c
proof (induction Ws)
  case Nil
  have Vs_sum_c: "sum_wdag_w n Vs \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Vs_c] .
  show ?case
    using Vs_sum_c
    by (intro eq_matI) (auto simp: sum_wdag_w_def)
next
  case (Cons W Ws)
  hence W_c: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n" by auto
  have Wd_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  have WdW_c: "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n"
    using Wd_c W_c by (rule mult_carrier_mat)
  have Ws_sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Ws_c'] .
  have Vs_sum_c: "sum_wdag_w n Vs \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Vs_c] .
  have IH: "sum_wdag_w n (Ws @ Vs)
              = sum_wdag_w n Ws + sum_wdag_w n Vs"
    using Cons.IH Ws_c' by simp

  have "sum_wdag_w n ((W # Ws) @ Vs)
          = (W\<^sup>\<dagger>) * W + sum_wdag_w n (Ws @ Vs)"
    by (simp add: sum_wdag_w_Cons)
  also have "\<dots> = (W\<^sup>\<dagger>) * W + (sum_wdag_w n Ws + sum_wdag_w n Vs)"
    using IH by simp
  also have "\<dots> = ((W\<^sup>\<dagger>) * W + sum_wdag_w n Ws) + sum_wdag_w n Vs"
    using WdW_c Ws_sum_c Vs_sum_c
    by simp
  also have "\<dots> = sum_wdag_w n (W # Ws) + sum_wdag_w n Vs"
    by (simp add: sum_wdag_w_Cons)
  finally show ?case.
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


subsection \<open>Fixed points of Pauli channels\<close>

lemma Pauli_X_conj_commute:
  fixes M :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat 2 2"
      and commute: "Pauli_X * M = M * Pauli_X"
  shows "Pauli_X * M * (Pauli_X\<^sup>\<dagger>) = M"
proof -
  have x_c: "Pauli_X \<in> carrier_mat 2 2" by simp
  have x_dag: "Pauli_X\<^sup>\<dagger> = Pauli_X" by (rule Pauli_X_dagger)
  have x_sq: "Pauli_X * Pauli_X = 1\<^sub>m 2" by (rule Pauli_X_squared)
  have "Pauli_X * M * (Pauli_X\<^sup>\<dagger>) = Pauli_X * M * Pauli_X"
    using x_dag by simp
  also have "\<dots> = (M * Pauli_X) * Pauli_X" using commute by simp
  also have "\<dots> = M * (Pauli_X * Pauli_X)"
    using x_c M_c by (metis assoc_mult_mat)
  also have "\<dots> = M * (1\<^sub>m 2)" using x_sq by simp
  also have "\<dots> = M" using M_c by simp
  finally show ?thesis.
qed

lemma bit_flip_channel_fixed_point_commute:
  fixes p :: real
  assumes M_c: "M \<in> carrier_mat 2 2"
      and commute: "Pauli_X * M = M * Pauli_X"
  shows "bit_flip_channel p M = M"
proof -
  have conj_eq: "Pauli_X * M * (Pauli_X\<^sup>\<dagger>) = M"
    using Pauli_X_conj_commute[OF M_c commute].
  have "bit_flip_channel p M
          = complex_of_real (1 - p) \<cdot>\<^sub>m M
            + complex_of_real p \<cdot>\<^sub>m M"
    unfolding bit_flip_channel_def using conj_eq by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) \<cdot>\<^sub>m M"
    using M_c by (rule add_smult_distrib_right_mat[symmetric])
  also have "\<dots> = (1 :: complex) \<cdot>\<^sub>m M" by simp
  also have "\<dots> = M" using M_c by (intro eq_matI, auto)
  finally show ?thesis .
qed


lemma Pauli_Z_conj_commute:
  fixes M :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat 2 2"
      and commute: "Pauli_Z * M = M * Pauli_Z"
  shows "Pauli_Z * M * (Pauli_Z\<^sup>\<dagger>) = M"
proof -
  have z_c: "Pauli_Z \<in> carrier_mat 2 2" by simp
  have z_dag: "Pauli_Z\<^sup>\<dagger> = Pauli_Z" by (rule Pauli_Z_dagger)
  have z_sq: "Pauli_Z * Pauli_Z = 1\<^sub>m 2" by (rule Pauli_Z_squared)
  have "Pauli_Z * M * (Pauli_Z\<^sup>\<dagger>) = Pauli_Z * M * Pauli_Z"
    using z_dag by simp
  also have "\<dots> = (M * Pauli_Z) * Pauli_Z" using commute by simp
  also have "\<dots> = M * (Pauli_Z * Pauli_Z)"
    using z_c M_c by (metis assoc_mult_mat)
  also have "\<dots> = M * (1\<^sub>m 2)" using z_sq by simp
  also have "\<dots> = M" using M_c by simp
  finally show ?thesis.
qed

lemma phase_flip_channel_fixed_point_commute:
  fixes p :: real
  assumes M_c: "M \<in> carrier_mat 2 2"
      and commute: "Pauli_Z * M = M * Pauli_Z"
  shows "phase_flip_channel p M = M"
proof -
  have conj_eq: "Pauli_Z * M * (Pauli_Z\<^sup>\<dagger>) = M"
    using Pauli_Z_conj_commute[OF M_c commute].
  have "phase_flip_channel p M
          = complex_of_real (1 - p) \<cdot>\<^sub>m M
            + complex_of_real p \<cdot>\<^sub>m M"
    unfolding phase_flip_channel_def using conj_eq by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) \<cdot>\<^sub>m M"
    using M_c by (rule add_smult_distrib_right_mat[symmetric])
  also have "\<dots> = (1 :: complex) \<cdot>\<^sub>m M" by simp
  also have "\<dots> = M" using M_c by (intro eq_matI) auto
  finally show ?thesis.
qed



lemma unitary_conj_channel_identity_op:
  fixes p :: real
  assumes \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "unitary_conj_channel (1\<^sub>m n) p \<rho> = \<rho>"
proof -
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have I_dag: "(1\<^sub>m n :: complex Matrix.mat)\<^sup>\<dagger> = 1\<^sub>m n"
    by (intro eq_matI, auto simp: dagger_def)
  have I\<rho>I: "(1\<^sub>m n :: complex Matrix.mat) * \<rho> * ((1\<^sub>m n)\<^sup>\<dagger>) = \<rho>"
    using \<rho>_c I_dag by simp
  have "unitary_conj_channel (1\<^sub>m n) p \<rho>
          = complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
            + complex_of_real p \<cdot>\<^sub>m \<rho>"
    unfolding unitary_conj_channel_def using I\<rho>I by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) \<cdot>\<^sub>m \<rho>"
    using \<rho>_c by (rule add_smult_distrib_right_mat[symmetric])
  also have "\<dots> = (1 :: complex) \<cdot>\<^sub>m \<rho>" by simp
  also have "\<dots> = \<rho>" using \<rho>_c by (intro eq_matI, auto)
  finally show ?thesis.
qed


lemma unitary_conj_channel_identity_op_eq:
  fixes p :: real
  shows "(\<lambda>\<rho>. if \<rho> \<in> carrier_mat n n
              then unitary_conj_channel (1\<^sub>m n) p \<rho> else identity_channel \<rho>)
         = identity_channel"
  by (rule ext, simp add: unitary_conj_channel_identity_op identity_channel_def)


subsection \<open>The maximally mixed state\<close>

definition maximally_mixed_state :: "nat \<Rightarrow> complex Matrix.mat" where
  "maximally_mixed_state n \<equiv> complex_of_real (1 / real n) \<cdot>\<^sub>m (1\<^sub>m n)"

lemma maximally_mixed_state_carrier [simp]:
  "maximally_mixed_state n \<in> carrier_mat n n"
  by (simp add: maximally_mixed_state_def)

lemma Tr_one_mat:
  "Tr (1\<^sub>m n :: complex Matrix.mat) = of_nat n"
proof -
  have "Tr (1\<^sub>m n :: complex Matrix.mat)
          = (\<Sum>r < n. if r < n then (1\<^sub>m n :: complex Matrix.mat) $$ (r, r)
                       else 0)"
    by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>r < n. (1 :: complex))" by simp
  also have "\<dots> = of_nat n" by simp
  finally show ?thesis.
qed

lemma maximally_mixed_state_trace:
  assumes npos: "0 < n"
  shows "Tr (maximally_mixed_state n) = 1"
proof -
  have "Tr (maximally_mixed_state n)
          = complex_of_real (1 / real n) * Tr (1\<^sub>m n :: complex Matrix.mat)"
    unfolding maximally_mixed_state_def by (rule Tr_smult)
  also have "\<dots> = complex_of_real (1 / real n) * of_nat n"
    by (simp add: Tr_one_mat)
  also have "\<dots> = complex_of_real (1 / real n * real n)"
    by simp
  also have "\<dots> = complex_of_real 1"
    using npos by simp
  also have "\<dots> = 1" by simp
  finally show ?thesis.
qed

lemma maximally_mixed_state_psd:
  "psd (maximally_mixed_state n)"
proof -
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have I_psd: "psd (1\<^sub>m n :: complex Matrix.mat)"
    using projection_psd[OF projection_one] .
  have nn: "(0 :: real) \<le> 1 / real n"
    by (cases n) auto
  show ?thesis
    unfolding maximally_mixed_state_def
    using nn I_psd I_c by (rule psd_smult_nonneg)
qed

lemma maximally_mixed_state_density_matrix:
  assumes npos: "0 < n"
  shows "density_matrix n (maximally_mixed_state n)"
  unfolding density_matrix_def
  using maximally_mixed_state_carrier maximally_mixed_state_psd
        maximally_mixed_state_trace[OF npos]
  by blast


subsection \<open>Fixed points of unitary-conjugation channels\<close>

lemma unitary_conj_commute:
  fixes M :: "complex Matrix.mat"
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and M_c: "M \<in> carrier_mat n n"
      and commute: "U * M = M * U"
  shows "U * M * (U\<^sup>\<dagger>) = M"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using U_unit U_c by (auto simp: unitary_def)
  have "U * M * (U\<^sup>\<dagger>) = (M * U) * (U\<^sup>\<dagger>)" using commute by simp
  also have "\<dots> = M * (U * (U\<^sup>\<dagger>))"
    using M_c U_c Ud_c by (metis assoc_mult_mat)
  also have "\<dots> = M * (1\<^sub>m n)" using UUd by simp
  also have "\<dots> = M" using M_c by simp
  finally show ?thesis.
qed

lemma unitary_conj_channel_fixed_point_commute:
  fixes p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and M_c: "M \<in> carrier_mat n n"
      and commute: "U * M = M * U"
  shows "unitary_conj_channel U p M = M"
proof -
  have conj_eq: "U * M * (U\<^sup>\<dagger>) = M"
    using unitary_conj_commute[OF U_c U_unit M_c commute].
  have "unitary_conj_channel U p M
          = complex_of_real (1 - p) \<cdot>\<^sub>m M
            + complex_of_real p \<cdot>\<^sub>m M"
    unfolding unitary_conj_channel_def using conj_eq by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) \<cdot>\<^sub>m M"
    using M_c by (rule add_smult_distrib_right_mat[symmetric])
  also have "\<dots> = (1 :: complex) \<cdot>\<^sub>m M" by simp
  also have "\<dots> = M" using M_c by (intro eq_matI) auto
  finally show ?thesis.
qed


lemma maximally_mixed_state_commutes:
  fixes U :: "complex Matrix.mat"
  assumes U_c: "U \<in> carrier_mat n n"
  shows "U * maximally_mixed_state n = maximally_mixed_state n * U"
proof -
  let ?c = "complex_of_real (1 / real n)"
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have UI: "U * (1\<^sub>m n) = U" using U_c by simp
  have IU: "(1\<^sub>m n) * U = U" using U_c by simp
  have l: "U * maximally_mixed_state n = ?c \<cdot>\<^sub>m U"
  proof -
    have "U * maximally_mixed_state n = U * (?c \<cdot>\<^sub>m (1\<^sub>m n))"
      by (simp add: maximally_mixed_state_def)
    also have "\<dots> = ?c \<cdot>\<^sub>m (U * 1\<^sub>m n)"
      using U_c I_c by (metis mult_smult_distrib)
    also have "\<dots> = ?c \<cdot>\<^sub>m U" using UI by simp
    finally show ?thesis .
  qed
  have r: "maximally_mixed_state n * U = ?c \<cdot>\<^sub>m U"
  proof -
    have "maximally_mixed_state n * U = (?c \<cdot>\<^sub>m (1\<^sub>m n)) * U"
      by (simp add: maximally_mixed_state_def)
    also have "\<dots> = ?c \<cdot>\<^sub>m ((1\<^sub>m n) * U)"
      using I_c U_c by (metis mult_smult_assoc_mat)
    also have "\<dots> = ?c \<cdot>\<^sub>m U" using IU by simp
    finally show ?thesis .
  qed
  show ?thesis using l r by simp
qed

lemma unitary_conj_channel_fixes_max_mixed:
  fixes p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
  shows "unitary_conj_channel U p (maximally_mixed_state n)
         = maximally_mixed_state n"
proof -
  have M_c: "maximally_mixed_state n \<in> carrier_mat n n" by simp
  have commute:
    "U * maximally_mixed_state n = maximally_mixed_state n * U"
    using maximally_mixed_state_commutes[OF U_c] .
  show ?thesis
    using unitary_conj_channel_fixed_point_commute[OF U_c U_unit M_c commute] .
qed



lemma bit_flip_channel_fixes_max_mixed:
  fixes p :: real
  shows "bit_flip_channel p (maximally_mixed_state 2)
           = maximally_mixed_state 2"
  using unitary_conj_channel_fixes_max_mixed[OF Pauli_X_carrier
                                                 Pauli_X_unitary]
  by (simp add: bit_flip_channel_eq)

lemma phase_flip_channel_fixes_max_mixed:
  fixes p :: real
  shows "phase_flip_channel p (maximally_mixed_state 2)
           = maximally_mixed_state 2"
  using unitary_conj_channel_fixes_max_mixed[OF Pauli_Z_carrier
                                                 Pauli_Z_unitary]
  by (simp add: phase_flip_channel_eq)

lemma bit_phase_flip_channel_fixes_max_mixed:
  fixes p :: real
  shows "bit_phase_flip_channel p (maximally_mixed_state 2)
           = maximally_mixed_state 2"
  using unitary_conj_channel_fixes_max_mixed[OF Pauli_Y_carrier
                                                 Pauli_Y_unitary]
  by (simp add: bit_phase_flip_channel_eq)


subsection \<open>Channels preserve density matrices\<close>

lemma unitary_conj_channel_preserves_density_matrix:
  fixes p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and p_nn: "0 \<le> p"
      and p_le: "p \<le> 1"
      and dm: "density_matrix n \<rho>"
  shows "density_matrix n (unitary_conj_channel U p \<rho>)"
proof -
  have \<rho>_c: "\<rho> \<in> carrier_mat n n" using dm by (simp add: density_matrix_def)
  have \<rho>_psd: "psd \<rho>" using dm by (simp add: density_matrix_def)
  have \<rho>_tr: "Tr \<rho> = 1" using dm by (simp add: density_matrix_def)
  have c: "unitary_conj_channel U p \<rho> \<in> carrier_mat n n"
    using unitary_conj_channel_carrier[OF U_c \<rho>_c] .
  have psd: "psd (unitary_conj_channel U p \<rho>)"
    using unitary_conj_channel_psd[OF p_nn p_le U_c \<rho>_c \<rho>_psd] .
  have tr: "Tr (unitary_conj_channel U p \<rho>) = 1"
    using unitary_conj_channel_trace_preserving[OF U_c U_unit \<rho>_c] \<rho>_tr
    by simp
  show ?thesis unfolding density_matrix_def using c psd tr by blast
qed

lemma bit_flip_channel_preserves_density_matrix:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
      and dm: "density_matrix 2 \<rho>"
  shows "density_matrix 2 (bit_flip_channel p \<rho>)"
  using unitary_conj_channel_preserves_density_matrix
          [OF Pauli_X_carrier Pauli_X_unitary p_nn p_le dm]
  by (simp add: bit_flip_channel_eq)

lemma phase_flip_channel_preserves_density_matrix:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
      and dm: "density_matrix 2 \<rho>"
  shows "density_matrix 2 (phase_flip_channel p \<rho>)"
  using unitary_conj_channel_preserves_density_matrix
          [OF Pauli_Z_carrier Pauli_Z_unitary p_nn p_le dm]
  by (simp add: phase_flip_channel_eq)

lemma bit_phase_flip_channel_preserves_density_matrix:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
      and dm: "density_matrix 2 \<rho>"
  shows "density_matrix 2 (bit_phase_flip_channel p \<rho>)"
  using unitary_conj_channel_preserves_density_matrix
          [OF Pauli_Y_carrier Pauli_Y_unitary p_nn p_le dm]
  by (simp add: bit_phase_flip_channel_eq)


subsection \<open>Pauli product identities\<close>

text \<open>With the Day 32 convention for $Y$: $XY=-iZ$, $YZ=-iX$, $ZX=-iY$.\<close>

lemma Pauli_X_times_Pauli_Y: "Pauli_X * Pauli_Y = -\<i> \<cdot>\<^sub>m Pauli_Z"
proof (rule eq_matI)
  show "dim_row (Pauli_X * Pauli_Y) = dim_row (-\<i> \<cdot>\<^sub>m Pauli_Z)"
    by (simp add: Pauli_X_def Pauli_Y_def Pauli_Z_def)
  show "dim_col (Pauli_X * Pauli_Y) = dim_col (-\<i> \<cdot>\<^sub>m Pauli_Z)"
    by (simp add: Pauli_X_def Pauli_Y_def Pauli_Z_def)
next
  fix i j
  assume i_lt: "i < dim_row (-\<i> \<cdot>\<^sub>m Pauli_Z)"
     and j_lt: "j < dim_col (-\<i> \<cdot>\<^sub>m Pauli_Z)"
  hence ij: "i < 2" "j < 2"
    by (simp_all add: Pauli_Z_def)
  show "(Pauli_X * Pauli_Y) $$ (i, j) = (-\<i> \<cdot>\<^sub>m Pauli_Z) $$ (i, j)"
    using ij
    unfolding Pauli_X_def Pauli_Y_def Pauli_Z_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

lemma Pauli_Y_times_Pauli_Z: "Pauli_Y * Pauli_Z = -\<i> \<cdot>\<^sub>m Pauli_X"
proof (rule eq_matI)
  show "dim_row (Pauli_Y * Pauli_Z) = dim_row (-\<i> \<cdot>\<^sub>m Pauli_X)"
    by (simp add: Pauli_Y_def Pauli_Z_def Pauli_X_def)
  show "dim_col (Pauli_Y * Pauli_Z) = dim_col (-\<i> \<cdot>\<^sub>m Pauli_X)"
    by (simp add: Pauli_Y_def Pauli_Z_def Pauli_X_def)
next
  fix i j
  assume i_lt: "i < dim_row (-\<i> \<cdot>\<^sub>m Pauli_X)"
     and j_lt: "j < dim_col (-\<i> \<cdot>\<^sub>m Pauli_X)"
  hence ij: "i < 2" "j < 2"
    by (simp_all add: Pauli_X_def)
  show "(Pauli_Y * Pauli_Z) $$ (i, j) = (-\<i> \<cdot>\<^sub>m Pauli_X) $$ (i, j)"
    using ij
    unfolding Pauli_Y_def Pauli_Z_def Pauli_X_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

lemma Pauli_Z_times_Pauli_X: "Pauli_Z * Pauli_X = -\<i> \<cdot>\<^sub>m Pauli_Y"
proof (rule eq_matI)
  show "dim_row (Pauli_Z * Pauli_X) = dim_row (-\<i> \<cdot>\<^sub>m Pauli_Y)"
    by (simp add: Pauli_Z_def Pauli_X_def Pauli_Y_def)
  show "dim_col (Pauli_Z * Pauli_X) = dim_col (-\<i> \<cdot>\<^sub>m Pauli_Y)"
    by (simp add: Pauli_Z_def Pauli_X_def Pauli_Y_def)
next
  fix i j
  assume i_lt: "i < dim_row (-\<i> \<cdot>\<^sub>m Pauli_Y)"
     and j_lt: "j < dim_col (-\<i> \<cdot>\<^sub>m Pauli_Y)"
  hence ij: "i < 2" "j < 2"
    by (simp_all add: Pauli_Y_def)
  show "(Pauli_Z * Pauli_X) $$ (i, j) = (-\<i> \<cdot>\<^sub>m Pauli_Y) $$ (i, j)"
    using ij
    unfolding Pauli_Z_def Pauli_X_def Pauli_Y_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

end
