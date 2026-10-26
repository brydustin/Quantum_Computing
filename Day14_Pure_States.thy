(*  Title:   Day14_Pure_States.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 28 September 2011 (Day 14)
*)

theory Day14_Pure_States
  imports Day13_Density_Matrices
begin

section \<open>Day 14 (28 September 2011): density matrices, pure states, composite ensembles\<close>

text \<open>\begin{notesprop}
$\rho\in L(\Hil_A)$ is the density matrix of some ensemble if and only if $\rho\ge0$ and
$\Tr\rho=1$.
\end{notesprop}
\begin{notesdef}
$\rho$ is a \emph{density matrix} when $\rho\ge0$ and $\Tr\rho=1$.  The ensemble
$\{\lambda_i,\psi_i\}$ of eigenvalues and an orthonormal eigenbasis is the \emph{spectral
ensemble}.
\end{notesdef}
Many ensembles have the same density matrix: writing $\rho=XX^*=\sum_ic_ic_i^*$ with columns
$c_i$ gives the ensemble $\{\norm{c_i}^2,c_i/\norm{c_i}\}$.\<close>

theorem density_matrix_characterisation:
  fixes \<rho> :: "complex Matrix.mat"
  assumes sq: "\<rho> \<in> carrier_mat n n"
  shows "density_matrix n \<rho> \<longleftrightarrow> psd \<rho> \<and> Tr \<rho> = 1"
  using sq by (simp add: density_matrix_def)


lemma ensemble_density_carrier_dim:
  shows "ensemble_density n E \<in> carrier_mat n n"
proof (induct E)
  case Nil show ?case by (simp add: ensemble_density_def)
next
  case (Cons a E)
  obtain p \<psi> where a: "a = (p, \<psi>)" by (cases a) auto
  have "ensemble_density n (a # E)
          = complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + ensemble_density n E"
    by (simp add: a ensemble_density_Cons)
  moreover have "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n"
    by auto
  ultimately show ?case using Cons.hyps by auto
qed

lemma outer_sum_singleton_index:
  assumes r: "r < n" and c: "c < n"
  shows "outer_sum n [\<psi>] $$ (r, c) = \<psi> $ r * cnj (\<psi> $ c)"
proof -
  let ?M = "mat_of_cols n [\<psi>]"
  let ?Md = "(?M)\<^sup>\<dagger>"
  have M_car: "?M \<in> carrier_mat n 1"
    by (simp add: mat_of_cols_def)
  have Md_car: "?Md \<in> carrier_mat 1 n"
    using M_car by auto
  have dr: "r < dim_row ?M" using M_car r by auto
  have dc: "c < dim_col ?Md" using Md_car c by auto
  have "outer_sum n [\<psi>] $$ (r, c) = (?M * ?Md) $$ (r, c)"
    by (simp add: outer_sum_def)
  also have "\<dots> = Matrix.row ?M r \<bullet> Matrix.col ?Md c"
    using dc dr index_mult_mat(1) by blast
  also have "\<dots> = (\<Sum>j = 0..<1. ?M $$ (r, j) * ?Md $$ (j, c))"
    using M_car Md_car r c
    by (simp add: scalar_prod_def Matrix.row_def Matrix.col_def)
  also have "\<dots> = ?M $$ (r, 0) * ?Md $$ (0, c)"
    by simp
  also have "\<dots> = \<psi> $ r * cnj (\<psi> $ c)"
    using r c by (simp add: mat_of_cols_def dagger_def)
  finally show ?thesis.
qed

text \<open>Day 13: $\ketbra{e^{i\theta}\psi}{e^{i\theta}\psi}=\ketbra\psi\psi$; the density matrix forgets the phase.\<close>

lemma pure_density_smult_unit:
  fixes \<psi> :: "complex Matrix.vec" and c :: complex
  assumes c: "cmod c = 1"
  shows "pure_density (c \<cdot>\<^sub>v \<psi>) = pure_density \<psi>"
proof -
  let ?n = "dim_vec \<psi>"
  have cc: "c * cnj c = 1"
    using c by (metis complex_norm_square of_real_1 one_power2)
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

lemma ensemble_density_index:
  assumes r: "r < n" and c: "c < n"
  shows "ensemble_density n E $$ (r, c) =
         (\<Sum>(p, \<psi>) \<leftarrow> E. complex_of_real p * \<psi> $ r * cnj (\<psi> $ c))"
proof (induct E)
  case Nil
  have "ensemble_density n [] $$ (r, c) = (0\<^sub>m n n) $$ (r, c)"
    by (simp add: ensemble_density_def)
  also have "\<dots> = 0" using r c by simp
  finally show ?case by simp
next
  case (Cons a E)
  obtain p \<psi> where a: "a = (p, \<psi>)" by (cases a) auto
  let ?S = "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>]"
  have S_car: "?S \<in> carrier_mat n n" by auto
  have ED_car: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier_dim)
  have sum_car: "?S + ensemble_density n E \<in> carrier_mat n n"
    using S_car ED_car by auto
  have "ensemble_density n (a # E) $$ (r, c)
          = (?S + ensemble_density n E) $$ (r, c)"
    by (simp add: a ensemble_density_Cons)
  also have "\<dots> = ?S $$ (r, c) + ensemble_density n E $$ (r, c)"
    using S_car ED_car r c by simp
  also have "?S $$ (r, c) = complex_of_real p * outer_sum n [\<psi>] $$ (r, c)"
    using r c by simp
  also have "outer_sum n [\<psi>] $$ (r, c) = \<psi> $ r * cnj (\<psi> $ c)"
    using r c by (rule outer_sum_singleton_index)
  also have "ensemble_density n E $$ (r, c) =
               (\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<phi> $ r * cnj (\<phi> $ c))"
    by (rule Cons.hyps)
  finally show ?case
    by (simp add: a mult.assoc)
qed

text \<open>The spectral ensemble: every density matrix comes from an ensemble.\<close>

theorem spectral_ensemble_exists:
  fixes \<rho> :: "complex Matrix.mat"
  assumes dm: "density_matrix n \<rho>"
  shows "\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>"
proof -
  have rho_car: "\<rho> \<in> carrier_mat n n"
   and rho_psd: "psd \<rho>"
   and rho_Tr: "Tr \<rho> = 1"
    using dm unfolding density_matrix_def by auto
  have rho_herm: "hermitian \<rho>" using rho_psd by (rule psd_hermitian)

  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
       and Dlen: "length D = n"
       and spec: "U\<^sup>\<dagger> * \<rho> * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF rho_car rho_herm] by blast
  have Udag_car: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have rho_times_U: "\<rho> * U = U * diag_mat_of_real D"
    using hermitian_spectral_decomp_right[OF Uc rho_car UU spec].

  \<comment> \<open>Columns of U are unit vectors of length n.\<close>
  have col_dim: "\<And>i. i < n \<Longrightarrow> dim_vec (Matrix.col U i) = n" using Uc by simp
  have col_norm: "\<And>i. i < n \<Longrightarrow> \<parallel>Matrix.col U i\<parallel> = 1"
    using UU Uc unitary_unit_col by (metis carrier_matD(2))
  have col_qs: "\<And>i. i < n \<Longrightarrow> quantum_state n (Matrix.col U i)"
    using col_dim col_norm by (auto simp: quantum_state_def)
  have col_ne: "\<And>i. i < n \<Longrightarrow> Matrix.col U i \<noteq> 0\<^sub>v n"
  proof -
    fix i assume i: "i < n"
    show "Matrix.col U i \<noteq> 0\<^sub>v n"
    proof
      assume z: "Matrix.col U i = 0\<^sub>v n"
      hence "\<parallel>Matrix.col U i\<parallel> = 0"
        using col_dim[OF i] cpx_vec_length_zero_iff by metis
      with col_norm[OF i] show False by simp
    qed
  qed

  \<comment> \<open>Each column of U is an eigenvector of \<open>\<rho>\<close> with eigenvalue \<open>D ! i\<close>.\<close>
  have eig: "\<And>i. i < n \<Longrightarrow>
               \<rho> *\<^sub>v Matrix.col U i = complex_of_real (D!i) \<cdot>\<^sub>v Matrix.col U i"
  proof -
    fix i assume i: "i < n"
    let ?u = "Matrix.col U i"
    show "\<rho> *\<^sub>v ?u = complex_of_real (D!i) \<cdot>\<^sub>v ?u"
    proof (rule eq_vecI)
      show "dim_vec (\<rho> *\<^sub>v ?u) = dim_vec (complex_of_real (D!i) \<cdot>\<^sub>v ?u)"
        using rho_car col_dim[OF i] by simp
    next
      fix k assume k: "k < dim_vec (complex_of_real (D!i) \<cdot>\<^sub>v ?u)"
      hence klt: "k < n" using col_dim[OF i] by simp
      have "(\<rho> *\<^sub>v ?u) $ k = (\<rho> * U) $$ (k, i)"
        using rho_car Uc i klt
        by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using rho_times_U by simp
      also have "\<dots> = (\<Sum>j = 0..<n.
                          U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
        using Uc Dlen klt i by (simp add: scalar_prod_def lessThan_atLeast0)
      also have "\<dots> = (\<Sum>j = 0..<n.
                          if j = i then U $$ (k, j) * complex_of_real (D!i) else 0)"
        using Dlen i by (intro sum.cong refl) auto
      also have "\<dots> = U $$ (k, i) * complex_of_real (D!i)"
        using i by simp
      also have "\<dots> = complex_of_real (D!i) * U $$ (k, i)"
        by (simp add: mult.commute)
      also have "\<dots> = (complex_of_real (D!i) \<cdot>\<^sub>v ?u) $ k"
        using klt Uc i by simp
      finally show "(\<rho> *\<^sub>v ?u) $ k = (complex_of_real (D!i) \<cdot>\<^sub>v ?u) $ k".
    qed
  qed

  \<comment> \<open>Eigenvalues are non-negative (\<open>\<rho>\<close> is PSD).\<close>
  have eig_nn:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> \<rho> *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    using psd_iff_nonneg_eigenvalues[OF rho_car] rho_psd by blast
  have D_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  proof -
    fix i assume i: "i < n"
    have "0 \<le> Re (complex_of_real (D ! i))"
      using eig_nn eig[OF i] col_ne[OF i] col_dim[OF i] by blast
    thus "0 \<le> D ! i" by simp
  qed

  \<comment> \<open>Eigenvalues sum to \<open>Tr \<rho> = 1\<close>.\<close>
  have Tr_diag: "Tr (diag_mat_of_real D) = (\<Sum>i<n. complex_of_real (D!i))"
    using Dlen by (simp add: Tr_def)
  have D_sum_complex: "(\<Sum>i<n. complex_of_real (D!i)) = 1"
  proof -
    have "(\<Sum>i<n. complex_of_real (D!i)) = Tr (diag_mat_of_real D)"
      using Tr_diag by simp
    also have "\<dots> = Tr (U\<^sup>\<dagger> * \<rho> * U)" using spec by simp
    also have "\<dots> = Tr \<rho>"
      using Tr_unitary_conjugation[OF UU] rho_car Uc by simp
    also have "\<dots> = 1" using rho_Tr by simp
    finally show ?thesis.
  qed
  have D_sum: "(\<Sum>i<n. D!i) = 1"
  proof -
    have "complex_of_real (\<Sum>i<n. D!i) = (\<Sum>i<n. complex_of_real (D!i))"
      by simp
    also have "\<dots> = 1" by (rule D_sum_complex)
    finally show ?thesis
      using of_real_eq_1_iff by blast
  qed

  \<comment> \<open>Build the ensemble \<open>E = map (\<lambda>i. (D!i, col U i)) [0..<n]\<close>.\<close>
  define E where "E = map (\<lambda>i. (D!i, Matrix.col U i)) [0..<n]"
  have E_set: "set E = (\<lambda>i. (D!i, Matrix.col U i)) ` {..<n}"
    by (simp add: E_def atLeast0LessThan)
  have ens_ok: "\<forall>(p, \<psi>) \<in> set E. 0 \<le> p \<and> quantum_state n \<psi>"
    using E_set D_nn col_qs by auto
  have probs: "(\<Sum>(p, _) \<leftarrow> E. p) = 1"
  proof -
    have "(\<Sum>(p, _) \<leftarrow> E. p) = sum_list (map (\<lambda>i. D!i) [0..<n])"
      unfolding E_def by (simp add: o_def case_prod_beta)
    also have "\<dots> = (\<Sum>i = 0..<n. D!i)"
      by (simp add: interv_sum_list_conv_sum_set_nat)
    also have "\<dots> = (\<Sum>i<n. D!i)"
      by (simp add: atLeast0LessThan)
    also have "\<dots> = 1" by (rule D_sum)
    finally show ?thesis.
  qed
  have ens: "ensemble n E"
    unfolding ensemble_def using ens_ok probs by blast

  \<comment> \<open>Entry-wise: \<open>ensemble_density n E = U * diag_mat_of_real D * U\<^sup>\<dagger> = \<rho>\<close>.\<close>
  have ED_car: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier_dim)
  have ED_eq: "ensemble_density n E = \<rho>"
  proof (rule eq_matI)
    show "dim_row (ensemble_density n E) = dim_row \<rho>"
      using ED_car rho_car by simp
    show "dim_col (ensemble_density n E) = dim_col \<rho>"
      using ED_car rho_car by simp
  next
    fix r c assume rc: "r < dim_row \<rho>" "c < dim_col \<rho>"
    then have r: "r < n" and c: "c < n" using rho_car by auto

    \<comment> \<open>LHS via entry formula.\<close>
    have LHS: "ensemble_density n E $$ (r, c) =
               (\<Sum>i<n. complex_of_real (D!i) * U $$ (r, i) * cnj (U $$ (c, i)))"
    proof -
      have "ensemble_density n E $$ (r, c) =
              (\<Sum>(p, \<psi>) \<leftarrow> E. complex_of_real p * \<psi> $ r * cnj (\<psi> $ c))"
        by (rule ensemble_density_index[OF r c])
      also have "\<dots> = sum_list (map (\<lambda>i. complex_of_real (D!i)
                                          * Matrix.col U i $ r
                                          * cnj (Matrix.col U i $ c)) [0..<n])"
        unfolding E_def by (simp add: o_def case_prod_beta)
      also have "\<dots> = (\<Sum>i = 0..<n.
                          complex_of_real (D!i)
                            * Matrix.col U i $ r
                            * cnj (Matrix.col U i $ c))"
        by (simp add: interv_sum_list_conv_sum_set_nat)
      also have "\<dots> = (\<Sum>i<n. complex_of_real (D!i)
                                * Matrix.col U i $ r
                                * cnj (Matrix.col U i $ c))"
        by (simp add: atLeast0LessThan)
      also have "\<dots> = (\<Sum>i<n. complex_of_real (D!i) * U $$ (r, i) * cnj (U $$ (c, i)))"
        using Uc r c by (intro sum.cong refl) simp
      finally show ?thesis.
    qed

    \<comment> \<open>RHS: expand \<open>\<rho>\<close> = U * \<open>diag_mat_of_real\<close> D * U-dagger entry-wise.\<close>
    let ?UD = "U * diag_mat_of_real D"
    have diag_car: "diag_mat_of_real D \<in> carrier_mat n n"
      using Dlen by force
    have UD_car: "?UD \<in> carrier_mat n n"
      using Uc diag_car by auto

    have UD_index: "\<And>k. k < n \<Longrightarrow>
         ?UD $$ (r, k) = complex_of_real (D!k) * U $$ (r, k)"
    proof -
      fix k assume k: "k < n"
      have "?UD $$ (r, k) = (\<Sum>j = 0..<n. U $$ (r, j) * diag_mat_of_real D $$ (j, k))"
        using Uc Dlen r k by (simp add: scalar_prod_def lessThan_atLeast0)
      also have "\<dots> = (\<Sum>j = 0..<n.
                          if j = k then U $$ (r, j) * complex_of_real (D!k) else 0)"
        using Dlen k by (intro sum.cong refl) auto
      also have "\<dots> = U $$ (r, k) * complex_of_real (D!k)"
        using k by simp
      also have "\<dots> = complex_of_real (D!k) * U $$ (r, k)"
        by (simp add: mult.commute)
      finally show "?UD $$ (r, k) = complex_of_real (D!k) * U $$ (r, k)".
    qed

    have RHS: "\<rho> $$ (r, c) =
               (\<Sum>i<n. complex_of_real (D!i) * U $$ (r, i) * cnj (U $$ (c, i)))"
    proof -
      have r_UD: "r < dim_row ?UD" using UD_car r by auto
      have c_Ud: "c < dim_col (U\<^sup>\<dagger>)" using Udag_car c by auto
      have rho_expand: "\<rho> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
        by (rule hermitian_spectral_decomp_eq[OF Uc rho_car UU spec])
      have dim_col_Ud: "dim_vec (Matrix.col (U\<^sup>\<dagger>) c) = n"
        using Uc by simp
      have "\<rho> $$ (r, c) = (?UD * (U\<^sup>\<dagger>)) $$ (r, c)"
        using rho_expand by simp
      also have "\<dots> = Matrix.row ?UD r \<bullet> Matrix.col (U\<^sup>\<dagger>) c"
        using index_mult_mat(1)[OF r_UD c_Ud] .
      also have "\<dots> = (\<Sum>k = 0..<n. Matrix.row ?UD r $ k * Matrix.col (U\<^sup>\<dagger>) c $ k)"
        unfolding scalar_prod_def using dim_col_Ud by simp
      also have "\<dots> = (\<Sum>k = 0..<n. ?UD $$ (r, k) * (U\<^sup>\<dagger>) $$ (k, c))"
      proof (intro sum.cong refl)
        fix k assume k: "k \<in> {0..<n}"
        hence klt: "k < n" by simp
        have kr: "r < dim_row ?UD" using UD_car r by auto
        have kc_UD: "k < dim_col ?UD" using UD_car klt by auto
        have rowk: "Matrix.row ?UD r $ k = ?UD $$ (r, k)"
          using kr kc_UD by simp
        have kr_Ud: "k < dim_row (U\<^sup>\<dagger>)" using Udag_car klt by auto
        have kc_Ud: "c < dim_col (U\<^sup>\<dagger>)" using Udag_car c by auto
        have colk: "Matrix.col (U\<^sup>\<dagger>) c $ k = (U\<^sup>\<dagger>) $$ (k, c)"
          using kr_Ud kc_Ud by (simp add: dagger_def)
        show "Matrix.row ?UD r $ k * Matrix.col (U\<^sup>\<dagger>) c $ k
                = ?UD $$ (r, k) * (U\<^sup>\<dagger>) $$ (k, c)"
          by (simp add: rowk colk)
      qed
      also have "\<dots> = (\<Sum>k = 0..<n. complex_of_real (D!k) * U $$ (r, k)
                                      * cnj (U $$ (c, k)))"
        using UD_index Uc c by (intro sum.cong refl, simp add: dagger_def)
      also have "\<dots> = (\<Sum>i<n. complex_of_real (D!i) * U $$ (r, i)
                                * cnj (U $$ (c, i)))"
        by (simp add: atLeast0LessThan)
      finally show ?thesis.
    qed
    from LHS RHS show "ensemble_density n E $$ (r, c) = \<rho> $$ (r, c)" 
      by simp
  qed

  from ens ED_eq show ?thesis by blast
qed

corollary density_matrix_iff_ensemble:
  fixes \<rho> :: "complex Matrix.mat"
  shows "density_matrix n \<rho> \<longleftrightarrow>
           (\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>)"
proof
  assume "density_matrix n \<rho>"
  thus "\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>"
    by (rule spectral_ensemble_exists)
next
  assume "\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>"
  then obtain E where ens: "ensemble n E"
                 and eq: "ensemble_density n E = \<rho>" by blast
  have "density_matrix n (ensemble_density n E)"
    by (rule ensemble_density_is_dm[OF ens])
  with eq show "density_matrix n \<rho>" by simp
qed

subsection \<open>Pure states\<close>

text \<open>If $\rho=\ketbra\psi\psi=\sum_ip_i\ketbra{\psi_i}{\psi_i}$ then for $\gamma\perp\psi$,
$0=\braket\gamma{\rho\gamma}=\sum_ip_i|\braket{\psi_i}\gamma|^2$, so every $\psi_i$ with
$p_i>0$ is parallel to $\psi$: $\psi_i=\beta_i\psi$ with $|\beta_i|=1$ and
$\ketbra{\psi_i}{\psi_i}=\ketbra\psi\psi$.  These density matrices are the \emph{pure
states}.\<close>

definition pure_state_density :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "pure_state_density n \<rho> \<equiv>
     density_matrix n \<rho> \<and>
     (\<exists>\<psi>. quantum_state n \<psi> \<and> \<rho> = pure_density \<psi>)"

lemma pure_state_density_is_density:
  assumes "pure_state_density n \<rho>"
  shows "density_matrix n \<rho>"
  using assms by (simp add: pure_state_density_def)

lemma pure_density_is_pure_state_density:
  assumes "quantum_state n \<psi>"
  shows "pure_state_density n (pure_density \<psi>)"
  unfolding pure_state_density_def
  using assms pure_density_is_density_matrix by blast

text \<open>A companion fact not in the notes: a density matrix is pure iff it is idempotent.\<close>

theorem pure_density_iff_idempotent:
  fixes \<rho> :: "complex Matrix.mat"
  assumes dm: "density_matrix n \<rho>"
  shows "pure_state_density n \<rho> \<longleftrightarrow> \<rho> * \<rho> = \<rho>"
proof
  assume pure: "pure_state_density n \<rho>"
  then obtain \<psi> where st: "quantum_state n \<psi>" and rho_eq: "\<rho> = pure_density \<psi>"
    unfolding pure_state_density_def by blast
  have \<psi>_dim: "dim_vec \<psi> = n" using st by (simp add: quantum_state_def)
  have \<psi>_norm: "\<parallel>\<psi>\<parallel> = 1" using st by (simp add: quantum_state_def)
  have \<psi>_inner: "\<langle>\<psi> | \<psi>\<rangle> = 1"
    using \<psi>_norm cpx_vec_length_inner_prod[of \<psi>]
    by (metis of_real_1 one_power2)

  let ?M = "mat_of_cols n [\<psi>]"
  let ?Md = "(?M)\<^sup>\<dagger>"
  have M_car: "?M \<in> carrier_mat n 1"
    by (simp add: mat_of_cols_def)
  have Md_car: "?Md \<in> carrier_mat 1 n"
    using M_car by auto
  have MMd_car: "?M * ?Md \<in> carrier_mat n n"
    using M_car Md_car by auto

  have rho_MMd: "\<rho> = ?M * ?Md"
  proof -
    have "pure_density \<psi> = outer_sum n [\<psi>]"
      using \<psi>_dim by (simp add: pure_density_def)
    also have "\<dots> = ?M * ?Md"
      by (simp add: outer_sum_def)
    finally show ?thesis using rho_eq by simp
  qed

  have MdM: "?Md * ?M = 1\<^sub>m 1"
  proof (rule eq_matI)
    show "dim_row (?Md * ?M) = dim_row (1\<^sub>m 1)" using Md_car M_car by auto
    show "dim_col (?Md * ?M) = dim_col (1\<^sub>m 1)" using Md_car M_car by auto
  next
    fix i j assume ij: "i < dim_row (1\<^sub>m 1)" "j < dim_col (1\<^sub>m 1)"
    then have i0: "i = 0" and j0: "j = 0" by simp_all
    have r_Md: "0 < dim_row ?Md" using Md_car by simp
    have c_M: "0 < dim_col ?M" using M_car by simp
    have dvc: "dim_vec (Matrix.col ?M 0) = n" using M_car by simp
    have "(?Md * ?M) $$ (0, 0) = Matrix.row ?Md 0 \<bullet> Matrix.col ?M 0"
      using index_mult_mat(1)[OF r_Md c_M] .
    also have "\<dots> = (\<Sum>k = 0..<n. Matrix.row ?Md 0 $ k * Matrix.col ?M 0 $ k)"
      unfolding scalar_prod_def using dvc by simp
    also have "\<dots> = (\<Sum>k = 0..<n. ?Md $$ (0, k) * ?M $$ (k, 0))"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {0..<n}"
      hence klt: "k < n" by simp
      have kr_Md: "0 < dim_row ?Md" using Md_car by simp
      have kc_Md: "k < dim_col ?Md" using Md_car klt by simp
      have kr_M: "k < dim_row ?M" using M_car klt by simp
      have kc_M: "0 < dim_col ?M" using M_car by simp
      have rowk: "Matrix.row ?Md 0 $ k = ?Md $$ (0, k)"
        using kr_Md kc_Md by (simp add: dagger_def)
      have colk: "Matrix.col ?M 0 $ k = ?M $$ (k, 0)"
        using kr_M kc_M by simp
      show "Matrix.row ?Md 0 $ k * Matrix.col ?M 0 $ k = ?Md $$ (0, k) * ?M $$ (k, 0)"
        using rowk by (simp add: rowk colk)
    qed
    also have "\<dots> = (\<Sum>k = 0..<n. cnj (\<psi> $ k) * \<psi> $ k)"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {0..<n}"
      hence klt: "k < n" by simp
      have md_eq: "?Md $$ (0, k) = cnj (\<psi> $ k)"
        using klt \<psi>_dim by (simp add: mat_of_cols_def dagger_def)
      have m_eq: "?M $$ (k, 0) = \<psi> $ k"
        using klt \<psi>_dim by (simp add: mat_of_cols_def)
      show "?Md $$ (0, k) * ?M $$ (k, 0) = cnj (\<psi> $ k) * \<psi> $ k"
        by (simp add: md_eq m_eq)
    qed
    also have "\<dots> = \<langle>\<psi> | \<psi>\<rangle>"
      using \<psi>_dim by (simp add: inner_prod_def lessThan_atLeast0)
    also have "\<dots> = 1" using \<psi>_inner .
    finally have e00: "(?Md * ?M) $$ (0, 0) = 1" .
    show "(?Md * ?M) $$ (i, j) = (1\<^sub>m 1) $$ (i, j)"
      using i0 j0 e00 by simp
  qed

  have "\<rho> * \<rho> = (?M * ?Md) * (?M * ?Md)"
    using rho_MMd by simp
  also have "\<dots> = ?M * (?Md * (?M * ?Md))"
    using assoc_mult_mat[OF M_car Md_car MMd_car] .
  also have "\<dots> = ?M * ((?Md * ?M) * ?Md)"
    using assoc_mult_mat[OF Md_car M_car Md_car] by simp
  also have "\<dots> = ?M * ((1\<^sub>m 1) * ?Md)"
    using MdM by simp
  also have "\<dots> = ?M * ?Md"
    using Md_car by simp
  also have "\<dots> = \<rho>" using rho_MMd by simp
  finally show "\<rho> * \<rho> = \<rho>" .
next
  assume idem: "\<rho> * \<rho> = \<rho>"

  have rho_car: "\<rho> \<in> carrier_mat n n"
   and rho_psd: "psd \<rho>"
   and rho_Tr: "Tr \<rho> = 1"
    using dm unfolding density_matrix_def by auto
  have rho_herm: "hermitian \<rho>" using rho_psd by (rule psd_hermitian)

  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
       and Dlen: "length D = n"
       and spec: "U\<^sup>\<dagger> * \<rho> * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF rho_car rho_herm] by blast
  have Udag_car: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have UdU: "U\<^sup>\<dagger> * U = 1\<^sub>m n"
    using Uc UU unfolding unitary_def by auto
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using Uc UU unfolding unitary_def by auto
  have rho_eq: "\<rho> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    by (rule hermitian_spectral_decomp_eq[OF Uc rho_car UU spec])
  have rho_times_U: "\<rho> * U = U * diag_mat_of_real D"
    by (rule hermitian_spectral_decomp_right[OF Uc rho_car UU spec])
  have diag_car: "diag_mat_of_real D \<in> carrier_mat n n"
    using Dlen by force

  \<comment> \<open>Columns of U are unit vectors; eigenvectors with eigenvalues D!i.\<close>
  have col_dim: "\<And>i. i < n \<Longrightarrow> dim_vec (Matrix.col U i) = n" using Uc by simp
  have col_norm: "\<And>i. i < n \<Longrightarrow> \<parallel>Matrix.col U i\<parallel> = 1"
    using UU Uc unitary_unit_col by (metis carrier_matD(2))
  have col_qs: "\<And>i. i < n \<Longrightarrow> quantum_state n (Matrix.col U i)"
    using col_dim col_norm by (auto simp: quantum_state_def)
  have col_ne: "\<And>i. i < n \<Longrightarrow> Matrix.col U i \<noteq> 0\<^sub>v n"
  proof -
    fix i assume i: "i < n"
    show "Matrix.col U i \<noteq> 0\<^sub>v n"
    proof
      assume z: "Matrix.col U i = 0\<^sub>v n"
      hence "\<parallel>Matrix.col U i\<parallel> = 0"
        using col_dim[OF i] cpx_vec_length_zero_iff by metis
      with col_norm[OF i] show False by simp
    qed
  qed
  have eig: "\<And>i. i < n \<Longrightarrow>
               \<rho> *\<^sub>v Matrix.col U i = complex_of_real (D!i) \<cdot>\<^sub>v Matrix.col U i"
  proof -
    fix i assume i: "i < n"
    let ?u = "Matrix.col U i"
    show "\<rho> *\<^sub>v ?u = complex_of_real (D!i) \<cdot>\<^sub>v ?u"
    proof (rule eq_vecI)
      show "dim_vec (\<rho> *\<^sub>v ?u) = dim_vec (complex_of_real (D!i) \<cdot>\<^sub>v ?u)"
        using rho_car col_dim[OF i] by simp
    next
      fix k assume k: "k < dim_vec (complex_of_real (D!i) \<cdot>\<^sub>v ?u)"
      hence klt: "k < n" using col_dim[OF i] by simp
      have "(\<rho> *\<^sub>v ?u) $ k = (\<rho> * U) $$ (k, i)"
        using rho_car Uc i klt
        by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using rho_times_U by simp
      also have "\<dots> = (\<Sum>j = 0..<n.
                          U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
        using Uc Dlen klt i by (simp add: scalar_prod_def lessThan_atLeast0)
      also have "\<dots> = (\<Sum>j = 0..<n.
                          if j = i then U $$ (k, j) * complex_of_real (D!i) else 0)"
        using Dlen i by (intro sum.cong refl) auto
      also have "\<dots> = U $$ (k, i) * complex_of_real (D!i)"
        using i by simp
      also have "\<dots> = complex_of_real (D!i) * U $$ (k, i)"
        by (simp add: mult.commute)
      also have "\<dots> = (complex_of_real (D!i) \<cdot>\<^sub>v ?u) $ k"
        using klt Uc i by simp
      finally show "(\<rho> *\<^sub>v ?u) $ k = (complex_of_real (D!i) \<cdot>\<^sub>v ?u) $ k" .
    qed
  qed

  \<comment> \<open>Eigenvalues are non-negative and sum to 1.\<close>
  have D_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  proof -
    fix i assume i: "i < n"
    have "0 \<le> Re (complex_of_real (D ! i))"
      using psd_iff_nonneg_eigenvalues[OF rho_car] rho_psd eig[OF i]
            col_ne[OF i] col_dim[OF i] by blast
    thus "0 \<le> D ! i" by simp
  qed
  have D_sum: "(\<Sum>i<n. D!i) = 1"
  proof -
    have "complex_of_real (\<Sum>i<n. D!i) = (\<Sum>i<n. complex_of_real (D!i))"
      by simp
    also have "\<dots> = Tr (diag_mat_of_real D)"
      using Dlen by (simp add: Tr_def)
    also have "\<dots> = Tr (U\<^sup>\<dagger> * \<rho> * U)" using spec by simp
    also have "\<dots> = Tr \<rho>"
      using Tr_unitary_conjugation[OF UU] rho_car Uc by simp
    also have "\<dots> = 1" using rho_Tr .
    finally show ?thesis using of_real_eq_1_iff by blast
  qed

  \<comment> \<open>Idempotence of \<open>\<rho>\<close> forces (D!i) squared = D!i for each i, so D!i in \<open>{0,1}\<close>.\<close>
  have DD_eq_D: "diag_mat_of_real D * diag_mat_of_real D = diag_mat_of_real D"
  proof -
    have "diag_mat_of_real D * diag_mat_of_real D
            = ((U\<^sup>\<dagger>) * \<rho> * U) * ((U\<^sup>\<dagger>) * \<rho> * U)"
      using spec by simp
    also have "\<dots> = (U\<^sup>\<dagger>) * \<rho> * (U * (U\<^sup>\<dagger>)) * \<rho> * U"
      using Uc Udag_car rho_car by (simp, smt (verit, best) assoc_mult_mat mult_carrier_mat)
    also have "\<dots> = (U\<^sup>\<dagger>) * \<rho> * (1\<^sub>m n) * \<rho> * U"
      using UUd by simp
    also have "\<dots> = (U\<^sup>\<dagger>) * \<rho> * \<rho> * U"
      using rho_car Uc Udag_car by simp
    also have "\<dots> = (U\<^sup>\<dagger>) * \<rho> * U"
      using idem rho_car Uc Udag_car by simp
    also have "\<dots> = diag_mat_of_real D" using spec.
    finally show ?thesis.
  qed
  have D_sq: "\<And>i. i < n \<Longrightarrow> (D!i) * (D!i) = D!i"
  proof -
    fix i assume i: "i < n"
    have "complex_of_real (D!i) * complex_of_real (D!i) =
          (\<Sum>j = 0..<n. diag_mat_of_real D $$ (i, j) * diag_mat_of_real D $$ (j, i))"
    proof -
      have "(\<Sum>j = 0..<n. diag_mat_of_real D $$ (i, j) * diag_mat_of_real D $$ (j, i))
            = (\<Sum>j = 0..<n. if j = i then complex_of_real (D!i) * complex_of_real (D!i) else 0)"
        using Dlen i by (intro sum.cong refl) auto
      also have "\<dots> = complex_of_real (D!i) * complex_of_real (D!i)"
        using i by simp
      finally show ?thesis by simp
    qed
    also have "\<dots> = (diag_mat_of_real D * diag_mat_of_real D) $$ (i, i)"
      using diag_car Dlen i by (simp add: scalar_prod_def lessThan_atLeast0)
    also have "\<dots> = diag_mat_of_real D $$ (i, i)"
      using DD_eq_D by simp
    also have "\<dots> = complex_of_real (D!i)"
      using Dlen i by simp
    finally have "complex_of_real (D!i) * complex_of_real (D!i) = complex_of_real (D!i)" .
    hence "complex_of_real ((D!i) * (D!i)) = complex_of_real (D!i)" by simp
    thus "(D!i) * (D!i) = D!i" using of_real_eq_iff by blast
  qed
  have D_binary: "\<And>i. i < n \<Longrightarrow> D!i = 0 \<or> D!i = 1"
  proof -
    fix i assume i: "i < n"
    have "(D!i) * (D!i - 1) = 0" using D_sq[OF i] by simp
    thus "D!i = 0 \<or> D!i = 1" by auto
  qed

  \<comment> \<open>Exactly one index has eigenvalue 1; the rest are 0.\<close>
  have card_ones: "card {i. i < n \<and> D!i = 1} = 1"
  proof -
    let ?S = "{i. i < n \<and> D!i = 1}"
    have fin: "finite ?S" by auto
    have intEq: "{..<n} \<inter> {i. D!i = 1} = ?S" by auto
    have "(1::real) = (\<Sum>i<n. D ! i)" using D_sum by simp
    also have "\<dots> = (\<Sum>i<n. if D!i = 1 then (1::real) else 0)"
      using D_binary by (intro sum.cong refl) auto
    also have "\<dots> = (\<Sum>i \<in> {..<n} \<inter> {i. D!i = 1}. (1::real))
                  + (\<Sum>i \<in> {..<n} \<inter> -{i. D!i = 1}. (0::real))"
      by (rule sum.If_cases[OF finite_lessThan])
    also have "\<dots> = (\<Sum>i \<in> ?S. (1::real))"
      using intEq by simp
    also have "\<dots> = real (card ?S)" by simp
    finally have "real (card ?S) = 1" by simp
    thus ?thesis by (metis of_nat_1_eq_iff)
  qed
  obtain j where Sj: "{i. i < n \<and> D!i = 1} = {j}"
    using card_1_singletonE[OF card_ones] by blast
  have ex_one: "\<exists>!j. j < n \<and> D!j = 1"
  proof
    show "j < n \<and> D!j = 1" using Sj by auto
  next
    fix k assume "k < n \<and> D!k = 1"
    thus "k = j" using Sj by auto
  qed
  then obtain j where j_lt: "j < n" and D_j: "D!j = 1"
    and D_unique: "\<And>i. i < n \<Longrightarrow> D!i = 1 \<Longrightarrow> i = j"
    by blast
  have D_others: "\<And>i. i < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> D!i = 0"
    using D_binary D_unique by blast

  \<comment> \<open>Then \<open>\<rho>\<close> = \<open>pure_density\<close> (col U j).\<close>
  let ?\<psi> = "Matrix.col U j"
  have psi_qs: "quantum_state n ?\<psi>" using col_qs[OF j_lt] .

  have rho_pure: "\<rho> = pure_density ?\<psi>"
  proof (rule eq_matI)
    have rho_pdim: "pure_density ?\<psi> = outer_sum n [?\<psi>]"
      using col_dim[OF j_lt] by (simp add: pure_density_def)
    have pd_car: "outer_sum n [?\<psi>] \<in> carrier_mat n n" by auto
    show "dim_row \<rho> = dim_row (pure_density ?\<psi>)"
      using rho_car pd_car rho_pdim by simp
    show "dim_col \<rho> = dim_col (pure_density ?\<psi>)"
      using rho_car pd_car rho_pdim by simp
  next
    fix r c assume rc: "r < dim_row (pure_density ?\<psi>)" "c < dim_col (pure_density ?\<psi>)"
    have rho_pdim: "pure_density ?\<psi> = outer_sum n [?\<psi>]"
      using col_dim[OF j_lt] by (simp add: pure_density_def)
    have pd_car: "outer_sum n [?\<psi>] \<in> carrier_mat n n" by auto
    from rc rho_pdim pd_car have r: "r < n" and c: "c < n" by auto

    have pd_index: "pure_density ?\<psi> $$ (r, c) = ?\<psi> $ r * cnj (?\<psi> $ c)"
      using rho_pdim outer_sum_singleton_index[OF r c] by simp

    let ?UD = "U * diag_mat_of_real D"
    have UD_car: "?UD \<in> carrier_mat n n" using Uc diag_car by auto

    have UD_index: "\<And>k. k < n \<Longrightarrow>
         ?UD $$ (r, k) = complex_of_real (D!k) * U $$ (r, k)"
    proof -
      fix k assume k: "k < n"
      have "?UD $$ (r, k) = (\<Sum>j = 0..<n. U $$ (r, j) * diag_mat_of_real D $$ (j, k))"
        using Uc Dlen r k by (simp add: scalar_prod_def lessThan_atLeast0)
      also have "\<dots> = (\<Sum>j = 0..<n.
                          if j = k then U $$ (r, j) * complex_of_real (D!k) else 0)"
        using Dlen k by (intro sum.cong refl) auto
      also have "\<dots> = U $$ (r, k) * complex_of_real (D!k)"
        using k by simp
      also have "\<dots> = complex_of_real (D!k) * U $$ (r, k)"
        by (simp add: mult.commute)
      finally show "?UD $$ (r, k) = complex_of_real (D!k) * U $$ (r, k)" .
    qed

    have r_UD: "r < dim_row ?UD" using UD_car r by auto
    have c_Ud: "c < dim_col (U\<^sup>\<dagger>)" using Udag_car c by auto
    have dim_col_Ud: "dim_vec (Matrix.col (U\<^sup>\<dagger>) c) = n" using Uc by simp

    have "\<rho> $$ (r, c) = (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) $$ (r, c)"
      by (simp only: rho_eq)
    also have "\<dots> = Matrix.row ?UD r \<bullet> Matrix.col (U\<^sup>\<dagger>) c"
      using index_mult_mat(1)[OF r_UD c_Ud] .
    also have "\<dots> = (\<Sum>k = 0..<n. Matrix.row ?UD r $ k * Matrix.col (U\<^sup>\<dagger>) c $ k)"
      unfolding scalar_prod_def using dim_col_Ud by simp
    also have "\<dots> = (\<Sum>k = 0..<n. ?UD $$ (r, k) * (U\<^sup>\<dagger>) $$ (k, c))"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {0..<n}"
      hence klt: "k < n" by simp
      have kr: "r < dim_row ?UD" using UD_car r by auto
      have kc_UD: "k < dim_col ?UD" using UD_car klt by auto
      have rowk: "Matrix.row ?UD r $ k = ?UD $$ (r, k)"
        using kr kc_UD by simp
      have kr_Ud: "k < dim_row (U\<^sup>\<dagger>)" using Udag_car klt by auto
      have kc_Ud': "c < dim_col (U\<^sup>\<dagger>)" using Udag_car c by auto
      have colk: "Matrix.col (U\<^sup>\<dagger>) c $ k = (U\<^sup>\<dagger>) $$ (k, c)"
        using kr_Ud kc_Ud' by (simp add: dagger_def)
      show "Matrix.row ?UD r $ k * Matrix.col (U\<^sup>\<dagger>) c $ k
              = ?UD $$ (r, k) * (U\<^sup>\<dagger>) $$ (k, c)"
        by (simp add: rowk colk)
    qed
    also have "\<dots> = (\<Sum>k = 0..<n. complex_of_real (D!k) * U $$ (r, k)
                                    * cnj (U $$ (c, k)))"
      using UD_index Uc c by (intro sum.cong refl, simp add: dagger_def)
    also have "\<dots> = (\<Sum>k = 0..<n. if k = j
                                  then U $$ (r, j) * cnj (U $$ (c, j)) else 0)"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {0..<n}"
      hence klt: "k < n" by simp
      show "complex_of_real (D!k) * U $$ (r, k) * cnj (U $$ (c, k))
            = (if k = j then U $$ (r, j) * cnj (U $$ (c, j)) else 0)"
      proof (cases "k = j")
        case True
        thus ?thesis using D_j by simp
      next
        case False
        hence "D!k = 0" using D_others klt by simp
        thus ?thesis using False by simp
      qed
    qed
    also have "\<dots> = U $$ (r, j) * cnj (U $$ (c, j))"
      using j_lt by simp
    also have "\<dots> = ?\<psi> $ r * cnj (?\<psi> $ c)"
      using Uc r c j_lt by simp
    also have "\<dots> = pure_density ?\<psi> $$ (r, c)"
      using pd_index by simp
    finally show "\<rho> $$ (r, c) = pure_density ?\<psi> $$ (r, c)".
  qed

  show "pure_state_density n \<rho>"
    unfolding pure_state_density_def using dm rho_pure psi_qs by blast
qed


lemma outer_sum_singleton_mult_vec:
  assumes \<psi>_dim: "dim_vec \<psi> = n" and \<gamma>_dim: "dim_vec \<gamma> = n"
  shows "outer_sum n [\<psi>] *\<^sub>v \<gamma> = \<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>"
proof (rule eq_vecI)
  show "dim_vec (outer_sum n [\<psi>] *\<^sub>v \<gamma>) = dim_vec (\<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>)"
    using \<psi>_dim by simp
next
  fix i assume i: "i < dim_vec (\<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>)"
  hence ilt: "i < n" using \<psi>_dim by simp
  have os_car: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have dcg: "dim_vec \<gamma> = n" using \<gamma>_dim .
  have "(outer_sum n [\<psi>] *\<^sub>v \<gamma>) $ i
        = (\<Sum>k = 0..<n. outer_sum n [\<psi>] $$ (i, k) * \<gamma> $ k)"
    using ilt \<gamma>_dim os_car by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<n. \<psi> $ i * cnj (\<psi> $ k) * \<gamma> $ k)"
    by (intro sum.cong refl) (simp add: outer_sum_singleton_index[OF ilt])
  also have "\<dots> = (\<Sum>k = 0..<n. \<psi> $ i * (cnj (\<psi> $ k) * \<gamma> $ k))"
    by (intro sum.cong refl) (simp add: mult.assoc)
  also have "\<dots> = \<psi> $ i * (\<Sum>k = 0..<n. cnj (\<psi> $ k) * \<gamma> $ k)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = \<psi> $ i * \<langle>\<psi>|\<gamma>\<rangle>"
    using \<gamma>_dim by (simp add: inner_prod_def lessThan_atLeast0)
  also have "\<dots> = \<langle>\<psi>|\<gamma>\<rangle> * \<psi> $ i" by (simp add: mult.commute)
  also have "\<dots> = (\<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>) $ i" using ilt \<psi>_dim by simp
  finally show "(outer_sum n [\<psi>] *\<^sub>v \<gamma>) $ i = (\<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>) $ i" .
qed


lemma ensemble_density_quad_form:
  assumes E_dim: "\<forall>(p, \<psi>) \<in> set E. dim_vec \<psi> = n"
      and \<gamma>_dim: "dim_vec \<gamma> = n"
  shows "\<langle>\<gamma> | ensemble_density n E *\<^sub>v \<gamma>\<rangle> =
         (\<Sum>(p, \<psi>) \<leftarrow> E. complex_of_real p * \<langle>\<psi>|\<gamma>\<rangle> * cnj \<langle>\<psi>|\<gamma>\<rangle>)"
  using E_dim
proof (induction E)
  case Nil
  have ed_nil: "ensemble_density n [] = 0\<^sub>m n n"
    by (simp add: ensemble_density_def)
  have "ensemble_density n [] *\<^sub>v \<gamma> = 0\<^sub>v n"
  proof (rule eq_vecI)
    show "dim_vec (ensemble_density n [] *\<^sub>v \<gamma>) = dim_vec (0\<^sub>v n)"
      using ed_nil by simp
  next
    fix i assume i: "i < dim_vec (0\<^sub>v n)"
    hence ilt: "i < n" by simp
    have "(ensemble_density n [] *\<^sub>v \<gamma>) $ i
          = (\<Sum>k = 0..<n. (0\<^sub>m n n) $$ (i, k) * \<gamma> $ k)"
      using ed_nil ilt \<gamma>_dim by (simp add: scalar_prod_def)
    also have "\<dots> = 0" using ilt by simp
    also have "\<dots> = (0\<^sub>v n) $ i" using ilt by simp
    finally show "(ensemble_density n [] *\<^sub>v \<gamma>) $ i = (0\<^sub>v n) $ i" .
  qed
  hence "\<langle>\<gamma> | ensemble_density n [] *\<^sub>v \<gamma>\<rangle> = \<langle>\<gamma> | 0\<^sub>v n\<rangle>" by simp
  also have "\<dots> = 0" using \<gamma>_dim by (simp add: inner_prod_def)
  finally show ?case by simp
next
  case (Cons a E')
  obtain p \<psi>\<^sub>0 where a: "a = (p, \<psi>\<^sub>0)" by (cases a) auto
  have \<psi>\<^sub>0_dim: "dim_vec \<psi>\<^sub>0 = n" using Cons.prems a by auto
  have rest_dim: "\<forall>(p, \<psi>) \<in> set E'. dim_vec \<psi> = n"
    using Cons.prems by auto
  have IH: "\<langle>\<gamma> | ensemble_density n E' *\<^sub>v \<gamma>\<rangle> =
            (\<Sum>(q, \<phi>) \<leftarrow> E'. complex_of_real q * \<langle>\<phi>|\<gamma>\<rangle> * cnj \<langle>\<phi>|\<gamma>\<rangle>)"
    by (rule Cons.IH[OF rest_dim])

  let ?pM = "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>\<^sub>0]"
  let ?ED = "ensemble_density n E'"
  have pM_car: "?pM \<in> carrier_mat n n" by auto
  have ED_car: "?ED \<in> carrier_mat n n"
    by (rule ensemble_density_carrier_dim)
  have \<gamma>_car: "\<gamma> \<in> carrier_vec n" using \<gamma>_dim by auto

  have split: "ensemble_density n ((p, \<psi>\<^sub>0) # E') *\<^sub>v \<gamma>
               = ?pM *\<^sub>v \<gamma> + ?ED *\<^sub>v \<gamma>"
  proof -
    have "ensemble_density n ((p, \<psi>\<^sub>0) # E') *\<^sub>v \<gamma>
          = (?pM + ?ED) *\<^sub>v \<gamma>"
      by (simp add: ensemble_density_Cons)
    also have "\<dots> = ?pM *\<^sub>v \<gamma> + ?ED *\<^sub>v \<gamma>"
      by (rule add_mult_distrib_mat_vec[OF pM_car ED_car \<gamma>_car])
    finally show ?thesis .
  qed

  have pM_mv: "?pM *\<^sub>v \<gamma> = complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>)"
  proof (rule eq_vecI)
    show "dim_vec (?pM *\<^sub>v \<gamma>) = dim_vec (complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>))"
      by simp
  next
    fix i assume i: "i < dim_vec (complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>))"
    hence ilt: "i < n" by simp
    have os_car: "outer_sum n [\<psi>\<^sub>0] \<in> carrier_mat n n" by auto
    have "(?pM *\<^sub>v \<gamma>) $ i
          = (\<Sum>k = 0..<n. ?pM $$ (i, k) * \<gamma> $ k)"
      using ilt \<gamma>_dim pM_car by (simp add: scalar_prod_def)
    also have "\<dots> = (\<Sum>k = 0..<n.
                      complex_of_real p * (outer_sum n [\<psi>\<^sub>0] $$ (i, k)) * \<gamma> $ k)"
      using ilt os_car by (intro sum.cong refl) simp
    also have "\<dots> = (\<Sum>k = 0..<n.
                      complex_of_real p * (outer_sum n [\<psi>\<^sub>0] $$ (i, k) * \<gamma> $ k))"
      by (intro sum.cong refl) (simp add: mult.assoc)
    also have "\<dots> = complex_of_real p
                      * (\<Sum>k = 0..<n. outer_sum n [\<psi>\<^sub>0] $$ (i, k) * \<gamma> $ k)"
      by (simp add: sum_distrib_left)
    also have "\<dots> = complex_of_real p * ((outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>) $ i)"
      using ilt \<gamma>_dim os_car by (simp add: scalar_prod_def)
    also have "\<dots> = (complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>)) $ i"
      using ilt os_car by simp
    finally show "(?pM *\<^sub>v \<gamma>) $ i = (complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>)) $ i" .
  qed

  have pM_inner: "\<langle>\<gamma> | ?pM *\<^sub>v \<gamma>\<rangle>
                 = complex_of_real p * \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * cnj \<langle>\<psi>\<^sub>0|\<gamma>\<rangle>"
  proof -
    have "\<langle>\<gamma> | ?pM *\<^sub>v \<gamma>\<rangle>
          = \<langle>\<gamma> | complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>)\<rangle>"
      using pM_mv by simp
    also have "\<dots> = complex_of_real p * \<langle>\<gamma> | outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>\<rangle>"
      by (rule inner_prod_right_smult')
    also have "\<dots> = complex_of_real p * \<langle>\<gamma> | \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>\<^sub>0\<rangle>"
      using outer_sum_singleton_mult_vec[OF \<psi>\<^sub>0_dim \<gamma>_dim] by simp
    also have "\<dots> = complex_of_real p * (\<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * \<langle>\<gamma>|\<psi>\<^sub>0\<rangle>)"
      by (simp add: inner_prod_right_smult')
    also have "\<dots> = complex_of_real p * \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * \<langle>\<gamma>|\<psi>\<^sub>0\<rangle>"
      by (simp add: mult.assoc)
    also have "\<dots> = complex_of_real p * \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * cnj \<langle>\<psi>\<^sub>0|\<gamma>\<rangle>"
      using inner_prod_cnj[of \<psi>\<^sub>0 \<gamma>] \<psi>\<^sub>0_dim \<gamma>_dim by simp
    finally show ?thesis .
  qed

  have dim_eq: "dim_vec (?pM *\<^sub>v \<gamma>) = dim_vec (?ED *\<^sub>v \<gamma>)"
    using pM_car ED_car by auto

  have "\<langle>\<gamma> | ensemble_density n ((p, \<psi>\<^sub>0) # E') *\<^sub>v \<gamma>\<rangle>
        = \<langle>\<gamma> | ?pM *\<^sub>v \<gamma> + ?ED *\<^sub>v \<gamma>\<rangle>"
    using split by simp
  also have "\<dots> = \<langle>\<gamma> | ?pM *\<^sub>v \<gamma>\<rangle> + \<langle>\<gamma> | ?ED *\<^sub>v \<gamma>\<rangle>"
    by (rule inner_prod_right_add'[OF dim_eq])
  also have "\<dots> = complex_of_real p * \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * cnj \<langle>\<psi>\<^sub>0|\<gamma>\<rangle>
                 + (\<Sum>(q, \<phi>) \<leftarrow> E'. complex_of_real q * \<langle>\<phi>|\<gamma>\<rangle> * cnj \<langle>\<phi>|\<gamma>\<rangle>)"
    using pM_inner IH by simp
  also have "\<dots> = (\<Sum>(q, \<phi>) \<leftarrow> (p, \<psi>\<^sub>0) # E'. complex_of_real q * \<langle>\<phi>|\<gamma>\<rangle> * cnj \<langle>\<phi>|\<gamma>\<rangle>)"
    by simp
  finally show ?case using a by simp
qed


theorem pure_ensemble_parallel:
  fixes \<psi> :: "complex Matrix.vec"
  assumes st: "quantum_state n \<psi>"
      and ens: "ensemble n E"
      and dens: "ensemble_density n E = pure_density \<psi>"
      and mem: "(p, \<psi>\<^sub>i) \<in> set E"
      and ppos: "0 < p"
  shows "\<exists>\<beta>. \<psi>\<^sub>i = \<beta> \<cdot>\<^sub>v \<psi>"
proof -
  \<comment> \<open>Basic facts about psi, \<open>psi_i\<close>, and E.\<close>
  have \<psi>_dim: "dim_vec \<psi> = n" using st by (simp add: quantum_state_def)
  have \<psi>_norm: "\<parallel>\<psi>\<parallel> = 1" using st by (simp add: quantum_state_def)
  have \<psi>_inner: "\<langle>\<psi>|\<psi>\<rangle> = 1"
    using \<psi>_norm cpx_vec_length_inner_prod[of \<psi>]
    by (metis of_real_1 one_power2)

  have E_qs: "\<forall>(p, \<phi>) \<in> set E. quantum_state n \<phi>"
    using ens by (auto simp: ensemble_def)
  have E_p_nn: "\<forall>(p, \<phi>) \<in> set E. 0 \<le> p"
    using ens by (auto simp: ensemble_def)
  have E_dim: "\<forall>(q, \<phi>) \<in> set E. dim_vec \<phi> = n"
    using E_qs by (auto simp: quantum_state_def)

  have \<psi>\<^sub>i_qs: "quantum_state n \<psi>\<^sub>i" using E_qs mem by fastforce
  have \<psi>\<^sub>i_dim: "dim_vec \<psi>\<^sub>i = n"
    using \<psi>\<^sub>i_qs by (simp add: quantum_state_def)

  \<comment> \<open>Define beta = inner psi \<open>psi_i\<close> and w = \<open>psi_i\<close> - beta * psi.\<close>
  define \<beta> where "\<beta> = \<langle>\<psi>|\<psi>\<^sub>i\<rangle>"
  define w where "w = \<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>"
  have w_dim: "dim_vec w = n"
    unfolding w_def using \<psi>_dim \<psi>\<^sub>i_dim by simp
  have \<psi>_\<beta>\<psi>_dim: "dim_vec (\<beta> \<cdot>\<^sub>v \<psi>) = dim_vec \<psi>\<^sub>i"
    using \<psi>_dim \<psi>\<^sub>i_dim by simp

  \<comment> \<open>Step 1: w is orthogonal to \<open>\<psi>\<close>, i.e. \<open>\<langle>\<psi>|w\<rangle>\<close> = 0.\<close>
  have \<psi>_perp_w: "\<langle>\<psi>|w\<rangle> = 0"
  proof -
    have "\<langle>\<psi>|w\<rangle> = \<langle>\<psi>|\<psi>\<^sub>i\<rangle> - \<langle>\<psi>|\<beta> \<cdot>\<^sub>v \<psi>\<rangle>"
      unfolding w_def
      by (rule inner_prod_right_minus'[OF \<psi>_\<beta>\<psi>_dim[symmetric]])
    also have "\<dots> = \<langle>\<psi>|\<psi>\<^sub>i\<rangle> - \<beta> * \<langle>\<psi>|\<psi>\<rangle>"
      by (simp add: inner_prod_right_smult')
    also have "\<dots> = \<beta> - \<beta>" using \<psi>_inner by (simp add: \<beta>_def)
    also have "\<dots> = 0" by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Step 2: pure-density psi acting on w is zero.\<close>
  have pd_w_zero: "pure_density \<psi> *\<^sub>v w = 0\<^sub>v n"
  proof -
    have "pure_density \<psi> *\<^sub>v w = outer_sum n [\<psi>] *\<^sub>v w"
      by (simp add: pure_density_def \<psi>_dim)
    also have "\<dots> = \<langle>\<psi>|w\<rangle> \<cdot>\<^sub>v \<psi>"
      by (rule outer_sum_singleton_mult_vec[OF \<psi>_dim w_dim])
    also have "\<dots> = 0 \<cdot>\<^sub>v \<psi>" using \<psi>_perp_w by simp
    also have "\<dots> = 0\<^sub>v n"
      using \<psi>_dim by (intro eq_vecI) simp_all
    finally show ?thesis .
  qed

  \<comment> \<open>Step 3: quadratic form at w is zero via dens.\<close>
  have quad_zero: "\<langle>w | ensemble_density n E *\<^sub>v w\<rangle> = 0"
  proof -
    have "\<langle>w | ensemble_density n E *\<^sub>v w\<rangle> = \<langle>w | pure_density \<psi> *\<^sub>v w\<rangle>"
      using dens by simp
    also have "\<dots> = \<langle>w | 0\<^sub>v n\<rangle>" using pd_w_zero by simp
    also have "\<dots> = 0" using w_dim by (simp add: inner_prod_def)
    finally show ?thesis .
  qed

  \<comment> \<open>Step 4: expand via \<open>quad_form\<close>, extract real sum, show each term is 0.\<close>
  have sum_cplx_zero:
    "(\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>) = 0"
    using ensemble_density_quad_form[OF E_dim w_dim] quad_zero by simp

  have termwise: "\<And>q \<phi>. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>
                        = complex_of_real (q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
  proof -
    fix q :: real and \<phi> :: "complex Matrix.vec"
    have "\<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle> = complex_of_real ((cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
      using complex_norm_square[of "\<langle>\<phi>|w\<rangle>"] by simp
    hence "complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>
           = complex_of_real q * complex_of_real ((cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
      by (simp add: mult.assoc)
    also have "\<dots> = complex_of_real (q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
      by simp
    finally show "complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>
                 = complex_of_real (q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)" .
  qed

  have cplx_eq_real:
    "(\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>)
      = complex_of_real (\<Sum>(q, \<phi>) \<leftarrow> E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
  proof -
    have "(\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>)
          = (\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real (q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2))"
      by (intro arg_cong[where f=sum_list] map_cong refl)
         (simp add: termwise case_prod_beta)
    also have "\<dots> = complex_of_real (\<Sum>(q, \<phi>) \<leftarrow> E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
    proof (induct E)
      case Nil show ?case by simp
    next
      case (Cons a E'') thus ?case by (cases a) simp
    qed
    finally show ?thesis .
  qed

  have sum_real_zero: "(\<Sum>(q, \<phi>) \<leftarrow> E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2) = 0"
    using sum_cplx_zero cplx_eq_real
    by auto

  have terms_nn: "\<forall>(q, \<phi>) \<in> set E. 0 \<le> q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2"
    using E_p_nn by (auto simp:)

  have each_zero: "\<forall>(q, \<phi>) \<in> set E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2 = 0"
  proof -
    let ?xs = "map (\<lambda>(q, \<phi>). q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2) E"
    have nn: "\<And>x. x \<in> set ?xs \<Longrightarrow> 0 \<le> x"
      using terms_nn by (auto simp: case_prod_beta)
    have sum0: "sum_list ?xs = 0"
      using sum_real_zero by (simp add: o_def case_prod_beta)
    have "\<forall>x \<in> set ?xs. x = 0"
      using sum_list_nonneg_eq_0_iff[OF nn] sum0 by blast
    thus ?thesis by (auto simp: case_prod_beta)
  qed

  \<comment> \<open>Step 5: for our (p, \<open>psi_i\<close>), p > 0 and the term is 0, so inner \<open>psi_i\<close> w = 0.\<close>
  have \<psi>\<^sub>i_perp_w: "\<langle>\<psi>\<^sub>i|w\<rangle> = 0"
  proof -
    have "p * (cmod \<langle>\<psi>\<^sub>i|w\<rangle>)\<^sup>2 = 0"
      using each_zero mem by auto
    hence "(cmod \<langle>\<psi>\<^sub>i|w\<rangle>)\<^sup>2 = 0" using ppos by simp
    hence "cmod \<langle>\<psi>\<^sub>i|w\<rangle> = 0" by simp
    thus ?thesis by simp
  qed

  \<comment> \<open>Step 6: compute inner \<open>psi_i\<close> w = inner \<open>psi_i\<close> \<open>psi_i\<close> minus beta cnj beta.\<close>
  have \<psi>\<^sub>i\<psi>_cnj: "\<langle>\<psi>\<^sub>i|\<psi>\<rangle> = cnj \<beta>"
    unfolding \<beta>_def using inner_prod_cnj[of \<psi> \<psi>\<^sub>i] \<psi>_dim \<psi>\<^sub>i_dim by simp

  have \<psi>\<^sub>i_inner_sq: "\<langle>\<psi>\<^sub>i|\<psi>\<^sub>i\<rangle> = \<beta> * cnj \<beta>"
  proof -
    have dim_eq: "dim_vec \<psi>\<^sub>i = dim_vec (\<beta> \<cdot>\<^sub>v \<psi>)" using \<psi>_dim \<psi>\<^sub>i_dim by simp
    have "0 = \<langle>\<psi>\<^sub>i|w\<rangle>" using \<psi>\<^sub>i_perp_w by simp
    also have "\<dots> = \<langle>\<psi>\<^sub>i|\<psi>\<^sub>i\<rangle> - \<langle>\<psi>\<^sub>i|\<beta> \<cdot>\<^sub>v \<psi>\<rangle>"
      unfolding w_def
      by (rule inner_prod_right_minus'[OF dim_eq])
    also have "\<dots> = \<langle>\<psi>\<^sub>i|\<psi>\<^sub>i\<rangle> - \<beta> * \<langle>\<psi>\<^sub>i|\<psi>\<rangle>"
      by (simp add: inner_prod_right_smult')
    also have "\<dots> = \<langle>\<psi>\<^sub>i|\<psi>\<^sub>i\<rangle> - \<beta> * cnj \<beta>"
      using \<psi>\<^sub>i\<psi>_cnj by simp
    finally show ?thesis by simp
  qed

  \<comment> \<open>Step 7: \<open>\<langle>w|w\<rangle>\<close> = 0.\<close>
  have w_inner_zero: "\<langle>w|w\<rangle> = 0"
  proof -
    have dim_eq: "dim_vec (\<beta> \<cdot>\<^sub>v \<psi>) = dim_vec \<psi>\<^sub>i" using \<psi>_dim \<psi>\<^sub>i_dim by simp
    have w_equiv: "w = \<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>" by (simp add: w_def)
    have "\<langle>w|w\<rangle> = \<langle>\<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>| w\<rangle>" using w_equiv by simp
    also have "\<dots> = \<langle>\<psi>\<^sub>i|w\<rangle> - \<langle>\<beta> \<cdot>\<^sub>v \<psi>|w\<rangle>"
      by (rule inner_prod_left_minus'[OF dim_eq[symmetric]])
         (simp add: w_dim \<psi>\<^sub>i_dim)
    also have "\<langle>\<beta> \<cdot>\<^sub>v \<psi>|w\<rangle> = cnj \<beta> * \<langle>\<psi>|w\<rangle>"
    proof -
      have "dim_vec \<psi> = dim_vec w" using \<psi>_dim w_dim by simp
      thus ?thesis by (rule No_Cloning.inner_prod_distrib_left)
    qed
    also have "cnj \<beta> * \<langle>\<psi>|w\<rangle> = 0" using \<psi>_perp_w by simp
    finally show ?thesis using \<psi>\<^sub>i_perp_w by simp
  qed

  \<comment> \<open>Step 8: inner w w = 0 so w = 0.\<close>
  have w_zero: "w = 0\<^sub>v n"
  proof -
    have "(complex_of_real (\<parallel>w\<parallel>))\<^sup>2 = \<langle>w|w\<rangle>"
      using cpx_vec_length_inner_prod[of w] by simp
    hence "(complex_of_real (\<parallel>w\<parallel>))\<^sup>2 = 0" using w_inner_zero by simp
    hence "(\<parallel>w\<parallel>)\<^sup>2 = 0"
      by (metis of_real_0 of_real_eq_iff of_real_power)
    hence "\<parallel>w\<parallel> = 0" by simp
    thus "w = 0\<^sub>v n"
      using w_dim cpx_vec_length_zero_iff by metis
  qed

  \<comment> \<open>Conclusion: \<open>psi_i\<close> = beta * psi.\<close>
  have "\<psi>\<^sub>i = \<beta> \<cdot>\<^sub>v \<psi>"
  proof (rule eq_vecI)
    show "dim_vec \<psi>\<^sub>i = dim_vec (\<beta> \<cdot>\<^sub>v \<psi>)" using \<psi>_dim \<psi>\<^sub>i_dim by simp
  next
    fix i assume i: "i < dim_vec (\<beta> \<cdot>\<^sub>v \<psi>)"
    hence ilt: "i < n" using \<psi>_dim by simp
    have "(\<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>) $ i = 0" using w_zero ilt by (simp add: w_def)
    moreover have "(\<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>) $ i = \<psi>\<^sub>i $ i - \<beta> * \<psi> $ i"
      using ilt \<psi>_dim \<psi>\<^sub>i_dim by (simp add: minus_vec_def)
    ultimately have "\<psi>\<^sub>i $ i = \<beta> * \<psi> $ i" by simp
    thus "\<psi>\<^sub>i $ i = (\<beta> \<cdot>\<^sub>v \<psi>) $ i"
      using ilt \<psi>_dim by simp
  qed
  thus ?thesis by blast
qed

subsection \<open>Composite ensembles\<close>

text \<open>For ensembles $\{p_i,\psi_i\}$ in lab A and $\{q_l,\phi_l\}$ in lab B the composite is
the ensemble $\{p_iq_l,\psi_i\otimes\phi_l\}$ with density matrix
$\rho=\sum_{i,l}p_iq_l\ketbra{\psi_i}{\psi_i}\otimes\ketbra{\phi_l}{\phi_l}$, because
$\ketbra{\psi\otimes\phi}{\psi\otimes\phi}=\ketbra\psi\psi\otimes\ketbra\phi\phi$ (checked on
elementary tensors $h\otimes k$).  The identity is formalised below; that $\rho_1\otimes\rho_2$ is
again a density matrix is \<open>density_matrix_tensor\<close> (Day 15).\<close>

lemma tensor_pure_density:
  fixes \<psi> \<phi> :: "complex Matrix.vec"
  assumes \<psi>_dim: "dim_vec \<psi> = m"
      and \<phi>_dim: "dim_vec \<phi> = p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "pure_density (tensor_vec \<psi> \<phi>) =
         (pure_density \<psi>) \<Otimes> (pure_density \<phi>)"
proof -
  let ?T = "tensor_vec \<psi> \<phi>"
  let ?A = "pure_density \<psi>"
  let ?B = "pure_density \<phi>"
  have T_dim: "dim_vec ?T = m * p"
    using tensor_vec_dim \<psi>_dim \<phi>_dim by simp
  have lhs_eq: "pure_density ?T = outer_sum (m * p) [?T]"
    using T_dim by (simp add: pure_density_def)
  have lhs_car: "pure_density ?T \<in> carrier_mat (m*p) (m*p)"
    using lhs_eq by force
  have A_car: "?A \<in> carrier_mat m m"
    using \<psi>_dim by (simp add: pure_density_def, simp add: carrier_matI)
  have B_car: "?B \<in> carrier_mat p p"
    using \<phi>_dim by (simp add: pure_density_def, simp add: carrier_matI)
  have rhs_dim_row: "dim_row (?A \<Otimes> ?B) = m * p" using A_car B_car by auto
  have rhs_dim_col: "dim_col (?A \<Otimes> ?B) = m * p" using A_car B_car by auto

  show ?thesis
  proof (rule eq_matI)
    show "dim_row (pure_density ?T) = dim_row (?A \<Otimes> ?B)"
      using lhs_car rhs_dim_row by auto
    show "dim_col (pure_density ?T) = dim_col (?A \<Otimes> ?B)"
      using lhs_car rhs_dim_col by auto
  next
    fix r c
    assume rc: "r < dim_row (?A \<Otimes> ?B)" "c < dim_col (?A \<Otimes> ?B)"
    from rc rhs_dim_row rhs_dim_col have r_lt: "r < m * p" and c_lt: "c < m * p"
      by auto

    let ?r1 = "r div p"  let ?r2 = "r mod p"
    let ?c1 = "c div p"  let ?c2 = "c mod p"
    have r1_lt: "?r1 < m" using r_lt less_mult_imp_div_less by blast
    have r2_lt: "?r2 < p" using p_pos by simp
    have c1_lt: "?c1 < m" using c_lt less_mult_imp_div_less by blast
    have c2_lt: "?c2 < p" using p_pos by simp

    \<comment> \<open>LHS entry.\<close>
    have lhs_ent: "pure_density ?T $$ (r, c) = ?T $ r * cnj (?T $ c)"
      using lhs_eq outer_sum_singleton_index[OF r_lt c_lt] by simp
    have T_r: "?T $ r = \<psi> $ ?r1 * \<phi> $ ?r2"
      using tensor_vec_index[OF \<psi>_dim \<phi>_dim r_lt] .
    have T_c: "?T $ c = \<psi> $ ?c1 * \<phi> $ ?c2"
      using tensor_vec_index[OF \<psi>_dim \<phi>_dim c_lt] .
    have lhs_ent': "pure_density ?T $$ (r, c)
                    = \<psi> $ ?r1 * \<phi> $ ?r2 * (cnj (\<psi> $ ?c1) * cnj (\<phi> $ ?c2))"
      using lhs_ent T_r T_c by simp

    \<comment> \<open>RHS entry via \<open>index_tensor_mat\<close>.\<close>
    have AB_ent: "(?A \<Otimes> ?B) $$ (r, c) = ?A $$ (?r1, ?c1) * ?B $$ (?r2, ?c2)"
    proof -
      have drA: "dim_row ?A = m" using A_car by auto
      have dcA: "dim_col ?A = m" using A_car by auto
      have drB: "dim_row ?B = p" using B_car by auto
      have dcB: "dim_col ?B = p" using B_car by auto
      show ?thesis
        using index_tensor_mat[OF drA dcA drB dcB] r_lt c_lt m_pos p_pos
        by simp
    qed
    have A_ent: "?A $$ (?r1, ?c1) = \<psi> $ ?r1 * cnj (\<psi> $ ?c1)"
    proof -
      have "?A = outer_sum m [\<psi>]"
        using \<psi>_dim by (simp add: pure_density_def)
      thus ?thesis
        using outer_sum_singleton_index[OF r1_lt c1_lt] by simp
    qed
    have B_ent: "?B $$ (?r2, ?c2) = \<phi> $ ?r2 * cnj (\<phi> $ ?c2)"
    proof -
      have "?B = outer_sum p [\<phi>]"
        using \<phi>_dim by (simp add: pure_density_def)
      thus ?thesis
        using outer_sum_singleton_index[OF r2_lt c2_lt] by simp
    qed
    have rhs_ent: "(?A \<Otimes> ?B) $$ (r, c)
                   = (\<psi> $ ?r1 * cnj (\<psi> $ ?c1)) * (\<phi> $ ?r2 * cnj (\<phi> $ ?c2))"
      using AB_ent A_ent B_ent by simp

    show "pure_density ?T $$ (r, c) = (?A \<Otimes> ?B) $$ (r, c)"
      using lhs_ent' rhs_ent by (simp add: mult.commute mult.left_commute)
  qed
qed

subsection \<open>Partial traces: motivation\<close>

text \<open>For a density matrix $\rho\in L(\Hil_A\otimes\Hil_B)$ and measurements $\{M_\alpha\}$ in
lab A, which act as $M_\alpha\otimes I$, $p_\alpha(\rho)=\Tr((M_\alpha^*M_\alpha\otimes I)\rho)$.
The notes announce a density matrix $\rho_A\in L(\Hil_A)$ with
$\Tr_{\Hil_A\otimes\Hil_B}((M^*M\otimes I)\rho)=\Tr_{\Hil_A}(M^*M\rho_A)$ for all $M$; it is
constructed on Day 15.\<close>

end
