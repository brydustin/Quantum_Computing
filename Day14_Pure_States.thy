(*  Title:   Day14_Pure_States.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 28 September 2011 (Day 14)
*)

theory Day14_Pure_States
  imports Day09_POVMs_Entanglement Day13_Density_Matrices
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

text \<open>$UDU^*=\sum_iD_i\,\ketbra{u_i}{u_i}$ for the columns $u_i$ of $U$, which are unit vectors: the
spectral decomposition of a density matrix is the ensemble of its eigenvectors weighted by the
eigenvalues.\<close>

lemma unitary_diag_ensemble:
  assumes U: "U \<in> carrier_mat n n" and D: "length D = n"
  shows "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = ensemble_density n (map (\<lambda>i. (D ! i, Matrix.col U i)) [0..<n])"
proof (rule eq_matI)
  let ?E = "map (\<lambda>i. (D ! i, Matrix.col U i)) [0..<n]"
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] D by simp
  fix r c assume "r < dim_row (ensemble_density n ?E)" "c < dim_col (ensemble_density n ?E)"
  hence r: "r < n" and c: "c < n" using ensemble_density_carrier_dim[of n ?E] by auto
  have "(U * diag_mat_of_real D * (U\<^sup>\<dagger>)) $$ (r, c) = (\<Sum>k<n. U $$ (r, k) * complex_of_real (D ! k) * cnj (U $$ (c, k)))"
    using r c U D
    by (simp add: mat_mult_entry[OF mult_carrier_mat[OF U Dc] dagger_carrier[OF U] r c] diag_mat_of_real_def
                  mat_diag_mult_right[OF U] dagger_def)
  also have "\<dots> = ensemble_density n ?E $$ (r, c)"
    using r c U by (simp add: ensemble_density_index[OF r c] sum_list_sum_nth atLeast0LessThan mult_ac)
  finally show "(U * diag_mat_of_real D * (U\<^sup>\<dagger>)) $$ (r, c) = ensemble_density n ?E $$ (r, c)" .
qed (use U in \<open>simp_all add: carrier_matD[OF ensemble_density_carrier_dim]\<close>)

lemma unitary_col_quantum_state:
  assumes U: "U \<in> carrier_mat n n" and Uu: "unitary U" and i: "i < n"
  shows "quantum_state n (Matrix.col U i)"
proof -
  have "\<langle>Matrix.col U i | Matrix.col U i\<rangle> = 1" using unitary_cols_orthonormal[OF Uu] i U by simp
  hence "complex_of_real ((\<parallel>Matrix.col U i\<parallel>)\<^sup>2) = 1" by (simp only: cpx_vec_length_inner_prod)
  hence "(\<parallel>Matrix.col U i\<parallel>)\<^sup>2 = 1" using of_real_eq_1_iff by blast
  moreover have "0 \<le> \<parallel>Matrix.col U i\<parallel>" by (simp add: cpx_vec_length_def sum_nonneg)
  ultimately show ?thesis using U by (auto simp: quantum_state_def power2_eq_1_iff)
qed

theorem spectral_ensemble_exists:
  fixes \<rho> :: "complex Matrix.mat"
  assumes dm: "density_matrix n \<rho>"
  shows "\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>"
proof -
  have \<rho>c: "\<rho> \<in> carrier_mat n n" and psd: "psd \<rho>" and tr: "Tr \<rho> = 1" using dm by (auto simp: density_matrix_def)
  obtain U D where U: "U \<in> carrier_mat n n" and Uu: "unitary U" and D: "length D = n"
    and Dnn: "\<forall>i<n. 0 \<le> D ! i" and \<rho>_eq: "\<rho> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF \<rho>c psd] by blast
  let ?E = "map (\<lambda>i. (D ! i, Matrix.col U i)) [0..<n]"
  have "complex_of_real (sum_list D) = Tr \<rho>" unfolding \<rho>_eq by (rule Tr_unitary_diag[OF U Uu D, symmetric])
  hence sumD: "sum_list D = 1" using tr by (simp only: of_real_eq_1_iff)
  have sum: "sum_list (map (\<lambda>i. D ! i) [0..<n]) = 1" using sumD D by (simp add: sum_list_sum_nth)
  have "ensemble n ?E"
  proof (unfold ensemble_def, intro conjI)
    have mem: "0 \<le> fst x \<and> quantum_state n (snd x)" if "x \<in> set ?E" for x
    proof -
      from that obtain i where i: "i < n" and x: "x = (D ! i, Matrix.col U i)" by auto
      show ?thesis using Dnn i unitary_col_quantum_state[OF U Uu i] by (simp add: x)
    qed
    show "\<forall>x \<in> set ?E. case x of (p, \<psi>) \<Rightarrow> 0 \<le> p \<and> quantum_state n \<psi>"
      using mem by (simp add: case_prod_beta)
    show "(\<Sum>(p, _) \<leftarrow> ?E. p) = 1" using sum by (simp add: o_def)
  qed
  moreover have "ensemble_density n ?E = \<rho>" unfolding \<rho>_eq by (rule unitary_diag_ensemble[OF U D, symmetric])
  ultimately have "ensemble n ?E \<and> ensemble_density n ?E = \<rho>" ..
  thus ?thesis by (rule exI)
qed

text \<open>The spectral ensemble: every density matrix comes from an ensemble.\<close>

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

text \<open>A companion fact not in the notes: a density matrix is pure iff it is idempotent.  For
$\rho=UDU^*$ idempotence makes every eigenvalue $0$ or $1$, and the trace makes exactly one of them
$1$.\<close>

theorem pure_density_iff_idempotent:
  fixes \<rho> :: "complex Matrix.mat"
  assumes dm: "density_matrix n \<rho>"
  shows "pure_state_density n \<rho> \<longleftrightarrow> \<rho> * \<rho> = \<rho>"
proof
  assume "pure_state_density n \<rho>"
  then obtain \<psi> where \<psi>: "quantum_state n \<psi>" and \<rho>_eq: "\<rho> = pure_density \<psi>"
    by (auto simp: pure_state_density_def)
  have \<psi>n: "dim_vec \<psi> = n" and one: "\<langle>\<psi>|\<psi>\<rangle> = 1"
    using \<psi> by (simp_all add: quantum_state_def flip: cpx_vec_length_inner_prod)
  let ?V = "mat_of_cols n [\<psi>]"
  have Vc: "?V \<in> carrier_mat n 1" using mat_of_cols_carrier(1)[of n "[\<psi>]"] by simp
  have "(?V\<^sup>\<dagger>) * ?V = 1\<^sub>m 1"
    using inner_prod_sum[OF \<psi>n \<psi>n] one
    by (intro eq_matI) (auto simp: mat_mult_entry[OF dagger_carrier[OF Vc] Vc] dagger_def mat_of_cols_index \<psi>n atLeast0LessThan)
  hence "(?V * (?V\<^sup>\<dagger>)) * (?V * (?V\<^sup>\<dagger>)) = ?V * (?V\<^sup>\<dagger>)"
    using Vc dagger_carrier[OF Vc]
    by (simp only: assoc_mult_mat[OF Vc dagger_carrier[OF Vc] mult_carrier_mat[OF Vc dagger_carrier[OF Vc]]]
                   assoc_mult_mat[OF dagger_carrier[OF Vc] Vc dagger_carrier[OF Vc], symmetric]
                   left_mult_one_mat[OF dagger_carrier[OF Vc]])
  thus "\<rho> * \<rho> = \<rho>" by (simp add: \<rho>_eq pure_density_def \<psi>n outer_sum_def)
next
  assume idem: "\<rho> * \<rho> = \<rho>"
  have \<rho>c: "\<rho> \<in> carrier_mat n n" and psd: "psd \<rho>" and tr: "Tr \<rho> = 1" using dm by (auto simp: density_matrix_def)
  obtain U D where U: "U \<in> carrier_mat n n" and Uu: "unitary U" and D: "length D = n"
    and \<rho>_eq: "\<rho> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF \<rho>c psd] by blast
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] D by simp
  have "U * (diag_mat_of_real D * diag_mat_of_real D) * (U\<^sup>\<dagger>) = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using idem unfolding \<rho>_eq unitary_conj_mult[OF U Uu Dc Dc] .
  hence DD: "diag_mat_of_real D * diag_mat_of_real D = diag_mat_of_real D"
    using unitary_conj_cancel[OF U Uu mult_carrier_mat[OF Dc Dc]] unitary_conj_cancel[OF U Uu Dc] by simp
  have D01: "D ! i = 0 \<or> D ! i = 1" if i: "i < n" for i
  proof -
    have "mat_diag n (\<lambda>k. complex_of_real (D ! k) * complex_of_real (D ! k)) $$ (i, i)
        = mat_diag n (\<lambda>k. complex_of_real (D ! k)) $$ (i, i)"
      using arg_cong[OF DD, of "\<lambda>M. M $$ (i, i)"] by (simp only: diag_mat_of_real_def mat_diag_diag D)
    hence "complex_of_real (D ! i * D ! i) = complex_of_real (D ! i)" using i by (simp add: mat_diag_def)
    hence "D ! i * D ! i = D ! i" by (rule of_real_eq_iff[THEN iffD1])
    hence "D ! i * (D ! i - 1) = 0" by (simp add: algebra_simps)
    thus ?thesis by auto
  qed
  have "complex_of_real (sum_list D) = Tr \<rho>" unfolding \<rho>_eq by (rule Tr_unitary_diag[OF U Uu D, symmetric])
  hence sumD: "sum_list D = 1" using tr by (simp only: of_real_eq_1_iff)
  obtain j where j: "j < n" "D ! j = 1" and others: "\<forall>i<n. i \<noteq> j \<longrightarrow> D ! i = 0"
    using sum_zero_one_eq_one[OF D01 D sumD] by blast
  have uj: "quantum_state n (Matrix.col U j)" by (rule unitary_col_quantum_state[OF U Uu j(1)])
  have "\<rho> = pure_density (Matrix.col U j)"
  proof (rule eq_matI)
    fix r c assume "r < dim_row (pure_density (Matrix.col U j))" "c < dim_col (pure_density (Matrix.col U j))"
    hence r: "r < n" and c: "c < n" using U by (simp_all add: pure_density_def)
    have "\<rho> $$ (r, c) = (\<Sum>i<n. complex_of_real (D ! i) * Matrix.col U i $ r * cnj (Matrix.col U i $ c))"
      unfolding \<rho>_eq unitary_diag_ensemble[OF U D]
      by (simp add: ensemble_density_index[OF r c] sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>i<n. if i = j then Matrix.col U j $ r * cnj (Matrix.col U j $ c) else 0)"
      by (intro sum.cong refl) (auto simp: j others)
    also have "\<dots> = pure_density (Matrix.col U j) $$ (r, c)"
      using j(1) U r c by (simp add: sum.delta pure_density_def outer_sum_singleton_index)
    finally show "\<rho> $$ (r, c) = pure_density (Matrix.col U j) $$ (r, c)" .
  qed (use \<rho>c U in \<open>simp_all add: pure_density_def\<close>)
  thus "pure_state_density n \<rho>" using dm uj unfolding pure_state_density_def by blast
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
  have \<psi>d: "dim_vec \<psi> = n" using st by (simp add: quantum_state_def)
  have \<psi>1: "\<langle>\<psi>|\<psi>\<rangle> = 1"
    using st unfolding quantum_state_def by (simp flip: cpx_vec_length_inner_prod)
  have E: "\<forall>(q, \<phi>) \<in> set E. 0 \<le> q \<and> dim_vec \<phi> = n"
    using ens by (auto simp: ensemble_def quantum_state_def)
  have E': "\<forall>(q, \<phi>) \<in> set E. dim_vec \<phi> = n" using E by auto
  have \<psi>id: "dim_vec \<psi>\<^sub>i = n" using E mem by auto
  define \<beta> where "\<beta> = \<langle>\<psi>|\<psi>\<^sub>i\<rangle>"
  define w where "w = \<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>"
  have wd: "dim_vec w = n" and d: "dim_vec \<psi>\<^sub>i = dim_vec (\<beta> \<cdot>\<^sub>v \<psi>)"
    and wd': "dim_vec \<psi>\<^sub>i = dim_vec w" and \<psi>wd: "dim_vec \<psi> = dim_vec w"
    by (simp_all add: w_def \<psi>id \<psi>d)
  have \<psi>w: "\<langle>\<psi>|w\<rangle> = 0"
    unfolding w_def inner_prod_right_minus'[OF d] inner_prod_right_smult' \<psi>1 by (simp add: \<beta>_def)
  have "\<langle>w | ensemble_density n E *\<^sub>v w\<rangle> = \<langle>w | \<langle>\<psi>|w\<rangle> \<cdot>\<^sub>v \<psi>\<rangle>"
    unfolding dens pure_density_def Let_def \<psi>d by (simp add: outer_sum_singleton_mult_vec[OF \<psi>d wd])
  also have "\<dots> = 0" unfolding \<psi>w by (simp add: inner_prod_right_smult')
  finally have quad0: "\<langle>w | ensemble_density n E *\<^sub>v w\<rangle> = 0" .
  have "complex_of_real (\<Sum>(q, \<phi>) \<leftarrow> E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)
        = (\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>)"
    by (induction E) (auto simp: case_prod_beta complex_norm_square[symmetric] mult.assoc)
  hence S0: "(\<Sum>(q, \<phi>) \<leftarrow> E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2) = 0"
    using quad0 ensemble_density_quad_form[OF E' wd] by simp
  have nn: "0 \<le> x" if "x \<in> set (map (\<lambda>(q, \<phi>). q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2) E)" for x
    using that E by auto
  have "\<forall>x \<in> set (map (\<lambda>(q, \<phi>). q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2) E). x = 0"
    by (rule sum_list_nonneg_eq_0_iff[THEN iffD1, OF nn S0])
  hence "p * (cmod \<langle>\<psi>\<^sub>i|w\<rangle>)\<^sup>2 = 0" using mem by auto
  hence \<psi>iw: "\<langle>\<psi>\<^sub>i|w\<rangle> = 0" using ppos by simp
  have "\<langle>\<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi> | w\<rangle> = \<langle>\<psi>\<^sub>i|w\<rangle> - cnj \<beta> * \<langle>\<psi>|w\<rangle>"
    by (simp only: inner_prod_left_minus'[OF d wd'] inner_prod_distrib_left[OF \<psi>wd])
  hence "\<langle>w|w\<rangle> = 0" unfolding \<psi>iw \<psi>w w_def[symmetric] by simp
  hence w0: "w = 0\<^sub>v n" using inner_prod_self_eq_zero_iff[of w] wd by simp
  have "\<psi>\<^sub>i = \<beta> \<cdot>\<^sub>v \<psi>"
  proof (intro eq_vecI)
    fix i assume "i < dim_vec (\<beta> \<cdot>\<^sub>v \<psi>)"
    with w0 show "\<psi>\<^sub>i $ i = (\<beta> \<cdot>\<^sub>v \<psi>) $ i"
      using \<psi>id \<psi>d by (auto dest!: arg_cong[where f = "\<lambda>v. v $ i"] simp: w_def)
  qed (simp add: \<psi>id \<psi>d)
  thus ?thesis by blast
qed

subsection \<open>Composite ensembles\<close>

text \<open>For ensembles $\{p_i,\psi_i\}$ in lab A and $\{q_l,\phi_l\}$ in lab B the composite is
the ensemble $\{p_iq_l,\psi_i\otimes\phi_l\}$ with density matrix
$\rho=\sum_{i,l}p_iq_l\ketbra{\psi_i}{\psi_i}\otimes\ketbra{\phi_l}{\phi_l}$, because
$\ketbra{\psi\otimes\phi}{\psi\otimes\phi}=\ketbra\psi\psi\otimes\ketbra\phi\phi$ (checked on
elementary tensors $h\otimes k$).  The identity is formalised below; that $\rho_1\otimes\rho_2$ is
again a density matrix is \<open>density_matrix_tensor\<close> (Day 15).\<close>

text \<open>$|\psi\otimes\varphi\rangle\langle\psi\otimes\varphi|=|\psi\rangle\langle\psi|\otimes|\varphi\rangle\langle\varphi|$.\<close>

lemma outer_sum_tensor:
  assumes \<psi>: "dim_vec \<psi> = n" and \<phi>: "dim_vec \<phi> = m"
  shows "outer_sum (n * m) [tensor_vec \<psi> \<phi>] = outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]"
proof (rule eq_matI)
  have A: "outer_sum n [\<psi>] \<in> carrier_mat n n" and B: "outer_sum m [\<phi>] \<in> carrier_mat m m"
    by (rule outer_sum_carrier)+
  fix r s assume "r < dim_row (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>])" "s < dim_col (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>])"
  hence r: "r < n * m" and s: "s < n * m" using carrier_matD[OF A] carrier_matD[OF B] by simp_all
  have m: "0 < m" using r by (cases m) auto
  have rd: "r div m < n" "s div m < n" using r s by (simp_all add: less_mult_imp_div_less)
  have rm: "r mod m < m" "s mod m < m" using m by simp_all
  have "outer_sum (n * m) [tensor_vec \<psi> \<phi>] $$ (r, s) = tensor_vec \<psi> \<phi> $ r * cnj (tensor_vec \<psi> \<phi> $ s)"
    by (rule outer_sum_singleton_index[OF r s])
  also have "\<dots> = (\<psi> $ (r div m) * \<phi> $ (r mod m)) * cnj (\<psi> $ (s div m) * \<phi> $ (s mod m))"
    using tensor_vec_index[OF \<psi> \<phi> r] tensor_vec_index[OF \<psi> \<phi> s] by simp
  also have "\<dots> = outer_sum n [\<psi>] $$ (r div m, s div m) * outer_sum m [\<phi>] $$ (r mod m, s mod m)"
    using outer_sum_singleton_index[OF rd] outer_sum_singleton_index[OF rm] by (simp add: algebra_simps)
  also have "\<dots> = (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]) $$ (r, s)"
  proof -
    have n: "0 < n" using r by (cases n) auto
    show ?thesis
      by (rule index_tensor_mat[of _ n n _ m m, symmetric]) (use carrier_matD[OF A] carrier_matD[OF B] r s m n in simp_all)
  qed
  finally show "outer_sum (n * m) [tensor_vec \<psi> \<phi>] $$ (r, s) = (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]) $$ (r, s)" .
qed (simp_all add: outer_sum_def)

lemma tensor_pure_density:
  fixes \<psi> \<phi> :: "complex Matrix.vec"
  assumes \<psi>_dim: "dim_vec \<psi> = m"
      and \<phi>_dim: "dim_vec \<phi> = p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "pure_density (tensor_vec \<psi> \<phi>) =
         (pure_density \<psi>) \<Otimes> (pure_density \<phi>)"
  unfolding pure_density_def using \<psi>_dim \<phi>_dim by (simp add: tensor_vec_dim outer_sum_tensor)

text \<open>For ensembles $\{p_i,\psi_i\}$ on $\Hil_A$ and $\{q_j,\varphi_j\}$ on $\Hil_B$, the composite ensemble
is $\{p_iq_j,\psi_i\otimes\varphi_j\}$.\<close>

definition product_ensemble :: "(real \<times> complex Matrix.vec) list \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> (real \<times> complex Matrix.vec) list" where
  "product_ensemble EA EB = map (\<lambda>((p, \<psi>), (q, \<phi>)). (p * q, tensor_vec \<psi> \<phi>)) (List.product EA EB)"

lemma sum_list_product:
  fixes f :: "'a \<Rightarrow> real" and g :: "'b \<Rightarrow> real"
  shows "(\<Sum>(x, y) \<leftarrow> List.product xs ys. f x * g y) = (\<Sum>x \<leftarrow> xs. f x) * (\<Sum>y \<leftarrow> ys. g y)"
  by (induction xs) (simp_all add: sum_list_const_mult algebra_simps comp_def)

lemma product_ensemble_ensemble:
  assumes A: "ensemble n EA" and B: "ensemble m EB"
  shows "ensemble (n * m) (product_ensemble EA EB)"
proof -
  have As: "\<forall>(p, \<psi>) \<in> set EA. p \<ge> 0 \<and> quantum_state n \<psi>" and Asum: "(\<Sum>(p, _) \<leftarrow> EA. p) = 1"
    using A unfolding ensemble_def by blast+
  have Bs: "\<forall>(q, \<phi>) \<in> set EB. q \<ge> 0 \<and> quantum_state m \<phi>" and Bsum: "(\<Sum>(q, _) \<leftarrow> EB. q) = 1"
    using B unfolding ensemble_def by blast+
  have mem: "\<forall>(r, u) \<in> set (product_ensemble EA EB). r \<ge> 0 \<and> quantum_state (n * m) u"
  proof -
    have As': "\<And>p \<psi>. (p, \<psi>) \<in> set EA \<Longrightarrow> p \<ge> 0 \<and> quantum_state n \<psi>" using As by blast
    have Bs': "\<And>q \<phi>. (q, \<phi>) \<in> set EB \<Longrightarrow> q \<ge> 0 \<and> quantum_state m \<phi>" using Bs by blast
    show ?thesis by (auto simp: product_ensemble_def dest!: As' Bs' intro: tensor_of_states_is_state)
  qed
  have "(\<Sum>(r, _) \<leftarrow> product_ensemble EA EB. r) = (\<Sum>(x, y) \<leftarrow> List.product EA EB. fst x * fst y)"
    by (simp add: product_ensemble_def comp_def split_def)
  also have "\<dots> = (\<Sum>x \<leftarrow> EA. fst x) * (\<Sum>y \<leftarrow> EB. fst y)" by (rule sum_list_product)
  also have "\<dots> = 1" using Asum Bsum by (simp add: split_def)
  finally show ?thesis unfolding ensemble_def using mem by blast
qed

text \<open>The notes' composite density $\sum_{i,j}p_iq_j\,|\psi_i\rangle\langle\psi_i|\otimes|\varphi_j\rangle\langle\varphi_j|$
is the density of the composite ensemble, hence a density matrix.\<close>

definition composite_density :: "nat \<Rightarrow> nat \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> complex Matrix.mat" where
  "composite_density n m EA EB = foldr (\<lambda>((p, \<psi>), (q, \<phi>)) acc.
      complex_of_real (p * q) \<cdot>\<^sub>m (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]) + acc) (List.product EA EB) (0\<^sub>m (n * m) (n * m))"

lemma composite_density_eq:
  assumes A: "ensemble n EA" and B: "ensemble m EB"
  shows "composite_density n m EA EB = ensemble_density (n * m) (product_ensemble EA EB)"
proof -
  have dims: "\<forall>((p, \<psi>), (q, \<phi>)) \<in> set (List.product EA EB). dim_vec \<psi> = n \<and> dim_vec \<phi> = m"
    using A B unfolding ensemble_def quantum_state_def by auto
  have "\<And>L. \<forall>((p, \<psi>), (q, \<phi>)) \<in> set L. dim_vec \<psi> = n \<and> dim_vec \<phi> = m \<Longrightarrow>
        foldr (\<lambda>((p, \<psi>), (q, \<phi>)) acc. complex_of_real (p * q) \<cdot>\<^sub>m (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]) + acc) L (0\<^sub>m (n * m) (n * m))
        = ensemble_density (n * m) (map (\<lambda>((p, \<psi>), (q, \<phi>)). (p * q, tensor_vec \<psi> \<phi>)) L)"
  proof -
    fix L :: "((real \<times> complex Matrix.vec) \<times> (real \<times> complex Matrix.vec)) list"
    show "\<forall>((p, \<psi>), (q, \<phi>)) \<in> set L. dim_vec \<psi> = n \<and> dim_vec \<phi> = m \<Longrightarrow> ?thesis L" for dummy :: unit
      by (induction L) (auto simp: ensemble_density_def outer_sum_tensor)
  qed
  thus ?thesis using dims unfolding composite_density_def product_ensemble_def by blast
qed

theorem composite_density_is_dm:
  assumes A: "ensemble n EA" and B: "ensemble m EB"
  shows "density_matrix (n * m) (composite_density n m EA EB)"
  unfolding composite_density_eq[OF A B] by (rule ensemble_density_is_dm[OF product_ensemble_ensemble[OF A B]])

subsection \<open>Partial traces: motivation\<close>

text \<open>For a density matrix $\rho\in L(\Hil_A\otimes\Hil_B)$ and measurements $\{M_\alpha\}$ in
lab A, which act as $M_\alpha\otimes I$, $p_\alpha(\rho)=\Tr((M_\alpha^*M_\alpha\otimes I)\rho)$.
The notes announce a density matrix $\rho_A\in L(\Hil_A)$ with
$\Tr_{\Hil_A\otimes\Hil_B}((M^*M\otimes I)\rho)=\Tr_{\Hil_A}(M^*M\rho_A)$ for all $M$; it is
constructed on Day 15.\<close>

end
