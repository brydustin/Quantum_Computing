theory Day15_Partial_Trace_A
  imports Day16_Density_Postulates
begin

section \<open>Day 15: the partial trace over $A$ (D15-6)\<close>

text \<open>Reordering the basis: for a bijection $\sigma$ of $\{0,\dots,N-1\}$ the matrix
$(x_{\sigma(r)\sigma(s)})$ has the trace of $X$ and is Hermitian, resp.\ positive, with $X$.\<close>

definition perm_conj :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "perm_conj N \<sigma> X = Matrix.mat N N (\<lambda>(r, s). X $$ (\<sigma> r, \<sigma> s))"

lemma perm_conj_carrier [simp]: "perm_conj N \<sigma> X \<in> carrier_mat N N"
  by (simp add: perm_conj_def)

lemma perm_conj_dims [simp]: "dim_row (perm_conj N \<sigma> X) = N" "dim_col (perm_conj N \<sigma> X) = N"
  by (simp_all add: perm_conj_def)

lemma perm_conj_trace:
  assumes \<sigma>: "bij_betw \<sigma> {..<N} {..<N}" and X: "X \<in> carrier_mat N N"
  shows "Tr (perm_conj N \<sigma> X) = Tr X"
proof -
  have "Tr (perm_conj N \<sigma> X) = (\<Sum>r<N. X $$ (\<sigma> r, \<sigma> r))"
    by (simp add: Tr_def perm_conj_def)
  also have "\<dots> = (\<Sum>r<N. X $$ (r, r))"
    using sum.reindex_bij_betw[OF \<sigma>, of "\<lambda>r. X $$ (r, r)"] by simp
  also have "\<dots> = Tr X" using X by (simp add: Tr_def)
  finally show ?thesis .
qed

lemma perm_conj_hermitian:
  assumes \<sigma>: "\<And>r. r < N \<Longrightarrow> \<sigma> r < N" and X: "X \<in> carrier_mat N N" and h: "hermitian X"
  shows "hermitian (perm_conj N \<sigma> X)"
  unfolding hermitian_def
proof (rule eq_matI)
  have Xd: "X\<^sup>\<dagger> = X" using h by (simp add: hermitian_def)
  fix r s assume "r < dim_row (perm_conj N \<sigma> X)" "s < dim_col (perm_conj N \<sigma> X)"
  hence r: "r < N" and s: "s < N" by simp_all
  have "X $$ (\<sigma> r, \<sigma> s) = X\<^sup>\<dagger> $$ (\<sigma> r, \<sigma> s)" using Xd by simp
  also have "\<dots> = cnj (X $$ (\<sigma> s, \<sigma> r))" using X \<sigma>[OF r] \<sigma>[OF s] by (simp add: dagger_def)
  finally show "(perm_conj N \<sigma> X)\<^sup>\<dagger> $$ (r, s) = perm_conj N \<sigma> X $$ (r, s)"
    using r s by (simp add: dagger_def perm_conj_def)
qed (simp_all add: dagger_def)

lemma perm_conj_psd:
  assumes \<sigma>: "bij_betw \<sigma> {..<N} {..<N}" and X: "X \<in> carrier_mat N N" and ps: "psd X"
  shows "psd (perm_conj N \<sigma> X)"
proof -
  have \<sigma>N: "\<And>r. r < N \<Longrightarrow> \<sigma> r < N" using bij_betwE[OF \<sigma>] by auto
  define \<tau> where "\<tau> = inv_into {..<N} \<sigma>"
  have \<tau>\<sigma>: "\<And>r. r < N \<Longrightarrow> \<tau> (\<sigma> r) = r" unfolding \<tau>_def using bij_betw_inv_into_left[OF \<sigma>] by simp
  have h: "hermitian (perm_conj N \<sigma> X)" by (rule perm_conj_hermitian[OF \<sigma>N X psd_hermitian[OF ps]])
  have q: "0 \<le> Re (Quantum.inner_prod v (perm_conj N \<sigma> X *\<^sub>v v))" if v: "dim_vec v = N" for v
  proof -
    define w where "w = Matrix.vec N (\<lambda>t. v $ \<tau> t)"
    have wd: "dim_vec w = N" by (simp add: w_def)
    have w\<sigma>: "\<And>r. r < N \<Longrightarrow> w $ \<sigma> r = v $ r" using \<sigma>N \<tau>\<sigma> by (simp add: w_def)
    have "Quantum.inner_prod v (perm_conj N \<sigma> X *\<^sub>v v)
          = (\<Sum>r = 0..<N. \<Sum>s = 0..<N. cnj (v $ r) * perm_conj N \<sigma> X $$ (r, s) * v $ s)"
      by (rule inner_T_double_sum[OF perm_conj_carrier v v])
    also have "\<dots> = (\<Sum>r<N. \<Sum>s<N. cnj (w $ \<sigma> r) * X $$ (\<sigma> r, \<sigma> s) * w $ \<sigma> s)"
      by (simp add: perm_conj_def w\<sigma> atLeast0LessThan)
    also have "\<dots> = (\<Sum>a<N. \<Sum>b<N. cnj (w $ a) * X $$ (a, b) * w $ b)"
    proof -
      have inner: "\<And>a. (\<Sum>s<N. cnj (w $ a) * X $$ (a, \<sigma> s) * w $ \<sigma> s) = (\<Sum>b<N. cnj (w $ a) * X $$ (a, b) * w $ b)"
        using sum.reindex_bij_betw[OF \<sigma>, of "\<lambda>b. cnj (w $ _) * X $$ (_, b) * w $ b"] by simp
      have "(\<Sum>r<N. \<Sum>s<N. cnj (w $ \<sigma> r) * X $$ (\<sigma> r, \<sigma> s) * w $ \<sigma> s)
            = (\<Sum>r<N. \<Sum>b<N. cnj (w $ \<sigma> r) * X $$ (\<sigma> r, b) * w $ b)"
        by (rule sum.cong) (simp_all add: inner)
      also have "\<dots> = (\<Sum>a<N. \<Sum>b<N. cnj (w $ a) * X $$ (a, b) * w $ b)"
        using sum.reindex_bij_betw[OF \<sigma>, of "\<lambda>a. \<Sum>b<N. cnj (w $ a) * X $$ (a, b) * w $ b"] by simp
      finally show ?thesis .
    qed
    also have "\<dots> = Quantum.inner_prod w (X *\<^sub>v w)"
      using inner_T_double_sum[OF X wd wd] by (simp add: atLeast0LessThan)
    finally have e: "Quantum.inner_prod v (perm_conj N \<sigma> X *\<^sub>v v) = Quantum.inner_prod w (X *\<^sub>v w)" .
    have "\<forall>x. dim_vec x = dim_row X \<longrightarrow> 0 \<le> Re (Quantum.inner_prod x (X *\<^sub>v x))" using ps unfolding psd_def by blast
    thus ?thesis unfolding e using wd carrier_matD(1)[OF X] by simp
  qed
  show ?thesis unfolding psd_def using h q by simp
qed

text \<open>Exchanging the factors: with $\sigma(i m+k)=k p+i$ ($i<p$, $k<m$), tracing out $A$ is tracing out
$B$ after the exchange.\<close>

definition swap_index :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "swap_index m p r = (r mod m) * p + r div m"

lemma swap_index_less:
  assumes "r < m * p" shows "swap_index m p r < m * p"
proof -
  have m: "0 < m" using assms by (cases m) auto
  have "r div m < p" using assms by (simp add: less_mult_imp_div_less mult.commute)
  moreover have "r mod m < m" using m by simp
  ultimately have "(r mod m) * p + r div m < (r mod m) * p + p" by simp
  also have "\<dots> = Suc (r mod m) * p" by simp
  also have "\<dots> \<le> m * p" using \<open>r mod m < m\<close> by (intro mult_le_mono1) simp
  finally show ?thesis unfolding swap_index_def .
qed

lemma swap_index_bij: "bij_betw (swap_index m p) {..<m * p} {..<m * p}"
proof (rule bij_betwI[where g = "swap_index p m"])
  show "swap_index m p \<in> {..<m * p} \<rightarrow> {..<m * p}" using swap_index_less by auto
  show "swap_index p m \<in> {..<m * p} \<rightarrow> {..<m * p}" using swap_index_less[of _ p m] by (auto simp: mult.commute)
next
  fix r assume r: "r \<in> {..<m * p}"
  hence r': "r < m * p" by simp
  have m: "0 < m" and p: "0 < p" using r' by (cases m; cases p; auto)+
  have d: "r div m < p" using r' by (simp add: less_mult_imp_div_less mult.commute)
  show "swap_index p m (swap_index m p r) = r"
    unfolding swap_index_def using d m p div_mult_mod_eq[of r m] by (simp add: mult.commute)
next
  fix r assume r: "r \<in> {..<m * p}"
  hence r': "r < m * p" by simp
  have m: "0 < m" and p: "0 < p" using r' by (cases m; cases p; auto)+
  have d: "r div p < m" using r' by (simp add: less_mult_imp_div_less)
  show "swap_index m p (swap_index p m r) = r"
    unfolding swap_index_def using d m p div_mult_mod_eq[of r p] by (simp add: mult.commute)
qed

lemma partial_trace_A_as_B:
  assumes X: "X \<in> carrier_mat (m * p) (m * p)"
  shows "partial_trace_A m p X = partial_trace_B p m (perm_conj (m * p) (swap_index m p) X)"
proof (rule eq_matI)
  fix i j assume "i < dim_row (partial_trace_B p m (perm_conj (m * p) (swap_index m p) X))"
    "j < dim_col (partial_trace_B p m (perm_conj (m * p) (swap_index m p) X))"
  hence i: "i < p" and j: "j < p" by (simp_all add: partial_trace_B_def)
  have lt: "\<And>i k. i < p \<Longrightarrow> k < m \<Longrightarrow> i * m + k < m * p"
  proof -
    fix i k assume "i < p" "k < m"
    have "i * m + k < Suc i * m" using \<open>k < m\<close> by simp
    also have "\<dots> \<le> p * m" using \<open>i < p\<close> by (intro mult_le_mono1) simp
    finally show "i * m + k < m * p" by (simp add: mult.commute)
  qed
  have "partial_trace_B p m (perm_conj (m * p) (swap_index m p) X) $$ (i, j)
        = (\<Sum>k<m. X $$ (swap_index m p (i * m + k), swap_index m p (j * m + k)))"
    using i j lt by (simp add: partial_trace_B_def perm_conj_def)
  also have "\<dots> = (\<Sum>k<m. X $$ (k * p + i, k * p + j))"
    by (rule sum.cong) (simp_all add: swap_index_def)
  also have "\<dots> = partial_trace_A m p X $$ (i, j)" using i j by (simp add: partial_trace_A_def)
  finally show "partial_trace_A m p X $$ (i, j) = partial_trace_B p m (perm_conj (m * p) (swap_index m p) X) $$ (i, j)" ..
qed (simp_all add: partial_trace_A_def partial_trace_B_def)

theorem partial_trace_A_trace:
  assumes X: "X \<in> carrier_mat (m * p) (m * p)" and m: "0 < m"
  shows "Tr (partial_trace_A m p X) = Tr X"
proof -
  have Y: "perm_conj (m * p) (swap_index m p) X \<in> carrier_mat (p * m) (p * m)" by (simp add: mult.commute)
  have "Tr (partial_trace_A m p X) = Tr (perm_conj (m * p) (swap_index m p) X)"
    unfolding partial_trace_A_as_B[OF X] by (rule partial_trace_B_trace[OF Y m])
  also have "\<dots> = Tr X" by (rule perm_conj_trace[OF swap_index_bij X])
  finally show ?thesis .
qed

theorem partial_trace_A_hermitian:
  assumes X: "X \<in> carrier_mat (m * p) (m * p)" and h: "hermitian X"
  shows "hermitian (partial_trace_A m p X)"
proof -
  have Y: "perm_conj (m * p) (swap_index m p) X \<in> carrier_mat (p * m) (p * m)" by (simp add: mult.commute)
  have "hermitian (perm_conj (m * p) (swap_index m p) X)"
    by (rule perm_conj_hermitian[OF swap_index_less X h])
  thus ?thesis unfolding partial_trace_A_as_B[OF X] by (rule partial_trace_B_hermitian[OF Y])
qed

theorem partial_trace_A_is_density:
  assumes dm: "density_matrix (m * p) X" and m: "0 < m"
  shows "density_matrix p (partial_trace_A m p X)"
proof -
  have X: "X \<in> carrier_mat (m * p) (m * p)" and ps: "psd X" and tr: "Tr X = 1"
    using dm by (auto simp: density_matrix_def)
  let ?Y = "perm_conj (m * p) (swap_index m p) X"
  have "density_matrix (p * m) ?Y"
    unfolding density_matrix_def
    using perm_conj_psd[OF swap_index_bij X ps] perm_conj_trace[OF swap_index_bij X] tr
    by (simp add: mult.commute)
  thus ?thesis unfolding partial_trace_A_as_B[OF X] by (rule partial_trace_B_is_density[OF _ m])
qed

end
