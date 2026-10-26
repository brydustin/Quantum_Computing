theory Phase_Estimation
  imports Quantum_Computing_by_VP.Day10_Quantum_Gates Hermitian_Functional_Calculus.Trotter_Product_Formula
    "HOL-Analysis.Convex"
begin

section \<open>Phase estimation\<close>

text \<open>The Fourier matrix $F_N$, $(F_N)_{jk}=\omega^{jk}/\sqrt N$ with $\omega=e^{2\pi i/N}$, and phase
estimation: for $Uu=e^{2\pi i\varphi}u$, the circuit
$(F_N^*\otimes I)\,\mathrm{C}U\,(\tfrac1{\sqrt N}\sum_k\ket k\otimes u)$ leaves the register in
$\sum_j\alpha_j\ket j$ with $\alpha_j=\frac1N\sum_k e^{2\pi ik(\varphi-j/N)}$.\<close>

subsection \<open>Conventions\<close>

text \<open>This entry uses QHLProver's \<^const>\<open>hermitian\<close>, as the functional calculus does, and otherwise
the notes' and IMD's names (\<^const>\<open>unitary\<close>, inner and outer products).\<close>

hide_const (open) Complex_Matrix.unitary Complex_Matrix.inner_prod Complex_Matrix.outer_prod
  Complex_Matrix.vec_normalize Linear_Algebra.adjoint Day04_Hermitian_Matrices.hermitian
hide_fact (open) Complex_Matrix.unitary_def Complex_Matrix.outer_prod_def Complex_Matrix.vec_normalize_def
  Complex_Matrix.inner_prod_distrib_left Complex_Matrix.inner_prod_distrib_right
  Complex_Matrix.normalized_vec_norm Complex_Matrix.outer_prod_mult_vec Day04_Hermitian_Matrices.hermitian_def
  Linear_Algebra.adjoint_adjoint

lemma hermitian_notes: "Day04_Hermitian_Matrices.hermitian A \<longleftrightarrow> hermitian A"
  by (simp add: Day04_Hermitian_Matrices.hermitian_def hermitian_dagger)

lemmas hermitian_index_cnj = Day04_Hermitian_Matrices.hermitian_index[unfolded hermitian_notes]

lemma diag_mat_of_real_cmat: "diag_mat_of_real D = diag_matrix (map complex_of_real D)"
  by (rule eq_matI) (auto simp: diag_mat_of_real_def mat_diag_def diag_matrix_def)

subsection \<open>Sums of roots of unity\<close>

lemma root_of_unity_sum:
  assumes N: "0 < N" and j: "j < N" and l: "l < N"
  shows "(\<Sum>k<N. cis (2 * pi * real k * (real l - real j) / real N)) = (if l = j then of_nat N else 0)"
proof (cases "l = j")
  case True
  thus ?thesis by simp
next
  case False
  define z where "z = cis (2 * pi * (real l - real j) / real N)"
  have zk: "cis (2 * pi * real k * (real l - real j) / real N) = z ^ k" for k
    unfolding z_def DeMoivre by (simp add: mult_ac)
  have "z ^ N = cis (2 * pi * (real l - real j))"
    unfolding z_def DeMoivre using N by simp
  also have "\<dots> = 1" by (rule cis_multiple_2pi) (simp add: Ints_diff)
  finally have zN: "z ^ N = 1" .
  have z1: "z \<noteq> 1"
  proof
    assume z: "z = 1"
    have "cos (2 * pi * (real l - real j) / real N) = 1" using arg_cong[OF z, of Re] by (simp add: z_def)
    then obtain i :: int where i: "2 * pi * (real l - real j) / real N = of_int i * 2 * pi"
      by (auto simp: cos_one_2pi_int)
    hence "pi * (2 * (real l - real j)) = pi * (2 * (of_int i * real N))" using N by (simp add: field_simps)
    hence eq: "real l - real j = of_int i * real N" by simp
    have a: "of_int i * real N < 1 * real N" and b: "-1 * real N < of_int i * real N" using eq j l by linarith+
    have "of_int i < (1::real)" by (rule mult_right_less_imp_less[OF a]) simp
    moreover have "-1 < (of_int i :: real)" by (rule mult_right_less_imp_less[OF b]) simp
    ultimately
    have "i = 0" by linarith
    thus False using eq False by simp
  qed
  have "(\<Sum>k<N. z ^ k) = 0" using geometric_sum[OF z1, of N] zN by simp
  thus ?thesis using zk False by simp
qed

subsection \<open>The Fourier matrix\<close>

definition fourier :: "nat \<Rightarrow> complex Matrix.mat" where
  "fourier N = Matrix.mat N N (\<lambda>(j,k). cis (2 * pi * real j * real k / real N) / complex_of_real (sqrt (real N)))"

lemma fourier_carrier [simp]: "fourier N \<in> carrier_mat N N"
  by (simp add: fourier_def)

lemma dim_fourier [simp]: "dim_row (fourier N) = N" "dim_col (fourier N) = N"
  by (simp_all add: fourier_def)

lemma fourier_index:
  "j < N \<Longrightarrow> k < N \<Longrightarrow> fourier N $$ (j, k) = cis (2 * pi * real j * real k / real N) / complex_of_real (sqrt (real N))"
  by (simp add: fourier_def)

lemma sqrt_N_sq: "complex_of_real (sqrt (real N)) * complex_of_real (sqrt (real N)) = of_nat N"
  by (simp flip: of_real_mult)

text \<open>The entries pair to a root of unity: $\overline{F_{kj}}F_{kl}=\omega^{k(l-j)}/N$.\<close>

lemma fourier_entry_pair:
  assumes "j < N" "k < N" "l < N"
  shows "cnj (fourier N $$ (k, j)) * fourier N $$ (k, l) = cis (2 * pi * real k * (real l - real j) / real N) / of_nat N"
proof -
  have "cnj (fourier N $$ (k, j)) * fourier N $$ (k, l) =
        (cis (- (2 * pi * real k * real j / real N)) * cis (2 * pi * real k * real l / real N)) /
        (complex_of_real (sqrt (real N)) * complex_of_real (sqrt (real N)))"
    using assms by (simp add: fourier_index cis_cnj)
  also have "cis (- (2 * pi * real k * real j / real N)) * cis (2 * pi * real k * real l / real N) =
             cis (2 * pi * real k * (real l - real j) / real N)"
    by (simp add: cis_mult algebra_simps diff_divide_distrib)
  finally show ?thesis by (simp add: sqrt_N_sq)
qed

theorem fourier_unitary:
  assumes N: "0 < N"
  shows "unitary (fourier N)"
proof -
  have FF: "(fourier N)\<^sup>\<dagger> * fourier N = 1\<^sub>m N"
  proof (rule eq_matI)
    fix j l assume "j < dim_row (1\<^sub>m N :: complex Matrix.mat)" "l < dim_col (1\<^sub>m N :: complex Matrix.mat)"
    hence j: "j < N" and l: "l < N" by simp_all
    have "((fourier N)\<^sup>\<dagger> * fourier N) $$ (j, l) = (\<Sum>k<N. cnj (fourier N $$ (k, j)) * fourier N $$ (k, l))"
      using j l by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>k<N. cis (2 * pi * real k * (real l - real j) / real N) / of_nat N)"
      by (rule sum.cong) (simp_all add: fourier_entry_pair j l)
    also have "\<dots> = (if l = j then 1 else 0)"
      using root_of_unity_sum[OF N j l] N by (simp flip: sum_divide_distrib)
    finally show "((fourier N)\<^sup>\<dagger> * fourier N) $$ (j, l) = 1\<^sub>m N $$ (j, l)" using j l by auto
  qed (simp_all add: dagger_def)
  have FF': "fourier N * ((fourier N)\<^sup>\<dagger>) = 1\<^sub>m N"
  proof (rule eq_matI)
    fix j l assume "j < dim_row (1\<^sub>m N :: complex Matrix.mat)" "l < dim_col (1\<^sub>m N :: complex Matrix.mat)"
    hence j: "j < N" and l: "l < N" by simp_all
    have sym: "fourier N $$ (a, b) = fourier N $$ (b, a)" if "a < N" "b < N" for a b
      using that by (simp add: fourier_index mult_ac)
    have "(fourier N * ((fourier N)\<^sup>\<dagger>)) $$ (j, l) = (\<Sum>k<N. fourier N $$ (j, k) * cnj (fourier N $$ (l, k)))"
      using j l by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>k<N. cnj (fourier N $$ (k, l)) * fourier N $$ (k, j))"
      by (rule sum.cong) (simp_all add: sym j l mult.commute)
    also have "\<dots> = (\<Sum>k<N. cis (2 * pi * real k * (real j - real l) / real N) / of_nat N)"
      by (rule sum.cong) (simp_all add: fourier_entry_pair j l)
    also have "\<dots> = (if j = l then 1 else 0)"
      using root_of_unity_sum[OF N l j] N by (simp flip: sum_divide_distrib)
    finally show "(fourier N * ((fourier N)\<^sup>\<dagger>)) $$ (j, l) = 1\<^sub>m N $$ (j, l)" using j l by auto
  qed (simp_all add: dagger_def)
  show ?thesis unfolding unitary_def using FF FF' by simp
qed

subsection \<open>Controlled powers and phase kickback\<close>

text \<open>$\sum_k\ket k\bra k\otimes B_k$ on $\C^N\otimes\C^m$ (index $km+i$), and the controlled
power $\mathrm{C}U=\sum_k\ket k\bra k\otimes U^k$.\<close>

definition ctrl_blocks :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "ctrl_blocks N m B = Matrix.mat (N * m) (N * m)
     (\<lambda>(r, c). if r div m = c div m then B (r div m) $$ (r mod m, c mod m) else 0)"

lemma ctrl_blocks_carrier [simp]: "ctrl_blocks N m B \<in> carrier_mat (N * m) (N * m)"
  by (simp add: ctrl_blocks_def)

lemma dim_ctrl_blocks [simp]: "dim_row (ctrl_blocks N m B) = N * m" "dim_col (ctrl_blocks N m B) = N * m"
  by (simp_all add: ctrl_blocks_def)

lemma ctrl_blocks_index:
  "r < N * m \<Longrightarrow> c < N * m \<Longrightarrow>
   ctrl_blocks N m B $$ (r, c) = (if r div m = c div m then B (r div m) $$ (r mod m, c mod m) else 0)"
  by (simp add: ctrl_blocks_def)

abbreviation ctrl_pow :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "ctrl_pow N m U \<equiv> ctrl_blocks N m (\<lambda>k. U ^\<^sub>m k)"

lemma sum_blocks:
  fixes N m :: nat
  shows "(\<Sum>c<N * m. f c) = (\<Sum>k<N. \<Sum>i<m. f (k * m + i))"
proof -
  have "(\<Sum>c\<in>{k * m..<k * m + m}. f c) = (\<Sum>i<m. f (k * m + i))" for k
    using sum.shift_bounds_nat_ivl[of f 0 "k * m" m] by (simp add: atLeast0LessThan add.commute)
  thus ?thesis unfolding sum.nat_group[symmetric] by simp
qed

text \<open>Phase kickback: if $Uu=zu$ then $\mathrm{C}U(a\otimes u)=(\sum_k z^ka_k\ket k)\otimes u$.\<close>

theorem ctrl_pow_kickback:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat m m" and u: "dim_vec u = m" and ev: "U *\<^sub>v u = z \<cdot>\<^sub>v u"
      and a: "dim_vec a = N"
  shows "ctrl_pow N m U *\<^sub>v tensor_vec a u = tensor_vec (Matrix.vec N (\<lambda>k. z ^ k * a $ k)) u"
proof -
  have dt: "dim_vec (tensor_vec a u) = N * m" by (rule tensor_vec_dim[OF a u])
  have dt2: "dim_vec (tensor_vec (Matrix.vec N (\<lambda>k. z ^ k * a $ k)) u) = N * m"
    by (rule tensor_vec_dim) (simp_all add: u)
  show ?thesis
  proof (rule eq_vecI)
    fix r assume "r < dim_vec (tensor_vec (Matrix.vec N (\<lambda>k. z ^ k * a $ k)) u)"
    hence r: "r < N * m" using dt2 by simp
    hence m: "0 < m" by (cases m) auto
    define k i where "k = r div m" and "i = r mod m"
    have k: "k < N" unfolding k_def using r by (simp add: less_mult_imp_div_less)
    have i: "i < m" unfolding i_def using m by simp
    have Uk: "U ^\<^sub>m k \<in> carrier_mat m m" using U by simp
    have "(ctrl_pow N m U *\<^sub>v tensor_vec a u) $ r = (\<Sum>c<N * m. ctrl_pow N m U $$ (r, c) * tensor_vec a u $ c)"
      using r dt by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>k'<N. \<Sum>i'<m. ctrl_pow N m U $$ (r, k' * m + i') * tensor_vec a u $ (k' * m + i'))"
      by (rule sum_blocks)
    also have "\<dots> = (\<Sum>k'<N. if k' = k then (\<Sum>i'<m. (U ^\<^sub>m k) $$ (i, i') * (a $ k * u $ i')) else 0)"
    proof (rule sum.cong[OF refl])
      fix k' assume "k' \<in> {..<N}"
      hence k': "k' < N" by simp
      show "(\<Sum>i'<m. ctrl_pow N m U $$ (r, k' * m + i') * tensor_vec a u $ (k' * m + i')) =
            (if k' = k then (\<Sum>i'<m. (U ^\<^sub>m k) $$ (i, i') * (a $ k * u $ i')) else 0)"
        using mult_index_lt[OF k'] mult_index_div_mod r a u
        by (auto simp: ctrl_blocks_index tensor_vec_index k_def i_def intro!: sum.cong)
    qed
    also have "\<dots> = (\<Sum>i'<m. (U ^\<^sub>m k) $$ (i, i') * (a $ k * u $ i'))" using k by simp
    also have "\<dots> = a $ k * ((U ^\<^sub>m k) *\<^sub>v u) $ i"
      using carrier_matD[OF Uk] i u by (simp add: scalar_prod_def atLeast0LessThan sum_distrib_left mult_ac)
    also have "\<dots> = z ^ k * a $ k * u $ i" using pow_eigen[OF U u ev, of k] i u by simp
    also have "\<dots> = tensor_vec (Matrix.vec N (\<lambda>k. z ^ k * a $ k)) u $ r"
      using tensor_vec_index[of "Matrix.vec N (\<lambda>k. z ^ k * a $ k)" N u m r] r u k
      by (simp add: k_def i_def)
    finally show "(ctrl_pow N m U *\<^sub>v tensor_vec a u) $ r = tensor_vec (Matrix.vec N (\<lambda>k. z ^ k * a $ k)) u $ r" .
  qed (use dt2 in simp)
qed

subsection \<open>The phase estimation circuit\<close>

text \<open>The register starts in the uniform state $\frac1{\sqrt N}\sum_k\ket k$ ($=H^{\otimes t}\ket{0}$
for $N=2^t$).\<close>

definition uniform_state :: "nat \<Rightarrow> complex Matrix.vec" where
  "uniform_state N = Matrix.vec N (\<lambda>_. 1 / complex_of_real (sqrt (real N)))"

definition pe_amp :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex" where
  "pe_amp N \<phi> j = (\<Sum>k<N. cis (2 * pi * real k * (\<phi> - real j / real N))) / of_nat N"

text \<open>The amplitudes for any register state $\psi$: $\alpha=F_N^*(\sum_k e^{2\pi ik\varphi}\psi_k\ket k)$.\<close>

definition pe_amp_reg :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex" where
  "pe_amp_reg N psi \<phi> j = ((fourier N)\<^sup>\<dagger> *\<^sub>v Matrix.vec N (\<lambda>k. cis (2 * pi * \<phi>) ^ k * psi $ k)) $ j"

lemma pe_amp_reg_formula:
  assumes j: "j < N"
  shows "pe_amp_reg N psi \<phi> j = (\<Sum>k<N. psi $ k * cis (2 * pi * real k * (\<phi> - real j / real N))) / complex_of_real (sqrt (real N))"
proof -
  have e: "cnj (fourier N $$ (k, j)) * (cis (2 * pi * \<phi>) ^ k * psi $ k) =
           psi $ k * cis (2 * pi * real k * (\<phi> - real j / real N)) / complex_of_real (sqrt (real N))" if k: "k < N" for k
  proof -
    have "cnj (fourier N $$ (k, j)) * (cis (2 * pi * \<phi>) ^ k * psi $ k) =
          cis (- (2 * pi * real k * real j / real N)) * cis (real k * (2 * pi * \<phi>)) * psi $ k / complex_of_real (sqrt (real N))"
      using j k by (simp add: fourier_index cis_cnj DeMoivre)
    also have "cis (- (2 * pi * real k * real j / real N)) * cis (real k * (2 * pi * \<phi>)) =
               cis (2 * pi * real k * (\<phi> - real j / real N))"
      by (simp add: cis_mult algebra_simps)
    finally show ?thesis by (simp add: mult_ac)
  qed
  have "pe_amp_reg N psi \<phi> j = (\<Sum>k<N. cnj (fourier N $$ (k, j)) * (cis (2 * pi * \<phi>) ^ k * psi $ k))"
    using j by (simp add: pe_amp_reg_def scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<N. psi $ k * cis (2 * pi * real k * (\<phi> - real j / real N)) / complex_of_real (sqrt (real N)))"
    by (rule sum.cong) (simp_all add: e)
  finally show ?thesis by (simp add: sum_divide_distrib)
qed

lemma pe_amp_reg_uniform:
  assumes j: "j < N"
  shows "pe_amp_reg N (uniform_state N) \<phi> j = pe_amp N \<phi> j"
proof -
  have "pe_amp_reg N (uniform_state N) \<phi> j =
        (\<Sum>k<N. cis (2 * pi * real k * (\<phi> - real j / real N)) / (complex_of_real (sqrt (real N)) * complex_of_real (sqrt (real N))))"
    unfolding pe_amp_reg_formula[OF j] sum_divide_distrib
    by (rule sum.cong) (use j in \<open>simp_all add: uniform_state_def\<close>)
  thus ?thesis unfolding sqrt_N_sq pe_amp_def by (simp add: sum_divide_distrib)
qed

text \<open>The output of phase estimation for an eigenvector $u$, $Uu=e^{2\pi i\varphi}u$.\<close>

theorem phase_estimation_reg:
  assumes U: "U \<in> carrier_mat m m" and u: "dim_vec u = m"
      and ev: "U *\<^sub>v u = cis (2 * pi * \<phi>) \<cdot>\<^sub>v u" and psi: "dim_vec psi = N"
  shows "(((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec psi u) =
         tensor_vec (Matrix.vec N (pe_amp_reg N psi \<phi>)) u"
proof -
  let ?b = "Matrix.vec N (\<lambda>k. cis (2 * pi * \<phi>) ^ k * psi $ k)"
  have kick: "ctrl_pow N m U *\<^sub>v tensor_vec psi u = tensor_vec ?b u"
    by (rule ctrl_pow_kickback[OF U u ev psi])
  have uc: "u \<in> carrier_vec m" using u by (rule carrier_vecI)
  have "(((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec ?b u = tensor_vec ((fourier N)\<^sup>\<dagger> *\<^sub>v ?b) (1\<^sub>m m *\<^sub>v u)"
    by (rule tensor_mat_vec_mult[OF dagger_carrier[OF fourier_carrier] one_carrier_mat]) (simp_all add: u)
  also have "(fourier N)\<^sup>\<dagger> *\<^sub>v ?b = Matrix.vec N (pe_amp_reg N psi \<phi>)"
    by (rule eq_vecI) (simp_all add: pe_amp_reg_def)
  also have "1\<^sub>m m *\<^sub>v u = u" using uc by simp
  finally show ?thesis unfolding kick .
qed

theorem phase_estimation:
  assumes U: "U \<in> carrier_mat m m" and u: "dim_vec u = m"
      and ev: "U *\<^sub>v u = cis (2 * pi * \<phi>) \<cdot>\<^sub>v u"
  shows "(((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec (uniform_state N) u) =
         tensor_vec (Matrix.vec N (pe_amp N \<phi>)) u"
proof -
  have "Matrix.vec N (pe_amp_reg N (uniform_state N) \<phi>) = Matrix.vec N (pe_amp N \<phi>)"
    by (rule eq_vecI) (simp_all add: pe_amp_reg_uniform)
  thus ?thesis using phase_estimation_reg[OF U u ev, of "uniform_state N"] by (simp add: uniform_state_def)
qed

text \<open>If $\varphi=j_0/N$ exactly, the register ends in $\ket{j_0}$.\<close>

theorem phase_estimation_exact:
  assumes N: "0 < N" and j0: "j0 < N"
  shows "Matrix.vec N (pe_amp N (real j0 / real N)) = unit_vec N j0"
proof (rule eq_vecI)
  fix j assume "j < dim_vec (unit_vec N j0)"
  hence j: "j < N" by simp
  have "pe_amp N (real j0 / real N) j = (\<Sum>k<N. cis (2 * pi * real k * (real j0 - real j) / real N)) / of_nat N"
    unfolding pe_amp_def by (rule arg_cong[where f = "\<lambda>x. x / _"], rule sum.cong) (simp_all add: diff_divide_distrib algebra_simps)
  also have "\<dots> = (if j0 = j then 1 else 0)" using root_of_unity_sum[OF N j j0] N by simp
  finally show "Matrix.vec N (pe_amp N (real j0 / real N)) $ j = unit_vec N j0 $ j"
    using j by (simp add: unit_vec_def)
qed simp

subsection \<open>Measuring the register\<close>

text \<open>Probability of outcome $j$ when the register of $\psi\in\C^N\otimes\C^m$ is measured.\<close>

definition reg_prob :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> nat \<Rightarrow> real" where
  "reg_prob m \<psi> j = (\<Sum>i<m. (cmod (\<psi> $ (j * m + i)))\<^sup>2)"

lemma reg_prob_tensor:
  assumes b: "dim_vec b = N" and u: "dim_vec u = m" and j: "j < N"
      and unit: "(\<Sum>i<m. (cmod (u $ i))\<^sup>2) = 1"
  shows "reg_prob m (tensor_vec b u) j = (cmod (b $ j))\<^sup>2"
proof -
  have "reg_prob m (tensor_vec b u) j = (\<Sum>i<m. (cmod (b $ j))\<^sup>2 * (cmod (u $ i))\<^sup>2)"
    unfolding reg_prob_def
    by (rule sum.cong) (use mult_index_lt[OF j] mult_index_div_mod b u in \<open>auto simp: tensor_vec_index norm_mult power_mult_distrib\<close>)
  also have "\<dots> = (cmod (b $ j))\<^sup>2" using unit by (simp flip: sum_distrib_left)
  finally show ?thesis .
qed

subsection \<open>The success probability\<close>

text \<open>Jordan's inequality $\sin x\ge 2x/\pi$ on $[0,\pi/2]$, by concavity (as in
\<open>Gauss_Sums.Polya_Vinogradov\<close>).\<close>

lemma jordan_inequality:
  assumes "0 \<le> x" "x \<le> pi / 2"
  shows "2 / pi * x \<le> sin x"
proof -
  have "convex_on {0..pi/2} (\<lambda>x. - sin x)"
    by (rule convex_on_realI[where f' = "\<lambda>x. - cos x"])
       (auto intro!: derivative_eq_intros simp: cos_monotone_0_pi_le)
  from convex_onD_Icc'[OF this, of x] assms show ?thesis by simp
qed

lemma jordan_inequality_abs:
  assumes "\<bar>x\<bar> \<le> pi / 2"
  shows "2 / pi * \<bar>x\<bar> \<le> \<bar>sin x\<bar>"
proof (cases "0 \<le> x")
  case True
  thus ?thesis using jordan_inequality[of x] assms sin_ge_zero[of x] by simp
next
  case False
  thus ?thesis using jordan_inequality[of "- x"] assms sin_ge_zero[of "- x"] by simp
qed

lemma cmod_cis_minus_one: "cmod (cis x - 1) = 2 * \<bar>sin (x / 2)\<bar>"
proof -
  have "(cmod (cis x - 1))\<^sup>2 = (cos x - 1)\<^sup>2 + (sin x)\<^sup>2" by (simp add: cmod_power2)
  also have "\<dots> = 2 - 2 * cos x" by (simp add: power2_diff sin_squared_eq algebra_simps)
  also have "cos x = 1 - 2 * (sin (x / 2))\<^sup>2" using cos_double_sin[of "x / 2"] by simp
  finally have "(cmod (cis x - 1))\<^sup>2 = (2 * \<bar>sin (x / 2)\<bar>)\<^sup>2" by (simp add: power_mult_distrib)
  thus ?thesis by (rule power2_eq_imp_eq) simp_all
qed

text \<open>The key estimate: $\bigl|\frac1N\sum_k e^{2\pi ik\delta}\bigr|\ge 2/\pi$ for $|\delta|\le\frac1{2N}$.\<close>

theorem geometric_amp_bound:
  assumes N: "0 < N" and d: "\<bar>\<delta>\<bar> \<le> 1 / (2 * real N)"
  shows "2 / pi \<le> cmod ((\<Sum>k<N. cis (2 * pi * real k * \<delta>)) / of_nat N)"
proof (cases "\<delta> = 0")
  case True
  thus ?thesis using N pi_ge_two by (simp add: field_simps)
next
  case False
  define z where "z = cis (2 * pi * \<delta>)"
  have zk: "cis (2 * pi * real k * \<delta>) = z ^ k" for k unfolding z_def DeMoivre by (simp add: mult_ac)
  have "\<bar>\<delta>\<bar> * 2 * 1 \<le> \<bar>\<delta>\<bar> * 2 * real N" by (rule mult_left_mono) (use N in simp_all)
  hence dle: "\<bar>\<delta>\<bar> \<le> 1 / 2" using d N by (simp add: field_simps)
  have sne: "sin (pi * \<delta>) \<noteq> 0"
  proof
    assume "sin (pi * \<delta>) = 0"
    then obtain i :: int where "pi * \<delta> = of_int i * pi" by (auto simp: sin_zero_iff_int2)
    hence di: "\<delta> = of_int i" by simp
    hence "\<bar>of_int i\<bar> \<le> (1 / 2 :: real)" using dle by simp
    hence "i = 0" by linarith
    thus False using di False by simp
  qed
  have z1: "z \<noteq> 1"
  proof
    assume "z = 1"
    hence "cmod (z - 1) = 0" by simp
    thus False using sne unfolding z_def cmod_cis_minus_one by simp
  qed
  have S: "(\<Sum>k<N. cis (2 * pi * real k * \<delta>)) = (z ^ N - 1) / (z - 1)"
    unfolding zk using geometric_sum[OF z1] by simp
  have n1: "cmod (z ^ N - 1) = 2 * \<bar>sin (real N * (pi * \<delta>))\<bar>"
    unfolding z_def DeMoivre cmod_cis_minus_one by (simp add: mult_ac)
  have n2: "cmod (z - 1) = 2 * \<bar>sin (pi * \<delta>)\<bar>"
    unfolding z_def cmod_cis_minus_one by (simp add: mult_ac)
  have "cmod ((\<Sum>k<N. cis (2 * pi * real k * \<delta>)) / of_nat N) = cmod (z ^ N - 1) / (cmod (z - 1) * real N)"
    unfolding S by (simp add: norm_divide norm_mult)
  hence A: "cmod ((\<Sum>k<N. cis (2 * pi * real k * \<delta>)) / of_nat N) =
         \<bar>sin (real N * (pi * \<delta>))\<bar> / (\<bar>sin (pi * \<delta>)\<bar> * real N)"
    unfolding n1 n2 by simp
  have big: "2 * real N * \<bar>\<delta>\<bar> \<le> \<bar>sin (real N * (pi * \<delta>))\<bar>"
  proof -
    have "\<bar>real N * (pi * \<delta>)\<bar> \<le> pi / 2"
      using d N by (simp add: abs_mult field_simps)
    from jordan_inequality_abs[OF this] show ?thesis by (simp add: abs_mult)
  qed
  have small: "\<bar>sin (pi * \<delta>)\<bar> \<le> pi * \<bar>\<delta>\<bar>"
    using abs_sin_x_le_abs_x[of "pi * \<delta>"] by (simp add: abs_mult)
  have pos: "0 < \<bar>sin (pi * \<delta>)\<bar>" using sne by simp
  have "2 / pi = 2 * \<bar>\<delta>\<bar> / (pi * \<bar>\<delta>\<bar>)" using False by simp
  also have "\<dots> \<le> 2 * \<bar>\<delta>\<bar> / \<bar>sin (pi * \<delta>)\<bar>"
    by (rule divide_left_mono[OF small]) (use pos False in simp_all)
  also have "\<dots> = 2 * real N * \<bar>\<delta>\<bar> / (\<bar>sin (pi * \<delta>)\<bar> * real N)" using N by simp
  also have "\<dots> \<le> \<bar>sin (real N * (pi * \<delta>))\<bar> / (\<bar>sin (pi * \<delta>)\<bar> * real N)"
    by (rule divide_right_mono[OF big]) (use pos in simp)
  finally show ?thesis unfolding A .
qed

text \<open>With $\varphi$ within $\frac1{2N}$ of $j/N$, outcome $j$ has probability at least $4/\pi^2$.\<close>

theorem phase_estimation_bound:
  assumes N: "0 < N" and close: "\<bar>\<phi> - real j / real N\<bar> \<le> 1 / (2 * real N)"
  shows "4 / pi\<^sup>2 \<le> (cmod (pe_amp N \<phi> j))\<^sup>2"
proof -
  have "2 / pi \<le> cmod (pe_amp N \<phi> j)"
    unfolding pe_amp_def by (rule geometric_amp_bound[OF N close])
  hence "(2 / pi)\<^sup>2 \<le> (cmod (pe_amp N \<phi> j))\<^sup>2" by (rule power_mono) simp
  thus ?thesis by (simp add: power_divide)
qed

text \<open>The phase is periodic: $\alpha_0$ is unchanged by $\varphi\mapsto\varphi-1$.\<close>

lemma pe_amp_shift: "pe_amp N \<phi> 0 = pe_amp N (\<phi> - 1) 0"
proof -
  have "cis (2 * pi * real k * (\<phi> - 1)) = cis (2 * pi * real k * \<phi>)" for k
  proof -
    have "cis (2 * pi * real k * (\<phi> - 1)) = cis (2 * pi * real k * \<phi>) / cis (2 * pi * real k)"
      by (simp add: cis_divide algebra_simps)
    also have "cis (2 * pi * real k) = 1" by (rule cis_multiple_2pi) simp
    finally show ?thesis by simp
  qed
  thus ?thesis unfolding pe_amp_def by simp
qed

lemma scaled_close:
  assumes N: "0 < N" and x: "\<bar>real N * x\<bar> \<le> 1 / 2"
  shows "\<bar>x\<bar> \<le> 1 / (2 * real N)"
proof -
  have "real N * \<bar>x\<bar> \<le> 1 / 2" using x by (simp add: abs_mult)
  hence "\<bar>x\<bar> \<le> (1 / 2) / real N" using N by (simp add: le_divide_eq mult.commute)
  thus ?thesis by simp
qed

text \<open>Phase estimation succeeds: for $0\le\varphi<1$ and a unit eigenvector, some outcome
$j<N$ (the nearest to $N\varphi$, read mod $N$) is observed with probability at least $4/\pi^2$.\<close>

theorem phase_estimation_success:
  fixes U :: "complex Matrix.mat"
  assumes N: "0 < N" and U: "U \<in> carrier_mat m m" and u: "dim_vec u = m"
      and unit: "(\<Sum>i<m. (cmod (u $ i))\<^sup>2) = 1"
      and ev: "U *\<^sub>v u = cis (2 * pi * \<phi>) \<cdot>\<^sub>v u" and \<phi>: "0 \<le> \<phi>" "\<phi> < 1"
  shows "\<exists>j<N. 4 / pi\<^sup>2 \<le>
           reg_prob m ((((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec (uniform_state N) u)) j"
proof -
  have prob: "reg_prob m ((((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec (uniform_state N) u)) j =
              (cmod (pe_amp N \<phi> j))\<^sup>2" if j: "j < N" for j
    unfolding phase_estimation[OF U u ev]
    using reg_prob_tensor[OF _ u j unit, of "Matrix.vec N (pe_amp N \<phi>)"] j by simp
  define r where "r = round (real N * \<phi>)"
  have rd1: "real N * \<phi> - 1 / 2 \<le> of_int r" unfolding r_def by (rule of_int_round_ge)
  have rd2: "of_int r \<le> real N * \<phi> + 1 / 2" unfolding r_def by (rule of_int_round_le)
  have rd: "\<bar>of_int r - real N * \<phi>\<bar> \<le> 1 / 2" using rd1 rd2 by linarith
  have "real N * \<phi> < real N" using \<phi> N by simp
  hence rN: "r \<le> int N" using rd2 by linarith
  have "0 \<le> real N * \<phi>" using \<phi> by simp
  hence r0: "0 \<le> r" using rd1 by linarith
  show ?thesis
  proof (cases "r = int N")
    case True
    have "\<bar>(\<phi> - 1) - real 0 / real N\<bar> \<le> 1 / (2 * real N)"
    proof -
      have "\<bar>real N * \<phi> - real N\<bar> \<le> 1 / 2" using rd True by (simp add: abs_minus_commute)
      hence "\<bar>real N * (\<phi> - 1)\<bar> \<le> 1 / 2" by (simp only: right_diff_distrib mult_1_right)
      from scaled_close[OF N this] show ?thesis by simp
    qed
    from phase_estimation_bound[OF N this] have "4 / pi\<^sup>2 \<le> (cmod (pe_amp N (\<phi> - 1) 0))\<^sup>2" .
    hence "4 / pi\<^sup>2 \<le> (cmod (pe_amp N \<phi> 0))\<^sup>2" by (simp only: pe_amp_shift[of N \<phi>])
    hence "4 / pi\<^sup>2 \<le> reg_prob m ((((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec (uniform_state N) u)) 0"
      by (simp only: prob[OF N])
    thus ?thesis using N by blast
  next
    case False
    define j where "j = nat r"
    have j: "j < N" using False rN r0 unfolding j_def by linarith
    have rj: "of_int r = real j" unfolding j_def using r0 by simp
    have "\<bar>\<phi> - real j / real N\<bar> \<le> 1 / (2 * real N)"
    proof -
      have "\<bar>real N * \<phi> - real j\<bar> \<le> 1 / 2" using rd rj by (simp add: abs_minus_commute)
      moreover have "real N * (\<phi> - real j / real N) = real N * \<phi> - real j" using N by (simp add: right_diff_distrib)
      ultimately have "\<bar>real N * (\<phi> - real j / real N)\<bar> \<le> 1 / 2" by simp
      from scaled_close[OF N this] show ?thesis .
    qed
    from phase_estimation_bound[OF N this]
    have "4 / pi\<^sup>2 \<le> reg_prob m ((((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec (uniform_state N) u)) j"
      by (simp only: prob[OF j])
    thus ?thesis using j by blast
  qed
qed

subsection \<open>The signed distance to the nearest integer\<close>

definition wrap :: "real \<Rightarrow> real" where
  "wrap x = x - of_int (round x)"

lemma wrap_range: "- (1 / 2) \<le> wrap x" "wrap x \<le> 1 / 2"
  using of_int_round_ge[of x] of_int_round_le[of x] unfolding wrap_def by linarith+

lemma wrap_int: "x - wrap x \<in> \<int>"
  unfolding wrap_def by simp

end
