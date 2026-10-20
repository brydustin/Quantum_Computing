theory HHL_Approximate
  imports HHL
begin

section \<open>HHL with inexact phase estimation\<close>

text \<open>When the eigenvalue $\lambda$ of $u$ is not one of the register values $\lambda_k$, phase
estimation leaves the register in $\sum_j\alpha_j\ket j$ with $\alpha_j=$\<^const>\<open>pe_amp\<close>, the
rotation acts with $C/\lambda_j$ on the $j$-th branch, and uncomputation no longer returns the
register to the uniform state.  The output is compared with the ideal output
$u\otimes R(C/\lambda)\ket0$ of the exact case; the squared distance is
$\sum_j|\alpha_j|^2\,\norm{R(C/\lambda_j)\ket0-R(C/\lambda)\ket0}^2$.\<close>

subsection \<open>Register sums\<close>

text \<open>$\sum_{j<N}\ket j\otimes f_j$ on $\C^N\otimes\C^m$.\<close>

definition reg_sum :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.vec) \<Rightarrow> complex Matrix.vec" where
  "reg_sum N m f = Matrix.vec (N * m) (\<lambda>r. f (r div m) $ (r mod m))"

lemma dim_reg_sum [simp]: "dim_vec (reg_sum N m f) = N * m"
  by (simp add: reg_sum_def)

lemma reg_sum_index:
  "k < N \<Longrightarrow> i < m \<Longrightarrow> reg_sum N m f $ (k * m + i) = f k $ i"
  using block_index[of k N i m] by (simp add: reg_sum_def)

lemma reg_sum_cong: "(\<And>k. k < N \<Longrightarrow> f k = g k) \<Longrightarrow> reg_sum N m f = reg_sum N m g"
  by (rule eq_vecI) (auto simp: reg_sum_def less_mult_imp_div_less)

lemma tensor_reg_sum:
  assumes a: "dim_vec a = N" and w: "dim_vec w = m"
  shows "tensor_vec a w = reg_sum N m (\<lambda>k. a $ k \<cdot>\<^sub>v w)"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (reg_sum N m (\<lambda>k. a $ k \<cdot>\<^sub>v w))"
  hence r: "r < N * m" by simp
  hence m: "0 < m" by (cases m) auto
  show "tensor_vec a w $ r = reg_sum N m (\<lambda>k. a $ k \<cdot>\<^sub>v w) $ r"
    using tensor_vec_index[OF a w r] r m w by (simp add: reg_sum_def)
qed (simp add: tensor_vec_dim[OF a w])

lemma reg_sum_index_div:
  fixes r N m :: nat
  assumes "r < N * m"
  shows "r div m < N" "r mod m < m"
proof -
  show "r div m < N" using assms by (simp add: less_mult_imp_div_less)
  have "0 < m" using assms by (cases m) auto
  thus "r mod m < m" by simp
qed

lemma reg_sum_add:
  assumes f: "\<And>k. k < N \<Longrightarrow> dim_vec (f k) = m" and g: "\<And>k. k < N \<Longrightarrow> dim_vec (g k) = m"
  shows "reg_sum N m f + reg_sum N m g = reg_sum N m (\<lambda>k. f k + g k)"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (reg_sum N m (\<lambda>k. f k + g k))"
  hence r: "r < N * m" by simp
  note ki = reg_sum_index_div[OF r]
  show "(reg_sum N m f + reg_sum N m g) $ r = reg_sum N m (\<lambda>k. f k + g k) $ r"
    using r ki g[OF ki(1)] by (simp add: reg_sum_def)
qed simp

lemma reg_sum_diff:
  assumes g: "\<And>k. k < N \<Longrightarrow> dim_vec (g k) = m"
  shows "reg_sum N m f - reg_sum N m g = reg_sum N m (\<lambda>k. f k - g k)"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (reg_sum N m (\<lambda>k. f k - g k))"
  hence r: "r < N * m" by simp
  note ki = reg_sum_index_div[OF r]
  show "(reg_sum N m f - reg_sum N m g) $ r = reg_sum N m (\<lambda>k. f k - g k) $ r"
    using r ki g[OF ki(1)] by (simp add: reg_sum_def)
qed simp

lemma reg_sum_smult:
  assumes f: "\<And>k. k < N \<Longrightarrow> dim_vec (f k) = m"
  shows "c \<cdot>\<^sub>v reg_sum N m f = reg_sum N m (\<lambda>k. c \<cdot>\<^sub>v f k)"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (reg_sum N m (\<lambda>k. c \<cdot>\<^sub>v f k))"
  hence r: "r < N * m" by simp
  note ki = reg_sum_index_div[OF r]
  show "(c \<cdot>\<^sub>v reg_sum N m f) $ r = reg_sum N m (\<lambda>k. c \<cdot>\<^sub>v f k) $ r"
    using r ki f[OF ki(1)] by (simp add: reg_sum_def)
qed simp

text \<open>Block-diagonal operators act branch by branch.\<close>

lemma ctrl_blocks_reg_sum:
  assumes B: "\<And>k. k < N \<Longrightarrow> B k \<in> carrier_mat m m" and f: "\<And>k. k < N \<Longrightarrow> dim_vec (f k) = m"
  shows "ctrl_blocks N m B *\<^sub>v reg_sum N m f = reg_sum N m (\<lambda>k. B k *\<^sub>v f k)"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (reg_sum N m (\<lambda>k. B k *\<^sub>v f k))"
  hence r: "r < N * m" by simp
  hence m: "0 < m" by (cases m) auto
  define k i where "k = r div m" and "i = r mod m"
  have k: "k < N" unfolding k_def using r by (simp add: less_mult_imp_div_less)
  have i: "i < m" unfolding i_def using m by simp
  have Bd: "dim_row (B k) = m" "dim_col (B k) = m" using B[OF k] by auto
  have "(ctrl_blocks N m B *\<^sub>v reg_sum N m f) $ r = (\<Sum>c<N * m. ctrl_blocks N m B $$ (r, c) * reg_sum N m f $ c)"
    using r by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k'<N. \<Sum>i'<m. ctrl_blocks N m B $$ (r, k' * m + i') * reg_sum N m f $ (k' * m + i'))"
    by (rule sum_blocks)
  also have "\<dots> = (\<Sum>k'<N. if k' = k then (\<Sum>i'<m. B k $$ (i, i') * f k $ i') else 0)"
  proof (rule sum.cong[OF refl])
    fix k' assume "k' \<in> {..<N}"
    hence k': "k' < N" by simp
    have "(\<Sum>i'<m. ctrl_blocks N m B $$ (r, k' * m + i') * reg_sum N m f $ (k' * m + i')) =
          (\<Sum>i'<m. if k' = k then B k $$ (i, i') * f k $ i' else 0)"
      by (rule sum.cong[OF refl]) (auto simp: ctrl_blocks_col_index[OF r k'] reg_sum_index[OF k'] k_def i_def)
    also have "\<dots> = (if k' = k then (\<Sum>i'<m. B k $$ (i, i') * f k $ i') else 0)" by (rule sum_if_const)
    finally show "(\<Sum>i'<m. ctrl_blocks N m B $$ (r, k' * m + i') * reg_sum N m f $ (k' * m + i')) =
          (if k' = k then (\<Sum>i'<m. B k $$ (i, i') * f k $ i') else 0)" .
  qed
  also have "\<dots> = (\<Sum>i'<m. B k $$ (i, i') * f k $ i')" using k by simp
  also have "\<dots> = (B k *\<^sub>v f k) $ i" using i Bd f[OF k] by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = reg_sum N m (\<lambda>k. B k *\<^sub>v f k) $ r" using r m by (simp add: reg_sum_def k_def i_def)
  finally show "(ctrl_blocks N m B *\<^sub>v reg_sum N m f) $ r = reg_sum N m (\<lambda>k. B k *\<^sub>v f k) $ r" .
qed simp

text \<open>Branches are orthogonal: $\langle\sum_j\ket j\otimes f_j,\sum_j\ket j\otimes g_j\rangle=\sum_j\langle f_j,g_j\rangle$.\<close>

lemma reg_sum_inner:
  assumes f: "\<And>k. k < N \<Longrightarrow> dim_vec (f k) = m" and g: "\<And>k. k < N \<Longrightarrow> dim_vec (g k) = m"
  shows "\<langle>reg_sum N m f|reg_sum N m g\<rangle> = (\<Sum>k<N. \<langle>f k|g k\<rangle>)"
proof -
  have "\<langle>reg_sum N m f|reg_sum N m g\<rangle> = (\<Sum>r<N * m. cnj (reg_sum N m f $ r) * reg_sum N m g $ r)"
    by (simp add: inner_prod_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<N. \<Sum>i<m. cnj (reg_sum N m f $ (k * m + i)) * reg_sum N m g $ (k * m + i))"
    by (rule sum_blocks)
  also have "\<dots> = (\<Sum>k<N. \<langle>f k|g k\<rangle>)"
    by (rule sum.cong[OF refl]) (simp add: reg_sum_index inner_prod_def scalar_prod_def atLeast0LessThan f g)
  finally show ?thesis .
qed

subsection \<open>Phase estimation on a branch\<close>

text \<open>$W(u_N\otimes u\otimes w)=\alpha\otimes u\otimes w$ for every ancilla vector $w$, where
$\alpha_j=\alpha_j(\varphi)$, $e^{it_0\lambda}=e^{2\pi i\varphi}$.\<close>

lemma unitary_inner_self:
  assumes W: "W \<in> carrier_mat K K" "unitary W" and y: "dim_vec y = K"
  shows "\<langle>W\<^sup>\<dagger> *\<^sub>v y|W\<^sup>\<dagger> *\<^sub>v y\<rangle> = \<langle>y|y\<rangle>"
proof -
  have yc: "y \<in> carrier_vec K" by (rule carrier_vecI[OF y])
  have Wd: "W\<^sup>\<dagger> \<in> carrier_mat K K" by (rule dagger_carrier[OF W(1)])
  have d: "dim_vec (W\<^sup>\<dagger> *\<^sub>v y) = K" using carrier_matD(2)[OF W(1)] by simp
  have "\<langle>W\<^sup>\<dagger> *\<^sub>v y|W\<^sup>\<dagger> *\<^sub>v y\<rangle> = \<langle>(W\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v (W\<^sup>\<dagger> *\<^sub>v y)|y\<rangle>"
    by (rule inner_prod_adjoint_swap[OF Wd d y])
  also have "(W\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v (W\<^sup>\<dagger> *\<^sub>v y) = (W * (W\<^sup>\<dagger>)) *\<^sub>v y"
    unfolding dagger_of_dagger_is_id by (rule assoc_mult_mat_vec[OF W(1) Wd yc, symmetric])
  also have "W * (W\<^sup>\<dagger>) = 1\<^sub>m K" using W unfolding unitary_def by auto
  finally show ?thesis using yc by simp
qed

lemma rot_e0_vec:
  "rot c *\<^sub>v unit_vec 2 0 = Matrix.vec 2 (\<lambda>i. if i = 0 then complex_of_real (sqrt (1 - c\<^sup>2)) else complex_of_real c)"
  by (rule eq_vecI) (auto simp: rot_def scalar_prod_def unit_vec_def less_2_cases numeral_2_eq_2)

lemma rot_diff_inner:
  "\<langle>rot c1 *\<^sub>v unit_vec 2 0 - rot c2 *\<^sub>v unit_vec 2 0|rot c1 *\<^sub>v unit_vec 2 0 - rot c2 *\<^sub>v unit_vec 2 0\<rangle> =
   complex_of_real ((sqrt (1 - c1\<^sup>2) - sqrt (1 - c2\<^sup>2))\<^sup>2 + (c1 - c2)\<^sup>2)"
  unfolding rot_e0_vec
  by (simp add: inner_prod_def scalar_prod_def numeral_2_eq_2 power2_eq_square flip: of_real_diff of_real_mult of_real_add)

lemma cnj_mult_self: "cnj z * z = complex_of_real ((cmod z)\<^sup>2)"
  by (metis complex_norm_square mult.commute)

lemma inner_self_sum: "dim_vec v = N \<Longrightarrow> \<langle>v|v\<rangle> = (\<Sum>i<N. complex_of_real ((cmod (v $ i))\<^sup>2))"
  by (simp add: inner_prod_def scalar_prod_def atLeast0LessThan cnj_mult_self)

text \<open>The register amplitudes have total weight one: $\alpha=F_N^*b$ with $b$ a unit vector.\<close>

lemma pe_amp_sum_sq:
  assumes N: "0 < N"
  shows "(\<Sum>j<N. (cmod (pe_amp N \<phi> j))\<^sup>2) = 1"
proof -
  let ?b = "Matrix.vec N (\<lambda>k. cis (2 * pi * \<phi>) ^ k * uniform_state N $ k)"
  let ?a = "Matrix.vec N (pe_amp N \<phi>)"
  have a: "(fourier N)\<^sup>\<dagger> *\<^sub>v ?b = ?a"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec ?a"
    hence i: "i < N" by simp
    show "((fourier N)\<^sup>\<dagger> *\<^sub>v ?b) $ i = ?a $ i" unfolding fourier_dagger_kick[OF i] using i by simp
  qed simp
  have "complex_of_real (\<Sum>j<N. (cmod (pe_amp N \<phi> j))\<^sup>2) = (\<Sum>j<N. complex_of_real ((cmod (?a $ j))\<^sup>2))"
    by (simp add: of_real_sum)
  also have "\<dots> = \<langle>?a|?a\<rangle>" by (rule inner_self_sum[symmetric]) simp
  also have "\<dots> = \<langle>?b|?b\<rangle>"
    unfolding a[symmetric] by (rule unitary_inner_self[OF fourier_carrier fourier_unitary[OF N]]) simp
  also have "\<dots> = (\<Sum>k<N. complex_of_real ((cmod (?b $ k))\<^sup>2))" by (rule inner_self_sum) simp
  also have "\<dots> = (\<Sum>k<N. complex_of_real (1 / real N))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<N}"
    hence k: "k < N" by simp
    have "(cmod (?b $ k))\<^sup>2 = (1 / sqrt (real N))\<^sup>2"
      using k by (simp add: uniform_state_def norm_mult norm_power norm_divide)
    also have "\<dots> = 1 / real N" by (simp add: power_divide)
    finally show "complex_of_real ((cmod (?b $ k))\<^sup>2) = complex_of_real (1 / real N)" by simp
  qed
  also have "\<dots> = 1" using N by simp
  finally show ?thesis using of_real_eq_1_iff by blast
qed

text \<open>Tail bound: $|\alpha_j|\le 1/(2N|\delta|)$ for $\delta=\varphi-j/N$, $0<|\delta|\le\frac12$.\<close>

lemma geometric_amp_tail:
  assumes N: "0 < N" and d: "\<bar>\<delta>\<bar> \<le> 1 / 2" and d0: "\<delta> \<noteq> 0"
  shows "cmod ((\<Sum>k<N. cis (2 * pi * real k * \<delta>)) / of_nat N) \<le> 1 / (2 * real N * \<bar>\<delta>\<bar>)"
proof -
  define z where "z = cis (2 * pi * \<delta>)"
  have zk: "cis (2 * pi * real k * \<delta>) = z ^ k" for k unfolding z_def DeMoivre by (simp add: mult_ac)
  have sne: "sin (pi * \<delta>) \<noteq> 0"
  proof
    assume "sin (pi * \<delta>) = 0"
    then obtain i :: int where "pi * \<delta> = of_int i * pi" by (auto simp: sin_zero_iff_int2)
    hence di: "\<delta> = of_int i" by simp
    hence "\<bar>of_int i\<bar> \<le> (1 / 2 :: real)" using d by simp
    hence "i = 0" by linarith
    thus False using di d0 by simp
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
  have A: "cmod ((\<Sum>k<N. cis (2 * pi * real k * \<delta>)) / of_nat N) = \<bar>sin (real N * (pi * \<delta>))\<bar> / (\<bar>sin (pi * \<delta>)\<bar> * real N)"
    unfolding S by (simp add: norm_divide norm_mult n1 n2)
  have jor: "2 * \<bar>\<delta>\<bar> \<le> \<bar>sin (pi * \<delta>)\<bar>"
  proof -
    have "\<bar>pi * \<delta>\<bar> \<le> pi / 2" using d by (simp add: abs_mult)
    from jordan_inequality_abs[OF this] show ?thesis by (simp add: abs_mult)
  qed
  have pos: "0 < 2 * \<bar>\<delta>\<bar>" using d0 by simp
  have "\<bar>sin (real N * (pi * \<delta>))\<bar> / (\<bar>sin (pi * \<delta>)\<bar> * real N) \<le> 1 / (\<bar>sin (pi * \<delta>)\<bar> * real N)"
    by (rule divide_right_mono) (use sne N in simp_all)
  also have "\<dots> \<le> 1 / (2 * \<bar>\<delta>\<bar> * real N)"
    by (rule divide_left_mono) (use jor pos N in \<open>simp_all add: mult_right_mono\<close>)
  finally show ?thesis unfolding A by (simp add: mult_ac)
qed

lemma pe_amp_tail:
  assumes N: "0 < N" and d: "\<bar>\<phi> - real j / real N\<bar> \<le> 1 / 2" and d0: "\<phi> \<noteq> real j / real N"
  shows "cmod (pe_amp N \<phi> j) \<le> 1 / (2 * real N * \<bar>\<phi> - real j / real N\<bar>)"
  unfolding pe_amp_def using geometric_amp_tail[OF N d] d0 by simp

context
  fixes A :: "complex Matrix.mat" and n N :: nat and t0 C l :: real and u :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
begin

text \<open>The phase of $u$, the register amplitudes, the ideal and the branch rotations.\<close>

definition "phi = t0 * l / (2 * pi)"
definition "alpha = Matrix.vec N (pe_amp N phi)"
definition "r_ideal = rot (C / l) *\<^sub>v unit_vec 2 0"
definition "r_br k = rot (C / reg_eig t0 N k) *\<^sub>v unit_vec 2 0"

lemma phi_phase: "cis (t0 * l) = cis (2 * pi * phi)"
  unfolding phi_def by simp

lemma dim_alpha [simp]: "dim_vec alpha = N" by (simp add: alpha_def)
lemma dim_r_ideal [simp]: "dim_vec r_ideal = 2" by (simp add: r_ideal_def)
lemma dim_r_br [simp]: "dim_vec (r_br k) = 2" by (simp add: r_br_def)

lemma W_branch:
  assumes w: "dim_vec w = 2"
  shows "hhl_W A t0 N *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u w) = tensor_vec alpha (tensor_vec u w)"
proof -
  let ?E = "evolution A t0" and ?V = "evolution A t0 \<Otimes> 1\<^sub>m 2"
  have nA: "dim_row A = n" using A(1) by simp
  have Ec: "?E \<in> carrier_mat n n" using A by (rule evolution_carrier)
  have Vc: "?V \<in> carrier_mat (n * 2) (n * 2)" using Ec by (intro carrier_matI) auto
  have uw: "dim_vec (tensor_vec u w) = n * 2" by (rule tensor_vec_dim[OF u w])
  have Vev: "?V *\<^sub>v tensor_vec u w = cis (2 * pi * phi) \<cdot>\<^sub>v tensor_vec u w"
  proof -
    have "?V *\<^sub>v tensor_vec u w = tensor_vec (?E *\<^sub>v u) (1\<^sub>m 2 *\<^sub>v w)"
      by (rule tensor_mat_vec_mult[OF Ec one_carrier_mat u w])
    also have "?E *\<^sub>v u = cis (t0 * l) \<cdot>\<^sub>v u" by (rule evolution_eigen[OF A u ev])
    also have "1\<^sub>m 2 *\<^sub>v w = w" using carrier_vecI[OF w] by simp
    finally show ?thesis unfolding phi_phase using tensor_vec_smult_left[OF u w] by simp
  qed
  have Fc: "((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m (n * 2) \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" by (rule carrier_matI) simp_all
  have xc: "tensor_vec (uniform_state N) (tensor_vec u w) \<in> carrier_vec (N * (n * 2))"
    by (rule carrier_vecI, rule tensor_vec_dim) (simp_all add: uniform_state_def uw)
  have "hhl_W A t0 N *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u w) =
        (((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m (n * 2)) *\<^sub>v (ctrl_pow N (n * 2) ?V *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u w))"
    unfolding hhl_W_def pe_unitary_def nA by (rule assoc_mult_mat_vec[OF Fc ctrl_pow_carrier xc])
  also have "\<dots> = tensor_vec alpha (tensor_vec u w)"
    unfolding alpha_def by (rule phase_estimation[OF Vc uw Vev])
  finally show ?thesis .
qed

text \<open>The output of the circuit and the ideal output as register sums.\<close>

lemma hhl_output_branches:
  "hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
   (hhl_W A t0 N)\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k))"
proof -
  let ?W = "hhl_W A t0 N" and ?CR = "ctrl_blocks N (n * 2) (hhl_rot C t0 N n)"
  have nA: "dim_row A = n" using A(1) by simp
  have Wc: "?W \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" unfolding hhl_W_def nA by simp
  have CRc: "?CR \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" by simp
  have u0: "dim_vec (tensor_vec u (unit_vec 2 0)) = n * 2" by (rule tensor_vec_dim[OF u]) simp
  have x0: "tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) \<in> carrier_vec (N * (n * 2))"
    by (rule carrier_vecI, rule tensor_vec_dim) (simp_all add: uniform_state_def u0)
  have br: "hhl_rot C t0 N n k *\<^sub>v (alpha $ k \<cdot>\<^sub>v tensor_vec u (unit_vec 2 0)) = alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k)" for k
  proof -
    have "hhl_rot C t0 N n k *\<^sub>v (alpha $ k \<cdot>\<^sub>v tensor_vec u (unit_vec 2 0)) =
          alpha $ k \<cdot>\<^sub>v (hhl_rot C t0 N n k *\<^sub>v tensor_vec u (unit_vec 2 0))"
      by (rule mult_mat_vec[OF hhl_rot_carrier carrier_vecI[OF u0]])
    also have "hhl_rot C t0 N n k *\<^sub>v tensor_vec u (unit_vec 2 0) = tensor_vec (1\<^sub>m n *\<^sub>v u) (r_br k)"
      unfolding hhl_rot_def r_br_def by (rule tensor_mat_vec_mult[OF one_carrier_mat rot_carrier u]) simp
    also have "1\<^sub>m n *\<^sub>v u = u" using carrier_vecI[OF u] by simp
    finally show ?thesis .
  qed
  have "hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
        ?W\<^sup>\<dagger> *\<^sub>v (?CR *\<^sub>v (?W *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0))))"
    unfolding hhl_circuit_def nA
    using assoc_mult_mat_vec[OF dagger_carrier[OF Wc] mult_carrier_mat[OF CRc Wc] x0] assoc_mult_mat_vec[OF CRc Wc x0]
    by simp
  also have "?W *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) = tensor_vec alpha (tensor_vec u (unit_vec 2 0))"
    by (rule W_branch) simp
  also have "\<dots> = reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (unit_vec 2 0))"
    by (rule tensor_reg_sum[OF dim_alpha u0])
  also have "?CR *\<^sub>v \<dots> = reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k))"
    by (subst ctrl_blocks_reg_sum) (simp_all add: u0 br)
  finally show ?thesis .
qed

lemma hhl_ideal_branches:
  "tensor_vec (uniform_state N) (tensor_vec u r_ideal) =
   (hhl_W A t0 N)\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal)"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have Wc: "hhl_W A t0 N \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" unfolding hhl_W_def nA by simp
  have Wu: "unitary (hhl_W A t0 N)"
  proof -
    have Ec: "evolution A t0 \<in> carrier_mat n n" using A by (rule evolution_carrier)
    have Vc: "evolution A t0 \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)" using Ec by (intro carrier_matI) auto
    have Vu: "unitary (evolution A t0 \<Otimes> 1\<^sub>m 2)" by (rule tensor_mat_unitary_one_right) (rule evolution_unitary[OF A])
    show ?thesis unfolding hhl_W_def nA by (rule pe_unitary_unitary[OF N Vc Vu])
  qed
  have ur: "dim_vec (tensor_vec u r_ideal) = n * 2" by (rule tensor_vec_dim[OF u]) simp
  have "tensor_vec alpha (tensor_vec u r_ideal) = reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal)"
    by (rule tensor_reg_sum[OF dim_alpha ur])
  moreover have "(hhl_W A t0 N)\<^sup>\<dagger> *\<^sub>v tensor_vec alpha (tensor_vec u r_ideal) = tensor_vec (uniform_state N) (tensor_vec u r_ideal)"
    by (rule unitary_undo[OF Wc Wu _ W_branch[OF dim_r_ideal]]) (rule tensor_vec_dim; simp add: uniform_state_def ur)
  ultimately show ?thesis by simp
qed

text \<open>The squared distance between output and ideal output.\<close>

theorem hhl_approx_error:
  "\<langle>hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal) |
    hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal)\<rangle> =
   \<langle>u|u\<rangle> * (\<Sum>k<N. complex_of_real ((cmod (pe_amp N phi k))\<^sup>2) * \<langle>r_br k - r_ideal|r_br k - r_ideal\<rangle>)"
proof -
  let ?W = "hhl_W A t0 N"
  let ?f = "\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k - r_ideal)"
  have nA: "dim_row A = n" using A(1) by simp
  have Wc: "?W \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" unfolding hhl_W_def nA by simp
  have Wu: "unitary ?W"
  proof -
    have Ec: "evolution A t0 \<in> carrier_mat n n" using A by (rule evolution_carrier)
    have Vc: "evolution A t0 \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)" using Ec by (intro carrier_matI) auto
    have Vu: "unitary (evolution A t0 \<Otimes> 1\<^sub>m 2)" by (rule tensor_mat_unitary_one_right) (rule evolution_unitary[OF A])
    show ?thesis unfolding hhl_W_def nA by (rule pe_unitary_unitary[OF N Vc Vu])
  qed
  have Wd: "?W\<^sup>\<dagger> \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" by (rule dagger_carrier[OF Wc])
  have dbr: "dim_vec (tensor_vec u (r_br k)) = n * 2" for k by (rule tensor_vec_dim[OF u]) simp
  have did: "dim_vec (tensor_vec u r_ideal) = n * 2" by (rule tensor_vec_dim[OF u]) simp
  have ddf: "dim_vec (tensor_vec u (r_br k - r_ideal)) = n * 2" for k by (rule tensor_vec_dim[OF u]) simp
  have diff_br: "alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k) - alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal = ?f k" for k
  proof -
    have e: "r_ideal + (r_br k - r_ideal) = r_br k" by (rule eq_vecI) simp_all
    have "tensor_vec u (r_ideal + (r_br k - r_ideal)) = tensor_vec u r_ideal + tensor_vec u (r_br k - r_ideal)"
      by (rule tensor_vec_bilinear_right[OF u]) simp_all
    hence split: "tensor_vec u (r_br k) = tensor_vec u r_ideal + tensor_vec u (r_br k - r_ideal)" unfolding e .
    show ?thesis unfolding split
      using did ddf[of k] by (intro eq_vecI) (simp_all add: algebra_simps)
  qed
  have "hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal) =
        ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k)) - ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal)"
    unfolding hhl_output_branches hhl_ideal_branches ..
  also have "\<dots> = ?W\<^sup>\<dagger> *\<^sub>v (reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k)) - reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal))"
    by (rule mult_minus_distrib_mat_vec[OF Wd, symmetric]) (simp_all add: carrier_vecI)
  also have "reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k)) - reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal) =
             reg_sum N (n * 2) ?f"
    by (subst reg_sum_diff) (simp_all add: did diff_br)
  finally have E: "hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal) =
                   ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) ?f" .
  have "\<langle>?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) ?f|?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) ?f\<rangle> = \<langle>reg_sum N (n * 2) ?f|reg_sum N (n * 2) ?f\<rangle>"
    by (rule unitary_inner_self[OF Wc Wu]) simp
  also have "\<dots> = (\<Sum>k<N. \<langle>?f k|?f k\<rangle>)" by (rule reg_sum_inner) (simp_all add: ddf)
  also have "\<dots> = (\<Sum>k<N. complex_of_real ((cmod (pe_amp N phi k))\<^sup>2) * (\<langle>u|u\<rangle> * \<langle>r_br k - r_ideal|r_br k - r_ideal\<rangle>))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<N}"
    hence k: "k < N" by simp
    have "\<langle>?f k|?f k\<rangle> = (cnj (alpha $ k) * alpha $ k) * \<langle>tensor_vec u (r_br k - r_ideal)|tensor_vec u (r_br k - r_ideal)\<rangle>"
      using inner_prod_distrib_left[of "tensor_vec u (r_br k - r_ideal)" "alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k - r_ideal)" "alpha $ k"]
            inner_prod_distrib_right[of "tensor_vec u (r_br k - r_ideal)" "tensor_vec u (r_br k - r_ideal)" "alpha $ k"]
      by (simp add: mult.assoc)
    also have "\<langle>tensor_vec u (r_br k - r_ideal)|tensor_vec u (r_br k - r_ideal)\<rangle> = \<langle>u|u\<rangle> * \<langle>r_br k - r_ideal|r_br k - r_ideal\<rangle>"
      by (rule tensor_inner_prod[OF u u]) simp_all
    also have "cnj (alpha $ k) * alpha $ k = complex_of_real ((cmod (pe_amp N phi k))\<^sup>2)"
    proof -
      have ak: "alpha $ k = pe_amp N phi k" using k by (simp add: alpha_def)
      show ?thesis unfolding ak by (metis complex_norm_square mult.commute)
    qed
    finally show "\<langle>?f k|?f k\<rangle> = complex_of_real ((cmod (pe_amp N phi k))\<^sup>2) * (\<langle>u|u\<rangle> * \<langle>r_br k - r_ideal|r_br k - r_ideal\<rangle>)"
      by (simp add: mult_ac)
  qed
  also have "\<dots> = \<langle>u|u\<rangle> * (\<Sum>k<N. complex_of_real ((cmod (pe_amp N phi k))\<^sup>2) * \<langle>r_br k - r_ideal|r_br k - r_ideal\<rangle>)"
    by (simp add: sum_distrib_left mult_ac)
  finally show ?thesis unfolding E .
qed


text \<open>The branch distance in real terms, $c_k=C/\lambda_k$, $c=C/\lambda$.\<close>

corollary hhl_approx_error_real:
  "\<langle>hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal) |
    hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal)\<rangle> =
   \<langle>u|u\<rangle> * complex_of_real (\<Sum>k<N. (cmod (pe_amp N phi k))\<^sup>2 *
      ((sqrt (1 - (C / reg_eig t0 N k)\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (C / reg_eig t0 N k - C / l)\<^sup>2))"
proof -
  have "(\<Sum>k<N. complex_of_real ((cmod (pe_amp N phi k))\<^sup>2) * \<langle>r_br k - r_ideal|r_br k - r_ideal\<rangle>) =
        complex_of_real (\<Sum>k<N. (cmod (pe_amp N phi k))\<^sup>2 *
          ((sqrt (1 - (C / reg_eig t0 N k)\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (C / reg_eig t0 N k - C / l)\<^sup>2))"
    unfolding r_br_def r_ideal_def rot_diff_inner by (simp add: of_real_sum)
  thus ?thesis unfolding hhl_approx_error by (rule arg_cong[where f = "\<lambda>x. \<langle>u|u\<rangle> * x"])
qed

end

end
