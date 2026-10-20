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

text \<open>The circuit with an arbitrary angle $f(k)$ on register value $k$; \<^const>\<open>hhl_circuit\<close> is
$f(k)=C/\lambda_k$, the physical circuit clamps the angle to $[-1,1]$.\<close>

definition hhl_gen :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat" where
  "hhl_gen A t0 N f = (hhl_W A t0 N)\<^sup>\<dagger> * (ctrl_blocks N (dim_row A * 2) (\<lambda>k. 1\<^sub>m (dim_row A) \<Otimes> rot (f k)) * hhl_W A t0 N)"

definition clamp :: "real \<Rightarrow> real" where
  "clamp x = max (-1) (min 1 x)"

definition hhl_circuit_clamped :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "hhl_circuit_clamped A t0 N C = hhl_gen A t0 N (\<lambda>k. clamp (C / reg_eig t0 N k))"

lemma hhl_circuit_gen: "hhl_circuit A t0 N C = hhl_gen A t0 N (\<lambda>k. C / reg_eig t0 N k)"
  by (simp add: hhl_circuit_def hhl_gen_def hhl_rot_def[abs_def])

lemma rot_blk_carrier [simp]: "1\<^sub>m n \<Otimes> rot x \<in> carrier_mat (n * 2) (n * 2)"
  by (rule carrier_matI) simp_all

lemma clamp_abs: "\<bar>clamp x\<bar> \<le> 1"
  by (simp add: clamp_def)

lemma clamp_id: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> clamp x = x"
  by (simp add: clamp_def)

definition hhl_phi :: "real \<Rightarrow> real \<Rightarrow> real" where
  "hhl_phi t0 l = t0 * l / (2 * pi)"

context
  fixes A :: "complex Matrix.mat" and n N :: nat and t0 l :: real and u :: "complex Matrix.vec"
    and f :: "nat \<Rightarrow> real" and c :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
begin

text \<open>The phase of $u$, the register amplitudes, the ideal and the branch rotations.\<close>

abbreviation "phi \<equiv> hhl_phi t0 l"
definition "alpha = Matrix.vec N (pe_amp N phi)"
abbreviation "r_ideal \<equiv> rot c *\<^sub>v unit_vec 2 0"
definition "r_br k = rot (f k) *\<^sub>v unit_vec 2 0"

lemma phi_phase: "cis (t0 * l) = cis (2 * pi * phi)"
  unfolding hhl_phi_def by simp

lemma dim_alpha [simp]: "dim_vec alpha = N" by (simp add: alpha_def)
lemma dim_r_ideal: "dim_vec r_ideal = 2" by simp
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
  "hhl_gen A t0 N f *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
   (hhl_W A t0 N)\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k))"
proof -
  let ?W = "hhl_W A t0 N" and ?CR = "ctrl_blocks N (n * 2) (\<lambda>k. 1\<^sub>m n \<Otimes> rot (f k))"
  have nA: "dim_row A = n" using A(1) by simp
  have Wc: "?W \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" unfolding hhl_W_def nA by simp
  have CRc: "?CR \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" by simp
  have u0: "dim_vec (tensor_vec u (unit_vec 2 0)) = n * 2" by (rule tensor_vec_dim[OF u]) simp
  have x0: "tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) \<in> carrier_vec (N * (n * 2))"
    by (rule carrier_vecI, rule tensor_vec_dim) (simp_all add: uniform_state_def u0)
  have br: "(1\<^sub>m n \<Otimes> rot (f k)) *\<^sub>v (alpha $ k \<cdot>\<^sub>v tensor_vec u (unit_vec 2 0)) = alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k)" for k
  proof -
    have "(1\<^sub>m n \<Otimes> rot (f k)) *\<^sub>v (alpha $ k \<cdot>\<^sub>v tensor_vec u (unit_vec 2 0)) =
          alpha $ k \<cdot>\<^sub>v ((1\<^sub>m n \<Otimes> rot (f k)) *\<^sub>v tensor_vec u (unit_vec 2 0))"
      by (rule mult_mat_vec[OF rot_blk_carrier carrier_vecI[OF u0]])
    also have "(1\<^sub>m n \<Otimes> rot (f k)) *\<^sub>v tensor_vec u (unit_vec 2 0) = tensor_vec (1\<^sub>m n *\<^sub>v u) (r_br k)"
      unfolding r_br_def by (rule tensor_mat_vec_mult[OF one_carrier_mat rot_carrier u]) simp
    also have "1\<^sub>m n *\<^sub>v u = u" using carrier_vecI[OF u] by simp
    finally show ?thesis .
  qed
  have "hhl_gen A t0 N f *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
        ?W\<^sup>\<dagger> *\<^sub>v (?CR *\<^sub>v (?W *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0))))"
    unfolding hhl_gen_def nA
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
  "\<langle>hhl_gen A t0 N f *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal) |
    hhl_gen A t0 N f *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal)\<rangle> =
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
  have "hhl_gen A t0 N f *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal) =
        ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k)) - ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal)"
    unfolding hhl_output_branches hhl_ideal_branches ..
  also have "\<dots> = ?W\<^sup>\<dagger> *\<^sub>v (reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k)) - reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal))"
    by (rule mult_minus_distrib_mat_vec[OF Wd, symmetric]) (simp_all add: carrier_vecI)
  also have "reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u (r_br k)) - reg_sum N (n * 2) (\<lambda>k. alpha $ k \<cdot>\<^sub>v tensor_vec u r_ideal) =
             reg_sum N (n * 2) ?f"
    by (subst reg_sum_diff) (simp_all add: did diff_br)
  finally have E: "hhl_gen A t0 N f *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal) =
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


text \<open>The branch distance in real terms.\<close>

corollary hhl_approx_error_real:
  "\<langle>hhl_gen A t0 N f *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal) |
    hhl_gen A t0 N f *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) - tensor_vec (uniform_state N) (tensor_vec u r_ideal)\<rangle> =
   \<langle>u|u\<rangle> * complex_of_real (\<Sum>k<N. (cmod (pe_amp N phi k))\<^sup>2 *
      ((sqrt (1 - (f k)\<^sup>2) - sqrt (1 - c\<^sup>2))\<^sup>2 + (f k - c)\<^sup>2))"
proof -
  have "(\<Sum>k<N. complex_of_real ((cmod (pe_amp N phi k))\<^sup>2) * \<langle>r_br k - r_ideal|r_br k - r_ideal\<rangle>) =
        complex_of_real (\<Sum>k<N. (cmod (pe_amp N phi k))\<^sup>2 *
          ((sqrt (1 - (f k)\<^sup>2) - sqrt (1 - c\<^sup>2))\<^sup>2 + (f k - c)\<^sup>2))"
    unfolding r_br_def rot_diff_inner by (simp add: of_real_sum)
  thus ?thesis unfolding hhl_approx_error by (rule arg_cong[where f = "\<lambda>x. \<langle>u|u\<rangle> * x"])
qed

end


subsection \<open>Bounds on the branch distances and amplitudes\<close>

text \<open>$\norm{R(a)\ket0-R(b)\ket0}^2\le4$ for $|a|,|b|\le1$.\<close>

lemma rot_dist_le_four:
  assumes "\<bar>a\<bar> \<le> 1" "\<bar>b\<bar> \<le> 1"
  shows "(sqrt (1 - a\<^sup>2) - sqrt (1 - b\<^sup>2))\<^sup>2 + (a - b)\<^sup>2 \<le> 4"
proof -
  have a2: "a\<^sup>2 \<le> 1" and b2: "b\<^sup>2 \<le> 1" using assms abs_square_le_1 by auto
  have sq: "(x - y)\<^sup>2 \<le> 2 * x\<^sup>2 + 2 * y\<^sup>2" for x y :: real
    using sum_squares_bound[of x y] sum_squares_bound[of x "- y"] by (simp add: power2_diff algebra_simps)
  have "(sqrt (1 - a\<^sup>2) - sqrt (1 - b\<^sup>2))\<^sup>2 \<le> 2 * (sqrt (1 - a\<^sup>2))\<^sup>2 + 2 * (sqrt (1 - b\<^sup>2))\<^sup>2" by (rule sq)
  also have "\<dots> = 2 * (1 - a\<^sup>2) + 2 * (1 - b\<^sup>2)" using a2 b2 by simp
  finally show ?thesis using sq[of a b] by simp
qed

text \<open>Lipschitz estimate for $0\le a,b\le\theta<1$:
$\norm{R(a)\ket0-R(b)\ket0}^2\le(a-b)^2/(1-\theta^2)$.\<close>

lemma rot_dist_lipschitz:
  assumes th: "0 < \<theta>" "\<theta> < 1" and a: "0 \<le> a" "a \<le> \<theta>" and b: "0 \<le> b" "b \<le> \<theta>"
  shows "(sqrt (1 - a\<^sup>2) - sqrt (1 - b\<^sup>2))\<^sup>2 + (a - b)\<^sup>2 \<le> (a - b)\<^sup>2 / (1 - \<theta>\<^sup>2)"
proof -
  let ?sa = "sqrt (1 - a\<^sup>2)" and ?sb = "sqrt (1 - b\<^sup>2)" and ?st = "sqrt (1 - \<theta>\<^sup>2)"
  have t2: "0 < 1 - \<theta>\<^sup>2" using th mult_strict_mono[of \<theta> 1 \<theta> 1] by (simp add: power2_eq_square)
  have a2: "a\<^sup>2 \<le> \<theta>\<^sup>2" and b2: "b\<^sup>2 \<le> \<theta>\<^sup>2" using a b by (auto intro: power_mono)
  have sa: "?st \<le> ?sa" and sb: "?st \<le> ?sb" using a2 b2 by (auto intro: real_sqrt_le_mono)
  have st: "0 < ?st" using t2 by simp
  have den: "2 * ?st \<le> ?sa + ?sb" using sa sb by linarith
  have sa2: "?sa * ?sa = 1 - a\<^sup>2" and sb2: "?sb * ?sb = 1 - b\<^sup>2"
    using a2 b2 t2 by (auto intro!: real_sqrt_mult_self)
  have pa: "\<bar>1 - a\<^sup>2\<bar> = 1 - a\<^sup>2" and pb: "\<bar>1 - b\<^sup>2\<bar> = 1 - b\<^sup>2" using a2 b2 t2 by simp_all
  have prod: "(?sa - ?sb) * (?sa + ?sb) = b\<^sup>2 - a\<^sup>2"
    by (simp add: algebra_simps pa pb)
  have "\<bar>?sa - ?sb\<bar> * (2 * ?st) \<le> \<bar>?sa - ?sb\<bar> * (?sa + ?sb)" by (rule mult_left_mono[OF den]) simp
  also have "\<dots> = \<bar>(?sa - ?sb) * (?sa + ?sb)\<bar>"
  proof -
    have pos: "0 \<le> ?sa + ?sb" using a2 b2 t2 by (intro add_nonneg_nonneg real_sqrt_ge_zero) linarith+
    show ?thesis unfolding abs_mult abs_of_nonneg[OF pos] ..
  qed
  also have "\<dots> = \<bar>b\<^sup>2 - a\<^sup>2\<bar>" unfolding prod ..
  also have "\<dots> = \<bar>a - b\<bar> * (a + b)"
  proof -
    have "b\<^sup>2 - a\<^sup>2 = (a - b) * (- (a + b))" by (simp add: algebra_simps power2_eq_square)
    thus ?thesis using abs_of_nonneg[of "a + b"] a b by (simp add: abs_mult)
  qed
  also have "\<dots> \<le> \<bar>a - b\<bar> * (2 * \<theta>)" using a b by (intro mult_left_mono) auto
  finally have "\<bar>?sa - ?sb\<bar> \<le> \<bar>a - b\<bar> * \<theta> / ?st" using st by (simp add: field_simps)
  hence "(?sa - ?sb)\<^sup>2 \<le> (\<bar>a - b\<bar> * \<theta> / ?st)\<^sup>2"
    using power_mono[OF _ abs_ge_zero, of "?sa - ?sb" "\<bar>a - b\<bar> * \<theta> / ?st" 2] by (simp add: power2_abs)
  also have "\<dots> = (a - b)\<^sup>2 * (\<theta>\<^sup>2 / (1 - \<theta>\<^sup>2))" using t2 by (simp add: power_divide power_mult_distrib)
  finally have "(?sa - ?sb)\<^sup>2 + (a - b)\<^sup>2 \<le> (a - b)\<^sup>2 * (\<theta>\<^sup>2 / (1 - \<theta>\<^sup>2)) + (a - b)\<^sup>2" by simp
  also have "\<dots> = (a - b)\<^sup>2 / (1 - \<theta>\<^sup>2)" using t2 by (simp add: field_simps)
  finally show ?thesis .
qed

text \<open>The amplitudes are $1$-periodic in $\varphi$.\<close>

lemma pe_amp_shift_up: "pe_amp N \<phi> j = pe_amp N (\<phi> + 1) j"
proof -
  have "cis (2 * pi * real k * (\<phi> + 1 - real j / real N)) = cis (2 * pi * real k * (\<phi> - real j / real N))" for k
  proof -
    have "cis (2 * pi * real k * (\<phi> + 1 - real j / real N)) = cis (2 * pi * real k * (\<phi> - real j / real N)) * cis (2 * pi * real k)"
      by (subst cis_mult) (simp add: algebra_simps)
    also have "cis (2 * pi * real k) = 1" by (rule cis_multiple_2pi) simp
    finally show ?thesis by simp
  qed
  thus ?thesis unfolding pe_amp_def by simp
qed


subsection \<open>The error bound\<close>

lemma pe_amp_tail_sq:
  assumes N: "0 < N" and d: "\<bar>\<phi> - real j / real N\<bar> \<le> 1 / 2" and d0: "\<phi> \<noteq> real j / real N"
  shows "(cmod (pe_amp N \<phi> j))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * (\<phi> - real j / real N)\<^sup>2)"
proof -
  have "(cmod (pe_amp N \<phi> j))\<^sup>2 \<le> (1 / (2 * real N * \<bar>\<phi> - real j / real N\<bar>))\<^sup>2"
    by (rule power_mono[OF pe_amp_tail[OF N d d0]]) simp
  also have "\<dots> = 1 / (4 * (real N)\<^sup>2 * (\<phi> - real j / real N)\<^sup>2)"
    by (simp add: power_divide power_mult_distrib power2_abs)
  finally show ?thesis .
qed

text \<open>Standing hypotheses of the bound: $0<C$, $0<\theta<1$, $\lambda\ge2C/\theta$ (the eigenvalue
is at least twice the threshold $\lambda_{\mathrm{lo}}=C/\theta$ below which the angle is clamped)
and $t_0\lambda\le\pi/2$ (the phase $\varphi=t_0\lambda/2\pi$ is at most $\tfrac14$).\<close>

lemma hhl_param_facts:
  assumes t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
  shows "0 < l" "0 < hhl_phi t0 l" "hhl_phi t0 l \<le> 1 / 4" "C / l \<le> \<theta> / 2" "0 \<le> C / l" "\<bar>C / l\<bar> \<le> 1"
    "2 * C \<le> \<theta> * l"
proof -
  have "0 < 2 * C / \<theta>" using C th by simp
  thus l0: "0 < l" using l_lo by linarith
  show "0 < hhl_phi t0 l" unfolding hhl_phi_def using t0 l0 by simp
  show "hhl_phi t0 l \<le> 1 / 4" unfolding hhl_phi_def using l_hi t0 by (simp add: field_simps)
  show Cl: "2 * C \<le> \<theta> * l" using l_lo th by (simp add: field_simps)
  have "C / l \<le> C / (2 * C / \<theta>)" by (rule divide_left_mono[OF l_lo]) (use C th l0 in simp_all)
  also have "C / (2 * C / \<theta>) = \<theta> / 2" using C th by (simp add: field_simps)
  finally show cle: "C / l \<le> \<theta> / 2" .
  show c0: "0 \<le> C / l" using C l0 by simp
  show "\<bar>C / l\<bar> \<le> 1" unfolding abs_of_nonneg[OF c0] using cle th by linarith
qed

text \<open>Good branches: register value $\lambda_k\ge C/\theta$ in the positive half.\<close>

lemma hhl_branch_good:
  assumes N: "0 < N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
      and k: "2 * k < N" and lam: "C / \<theta> \<le> reg_eig t0 N k"
  shows "(cmod (pe_amp N (hhl_phi t0 l) k))\<^sup>2 *
           ((sqrt (1 - (clamp (C / reg_eig t0 N k))\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (clamp (C / reg_eig t0 N k) - C / l)\<^sup>2)
         \<le> pi\<^sup>2 * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
proof -
  note pf = hhl_param_facts[OF t0 C th l_lo l_hi]
  let ?lam = "reg_eig t0 N k" and ?ph = "hhl_phi t0 l" and ?c = "C / l"
  let ?d = "\<lambda>x. (sqrt (1 - x\<^sup>2) - sqrt (1 - ?c\<^sup>2))\<^sup>2 + (x - ?c)\<^sup>2"
  define \<delta> where "\<delta> = ?ph - real k / real N"
  have lamv: "?lam = 2 * pi * real k / (t0 * real N)" using k by (simp add: reg_eig_def)
  have Ct: "0 < C / \<theta>" using C th by simp
  have lam_pos: "0 < ?lam" using lam Ct by linarith
  have t2: "0 < 1 - \<theta>\<^sup>2" using th mult_strict_mono[of \<theta> 1 \<theta> 1] by (simp add: power2_eq_square)
  have fk_le: "C / ?lam \<le> \<theta>"
  proof -
    have "C / ?lam \<le> C / (C / \<theta>)" by (rule divide_left_mono[OF lam]) (use C Ct lam_pos th in simp_all)
    thus ?thesis using C by simp
  qed
  have fk0: "0 \<le> C / ?lam" using C lam_pos by simp
  have fk: "clamp (C / ?lam) = C / ?lam" by (rule clamp_id) (use fk_le fk0 th in simp)
  have c_le: "?c \<le> \<theta>" using pf(4) th by linarith
  have lip: "?d (C / ?lam) \<le> (C / ?lam - ?c)\<^sup>2 / (1 - \<theta>\<^sup>2)"
    by (rule rot_dist_lipschitz[OF th fk0 fk_le pf(5) c_le])
  have diff: "l - ?lam = 2 * pi / t0 * \<delta>"
    unfolding lamv \<delta>_def hhl_phi_def using t0 N by (simp add: field_simps)
  have cd: "C / ?lam - ?c = C * (l - ?lam) / (?lam * l)" using lam_pos pf(1) by (simp add: field_simps)
  have ll: "C\<^sup>2 / \<theta>\<^sup>2 \<le> ?lam * l"
  proof -
    have "C / \<theta> \<le> l" using l_lo Ct by linarith
    hence "C / \<theta> * (C / \<theta>) \<le> ?lam * l" by (intro mult_mono lam) (use Ct lam_pos in simp_all)
    thus ?thesis by (simp add: power_divide power2_eq_square)
  qed
  have sq: "(C / ?lam - ?c)\<^sup>2 \<le> 4 * pi\<^sup>2 * \<theta> ^ 4 * \<delta>\<^sup>2 / (t0\<^sup>2 * C\<^sup>2)"
  proof -
    have "(C / ?lam - ?c)\<^sup>2 = C\<^sup>2 * (l - ?lam)\<^sup>2 / (?lam * l)\<^sup>2" unfolding cd by (simp add: power_divide power_mult_distrib)
    also have "\<dots> \<le> C\<^sup>2 * (l - ?lam)\<^sup>2 / (C\<^sup>2 / \<theta>\<^sup>2)\<^sup>2"
      by (rule divide_left_mono[OF power_mono[OF ll]]) (use C th lam_pos pf(1) in \<open>simp_all add: power2_eq_square\<close>)
    also have "\<dots> = (l - ?lam)\<^sup>2 * \<theta> ^ 4 / C\<^sup>2" using C th by (simp add: power_divide field_simps)
    also have "\<dots> = 4 * pi\<^sup>2 * \<theta> ^ 4 * \<delta>\<^sup>2 / (t0\<^sup>2 * C\<^sup>2)" unfolding diff using t0 by (simp add: power_divide power_mult_distrib field_simps)
    finally show ?thesis .
  qed
  have d_le: "?d (C / ?lam) \<le> 4 * pi\<^sup>2 * \<theta> ^ 4 * \<delta>\<^sup>2 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
    using lip divide_right_mono[OF sq, of "1 - \<theta>\<^sup>2"] t2 by (simp add: divide_divide_eq_left)
  have d0: "0 \<le> ?d (C / ?lam)" by simp
  have a0: "0 \<le> (cmod (pe_amp N ?ph k))\<^sup>2" by simp
  have dabs: "\<bar>\<delta>\<bar> \<le> 1 / 2"
  proof -
    have "real k / real N < 1 / 2" using k N by (simp add: field_simps)
    moreover have "0 \<le> real k / real N" by simp
    ultimately show ?thesis unfolding \<delta>_def using pf(2,3) by (intro abs_leI; linarith)
  qed
  show ?thesis
  proof (cases "\<delta> = 0")
    case True
    hence "?d (C / ?lam) = 0" using d_le d0 by simp
    thus ?thesis unfolding fk using t2 C t0 N th by simp
  next
    case False
    have a: "(cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * \<delta>\<^sup>2)"
      using pe_amp_tail_sq[OF N, of ?ph k] dabs False unfolding \<delta>_def by simp
    have "(cmod (pe_amp N ?ph k))\<^sup>2 * ?d (C / ?lam) \<le>
          1 / (4 * (real N)\<^sup>2 * \<delta>\<^sup>2) * (4 * pi\<^sup>2 * \<theta> ^ 4 * \<delta>\<^sup>2 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)))"
      by (rule mult_mono[OF a d_le]) (simp_all add: d0)
    also have "\<dots> = pi\<^sup>2 * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
      using False N t0 C t2 by (simp add: field_simps)
    finally show ?thesis unfolding fk .
  qed
qed

text \<open>Branches below the threshold in the positive half: weight at most $1/(N\varphi)^2$.\<close>

lemma hhl_branch_low:
  assumes N: "0 < N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
      and k: "2 * k < N" and lam: "reg_eig t0 N k < C / \<theta>"
  shows "(cmod (pe_amp N (hhl_phi t0 l) k))\<^sup>2 \<le> 1 / ((real N)\<^sup>2 * (hhl_phi t0 l)\<^sup>2)"
proof -
  note pf = hhl_param_facts[OF t0 C th l_lo l_hi]
  let ?ph = "hhl_phi t0 l"
  define \<delta> where "\<delta> = ?ph - real k / real N"
  have lamv: "reg_eig t0 N k = 2 * pi * real k / (t0 * real N)" using k by (simp add: reg_eig_def)
  have kN: "real k / real N < C * t0 / (2 * pi * \<theta>)"
    using lam unfolding lamv using t0 th N by (simp add: field_simps)
  have ph2: "C * t0 / (2 * pi * \<theta>) \<le> ?ph / 2"
    unfolding hhl_phi_def using pf(7) t0 th by (simp add: field_simps)
  have dgt: "?ph / 2 < \<delta>" unfolding \<delta>_def using kN ph2 by linarith
  have dle: "\<delta> \<le> ?ph" unfolding \<delta>_def by simp
  have dabs: "\<bar>\<delta>\<bar> \<le> 1 / 2" using dgt dle pf(2,3) by (intro abs_leI; linarith)
  have d0: "\<delta> \<noteq> 0" using dgt pf(2) by simp
  have "(cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * \<delta>\<^sup>2)"
    using pe_amp_tail_sq[OF N, of ?ph k] dabs d0 unfolding \<delta>_def by simp
  also have "\<dots> \<le> 1 / (4 * (real N)\<^sup>2 * (?ph / 2)\<^sup>2)"
  proof (rule divide_left_mono)
    have "(?ph / 2)\<^sup>2 \<le> \<delta>\<^sup>2" using dgt pf(2) by (intro power_mono) simp_all
    thus "4 * (real N)\<^sup>2 * (?ph / 2)\<^sup>2 \<le> 4 * (real N)\<^sup>2 * \<delta>\<^sup>2" by (intro mult_left_mono) simp_all
    show "0 \<le> (1::real)" by simp
    show "0 < 4 * (real N)\<^sup>2 * \<delta>\<^sup>2 * (4 * (real N)\<^sup>2 * (?ph / 2)\<^sup>2)" using N d0 pf(2) by simp
  qed
  also have "\<dots> = 1 / ((real N)\<^sup>2 * ?ph\<^sup>2)" by (simp add: power_divide)
  finally show ?thesis .
qed

text \<open>Branches in the negative half: weight at most $1/(N\varphi)^2$.\<close>

lemma hhl_branch_neg:
  assumes N: "0 < N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
      and k: "k < N" and k2: "\<not> 2 * k < N"
  shows "(cmod (pe_amp N (hhl_phi t0 l) k))\<^sup>2 \<le> 1 / ((real N)\<^sup>2 * (hhl_phi t0 l)\<^sup>2)"
proof -
  note pf = hhl_param_facts[OF t0 C th l_lo l_hi]
  let ?ph = "hhl_phi t0 l"
  define \<delta> where "\<delta> = ?ph - real k / real N"
  have kN1: "1 / 2 \<le> real k / real N" using k2 N by (simp add: field_simps)
  have kN2: "real k / real N < 1" using k N by simp
  have ph16: "?ph\<^sup>2 \<le> (1 / 4)\<^sup>2" using pf(2,3) by (intro power_mono) simp_all
  have bound_from: "(cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * g\<^sup>2) \<Longrightarrow> ?ph \<le> 2 * g \<Longrightarrow> 0 < g \<Longrightarrow>
                    (cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / ((real N)\<^sup>2 * ?ph\<^sup>2)" for g
  proof -
    assume a: "(cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * g\<^sup>2)" and g: "?ph \<le> 2 * g" "0 < g"
    have "?ph\<^sup>2 \<le> (2 * g)\<^sup>2" using g pf(2) by (intro power_mono) simp_all
    hence "(real N)\<^sup>2 * ?ph\<^sup>2 \<le> 4 * (real N)\<^sup>2 * g\<^sup>2"
      using mult_left_mono[of "?ph\<^sup>2" "4 * g\<^sup>2" "(real N)\<^sup>2"] by (simp add: power_mult_distrib algebra_simps)
    hence "1 / (4 * (real N)\<^sup>2 * g\<^sup>2) \<le> 1 / ((real N)\<^sup>2 * ?ph\<^sup>2)"
      by (rule divide_left_mono) (use N pf(2) g in simp_all)
    with a show ?thesis by linarith
  qed
  show ?thesis
  proof (cases "- (1 / 2) \<le> \<delta>")
    case True
    have dneg: "\<delta> \<le> - (1 / 4)" unfolding \<delta>_def using kN1 pf(3) by linarith
    have dabs: "\<bar>\<delta>\<bar> \<le> 1 / 2" using True dneg by (intro abs_leI; linarith)
    have d0: "\<delta> \<noteq> 0" using dneg by simp
    have a: "(cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * \<delta>\<^sup>2)"
      using pe_amp_tail_sq[OF N, of ?ph k] dabs d0 unfolding \<delta>_def by simp
    have "(1 / 4)\<^sup>2 \<le> \<delta>\<^sup>2"
    proof -
      have "1 / 4 \<le> \<bar>\<delta>\<bar>" using dneg by simp
      from power_mono[OF this, of 2] show ?thesis by (simp add: power2_abs)
    qed
    hence "1 / (4 * (real N)\<^sup>2 * \<delta>\<^sup>2) \<le> 1 / (4 * (real N)\<^sup>2 * (1 / 4)\<^sup>2)"
      by (rule divide_left_mono[OF mult_left_mono]) (use N d0 in simp_all)
    with a have "(cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * (1 / 4)\<^sup>2)" by linarith
    thus ?thesis by (rule bound_from) (use pf(3) in simp_all)
  next
    case False
    define \<delta>' where "\<delta>' = (?ph + 1) - real k / real N"
    have d'1: "\<delta>' < 1 / 2" unfolding \<delta>'_def using False \<delta>_def by linarith
    have d'2: "?ph < \<delta>'" unfolding \<delta>'_def using kN2 by linarith
    have dabs: "\<bar>\<delta>'\<bar> \<le> 1 / 2" using d'1 d'2 pf(2) by (intro abs_leI; linarith)
    have d0: "\<delta>' \<noteq> 0" using d'2 pf(2) by simp
    have a: "(cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * \<delta>'\<^sup>2)"
      using pe_amp_tail_sq[OF N, of "?ph + 1" k] dabs d0 unfolding \<delta>'_def pe_amp_shift_up[of N ?ph k] by simp
    have "?ph\<^sup>2 \<le> \<delta>'\<^sup>2" using d'2 pf(2) by (intro power_mono) simp_all
    hence "1 / (4 * (real N)\<^sup>2 * \<delta>'\<^sup>2) \<le> 1 / (4 * (real N)\<^sup>2 * ?ph\<^sup>2)"
      by (rule divide_left_mono[OF mult_left_mono]) (use N d0 pf(2) in simp_all)
    with a have "(cmod (pe_amp N ?ph k))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * ?ph\<^sup>2)" by linarith
    thus ?thesis by (rule bound_from) (use pf(2) in simp_all)
  qed
qed

text \<open>Every branch: $|\alpha_k|^2d_k^2\le b_1+b_2$ with
$b_1=\pi^2\theta^4/(N^2t_0^2C^2(1-\theta^2))$, $b_2=4/(N\varphi)^2$.\<close>

lemma hhl_branch_bound:
  assumes N: "0 < N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2" and k: "k < N"
  shows "(cmod (pe_amp N (hhl_phi t0 l) k))\<^sup>2 *
           ((sqrt (1 - (clamp (C / reg_eig t0 N k))\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (clamp (C / reg_eig t0 N k) - C / l)\<^sup>2)
         \<le> pi\<^sup>2 * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 4 / ((real N)\<^sup>2 * (hhl_phi t0 l)\<^sup>2)"
proof -
  note pf = hhl_param_facts[OF t0 C th l_lo l_hi]
  let ?a = "(cmod (pe_amp N (hhl_phi t0 l) k))\<^sup>2"
  let ?d = "(sqrt (1 - (clamp (C / reg_eig t0 N k))\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (clamp (C / reg_eig t0 N k) - C / l)\<^sup>2"
  have t2: "0 < 1 - \<theta>\<^sup>2" using th mult_strict_mono[of \<theta> 1 \<theta> 1] by (simp add: power2_eq_square)
  have b1: "0 \<le> pi\<^sup>2 * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))" using t2 by simp
  have b2: "0 \<le> 4 / ((real N)\<^sup>2 * (hhl_phi t0 l)\<^sup>2)" by simp
  have d4: "?d \<le> 4" by (rule rot_dist_le_four[OF clamp_abs pf(6)])
  have d0: "0 \<le> ?d" by simp
  have weight: "?a \<le> 1 / ((real N)\<^sup>2 * (hhl_phi t0 l)\<^sup>2) \<Longrightarrow> ?thesis"
  proof -
    assume a: "?a \<le> 1 / ((real N)\<^sup>2 * (hhl_phi t0 l)\<^sup>2)"
    have "?a * ?d \<le> 1 / ((real N)\<^sup>2 * (hhl_phi t0 l)\<^sup>2) * 4" by (rule mult_mono[OF a d4]) simp_all
    thus ?thesis using b1 by simp
  qed
  show ?thesis
  proof (cases "2 * k < N")
    case True
    show ?thesis
    proof (cases "C / \<theta> \<le> reg_eig t0 N k")
      case True
      with \<open>2 * k < N\<close> show ?thesis using hhl_branch_good[OF N t0 C th l_lo l_hi] b2 by (simp add: add_increasing2)
    next
      case False
      thus ?thesis by (intro weight hhl_branch_low[OF N t0 C th l_lo l_hi True]) simp
    qed
  next
    case False
    thus ?thesis by (intro weight hhl_branch_neg[OF N t0 C th l_lo l_hi k])
  qed
qed

text \<open>The error bound for the clamped circuit on an eigenvector: with $\varphi=t_0\lambda/2\pi$,
\[\norm{\text{output}-u_N\otimes u\otimes R(C/\lambda)\ket0}^2
  \le\norm u^2\,\frac{\pi^2}{N t_0^2}\Bigl(\frac{\theta^4}{C^2(1-\theta^2)}+\frac{16}{\lambda^2}\Bigr).\]\<close>

lemma hhl_bound_algebra:
  assumes N: "0 < N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and l0: "0 < l"
  shows "real N * (pi\<^sup>2 * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 4 / ((real N)\<^sup>2 * (hhl_phi t0 l)\<^sup>2)) =
         pi\<^sup>2 / (real N * t0\<^sup>2) * (\<theta> ^ 4 / (C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 16 / l\<^sup>2)"
proof -
  have t2: "0 < 1 - \<theta>\<^sup>2" using th mult_strict_mono[of \<theta> 1 \<theta> 1] by (simp add: power2_eq_square)
  have Nn: "real N \<noteq> 0" using N by simp
  have cancel: "real N * (X / ((real N)\<^sup>2 * Y)) = X / (real N * Y)" for X Y :: real
    using Nn by (cases "Y = 0") (simp_all add: power2_eq_square field_simps)
  have p2: "(hhl_phi t0 l)\<^sup>2 = t0\<^sup>2 * l\<^sup>2 / (4 * pi\<^sup>2)"
    unfolding hhl_phi_def by (simp add: power_divide power_mult_distrib)
  have e1: "pi\<^sup>2 * \<theta> ^ 4 / (real N * (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))) = pi\<^sup>2 / (real N * t0\<^sup>2) * (\<theta> ^ 4 / (C\<^sup>2 * (1 - \<theta>\<^sup>2)))"
    by (simp add: field_simps)
  have e2: "4 / (real N * (hhl_phi t0 l)\<^sup>2) = pi\<^sup>2 / (real N * t0\<^sup>2) * (16 / l\<^sup>2)"
    unfolding p2 using N t0 l0 by (simp add: field_simps)
  have g: "(real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2) = (real N)\<^sup>2 * (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
    by (simp add: mult.assoc)
  show ?thesis unfolding distrib_left g cancel e1 e2 by simp
qed

theorem hhl_clamped_error_bound:
  fixes A :: "complex Matrix.mat" and u :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
  shows "Re \<langle>hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) -
              tensor_vec (uniform_state N) (tensor_vec u (rot (C / l) *\<^sub>v unit_vec 2 0)) |
            hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) -
              tensor_vec (uniform_state N) (tensor_vec u (rot (C / l) *\<^sub>v unit_vec 2 0))\<rangle>
         \<le> Re \<langle>u|u\<rangle> * (pi\<^sup>2 / (real N * t0\<^sup>2) * (\<theta> ^ 4 / (C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 16 / l\<^sup>2))"
proof -
  note pf = hhl_param_facts[OF t0 C th l_lo l_hi]
  let ?f = "\<lambda>k. clamp (C / reg_eig t0 N k)" and ?c = "C / l" and ?ph = "hhl_phi t0 l"
  let ?S = "\<Sum>k<N. (cmod (pe_amp N ?ph k))\<^sup>2 * ((sqrt (1 - (?f k)\<^sup>2) - sqrt (1 - ?c\<^sup>2))\<^sup>2 + (?f k - ?c)\<^sup>2)"
  let ?b = "pi\<^sup>2 * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 4 / ((real N)\<^sup>2 * ?ph\<^sup>2)"
  define ru where "ru = (\<Sum>i<n. (cmod (u $ i))\<^sup>2)"
  have uu: "\<langle>u|u\<rangle> = complex_of_real ru" unfolding ru_def by (simp add: inner_self_sum[OF u])
  have ru0: "0 \<le> ru" unfolding ru_def by (simp add: sum_nonneg)
  have E: "\<langle>hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) -
              tensor_vec (uniform_state N) (tensor_vec u (rot ?c *\<^sub>v unit_vec 2 0)) |
            hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) -
              tensor_vec (uniform_state N) (tensor_vec u (rot ?c *\<^sub>v unit_vec 2 0))\<rangle> = complex_of_real (ru * ?S)"
    unfolding hhl_circuit_clamped_def
    using hhl_approx_error_real[OF A t0 N u ev, of ?f ?c] unfolding uu by simp
  have S: "?S \<le> real N * ?b"
  proof -
    have "?S \<le> (\<Sum>k<N. ?b)" by (rule sum_mono) (rule hhl_branch_bound[OF N t0 C th l_lo l_hi], simp)
    thus ?thesis by simp
  qed
  have Nb: "real N * ?b = pi\<^sup>2 / (real N * t0\<^sup>2) * (\<theta> ^ 4 / (C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 16 / l\<^sup>2)"
    by (rule hhl_bound_algebra[OF N t0 C th pf(1)])
  have "Re (complex_of_real (ru * ?S)) = ru * ?S" by simp
  also have "\<dots> \<le> ru * (real N * ?b)" by (rule mult_left_mono[OF S ru0])
  finally show ?thesis unfolding E Nb uu by simp
qed

end
