theory HHL_Runtime
  imports HHL_Filter_Bounds
begin

section \<open>Further results of the HHL paper\<close>

text \<open>The error metric of Appendix A, the concentration bound (A32) with the paper's constant,
amplification without knowing the success probability (BHMT's averaging lemma), amplification
of the post-selection on $\ket{\mathrm{well}}$, and the run time in the paper's normalisation:
accuracy $\varepsilon$ with total evolution time $t=O(\kappa/\varepsilon)$, $O(\kappa)$ amplification
rounds, total evolution time $O(\kappa^2/\varepsilon)$ over all oracle calls.\<close>


subsection \<open>The error metric\<close>

text \<open>For unit vectors $\norm{\ket\alpha-\ket\beta}=\sqrt{2(1-\mathrm{Re}\langle\alpha|\beta\rangle)}$, the metric of App.~A.\<close>

lemma inner_minus_expand:
  assumes "dim_vec a = n" "dim_vec b = n"
  shows "\<langle>a - b|a - b\<rangle> = \<langle>a|a\<rangle> - \<langle>a|b\<rangle> - \<langle>b|a\<rangle> + \<langle>b|b\<rangle>"
  using assms by (simp add: Quantum.inner_prod_def atLeast0LessThan sum_subtractf sum.distrib algebra_simps)

lemma unit_dist:
  assumes a: "dim_vec a = n" "\<parallel>a\<parallel> = 1" and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1"
  shows "\<parallel>a - b\<parallel> = sqrt (2 * (1 - Re \<langle>a|b\<rangle>))"
proof -
  have aa: "\<langle>a|a\<rangle> = 1" and bb: "\<langle>b|b\<rangle> = 1" using a(2) b(2) unfolding cpx_vec_length_inner_prod[symmetric] by simp_all
  have ba: "\<langle>b|a\<rangle> = cnj \<langle>a|b\<rangle>" using inner_prod_cnj[of a b] a b by simp
  have "complex_of_real (\<parallel>a - b\<parallel>\<^sup>2) = 2 - (\<langle>a|b\<rangle> + cnj \<langle>a|b\<rangle>)"
    unfolding cpx_vec_length_inner_prod inner_minus_expand[OF a(1) b(1)] aa bb ba by simp
  also have "\<langle>a|b\<rangle> + cnj \<langle>a|b\<rangle> = complex_of_real (2 * Re \<langle>a|b\<rangle>)" by (simp add: complex_add_cnj)
  finally have "complex_of_real (\<parallel>a - b\<parallel>\<^sup>2) = complex_of_real (2 * (1 - Re \<langle>a|b\<rangle>))" by simp
  hence "\<parallel>a - b\<parallel>\<^sup>2 = 2 * (1 - Re \<langle>a|b\<rangle>)" by (simp only: of_real_eq_iff)
  thus ?thesis using vnorm_ge0 by (metis real_sqrt_unique)
qed

subsection \<open>The concentration bound (A32)\<close>

lemma sin_cubic_lower:
  fixes y :: real
  shows "0 \<le> y \<Longrightarrow> y - y ^ 3 / 6 \<le> sin y"
proof -
  assume y0: "0 \<le> y"
  have "\<bar>sin y - (\<Sum>m<3. sin_coeff m * y ^ m)\<bar> \<le> inverse (fact 3) * \<bar>y\<bar> ^ 3" by (rule Maclaurin_sin_bound)
  moreover have "(\<Sum>m<3. sin_coeff m * y ^ m) = y" by (simp add: numeral_3_eq_3 sin_coeff_def)
  moreover have "inverse (fact 3) * \<bar>y\<bar> ^ 3 = y ^ 3 / 6" using y0 by (simp add: numeral_3_eq_3 field_simps)
  ultimately show ?thesis by linarith
qed

text \<open>(A32): with $\delta=\lambda_jt-2\pi k$ (here $\delta=2\pi N(\varphi-k/N)$),
$|\alpha_{k|j}|\le8\pi/\delta^2$ for $2\pi\le|\delta|\le N$.\<close>

theorem win_amp_A32:
  fixes \<phi> :: real
  assumes N: "4 \<le> N" and k: "k < N"
  defines "\<delta> \<equiv> 2 * pi * real N * (\<phi> - real k / real N)"
  assumes lo: "2 * pi \<le> \<bar>\<delta>\<bar>" and hi: "\<bar>\<delta>\<bar> \<le> real N"
  shows "cmod (pe_amp_reg N (win_state N) \<phi> k) \<le> 8 * pi / \<delta>\<^sup>2"
proof -
  have NR: "0 < real N" and N4: "4 \<le> real N" using N by simp_all
  define a x where "a = pi / real N" and "x = 2 * pi * (\<phi> - real k / real N)"
  have Na: "real N * a = pi" unfolding a_def using NR by simp
  have xd: "x = \<delta> / real N" unfolding x_def \<delta>_def using NR by simp
  have a0: "0 < a" unfolding a_def using NR by simp
  define yp ym where "yp = (\<bar>x\<bar> + a) / 2" and "ym = (\<bar>x\<bar> - a) / 2"
  have ax: "\<bar>x\<bar> = \<bar>\<delta>\<bar> / real N" unfolding xd using NR by (simp add: abs_divide)
  have ym0: "0 < ym"
  proof -
    have "pi < \<bar>\<delta>\<bar>" using lo pi_gt_zero by linarith
    hence "a < \<bar>x\<bar>" unfolding ax a_def using NR by (simp add: divide_strict_right_mono)
    thus ?thesis unfolding ym_def by simp
  qed
  have yp1: "yp \<le> 1"
  proof -
    have "\<bar>\<delta>\<bar> + pi \<le> 2 * real N" using hi N4 pi_less_4 by linarith
    thus ?thesis unfolding yp_def ax a_def using NR by (simp add: field_simps)
  qed
  have ymp: "ym \<le> yp" unfolding ym_def yp_def using a0 by simp
  have sp: "5 / 6 * yp \<le> sin yp" and sm: "5 / 6 * ym \<le> sin ym"
  proof -
    have c: "5 / 6 * y \<le> sin y" if "0 \<le> y" "y \<le> 1" for y :: real
    proof -
      have "y * y \<le> 1" using that mult_mono[of y 1 y 1] by simp
      hence "y * y * y \<le> 1 * y" using that by (intro mult_right_mono) simp_all
      hence "y ^ 3 \<le> y" by (simp add: power3_eq_cube)
      thus ?thesis using sin_cubic_lower[OF that(1)] by linarith
    qed
    show "5 / 6 * yp \<le> sin yp" by (rule c) (use ym0 ymp yp1 in linarith)+
    show "5 / 6 * ym \<le> sin ym" by (rule c) (use ym0 ymp yp1 in linarith)+
  qed
  have sins: "\<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar> = sin yp * sin ym"
  proof (cases "0 \<le> x")
    case True
    have "\<bar>sin ((x + a) / 2)\<bar> = sin yp" "\<bar>sin ((x - a) / 2)\<bar> = sin ym"
      using True sp sm ym0 ymp unfolding yp_def ym_def by (simp_all add: abs_of_nonneg)
    thus ?thesis by simp
  next
    case False
    have e1: "(x + a) / 2 = - ym" and e2: "(x - a) / 2 = - yp" using False unfolding yp_def ym_def by (simp_all add: field_simps)
    have "\<bar>sin ((x + a) / 2)\<bar> = sin ym" "\<bar>sin ((x - a) / 2)\<bar> = sin yp"
      unfolding e1 e2 using sp sm ym0 ymp by (simp_all add: abs_of_nonneg)
    thus ?thesis by simp
  qed
  have sp0: "0 < sin yp" and sm0: "0 < sin ym" using sp sm ym0 ymp by linarith+
  have c1: "cis (x + a) \<noteq> 1" and c2: "cis (x - a) \<noteq> 1"
  proof -
    have "\<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar> \<noteq> 0" unfolding sins using sp0 sm0 by simp
    hence n1: "sin ((x + a) / 2) \<noteq> 0" and n2: "sin ((x - a) / 2) \<noteq> 0" by simp_all
    show "cis (x + a) \<noteq> 1" by (rule cis_ne_one_of_sin[OF n1])
    show "cis (x - a) \<noteq> 1" by (rule cis_ne_one_of_sin[OF n2])
  qed
  have amp: "pe_amp_reg N (win_state N) \<phi> k =
             complex_of_real (sqrt 2 / real N) * (\<Sum>\<tau><N. complex_of_real (sin (a * real \<tau> + a / 2)) * cis (real \<tau> * x))"
    unfolding win_amp_formula[OF k] a_def x_def by (simp add: field_simps)
  have "cmod (pe_amp_reg N (win_state N) \<phi> k) \<le> sqrt 2 / real N * (\<bar>sin (a / 2)\<bar> / (sin yp * sin ym))"
  proof -
    have ab: "\<bar>sqrt 2 / real N\<bar> = sqrt 2 / real N" by simp
    show ?thesis unfolding amp norm_mult norm_of_real ab sins[symmetric] using NR
      by (intro mult_left_mono window_sum_bound[OF Na c1 c2]) simp_all
  qed
  also have "\<dots> \<le> sqrt 2 / real N * ((a / 2) / (5 / 6 * yp * (5 / 6 * ym)))"
  proof (intro mult_left_mono frac_le)
    show "\<bar>sin (a / 2)\<bar> \<le> a / 2" using abs_sin_x_le_abs_x[of "a / 2"] a0 by simp
    show "5 / 6 * yp * (5 / 6 * ym) \<le> sin yp * sin ym" using sp sm ym0 ymp by (intro mult_mono) simp_all
  qed (use a0 ym0 ymp in simp_all)
  also have "\<dots> = 72 * sqrt 2 / 25 * pi / (\<delta>\<^sup>2 - pi\<^sup>2)"
  proof -
    have pr: "yp * ym = (\<delta>\<^sup>2 - pi\<^sup>2) / (4 * (real N)\<^sup>2)"
      unfolding yp_def ym_def ax a_def using NR by (simp add: field_simps power2_eq_square power2_abs)
    have dpos: "0 < \<delta>\<^sup>2 - pi\<^sup>2"
    proof -
      have "pi\<^sup>2 < (2 * pi)\<^sup>2" by (simp add: power_mult_distrib)
      also have "(2 * pi)\<^sup>2 \<le> \<delta>\<^sup>2" using power_mono[OF lo, of 2] by (simp add: power2_abs)
      finally show ?thesis by simp
    qed
    have e: "5 / 6 * yp * (5 / 6 * ym) = 25 / 36 * (yp * ym)" by simp
    show ?thesis unfolding e pr a_def using NR dpos by (simp add: field_simps power2_eq_square)
  qed
  also have "\<dots> \<le> 8 * pi / \<delta>\<^sup>2"
  proof -
    have d2: "4 * pi\<^sup>2 \<le> \<delta>\<^sup>2" using power_mono[OF lo, of 2] by (simp add: power2_abs power_mult_distrib)
    have dp: "0 < \<delta>\<^sup>2 - pi\<^sup>2" using d2 pi_gt_zero by (smt (verit) zero_less_power)
    have s2: "sqrt 2 \<le> 3 / 2"
    proof -
      have "sqrt 2 \<le> sqrt ((3 / 2)\<^sup>2)" by (rule real_sqrt_le_mono) (simp add: power2_eq_square)
      thus ?thesis by simp
    qed
    have "72 * sqrt 2 / 25 * pi * \<delta>\<^sup>2 \<le> 8 * pi * (\<delta>\<^sup>2 - pi\<^sup>2)"
    proof -
      have "72 * sqrt 2 / 25 \<le> 108 / 25" using s2 by simp
      hence "72 * sqrt 2 / 25 * (pi * \<delta>\<^sup>2) \<le> 108 / 25 * (pi * \<delta>\<^sup>2)" by (intro mult_right_mono) simp_all
      moreover have "108 / 25 * (pi * \<delta>\<^sup>2) \<le> 8 * pi * (\<delta>\<^sup>2 - pi\<^sup>2)"
      proof -
        have "pi * (92 / 25 * \<delta>\<^sup>2) \<ge> pi * (8 * pi\<^sup>2)" by (intro mult_left_mono; use d2 zero_le_power2[of pi] pi_gt_zero in linarith)
        moreover have "8 * pi * (\<delta>\<^sup>2 - pi\<^sup>2) = 8 * (pi * \<delta>\<^sup>2) - 8 * (pi * pi\<^sup>2)" by (simp add: algebra_simps)
        moreover have "pi * (92 / 25 * \<delta>\<^sup>2) = 92 / 25 * (pi * \<delta>\<^sup>2)" "pi * (8 * pi\<^sup>2) = 8 * (pi * pi\<^sup>2)"
          "108 / 25 * (pi * \<delta>\<^sup>2) = 108 / 25 * (pi * \<delta>\<^sup>2)" by simp_all
        ultimately show ?thesis by linarith
      qed
      ultimately show ?thesis by simp
    qed
    hence "72 * sqrt 2 / 25 * pi * \<delta>\<^sup>2 / ((\<delta>\<^sup>2 - pi\<^sup>2) * \<delta>\<^sup>2) \<le> 8 * pi * (\<delta>\<^sup>2 - pi\<^sup>2) / ((\<delta>\<^sup>2 - pi\<^sup>2) * \<delta>\<^sup>2)"
      using dp d2 by (intro divide_right_mono) simp_all
    moreover have "72 * sqrt 2 / 25 * pi * \<delta>\<^sup>2 / ((\<delta>\<^sup>2 - pi\<^sup>2) * \<delta>\<^sup>2) = 72 * sqrt 2 / 25 * pi / (\<delta>\<^sup>2 - pi\<^sup>2)"
    proof -
      have dz: "\<delta>\<^sup>2 \<noteq> 0" using d2 pi_gt_zero by (smt (verit) zero_less_power)
      show ?thesis by (rule mult_divide_mult_cancel_right[OF dz])
    qed
    moreover have "8 * pi * (\<delta>\<^sup>2 - pi\<^sup>2) / ((\<delta>\<^sup>2 - pi\<^sup>2) * \<delta>\<^sup>2) = 8 * pi / \<delta>\<^sup>2"
    proof -
      have Dz: "\<delta>\<^sup>2 - pi\<^sup>2 \<noteq> 0" using dp by simp
      have "(\<delta>\<^sup>2 - pi\<^sup>2) * \<delta>\<^sup>2 = \<delta>\<^sup>2 * (\<delta>\<^sup>2 - pi\<^sup>2)" by (simp only: mult_ac)
      thus ?thesis using mult_divide_mult_cancel_right[OF Dz, of "8 * pi" "\<delta>\<^sup>2"] by simp
    qed
    ultimately show ?thesis by simp
  qed
  finally show ?thesis .
qed

subsection \<open>Amplification with unknown success probability\<close>

text \<open>The paper (citing Brassard, H{\o}yer, Mosca and Tapp) runs amplitude amplification without
knowing $p$.  The precise statement behind this is BHMT's averaging lemma: for $k$ uniform in
$\{0,\dots,M-1\}$ the mean success probability is
$\frac12-\frac{\sin(4M\theta)}{4M\sin(2\theta)}$, at least $\frac14$ once $M\ge1/\sin(2\theta)$.\<close>

lemma cos_telescope:
  fixes \<theta> :: real
  shows "(\<Sum>k<M. 2 * sin (2 * \<theta>) * cos ((2 * real k + 1) * (2 * \<theta>))) = sin (4 * real M * \<theta>)"
proof (induction M)
  case 0 show ?case by simp
next
  case (Suc M)
  have "2 * sin (2 * \<theta>) * cos ((2 * real M + 1) * (2 * \<theta>)) = sin (4 * real (Suc M) * \<theta>) - sin (4 * real M * \<theta>)"
  proof -
    have "sin (4 * real (Suc M) * \<theta>) - sin (4 * real M * \<theta>) =
          2 * sin ((4 * real (Suc M) * \<theta> - 4 * real M * \<theta>) / 2) * cos ((4 * real (Suc M) * \<theta> + 4 * real M * \<theta>) / 2)"
      by (rule sin_diff_sin)
    also have "(4 * real (Suc M) * \<theta> - 4 * real M * \<theta>) / 2 = 2 * \<theta>" by (simp add: algebra_simps)
    also have "(4 * real (Suc M) * \<theta> + 4 * real M * \<theta>) / 2 = (2 * real M + 1) * (2 * \<theta>)" by (simp add: algebra_simps)
    finally show ?thesis ..
  qed
  thus ?case using Suc.IH by simp
qed

theorem bhmt_average:
  fixes \<theta> :: real
  assumes M: "0 < M" and s: "sin (2 * \<theta>) \<noteq> 0"
  shows "(\<Sum>k<M. (sin ((2 * real k + 1) * \<theta>))\<^sup>2) / real M = 1 / 2 - sin (4 * real M * \<theta>) / (4 * real M * sin (2 * \<theta>))"
proof -
  have sq: "(sin y)\<^sup>2 = (1 - cos (2 * y)) / 2" for y :: real by (simp add: cos_double_sin)
  have "(\<Sum>k<M. (sin ((2 * real k + 1) * \<theta>))\<^sup>2) = (\<Sum>k<M. (1 - cos ((2 * real k + 1) * (2 * \<theta>))) / 2)"
    by (rule sum.cong[OF refl]) (simp add: sq algebra_simps)
  also have "\<dots> = real M / 2 - (\<Sum>k<M. cos ((2 * real k + 1) * (2 * \<theta>))) / 2"
    by (simp add: sum_divide_distrib[symmetric] sum_subtractf)
  also have "(\<Sum>k<M. cos ((2 * real k + 1) * (2 * \<theta>))) = sin (4 * real M * \<theta>) / (2 * sin (2 * \<theta>))"
  proof -
    have "2 * sin (2 * \<theta>) * (\<Sum>k<M. cos ((2 * real k + 1) * (2 * \<theta>))) = sin (4 * real M * \<theta>)"
      unfolding cos_telescope[symmetric] sum_distrib_left by simp
    thus ?thesis using s by (simp add: field_simps)
  qed
  finally show ?thesis using M s by (simp add: field_simps)
qed

corollary bhmt_quarter:
  fixes \<theta> :: real
  assumes M: "0 < M" and s0: "0 < sin (2 * \<theta>)" and big: "1 / sin (2 * \<theta>) \<le> real M"
  shows "1 / 4 \<le> (\<Sum>k<M. (sin ((2 * real k + 1) * \<theta>))\<^sup>2) / real M"
proof -
  have MR: "0 < real M" using M by simp
  have "sin (4 * real M * \<theta>) / (4 * real M * sin (2 * \<theta>)) \<le> 1 / (4 * real M * sin (2 * \<theta>))"
    using s0 MR by (intro divide_right_mono) simp_all
  also have "\<dots> \<le> 1 / 4"
  proof -
    have "1 \<le> real M * sin (2 * \<theta>)" using big s0 by (simp add: field_simps)
    thus ?thesis using s0 MR by (simp add: field_simps)
  qed
  moreover have sn: "sin (2 * \<theta>) \<noteq> 0" using s0 by simp
  ultimately show ?thesis unfolding bhmt_average[OF M sn] by linarith
qed

subsection \<open>The flag circuit with oracle calls\<close>

definition flag_stage :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "flag_stage N n G = ctrl_blocks N (n * 3) (\<lambda>k. 1\<^sub>m n \<Otimes> G k)"

definition flag_full_prog :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow> qcirc" where
  "flag_full_prog N n G Prep = QSeq (Gate Prep) (hhl_prog N (n * 3) (flag_stage N n G))"

lemma calls_flag_full_prog: "calls (flag_full_prog N n G Prep) = 2 * (N - 1)"
  by (simp add: flag_full_prog_def calls_hhl_prog)

lemma flag_stage_ok:
  assumes G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3 \<and> unitary (G k)"
  shows "flag_stage N n G \<in> carrier_mat (N * (n * 3)) (N * (n * 3))" "unitary (flag_stage N n G)"
proof -
  show "flag_stage N n G \<in> carrier_mat (N * (n * 3)) (N * (n * 3))" by (simp add: flag_stage_def)
  show "unitary (flag_stage N n G)" unfolding flag_stage_def
  proof (rule ctrl_blocks_unitary)
    fix k assume k: "k < N"
    show "1\<^sub>m n \<Otimes> G k \<in> carrier_mat (n * 3) (n * 3)" using G[OF k] by (intro carrier_matI) auto
    show "unitary (1\<^sub>m n \<Otimes> G k)" using G[OF k] by (simp add: tensor_mat_unitary_one_left)
  qed
qed

lemma gates_ok_flag_full_prog:
  assumes N0: "0 < N" and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3 \<and> unitary (G k)"
      and Prep: "Prep \<in> carrier_mat (N * (n * 3)) (N * (n * 3))" "unitary Prep"
  shows "gates_ok (N * (n * 3)) (flag_full_prog N n G Prep)"
  using gates_ok_pe_prog[OF N0, of "n * 3"] gates_ok_adj[OF gates_ok_pe_prog[OF N0, of "n * 3"]] flag_stage_ok[where G = G and n = n, OF G] Prep
  unfolding flag_full_prog_def hhl_prog_def by simp

lemma flag_full_exact:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and N0: "0 < N"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3 \<and> unitary (G k)"
      and Prep: "Prep \<in> carrier_mat (N * (n * 3)) (N * (n * 3))"
  shows "sem N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (flag_full_prog N n G Prep) = flag_circuit A t0 N 3 G * Prep"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have E0: "evolution A t0 \<in> carrier_mat n n" using A by (rule evolution_carrier)
  have E: "evolution A t0 \<Otimes> 1\<^sub>m 3 \<in> carrier_mat (n * 3) (n * 3)" using E0 by (intro carrier_matI) simp_all
  have EU: "unitary (evolution A t0 \<Otimes> 1\<^sub>m 3)" by (rule tensor_mat_unitary_one_right[OF evolution_unitary[OF A]])
  have "sem N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (hhl_prog N (n * 3) (flag_stage N n G)) = flag_circuit A t0 N 3 G"
  proof -
    have "sem N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (hhl_prog N (n * 3) (flag_stage N n G))
          = (pe_unitary N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3))\<^sup>\<dagger> * (flag_stage N n G * pe_unitary N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3))"
      by (rule sem_hhl_prog[OF E EU N0 flag_stage_ok(1)[where G = G and n = n, OF G]])
    thus ?thesis unfolding flag_circuit_def hhl_Wd_def nA flag_stage_def .
  qed
  thus ?thesis unfolding flag_full_prog_def by simp
qed

subsection \<open>Run time in the paper's normalisation\<close>

text \<open>The paper assumes the spectrum in $[1/\kappa,1]$.  With total evolution time
$t=Nt_0\ge c\,\kappa/\varepsilon$, $c=12\pi^2\sqrt{4+2\pi^2}$, the state post-selected on
$\ket{\mathrm{well}}$ is within $\varepsilon$ of $\psi\otimes A^{-1}b/\norm{A^{-1}b}\otimes\ket{\mathrm{well}}$, the
success amplitude is at least $1/(4\kappa)$, and amplification needs at most $\pi\kappa$ rounds, each
using $2(N-1)$ oracle calls and $\mathit{Prep}$ twice: $O(\kappa)$ uses of the state preparation and
total evolution time $(2k+1)\cdot2(N-1)t_0\le(2\pi\kappa+1)\,2t=O(\kappa^2/\varepsilon)$.\<close>

theorem hhl_paper_runtime:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and k1: "1 \<le> \<kappa>"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> 1 / \<kappa> \<le> l \<and> l \<le> 1"
      and t0: "0 < t0" "t0 \<le> pi / 2" and N: "2 \<le> N"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3 \<and> unitary (G k)"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1"
      and Prep: "Prep \<in> carrier_mat (N * (n * 3)) (N * (n * 3))" "unitary Prep"
        "Prep *\<^sub>v unit_vec (N * (n * 3)) 0 = tensor_vec (win_state N) (tensor_vec b (unit_vec 3 0))"
      and e: "0 < \<epsilon>" "\<epsilon> * \<kappa> \<le> 1"
      and big: "12 * pi\<^sup>2 * sqrt (4 + 2 * pi\<^sup>2) * \<kappa> / \<epsilon> \<le> real N * t0"
  defines "out \<equiv> sem N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (flag_full_prog N n G Prep) *\<^sub>v unit_vec (N * (n * 3)) 0"
  defines "y \<equiv> pflag 3 (\<lambda>c. c = 1) out" and "x \<equiv> herm_inv A *\<^sub>v b"
  shows "\<parallel>complex_of_real (1 / \<parallel>y\<parallel>) \<cdot>\<^sub>v y - tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x) (unit_vec 3 1))\<parallel> \<le> \<epsilon>"
    and "1 / (4 * \<kappa>) \<le> \<parallel>y\<parallel>"
    and "\<parallel>y\<parallel> < 1 \<Longrightarrow> \<exists>k.
           1 - \<parallel>y\<parallel>\<^sup>2 \<le> \<parallel>pflag 3 (\<lambda>c. c = 1) (sem N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (aa_prog (N * (n * 3)) 3 (\<lambda>c. c = 1) (flag_full_prog N n G Prep) k) *\<^sub>v unit_vec (N * (n * 3)) 0)\<parallel>\<^sup>2
         \<and> calls (aa_prog (N * (n * 3)) 3 (\<lambda>c. c = 1) (flag_full_prog N n G Prep) k) = (2 * k + 1) * (2 * (N - 1))
         \<and> real k \<le> pi * \<kappa>"
proof -
  let ?\<psi> = "win_state N" and ?K = "N * (n * 3)"
  let ?C = "flag_circuit A t0 N 3 G" and ?I = "flag_idl n \<kappa> A (win_state N)"
  let ?bx = "tensor_vec ?\<psi> (tensor_vec b (unit_vec 3 0))"
  let ?c = "12 * pi\<^sup>2 * sqrt (4 + 2 * pi\<^sup>2)"
  have N0: "0 < N" using N by simp
  have NR: "0 < real N" using N by simp
  have k0: "0 < \<kappa>" using k1 by simp
  have nA: "dim_row A = n" using A(1) by simp
  have d3: "0 < (3::nat)" by simp
  have Gc: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3" using G by blast
  have spec': "\<bar>t0 * l\<bar> \<le> pi / 2" if "l \<in> herm_spectrum A" for l
  proof -
    have l: "1 / \<kappa> \<le> l" "l \<le> 1" using spec[OF that] by simp_all
    have l0: "0 < l" using l(1) k0 by (smt (verit) divide_pos_pos)
    have "t0 * l \<le> pi / 2 * 1" using t0 l l0 by (intro mult_mono) simp_all
    thus ?thesis using t0 l0 by simp
  qed
  have Cc: "?C \<in> carrier_mat ?K ?K"
    unfolding flag_circuit_def hhl_Wd_def nA
    by (rule mult_carrier_mat[OF dagger_carrier[OF pe_unitary_carrier] mult_carrier_mat[OF ctrl_blocks_carrier pe_unitary_carrier]])
  have outC: "out = ?C *\<^sub>v ?bx"
  proof -
    have e0: "unit_vec ?K 0 \<in> carrier_vec ?K" by (rule carrier_vecI) simp
    have h: "sem N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (flag_full_prog N n G Prep) = ?C * Prep"
      by (rule flag_full_exact[OF A N0 G Prep(1)])
    show ?thesis unfolding out_def h using assoc_mult_mat_vec[OF Cc Prep(1) e0] Prep(3) by simp
  qed
  have wc': "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> 1 / \<kappa> \<le> l" using spec by blast
  have H2: "flag_H \<kappa> A 2 = 0\<^sub>m n n" by (rule flag_H_well_conditioned(1)[OF A k0]) (rule wc')
  have H1: "flag_H \<kappa> A 1 = complex_of_real (1 / (2 * \<kappa>)) \<cdot>\<^sub>m herm_inv A" by (rule flag_H_well_conditioned(2)[OF A k0]) (rule wc')
  have Hi: "herm_inv A \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
  have dx: "dim_vec x = n" unfolding x_def using Hi by simp
  have ill: "flag_H \<kappa> A 2 *\<^sub>v b = 0\<^sub>v n" unfolding H2 using b(1) by (intro eq_vecI) (simp_all add: scalar_prod_def)
  have H1b: "flag_H \<kappa> A 1 *\<^sub>v b = complex_of_real (1 / (2 * \<kappa>)) \<cdot>\<^sub>v x"
    unfolding H1 x_def by (rule smult_mat_mult_vec[OF Hi carrier_vecI[OF b(1)]])
  have xge: "1 \<le> \<parallel>x\<parallel>"
  proof -
    have sp: "1 / \<kappa> \<le> \<bar>l\<bar> \<and> \<bar>l\<bar> \<le> 1" if "l \<in> herm_spectrum A" for l
      using spec[OF that] k0 by (auto simp: abs_if) (smt (verit) divide_pos_pos)+
    have "(1 / \<kappa> / 1)\<^sup>2 * Re \<langle>b|b\<rangle> \<le> (1 / \<kappa>)\<^sup>2 * Re \<langle>x|x\<rangle>"
      unfolding x_def by (rule hhl_success_bound[OF A _ sp b(1)]) (use k0 in simp)
    hence "(1 / \<kappa>)\<^sup>2 * 1 \<le> (1 / \<kappa>)\<^sup>2 * \<parallel>x\<parallel>\<^sup>2" unfolding vnorm_Re_inner b(2) by simp
    hence "1 \<le> \<parallel>x\<parallel>\<^sup>2" using k0 by (simp add: mult_le_cancel_left_pos)
    thus ?thesis using vnorm_ge0[of x] by (smt (verit) power2_le_imp_le one_power2)
  qed
  have x0: "\<parallel>x\<parallel> \<noteq> 0" using xge by simp
  have xn0: "x \<noteq> 0\<^sub>v n" using x0 by (auto simp: cpx_vec_length_def)
  have well: "flag_H \<kappa> A 1 *\<^sub>v b \<noteq> 0\<^sub>v n"
  proof
    assume "flag_H \<kappa> A 1 *\<^sub>v b = 0\<^sub>v n"
    hence "\<parallel>complex_of_real (1 / (2 * \<kappa>)) \<cdot>\<^sub>v x\<parallel> = 0" unfolding H1b by (simp add: cpx_vec_length_def)
    thus False unfolding cpx_vec_length_smult using k0 x0 by simp
  qed
  define \<rho> where "\<rho> = 6 * pi\<^sup>2 * sqrt (4 + 2 * pi\<^sup>2) * \<kappa> / (real N * t0)"
  have \<rho>e: "2 * \<rho> \<le> \<epsilon>"
  proof -
    have "?c * \<kappa> \<le> \<epsilon> * (real N * t0)" using big e(1) by (simp add: divide_le_eq mult.commute)
    hence "?c * \<kappa> / (real N * t0) \<le> \<epsilon>" using NR t0 by (simp add: divide_le_eq)
    thus ?thesis unfolding \<rho>_def by (simp add: field_simps)
  qed
  have e1: "\<epsilon> \<le> 1"
  proof -
    have "\<epsilon> * 1 \<le> \<epsilon> * \<kappa>" using e(1) k1 by (intro mult_left_mono) simp_all
    thus ?thesis using e(2) by simp
  qed
  have \<rho>1: "\<rho> < 1" using \<rho>e e1 by linarith
  note fw = flag_well_normalized[where G = G, OF A n0 t0(1) N k0 spec' Gc Gh b(1) ill well \<rho>1[unfolded \<rho>_def], folded \<rho>_def]
  let ?X = "tensor_vec ?\<psi> (tensor_vec (flag_H \<kappa> A 1 *\<^sub>v b) (unit_vec 3 1))"
  let ?Xn = "tensor_vec ?\<psi> (tensor_vec (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x) (unit_vec 3 1))"
  have yC: "y = pflag 3 (\<lambda>c. c = 1) (?C *\<^sub>v ?bx)" unfolding y_def outC ..
  have Xn: "complex_of_real (1 / \<parallel>?X\<parallel>) \<cdot>\<^sub>v ?X = ?Xn"
  proof -
    have x1: "dim_vec (tensor_vec x (unit_vec 3 1)) = n * 3" by (rule tensor_vec_dim[OF dx]) simp
    have sl: "tensor_vec (z \<cdot>\<^sub>v x) (unit_vec 3 1) = z \<cdot>\<^sub>v tensor_vec x (unit_vec 3 1)" for z by (rule tensor_vec_smult_left[OF dx]) simp
    have sr: "tensor_vec ?\<psi> (z \<cdot>\<^sub>v tensor_vec x (unit_vec 3 1)) = z \<cdot>\<^sub>v tensor_vec ?\<psi> (tensor_vec x (unit_vec 3 1))" for z
      by (rule tensor_vec_smult_right[OF dim_win_state x1])
    have nX0: "\<parallel>tensor_vec ?\<psi> (tensor_vec x (unit_vec 3 1))\<parallel> = \<parallel>x\<parallel>"
    proof -
      have t1: "\<parallel>tensor_vec x (unit_vec 3 1)\<parallel> = \<parallel>x\<parallel>" using vnorm_tensor[OF dx, where b = "unit_vec 3 1" and m = 3] by simp
      show ?thesis unfolding vnorm_tensor[OF dim_win_state x1] t1 win_state_norm[OF N] by simp
    qed
    have "?X = complex_of_real (1 / (2 * \<kappa>)) \<cdot>\<^sub>v tensor_vec ?\<psi> (tensor_vec x (unit_vec 3 1))" unfolding H1b sl sr ..
    hence "complex_of_real (1 / \<parallel>?X\<parallel>) \<cdot>\<^sub>v ?X = complex_of_real (1 / \<parallel>tensor_vec ?\<psi> (tensor_vec x (unit_vec 3 1))\<parallel>) \<cdot>\<^sub>v tensor_vec ?\<psi> (tensor_vec x (unit_vec 3 1))"
      using normalize_smult_pos[of "1 / (2 * \<kappa>)" "tensor_vec ?\<psi> (tensor_vec x (unit_vec 3 1))"] k0 nX0 x0 by simp
    also have "\<dots> = ?Xn" unfolding nX0 sl sr ..
    finally show ?thesis .
  qed
  show "\<parallel>complex_of_real (1 / \<parallel>y\<parallel>) \<cdot>\<^sub>v y - ?Xn\<parallel> \<le> \<epsilon>" using fw \<rho>e unfolding yC Xn[symmetric] by linarith
  have dX: "dim_vec (flag_H \<kappa> A 1 *\<^sub>v b) = n" using carrier_matD(1)[OF flag_H_carrier[OF A, of \<kappa> 1]] by simp
  have nX: "\<parallel>?X\<parallel> = \<parallel>x\<parallel> / (2 * \<kappa>)"
  proof -
    have x1: "dim_vec (tensor_vec (flag_H \<kappa> A 1 *\<^sub>v b) (unit_vec 3 1)) = n * 3" by (rule tensor_vec_dim[OF dX]) simp
    have t1: "\<parallel>tensor_vec (flag_H \<kappa> A 1 *\<^sub>v b) (unit_vec 3 1)\<parallel> = \<parallel>flag_H \<kappa> A 1 *\<^sub>v b\<parallel>"
      using vnorm_tensor[OF dX, where b = "unit_vec 3 1" and m = 3] by simp
    have "\<parallel>?X\<parallel> = \<parallel>flag_H \<kappa> A 1 *\<^sub>v b\<parallel>" unfolding vnorm_tensor[OF dim_win_state x1] t1 win_state_norm[OF N] by simp
    also have "\<dots> = \<parallel>x\<parallel> / (2 * \<kappa>)" unfolding H1b cpx_vec_length_smult norm_of_real using k0 by simp
    finally show ?thesis .
  qed
  have PX: "pflag 3 (\<lambda>c. c = 1) (?I *\<^sub>v b) = ?X"
    unfolding flag_idl_def by (rule lift_post(1)[where H = "flag_H \<kappa> A", OF flag_H_carrier[OF A] b(1) dim_win_state])
  have dCb: "dim_vec (?C *\<^sub>v ?bx) = ?K" using Cc by simp
  have dIb: "dim_vec (?I *\<^sub>v b) = ?K" using carrier_matD(1)[OF lift_carrier[of 3 n ?\<psi> "flag_H \<kappa> A"]] by (simp add: flag_idl_def)
  have errb: "\<parallel>?C *\<^sub>v ?bx - ?I *\<^sub>v b\<parallel> \<le> \<rho> / 2"
  proof (rule power2_le_imp_le)
    have "\<parallel>?C *\<^sub>v ?bx - ?I *\<^sub>v b\<parallel>\<^sup>2 \<le> 9 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2) * \<parallel>b\<parallel>\<^sup>2"
      by (rule flag_bound[where G = G, OF A n0 t0(1) N k0 spec' Gc Gh b(1)])
    also have "\<dots> = (\<rho> / 2)\<^sup>2" unfolding b(2) \<rho>_def using NR t0
      by (simp add: power_mult_distrib power_divide field_simps power2_eq_square power4_eq_xxxx)
    finally show "\<parallel>?C *\<^sub>v ?bx - ?I *\<^sub>v b\<parallel>\<^sup>2 \<le> (\<rho> / 2)\<^sup>2" .
    show "0 \<le> \<rho> / 2" unfolding \<rho>_def using k0 NR t0 by simp
  qed
  have yX: "\<parallel>y - ?X\<parallel> \<le> \<rho> / 2"
  proof -
    have "y - ?X = pflag 3 (\<lambda>c. c = 1) (?C *\<^sub>v ?bx - ?I *\<^sub>v b)" unfolding yC PX[symmetric]
      by (rule pflag_minus[symmetric]) (simp only: dCb dIb)
    hence "\<parallel>y - ?X\<parallel> = \<parallel>pflag 3 (\<lambda>c. c = 1) (?C *\<^sub>v ?bx - ?I *\<^sub>v b)\<parallel>" by (rule arg_cong)
    also have "\<dots> \<le> \<parallel>?C *\<^sub>v ?bx - ?I *\<^sub>v b\<parallel>" by (rule vnorm_pflag_le)
    finally show ?thesis using errb by (rule order_trans)
  qed
  have dyX: "dim_vec y = dim_vec ?X" unfolding yC PX[symmetric] using dCb dIb by simp
  show ylo: "1 / (4 * \<kappa>) \<le> \<parallel>y\<parallel>"
  proof -
    have "\<parallel>?X\<parallel> - \<parallel>y\<parallel> \<le> \<parallel>y - ?X\<parallel>" using vnorm_reverse[OF dyX] by (simp add: abs_le_iff)
    moreover have "1 / (2 * \<kappa>) \<le> \<parallel>?X\<parallel>" unfolding nX using xge k0 by (simp add: divide_right_mono)
    moreover have "\<rho> / 2 \<le> 1 / (4 * \<kappa>)"
    proof -
      have "\<rho> / 2 \<le> \<epsilon> / 4" using \<rho>e by simp
      also have "\<epsilon> / 4 \<le> 1 / (4 * \<kappa>)" using e k0 by (simp add: field_simps)
      finally show ?thesis .
    qed
    moreover have "1 / (2 * \<kappa>) - 1 / (4 * \<kappa>) = 1 / (4 * \<kappa>)" using k0 by (simp add: field_simps)
    ultimately show ?thesis using yX by linarith
  qed
  assume y1: "\<parallel>y\<parallel> < 1"
  have y0: "0 < \<parallel>y\<parallel>" using ylo k0 by (smt (verit) divide_pos_pos)
  have O: "evolution A t0 \<Otimes> 1\<^sub>m 3 \<in> carrier_mat (n * 3) (n * 3)" "unitary (evolution A t0 \<Otimes> 1\<^sub>m 3)"
  proof -
    have E0: "evolution A t0 \<in> carrier_mat n n" using A by (rule evolution_carrier)
    show "evolution A t0 \<Otimes> 1\<^sub>m 3 \<in> carrier_mat (n * 3) (n * 3)" using E0 by (intro carrier_matI) simp_all
    show "unitary (evolution A t0 \<Otimes> 1\<^sub>m 3)" by (rule tensor_mat_unitary_one_right[OF evolution_unitary[OF A]])
  qed
  have gk: "gates_ok ?K (flag_full_prog N n G Prep)" by (rule gates_ok_flag_full_prog[where G = G, OF N0 G Prep(1,2)])
  have K0: "0 < ?K" using N0 n0 by simp
  obtain k where k1: "1 - \<parallel>pflag 3 (\<lambda>c. c = 1) out\<parallel>\<^sup>2 \<le> \<parallel>pflag 3 (\<lambda>c. c = 1) (sem N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (aa_prog ?K 3 (\<lambda>c. c = 1) (flag_full_prog N n G Prep) k) *\<^sub>v unit_vec ?K 0)\<parallel>\<^sup>2"
      and k3: "calls (aa_prog ?K 3 (\<lambda>c. c = 1) (flag_full_prog N n G Prep) k) = (2 * k + 1) * calls (flag_full_prog N n G Prep)"
      and k4: "real k \<le> pi / (4 * \<parallel>pflag 3 (\<lambda>c. c = 1) out\<parallel>)"
    using circuit_amplification[OF O gk K0, of 3 "\<lambda>c. c = 1", folded out_def] y0 y1 unfolding y_def by blast
  have "pi / (4 * \<parallel>y\<parallel>) \<le> pi / (4 * (1 / (4 * \<kappa>)))" using ylo k0 y0 by (intro divide_left_mono) simp_all
  also have "\<dots> = pi * \<kappa>" using k0 by simp
  finally have "real k \<le> pi * \<kappa>" using k4 unfolding y_def by linarith
  thus "\<exists>k. 1 - \<parallel>y\<parallel>\<^sup>2 \<le> \<parallel>pflag 3 (\<lambda>c. c = 1) (sem N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (aa_prog (N * (n * 3)) 3 (\<lambda>c. c = 1) (flag_full_prog N n G Prep) k) *\<^sub>v unit_vec (N * (n * 3)) 0)\<parallel>\<^sup>2
         \<and> calls (aa_prog (N * (n * 3)) 3 (\<lambda>c. c = 1) (flag_full_prog N n G Prep) k) = (2 * k + 1) * (2 * (N - 1))
         \<and> real k \<le> pi * \<kappa>"
    using k1 k3[unfolded calls_flag_full_prog] unfolding y_def by (intro exI[of _ k] conjI)
qed

end
