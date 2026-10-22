theory HHL_Window
  imports HHL_Approximate
begin

section \<open>HHL with a sine-window phase register\<close>

text \<open>With the uniform register state the error of approximate phase estimation is
$O(1/\sqrt N)$, so precision $\varepsilon$ needs $N\sim1/\varepsilon^2$.  Preparing the register
in the window state $\psi_\tau=\sqrt{2/N}\,\sin(\pi(\tau+\frac12)/N)$ makes the amplitudes decay
like $1/(N\delta)^2$ instead of $1/(N\delta)$, and the error drops to $O(1/N)$: a register of size
$N\sim1/\varepsilon$ suffices (theorem \<open>hhl_window_precision\<close>).\<close>

subsection \<open>The window amplitude\<close>

lemma cis_minus_cis_neg: "cis t - cis (- t) = 2 * \<i> * complex_of_real (sin t)"
  by (simp add: complex_eq_iff)

lemma of_real_sin_cis: "complex_of_real (sin t) = (cis t - cis (- t)) / (2 * \<i>)"
  unfolding cis_minus_cis_neg by simp

text \<open>The window sum: with $a=\pi/N$,
$\bigl|\sum_{\tau<N}\sin(a\tau+a/2)\,e^{i\tau x}\bigr|\le|\sin(a/2)|/(|\sin\frac{x+a}2|\,|\sin\frac{x-a}2|)$.\<close>

lemma window_sum_bound:
  fixes x a :: real and N :: nat
  assumes Na: "real N * a = pi" and p1: "cis (x + a) \<noteq> 1" and q1: "cis (x - a) \<noteq> 1"
  shows "cmod (\<Sum>\<tau><N. complex_of_real (sin (a * real \<tau> + a / 2)) * cis (real \<tau> * x))
         \<le> \<bar>sin (a / 2)\<bar> / (\<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar>)"
proof -
  define p q where "p = cis (x + a)" and "q = cis (x - a)"
  have tm: "complex_of_real (sin (a * real \<tau> + a / 2)) * cis (real \<tau> * x)
              = (cis (a / 2) * p ^ \<tau> - cis (- (a / 2)) * q ^ \<tau>) / (2 * \<i>)" for \<tau>
  proof -
    have "complex_of_real (sin (a * real \<tau> + a / 2)) * cis (real \<tau> * x)
          = (cis (a * real \<tau> + a / 2) * cis (real \<tau> * x) - cis (- (a * real \<tau> + a / 2)) * cis (real \<tau> * x)) / (2 * \<i>)"
      unfolding of_real_sin_cis by (simp add: field_simps)
    also have "cis (a * real \<tau> + a / 2) * cis (real \<tau> * x) = cis (a / 2) * p ^ \<tau>"
      unfolding p_def DeMoivre cis_mult by (simp add: algebra_simps)
    also have "cis (- (a * real \<tau> + a / 2)) * cis (real \<tau> * x) = cis (- (a / 2)) * q ^ \<tau>"
      unfolding q_def DeMoivre cis_mult by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have pN: "p ^ N = - cis (real N * x)"
    unfolding p_def DeMoivre using Na by (simp add: distrib_left minus_cis[symmetric])
  have qN: "q ^ N = - cis (real N * x)"
    unfolding q_def DeMoivre using Na by (simp add: right_diff_distrib minus_cis'[symmetric])
  have Sp: "(\<Sum>\<tau><N. p ^ \<tau>) = (p ^ N - 1) / (p - 1)" using geometric_sum[of p N] p1 by (simp add: p_def)
  have Sq: "(\<Sum>\<tau><N. q ^ \<tau>) = (q ^ N - 1) / (q - 1)" using geometric_sum[of q N] q1 by (simp add: q_def)
  have p1': "p - 1 \<noteq> 0" and q1': "q - 1 \<noteq> 0" using p1 q1 by (simp_all add: p_def q_def)
  have num: "cis (a / 2) * (q - 1) - cis (- (a / 2)) * (p - 1) = (cis x + 1) * (cis (- (a / 2)) - cis (a / 2))"
  proof -
    have "cis (a / 2) * q = cis (x - a / 2)" unfolding q_def cis_mult by (simp add: algebra_simps)
    moreover have "cis (- (a / 2)) * p = cis (x + a / 2)" unfolding p_def cis_mult by (simp add: algebra_simps)
    moreover have "cis x * cis (- (a / 2)) = cis (x - a / 2)" unfolding cis_mult by simp
    moreover have "cis x * cis (a / 2) = cis (x + a / 2)" unfolding cis_mult by simp
    ultimately show ?thesis by (simp add: algebra_simps)
  qed
  have Sigma: "(\<Sum>\<tau><N. complex_of_real (sin (a * real \<tau> + a / 2)) * cis (real \<tau> * x))
        = - (cis (real N * x) + 1) / (2 * \<i>) * ((cis x + 1) * (cis (- (a / 2)) - cis (a / 2))) / ((p - 1) * (q - 1))"
  proof -
    have "(\<Sum>\<tau><N. complex_of_real (sin (a * real \<tau> + a / 2)) * cis (real \<tau> * x))
          = (cis (a / 2) * (\<Sum>\<tau><N. p ^ \<tau>) - cis (- (a / 2)) * (\<Sum>\<tau><N. q ^ \<tau>)) / (2 * \<i>)"
      unfolding tm by (simp only: sum_divide_distrib[symmetric] sum_subtractf sum_distrib_left[symmetric])
    also have "\<dots> = - (cis (real N * x) + 1) / (2 * \<i>) * (cis (a / 2) * (q - 1) - cis (- (a / 2)) * (p - 1)) / ((p - 1) * (q - 1))"
      unfolding Sp Sq pN qN using p1' q1' by (simp add: field_simps)
    finally show ?thesis unfolding num .
  qed
  have c1: "cmod (cis (real N * x) + 1) \<le> 2" using norm_triangle_ineq[of "cis (real N * x)" 1] by simp
  have c2: "cmod (cis x + 1) \<le> 2" using norm_triangle_ineq[of "cis x" 1] by simp
  have c3: "cmod (cis (- (a / 2)) - cis (a / 2)) = 2 * \<bar>sin (a / 2)\<bar>"
  proof -
    have ca: "cis a * cis (- (a / 2)) = cis (a / 2)" using cis_mult[of a "- (a / 2)"] by simp
    have "cis (- (a / 2)) - cis (a / 2) = cis (- (a / 2)) * (1 - cis a)" by (simp add: algebra_simps ca)
    hence "cmod (cis (- (a / 2)) - cis (a / 2)) = cmod (cis a - 1)" by (simp add: norm_mult norm_minus_commute)
    thus ?thesis unfolding cmod_cis_minus_one .
  qed
  have dp: "cmod (p - 1) = 2 * \<bar>sin ((x + a) / 2)\<bar>" unfolding p_def cmod_cis_minus_one ..
  have dq: "cmod (q - 1) = 2 * \<bar>sin ((x - a) / 2)\<bar>" unfolding q_def cmod_cis_minus_one ..
  have sp: "0 < \<bar>sin ((x + a) / 2)\<bar>"
  proof -
    have "0 < cmod (p - 1)" using p1' by simp
    thus ?thesis using dp by simp
  qed
  have sq: "0 < \<bar>sin ((x - a) / 2)\<bar>"
  proof -
    have "0 < cmod (q - 1)" using q1' by simp
    thus ?thesis using dq by simp
  qed
  have "cmod (\<Sum>\<tau><N. complex_of_real (sin (a * real \<tau> + a / 2)) * cis (real \<tau> * x))
        = cmod (cis (real N * x) + 1) / 2 * (cmod (cis x + 1) * (2 * \<bar>sin (a / 2)\<bar>)) / (2 * \<bar>sin ((x + a) / 2)\<bar> * (2 * \<bar>sin ((x - a) / 2)\<bar>))"
  proof -
    have "cmod (- (cis (real N * x) + 1) / (2 * \<i>) * ((cis x + 1) * (cis (- (a / 2)) - cis (a / 2))) / ((p - 1) * (q - 1)))
          = cmod (cis (real N * x) + 1) / cmod (2 * \<i>) * (cmod (cis x + 1) * cmod (cis (- (a / 2)) - cis (a / 2))) / (cmod (p - 1) * cmod (q - 1))"
      by (simp only: norm_mult norm_divide norm_minus_cancel)
    also have "cmod (2 * \<i>) = 2" by (simp add: norm_mult)
    finally show ?thesis unfolding Sigma c3 dp dq .
  qed
  also have "\<dots> \<le> 2 / 2 * (2 * (2 * \<bar>sin (a / 2)\<bar>)) / (2 * \<bar>sin ((x + a) / 2)\<bar> * (2 * \<bar>sin ((x - a) / 2)\<bar>))"
    by (intro divide_right_mono mult_mono c1 c2 divide_right_mono) (use sp sq in simp_all)
  also have "\<dots> = \<bar>sin (a / 2)\<bar> / (\<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar>)" by simp
  finally show ?thesis .
qed

lemma sin_ge_min:
  assumes "0 \<le> y" "y \<le> pi"
  shows "2 / pi * min y (pi - y) \<le> sin y"
proof (cases "y \<le> pi / 2")
  case True
  thus ?thesis using jordan_inequality[of y] assms by (simp add: min_def)
next
  case False
  have "2 / pi * (pi - y) \<le> sin (pi - y)" by (rule jordan_inequality) (use False assms in simp_all)
  thus ?thesis using False by (simp add: min_def)
qed

lemma window_denominator:
  fixes x a :: real
  assumes a0: "0 < a" and a2: "a \<le> pi / 2" and xlo: "2 * a \<le> \<bar>x\<bar>" and xhi: "\<bar>x\<bar> \<le> pi"
  shows "x\<^sup>2 / (4 * pi\<^sup>2) \<le> \<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar>"
proof -
  define y where "y = \<bar>x\<bar>"
  have y: "2 * a \<le> y" "y \<le> pi" using xlo xhi by (simp_all add: y_def)
  have prod: "\<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar> = \<bar>sin ((y + a) / 2)\<bar> * \<bar>sin ((y - a) / 2)\<bar>"
  proof (cases "0 \<le> x")
    case True thus ?thesis by (simp add: y_def)
  next
    case False
    have yx: "y = - x" using False by (simp add: y_def)
    have e1: "(x + a) / 2 = - ((y - a) / 2)" unfolding yx by (simp add: field_simps)
    have e2: "(x - a) / 2 = - ((y + a) / 2)" unfolding yx by (simp add: field_simps)
    show ?thesis unfolding e1 e2 sin_minus abs_minus_cancel by (simp only: mult.commute)
  qed
  have s1: "y / (2 * pi) \<le> sin ((y + a) / 2)"
  proof -
    have r: "0 \<le> (y + a) / 2" "(y + a) / 2 \<le> pi" using y a0 a2 by simp_all
    have m1: "y / 4 \<le> (y + a) / 2" using y a0 by (auto simp: field_simps)
    have m2: "y / 4 \<le> pi - (y + a) / 2" using y a2 by (auto simp: field_simps)
    have m: "y / 4 \<le> min ((y + a) / 2) (pi - (y + a) / 2)" using m1 m2 by simp
    have "2 / pi * (y / 4) \<le> 2 / pi * min ((y + a) / 2) (pi - (y + a) / 2)"
      by (rule mult_left_mono[OF m]) simp
    also have "\<dots> \<le> sin ((y + a) / 2)" by (rule sin_ge_min[OF r])
    finally show ?thesis by simp
  qed
  have s2: "y / (2 * pi) \<le> sin ((y - a) / 2)"
  proof -
    have r: "0 \<le> (y - a) / 2" "(y - a) / 2 \<le> pi / 2" using y a0 by simp_all
    have "2 / pi * (y / 4) \<le> 2 / pi * ((y - a) / 2)" using y by (intro mult_left_mono) simp_all
    also have "\<dots> \<le> sin ((y - a) / 2)" by (rule jordan_inequality[OF r])
    finally show ?thesis by simp
  qed
  have y0: "0 \<le> y / (2 * pi)" using y a0 by simp
  have "(y / (2 * pi)) * (y / (2 * pi)) \<le> sin ((y + a) / 2) * sin ((y - a) / 2)"
    by (rule mult_mono[OF s1 s2 _ y0]) (use s1 y0 in linarith)
  moreover have "0 \<le> sin ((y + a) / 2)" "0 \<le> sin ((y - a) / 2)" using s1 s2 y0 by linarith+
  ultimately have "(y / (2 * pi)) * (y / (2 * pi)) \<le> \<bar>sin ((y + a) / 2)\<bar> * \<bar>sin ((y - a) / 2)\<bar>" by simp
  moreover have "(y / (2 * pi)) * (y / (2 * pi)) = x\<^sup>2 / (4 * pi\<^sup>2)" by (simp add: y_def power2_eq_square)
  ultimately show ?thesis unfolding prod by simp
qed

lemma cis_ne_one_of_sin: "sin (y / 2) \<noteq> 0 \<Longrightarrow> cis y \<noteq> 1"
  using cmod_cis_minus_one[of y] by auto

text \<open>The window amplitude bound: for $N\ge2$ and $2\pi/N\le|x|\le\pi$,
$\bigl|\frac{\sqrt2}N\sum_{\tau<N}\sin\frac{\pi(\tau+1/2)}N e^{i\tau x}\bigr|\le\frac{2\sqrt2\,\pi^3}{N^2x^2}$.\<close>

theorem window_amp_bound:
  fixes x :: real and N :: nat
  assumes N: "2 \<le> N" and xlo: "2 * pi / real N \<le> \<bar>x\<bar>" and xhi: "\<bar>x\<bar> \<le> pi"
  shows "cmod (complex_of_real (sqrt 2 / real N) * (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * x)))
         \<le> 2 * sqrt 2 * pi ^ 3 / ((real N)\<^sup>2 * x\<^sup>2)"
proof -
  define a where "a = pi / real N"
  have N0: "0 < real N" using N by simp
  have a0: "0 < a" and a2: "a \<le> pi / 2" using N by (simp_all add: a_def field_simps)
  have Na: "real N * a = pi" using N0 by (simp add: a_def)
  have x2a: "2 * a \<le> \<bar>x\<bar>" using xlo by (simp add: a_def)
  have den: "x\<^sup>2 / (4 * pi\<^sup>2) \<le> \<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar>" by (rule window_denominator[OF a0 a2 x2a xhi])
  have x0: "0 < x\<^sup>2" using x2a a0 by simp
  have dpos: "0 < x\<^sup>2 / (4 * pi\<^sup>2)" using x0 by simp
  have sp: "sin ((x + a) / 2) \<noteq> 0" and sm: "sin ((x - a) / 2) \<noteq> 0" using den dpos by auto
  have arg: "a * real \<tau> + a / 2 = pi * (real \<tau> + 1 / 2) / real N" for \<tau> using N0 by (simp add: a_def field_simps)
  have S: "cmod (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * x))
           \<le> \<bar>sin (a / 2)\<bar> / (\<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar>)"
    using window_sum_bound[OF Na cis_ne_one_of_sin[OF sp] cis_ne_one_of_sin[OF sm]] unfolding arg .
  have "\<bar>sin (a / 2)\<bar> / (\<bar>sin ((x + a) / 2)\<bar> * \<bar>sin ((x - a) / 2)\<bar>) \<le> (a / 2) / (x\<^sup>2 / (4 * pi\<^sup>2))"
  proof (rule frac_le)
    show "0 \<le> a / 2" using a0 by simp
    show "\<bar>sin (a / 2)\<bar> \<le> a / 2" using abs_sin_x_le_abs_x[of "a / 2"] a0 by simp
    show "0 < x\<^sup>2 / (4 * pi\<^sup>2)" by (rule dpos)
  qed (rule den)
  also have "(a / 2) / (x\<^sup>2 / (4 * pi\<^sup>2)) = 2 * pi ^ 3 / (real N * x\<^sup>2)" using N0 x0 by (simp add: a_def field_simps power3_eq_cube power2_eq_square)
  finally have S': "cmod (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * x)) \<le> 2 * pi ^ 3 / (real N * x\<^sup>2)"
    using S by linarith
  have "cmod (complex_of_real (sqrt 2 / real N) * (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * x)))
        = sqrt 2 / real N * cmod (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * x))"
    unfolding norm_mult norm_of_real using N0 by simp
  also have "\<dots> \<le> sqrt 2 / real N * (2 * pi ^ 3 / (real N * x\<^sup>2))" by (rule mult_left_mono[OF S']) (use N0 in simp)
  also have "\<dots> = 2 * sqrt 2 * pi ^ 3 / ((real N)\<^sup>2 * x\<^sup>2)" by (simp add: power2_eq_square mult_ac)
  finally show ?thesis .
qed

subsection \<open>The sine window\<close>

definition win_coef :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "win_coef N \<tau> = sqrt (2 / real N) * sin (pi * (real \<tau> + 1 / 2) / real N)"

definition win_state :: "nat \<Rightarrow> complex Matrix.vec" where
  "win_state N = Matrix.vec N (\<lambda>\<tau>. complex_of_real (win_coef N \<tau>))"

lemma dim_win_state [simp]: "dim_vec (win_state N) = N"
  by (simp add: win_state_def)

lemma win_amp_formula:
  assumes j: "j < N"
  shows "pe_amp_reg N (win_state N) \<phi> j =
         complex_of_real (sqrt 2 / real N) * (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * (2 * pi * (\<phi> - real j / real N))))"
proof -
  have N0: "0 < real N" using j by simp
  have c: "sqrt (2 / real N) / sqrt (real N) = sqrt 2 / real N"
    using N0 by (simp add: real_sqrt_divide field_simps)
  have "pe_amp_reg N (win_state N) \<phi> j
        = (\<Sum>\<tau><N. complex_of_real (sqrt (2 / real N)) * complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (2 * pi * real \<tau> * (\<phi> - real j / real N))) / complex_of_real (sqrt (real N))"
    unfolding pe_amp_reg_formula[OF j] by (rule arg_cong[where f = "\<lambda>x. x / _"], rule sum.cong) (simp_all add: win_state_def win_coef_def)
  also have "\<dots> = complex_of_real (sqrt (2 / real N) / sqrt (real N)) * (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * (2 * pi * (\<phi> - real j / real N))))"
    by (simp add: sum_distrib_left sum_divide_distrib mult_ac)
  finally show ?thesis unfolding c .
qed

text \<open>The quadratic decay: $|\alpha_j|^2\le\pi^2/(2N^4\delta^4)$ for $1/N\le|\delta|\le1/2$, $\delta=\varphi-j/N$.\<close>

theorem win_amp_tail:
  assumes N: "2 \<le> N" and j: "j < N" and dlo: "1 / real N \<le> \<bar>\<phi> - real j / real N\<bar>" and dhi: "\<bar>\<phi> - real j / real N\<bar> \<le> 1 / 2"
  shows "(cmod (pe_amp_reg N (win_state N) \<phi> j))\<^sup>2 \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * (\<phi> - real j / real N) ^ 4)"
proof -
  define \<delta> where "\<delta> = \<phi> - real j / real N"
  have N0: "0 < real N" using N by simp
  have dlo': "1 / real N \<le> \<bar>\<delta>\<bar>" using dlo unfolding \<delta>_def .
  have "2 * pi * (1 / real N) \<le> 2 * pi * \<bar>\<delta>\<bar>" by (rule mult_left_mono[OF dlo']) simp
  hence xlo: "2 * pi / real N \<le> \<bar>2 * pi * \<delta>\<bar>" by (simp add: abs_mult)
  have xhi: "\<bar>2 * pi * \<delta>\<bar> \<le> pi" using dhi by (simp add: \<delta>_def abs_mult)
  have d0: "0 < \<delta>\<^sup>2" using dlo' N0 by (cases "\<delta> = 0") (simp_all add: field_simps)
  have "cmod (pe_amp_reg N (win_state N) \<phi> j) \<le> 2 * sqrt 2 * pi ^ 3 / ((real N)\<^sup>2 * (2 * pi * \<delta>)\<^sup>2)"
    unfolding win_amp_formula[OF j] \<delta>_def[symmetric] by (rule window_amp_bound[OF N xlo xhi])
  also have "\<dots> = sqrt 2 * pi / (2 * (real N)\<^sup>2 * \<delta>\<^sup>2)" by (simp add: power2_eq_square power3_eq_cube field_simps)
  finally have a: "cmod (pe_amp_reg N (win_state N) \<phi> j) \<le> sqrt 2 * pi / (2 * (real N)\<^sup>2 * \<delta>\<^sup>2)" .
  have "(cmod (pe_amp_reg N (win_state N) \<phi> j))\<^sup>2 \<le> (sqrt 2 * pi / (2 * (real N)\<^sup>2 * \<delta>\<^sup>2))\<^sup>2"
    by (rule power_mono[OF a]) simp
  also have "\<dots> = pi\<^sup>2 / (2 * (real N) ^ 4 * \<delta> ^ 4)" using d0 by (simp add: power_divide power_mult_distrib field_simps)
  finally show ?thesis unfolding \<delta>_def .
qed

lemma win_amp_crude:
  assumes j: "j < N"
  shows "(cmod (pe_amp_reg N (win_state N) \<phi> j))\<^sup>2 \<le> 2"
proof -
  have N0: "0 < real N" using j by simp
  have "cmod (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * (2 * pi * (\<phi> - real j / real N))))
        \<le> (\<Sum>\<tau><N. cmod (complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * (2 * pi * (\<phi> - real j / real N)))))"
    by (rule norm_sum)
  also have "\<dots> \<le> (\<Sum>\<tau><N. 1)" by (rule sum_mono) (simp add: norm_mult abs_sin_le_one)
  finally have s: "cmod (\<Sum>\<tau><N. complex_of_real (sin (pi * (real \<tau> + 1 / 2) / real N)) * cis (real \<tau> * (2 * pi * (\<phi> - real j / real N)))) \<le> real N" by simp
  have "cmod (pe_amp_reg N (win_state N) \<phi> j) \<le> sqrt 2 / real N * real N"
  proof -
    have ab: "\<bar>sqrt 2 / real N\<bar> = sqrt 2 / real N" by simp
    show ?thesis unfolding win_amp_formula[OF j] norm_mult norm_of_real ab
      by (rule mult_left_mono[OF s]) simp
  qed
  hence "cmod (pe_amp_reg N (win_state N) \<phi> j) \<le> sqrt 2" using N0 by simp
  hence "(cmod (pe_amp_reg N (win_state N) \<phi> j))\<^sup>2 \<le> (sqrt 2)\<^sup>2" by (rule power_mono) simp
  thus ?thesis by simp
qed

lemma pe_amp_reg_shift_up: "pe_amp_reg N psi (\<phi> + 1) j = pe_amp_reg N psi \<phi> j"
proof -
  have "cis (2 * pi * (\<phi> + 1)) = cis (2 * pi * \<phi>)"
    using cis_mult[of "2 * pi * \<phi>" "2 * pi"] by (simp add: distrib_left)
  thus ?thesis by (simp add: pe_amp_reg_def)
qed

subsection \<open>Counting lemmas\<close>

lemma near_count:
  fixes y :: real
  shows "card {k. k < N \<and> \<bar>y - real k\<bar> < 1} \<le> 2"
proof -
  have "{k. k < N \<and> \<bar>y - real k\<bar> < 1} \<subseteq> {nat \<lfloor>y\<rfloor>, nat \<lfloor>y\<rfloor> + 1}"
  proof
    fix k assume "k \<in> {k. k < N \<and> \<bar>y - real k\<bar> < 1}"
    hence k: "\<bar>y - real k\<bar> < 1" by simp
    have "real k - 1 < y" "y < real k + 1" using k by linarith+
    hence "\<lfloor>y\<rfloor> = int k \<or> \<lfloor>y\<rfloor> = int k - 1" by linarith
    thus "k \<in> {nat \<lfloor>y\<rfloor>, nat \<lfloor>y\<rfloor> + 1}" by auto
  qed
  hence "card {k. k < N \<and> \<bar>y - real k\<bar> < 1} \<le> card {nat \<lfloor>y\<rfloor>, nat \<lfloor>y\<rfloor> + 1}" by (intro card_mono) simp_all
  also have "\<dots> \<le> 2" by (simp add: card_insert_if)
  finally show ?thesis .
qed

text \<open>$\sum_{m\le n}1/(m+1)^2\le2-1/(n+1)$, by telescoping.\<close>

lemma inv_sq_partial: "(\<Sum>m<Suc n. 1 / (real m + 1)\<^sup>2) \<le> 2 - 1 / (real n + 1)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have t: "1 / (real n + 2)\<^sup>2 \<le> 1 / (real n + 1) - 1 / (real n + 2)"
  proof -
    have "1 / (real n + 1) - 1 / (real n + 2) = 1 / ((real n + 1) * (real n + 2))" by (simp add: field_simps)
    moreover have "1 / (real n + 2)\<^sup>2 \<le> 1 / ((real n + 1) * (real n + 2))"
      by (rule divide_left_mono) (simp_all add: power2_eq_square mult_right_mono)
    ultimately show ?thesis by simp
  qed
  have "(\<Sum>m<Suc (Suc n). 1 / (real m + 1)\<^sup>2) = (\<Sum>m<Suc n. 1 / (real m + 1)\<^sup>2) + 1 / (real n + 2)\<^sup>2"
    by (simp add: add.commute)
  also have "\<dots> \<le> 2 - 1 / (real n + 1) + (1 / (real n + 1) - 1 / (real n + 2))" using Suc.IH t by linarith
  also have "\<dots> = 2 - 1 / (real (Suc n) + 1)" by (simp add: add.commute)
  finally show ?case .
qed

lemma inv_sq_finite_nat:
  assumes "finite X"
  shows "(\<Sum>m\<in>X. 1 / (real m + 1)\<^sup>2) \<le> 2"
proof (cases "X = {}")
  case True thus ?thesis by simp
next
  case False
  have "X \<subseteq> {..<Suc (Lattices_Big.Max X)}" using assms by (auto simp: less_Suc_eq_le)
  hence "(\<Sum>m\<in>X. 1 / (real m + 1)\<^sup>2) \<le> (\<Sum>m<Suc (Lattices_Big.Max X). 1 / (real m + 1)\<^sup>2)" by (intro sum_mono2) simp_all
  also have "\<dots> \<le> 2 - 1 / (real (Lattices_Big.Max X) + 1)" by (rule inv_sq_partial)
  also have "\<dots> \<le> 2" by simp
  finally show ?thesis .
qed

text \<open>If $h\ge1$ on $A$ and $\lfloor h\rfloor$ is injective there, $\sum_{k\in A}1/h(k)^2\le2$.\<close>

lemma inv_sq_floor_inj:
  fixes h :: "nat \<Rightarrow> real"
  assumes A: "finite A" and h1: "\<And>k. k \<in> A \<Longrightarrow> 1 \<le> h k" and inj: "inj_on (\<lambda>k. \<lfloor>h k\<rfloor>) A"
  shows "(\<Sum>k\<in>A. 1 / (h k)\<^sup>2) \<le> 2"
proof -
  define g where "g k = nat \<lfloor>h k\<rfloor> - 1" for k
  have fl: "1 \<le> \<lfloor>h k\<rfloor>" if "k \<in> A" for k using h1[OF that] by linarith
  have g1: "real (g k) + 1 = real_of_int \<lfloor>h k\<rfloor>" if "k \<in> A" for k
  proof -
    have f: "1 \<le> \<lfloor>h k\<rfloor>" by (rule fl[OF that])
    hence "1 \<le> nat \<lfloor>h k\<rfloor>" by linarith
    hence "real (nat \<lfloor>h k\<rfloor> - 1) = real (nat \<lfloor>h k\<rfloor>) - 1" by (simp add: of_nat_diff)
    moreover have "real (nat \<lfloor>h k\<rfloor>) = real_of_int \<lfloor>h k\<rfloor>" using f by simp
    ultimately show ?thesis unfolding g_def by simp
  qed
  have ginj: "inj_on g A"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> A" and y: "y \<in> A" and e: "g x = g y"
    have "real_of_int \<lfloor>h x\<rfloor> = real_of_int \<lfloor>h y\<rfloor>" using g1[OF x] g1[OF y] e by simp
    hence "\<lfloor>h x\<rfloor> = \<lfloor>h y\<rfloor>" by simp
    thus "x = y" using inj x y by (auto dest: inj_onD)
  qed
  have "(\<Sum>k\<in>A. 1 / (h k)\<^sup>2) \<le> (\<Sum>k\<in>A. 1 / (real (g k) + 1)\<^sup>2)"
  proof (rule sum_mono)
    fix k assume k: "k \<in> A"
    have "real (g k) + 1 \<le> h k" unfolding g1[OF k] by simp
    moreover have "0 < real (g k) + 1" by simp
    ultimately show "1 / (h k)\<^sup>2 \<le> 1 / (real (g k) + 1)\<^sup>2"
      by (intro divide_left_mono power_mono) simp_all
  qed
  also have "\<dots> = (\<Sum>m\<in>g ` A. 1 / (real m + 1)\<^sup>2)" by (simp add: sum.reindex[OF ginj])
  also have "\<dots> \<le> 2" by (rule inv_sq_finite_nat) (use A in simp)
  finally show ?thesis .
qed

text \<open>$\sum_{k<N,\,|y-k|\ge1}1/(y-k)^2\le4$.\<close>

lemma far_inv_sq_sum:
  fixes y :: real
  shows "(\<Sum>k\<in>{k. k < N \<and> 1 \<le> \<bar>y - real k\<bar>}. 1 / (y - real k)\<^sup>2) \<le> 4"
proof -
  let ?P = "{k. k < N \<and> 1 \<le> real k - y}" and ?M = "{k. k < N \<and> 1 \<le> y - real k}"
  have split: "{k. k < N \<and> 1 \<le> \<bar>y - real k\<bar>} = ?P \<union> ?M" by auto
  have disj: "?P \<inter> ?M = {}" by auto
  have fP: "finite ?P" and fM: "finite ?M" by simp_all
  have P: "(\<Sum>k\<in>?P. 1 / (real k - y)\<^sup>2) \<le> 2"
  proof (rule inv_sq_floor_inj)
    show "inj_on (\<lambda>k. \<lfloor>real k - y\<rfloor>) ?P"
    proof (rule inj_onI)
      fix a b assume "\<lfloor>real a - y\<rfloor> = \<lfloor>real b - y\<rfloor>"
      moreover have "\<lfloor>real a - y\<rfloor> = \<lfloor>- y\<rfloor> + int a" "\<lfloor>real b - y\<rfloor> = \<lfloor>- y\<rfloor> + int b"
        using floor_add_int[of "- y" "int a"] floor_add_int[of "- y" "int b"] by simp_all
      ultimately show "a = b" by simp
    qed
  qed simp_all
  have M: "(\<Sum>k\<in>?M. 1 / (y - real k)\<^sup>2) \<le> 2"
  proof (rule inv_sq_floor_inj)
    show "inj_on (\<lambda>k. \<lfloor>y - real k\<rfloor>) ?M"
    proof (rule inj_onI)
      fix a b assume "\<lfloor>y - real a\<rfloor> = \<lfloor>y - real b\<rfloor>"
      moreover have "\<lfloor>y - real a\<rfloor> = \<lfloor>y\<rfloor> - int a" "\<lfloor>y - real b\<rfloor> = \<lfloor>y\<rfloor> - int b"
        using floor_diff_of_int[of y "int a"] floor_diff_of_int[of y "int b"] by simp_all
      ultimately show "a = b" by simp
    qed
  qed simp_all
  have Pe: "(\<Sum>k\<in>?P. 1 / (y - real k)\<^sup>2) = (\<Sum>k\<in>?P. 1 / (real k - y)\<^sup>2)"
    by (rule sum.cong) (simp_all add: power2_commute)
  have "(\<Sum>k\<in>{k. k < N \<and> 1 \<le> \<bar>y - real k\<bar>}. 1 / (y - real k)\<^sup>2)
        = (\<Sum>k\<in>?P. 1 / (y - real k)\<^sup>2) + (\<Sum>k\<in>?M. 1 / (y - real k)\<^sup>2)"
    unfolding split by (rule sum.union_disjoint[OF fP fM disj])
  thus ?thesis using P M Pe by linarith
qed

text \<open>The branch weight: $w(t)=2$ for $|t|<1$, $\pi^2/(2t^2)$ otherwise; $\sum_{k<N}w(y-k)\le4+2\pi^2$.\<close>

definition win_w :: "real \<Rightarrow> real" where
  "win_w t = (if \<bar>t\<bar> < 1 then 2 else pi\<^sup>2 / (2 * t\<^sup>2))"

lemma win_w_nonneg: "0 \<le> win_w t"
  by (simp add: win_w_def)

lemma win_w_sum: "(\<Sum>k<N. win_w (y - real k)) \<le> 4 + 2 * pi\<^sup>2"
proof -
  let ?n = "{k. k < N \<and> \<bar>y - real k\<bar> < 1}" and ?f = "{k. k < N \<and> 1 \<le> \<bar>y - real k\<bar>}"
  have split: "{..<N} = ?n \<union> ?f" by auto
  have disj: "?n \<inter> ?f = {}" by auto
  have "(\<Sum>k<N. win_w (y - real k)) = (\<Sum>k\<in>?n. win_w (y - real k)) + (\<Sum>k\<in>?f. win_w (y - real k))"
    unfolding split by (rule sum.union_disjoint) (simp_all add: disj)
  also have "(\<Sum>k\<in>?n. win_w (y - real k)) = 2 * real (card ?n)"
    by (simp add: win_w_def)
  also have "(\<Sum>k\<in>?f. win_w (y - real k)) = pi\<^sup>2 / 2 * (\<Sum>k\<in>?f. 1 / (y - real k)\<^sup>2)"
    by (simp add: win_w_def sum_distrib_left)
  also have "2 * real (card ?n) + pi\<^sup>2 / 2 * (\<Sum>k\<in>?f. 1 / (y - real k)\<^sup>2) \<le> 2 * 2 + pi\<^sup>2 / 2 * 4"
    using near_count[where y=y and N=N] far_inv_sq_sum[where y=y and N=N] by (intro add_mono mult_left_mono) simp_all
  finally show ?thesis by simp
qed

subsection \<open>Branch bounds for the window register\<close>

text \<open>If $g\le|\delta|\le\frac12$ then $|\alpha_j|^2\le\pi^2/(2N^4g^4)$.\<close>

lemma win_amp_gap:
  assumes N: "2 \<le> N" and j: "j < N" and dhi: "\<bar>\<phi> - real j / real N\<bar> \<le> 1 / 2"
      and g0: "0 < g" and g: "g \<le> \<bar>\<phi> - real j / real N\<bar>"
  shows "(cmod (pe_amp_reg N (win_state N) \<phi> j))\<^sup>2 \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * g ^ 4)"
proof -
  define \<delta> where "\<delta> = \<phi> - real j / real N"
  have N0: "0 < real N" using N by simp
  have g4: "g ^ 4 \<le> \<delta> ^ 4"
  proof -
    have "g ^ 4 \<le> \<bar>\<delta>\<bar> ^ 4" by (rule power_mono) (use g g0 in \<open>simp_all add: \<delta>_def\<close>)
    thus ?thesis by (simp add: power_abs)
  qed
  have d4: "0 < \<delta> ^ 4" using g4 g0 by (smt (verit) zero_less_power)
  show ?thesis
  proof (cases "1 / real N \<le> \<bar>\<delta>\<bar>")
    case True
    have "(cmod (pe_amp_reg N (win_state N) \<phi> j))\<^sup>2 \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * \<delta> ^ 4)"
      using win_amp_tail[OF N j] True dhi unfolding \<delta>_def by simp
    also have "\<dots> \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * g ^ 4)"
      by (rule divide_left_mono) (use g4 g0 N0 d4 in \<open>simp_all add: mult_left_mono\<close>)
    finally show ?thesis .
  next
    case False
    have lt: "\<bar>\<delta>\<bar> * real N < 1" using False N0 by (simp add: field_simps)
    have "g * real N \<le> \<bar>\<delta>\<bar> * real N" using g N0 unfolding \<delta>_def[symmetric] by (simp add: mult_right_mono)
    hence "real N * g < 1" using lt by (simp add: mult.commute)
    hence "(real N * g) ^ 4 \<le> 1" using g0 N0 by (intro power_le_one) simp_all
    hence "(real N) ^ 4 * g ^ 4 \<le> 1" by (simp add: power_mult_distrib)
    moreover have "4 \<le> pi\<^sup>2" using power_mono[OF pi_ge_two, of 2] by simp
    ultimately have "2 \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * g ^ 4)"
      using g0 N0 by (simp add: field_simps)
    thus ?thesis using win_amp_crude[OF j, of \<phi>] by linarith
  qed
qed

text \<open>The distance on a good branch is quadratic in $\delta$.\<close>

lemma hhl_good_dist:
  assumes N: "0 < N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
      and k: "2 * k < N" and lam: "C / \<theta> \<le> reg_eig t0 N k"
  shows "(sqrt (1 - (clamp (C / reg_eig t0 N k))\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (clamp (C / reg_eig t0 N k) - C / l)\<^sup>2
         \<le> 4 * pi\<^sup>2 * \<theta> ^ 4 * (hhl_phi t0 l - real k / real N)\<^sup>2 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
    and "\<bar>hhl_phi t0 l - real k / real N\<bar> \<le> 1 / 2"
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
  show "?d (clamp (C / ?lam)) \<le> 4 * pi\<^sup>2 * \<theta> ^ 4 * (?ph - real k / real N)\<^sup>2 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
    using lip divide_right_mono[OF sq, of "1 - \<theta>\<^sup>2"] t2 unfolding fk \<delta>_def by (simp add: divide_divide_eq_left)
  have "real k / real N < 1 / 2" using k N by (simp add: field_simps)
  moreover have "0 \<le> real k / real N" by simp
  ultimately show "\<bar>?ph - real k / real N\<bar> \<le> 1 / 2" using pf(2,3) by (intro abs_leI; linarith)
qed

text \<open>Good branches: $|\alpha_k|^2d_k^2\le K\,w(N\varphi-k)/N^2$ with
$K=4\pi^2\theta^4/(t_0^2C^2(1-\theta^2))$.\<close>

lemma win_branch_good:
  assumes N: "2 \<le> N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
      and k: "2 * k < N" and lam: "C / \<theta> \<le> reg_eig t0 N k"
  shows "(cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2 *
           ((sqrt (1 - (clamp (C / reg_eig t0 N k))\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (clamp (C / reg_eig t0 N k) - C / l)\<^sup>2)
         \<le> 4 * pi\<^sup>2 * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) / (real N)\<^sup>2 * win_w (real N * hhl_phi t0 l - real k)"
proof -
  have N0: "0 < N" using N by simp
  have NR: "0 < real N" using N by simp
  let ?a = "(cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2"
  let ?d = "(sqrt (1 - (clamp (C / reg_eig t0 N k))\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (clamp (C / reg_eig t0 N k) - C / l)\<^sup>2"
  define K where "K = 4 * pi\<^sup>2 * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
  define \<delta> where "\<delta> = hhl_phi t0 l - real k / real N"
  have t2: "0 < 1 - \<theta>\<^sup>2" using th mult_strict_mono[of \<theta> 1 \<theta> 1] by (simp add: power2_eq_square)
  have K0: "0 \<le> K" unfolding K_def using t2 by simp
  note gd = hhl_good_dist[OF N0 t0 C th l_lo l_hi k lam]
  have dK: "?d \<le> K * \<delta>\<^sup>2" using gd(1) unfolding K_def \<delta>_def by (simp add: field_simps)
  have dabs: "\<bar>\<delta>\<bar> \<le> 1 / 2" using gd(2) unfolding \<delta>_def .
  have kN: "k < N" using k by simp
  have Nd: "real N * hhl_phi t0 l - real k = real N * \<delta>" unfolding \<delta>_def using NR by (simp add: field_simps)
  have d0: "0 \<le> ?d" by simp
  show ?thesis
  proof (cases "\<bar>real N * \<delta>\<bar> < 1")
    case True
    have w: "win_w (real N * hhl_phi t0 l - real k) = 2" unfolding Nd win_w_def using True by simp
    have "(real N * \<delta>)\<^sup>2 \<le> 1" using True by (simp add: abs_square_le_1)
    hence dd: "\<delta>\<^sup>2 \<le> 1 / (real N)\<^sup>2" using NR by (simp add: power_mult_distrib field_simps)
    have "?a * ?d \<le> 2 * (K * \<delta>\<^sup>2)" by (rule mult_mono[OF win_amp_crude[OF kN] dK]) simp_all
    also have "\<dots> \<le> 2 * (K * (1 / (real N)\<^sup>2))" using dd K0 by (intro mult_left_mono) simp_all
    finally show ?thesis unfolding w K_def[symmetric] by (simp add: mult_ac)
  next
    case False
    have w: "win_w (real N * hhl_phi t0 l - real k) = pi\<^sup>2 / (2 * (real N * \<delta>)\<^sup>2)" unfolding Nd win_w_def using False by simp
    have dlo: "1 / real N \<le> \<bar>\<delta>\<bar>" using False NR by (simp add: abs_mult field_simps)
    have dz: "\<delta> \<noteq> 0" using dlo NR by auto
    have a: "?a \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * \<delta> ^ 4)"
      using win_amp_tail[OF N kN] dlo dabs unfolding \<delta>_def by simp
    have "?a * ?d \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * \<delta> ^ 4) * (K * \<delta>\<^sup>2)" by (rule mult_mono[OF a dK]) simp_all
    also have "\<dots> = K / (real N)\<^sup>2 * (pi\<^sup>2 / (2 * (real N * \<delta>)\<^sup>2))"
      using dz NR by (simp add: power_mult_distrib field_simps power2_eq_square power4_eq_xxxx)
    finally show ?thesis unfolding w K_def by simp
  qed
qed

text \<open>Bad branches (clamped or in the negative half): $|\alpha_k|^2\le8\pi^2/(N\varphi)^4$.\<close>

lemma win_branch_bad:
  assumes N: "2 \<le> N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
      and k: "k < N" and bad: "\<not> (2 * k < N \<and> C / \<theta> \<le> reg_eig t0 N k)"
  shows "(cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2 \<le> 8 * pi\<^sup>2 / ((real N) ^ 4 * (hhl_phi t0 l) ^ 4)"
proof -
  note pf = hhl_param_facts[OF t0 C th l_lo l_hi]
  let ?ph = "hhl_phi t0 l"
  have NR: "0 < real N" using N by simp
  have g0: "0 < ?ph / 2" using pf(2) by simp
  have e: "pi\<^sup>2 / (2 * (real N) ^ 4 * (?ph / 2) ^ 4) = 8 * pi\<^sup>2 / ((real N) ^ 4 * ?ph ^ 4)"
    by (simp add: power_divide field_simps)
  define \<delta> where "\<delta> = ?ph - real k / real N"
  have gap: "\<bar>\<phi>' - real k / real N\<bar> \<le> 1 / 2 \<Longrightarrow> ?ph / 2 \<le> \<bar>\<phi>' - real k / real N\<bar> \<Longrightarrow>
             (cmod (pe_amp_reg N (win_state N) \<phi>' k))\<^sup>2 \<le> 8 * pi\<^sup>2 / ((real N) ^ 4 * ?ph ^ 4)" for \<phi>'
    using win_amp_gap[OF N k _ g0] unfolding e by simp
  show ?thesis
  proof (cases "2 * k < N")
    case True
    hence lam: "reg_eig t0 N k < C / \<theta>" using bad by simp
    have lamv: "reg_eig t0 N k = 2 * pi * real k / (t0 * real N)" using True by (simp add: reg_eig_def)
    have kN: "real k / real N < C * t0 / (2 * pi * \<theta>)"
      using lam unfolding lamv using t0 th NR by (simp add: field_simps)
    have ph2: "C * t0 / (2 * pi * \<theta>) \<le> ?ph / 2"
      unfolding hhl_phi_def using pf(7) t0 th by (simp add: field_simps)
    have dgt: "?ph / 2 < \<delta>" unfolding \<delta>_def using kN ph2 by linarith
    have dle: "\<delta> \<le> ?ph" unfolding \<delta>_def by simp
    have dabs: "\<bar>\<delta>\<bar> \<le> 1 / 2" using dgt dle pf(2,3) by (intro abs_leI; linarith)
    have "?ph / 2 \<le> \<bar>\<delta>\<bar>" using dgt by linarith
    thus ?thesis using dabs unfolding \<delta>_def by (rule gap[rotated])
  next
    case False
    have kN1: "1 / 2 \<le> real k / real N" using False NR by (simp add: field_simps)
    have kN2: "real k / real N < 1" using k NR by simp
    show ?thesis
    proof (cases "- (1 / 2) \<le> \<delta>")
      case True
      have dneg: "\<delta> \<le> - (1 / 4)" unfolding \<delta>_def using kN1 pf(3) by linarith
      have dabs: "\<bar>\<delta>\<bar> \<le> 1 / 2" using True dneg by (intro abs_leI; linarith)
      have "?ph / 2 \<le> \<bar>\<delta>\<bar>" using dneg pf(3) by linarith
      thus ?thesis by (intro gap) (use dabs in \<open>simp_all add: \<delta>_def\<close>)
    next
      case False
      have d'1: "?ph + 1 - real k / real N < 1 / 2" using False \<delta>_def by linarith
      have d'2: "?ph < ?ph + 1 - real k / real N" using kN2 by linarith
      have dabs: "\<bar>?ph + 1 - real k / real N\<bar> \<le> 1 / 2" using d'1 d'2 pf(2) by (intro abs_leI; linarith)
      have "?ph / 2 \<le> \<bar>?ph + 1 - real k / real N\<bar>" using d'2 pf(2) by linarith
      hence "(cmod (pe_amp_reg N (win_state N) (?ph + 1) k))\<^sup>2 \<le> 8 * pi\<^sup>2 / ((real N) ^ 4 * ?ph ^ 4)"
        using dabs by (intro gap) (simp_all add: algebra_simps)
      thus ?thesis unfolding pe_amp_reg_shift_up .
    qed
  qed
qed

subsection \<open>The error bound on an eigenvector\<close>

lemma win_branch_bound:
  assumes N: "2 \<le> N" and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2" and k: "k < N"
  shows "(cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2 *
           ((sqrt (1 - (clamp (C / reg_eig t0 N k))\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (clamp (C / reg_eig t0 N k) - C / l)\<^sup>2)
         \<le> 4 * pi\<^sup>2 * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) / (real N)\<^sup>2 * win_w (real N * hhl_phi t0 l - real k)
           + 32 * pi\<^sup>2 / ((real N) ^ 4 * (hhl_phi t0 l) ^ 4)"
proof -
  note pf = hhl_param_facts[OF t0 C th l_lo l_hi]
  let ?a = "(cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2"
  let ?d = "(sqrt (1 - (clamp (C / reg_eig t0 N k))\<^sup>2) - sqrt (1 - (C / l)\<^sup>2))\<^sup>2 + (clamp (C / reg_eig t0 N k) - C / l)\<^sup>2"
  have t2: "0 < 1 - \<theta>\<^sup>2" using th mult_strict_mono[of \<theta> 1 \<theta> 1] by (simp add: power2_eq_square)
  have b1: "0 \<le> 4 * pi\<^sup>2 * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) / (real N)\<^sup>2 * win_w (real N * hhl_phi t0 l - real k)"
    using t2 win_w_nonneg by simp
  have b2: "0 \<le> 32 * pi\<^sup>2 / ((real N) ^ 4 * (hhl_phi t0 l) ^ 4)" by simp
  show ?thesis
  proof (cases "2 * k < N \<and> C / \<theta> \<le> reg_eig t0 N k")
    case True
    thus ?thesis using win_branch_good[OF N t0 C th l_lo l_hi] b2 by (simp add: add_increasing2)
  next
    case False
    have a: "?a \<le> 8 * pi\<^sup>2 / ((real N) ^ 4 * (hhl_phi t0 l) ^ 4)"
      by (rule win_branch_bad[OF N t0 C th l_lo l_hi k False])
    have d4: "?d \<le> 4" by (rule rot_dist_le_four[OF clamp_abs pf(6)])
    have "?a * ?d \<le> 8 * pi\<^sup>2 / ((real N) ^ 4 * (hhl_phi t0 l) ^ 4) * 4" by (rule mult_mono[OF a d4]) simp_all
    thus ?thesis using b1 by simp
  qed
qed

text \<open>The error bound for the window circuit on an eigenvector:
\[\norm{\text{output}-\psi\otimes u\otimes R(C/\lambda)\ket0}^2
  \le\norm u^2\Bigl(\frac{8\pi^2(2+\pi^2)\theta^4}{N^2t_0^2C^2(1-\theta^2)}+\frac{512\pi^6}{N^3t_0^4\lambda^4}\Bigr).\]\<close>

theorem hhl_window_error_bound:
  fixes A :: "complex Matrix.mat" and u :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1"
      and l_lo: "2 * C / \<theta> \<le> l" and l_hi: "t0 * l \<le> pi / 2"
  shows "Re \<langle>hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 2 0)) -
              tensor_vec (win_state N) (tensor_vec u (rot (C / l) *\<^sub>v unit_vec 2 0)) |
            hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 2 0)) -
              tensor_vec (win_state N) (tensor_vec u (rot (C / l) *\<^sub>v unit_vec 2 0))\<rangle>
         \<le> Re \<langle>u|u\<rangle> * (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))
                        + 512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * l ^ 4))"
proof -
  note pf = hhl_param_facts[OF t0 C th l_lo l_hi]
  have N0: "0 < N" using N by simp
  have NR: "0 < real N" using N by simp
  let ?f = "\<lambda>k. clamp (C / reg_eig t0 N k)" and ?c = "C / l" and ?ph = "hhl_phi t0 l"
  let ?S = "\<Sum>k<N. (cmod (pe_amp_reg N (win_state N) ?ph k))\<^sup>2 * ((sqrt (1 - (?f k)\<^sup>2) - sqrt (1 - ?c\<^sup>2))\<^sup>2 + (?f k - ?c)\<^sup>2)"
  define K where "K = 4 * pi\<^sup>2 * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
  define B where "B = 32 * pi\<^sup>2 / ((real N) ^ 4 * ?ph ^ 4)"
  have t2: "0 < 1 - \<theta>\<^sup>2" using th mult_strict_mono[of \<theta> 1 \<theta> 1] by (simp add: power2_eq_square)
  have K0: "0 \<le> K" unfolding K_def using t2 by simp
  define ru where "ru = (\<Sum>i<n. (cmod (u $ i))\<^sup>2)"
  have uu: "\<langle>u|u\<rangle> = complex_of_real ru" unfolding ru_def by (simp add: inner_self_sum[OF u])
  have ru0: "0 \<le> ru" unfolding ru_def by (simp add: sum_nonneg)
  have E: "\<langle>hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 2 0)) -
              tensor_vec (win_state N) (tensor_vec u (rot ?c *\<^sub>v unit_vec 2 0)) |
            hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 2 0)) -
              tensor_vec (win_state N) (tensor_vec u (rot ?c *\<^sub>v unit_vec 2 0))\<rangle> = complex_of_real (ru * ?S)"
    using hhl_approx_error_real[OF A t0 N0 u ev dim_win_state, of ?f ?c] unfolding uu by simp
  have S: "?S \<le> K / (real N)\<^sup>2 * (4 + 2 * pi\<^sup>2) + real N * B"
  proof -
    have "?S \<le> (\<Sum>k<N. K / (real N)\<^sup>2 * win_w (real N * ?ph - real k) + B)"
      by (rule sum_mono) (unfold K_def B_def, rule win_branch_bound[OF N t0 C th l_lo l_hi], simp)
    also have "\<dots> = K / (real N)\<^sup>2 * (\<Sum>k<N. win_w (real N * ?ph - real k)) + real N * B"
      by (simp add: sum.distrib sum_distrib_left)
    also have "\<dots> \<le> K / (real N)\<^sup>2 * (4 + 2 * pi\<^sup>2) + real N * B"
      using win_w_sum[where N=N and y="real N * ?ph"] K0 by (intro add_right_mono mult_left_mono) simp_all
    finally show ?thesis .
  qed
  have alg: "K / (real N)\<^sup>2 * (4 + 2 * pi\<^sup>2) + real N * B =
             8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * l ^ 4)"
  proof -
    have p4: "?ph ^ 4 = t0 ^ 4 * l ^ 4 / (16 * pi ^ 4)" unfolding hhl_phi_def by (simp add: power_divide power_mult_distrib)
    have e1: "K / (real N)\<^sup>2 * (4 + 2 * pi\<^sup>2) = 8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))"
      unfolding K_def using t2 NR t0 C by (simp add: field_simps)
    have e2: "real N * B = 512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * l ^ 4)"
    proof -
      have p6: "(pi::real) ^ 6 = pi\<^sup>2 * pi ^ 4" by (simp flip: power_add)
      show ?thesis unfolding B_def p4 p6 using NR t0 pf(1) by (simp add: field_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
    qed
    show ?thesis unfolding e1 e2 ..
  qed
  have "Re (complex_of_real (ru * ?S)) = ru * ?S" by simp
  also have "\<dots> \<le> ru * (K / (real N)\<^sup>2 * (4 + 2 * pi\<^sup>2) + real N * B)" by (rule mult_left_mono[OF S ru0])
  finally show ?thesis unfolding E alg uu by simp
qed

subsection \<open>Every right-hand side\<close>

theorem hhl_window_bound:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n"
  shows "Re \<langle>hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
              tensor_vec (win_state N)
                (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
                 tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1)) |
            hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
              tensor_vec (win_state N)
                (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
                 tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))\<rangle>
         \<le> (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * lmin ^ 4)) * Re \<langle>b|b\<rangle>"
proof -
  let ?G0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A"
  let ?G1 = "complex_of_real C \<cdot>\<^sub>m herm_inv A"
  let ?H = "hhl_circuit_clamped A t0 N C" and ?u = "win_state N"
  let ?Emb = "lift_mat n ?u (1\<^sub>m n) (0\<^sub>m n n)" and ?Idl = "lift_mat n ?u ?G0 ?G1"
  let ?Err = "?H * ?Emb - ?Idl"
  let ?e = "(8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * lmin ^ 4))"
  let ?f = "\<lambda>k. clamp (C / reg_eig t0 N k)"
  have N0: "0 < N" using N by simp
  have du: "dim_vec ?u = N" by simp
  have nA: "dim_row A = n" using A(1) by simp
  have G0: "?G0 \<in> carrier_mat n n" using A by simp
  have G1: "?G1 \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
  have Hc: "?H \<in> carrier_mat (N * (n * 2)) (N * (n * 2))"
    unfolding flag_circuit_def hhl_Wd_def nA
    by (rule mult_carrier_mat[OF dagger_carrier[OF pe_unitary_carrier] mult_carrier_mat[OF ctrl_blocks_carrier pe_unitary_carrier]])
  have Ec: "?Emb \<in> carrier_mat (N * (n * 2)) n" using lift_carrier[of 2 n ?u] du by simp
  have Ic: "?Idl \<in> carrier_mat (N * (n * 2)) n" using lift_carrier[of 2 n ?u] du by simp
  have Errc: "?Err \<in> carrier_mat (N * (n * 2)) n" by (rule minus_carrier_mat[OF Ic])
  have Errv: "?Err *\<^sub>v v = ?H *\<^sub>v tensor_vec ?u (tensor_vec v (unit_vec 2 0)) - ?Idl *\<^sub>v v" if v: "dim_vec v = n" for v
  proof -
    have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
    have "?Err *\<^sub>v v = (?H * ?Emb) *\<^sub>v v - ?Idl *\<^sub>v v" by (rule minus_mult_distrib_mat_vec[OF mult_carrier_mat[OF Hc Ec] Ic vc])
    also have "(?H * ?Emb) *\<^sub>v v = ?H *\<^sub>v (?Emb *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF Hc Ec vc])
    finally show ?thesis unfolding lift_mat_emb[OF v] .
  qed
  have ErrU: "?Err *\<^sub>v v = ?H *\<^sub>v tensor_vec ?u (tensor_vec v (unit_vec 2 0)) - tensor_vec ?u (tensor_vec v (rot (C / l) *\<^sub>v unit_vec 2 0))"
    if v: "dim_vec v = n" "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v" for v l
    unfolding Errv[OF v(1)] ideal_mat_eigen[OF A v] ..
  have lmin0: "0 < lmin"
  proof -
    have "0 < 2 * C / \<theta>" using C th by simp
    thus ?thesis using lmin by linarith
  qed
  have "\<parallel>?Err *\<^sub>v b\<parallel>\<^sup>2 \<le> ?e * \<parallel>b\<parallel>\<^sup>2"
  proof (rule every_rhs_bound[OF A Errc _ _ b])
    fix v v' l l' assume v: "dim_vec v = n" "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v" "l \<in> herm_spectrum A"
      and v': "dim_vec v' = n" "A *\<^sub>v v' = complex_of_real l' \<cdot>\<^sub>v v'" "l' \<in> herm_spectrum A" and o: "\<langle>v|v'\<rangle> = 0"
    show "\<langle>?Err *\<^sub>v v|?Err *\<^sub>v v'\<rangle> = 0"
      unfolding ErrU[OF v(1,2)] ErrU[OF v'(1,2)] by (rule hhl_err_orth[OF A t0 N0 v(1,2) v'(1,2) o du])
  next
    fix v l assume v: "dim_vec v = n" "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v" "l \<in> herm_spectrum A" "\<parallel>v\<parallel> = 1"
    have sl: "lmin \<le> l" "t0 * l \<le> pi / 2" using spec[OF v(3)] by simp_all
    have "Re \<langle>?Err *\<^sub>v v|?Err *\<^sub>v v\<rangle> \<le> Re \<langle>v|v\<rangle> * (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * l ^ 4))"
      unfolding ErrU[OF v(1,2)] by (rule hhl_window_error_bound[OF A t0 N v(1,2) C th _ sl(2)]) (use sl(1) lmin in linarith)
    also have "\<dots> \<le> ?e"
    proof -
      have "512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * l ^ 4) \<le> 512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * lmin ^ 4)"
        using sl(1) lmin0 N t0 by (intro divide_left_mono mult_left_mono power_mono) simp_all
      hence "8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * l ^ 4) \<le> ?e"
        by (rule add_left_mono)
      thus ?thesis using v(4) vnorm_Re_inner[of v] by simp
    qed
    finally show "\<parallel>?Err *\<^sub>v v\<parallel>\<^sup>2 \<le> ?e" unfolding vnorm_Re_inner .
  qed
  thus ?thesis unfolding vnorm_Re_inner Errv[OF b] lift_mat_mult_vec[OF G0 G1 b] .
qed

lemma window_rate:
  fixes a b \<epsilon> :: real
  assumes N: "2 \<le> N" and a: "0 \<le> a" and b: "0 \<le> b" and e: "0 < \<epsilon>" and NQ: "sqrt (a + b) / \<epsilon> \<le> real N"
  shows "a / (real N)\<^sup>2 + b / (real N) ^ 3 \<le> \<epsilon>\<^sup>2"
proof -
  have NR: "1 \<le> real N" using N by simp
  have "b / (real N) ^ 3 \<le> b / (real N)\<^sup>2"
    by (rule divide_left_mono[OF _ b]) (use NR in \<open>simp_all add: power2_eq_square power3_eq_cube\<close>)
  hence s: "a / (real N)\<^sup>2 + b / (real N) ^ 3 \<le> (a + b) / (real N)\<^sup>2" by (simp add: add_divide_distrib)
  have "sqrt (a + b) \<le> \<epsilon> * real N" using NQ e by (simp add: divide_le_eq mult.commute)
  hence "(sqrt (a + b))\<^sup>2 \<le> (\<epsilon> * real N)\<^sup>2" by (rule power_mono) (use a b in simp)
  hence "a + b \<le> \<epsilon>\<^sup>2 * (real N)\<^sup>2" using a b by (simp add: power_mult_distrib)
  hence "(a + b) / (real N)\<^sup>2 \<le> \<epsilon>\<^sup>2" using NR by (simp add: divide_le_eq)
  with s show ?thesis by linarith
qed

text \<open>Precision $\varepsilon$ with a register of size $N\ge Q/\varepsilon$:
$\norm{\text{output}-\text{ideal}}\le\varepsilon\norm b$, with $Q$ independent of $N$ and $\varepsilon$.\<close>

corollary hhl_window_precision:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real N"
  shows "Re \<langle>hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
              tensor_vec (win_state N)
                (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
                 tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1)) |
            hhl_circuit_clamped A t0 N C *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
              tensor_vec (win_state N)
                (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
                 tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))\<rangle>
         \<le> \<epsilon>\<^sup>2 * Re \<langle>b|b\<rangle>"
proof -
  let ?a = "8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2))" and ?b = "512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)"
  have t2: "0 < 1 - \<theta>\<^sup>2" using th mult_strict_mono[of \<theta> 1 \<theta> 1] by (simp add: power2_eq_square)
  have a0: "0 \<le> ?a" using t2 by simp
  have b0: "0 \<le> ?b" by simp
  have e1: "8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / ((real N)\<^sup>2 * t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) = ?a / (real N)\<^sup>2"
    by (simp add: field_simps)
  have e2: "512 * pi ^ 6 / ((real N) ^ 3 * t0 ^ 4 * lmin ^ 4) = ?b / (real N) ^ 3"
    by (simp add: field_simps)
  have bb: "0 \<le> Re \<langle>b|b\<rangle>" unfolding inner_self_sum[OF b] by (simp add: sum_nonneg)
  have "?a / (real N)\<^sup>2 + ?b / (real N) ^ 3 \<le> \<epsilon>\<^sup>2" by (rule window_rate[OF N a0 b0 e NQ])
  hence "(?a / (real N)\<^sup>2 + ?b / (real N) ^ 3) * Re \<langle>b|b\<rangle> \<le> \<epsilon>\<^sup>2 * Re \<langle>b|b\<rangle>" by (rule mult_right_mono[OF _ bb])
  with hhl_window_bound[OF A t0 N C th lmin spec b] show ?thesis unfolding e1 e2 by linarith
qed

end
