theory HHL_Filter
  imports HHL_Complete
begin

section \<open>The filter-function algorithm of the HHL paper\<close>

text \<open>Appendix A of the HHL paper replaces the two-level ancilla by a three-level flag register
(nothing, well, ill) set to $\ket{h(\tilde\lambda_k)}$ by the filter functions $f,g$.  We formalise the
filter functions, Lemma 2 ($\ket{h(\lambda)}$ is $\frac\pi2\kappa$-Lipschitz), Lemma 3 (relative
Lipschitz bound; the paper's constant $\pi^2/2$ is wrong, the correct constant is $\pi^2$), the
circuit with a $d$-level flag, and Theorem 1 parts (1) and (2) on eigenvectors with the window
register: errors $O(\kappa/(Nt_0))$.\<close>

subsection \<open>Filter functions\<close>

text \<open>The filter functions of the HHL paper (A3), with $\kappa'=2\kappa$:
$f(\lambda)=1/(2\kappa\lambda)$ for $\lambda\ge1/\kappa$, $\tfrac12\sin(\tfrac\pi2(2\kappa\lambda-1))$ on
$[1/2\kappa,1/\kappa)$, $0$ below; $g=0$, $\tfrac12\cos(\tfrac\pi2(2\kappa\lambda-1))$, $\tfrac12$.\<close>

definition filt_f :: "real \<Rightarrow> real \<Rightarrow> real" where
  "filt_f \<kappa> x = (if 1 / \<kappa> \<le> x then 1 / (2 * \<kappa> * x)
                   else if 1 / (2 * \<kappa>) \<le> x then sin (pi / 2 * (2 * \<kappa> * x - 1)) / 2 else 0)"

definition filt_g :: "real \<Rightarrow> real \<Rightarrow> real" where
  "filt_g \<kappa> x = (if 1 / \<kappa> \<le> x then 0
                   else if 1 / (2 * \<kappa>) \<le> x then cos (pi / 2 * (2 * \<kappa> * x - 1)) / 2 else 1 / 2)"

definition filt_s :: "real \<Rightarrow> real \<Rightarrow> real" where
  "filt_s \<kappa> x = sqrt (1 - (filt_f \<kappa> x)\<^sup>2 - (filt_g \<kappa> x)\<^sup>2)"

text \<open>The flag state $\ket{h(\lambda)}=s\ket{\mathrm{nothing}}+f\ket{\mathrm{well}}+g\ket{\mathrm{ill}}$.\<close>

definition hflag :: "real \<Rightarrow> real \<Rightarrow> complex Matrix.vec" where
  "hflag \<kappa> x = Matrix.vec 3 (\<lambda>c. complex_of_real (if c = 0 then filt_s \<kappa> x else if c = 1 then filt_f \<kappa> x else filt_g \<kappa> x))"

lemma dim_hflag [simp]: "dim_vec (hflag \<kappa> x) = 3"
  by (simp add: hflag_def)

context
  fixes \<kappa> :: real
  assumes k0: "0 < \<kappa>"
begin

text \<open>The three regions; on each closed region the functions are given by one formula.\<close>

lemma region1:
  assumes "1 / \<kappa> \<le> x"
  shows "filt_f \<kappa> x = 1 / (2 * \<kappa> * x)" "filt_g \<kappa> x = 0"
  using assms by (simp_all add: filt_f_def filt_g_def)

lemma region2:
  assumes "1 / (2 * \<kappa>) \<le> x" "x \<le> 1 / \<kappa>"
  shows "filt_f \<kappa> x = sin (pi / 2 * (2 * \<kappa> * x - 1)) / 2" "filt_g \<kappa> x = cos (pi / 2 * (2 * \<kappa> * x - 1)) / 2"
proof -
  show "filt_f \<kappa> x = sin (pi / 2 * (2 * \<kappa> * x - 1)) / 2"
  proof (cases "x = 1 / \<kappa>")
    case True
    have "2 * \<kappa> * x - 1 = 1" using True k0 by simp
    thus ?thesis using True k0 by (simp add: filt_f_def)
  qed (use assms in \<open>simp add: filt_f_def\<close>)
  show "filt_g \<kappa> x = cos (pi / 2 * (2 * \<kappa> * x - 1)) / 2"
  proof (cases "x = 1 / \<kappa>")
    case True
    have "2 * \<kappa> * x - 1 = 1" using True k0 by simp
    thus ?thesis using True k0 by (simp add: filt_g_def)
  qed (use assms in \<open>simp add: filt_g_def\<close>)
qed

lemma region3:
  assumes "x \<le> 1 / (2 * \<kappa>)"
  shows "filt_f \<kappa> x = 0" "filt_g \<kappa> x = 1 / 2"
proof -
  have k2: "1 / (2 * \<kappa>) < 1 / \<kappa>" using k0 by (simp add: field_simps)
  show "filt_f \<kappa> x = 0"
  proof (cases "x = 1 / (2 * \<kappa>)")
    case True
    have "2 * \<kappa> * x - 1 = 0" using True k0 by simp
    thus ?thesis using True k2 by (simp add: filt_f_def)
  qed (use assms k2 in \<open>simp add: filt_f_def\<close>)
  show "filt_g \<kappa> x = 1 / 2"
  proof (cases "x = 1 / (2 * \<kappa>)")
    case True
    have "2 * \<kappa> * x - 1 = 0" using True k0 by simp
    thus ?thesis using True k2 by (simp add: filt_g_def)
  qed (use assms k2 in \<open>simp add: filt_g_def\<close>)
qed

lemma fg_sq_le: "(filt_f \<kappa> x)\<^sup>2 + (filt_g \<kappa> x)\<^sup>2 \<le> 1 / 4"
proof -
  consider "1 / \<kappa> \<le> x" | "1 / (2 * \<kappa>) \<le> x" "x \<le> 1 / \<kappa>" | "x \<le> 1 / (2 * \<kappa>)" by linarith
  thus ?thesis
  proof cases
    case 1
    have "1 / (2 * \<kappa> * x) \<le> 1 / 2"
    proof -
      have "1 \<le> \<kappa> * x" using 1 k0 by (simp add: field_simps)
      thus ?thesis using k0 by (simp add: field_simps)
    qed
    moreover have "0 \<le> 1 / (2 * \<kappa> * x)" using 1 k0 by (simp add: field_simps)
    ultimately have "(1 / (2 * \<kappa> * x))\<^sup>2 \<le> (1 / 2)\<^sup>2" by (intro power_mono) simp_all
    thus ?thesis unfolding region1[OF 1] by (simp add: power_divide)
  next
    case 2
    show ?thesis unfolding region2[OF 2] by (simp add: power_divide)
  next
    case 3
    show ?thesis unfolding region3[OF 3] by (simp add: power2_eq_square)
  qed
qed

lemma fg_sq_mid: "1 / \<kappa> \<le> x \<or> (filt_f \<kappa> x)\<^sup>2 + (filt_g \<kappa> x)\<^sup>2 = 1 / 4"
proof -
  consider "1 / \<kappa> \<le> x" | "1 / (2 * \<kappa>) \<le> x" "x \<le> 1 / \<kappa>" | "x \<le> 1 / (2 * \<kappa>)" by linarith
  thus ?thesis
  proof cases
    case 2
    have "(sin (pi / 2 * (2 * \<kappa> * x - 1)) / 2)\<^sup>2 + (cos (pi / 2 * (2 * \<kappa> * x - 1)) / 2)\<^sup>2 = 1 / 4"
      by (simp add: power_divide)
    thus ?thesis unfolding region2[OF 2] by simp
  next
    case 3
    thus ?thesis unfolding region3[OF 3] by (simp add: power2_eq_square)
  qed simp
qed

end

lemma trig_pair_dist:
  fixes a b :: real
  shows "(sin a - sin b)\<^sup>2 + (cos a - cos b)\<^sup>2 \<le> (a - b)\<^sup>2"
proof -
  have alg: "(2 * S * c)\<^sup>2 + (2 * s * (- S))\<^sup>2 = 4 * S\<^sup>2 * (c\<^sup>2 + s\<^sup>2)" for S c s :: real
    by (simp add: power2_eq_square algebra_simps)
  have sneg: "sin ((b - a) / 2) = - sin ((a - b) / 2)" by (metis minus_diff_eq minus_divide_left sin_minus)
  have e: "(sin a - sin b)\<^sup>2 + (cos a - cos b)\<^sup>2 = 4 * (sin ((a - b) / 2))\<^sup>2 * ((cos ((a + b) / 2))\<^sup>2 + (sin ((a + b) / 2))\<^sup>2)"
    unfolding sin_diff_sin cos_diff_cos sneg by (rule alg)
  have one: "(cos ((a + b) / 2))\<^sup>2 + (sin ((a + b) / 2))\<^sup>2 = 1" by simp
  have "\<bar>sin ((a - b) / 2)\<bar>\<^sup>2 \<le> \<bar>(a - b) / 2\<bar>\<^sup>2" by (intro power_mono abs_sin_x_le_abs_x) simp
  hence "(sin ((a - b) / 2))\<^sup>2 \<le> ((a - b) / 2)\<^sup>2" by (simp only: power2_abs)
  hence "4 * (sin ((a - b) / 2))\<^sup>2 \<le> (a - b)\<^sup>2" by (simp add: power_divide)
  thus ?thesis unfolding e one by simp
qed

lemma vnorm_diff3_sq:
  assumes "dim_vec v = 3" "dim_vec w = 3"
  shows "\<parallel>v - w\<parallel>\<^sup>2 = (cmod (v $ 0 - w $ 0))\<^sup>2 + (cmod (v $ 1 - w $ 1))\<^sup>2 + (cmod (v $ 2 - w $ 2))\<^sup>2"
  unfolding vnorm_sq using assms by (simp add: numeral_3_eq_3 numeral_2_eq_2 lessThan_Suc)

context
  fixes \<kappa> :: real
  assumes k0: "0 < \<kappa>"
begin

lemma hflag_dist_sq:
  "\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel>\<^sup>2 = (filt_s \<kappa> a - filt_s \<kappa> b)\<^sup>2 + (filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2"
proof -
  have e: "cmod (complex_of_real x - complex_of_real y) = \<bar>x - y\<bar>" for x y by (metis norm_of_real of_real_diff)
  show ?thesis unfolding vnorm_diff3_sq[OF dim_hflag dim_hflag] by (simp add: hflag_def e)
qed

lemma filt_s_mid: "1 / \<kappa> \<le> x \<or> filt_s \<kappa> x = sqrt 3 / 2"
proof -
  have r: "sqrt (1 - 1 / 4) = sqrt 3 / 2" by (simp add: real_sqrt_divide)
  show ?thesis
  proof (cases "1 / \<kappa> \<le> x")
    case False
    hence "(filt_f \<kappa> x)\<^sup>2 + (filt_g \<kappa> x)\<^sup>2 = 1 / 4" using fg_sq_mid[OF k0, of x] by simp
    hence h: "1 - (filt_f \<kappa> x)\<^sup>2 - (filt_g \<kappa> x)\<^sup>2 = 1 - 1 / 4" by simp
    have "filt_s \<kappa> x = sqrt 3 / 2" by (simp only: filt_s_def h r)
    thus ?thesis by (rule disjI2)
  qed simp
qed

text \<open>Lemma 2 of the paper, region by region.\<close>

lemma lip_region1:
  assumes a: "1 / \<kappa> \<le> a" and b: "1 / \<kappa> \<le> b"
  shows "\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel> \<le> pi / 2 * \<kappa> * \<bar>a - b\<bar>"
proof -
  have a0: "0 < a" and b0: "0 < b" using a b k0 by (smt (verit) divide_pos_pos)+
  let ?fa = "1 / (2 * \<kappa> * a)" and ?fb = "1 / (2 * \<kappa> * b)"
  have fa: "filt_f \<kappa> a = ?fa" "filt_g \<kappa> a = 0" and fb: "filt_f \<kappa> b = ?fb" "filt_g \<kappa> b = 0"
    using region1[OF k0 a] region1[OF k0 b] by simp_all
  have fa12: "?fa \<le> 1 / 2" and fb12: "?fb \<le> 1 / 2"
  proof -
    have "1 \<le> \<kappa> * a" "1 \<le> \<kappa> * b" using a b k0 by (simp_all add: field_simps)
    thus "?fa \<le> 1 / 2" "?fb \<le> 1 / 2" using k0 by (simp_all add: field_simps)
  qed
  have fa0: "0 \<le> ?fa" and fb0: "0 \<le> ?fb" using a0 b0 k0 by simp_all
  have df: "\<bar>?fa - ?fb\<bar> \<le> \<kappa> / 2 * \<bar>a - b\<bar>"
  proof -
    have "?fa - ?fb = (b - a) / (2 * \<kappa> * a * b)" using a0 b0 k0 by (simp add: field_simps)
    hence "\<bar>?fa - ?fb\<bar> = \<bar>a - b\<bar> / (2 * \<kappa> * a * b)" using a0 b0 k0 by (simp add: abs_minus_commute)
    also have "\<dots> \<le> \<bar>a - b\<bar> / (2 * \<kappa> * (1 / \<kappa>) * (1 / \<kappa>))"
      using a b a0 b0 k0 by (intro divide_left_mono mult_mono) simp_all
    also have "\<dots> = \<kappa> / 2 * \<bar>a - b\<bar>" using k0 by (simp add: field_simps)
    finally show ?thesis .
  qed
  let ?sa = "sqrt (1 - ?fa\<^sup>2)" and ?sb = "sqrt (1 - ?fb\<^sup>2)"
  have sa: "filt_s \<kappa> a = ?sa" and sb: "filt_s \<kappa> b = ?sb" unfolding filt_s_def fa fb by simp_all
  have s3: "sqrt 3 / 2 \<le> ?sa" "sqrt 3 / 2 \<le> ?sb"
  proof -
    have "?fa\<^sup>2 \<le> 1 / 4" "?fb\<^sup>2 \<le> 1 / 4" using power_mono[OF fa12 fa0, of 2] power_mono[OF fb12 fb0, of 2] by (simp_all add: power_divide)
    hence "3 / 4 \<le> 1 - ?fa\<^sup>2" "3 / 4 \<le> 1 - ?fb\<^sup>2" by simp_all
    hence "sqrt (3 / 4) \<le> ?sa" "sqrt (3 / 4) \<le> ?sb" by (simp_all add: real_sqrt_le_mono)
    thus "sqrt 3 / 2 \<le> ?sa" "sqrt 3 / 2 \<le> ?sb" by (simp_all add: real_sqrt_divide)
  qed
  have ds: "(?sa - ?sb)\<^sup>2 \<le> (?fa - ?fb)\<^sup>2 / 3"
  proof -
    have sq: "?sa\<^sup>2 = 1 - ?fa\<^sup>2" "?sb\<^sup>2 = 1 - ?fb\<^sup>2" using fa12 fb12 fa0 fb0
      by (simp_all add: power_le_one real_sqrt_pow2 power_mono[of _ 1, simplified])
    have p: "(?sa - ?sb) * (?sa + ?sb) = (?fb - ?fa) * (?fb + ?fa)" using sq by (simp add: algebra_simps power2_eq_square)
    have spos: "sqrt 3 \<le> ?sa + ?sb" using s3 by simp
    have "\<bar>?sa - ?sb\<bar> * sqrt 3 \<le> \<bar>?sa - ?sb\<bar> * (?sa + ?sb)" by (intro mult_left_mono spos) simp
    also have "\<dots> = \<bar>?fb - ?fa\<bar> * \<bar>?fb + ?fa\<bar>"
    proof -
      have yp: "\<bar>?sa + ?sb\<bar> = ?sa + ?sb" by (rule abs_of_nonneg) (use s3 real_sqrt_ge_zero[of 3] in linarith)
      have "\<bar>?sa - ?sb\<bar> * (?sa + ?sb) = \<bar>(?sa - ?sb) * (?sa + ?sb)\<bar>" unfolding abs_mult yp ..
      thus ?thesis unfolding p abs_mult .
    qed
    also have "\<dots> \<le> \<bar>?fa - ?fb\<bar> * 1" using fa12 fb12 fa0 fb0 by (intro mult_mono) (simp_all add: abs_minus_commute)
    finally have "\<bar>?sa - ?sb\<bar> \<le> \<bar>?fa - ?fb\<bar> / sqrt 3" by (simp add: field_simps)
    hence "\<bar>?sa - ?sb\<bar>\<^sup>2 \<le> (\<bar>?fa - ?fb\<bar> / sqrt 3)\<^sup>2" by (intro power_mono) simp_all
    thus ?thesis by (simp add: power_divide)
  qed
  have "\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel>\<^sup>2 \<le> 4 / 3 * (?fa - ?fb)\<^sup>2"
    unfolding hflag_dist_sq sa sb fa fb using ds by simp
  also have "\<dots> \<le> 4 / 3 * (\<kappa> / 2 * \<bar>a - b\<bar>)\<^sup>2"
    using power_mono[OF df, of 2] by (simp add: power2_abs)
  also have "\<dots> \<le> (pi / 2 * \<kappa> * \<bar>a - b\<bar>)\<^sup>2"
  proof -
    have "4 / 3 * (1 / 2)\<^sup>2 \<le> (pi / 2)\<^sup>2" using pi_ge_two power_mono[OF pi_ge_two, of 2] by (simp add: power_divide)
    hence "4 / 3 * (1 / 2)\<^sup>2 * (\<kappa> * \<bar>a - b\<bar>)\<^sup>2 \<le> (pi / 2)\<^sup>2 * (\<kappa> * \<bar>a - b\<bar>)\<^sup>2" by (intro mult_right_mono) simp_all
    thus ?thesis by (simp add: power_mult_distrib power_divide algebra_simps)
  qed
  finally show ?thesis by (rule power2_le_imp_le) (use k0 in simp)
qed

lemma lip_region2:
  assumes a: "1 / (2 * \<kappa>) \<le> a" "a \<le> 1 / \<kappa>" and b: "1 / (2 * \<kappa>) \<le> b" "b \<le> 1 / \<kappa>"
  shows "\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel> \<le> pi / 2 * \<kappa> * \<bar>a - b\<bar>"
proof -
  have sa: "filt_s \<kappa> a = sqrt 3 / 2" and sb: "filt_s \<kappa> b = sqrt 3 / 2"
  proof -
    show "filt_s \<kappa> a = sqrt 3 / 2"
    proof (cases "a = 1 / \<kappa>")
      case True
      have e: "filt_f \<kappa> a = 1 / 2" "filt_g \<kappa> a = 0" using region1[OF k0, of a] True k0 by simp_all
      have r: "sqrt (1 - 1 / 4) = sqrt 3 / 2" by (simp add: real_sqrt_divide)
      have h: "1 - (filt_f \<kappa> a)\<^sup>2 - (filt_g \<kappa> a)\<^sup>2 = 1 - 1 / 4" unfolding e by (simp add: power_divide)
      show ?thesis by (simp only: filt_s_def h r)
    next
      case False thus ?thesis using filt_s_mid[of a] a by simp
    qed
    show "filt_s \<kappa> b = sqrt 3 / 2"
    proof (cases "b = 1 / \<kappa>")
      case True
      have e: "filt_f \<kappa> b = 1 / 2" "filt_g \<kappa> b = 0" using region1[OF k0, of b] True k0 by simp_all
      have r: "sqrt (1 - 1 / 4) = sqrt 3 / 2" by (simp add: real_sqrt_divide)
      have h: "1 - (filt_f \<kappa> b)\<^sup>2 - (filt_g \<kappa> b)\<^sup>2 = 1 - 1 / 4" unfolding e by (simp add: power_divide)
      show ?thesis by (simp only: filt_s_def h r)
    next
      case False thus ?thesis using filt_s_mid[of b] b by simp
    qed
  qed
  let ?A = "pi / 2 * (2 * \<kappa> * a - 1)" and ?B = "pi / 2 * (2 * \<kappa> * b - 1)"
  have "\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel>\<^sup>2 = ((sin ?A - sin ?B)\<^sup>2 + (cos ?A - cos ?B)\<^sup>2) / 4"
    unfolding hflag_dist_sq sa sb region2[OF k0 a] region2[OF k0 b] by (simp add: power_divide diff_divide_distrib[symmetric] add_divide_distrib)
  also have "\<dots> \<le> (?A - ?B)\<^sup>2 / 4" by (intro divide_right_mono trig_pair_dist) simp
  also have "(?A - ?B)\<^sup>2 / 4 = (pi / 2 * \<kappa> * \<bar>a - b\<bar>)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis by (rule power2_le_imp_le) (use k0 in simp)
qed

lemma lip_region3:
  assumes a: "a \<le> 1 / (2 * \<kappa>)" and b: "b \<le> 1 / (2 * \<kappa>)"
  shows "\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel> \<le> pi / 2 * \<kappa> * \<bar>a - b\<bar>"
proof -
  have "hflag \<kappa> a = hflag \<kappa> b" unfolding hflag_def filt_s_def region3[OF k0 a] region3[OF k0 b] ..
  thus ?thesis using k0 by (simp add: cpx_vec_length_def)
qed

text \<open>Gluing Lipschitz bounds at a common point.\<close>

lemma lip_glue:
  assumes l: "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> \<parallel>H a - H b\<parallel> \<le> L * \<bar>a - b\<bar>"
      and r: "\<And>a b. a \<in> T \<Longrightarrow> b \<in> T \<Longrightarrow> \<parallel>H a - H b\<parallel> \<le> L * \<bar>a - b\<bar>"
      and q: "q \<in> S" "q \<in> T" and dims: "\<And>x. dim_vec (H x) = d"
      and a: "a \<in> S" and b: "b \<in> T" and ab: "a \<le> q" "q \<le> b"
  shows "\<parallel>H a - H b\<parallel> \<le> L * \<bar>a - b\<bar>"
proof -
  have "\<parallel>H a - H b\<parallel> \<le> \<parallel>H a - H q\<parallel> + \<parallel>H q - H b\<parallel>" by (rule vnorm_diff_le[where n = d]) (simp_all add: dims)
  also have "\<dots> \<le> L * \<bar>a - q\<bar> + L * \<bar>q - b\<bar>" using l[OF a q(1)] r[OF q(2) b] by linarith
  also have "\<dots> = L * \<bar>a - b\<bar>" using ab by (simp add: algebra_simps)
  finally show ?thesis .
qed

end

lemma abs_split:
  fixes x y z L :: real
  assumes "x \<le> y" "y \<le> z"
  shows "L * \<bar>x - y\<bar> + L * \<bar>y - z\<bar> = L * \<bar>x - z\<bar>"
proof -
  have "\<bar>x - y\<bar> + \<bar>y - z\<bar> = \<bar>x - z\<bar>" using assms by linarith
  thus ?thesis by (metis distrib_left)
qed

context
  fixes \<kappa> :: real
  assumes k0: "0 < \<kappa>"
begin

lemma lemma2_le:
  assumes ab: "a \<le> b"
  shows "\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel> \<le> pi / 2 * \<kappa> * \<bar>a - b\<bar>"
proof -
  let ?L = "pi / 2 * \<kappa>" and ?H = "hflag \<kappa>"
  define \<mu> \<nu> where "\<mu> = 1 / \<kappa>" and "\<nu> = 1 / (2 * \<kappa>)"
  have nm: "\<nu> \<le> \<mu>" unfolding \<mu>_def \<nu>_def using k0 by (simp add: field_simps)
  note R1 = lip_region1[OF k0, folded \<mu>_def] and R2 = lip_region2[OF k0, folded \<mu>_def \<nu>_def]
    and R3 = lip_region3[OF k0, folded \<nu>_def]
  have tri: "\<parallel>?H x - ?H z\<parallel> \<le> \<parallel>?H x - ?H y\<parallel> + \<parallel>?H y - ?H z\<parallel>" for x y z
    by (rule vnorm_diff_le[where n = 3]) simp_all
  consider "b \<le> \<nu>" | "\<nu> \<le> a" "b \<le> \<mu>" | "\<mu> \<le> a" | "a \<le> \<nu>" "\<nu> \<le> b" "b \<le> \<mu>"
         | "\<nu> \<le> a" "a \<le> \<mu>" "\<mu> \<le> b" | "a \<le> \<nu>" "\<mu> \<le> b"
    using nm by linarith
  thus ?thesis
  proof cases
    case 1 show ?thesis by (rule R3) (use 1 ab in linarith)+
  next
    case 2 show ?thesis by (rule R2) (use 2 ab in linarith)+
  next
    case 3 show ?thesis by (rule R1) (use 3 ab in linarith)+
  next
    case 4
    have "\<parallel>?H a - ?H \<nu>\<parallel> \<le> ?L * \<bar>a - \<nu>\<bar>" by (rule R3) (use 4 in linarith)+
    moreover have "\<parallel>?H \<nu> - ?H b\<parallel> \<le> ?L * \<bar>\<nu> - b\<bar>" by (rule R2) (use 4 in linarith)+
    ultimately have "\<parallel>?H a - ?H b\<parallel> \<le> ?L * \<bar>a - \<nu>\<bar> + ?L * \<bar>\<nu> - b\<bar>" using tri[where x = a and y = \<nu> and z = b] by linarith
    thus ?thesis using abs_split[of a \<nu> b ?L] 4 by simp
  next
    case 5
    have "\<parallel>?H a - ?H \<mu>\<parallel> \<le> ?L * \<bar>a - \<mu>\<bar>" by (rule R2) (use 5 nm in linarith)+
    moreover have "\<parallel>?H \<mu> - ?H b\<parallel> \<le> ?L * \<bar>\<mu> - b\<bar>" by (rule R1) (use 5 in linarith)+
    ultimately have "\<parallel>?H a - ?H b\<parallel> \<le> ?L * \<bar>a - \<mu>\<bar> + ?L * \<bar>\<mu> - b\<bar>" using tri[where x = a and y = \<mu> and z = b] by linarith
    thus ?thesis using abs_split[of a \<mu> b ?L] 5 by simp
  next
    case 6
    have "\<parallel>?H a - ?H b\<parallel> \<le> \<parallel>?H a - ?H \<nu>\<parallel> + (\<parallel>?H \<nu> - ?H \<mu>\<parallel> + \<parallel>?H \<mu> - ?H b\<parallel>)"
      using tri[where x = a and y = \<nu> and z = b] tri[where x = \<nu> and y = \<mu> and z = b] by linarith
    also have "\<dots> \<le> ?L * \<bar>a - \<nu>\<bar> + (?L * \<bar>\<nu> - \<mu>\<bar> + ?L * \<bar>\<mu> - b\<bar>)"
    proof (intro add_mono)
      show "\<parallel>?H a - ?H \<nu>\<parallel> \<le> ?L * \<bar>a - \<nu>\<bar>" by (rule R3) (use 6 in linarith)+
      show "\<parallel>?H \<nu> - ?H \<mu>\<parallel> \<le> ?L * \<bar>\<nu> - \<mu>\<bar>" by (rule R2) (use nm in linarith)+
      show "\<parallel>?H \<mu> - ?H b\<parallel> \<le> ?L * \<bar>\<mu> - b\<bar>" by (rule R1) (use 6 in linarith)+
    qed
    finally show ?thesis using abs_split[of \<nu> \<mu> b ?L] abs_split[of a \<nu> b ?L] 6 nm by simp
  qed
qed

text \<open>Lemma 2 of the paper: $\lambda\mapsto\ket{h(\lambda)}$ is $\frac\pi2\kappa$-Lipschitz.\<close>

theorem hflag_lipschitz: "\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel> \<le> pi / 2 * \<kappa> * \<bar>a - b\<bar>"
proof (cases "a \<le> b")
  case True thus ?thesis by (rule lemma2_le)
next
  case False
  hence "\<parallel>hflag \<kappa> b - hflag \<kappa> a\<parallel> \<le> pi / 2 * \<kappa> * \<bar>b - a\<bar>" by (intro lemma2_le) simp
  thus ?thesis by (simp add: vnorm_minus_commute[of "hflag \<kappa> a"] abs_minus_commute)
qed

lemma fg_dist_le: "sqrt ((filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2) \<le> pi / 2 * \<kappa> * \<bar>a - b\<bar>"
proof -
  have "sqrt ((filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2) \<le> sqrt (\<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel>\<^sup>2)"
    unfolding hflag_dist_sq[OF k0] by (intro real_sqrt_le_mono) simp
  also have "\<dots> = \<parallel>hflag \<kappa> a - hflag \<kappa> b\<parallel>" using vnorm_ge0 by simp
  finally show ?thesis using hflag_lipschitz[of a b] by linarith
qed

end

lemma pi_sq_lt_16: "pi\<^sup>2 < 16"
proof -
  have "pi * pi < 4 * 4" by (rule mult_strict_mono) (use pi_less_4 pi_gt_zero in auto)
  thus ?thesis by (simp add: power2_eq_square)
qed

context
  fixes \<kappa> :: real
  assumes k0: "0 < \<kappa>"
begin

definition fg_pt :: "real \<Rightarrow> complex" where
  "fg_pt x = Complex (filt_f \<kappa> x) (filt_g \<kappa> x)"

lemma fg_pt_dist: "cmod (fg_pt a - fg_pt b) = sqrt ((filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2)"
  by (simp add: fg_pt_def cmod_def)

text \<open>Lemma 3 of the paper, with the constant $\pi^2$.  The paper states $c=\pi^2/2$; that is
false: in the middle region $f^2+g^2=\tfrac14$ (the proof uses $\tfrac12$) and the ratio of the two
sides tends to $\pi^2$.\<close>

theorem lemma3:
  "(filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2
     \<le> pi\<^sup>2 * \<kappa>\<^sup>2 * (a - b)\<^sup>2 * ((filt_f \<kappa> a)\<^sup>2 + (filt_g \<kappa> a)\<^sup>2)"
proof -
  let ?D = "(filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2"
  define \<mu> \<nu> where "\<mu> = 1 / \<kappa>" and "\<nu> = 1 / (2 * \<kappa>)"
  have nm: "\<nu> < \<mu>" unfolding \<mu>_def \<nu>_def using k0 by (simp add: field_simps)
  have m0: "0 < \<mu>" and n0: "0 < \<nu>" unfolding \<mu>_def \<nu>_def using k0 by simp_all
  have D0: "0 \<le> ?D" by simp
  have Dlip: "?D \<le> (pi / 2 * \<kappa> * \<bar>a - b\<bar>)\<^sup>2"
  proof -
    have "sqrt ?D \<le> pi / 2 * \<kappa> * \<bar>a - b\<bar>" by (rule fg_dist_le[OF k0])
    hence "(sqrt ?D)\<^sup>2 \<le> (pi / 2 * \<kappa> * \<bar>a - b\<bar>)\<^sup>2" by (intro power_mono) simp_all
    thus ?thesis using D0 by simp
  qed
  show ?thesis
  proof (cases "\<mu> \<le> a")
    case False
    hence q: "(filt_f \<kappa> a)\<^sup>2 + (filt_g \<kappa> a)\<^sup>2 = 1 / 4" using fg_sq_mid[OF k0, of a] unfolding \<mu>_def by simp
    have "(pi / 2 * \<kappa> * \<bar>a - b\<bar>)\<^sup>2 = pi\<^sup>2 * \<kappa>\<^sup>2 * (a - b)\<^sup>2 * (1 / 4)"
      by (simp add: power_mult_distrib power2_abs power_divide)
    thus ?thesis unfolding q using Dlip by simp
  next
    case a: True
    have a0: "0 < a" using a m0 by linarith
    have fa: "filt_f \<kappa> a = 1 / (2 * \<kappa> * a)" "filt_g \<kappa> a = 0" using region1[OF k0, of a] a unfolding \<mu>_def by simp_all
    have rhs: "pi\<^sup>2 * \<kappa>\<^sup>2 * (a - b)\<^sup>2 * ((filt_f \<kappa> a)\<^sup>2 + (filt_g \<kappa> a)\<^sup>2) = (pi * \<bar>a - b\<bar> / (2 * a))\<^sup>2"
      unfolding fa using k0 a0 by (simp add: power_mult_distrib power_divide power2_abs field_simps)
    show ?thesis
    proof (cases "\<mu> \<le> b")
      case b: True
      have b0: "0 < b" using b m0 by linarith
      have fb: "filt_f \<kappa> b = 1 / (2 * \<kappa> * b)" "filt_g \<kappa> b = 0" using region1[OF k0, of b] b unfolding \<mu>_def by simp_all
      have df: "\<bar>1 / (2 * \<kappa> * a) - 1 / (2 * \<kappa> * b)\<bar> \<le> \<bar>a - b\<bar> / (2 * a)"
      proof -
        have "1 / (2 * \<kappa> * a) - 1 / (2 * \<kappa> * b) = (b - a) / (2 * a * (\<kappa> * b))" using k0 a0 b0 by (simp add: field_simps)
        hence "\<bar>1 / (2 * \<kappa> * a) - 1 / (2 * \<kappa> * b)\<bar> = \<bar>a - b\<bar> / (2 * a * (\<kappa> * b))" using k0 a0 b0 by (simp add: abs_minus_commute)
        also have "\<dots> \<le> \<bar>a - b\<bar> / (2 * a * 1)"
        proof (rule divide_left_mono)
          show "2 * a * 1 \<le> 2 * a * (\<kappa> * b)" using b k0 a0 unfolding \<mu>_def by (simp add: field_simps)
        qed (use a0 k0 b0 in simp_all)
        finally show ?thesis by simp
      qed
      have "?D = (1 / (2 * \<kappa> * a) - 1 / (2 * \<kappa> * b))\<^sup>2" unfolding fa fb by simp
      also have "\<dots> \<le> (\<bar>a - b\<bar> / (2 * a))\<^sup>2" using power_mono[OF df, of 2] by (simp add: power2_abs)
      also have "\<dots> \<le> (pi * \<bar>a - b\<bar> / (2 * a))\<^sup>2"
      proof -
        have "1 * \<bar>a - b\<bar> \<le> pi * \<bar>a - b\<bar>" using pi_ge_two by (intro mult_right_mono) simp_all
        thus ?thesis using a0 by (intro power_mono divide_right_mono) simp_all
      qed
      finally show ?thesis unfolding rhs .
    next
      case b: False
      define b' where "b' = max b \<nu>"
      have b'1: "\<nu> \<le> b'" and b'2: "b' < \<mu>" and bb: "b \<le> b'" using b nm unfolding b'_def by auto
      have fgb: "filt_f \<kappa> b = filt_f \<kappa> b'" "filt_g \<kappa> b = filt_g \<kappa> b'"
      proof -
        have "filt_f \<kappa> b = filt_f \<kappa> b' \<and> filt_g \<kappa> b = filt_g \<kappa> b'"
        proof (cases "b \<le> \<nu>")
          case le: True
          hence bn: "b' = \<nu>" unfolding b'_def by simp
          have "filt_f \<kappa> b = 0" "filt_g \<kappa> b = 1 / 2" using region3[OF k0, of b] le unfolding \<nu>_def by simp_all
          moreover have "filt_f \<kappa> \<nu> = 0" "filt_g \<kappa> \<nu> = 1 / 2" using region3[OF k0, of \<nu>] unfolding \<nu>_def by simp_all
          ultimately show ?thesis unfolding bn by simp
        next
          case gt: False
          hence "b' = b" unfolding b'_def by simp
          thus ?thesis by simp
        qed
        thus "filt_f \<kappa> b = filt_f \<kappa> b'" "filt_g \<kappa> b = filt_g \<kappa> b'" by simp_all
      qed
      define p q where "p = a - \<mu>" and "q = \<mu> - b'"
      have p0: "0 \<le> p" and q0: "0 < q" and q2: "q \<le> \<mu> / 2" unfolding p_def q_def using a b'1 b'2 \<nu>_def \<mu>_def by (simp_all add: field_simps)
      have fm: "filt_f \<kappa> \<mu> = 1 / 2" "filt_g \<kappa> \<mu> = 0" using region1[OF k0, of \<mu>] k0 unfolding \<mu>_def by simp_all
      have d1: "cmod (fg_pt a - fg_pt \<mu>) = p / (2 * a)"
      proof -
        have "1 / (2 * \<kappa> * a) - 1 / 2 = - (p / (2 * a))" unfolding p_def \<mu>_def using k0 a0 by (simp add: field_simps)
        moreover have "0 \<le> p / (2 * a)" using p0 a0 by simp
        ultimately show ?thesis unfolding fg_pt_dist fa fm using p0 a0 by simp
      qed
      have d2: "cmod (fg_pt \<mu> - fg_pt b') \<le> pi / (2 * \<mu>) * q"
      proof -
        have aq: "\<bar>\<mu> - b'\<bar> = q" unfolding q_def using b'2 by simp
        have kk: "\<kappa> = 1 / \<mu>" unfolding \<mu>_def using k0 by simp
        have "cmod (fg_pt \<mu> - fg_pt b') \<le> pi / 2 * \<kappa> * \<bar>\<mu> - b'\<bar>" unfolding fg_pt_dist by (rule fg_dist_le[OF k0])
        also have "\<dots> = pi / (2 * \<mu>) * q" unfolding aq kk by simp
        finally show ?thesis .
      qed
      have tri: "cmod (fg_pt a - fg_pt b') \<le> p / (2 * a) + pi / (2 * \<mu>) * q"
        using norm_triangle_ineq[of "fg_pt a - fg_pt \<mu>" "fg_pt \<mu> - fg_pt b'"] d1 d2 by simp
      have key: "p / (2 * a) + pi / (2 * \<mu>) * q \<le> pi * (p + q) / (2 * a)"
      proof -
        have "pi * q * p \<le> (pi - 1) * p * \<mu>"
        proof -
          have "pi * q \<le> pi * (\<mu> / 2)" by (rule mult_left_mono[OF q2]) simp
          moreover have "0 \<le> (pi / 2 - 1) * \<mu>" using pi_ge_two m0 by (intro mult_nonneg_nonneg) simp_all
          moreover have "(pi - 1) * \<mu> - pi * (\<mu> / 2) = (pi / 2 - 1) * \<mu>" by (simp add: algebra_simps)
          ultimately have "pi * q \<le> (pi - 1) * \<mu>" by linarith
          thus ?thesis using p0 by (metis mult.commute mult.left_commute mult_left_mono)
        qed
        hence "p * \<mu> + pi * q * a \<le> pi * (p + q) * \<mu>" unfolding p_def by (simp add: algebra_simps)
        hence "(p * \<mu> + pi * q * a) / (2 * a * \<mu>) \<le> pi * (p + q) * \<mu> / (2 * a * \<mu>)"
          using a0 m0 by (intro divide_right_mono) simp_all
        moreover have "(p * \<mu> + pi * q * a) / (2 * a * \<mu>) = p / (2 * a) + pi / (2 * \<mu>) * q" using a0 m0 by (simp add: field_simps)
        moreover have "pi * (p + q) * \<mu> / (2 * a * \<mu>) = pi * (p + q) / (2 * a)" using a0 m0 by (simp add: field_simps)
        ultimately show ?thesis by simp
      qed
      have "?D = (cmod (fg_pt a - fg_pt b'))\<^sup>2" unfolding fg_pt_dist fgb by simp
      also have "\<dots> \<le> (pi * (p + q) / (2 * a))\<^sup>2" using tri key by (intro power_mono) simp_all
      also have "\<dots> \<le> (pi * \<bar>a - b\<bar> / (2 * a))\<^sup>2"
      proof -
        have "p + q \<le> \<bar>a - b\<bar>" unfolding p_def q_def using bb a b'2 by linarith
        thus ?thesis using p0 q0 a0 by (intro power_mono divide_right_mono mult_left_mono) simp_all
      qed
      finally show ?thesis unfolding rhs .
    qed
  qed
qed

text \<open>The paper's constant fails at $\lambda=1/(2\kappa)$, $\tilde\lambda=1/\kappa$; $\pi^2$ is sharp.\<close>

theorem lemma3_paper_constant:
  "pi\<^sup>2 / 2 * \<kappa>\<^sup>2 * (1 / (2 * \<kappa>) - 1 / \<kappa>)\<^sup>2 * ((filt_f \<kappa> (1 / (2 * \<kappa>)))\<^sup>2 + (filt_g \<kappa> (1 / (2 * \<kappa>)))\<^sup>2)
   < (filt_f \<kappa> (1 / (2 * \<kappa>)) - filt_f \<kappa> (1 / \<kappa>))\<^sup>2 + (filt_g \<kappa> (1 / (2 * \<kappa>)) - filt_g \<kappa> (1 / \<kappa>))\<^sup>2"
proof -
  have fa: "filt_f \<kappa> (1 / (2 * \<kappa>)) = 0" "filt_g \<kappa> (1 / (2 * \<kappa>)) = 1 / 2"
    using region3[OF k0, of "1 / (2 * \<kappa>)"] by simp_all
  have fb: "filt_f \<kappa> (1 / \<kappa>) = 1 / 2" "filt_g \<kappa> (1 / \<kappa>) = 0"
    using region1[OF k0, of "1 / \<kappa>"] k0 by simp_all
  have d: "\<kappa>\<^sup>2 * (1 / (2 * \<kappa>) - 1 / \<kappa>)\<^sup>2 = 1 / 4"
  proof -
    have e: "\<kappa> * (1 / (2 * \<kappa>) - 1 / \<kappa>) = - (1 / 2)" using k0 by (simp add: field_simps)
    have "\<kappa>\<^sup>2 * (1 / (2 * \<kappa>) - 1 / \<kappa>)\<^sup>2 = (\<kappa> * (1 / (2 * \<kappa>) - 1 / \<kappa>))\<^sup>2" by (simp only: power_mult_distrib)
    also have "\<dots> = 1 / 4" unfolding e by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  have L: "pi\<^sup>2 / 2 * \<kappa>\<^sup>2 * (1 / (2 * \<kappa>) - 1 / \<kappa>)\<^sup>2 * ((filt_f \<kappa> (1 / (2 * \<kappa>)))\<^sup>2 + (filt_g \<kappa> (1 / (2 * \<kappa>)))\<^sup>2)
           = pi\<^sup>2 / 32"
  proof -
    have "pi\<^sup>2 / 2 * \<kappa>\<^sup>2 * (1 / (2 * \<kappa>) - 1 / \<kappa>)\<^sup>2 * ((filt_f \<kappa> (1 / (2 * \<kappa>)))\<^sup>2 + (filt_g \<kappa> (1 / (2 * \<kappa>)))\<^sup>2)
          = pi\<^sup>2 / 2 * (\<kappa>\<^sup>2 * (1 / (2 * \<kappa>) - 1 / \<kappa>)\<^sup>2) * (1 / 4)" unfolding fa by (simp add: power2_eq_square)
    also have "\<dots> = pi\<^sup>2 / 32" unfolding d by simp
    finally show ?thesis .
  qed
  have R: "(filt_f \<kappa> (1 / (2 * \<kappa>)) - filt_f \<kappa> (1 / \<kappa>))\<^sup>2 + (filt_g \<kappa> (1 / (2 * \<kappa>)) - filt_g \<kappa> (1 / \<kappa>))\<^sup>2 = 1 / 2"
    unfolding fa fb by (simp add: power2_eq_square)
  show ?thesis unfolding L R using pi_sq_lt_16 by simp
qed

theorem lemma3_sharp:
  assumes c: "c < pi\<^sup>2"
  shows "\<exists>a b. c * \<kappa>\<^sup>2 * (a - b)\<^sup>2 * ((filt_f \<kappa> a)\<^sup>2 + (filt_g \<kappa> a)\<^sup>2)
                < (filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2"
proof -
  define r where "r = c / pi\<^sup>2"
  have r1: "r < 1" using c by (simp add: r_def)
  define w where "w = min (pi / 4) (sqrt (3 * (1 - r)) / 2)"
  have w0: "0 < w" using r1 pi_gt_zero by (simp add: w_def)
  have w4: "w \<le> pi / 4" by (simp add: w_def)
  have w1: "w < 1" using w4 pi_less_4 by linarith
  have ww: "w\<^sup>2 < 3 * (1 - r)"
  proof -
    have "w \<le> sqrt (3 * (1 - r)) / 2" by (simp add: w_def)
    hence "w\<^sup>2 \<le> (sqrt (3 * (1 - r)) / 2)\<^sup>2" using w0 by (intro power_mono) simp_all
    also have "\<dots> = 3 * (1 - r) / 4" using r1 by (simp add: power_divide)
    finally have "w\<^sup>2 \<le> 3 * (1 - r) / 4" .
    moreover have "3 * (1 - r) / 4 < 3 * (1 - r)" using r1 by simp
    ultimately show ?thesis by (rule le_less_trans)
  qed
  have sb: "w - w ^ 3 / 6 \<le> sin w"
  proof -
    have "\<bar>sin w - (\<Sum>m<3. sin_coeff m * w ^ m)\<bar> \<le> inverse (fact 3) * \<bar>w\<bar> ^ 3" by (rule Maclaurin_sin_bound)
    moreover have "(\<Sum>m<3. sin_coeff m * w ^ m) = w" by (simp add: numeral_3_eq_3 sin_coeff_def)
    moreover have "inverse (fact 3 :: real) = 1 / 6" by (simp add: fact_numeral)
    ultimately have "\<bar>sin w - w\<bar> \<le> w ^ 3 / 6" using w0 by simp
    thus ?thesis unfolding abs_le_iff by linarith
  qed
  have w2: "w\<^sup>2 < 1" using w0 w1 by (simp add: power2_eq_square) (metis mult_strict_mono' less_eq_real_def mult_1 w0)
  have sq: "w\<^sup>2 * r < (sin w)\<^sup>2"
  proof -
    have "w\<^sup>2 * r < w\<^sup>2 * (1 - w\<^sup>2 / 3)" using ww w0 by (intro mult_strict_left_mono) simp_all
    also have "\<dots> \<le> w\<^sup>2 * (1 - w\<^sup>2 / 6)\<^sup>2"
    proof (rule mult_left_mono)
      have "(1 - w\<^sup>2 / 6)\<^sup>2 = 1 - w\<^sup>2 / 3 + (w\<^sup>2)\<^sup>2 / 36" by (simp add: power2_eq_square field_simps)
      thus "1 - w\<^sup>2 / 3 \<le> (1 - w\<^sup>2 / 6)\<^sup>2" by simp
    qed simp
    also have "\<dots> = (w - w ^ 3 / 6)\<^sup>2" by (simp add: power2_eq_square power3_eq_cube field_simps)
    also have "\<dots> \<le> (sin w)\<^sup>2"
    proof (rule power_mono[OF sb])
      have "w ^ 3 = w * w\<^sup>2" by (simp add: power2_eq_square power3_eq_cube)
      hence "w ^ 3 / 6 \<le> w" using w0 w2 by (simp add: mult_le_cancel_left1)
      thus "0 \<le> w - w ^ 3 / 6" by simp
    qed
    finally show ?thesis .
  qed
  define a where "a = 1 / (2 * \<kappa>)"
  define b where "b = (1 + 4 * w / pi) / (2 * \<kappa>)"
  have ab: "a \<le> b" "b \<le> 1 / \<kappa>"
  proof -
    show "a \<le> b" using w0 k0 pi_gt_zero by (simp add: a_def b_def divide_right_mono)
    have "4 * w / pi \<le> 1" using w4 pi_gt_zero by (simp add: field_simps)
    hence "(1 + 4 * w / pi) / (2 * \<kappa>) \<le> 2 / (2 * \<kappa>)" using k0 by (intro divide_right_mono) simp_all
    thus "b \<le> 1 / \<kappa>" using k0 by (simp add: b_def)
  qed
  have fa: "filt_f \<kappa> a = 0" "filt_g \<kappa> a = 1 / 2" using region3[OF k0, of a] by (simp_all add: a_def)
  have th: "pi / 2 * (2 * \<kappa> * b - 1) = 2 * w" using k0 pi_gt_zero by (simp add: b_def field_simps)
  have fb: "filt_f \<kappa> b = sin (2 * w) / 2" "filt_g \<kappa> b = cos (2 * w) / 2"
    using region2[OF k0, of b] ab unfolding th by (simp_all add: a_def)
  have lhs: "(filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2 = (sin w)\<^sup>2"
  proof -
    have "(0 - sin (2 * w) / 2)\<^sup>2 + (1 / 2 - cos (2 * w) / 2)\<^sup>2 = ((sin (2 * w))\<^sup>2 + (cos (2 * w))\<^sup>2 + 1 - 2 * cos (2 * w)) / 4"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> = (1 - cos (2 * w)) / 2" by simp
    also have "\<dots> = (sin w)\<^sup>2" by (simp add: cos_double_sin)
    finally show ?thesis unfolding fa fb .
  qed
  have ab2: "\<kappa>\<^sup>2 * (a - b)\<^sup>2 = 4 * w\<^sup>2 / pi\<^sup>2"
  proof -
    have e: "\<kappa> * (a - b) = - (2 * w / pi)" using k0 pi_gt_zero by (simp add: a_def b_def field_simps)
    have "\<kappa>\<^sup>2 * (a - b)\<^sup>2 = (\<kappa> * (a - b))\<^sup>2" by (simp only: power_mult_distrib)
    also have "\<dots> = 4 * w\<^sup>2 / pi\<^sup>2" unfolding e by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  have rhs: "c * \<kappa>\<^sup>2 * (a - b)\<^sup>2 * ((filt_f \<kappa> a)\<^sup>2 + (filt_g \<kappa> a)\<^sup>2) = w\<^sup>2 * r"
  proof -
    have "c * \<kappa>\<^sup>2 * (a - b)\<^sup>2 * ((filt_f \<kappa> a)\<^sup>2 + (filt_g \<kappa> a)\<^sup>2) = c * (\<kappa>\<^sup>2 * (a - b)\<^sup>2) * (1 / 4)"
      unfolding fa by (simp add: power2_eq_square)
    also have "\<dots> = w\<^sup>2 * r" unfolding ab2 r_def using pi_gt_zero by simp
    finally show ?thesis .
  qed
  show ?thesis by (rule exI[of _ a], rule exI[of _ b]) (simp only: lhs rhs sq)
qed

end

subsection \<open>A $d$-level flag register\<close>

definition hhl_Wd :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "hhl_Wd A t0 N d = pe_unitary N (dim_row A * d) (evolution A t0 \<Otimes> 1\<^sub>m d)"

definition flag_circuit :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "flag_circuit A t0 N d G = (hhl_Wd A t0 N d)\<^sup>\<dagger> * (ctrl_blocks N (dim_row A * d) (\<lambda>k. 1\<^sub>m (dim_row A) \<Otimes> G k) * hhl_Wd A t0 N d)"

context
  fixes A :: "complex Matrix.mat" and n N :: nat and t0 l :: real and u :: "complex Matrix.vec"
    and psi :: "complex Matrix.vec" and d :: nat and G :: "nat \<Rightarrow> complex Matrix.mat" and hid :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
      and psi: "dim_vec psi = N" and d0: "0 < d" and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat d d"
      and hd: "dim_vec hid = d"
begin

text \<open>The phase of $u$, the register amplitudes and the flag vectors of the branches.\<close>

abbreviation "dphi \<equiv> hhl_phi t0 l"
definition "dalpha = Matrix.vec N (pe_amp_reg N psi dphi)"
abbreviation "fbr k \<equiv> G k *\<^sub>v unit_vec d 0"

lemma phi_phase_d: "cis (t0 * l) = cis (2 * pi * dphi)"
  unfolding hhl_phi_def by simp

lemma dim_alpha_d [simp]: "dim_vec dalpha = N" by (simp add: dalpha_def)
lemma dim_hid: "dim_vec hid = d" by (rule hd)
lemma Gblk: "k < N \<Longrightarrow> 1\<^sub>m n \<Otimes> G k \<in> carrier_mat (n * d) (n * d)"
  using G[of k] by (intro carrier_matI) auto

lemma W_branch_d:
  assumes w: "dim_vec w = d"
  shows "hhl_Wd A t0 N d *\<^sub>v tensor_vec psi (tensor_vec u w) = tensor_vec dalpha (tensor_vec u w)"
proof -
  let ?E = "evolution A t0" and ?V = "evolution A t0 \<Otimes> 1\<^sub>m d"
  have nA: "dim_row A = n" using A(1) by simp
  have Ec: "?E \<in> carrier_mat n n" using A by (rule evolution_carrier)
  have Vc: "?V \<in> carrier_mat (n * d) (n * d)" using Ec by (intro carrier_matI) auto
  have uw: "dim_vec (tensor_vec u w) = n * d" by (rule tensor_vec_dim[OF u w])
  have Vev: "?V *\<^sub>v tensor_vec u w = cis (2 * pi * dphi) \<cdot>\<^sub>v tensor_vec u w"
  proof -
    have "?V *\<^sub>v tensor_vec u w = tensor_vec (?E *\<^sub>v u) (1\<^sub>m d *\<^sub>v w)"
      by (rule tensor_mat_vec_mult[OF Ec one_carrier_mat u w])
    also have "?E *\<^sub>v u = cis (t0 * l) \<cdot>\<^sub>v u" by (rule evolution_eigen[OF A u ev])
    also have "1\<^sub>m d *\<^sub>v w = w" using carrier_vecI[OF w] by simp
    finally show ?thesis unfolding phi_phase_d using tensor_vec_smult_left[OF u w] by simp
  qed
  have Fc: "((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m (n * d) \<in> carrier_mat (N * (n * d)) (N * (n * d))" by (rule carrier_matI) simp_all
  have xc: "tensor_vec psi (tensor_vec u w) \<in> carrier_vec (N * (n * d))"
    by (rule carrier_vecI, rule tensor_vec_dim) (simp_all add: psi uw)
  have "hhl_Wd A t0 N d *\<^sub>v tensor_vec psi (tensor_vec u w) =
        (((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m (n * d)) *\<^sub>v (ctrl_pow N (n * d) ?V *\<^sub>v tensor_vec psi (tensor_vec u w))"
    unfolding hhl_Wd_def pe_unitary_def nA by (rule assoc_mult_mat_vec[OF Fc ctrl_pow_carrier xc])
  also have "\<dots> = tensor_vec dalpha (tensor_vec u w)"
    unfolding dalpha_def by (rule phase_estimation_reg[OF Vc uw Vev psi])
  finally show ?thesis .
qed

lemma hhl_Wd_carrier: "hhl_Wd A t0 N d \<in> carrier_mat (N * (n * d)) (N * (n * d))"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  show ?thesis unfolding hhl_Wd_def nA by simp
qed

lemma hhl_Wd_unitary: "unitary (hhl_Wd A t0 N d)"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have Ec: "evolution A t0 \<in> carrier_mat n n" using A by (rule evolution_carrier)
  have Vc: "evolution A t0 \<Otimes> 1\<^sub>m d \<in> carrier_mat (n * d) (n * d)" using Ec by (intro carrier_matI) auto
  have Vu: "unitary (evolution A t0 \<Otimes> 1\<^sub>m d)" by (rule tensor_mat_unitary_one_right) (rule evolution_unitary[OF A])
  show ?thesis unfolding hhl_Wd_def nA by (rule pe_unitary_unitary[OF N Vc Vu])
qed

text \<open>The output of the circuit and the ideal output as register sums.\<close>

lemma flag_output_branches:
  "flag_circuit A t0 N d G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec d 0)) =
   (hhl_Wd A t0 N d)\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k))"
proof -
  let ?W = "hhl_Wd A t0 N d" and ?CR = "ctrl_blocks N (n * d) (\<lambda>k. 1\<^sub>m n \<Otimes> G k)"
  have nA: "dim_row A = n" using A(1) by simp
  have Wc: "?W \<in> carrier_mat (N * (n * d)) (N * (n * d))" unfolding hhl_Wd_def nA by simp
  have CRc: "?CR \<in> carrier_mat (N * (n * d)) (N * (n * d))" by simp
  have u0: "dim_vec (tensor_vec u (unit_vec d 0)) = n * d" by (rule tensor_vec_dim[OF u]) (simp add: hd)
  have x0: "tensor_vec psi (tensor_vec u (unit_vec d 0)) \<in> carrier_vec (N * (n * d))"
    by (rule carrier_vecI, rule tensor_vec_dim) (simp_all add: psi u0)
  have br: "(1\<^sub>m n \<Otimes> G k) *\<^sub>v (dalpha $ k \<cdot>\<^sub>v tensor_vec u (unit_vec d 0)) = dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k)" if k: "k < N" for k
  proof -
    have "(1\<^sub>m n \<Otimes> G k) *\<^sub>v (dalpha $ k \<cdot>\<^sub>v tensor_vec u (unit_vec d 0)) =
          dalpha $ k \<cdot>\<^sub>v ((1\<^sub>m n \<Otimes> G k) *\<^sub>v tensor_vec u (unit_vec d 0))"
      by (rule mult_mat_vec[OF Gblk[OF k] carrier_vecI[OF u0]])
    also have "(1\<^sub>m n \<Otimes> G k) *\<^sub>v tensor_vec u (unit_vec d 0) = tensor_vec (1\<^sub>m n *\<^sub>v u) (fbr k)"
      by (rule tensor_mat_vec_mult[OF one_carrier_mat G[OF k] u]) simp
    also have "1\<^sub>m n *\<^sub>v u = u" using carrier_vecI[OF u] by simp
    finally show ?thesis .
  qed
  have "flag_circuit A t0 N d G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec d 0)) =
        ?W\<^sup>\<dagger> *\<^sub>v (?CR *\<^sub>v (?W *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec d 0))))"
    unfolding flag_circuit_def nA
    using assoc_mult_mat_vec[OF dagger_carrier[OF Wc] mult_carrier_mat[OF CRc Wc] x0] assoc_mult_mat_vec[OF CRc Wc x0]
    by simp
  also have "?W *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec d 0)) = tensor_vec dalpha (tensor_vec u (unit_vec d 0))"
    by (rule W_branch_d) simp
  also have "\<dots> = reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (unit_vec d 0))"
    by (rule tensor_reg_sum[OF dim_alpha_d u0])
  also have "?CR *\<^sub>v \<dots> = reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k))"
    by (subst ctrl_blocks_reg_sum) (simp_all add: u0 Gblk br cong: reg_sum_cong)
  finally show ?thesis .
qed

lemma flag_ideal_branches:
  "tensor_vec psi (tensor_vec u hid) =
   (hhl_Wd A t0 N d)\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u hid)"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have Wc: "hhl_Wd A t0 N d \<in> carrier_mat (N * (n * d)) (N * (n * d))" unfolding hhl_Wd_def nA by simp
  have Wu: "unitary (hhl_Wd A t0 N d)"
  proof -
    have Ec: "evolution A t0 \<in> carrier_mat n n" using A by (rule evolution_carrier)
    have Vc: "evolution A t0 \<Otimes> 1\<^sub>m d \<in> carrier_mat (n * d) (n * d)" using Ec by (intro carrier_matI) auto
    have Vu: "unitary (evolution A t0 \<Otimes> 1\<^sub>m d)" by (rule tensor_mat_unitary_one_right) (rule evolution_unitary[OF A])
    show ?thesis unfolding hhl_Wd_def nA by (rule pe_unitary_unitary[OF N Vc Vu])
  qed
  have ur: "dim_vec (tensor_vec u hid) = n * d" by (rule tensor_vec_dim[OF u]) (simp add: hd)
  have "tensor_vec dalpha (tensor_vec u hid) = reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u hid)"
    by (rule tensor_reg_sum[OF dim_alpha_d ur])
  moreover have "(hhl_Wd A t0 N d)\<^sup>\<dagger> *\<^sub>v tensor_vec dalpha (tensor_vec u hid) = tensor_vec psi (tensor_vec u hid)"
    by (rule unitary_undo[OF Wc Wu _ W_branch_d[OF dim_hid]]) (rule tensor_vec_dim; simp add: psi ur)
  ultimately show ?thesis by simp
qed

text \<open>The squared distance between output and ideal output.\<close>

text \<open>The error vector: $W^*\sum_k\alpha_k\ket k\otimes u\otimes(R(f_k)\ket0-R(c)\ket0)$.\<close>

lemma flag_err_vec:
  "flag_circuit A t0 N d G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec d 0)) - tensor_vec psi (tensor_vec u hid) =
   (hhl_Wd A t0 N d)\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k - hid))"
proof -
  let ?W = "hhl_Wd A t0 N d"
  let ?f = "\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k - hid)"
  have Wd: "?W\<^sup>\<dagger> \<in> carrier_mat (N * (n * d)) (N * (n * d))" by (rule dagger_carrier[OF hhl_Wd_carrier])
  have did: "dim_vec (tensor_vec u hid) = n * d" by (rule tensor_vec_dim[OF u]) (simp add: hd)
  have ddf: "dim_vec (tensor_vec u (fbr k - hid)) = n * d" for k by (rule tensor_vec_dim[OF u]) (simp add: hd)
  have diff_br: "dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k) - dalpha $ k \<cdot>\<^sub>v tensor_vec u hid = ?f k" if k: "k < N" for k
  proof -
    have fk: "dim_vec (fbr k) = d" using G[OF k] by simp
    have e: "hid + (fbr k - hid) = fbr k" using fk hd by (intro eq_vecI) simp_all
    have "tensor_vec u (hid + (fbr k - hid)) = tensor_vec u hid + tensor_vec u (fbr k - hid)"
      by (rule tensor_vec_bilinear_right[OF u]) (simp_all add: hd)
    hence split: "tensor_vec u (fbr k) = tensor_vec u hid + tensor_vec u (fbr k - hid)" unfolding e .
    show ?thesis unfolding split
      using did ddf[of k] by (intro eq_vecI) (simp_all add: algebra_simps)
  qed
  have "flag_circuit A t0 N d G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec d 0)) - tensor_vec psi (tensor_vec u hid) =
        ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k)) - ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u hid)"
    unfolding flag_output_branches flag_ideal_branches ..
  also have "\<dots> = ?W\<^sup>\<dagger> *\<^sub>v (reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k)) - reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u hid))"
    by (rule mult_minus_distrib_mat_vec[OF Wd, symmetric]) (simp_all add: carrier_vecI)
  also have "reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k)) - reg_sum N (n * d) (\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u hid) =
             reg_sum N (n * d) ?f"
    by (subst reg_sum_diff) (simp_all add: did diff_br cong: reg_sum_cong)
  finally show ?thesis .
qed

text \<open>The squared distance between output and ideal output.\<close>

theorem flag_error:
  "\<langle>flag_circuit A t0 N d G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec d 0)) - tensor_vec psi (tensor_vec u hid) |
    flag_circuit A t0 N d G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec d 0)) - tensor_vec psi (tensor_vec u hid)\<rangle> =
   \<langle>u|u\<rangle> * (\<Sum>k<N. complex_of_real ((cmod (pe_amp_reg N psi dphi k))\<^sup>2) * \<langle>fbr k - hid|fbr k - hid\<rangle>)"
proof -
  let ?W = "hhl_Wd A t0 N d"
  let ?f = "\<lambda>k. dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k - hid)"
  have ddf: "dim_vec (tensor_vec u (fbr k - hid)) = n * d" for k by (rule tensor_vec_dim[OF u]) (simp add: hd)
  have "\<langle>?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) ?f|?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) ?f\<rangle> = \<langle>reg_sum N (n * d) ?f|reg_sum N (n * d) ?f\<rangle>"
    by (rule unitary_inner_self[OF hhl_Wd_carrier hhl_Wd_unitary]) simp
  also have "\<dots> = (\<Sum>k<N. \<langle>?f k|?f k\<rangle>)" by (rule reg_sum_inner) (simp_all add: ddf)
  also have "\<dots> = (\<Sum>k<N. complex_of_real ((cmod (pe_amp_reg N psi dphi k))\<^sup>2) * (\<langle>u|u\<rangle> * \<langle>fbr k - hid|fbr k - hid\<rangle>))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<N}"
    hence k: "k < N" by simp
    have "\<langle>?f k|?f k\<rangle> = (cnj (dalpha $ k) * dalpha $ k) * \<langle>tensor_vec u (fbr k - hid)|tensor_vec u (fbr k - hid)\<rangle>"
      using inner_prod_distrib_left[of "tensor_vec u (fbr k - hid)" "dalpha $ k \<cdot>\<^sub>v tensor_vec u (fbr k - hid)" "dalpha $ k"]
            inner_prod_distrib_right[of "tensor_vec u (fbr k - hid)" "tensor_vec u (fbr k - hid)" "dalpha $ k"]
      by (simp add: mult.assoc)
    also have "\<langle>tensor_vec u (fbr k - hid)|tensor_vec u (fbr k - hid)\<rangle> = \<langle>u|u\<rangle> * \<langle>fbr k - hid|fbr k - hid\<rangle>"
      by (rule tensor_inner_prod[OF u u]) simp_all
    also have "cnj (dalpha $ k) * dalpha $ k = complex_of_real ((cmod (pe_amp_reg N psi dphi k))\<^sup>2)"
    proof -
      have ak: "dalpha $ k = pe_amp_reg N psi dphi k" using k by (simp add: dalpha_def)
      show ?thesis unfolding ak by (metis complex_norm_square mult.commute)
    qed
    finally show "\<langle>?f k|?f k\<rangle> = complex_of_real ((cmod (pe_amp_reg N psi dphi k))\<^sup>2) * (\<langle>u|u\<rangle> * \<langle>fbr k - hid|fbr k - hid\<rangle>)"
      by (simp add: mult_ac)
  qed
  also have "\<dots> = \<langle>u|u\<rangle> * (\<Sum>k<N. complex_of_real ((cmod (pe_amp_reg N psi dphi k))\<^sup>2) * \<langle>fbr k - hid|fbr k - hid\<rangle>)"
    by (simp add: sum_distrib_left mult_ac)
  finally show ?thesis unfolding flag_err_vec .
qed

text \<open>The branch distance in real terms.\<close>

end

subsection \<open>Window weights with wrapped distances\<close>

lemma pe_amp_reg_int_shift: "pe_amp_reg N psi (\<phi> - real_of_int m) j = pe_amp_reg N psi \<phi> j"
proof -
  have "cis (2 * pi * (\<phi> - real_of_int m)) = cis (2 * pi * \<phi>) * cis (- (2 * pi * real_of_int m))"
    unfolding cis_mult by (rule arg_cong[where f = cis]) (simp add: algebra_simps)
  also have "cis (- (2 * pi * real_of_int m)) = 1"
    using cis_multiple_2pi[of "- real_of_int m"] by simp
  finally show ?thesis by (simp add: pe_amp_reg_def)
qed

definition wrap :: "real \<Rightarrow> real" where
  "wrap x = x - real_of_int \<lceil>x - 1 / 2\<rceil>"

lemma wrap_range: "- (1 / 2) < wrap x" "wrap x \<le> 1 / 2"
  unfolding wrap_def by linarith+

lemma wrap_int: "x - wrap x \<in> \<int>"
  unfolding wrap_def by simp

text \<open>The amplitude in terms of the wrapped distance $r=\mathrm{wrap}(\varphi-k/N)$.\<close>

lemma win_amp_wrapped:
  fixes \<phi> :: real
  assumes N: "2 \<le> N" and k: "k < N"
  defines "r \<equiv> wrap (\<phi> - real k / real N)"
  shows "(cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2 \<le> 2"
    and "1 / real N \<le> \<bar>r\<bar> \<Longrightarrow> (cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2 \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * r ^ 4)"
proof -
  show "(cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2 \<le> 2" by (rule win_amp_crude[OF k])
  assume lo: "1 / real N \<le> \<bar>r\<bar>"
  define m where "m = \<lceil>\<phi> - real k / real N - 1 / 2\<rceil>"
  have rr: "\<phi> - real_of_int m - real k / real N = r" unfolding r_def wrap_def m_def by simp
  have hi: "\<bar>r\<bar> \<le> 1 / 2" using wrap_range[of "\<phi> - real k / real N"] unfolding r_def by linarith
  have "(cmod (pe_amp_reg N (win_state N) (\<phi> - real_of_int m) k))\<^sup>2 \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * (\<phi> - real_of_int m - real k / real N) ^ 4)"
    by (rule win_amp_tail[OF N k]) (use lo hi rr in simp_all)
  thus "(cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2 \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * r ^ 4)"
    unfolding pe_amp_reg_int_shift rr .
qed

lemma win_amp_weight:
  fixes \<phi> :: real
  assumes N: "2 \<le> N" and k: "k < N"
  defines "r \<equiv> wrap (\<phi> - real k / real N)"
  shows "(cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2 * r\<^sup>2 \<le> win_w (real N * r) / (real N)\<^sup>2"
proof -
  have NR: "0 < real N" using N by simp
  note a = win_amp_wrapped[where \<phi> = \<phi>, OF N k, folded r_def]
  show ?thesis
  proof (cases "\<bar>real N * r\<bar> < 1")
    case True
    have w: "win_w (real N * r) = 2" using True by (simp add: win_w_def)
    have "r\<^sup>2 \<le> 1 / (real N)\<^sup>2"
    proof -
      have "(real N * r)\<^sup>2 \<le> 1" using True by (simp add: abs_square_le_1)
      thus ?thesis using NR by (simp add: power_mult_distrib field_simps)
    qed
    hence "(cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2 * r\<^sup>2 \<le> 2 * (1 / (real N)\<^sup>2)" by (intro mult_mono a(1)) simp_all
    thus ?thesis unfolding w by simp
  next
    case False
    have lo: "1 / real N \<le> \<bar>r\<bar>" using False NR by (simp add: abs_mult field_simps)
    have r0: "r \<noteq> 0" using lo NR by auto
    have w: "win_w (real N * r) = pi\<^sup>2 / (2 * (real N * r)\<^sup>2)" using False by (simp add: win_w_def)
    have "(cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2 * r\<^sup>2 \<le> pi\<^sup>2 / (2 * (real N) ^ 4 * r ^ 4) * r\<^sup>2"
      by (intro mult_right_mono a(2)[OF lo]) simp
    also have "\<dots> = pi\<^sup>2 / (2 * (real N * r)\<^sup>2) / (real N)\<^sup>2" using r0 NR by (simp add: field_simps power2_eq_square power4_eq_xxxx)
    finally show ?thesis unfolding w .
  qed
qed

text \<open>Points with pairwise non-zero integer differences.\<close>

lemma spaced_floor_inj:
  fixes z :: "nat \<Rightarrow> real"
  assumes sp: "\<And>i j. i \<in> K \<Longrightarrow> j \<in> K \<Longrightarrow> i \<noteq> j \<Longrightarrow> z i - z j \<in> \<int> \<and> z i \<noteq> z j"
  shows "inj_on (\<lambda>k. \<lfloor>z k\<rfloor>) K" "inj_on (\<lambda>k. \<lfloor>- z k\<rfloor>) K"
proof -
  have fl: "\<lfloor>z i\<rfloor> \<noteq> \<lfloor>z j\<rfloor>" "\<lfloor>- z i\<rfloor> \<noteq> \<lfloor>- z j\<rfloor>" if ij: "i \<in> K" "j \<in> K" "i \<noteq> j" for i j
  proof -
    obtain m where m: "z i - z j = real_of_int m" using sp[OF ij] Ints_cases by metis
    have m0: "m \<noteq> 0" using sp[OF ij] m by auto
    have "z i = z j + real_of_int m" using m by simp
    hence "\<lfloor>z i\<rfloor> = \<lfloor>z j\<rfloor> + m" "\<lfloor>- z i\<rfloor> = \<lfloor>- z j\<rfloor> - m"
      using floor_add_int[of "z j" m] floor_diff_of_int[of "- z j" m] by simp_all
    thus "\<lfloor>z i\<rfloor> \<noteq> \<lfloor>z j\<rfloor>" "\<lfloor>- z i\<rfloor> \<noteq> \<lfloor>- z j\<rfloor>" using m0 by simp_all
  qed
  show "inj_on (\<lambda>k. \<lfloor>z k\<rfloor>) K" "inj_on (\<lambda>k. \<lfloor>- z k\<rfloor>) K" by (auto intro!: inj_onI dest: fl)
qed

lemma spaced_weight_sum:
  fixes z :: "nat \<Rightarrow> real"
  assumes K: "finite K" and sp: "\<And>i j. i \<in> K \<Longrightarrow> j \<in> K \<Longrightarrow> i \<noteq> j \<Longrightarrow> z i - z j \<in> \<int> \<and> z i \<noteq> z j"
  shows "(\<Sum>k\<in>K. win_w (z k)) \<le> 4 + 2 * pi\<^sup>2"
proof -
  note inj = spaced_floor_inj[OF sp]
  let ?n = "{k \<in> K. \<bar>z k\<bar> < 1}" and ?P = "{k \<in> K. 1 \<le> z k}" and ?M = "{k \<in> K. 1 \<le> - z k}"
  have near: "card ?n \<le> 2"
  proof -
    have "(\<lambda>k. \<lfloor>z k\<rfloor>) ` ?n \<subseteq> {-1, 0}" by (auto simp: abs_less_iff) linarith+
    hence "card ((\<lambda>k. \<lfloor>z k\<rfloor>) ` ?n) \<le> card {-1, 0 :: int}" by (intro card_mono) simp_all
    moreover have "card ((\<lambda>k. \<lfloor>z k\<rfloor>) ` ?n) = card ?n" by (rule card_image) (rule inj_on_subset[OF inj(1)], auto)
    ultimately show ?thesis by simp
  qed
  have P: "(\<Sum>k\<in>?P. 1 / (z k)\<^sup>2) \<le> 2"
    by (rule inv_sq_floor_inj) (use K inj_on_subset[OF inj(1)] in auto)
  have M: "(\<Sum>k\<in>?M. 1 / (- z k)\<^sup>2) \<le> 2"
    by (rule inv_sq_floor_inj) (use K inj_on_subset[OF inj(2)] in auto)
  have split: "K = ?n \<union> (?P \<union> ?M)" by auto
  have "(\<Sum>k\<in>K. win_w (z k)) = (\<Sum>k\<in>?n. win_w (z k)) + ((\<Sum>k\<in>?P. win_w (z k)) + (\<Sum>k\<in>?M. win_w (z k)))"
  proof -
    have "(\<Sum>k\<in>K. win_w (z k)) = (\<Sum>k\<in>?n \<union> (?P \<union> ?M). win_w (z k))" using split by simp
    also have "\<dots> = (\<Sum>k\<in>?n. win_w (z k)) + (\<Sum>k\<in>?P \<union> ?M. win_w (z k))"
      by (rule sum.union_disjoint) (use K in auto)
    also have "(\<Sum>k\<in>?P \<union> ?M. win_w (z k)) = (\<Sum>k\<in>?P. win_w (z k)) + (\<Sum>k\<in>?M. win_w (z k))"
      by (rule sum.union_disjoint) (use K in auto)
    finally show ?thesis .
  qed
  also have "(\<Sum>k\<in>?n. win_w (z k)) = 2 * real (card ?n)" by (simp add: win_w_def)
  also have "(\<Sum>k\<in>?P. win_w (z k)) = pi\<^sup>2 / 2 * (\<Sum>k\<in>?P. 1 / (z k)\<^sup>2)" by (simp add: win_w_def sum_distrib_left)
  also have "(\<Sum>k\<in>?M. win_w (z k)) = pi\<^sup>2 / 2 * (\<Sum>k\<in>?M. 1 / (- z k)\<^sup>2)" by (simp add: win_w_def sum_distrib_left)
  also have "2 * real (card ?n) + (pi\<^sup>2 / 2 * (\<Sum>k\<in>?P. 1 / (z k)\<^sup>2) + pi\<^sup>2 / 2 * (\<Sum>k\<in>?M. 1 / (- z k)\<^sup>2))
             \<le> 2 * 2 + (pi\<^sup>2 / 2 * 2 + pi\<^sup>2 / 2 * 2)"
    using near P M by (intro add_mono mult_left_mono) simp_all
  finally show ?thesis by simp
qed

lemma reg_e_bound:
  assumes t0: "0 < t0" and N: "0 < N" and k: "k < N" and ph: "\<bar>\<phi>\<bar> \<le> 1 / 4"
  shows "\<bar>t0 * reg_eig t0 N k / (2 * pi) - \<phi>\<bar> \<le> 3 * \<bar>wrap (\<phi> - real k / real N)\<bar>"
proof -
  define x where "x = (if 2 * k < N then real k else real k - real N) / real N"
  have NR: "0 < real N" using N by simp
  have xe: "t0 * reg_eig t0 N k / (2 * pi) = x" unfolding x_def reg_eig_def using t0 by (simp add: field_simps)
  have xh: "\<bar>x\<bar> \<le> 1 / 2"
  proof (cases "2 * k < N")
    case True thus ?thesis unfolding x_def using NR by (simp add: field_simps)
  next
    case False thus ?thesis unfolding x_def using NR k by (simp add: field_simps abs_if)
  qed
  have xi: "x - real k / real N \<in> \<int>"
  proof (cases "2 * k < N")
    case True thus ?thesis unfolding x_def by simp
  next
    case False
    have "x - real k / real N = - 1" unfolding x_def using False NR by (simp add: field_simps)
    thus ?thesis by simp
  qed
  define r where "r = wrap (\<phi> - real k / real N)"
  define e where "e = x - \<phi>"
  have ri: "(\<phi> - real k / real N) - r \<in> \<int>" unfolding r_def by (rule wrap_int)
  have re: "r + e \<in> \<int>"
  proof -
    have eq: "r + e = (x - real k / real N) - ((\<phi> - real k / real N) - r)" unfolding e_def by simp
    show ?thesis unfolding eq by (rule Ints_diff[OF xi ri])
  qed
  have rh: "\<bar>r\<bar> \<le> 1 / 2" using wrap_range[of "\<phi> - real k / real N"] unfolding r_def by linarith
  have eh: "\<bar>e\<bar> \<le> 3 / 4" unfolding e_def using xh ph by linarith
  have "\<bar>e\<bar> \<le> 3 * \<bar>r\<bar>"
  proof (cases "r + e = 0")
    case True thus ?thesis by linarith
  next
    case False
    obtain m where m: "r + e = real_of_int m" using re Ints_cases by metis
    hence "m \<noteq> 0" using False by auto
    hence "1 \<le> \<bar>r + e\<bar>" unfolding m by linarith
    thus ?thesis using eh by linarith
  qed
  thus ?thesis unfolding xe e_def r_def .
qed

lemma wrap_spaced:
  assumes N: "0 < N" and i: "i < N" and j: "j < N" and ij: "i \<noteq> j"
  shows "real N * wrap (\<phi> - real i / real N) - real N * wrap (\<phi> - real j / real N) \<in> \<int>
         \<and> real N * wrap (\<phi> - real i / real N) \<noteq> real N * wrap (\<phi> - real j / real N)"
proof -
  let ?ri = "wrap (\<phi> - real i / real N)" and ?rj = "wrap (\<phi> - real j / real N)"
  have NR: "0 < real N" using N by simp
  obtain a where a: "(\<phi> - real i / real N) - ?ri = real_of_int a" using wrap_int Ints_cases by metis
  obtain b where b: "(\<phi> - real j / real N) - ?rj = real_of_int b" using wrap_int Ints_cases by metis
  have e: "real N * ?ri - real N * ?rj = real_of_int (int j - int i + int N * (b - a))"
  proof -
    have "?ri - ?rj = real j / real N - real i / real N + (real_of_int b - real_of_int a)" using a b by linarith
    hence "?ri - ?rj = (real j - real i) / real N + (real_of_int b - real_of_int a)" by (simp add: diff_divide_distrib)
    hence eq: "?ri - ?rj = (real j - real i) / real N + (real_of_int b - real_of_int a)" .
    have "real N * ?ri - real N * ?rj = real N * (?ri - ?rj)" by (simp only: right_diff_distrib)
    also have "\<dots> = real N * ((real j - real i) / real N) + real N * (real_of_int b - real_of_int a)"
      unfolding eq by (simp only: distrib_left)
    also have "real N * ((real j - real i) / real N) = real j - real i" using NR by simp
    finally show ?thesis by simp
  qed
  have ne: "int j - int i + int N * (b - a) \<noteq> 0"
  proof
    assume z: "int j - int i + int N * (b - a) = 0"
    hence "int N * (a - b) = int j - int i" by (simp add: algebra_simps)
    moreover have "\<bar>int j - int i\<bar> < int N" using i j by linarith
    ultimately have lt: "\<bar>int N * (a - b)\<bar> < int N" by simp
    have "a - b = 0"
    proof (rule ccontr)
      assume "a - b \<noteq> 0"
      hence "1 \<le> \<bar>a - b\<bar>" by linarith
      hence "int N * 1 \<le> int N * \<bar>a - b\<bar>" by (intro mult_left_mono) simp_all
      thus False using lt by (simp add: abs_mult)
    qed
    thus False using z ij by simp
  qed
  have "real_of_int (int j - int i + int N * (b - a)) \<noteq> 0" using ne by (simp only: of_int_eq_0_iff) simp
  hence d0: "real N * ?ri - real N * ?rj \<noteq> 0" unfolding e .
  have di: "real N * ?ri - real N * ?rj \<in> \<int>" unfolding e by (rule Ints_of_int)
  show ?thesis using d0 di by (simp only: right_minus_eq) simp
qed

text \<open>Theorem 1(1) of the paper on an eigenvector, for the flag circuit with the window register:
the squared error is at most $9\pi^4(4+2\pi^2)\kappa^2/(Nt_0)^2$, i.e.\ $O(\kappa/t)$ with
$t=Nt_0$ the total evolution time.\<close>

theorem flag_window_eigen:
  fixes A :: "complex Matrix.mat" and u :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
      and k0: "0 < \<kappa>" and ph: "\<bar>t0 * l\<bar> \<le> pi / 2"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
  shows "Re \<langle>flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 3 0)) - tensor_vec (win_state N) (tensor_vec u (hflag \<kappa> l)) |
             flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 3 0)) - tensor_vec (win_state N) (tensor_vec u (hflag \<kappa> l))\<rangle>
         \<le> Re \<langle>u|u\<rangle> * (9 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2))"
proof -
  have N0: "0 < N" using N by simp
  have NR: "0 < real N" using N by simp
  define \<phi> where "\<phi> = hhl_phi t0 l"
  have phq: "\<bar>\<phi>\<bar> \<le> 1 / 4" unfolding \<phi>_def hhl_phi_def using ph t0 by (simp add: abs_mult abs_divide field_simps)
  let ?a = "\<lambda>k. (cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2"
  let ?h = "\<lambda>k. \<parallel>hflag \<kappa> (reg_eig t0 N k) - hflag \<kappa> l\<parallel>\<^sup>2"
  let ?r = "\<lambda>k. wrap (\<phi> - real k / real N)"
  define c where "c = 9 * pi ^ 4 * \<kappa>\<^sup>2 / t0\<^sup>2"
  have E: "\<langle>flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 3 0)) - tensor_vec (win_state N) (tensor_vec u (hflag \<kappa> l)) |
             flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 3 0)) - tensor_vec (win_state N) (tensor_vec u (hflag \<kappa> l))\<rangle>
        = \<langle>u|u\<rangle> * complex_of_real (\<Sum>k<N. ?a k * ?h k)"
  proof -
    have "(\<Sum>k<N. complex_of_real (?a k) * \<langle>G k *\<^sub>v unit_vec 3 0 - hflag \<kappa> l|G k *\<^sub>v unit_vec 3 0 - hflag \<kappa> l\<rangle>)
          = (\<Sum>k<N. complex_of_real (?a k * ?h k))"
      by (rule sum.cong) (simp_all add: Gh cpx_vec_length_inner_prod[symmetric] \<phi>_def)
    moreover have d3: "0 < (3::nat)" by simp
    ultimately show ?thesis using flag_error[OF A t0 N0 u ev dim_win_state d3 G dim_hflag[of \<kappa> l]] unfolding \<phi>_def by (simp add: of_real_sum)
  qed
  have tm: "?a k * ?h k \<le> c * (win_w (real N * ?r k) / (real N)\<^sup>2)" if k: "k < N" for k
  proof -
    have lip: "\<parallel>hflag \<kappa> (reg_eig t0 N k) - hflag \<kappa> l\<parallel> \<le> pi / 2 * \<kappa> * \<bar>reg_eig t0 N k - l\<bar>" by (rule hflag_lipschitz[OF k0])
    have dl: "\<bar>reg_eig t0 N k - l\<bar> = 2 * pi / t0 * \<bar>t0 * reg_eig t0 N k / (2 * pi) - \<phi>\<bar>"
    proof -
      have i: "t0 * reg_eig t0 N k / (2 * pi) - \<phi> = t0 / (2 * pi) * (reg_eig t0 N k - l)"
        unfolding \<phi>_def hhl_phi_def by (simp add: algebra_simps diff_divide_distrib)
      have p: "0 < t0 / (2 * pi)" using t0 by simp
      have "2 * pi / t0 * \<bar>t0 * reg_eig t0 N k / (2 * pi) - \<phi>\<bar> = (2 * pi / t0 * (t0 / (2 * pi))) * \<bar>reg_eig t0 N k - l\<bar>"
        unfolding i abs_mult abs_of_pos[OF p] by (simp only: mult.assoc)
      also have "2 * pi / t0 * (t0 / (2 * pi)) = 1" using t0 by simp
      finally show ?thesis by simp
    qed
    have rb: "\<bar>reg_eig t0 N k - l\<bar> \<le> 2 * pi / t0 * (3 * \<bar>?r k\<bar>)"
      unfolding dl using reg_e_bound[OF t0 N0 k phq] t0 by (intro mult_left_mono) simp_all
    have "\<parallel>hflag \<kappa> (reg_eig t0 N k) - hflag \<kappa> l\<parallel> \<le> pi / 2 * \<kappa> * (2 * pi / t0 * (3 * \<bar>?r k\<bar>))"
    proof -
      have L0: "0 \<le> pi / 2 * \<kappa>" using k0 by simp
      have "pi / 2 * \<kappa> * \<bar>reg_eig t0 N k - l\<bar> \<le> pi / 2 * \<kappa> * (2 * pi / t0 * (3 * \<bar>?r k\<bar>))"
        by (rule mult_left_mono[OF rb L0])
      thus ?thesis using lip by linarith
    qed
    hence "?h k \<le> (pi / 2 * \<kappa> * (2 * pi / t0 * (3 * \<bar>?r k\<bar>)))\<^sup>2" by (intro power_mono) (simp_all add: vnorm_ge0)
    also have "\<dots> = c * (?r k)\<^sup>2" unfolding c_def using t0 by (simp add: power_mult_distrib power_divide power2_abs field_simps power4_eq_xxxx power2_eq_square)
    finally have hk: "?h k \<le> c * (?r k)\<^sup>2" .
    have c0: "0 \<le> c" unfolding c_def by simp
    have "?a k * ?h k \<le> ?a k * (c * (?r k)\<^sup>2)" by (intro mult_left_mono hk) simp
    also have "\<dots> = c * (?a k * (?r k)\<^sup>2)" by simp
    also have "\<dots> \<le> c * (win_w (real N * ?r k) / (real N)\<^sup>2)"
      by (intro mult_left_mono c0 win_amp_weight[OF N k])
    finally show ?thesis .
  qed
  have S: "(\<Sum>k<N. ?a k * ?h k) \<le> c * (4 + 2 * pi\<^sup>2) / (real N)\<^sup>2"
  proof -
    have "(\<Sum>k<N. ?a k * ?h k) \<le> (\<Sum>k<N. c * (win_w (real N * ?r k) / (real N)\<^sup>2))" by (rule sum_mono) (rule tm, simp)
    also have "\<dots> = c / (real N)\<^sup>2 * (\<Sum>k<N. win_w (real N * ?r k))" by (simp add: sum_distrib_left)
    also have "\<dots> \<le> c / (real N)\<^sup>2 * (4 + 2 * pi\<^sup>2)"
    proof (rule mult_left_mono)
      show "(\<Sum>k<N. win_w (real N * ?r k)) \<le> 4 + 2 * pi\<^sup>2"
        by (rule spaced_weight_sum[where z = "\<lambda>k. real N * ?r k"]) (use wrap_spaced[OF N0] in auto)
    qed (simp add: c_def)
    finally show ?thesis by simp
  qed
  define ru where "ru = (\<Sum>i<n. (cmod (u $ i))\<^sup>2)"
  have uu: "\<langle>u|u\<rangle> = complex_of_real ru" unfolding ru_def by (simp add: inner_self_sum[OF u])
  have ru0: "0 \<le> ru" unfolding ru_def by (simp add: sum_nonneg)
  have "Re (\<langle>u|u\<rangle> * complex_of_real (\<Sum>k<N. ?a k * ?h k)) = ru * (\<Sum>k<N. ?a k * ?h k)" unfolding uu by simp
  also have "\<dots> \<le> ru * (c * (4 + 2 * pi\<^sup>2) / (real N)\<^sup>2)" by (rule mult_left_mono[OF S ru0])
  also have "c * (4 + 2 * pi\<^sup>2) / (real N)\<^sup>2 = 9 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2)"
    unfolding c_def by (simp add: field_simps)
  finally show ?thesis unfolding E uu by simp
qed

subsection \<open>Post-selection on the flag register\<close>

text \<open>Matrices that do not mix flag values.\<close>

definition flagdiag :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "flagdiag d M \<longleftrightarrow> (\<forall>r s. r < dim_row M \<longrightarrow> s < dim_col M \<longrightarrow> r mod d \<noteq> s mod d \<longrightarrow> M $$ (r, s) = 0)"

lemma flagdiag_mult:
  assumes "flagdiag d A" "flagdiag d B" "dim_col A = dim_row B"
  shows "flagdiag d (A * B)"
  unfolding flagdiag_def
proof (intro allI impI)
  fix r s assume r: "r < dim_row (A * B)" and s: "s < dim_col (A * B)" and rs: "r mod d \<noteq> s mod d"
  have "(A * B) $$ (r, s) = (\<Sum>t<dim_row B. A $$ (r, t) * B $$ (t, s))"
    using r s assms(3) by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = 0"
  proof (rule sum.neutral, rule ballI)
    fix t assume t: "t \<in> {..<dim_row B}"
    show "A $$ (r, t) * B $$ (t, s) = 0"
    proof (cases "r mod d = t mod d")
      case True
      hence "t mod d \<noteq> s mod d" using rs by simp
      thus ?thesis using assms(2) t s unfolding flagdiag_def by simp
    next
      case False
      thus ?thesis using assms(1,3) r t unfolding flagdiag_def by simp
    qed
  qed
  finally show "(A * B) $$ (r, s) = 0" .
qed

lemma flagdiag_dagger: "flagdiag d M \<Longrightarrow> flagdiag d (M\<^sup>\<dagger>)"
  unfolding flagdiag_def by (auto simp: dagger_def)

lemma flagdiag_one: "flagdiag d (1\<^sub>m K)"
  unfolding flagdiag_def by auto

lemma flagdiag_pow: "flagdiag d M \<Longrightarrow> M \<in> carrier_mat K K \<Longrightarrow> flagdiag d (M ^\<^sub>m j)"
proof (induction j)
  case 0 thus ?case by (simp add: flagdiag_one)
next
  case (Suc j)
  thus ?case using pow_carrier_mat[OF Suc.prems(2), of j] by (simp add: flagdiag_mult)
qed

lemma pflag_commute:
  assumes M: "M \<in> carrier_mat K K" and f: "flagdiag d M" and v: "dim_vec v = K"
  shows "pflag d P (M *\<^sub>v v) = M *\<^sub>v pflag d P v"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (M *\<^sub>v pflag d P v)"
  hence r: "r < K" using M by simp
  have "(M *\<^sub>v pflag d P v) $ r = (\<Sum>s<K. M $$ (r, s) * (if P (s mod d) then v $ s else 0))"
    using M r v by (simp add: pflag_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>s<K. (if P (r mod d) then M $$ (r, s) * v $ s else 0))"
  proof (rule sum.cong[OF refl])
    fix s assume "s \<in> {..<K}"
    hence s: "s < K" by simp
    show "M $$ (r, s) * (if P (s mod d) then v $ s else 0) = (if P (r mod d) then M $$ (r, s) * v $ s else 0)"
    proof (cases "r mod d = s mod d")
      case False
      hence "M $$ (r, s) = 0" using f M r s unfolding flagdiag_def by simp
      thus ?thesis by simp
    qed simp
  qed
  also have "\<dots> = pflag d P (M *\<^sub>v v) $ r"
    using M r v by (simp add: pflag_def scalar_prod_def atLeast0LessThan)
  finally show "pflag d P (M *\<^sub>v v) $ r = (M *\<^sub>v pflag d P v) $ r" ..
qed (use M in simp)

text \<open>Tensoring with $I_d$ on the right and block operators on top of it do not mix flag values.\<close>

lemma flagdiag_tensor_one:
  assumes "0 < d"
  shows "flagdiag d (X \<Otimes> 1\<^sub>m d)"
  unfolding flagdiag_def
proof (intro allI impI)
  fix r s assume r: "r < dim_row (X \<Otimes> 1\<^sub>m d)" and s: "s < dim_col (X \<Otimes> 1\<^sub>m d)" and rs: "r mod d \<noteq> s mod d"
  have c0: "0 < dim_col X" using s by (cases "dim_col X") simp_all
  have "(X \<Otimes> 1\<^sub>m d) $$ (r, s) = X $$ (r div d, s div d) * 1\<^sub>m d $$ (r mod d, s mod d)"
    using index_tensor_mat[of X "dim_row X" "dim_col X" "1\<^sub>m d" d d r s] r s c0 assms by simp
  thus "(X \<Otimes> 1\<^sub>m d) $$ (r, s) = 0" using rs assms by simp
qed

lemma flagdiag_ctrl_blocks:
  assumes d0: "0 < d" and B: "\<And>k. k < N \<Longrightarrow> flagdiag d (B k) \<and> B k \<in> carrier_mat (n * d) (n * d)"
  shows "flagdiag d (ctrl_blocks N (n * d) B)"
  unfolding flagdiag_def
proof (intro allI impI)
  fix r s assume r: "r < dim_row (ctrl_blocks N (n * d) B)" and s: "s < dim_col (ctrl_blocks N (n * d) B)" and rs: "r mod d \<noteq> s mod d"
  hence r': "r < N * (n * d)" and s': "s < N * (n * d)" by simp_all
  show "ctrl_blocks N (n * d) B $$ (r, s) = 0"
  proof (cases "r div (n * d) = s div (n * d)")
    case True
    have k: "r div (n * d) < N" using r' by (simp add: less_mult_imp_div_less)
    have nd: "0 < n * d" using r' by (cases "n * d") simp_all
    have m: "r mod (n * d) mod d = r mod d" "s mod (n * d) mod d = s mod d"
      by (simp_all add: mod_mod_cancel)
    have Bk: "flagdiag d (B (r div (n * d)))" "B (r div (n * d)) \<in> carrier_mat (n * d) (n * d)" using B[OF k] by simp_all
    have i1: "r mod (n * d) < dim_row (B (r div (n * d)))" and i2: "s mod (n * d) < dim_col (B (r div (n * d)))"
      using Bk(2) nd by simp_all
    have "r mod (n * d) mod d \<noteq> s mod (n * d) mod d" unfolding m by (rule rs)
    hence "B (r div (n * d)) $$ (r mod (n * d), s mod (n * d)) = 0" using Bk(1) i1 i2 unfolding flagdiag_def by blast
    thus ?thesis using r' s' True by (simp add: ctrl_blocks_index)
  next
    case False thus ?thesis using r' s' by (simp add: ctrl_blocks_index)
  qed
qed

lemma flagdiag_dvd: "flagdiag D M \<Longrightarrow> d dvd D \<Longrightarrow> flagdiag d M"
  unfolding flagdiag_def by (metis mod_mod_cancel)

lemma hhl_Wd_flagdiag:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n"
  shows "flagdiag 3 (hhl_Wd A t0 N 3)"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have E0: "evolution A t0 \<in> carrier_mat n n" using A by (rule evolution_carrier)
  have E: "evolution A t0 \<Otimes> 1\<^sub>m 3 \<in> carrier_mat (n * 3) (n * 3)" using E0 by (intro carrier_matI) simp_all
  have F: "flagdiag 3 ((fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 3))"
    by (rule flagdiag_dvd[OF flagdiag_tensor_one]) (use n0 in simp_all)
  have C: "flagdiag 3 (ctrl_pow N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3))"
    unfolding ctrl_pow_blocks
    by (rule flagdiag_ctrl_blocks) (use flagdiag_pow[OF flagdiag_tensor_one E] pow_carrier_mat[OF E] in simp_all)
  show ?thesis unfolding hhl_Wd_def pe_unitary_def nA
    by (rule flagdiag_mult[OF F C]) simp
qed

lemma pflag_reg_sum:
  assumes f: "\<And>k. k < N \<Longrightarrow> dim_vec (f k) = n * d" and d0: "0 < d"
  shows "pflag d P (reg_sum N (n * d) f) = reg_sum N (n * d) (\<lambda>k. pflag d P (f k))"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (reg_sum N (n * d) (\<lambda>k. pflag d P (f k)))"
  hence r: "r < N * (n * d)" by simp
  note ki = less_mult_imp_div_less[OF r] reg_sum_index_mod[OF r]
  have m: "r mod (n * d) mod d = r mod d" by (simp add: mod_mod_cancel)
  show "pflag d P (reg_sum N (n * d) f) $ r = reg_sum N (n * d) (\<lambda>k. pflag d P (f k)) $ r"
    using r ki f[OF ki(1)] m by (simp add: pflag_def reg_sum_def)
qed simp

lemma pflag_tensor:
  assumes u: "dim_vec u = n" and w: "dim_vec w = d" and d0: "0 < d"
  shows "pflag d P (tensor_vec u w) = tensor_vec u (pflag d P w)"
proof (rule eq_vecI)
  have du: "dim_vec (tensor_vec u w) = n * d" by (rule tensor_vec_dim[OF u w])
  have dp: "dim_vec (tensor_vec u (pflag d P w)) = n * d" by (rule tensor_vec_dim[OF u]) (simp add: w)
  show "dim_vec (pflag d P (tensor_vec u w)) = dim_vec (tensor_vec u (pflag d P w))" using du dp by simp
  fix r assume "r < dim_vec (tensor_vec u (pflag d P w))"
  hence r: "r < n * d" using dp by simp
  have "r mod d < d" using d0 by simp
  thus "pflag d P (tensor_vec u w) $ r = tensor_vec u (pflag d P w) $ r"
    using r du tensor_vec_index[OF u w r] tensor_vec_index[OF u _ r, of "pflag d P w"] w by (simp add: pflag_def)
qed

lemma pflag_smult: "pflag d P (c \<cdot>\<^sub>v v) = c \<cdot>\<^sub>v pflag d P v"
  by (intro eq_vecI) (simp_all add: pflag_def)

text \<open>The norm of a branch sum behind a unitary.\<close>

lemma unitary_reg_sum_norm:
  assumes W: "W \<in> carrier_mat (N * (n * d)) (N * (n * d))" "unitary W"
      and u: "dim_vec u = n" and w: "\<And>k. k < N \<Longrightarrow> dim_vec (w k) = d"
  shows "\<langle>W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) (\<lambda>k. a k \<cdot>\<^sub>v tensor_vec u (w k))|W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) (\<lambda>k. a k \<cdot>\<^sub>v tensor_vec u (w k))\<rangle>
         = \<langle>u|u\<rangle> * (\<Sum>k<N. complex_of_real ((cmod (a k))\<^sup>2) * \<langle>w k|w k\<rangle>)"
proof -
  let ?f = "\<lambda>k. a k \<cdot>\<^sub>v tensor_vec u (w k)"
  have dt: "dim_vec (tensor_vec u (w k)) = n * d" if "k < N" for k using tensor_vec_dim[OF u w[OF that]] .
  have df: "dim_vec (?f k) = n * d" if "k < N" for k using dt[OF that] by simp
  have "\<langle>W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) ?f|W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * d) ?f\<rangle> = \<langle>reg_sum N (n * d) ?f|reg_sum N (n * d) ?f\<rangle>"
    by (rule unitary_inner_self[OF W]) simp
  also have "\<dots> = (\<Sum>k<N. \<langle>?f k|?f k\<rangle>)" by (rule reg_sum_inner) (simp_all add: df dt)
  also have "\<dots> = (\<Sum>k<N. complex_of_real ((cmod (a k))\<^sup>2) * (\<langle>u|u\<rangle> * \<langle>w k|w k\<rangle>))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<N}"
    hence k: "k < N" by simp
    have dt: "dim_vec (tensor_vec u (w k)) = n * d" using tensor_vec_dim[OF u w[OF k]] .
    have "\<langle>?f k|?f k\<rangle> = (cnj (a k) * a k) * \<langle>tensor_vec u (w k)|tensor_vec u (w k)\<rangle>"
      using inner_prod_distrib_left[of "tensor_vec u (w k)" "?f k" "a k"]
            inner_prod_distrib_right[of "tensor_vec u (w k)" "tensor_vec u (w k)" "a k"] dt
      by (simp add: mult.assoc)
    also have "\<langle>tensor_vec u (w k)|tensor_vec u (w k)\<rangle> = \<langle>u|u\<rangle> * \<langle>w k|w k\<rangle>"
      by (rule tensor_inner_prod[OF u u w[OF k] w[OF k]])
    also have "cnj (a k) * a k = complex_of_real ((cmod (a k))\<^sup>2)" by (metis complex_norm_square mult.commute)
    finally show "\<langle>?f k|?f k\<rangle> = complex_of_real ((cmod (a k))\<^sup>2) * (\<langle>u|u\<rangle> * \<langle>w k|w k\<rangle>)" by (simp add: mult_ac)
  qed
  also have "\<dots> = \<langle>u|u\<rangle> * (\<Sum>k<N. complex_of_real ((cmod (a k))\<^sup>2) * \<langle>w k|w k\<rangle>)"
    by (simp add: sum_distrib_left mult_ac)
  finally show ?thesis .
qed

text \<open>The window-weighted spread of the register eigenvalues around $\lambda$:
$\sum_k|\alpha_k|^2(\tilde\lambda_k-\lambda)^2\le36\pi^2(4+2\pi^2)/(Nt_0)^2$.\<close>

lemma window_spread:
  assumes t0: "0 < t0" and N: "2 \<le> N" and ph: "\<bar>t0 * l\<bar> \<le> pi / 2"
  shows "(\<Sum>k<N. (cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2 * (reg_eig t0 N k - l)\<^sup>2)
         \<le> 36 * pi\<^sup>2 * (4 + 2 * pi\<^sup>2) / ((real N)\<^sup>2 * t0\<^sup>2)"
proof -
  have N0: "0 < N" using N by simp
  define \<phi> where "\<phi> = hhl_phi t0 l"
  have phq: "\<bar>\<phi>\<bar> \<le> 1 / 4" unfolding \<phi>_def hhl_phi_def using ph t0 by (simp add: abs_mult abs_divide field_simps)
  let ?a = "\<lambda>k. (cmod (pe_amp_reg N (win_state N) \<phi> k))\<^sup>2"
  let ?r = "\<lambda>k. wrap (\<phi> - real k / real N)"
  define c where "c = 36 * pi\<^sup>2 / t0\<^sup>2"
  have tm: "?a k * (reg_eig t0 N k - l)\<^sup>2 \<le> c * (win_w (real N * ?r k) / (real N)\<^sup>2)" if k: "k < N" for k
  proof -
    have dl: "\<bar>reg_eig t0 N k - l\<bar> = 2 * pi / t0 * \<bar>t0 * reg_eig t0 N k / (2 * pi) - \<phi>\<bar>"
    proof -
      have i: "t0 * reg_eig t0 N k / (2 * pi) - \<phi> = t0 / (2 * pi) * (reg_eig t0 N k - l)"
        unfolding \<phi>_def hhl_phi_def by (simp add: algebra_simps diff_divide_distrib)
      have p: "0 < t0 / (2 * pi)" using t0 by simp
      have "2 * pi / t0 * \<bar>t0 * reg_eig t0 N k / (2 * pi) - \<phi>\<bar> = (2 * pi / t0 * (t0 / (2 * pi))) * \<bar>reg_eig t0 N k - l\<bar>"
        unfolding i abs_mult abs_of_pos[OF p] by (simp only: mult.assoc)
      also have "2 * pi / t0 * (t0 / (2 * pi)) = 1" using t0 by simp
      finally show ?thesis by simp
    qed
    have rb: "\<bar>reg_eig t0 N k - l\<bar> \<le> 2 * pi / t0 * (3 * \<bar>?r k\<bar>)"
      unfolding dl using reg_e_bound[OF t0 N0 k phq] t0 by (intro mult_left_mono) simp_all
    have "(reg_eig t0 N k - l)\<^sup>2 \<le> (2 * pi / t0 * (3 * \<bar>?r k\<bar>))\<^sup>2"
      using power_mono[OF rb, of 2] by (simp add: power2_abs)
    also have "\<dots> = c * (?r k)\<^sup>2" unfolding c_def using t0 by (simp add: power_mult_distrib power_divide power2_abs)
    finally have hk: "(reg_eig t0 N k - l)\<^sup>2 \<le> c * (?r k)\<^sup>2" .
    have c0: "0 \<le> c" unfolding c_def by simp
    have "?a k * (reg_eig t0 N k - l)\<^sup>2 \<le> ?a k * (c * (?r k)\<^sup>2)" by (intro mult_left_mono hk) simp
    also have "\<dots> = c * (?a k * (?r k)\<^sup>2)" by simp
    also have "\<dots> \<le> c * (win_w (real N * ?r k) / (real N)\<^sup>2)" by (intro mult_left_mono c0 win_amp_weight[OF N k])
    finally show ?thesis .
  qed
  have "(\<Sum>k<N. ?a k * (reg_eig t0 N k - l)\<^sup>2) \<le> (\<Sum>k<N. c * (win_w (real N * ?r k) / (real N)\<^sup>2))"
    by (rule sum_mono) (rule tm, simp)
  also have "\<dots> = c / (real N)\<^sup>2 * (\<Sum>k<N. win_w (real N * ?r k))" by (simp add: sum_distrib_left)
  also have "\<dots> \<le> c / (real N)\<^sup>2 * (4 + 2 * pi\<^sup>2)"
  proof (rule mult_left_mono)
    show "(\<Sum>k<N. win_w (real N * ?r k)) \<le> 4 + 2 * pi\<^sup>2"
      by (rule spaced_weight_sum[where z = "\<lambda>k. real N * ?r k"]) (use wrap_spaced[OF N0] in auto)
  qed (simp add: c_def)
  also have "\<dots> = 36 * pi\<^sup>2 * (4 + 2 * pi\<^sup>2) / ((real N)\<^sup>2 * t0\<^sup>2)" unfolding c_def by (simp add: field_simps)
  finally show ?thesis unfolding \<phi>_def .
qed

lemma vnorm3_sq: "dim_vec v = 3 \<Longrightarrow> \<parallel>v\<parallel>\<^sup>2 = (cmod (v $ 0))\<^sup>2 + (cmod (v $ 1))\<^sup>2 + (cmod (v $ 2))\<^sup>2"
  unfolding vnorm_sq by (simp add: numeral_3_eq_3 numeral_2_eq_2 lessThan_Suc)

lemma pflag3_entries:
  assumes "dim_vec v = 3"
  shows "pflag 3 (\<lambda>c. c \<noteq> 0) v $ 0 = 0" "pflag 3 (\<lambda>c. c \<noteq> 0) v $ 1 = v $ 1" "pflag 3 (\<lambda>c. c \<noteq> 0) v $ 2 = v $ 2"
  using assms by (simp_all add: pflag_def)

lemma hflag_entries: "hflag \<kappa> x $ 1 = complex_of_real (filt_f \<kappa> x)" "hflag \<kappa> x $ 2 = complex_of_real (filt_g \<kappa> x)"
  by (simp_all add: hflag_def)

lemma pflag_flag_dist:
  "\<parallel>pflag 3 (\<lambda>c. c \<noteq> 0) (hflag \<kappa> a - hflag \<kappa> b)\<parallel>\<^sup>2 = (filt_f \<kappa> a - filt_f \<kappa> b)\<^sup>2 + (filt_g \<kappa> a - filt_g \<kappa> b)\<^sup>2"
proof -
  have d: "dim_vec (hflag \<kappa> a - hflag \<kappa> b) = 3" by simp
  have e: "cmod (complex_of_real x - complex_of_real y) = \<bar>x - y\<bar>" for x y by (metis norm_of_real of_real_diff)
  have i1: "(hflag \<kappa> a - hflag \<kappa> b) $ 1 = complex_of_real (filt_f \<kappa> a) - complex_of_real (filt_f \<kappa> b)"
    and i2: "(hflag \<kappa> a - hflag \<kappa> b) $ 2 = complex_of_real (filt_g \<kappa> a) - complex_of_real (filt_g \<kappa> b)"
    by (simp_all add: hflag_def)
  show ?thesis unfolding vnorm3_sq[OF dim_pflag[of 3 _ "hflag \<kappa> a - hflag \<kappa> b", unfolded d]] pflag3_entries[OF d] i1 i2 e
    by simp
qed

lemma pflag_flag_norm:
  "\<parallel>pflag 3 (\<lambda>c. c \<noteq> 0) (hflag \<kappa> a)\<parallel>\<^sup>2 = (filt_f \<kappa> a)\<^sup>2 + (filt_g \<kappa> a)\<^sup>2"
  unfolding vnorm3_sq[OF dim_pflag[of 3 _ "hflag \<kappa> a", unfolded dim_hflag]] pflag3_entries[OF dim_hflag] hflag_entries
  by simp

lemma pflag_tensor_left:
  assumes a: "dim_vec a = N" and z: "dim_vec z = m * d" and d0: "0 < d"
  shows "pflag d P (tensor_vec a z) = tensor_vec a (pflag d P z)"
proof (rule eq_vecI)
  have da: "dim_vec (tensor_vec a z) = N * (m * d)" by (rule tensor_vec_dim[OF a z])
  have dp: "dim_vec (tensor_vec a (pflag d P z)) = N * (m * d)" by (rule tensor_vec_dim[OF a]) (simp add: z)
  show "dim_vec (pflag d P (tensor_vec a z)) = dim_vec (tensor_vec a (pflag d P z))" using da dp by simp
  fix r assume "r < dim_vec (tensor_vec a (pflag d P z))"
  hence r: "r < N * (m * d)" using dp by simp
  have md: "0 < m * d" using r by (cases "m * d") simp_all
  have mm: "r mod (m * d) mod d = r mod d" by (simp add: mod_mod_cancel)
  have rm: "r mod (m * d) < m * d" using md by simp
  show "pflag d P (tensor_vec a z) $ r = tensor_vec a (pflag d P z) $ r"
    using r da tensor_vec_index[OF a z r] tensor_vec_index[OF a _ r, of "pflag d P z"] z rm mm by (simp add: pflag_def)
qed

text \<open>Theorem 1(2) on an eigenvector: after post-selecting the flag on $\{\mathrm{well},\mathrm{ill}\}$
the error is at most $\rho$ times the post-selected ideal, $\rho^2=36\pi^4(4+2\pi^2)\kappa^2/(Nt_0)^2$,
by Lemma 3 (relative error) and the window spread.\<close>

theorem flag_post_eigen:
  fixes A :: "complex Matrix.mat" and u :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and t0: "0 < t0" and N: "2 \<le> N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
      and k0: "0 < \<kappa>" and ph: "\<bar>t0 * l\<bar> \<le> pi / 2"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
  defines "P \<equiv> \<lambda>c::nat. c \<noteq> 0"
  shows "\<parallel>pflag 3 P (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec u (unit_vec 3 0)))
           - pflag 3 P (tensor_vec (win_state N) (tensor_vec u (hflag \<kappa> l)))\<parallel>\<^sup>2
         \<le> 36 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2) * \<parallel>pflag 3 P (tensor_vec (win_state N) (tensor_vec u (hflag \<kappa> l)))\<parallel>\<^sup>2"
    and "\<parallel>pflag 3 P (tensor_vec (win_state N) (tensor_vec u (hflag \<kappa> l)))\<parallel>\<^sup>2 = \<parallel>u\<parallel>\<^sup>2 * ((filt_f \<kappa> l)\<^sup>2 + (filt_g \<kappa> l)\<^sup>2)"
proof -
  have N0: "0 < N" using N by simp
  have d3: "0 < (3::nat)" by simp
  let ?x = "tensor_vec (win_state N) (tensor_vec u (unit_vec 3 0))"
  let ?I = "tensor_vec (win_state N) (tensor_vec u (hflag \<kappa> l))"
  let ?W = "hhl_Wd A t0 N 3"
  let ?C = "flag_circuit A t0 N 3 G"
  let ?w = "\<lambda>k. G k *\<^sub>v unit_vec 3 0 - hflag \<kappa> l"
  let ?a = "\<lambda>k. Matrix.vec N (pe_amp_reg N (win_state N) (hhl_phi t0 l)) $ k"
  let ?ff = "(filt_f \<kappa> l)\<^sup>2 + (filt_g \<kappa> l)\<^sup>2"
  note ctx = A t0 N0 u ev dim_win_state d3 G dim_hflag[of \<kappa> l]
  have Wc: "?W \<in> carrier_mat (N * (n * 3)) (N * (n * 3))" by (rule hhl_Wd_carrier[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = "win_state N" and d = 3 and G = G and hid = "hflag \<kappa> l", OF ctx])
  have Wu: "unitary ?W" by (rule hhl_Wd_unitary[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = "win_state N" and d = 3 and G = G and hid = "hflag \<kappa> l", OF ctx])
  have Wd: "?W\<^sup>\<dagger> \<in> carrier_mat (N * (n * 3)) (N * (n * 3))" by (rule dagger_carrier[OF Wc])
  have Wf: "flagdiag 3 (?W\<^sup>\<dagger>)" by (rule flagdiag_dagger[OF hhl_Wd_flagdiag[OF A n0]])
  have u1: "dim_vec (tensor_vec u (hflag \<kappa> l)) = n * 3" by (rule tensor_vec_dim[OF u]) simp
  have dI: "dim_vec ?I = N * (n * 3)" by (rule tensor_vec_dim[OF dim_win_state u1])
  have dC: "dim_vec (?C *\<^sub>v ?x) = N * (n * 3)"
    unfolding flag_circuit_def using Wc A(1) by simp
  have wk: "dim_vec (?w k) = 3" for k by simp
  have pwk: "dim_vec (pflag 3 P (?w k)) = 3" for k by simp
  have err: "?C *\<^sub>v ?x - ?I = ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 3) (\<lambda>k. ?a k \<cdot>\<^sub>v tensor_vec u (?w k))"
    using flag_err_vec[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = "win_state N" and d = 3 and G = G and hid = "hflag \<kappa> l", OF ctx] by (simp add: dalpha_def[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = "win_state N" and d = 3 and G = G and hid = "hflag \<kappa> l", OF ctx])
  have dreg: "dim_vec (?a k \<cdot>\<^sub>v tensor_vec u (?w k)) = n * 3" for k using tensor_vec_dim[OF u wk[of k]] by simp
  have perr: "pflag 3 P (?C *\<^sub>v ?x) - pflag 3 P ?I = ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 3) (\<lambda>k. ?a k \<cdot>\<^sub>v tensor_vec u (pflag 3 P (?w k)))"
  proof -
    have "pflag 3 P (?C *\<^sub>v ?x) - pflag 3 P ?I = pflag 3 P (?C *\<^sub>v ?x - ?I)" by (rule pflag_minus[symmetric]) (simp only: dC dI)
    also have "\<dots> = ?W\<^sup>\<dagger> *\<^sub>v pflag 3 P (reg_sum N (n * 3) (\<lambda>k. ?a k \<cdot>\<^sub>v tensor_vec u (?w k)))"
      unfolding err by (rule pflag_commute[OF Wd Wf]) simp
    also have "pflag 3 P (reg_sum N (n * 3) (\<lambda>k. ?a k \<cdot>\<^sub>v tensor_vec u (?w k))) = reg_sum N (n * 3) (\<lambda>k. ?a k \<cdot>\<^sub>v tensor_vec u (pflag 3 P (?w k)))"
      unfolding pflag_reg_sum[OF dreg d3] pflag_smult pflag_tensor[OF u wk d3] ..
    finally show ?thesis .
  qed
  have nrm: "\<langle>pflag 3 P (?C *\<^sub>v ?x) - pflag 3 P ?I|pflag 3 P (?C *\<^sub>v ?x) - pflag 3 P ?I\<rangle>
             = \<langle>u|u\<rangle> * (\<Sum>k<N. complex_of_real ((cmod (?a k))\<^sup>2) * \<langle>pflag 3 P (?w k)|pflag 3 P (?w k)\<rangle>)"
    unfolding perr by (rule unitary_reg_sum_norm[OF Wc Wu u pwk])
  have tm: "(cmod (?a k))\<^sup>2 * \<parallel>pflag 3 P (?w k)\<parallel>\<^sup>2
            \<le> pi\<^sup>2 * \<kappa>\<^sup>2 * ?ff * ((cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2 * (reg_eig t0 N k - l)\<^sup>2)" if k: "k < N" for k
  proof -
    have ak: "?a k = pe_amp_reg N (win_state N) (hhl_phi t0 l) k" using k by simp
    have "\<parallel>pflag 3 P (?w k)\<parallel>\<^sup>2 = (filt_f \<kappa> (reg_eig t0 N k) - filt_f \<kappa> l)\<^sup>2 + (filt_g \<kappa> (reg_eig t0 N k) - filt_g \<kappa> l)\<^sup>2"
      unfolding Gh[OF k] P_def by (rule pflag_flag_dist)
    also have "\<dots> = (filt_f \<kappa> l - filt_f \<kappa> (reg_eig t0 N k))\<^sup>2 + (filt_g \<kappa> l - filt_g \<kappa> (reg_eig t0 N k))\<^sup>2"
      by (simp add: power2_commute)
    also have "\<dots> \<le> pi\<^sup>2 * \<kappa>\<^sup>2 * (l - reg_eig t0 N k)\<^sup>2 * ?ff" by (rule lemma3[OF k0])
    finally have b: "\<parallel>pflag 3 P (?w k)\<parallel>\<^sup>2 \<le> pi\<^sup>2 * \<kappa>\<^sup>2 * ?ff * (reg_eig t0 N k - l)\<^sup>2" by (simp add: power2_commute mult_ac)
    show ?thesis unfolding ak using mult_left_mono[OF b, of "(cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2"] by (simp add: mult_ac)
  qed
  have S: "(\<Sum>k<N. (cmod (?a k))\<^sup>2 * \<parallel>pflag 3 P (?w k)\<parallel>\<^sup>2) \<le> pi\<^sup>2 * \<kappa>\<^sup>2 * ?ff * (36 * pi\<^sup>2 * (4 + 2 * pi\<^sup>2) / ((real N)\<^sup>2 * t0\<^sup>2))"
  proof -
    have "(\<Sum>k<N. (cmod (?a k))\<^sup>2 * \<parallel>pflag 3 P (?w k)\<parallel>\<^sup>2)
          \<le> (\<Sum>k<N. pi\<^sup>2 * \<kappa>\<^sup>2 * ?ff * ((cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2 * (reg_eig t0 N k - l)\<^sup>2))"
      by (rule sum_mono) (rule tm, simp)
    also have "\<dots> = pi\<^sup>2 * \<kappa>\<^sup>2 * ?ff * (\<Sum>k<N. (cmod (pe_amp_reg N (win_state N) (hhl_phi t0 l) k))\<^sup>2 * (reg_eig t0 N k - l)\<^sup>2)"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> pi\<^sup>2 * \<kappa>\<^sup>2 * ?ff * (36 * pi\<^sup>2 * (4 + 2 * pi\<^sup>2) / ((real N)\<^sup>2 * t0\<^sup>2))"
      by (intro mult_left_mono window_spread[OF t0 N ph]) simp
    finally show ?thesis .
  qed
  have I2: "\<parallel>pflag 3 P ?I\<parallel>\<^sup>2 = \<parallel>u\<parallel>\<^sup>2 * ?ff"
  proof -
    have h3: "dim_vec (hflag \<kappa> l) = 3" by simp
    have pI: "pflag 3 P ?I = tensor_vec (win_state N) (tensor_vec u (pflag 3 P (hflag \<kappa> l)))"
      unfolding pflag_tensor_left[OF dim_win_state u1 d3] pflag_tensor[OF u h3 d3] ..
    have p3: "dim_vec (pflag 3 P (hflag \<kappa> l)) = 3" by simp
    have up: "dim_vec (tensor_vec u (pflag 3 P (hflag \<kappa> l))) = n * 3" by (rule tensor_vec_dim[OF u p3])
    have "\<parallel>pflag 3 P ?I\<parallel> = \<parallel>u\<parallel> * \<parallel>pflag 3 P (hflag \<kappa> l)\<parallel>"
      unfolding pI vnorm_tensor[OF dim_win_state up] vnorm_tensor[OF u p3] win_state_norm[OF N] by simp
    hence "\<parallel>pflag 3 P ?I\<parallel>\<^sup>2 = \<parallel>u\<parallel>\<^sup>2 * \<parallel>pflag 3 P (hflag \<kappa> l)\<parallel>\<^sup>2" by (simp add: power_mult_distrib)
    thus ?thesis unfolding P_def pflag_flag_norm .
  qed
  thus "\<parallel>pflag 3 P ?I\<parallel>\<^sup>2 = \<parallel>u\<parallel>\<^sup>2 * ?ff" .
  have "\<parallel>pflag 3 P (?C *\<^sub>v ?x) - pflag 3 P ?I\<parallel>\<^sup>2 = \<parallel>u\<parallel>\<^sup>2 * (\<Sum>k<N. (cmod (?a k))\<^sup>2 * \<parallel>pflag 3 P (?w k)\<parallel>\<^sup>2)"
  proof -
    have "complex_of_real (\<parallel>pflag 3 P (?C *\<^sub>v ?x) - pflag 3 P ?I\<parallel>\<^sup>2)
          = complex_of_real (\<parallel>u\<parallel>\<^sup>2) * (\<Sum>k<N. complex_of_real ((cmod (?a k))\<^sup>2) * complex_of_real (\<parallel>pflag 3 P (?w k)\<parallel>\<^sup>2))"
      unfolding cpx_vec_length_inner_prod nrm ..
    also have "\<dots> = complex_of_real (\<parallel>u\<parallel>\<^sup>2 * (\<Sum>k<N. (cmod (?a k))\<^sup>2 * \<parallel>pflag 3 P (?w k)\<parallel>\<^sup>2))"
      by (simp add: of_real_sum)
    finally show ?thesis by (simp only: of_real_eq_iff)
  qed
  also have "\<dots> \<le> \<parallel>u\<parallel>\<^sup>2 * (pi\<^sup>2 * \<kappa>\<^sup>2 * ?ff * (36 * pi\<^sup>2 * (4 + 2 * pi\<^sup>2) / ((real N)\<^sup>2 * t0\<^sup>2)))"
    by (intro mult_left_mono S) simp
  also have "\<dots> = 36 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2) * (\<parallel>u\<parallel>\<^sup>2 * ?ff)"
    by (simp add: field_simps power2_eq_square power4_eq_xxxx)
  finally show "\<parallel>pflag 3 P (?C *\<^sub>v ?x) - pflag 3 P ?I\<parallel>\<^sup>2
         \<le> 36 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2) * \<parallel>pflag 3 P ?I\<parallel>\<^sup>2" unfolding I2 .
qed

end
