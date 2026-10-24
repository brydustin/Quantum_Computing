theory Trotter_Product_Formula
  imports Hermitian_Functional_Calculus
begin

section \<open>The Lie--Trotter product formula\<close>

text \<open>For Hermitian $H_1,\dots,H_m$ with $\norm{H_jv}\le L\norm v$, $r$ rounds of
$e^{itH_1/r}\cdots e^{itH_m/r}$ are within $2(mLt)^2/r$ of $e^{it(H_1+\dots+H_m)}$ (\<open>trotter\<close>).
Each factor is $I+i\delta H_j$ up to $(\delta L)^2$, from $|e^{ix}-1-ix|\le x^2$ and the functional
calculus; the errors add along products and powers of unitaries.\<close>

subsection \<open>Scalar bounds\<close>

text \<open>Taylor remainders of first order:
\[ |\sin x-x|\le\tfrac{x^2}{2},\qquad|\cos x-1|\le\tfrac{x^2}{2},\qquad|e^{ix}-1-ix|\le x^2,\qquad|e^{ix}-1|\le|x|. \]\<close>

lemma sin_minus_x_bound: "\<bar>sin (x::real) - x\<bar> \<le> x\<^sup>2 / 2"
proof (cases "\<bar>x\<bar> \<le> 3")
  case True
  have m: "\<bar>sin x - (\<Sum>m<3. sin_coeff m * x ^ m)\<bar> \<le> inverse (fact 3) * \<bar>x\<bar> ^ 3"
    by (rule Maclaurin_sin_bound)
  have s: "(\<Sum>m<3. sin_coeff m * x ^ m) = x"
    by (simp add: sin_coeff_def eval_nat_numeral)
  have f: "inverse (fact 3) * \<bar>x\<bar> ^ 3 = \<bar>x\<bar> ^ 3 / (6::real)" by (simp add: fact_numeral)
  have "\<bar>sin x - x\<bar> \<le> \<bar>x\<bar> ^ 3 / 6" using m unfolding s f .
  also have "\<dots> = \<bar>x\<bar> * x\<^sup>2 / 6" by (simp add: power2_eq_square power3_eq_cube)
  also have "\<dots> \<le> 3 * x\<^sup>2 / 6" by (rule divide_right_mono, rule mult_right_mono) (use True in simp_all)
  finally show ?thesis by simp
next
  case False
  have "\<bar>sin x - x\<bar> \<le> 1 + \<bar>x\<bar>" using abs_sin_le_one[of x] by linarith
  also have "\<dots> \<le> x\<^sup>2 / 2"
  proof -
    have "3 * \<bar>x\<bar> \<le> \<bar>x\<bar> * \<bar>x\<bar>" using False by (intro mult_right_mono) simp_all
    thus ?thesis using False by (simp add: power2_eq_square)
  qed
  finally show ?thesis .
qed

lemma cos_minus_one_bound: "\<bar>cos (x::real) - 1\<bar> \<le> x\<^sup>2 / 2"
proof -
  have "cos x = 1 - 2 * sin (x / 2) ^ 2" using cos_double_sin[of "x / 2"] by simp
  hence "\<bar>cos x - 1\<bar> = 2 * sin (x / 2) ^ 2" by simp
  also have "\<dots> \<le> 2 * (x / 2) ^ 2"
    using abs_le_square_iff[THEN iffD1, OF abs_sin_x_le_abs_x[of "x / 2"]] by simp
  also have "\<dots> = x\<^sup>2 / 2" by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma cis_remainder: "cmod (cis (x::real) - 1 - \<i> * complex_of_real x) \<le> x\<^sup>2"
proof -
  have "cmod (cis x - 1 - \<i> * complex_of_real x) \<le> \<bar>Re (cis x - 1 - \<i> * complex_of_real x)\<bar> + \<bar>Im (cis x - 1 - \<i> * complex_of_real x)\<bar>"
    by (rule cmod_le)
  also have "\<dots> = \<bar>cos x - 1\<bar> + \<bar>sin x - x\<bar>" by simp
  also have "\<dots> \<le> x\<^sup>2 / 2 + x\<^sup>2 / 2" by (rule add_mono[OF cos_minus_one_bound sin_minus_x_bound])
  finally show ?thesis by simp
qed

lemma cis_minus_one: "cmod (cis (x::real) - 1) \<le> \<bar>x\<bar>"
proof -
  have "(cmod (cis x - 1))\<^sup>2 = (cos x - 1)\<^sup>2 + (sin x)\<^sup>2" by (simp add: cmod_def)
  also have "\<dots> = 2 - 2 * cos x" using sin_cos_squared_add[of x] by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> = 4 * (sin (x / 2))\<^sup>2" using cos_double_sin[of "x / 2"] by simp
  also have "\<dots> \<le> 4 * (x / 2)\<^sup>2"
    using abs_le_square_iff[THEN iffD1, OF abs_sin_x_le_abs_x[of "x / 2"]] by simp
  also have "\<dots> = \<bar>x\<bar>\<^sup>2" by (simp add: power2_eq_square)
  finally show ?thesis by (simp add: abs_le_square_iff[symmetric])
qed

subsection \<open>Bounds from the spectrum\<close>

lemma vnorm_minus_le:
  assumes "dim_vec a = dim_vec b"
  shows "\<parallel>a - b\<parallel> \<le> \<parallel>a\<parallel> + \<parallel>b\<parallel>"
proof -
  have "a - b = a + (-1) \<cdot>\<^sub>v b" using assms by (intro eq_vecI) simp_all
  thus ?thesis using vnorm_add_le[of a "(-1) \<cdot>\<^sub>v b"] assms cpx_vec_length_smult[of "-1" b] by simp
qed

text \<open>If $\norm{Av}\le L\norm v$ for all $v$, every eigenvalue satisfies $|\lambda|\le L$; and if $|g|\le c$ on
the spectrum, $\norm{g(A)v}\le c\norm v$.\<close>

lemma herm_spectrum_bound:
  assumes A: "A \<in> carrier_mat n n" and b: "\<And>v. dim_vec v = n \<Longrightarrow> \<parallel>A *\<^sub>v v\<parallel> \<le> L * \<parallel>v\<parallel>"
      and l: "l \<in> herm_spectrum A"
  shows "\<bar>l\<bar> \<le> L"
proof -
  obtain v where v: "dim_vec v = n" "v \<noteq> 0\<^sub>v n" "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    using l A unfolding herm_spectrum_iff by auto
  have "\<bar>l\<bar> * \<parallel>v\<parallel> = \<parallel>A *\<^sub>v v\<parallel>" using v(3) by (simp add: cpx_vec_length_smult)
  also have "\<dots> \<le> L * \<parallel>v\<parallel>" by (rule b[OF v(1)])
  finally show ?thesis using mult_right_le_imp_le vnorm_pos[OF v(1,2)] by blast
qed

lemma mat_fun_bound:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and c: "0 \<le> c"
      and g: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> cmod (g l) \<le> c" and v: "dim_vec v = n"
  shows "\<parallel>mat_fun g A *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>"
proof -
  obtain U Dl where sd: "spectral_decomp A U Dl" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF d(1)])
  have gD: "diag_matrix (map g Dl) \<in> carrier_mat n n" using diag_matrix_carrier[of "map g Dl"] d(3) by simp
  define w where "w = U\<^sup>\<dagger> *\<^sub>v v"
  have w: "dim_vec w = n" using carrier_matD[OF d(1)] by (simp add: w_def)
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
  have wc: "w \<in> carrier_vec n" by (rule carrier_vecI[OF w])
  have "mat_fun g A *\<^sub>v v = (U * diag_matrix (map g Dl)) *\<^sub>v w"
    unfolding mat_fun_decomp[OF A sd] w_def by (rule assoc_mult_mat_vec[OF mult_carrier_mat[OF d(1) gD] Ud vc])
  also have "\<dots> = U *\<^sub>v (diag_matrix (map g Dl) *\<^sub>v w)" by (rule assoc_mult_mat_vec[OF d(1) gD wc])
  finally have "\<parallel>mat_fun g A *\<^sub>v v\<parallel> = \<parallel>diag_matrix (map g Dl) *\<^sub>v w\<parallel>"
    using unitary_vnorm[OF d(1,2), of "diag_matrix (map g Dl) *\<^sub>v w"] gD d(3) by simp
  also have "\<dots> \<le> c * \<parallel>w\<parallel>"
  proof -
    have dv: "diag_matrix (map g Dl) *\<^sub>v w = Matrix.vec n (\<lambda>i. g (Dl ! i) * w $ i)"
      using diag_matrix_mult_vec[of w "map g Dl"] w d(3) by (auto intro!: eq_vecI)
    have "\<parallel>diag_matrix (map g Dl) *\<^sub>v w\<parallel>\<^sup>2 = (\<Sum>i<n. (cmod (g (Dl ! i) * w $ i))\<^sup>2)"
      unfolding dv vnorm_sq by simp
    also have "\<dots> \<le> (\<Sum>i<n. c\<^sup>2 * (cmod (w $ i))\<^sup>2)"
    proof (rule sum_mono)
      fix i assume "i \<in> {..<n}"
      hence "cmod (g (Dl ! i)) \<le> c" using g spectral_decomp_eig_in_spectrum[OF A(1) sd] by simp
      hence "(cmod (g (Dl ! i)))\<^sup>2 \<le> c\<^sup>2" by (rule power_mono) simp
      thus "(cmod (g (Dl ! i) * w $ i))\<^sup>2 \<le> c\<^sup>2 * (cmod (w $ i))\<^sup>2"
        by (simp add: norm_mult power_mult_distrib mult_right_mono)
    qed
    also have "\<dots> = (c * \<parallel>w\<parallel>)\<^sup>2" by (simp add: vnorm_sq w power_mult_distrib sum_distrib_left)
    finally show ?thesis by (rule power2_le_imp_le) (simp add: c vnorm_ge0)
  qed
  also have "\<parallel>w\<parallel> = \<parallel>v\<parallel>" unfolding w_def by (rule unitary_vnorm[OF Ud unitary_dagger[OF d(2)] v])
  finally show ?thesis .
qed

text \<open>The functions $e^{idx}-1-idx$ and $e^{idx}-1$ applied to $A$ give $e^{idA}-I-idA$ and $e^{idA}-I$.\<close>

lemma mat_fun_evolution_rem:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "mat_fun (\<lambda>x. cis (d * x) - 1 - \<i> * complex_of_real (d * x)) A =
    evolution A d - 1\<^sub>m n - (\<i> * complex_of_real d) \<cdot>\<^sub>m A" (is "_ = ?B")
proof (rule mat_fun_eqI[OF A])
  show "?B \<in> carrier_mat n n" by (intro minus_carrier_mat smult_carrier_mat) (rule A(1))
  show "?B acts_as (\<lambda>x. cis (d * x) - 1 - \<i> * complex_of_real (d * x)) on_eigenvectors_of A" unfolding acts_on_eigenvectors_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vn: "dim_vec v = n" using v A(1) by simp
    have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF vn])
    have e: "evolution A d *\<^sub>v v = cis (d * l) \<cdot>\<^sub>v v" by (rule evolution_eigen[OF A vn ev])
    have E1: "evolution A d - 1\<^sub>m n \<in> carrier_mat n n" by (rule minus_carrier_mat) simp
    have m1: "(evolution A d - 1\<^sub>m n) *\<^sub>v v = evolution A d *\<^sub>v v - 1\<^sub>m n *\<^sub>v v"
      by (rule minus_mult_distrib_mat_vec[OF evolution_carrier[OF A] one_carrier_mat vc])
    have "?B *\<^sub>v v = (evolution A d - 1\<^sub>m n) *\<^sub>v v - ((\<i> * complex_of_real d) \<cdot>\<^sub>m A) *\<^sub>v v"
      by (rule minus_mult_distrib_mat_vec[OF E1 smult_carrier_mat[OF A(1)] vc])
    also have "\<dots> = evolution A d *\<^sub>v v - 1\<^sub>m n *\<^sub>v v - ((\<i> * complex_of_real d) \<cdot>\<^sub>m A) *\<^sub>v v"
      by (simp only: m1)
    also have "\<dots> = cis (d * l) \<cdot>\<^sub>v v - v - (\<i> * complex_of_real d) \<cdot>\<^sub>v (complex_of_real l \<cdot>\<^sub>v v)"
      using e ev smult_mat_mult_mat_vec_assoc[OF A(1) carrier_vecI[OF vn]] vc by simp
    also have "\<dots> = (cis (d * l) - 1 - \<i> * complex_of_real (d * l)) \<cdot>\<^sub>v v"
      by (intro eq_vecI) (simp_all add: algebra_simps)
    finally show "?B *\<^sub>v v = (cis (d * l) - 1 - \<i> * complex_of_real (d * l)) \<cdot>\<^sub>v v" .
  qed
qed

lemma mat_fun_evolution_one:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "mat_fun (\<lambda>x. cis (d * x) - 1) A = evolution A d - 1\<^sub>m n" (is "_ = ?B")
proof (rule mat_fun_eqI[OF A])
  show "?B \<in> carrier_mat n n" by (rule minus_carrier_mat) simp
  show "?B acts_as (\<lambda>x. cis (d * x) - 1) on_eigenvectors_of A" unfolding acts_on_eigenvectors_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vn: "dim_vec v = n" using v A(1) by simp
    have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF vn])
    have e: "evolution A d *\<^sub>v v = cis (d * l) \<cdot>\<^sub>v v" by (rule evolution_eigen[OF A vn ev])
    have "?B *\<^sub>v v = evolution A d *\<^sub>v v - 1\<^sub>m n *\<^sub>v v"
      by (rule minus_mult_distrib_mat_vec[OF evolution_carrier[OF A] one_carrier_mat vc])
    also have "\<dots> = (cis (d * l) - 1) \<cdot>\<^sub>v v" using e vc by (intro eq_vecI, simp_all add: algebra_simps)
    finally show "?B *\<^sub>v v = (cis (d * l) - 1) \<cdot>\<^sub>v v" .
  qed
qed

subsection \<open>Closeness of operators\<close>

text \<open>$\eta$-closeness of two operators: $\norm{Uv-Vv}\le\eta\norm v$ for every $v$.\<close>

definition op_close :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "op_close n \<eta> U V \<longleftrightarrow> (\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>)"

lemma op_closeD: "op_close n \<eta> U V \<Longrightarrow> dim_vec v = n \<Longrightarrow> \<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>"
  by (simp add: op_close_def)

text \<open>Closeness is reflexive and symmetric, and passes to adjoints of unitaries, since
$U^*-V^*=U^*(V-U)V^*$ and unitaries preserve norms.\<close>

lemma op_close_refl:
  assumes e: "0 \<le> \<eta>" and U: "U \<in> carrier_mat n n"
  shows "op_close n \<eta> U U"
proof -
  have z: "U *\<^sub>v v - U *\<^sub>v v = 0\<^sub>v n" if "dim_vec v = n" for v :: "complex Matrix.vec"
    using that U by (intro eq_vecI) simp_all
  show ?thesis unfolding op_close_def
  proof (intro allI impI)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have "\<parallel>U *\<^sub>v v - U *\<^sub>v v\<parallel> = 0" unfolding z[OF v] by (simp add: cpx_vec_length_def)
    thus "\<parallel>U *\<^sub>v v - U *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>" using e vnorm_ge0[of v] by simp
  qed
qed

lemma op_close_sym:
  assumes "op_close n \<eta> U V" "U \<in> carrier_mat n n" "V \<in> carrier_mat n n"
  shows "op_close n \<eta> V U"
  unfolding op_close_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
  have "\<parallel>V *\<^sub>v v - U *\<^sub>v v\<parallel> = \<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel>" by (rule vnorm_minus_commute) (use assms in simp)
  thus "\<parallel>V *\<^sub>v v - U *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>" using op_closeD[OF assms(1) v] by simp
qed

lemma op_close_dagger:
  assumes U: "U \<in> carrier_mat n n" "unitary U" and V: "V \<in> carrier_mat n n" "unitary V"
      and c: "op_close n \<eta> U V"
  shows "op_close n \<eta> (U\<^sup>\<dagger>) (V\<^sup>\<dagger>)"
  unfolding op_close_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
  have vc: "v \<in> carrier_vec n" using v by (rule carrier_vecI)
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" and Vd: "V\<^sup>\<dagger> \<in> carrier_mat n n" using U V by (simp_all add: dagger_carrier)
  have UU: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" and VV: "V * (V\<^sup>\<dagger>) = 1\<^sub>m n" using U V unfolding unitary_def by auto
  let ?w = "V\<^sup>\<dagger> *\<^sub>v v"
  have w: "dim_vec ?w = n" using V(1) by simp
  have dd: "dim_vec (U\<^sup>\<dagger> *\<^sub>v v - ?w) = n" using U(1) V(1) by simp
  have uv: "U *\<^sub>v (U\<^sup>\<dagger> *\<^sub>v v) = v" using assoc_mult_mat_vec[OF U(1) Ud vc, symmetric] UU vc by simp
  have vw: "V *\<^sub>v ?w = v" using assoc_mult_mat_vec[OF V(1) Vd vc, symmetric] VV vc by simp
  have e: "U *\<^sub>v (U\<^sup>\<dagger> *\<^sub>v v - ?w) = V *\<^sub>v ?w - U *\<^sub>v ?w"
  proof -
    have "U *\<^sub>v (U\<^sup>\<dagger> *\<^sub>v v - ?w) = U *\<^sub>v (U\<^sup>\<dagger> *\<^sub>v v) - U *\<^sub>v ?w"
      by (rule mult_minus_distrib_mat_vec[OF U(1)]) (use Ud Vd vc in simp_all)
    thus ?thesis unfolding uv vw .
  qed
  have "\<parallel>U\<^sup>\<dagger> *\<^sub>v v - ?w\<parallel> = \<parallel>U *\<^sub>v (U\<^sup>\<dagger> *\<^sub>v v - ?w)\<parallel>" by (rule unitary_vnorm[OF U dd, symmetric])
  also have "\<dots> = \<parallel>U *\<^sub>v ?w - V *\<^sub>v ?w\<parallel>" unfolding e by (rule vnorm_minus_commute) (use U V in simp)
  also have "\<dots> \<le> \<eta> * \<parallel>?w\<parallel>" by (rule op_closeD[OF c w])
  also have "\<parallel>?w\<parallel> = \<parallel>v\<parallel>" by (rule unitary_vnorm[OF Vd unitary_dagger[OF V(2)] v])
  finally show "\<parallel>U\<^sup>\<dagger> *\<^sub>v v - V\<^sup>\<dagger> *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>" .
qed

subsection \<open>First-order bounds\<close>

context
  fixes A :: "complex Matrix.mat" and n :: nat and L :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and Ab: "\<And>v. dim_vec v = n \<Longrightarrow> \<parallel>A *\<^sub>v v\<parallel> \<le> L * \<parallel>v\<parallel>"
begin

text \<open>For $\norm{Av}\le L\norm v$, the bounds above applied on the spectrum give
\[ \norm{e^{idA}v-v-id\,Av}\le(dL)^2\norm v,\qquad \norm{e^{idA}v-v}\le|d|L\norm v. \]\<close>

lemma evolution_first_order:
  assumes v: "dim_vec v = n"
  shows "\<parallel>evolution A d *\<^sub>v v - v - (\<i> * complex_of_real d) \<cdot>\<^sub>v (A *\<^sub>v v)\<parallel> \<le> (d * L)\<^sup>2 * \<parallel>v\<parallel>"
proof -
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
  have E1: "evolution A d - 1\<^sub>m n \<in> carrier_mat n n" by (rule minus_carrier_mat) simp
  have m1: "(evolution A d - 1\<^sub>m n) *\<^sub>v v = evolution A d *\<^sub>v v - 1\<^sub>m n *\<^sub>v v"
    by (rule minus_mult_distrib_mat_vec[OF evolution_carrier[OF A] one_carrier_mat vc])
  have "mat_fun (\<lambda>x. cis (d * x) - 1 - \<i> * complex_of_real (d * x)) A *\<^sub>v v =
      (evolution A d - 1\<^sub>m n - (\<i> * complex_of_real d) \<cdot>\<^sub>m A) *\<^sub>v v"
    by (simp only: mat_fun_evolution_rem[OF A])
  also have "\<dots> = (evolution A d - 1\<^sub>m n) *\<^sub>v v - ((\<i> * complex_of_real d) \<cdot>\<^sub>m A) *\<^sub>v v"
    by (rule minus_mult_distrib_mat_vec[OF E1 smult_carrier_mat[OF A(1)] vc])
  also have "\<dots> = evolution A d *\<^sub>v v - v - (\<i> * complex_of_real d) \<cdot>\<^sub>v (A *\<^sub>v v)"
    using m1 smult_mat_mult_mat_vec_assoc[OF A(1) carrier_vecI[OF v]] vc by simp
  finally have e: "mat_fun (\<lambda>x. cis (d * x) - 1 - \<i> * complex_of_real (d * x)) A *\<^sub>v v =
      evolution A d *\<^sub>v v - v - (\<i> * complex_of_real d) \<cdot>\<^sub>v (A *\<^sub>v v)" .
  have "\<parallel>mat_fun (\<lambda>x. cis (d * x) - 1 - \<i> * complex_of_real (d * x)) A *\<^sub>v v\<parallel> \<le> (d * L)\<^sup>2 * \<parallel>v\<parallel>"
  proof (rule mat_fun_bound[OF A _ _ v])
    fix l assume l0: "l \<in> herm_spectrum A"
    have l: "\<bar>l\<bar> \<le> L" by (rule herm_spectrum_bound[OF A(1) _ l0]) (rule Ab)
    have "l\<^sup>2 \<le> L\<^sup>2" using power_mono[OF l, of 2] by simp
    hence "d\<^sup>2 * l\<^sup>2 \<le> d\<^sup>2 * L\<^sup>2" by (rule mult_left_mono) simp
    hence "(d * l)\<^sup>2 \<le> (d * L)\<^sup>2" by (simp add: power_mult_distrib)
    thus "cmod (cis (d * l) - 1 - \<i> * complex_of_real (d * l)) \<le> (d * L)\<^sup>2"
      using cis_remainder[of "d * l"] by linarith
  qed simp
  thus ?thesis unfolding e .
qed

lemma evolution_step:
  assumes v: "dim_vec v = n"
  shows "\<parallel>evolution A d *\<^sub>v v - v\<parallel> \<le> \<bar>d\<bar> * L * \<parallel>v\<parallel>"
proof -
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
  have "mat_fun (\<lambda>x. cis (d * x) - 1) A *\<^sub>v v = (evolution A d - 1\<^sub>m n) *\<^sub>v v"
    by (simp only: mat_fun_evolution_one[OF A])
  also have "\<dots> = evolution A d *\<^sub>v v - v"
    using minus_mult_distrib_mat_vec[OF evolution_carrier[OF A] one_carrier_mat vc] vc by simp
  finally have e: "mat_fun (\<lambda>x. cis (d * x) - 1) A *\<^sub>v v = evolution A d *\<^sub>v v - v" .
  have L0: "0 \<le> L" if "0 < n"
  proof -
    have "\<parallel>A *\<^sub>v unit_vec n 0\<parallel> \<le> L * \<parallel>unit_vec n 0\<parallel>" by (rule Ab) simp
    thus ?thesis using that vnorm_ge0[of "A *\<^sub>v unit_vec n 0"] by simp
  qed
  show ?thesis
  proof (cases "n = 0")
    case True
    hence "evolution A d *\<^sub>v v - v = 0\<^sub>v 0" using v evolution_carrier[OF A, of d] by (intro eq_vecI) simp_all
    thus ?thesis using vnorm_ge0[of v] True v by (simp add: cpx_vec_length_def)
  next
    case False
    have "\<parallel>mat_fun (\<lambda>x. cis (d * x) - 1) A *\<^sub>v v\<parallel> \<le> (\<bar>d\<bar> * L) * \<parallel>v\<parallel>"
    proof (rule mat_fun_bound[OF A _ _ v])
      show "0 \<le> \<bar>d\<bar> * L" using L0 False by simp
      fix l assume l0: "l \<in> herm_spectrum A"
      have l: "\<bar>l\<bar> \<le> L" by (rule herm_spectrum_bound[OF A(1) _ l0]) (rule Ab)
      have "\<bar>d\<bar> * \<bar>l\<bar> \<le> \<bar>d\<bar> * L" by (rule mult_left_mono[OF l]) simp
      thus "cmod (cis (d * l) - 1) \<le> \<bar>d\<bar> * L" using cis_minus_one[of "d * l"] by (simp add: abs_mult)
    qed
    thus ?thesis unfolding e by simp
  qed
qed

end

subsection \<open>Products of evolutions\<close>

text \<open>\<open>evolution_product n d Hs\<close> is $e^{idH_1}\cdots e^{idH_m}$ and \<open>hamiltonian_sum n Hs\<close> is $H_1+\dots+H_m$.\<close>

fun evolution_product :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "evolution_product n d [] = 1\<^sub>m n"
| "evolution_product n d (H # Hs) = evolution H d * evolution_product n d Hs"

fun hamiltonian_sum :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "hamiltonian_sum n [] = 0\<^sub>m n n"
| "hamiltonian_sum n (H # Hs) = H + hamiltonian_sum n Hs"

text \<open>\<open>herm_bounded n L H\<close>: $H$ is a Hermitian $n\times n$ matrix with $\norm{Hv}\le L\norm v$.\<close>

definition herm_bounded :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "herm_bounded n L H \<longleftrightarrow> H \<in> carrier_mat n n \<and> hermitian H \<and>
     (\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>H *\<^sub>v v\<parallel> \<le> L * \<parallel>v\<parallel>)"

lemma herm_boundedD:
  assumes "herm_bounded n L H"
  shows "H \<in> carrier_mat n n" "hermitian H" "\<And>v. dim_vec v = n \<Longrightarrow> \<parallel>H *\<^sub>v v\<parallel> \<le> L * \<parallel>v\<parallel>"
  using assms unfolding herm_bounded_def by auto

lemma herm_bounded_herm: "herm_bounded n L H \<Longrightarrow> H \<in> carrier_mat n n \<and> hermitian H"
  by (simp add: herm_bounded_def)

lemma evolution_product_carrier:
  "(\<And>H. H \<in> set Hs \<Longrightarrow> H \<in> carrier_mat n n \<and> hermitian H) \<Longrightarrow> evolution_product n d Hs \<in> carrier_mat n n"
proof (induction Hs)
  case (Cons H Hs)
  have h: "H \<in> carrier_mat n n" "hermitian H" using Cons.prems by auto
  show ?case using mult_carrier_mat[OF evolution_carrier[OF h] Cons.IH] Cons.prems by simp
qed simp

lemma hamiltonian_sum_carrier: "(\<And>H. H \<in> set Hs \<Longrightarrow> H \<in> carrier_mat n n) \<Longrightarrow> hamiltonian_sum n Hs \<in> carrier_mat n n"
  by (induction Hs) auto

context
  fixes n :: nat and L :: real
begin

text \<open>For Hamiltonians bounded by $L$: the product of their evolutions is unitary, their sum is Hermitian
with $\norm{\sum_jH_jv}\le mL\norm v$, and
\[ \norm{e^{idH_1}\cdots e^{idH_m}v-v}\le m\,|d|L\,\norm v. \]\<close>

lemma evolution_product_unitary:
  "(\<And>H. H \<in> set Hs \<Longrightarrow> herm_bounded n L H) \<Longrightarrow> unitary (evolution_product n d Hs)"
proof (induction Hs)
  case Nil
  show ?case by (simp add: id_is_unitary)
next
  case (Cons H Hs)
  note h = herm_boundedD[OF Cons.prems[of H, OF list.set_intros(1)]]
  have "unitary (evolution H d * evolution_product n d Hs)"
    by (rule unitary_mult[OF evolution_unitary[OF h(1,2)] Cons.IH evolution_carrier[OF h(1,2)] evolution_product_carrier])
      (use Cons.prems in \<open>simp_all add: herm_bounded_def\<close>)
  thus ?case by simp
qed

lemma hamiltonian_sum_hermitian:
  "(\<And>H. H \<in> set Hs \<Longrightarrow> herm_bounded n L H) \<Longrightarrow> hermitian (hamiltonian_sum n Hs)"
proof (induction Hs)
  case Nil
  show ?case unfolding hermitian_def by (rule eq_matI) (simp_all add: adjoint_eval)
next
  case (Cons H Hs)
  note h = herm_boundedD[OF Cons.prems[of H, OF list.set_intros(1)]]
  have c: "hamiltonian_sum n Hs \<in> carrier_mat n n" by (rule hamiltonian_sum_carrier) (use Cons.prems in \<open>simp add: herm_bounded_def\<close>)
  have ih: "hermitian (hamiltonian_sum n Hs)" by (rule Cons.IH) (use Cons.prems in simp)
  have "hermitian (H + hamiltonian_sum n Hs)" using adjoint_add[OF h(1) c] h(2) ih unfolding hermitian_def by simp
  thus ?case by simp
qed

lemma hamiltonian_sum_bound:
  "(\<And>H. H \<in> set Hs \<Longrightarrow> herm_bounded n L H) \<Longrightarrow> dim_vec v = n \<Longrightarrow>
   \<parallel>hamiltonian_sum n Hs *\<^sub>v v\<parallel> \<le> real (length Hs) * L * \<parallel>v\<parallel>"
proof (induction Hs)
  case Nil
  have "hamiltonian_sum n [] *\<^sub>v v = 0\<^sub>v n" using carrier_vecI[OF Nil.prems(2)] Nil.prems(2) by (intro eq_vecI) simp_all
  thus ?case by (simp add: cpx_vec_length_def)
next
  case (Cons H Hs)
  note h = herm_boundedD[OF Cons.prems(1)[of H, OF list.set_intros(1)]]
  have S: "hamiltonian_sum n Hs \<in> carrier_mat n n" by (rule hamiltonian_sum_carrier) (use Cons.prems in \<open>simp add: herm_bounded_def\<close>)
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF Cons.prems(2)])
  have "hamiltonian_sum n (H # Hs) *\<^sub>v v = H *\<^sub>v v + hamiltonian_sum n Hs *\<^sub>v v"
    using add_mult_distrib_mat_vec[OF h(1) S vc] by simp
  hence "\<parallel>hamiltonian_sum n (H # Hs) *\<^sub>v v\<parallel> \<le> \<parallel>H *\<^sub>v v\<parallel> + \<parallel>hamiltonian_sum n Hs *\<^sub>v v\<parallel>"
    using vnorm_add_le[of "H *\<^sub>v v" "hamiltonian_sum n Hs *\<^sub>v v"] h(1) S by simp
  also have "\<dots> \<le> L * \<parallel>v\<parallel> + real (length Hs) * L * \<parallel>v\<parallel>"
    using h(3)[OF Cons.prems(2)] Cons.IH Cons.prems by (intro add_mono) simp_all
  finally show ?case by (simp add: algebra_simps)
qed

lemma evolution_product_norm:
  "(\<And>H. H \<in> set Hs \<Longrightarrow> herm_bounded n L H) \<Longrightarrow> dim_vec v = n \<Longrightarrow> \<parallel>evolution_product n d Hs *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
  by (rule unitary_vnorm[OF evolution_product_carrier[OF herm_bounded_herm] evolution_product_unitary])

lemma evolution_product_step:
  "(\<And>H. H \<in> set Hs \<Longrightarrow> herm_bounded n L H) \<Longrightarrow> dim_vec v = n \<Longrightarrow>
   \<parallel>evolution_product n d Hs *\<^sub>v v - v\<parallel> \<le> real (length Hs) * (\<bar>d\<bar> * L) * \<parallel>v\<parallel>"
proof (induction Hs arbitrary: v)
  case Nil
  have "evolution_product n d [] *\<^sub>v v - v = 0\<^sub>v n" using carrier_vecI[OF Nil.prems(2)] Nil.prems(2) by (intro eq_vecI) simp_all
  thus ?case by (simp add: cpx_vec_length_def)
next
  case (Cons H Hs v)
  note h = herm_boundedD[OF Cons.prems(1)[of H, OF list.set_intros(1)]]
  have hs: "\<And>G. G \<in> set Hs \<Longrightarrow> herm_bounded n L G" using Cons.prems(1) by simp
  have P: "evolution_product n d Hs \<in> carrier_mat n n" by (rule evolution_product_carrier[OF herm_bounded_herm[OF hs]])
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF Cons.prems(2)])
  let ?w = "evolution_product n d Hs *\<^sub>v v"
  have w: "dim_vec ?w = n" using P by simp
  have e: "evolution_product n d (H # Hs) *\<^sub>v v = evolution H d *\<^sub>v ?w"
    using assoc_mult_mat_vec[OF evolution_carrier[OF h(1,2)] P vc] by simp
  have "\<parallel>evolution H d *\<^sub>v ?w - v\<parallel> \<le> \<parallel>evolution H d *\<^sub>v ?w - ?w\<parallel> + \<parallel>?w - v\<parallel>"
    by (rule vnorm_diff_le[where n = n]) (use w Cons.prems(2) evolution_carrier[OF h(1,2), of d] in simp_all)
  also have "\<dots> \<le> \<bar>d\<bar> * L * \<parallel>?w\<parallel> + real (length Hs) * (\<bar>d\<bar> * L) * \<parallel>v\<parallel>"
    by (rule add_mono[OF evolution_step[OF h(1,2) h(3) w] Cons.IH[OF hs Cons.prems(2)]])
  also have "\<parallel>?w\<parallel> = \<parallel>v\<parallel>" by (rule evolution_product_norm[OF hs Cons.prems(2)])
  finally show ?case unfolding e by (simp add: algebra_simps)
qed

end

text \<open>To first order the product of the evolutions is the evolution of the sum:
\[ \Bigl\|e^{idH_1}\cdots e^{idH_m}v-v-id\sum_jH_jv\Bigr\|\le m^2(dL)^2\norm v. \]\<close>

lemma evolution_product_first_order:
  fixes n :: nat and L :: real
  shows "(\<And>H. H \<in> set Hs \<Longrightarrow> herm_bounded n L H) \<Longrightarrow> dim_vec v = n \<Longrightarrow>
   \<parallel>evolution_product n d Hs *\<^sub>v v - v - (\<i> * complex_of_real d) \<cdot>\<^sub>v (hamiltonian_sum n Hs *\<^sub>v v)\<parallel>
     \<le> (d * L)\<^sup>2 * (real (length Hs))\<^sup>2 * \<parallel>v\<parallel>"
proof (induction Hs arbitrary: v)
  case Nil
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF Nil.prems(2)])
  have "evolution_product n d [] *\<^sub>v v - v - (\<i> * complex_of_real d) \<cdot>\<^sub>v (hamiltonian_sum n [] *\<^sub>v v) = 0\<^sub>v n"
    using vc Nil.prems(2) by (intro eq_vecI) simp_all
  thus ?case by (simp add: cpx_vec_length_def)
next
  case (Cons H Hs v)
  note h = herm_boundedD[OF Cons.prems(1)[of H, OF list.set_intros(1)]]
  have hs: "\<And>G. G \<in> set Hs \<Longrightarrow> herm_bounded n L G" using Cons.prems(1) by simp
  have v: "dim_vec v = n" by (rule Cons.prems(2))
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
  have P: "evolution_product n d Hs \<in> carrier_mat n n" by (rule evolution_product_carrier[OF herm_bounded_herm[OF hs]])
  have S: "hamiltonian_sum n Hs \<in> carrier_mat n n" by (rule hamiltonian_sum_carrier[OF herm_boundedD(1)[OF hs]])
  have E: "evolution H d \<in> carrier_mat n n" by (rule evolution_carrier[OF h(1,2)])
  define c where "c = \<i> * complex_of_real d"
  define k where "k = real (length Hs)"
  let ?w = "evolution_product n d Hs *\<^sub>v v"
  have w: "dim_vec ?w = n" using P by simp
  have wc: "?w \<in> carrier_vec n" by (rule carrier_vecI[OF w])
  have e1: "evolution_product n d (H # Hs) *\<^sub>v v = evolution H d *\<^sub>v ?w"
    using assoc_mult_mat_vec[OF E P vc] by simp
  have e2: "hamiltonian_sum n (H # Hs) *\<^sub>v v = H *\<^sub>v v + hamiltonian_sum n Hs *\<^sub>v v"
    using add_mult_distrib_mat_vec[OF h(1) S vc] by simp
  have e3: "H *\<^sub>v (?w - v) = H *\<^sub>v ?w - H *\<^sub>v v" by (rule mult_minus_distrib_mat_vec[OF h(1) wc vc])
  have split: "evolution H d *\<^sub>v ?w - v - c \<cdot>\<^sub>v (H *\<^sub>v v + hamiltonian_sum n Hs *\<^sub>v v) =
      (evolution H d *\<^sub>v ?w - ?w - c \<cdot>\<^sub>v (H *\<^sub>v ?w)) + ((?w - v - c \<cdot>\<^sub>v (hamiltonian_sum n Hs *\<^sub>v v)) + c \<cdot>\<^sub>v (H *\<^sub>v (?w - v)))"
    unfolding e3 using E h(1) S w v by (intro eq_vecI) (simp_all add: algebra_simps)
  have b1: "\<parallel>evolution H d *\<^sub>v ?w - ?w - c \<cdot>\<^sub>v (H *\<^sub>v ?w)\<parallel> \<le> (d * L)\<^sup>2 * \<parallel>v\<parallel>"
    using evolution_first_order[OF h(1,2) h(3) w, of d] evolution_product_norm[OF hs v] unfolding c_def by simp
  have b2: "\<parallel>?w - v - c \<cdot>\<^sub>v (hamiltonian_sum n Hs *\<^sub>v v)\<parallel> \<le> (d * L)\<^sup>2 * k\<^sup>2 * \<parallel>v\<parallel>"
    using Cons.IH[OF hs v] unfolding c_def k_def .
  have b3: "\<parallel>c \<cdot>\<^sub>v (H *\<^sub>v (?w - v))\<parallel> \<le> (d * L)\<^sup>2 * k * \<parallel>v\<parallel>"
  proof -
    have "\<parallel>c \<cdot>\<^sub>v (H *\<^sub>v (?w - v))\<parallel> = \<bar>d\<bar> * \<parallel>H *\<^sub>v (?w - v)\<parallel>" by (simp add: cpx_vec_length_smult c_def norm_mult)
    also have "\<dots> \<le> \<bar>d\<bar> * (L * \<parallel>?w - v\<parallel>)" by (rule mult_left_mono[OF h(3)]) (use w v in simp_all)
    also have "\<dots> \<le> \<bar>d\<bar> * (L * (k * (\<bar>d\<bar> * L) * \<parallel>v\<parallel>))"
    proof (cases "n = 0")
      case True
      hence "\<parallel>?w - v\<parallel> = 0" "\<parallel>v\<parallel> = 0" using w v by (simp_all add: cpx_vec_length_def)
      thus ?thesis by simp
    next
      case False
      have L0: "0 \<le> L"
      proof -
        have "\<parallel>H *\<^sub>v unit_vec n 0\<parallel> \<le> L * \<parallel>unit_vec n 0\<parallel>" by (rule h(3)) simp
        thus ?thesis using False vnorm_ge0[of "H *\<^sub>v unit_vec n 0"] by simp
      qed
      show ?thesis
        using evolution_product_step[where d = d, OF hs v] L0 unfolding k_def by (intro mult_left_mono) simp_all
    qed
    also have "\<dots> = (d * L)\<^sup>2 * k * \<parallel>v\<parallel>" by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  have nn: "0 \<le> (d * L)\<^sup>2 * \<parallel>v\<parallel>" using vnorm_ge0[of v] by simp
  have "\<parallel>evolution H d *\<^sub>v ?w - v - c \<cdot>\<^sub>v (H *\<^sub>v v + hamiltonian_sum n Hs *\<^sub>v v)\<parallel>
      \<le> \<parallel>evolution H d *\<^sub>v ?w - ?w - c \<cdot>\<^sub>v (H *\<^sub>v ?w)\<parallel> + (\<parallel>?w - v - c \<cdot>\<^sub>v (hamiltonian_sum n Hs *\<^sub>v v)\<parallel> + \<parallel>c \<cdot>\<^sub>v (H *\<^sub>v (?w - v))\<parallel>)"
  proof -
    let ?X = "evolution H d *\<^sub>v ?w - ?w - c \<cdot>\<^sub>v (H *\<^sub>v ?w)"
    let ?Y = "?w - v - c \<cdot>\<^sub>v (hamiltonian_sum n Hs *\<^sub>v v)" and ?Z = "c \<cdot>\<^sub>v (H *\<^sub>v (?w - v))"
    have dX: "dim_vec ?X = n" and dY: "dim_vec ?Y = n" and dZ: "dim_vec ?Z = n"
      using E h(1) S w v by simp_all
    have "\<parallel>?X + (?Y + ?Z)\<parallel> \<le> \<parallel>?X\<parallel> + \<parallel>?Y + ?Z\<parallel>" by (rule vnorm_add_le) (use dX dY in simp)
    also have "\<parallel>?Y + ?Z\<parallel> \<le> \<parallel>?Y\<parallel> + \<parallel>?Z\<parallel>" by (rule vnorm_add_le) (use dY dZ in simp)
    finally show ?thesis unfolding split by simp
  qed
  also have "\<dots> \<le> (d * L)\<^sup>2 * \<parallel>v\<parallel> + ((d * L)\<^sup>2 * k\<^sup>2 * \<parallel>v\<parallel> + (d * L)\<^sup>2 * k * \<parallel>v\<parallel>)"
    using b1 b2 b3 by linarith
  also have "\<dots> = (d * L)\<^sup>2 * \<parallel>v\<parallel> * (1 + k\<^sup>2 + k)" by (simp add: algebra_simps)
  also have "\<dots> \<le> (d * L)\<^sup>2 * \<parallel>v\<parallel> * (k + 1)\<^sup>2"
    by (rule mult_left_mono[OF _ nn]) (simp add: power2_eq_square algebra_simps k_def)
  finally show ?case unfolding e1 e2 c_def k_def by (simp add: algebra_simps)
qed

text \<open>One Trotter step: $\norm{e^{idH_1}\cdots e^{idH_m}-e^{id(H_1+\dots+H_m)}}\le 2m^2(dL)^2$.\<close>

lemma trotter_step:
  assumes Hs: "\<And>H. H \<in> set Hs \<Longrightarrow> herm_bounded n L H"
  shows "op_close n (2 * (d * L)\<^sup>2 * (real (length Hs))\<^sup>2) (evolution_product n d Hs) (evolution (hamiltonian_sum n Hs) d)"
  unfolding op_close_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
  have P: "evolution_product n d Hs \<in> carrier_mat n n" by (rule evolution_product_carrier[OF herm_bounded_herm[OF Hs]])
  have S: "hamiltonian_sum n Hs \<in> carrier_mat n n" "hermitian (hamiltonian_sum n Hs)"
    using hamiltonian_sum_carrier[OF herm_boundedD(1)[OF Hs]] hamiltonian_sum_hermitian[OF Hs] by simp_all
  have E: "evolution (hamiltonian_sum n Hs) d \<in> carrier_mat n n" by (rule evolution_carrier[OF S])
  let ?c = "\<i> * complex_of_real d" and ?m = "real (length Hs)"
  let ?a = "evolution_product n d Hs *\<^sub>v v - v - ?c \<cdot>\<^sub>v (hamiltonian_sum n Hs *\<^sub>v v)"
  let ?b = "evolution (hamiltonian_sum n Hs) d *\<^sub>v v - v - ?c \<cdot>\<^sub>v (hamiltonian_sum n Hs *\<^sub>v v)"
  have a: "\<parallel>?a\<parallel> \<le> (d * L)\<^sup>2 * ?m\<^sup>2 * \<parallel>v\<parallel>" by (rule evolution_product_first_order[OF Hs v])
  have b: "\<parallel>?b\<parallel> \<le> (d * (?m * L))\<^sup>2 * \<parallel>v\<parallel>"
    by (rule evolution_first_order[OF S _ v]) (rule hamiltonian_sum_bound[OF Hs])
  have "evolution_product n d Hs *\<^sub>v v - evolution (hamiltonian_sum n Hs) d *\<^sub>v v = ?a - ?b"
    using P E S(1) v by (intro eq_vecI) simp_all
  hence "\<parallel>evolution_product n d Hs *\<^sub>v v - evolution (hamiltonian_sum n Hs) d *\<^sub>v v\<parallel> \<le> \<parallel>?a\<parallel> + \<parallel>?b\<parallel>"
    using vnorm_minus_le[of ?a ?b] P E S(1) v by simp
  also have "\<dots> \<le> (d * L)\<^sup>2 * ?m\<^sup>2 * \<parallel>v\<parallel> + (d * (?m * L))\<^sup>2 * \<parallel>v\<parallel>" using a b by linarith
  also have "\<dots> = 2 * (d * L)\<^sup>2 * ?m\<^sup>2 * \<parallel>v\<parallel>" by (simp add: power_mult_distrib algebra_simps)
  finally show "\<parallel>evolution_product n d Hs *\<^sub>v v - evolution (hamiltonian_sum n Hs) d *\<^sub>v v\<parallel> \<le> 2 * (d * L)\<^sup>2 * ?m\<^sup>2 * \<parallel>v\<parallel>" .
qed

text \<open>Errors of unitaries add up along powers.\<close>

lemma op_close_pow:
  assumes U: "U \<in> carrier_mat n n" "unitary U" and V: "V \<in> carrier_mat n n" "unitary V"
      and c: "op_close n \<eta> U V"
  shows "op_close n (real k * \<eta>) (U ^\<^sub>m k) (V ^\<^sub>m k)"
proof (induction k)
  case 0
  show ?case unfolding op_close_def
  proof (intro allI impI)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have "U ^\<^sub>m 0 *\<^sub>v v - V ^\<^sub>m 0 *\<^sub>v v = 0\<^sub>v n" using v carrier_matD[OF U(1)] carrier_matD[OF V(1)] carrier_vecI[OF v] by (intro eq_vecI) simp_all
    thus "\<parallel>U ^\<^sub>m 0 *\<^sub>v v - V ^\<^sub>m 0 *\<^sub>v v\<parallel> \<le> real 0 * \<eta> * \<parallel>v\<parallel>" by (simp add: vnorm_zero_vec)
  qed
next
  case (Suc k)
  show ?case unfolding op_close_def
  proof (intro allI impI)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
    have Uk: "U ^\<^sub>m k \<in> carrier_mat n n" and Vk: "V ^\<^sub>m k \<in> carrier_mat n n"
      using pow_carrier_mat U(1) V(1) by blast+
    have uVk: "unitary (V ^\<^sub>m k)" by (rule unitary_pow[OF V])
    let ?x = "U *\<^sub>v v" and ?y = "V *\<^sub>v v"
    have x: "dim_vec ?x = n" and y: "dim_vec ?y = n" using U(1) V(1) by simp_all
    have e1: "U ^\<^sub>m Suc k *\<^sub>v v = U ^\<^sub>m k *\<^sub>v ?x" using assoc_mult_mat_vec[OF Uk U(1) vc] by simp
    have e2: "V ^\<^sub>m Suc k *\<^sub>v v = V ^\<^sub>m k *\<^sub>v ?y" using assoc_mult_mat_vec[OF Vk V(1) vc] by simp
    have "\<parallel>U ^\<^sub>m k *\<^sub>v ?x - V ^\<^sub>m k *\<^sub>v ?y\<parallel> \<le> \<parallel>U ^\<^sub>m k *\<^sub>v ?x - V ^\<^sub>m k *\<^sub>v ?x\<parallel> + \<parallel>V ^\<^sub>m k *\<^sub>v ?x - V ^\<^sub>m k *\<^sub>v ?y\<parallel>"
      by (rule vnorm_diff_le[where n = n]) (use Uk Vk carrier_matD[OF U(1)] carrier_matD[OF V(1)] in simp_all)
    also have "V ^\<^sub>m k *\<^sub>v ?x - V ^\<^sub>m k *\<^sub>v ?y = V ^\<^sub>m k *\<^sub>v (?x - ?y)"
      by (rule mult_minus_distrib_mat_vec[OF Vk, symmetric]) (use x y in \<open>simp_all add: carrier_vecI\<close>)
    also have "\<parallel>V ^\<^sub>m k *\<^sub>v (?x - ?y)\<parallel> = \<parallel>?x - ?y\<parallel>" by (rule unitary_vnorm[OF Vk uVk]) (use y in simp)
    also have "\<parallel>U ^\<^sub>m k *\<^sub>v ?x - V ^\<^sub>m k *\<^sub>v ?x\<parallel> \<le> real k * \<eta> * \<parallel>?x\<parallel>" by (rule op_closeD[OF Suc x])
    also have "\<parallel>?x\<parallel> = \<parallel>v\<parallel>" by (rule unitary_vnorm[OF U v])
    also have "\<parallel>?x - ?y\<parallel> \<le> \<eta> * \<parallel>v\<parallel>" by (rule op_closeD[OF c v])
    finally show "\<parallel>U ^\<^sub>m Suc k *\<^sub>v v - V ^\<^sub>m Suc k *\<^sub>v v\<parallel> \<le> real (Suc k) * \<eta> * \<parallel>v\<parallel>"
      unfolding e1 e2 by (simp add: algebra_simps)
  qed
qed

text \<open>The Lie--Trotter product formula with explicit error:
$\norm{(e^{itH_1/r}\cdots e^{itH_m/r})^r-e^{it(H_1+\dots+H_m)}}\le 2(mLt)^2/r$.\<close>

theorem trotter:
  assumes Hs: "\<And>H. H \<in> set Hs \<Longrightarrow> herm_bounded n L H" and r: "0 < r"
  shows "op_close n (2 * (real (length Hs) * L * t)\<^sup>2 / real r)
           (evolution_product n (t / real r) Hs ^\<^sub>m r) (evolution (hamiltonian_sum n Hs) t)"
proof -
  have S: "hamiltonian_sum n Hs \<in> carrier_mat n n" "hermitian (hamiltonian_sum n Hs)"
    using hamiltonian_sum_carrier[OF herm_boundedD(1)[OF Hs]] hamiltonian_sum_hermitian[OF Hs] by simp_all
  have c: "op_close n (real r * (2 * (t / real r * L)\<^sup>2 * (real (length Hs))\<^sup>2))
      (evolution_product n (t / real r) Hs ^\<^sub>m r) (evolution (hamiltonian_sum n Hs) (t / real r) ^\<^sub>m r)"
    by (rule op_close_pow[OF evolution_product_carrier[OF herm_bounded_herm[OF Hs]] evolution_product_unitary[OF Hs] evolution_carrier[OF S]
          evolution_unitary[OF S] trotter_step[OF Hs]])
  have p: "evolution (hamiltonian_sum n Hs) (t / real r) ^\<^sub>m r = evolution (hamiltonian_sum n Hs) t"
    using evolution_pow[OF S, of "t / real r" r] r by simp
  have a: "real r * (2 * (t / real r * L)\<^sup>2 * (real (length Hs))\<^sup>2) = 2 * (real (length Hs) * L * t)\<^sup>2 / real r"
    using r by (simp add: power2_eq_square field_simps)
  show ?thesis using c unfolding p a .
qed

end
