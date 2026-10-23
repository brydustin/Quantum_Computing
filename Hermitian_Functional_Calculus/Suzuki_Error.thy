theory Suzuki_Error
  imports Suzuki_Order
begin

section \<open>Higher-order product formulas\<close>

text \<open>Suzuki's formula of order $2k+2$ over $r$ steps is within
$r(2|F|+1)(\Lambda|t|/r)^{2k+3}e^{\Lambda|t|/r}/(2k+3)!$ of $e^{itH}$ (\<open>suzuki_error\<close>), so
$r\sim|t|^{1+1/(2k+2)}$ steps suffice.  The proof compares both sides with their Taylor
polynomials of degree $2k+2$, which agree by \<open>suzuki_order\<close>.\<close>

lemma fact_mult_le_fact_add: "fact i * fact k \<le> (fact (i + k) :: real)"
proof (induction k)
  case (Suc k)
  have "fact i * fact (Suc k) = (fact i * fact k) * real (Suc k)" by (simp add: algebra_simps)
  also have "\<dots> \<le> fact (i + k) * real (Suc (i + k))" by (rule mult_mono) (use Suc.IH in auto)
  also have "\<dots> = fact (i + Suc k)" by (simp add: algebra_simps)
  finally show ?case .
qed simp

lemma exp_tail:
  fixes z :: complex
  shows "cmod (exp z - (\<Sum>q\<le>P. z ^ q / fact q)) \<le> cmod z ^ Suc P * exp (cmod z) / fact (Suc P)"
proof -
  let ?f = "\<lambda>n. z ^ n /\<^sub>R fact n" and ?x = "cmod z"
  have s: "?f sums exp z" by (rule exp_converges)
  have t: "(\<lambda>i. ?f (i + Suc P)) sums (exp z - (\<Sum>i<Suc P. ?f i))" by (rule sums_split_initial_segment[OF s])
  have e: "exp z - (\<Sum>q\<le>P. z ^ q / fact q) = (\<Sum>i. ?f (i + Suc P))"
    using sums_unique[OF t] by (simp add: lessThan_Suc_atMost scaleR_conv_of_real field_simps)
  have sn: "summable (\<lambda>i. norm (?f (i + Suc P)))"
    by (rule summable_ignore_initial_segment[OF summable_norm_exp])
  have sx: "summable (\<lambda>i. ?x ^ i / fact i)" using summable_exp[of ?x] by (simp add: field_simps)
  have "cmod (\<Sum>i. ?f (i + Suc P)) \<le> (\<Sum>i. norm (?f (i + Suc P)))" by (rule summable_norm[OF sn])
  also have "\<dots> \<le> (\<Sum>i. ?x ^ Suc P / fact (Suc P) * (?x ^ i / fact i))"
  proof (rule suminf_le)
    fix i
    have "norm (?f (i + Suc P)) = ?x ^ (i + Suc P) / fact (i + Suc P)" by (simp add: norm_power norm_mult field_simps del: fact_Suc power_Suc add_Suc_right)
    also have "\<dots> \<le> ?x ^ (i + Suc P) / (fact i * fact (Suc P))"
      by (rule divide_left_mono) (use fact_mult_le_fact_add[of i "Suc P"] in \<open>simp_all del: fact_Suc add_Suc_right\<close>)
    also have "\<dots> = ?x ^ Suc P / fact (Suc P) * (?x ^ i / fact i)" by (simp add: power_add field_simps)
    finally show "norm (?f (i + Suc P)) \<le> ?x ^ Suc P / fact (Suc P) * (?x ^ i / fact i)" .
  qed (fact sn, fact summable_mult[OF sx, of "?x ^ Suc P / fact (Suc P)"])
  also have "\<dots> = ?x ^ Suc P / fact (Suc P) * exp ?x"
  proof -
    have ex: "(\<Sum>i. ?x ^ i / fact i) = exp ?x"
      using sums_unique[OF exp_converges[of ?x]] by (simp add: field_simps)
    show ?thesis using suminf_mult[OF sx, of "?x ^ Suc P / fact (Suc P)"] ex by simp
  qed
  finally show ?thesis using e by (simp add: field_simps)
qed

lemma matrix_sum_eigen:
  fixes F :: "nat \<Rightarrow> complex Matrix.mat"
  assumes F: "\<And>q. q < m \<Longrightarrow> F q \<in> carrier_mat n n" and v: "dim_vec v = n"
      and ev: "\<And>q. q < m \<Longrightarrow> F q *\<^sub>v v = c q \<cdot>\<^sub>v v"
  shows "matrix_sum n F m *\<^sub>v v = (\<Sum>q<m. c q) \<cdot>\<^sub>v v"
  using F ev
proof (induction m)
  case 0
  show ?case using v by (auto intro!: eq_vecI)
next
  case (Suc m)
  have S: "matrix_sum n F m \<in> carrier_mat n n" by (rule matrix_sum_dim) (use Suc.prems in auto)
  have "matrix_sum n F (Suc m) *\<^sub>v v = F m *\<^sub>v v + matrix_sum n F m *\<^sub>v v"
    using add_mult_distrib_mat_vec[OF Suc.prems(1)[of m] S carrier_vecI[OF v]] by simp
  also have "\<dots> = c m \<cdot>\<^sub>v v + (\<Sum>q<m. c q) \<cdot>\<^sub>v v" using Suc by simp
  also have "\<dots> = (\<Sum>q<Suc m. c q) \<cdot>\<^sub>v v" by (auto intro!: eq_vecI simp: algebra_simps)
  finally show ?case .
qed

definition etay :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "etay n H s P = matrix_sum n (\<lambda>q. texp ((\<i> * complex_of_real s) \<cdot>\<^sub>m H) q) (Suc P)"

lemma etay_carrier: "H \<in> carrier_mat n n \<Longrightarrow> etay n H s P \<in> carrier_mat n n"
  unfolding etay_def by (rule matrix_sum_dim) (simp add: texp_def)

lemma etay_eigen:
  assumes H: "H \<in> carrier_mat n n" and v: "dim_vec v = n" and ev: "H *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  shows "etay n H s P *\<^sub>v v = (\<Sum>q\<le>P. (\<i> * complex_of_real (s * l)) ^ q / fact q) \<cdot>\<^sub>v v"
proof -
  have "texp ((\<i> * complex_of_real s) \<cdot>\<^sub>m H) q *\<^sub>v v = ((\<i> * complex_of_real (s * l)) ^ q / fact q) \<cdot>\<^sub>v v" for q
  proof -
    let ?c = "complex_of_real (1 / fact q) * (\<i> * complex_of_real s) ^ q"
    have t: "texp ((\<i> * complex_of_real s) \<cdot>\<^sub>m H) q = ?c \<cdot>\<^sub>m H ^\<^sub>m q"
      using H by (simp add: texp_def smult_pow_mat) (rule eq_matI, auto)
    have Hq: "H ^\<^sub>m q \<in> carrier_mat n n" using H by simp
    have "texp ((\<i> * complex_of_real s) \<cdot>\<^sub>m H) q *\<^sub>v v = ?c \<cdot>\<^sub>v ((H ^\<^sub>m q) *\<^sub>v v)"
      unfolding t by (rule smult_mat_mult_mat_vec_assoc[OF Hq carrier_vecI[OF v]])
    also have "\<dots> = ?c \<cdot>\<^sub>v ((complex_of_real l ^ q) \<cdot>\<^sub>v v)" unfolding pow_eigen[OF H v ev] ..
    also have "\<dots> = ((\<i> * complex_of_real (s * l)) ^ q / fact q) \<cdot>\<^sub>v v"
      by (simp add: smult_smult_assoc power_mult_distrib field_simps)
    finally show ?thesis .
  qed
  thus ?thesis unfolding etay_def lessThan_Suc_atMost[symmetric]
    by (intro matrix_sum_eigen[OF _ v]) (use H in \<open>simp_all add: texp_def\<close>)
qed

lemma evolution_taylor:
  assumes H: "herm_bounded n L H" and L: "0 \<le> L"
  shows "op_close n ((\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P)) (evolution H s) (etay n H s P)"
proof -
  have Hc: "H \<in> carrier_mat n n" "hermitian H" using herm_boundedD[OF H] by simp_all
  let ?g = "\<lambda>x. cis (s * x) - (\<Sum>q\<le>P. (\<i> * complex_of_real (s * x)) ^ q / fact q)"
  let ?B = "evolution H s - etay n H s P"
  have mf: "mat_fun ?g H = ?B"
  proof (rule mat_fun_eqI[OF Hc])
    show "?B \<in> carrier_mat n n" by (rule minus_carrier_mat[OF etay_carrier[OF Hc(1)]])
    show "fun_on_eigen H ?g ?B" unfolding fun_on_eigen_def
    proof (intro allI impI)
      fix v l assume v: "dim_vec v = dim_row H" and ev: "H *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
      have vn: "dim_vec v = n" using v Hc(1) by simp
      have "?B *\<^sub>v v = evolution H s *\<^sub>v v - etay n H s P *\<^sub>v v"
        by (rule minus_mult_distrib_mat_vec[OF evolution_carrier[OF Hc] etay_carrier[OF Hc(1)] carrier_vecI[OF vn]])
      also have "\<dots> = ?g l \<cdot>\<^sub>v v"
        using evolution_eigen[OF Hc vn ev] etay_eigen[OF Hc(1) vn ev] by (auto intro!: eq_vecI simp: algebra_simps)
      finally show "?B *\<^sub>v v = ?g l \<cdot>\<^sub>v v" .
    qed
  qed
  have c0: "0 \<le> (\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P)" using L by simp
  show ?thesis unfolding op_close_def
  proof (intro allI impI)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have "evolution H s *\<^sub>v v - etay n H s P *\<^sub>v v = ?B *\<^sub>v v"
      by (rule minus_mult_distrib_mat_vec[OF evolution_carrier[OF Hc] etay_carrier[OF Hc(1)] carrier_vecI[OF v], symmetric])
    also have "\<dots> = mat_fun ?g H *\<^sub>v v" unfolding mf ..
    finally have e: "evolution H s *\<^sub>v v - etay n H s P *\<^sub>v v = mat_fun ?g H *\<^sub>v v" .
    have "\<parallel>mat_fun ?g H *\<^sub>v v\<parallel> \<le> (\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P) * \<parallel>v\<parallel>"
    proof (rule mat_fun_bound[OF Hc c0 _ v])
      fix l assume l: "l \<in> herm_spectrum H"
      have lL: "\<bar>l\<bar> \<le> L" by (rule herm_spectrum_bound[OF Hc(1) herm_boundedD(3)[OF H] l])
      have "cmod (?g l) = cmod (exp (\<i> * complex_of_real (s * l)) - (\<Sum>q\<le>P. (\<i> * complex_of_real (s * l)) ^ q / fact q))"
        by (simp add: cis_conv_exp)
      also have "\<dots> \<le> \<bar>s * l\<bar> ^ Suc P * exp \<bar>s * l\<bar> / fact (Suc P)"
      proof -
        have z: "cmod (\<i> * complex_of_real (s * l)) = \<bar>s * l\<bar>" by (simp add: norm_mult abs_mult)
        show ?thesis using exp_tail[of "\<i> * complex_of_real (s * l)" P] unfolding z .
      qed
      also have "\<dots> \<le> (\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P)"
      proof -
        have sl: "\<bar>s * l\<bar> \<le> \<bar>s\<bar> * L" using lL by (simp add: abs_mult mult_left_mono)
        show ?thesis by (intro divide_right_mono mult_mono power_mono sl) (simp_all add: sl L)
      qed
      finally show "cmod (?g l) \<le> (\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P)" .
    qed
    thus "\<parallel>evolution H s *\<^sub>v v - etay n H s P *\<^sub>v v\<parallel> \<le> (\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P) * \<parallel>v\<parallel>"
      unfolding e .
  qed
qed

lemma square_reindex:
  fixes G :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>q\<le>P. \<Sum>r\<le>Q. G q r) = (\<Sum>p\<le>P + Q. \<Sum>q\<le>p. if q \<le> P \<and> p - q \<le> Q then G q (p - q) else 0)"
proof -
  have "(\<Sum>q\<le>P. \<Sum>r\<le>Q. G q r) = (\<Sum>(q, r)\<in>{..P} \<times> {..Q}. G q r)" by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>(p, q)\<in>{(p, q). p \<le> P + Q \<and> q \<le> p \<and> q \<le> P \<and> p - q \<le> Q}. G q (p - q))"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>(p, q). (q, p - q)" and j = "\<lambda>(q, r). (q + r, q)"]) auto
  also have "\<dots> = (\<Sum>(p, q)\<in>Sigma {..P + Q} (\<lambda>p. {..p}). if q \<le> P \<and> p - q \<le> Q then G q (p - q) else 0)"
    by (rule sum.mono_neutral_cong_left) (auto split: if_splits)
  also have "\<dots> = (\<Sum>p\<le>P + Q. \<Sum>q\<le>p. if q \<le> P \<and> p - q \<le> Q then G q (p - q) else 0)"
    by (rule sum.Sigma[symmetric]) auto
  finally show ?thesis .
qed

definition peval :: "nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "peval n f P t = matrix_sum n (\<lambda>p. (complex_of_real t ^ p) \<cdot>\<^sub>m f p) (Suc P)"

definition trunc :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "trunc n P f p = (if p \<le> P then f p else 0\<^sub>m n n)"

lemma trunc_carr [simp]: "carr n f \<Longrightarrow> carr n (trunc n P f)"
  by (simp add: carr_def trunc_def)

lemma peval_carrier: "carr n f \<Longrightarrow> peval n f P t \<in> carrier_mat n n"
  unfolding peval_def by (rule matrix_sum_dim) simp

lemma peval_index:
  assumes "carr n f" "i < n" "j < n"
  shows "peval n f P t $$ (i, j) = (\<Sum>p\<le>P. complex_of_real t ^ p * f p $$ (i, j))"
  unfolding peval_def lessThan_Suc_atMost[symmetric] using assms by (subst matrix_sum_index) simp_all

lemma peval_mult:
  assumes f: "carr n f" and g: "carr n g"
  shows "peval n f P t * peval n g Q t = peval n (sconv n (trunc n P f) (trunc n Q g)) (P + Q) t"
proof (rule eq_matI)
  let ?t = "complex_of_real t"
  have c: "carr n (sconv n (trunc n P f) (trunc n Q g))" using f g by (simp add: sconv_carr)
  fix i j assume i: "i < dim_row (peval n (sconv n (trunc n P f) (trunc n Q g)) (P + Q) t)"
    and j: "j < dim_col (peval n (sconv n (trunc n P f) (trunc n Q g)) (P + Q) t)"
  have ij: "i < n" "j < n" using i j carrier_matD[OF peval_carrier[OF c]] by auto
  have sw: "(\<Sum>k<n. \<Sum>q\<le>P. \<Sum>r\<le>Q. T k q r) = (\<Sum>q\<le>P. \<Sum>r\<le>Q. \<Sum>k<n. T k q r)" for T :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
    by (subst sum.swap) (rule sum.cong[OF refl], rule sum.swap)
  have "(peval n f P t * peval n g Q t) $$ (i, j) = (\<Sum>k<n. peval n f P t $$ (i, k) * peval n g Q t $$ (k, j))"
    using ij carrier_matD[OF peval_carrier[OF f, where P = P and t = t]] carrier_matD[OF peval_carrier[OF g, where P = Q and t = t]]
    by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<n. (\<Sum>q\<le>P. ?t ^ q * f q $$ (i, k)) * (\<Sum>r\<le>Q. ?t ^ r * g r $$ (k, j)))"
    by (intro sum.cong refl) (simp add: peval_index[OF f ij(1)] peval_index[OF g _ ij(2)])
  also have "\<dots> = (\<Sum>q\<le>P. \<Sum>r\<le>Q. \<Sum>k<n. ?t ^ (q + r) * (f q $$ (i, k) * g r $$ (k, j)))"
    by (simp only: sum_product sw) (simp add: power_add mult_ac)
  also have "\<dots> = (\<Sum>p\<le>P + Q. \<Sum>q\<le>p. if q \<le> P \<and> p - q \<le> Q
      then \<Sum>k<n. ?t ^ (q + (p - q)) * (f q $$ (i, k) * g (p - q) $$ (k, j)) else 0)"
    by (rule square_reindex)
  also have "\<dots> = (\<Sum>p\<le>P + Q. ?t ^ p * (\<Sum>q\<le>p. \<Sum>k<n. trunc n P f q $$ (i, k) * trunc n Q g (p - q) $$ (k, j)))"
    unfolding sum_distrib_left
    by (intro sum.cong refl) (use ij in \<open>auto simp: trunc_def sum_distrib_left mult_ac\<close>)
  also have "\<dots> = peval n (sconv n (trunc n P f) (trunc n Q g)) (P + Q) t $$ (i, j)"
    using peval_index[OF c ij] sconv_index[OF trunc_carr[OF f] trunc_carr[OF g] ij] by simp
  finally show "(peval n f P t * peval n g Q t) $$ (i, j) = peval n (sconv n (trunc n P f) (trunc n Q g)) (P + Q) t $$ (i, j)" .
qed (use carrier_matD[OF peval_carrier[OF f, where P = P and t = t]] carrier_matD[OF peval_carrier[OF g, where P = Q and t = t]]
      carrier_matD[OF peval_carrier[OF sconv_carr[OF trunc_carr[OF f] trunc_carr[OF g]], where P = "P + Q" and t = t]] in simp_all)

definition obnd :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "obnd n c M \<longleftrightarrow> (\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>M *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>)"

lemma obndD: "obnd n c M \<Longrightarrow> dim_vec v = n \<Longrightarrow> \<parallel>M *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>"
  by (simp add: obnd_def)

lemma obnd_zero: "obnd n 0 (0\<^sub>m n n)"
proof -
  have "0\<^sub>m n n *\<^sub>v v = 0\<^sub>v n" if "dim_vec v = n" for v :: "complex Matrix.vec"
    using that by (intro eq_vecI) (auto simp: scalar_prod_def)
  thus ?thesis by (simp add: obnd_def vnorm_zero_vec)
qed

lemma obnd_mult:
  assumes A: "A \<in> carrier_mat n n" "obnd n a A" and B: "B \<in> carrier_mat n n" "obnd n b B" and a: "0 \<le> a"
  shows "obnd n (a * b) (A * B)"
  unfolding obnd_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
  have "\<parallel>(A * B) *\<^sub>v v\<parallel> = \<parallel>A *\<^sub>v (B *\<^sub>v v)\<parallel>" using assoc_mult_mat_vec[OF A(1) B(1) carrier_vecI[OF v]] by simp
  also have "\<dots> \<le> a * \<parallel>B *\<^sub>v v\<parallel>" by (rule obndD[OF A(2)]) (use B(1) in simp)
  also have "\<dots> \<le> a * (b * \<parallel>v\<parallel>)" by (rule mult_left_mono[OF obndD[OF B(2) v] a])
  finally show "\<parallel>(A * B) *\<^sub>v v\<parallel> \<le> a * b * \<parallel>v\<parallel>" by (simp add: mult_ac)
qed

lemma obnd_smult: "A \<in> carrier_mat n n \<Longrightarrow> obnd n a A \<Longrightarrow> obnd n (cmod c * a) (c \<cdot>\<^sub>m A)"
  unfolding obnd_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume A: "A \<in> carrier_mat n n" and b: "\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>A *\<^sub>v v\<parallel> \<le> a * \<parallel>v\<parallel>"
    and v: "dim_vec v = n"
  have "\<parallel>(c \<cdot>\<^sub>m A) *\<^sub>v v\<parallel> = cmod c * \<parallel>A *\<^sub>v v\<parallel>"
    using smult_mat_mult_mat_vec_assoc[OF A carrier_vecI[OF v]] by (simp add: cpx_vec_length_smult)
  also have "\<dots> \<le> cmod c * (a * \<parallel>v\<parallel>)" using b v by (simp add: mult_left_mono)
  finally show "\<parallel>(c \<cdot>\<^sub>m A) *\<^sub>v v\<parallel> \<le> cmod c * a * \<parallel>v\<parallel>" by (simp add: mult_ac)
qed

lemma obnd_matrix_sum:
  assumes "\<And>q. q < m \<Longrightarrow> F q \<in> carrier_mat n n" "\<And>q. q < m \<Longrightarrow> obnd n (c q) (F q)"
  shows "obnd n (\<Sum>q<m. c q) (matrix_sum n F m)"
  using assms
proof (induction m)
  case 0
  show ?case using obnd_zero by simp
next
  case (Suc m)
  have S: "matrix_sum n F m \<in> carrier_mat n n" by (rule matrix_sum_dim) (use Suc.prems in auto)
  have IH: "obnd n (\<Sum>q<m. c q) (matrix_sum n F m)" by (rule Suc.IH) (use Suc.prems in auto)
  show ?case unfolding obnd_def
  proof (intro allI impI)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have "matrix_sum n F (Suc m) *\<^sub>v v = F m *\<^sub>v v + matrix_sum n F m *\<^sub>v v"
      using add_mult_distrib_mat_vec[OF Suc.prems(1)[of m] S carrier_vecI[OF v]] by simp
    hence "\<parallel>matrix_sum n F (Suc m) *\<^sub>v v\<parallel> \<le> \<parallel>F m *\<^sub>v v\<parallel> + \<parallel>matrix_sum n F m *\<^sub>v v\<parallel>"
      using vnorm_add_le[of "F m *\<^sub>v v" "matrix_sum n F m *\<^sub>v v"] Suc.prems(1)[of m] S by simp
    also have "\<dots> \<le> c m * \<parallel>v\<parallel> + (\<Sum>q<m. c q) * \<parallel>v\<parallel>"
      using obndD[OF Suc.prems(2)[of m] v] obndD[OF IH v] by simp
    finally show "\<parallel>matrix_sum n F (Suc m) *\<^sub>v v\<parallel> \<le> (\<Sum>q<Suc m. c q) * \<parallel>v\<parallel>" by (simp add: algebra_simps)
  qed
qed

lemma obnd_pow:
  assumes A: "A \<in> carrier_mat n n" "obnd n a A" and a: "0 \<le> a"
  shows "obnd n (a ^ q) (A ^\<^sub>m q)"
proof (induction q)
  case 0
  show ?case using A(1) by (simp add: obnd_def one_mult_mat_vec[OF carrier_vecI])
next
  case (Suc q)
  have "obnd n (a ^ q * a) (A ^\<^sub>m q * A)" by (rule obnd_mult[OF _ Suc A]) (use A a in simp_all)
  thus ?case by (simp add: mult.commute)
qed

lemma texp_obnd:
  assumes Y: "Y \<in> carrier_mat n n" "obnd n a Y" and a: "0 \<le> a"
  shows "obnd n (a ^ q / fact q) (texp Y q)"
proof -
  have "cmod (complex_of_real (1 / fact q)) * a ^ q = a ^ q / fact q" by (simp only: norm_of_real) simp
  thus ?thesis using obnd_smult[OF pow_carrier_mat[OF Y(1)] obnd_pow[OF Y a], of "complex_of_real (1 / fact q)" q]
    unfolding texp_def by simp
qed

lemma binomial_exp_coef:
  fixes a b :: "'a::field_char_0"
  shows "(\<Sum>q\<le>p. a ^ q * b ^ (p - q) / (fact q * fact (p - q))) = (a + b) ^ p / fact p"
proof -
  have "(a + b) ^ p = (\<Sum>q\<le>p. of_nat (p choose q) * a ^ q * b ^ (p - q))" by (rule binomial_ring)
  also have "\<dots> = fact p * (\<Sum>q\<le>p. a ^ q * b ^ (p - q) / (fact q * fact (p - q)))"
    unfolding sum_distrib_left by (intro sum.cong refl) (simp add: binomial_fact field_simps)
  finally show ?thesis by (simp add: field_simps)
qed

lemma obnd_mono: "obnd n c M \<Longrightarrow> c \<le> c' \<Longrightarrow> obnd n c' M"
  unfolding obnd_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume b: "\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>M *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>" and cc: "c \<le> c'" and v: "dim_vec v = n"
  have "\<parallel>M *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>" using b v by simp
  also have "\<dots> \<le> c' * \<parallel>v\<parallel>" by (rule mult_right_mono[OF cc vnorm_ge0])
  finally show "\<parallel>M *\<^sub>v v\<parallel> \<le> c' * \<parallel>v\<parallel>" .
qed

lemma sconv_obnd:
  assumes f: "carr n f" and g: "carr n g" and bf: "\<And>q. obnd n (cf q) (f q)" and bg: "\<And>q. obnd n (cg q) (g q)"
      and cf: "\<And>q. 0 \<le> cf q"
  shows "obnd n (\<Sum>q\<le>p. cf q * cg (p - q)) (sconv n f g p)"
  unfolding sconv_def lessThan_Suc_atMost[symmetric]
  by (rule obnd_matrix_sum) (use f g in \<open>simp_all add: obnd_mult[OF carr_in[OF f] bf carr_in[OF g] bg cf]\<close>)

definition lam :: "real \<Rightarrow> (real \<times> complex Matrix.mat) list \<Rightarrow> real" where
  "lam L F = (\<Sum>x\<leftarrow>F. \<bar>fst x\<bar>) * L"

lemma lam_nonneg: "0 \<le> L \<Longrightarrow> 0 \<le> lam L F"
  unfolding lam_def by (intro mult_nonneg_nonneg sum_list_nonneg) auto

lemma tomat_carrier: "herm_bounded n L (snd x) \<Longrightarrow> tomat x \<in> carrier_mat n n"
  using herm_boundedD(1) by (simp add: tomat_def)

lemma tomat_obnd:
  assumes "herm_bounded n L (snd x)"
  shows "obnd n (\<bar>fst x\<bar> * L) (tomat x)"
proof -
  have "obnd n L (snd x)" using herm_boundedD(3)[OF assms] by (simp add: obnd_def)
  from obnd_smult[OF herm_boundedD(1)[OF assms] this, of "\<i> * complex_of_real (fst x)"]
  show ?thesis by (simp add: tomat_def norm_mult)
qed

lemma fcoef_obnd:
  assumes F: "\<forall>x \<in> set F. herm_bounded n L (snd x)" and L: "0 \<le> L"
  shows "obnd n (lam L F ^ p / fact p) (fcoef n (map tomat F) p)"
  using F
proof (induction F arbitrary: p)
  case Nil
  show ?case using obnd_zero by (cases p) (simp_all add: lam_def sunit_def obnd_def one_mult_mat_vec[OF carrier_vecI])
next
  case (Cons x G)
  have Y: "tomat x \<in> carrier_mat n n" "obnd n (\<bar>fst x\<bar> * L) (tomat x)"
    using Cons.prems tomat_carrier[of n L x] tomat_obnd[of n L x] by auto
  have G: "\<forall>Z \<in> set (map tomat G). Z \<in> carrier_mat n n" using Cons.prems tomat_carrier by auto
  have a0: "0 \<le> \<bar>fst x\<bar> * L" using L by simp
  have "obnd n (\<Sum>q\<le>p. (\<bar>fst x\<bar> * L) ^ q / fact q * (lam L G ^ (p - q) / fact (p - q))) (sconv n (texp (tomat x)) (fcoef n (map tomat G)) p)"
    by (rule sconv_obnd[OF texp_carr[OF Y(1)] fcoef_carr[OF G] texp_obnd[OF Y a0] Cons.IH]) (use Cons.prems a0 in simp_all)
  moreover have "(\<Sum>q\<le>p. (\<bar>fst x\<bar> * L) ^ q / fact q * (lam L G ^ (p - q) / fact (p - q))) = lam L (x # G) ^ p / fact p"
    using binomial_exp_coef[where a = "\<bar>fst x\<bar> * L" and b = "lam L G" and p = p] by (simp add: lam_def algebra_simps)
  ultimately show ?case by simp
qed

fun sprod :: "nat \<Rightarrow> real \<Rightarrow> (real \<times> complex Matrix.mat) list \<Rightarrow> complex Matrix.mat" where
  "sprod n t [] = 1\<^sub>m n"
| "sprod n t (x # F) = evolution (snd x) (fst x * t) * sprod n t F"

lemma sprod_carrier_unitary:
  assumes "\<forall>x \<in> set F. herm_bounded n L (snd x)"
  shows "sprod n t F \<in> carrier_mat n n \<and> Quantum.unitary (sprod n t F)"
  using assms
proof (induction F)
  case Nil
  show ?case by (simp add: id_is_unitary)
next
  case (Cons x F)
  note h = herm_boundedD[of n L "snd x"]
  have hx: "snd x \<in> carrier_mat n n" "hermitian (snd x)" using Cons.prems h by auto
  have IH: "sprod n t F \<in> carrier_mat n n" "Quantum.unitary (sprod n t F)" using Cons by auto
  have "Quantum.unitary (evolution (snd x) (fst x * t) * sprod n t F)"
    by (rule unitary_mult[OF evolution_unitary[OF hx] IH(2) evolution_carrier[OF hx] IH(1)])
  thus ?case using mult_carrier_mat[OF evolution_carrier[OF hx] IH(1)] by simp
qed

lemma etay_peval:
  assumes H: "H \<in> carrier_mat n n"
  shows "etay n H (a * t) P = peval n (texp (tomat (a, H))) P t"
  unfolding etay_def peval_def tomat_def fst_conv snd_conv
proof (rule matrix_sum_cong)
  fix q assume "q < Suc P"
  have "(\<i> * complex_of_real (a * t)) \<cdot>\<^sub>m H = complex_of_real t \<cdot>\<^sub>m ((\<i> * complex_of_real a) \<cdot>\<^sub>m H)"
    by (rule eq_matI) auto
  thus "texp ((\<i> * complex_of_real (a * t)) \<cdot>\<^sub>m H) q = complex_of_real t ^ q \<cdot>\<^sub>m texp ((\<i> * complex_of_real a) \<cdot>\<^sub>m H) q"
    using texp_smult[of "(\<i> * complex_of_real a) \<cdot>\<^sub>m H" n "complex_of_real t" q] H by (simp add: sscale_def)
qed

lemma peval_cong: "(\<And>p. p \<le> P \<Longrightarrow> f p = g p) \<Longrightarrow> peval n f P t = peval n g P t"
  unfolding peval_def by (rule matrix_sum_cong) simp

lemma peval_split:
  assumes f: "carr n f"
  shows "peval n f (P + Q) t = peval n f P t + matrix_sum n (\<lambda>p. (complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m f (Suc P + p)) Q"
proof (induction Q)
  case 0
  show ?case using peval_carrier[OF f, where P = P and t = t] by simp
next
  case (Suc Q)
  let ?h = "matrix_sum n (\<lambda>p. (complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m f (Suc P + p)) Q"
  have c: "(complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) \<in> carrier_mat n n" "peval n f P t \<in> carrier_mat n n"
    "?h \<in> carrier_mat n n" using f peval_carrier[OF f] by (auto intro!: matrix_sum_dim)
  have "peval n f (P + Suc Q) t = (complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + peval n f (P + Q) t"
    by (simp add: peval_def)
  also have "\<dots> = (complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + (peval n f P t + ?h)" unfolding Suc ..
  also have "\<dots> = ((complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + peval n f P t) + ?h"
    by (rule assoc_add_mat[OF c, symmetric])
  also have "(complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + peval n f P t
      = peval n f P t + (complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q)"
    by (rule comm_add_mat[OF c(1,2)])
  also have "(peval n f P t + (complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q)) + ?h
      = peval n f P t + ((complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + ?h)"
    by (rule assoc_add_mat[OF c(2) c(1) c(3)])
  finally show ?case by simp
qed

lemma partial_tail:
  fixes z :: real
  assumes z: "0 \<le> z"
  shows "(\<Sum>p<Q. z ^ (K + p) / fact (K + p)) \<le> z ^ K * exp z / fact K"
proof -
  have "(\<Sum>p<Q. z ^ (K + p) / fact (K + p)) \<le> (\<Sum>p<Q. z ^ K / fact K * (z ^ p / fact p))"
  proof (rule sum_mono)
    fix p
    have "z ^ (K + p) / fact (K + p) \<le> z ^ (K + p) / (fact K * fact p)"
      by (rule divide_left_mono) (use z fact_mult_le_fact_add[of K p] in simp_all)
    thus "z ^ (K + p) / fact (K + p) \<le> z ^ K / fact K * (z ^ p / fact p)" by (simp add: power_add field_simps)
  qed
  also have "\<dots> = z ^ K / fact K * (\<Sum>p<Q. z ^ p / fact p)" by (simp add: sum_distrib_left)
  also have "(\<Sum>p<Q. z ^ p / fact p) \<le> exp z"
  proof -
    have s: "summable (\<lambda>p. z ^ p / fact p)" using summable_exp[of z] by (simp add: field_simps)
    have "(\<Sum>p<Q. z ^ p / fact p) \<le> (\<Sum>p. z ^ p / fact p)" by (rule sum_le_suminf[OF s]) (use z in simp_all)
    also have "\<dots> = exp z" using sums_unique[OF exp_converges[of z]] by (simp add: field_simps)
    finally show ?thesis .
  qed
  hence "z ^ K / fact K * (\<Sum>p<Q. z ^ p / fact p) \<le> z ^ K / fact K * exp z" by (rule mult_left_mono) (use z in simp)
  finally show ?thesis by simp
qed

lemma peval_obnd:
  assumes f: "carr n f" and b: "\<And>p. obnd n (c p) (f p)"
  shows "obnd n (\<Sum>p\<le>P. \<bar>t\<bar> ^ p * c p) (peval n f P t)"
  unfolding peval_def lessThan_Suc_atMost[symmetric]
proof (rule obnd_matrix_sum)
  fix p
  show "(complex_of_real t ^ p) \<cdot>\<^sub>m f p \<in> carrier_mat n n" using f by simp
  have "cmod (complex_of_real t ^ p) = \<bar>t\<bar> ^ p" by (simp add: norm_power)
  thus "obnd n (\<bar>t\<bar> ^ p * c p) ((complex_of_real t ^ p) \<cdot>\<^sub>m f p)"
    using obnd_smult[OF carr_in[OF f] b, of "complex_of_real t ^ p" p] by simp
qed

lemma peval_sunit: "peval n (sunit n) P t = 1\<^sub>m n"
proof -
  have "peval n (sunit n) P t = (complex_of_real t ^ 0) \<cdot>\<^sub>m sunit n 0"
    unfolding peval_def by (rule matrix_sum_single) (auto simp: sunit_def)
  thus ?thesis by (simp add: sunit_def one_smult_mat)
qed

theorem sprod_approx:
  assumes F: "\<forall>x \<in> set F. herm_bounded n L (snd x)" and L: "0 \<le> L"
  shows "op_close n (2 * real (length F) * (lam L F * \<bar>t\<bar>) ^ Suc P * exp (lam L F * \<bar>t\<bar>) / fact (Suc P))
           (sprod n t F) (peval n (fcoef n (map tomat F)) P t)"
  using F
proof (induction F)
  case Nil
  show ?case unfolding op_close_def
  proof (intro allI impI)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have "sprod n t [] *\<^sub>v v - peval n (fcoef n (map tomat [])) P t *\<^sub>v v = 0\<^sub>v n"
      using v by (intro eq_vecI) (simp_all add: peval_sunit)
    thus "\<parallel>sprod n t [] *\<^sub>v v - peval n (fcoef n (map tomat [])) P t *\<^sub>v v\<parallel>
        \<le> 2 * real (length []) * (lam L [] * \<bar>t\<bar>) ^ Suc P * exp (lam L [] * \<bar>t\<bar>) / fact (Suc P) * \<parallel>v\<parallel>"
      by (simp add: vnorm_zero_vec)
  qed
next
  case (Cons x G)
  let ?a = "fst x" and ?H = "snd x" and ?Y = "tomat x" and ?fG = "fcoef n (map tomat G)"
  let ?x0 = "\<bar>fst x\<bar> * L" and ?y0 = "lam L G" and ?P' = "Suc P"
  let ?z = "(?x0 + ?y0) * \<bar>t\<bar>"
  have hx: "herm_bounded n L ?H" and hG: "\<forall>y \<in> set G. herm_bounded n L (snd y)" using Cons.prems by auto
  have Hc: "?H \<in> carrier_mat n n" "hermitian ?H" using herm_boundedD[OF hx] by simp_all
  have G: "\<forall>Z \<in> set (map tomat G). Z \<in> carrier_mat n n" using hG tomat_carrier by auto
  have Yc: "?Y \<in> carrier_mat n n" and Yb: "obnd n ?x0 ?Y" using tomat_carrier[OF hx] tomat_obnd[OF hx] by simp_all
  have x0: "0 \<le> ?x0" and y0: "0 \<le> ?y0" using L lam_nonneg by simp_all
  have fGc: "carr n ?fG" by (rule fcoef_carr[OF G])
  have tYc: "carr n (texp ?Y)" by (rule texp_carr[OF Yc])
  define E where "E = evolution ?H (?a * t)"
  define T where "T = peval n (texp ?Y) P t"
  define SG where "SG = peval n ?fG P t"
  define W where "W = sprod n t G"
  define C where "C = sconv n (trunc n P (texp ?Y)) (trunc n P ?fG)"
  define hi where "hi = matrix_sum n (\<lambda>p. (complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m C (Suc P + p)) P"
  have Cc: "carr n C" unfolding C_def by (simp add: sconv_carr tYc fGc)
  have Ec: "E \<in> carrier_mat n n" unfolding E_def by (rule evolution_carrier[OF Hc])
  have Tc: "T \<in> carrier_mat n n" unfolding T_def by (rule peval_carrier[OF tYc])
  have SGc: "SG \<in> carrier_mat n n" unfolding SG_def by (rule peval_carrier[OF fGc])
  have Wcu: "W \<in> carrier_mat n n" "Quantum.unitary W" using sprod_carrier_unitary[OF hG] by (simp_all add: W_def)
  have hic: "hi \<in> carrier_mat n n" unfolding hi_def by (rule matrix_sum_dim) (simp add: Cc)
  have fx: "fcoef n (map tomat (x # G)) = sconv n (texp ?Y) ?fG" by simp
  have lamx: "lam L (x # G) * \<bar>t\<bar> = ?z" by (simp add: lam_def algebra_simps)
  have TE: "T = etay n ?H (?a * t) P" unfolding T_def using etay_peval[OF Hc(1), of ?a t P] by (simp add: tomat_def)
  have TSG: "T * SG = peval n (sconv n (texp ?Y) ?fG) P t + hi"
  proof -
    have "T * SG = peval n C (P + P) t" unfolding T_def SG_def C_def by (rule peval_mult[OF tYc fGc])
    also have "\<dots> = peval n C P t + hi" unfolding hi_def by (rule peval_split[OF Cc])
    also have "peval n C P t = peval n (sconv n (texp ?Y) ?fG) P t"
      unfolding C_def by (rule peval_cong, rule sconv_congr) (auto simp: trunc_def)
    finally show ?thesis .
  qed
  \<comment> \<open>the three error terms\<close>
  have rY: "op_close n ((?x0 * \<bar>t\<bar>) ^ ?P' * exp (?x0 * \<bar>t\<bar>) / fact ?P') E T"
  proof -
    have e: "\<bar>?a * t\<bar> * L = ?x0 * \<bar>t\<bar>" by (simp add: abs_mult mult_ac)
    show ?thesis using evolution_taylor[OF hx L, of "?a * t" P] unfolding E_def TE e .
  qed
  have cT: "obnd n (exp (?x0 * \<bar>t\<bar>)) T"
  proof -
    have "obnd n (\<Sum>p\<le>P. \<bar>t\<bar> ^ p * (?x0 ^ p / fact p)) T"
      unfolding T_def by (rule peval_obnd[OF tYc texp_obnd[OF Yc Yb x0]])
    moreover have "(\<Sum>p\<le>P. \<bar>t\<bar> ^ p * (?x0 ^ p / fact p)) \<le> exp (?x0 * \<bar>t\<bar>)"
      using partial_tail[where z = "?x0 * \<bar>t\<bar>" and Q = "Suc P" and K = 0, OF mult_nonneg_nonneg[OF x0 abs_ge_zero]]
      by (simp add: lessThan_Suc_atMost power_mult_distrib mult_ac)
    ultimately show ?thesis by (rule obnd_mono)
  qed
  have Cb: "obnd n ((?x0 + ?y0) ^ p / fact p) (C p)" for p
  proof -
    have tb: "obnd n (?x0 ^ q / fact q) (trunc n P (texp ?Y) q)" for q
      using texp_obnd[OF Yc Yb x0, of q] obnd_mono[OF obnd_zero, of "?x0 ^ q / fact q" n] x0
      by (simp add: trunc_def)
    have gb: "obnd n (?y0 ^ q / fact q) (trunc n P ?fG q)" for q
      using fcoef_obnd[OF hG L, of q] obnd_mono[OF obnd_zero, of "?y0 ^ q / fact q" n] y0
      by (simp add: trunc_def)
    have "obnd n (\<Sum>q\<le>p. ?x0 ^ q / fact q * (?y0 ^ (p - q) / fact (p - q))) (C p)"
      unfolding C_def by (rule sconv_obnd[OF trunc_carr[OF tYc] trunc_carr[OF fGc] tb gb]) (use x0 in simp)
    moreover have "(\<Sum>q\<le>p. ?x0 ^ q / fact q * (?y0 ^ (p - q) / fact (p - q))) = (?x0 + ?y0) ^ p / fact p"
      using binomial_exp_coef[where a = ?x0 and b = ?y0 and p = p] by simp
    ultimately show ?thesis by simp
  qed
  have hb: "obnd n (?z ^ ?P' * exp ?z / fact ?P') hi"
  proof -
    have "obnd n (\<Sum>p<P. \<bar>t\<bar> ^ (Suc P + p) * ((?x0 + ?y0) ^ (Suc P + p) / fact (Suc P + p))) hi"
    proof (unfold hi_def, rule obnd_matrix_sum)
      fix p
      show "(complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m C (Suc P + p) \<in> carrier_mat n n" using Cc by simp
      have "cmod (complex_of_real t ^ (Suc P + p)) = \<bar>t\<bar> ^ (Suc P + p)" by (simp only: norm_power norm_of_real)
      thus "obnd n (\<bar>t\<bar> ^ (Suc P + p) * ((?x0 + ?y0) ^ (Suc P + p) / fact (Suc P + p)))
          ((complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m C (Suc P + p))"
        using obnd_smult[OF carr_in[OF Cc] Cb, of "complex_of_real t ^ (Suc P + p)" "Suc P + p"] by simp
    qed
    moreover have "(\<Sum>p<P. \<bar>t\<bar> ^ (Suc P + p) * ((?x0 + ?y0) ^ (Suc P + p) / fact (Suc P + p)))
        \<le> ?z ^ ?P' * exp ?z / fact ?P'"
      using partial_tail[where z = ?z and Q = P and K = "Suc P", OF mult_nonneg_nonneg[OF add_nonneg_nonneg[OF x0 y0] abs_ge_zero]]
      by (simp add: power_mult_distrib mult_ac)
    ultimately show ?thesis by (rule obnd_mono)
  qed
  let ?rG = "2 * real (length G) * (?y0 * \<bar>t\<bar>) ^ ?P' * exp (?y0 * \<bar>t\<bar>) / fact ?P'"
  have IH: "op_close n ?rG W SG" using Cons.IH[OF hG] by (simp add: W_def SG_def)
  show ?case unfolding op_close_def lamx
  proof (intro allI impI)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    define w where "w = W *\<^sub>v v"
    have wn: "dim_vec w = n" and nw: "\<parallel>w\<parallel> = \<parallel>v\<parallel>" using Wcu v unitary_vnorm[OF Wcu v] by (simp_all add: w_def)
    have sp: "sprod n t (x # G) *\<^sub>v v = E *\<^sub>v w"
      unfolding w_def E_def W_def using assoc_mult_mat_vec[OF evolution_carrier[OF Hc] _ carrier_vecI[OF v]] Wcu(1)
      by (simp add: W_def)
    have pf: "peval n (fcoef n (map tomat (x # G))) P t *\<^sub>v v = peval n (sconv n (texp ?Y) ?fG) P t *\<^sub>v v" by simp
    let ?pf = "peval n (sconv n (texp ?Y) ?fG) P t"
    have pfc: "?pf \<in> carrier_mat n n" by (rule peval_carrier) (simp add: sconv_carr tYc fGc)
    have e3: "T *\<^sub>v (SG *\<^sub>v v) - ?pf *\<^sub>v v = hi *\<^sub>v v"
    proof -
      have "T *\<^sub>v (SG *\<^sub>v v) = (?pf + hi) *\<^sub>v v" using assoc_mult_mat_vec[OF Tc SGc carrier_vecI[OF v]] TSG by simp
      also have "\<dots> = ?pf *\<^sub>v v + hi *\<^sub>v v" by (rule add_mult_distrib_mat_vec[OF pfc hic carrier_vecI[OF v]])
      finally have tsg: "T *\<^sub>v (SG *\<^sub>v v) = ?pf *\<^sub>v v + hi *\<^sub>v v" .
      have g: "dim_vec a = n \<Longrightarrow> dim_vec b = n \<Longrightarrow> (a + b) - a = b" for a b :: "complex Matrix.vec"
        by (intro eq_vecI) auto
      show ?thesis unfolding tsg by (rule g) (use pfc hic v in simp_all)
    qed
    have e2: "T *\<^sub>v w - T *\<^sub>v (SG *\<^sub>v v) = T *\<^sub>v (w - SG *\<^sub>v v)"
    proof -
      have "SG *\<^sub>v v \<in> carrier_vec n" by (rule carrier_vecI) (use SGc in simp)
      thus ?thesis by (rule mult_minus_distrib_mat_vec[OF Tc carrier_vecI[OF wn], symmetric])
    qed
    have b1: "\<parallel>E *\<^sub>v w - T *\<^sub>v w\<parallel> \<le> (?x0 * \<bar>t\<bar>) ^ ?P' * exp (?x0 * \<bar>t\<bar>) / fact ?P' * \<parallel>v\<parallel>"
      using op_closeD[OF rY wn] nw by simp
    have b2: "\<parallel>T *\<^sub>v (w - SG *\<^sub>v v)\<parallel> \<le> exp (?x0 * \<bar>t\<bar>) * (?rG * \<parallel>v\<parallel>)"
    proof -
      have "\<parallel>T *\<^sub>v (w - SG *\<^sub>v v)\<parallel> \<le> exp (?x0 * \<bar>t\<bar>) * \<parallel>w - SG *\<^sub>v v\<parallel>"
        by (rule obndD[OF cT]) (use wn SGc in simp)
      also have "\<parallel>w - SG *\<^sub>v v\<parallel> \<le> ?rG * \<parallel>v\<parallel>" using op_closeD[OF IH v] by (simp add: w_def)
      finally show ?thesis by simp
    qed
    have b3: "\<parallel>hi *\<^sub>v v\<parallel> \<le> ?z ^ ?P' * exp ?z / fact ?P' * \<parallel>v\<parallel>" by (rule obndD[OF hb v])
    have "\<parallel>E *\<^sub>v w - ?pf *\<^sub>v v\<parallel> \<le> \<parallel>E *\<^sub>v w - T *\<^sub>v w\<parallel> + \<parallel>T *\<^sub>v w - ?pf *\<^sub>v v\<parallel>"
      by (rule vnorm_diff_le[where n = n]) (use Ec Tc pfc wn v in simp_all)
    also have "\<parallel>T *\<^sub>v w - ?pf *\<^sub>v v\<parallel> \<le> \<parallel>T *\<^sub>v w - T *\<^sub>v (SG *\<^sub>v v)\<parallel> + \<parallel>T *\<^sub>v (SG *\<^sub>v v) - ?pf *\<^sub>v v\<parallel>"
      by (rule vnorm_diff_le[where n = n]) (use Tc SGc pfc wn v in simp_all)
    finally have tri: "\<parallel>E *\<^sub>v w - ?pf *\<^sub>v v\<parallel> \<le> (?x0 * \<bar>t\<bar>) ^ ?P' * exp (?x0 * \<bar>t\<bar>) / fact ?P' * \<parallel>v\<parallel>
        + exp (?x0 * \<bar>t\<bar>) * (?rG * \<parallel>v\<parallel>) + ?z ^ ?P' * exp ?z / fact ?P' * \<parallel>v\<parallel>"
      using b1 b2 b3 unfolding e2 e3 by linarith
    have z0: "0 \<le> ?z" "?x0 * \<bar>t\<bar> \<le> ?z" "?y0 * \<bar>t\<bar> \<le> ?z" using x0 y0 by (simp_all add: distrib_right)
    have k1: "(?x0 * \<bar>t\<bar>) ^ ?P' * exp (?x0 * \<bar>t\<bar>) \<le> ?z ^ ?P' * exp ?z"
      by (intro mult_mono power_mono) (use z0 x0 y0 in simp_all)
    have k2: "exp (?x0 * \<bar>t\<bar>) * ((?y0 * \<bar>t\<bar>) ^ ?P' * exp (?y0 * \<bar>t\<bar>)) \<le> ?z ^ ?P' * exp ?z"
    proof -
      have "exp (?x0 * \<bar>t\<bar>) * exp (?y0 * \<bar>t\<bar>) = exp ?z" by (simp add: exp_add[symmetric] distrib_right)
      moreover have "(?y0 * \<bar>t\<bar>) ^ ?P' \<le> ?z ^ ?P'" by (rule power_mono) (use z0 y0 in simp_all)
      ultimately show ?thesis by (metis mult.left_commute mult_right_mono exp_ge_zero)
    qed
    have "(?x0 * \<bar>t\<bar>) ^ ?P' * exp (?x0 * \<bar>t\<bar>) / fact ?P' * \<parallel>v\<parallel>
        + exp (?x0 * \<bar>t\<bar>) * (?rG * \<parallel>v\<parallel>) + ?z ^ ?P' * exp ?z / fact ?P' * \<parallel>v\<parallel>
        \<le> 2 * real (length (x # G)) * ?z ^ ?P' * exp ?z / fact ?P' * \<parallel>v\<parallel>"
    proof -
      have "(?x0 * \<bar>t\<bar>) ^ ?P' * exp (?x0 * \<bar>t\<bar>) + exp (?x0 * \<bar>t\<bar>) * (2 * real (length G) * (?y0 * \<bar>t\<bar>) ^ ?P' * exp (?y0 * \<bar>t\<bar>))
          + ?z ^ ?P' * exp ?z \<le> 2 * real (length (x # G)) * (?z ^ ?P' * exp ?z)"
        using k1 mult_left_mono[OF k2, of "2 * real (length G)"] by (simp add: algebra_simps)
      hence "((?x0 * \<bar>t\<bar>) ^ ?P' * exp (?x0 * \<bar>t\<bar>) + exp (?x0 * \<bar>t\<bar>) * (2 * real (length G) * (?y0 * \<bar>t\<bar>) ^ ?P' * exp (?y0 * \<bar>t\<bar>))
          + ?z ^ ?P' * exp ?z) / fact ?P' * \<parallel>v\<parallel> \<le> 2 * real (length (x # G)) * (?z ^ ?P' * exp ?z) / fact ?P' * \<parallel>v\<parallel>"
        by (intro mult_right_mono divide_right_mono) (simp_all add: vnorm_ge0)
      thus ?thesis by (simp add: algebra_simps add_divide_distrib)
    qed
    with tri show "\<parallel>sprod n t (x # G) *\<^sub>v v - peval n (fcoef n (map tomat (x # G))) P t *\<^sub>v v\<parallel>
        \<le> 2 * real (length (x # G)) * ?z ^ ?P' * exp ?z / fact ?P' * \<parallel>v\<parallel>"
      unfolding sp pf by linarith
  qed
qed


lemma op_close_trans:
  assumes "op_close n a U V" "op_close n b V W" "U \<in> carrier_mat n n" "V \<in> carrier_mat n n" "W \<in> carrier_mat n n"
  shows "op_close n (a + b) U W"
  unfolding op_close_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
  have "\<parallel>U *\<^sub>v v - W *\<^sub>v v\<parallel> \<le> \<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel> + \<parallel>V *\<^sub>v v - W *\<^sub>v v\<parallel>"
    by (rule vnorm_diff_le[where n = n]) (use assms in simp_all)
  also have "\<dots> \<le> a * \<parallel>v\<parallel> + b * \<parallel>v\<parallel>" using op_closeD[OF assms(1) v] op_closeD[OF assms(2) v] by simp
  finally show "\<parallel>U *\<^sub>v v - W *\<^sub>v v\<parallel> \<le> (a + b) * \<parallel>v\<parallel>" by (simp add: algebra_simps)
qed

lemma op_close_mono:
  assumes "op_close n a U V" "a \<le> b"
  shows "op_close n b U V"
  unfolding op_close_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume "dim_vec v = n"
  thus "\<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel> \<le> b * \<parallel>v\<parallel>"
    using op_closeD[OF assms(1)] mult_right_mono[OF assms(2) vnorm_ge0[of v]] order_trans by blast
qed

lemma hsum_herm_bounded:
  "\<forall>H \<in> set Hs. herm_bounded n L H \<Longrightarrow> herm_bounded n (real (length Hs) * L) (hsum n Hs)"
  unfolding herm_bounded_def[of n "real (length Hs) * L"]
  using hsum_carrier[of Hs n] hsum_hermitian[of Hs n L] hsum_bound[of Hs n L] herm_boundedD(1) by blast

lemma length_suzuki: "length (suzuki k Hs) = 2 * 5 ^ k * length Hs"
  by (induction k) (simp_all add: strang_def suz_rs_def Let_def length_concat comp_def)

lemma sum_suzuki: "(\<Sum>x\<leftarrow>suzuki k Hs. fst x) = real (length Hs)"
proof (induction k)
  case 0
  show ?case by (simp add: strang_def comp_def sum_list_triv rev_map)
next
  case (Suc k)
  thus ?case by (simp add: suz_rs_def Let_def comp_def sum_list_const_mult) (simp add: algebra_simps)
qed

lemma lam_suzuki: "0 \<le> L \<Longrightarrow> real (length Hs) * L \<le> lam L (suzuki k Hs)"
  unfolding lam_def sum_suzuki[of k Hs, symmetric]
  by (intro mult_right_mono sum_list_mono) simp_all

text \<open>One Suzuki step: $\norm{S_{2k+2}(\delta)-e^{i\delta H}}\le(2|F|+1)(\Lambda|\delta|)^{2k+3}e^{\Lambda|\delta|}/(2k+3)!$.\<close>

lemma suzuki_step:
  fixes k :: nat and d :: real
  assumes Hs: "\<forall>H \<in> set Hs. herm_bounded n L H" and L: "0 \<le> L"
  defines "F \<equiv> suzuki k Hs" and "q \<equiv> 2 * k + 3"
  shows "op_close n ((2 * real (length F) + 1) * (lam L F * \<bar>d\<bar>) ^ q * exp (lam L F * \<bar>d\<bar>) / fact q)
           (sprod n d F) (evolution (hsum n Hs) d)"
proof -
  have F: "\<forall>x \<in> set F. herm_bounded n L (snd x)" using Hs suzuki_snd unfolding F_def by blast
  have C: "\<forall>H \<in> set Hs. H \<in> carrier_mat n n" using Hs herm_boundedD(1) by blast
  have Hb: "herm_bounded n (real (length Hs) * L) (hsum n Hs)" by (rule hsum_herm_bounded[OF Hs])
  note Hh = herm_boundedD[OF Hb]
  have mL: "0 \<le> real (length Hs) * L" using L by simp
  let ?X = "\<i> \<cdot>\<^sub>m hsum n Hs" and ?f = "fcoef n (map tomat F)"
  have q: "q = Suc (2 * k + 2)" by (simp add: q_def)
  have pe: "peval n ?f (2 * k + 2) d = etay n (hsum n Hs) d (2 * k + 2)"
  proof -
    have "peval n ?f (2 * k + 2) d = peval n (texp (tomat (1, hsum n Hs))) (2 * k + 2) d"
      by (rule peval_cong) (use suzuki_order[OF C, of k] in \<open>simp add: F_def tomat_def\<close>)
    also have "\<dots> = etay n (hsum n Hs) d (2 * k + 2)" using etay_peval[OF Hh(1), of 1 d] by simp
    finally show ?thesis .
  qed
  have a: "op_close n (2 * real (length F) * (lam L F * \<bar>d\<bar>) ^ q * exp (lam L F * \<bar>d\<bar>) / fact q)
      (sprod n d F) (etay n (hsum n Hs) d (2 * k + 2))"
    using sprod_approx[OF F L, of d "2 * k + 2"] unfolding pe q .
  have b0: "op_close n ((\<bar>d\<bar> * (real (length Hs) * L)) ^ q * exp (\<bar>d\<bar> * (real (length Hs) * L)) / fact q)
      (etay n (hsum n Hs) d (2 * k + 2)) (evolution (hsum n Hs) d)"
    unfolding q by (rule op_close_sym[OF evolution_taylor[OF Hb mL] evolution_carrier[OF Hh(1,2)] etay_carrier[OF Hh(1)]])
  have le: "\<bar>d\<bar> * (real (length Hs) * L) \<le> lam L F * \<bar>d\<bar>"
    using mult_left_mono[OF lam_suzuki[OF L, of Hs k] abs_ge_zero[of d]] unfolding F_def by (simp add: mult_ac)
  have b: "op_close n ((lam L F * \<bar>d\<bar>) ^ q * exp (lam L F * \<bar>d\<bar>) / fact q)
      (etay n (hsum n Hs) d (2 * k + 2)) (evolution (hsum n Hs) d)"
  proof (rule op_close_mono[OF b0])
    have x0: "0 \<le> \<bar>d\<bar> * (real (length Hs) * L)" using mL by simp
    have "(\<bar>d\<bar> * (real (length Hs) * L)) ^ q * exp (\<bar>d\<bar> * (real (length Hs) * L))
        \<le> (lam L F * \<bar>d\<bar>) ^ q * exp (lam L F * \<bar>d\<bar>)"
      by (rule mult_mono[OF power_mono[OF le x0]]) (use le order_trans[OF x0 le] in simp_all)
    thus "(\<bar>d\<bar> * (real (length Hs) * L)) ^ q * exp (\<bar>d\<bar> * (real (length Hs) * L)) / fact q
        \<le> (lam L F * \<bar>d\<bar>) ^ q * exp (lam L F * \<bar>d\<bar>) / fact q"
      by (rule divide_right_mono) simp
  qed
  show ?thesis
    using op_close_trans[OF a b conjunct1[OF sprod_carrier_unitary[OF F]] etay_carrier[OF Hh(1)] evolution_carrier[OF Hh(1,2)]]
    by (simp add: algebra_simps add_divide_distrib)
qed

text \<open>Suzuki's formula of order $2k+2$ over $r$ steps:
$\norm{S_{2k+2}(t/r)^r-e^{itH}}\le r(2|F|+1)(\Lambda|t|/r)^{2k+3}e^{\Lambda|t|/r}/(2k+3)!$,
with $|F|=2\cdot5^k m$ factors and $\Lambda\ge mL$.\<close>

theorem suzuki_error:
  fixes k :: nat and t :: real
  assumes Hs: "\<forall>H \<in> set Hs. herm_bounded n L H" and L: "0 \<le> L" and r: "0 < r"
  defines "F \<equiv> suzuki k Hs" and "q \<equiv> 2 * k + 3"
  shows "op_close n (real r * ((2 * real (length F) + 1) * (lam L F * \<bar>t\<bar> / real r) ^ q
             * exp (lam L F * \<bar>t\<bar> / real r) / fact q))
           (sprod n (t / real r) F ^\<^sub>m r) (evolution (hsum n Hs) t)"
proof -
  have Fh: "\<forall>x \<in> set F. herm_bounded n L (snd x)" using Hs suzuki_snd unfolding F_def by blast
  note Hh = herm_boundedD[OF hsum_herm_bounded[OF Hs]]
  note U = sprod_carrier_unitary[OF Fh, of "t / real r"]
  have d: "lam L F * \<bar>t / real r\<bar> = lam L F * \<bar>t\<bar> / real r" using r by simp
  have c: "op_close n (real r * ((2 * real (length F) + 1) * (lam L F * \<bar>t / real r\<bar>) ^ q
      * exp (lam L F * \<bar>t / real r\<bar>) / fact q))
      (sprod n (t / real r) F ^\<^sub>m r) (evolution (hsum n Hs) (t / real r) ^\<^sub>m r)"
    by (rule op_close_pow[OF conjunct1[OF U] conjunct2[OF U] evolution_carrier[OF Hh(1,2)]
          evolution_unitary[OF Hh(1,2)]]) (use suzuki_step[OF Hs L, of k "t / real r"] in \<open>simp add: F_def q_def\<close>)
  have p: "evolution (hsum n Hs) (t / real r) ^\<^sub>m r = evolution (hsum n Hs) t"
    using evolution_pow[OF Hh(1,2), of "t / real r" r] r by simp
  show ?thesis using c unfolding p d .
qed

end
