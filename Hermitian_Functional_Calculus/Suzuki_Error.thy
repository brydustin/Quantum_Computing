theory Suzuki_Error
  imports Suzuki_Order
begin

section \<open>Higher-order product formulas\<close>

text \<open>Suzuki's formula of order $2k+2$ over $r$ steps is within
$r(2|F|+1)(\Lambda|t|/r)^{2k+3}e^{\Lambda|t|/r}/(2k+3)!$ of $e^{itH}$ (\<open>suzuki_error\<close>), so
$r\sim|t|^{1+1/(2k+2)}$ steps suffice.  The proof compares both sides with their Taylor
polynomials of degree $2k+2$, which agree by \<open>suzuki_order\<close>.\<close>

text \<open>Two facts about factorials and the exponential series: $i!\,k!\le(i+k)!$, and
\[ \Bigl|e^z-\sum_{q\le P}\frac{z^q}{q!}\Bigr|\le\frac{|z|^{P+1}e^{|z|}}{(P+1)!}. \]\<close>

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

text \<open>A sum of matrices that act on $v$ by scalars acts by the sum of the scalars.\<close>

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

text \<open>The Taylor polynomial $\sum_{q\le P}(isH)^q/q!$ of $e^{isH}$.  On an eigenvector it is the Taylor
polynomial of $e^{is\lambda}$, so it is within $(|s|L)^{P+1}e^{|s|L}/(P+1)!$ of $e^{isH}$ when
$\norm{Hv}\le L\norm v$ (\<open>evolution_taylor\<close>).\<close>

definition exp_taylor :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "exp_taylor n H s P = matrix_sum n (\<lambda>q. exp_coeff ((\<i> * complex_of_real s) \<cdot>\<^sub>m H) q) (Suc P)"

lemma exp_taylor_carrier: "H \<in> carrier_mat n n \<Longrightarrow> exp_taylor n H s P \<in> carrier_mat n n"
  unfolding exp_taylor_def by (rule matrix_sum_dim) (simp add: exp_coeff_def)

lemma exp_taylor_eigen:
  assumes H: "H \<in> carrier_mat n n" and v: "dim_vec v = n" and ev: "H *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  shows "exp_taylor n H s P *\<^sub>v v = (\<Sum>q\<le>P. (\<i> * complex_of_real (s * l)) ^ q / fact q) \<cdot>\<^sub>v v"
proof -
  have "exp_coeff ((\<i> * complex_of_real s) \<cdot>\<^sub>m H) q *\<^sub>v v = ((\<i> * complex_of_real (s * l)) ^ q / fact q) \<cdot>\<^sub>v v" for q
  proof -
    let ?c = "complex_of_real (1 / fact q) * (\<i> * complex_of_real s) ^ q"
    have t: "exp_coeff ((\<i> * complex_of_real s) \<cdot>\<^sub>m H) q = ?c \<cdot>\<^sub>m H ^\<^sub>m q"
      using H by (simp add: exp_coeff_def smult_pow_mat) (rule eq_matI, auto)
    have Hq: "H ^\<^sub>m q \<in> carrier_mat n n" using H by simp
    have "exp_coeff ((\<i> * complex_of_real s) \<cdot>\<^sub>m H) q *\<^sub>v v = ?c \<cdot>\<^sub>v ((H ^\<^sub>m q) *\<^sub>v v)"
      unfolding t by (rule smult_mat_mult_mat_vec_assoc[OF Hq carrier_vecI[OF v]])
    also have "\<dots> = ?c \<cdot>\<^sub>v ((complex_of_real l ^ q) \<cdot>\<^sub>v v)" unfolding pow_eigen[OF H v ev] ..
    also have "\<dots> = ((\<i> * complex_of_real (s * l)) ^ q / fact q) \<cdot>\<^sub>v v"
      by (simp add: smult_smult_assoc power_mult_distrib field_simps)
    finally show ?thesis .
  qed
  thus ?thesis unfolding exp_taylor_def lessThan_Suc_atMost[symmetric]
    by (intro matrix_sum_eigen[OF _ v]) (use H in \<open>simp_all add: exp_coeff_def\<close>)
qed

lemma evolution_taylor:
  assumes H: "herm_bounded n L H" and L: "0 \<le> L"
  shows "evolution H s \<approx>\<^bsub>(\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P)\<^esub> exp_taylor n H s P"
proof -
  have Hc: "H \<in> carrier_mat n n" "hermitian H" using herm_boundedD[OF H] by simp_all
  let ?g = "\<lambda>x. cis (s * x) - (\<Sum>q\<le>P. (\<i> * complex_of_real (s * x)) ^ q / fact q)"
  let ?B = "evolution H s - exp_taylor n H s P"
  have mf: "mat_fun ?g H = ?B"
  proof (rule mat_fun_eqI[OF Hc])
    show "?B \<in> carrier_mat n n" by (rule minus_carrier_mat[OF exp_taylor_carrier[OF Hc(1)]])
    show "?B acts_as ?g on_eigenvectors_of H" unfolding acts_on_eigenvectors_def
    proof (intro allI impI)
      fix v l assume v: "dim_vec v = dim_row H" and ev: "H *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
      have vn: "dim_vec v = n" using v Hc(1) by simp
      have "?B *\<^sub>v v = evolution H s *\<^sub>v v - exp_taylor n H s P *\<^sub>v v"
        by (rule minus_mult_distrib_mat_vec[OF evolution_carrier[OF Hc] exp_taylor_carrier[OF Hc(1)] carrier_vecI[OF vn]])
      also have "\<dots> = ?g l \<cdot>\<^sub>v v"
        using evolution_eigen[OF Hc vn ev] exp_taylor_eigen[OF Hc(1) vn ev] by (auto intro!: eq_vecI simp: algebra_simps)
      finally show "?B *\<^sub>v v = ?g l \<cdot>\<^sub>v v" .
    qed
  qed
  have c0: "0 \<le> (\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P)" using L by simp
  show ?thesis
  proof (rule op_closeI[OF evolution_carrier[OF Hc]])
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have "evolution H s *\<^sub>v v - exp_taylor n H s P *\<^sub>v v = ?B *\<^sub>v v"
      by (rule minus_mult_distrib_mat_vec[OF evolution_carrier[OF Hc] exp_taylor_carrier[OF Hc(1)] carrier_vecI[OF v], symmetric])
    also have "\<dots> = mat_fun ?g H *\<^sub>v v" unfolding mf ..
    finally have e: "evolution H s *\<^sub>v v - exp_taylor n H s P *\<^sub>v v = mat_fun ?g H *\<^sub>v v" .
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
    thus "\<parallel>evolution H s *\<^sub>v v - exp_taylor n H s P *\<^sub>v v\<parallel> \<le> (\<bar>s\<bar> * L) ^ Suc P * exp (\<bar>s\<bar> * L) / fact (Suc P) * \<parallel>v\<parallel>"
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

text \<open>Evaluating a series up to degree $P$, $\sum_{p\le P}t^pf_p$, and truncating it at degree $P$.  Evaluation
turns Cauchy products of truncations into products of matrices:
\[ \Bigl(\sum_{p\le P}t^pf_p\Bigr)\Bigl(\sum_{q\le Q}t^qg_q\Bigr)=\sum_{p\le P+Q}t^p\,(f^{\le P}\ast g^{\le Q})_p. \]\<close>

definition poly_eval :: "nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "poly_eval n f P t = matrix_sum n (\<lambda>p. (complex_of_real t ^ p) \<cdot>\<^sub>m f p) (Suc P)"

definition truncate_seq :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "truncate_seq n P f p = (if p \<le> P then f p else 0\<^sub>m n n)"

lemma truncate_seq_carrier [simp]: "seq_carrier n f \<Longrightarrow> seq_carrier n (truncate_seq n P f)"
  by (simp add: seq_carrier_def truncate_seq_def)

lemma poly_eval_carrier: "seq_carrier n f \<Longrightarrow> poly_eval n f P t \<in> carrier_mat n n"
  unfolding poly_eval_def by (rule matrix_sum_dim) simp

lemma poly_eval_index:
  assumes "seq_carrier n f" "i < n" "j < n"
  shows "poly_eval n f P t $$ (i, j) = (\<Sum>p\<le>P. complex_of_real t ^ p * f p $$ (i, j))"
  unfolding poly_eval_def lessThan_Suc_atMost[symmetric] using assms by (subst matrix_sum_index) simp_all

lemma poly_eval_mult:
  assumes f: "seq_carrier n f" and g: "seq_carrier n g"
  shows "poly_eval n f P t * poly_eval n g Q t = poly_eval n (cauchy_prod n (truncate_seq n P f) (truncate_seq n Q g)) (P + Q) t"
proof (rule eq_matI)
  let ?t = "complex_of_real t"
  have c: "seq_carrier n (cauchy_prod n (truncate_seq n P f) (truncate_seq n Q g))" using f g by (simp add: cauchy_prod_carrier)
  fix i j assume i: "i < dim_row (poly_eval n (cauchy_prod n (truncate_seq n P f) (truncate_seq n Q g)) (P + Q) t)"
    and j: "j < dim_col (poly_eval n (cauchy_prod n (truncate_seq n P f) (truncate_seq n Q g)) (P + Q) t)"
  have ij: "i < n" "j < n" using i j carrier_matD[OF poly_eval_carrier[OF c]] by auto
  have sw: "(\<Sum>k<n. \<Sum>q\<le>P. \<Sum>r\<le>Q. T k q r) = (\<Sum>q\<le>P. \<Sum>r\<le>Q. \<Sum>k<n. T k q r)" for T :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"
    by (subst sum.swap) (rule sum.cong[OF refl], rule sum.swap)
  have "(poly_eval n f P t * poly_eval n g Q t) $$ (i, j) = (\<Sum>k<n. poly_eval n f P t $$ (i, k) * poly_eval n g Q t $$ (k, j))"
    using ij carrier_matD[OF poly_eval_carrier[OF f, where P = P and t = t]] carrier_matD[OF poly_eval_carrier[OF g, where P = Q and t = t]]
    by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<n. (\<Sum>q\<le>P. ?t ^ q * f q $$ (i, k)) * (\<Sum>r\<le>Q. ?t ^ r * g r $$ (k, j)))"
    by (intro sum.cong refl) (simp add: poly_eval_index[OF f ij(1)] poly_eval_index[OF g _ ij(2)])
  also have "\<dots> = (\<Sum>q\<le>P. \<Sum>r\<le>Q. \<Sum>k<n. ?t ^ (q + r) * (f q $$ (i, k) * g r $$ (k, j)))"
    by (simp only: sum_product sw) (simp add: power_add mult_ac)
  also have "\<dots> = (\<Sum>p\<le>P + Q. \<Sum>q\<le>p. if q \<le> P \<and> p - q \<le> Q
      then \<Sum>k<n. ?t ^ (q + (p - q)) * (f q $$ (i, k) * g (p - q) $$ (k, j)) else 0)"
    by (rule square_reindex)
  also have "\<dots> = (\<Sum>p\<le>P + Q. ?t ^ p * (\<Sum>q\<le>p. \<Sum>k<n. truncate_seq n P f q $$ (i, k) * truncate_seq n Q g (p - q) $$ (k, j)))"
    unfolding sum_distrib_left
    by (intro sum.cong refl) (use ij in \<open>auto simp: truncate_seq_def sum_distrib_left mult_ac\<close>)
  also have "\<dots> = poly_eval n (cauchy_prod n (truncate_seq n P f) (truncate_seq n Q g)) (P + Q) t $$ (i, j)"
    using poly_eval_index[OF c ij] cauchy_prod_index[OF truncate_seq_carrier[OF f] truncate_seq_carrier[OF g] ij] by simp
  finally show "(poly_eval n f P t * poly_eval n g Q t) $$ (i, j) = poly_eval n (cauchy_prod n (truncate_seq n P f) (truncate_seq n Q g)) (P + Q) t $$ (i, j)" .
qed (use carrier_matD[OF poly_eval_carrier[OF f, where P = P and t = t]] carrier_matD[OF poly_eval_carrier[OF g, where P = Q and t = t]]
      carrier_matD[OF poly_eval_carrier[OF cauchy_prod_carrier[OF truncate_seq_carrier[OF f] truncate_seq_carrier[OF g]], where P = "P + Q" and t = t]] in simp_all)

text \<open>\<open>op_bound n c M\<close>: $\norm{Mv}\le c\norm v$ for all $v$.  Bounds multiply over products, scale, add over
sums, and give $\norm{X^p/p!}\le a^p/p!$ and $\norm{(f\ast g)_p}\le\sum_{q\le p}c_q\,c'_{p-q}$.\<close>

definition op_bound :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "op_bound n c M \<longleftrightarrow> (\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>M *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>)"

lemma op_boundD: "op_bound n c M \<Longrightarrow> dim_vec v = n \<Longrightarrow> \<parallel>M *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>"
  by (simp add: op_bound_def)

lemma op_bound_zero: "op_bound n 0 (0\<^sub>m n n)"
proof -
  have "0\<^sub>m n n *\<^sub>v v = 0\<^sub>v n" if "dim_vec v = n" for v :: "complex Matrix.vec"
    using that by (intro eq_vecI) (auto simp: scalar_prod_def)
  thus ?thesis by (simp add: op_bound_def vnorm_zero_vec)
qed

lemma op_bound_mult:
  assumes A: "A \<in> carrier_mat n n" "op_bound n a A" and B: "B \<in> carrier_mat n n" "op_bound n b B" and a: "0 \<le> a"
  shows "op_bound n (a * b) (A * B)"
  unfolding op_bound_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
  have "\<parallel>(A * B) *\<^sub>v v\<parallel> = \<parallel>A *\<^sub>v (B *\<^sub>v v)\<parallel>" using assoc_mult_mat_vec[OF A(1) B(1) carrier_vecI[OF v]] by simp
  also have "\<dots> \<le> a * \<parallel>B *\<^sub>v v\<parallel>" by (rule op_boundD[OF A(2)]) (use B(1) in simp)
  also have "\<dots> \<le> a * (b * \<parallel>v\<parallel>)" by (rule mult_left_mono[OF op_boundD[OF B(2) v] a])
  finally show "\<parallel>(A * B) *\<^sub>v v\<parallel> \<le> a * b * \<parallel>v\<parallel>" by (simp add: mult_ac)
qed

lemma op_bound_smult: "A \<in> carrier_mat n n \<Longrightarrow> op_bound n a A \<Longrightarrow> op_bound n (cmod c * a) (c \<cdot>\<^sub>m A)"
  unfolding op_bound_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume A: "A \<in> carrier_mat n n" and b: "\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>A *\<^sub>v v\<parallel> \<le> a * \<parallel>v\<parallel>"
    and v: "dim_vec v = n"
  have "\<parallel>(c \<cdot>\<^sub>m A) *\<^sub>v v\<parallel> = cmod c * \<parallel>A *\<^sub>v v\<parallel>"
    using smult_mat_mult_mat_vec_assoc[OF A carrier_vecI[OF v]] by (simp add: cpx_vec_length_smult)
  also have "\<dots> \<le> cmod c * (a * \<parallel>v\<parallel>)" using b v by (simp add: mult_left_mono)
  finally show "\<parallel>(c \<cdot>\<^sub>m A) *\<^sub>v v\<parallel> \<le> cmod c * a * \<parallel>v\<parallel>" by (simp add: mult_ac)
qed

lemma op_bound_matrix_sum:
  assumes "\<And>q. q < m \<Longrightarrow> F q \<in> carrier_mat n n" "\<And>q. q < m \<Longrightarrow> op_bound n (c q) (F q)"
  shows "op_bound n (\<Sum>q<m. c q) (matrix_sum n F m)"
  using assms
proof (induction m)
  case 0
  show ?case using op_bound_zero by simp
next
  case (Suc m)
  have S: "matrix_sum n F m \<in> carrier_mat n n" by (rule matrix_sum_dim) (use Suc.prems in auto)
  have IH: "op_bound n (\<Sum>q<m. c q) (matrix_sum n F m)" by (rule Suc.IH) (use Suc.prems in auto)
  show ?case unfolding op_bound_def
  proof (intro allI impI)
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have "matrix_sum n F (Suc m) *\<^sub>v v = F m *\<^sub>v v + matrix_sum n F m *\<^sub>v v"
      using add_mult_distrib_mat_vec[OF Suc.prems(1)[of m] S carrier_vecI[OF v]] by simp
    hence "\<parallel>matrix_sum n F (Suc m) *\<^sub>v v\<parallel> \<le> \<parallel>F m *\<^sub>v v\<parallel> + \<parallel>matrix_sum n F m *\<^sub>v v\<parallel>"
      using vnorm_add_le[of "F m *\<^sub>v v" "matrix_sum n F m *\<^sub>v v"] Suc.prems(1)[of m] S by simp
    also have "\<dots> \<le> c m * \<parallel>v\<parallel> + (\<Sum>q<m. c q) * \<parallel>v\<parallel>"
      using op_boundD[OF Suc.prems(2)[of m] v] op_boundD[OF IH v] by simp
    finally show "\<parallel>matrix_sum n F (Suc m) *\<^sub>v v\<parallel> \<le> (\<Sum>q<Suc m. c q) * \<parallel>v\<parallel>" by (simp add: algebra_simps)
  qed
qed

lemma op_bound_pow:
  assumes A: "A \<in> carrier_mat n n" "op_bound n a A" and a: "0 \<le> a"
  shows "op_bound n (a ^ q) (A ^\<^sub>m q)"
proof (induction q)
  case 0
  show ?case using A(1) by (simp add: op_bound_def one_mult_mat_vec[OF carrier_vecI])
next
  case (Suc q)
  have "op_bound n (a ^ q * a) (A ^\<^sub>m q * A)" by (rule op_bound_mult[OF _ Suc A]) (use A a in simp_all)
  thus ?case by (simp add: mult.commute)
qed

lemma exp_coeff_op_bound:
  assumes Y: "Y \<in> carrier_mat n n" "op_bound n a Y" and a: "0 \<le> a"
  shows "op_bound n (a ^ q / fact q) (exp_coeff Y q)"
proof -
  have "cmod (complex_of_real (1 / fact q)) * a ^ q = a ^ q / fact q" by (simp only: norm_of_real) simp
  thus ?thesis using op_bound_smult[OF pow_carrier_mat[OF Y(1)] op_bound_pow[OF Y a], of "complex_of_real (1 / fact q)" q]
    unfolding exp_coeff_def by simp
qed

text \<open>\[ \sum_{q\le p}\frac{a^q\,b^{p-q}}{q!\,(p-q)!}=\frac{(a+b)^p}{p!}. \]\<close>

lemma binomial_exp_coef:
  fixes a b :: "'a::field_char_0"
  shows "(\<Sum>q\<le>p. a ^ q * b ^ (p - q) / (fact q * fact (p - q))) = (a + b) ^ p / fact p"
proof -
  have "(a + b) ^ p = (\<Sum>q\<le>p. of_nat (p choose q) * a ^ q * b ^ (p - q))" by (rule binomial_ring)
  also have "\<dots> = fact p * (\<Sum>q\<le>p. a ^ q * b ^ (p - q) / (fact q * fact (p - q)))"
    unfolding sum_distrib_left by (intro sum.cong refl) (simp add: binomial_fact field_simps)
  finally show ?thesis by (simp add: field_simps)
qed

lemma op_bound_mono: "op_bound n c M \<Longrightarrow> c \<le> c' \<Longrightarrow> op_bound n c' M"
  unfolding op_bound_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume b: "\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>M *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>" and cc: "c \<le> c'" and v: "dim_vec v = n"
  have "\<parallel>M *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>" using b v by simp
  also have "\<dots> \<le> c' * \<parallel>v\<parallel>" by (rule mult_right_mono[OF cc vnorm_ge0])
  finally show "\<parallel>M *\<^sub>v v\<parallel> \<le> c' * \<parallel>v\<parallel>" .
qed

lemma cauchy_prod_op_bound:
  assumes f: "seq_carrier n f" and g: "seq_carrier n g" and bf: "\<And>q. op_bound n (cf q) (f q)" and bg: "\<And>q. op_bound n (cg q) (g q)"
      and cf: "\<And>q. 0 \<le> cf q"
  shows "op_bound n (\<Sum>q\<le>p. cf q * cg (p - q)) (cauchy_prod n f g p)"
  unfolding cauchy_prod_def lessThan_Suc_atMost[symmetric]
  by (rule op_bound_matrix_sum) (use f g in \<open>simp_all add: op_bound_mult[OF seq_carrier_in[OF f] bf seq_carrier_in[OF g] bg cf]\<close>)

text \<open>The total weight $\Lambda=L\sum_{(a,H)\in F}|a|$ of a formula.  The $p$-th coefficient of the formula is
bounded by $\Lambda^p/p!$ (\<open>prod_coeff_op_bound\<close>).\<close>

definition total_weight :: "real \<Rightarrow> (real \<times> complex Matrix.mat) list \<Rightarrow> real" where
  "total_weight L F = (\<Sum>x\<leftarrow>F. \<bar>fst x\<bar>) * L"

lemma total_weight_nonneg: "0 \<le> L \<Longrightarrow> 0 \<le> total_weight L F"
  unfolding total_weight_def by (intro mult_nonneg_nonneg sum_list_nonneg) auto

lemma factor_gen_carrier: "herm_bounded n L (snd x) \<Longrightarrow> factor_gen x \<in> carrier_mat n n"
  using herm_boundedD(1) by (simp add: factor_gen_def)

lemma factor_gen_op_bound:
  assumes "herm_bounded n L (snd x)"
  shows "op_bound n (\<bar>fst x\<bar> * L) (factor_gen x)"
proof -
  have "op_bound n L (snd x)" using herm_boundedD(3)[OF assms] by (simp add: op_bound_def)
  from op_bound_smult[OF herm_boundedD(1)[OF assms] this, of "\<i> * complex_of_real (fst x)"]
  show ?thesis by (simp add: factor_gen_def norm_mult)
qed

lemma prod_coeff_op_bound:
  assumes F: "\<forall>x \<in> set F. herm_bounded n L (snd x)" and L: "0 \<le> L"
  shows "op_bound n (total_weight L F ^ p / fact p) (prod_coeff n (map factor_gen F) p)"
  using F
proof (induction F arbitrary: p)
  case Nil
  show ?case using op_bound_zero by (cases p) (simp_all add: total_weight_def seq_one_def op_bound_def one_mult_mat_vec[OF carrier_vecI])
next
  case (Cons x G)
  have Y: "factor_gen x \<in> carrier_mat n n" "op_bound n (\<bar>fst x\<bar> * L) (factor_gen x)"
    using Cons.prems factor_gen_carrier[of n L x] factor_gen_op_bound[of n L x] by auto
  have G: "\<forall>Z \<in> set (map factor_gen G). Z \<in> carrier_mat n n" using Cons.prems factor_gen_carrier by auto
  have a0: "0 \<le> \<bar>fst x\<bar> * L" using L by simp
  have "op_bound n (\<Sum>q\<le>p. (\<bar>fst x\<bar> * L) ^ q / fact q * (total_weight L G ^ (p - q) / fact (p - q))) (cauchy_prod n (exp_coeff (factor_gen x)) (prod_coeff n (map factor_gen G)) p)"
    by (rule cauchy_prod_op_bound[OF exp_coeff_carrier[OF Y(1)] prod_coeff_carrier[OF G] exp_coeff_op_bound[OF Y a0] Cons.IH]) (use Cons.prems a0 in simp_all)
  moreover have "(\<Sum>q\<le>p. (\<bar>fst x\<bar> * L) ^ q / fact q * (total_weight L G ^ (p - q) / fact (p - q))) = total_weight L (x # G) ^ p / fact p"
    using binomial_exp_coef[where a = "\<bar>fst x\<bar> * L" and b = "total_weight L G" and p = p] by (simp add: total_weight_def algebra_simps)
  ultimately show ?case by simp
qed

text \<open>The operator of a formula, $\prod_{(a,H)\in F}e^{iatH}$; it is unitary.\<close>

fun formula_product :: "nat \<Rightarrow> real \<Rightarrow> (real \<times> complex Matrix.mat) list \<Rightarrow> complex Matrix.mat" where
  "formula_product n t [] = 1\<^sub>m n"
| "formula_product n t (x # F) = evolution (snd x) (fst x * t) * formula_product n t F"

lemma formula_product_carrier_unitary:
  assumes "\<forall>x \<in> set F. herm_bounded n L (snd x)"
  shows "formula_product n t F \<in> carrier_mat n n \<and> Quantum.unitary (formula_product n t F)"
  using assms
proof (induction F)
  case Nil
  show ?case by (simp add: id_is_unitary)
next
  case (Cons x F)
  note h = herm_boundedD[of n L "snd x"]
  have hx: "snd x \<in> carrier_mat n n" "hermitian (snd x)" using Cons.prems h by auto
  have IH: "formula_product n t F \<in> carrier_mat n n" "Quantum.unitary (formula_product n t F)" using Cons by auto
  have "Quantum.unitary (evolution (snd x) (fst x * t) * formula_product n t F)"
    by (rule unitary_mult[OF evolution_unitary[OF hx] IH(2) evolution_carrier[OF hx] IH(1)])
  thus ?case using mult_carrier_mat[OF evolution_carrier[OF hx] IH(1)] by simp
qed

lemma exp_taylor_poly_eval:
  assumes H: "H \<in> carrier_mat n n"
  shows "exp_taylor n H (a * t) P = poly_eval n (exp_coeff (factor_gen (a, H))) P t"
  unfolding exp_taylor_def poly_eval_def factor_gen_def fst_conv snd_conv
proof (rule matrix_sum_cong)
  fix q assume "q < Suc P"
  have "(\<i> * complex_of_real (a * t)) \<cdot>\<^sub>m H = complex_of_real t \<cdot>\<^sub>m ((\<i> * complex_of_real a) \<cdot>\<^sub>m H)"
    by (rule eq_matI) auto
  thus "exp_coeff ((\<i> * complex_of_real (a * t)) \<cdot>\<^sub>m H) q = complex_of_real t ^ q \<cdot>\<^sub>m exp_coeff ((\<i> * complex_of_real a) \<cdot>\<^sub>m H) q"
    using exp_coeff_smult[of "(\<i> * complex_of_real a) \<cdot>\<^sub>m H" n "complex_of_real t" q] H by (simp add: seq_scale_def)
qed

lemma poly_eval_cong: "(\<And>p. p \<le> P \<Longrightarrow> f p = g p) \<Longrightarrow> poly_eval n f P t = poly_eval n g P t"
  unfolding poly_eval_def by (rule matrix_sum_cong) simp

text \<open>Splitting a polynomial at degree $P$, and the tail bound
$\sum_{p<Q}z^{K+p}/(K+p)!\le z^Ke^z/K!$ for $z\ge0$.\<close>

lemma poly_eval_split:
  assumes f: "seq_carrier n f"
  shows "poly_eval n f (P + Q) t = poly_eval n f P t + matrix_sum n (\<lambda>p. (complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m f (Suc P + p)) Q"
proof (induction Q)
  case 0
  show ?case using poly_eval_carrier[OF f, where P = P and t = t] by simp
next
  case (Suc Q)
  let ?h = "matrix_sum n (\<lambda>p. (complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m f (Suc P + p)) Q"
  have c: "(complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) \<in> carrier_mat n n" "poly_eval n f P t \<in> carrier_mat n n"
    "?h \<in> carrier_mat n n" using f poly_eval_carrier[OF f] by (auto intro!: matrix_sum_dim)
  have "poly_eval n f (P + Suc Q) t = (complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + poly_eval n f (P + Q) t"
    by (simp add: poly_eval_def)
  also have "\<dots> = (complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + (poly_eval n f P t + ?h)" unfolding Suc ..
  also have "\<dots> = ((complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + poly_eval n f P t) + ?h"
    by (rule assoc_add_mat[OF c, symmetric])
  also have "(complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + poly_eval n f P t
      = poly_eval n f P t + (complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q)"
    by (rule comm_add_mat[OF c(1,2)])
  also have "(poly_eval n f P t + (complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q)) + ?h
      = poly_eval n f P t + ((complex_of_real t ^ (Suc P + Q)) \<cdot>\<^sub>m f (Suc P + Q) + ?h)"
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

lemma poly_eval_op_bound:
  assumes f: "seq_carrier n f" and b: "\<And>p. op_bound n (c p) (f p)"
  shows "op_bound n (\<Sum>p\<le>P. \<bar>t\<bar> ^ p * c p) (poly_eval n f P t)"
  unfolding poly_eval_def lessThan_Suc_atMost[symmetric]
proof (rule op_bound_matrix_sum)
  fix p
  show "(complex_of_real t ^ p) \<cdot>\<^sub>m f p \<in> carrier_mat n n" using f by simp
  have "cmod (complex_of_real t ^ p) = \<bar>t\<bar> ^ p" by (simp add: norm_power)
  thus "op_bound n (\<bar>t\<bar> ^ p * c p) ((complex_of_real t ^ p) \<cdot>\<^sub>m f p)"
    using op_bound_smult[OF seq_carrier_in[OF f] b, of "complex_of_real t ^ p" p] by simp
qed

lemma poly_eval_seq_one: "poly_eval n (seq_one n) P t = 1\<^sub>m n"
proof -
  have "poly_eval n (seq_one n) P t = (complex_of_real t ^ 0) \<cdot>\<^sub>m seq_one n 0"
    unfolding poly_eval_def by (rule matrix_sum_single) (auto simp: seq_one_def)
  thus ?thesis by (simp add: seq_one_def one_smult_mat)
qed

text \<open>A formula is close to its own Taylor polynomial: with $|F|$ factors and weight $\Lambda$,
\[ \Bigl\|\prod_{(a,H)\in F}e^{iatH}-\sum_{p\le P}t^p\,\mathrm{coeff}_p\Bigr\|\le
   2|F|\,\frac{(\Lambda|t|)^{P+1}e^{\Lambda|t|}}{(P+1)!}. \]\<close>

theorem formula_product_approx:
  assumes F: "\<forall>x \<in> set F. herm_bounded n L (snd x)" and L: "0 \<le> L"
  shows "formula_product n t F \<approx>\<^bsub>2 * real (length F) * (total_weight L F * \<bar>t\<bar>) ^ Suc P * exp (total_weight L F * \<bar>t\<bar>) / fact (Suc P)\<^esub> poly_eval n (prod_coeff n (map factor_gen F)) P t"
  using F
proof (induction F)
  case Nil
  show ?case
  proof (rule op_closeI[where m = n and n = n])
    show "formula_product n t [] \<in> carrier_mat n n" by simp
  next
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    have "formula_product n t [] *\<^sub>v v - poly_eval n (prod_coeff n (map factor_gen [])) P t *\<^sub>v v = 0\<^sub>v n"
      using v by (intro eq_vecI) (simp_all add: poly_eval_seq_one)
    thus "\<parallel>formula_product n t [] *\<^sub>v v - poly_eval n (prod_coeff n (map factor_gen [])) P t *\<^sub>v v\<parallel>
        \<le> 2 * real (length []) * (total_weight L [] * \<bar>t\<bar>) ^ Suc P * exp (total_weight L [] * \<bar>t\<bar>) / fact (Suc P) * \<parallel>v\<parallel>"
      by (simp add: vnorm_zero_vec)
  qed
next
  case (Cons x G)
  let ?a = "fst x" and ?H = "snd x" and ?Y = "factor_gen x" and ?fG = "prod_coeff n (map factor_gen G)"
  let ?x0 = "\<bar>fst x\<bar> * L" and ?y0 = "total_weight L G" and ?P' = "Suc P"
  let ?z = "(?x0 + ?y0) * \<bar>t\<bar>"
  have hx: "herm_bounded n L ?H" and hG: "\<forall>y \<in> set G. herm_bounded n L (snd y)" using Cons.prems by auto
  have Hc: "?H \<in> carrier_mat n n" "hermitian ?H" using herm_boundedD[OF hx] by simp_all
  have G: "\<forall>Z \<in> set (map factor_gen G). Z \<in> carrier_mat n n" using hG factor_gen_carrier by auto
  have Yc: "?Y \<in> carrier_mat n n" and Yb: "op_bound n ?x0 ?Y" using factor_gen_carrier[OF hx] factor_gen_op_bound[OF hx] by simp_all
  have x0: "0 \<le> ?x0" and y0: "0 \<le> ?y0" using L total_weight_nonneg by simp_all
  have fGc: "seq_carrier n ?fG" by (rule prod_coeff_carrier[OF G])
  have tYc: "seq_carrier n (exp_coeff ?Y)" by (rule exp_coeff_carrier[OF Yc])
  define E where "E = evolution ?H (?a * t)"
  define T where "T = poly_eval n (exp_coeff ?Y) P t"
  define SG where "SG = poly_eval n ?fG P t"
  define W where "W = formula_product n t G"
  define C where "C = cauchy_prod n (truncate_seq n P (exp_coeff ?Y)) (truncate_seq n P ?fG)"
  define hi where "hi = matrix_sum n (\<lambda>p. (complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m C (Suc P + p)) P"
  have Cc: "seq_carrier n C" unfolding C_def by (simp add: cauchy_prod_carrier tYc fGc)
  have Ec: "E \<in> carrier_mat n n" unfolding E_def by (rule evolution_carrier[OF Hc])
  have Tc: "T \<in> carrier_mat n n" unfolding T_def by (rule poly_eval_carrier[OF tYc])
  have SGc: "SG \<in> carrier_mat n n" unfolding SG_def by (rule poly_eval_carrier[OF fGc])
  have Wcu: "W \<in> carrier_mat n n" "Quantum.unitary W" using formula_product_carrier_unitary[OF hG] by (simp_all add: W_def)
  have hic: "hi \<in> carrier_mat n n" unfolding hi_def by (rule matrix_sum_dim) (simp add: Cc)
  have fx: "prod_coeff n (map factor_gen (x # G)) = cauchy_prod n (exp_coeff ?Y) ?fG" by simp
  have lamx: "total_weight L (x # G) * \<bar>t\<bar> = ?z" by (simp add: total_weight_def algebra_simps)
  have TE: "T = exp_taylor n ?H (?a * t) P" unfolding T_def using exp_taylor_poly_eval[OF Hc(1), of ?a t P] by (simp add: factor_gen_def)
  have TSG: "T * SG = poly_eval n (cauchy_prod n (exp_coeff ?Y) ?fG) P t + hi"
  proof -
    have "T * SG = poly_eval n C (P + P) t" unfolding T_def SG_def C_def by (rule poly_eval_mult[OF tYc fGc])
    also have "\<dots> = poly_eval n C P t + hi" unfolding hi_def by (rule poly_eval_split[OF Cc])
    also have "poly_eval n C P t = poly_eval n (cauchy_prod n (exp_coeff ?Y) ?fG) P t"
      unfolding C_def by (rule poly_eval_cong, rule cauchy_prod_congr) (auto simp: truncate_seq_def)
    finally show ?thesis .
  qed
  \<comment> \<open>the three error terms\<close>
  have rY: "E \<approx>\<^bsub>(?x0 * \<bar>t\<bar>) ^ ?P' * exp (?x0 * \<bar>t\<bar>) / fact ?P'\<^esub> T"
  proof -
    have e: "\<bar>?a * t\<bar> * L = ?x0 * \<bar>t\<bar>" by (simp add: abs_mult mult_ac)
    show ?thesis using evolution_taylor[OF hx L, of "?a * t" P] unfolding E_def TE e .
  qed
  have cT: "op_bound n (exp (?x0 * \<bar>t\<bar>)) T"
  proof -
    have "op_bound n (\<Sum>p\<le>P. \<bar>t\<bar> ^ p * (?x0 ^ p / fact p)) T"
      unfolding T_def by (rule poly_eval_op_bound[OF tYc exp_coeff_op_bound[OF Yc Yb x0]])
    moreover have "(\<Sum>p\<le>P. \<bar>t\<bar> ^ p * (?x0 ^ p / fact p)) \<le> exp (?x0 * \<bar>t\<bar>)"
      using partial_tail[where z = "?x0 * \<bar>t\<bar>" and Q = "Suc P" and K = 0, OF mult_nonneg_nonneg[OF x0 abs_ge_zero]]
      by (simp add: lessThan_Suc_atMost power_mult_distrib mult_ac)
    ultimately show ?thesis by (rule op_bound_mono)
  qed
  have Cb: "op_bound n ((?x0 + ?y0) ^ p / fact p) (C p)" for p
  proof -
    have tb: "op_bound n (?x0 ^ q / fact q) (truncate_seq n P (exp_coeff ?Y) q)" for q
      using exp_coeff_op_bound[OF Yc Yb x0, of q] op_bound_mono[OF op_bound_zero, of "?x0 ^ q / fact q" n] x0
      by (simp add: truncate_seq_def)
    have gb: "op_bound n (?y0 ^ q / fact q) (truncate_seq n P ?fG q)" for q
      using prod_coeff_op_bound[OF hG L, of q] op_bound_mono[OF op_bound_zero, of "?y0 ^ q / fact q" n] y0
      by (simp add: truncate_seq_def)
    have "op_bound n (\<Sum>q\<le>p. ?x0 ^ q / fact q * (?y0 ^ (p - q) / fact (p - q))) (C p)"
      unfolding C_def by (rule cauchy_prod_op_bound[OF truncate_seq_carrier[OF tYc] truncate_seq_carrier[OF fGc] tb gb]) (use x0 in simp)
    moreover have "(\<Sum>q\<le>p. ?x0 ^ q / fact q * (?y0 ^ (p - q) / fact (p - q))) = (?x0 + ?y0) ^ p / fact p"
      using binomial_exp_coef[where a = ?x0 and b = ?y0 and p = p] by simp
    ultimately show ?thesis by simp
  qed
  have hb: "op_bound n (?z ^ ?P' * exp ?z / fact ?P') hi"
  proof -
    have "op_bound n (\<Sum>p<P. \<bar>t\<bar> ^ (Suc P + p) * ((?x0 + ?y0) ^ (Suc P + p) / fact (Suc P + p))) hi"
    proof (unfold hi_def, rule op_bound_matrix_sum)
      fix p
      show "(complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m C (Suc P + p) \<in> carrier_mat n n" using Cc by simp
      have "cmod (complex_of_real t ^ (Suc P + p)) = \<bar>t\<bar> ^ (Suc P + p)" by (simp only: norm_power norm_of_real)
      thus "op_bound n (\<bar>t\<bar> ^ (Suc P + p) * ((?x0 + ?y0) ^ (Suc P + p) / fact (Suc P + p)))
          ((complex_of_real t ^ (Suc P + p)) \<cdot>\<^sub>m C (Suc P + p))"
        using op_bound_smult[OF seq_carrier_in[OF Cc] Cb, of "complex_of_real t ^ (Suc P + p)" "Suc P + p"] by simp
    qed
    moreover have "(\<Sum>p<P. \<bar>t\<bar> ^ (Suc P + p) * ((?x0 + ?y0) ^ (Suc P + p) / fact (Suc P + p)))
        \<le> ?z ^ ?P' * exp ?z / fact ?P'"
      using partial_tail[where z = ?z and Q = P and K = "Suc P", OF mult_nonneg_nonneg[OF add_nonneg_nonneg[OF x0 y0] abs_ge_zero]]
      by (simp add: power_mult_distrib mult_ac)
    ultimately show ?thesis by (rule op_bound_mono)
  qed
  let ?rG = "2 * real (length G) * (?y0 * \<bar>t\<bar>) ^ ?P' * exp (?y0 * \<bar>t\<bar>) / fact ?P'"
  have IH: "W \<approx>\<^bsub>?rG\<^esub> SG" using Cons.IH[OF hG] by (simp add: W_def SG_def)
  show ?case unfolding lamx
  proof (rule op_closeI[where m = n and n = n])
    show "formula_product n t (x # G) \<in> carrier_mat n n"
      using formula_product_carrier_unitary[OF Cons.prems] by simp
  next
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
    define w where "w = W *\<^sub>v v"
    have wn: "dim_vec w = n" and nw: "\<parallel>w\<parallel> = \<parallel>v\<parallel>" using Wcu v unitary_vnorm[OF Wcu v] by (simp_all add: w_def)
    have sp: "formula_product n t (x # G) *\<^sub>v v = E *\<^sub>v w"
      unfolding w_def E_def W_def using assoc_mult_mat_vec[OF evolution_carrier[OF Hc] _ carrier_vecI[OF v]] Wcu(1)
      by (simp add: W_def)
    have pf: "poly_eval n (prod_coeff n (map factor_gen (x # G))) P t *\<^sub>v v = poly_eval n (cauchy_prod n (exp_coeff ?Y) ?fG) P t *\<^sub>v v" by simp
    let ?pf = "poly_eval n (cauchy_prod n (exp_coeff ?Y) ?fG) P t"
    have pfc: "?pf \<in> carrier_mat n n" by (rule poly_eval_carrier) (simp add: cauchy_prod_carrier tYc fGc)
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
      using op_closeD[OF rY Ec wn] nw by simp
    have b2: "\<parallel>T *\<^sub>v (w - SG *\<^sub>v v)\<parallel> \<le> exp (?x0 * \<bar>t\<bar>) * (?rG * \<parallel>v\<parallel>)"
    proof -
      have "\<parallel>T *\<^sub>v (w - SG *\<^sub>v v)\<parallel> \<le> exp (?x0 * \<bar>t\<bar>) * \<parallel>w - SG *\<^sub>v v\<parallel>"
        by (rule op_boundD[OF cT]) (use wn SGc in simp)
      also have "\<parallel>w - SG *\<^sub>v v\<parallel> \<le> ?rG * \<parallel>v\<parallel>" using op_closeD[OF IH Wcu(1) v] by (simp add: w_def)
      finally show ?thesis by simp
    qed
    have b3: "\<parallel>hi *\<^sub>v v\<parallel> \<le> ?z ^ ?P' * exp ?z / fact ?P' * \<parallel>v\<parallel>" by (rule op_boundD[OF hb v])
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
    with tri show "\<parallel>formula_product n t (x # G) *\<^sub>v v - poly_eval n (prod_coeff n (map factor_gen (x # G))) P t *\<^sub>v v\<parallel>
        \<le> 2 * real (length (x # G)) * ?z ^ ?P' * exp ?z / fact ?P' * \<parallel>v\<parallel>"
      unfolding sp pf by linarith
  qed
qed


text \<open>Closeness is transitive, the errors adding up, and monotone in the error.\<close>

lemma op_close_trans:
  assumes "U \<approx>\<^bsub>a\<^esub> V" "V \<approx>\<^bsub>b\<^esub> W" "U \<in> carrier_mat n n" "V \<in> carrier_mat n n" "W \<in> carrier_mat n n"
  shows "U \<approx>\<^bsub>a + b\<^esub> W"
proof (rule op_closeI[OF assms(3)])
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
  have "\<parallel>U *\<^sub>v v - W *\<^sub>v v\<parallel> \<le> \<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel> + \<parallel>V *\<^sub>v v - W *\<^sub>v v\<parallel>"
    by (rule vnorm_diff_le[where n = n]) (use assms in simp_all)
  also have "\<dots> \<le> a * \<parallel>v\<parallel> + b * \<parallel>v\<parallel>" using op_closeD[OF assms(1,3) v] op_closeD[OF assms(2,4) v] by simp
  finally show "\<parallel>U *\<^sub>v v - W *\<^sub>v v\<parallel> \<le> (a + b) * \<parallel>v\<parallel>" by (simp add: algebra_simps)
qed

lemma op_close_mono:
  assumes "U \<approx>\<^bsub>a\<^esub> V" "a \<le> b"
  shows "U \<approx>\<^bsub>b\<^esub> V"
  unfolding op_close_def
proof (intro allI impI)
  fix v :: "complex Matrix.vec" assume "dim_vec v = dim_col U"
  thus "\<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel> \<le> b * \<parallel>v\<parallel>"
    using assms(1)[unfolded op_close_def] mult_right_mono[OF assms(2) vnorm_ge0[of v]] order_trans by blast
qed

text \<open>For Suzuki's formula: the sum of $m$ Hamiltonians bounded by $L$ is bounded by $mL$, the formula has
$2\cdot5^km$ factors, its weights add up to $m$, and $\Lambda\ge mL$.\<close>

lemma hamiltonian_sum_herm_bounded:
  "\<forall>H \<in> set Hs. herm_bounded n L H \<Longrightarrow> herm_bounded n (real (length Hs) * L) (hamiltonian_sum n Hs)"
  unfolding herm_bounded_def[of n "real (length Hs) * L"]
  using hamiltonian_sum_carrier[of Hs n] hamiltonian_sum_hermitian[of Hs n L] hamiltonian_sum_bound[of Hs n L] herm_boundedD(1) by blast

lemma length_suzuki: "length (suzuki k Hs) = 2 * 5 ^ k * length Hs"
  by (induction k) (simp_all add: strang_def suzuki_weights_def Let_def length_concat comp_def)

lemma sum_suzuki: "(\<Sum>x\<leftarrow>suzuki k Hs. fst x) = real (length Hs)"
proof (induction k)
  case 0
  show ?case by (simp add: strang_def comp_def sum_list_triv rev_map)
next
  case (Suc k)
  thus ?case by (simp add: suzuki_weights_def Let_def comp_def sum_list_const_mult) (simp add: algebra_simps)
qed

lemma total_weight_suzuki: "0 \<le> L \<Longrightarrow> real (length Hs) * L \<le> total_weight L (suzuki k Hs)"
  unfolding total_weight_def sum_suzuki[of k Hs, symmetric]
  by (intro mult_right_mono sum_list_mono) simp_all

text \<open>One Suzuki step: $\norm{S_{2k+2}(\delta)-e^{i\delta H}}\le(2|F|+1)(\Lambda|\delta|)^{2k+3}e^{\Lambda|\delta|}/(2k+3)!$.\<close>

lemma suzuki_step:
  fixes k :: nat and d :: real
  assumes Hs: "\<forall>H \<in> set Hs. herm_bounded n L H" and L: "0 \<le> L"
  defines "F \<equiv> suzuki k Hs" and "q \<equiv> 2 * k + 3"
  shows "formula_product n d F \<approx>\<^bsub>(2 * real (length F) + 1) * (total_weight L F * \<bar>d\<bar>) ^ q * exp (total_weight L F * \<bar>d\<bar>) / fact q\<^esub> evolution (hamiltonian_sum n Hs) d"
proof -
  have F: "\<forall>x \<in> set F. herm_bounded n L (snd x)" using Hs suzuki_snd unfolding F_def by blast
  have C: "\<forall>H \<in> set Hs. H \<in> carrier_mat n n" using Hs herm_boundedD(1) by blast
  have Hb: "herm_bounded n (real (length Hs) * L) (hamiltonian_sum n Hs)" by (rule hamiltonian_sum_herm_bounded[OF Hs])
  note Hh = herm_boundedD[OF Hb]
  have mL: "0 \<le> real (length Hs) * L" using L by simp
  let ?X = "\<i> \<cdot>\<^sub>m hamiltonian_sum n Hs" and ?f = "prod_coeff n (map factor_gen F)"
  have q: "q = Suc (2 * k + 2)" by (simp add: q_def)
  have pe: "poly_eval n ?f (2 * k + 2) d = exp_taylor n (hamiltonian_sum n Hs) d (2 * k + 2)"
  proof -
    have "poly_eval n ?f (2 * k + 2) d = poly_eval n (exp_coeff (factor_gen (1, hamiltonian_sum n Hs))) (2 * k + 2) d"
      by (rule poly_eval_cong) (use suzuki_order[OF C, of k] in \<open>simp add: F_def factor_gen_def\<close>)
    also have "\<dots> = exp_taylor n (hamiltonian_sum n Hs) d (2 * k + 2)" using exp_taylor_poly_eval[OF Hh(1), of 1 d] by simp
    finally show ?thesis .
  qed
  have a: "formula_product n d F \<approx>\<^bsub>2 * real (length F) * (total_weight L F * \<bar>d\<bar>) ^ q * exp (total_weight L F * \<bar>d\<bar>) / fact q\<^esub> exp_taylor n (hamiltonian_sum n Hs) d (2 * k + 2)"
    using formula_product_approx[OF F L, of d "2 * k + 2"] unfolding pe q .
  have b0: "exp_taylor n (hamiltonian_sum n Hs) d (2 * k + 2) \<approx>\<^bsub>(\<bar>d\<bar> * (real (length Hs) * L)) ^ q * exp (\<bar>d\<bar> * (real (length Hs) * L)) / fact q\<^esub> evolution (hamiltonian_sum n Hs) d"
    unfolding q by (rule op_close_sym[OF evolution_taylor[OF Hb mL] evolution_carrier[OF Hh(1,2)] exp_taylor_carrier[OF Hh(1)]])
  have le: "\<bar>d\<bar> * (real (length Hs) * L) \<le> total_weight L F * \<bar>d\<bar>"
    using mult_left_mono[OF total_weight_suzuki[OF L, of Hs k] abs_ge_zero[of d]] unfolding F_def by (simp add: mult_ac)
  have b: "exp_taylor n (hamiltonian_sum n Hs) d (2 * k + 2) \<approx>\<^bsub>(total_weight L F * \<bar>d\<bar>) ^ q * exp (total_weight L F * \<bar>d\<bar>) / fact q\<^esub> evolution (hamiltonian_sum n Hs) d"
  proof (rule op_close_mono[OF b0])
    have x0: "0 \<le> \<bar>d\<bar> * (real (length Hs) * L)" using mL by simp
    have "(\<bar>d\<bar> * (real (length Hs) * L)) ^ q * exp (\<bar>d\<bar> * (real (length Hs) * L))
        \<le> (total_weight L F * \<bar>d\<bar>) ^ q * exp (total_weight L F * \<bar>d\<bar>)"
      by (rule mult_mono[OF power_mono[OF le x0]]) (use le order_trans[OF x0 le] in simp_all)
    thus "(\<bar>d\<bar> * (real (length Hs) * L)) ^ q * exp (\<bar>d\<bar> * (real (length Hs) * L)) / fact q
        \<le> (total_weight L F * \<bar>d\<bar>) ^ q * exp (total_weight L F * \<bar>d\<bar>) / fact q"
      by (rule divide_right_mono) simp
  qed
  show ?thesis
    using op_close_trans[OF a b conjunct1[OF formula_product_carrier_unitary[OF F]] exp_taylor_carrier[OF Hh(1)] evolution_carrier[OF Hh(1,2)]]
    by (simp add: algebra_simps add_divide_distrib)
qed

text \<open>Suzuki's formula of order $2k+2$ over $r$ steps:
$\norm{S_{2k+2}(t/r)^r-e^{itH}}\le r(2|F|+1)(\Lambda|t|/r)^{2k+3}e^{\Lambda|t|/r}/(2k+3)!$,
with $|F|=2\cdot5^k m$ factors and $\Lambda\ge mL$.\<close>

theorem suzuki_error:
  fixes k :: nat and t :: real
  assumes Hs: "\<forall>H \<in> set Hs. herm_bounded n L H" and L: "0 \<le> L" and r: "0 < r"
  defines "F \<equiv> suzuki k Hs" and "q \<equiv> 2 * k + 3"
  shows "formula_product n (t / real r) F ^\<^sub>m r \<approx>\<^bsub>real r * ((2 * real (length F) + 1) * (total_weight L F * \<bar>t\<bar> / real r) ^ q
             * exp (total_weight L F * \<bar>t\<bar> / real r) / fact q)\<^esub> evolution (hamiltonian_sum n Hs) t"
proof -
  have Fh: "\<forall>x \<in> set F. herm_bounded n L (snd x)" using Hs suzuki_snd unfolding F_def by blast
  note Hh = herm_boundedD[OF hamiltonian_sum_herm_bounded[OF Hs]]
  note U = formula_product_carrier_unitary[OF Fh, of "t / real r"]
  have d: "total_weight L F * \<bar>t / real r\<bar> = total_weight L F * \<bar>t\<bar> / real r" using r by simp
  have c: "formula_product n (t / real r) F ^\<^sub>m r \<approx>\<^bsub>real r * ((2 * real (length F) + 1) * (total_weight L F * \<bar>t / real r\<bar>) ^ q
      * exp (total_weight L F * \<bar>t / real r\<bar>) / fact q)\<^esub> evolution (hamiltonian_sum n Hs) (t / real r) ^\<^sub>m r"
    by (rule op_close_pow[OF conjunct1[OF U] conjunct2[OF U] evolution_carrier[OF Hh(1,2)]
          evolution_unitary[OF Hh(1,2)]]) (use suzuki_step[OF Hs L, where k = k and d = "t / real r"] in \<open>simp add: F_def q_def\<close>)
  have p: "evolution (hamiltonian_sum n Hs) (t / real r) ^\<^sub>m r = evolution (hamiltonian_sum n Hs) t"
    using evolution_pow[OF Hh(1,2), of "t / real r" r] r by simp
  show ?thesis using c unfolding p d .
qed

end
