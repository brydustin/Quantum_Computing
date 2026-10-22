theory HHL_Discussion
  imports HHL_Rectangular
begin


section \<open>The paper's Discussion\<close>

text \<open>Section~IV and App.~A5 of the paper.  Flagging the ill-conditioned part is Theorem~1(2)
(\<open>flag_post_bound\<close>); the paper's displayed state swaps the conditions: $\lambda_j^{-1}$ belongs
to $\lambda_j\ge1/\kappa$ (\<open>well\<close>), and $\lambda_j<1/\kappa$ is flagged \<open>ill\<close>.\<close>

subsection \<open>Expectation values and sampling\<close>

lemma vnorm_cs:
  assumes "dim_vec u = dim_vec v"
  shows "cmod \<langle>u|v\<rangle> \<le> \<parallel>u\<parallel> * \<parallel>v\<parallel>"
proof -
  have "(cmod \<langle>u|v\<rangle>)\<^sup>2 \<le> Re (\<langle>u|u\<rangle> * \<langle>v|v\<rangle>)" by (rule No_Cloning.cauchy_schwarz_ineq[OF assms])
  also have "\<dots> = (\<parallel>u\<parallel> * \<parallel>v\<parallel>)\<^sup>2" unfolding cpx_vec_length_inner_prod[symmetric] power_mult_distrib by (simp flip: of_real_mult)
  finally show ?thesis by (rule power2_le_imp_le) (simp add: vnorm_ge0)
qed

text \<open>Measuring $M$ on $\ket{\tilde x}$ instead of $\ket x$ shifts the expectation by at most
$2\norm M\norm{\tilde x-x}$.\<close>

lemma expect_stable:
  assumes x: "dim_vec x = n" "\<parallel>x\<parallel> = 1" and y: "dim_vec y = n" "\<parallel>y\<parallel> = 1"
      and Mc: "M \<in> carrier_mat n n" and Mb: "\<And>v. dim_vec v = n \<Longrightarrow> \<parallel>M *\<^sub>v v\<parallel> \<le> m * \<parallel>v\<parallel>"
  shows "cmod (\<langle>y|M *\<^sub>v y\<rangle> - \<langle>x|M *\<^sub>v x\<rangle>) \<le> 2 * m * \<parallel>y - x\<parallel>"
proof -
  let ?d = "y - x"
  have dd: "dim_vec ?d = n" using x by simp
  have yd: "y = x + ?d" using x y by (intro eq_vecI) simp_all
  have Mxd: "M *\<^sub>v (x + ?d) = M *\<^sub>v x + M *\<^sub>v ?d"
    by (rule mult_add_distrib_mat_vec[OF Mc carrier_vecI carrier_vecI]) (use x dd in simp_all)
  have dM: "dim_vec (M *\<^sub>v v) = n" for v using Mc by simp
  have "\<langle>y|M *\<^sub>v y\<rangle> = \<langle>x + ?d|M *\<^sub>v x + M *\<^sub>v ?d\<rangle>" using yd Mxd by metis
  also have "\<dots> = \<langle>x|M *\<^sub>v x\<rangle> + \<langle>x|M *\<^sub>v ?d\<rangle> + \<langle>?d|M *\<^sub>v x\<rangle> + \<langle>?d|M *\<^sub>v ?d\<rangle>"
    by (rule No_Cloning.inner_prod_expand) (use Mc in \<open>simp_all add: x dd\<close>)
  finally have e: "\<langle>y|M *\<^sub>v y\<rangle> - \<langle>x|M *\<^sub>v x\<rangle> = \<langle>x|M *\<^sub>v ?d\<rangle> + \<langle>?d|M *\<^sub>v y\<rangle>"
    using inner_prod_add_right[OF dd dM dM, of x ?d] yd Mxd by (simp add: algebra_simps)
  have "cmod (\<langle>x|M *\<^sub>v ?d\<rangle> + \<langle>?d|M *\<^sub>v y\<rangle>) \<le> cmod \<langle>x|M *\<^sub>v ?d\<rangle> + cmod \<langle>?d|M *\<^sub>v y\<rangle>" by (rule norm_triangle_ineq)
  also have "cmod \<langle>x|M *\<^sub>v ?d\<rangle> \<le> \<parallel>x\<parallel> * \<parallel>M *\<^sub>v ?d\<parallel>" by (rule vnorm_cs) (use Mc x in simp)
  also have "\<dots> \<le> m * \<parallel>?d\<parallel>" using Mb[OF dd] x(2) by simp
  also have "cmod \<langle>?d|M *\<^sub>v y\<rangle> \<le> \<parallel>?d\<parallel> * \<parallel>M *\<^sub>v y\<parallel>" by (rule vnorm_cs) (use Mc dd in simp)
  also have "\<dots> \<le> \<parallel>?d\<parallel> * m" using Mb[OF y(1)] y(2) by (simp add: mult_left_mono vnorm_ge0)
  finally show ?thesis unfolding e by simp
qed

text \<open>Sampling $i$ with probability $|x_i|^2$ (the quantum Monte-Carlo output): the two distributions
are within $2\norm{\tilde x-x}$ in $\ell^1$.\<close>

lemma sample_dist_close:
  assumes x: "dim_vec x = n" "\<parallel>x\<parallel> = 1" and y: "dim_vec y = n" "\<parallel>y\<parallel> = 1"
  shows "(\<Sum>i<n. \<bar>(cmod (y $ i))\<^sup>2 - (cmod (x $ i))\<^sup>2\<bar>) \<le> 2 * \<parallel>y - x\<parallel>"
proof -
  let ?c = "\<lambda>i. cmod ((y - x) $ i)" and ?s = "\<lambda>i. cmod (y $ i) + cmod (x $ i)"
  have pt: "\<bar>(cmod (y $ i))\<^sup>2 - (cmod (x $ i))\<^sup>2\<bar> \<le> \<bar>?c i\<bar> * \<bar>?s i\<bar>" if i: "i < n" for i
  proof -
    have "(cmod (y $ i))\<^sup>2 - (cmod (x $ i))\<^sup>2 = (cmod (y $ i) - cmod (x $ i)) * ?s i"
      by (simp add: power2_eq_square algebra_simps)
    hence "\<bar>(cmod (y $ i))\<^sup>2 - (cmod (x $ i))\<^sup>2\<bar> = \<bar>cmod (y $ i) - cmod (x $ i)\<bar> * \<bar>?s i\<bar>" by (simp add: abs_mult)
    also have "\<bar>cmod (y $ i) - cmod (x $ i)\<bar> \<le> ?c i" using i x y by (simp add: norm_triangle_ineq3)
    finally show ?thesis by (simp add: mult_right_mono)
  qed
  have "(\<Sum>i<n. \<bar>(cmod (y $ i))\<^sup>2 - (cmod (x $ i))\<^sup>2\<bar>) \<le> (\<Sum>i<n. \<bar>?c i\<bar> * \<bar>?s i\<bar>)" by (rule sum_mono) (use pt in simp)
  also have "\<dots> \<le> L2_set ?c {..<n} * L2_set ?s {..<n}" by (rule L2_set_mult_ineq)
  finally have S: "(\<Sum>i<n. \<bar>(cmod (y $ i))\<^sup>2 - (cmod (x $ i))\<^sup>2\<bar>) \<le> L2_set ?c {..<n} * L2_set ?s {..<n}" .
  have Lc: "L2_set ?c {..<n} = \<parallel>y - x\<parallel>" using vnorm_L2[of "y - x"] x by simp
  have "L2_set ?s {..<n} \<le> L2_set (\<lambda>i. cmod (y $ i)) {..<n} + L2_set (\<lambda>i. cmod (x $ i)) {..<n}"
    by (rule L2_set_triangle_ineq)
  also have "\<dots> = 2" using vnorm_L2[of y] vnorm_L2[of x] x y by simp
  finally have "\<parallel>y - x\<parallel> * L2_set ?s {..<n} \<le> \<parallel>y - x\<parallel> * 2" by (rule mult_left_mono) (rule vnorm_ge0)
  thus ?thesis using S unfolding Lc by simp
qed

subsection \<open>$k$ copies\<close>

text \<open>Degree-$2k$ polynomials in the entries of $x$ are expectations on $\ket x^{\otimes k}$, whose
entries are $k$-fold products of entries of $x$; $k$ copies of an approximation are within
$k\norm{\tilde x-x}$.\<close>

primrec tpow :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "tpow x 0 = Matrix.vec 1 (\<lambda>_. 1)"
| "tpow x (Suc k) = tensor_vec x (tpow x k)"

lemma dim_tpow: "dim_vec x = n \<Longrightarrow> dim_vec (tpow x k) = n ^ k"
  by (induction k) (simp_all add: tensor_vec_dim)

lemma mod_div_digit: "0 < (p::nat) \<Longrightarrow> i mod (p * q) div p = i div p mod q"
  by (simp add: mod_mult2_eq)

lemma tpow_index:
  assumes x: "dim_vec x = n" and i: "i < n ^ k"
  shows "tpow x k $ i = (\<Prod>l<k. x $ (i div n ^ (k - 1 - l) mod n))"
  using i
proof (induction k arbitrary: i)
  case 0 thus ?case by simp
next
  case (Suc k)
  have nk: "0 < n ^ k" using Suc.prems by (cases "n ^ k = 0") auto
  have d: "i div n ^ k < n" using Suc.prems by (simp add: less_mult_imp_div_less mult.commute)
  have m: "i mod n ^ k < n ^ k" using nk by simp
  have "tpow x (Suc k) $ i = x $ (i div n ^ k) * tpow x k $ (i mod n ^ k)"
    using Suc.prems x by (simp add: tensor_vec_index dim_tpow mult.commute)
  also have "tpow x k $ (i mod n ^ k) = (\<Prod>l<k. x $ (i mod n ^ k div n ^ (k - 1 - l) mod n))" by (rule Suc.IH[OF m])
  also have "\<dots> = (\<Prod>l<k. x $ (i div n ^ (k - 1 - l) mod n))"
  proof (rule prod.cong[OF refl])
    fix l assume "l \<in> {..<k}"
    hence l: "k - 1 - l < k" by simp
    have "i mod n ^ k div n ^ (k - 1 - l) mod n = i div n ^ (k - 1 - l) mod n"
    proof -
      obtain r where r: "k = (k - 1 - l) + Suc r" using l by (metis add_Suc_right le_add_diff_inverse less_imp_Suc_add)
      let ?p = "n ^ (k - 1 - l)" and ?q = "n * n ^ r"
      have nk': "n ^ k = ?p * ?q" using r by (metis power_Suc power_add)
      have p0: "0 < ?p" using nk nk' by (cases "?p = 0") auto
      have A: "i mod n ^ k div ?p = i div ?p mod ?q" unfolding nk' by (rule mod_div_digit[OF p0])
      have B: "i div ?p mod ?q mod n = i div ?p mod n" by (rule mod_mod_cancel) (rule dvd_triv_left)
      show ?thesis by (simp only: A B)
    qed
    thus "x $ (i mod n ^ k div n ^ (k - 1 - l) mod n) = x $ (i div n ^ (k - 1 - l) mod n)" by simp
  qed
  also have "x $ (i div n ^ k) * (\<Prod>l<k. x $ (i div n ^ (k - 1 - l) mod n)) = (\<Prod>l<Suc k. x $ (i div n ^ (Suc k - 1 - l) mod n))"
    by (simp only: prod.lessThan_Suc_shift) (simp add: d)
  finally show ?case .
qed

lemma vnorm_tpow: "dim_vec x = n \<Longrightarrow> \<parallel>tpow x k\<parallel> = \<parallel>x\<parallel> ^ k"
proof (induction k)
  case 0
  have "\<parallel>Matrix.vec 1 (\<lambda>_. 1 :: complex)\<parallel>\<^sup>2 = 1\<^sup>2" by (simp add: vnorm_sq)
  thus ?case using power2_eq_iff_nonneg[OF vnorm_ge0 zero_le_one] by simp
next
  case (Suc k) thus ?case using vnorm_tensor[OF Suc.prems dim_tpow[OF Suc.prems]] by simp
qed

lemma tpow_close:
  assumes x: "dim_vec x = n" "\<parallel>x\<parallel> = 1" and y: "dim_vec y = n" "\<parallel>y\<parallel> = 1"
  shows "\<parallel>tpow y k - tpow x k\<parallel> \<le> real k * \<parallel>y - x\<parallel>"
proof (induction k)
  case 0 thus ?case by (simp add: cpx_vec_length_def)
next
  case (Suc k)
  let ?X = "tpow x k" and ?Y = "tpow y k"
  have dX: "dim_vec ?X = n ^ k" and dY: "dim_vec ?Y = n ^ k" using dim_tpow x y by blast+
  have e: "tensor_vec y ?Y - tensor_vec x ?X = tensor_vec (y - x) ?Y + tensor_vec x (?Y - ?X)"
  proof -
    have "tensor_vec y ?Y = tensor_vec x ?Y + tensor_vec (y - x) ?Y"
    proof -
      have "y = x + (y - x)" using x y by (intro eq_vecI) simp_all
      hence "tensor_vec y ?Y = tensor_vec (x + (y - x)) ?Y" by simp
      also have "\<dots> = tensor_vec x ?Y + tensor_vec (y - x) ?Y" by (rule tensor_vec_bilinear_left) (simp_all add: x y dY)
      finally show ?thesis .
    qed
    moreover have "tensor_vec x ?Y = tensor_vec x ?X + tensor_vec x (?Y - ?X)"
    proof -
      have "?Y = ?X + (?Y - ?X)" using dX dY by (intro eq_vecI) simp_all
      hence "tensor_vec x ?Y = tensor_vec x (?X + (?Y - ?X))" by simp
      also have "\<dots> = tensor_vec x ?X + tensor_vec x (?Y - ?X)" by (rule tensor_vec_bilinear_right) (simp_all add: x dX dY)
      finally show ?thesis .
    qed
    moreover have "dim_vec (tensor_vec x ?X) = n * n ^ k" "dim_vec (tensor_vec x (?Y - ?X)) = n * n ^ k"
        "dim_vec (tensor_vec (y - x) ?Y) = n * n ^ k" using x dX dY by (simp_all add: tensor_vec_dim)
    ultimately show ?thesis by (intro eq_vecI) simp_all
  qed
  have "\<parallel>tpow y (Suc k) - tpow x (Suc k)\<parallel> \<le> \<parallel>tensor_vec (y - x) ?Y\<parallel> + \<parallel>tensor_vec x (?Y - ?X)\<parallel>"
    unfolding tpow.simps e by (rule vnorm_add_le) (simp add: x dX dY tensor_vec_dim)
  also have "\<parallel>tensor_vec (y - x) ?Y\<parallel> = \<parallel>y - x\<parallel>"
    using vnorm_tensor[of "y - x" n ?Y "n ^ k"] vnorm_tpow[OF y(1), of k] x y dY by simp
  also have "\<parallel>tensor_vec x (?Y - ?X)\<parallel> = \<parallel>?Y - ?X\<parallel>"
    using vnorm_tensor[OF x(1), of "?Y - ?X" "n ^ k"] x dX by simp
  finally show ?case using Suc.IH by (simp add: algebra_simps)
qed


subsection \<open>The SWAP test\<close>

text \<open>A vector $a\oplus c$ of length $2K$ is $\ket0 a+\ket1 c$.  Hadamard on the control, controlled
SWAP, Hadamard: the control reads $\ket0$ with probability $(1+|\langle\psi|\varphi\rangle|^2)/2$.\<close>

definition swap_mat :: "nat \<Rightarrow> complex Matrix.mat" where
  "swap_mat n = Matrix.mat (n * n) (n * n) (\<lambda>(i, j). if j = i mod n * n + i div n then 1 else 0)"

definition cswap :: "nat \<Rightarrow> complex Matrix.mat" where
  "cswap n = four_block_mat (1\<^sub>m (n * n)) (0\<^sub>m (n * n) (n * n)) (0\<^sub>m (n * n) (n * n)) (swap_mat n)"

definition swap_test :: "nat \<Rightarrow> complex Matrix.mat" where
  "swap_test n = (Hadamard \<Otimes> 1\<^sub>m (n * n)) * (cswap n * (Hadamard \<Otimes> 1\<^sub>m (n * n)))"

lemma swap_mat_carrier [simp]: "swap_mat n \<in> carrier_mat (n * n) (n * n)"
  by (simp add: swap_mat_def)

lemma had_tensor_carrier [simp]: "Hadamard \<Otimes> 1\<^sub>m K \<in> carrier_mat (K + K) (K + K)"
  by (rule carrier_matI) (simp_all add: Hadamard_def H_def)

lemma cswap_carrier [simp]: "cswap n \<in> carrier_mat (n * n + n * n) (n * n + n * n)"
  by (simp add: cswap_def)

lemma swap_index_lt:
  fixes i n :: nat
  assumes i: "i < n * n"
  shows "i mod n * n + i div n < n * n"
proof -
  have n0: "0 < n" using i by (cases n) auto
  have d: "i div n < n" using i by (simp add: less_mult_imp_div_less)
  have m: "i mod n + 1 \<le> n" using n0 by (simp add: Suc_le_eq)
  have "i mod n * n + i div n < i mod n * n + n" using d by simp
  also have "\<dots> = (i mod n + 1) * n" by simp
  also have "\<dots> \<le> n * n" using m by (rule mult_right_mono) simp
  finally show ?thesis .
qed

lemma swap_mat_tensor:
  assumes u: "dim_vec u = n" and v: "dim_vec v = n"
  shows "swap_mat n *\<^sub>v tensor_vec u v = tensor_vec v u"
proof (rule eq_vecI)
  have dt: "dim_vec (tensor_vec u v) = n * n" by (rule tensor_vec_dim[OF u v])
  fix i assume "i < dim_vec (tensor_vec v u)"
  hence i: "i < n * n" using tensor_vec_dim[OF v u] by simp
  let ?j = "i mod n * n + i div n"
  have j: "?j < n * n" by (rule swap_index_lt[OF i])
  have n0: "0 < n" using i by (cases n) auto
  have d: "i div n < n" using i by (simp add: less_mult_imp_div_less)
  have "(swap_mat n *\<^sub>v tensor_vec u v) $ i = (\<Sum>k<n * n. (if k = ?j then 1 else 0) * tensor_vec u v $ k)"
    using i dt by (simp add: swap_mat_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<n * n. if k = ?j then tensor_vec u v $ k else 0)" by (rule sum.cong) simp_all
  also have "\<dots> = tensor_vec u v $ ?j" using j by simp
  also have "\<dots> = u $ (?j div n) * v $ (?j mod n)" by (rule tensor_vec_index[OF u v j])
  also have "?j div n = i mod n" using n0 d by simp
  also have "?j mod n = i div n" using d by simp
  also have "u $ (i mod n) * v $ (i div n) = tensor_vec v u $ i" using tensor_vec_index[OF v u i] by simp
  finally show "(swap_mat n *\<^sub>v tensor_vec u v) $ i = tensor_vec v u $ i" .
qed (use u v in \<open>simp add: tensor_vec_dim swap_mat_def\<close>)

lemma div_mod_upper: "(K::nat) \<le> i \<Longrightarrow> i < K + K \<Longrightarrow> i div K = 1 \<and> i mod K = i - K"
  by (simp add: le_div_geq le_mod_geq)

text \<open>$H\otimes I_K$ in block form.\<close>

lemma had_tensor_block:
  assumes K: "0 < K"
  shows "Hadamard \<Otimes> 1\<^sub>m K = four_block_mat (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K)
    (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (- 1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K)"
proof (rule eq_matI)
  have HD: "dim_row Hadamard = 2" "dim_col Hadamard = 2" by (simp_all add: Hadamard_def H_def)
  fix i j assume "i < dim_row (four_block_mat (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (- 1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K))" "j < dim_col (four_block_mat (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (- 1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K))"
  hence i: "i < K + K" and j: "j < K + K" by simp_all
  have [simp]: "\<not> i < K \<Longrightarrow> i - K < K" "\<not> j < K \<Longrightarrow> j - K < K" using i j by simp_all
  have t: "(Hadamard \<Otimes> 1\<^sub>m K) $$ (i, j) = Hadamard $$ (i div K, j div K) * 1\<^sub>m K $$ (i mod K, j mod K)"
    by (rule index_tensor_mat[OF HD]) (use i j K in simp_all)
  have b: "(four_block_mat (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (- 1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K)) $$ (i, j) =
     (if i < K then if j < K then (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) $$ (i, j) else (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) $$ (i, j - K)
      else if j < K then (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) $$ (i - K, j) else (complex_of_real (- 1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) $$ (i - K, j - K))"
    using i j by (subst index_mat_four_block) simp_all
  show "(Hadamard \<Otimes> 1\<^sub>m K) $$ (i, j) = (four_block_mat (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K) (complex_of_real (- 1 / sqrt 2) \<cdot>\<^sub>m 1\<^sub>m K)) $$ (i, j)"
  proof (cases "i < K"; cases "j < K")
    assume "i < K" "j < K" thus ?thesis unfolding t b by (simp add: Hadamard_def H_def)
  next
    assume ik: "i < K" and jk: "\<not> j < K"
    have jd: "j div K = 1" "j mod K = j - K" using div_mod_upper[of K j] jk j by simp_all
    show ?thesis unfolding t b jd using ik jk j by (simp add: Hadamard_def H_def)
  next
    assume ik: "\<not> i < K" and jk: "j < K"
    have id: "i div K = 1" "i mod K = i - K" using div_mod_upper[of K i] ik i by simp_all
    show ?thesis unfolding t b id using ik jk i by (simp add: Hadamard_def H_def)
  next
    assume ik: "\<not> i < K" and jk: "\<not> j < K"
    have id: "i div K = 1" "i mod K = i - K" using div_mod_upper[of K i] ik i by simp_all
    have jd: "j div K = 1" "j mod K = j - K" using div_mod_upper[of K j] jk j by simp_all
    show ?thesis unfolding t b id jd using ik jk i j by (simp add: Hadamard_def H_def)
  qed
qed (simp_all add: Hadamard_def H_def)

lemma had_tensor_mult:
  assumes K: "0 < K" and a: "dim_vec a = K" and c: "dim_vec c = K"
  shows "(Hadamard \<Otimes> 1\<^sub>m K) *\<^sub>v (a @\<^sub>v c) =
         (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>v (a + c)) @\<^sub>v (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>v (a - c))"
proof -
  have I: "(z \<cdot>\<^sub>m 1\<^sub>m K) *\<^sub>v w = z \<cdot>\<^sub>v w" if w: "dim_vec w = K" for z :: complex and w
    using smult_mat_mult_vec[OF one_carrier_mat carrier_vecI[OF w]] one_mult_mat_vec[OF carrier_vecI[OF w]] by simp
  have "(Hadamard \<Otimes> 1\<^sub>m K) *\<^sub>v (a @\<^sub>v c) =
        (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>v a + complex_of_real (1 / sqrt 2) \<cdot>\<^sub>v c) @\<^sub>v
        (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>v a + complex_of_real (- 1 / sqrt 2) \<cdot>\<^sub>v c)"
    unfolding had_tensor_block[OF K]
    by (subst four_block_mat_mult_vec[OF smult_carrier_mat[OF one_carrier_mat] smult_carrier_mat[OF one_carrier_mat]
          smult_carrier_mat[OF one_carrier_mat] smult_carrier_mat[OF one_carrier_mat] carrier_vecI[OF a] carrier_vecI[OF c]])
       (simp only: I[OF a] I[OF c])
  also have "\<dots> = (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>v (a + c)) @\<^sub>v (complex_of_real (1 / sqrt 2) \<cdot>\<^sub>v (a - c))"
    using a c by (intro eq_vecI) (auto simp: algebra_simps add_divide_distrib diff_divide_distrib)
  finally show ?thesis .
qed

lemma cswap_mult:
  assumes a: "dim_vec a = n * n" and c: "dim_vec c = n * n"
  shows "cswap n *\<^sub>v (a @\<^sub>v c) = a @\<^sub>v (swap_mat n *\<^sub>v c)"
proof -
  have "cswap n *\<^sub>v (a @\<^sub>v c) = (1\<^sub>m (n * n) *\<^sub>v a + 0\<^sub>m (n * n) (n * n) *\<^sub>v c) @\<^sub>v (0\<^sub>m (n * n) (n * n) *\<^sub>v a + swap_mat n *\<^sub>v c)"
    unfolding cswap_def
    by (rule four_block_mat_mult_vec[OF one_carrier_mat zero_carrier_mat zero_carrier_mat swap_mat_carrier carrier_vecI[OF a] carrier_vecI[OF c]])
  also have "1\<^sub>m (n * n) *\<^sub>v a = a" by (rule one_mult_mat_vec[OF carrier_vecI[OF a]])
  also have "0\<^sub>m (n * n) (n * n) *\<^sub>v c = 0\<^sub>v (n * n)" by (rule zero_mat_mult_vec[OF c])
  also have "0\<^sub>m (n * n) (n * n) *\<^sub>v a = 0\<^sub>v (n * n)" by (rule zero_mat_mult_vec[OF a])
  also have "a + 0\<^sub>v (n * n) = a" by (rule right_zero_vec[OF carrier_vecI[OF a]])
  also have "0\<^sub>v (n * n) + swap_mat n *\<^sub>v c = swap_mat n *\<^sub>v c"
    by (rule left_zero_vec, rule carrier_vecI) (simp add: swap_mat_def)
  finally show ?thesis .
qed

text \<open>$\ket0\otimes w$ is $w\oplus0$.\<close>

lemma ket0_block:
  assumes w: "dim_vec w = K"
  shows "tensor_vec (unit_vec 2 0) w = w @\<^sub>v 0\<^sub>v K"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (w @\<^sub>v 0\<^sub>v K)"
  hence i: "i < 2 * K" using w by simp
  have "tensor_vec (unit_vec 2 0) w $ i = unit_vec 2 0 $ (i div K) * w $ (i mod K)"
    by (rule tensor_vec_index[OF _ w i]) simp
  thus "tensor_vec (unit_vec 2 0) w $ i = (w @\<^sub>v 0\<^sub>v K) $ i"
    using i w div_mod_upper[of K i] by (cases "i < K") simp_all
qed (use w in \<open>simp add: tensor_vec_dim\<close>)

theorem swap_test_output:
  assumes p: "dim_vec \<psi> = n" and f: "dim_vec \<phi> = n"
  shows "swap_test n *\<^sub>v (tensor_vec \<psi> \<phi> @\<^sub>v 0\<^sub>v (n * n)) =
         ((1 / 2) \<cdot>\<^sub>v (tensor_vec \<psi> \<phi> + tensor_vec \<phi> \<psi>)) @\<^sub>v ((1 / 2) \<cdot>\<^sub>v (tensor_vec \<psi> \<phi> - tensor_vec \<phi> \<psi>))"
proof (cases "n = 0")
  case True
  have "dim_vec (tensor_vec \<psi> \<phi>) = 0" "dim_vec (tensor_vec \<phi> \<psi>) = 0" using p f True tensor_vec_dim by auto
  moreover have "dim_row (swap_test n) = 0" using True by (simp add: swap_test_def Hadamard_def H_def)
  ultimately show ?thesis by (intro eq_vecI) simp_all
next
  case False
  let ?w = "tensor_vec \<psi> \<phi>" and ?w' = "tensor_vec \<phi> \<psi>" and ?s = "complex_of_real (1 / sqrt 2)" and ?K = "n * n"
  have K0: "0 < ?K" using False by simp
  have dw: "dim_vec ?w = ?K" and dw': "dim_vec ?w' = ?K" using tensor_vec_dim p f by blast+
  have x0: "?w @\<^sub>v 0\<^sub>v ?K \<in> carrier_vec (?K + ?K)" using dw by (intro carrier_vecI) simp
  have ss: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2" by (simp flip: of_real_mult)
  have s1: "(Hadamard \<Otimes> 1\<^sub>m ?K) *\<^sub>v (?w @\<^sub>v 0\<^sub>v ?K) = (?s \<cdot>\<^sub>v ?w) @\<^sub>v (?s \<cdot>\<^sub>v ?w)"
  proof -
    have "(Hadamard \<Otimes> 1\<^sub>m ?K) *\<^sub>v (?w @\<^sub>v 0\<^sub>v ?K) = (?s \<cdot>\<^sub>v (?w + 0\<^sub>v ?K)) @\<^sub>v (?s \<cdot>\<^sub>v (?w - 0\<^sub>v ?K))"
      by (rule had_tensor_mult[OF K0 dw]) simp
    also have "?w + 0\<^sub>v ?K = ?w" using dw by (intro eq_vecI) simp_all
    also have "?w - 0\<^sub>v ?K = ?w" using dw by (intro eq_vecI) simp_all
    finally show ?thesis .
  qed
  have Sw: "swap_mat n *\<^sub>v (?s \<cdot>\<^sub>v ?w) = ?s \<cdot>\<^sub>v ?w'"
    using mult_mat_vec[OF swap_mat_carrier carrier_vecI[OF dw], of ?s] swap_mat_tensor[OF p f] by simp
  have s2: "cswap n *\<^sub>v ((?s \<cdot>\<^sub>v ?w) @\<^sub>v (?s \<cdot>\<^sub>v ?w)) = (?s \<cdot>\<^sub>v ?w) @\<^sub>v (?s \<cdot>\<^sub>v ?w')"
    unfolding Sw[symmetric] by (rule cswap_mult) (simp_all add: dw)
  have s3: "(Hadamard \<Otimes> 1\<^sub>m ?K) *\<^sub>v ((?s \<cdot>\<^sub>v ?w) @\<^sub>v (?s \<cdot>\<^sub>v ?w')) =
            ((1 / 2) \<cdot>\<^sub>v (?w + ?w')) @\<^sub>v ((1 / 2) \<cdot>\<^sub>v (?w - ?w'))"
  proof -
    have "(Hadamard \<Otimes> 1\<^sub>m ?K) *\<^sub>v ((?s \<cdot>\<^sub>v ?w) @\<^sub>v (?s \<cdot>\<^sub>v ?w')) =
          (?s \<cdot>\<^sub>v (?s \<cdot>\<^sub>v ?w + ?s \<cdot>\<^sub>v ?w')) @\<^sub>v (?s \<cdot>\<^sub>v (?s \<cdot>\<^sub>v ?w - ?s \<cdot>\<^sub>v ?w'))"
      by (rule had_tensor_mult[OF K0]) (simp_all add: dw dw')
    also have "?s \<cdot>\<^sub>v (?s \<cdot>\<^sub>v ?w + ?s \<cdot>\<^sub>v ?w') = (1 / 2) \<cdot>\<^sub>v (?w + ?w')"
      using dw dw' by (intro eq_vecI) (simp_all add: ss add_divide_distrib)
    also have "?s \<cdot>\<^sub>v (?s \<cdot>\<^sub>v ?w - ?s \<cdot>\<^sub>v ?w') = (1 / 2) \<cdot>\<^sub>v (?w - ?w')"
      using dw dw' by (intro eq_vecI) (simp_all add: ss diff_divide_distrib)
    finally show ?thesis .
  qed
  have "swap_test n *\<^sub>v (?w @\<^sub>v 0\<^sub>v ?K) = (Hadamard \<Otimes> 1\<^sub>m ?K) *\<^sub>v (cswap n *\<^sub>v ((Hadamard \<Otimes> 1\<^sub>m ?K) *\<^sub>v (?w @\<^sub>v 0\<^sub>v ?K)))"
    unfolding swap_test_def
    using assoc_mult_mat_vec[OF had_tensor_carrier mult_carrier_mat[OF cswap_carrier had_tensor_carrier] x0]
          assoc_mult_mat_vec[OF cswap_carrier had_tensor_carrier x0] by simp
  thus ?thesis unfolding s1 s2 s3 .
qed

theorem swap_test_prob:
  assumes p: "dim_vec \<psi> = n" "\<parallel>\<psi>\<parallel> = 1" and f: "dim_vec \<phi> = n" "\<parallel>\<phi>\<parallel> = 1"
  shows "\<parallel>(1 / 2) \<cdot>\<^sub>v (tensor_vec \<psi> \<phi> + tensor_vec \<phi> \<psi>)\<parallel>\<^sup>2 = (1 + (cmod \<langle>\<psi>|\<phi>\<rangle>)\<^sup>2) / 2"
proof -
  let ?w = "tensor_vec \<psi> \<phi>" and ?w' = "tensor_vec \<phi> \<psi>"
  have dw: "dim_vec ?w = n * n" and dw': "dim_vec ?w' = n * n" using tensor_vec_dim p f by blast+
  have pp: "\<langle>\<psi>|\<psi>\<rangle> = 1" and ff: "\<langle>\<phi>|\<phi>\<rangle> = 1" using p(2) f(2) unfolding cpx_vec_length_inner_prod[symmetric] by simp_all
  have c: "\<langle>\<phi>|\<psi>\<rangle> = cnj \<langle>\<psi>|\<phi>\<rangle>" using inner_prod_cnj[of \<psi> \<phi>] p f by simp
  have sq: "\<langle>\<psi>|\<phi>\<rangle> * cnj \<langle>\<psi>|\<phi>\<rangle> = complex_of_real ((cmod \<langle>\<psi>|\<phi>\<rangle>)\<^sup>2)" using complex_norm_square[of "\<langle>\<psi>|\<phi>\<rangle>"] by simp
  have "complex_of_real (\<parallel>?w + ?w'\<parallel>\<^sup>2) = \<langle>?w + ?w'|?w + ?w'\<rangle>" by (rule cpx_vec_length_inner_prod)
  also have "\<dots> = \<langle>?w|?w\<rangle> + \<langle>?w|?w'\<rangle> + \<langle>?w'|?w\<rangle> + \<langle>?w'|?w'\<rangle>"
    by (rule No_Cloning.inner_prod_expand) (simp_all add: dw dw')
  also have "\<langle>?w|?w\<rangle> = 1" using tensor_inner_prod[OF p(1) p(1) f(1) f(1)] pp ff by simp
  also have "\<langle>?w|?w'\<rangle> = \<langle>\<psi>|\<phi>\<rangle> * cnj \<langle>\<psi>|\<phi>\<rangle>" using tensor_inner_prod[OF p(1) f(1) f(1) p(1)] c by simp
  also have "\<langle>?w'|?w\<rangle> = cnj \<langle>\<psi>|\<phi>\<rangle> * \<langle>\<psi>|\<phi>\<rangle>" using tensor_inner_prod[OF f(1) p(1) p(1) f(1)] c by simp
  also have "\<langle>?w'|?w'\<rangle> = 1" using tensor_inner_prod[OF f(1) f(1) p(1) p(1)] pp ff by simp
  also have "cnj \<langle>\<psi>|\<phi>\<rangle> * \<langle>\<psi>|\<phi>\<rangle> = \<langle>\<psi>|\<phi>\<rangle> * cnj \<langle>\<psi>|\<phi>\<rangle>" by (simp only: mult_ac)
  also note sq
  finally have "complex_of_real (\<parallel>?w + ?w'\<parallel>\<^sup>2) = complex_of_real (2 + 2 * (cmod \<langle>\<psi>|\<phi>\<rangle>)\<^sup>2)" by simp
  hence "\<parallel>?w + ?w'\<parallel>\<^sup>2 = 2 + 2 * (cmod \<langle>\<psi>|\<phi>\<rangle>)\<^sup>2" by (simp only: of_real_eq_iff)
  moreover have "\<parallel>(1 / 2) \<cdot>\<^sub>v (?w + ?w')\<parallel> = \<parallel>?w + ?w'\<parallel> / 2" by (simp add: cpx_vec_length_smult)
  ultimately have "\<parallel>(1 / 2) \<cdot>\<^sub>v (?w + ?w')\<parallel>\<^sup>2 = (2 + 2 * (cmod \<langle>\<psi>|\<phi>\<rangle>)\<^sup>2) / 2\<^sup>2" by (simp only: power_divide)
  thus ?thesis by simp
qed


subsection \<open>Estimation by sampling (App.~A5)\<close>

text \<open>\<open>bern p n f\<close> is the expectation of $f$ over $n$ independent bits, each \<open>True\<close> with
probability $p$.\<close>

fun bern :: "real \<Rightarrow> nat \<Rightarrow> (bool list \<Rightarrow> real) \<Rightarrow> real" where
  "bern p 0 f = f []"
| "bern p (Suc n) f = p * bern p n (\<lambda>xs. f (True # xs)) + (1 - p) * bern p n (\<lambda>xs. f (False # xs))"

definition cnt :: "bool list \<Rightarrow> real" where
  "cnt xs = real (length (filter id xs))"

lemma cnt_simps [simp]: "cnt [] = 0" "cnt (True # xs) = 1 + cnt xs" "cnt (False # xs) = cnt xs"
  by (simp_all add: cnt_def)

lemma bern_const: "bern p n (\<lambda>_. c) = c"
  by (induction n) (simp_all add: algebra_simps)

lemma bern_add: "bern p n (\<lambda>x. f x + g x) = bern p n f + bern p n g"
proof (induction n arbitrary: f g)
  case (Suc n) show ?case by (simp only: bern.simps Suc.IH) (simp only: distrib_left add_ac)
qed simp

lemma bern_scale: "bern p n (\<lambda>x. c * f x) = c * bern p n f"
proof (induction n arbitrary: f)
  case (Suc n) show ?case by (simp only: bern.simps Suc.IH) (simp only: distrib_left mult_ac)
qed simp

lemma bern_mono:
  assumes p: "0 \<le> p" "p \<le> 1"
  shows "(\<And>x. f x \<le> g x) \<Longrightarrow> bern p n f \<le> bern p n g"
proof (induction n arbitrary: f g)
  case 0 thus ?case by simp
next
  case (Suc n)
  have T: "bern p n (\<lambda>xs. f (True # xs)) \<le> bern p n (\<lambda>xs. g (True # xs))" by (rule Suc.IH) (rule Suc.prems)
  have F: "bern p n (\<lambda>xs. f (False # xs)) \<le> bern p n (\<lambda>xs. g (False # xs))" by (rule Suc.IH) (rule Suc.prems)
  have q: "0 \<le> 1 - p" using p by simp
  show ?case unfolding bern.simps by (rule add_mono[OF mult_left_mono[OF T p(1)] mult_left_mono[OF F q]])
qed

lemma bern_mean: "bern p n cnt = real n * p"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "bern p n (\<lambda>xs. 1 + cnt xs) = 1 + bern p n cnt" using bern_add[of p n "\<lambda>_. 1" cnt] bern_const by simp
  thus ?case using Suc by (simp add: algebra_simps)
qed

lemma bern_var: "bern p n (\<lambda>xs. (cnt xs - real n * p)\<^sup>2) = real n * p * (1 - p)"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  let ?D = "\<lambda>xs. cnt xs - real n * p"
  have D0: "bern p n ?D = 0"
    using bern_add[of p n cnt "\<lambda>_. - real n * p"] bern_mean[of p n] bern_const by simp
  have gen: "bern p n (\<lambda>xs. (?D xs + a)\<^sup>2) = real n * p * (1 - p) + a\<^sup>2" for a
  proof -
    have "(\<lambda>xs. (?D xs + a)\<^sup>2) = (\<lambda>xs. (?D xs)\<^sup>2 + ((2 * a) * ?D xs + a\<^sup>2))"
      by (rule ext) (simp add: power2_eq_square algebra_simps)
    hence "bern p n (\<lambda>xs. (?D xs + a)\<^sup>2) = bern p n (\<lambda>xs. (?D xs)\<^sup>2) + ((2 * a) * bern p n ?D + a\<^sup>2)"
      by (simp only: bern_add bern_scale bern_const)
    thus ?thesis using Suc D0 by simp
  qed
  have T: "(\<lambda>xs. (cnt (True # xs) - real (Suc n) * p)\<^sup>2) = (\<lambda>xs. (?D xs + (1 - p))\<^sup>2)"
    by (rule ext) (simp add: algebra_simps)
  have F: "(\<lambda>xs. (cnt (False # xs) - real (Suc n) * p)\<^sup>2) = (\<lambda>xs. (?D xs + (- p))\<^sup>2)"
    by (rule ext) (simp add: algebra_simps)
  show ?case unfolding bern.simps T F gen by (simp add: power2_eq_square algebra_simps)
qed

text \<open>Chebyshev for the sample mean.\<close>

lemma bern_chebyshev:
  assumes p: "0 \<le> p" "p \<le> 1" and n: "0 < n" and d: "0 < \<delta>"
  shows "bern p n (\<lambda>xs. if \<delta> \<le> \<bar>cnt xs / real n - p\<bar> then 1 else 0) \<le> p * (1 - p) / (real n * \<delta>\<^sup>2)"
proof -
  let ?c = "1 / (real n * \<delta>)\<^sup>2"
  have nd: "0 < real n * \<delta>" using n d by simp
  have pt: "(if \<delta> \<le> \<bar>cnt xs / real n - p\<bar> then 1 else 0) \<le> ?c * (cnt xs - real n * p)\<^sup>2" for xs
  proof (cases "\<delta> \<le> \<bar>cnt xs / real n - p\<bar>")
    case True
    have "\<bar>cnt xs - real n * p\<bar> = real n * \<bar>cnt xs / real n - p\<bar>" using n by (simp add: field_simps abs_mult[symmetric])
    hence "real n * \<delta> \<le> \<bar>cnt xs - real n * p\<bar>" using True n by simp
    hence le: "(real n * \<delta>)\<^sup>2 \<le> (cnt xs - real n * p)\<^sup>2" using nd by (metis abs_le_square_iff abs_of_pos)
    have pos: "0 < (real n * \<delta>)\<^sup>2" using n d by simp
    have "1 \<le> (cnt xs - real n * p)\<^sup>2 / (real n * \<delta>)\<^sup>2" by (subst le_divide_eq_1_pos[OF pos]) (rule le)
    also have "\<dots> = ?c * (cnt xs - real n * p)\<^sup>2" by (rule divide_inverse_commute[unfolded inverse_eq_divide])
    finally show ?thesis using True by (simp only: if_True)
  qed simp
  have "bern p n (\<lambda>xs. if \<delta> \<le> \<bar>cnt xs / real n - p\<bar> then 1 else 0) \<le> bern p n (\<lambda>xs. ?c * (cnt xs - real n * p)\<^sup>2)"
    by (rule bern_mono[OF p pt])
  also have "\<dots> = ?c * (real n * p * (1 - p))" by (simp only: bern_scale bern_var)
  also have "\<dots> = p * (1 - p) / (real n * \<delta>\<^sup>2)" using n d by (simp add: field_simps power2_eq_square)
  finally show ?thesis .
qed

text \<open>$3/\varepsilon^2$ samples estimate $p$ within $\varepsilon/2$ with probability $\ge2/3$.\<close>

lemma bern_samples:
  assumes p: "0 \<le> p" "p \<le> 1" and e: "0 < \<epsilon>" and n: "3 / \<epsilon>\<^sup>2 \<le> real n"
  shows "bern p n (\<lambda>xs. if \<epsilon> / 2 \<le> \<bar>cnt xs / real n - p\<bar> then 1 else 0) \<le> 1 / 3"
proof -
  have e2: "0 < \<epsilon>\<^sup>2" using e by simp
  have n0: "0 < n" using n e2 by (cases n) (auto simp: field_simps)
  have "bern p n (\<lambda>xs. if \<epsilon> / 2 \<le> \<bar>cnt xs / real n - p\<bar> then 1 else 0) \<le> p * (1 - p) / (real n * (\<epsilon> / 2)\<^sup>2)"
    by (rule bern_chebyshev[OF p n0]) (use e in simp)
  also have "p * (1 - p) \<le> 1 / 4"
  proof -
    have "p * (1 - p) = 1 / 4 - (p - 1 / 2)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
    thus ?thesis by simp
  qed
  hence "p * (1 - p) / (real n * (\<epsilon> / 2)\<^sup>2) \<le> (1 / 4) / (real n * (\<epsilon> / 2)\<^sup>2)"
    using n0 e by (intro divide_right_mono) simp_all
  also have "(1 / 4) / (real n * (\<epsilon> / 2)\<^sup>2) = 1 / (real n * \<epsilon>\<^sup>2)" by (simp add: power_divide)
  also have "\<dots> \<le> 1 / 3"
  proof -
    have "3 \<le> real n * \<epsilon>\<^sup>2" using n e2 by (simp add: field_simps)
    thus ?thesis by (simp add: field_simps)
  qed
  finally show ?thesis .
qed

text \<open>The paper takes $1/(3\varepsilon^2)$ samples.  That is too few: for $\varepsilon=1/4$, $p=1/2$ and
$n=6\ge16/3$ samples, the estimate misses by more than $\varepsilon/2$ with probability $11/16>1/3$.\<close>

lemma paper_sample_count_too_small:
  "6 \<ge> 1 / (3 * (1 / 4 :: real)\<^sup>2)"
  "bern (1 / 2) 6 (\<lambda>xs. if 1 / 8 < \<bar>cnt xs / 6 - 1 / 2\<bar> then 1 else 0) = 11 / 16"
  by (simp_all add: numeral_eq_Suc)


text \<open>Matrix inversion estimation: run the algorithm to accuracy $\varepsilon/4$, measure $M$
($\norm M\le1$) and average $3/\varepsilon^2$ outcomes; the average is within $\varepsilon$ of
$\langle x|M|x\rangle$ with probability $\ge2/3$.\<close>

lemma abs_shift: "e \<le> \<bar>a - t\<bar> \<Longrightarrow> \<bar>m - t\<bar> \<le> e / 2 \<Longrightarrow> e / 2 \<le> \<bar>a - (m::real)\<bar>"
  by arith

theorem estimate_expectation:
  assumes x: "dim_vec x = n" "\<parallel>x\<parallel> = 1" and y: "dim_vec y = n" "\<parallel>y\<parallel> = 1"
      and Mc: "M \<in> carrier_mat n n" and Mb: "\<And>v. dim_vec v = n \<Longrightarrow> \<parallel>M *\<^sub>v v\<parallel> \<le> \<parallel>v\<parallel>"
      and close: "\<parallel>y - x\<parallel> \<le> \<epsilon> / 4" and e: "0 < \<epsilon>"
      and mu: "0 \<le> Re \<langle>y|M *\<^sub>v y\<rangle>" "Re \<langle>y|M *\<^sub>v y\<rangle> \<le> 1" and k: "3 / \<epsilon>\<^sup>2 \<le> real k"
  shows "bern (Re \<langle>y|M *\<^sub>v y\<rangle>) k (\<lambda>xs. if \<epsilon> \<le> \<bar>cnt xs / real k - Re \<langle>x|M *\<^sub>v x\<rangle>\<bar> then 1 else 0) \<le> 1 / 3"
proof -
  let ?\<mu> = "Re \<langle>y|M *\<^sub>v y\<rangle>" and ?t = "Re \<langle>x|M *\<^sub>v x\<rangle>"
  have "\<bar>?\<mu> - ?t\<bar> \<le> cmod (\<langle>y|M *\<^sub>v y\<rangle> - \<langle>x|M *\<^sub>v x\<rangle>)" using abs_Re_le_cmod[of "\<langle>y|M *\<^sub>v y\<rangle> - \<langle>x|M *\<^sub>v x\<rangle>"] by simp
  also have "\<dots> \<le> 2 * 1 * \<parallel>y - x\<parallel>" by (rule expect_stable[OF x y Mc]) (simp add: Mb)
  finally have mt: "\<bar>?\<mu> - ?t\<bar> \<le> \<epsilon> / 2" using close by simp
  have pt: "(if \<epsilon> \<le> \<bar>cnt xs / real k - ?t\<bar> then 1 else 0) \<le> (if \<epsilon> / 2 \<le> \<bar>cnt xs / real k - ?\<mu>\<bar> then 1 else (0::real))" for xs
    using abs_shift[OF _ mt] by simp
  have "bern ?\<mu> k (\<lambda>xs. if \<epsilon> \<le> \<bar>cnt xs / real k - ?t\<bar> then 1 else 0)
        \<le> bern ?\<mu> k (\<lambda>xs. if \<epsilon> / 2 \<le> \<bar>cnt xs / real k - ?\<mu>\<bar> then 1 else 0)" by (rule bern_mono[OF mu pt])
  also have "\<dots> \<le> 1 / 3" by (rule bern_samples[OF mu e k])
  finally show ?thesis .
qed

subsection \<open>Preconditioning\<close>

text \<open>Left preconditioning $BAx=Bb$ and right preconditioning $ABc=b$, $x=Bc$, are sound.  The paper
writes $(AB)c=Bb$, which is neither: in the example below its unique solution $c$ gives
$Ac\ne b$ and $A(Bc)\ne b$.\<close>

lemma precond_left:
  fixes A B Bi :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n" and Bi: "Bi \<in> carrier_mat n n" "Bi * B = 1\<^sub>m n"
      and x: "dim_vec x = n" and b: "dim_vec b = n"
  shows "(B * A) *\<^sub>v x = B *\<^sub>v b \<longleftrightarrow> A *\<^sub>v x = b"
proof
  have xc: "x \<in> carrier_vec n" by (rule carrier_vecI[OF x])
  have Axc: "A *\<^sub>v x \<in> carrier_vec n" using A x by (intro carrier_vecI) simp
  have bc: "b \<in> carrier_vec n" by (rule carrier_vecI[OF b])
  assume "(B * A) *\<^sub>v x = B *\<^sub>v b"
  hence BA: "B *\<^sub>v (A *\<^sub>v x) = B *\<^sub>v b" using assoc_mult_mat_vec[OF B A xc] by simp
  have "A *\<^sub>v x = (Bi * B) *\<^sub>v (A *\<^sub>v x)" using Bi(2) one_mult_mat_vec[OF Axc] by simp
  also have "\<dots> = Bi *\<^sub>v (B *\<^sub>v (A *\<^sub>v x))" by (rule assoc_mult_mat_vec[OF Bi(1) B Axc])
  also have "\<dots> = Bi *\<^sub>v (B *\<^sub>v b)" unfolding BA ..
  also have "\<dots> = (Bi * B) *\<^sub>v b" by (rule assoc_mult_mat_vec[OF Bi(1) B bc, symmetric])
  also have "\<dots> = b" using Bi(2) one_mult_mat_vec[OF bc] by simp
  finally show "A *\<^sub>v x = b" .
next
  assume "A *\<^sub>v x = b"
  thus "(B * A) *\<^sub>v x = B *\<^sub>v b" using assoc_mult_mat_vec[OF B A carrier_vecI[OF x]] by simp
qed

lemma precond_right:
  fixes A B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "dim_vec c = n" "(A * B) *\<^sub>v c = b"
  shows "A *\<^sub>v (B *\<^sub>v c) = b"
  using assoc_mult_mat_vec[OF assms(1,2) carrier_vecI[OF assms(3)]] assms(4) by simp

definition "pc_A = Matrix.mat 2 2 (\<lambda>(i, j). if i = 1 \<and> j = 0 then 0 else (1::complex))"
definition "pc_B = Matrix.mat 2 2 (\<lambda>(i, j). if i = 0 \<and> j = 1 then 0 else (1::complex))"
definition "pc_b = Matrix.vec 2 (\<lambda>i. if i = 0 then 1 else (0::complex))"
definition "pc_c = Matrix.vec 2 (\<lambda>i. if i = 0 then 0 else (1::complex))"

lemma paper_precondition_wrong:
  "(pc_A * pc_B) *\<^sub>v pc_c = pc_B *\<^sub>v pc_b"
  "\<And>d. dim_vec d = 2 \<Longrightarrow> (pc_A * pc_B) *\<^sub>v d = pc_B *\<^sub>v pc_b \<Longrightarrow> d = pc_c"
  "pc_A *\<^sub>v pc_c \<noteq> pc_b" "pc_A *\<^sub>v (pc_B *\<^sub>v pc_c) \<noteq> pc_b"
proof -
  show "(pc_A * pc_B) *\<^sub>v pc_c = pc_B *\<^sub>v pc_b"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (pc_B *\<^sub>v pc_b)"
    hence "i = 0 \<or> i = 1" by (simp add: pc_B_def less_2_cases_iff)
    thus "((pc_A * pc_B) *\<^sub>v pc_c) $ i = (pc_B *\<^sub>v pc_b) $ i"
      by (elim disjE) (simp_all add: pc_A_def pc_B_def pc_b_def pc_c_def scalar_prod_def atLeast0LessThan sumof2)
  qed (simp add: pc_A_def pc_B_def)
  show "pc_A *\<^sub>v pc_c \<noteq> pc_b"
  proof
    assume "pc_A *\<^sub>v pc_c = pc_b"
    hence "(pc_A *\<^sub>v pc_c) $ 1 = pc_b $ 1" by simp
    thus False by (simp add: pc_A_def pc_b_def pc_c_def scalar_prod_def atLeast0LessThan sumof2)
  qed
  show "pc_A *\<^sub>v (pc_B *\<^sub>v pc_c) \<noteq> pc_b"
  proof
    assume "pc_A *\<^sub>v (pc_B *\<^sub>v pc_c) = pc_b"
    hence "(pc_A *\<^sub>v (pc_B *\<^sub>v pc_c)) $ 1 = pc_b $ 1" by simp
    thus False by (simp add: pc_A_def pc_B_def pc_b_def pc_c_def scalar_prod_def atLeast0LessThan sumof2)
  qed
  fix d :: "complex Matrix.vec" assume d: "dim_vec d = 2" and e: "(pc_A * pc_B) *\<^sub>v d = pc_B *\<^sub>v pc_b"
  have e0: "2 * d $ 0 + d $ 1 = 1" using arg_cong[OF e, of "\<lambda>v. v $ 0"] d
    by (simp add: pc_A_def pc_B_def pc_b_def scalar_prod_def atLeast0LessThan sumof2)
  have e1: "d $ 0 + d $ 1 = 1" using arg_cong[OF e, of "\<lambda>v. v $ 1"] d
    by (simp add: pc_A_def pc_B_def pc_b_def scalar_prod_def atLeast0LessThan sumof2)
  have "d $ 0 = (2 * d $ 0 + d $ 1) - (d $ 0 + d $ 1)" by (simp add: algebra_simps)
  hence d0: "d $ 0 = 0" unfolding e0 e1 by simp
  have d1: "d $ 1 = 1" using e1 d0 by simp
  note d0 d1
  show "d = pc_c"
  proof (intro eq_vecI)
    fix i assume "i < dim_vec pc_c"
    hence "i = 0 \<or> i = 1" by (simp add: pc_c_def less_2_cases_iff)
    thus "d $ i = pc_c $ i" using \<open>d $ 0 = 0\<close> \<open>d $ 1 = 1\<close> by (elim disjE) (simp_all add: pc_c_def)
  qed (simp add: d pc_c_def)
qed

subsection \<open>Unknown success probability (App.~A1)\<close>

text \<open>Stage $j$ runs $k$ rounds of amplification, $k$ uniform below $2^j$, and measures; the
procedure stops at the first success.  Its stages $0,\dots,m$ all fail with probability
$\prod_j(1-q_j)$, $q_j$ the mean success of stage $j$, and use fewer than $2^{m+1}$ rounds.\<close>

definition aa_mean :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "aa_mean \<theta> M = (\<Sum>k<M. (sin ((2 * real k + 1) * \<theta>))\<^sup>2) / real M"

definition sched_fail :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "sched_fail \<theta> m = (\<Prod>j\<le>m. 1 - aa_mean \<theta> (2 ^ j))"

definition sched_rounds :: "nat \<Rightarrow> nat" where
  "sched_rounds m = (\<Sum>j\<le>m. 2 ^ j - 1)"

lemma aa_mean_bounds: "0 < M \<Longrightarrow> 0 \<le> aa_mean \<theta> M \<and> aa_mean \<theta> M \<le> 1"
proof -
  assume M: "0 < M"
  have "(\<Sum>k<M. (sin ((2 * real k + 1) * \<theta>))\<^sup>2) \<le> (\<Sum>k<M. 1)" by (rule sum_mono) (simp add: abs_sin_le_one abs_square_le_1)
  thus ?thesis using M by (simp add: aa_mean_def sum_nonneg divide_le_eq_1)
qed

lemma prod_le_factor:
  assumes "finite A" "j \<in> A" "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i \<and> f i \<le> (1::real)"
  shows "(\<Prod>i\<in>A. f i) \<le> f j"
proof -
  have "(\<Prod>i\<in>A. f i) = f j * (\<Prod>i\<in>A - {j}. f i)" by (rule prod.remove[OF assms(1,2)])
  also have "\<dots> \<le> f j * 1"
    by (rule mult_left_mono[OF prod_le_1]) (use assms in auto)
  finally show ?thesis by simp
qed

lemma sched_rounds_lt: "sched_rounds m < 2 ^ Suc m"
proof -
  have "sched_rounds m \<le> (\<Sum>j\<le>m. 2 ^ j)" unfolding sched_rounds_def by (rule sum_mono) simp
  also have "(\<Sum>j\<le>m. (2::nat) ^ j) = 2 ^ Suc m - 1" by (induction m) simp_all
  finally have le: "sched_rounds m \<le> 2 ^ Suc m - 1" .
  have "0 < (2::nat) ^ Suc m" by simp
  thus ?thesis using le by arith
qed

theorem doubling_schedule:
  assumes th: "0 < \<theta>" "\<theta> \<le> pi / 2" and s: "0 < s" "s \<le> sin \<theta>" and m: "1 / (sqrt 2 * s) \<le> 2 ^ m"
  shows "sched_fail \<theta> m \<le> 3 / 4" and "sched_rounds m < 2 ^ Suc m"
proof -
  have fac: "\<And>j. j \<in> {..m} \<Longrightarrow> 0 \<le> 1 - aa_mean \<theta> (2 ^ j) \<and> 1 - aa_mean \<theta> (2 ^ j) \<le> 1"
    using aa_mean_bounds by simp
  show "sched_fail \<theta> m \<le> 3 / 4"
  proof (cases "\<theta> \<le> pi / 4")
    case True
    have c: "sqrt 2 / 2 \<le> cos \<theta>"
    proof -
      have "cos (pi / 4) \<le> cos \<theta>" by (rule cos_monotone_0_pi_le) (use th True in simp_all)
      thus ?thesis by (simp add: cos_45)
    qed
    have "sqrt 2 * s \<le> sin (2 * \<theta>)"
    proof -
      have "sqrt 2 * s = 2 * s * (sqrt 2 / 2)" by simp
      also have "\<dots> \<le> 2 * sin \<theta> * cos \<theta>" using s c by (intro mult_mono) simp_all
      finally show ?thesis by (simp add: sin_double)
    qed
    moreover have ps: "0 < sqrt 2 * s" using s by simp
    ultimately have s2: "0 < sin (2 * \<theta>)" "1 / sin (2 * \<theta>) \<le> 1 / (sqrt 2 * s)"
      by (simp_all add: frac_le)
    have "1 / 4 \<le> aa_mean \<theta> (2 ^ m)" unfolding aa_mean_def
      by (rule bhmt_quarter) (use s2 m in simp_all)
    hence "1 - aa_mean \<theta> (2 ^ m) \<le> 3 / 4" by simp
    moreover have "sched_fail \<theta> m \<le> 1 - aa_mean \<theta> (2 ^ m)" unfolding sched_fail_def
      by (rule prod_le_factor[OF _ _ fac]) simp_all
    ultimately show ?thesis by simp
  next
    case False
    have "sin (pi / 4) \<le> sin \<theta>" by (rule sin_monotone_2pi_le) (use th False in simp_all)
    hence "sqrt 2 / 2 \<le> sin \<theta>" by (simp add: sin_45)
    hence "(sqrt 2 / 2)\<^sup>2 \<le> (sin \<theta>)\<^sup>2" by (rule power_mono) simp
    hence q0: "1 / 2 \<le> aa_mean \<theta> 1" by (simp add: aa_mean_def power_divide)
    have "sched_fail \<theta> m \<le> 1 - aa_mean \<theta> (2 ^ 0)" unfolding sched_fail_def
      by (rule prod_le_factor[OF _ _ fac]) simp_all
    thus ?thesis using q0 by simp
  qed
  show "sched_rounds m < 2 ^ Suc m" by (rule sched_rounds_lt)
qed

text \<open>With the success amplitude $\sin\theta\ge1/(4\kappa)$ of \<open>hhl_paper_runtime\<close>: doubling up
to the first power of two $\ge2\sqrt2\,\kappa$ succeeds with probability $\ge1/4$ and uses fewer than
$8\sqrt2\,\kappa$ rounds.\<close>

corollary doubling_schedule_kappa:
  assumes k: "1 \<le> \<kappa>" and th: "0 < \<theta>" "\<theta> \<le> pi / 2" and s: "1 / (4 * \<kappa>) \<le> sin \<theta>"
      and m: "2 * sqrt 2 * \<kappa> \<le> 2 ^ m" and least: "2 ^ (m - 1) < 2 * sqrt 2 * \<kappa>"
  shows "sched_fail \<theta> m \<le> 3 / 4" and "real (sched_rounds m) < 8 * sqrt 2 * \<kappa>"
proof -
  have s0: "0 < 1 / (4 * \<kappa>)" using k by simp
  have "1 / (sqrt 2 * (1 / (4 * \<kappa>))) = 2 * sqrt 2 * \<kappa>"
    using k by (simp add: field_simps real_div_sqrt)
  hence m': "1 / (sqrt 2 * (1 / (4 * \<kappa>))) \<le> 2 ^ m" using m by simp
  show "sched_fail \<theta> m \<le> 3 / 4" by (rule doubling_schedule(1)[OF th s0 s m'])
  have m1: "1 \<le> m"
  proof (rule ccontr)
    assume "\<not> 1 \<le> m"
    hence "m = 0" by simp
    hence "2 * sqrt 2 * \<kappa> \<le> 1" using m by simp
    moreover have "1 < 2 * sqrt 2 * \<kappa>"
    proof -
      have r: "1 \<le> sqrt 2" by simp
      have "2 * 1 * 1 \<le> 2 * sqrt 2 * \<kappa>" by (intro mult_mono) (use r k in simp_all)
      thus ?thesis by simp
    qed
    ultimately show False by simp
  qed
  have "real (sched_rounds m) < real ((2::nat) ^ Suc m)" using sched_rounds_lt[of m] by (simp only: of_nat_less_iff)
  also have "real ((2::nat) ^ Suc m) = (2::real) ^ Suc m" by simp
  also have "(2::real) ^ Suc m = 4 * 2 ^ (m - 1)"
  proof -
    obtain m' where m': "m = Suc m'" using m1 by (cases m) auto
    show ?thesis unfolding m' by simp
  qed
  also have "\<dots> < 4 * (2 * sqrt 2 * \<kappa>)" using least by (subst mult_less_cancel_left_pos) simp_all
  finally show "real (sched_rounds m) < 8 * sqrt 2 * \<kappa>" by simp
qed

end
