theory Day06_15_Universal
  imports Day02_11_Supplement
begin

section \<open>Day 6 and Day 15: the universal properties in the Kronecker model\<close>

text \<open>D6-1: for $\C^n\otimes\C^m=\C^{nm}$ with $(v\otimes w)_{im+j}=v_iw_j$, every bilinear map
$\beta:\C^n\times\C^m\to\C^p$ factors as $\beta(v,w)=L(v\otimes w)$ for a unique linear $L$.  First
for bilinear forms ($p=1$), then coordinatewise.\<close>

definition bilinear_on :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex) \<Rightarrow> bool" where
  "bilinear_on n m \<beta> \<longleftrightarrow>
     (\<forall>v1 v2 w. dim_vec v1 = n \<longrightarrow> dim_vec v2 = n \<longrightarrow> dim_vec w = m \<longrightarrow> \<beta> (v1 + v2) w = \<beta> v1 w + \<beta> v2 w)
   \<and> (\<forall>v w1 w2. dim_vec v = n \<longrightarrow> dim_vec w1 = m \<longrightarrow> dim_vec w2 = m \<longrightarrow> \<beta> v (w1 + w2) = \<beta> v w1 + \<beta> v w2)
   \<and> (\<forall>a v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> \<beta> (a \<cdot>\<^sub>v v) w = a * \<beta> v w \<and> \<beta> v (a \<cdot>\<^sub>v w) = a * \<beta> v w)"

definition linear_on :: "nat \<Rightarrow> (complex Matrix.vec \<Rightarrow> complex) \<Rightarrow> bool" where
  "linear_on K L \<longleftrightarrow> (\<forall>x y. dim_vec x = K \<longrightarrow> dim_vec y = K \<longrightarrow> L (x + y) = L x + L y)
                     \<and> (\<forall>a x. dim_vec x = K \<longrightarrow> L (a \<cdot>\<^sub>v x) = a * L x)"

definition trunc_vec :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "trunc_vec v k = Matrix.vec (dim_vec v) (\<lambda>i. if i < k then v $ i else 0)"

lemma dim_trunc_vec [simp]: "dim_vec (trunc_vec v k) = dim_vec v" by (simp add: trunc_vec_def)

lemma trunc_vec_full: "trunc_vec v (dim_vec v) = v" by (rule eq_vecI) (simp_all add: trunc_vec_def)

lemma trunc_vec_Suc: "k < dim_vec v \<Longrightarrow> trunc_vec v (Suc k) = trunc_vec v k + v $ k \<cdot>\<^sub>v unit_vec (dim_vec v) k"
  by (rule eq_vecI) (auto simp: trunc_vec_def unit_vec_def less_Suc_eq)

lemma trunc_vec_zero: "trunc_vec v 0 = 0\<^sub>v (dim_vec v)" by (rule eq_vecI) (simp_all add: trunc_vec_def)

text \<open>A linear map is determined by its values on the unit vectors.\<close>

lemma linear_on_zero: "linear_on K L \<Longrightarrow> L (0\<^sub>v K) = 0"
proof -
  assume l: "linear_on K L"
  have "L ((0::complex) \<cdot>\<^sub>v 0\<^sub>v K) = (0::complex) * L (0\<^sub>v K)" using l unfolding linear_on_def by simp
  moreover have "(0::complex) \<cdot>\<^sub>v 0\<^sub>v K = 0\<^sub>v K" by (rule eq_vecI) simp_all
  ultimately show ?thesis by simp
qed

lemma linear_on_expand:
  assumes l: "linear_on K L" and x: "dim_vec x = K"
  shows "L x = (\<Sum>k<K. x $ k * L (unit_vec K k))"
proof -
  have "k \<le> K \<Longrightarrow> L (trunc_vec x k) = (\<Sum>i<k. x $ i * L (unit_vec K i))" for k
  proof (induction k)
    case 0 thus ?case using linear_on_zero[OF l] x by (simp add: trunc_vec_zero)
  next
    case (Suc k)
    have "L (trunc_vec x (Suc k)) = L (trunc_vec x k) + L (x $ k \<cdot>\<^sub>v unit_vec K k)"
      using trunc_vec_Suc[of k x] Suc.prems x l unfolding linear_on_def by simp
    also have "L (x $ k \<cdot>\<^sub>v unit_vec K k) = x $ k * L (unit_vec K k)" using l unfolding linear_on_def by simp
    finally show ?case using Suc by simp
  qed
  from this[of K] show ?thesis using trunc_vec_full[of x] x by simp
qed

text \<open>A bilinear map is determined by its values on pairs of unit vectors.\<close>

lemma bilinear_on_expand:
  assumes b: "bilinear_on n m \<beta>" and v: "dim_vec v = n" and w: "dim_vec w = m"
  shows "\<beta> v w = (\<Sum>i<n. \<Sum>j<m. (v $ i * w $ j) * \<beta> (unit_vec n i) (unit_vec m j))"
proof -
  have lv: "linear_on n (\<lambda>x. \<beta> x w')" if w': "dim_vec w' = m" for w'
    using b w' unfolding bilinear_on_def linear_on_def by simp
  have lw: "linear_on m (\<lambda>y. \<beta> u y)" if u: "dim_vec u = n" for u
    using b u unfolding bilinear_on_def linear_on_def by simp
  have "\<beta> v w = (\<Sum>i<n. v $ i * \<beta> (unit_vec n i) w)" by (rule linear_on_expand[OF lv[OF w] v])
  also have "\<dots> = (\<Sum>i<n. v $ i * (\<Sum>j<m. w $ j * \<beta> (unit_vec n i) (unit_vec m j)))"
    by (rule sum.cong[OF refl]) (simp add: linear_on_expand[OF lw w])
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<m. (v $ i * w $ j) * \<beta> (unit_vec n i) (unit_vec m j))"
    by (simp add: sum_distrib_left Groups.mult.assoc)
  finally show ?thesis .
qed

lemma sum_div_mod:
  fixes n m :: nat and g :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>k<n * m. g (k div m) (k mod m)) = (\<Sum>i<n. \<Sum>j<m. g i j)"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  let ?f = "\<lambda>k. g (k div m) (k mod m)"
  have u: "{..<Suc n * m} = {..<n * m} \<union> {n * m..<n * m + m}" by auto
  have "(\<Sum>k<Suc n * m. ?f k) = (\<Sum>k\<in>{..<n * m} \<union> {n * m..<n * m + m}. ?f k)" unfolding u ..
  also have "\<dots> = (\<Sum>k<n * m. ?f k) + (\<Sum>k\<in>{n * m..<n * m + m}. ?f k)" by (rule sum.union_disjoint) auto
  also have "(\<Sum>k\<in>{n * m..<n * m + m}. ?f k) = (\<Sum>j<m. ?f (n * m + j))"
  proof -
    have "{n * m..<n * m + m} = (\<lambda>j. n * m + j) ` {..<m}"
    proof
      show "{n * m..<n * m + m} \<subseteq> (\<lambda>j. n * m + j) ` {..<m}"
      proof
        fix x assume x: "x \<in> {n * m..<n * m + m}"
        hence "x = n * m + (x - n * m)" "x - n * m \<in> {..<m}" by auto
        thus "x \<in> (\<lambda>j. n * m + j) ` {..<m}" by (rule image_eqI)
      qed
    qed auto
    moreover have "inj_on (\<lambda>j. n * m + j) {..<m}" by (simp add: inj_on_def)
    ultimately show ?thesis by (simp add: sum.reindex)
  qed
  also have "(\<Sum>j<m. ?f (n * m + j)) = (\<Sum>j<m. g n j)" by (rule sum.cong[OF refl]) auto
  finally show ?case using Suc by simp
qed

theorem tensor_universal_property:
  assumes b: "bilinear_on n m \<beta>"
  shows "\<exists>L. linear_on (n * m) L \<and> (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L (tensor_vec v w) = \<beta> v w)
           \<and> (\<forall>L'. linear_on (n * m) L' \<and> (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L' (tensor_vec v w) = \<beta> v w)
                  \<longrightarrow> (\<forall>x. dim_vec x = n * m \<longrightarrow> L' x = L x))"
proof -
  define L where "L x = (\<Sum>k<n * m. x $ k * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)))" for x
  have lin: "linear_on (n * m) L"
    unfolding linear_on_def L_def by (auto simp: distrib_right sum_distrib_left sum.distrib Groups.mult.assoc)
  have el: "L (tensor_vec v w) = \<beta> v w" if v: "dim_vec v = n" and w: "dim_vec w = m" for v w
  proof -
    have "L (tensor_vec v w) = (\<Sum>k<n * m. (v $ (k div m) * w $ (k mod m)) * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)))"
      unfolding L_def by (rule sum.cong[OF refl]) (simp add: tensor_vec_index[OF v w])
    also have "\<dots> = (\<Sum>i<n. \<Sum>j<m. (v $ i * w $ j) * \<beta> (unit_vec n i) (unit_vec m j))" by (rule sum_div_mod)
    also have "\<dots> = \<beta> v w" by (rule bilinear_on_expand[OF b v w, symmetric])
    finally show ?thesis .
  qed
  have un: "L' x = L x" if l': "linear_on (n * m) L'" and e': "\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L' (tensor_vec v w) = \<beta> v w"
    and x: "dim_vec x = n * m" for L' x
  proof -
    have "L' x = (\<Sum>k<n * m. x $ k * L' (unit_vec (n * m) k))" by (rule linear_on_expand[OF l' x])
    also have "\<dots> = L x" unfolding L_def
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {..<n * m}"
      hence k: "k < n * m" by simp
      have m0: "0 < m" using k by (cases m) auto
      have i: "k div m < n" using k by (simp add: less_mult_imp_div_less)
      have j: "k mod m < m" using m0 by simp
      have "unit_vec (n * m) k = tensor_vec (unit_vec n (k div m)) (unit_vec m (k mod m))"
        using tensor_unit_vec[OF i j] by (simp add: Groups.mult.commute)
      thus "x $ k * L' (unit_vec (n * m) k) = x $ k * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m))"
        using e' by simp
    qed
    finally show ?thesis .
  qed
  show ?thesis using lin el un by blast
qed


definition bilinear_vec_on :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec) \<Rightarrow> bool" where
  "bilinear_vec_on n m p \<beta> \<longleftrightarrow>
     (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> dim_vec (\<beta> v w) = p)
   \<and> (\<forall>v1 v2 w. dim_vec v1 = n \<longrightarrow> dim_vec v2 = n \<longrightarrow> dim_vec w = m \<longrightarrow> \<beta> (v1 + v2) w = \<beta> v1 w + \<beta> v2 w)
   \<and> (\<forall>v w1 w2. dim_vec v = n \<longrightarrow> dim_vec w1 = m \<longrightarrow> dim_vec w2 = m \<longrightarrow> \<beta> v (w1 + w2) = \<beta> v w1 + \<beta> v w2)
   \<and> (\<forall>a v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> \<beta> (a \<cdot>\<^sub>v v) w = a \<cdot>\<^sub>v \<beta> v w \<and> \<beta> v (a \<cdot>\<^sub>v w) = a \<cdot>\<^sub>v \<beta> v w)"

definition linear_vec_on :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.vec \<Rightarrow> complex Matrix.vec) \<Rightarrow> bool" where
  "linear_vec_on K p L \<longleftrightarrow> (\<forall>x. dim_vec x = K \<longrightarrow> dim_vec (L x) = p)
     \<and> (\<forall>x y. dim_vec x = K \<longrightarrow> dim_vec y = K \<longrightarrow> L (x + y) = L x + L y)
     \<and> (\<forall>a x. dim_vec x = K \<longrightarrow> L (a \<cdot>\<^sub>v x) = a \<cdot>\<^sub>v L x)"

lemma bilinear_vec_coord: "bilinear_vec_on n m p \<beta> \<Longrightarrow> r < p \<Longrightarrow> bilinear_on n m (\<lambda>v w. \<beta> v w $ r)"
  unfolding bilinear_vec_on_def bilinear_on_def by auto

lemma linear_vec_coord: "linear_vec_on K p L \<Longrightarrow> r < p \<Longrightarrow> linear_on K (\<lambda>x. L x $ r)"
  unfolding linear_vec_on_def linear_on_def by auto

theorem tensor_universal_property_vec:
  assumes b: "bilinear_vec_on n m p \<beta>"
  shows "\<exists>L. linear_vec_on (n * m) p L \<and> (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L (tensor_vec v w) = \<beta> v w)
           \<and> (\<forall>L'. linear_vec_on (n * m) p L' \<and> (\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L' (tensor_vec v w) = \<beta> v w)
                  \<longrightarrow> (\<forall>x. dim_vec x = n * m \<longrightarrow> L' x = L x))"
proof -
  define L where "L x = Matrix.vec p (\<lambda>r. \<Sum>k<n * m. x $ k * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)) $ r)" for x
  have dL: "dim_vec (L x) = p" for x by (simp add: L_def)
  have lin: "linear_vec_on (n * m) p L"
    unfolding linear_vec_on_def
    by (auto simp: dL L_def distrib_right sum_distrib_left sum.distrib Groups.mult.assoc intro!: eq_vecI)
  have el: "L (tensor_vec v w) = \<beta> v w" if v: "dim_vec v = n" and w: "dim_vec w = m" for v w
  proof (rule eq_vecI)
    have db: "dim_vec (\<beta> v w) = p" using b v w unfolding bilinear_vec_on_def by simp
    show "dim_vec (L (tensor_vec v w)) = dim_vec (\<beta> v w)" using db dL by simp
    fix r assume "r < dim_vec (\<beta> v w)"
    hence r: "r < p" using db by simp
    note sc = bilinear_vec_coord[OF b r]
    have "L (tensor_vec v w) $ r = (\<Sum>k<n * m. (v $ (k div m) * w $ (k mod m)) * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)) $ r)"
      unfolding L_def using r by (simp add: tensor_vec_index[OF v w])
    also have "\<dots> = (\<Sum>i<n. \<Sum>j<m. (v $ i * w $ j) * \<beta> (unit_vec n i) (unit_vec m j) $ r)" by (rule sum_div_mod)
    also have "\<dots> = \<beta> v w $ r" by (rule bilinear_on_expand[OF sc v w, symmetric])
    finally show "L (tensor_vec v w) $ r = \<beta> v w $ r" .
  qed
  have un: "L' x = L x" if l': "linear_vec_on (n * m) p L'" and e': "\<forall>v w. dim_vec v = n \<longrightarrow> dim_vec w = m \<longrightarrow> L' (tensor_vec v w) = \<beta> v w"
    and x: "dim_vec x = n * m" for L' x
  proof (rule eq_vecI)
    show "dim_vec (L' x) = dim_vec (L x)" using l' x dL unfolding linear_vec_on_def by simp
    fix r assume "r < dim_vec (L x)"
    hence r: "r < p" using dL by simp
    have "L' x $ r = (\<Sum>k<n * m. x $ k * L' (unit_vec (n * m) k) $ r)" by (rule linear_on_expand[OF linear_vec_coord[OF l' r] x])
    also have "\<dots> = L x $ r" unfolding L_def using r
    proof (simp, intro sum.cong refl)
      fix k assume "k \<in> {..<n * m}"
      hence k: "k < n * m" by simp
      have m0: "0 < m" using k by (cases m) auto
      have i: "k div m < n" using k by (simp add: less_mult_imp_div_less)
      have j: "k mod m < m" using m0 by simp
      have "unit_vec (n * m) k = tensor_vec (unit_vec n (k div m)) (unit_vec m (k mod m))"
        using tensor_unit_vec[OF i j] by (simp add: Groups.mult.commute)
      thus "x $ k * L' (unit_vec (n * m) k) $ r = x $ k * \<beta> (unit_vec n (k div m)) (unit_vec m (k mod m)) $ r"
        using e' by simp
    qed
    finally show "L' x $ r = L x $ r" .
  qed
  show ?thesis using lin el un by blast
qed


text \<open>D15-3: in the coordinate model $L(\Hil_A)\otimes L(\Hil_B)=M_{m^2\times p^2}$ the elementary
tensor $R\otimes T$ is the matrix $(R_{ij}T_{kl})_{(im+j,\,kp+l)}$.  The isomorphism $\Gamma$ of
\<open>operator_tensor_space_isomorphism\<close> sends it to the Kronecker product $R\otimes T$, and $\Gamma$ is
the only linear map that does.\<close>

definition op_elem :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "op_elem m p Ra Tb = Matrix.mat (m * m) (p * p) (\<lambda>(a, b). Ra $$ (a div m, a mod m) * Tb $$ (b div p, b mod p))"

lemma op_elem_carrier [simp]: "op_elem m p Ra Tb \<in> carrier_mat (m * m) (p * p)" by (simp add: op_elem_def)

theorem gamma_elementary:
  assumes Ra: "Ra \<in> carrier_mat m m" and Tb: "Tb \<in> carrier_mat p p"
  shows "operator_tensor_iso_map m p (op_elem m p Ra Tb) = Ra \<Otimes> Tb"
proof (rule eq_matI)
  fix r s assume "r < dim_row (Ra \<Otimes> Tb)" "s < dim_col (Ra \<Otimes> Tb)"
  hence rs: "r < m * p" "s < m * p" using Ra Tb by auto
  have m0: "0 < m" and p0: "0 < p" using rs by (auto intro: gr0I)
  have rd: "r div p < m" "s div p < m" using rs by (auto simp: less_mult_imp_div_less)
  have a: "(r div p) * m + s div p < m * m" and b: "(r mod p) * p + s mod p < p * p"
  proof -
    have "(r div p) * m + s div p < (r div p) * m + m" using rd by simp
    also have "\<dots> = (Suc (r div p)) * m" by simp
    also have "\<dots> \<le> m * m" using rd(1) by (intro mult_le_mono1) simp
    finally show "(r div p) * m + s div p < m * m" .
    have "(r mod p) * p + s mod p < (r mod p) * p + p" using p0 by simp
    also have "\<dots> = (Suc (r mod p)) * p" by simp
    also have "\<dots> \<le> p * p" using p0 by (intro mult_le_mono1) (simp add: Suc_leI)
    finally show "(r mod p) * p + s mod p < p * p" .
  qed
  have "operator_tensor_iso_map m p (op_elem m p Ra Tb) $$ (r, s)
        = Ra $$ (((r div p) * m + s div p) div m, ((r div p) * m + s div p) mod m)
          * Tb $$ (((r mod p) * p + s mod p) div p, ((r mod p) * p + s mod p) mod p)"
    using rs a b by (simp add: operator_tensor_iso_map_def op_elem_def)
  also have "\<dots> = Ra $$ (r div p, s div p) * Tb $$ (r mod p, s mod p)" using rd(2) m0 p0 by simp
  also have "\<dots> = (Ra \<Otimes> Tb) $$ (r, s)" using Ra Tb rs m0 p0 by (simp add: index_tensor_mat)
  finally show "operator_tensor_iso_map m p (op_elem m p Ra Tb) $$ (r, s) = (Ra \<Otimes> Tb) $$ (r, s)" .
qed (use Ra Tb in \<open>auto simp: operator_tensor_iso_map_def\<close>)

definition unit_mat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "unit_mat K1 K2 a b = Matrix.mat K1 K2 (\<lambda>(i, j). if i = a \<and> j = b then 1 else 0)"

lemma unit_mat_carrier [simp]: "unit_mat K1 K2 a b \<in> carrier_mat K1 K2" by (simp add: unit_mat_def)

text \<open>The unit matrices of $M_{m^2\times p^2}$ are elementary tensors of unit matrices.\<close>

lemma unit_mat_op_elem:
  assumes a: "a < m * m" and b: "b < p * p"
  shows "unit_mat (m * m) (p * p) a b = op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p))"
proof (rule eq_matI)
  fix i j assume "i < dim_row (op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p)))"
    "j < dim_col (op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p)))"
  hence ij: "i < m * m" "j < p * p" by (simp_all add: op_elem_def)
  have m0: "0 < m" and p0: "0 < p" using a b by (auto intro: gr0I)
  have e: "x = y \<longleftrightarrow> x div k = y div k \<and> x mod k = y mod k" for x y k :: nat
  proof
    assume h: "x div k = y div k \<and> x mod k = y mod k"
    have "x = x div k * k + x mod k" by simp
    also have "\<dots> = y div k * k + y mod k" using h by simp
    also have "\<dots> = y" by simp
    finally show "x = y" .
  qed simp
  show "unit_mat (m * m) (p * p) a b $$ (i, j) = op_elem m p (unit_mat m m (a div m) (a mod m)) (unit_mat p p (b div p) (b mod p)) $$ (i, j)"
    using ij m0 p0 a b by (auto simp: unit_mat_def op_elem_def less_mult_imp_div_less e[of i a m] e[of j b p])
qed (simp_all add: op_elem_def unit_mat_def)

text \<open>A linear map on $M_{K_1\times K_2}$ is determined by its values on the unit matrices.\<close>

definition linear_mat_on :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "linear_mat_on K1 K2 \<Phi> \<longleftrightarrow>
     (\<forall>x y. x \<in> carrier_mat K1 K2 \<longrightarrow> y \<in> carrier_mat K1 K2 \<longrightarrow> \<Phi> (x + y) = \<Phi> x + \<Phi> y)
   \<and> (\<forall>c x. x \<in> carrier_mat K1 K2 \<longrightarrow> \<Phi> (c \<cdot>\<^sub>m x) = c \<cdot>\<^sub>m \<Phi> x)"

text \<open>Reading a matrix row by row gives a vector, and \<^const>\<open>vec_to_mat\<close> undoes this:
\[
  \begin{pmatrix}a&b&c\\ d&e&f\end{pmatrix}\quad\longmapsto\quad(a,b,c,d,e,f).
\]\<close>

definition mat_to_vec :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec" where
  "mat_to_vec c = Matrix.vec (dim_row c * dim_col c) (\<lambda>k. c $$ (k div dim_col c, k mod dim_col c))"

lemma vec_to_mat_mat_to_vec: "c \<in> carrier_mat K1 K2 \<Longrightarrow> vec_to_mat K1 K2 (mat_to_vec c) = c"
proof (rule eq_matI)
  fix i j assume c: "c \<in> carrier_mat K1 K2" and ij: "i < dim_row c" "j < dim_col c"
  have j: "j < K2" using c ij by simp
  have "i * K2 + j < K1 * K2"
  proof -
    have "i * K2 + j < i * K2 + K2" using j by simp
    also have "\<dots> = Suc i * K2" by simp
    also have "\<dots> \<le> K1 * K2" using c ij by (intro mult_le_mono1) simp
    finally show ?thesis .
  qed
  thus "vec_to_mat K1 K2 (mat_to_vec c) $$ (i, j) = c $$ (i, j)" using c ij j by (simp add: vec_to_mat_def mat_to_vec_def carrier_matD[OF c])
qed (auto simp: vec_to_mat_def)

lemma dim_mat_to_vec: "c \<in> carrier_mat K1 K2 \<Longrightarrow> dim_vec (mat_to_vec c) = K1 * K2" by (simp add: mat_to_vec_def carrier_matD)

lemma vec_to_mat_unit:
  assumes k: "k < K1 * K2"
  shows "vec_to_mat K1 K2 (unit_vec (K1 * K2) k) = unit_mat K1 K2 (k div K2) (k mod K2)"
proof (rule eq_matI)
  fix i j assume ij: "i < dim_row (unit_mat K1 K2 (k div K2) (k mod K2))" "j < dim_col (unit_mat K1 K2 (k div K2) (k mod K2))"
  hence i: "i < K1" and j: "j < K2" by (simp_all add: unit_mat_def)
  have lt: "i * K2 + j < K1 * K2"
  proof -
    have "i * K2 + j < Suc i * K2" using j by simp
    also have "\<dots> \<le> K1 * K2" using i by (intro mult_le_mono1) simp
    finally show ?thesis .
  qed
  have "(i * K2 + j = k) \<longleftrightarrow> (i = k div K2 \<and> j = k mod K2)"
  proof
    assume "i * K2 + j = k" thus "i = k div K2 \<and> j = k mod K2" using j by auto
  next
    assume "i = k div K2 \<and> j = k mod K2" thus "i * K2 + j = k" by (simp add: div_mult_mod_eq)
  qed
  thus "vec_to_mat K1 K2 (unit_vec (K1 * K2) k) $$ (i, j) = unit_mat K1 K2 (k div K2) (k mod K2) $$ (i, j)"
    using i j lt by (simp add: vec_to_mat_def unit_mat_def unit_vec_def)
qed (simp_all add: vec_to_mat_def unit_mat_def)

lemma linear_mat_unique:
  assumes l1: "linear_mat_on K1 K2 \<Phi>" and l2: "linear_mat_on K1 K2 \<Psi>"
    and dims: "\<And>x. x \<in> carrier_mat K1 K2 \<Longrightarrow> dim_row (\<Phi> x) = Q1 \<and> dim_col (\<Phi> x) = Q2 \<and> dim_row (\<Psi> x) = Q1 \<and> dim_col (\<Psi> x) = Q2"
    and e: "\<And>a b. a < K1 \<Longrightarrow> b < K2 \<Longrightarrow> \<Phi> (unit_mat K1 K2 a b) = \<Psi> (unit_mat K1 K2 a b)"
    and c: "c \<in> carrier_mat K1 K2"
  shows "\<Phi> c = \<Psi> c"
proof (rule eq_matI)
  have K20: "K2 = 0 \<or> 0 < K2" by auto
  have uc: "vec_to_mat K1 K2 x \<in> carrier_mat K1 K2" for x by (simp add: vec_to_mat_def)
  have lin: "linear_on (K1 * K2) (\<lambda>x. F (vec_to_mat K1 K2 x) $$ (r, s))" if l: "linear_mat_on K1 K2 F"
    and rs: "\<And>x. x \<in> carrier_mat K1 K2 \<Longrightarrow> r < dim_row (F x) \<and> s < dim_col (F x)" for F r s
  proof -
    have add: "vec_to_mat K1 K2 (x + y) = vec_to_mat K1 K2 x + vec_to_mat K1 K2 y" if "dim_vec x = K1 * K2" "dim_vec y = K1 * K2" for x y
    proof (rule eq_matI)
      fix i j assume "i < dim_row (vec_to_mat K1 K2 x + vec_to_mat K1 K2 y)" "j < dim_col (vec_to_mat K1 K2 x + vec_to_mat K1 K2 y)"
      hence i: "i < K1" and j: "j < K2" by (simp_all add: vec_to_mat_def)
      have "i * K2 + j < K1 * K2"
      proof -
        have "i * K2 + j < Suc i * K2" using j by simp
        also have "\<dots> \<le> K1 * K2" using i by (intro mult_le_mono1) simp
        finally show ?thesis .
      qed
      thus "vec_to_mat K1 K2 (x + y) $$ (i, j) = (vec_to_mat K1 K2 x + vec_to_mat K1 K2 y) $$ (i, j)" using i j that by (simp add: vec_to_mat_def)
    qed (simp_all add: vec_to_mat_def)
    have sm: "vec_to_mat K1 K2 (a \<cdot>\<^sub>v x) = a \<cdot>\<^sub>m vec_to_mat K1 K2 x" if "dim_vec x = K1 * K2" for a x
      by (rule eq_matI) (use that mult_index_lt in \<open>simp_all add: vec_to_mat_def\<close>)
    show ?thesis unfolding linear_on_def
    proof (intro conjI allI impI)
      fix x y :: "complex Matrix.vec" assume x: "dim_vec x = K1 * K2" and y: "dim_vec y = K1 * K2"
      have rs': "r < dim_row (F (vec_to_mat K1 K2 x))" "s < dim_col (F (vec_to_mat K1 K2 x))"
        "r < dim_row (F (vec_to_mat K1 K2 y))" "s < dim_col (F (vec_to_mat K1 K2 y))" using rs uc by auto
      show "F (vec_to_mat K1 K2 (x + y)) $$ (r, s) = F (vec_to_mat K1 K2 x) $$ (r, s) + F (vec_to_mat K1 K2 y) $$ (r, s)"
        unfolding add[OF x y] using l uc rs' unfolding linear_mat_on_def by simp
    next
      fix a and x :: "complex Matrix.vec" assume x: "dim_vec x = K1 * K2"
      have rs': "r < dim_row (F (vec_to_mat K1 K2 x))" "s < dim_col (F (vec_to_mat K1 K2 x))" using rs uc by auto
      show "F (vec_to_mat K1 K2 (a \<cdot>\<^sub>v x)) $$ (r, s) = a * F (vec_to_mat K1 K2 x) $$ (r, s)"
        unfolding sm[OF x] using l uc rs' unfolding linear_mat_on_def by simp
    qed
  qed
  show "dim_row (\<Phi> c) = dim_row (\<Psi> c)" "dim_col (\<Phi> c) = dim_col (\<Psi> c)" using dims[OF c] by simp_all
  fix r s assume "r < dim_row (\<Psi> c)" "s < dim_col (\<Psi> c)"
  hence rs: "r < Q1" "s < Q2" using dims[OF c] by simp_all
  have r1: "\<And>x. x \<in> carrier_mat K1 K2 \<Longrightarrow> r < dim_row (\<Phi> x) \<and> s < dim_col (\<Phi> x)" using dims rs by auto
  have r2: "\<And>x. x \<in> carrier_mat K1 K2 \<Longrightarrow> r < dim_row (\<Psi> x) \<and> s < dim_col (\<Psi> x)" using dims rs by auto
  let ?x = "mat_to_vec c"
  have x: "dim_vec ?x = K1 * K2" by (rule dim_mat_to_vec[OF c])
  have "\<Phi> c $$ (r, s) = \<Phi> (vec_to_mat K1 K2 ?x) $$ (r, s)" unfolding vec_to_mat_mat_to_vec[OF c] ..
  also have "\<dots> = (\<Sum>k<K1 * K2. ?x $ k * \<Phi> (vec_to_mat K1 K2 (unit_vec (K1 * K2) k)) $$ (r, s))"
    by (rule linear_on_expand[OF lin[where F = \<Phi> and r = r and s = s, OF l1 r1] x])
  also have "\<dots> = (\<Sum>k<K1 * K2. ?x $ k * \<Psi> (vec_to_mat K1 K2 (unit_vec (K1 * K2) k)) $$ (r, s))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<K1 * K2}"
    hence k: "k < K1 * K2" by simp
    have K2: "0 < K2" using k by (cases K2) auto
    have "k div K2 < K1" "k mod K2 < K2" using k K2 by (simp_all add: less_mult_imp_div_less)
    thus "?x $ k * \<Phi> (vec_to_mat K1 K2 (unit_vec (K1 * K2) k)) $$ (r, s) = ?x $ k * \<Psi> (vec_to_mat K1 K2 (unit_vec (K1 * K2) k)) $$ (r, s)"
      unfolding vec_to_mat_unit[OF k] using e by simp
  qed
  also have "\<dots> = \<Psi> (vec_to_mat K1 K2 ?x) $$ (r, s)"
    by (rule linear_on_expand[OF lin[where F = \<Psi> and r = r and s = s, OF l2 r2] x, symmetric])
  finally show "\<Phi> c $$ (r, s) = \<Psi> c $$ (r, s)" unfolding vec_to_mat_mat_to_vec[OF c] .
qed

theorem gamma_unique:
  assumes p0: "0 < p" and l: "linear_mat_on (m * m) (p * p) \<Phi>"
    and dims: "\<And>x. x \<in> carrier_mat (m * m) (p * p) \<Longrightarrow> \<Phi> x \<in> carrier_mat (m * p) (m * p)"
    and e: "\<And>Ra Tb. Ra \<in> carrier_mat m m \<Longrightarrow> Tb \<in> carrier_mat p p \<Longrightarrow> \<Phi> (op_elem m p Ra Tb) = Ra \<Otimes> Tb"
    and c: "c \<in> carrier_mat (m * m) (p * p)"
  shows "\<Phi> c = operator_tensor_iso_map m p c"
proof (rule linear_mat_unique[OF l _ _ _ c])
  show "linear_mat_on (m * m) (p * p) (operator_tensor_iso_map m p)"
    unfolding linear_mat_on_def using operator_tensor_iso_map_add[OF p0] operator_tensor_iso_map_smult[OF p0] by blast
  show "\<And>x. x \<in> carrier_mat (m * m) (p * p) \<Longrightarrow> dim_row (\<Phi> x) = m * p \<and> dim_col (\<Phi> x) = m * p
          \<and> dim_row (operator_tensor_iso_map m p x) = m * p \<and> dim_col (operator_tensor_iso_map m p x) = m * p"
    using dims by (auto simp: operator_tensor_iso_map_def)
  fix a b assume a: "a < m * m" and b: "b < p * p"
  show "\<Phi> (unit_mat (m * m) (p * p) a b) = operator_tensor_iso_map m p (unit_mat (m * m) (p * p) a b)"
    unfolding unit_mat_op_elem[OF a b] by (simp add: e gamma_elementary)
qed

end
