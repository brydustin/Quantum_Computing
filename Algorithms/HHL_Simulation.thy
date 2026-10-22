theory HHL_Simulation
  imports HHL_Window
begin

section \<open>HHL with an approximate Hamiltonian simulation\<close>

text \<open>The HHL circuit uses $e^{iAt_0}$ only through controlled powers.  We write the circuit in
a small language of fixed gates and controlled calls of an oracle, count the calls ($2(N-1)$
for HHL) and show that replacing the oracle by any unitary $V$ with
$\norm{Vv-e^{iAt_0}v}\le\eta\norm v$ moves the output by at most (calls)$\cdot\eta$.  With the
window register this gives the end-to-end bound $(\varepsilon+2(N-1)\eta)\norm b$
(theorem \<open>hhl_sim_window_error\<close>).  Any $V$ with this accuracy can be plugged in;
\<open>HHL_Sparse_Circuit\<close> builds one from sparse access by a Trotter circuit.\<close>

subsection \<open>Closeness of block operators\<close>

text \<open>The blocks of a vector on $\C^N\otimes\C^m$.\<close>

definition blk :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "blk m x k = Matrix.vec m (\<lambda>i. x $ (k * m + i))"

lemma dim_blk [simp]: "dim_vec (blk m x k) = m"
  by (simp add: blk_def)

lemma reg_sum_blk:
  assumes "dim_vec x = N * m"
  shows "reg_sum N m (blk m x) = x"
proof (rule eq_vecI)
  fix r assume "r < dim_vec x"
  hence r: "r < N * m" using assms by simp
  note ki = less_mult_imp_div_less[OF r] reg_sum_index_mod[OF r]
  show "reg_sum N m (blk m x) $ r = x $ r"
    using r ki by (simp add: reg_sum_def blk_def mult.commute)
qed (simp add: assms)

lemma vnorm_reg_sum_sq:
  assumes f: "\<And>k. k < N \<Longrightarrow> dim_vec (f k) = m"
  shows "\<parallel>reg_sum N m f\<parallel>\<^sup>2 = (\<Sum>k<N. \<parallel>f k\<parallel>\<^sup>2)"
proof -
  have "complex_of_real (\<parallel>reg_sum N m f\<parallel>\<^sup>2) = (\<Sum>k<N. \<langle>f k|f k\<rangle>)"
    unfolding cpx_vec_length_inner_prod by (rule reg_sum_inner[OF f f])
  also have "\<dots> = complex_of_real (\<Sum>k<N. \<parallel>f k\<parallel>\<^sup>2)" by (simp add: cpx_vec_length_inner_prod[symmetric] of_real_sum)
  finally show ?thesis by (simp only: of_real_eq_iff)
qed

text \<open>If every block of $B$ is $\eta$-close to the block of $B'$, so is the block operator.\<close>

lemma ctrl_blocks_close:
  assumes B: "\<And>k. k < N \<Longrightarrow> B k \<in> carrier_mat m m" and B': "\<And>k. k < N \<Longrightarrow> B' k \<in> carrier_mat m m"
      and close: "\<And>k v. k < N \<Longrightarrow> dim_vec v = m \<Longrightarrow> \<parallel>B k *\<^sub>v v - B' k *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>"
      and x: "dim_vec x = N * m"
  shows "\<parallel>ctrl_blocks N m B *\<^sub>v x - ctrl_blocks N m B' *\<^sub>v x\<parallel> \<le> \<eta> * \<parallel>x\<parallel>"
proof -
  let ?f = "blk m x"
  have e0: "0 \<le> \<eta>" if "0 < N" "0 < m"
  proof -
    have "\<parallel>B 0 *\<^sub>v unit_vec m 0 - B' 0 *\<^sub>v unit_vec m 0\<parallel> \<le> \<eta> * \<parallel>unit_vec m 0\<parallel>" by (rule close) (use that in simp_all)
    moreover have "\<parallel>unit_vec m 0\<parallel> = 1" using that by simp
    ultimately show ?thesis using vnorm_ge0 by (metis mult.right_neutral order_trans)
  qed
  have d: "ctrl_blocks N m B *\<^sub>v x - ctrl_blocks N m B' *\<^sub>v x = reg_sum N m (\<lambda>k. B k *\<^sub>v ?f k - B' k *\<^sub>v ?f k)"
  proof -
    have cb: "ctrl_blocks N m C *\<^sub>v x = reg_sum N m (\<lambda>k. C k *\<^sub>v ?f k)" if C: "\<And>k. k < N \<Longrightarrow> C k \<in> carrier_mat m m" for C
      using ctrl_blocks_reg_sum[where B = C and f = ?f and N = N and m = m] C reg_sum_blk[OF x] by simp
    have c1: "ctrl_blocks N m B *\<^sub>v x = reg_sum N m (\<lambda>k. B k *\<^sub>v ?f k)" by (rule cb) (rule B)
    have c2: "ctrl_blocks N m B' *\<^sub>v x = reg_sum N m (\<lambda>k. B' k *\<^sub>v ?f k)" by (rule cb) (rule B')
    show ?thesis unfolding c1 c2 by (rule reg_sum_diff) (simp add: carrier_matD(1)[OF B'])
  qed
  have dd: "dim_vec (B k *\<^sub>v ?f k - B' k *\<^sub>v ?f k) = m" if "k < N" for k using carrier_matD(1)[OF B'[OF that]] by simp
  have "\<parallel>ctrl_blocks N m B *\<^sub>v x - ctrl_blocks N m B' *\<^sub>v x\<parallel>\<^sup>2 = (\<Sum>k<N. \<parallel>B k *\<^sub>v ?f k - B' k *\<^sub>v ?f k\<parallel>\<^sup>2)"
    unfolding d by (rule vnorm_reg_sum_sq[OF dd])
  also have "\<dots> \<le> (\<Sum>k<N. (\<eta> * \<parallel>?f k\<parallel>)\<^sup>2)"
    by (rule sum_mono, rule power_mono[OF close]) (simp_all add: vnorm_ge0)
  also have "\<dots> = \<eta>\<^sup>2 * \<parallel>x\<parallel>\<^sup>2"
    unfolding power_mult_distrib sum_distrib_left[symmetric]
    using vnorm_reg_sum_sq[of N ?f m] reg_sum_blk[OF x] by simp
  also have "\<dots> = (\<eta> * \<parallel>x\<parallel>)\<^sup>2" by (simp add: power_mult_distrib)
  finally have sq: "\<parallel>ctrl_blocks N m B *\<^sub>v x - ctrl_blocks N m B' *\<^sub>v x\<parallel>\<^sup>2 \<le> (\<eta> * \<parallel>x\<parallel>)\<^sup>2" .
  show ?thesis
  proof (cases "N = 0 \<or> m = 0")
    case True
    hence "x = 0\<^sub>v 0" using x by (auto intro: eq_vecI)
    moreover have "ctrl_blocks N m B *\<^sub>v x - ctrl_blocks N m B' *\<^sub>v x = 0\<^sub>v 0" using True by (auto intro: eq_vecI)
    ultimately show ?thesis by (simp add: cpx_vec_length_def)
  next
    case False
    hence "0 \<le> \<eta> * \<parallel>x\<parallel>" using e0 vnorm_ge0 by simp
    thus ?thesis by (rule power2_le_imp_le[OF sq])
  qed
qed

text \<open>$\eta$-closeness of two operators: $\norm{Uv-Vv}\le\eta\norm v$ for every $v$.\<close>

definition op_close :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "op_close n \<eta> U V \<longleftrightarrow> (\<forall>v. dim_vec v = n \<longrightarrow> \<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>)"

lemma op_closeD: "op_close n \<eta> U V \<Longrightarrow> dim_vec v = n \<Longrightarrow> \<parallel>U *\<^sub>v v - V *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>"
  by (simp add: op_close_def)

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

subsection \<open>Tensoring with the ancilla\<close>

definition half :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "half x b = Matrix.vec (dim_vec x div 2) (\<lambda>i. x $ (i * 2 + b))"

lemma dim_half [simp]: "dim_vec (half x b) = dim_vec x div 2"
  by (simp add: half_def)

lemma sum_pairs:
  fixes n :: nat and g :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>r<n * 2. g r) = (\<Sum>i<n. g (i * 2) + g (i * 2 + 1))"
proof (induction n)
  case (Suc n)
  have "Suc n * 2 = Suc (Suc (n * 2))" by simp
  thus ?case using Suc.IH by (simp add: add.assoc add.commute add.left_commute)
qed simp

lemma vnorm_half_sq:
  assumes "dim_vec x = n * 2"
  shows "\<parallel>x\<parallel>\<^sup>2 = \<parallel>half x 0\<parallel>\<^sup>2 + \<parallel>half x 1\<parallel>\<^sup>2"
  unfolding vnorm_sq using assms by (simp add: half_def sum_pairs sum.distrib)

lemma half_minus:
  assumes y: "dim_vec y = dim_vec x" and b: "b < 2"
  shows "half (x - y) b = half x b - half y b"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (half x b - half y b)"
  hence "i < dim_vec x div 2" using y by simp
  hence "i * 2 + b < dim_vec x" using b by linarith
  thus "half (x - y) b $ i = (half x b - half y b) $ i" using y \<open>i < dim_vec x div 2\<close> by (simp add: half_def)
qed (simp add: y)

lemma tensor_one2_index:
  assumes M: "M \<in> carrier_mat n n" and x: "dim_vec x = n * 2" and i: "i < n" and b: "b < 2"
  shows "((M \<Otimes> 1\<^sub>m 2) *\<^sub>v x) $ (i * 2 + b) = (M *\<^sub>v half x b) $ i"
proof -
  have n0: "0 < n" using i by simp
  have r: "i * 2 + b < n * 2" using i b by linarith
  have "((M \<Otimes> 1\<^sub>m 2) *\<^sub>v x) $ (i * 2 + b) = (\<Sum>c<n * 2. (M \<Otimes> 1\<^sub>m 2) $$ (i * 2 + b, c) * x $ c)"
    using M x r by (simp add: scalar_prod_def atLeast0LessThan mult.commute)
  also have "\<dots> = (\<Sum>j<n. M $$ (i, j) * x $ (j * 2 + b))"
  proof -
    have e: "(M \<Otimes> 1\<^sub>m 2) $$ (i * 2 + b, c) = M $$ (i, c div 2) * (if b = c mod 2 then 1 else 0)" if c: "c < n * 2" for c
      using index_tensor_mat[of M n n "1\<^sub>m 2" 2 2 "i * 2 + b" c] M r c b n0 by simp
    have "(\<Sum>c<n * 2. (M \<Otimes> 1\<^sub>m 2) $$ (i * 2 + b, c) * x $ c) =
          (\<Sum>c<n * 2. M $$ (i, c div 2) * (if b = c mod 2 then 1 else 0) * x $ c)"
      by (rule sum.cong) (simp_all add: e)
    also have "\<dots> = (\<Sum>j<n. M $$ (i, j) * x $ (j * 2 + b))"
    proof -
      have b01: "b = 0 \<or> b = 1" using b by auto
      have o: "Suc (j * 2) mod 2 = 1" "Suc (j * 2) div 2 = j" for j :: nat by presburger+
      show ?thesis unfolding sum_pairs by (intro sum.cong refl) (use b01 in \<open>elim disjE; simp add: o\<close>)
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = (M *\<^sub>v half x b) $ i"
    using M x i by (simp add: half_def scalar_prod_def atLeast0LessThan mult.commute)
  finally show ?thesis .
qed

lemma half_tensor_one2:
  assumes M: "M \<in> carrier_mat n n" and x: "dim_vec x = n * 2" and b: "b < 2"
  shows "half ((M \<Otimes> 1\<^sub>m 2) *\<^sub>v x) b = M *\<^sub>v half x b"
proof (rule eq_vecI)
  have d: "dim_vec ((M \<Otimes> 1\<^sub>m 2) *\<^sub>v x) = n * 2" using M by simp
  show "dim_vec (half ((M \<Otimes> 1\<^sub>m 2) *\<^sub>v x) b) = dim_vec (M *\<^sub>v half x b)" using d M by simp
  fix i assume "i < dim_vec (M *\<^sub>v half x b)"
  hence i: "i < n" using M by simp
  show "half ((M \<Otimes> 1\<^sub>m 2) *\<^sub>v x) b $ i = (M *\<^sub>v half x b) $ i"
    using tensor_one2_index[OF M x i b] d i by (simp add: half_def)
qed

lemma op_close_tensor_one2:
  assumes U: "U \<in> carrier_mat n n" and V: "V \<in> carrier_mat n n" and c: "op_close n \<eta> U V" and e: "0 \<le> \<eta>"
  shows "op_close (n * 2) \<eta> (U \<Otimes> 1\<^sub>m 2) (V \<Otimes> 1\<^sub>m 2)"
  unfolding op_close_def
proof (intro allI impI)
  fix x :: "complex Matrix.vec" assume x: "dim_vec x = n * 2"
  let ?d = "(U \<Otimes> 1\<^sub>m 2) *\<^sub>v x - (V \<Otimes> 1\<^sub>m 2) *\<^sub>v x"
  have dU: "dim_vec ((U \<Otimes> 1\<^sub>m 2) *\<^sub>v x) = n * 2" and dV: "dim_vec ((V \<Otimes> 1\<^sub>m 2) *\<^sub>v x) = n * 2" using U V by simp_all
  have hb: "half ?d b = U *\<^sub>v half x b - V *\<^sub>v half x b" if "b < 2" for b
    unfolding half_minus[OF dV[folded dU] that] half_tensor_one2[OF U x that] half_tensor_one2[OF V x that] ..
  have hx: "dim_vec (half x b) = n" for b using x by simp
  have "\<parallel>?d\<parallel>\<^sup>2 = \<parallel>half ?d 0\<parallel>\<^sup>2 + \<parallel>half ?d 1\<parallel>\<^sup>2" by (rule vnorm_half_sq) (use dU in simp)
  also have "\<dots> \<le> (\<eta> * \<parallel>half x 0\<parallel>)\<^sup>2 + (\<eta> * \<parallel>half x 1\<parallel>)\<^sup>2"
  proof -
    have h0: "half ?d 0 = U *\<^sub>v half x 0 - V *\<^sub>v half x 0" by (rule hb) simp
    have h1: "half ?d 1 = U *\<^sub>v half x 1 - V *\<^sub>v half x 1" by (rule hb) simp
    show ?thesis unfolding h0 h1 by (intro add_mono power_mono op_closeD[OF c hx]) (simp_all add: vnorm_ge0)
  qed
  also have "\<dots> = (\<eta> * \<parallel>x\<parallel>)\<^sup>2" unfolding power_mult_distrib distrib_left[symmetric] vnorm_half_sq[OF x] ..
  finally have "\<parallel>?d\<parallel>\<^sup>2 \<le> (\<eta> * \<parallel>x\<parallel>)\<^sup>2" .
  thus "\<parallel>?d\<parallel> \<le> \<eta> * \<parallel>x\<parallel>" by (rule power2_le_imp_le) (simp add: e vnorm_ge0)
qed

subsection \<open>Gate lists and permutation matrices\<close>

text \<open>The matrix of a gate list; the first gate acts first.\<close>

primrec circuit_mat :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "circuit_mat K [] = 1\<^sub>m K"
| "circuit_mat K (U # Us) = circuit_mat K Us * U"

lemma circuit_mat_carrier:
  "(\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K) \<Longrightarrow> circuit_mat K Us \<in> carrier_mat K K"
  by (induction Us) auto

lemma circuit_mat_append:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K" and "\<And>U. U \<in> set Vs \<Longrightarrow> U \<in> carrier_mat K K"
  shows "circuit_mat K (Us @ Vs) = circuit_mat K Vs * circuit_mat K Us"
proof -
  have Vc: "circuit_mat K Vs \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use assms(2) in auto)
  show ?thesis using assms(1)
  proof (induction Us)
    case Nil
    show ?case using Vc by simp
  next
    case (Cons U Us)
    have U: "U \<in> carrier_mat K K" and IH: "circuit_mat K (Us @ Vs) = circuit_mat K Vs * circuit_mat K Us" using Cons by auto
    have Uc: "circuit_mat K Us \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use Cons.prems in auto)
    have "circuit_mat K ((U # Us) @ Vs) = circuit_mat K Vs * circuit_mat K Us * U" using IH by simp
    also have "\<dots> = circuit_mat K Vs * (circuit_mat K Us * U)" by (rule assoc_mult_mat[OF Vc Uc U])
    finally show ?case by simp
  qed
qed

lemma circuit_mat_single: "U \<in> carrier_mat K K \<Longrightarrow> circuit_mat K [U] = U"
  by simp

lemma circuit_mat_concat:
  assumes "\<And>Us U. Us \<in> set Bs \<Longrightarrow> U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K"
  shows "circuit_mat K (concat Bs) = circuit_mat K (map (circuit_mat K) Bs)"
  using assms
proof (induction Bs)
  case (Cons Us Bs)
  have "circuit_mat K (concat (Us # Bs)) = circuit_mat K (concat Bs) * circuit_mat K Us"
    unfolding concat.simps by (rule circuit_mat_append) (use Cons.prems in auto)
  moreover have "circuit_mat K (concat Bs) = circuit_mat K (map (circuit_mat K) Bs)"
    by (rule Cons.IH) (use Cons.prems in auto)
  ultimately show ?case by simp
qed simp

lemma circuit_mat_replicate: "G \<in> carrier_mat K K \<Longrightarrow> circuit_mat K (replicate e G) = G ^\<^sub>m e"
  by (induction e) simp_all

lemma circuit_mat_concat_replicate:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K"
  shows "circuit_mat K (concat (replicate r Us)) = circuit_mat K Us ^\<^sub>m r"
proof (induction r)
  case 0
  have "circuit_mat K Us \<in> carrier_mat K K" by (rule circuit_mat_carrier) (rule assms)
  thus ?case by simp
next
  case (Suc r)
  have "circuit_mat K (concat (replicate (Suc r) Us)) = circuit_mat K (concat (replicate r Us)) * circuit_mat K Us"
    by (simp only: replicate_Suc concat.simps, rule circuit_mat_append) (use assms in auto)
  thus ?case using Suc by simp
qed

lemma mult_unit_vec:
  fixes M :: "complex Matrix.mat"
  assumes M: "M \<in> carrier_mat nr nc" and k: "k < nc"
  shows "M *\<^sub>v unit_vec nc k = Matrix.col M k"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (Matrix.col M k)"
  hence i: "i < nr" using M by simp
  have "(M *\<^sub>v unit_vec nc k) $ i = Matrix.row M i \<bullet> unit_vec nc k" using i M by simp
  also have "\<dots> = Matrix.row M i $ k" by (rule scalar_prod_right_unit[OF k])
  finally show "(M *\<^sub>v unit_vec nc k) $ i = Matrix.col M k $ i" using i k M by simp
qed (use M in simp)

lemma mat_eq_unit:
  fixes A B :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat K K" and B: "B \<in> carrier_mat K K"
    and e: "\<And>i. i < K \<Longrightarrow> A *\<^sub>v unit_vec K i = B *\<^sub>v unit_vec K i"
  shows "A = B"
proof (rule Matrix.mat_col_eqI)
  fix i assume "i < dim_col B"
  hence i: "i < K" using B by simp
  show "Matrix.col A i = Matrix.col B i" using e[OF i] mult_unit_vec[OF A i] mult_unit_vec[OF B i] by simp
qed (use A B in auto)

text \<open>The permutation matrix $\ket t\mapsto\ket{f(t)}$.\<close>


definition pmat :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "pmat N f = Matrix.mat N N (\<lambda>(r, t). if r = f t then 1 else 0)"

lemma pmat_carrier [simp]: "pmat N f \<in> carrier_mat N N" by (simp add: pmat_def)

lemma dim_pmat [simp]: "dim_row (pmat N f) = N" "dim_col (pmat N f) = N" by (simp_all add: pmat_def)

lemma pmat_unit:
  assumes t: "t < N" and f: "f t < N"
  shows "pmat N f *\<^sub>v unit_vec N t = unit_vec N (f t)"
  unfolding mult_unit_vec[OF pmat_carrier t] using t f by (intro eq_vecI) (auto simp: pmat_def unit_vec_def)

lemma pmat_mult:
  assumes g: "\<And>t. t < N \<Longrightarrow> g t < N"
  shows "pmat N f * pmat N g = pmat N (f \<circ> g)"
proof (rule eq_matI)
  fix r t assume "r < dim_row (pmat N (f \<circ> g))" "t < dim_col (pmat N (f \<circ> g))"
  hence rt: "r < N" "t < N" by (simp_all add: pmat_def)
  have "(pmat N f * pmat N g) $$ (r, t) = (\<Sum>u<N. (if r = f u then 1 else 0) * (if u = g t then 1 else 0))"
    using rt by (simp add: pmat_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>u<N. if u = g t then (if r = f (g t) then 1 else 0) else 0)"
    by (rule sum.cong) auto
  also have "\<dots> = (if r = f (g t) then 1 else 0)" using g[OF rt(2)] by (simp add: sum.delta)
  finally show "(pmat N f * pmat N g) $$ (r, t) = pmat N (f \<circ> g) $$ (r, t)" using rt by (simp add: pmat_def)
qed (simp_all add: pmat_def)

lemma pmat_id: "pmat N id = 1\<^sub>m N" by (rule eq_matI) (auto simp: pmat_def)

lemma pmat_dagger_invol:
  assumes f: "\<And>t. t < N \<Longrightarrow> f t < N" "\<And>t. t < N \<Longrightarrow> f (f t) = t"
  shows "(pmat N f)\<^sup>\<dagger> = pmat N f"
proof (rule eq_matI)
  fix r t assume "r < dim_row (pmat N f)" "t < dim_col (pmat N f)"
  hence rt: "r < N" "t < N" by simp_all
  have "(t = f r) \<longleftrightarrow> (r = f t)" using f rt by metis
  thus "(pmat N f)\<^sup>\<dagger> $$ (r, t) = pmat N f $$ (r, t)" using rt by (simp add: dagger_def pmat_def)
qed (simp_all add: dagger_def pmat_def)

lemma pmat_unitary_invol:
  assumes f: "\<And>t. t < N \<Longrightarrow> f t < N" "\<And>t. t < N \<Longrightarrow> f (f t) = t"
  shows "unitary (pmat N f)"
proof -
  have "pmat N f * pmat N f = 1\<^sub>m N"
  proof -
    have "pmat N f * pmat N f = pmat N (f \<circ> f)" by (rule pmat_mult[OF f(1)])
    also have "\<dots> = pmat N id" unfolding pmat_def using f(2) by (intro eq_matI) auto
    finally show ?thesis by (simp add: pmat_id)
  qed
  moreover have d: "(pmat N f)\<^sup>\<dagger> = pmat N f" by (rule pmat_dagger_invol) (use f in auto)
  ultimately show ?thesis unfolding unitary_def d by simp
qed

subsection \<open>Circuits with oracle calls\<close>

text \<open>Circuits on $\C^N\otimes\C^m$ built from fixed gates and calls of an oracle $V$ on $\C^m$,
controlled on a predicate of the register value.  \<^term>\<open>Call P d\<close> applies $V$ (or $V^*$ if
\<open>d\<close>) to the blocks $k$ with $P\,k$.\<close>

datatype qcirc = Gate "complex Matrix.mat" | Call "nat \<Rightarrow> bool" bool | QSeq qcirc qcirc

definition call_mat :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> complex Matrix.mat" where
  "call_mat N m V P d = ctrl_blocks N m (\<lambda>k. if P k then (if d then V\<^sup>\<dagger> else V) else 1\<^sub>m m)"

text \<open>\<^term>\<open>QSeq a b\<close> runs \<open>a\<close> first.\<close>

primrec sem :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> qcirc \<Rightarrow> complex Matrix.mat" where
  "sem N m V (Gate M) = M"
| "sem N m V (Call P d) = call_mat N m V P d"
| "sem N m V (QSeq a b) = sem N m V b * sem N m V a"

primrec calls :: "qcirc \<Rightarrow> nat" where
  "calls (Gate M) = 0"
| "calls (Call P d) = 1"
| "calls (QSeq a b) = calls a + calls b"

primrec gates_ok :: "nat \<Rightarrow> qcirc \<Rightarrow> bool" where
  "gates_ok K (Gate M) \<longleftrightarrow> M \<in> carrier_mat K K \<and> unitary M"
| "gates_ok K (Call P d) \<longleftrightarrow> True"
| "gates_ok K (QSeq a b) \<longleftrightarrow> gates_ok K a \<and> gates_ok K b"

primrec adj :: "qcirc \<Rightarrow> qcirc" where
  "adj (Gate M) = Gate (M\<^sup>\<dagger>)"
| "adj (Call P d) = Call P (\<not> d)"
| "adj (QSeq a b) = QSeq (adj b) (adj a)"

lemma calls_adj [simp]: "calls (adj c) = calls c"
  by (induction c) simp_all

lemma gates_ok_adj: "gates_ok K c \<Longrightarrow> gates_ok K (adj c)"
  by (induction c) (simp_all add: dagger_carrier unitary_dagger)

context
  fixes N m :: nat and V :: "complex Matrix.mat"
  assumes V: "V \<in> carrier_mat m m" "unitary V"
begin

lemma call_blocks:
  shows "(if P k then (if d then V\<^sup>\<dagger> else V) else 1\<^sub>m m) \<in> carrier_mat m m"
    and "unitary (if P k then (if d then V\<^sup>\<dagger> else V) else 1\<^sub>m m)"
  using V by (simp_all add: dagger_carrier unitary_dagger id_is_unitary)

lemma sem_carrier: "gates_ok (N * m) c \<Longrightarrow> sem N m V c \<in> carrier_mat (N * m) (N * m)"
  by (induction c) (simp_all add: call_mat_def mult_carrier_mat)

lemma sem_unitary: "gates_ok (N * m) c \<Longrightarrow> unitary (sem N m V c)"
proof (induction c)
  case (Call P d)
  show ?case unfolding sem.simps call_mat_def by (rule ctrl_blocks_unitary) (rule call_blocks)+
next
  case (QSeq a b)
  hence a: "gates_ok (N * m) a" and b: "gates_ok (N * m) b" by simp_all
  show ?case unfolding sem.simps by (rule unitary_mult[OF QSeq.IH(2)[OF b] QSeq.IH(1)[OF a] sem_carrier[OF b] sem_carrier[OF a]])
qed simp

lemma sem_adj: "gates_ok (N * m) c \<Longrightarrow> sem N m V (adj c) = ((sem N m V c)\<^sup>\<dagger>)"
proof (induction c)
  case (Call P d)
  have "((call_mat N m V P d)\<^sup>\<dagger>) = ctrl_blocks N m (\<lambda>k. (if P k then (if d then V\<^sup>\<dagger> else V) else 1\<^sub>m m)\<^sup>\<dagger>)"
    unfolding call_mat_def by (rule ctrl_blocks_dagger) (rule call_blocks)
  also have "\<dots> = call_mat N m V P (\<not> d)"
    unfolding call_mat_def by (rule ctrl_blocks_cong) (simp add: dagger_of_dagger_is_id dagger_of_id_is_id)
  finally show ?case by simp
next
  case (QSeq a b)
  hence a: "gates_ok (N * m) a" and b: "gates_ok (N * m) b" by simp_all
  have "((sem N m V b * sem N m V a)\<^sup>\<dagger>) = ((sem N m V a)\<^sup>\<dagger>) * ((sem N m V b)\<^sup>\<dagger>)"
    using dagger_of_prod[of "sem N m V b" "sem N m V a"] sem_carrier[OF a] sem_carrier[OF b] by simp
  thus ?case using QSeq a b by simp
qed simp

end

subsection \<open>Robustness: each call adds at most $\eta$\<close>

theorem sem_robust:
  assumes V: "V \<in> carrier_mat m m" "unitary V" and V': "V' \<in> carrier_mat m m" "unitary V'"
      and c: "op_close m \<eta> V V'" and e: "0 \<le> \<eta>" and g: "gates_ok (N * m) q"
  shows "op_close (N * m) (real (calls q) * \<eta>) (sem N m V q) (sem N m V' q)"
  using g
proof (induction q)
  case (Gate M)
  thus ?case by (simp add: op_close_refl)
next
  case (Call P d)
  have cd: "op_close m \<eta> (V\<^sup>\<dagger>) (V'\<^sup>\<dagger>)" by (rule op_close_dagger[OF V V' c])
  show ?case unfolding op_close_def sem.simps call_mat_def calls.simps
  proof (intro allI impI)
    fix x :: "complex Matrix.vec" assume x: "dim_vec x = N * m"
    show "\<parallel>ctrl_blocks N m (\<lambda>k. if P k then if d then V\<^sup>\<dagger> else V else 1\<^sub>m m) *\<^sub>v x -
           ctrl_blocks N m (\<lambda>k. if P k then if d then V'\<^sup>\<dagger> else V' else 1\<^sub>m m) *\<^sub>v x\<parallel> \<le> real 1 * \<eta> * \<parallel>x\<parallel>"
    proof -
      have "\<parallel>ctrl_blocks N m (\<lambda>k. if P k then if d then V\<^sup>\<dagger> else V else 1\<^sub>m m) *\<^sub>v x -
             ctrl_blocks N m (\<lambda>k. if P k then if d then V'\<^sup>\<dagger> else V' else 1\<^sub>m m) *\<^sub>v x\<parallel> \<le> \<eta> * \<parallel>x\<parallel>"
      proof (rule ctrl_blocks_close[OF _ _ _ x])
        fix k v assume v: "dim_vec (v :: complex Matrix.vec) = m"
        show "\<parallel>(if P k then if d then V\<^sup>\<dagger> else V else 1\<^sub>m m) *\<^sub>v v - (if P k then if d then V'\<^sup>\<dagger> else V' else 1\<^sub>m m) *\<^sub>v v\<parallel> \<le> \<eta> * \<parallel>v\<parallel>"
          using op_closeD[OF c v] op_closeD[OF cd v] op_closeD[OF op_close_refl[OF e one_carrier_mat] v] by auto
      qed (use V V' in \<open>simp_all add: dagger_carrier\<close>)
      thus ?thesis by simp
    qed
  qed
next
  case (QSeq a b)
  hence a: "gates_ok (N * m) a" and b: "gates_ok (N * m) b" by simp_all
  have ca: "op_close (N * m) (real (calls a) * \<eta>) (sem N m V a) (sem N m V' a)" using QSeq a by simp
  have cb: "op_close (N * m) (real (calls b) * \<eta>) (sem N m V b) (sem N m V' b)" using QSeq b by simp
  have Aa: "sem N m V a \<in> carrier_mat (N * m) (N * m)" and Ab: "sem N m V b \<in> carrier_mat (N * m) (N * m)"
    using sem_carrier[OF V a] sem_carrier[OF V b] by simp_all
  have Ba: "sem N m V' a \<in> carrier_mat (N * m) (N * m)" and Bb: "sem N m V' b \<in> carrier_mat (N * m) (N * m)"
    using sem_carrier[OF V' a] sem_carrier[OF V' b] by simp_all
  have Ub: "unitary (sem N m V b)" and Ua': "unitary (sem N m V' a)"
    using sem_unitary[OF V b] sem_unitary[OF V' a] by simp_all
  show ?case unfolding op_close_def
  proof (intro allI impI)
    fix x :: "complex Matrix.vec" assume x: "dim_vec x = N * m"
    have xc: "x \<in> carrier_vec (N * m)" using x by (rule carrier_vecI)
    let ?y = "sem N m V a *\<^sub>v x" and ?y' = "sem N m V' a *\<^sub>v x"
    have y: "dim_vec ?y = N * m" and y': "dim_vec ?y' = N * m" using Aa Ba by simp_all
    have e1: "sem N m V (QSeq a b) *\<^sub>v x = sem N m V b *\<^sub>v ?y" using assoc_mult_mat_vec[OF Ab Aa xc] by simp
    have e2: "sem N m V' (QSeq a b) *\<^sub>v x = sem N m V' b *\<^sub>v ?y'" using assoc_mult_mat_vec[OF Bb Ba xc] by simp
    have "\<parallel>sem N m V b *\<^sub>v ?y - sem N m V' b *\<^sub>v ?y'\<parallel>
          \<le> \<parallel>sem N m V b *\<^sub>v ?y - sem N m V b *\<^sub>v ?y'\<parallel> + \<parallel>sem N m V b *\<^sub>v ?y' - sem N m V' b *\<^sub>v ?y'\<parallel>"
      by (rule vnorm_diff_le[where n = "N * m"]) (use Ab Bb in simp_all)
    also have "sem N m V b *\<^sub>v ?y - sem N m V b *\<^sub>v ?y' = sem N m V b *\<^sub>v (?y - ?y')"
      by (rule mult_minus_distrib_mat_vec[OF Ab, symmetric]) (use y y' in \<open>simp_all add: carrier_vecI\<close>)
    also have "\<parallel>sem N m V b *\<^sub>v (?y - ?y')\<parallel> = \<parallel>?y - ?y'\<parallel>" by (rule unitary_vnorm[OF Ab Ub]) (use y' in simp)
    also have "\<parallel>?y - ?y'\<parallel> \<le> real (calls a) * \<eta> * \<parallel>x\<parallel>" by (rule op_closeD[OF ca x])
    also have "\<parallel>sem N m V b *\<^sub>v ?y' - sem N m V' b *\<^sub>v ?y'\<parallel> \<le> real (calls b) * \<eta> * \<parallel>?y'\<parallel>" by (rule op_closeD[OF cb y'])
    also have "\<parallel>?y'\<parallel> = \<parallel>x\<parallel>" by (rule unitary_vnorm[OF Ba Ua' x])
    finally show "\<parallel>sem N m V (QSeq a b) *\<^sub>v x - sem N m V' (QSeq a b) *\<^sub>v x\<parallel> \<le> real (calls (QSeq a b)) * \<eta> * \<parallel>x\<parallel>"
      unfolding e1 e2 by (simp add: algebra_simps)
  qed
qed

subsection \<open>Controlled powers with $N-1$ calls\<close>

text \<open>\<^term>\<open>pchain K j\<close> applies the oracle once on each block $k\ge i$, for $i=1,\dots,j$, so
block $k$ receives $O^{\min(k,j)}$.\<close>

primrec pchain :: "nat \<Rightarrow> nat \<Rightarrow> qcirc" where
  "pchain K 0 = Gate (1\<^sub>m K)"
| "pchain K (Suc j) = QSeq (Call (\<lambda>k. Suc j \<le> k) False) (pchain K j)"

lemma calls_pchain [simp]: "calls (pchain K j) = j"
  by (induction j) simp_all

lemma gates_ok_pchain: "gates_ok K (pchain K j)"
  by (induction j) (simp_all add: id_is_unitary)

lemma sem_pchain:
  assumes V: "V \<in> carrier_mat m m"
  shows "sem N m V (pchain (N * m) j) = ctrl_blocks N m (\<lambda>k. V ^\<^sub>m (min k j))"
proof (induction j)
  case 0
  have "ctrl_blocks N m (\<lambda>k. V ^\<^sub>m (min k 0)) = ctrl_blocks N m (\<lambda>_. 1\<^sub>m m)"
    by (rule ctrl_blocks_cong) (use V in simp)
  thus ?case by (simp add: ctrl_blocks_one)
next
  case (Suc j)
  have "sem N m V (pchain (N * m) (Suc j)) =
        ctrl_blocks N m (\<lambda>k. V ^\<^sub>m (min k j)) * ctrl_blocks N m (\<lambda>k. if Suc j \<le> k then V else 1\<^sub>m m)"
    using Suc by (simp add: call_mat_def)
  also have "\<dots> = ctrl_blocks N m (\<lambda>k. V ^\<^sub>m (min k j) * (if Suc j \<le> k then V else 1\<^sub>m m))"
    by (rule ctrl_blocks_mult) (use V in \<open>simp_all add: pow_carrier_mat\<close>)
  also have "\<dots> = ctrl_blocks N m (\<lambda>k. V ^\<^sub>m (min k (Suc j)))"
  proof (rule ctrl_blocks_cong)
    fix k
    show "V ^\<^sub>m (min k j) * (if Suc j \<le> k then V else 1\<^sub>m m) = V ^\<^sub>m (min k (Suc j))"
    proof (cases "Suc j \<le> k")
      case True
      hence "min k j = j" "min k (Suc j) = Suc j" by simp_all
      thus ?thesis using True by simp
    next
      case False
      hence "min k j = k" "min k (Suc j) = k" by simp_all
      thus ?thesis using False right_mult_one_mat[OF pow_carrier_mat[OF V, of k]] by simp
    qed
  qed
  finally show ?case .
qed

lemma sem_pchain_ctrl_pow:
  assumes V: "V \<in> carrier_mat m m"
  shows "sem N m V (pchain (N * m) (N - 1)) = ctrl_pow N m V"
  unfolding sem_pchain[OF V] by (rule ctrl_blocks_cong) simp

subsection \<open>HHL as a circuit with $2(N-1)$ calls\<close>

definition pe_prog :: "nat \<Rightarrow> nat \<Rightarrow> qcirc" where
  "pe_prog N m = QSeq (pchain (N * m) (N - 1)) (Gate ((fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m m))"

definition hhl_prog :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> qcirc" where
  "hhl_prog N m Rg = QSeq (pe_prog N m) (QSeq (Gate Rg) (adj (pe_prog N m)))"

lemma calls_hhl_prog: "calls (hhl_prog N m Rg) = 2 * (N - 1)"
  by (simp add: hhl_prog_def pe_prog_def)

lemma gates_ok_pe_prog:
  assumes N: "0 < N"
  shows "gates_ok (N * m) (pe_prog N m)"
proof -
  have F: "(fourier N)\<^sup>\<dagger> \<in> carrier_mat N N" by (rule dagger_carrier[OF fourier_carrier])
  have "(fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m m \<in> carrier_mat (N * m) (N * m)" using F by (intro carrier_matI) simp_all
  moreover have "unitary ((fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)"
    by (rule tensor_mat_unitary_one_right[OF unitary_dagger[OF fourier_unitary[OF N]]])
  ultimately show ?thesis by (simp add: pe_prog_def gates_ok_pchain)
qed

lemma sem_pe_prog:
  assumes V: "V \<in> carrier_mat m m"
  shows "sem N m V (pe_prog N m) = pe_unitary N m V"
  unfolding pe_prog_def pe_unitary_def sem.simps sem_pchain_ctrl_pow[OF V] ..

lemma sem_hhl_prog:
  assumes V: "V \<in> carrier_mat m m" "unitary V" and N: "0 < N" and Rg: "Rg \<in> carrier_mat (N * m) (N * m)"
  shows "sem N m V (hhl_prog N m Rg) = (pe_unitary N m V)\<^sup>\<dagger> * (Rg * pe_unitary N m V)"
proof -
  have P: "pe_unitary N m V \<in> carrier_mat (N * m) (N * m)" by (rule pe_unitary_carrier)
  have "sem N m V (adj (pe_prog N m)) = (pe_unitary N m V)\<^sup>\<dagger>"
    using sem_adj[OF V gates_ok_pe_prog[OF N]] sem_pe_prog[OF V(1)] by simp
  thus ?thesis unfolding hhl_prog_def sem.simps sem_pe_prog[OF V(1)]
    using assoc_mult_mat[OF dagger_carrier[OF P] Rg P] by simp
qed

text \<open>The rotation stage of the clamped circuit.\<close>

definition hhl_rot_stage :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "hhl_rot_stage A t0 N C = ctrl_blocks N (dim_row A * 2) (\<lambda>k. 1\<^sub>m (dim_row A) \<Otimes> rot (clamp (C / reg_eig t0 N k)))"

lemma hhl_rot_stage_ok: "hhl_rot_stage A t0 N C \<in> carrier_mat (N * (dim_row A * 2)) (N * (dim_row A * 2)) \<and> unitary (hhl_rot_stage A t0 N C)"
proof
  show "hhl_rot_stage A t0 N C \<in> carrier_mat (N * (dim_row A * 2)) (N * (dim_row A * 2))" by (simp add: hhl_rot_stage_def)
  show "unitary (hhl_rot_stage A t0 N C)" unfolding hhl_rot_stage_def
    by (rule ctrl_blocks_unitary) (simp_all add: tensor_mat_unitary_one_left rot_unitary clamp_abs)
qed

text \<open>The circuit with the oracle $V$ in place of $e^{iAt_0}$.\<close>

definition hhl_sim :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "hhl_sim A t0 N C V = sem N (dim_row A * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_prog N (dim_row A * 2) (hhl_rot_stage A t0 N C))"

lemma hhl_sim_exact:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and N: "0 < N"
  shows "hhl_sim A t0 N C (evolution A t0) = hhl_circuit_clamped A t0 N C"
proof -
  have E: "evolution A t0 \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (dim_row A * 2) (dim_row A * 2)"
  proof -
    have "evolution A t0 \<in> carrier_mat (dim_row A) (dim_row A)" using A mat_fun_carrier[of A n] by (simp add: evolution_def)
    thus ?thesis by (intro carrier_matI) simp_all
  qed
  have EU: "unitary (evolution A t0 \<Otimes> 1\<^sub>m 2)" by (rule tensor_mat_unitary_one_right[OF evolution_unitary[OF A]])
  show ?thesis unfolding hhl_sim_def flag_circuit_def hhl_Wd_def
    using sem_hhl_prog[OF E EU N conjunct1[OF hhl_rot_stage_ok]] by (simp add: hhl_rot_stage_def)
qed

theorem hhl_sim_robust:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and N: "0 < N"
      and V: "V \<in> carrier_mat n n" "unitary V" and c: "op_close n \<eta> V (evolution A t0)" and e: "0 \<le> \<eta>"
  shows "op_close (N * (n * 2)) (2 * real (N - 1) * \<eta>) (hhl_sim A t0 N C V) (hhl_circuit_clamped A t0 N C)"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have E: "evolution A t0 \<in> carrier_mat n n" using A mat_fun_carrier[of A n] by (simp add: evolution_def)
  have EU: "unitary (evolution A t0)" by (rule evolution_unitary[OF A])
  have T: "M \<in> carrier_mat n n \<Longrightarrow> M \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)" for M by (intro carrier_matI) simp_all
  have g: "gates_ok (N * (n * 2)) (hhl_prog N (n * 2) (hhl_rot_stage A t0 N C))"
    using gates_ok_pe_prog[OF N, of "n * 2"] gates_ok_adj[OF gates_ok_pe_prog[OF N, of "n * 2"]] hhl_rot_stage_ok[of A t0 N C]
    unfolding hhl_prog_def nA by simp
  have "op_close (N * (n * 2)) (real (calls (hhl_prog N (n * 2) (hhl_rot_stage A t0 N C))) * \<eta>)
          (sem N (n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_prog N (n * 2) (hhl_rot_stage A t0 N C)))
          (sem N (n * 2) (evolution A t0 \<Otimes> 1\<^sub>m 2) (hhl_prog N (n * 2) (hhl_rot_stage A t0 N C)))"
    by (rule sem_robust[OF T[OF V(1)] tensor_mat_unitary_one_right[OF V(2)] T[OF E] tensor_mat_unitary_one_right[OF EU]
          op_close_tensor_one2[OF V(1) E c e] e g])
  moreover have "sem N (n * 2) (evolution A t0 \<Otimes> 1\<^sub>m 2) (hhl_prog N (n * 2) (hhl_rot_stage A t0 N C)) = hhl_circuit_clamped A t0 N C"
    using hhl_sim_exact[OF A N, of t0 C] unfolding hhl_sim_def nA .
  ultimately show ?thesis unfolding hhl_sim_def nA calls_hhl_prog by simp
qed

subsection \<open>The window is a unit vector\<close>

lemma roots_of_unity_sum:
  assumes N: "2 \<le> N"
  shows "(\<Sum>\<tau><N. cis (2 * pi * real \<tau> / real N)) = 0"
proof -
  have N0: "0 < real N" using N by simp
  let ?z = "cis (2 * pi / real N)"
  have z1: "?z \<noteq> 1"
  proof (rule cis_ne_one_of_sin)
    have "0 < pi / real N" using N0 by simp
    moreover have "pi / real N < pi" using N by (simp add: field_simps)
    ultimately have "0 < sin (pi / real N)" by (rule sin_gt_zero)
    thus "sin (2 * pi / real N / 2) \<noteq> 0" by simp
  qed
  have zN: "?z ^ N = 1" unfolding DeMoivre using N0 by simp
  have "(\<Sum>\<tau><N. cis (2 * pi * real \<tau> / real N)) = (\<Sum>\<tau><N. ?z ^ \<tau>)"
    by (rule sum.cong) (simp_all add: DeMoivre field_simps)
  also have "\<dots> = 0" unfolding geometric_sum[OF z1] zN by simp
  finally show ?thesis .
qed

lemma win_state_norm:
  assumes N: "2 \<le> N"
  shows "\<parallel>win_state N\<parallel> = 1"
proof -
  have N0: "0 < real N" using N by simp
  let ?y = "\<lambda>\<tau>::nat. pi * (real \<tau> + 1 / 2) / real N"
  have c0: "(\<Sum>\<tau><N. cos (2 * ?y \<tau>)) = 0"
  proof -
    have e: "cis (2 * ?y \<tau>) = cis (pi / real N) * cis (2 * pi * real \<tau> / real N)" for \<tau>
      unfolding cis_mult by (rule arg_cong[where f = cis]) (use N0 in \<open>simp add: field_simps\<close>)
    have "(\<Sum>\<tau><N. cis (2 * ?y \<tau>)) = cis (pi / real N) * (\<Sum>\<tau><N. cis (2 * pi * real \<tau> / real N))"
      unfolding e sum_distrib_left ..
    hence "(\<Sum>\<tau><N. cis (2 * ?y \<tau>)) = 0" unfolding roots_of_unity_sum[OF N] by simp
    hence "Re (\<Sum>\<tau><N. cis (2 * ?y \<tau>)) = 0" by simp
    thus ?thesis by (simp add: Re_sum)
  qed
  have s: "(\<Sum>\<tau><N. (sin (?y \<tau>))\<^sup>2) = real N / 2"
  proof -
    have "(\<Sum>\<tau><N. (sin (?y \<tau>))\<^sup>2) = (\<Sum>\<tau><N. (1 - cos (2 * ?y \<tau>)) / 2)"
      unfolding cos_double_sin by simp
    also have "\<dots> = (real N - (\<Sum>\<tau><N. cos (2 * ?y \<tau>))) / 2"
      by (simp add: sum_divide_distrib[symmetric] sum_subtractf)
    finally show ?thesis unfolding c0 by simp
  qed
  have "\<parallel>win_state N\<parallel>\<^sup>2 = 2 / real N * (\<Sum>\<tau><N. (sin (?y \<tau>))\<^sup>2)"
    unfolding vnorm_sq sum_distrib_left using N0
    by (intro sum.cong) (simp_all add: win_state_def win_coef_def norm_mult power_mult_distrib)
  also have "\<dots> = 1" unfolding s using N0 by simp
  finally have "\<parallel>win_state N\<parallel>\<^sup>2 = 1" .
  hence "\<parallel>win_state N\<parallel>\<^sup>2 = 1\<^sup>2" by simp
  thus ?thesis using power2_eq_iff_nonneg[OF vnorm_ge0 zero_le_one] by simp
qed

lemma vnorm_tensor:
  assumes "dim_vec a = n" "dim_vec b = m"
  shows "\<parallel>tensor_vec a b\<parallel> = \<parallel>a\<parallel> * \<parallel>b\<parallel>"
proof -
  have "\<langle>tensor_vec a b|tensor_vec a b\<rangle> = \<langle>a|a\<rangle> * \<langle>b|b\<rangle>"
    by (rule tensor_inner_prod[OF assms(1) assms(1) assms(2) assms(2)])
  hence "complex_of_real (\<parallel>tensor_vec a b\<parallel>\<^sup>2) = complex_of_real (\<parallel>a\<parallel>\<^sup>2 * \<parallel>b\<parallel>\<^sup>2)"
    unfolding cpx_vec_length_inner_prod[symmetric] of_real_mult .
  hence "\<parallel>tensor_vec a b\<parallel>\<^sup>2 = (\<parallel>a\<parallel> * \<parallel>b\<parallel>)\<^sup>2" unfolding of_real_eq_iff power_mult_distrib .
  thus ?thesis using power2_eq_iff_nonneg[OF vnorm_ge0 mult_nonneg_nonneg[OF vnorm_ge0 vnorm_ge0]] by simp
qed

subsection \<open>End to end\<close>

text \<open>End to end: window register, clamped rotations and an oracle $V$ that is $\eta$-close to
$e^{iAt_0}$.  The output is within $(\varepsilon+2(N-1)\eta)\norm b$ of the exact-HHL output.\<close>

theorem hhl_sim_window_error:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real N"
      and V: "V \<in> carrier_mat n n" "unitary V" and Vc: "op_close n \<eta> V (evolution A t0)" and eta: "0 \<le> \<eta>"
  shows "\<parallel>hhl_sim A t0 N C V *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
           tensor_vec (win_state N)
             (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
              tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))\<parallel>
         \<le> (\<epsilon> + 2 * real (N - 1) * \<eta>) * \<parallel>b\<parallel>"
proof -
  let ?x = "tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0))"
  let ?I = "tensor_vec (win_state N)
             (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
              tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))"
  let ?H = "hhl_circuit_clamped A t0 N C" and ?S = "hhl_sim A t0 N C V"
  have N0: "0 < N" using N by simp
  have nA: "dim_row A = n" using A(1) by simp
  have G0: "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A \<in> carrier_mat n n" using A by simp
  have G1: "complex_of_real C \<cdot>\<^sub>m herm_inv A \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
  have bx: "dim_vec (tensor_vec b (unit_vec 2 0)) = n * 2" using tensor_vec_dim[OF b, of "unit_vec 2 0" 2] by simp
  have dx: "dim_vec ?x = N * (n * 2)" using tensor_vec_dim[OF dim_win_state bx] .
  have nx: "\<parallel>?x\<parallel> = \<parallel>b\<parallel>"
    unfolding vnorm_tensor[OF dim_win_state bx] vnorm_tensor[OF b, of "unit_vec 2 0" 2, simplified] win_state_norm[OF N]
    by simp
  have Hc: "?H \<in> carrier_mat (N * (n * 2)) (N * (n * 2))"
    unfolding flag_circuit_def hhl_Wd_def nA
    by (rule mult_carrier_mat[OF dagger_carrier[OF pe_unitary_carrier] mult_carrier_mat[OF ctrl_blocks_carrier pe_unitary_carrier]])
  have Sc: "?S \<in> carrier_mat (N * (n * 2)) (N * (n * 2))"
  proof -
    have T: "V \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)" using V by (intro carrier_matI) simp_all
    have g: "gates_ok (N * (n * 2)) (hhl_prog N (n * 2) (hhl_rot_stage A t0 N C))"
      using gates_ok_pe_prog[OF N0, of "n * 2"] gates_ok_adj[OF gates_ok_pe_prog[OF N0, of "n * 2"]] hhl_rot_stage_ok[of A t0 N C]
      unfolding hhl_prog_def nA by simp
    show ?thesis unfolding hhl_sim_def nA by (rule sem_carrier[OF T tensor_mat_unitary_one_right[OF V(2)] g])
  qed
  have dI: "dim_vec ?I = N * (n * 2)"
  proof -
    have "dim_vec (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
              tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1)) = n * 2"
    proof -
      have v0: "dim_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) = n" using G0 by simp
      have v1: "dim_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) = n" using carrier_matD(1)[OF G1] by (simp only: dim_mult_mat_vec)
      show ?thesis using tensor_vec_dim[OF v0, of "unit_vec 2 0" 2] tensor_vec_dim[OF v1, of "unit_vec 2 1" 2] by simp
    qed
    thus ?thesis using tensor_vec_dim[OF dim_win_state] by simp
  qed
  have d1: "\<parallel>?S *\<^sub>v ?x - ?H *\<^sub>v ?x\<parallel> \<le> 2 * real (N - 1) * \<eta> * \<parallel>b\<parallel>"
    using op_closeD[OF hhl_sim_robust[OF A N0 V Vc eta, where C = C] dx] unfolding nx .
  have d2: "\<parallel>?H *\<^sub>v ?x - ?I\<parallel> \<le> \<epsilon> * \<parallel>b\<parallel>"
  proof -
    have "Re \<langle>?H *\<^sub>v ?x - ?I|?H *\<^sub>v ?x - ?I\<rangle> \<le> \<epsilon>\<^sup>2 * Re \<langle>b|b\<rangle>"
      by (rule hhl_window_precision[OF A t0 N C th lmin spec b e NQ])
    hence "\<parallel>?H *\<^sub>v ?x - ?I\<parallel>\<^sup>2 \<le> (\<epsilon> * \<parallel>b\<parallel>)\<^sup>2" unfolding vnorm_Re_inner power_mult_distrib .
    thus ?thesis by (rule power2_le_imp_le) (use e vnorm_ge0[of b] in simp)
  qed
  have "\<parallel>?S *\<^sub>v ?x - ?I\<parallel> \<le> \<parallel>?S *\<^sub>v ?x - ?H *\<^sub>v ?x\<parallel> + \<parallel>?H *\<^sub>v ?x - ?I\<parallel>"
    by (rule vnorm_diff_le[where n = "N * (n * 2)"]) (use Sc Hc dI in simp_all)
  also have "\<dots> \<le> 2 * real (N - 1) * \<eta> * \<parallel>b\<parallel> + \<epsilon> * \<parallel>b\<parallel>" using d1 d2 by linarith
  finally show ?thesis by (simp add: algebra_simps)
qed

end
