theory Day04_29_Supplement
  imports Day27_Entangled_Examples Day29_Classical_Codes
begin

section \<open>Days 4--29: the converse Hermitian tests, composite ensembles, Choi's four conditions, codes\<close>

text \<open>Completions of variant rows of the audit: on Day 4 the directions (b)$\Rightarrow$(a) and
(c)$\Rightarrow$(a) of the characterisation of Hermitian matrices (D4-1); on Day 14 the density of
a composite ensemble (D14-5); on Day 19 Choi's theorem with the $n$-positivity condition (2)
stated in its own right (D19-1); on Day 29 the triangle inequality, the distance of a subspace
code and unique decoding (D29-4).\<close>

subsection \<open>Day 4: the converse directions for Hermitian matrices (D4-1)\<close>

lemma unitary_real_diag_imp_hermitian:
  assumes U: "U \<in> carrier_mat n n" and u: "unitary U" and H: "H \<in> carrier_mat n n"
      and D: "length D = n" and spec: "U\<^sup>\<dagger> * H * U = diag_mat_of_real D"
  shows "hermitian H"
proof -
  have He: "H = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF U H u spec])
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using D by (intro carrier_matI) simp_all
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have "(U * diag_mat_of_real D * (U\<^sup>\<dagger>))\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * diag_mat_of_real D)\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use U Dc Ud in auto)
  also have "(U * diag_mat_of_real D)\<^sup>\<dagger> = ((diag_mat_of_real D)\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use U Dc in auto)
  also have "(diag_mat_of_real D)\<^sup>\<dagger> = diag_mat_of_real D"
    by (rule Quantum_Computing11.diag_mat_of_real_hermitian)
  also have "(U\<^sup>\<dagger>)\<^sup>\<dagger> = U" by (rule dagger_of_dagger_is_id)
  finally have "(U * diag_mat_of_real D * (U\<^sup>\<dagger>))\<^sup>\<dagger> = U * (diag_mat_of_real D * (U\<^sup>\<dagger>))" .
  also have "\<dots> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" using U Dc Ud by (simp add: assoc_mult_mat)
  finally show ?thesis unfolding hermitian_def using He by simp
qed

lemma eigenbasis_real_imp_hermitian:
  assumes H: "H \<in> carrier_mat n n" and orth: "orthonormal_list n vs" and len: "length vs = n"
      and eig: "\<And>i. i < n \<Longrightarrow> H *\<^sub>v vs ! i = complex_of_real (lam ! i) \<cdot>\<^sub>v vs ! i" and lam: "length lam = n"
  shows "hermitian H"
proof -
  let ?U = "mat_of_cols n vs"
  have U: "?U \<in> carrier_mat n n" using mat_of_cols_carrier(1)[of n vs] len by simp
  have u: "unitary ?U" by (rule orthonormal_mat_unitary[OF orth len])
  have vd: "\<And>i. i < n \<Longrightarrow> dim_vec (vs ! i) = n" using orth len unfolding orthonormal_list_def by auto
  have HU: "H * ?U = ?U * diag_mat_of_real lam"
  proof (rule eq_matI)
    fix r c assume "r < dim_row (?U * diag_mat_of_real lam)" "c < dim_col (?U * diag_mat_of_real lam)"
    hence r: "r < n" and c: "c < n" using len lam by simp_all
    have "(H * ?U) $$ (r, c) = (H *\<^sub>v vs ! c) $ r"
      using carrier_matD[OF H] len r c vd[OF c] by (simp add: mat_of_cols_def Matrix.col_def Matrix.row_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = complex_of_real (lam ! c) * vs ! c $ r" using eig[OF c] vd[OF c] r by simp
    also have "\<dots> = (?U * diag_mat_of_real lam) $$ (r, c)"
    proof -
      have "(?U * diag_mat_of_real lam) $$ (r, c) = (\<Sum>k<n. ?U $$ (r, k) * diag_mat_of_real lam $$ (k, c))"
        using carrier_matD[OF U] r c lam by (auto simp: scalar_prod_def atLeast0LessThan intro!: sum.cong)
      also have "\<dots> = (\<Sum>k<n. if k = c then vs ! c $ r * complex_of_real (lam ! c) else 0)"
        by (rule sum.cong) (use r c lam len in \<open>auto simp: diag_mat_of_real_def mat_diag_def mat_of_cols_def\<close>)
      also have "\<dots> = vs ! c $ r * complex_of_real (lam ! c)" using c by simp
      finally show ?thesis by (simp add: mult.commute)
    qed
    finally show "(H * ?U) $$ (r, c) = (?U * diag_mat_of_real lam) $$ (r, c)" .
  qed (use carrier_matD[OF H] len lam in simp_all)
  have Ud: "?U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have UdU: "?U\<^sup>\<dagger> * ?U = 1\<^sub>m n" using u U len unfolding unitary_def by (simp add: inverts_mat_def)
  have "?U\<^sup>\<dagger> * H * ?U = ?U\<^sup>\<dagger> * (H * ?U)" using Ud H U by (simp add: assoc_mult_mat)
  also have "\<dots> = ?U\<^sup>\<dagger> * ?U * diag_mat_of_real lam"
  proof -
    have Dc: "diag_mat_of_real lam \<in> carrier_mat n n" using lam by (intro carrier_matI) simp_all
    show ?thesis unfolding HU by (rule assoc_mult_mat[OF Ud U Dc, symmetric])
  qed
  also have "\<dots> = diag_mat_of_real lam" unfolding UdU using lam by simp
  finally show ?thesis by (rule unitary_real_diag_imp_hermitian[OF U u H lam])
qed

subsection \<open>Choi's theorem with (2) isolated (D19-1)\<close>

lemma choi_seed_psd: "psd (choi_seed n)"
  unfolding choi_seed_unit_blocks by (rule unit_blocks_psd)

lemma choi_psd_if_n_positive:
  assumes n: "0 < n" and d: "0 < d" and pp: "p_positive n d n \<Phi>"
  shows "psd (choi_matrix n d \<Phi>)"
proof -
  have "choi_seed n \<in> carrier_mat (n * n) (n * n)" by (rule choi_seed_carrier)
  hence "psd (amplification n d n \<Phi> (choi_seed n))" using pp choi_seed_psd by (simp add: p_positive_def)
  thus ?thesis by (simp add: choi_matrix_as_amplification[OF n d])
qed

theorem choi_four_conditions:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult: "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and n: "0 < n" and d: "0 < d"
  shows "(completely_positive n d \<Phi> \<longleftrightarrow> p_positive n d n \<Phi>)
       \<and> (p_positive n d n \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>))
       \<and> (psd (choi_matrix n d \<Phi>) \<longleftrightarrow>
           (\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)))"
proof -
  have cp_choi: "completely_positive n d \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>)"
    by (rule choi_theorem[OF linear smult range n d])
  have np: "p_positive n d n \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>)"
  proof
    assume "p_positive n d n \<Phi>" thus "psd (choi_matrix n d \<Phi>)" by (rule choi_psd_if_n_positive[OF n d])
  next
    assume "psd (choi_matrix n d \<Phi>)"
    hence "completely_positive n d \<Phi>" using cp_choi by simp
    thus "p_positive n d n \<Phi>" using n by (simp add: completely_positive_def)
  qed
  have kraus: "psd (choi_matrix n d \<Phi>) \<longleftrightarrow>
           (\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A))"
  proof
    assume "psd (choi_matrix n d \<Phi>)"
    thus "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
      using kraus_rep_of_psd_choi[OF linear smult range n d] by blast
  next
    assume "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
    then obtain Ws where Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Wk: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A" by blast
    have "completely_positive n d (kraus_map_dim d Ws)" by (rule kraus_cp_no_tp[OF Wc n d])
    hence "completely_positive n d \<Phi>" using completely_positive_cong[of n \<Phi> "kraus_map_dim d Ws" d] Wk by blast
    thus "psd (choi_matrix n d \<Phi>)" using cp_choi by simp
  qed
  have "completely_positive n d \<Phi> \<longleftrightarrow> p_positive n d n \<Phi>" using cp_choi np by simp
  thus ?thesis using np kraus by blast
qed

subsection \<open>Composite ensembles (D14-5)\<close>

text \<open>$|\psi\otimes\varphi\rangle\langle\psi\otimes\varphi|=|\psi\rangle\langle\psi|\otimes|\varphi\rangle\langle\varphi|$.\<close>

lemma outer_sum_tensor:
  assumes \<psi>: "dim_vec \<psi> = n" and \<phi>: "dim_vec \<phi> = m"
  shows "outer_sum (n * m) [tensor_vec \<psi> \<phi>] = outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]"
proof (rule eq_matI)
  have A: "outer_sum n [\<psi>] \<in> carrier_mat n n" and B: "outer_sum m [\<phi>] \<in> carrier_mat m m"
    by (rule outer_sum_carrier)+
  fix r s assume "r < dim_row (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>])" "s < dim_col (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>])"
  hence r: "r < n * m" and s: "s < n * m" using carrier_matD[OF A] carrier_matD[OF B] by simp_all
  have m: "0 < m" using r by (cases m) auto
  have rd: "r div m < n" "s div m < n" using r s by (simp_all add: less_mult_imp_div_less)
  have rm: "r mod m < m" "s mod m < m" using m by simp_all
  have "outer_sum (n * m) [tensor_vec \<psi> \<phi>] $$ (r, s) = tensor_vec \<psi> \<phi> $ r * cnj (tensor_vec \<psi> \<phi> $ s)"
    by (rule outer_sum_singleton_index[OF r s])
  also have "\<dots> = (\<psi> $ (r div m) * \<phi> $ (r mod m)) * cnj (\<psi> $ (s div m) * \<phi> $ (s mod m))"
    using tensor_vec_index[OF \<psi> \<phi> r] tensor_vec_index[OF \<psi> \<phi> s] by simp
  also have "\<dots> = outer_sum n [\<psi>] $$ (r div m, s div m) * outer_sum m [\<phi>] $$ (r mod m, s mod m)"
    using outer_sum_singleton_index[OF rd] outer_sum_singleton_index[OF rm] by (simp add: algebra_simps)
  also have "\<dots> = (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]) $$ (r, s)"
  proof -
    have n: "0 < n" using r by (cases n) auto
    show ?thesis
      by (rule index_tensor_mat[of _ n n _ m m, symmetric]) (use carrier_matD[OF A] carrier_matD[OF B] r s m n in simp_all)
  qed
  finally show "outer_sum (n * m) [tensor_vec \<psi> \<phi>] $$ (r, s) = (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]) $$ (r, s)" .
qed (simp_all add: outer_sum_def)

text \<open>For ensembles $\{p_i,\psi_i\}$ on $\Hil_A$ and $\{q_j,\varphi_j\}$ on $\Hil_B$, the composite ensemble
is $\{p_iq_j,\psi_i\otimes\varphi_j\}$.\<close>

definition product_ensemble :: "(real \<times> complex Matrix.vec) list \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> (real \<times> complex Matrix.vec) list" where
  "product_ensemble EA EB = map (\<lambda>((p, \<psi>), (q, \<phi>)). (p * q, tensor_vec \<psi> \<phi>)) (List.product EA EB)"

lemma sum_list_product:
  fixes f :: "'a \<Rightarrow> real" and g :: "'b \<Rightarrow> real"
  shows "(\<Sum>(x, y) \<leftarrow> List.product xs ys. f x * g y) = (\<Sum>x \<leftarrow> xs. f x) * (\<Sum>y \<leftarrow> ys. g y)"
  by (induction xs) (simp_all add: sum_list_const_mult algebra_simps comp_def)

lemma product_ensemble_ensemble:
  assumes A: "ensemble n EA" and B: "ensemble m EB"
  shows "ensemble (n * m) (product_ensemble EA EB)"
proof -
  have As: "\<forall>(p, \<psi>) \<in> set EA. p \<ge> 0 \<and> quantum_state n \<psi>" and Asum: "(\<Sum>(p, _) \<leftarrow> EA. p) = 1"
    using A unfolding ensemble_def by blast+
  have Bs: "\<forall>(q, \<phi>) \<in> set EB. q \<ge> 0 \<and> quantum_state m \<phi>" and Bsum: "(\<Sum>(q, _) \<leftarrow> EB. q) = 1"
    using B unfolding ensemble_def by blast+
  have mem: "\<forall>(r, u) \<in> set (product_ensemble EA EB). r \<ge> 0 \<and> quantum_state (n * m) u"
  proof -
    have As': "\<And>p \<psi>. (p, \<psi>) \<in> set EA \<Longrightarrow> p \<ge> 0 \<and> quantum_state n \<psi>" using As by blast
    have Bs': "\<And>q \<phi>. (q, \<phi>) \<in> set EB \<Longrightarrow> q \<ge> 0 \<and> quantum_state m \<phi>" using Bs by blast
    show ?thesis by (auto simp: product_ensemble_def dest!: As' Bs' intro: tensor_of_states_is_state)
  qed
  have "(\<Sum>(r, _) \<leftarrow> product_ensemble EA EB. r) = (\<Sum>(x, y) \<leftarrow> List.product EA EB. fst x * fst y)"
    by (simp add: product_ensemble_def comp_def split_def)
  also have "\<dots> = (\<Sum>x \<leftarrow> EA. fst x) * (\<Sum>y \<leftarrow> EB. fst y)" by (rule sum_list_product)
  also have "\<dots> = 1" using Asum Bsum by (simp add: split_def)
  finally show ?thesis unfolding ensemble_def using mem by blast
qed

text \<open>The notes' composite density $\sum_{i,j}p_iq_j\,|\psi_i\rangle\langle\psi_i|\otimes|\varphi_j\rangle\langle\varphi_j|$
is the density of the composite ensemble, hence a density matrix.\<close>

definition composite_density :: "nat \<Rightarrow> nat \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> complex Matrix.mat" where
  "composite_density n m EA EB = foldr (\<lambda>((p, \<psi>), (q, \<phi>)) acc.
      complex_of_real (p * q) \<cdot>\<^sub>m (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]) + acc) (List.product EA EB) (0\<^sub>m (n * m) (n * m))"

lemma composite_density_eq:
  assumes A: "ensemble n EA" and B: "ensemble m EB"
  shows "composite_density n m EA EB = ensemble_density (n * m) (product_ensemble EA EB)"
proof -
  have dims: "\<forall>((p, \<psi>), (q, \<phi>)) \<in> set (List.product EA EB). dim_vec \<psi> = n \<and> dim_vec \<phi> = m"
    using A B unfolding ensemble_def quantum_state_def by auto
  have "\<And>L. \<forall>((p, \<psi>), (q, \<phi>)) \<in> set L. dim_vec \<psi> = n \<and> dim_vec \<phi> = m \<Longrightarrow>
        foldr (\<lambda>((p, \<psi>), (q, \<phi>)) acc. complex_of_real (p * q) \<cdot>\<^sub>m (outer_sum n [\<psi>] \<Otimes> outer_sum m [\<phi>]) + acc) L (0\<^sub>m (n * m) (n * m))
        = ensemble_density (n * m) (map (\<lambda>((p, \<psi>), (q, \<phi>)). (p * q, tensor_vec \<psi> \<phi>)) L)"
  proof -
    fix L :: "((real \<times> complex Matrix.vec) \<times> (real \<times> complex Matrix.vec)) list"
    show "\<forall>((p, \<psi>), (q, \<phi>)) \<in> set L. dim_vec \<psi> = n \<and> dim_vec \<phi> = m \<Longrightarrow> ?thesis L" for dummy :: unit
      by (induction L) (auto simp: ensemble_density_def outer_sum_tensor)
  qed
  thus ?thesis using dims unfolding composite_density_def product_ensemble_def by blast
qed

theorem composite_density_is_dm:
  assumes A: "ensemble n EA" and B: "ensemble m EB"
  shows "density_matrix (n * m) (composite_density n m EA EB)"
  unfolding composite_density_eq[OF A B] by (rule ensemble_density_is_dm[OF product_ensemble_ensemble[OF A B]])

subsection \<open>Hamming distance and subspace codes (D29-4)\<close>

lemma hamming_dist_xor: "hamming_dist v w = hamming_weight (xor_word v w)"
  by (simp add: hamming_dist_def xor_word_def)

text \<open>The triangle inequality for words of bits of equal length.\<close>

lemma hamming_dist_triangle:
  assumes "length u = length v" "length v = length w"
      and "\<forall>x \<in> set u. x < 2" "\<forall>x \<in> set v. x < 2" "\<forall>x \<in> set w. x < 2"
  shows "hamming_dist u w \<le> hamming_dist u v + hamming_dist v w"
  using assms
proof (induction u arbitrary: v w)
  case Nil thus ?case by simp
next
  case (Cons a u)
  then obtain b v' c w' where v: "v = b # v'" and w: "w = c # w'"
    by (cases v; cases w) auto
  have IH: "hamming_dist u w' \<le> hamming_dist u v' + hamming_dist v' w'"
    using Cons.IH[of v' w'] Cons.prems v w by simp
  have abc: "a < 2" "b < 2" "c < 2" using Cons.prems v w by auto
  show ?case unfolding v w hamming_dist_Cons using IH abc
    by (auto simp: less_2_cases_iff)
qed

text \<open>For a subspace code (closed under addition mod 2) the distance is the least weight of a
nonzero code word.\<close>

definition zero_word :: "nat \<Rightarrow> nat list" where
  "zero_word m = replicate m 0"

lemma xor_word_self: "xor_word v v = zero_word (length v)"
  by (induction v) (simp_all add: xor_word_def zero_word_def)

lemma xor_word_zero: "\<forall>x \<in> set v. x < 2 \<Longrightarrow> xor_word v (zero_word (length v)) = v"
  by (induction v) (auto simp: xor_word_def zero_word_def)

lemma xor_word_eq_zero_iff:
  assumes "length v = length w" "\<forall>x \<in> set v. x < 2" "\<forall>x \<in> set w. x < 2"
  shows "xor_word v w = zero_word (length v) \<longleftrightarrow> v = w"
  using assms
proof (induction v arbitrary: w)
  case Nil thus ?case by (simp add: xor_word_def zero_word_def)
next
  case (Cons a v)
  then obtain b w' where w: "w = b # w'" by (cases w) auto
  have ab: "a < 2" "b < 2" using Cons.prems w by auto
  have IH: "xor_word v w' = zero_word (length v) \<longleftrightarrow> v = w'" using Cons.IH[of w'] Cons.prems w by simp
  show ?case using IH ab unfolding w by (auto simp: xor_word_def zero_word_def less_2_cases_iff)
qed

lemma hamming_weight_zero_word [simp]: "hamming_weight (zero_word m) = 0"
  by (simp add: hamming_weight_def zero_word_def)

lemma hamming_weight_eq_zero_iff: "\<forall>x \<in> set v. x < 2 \<Longrightarrow> hamming_weight v = 0 \<longleftrightarrow> v = zero_word (length v)"
  by (induction v) (auto simp: hamming_weight_def zero_word_def)

definition subspace_code :: "nat \<Rightarrow> nat list set \<Rightarrow> bool" where
  "subspace_code m S \<longleftrightarrow> (\<forall>v \<in> S. length v = m \<and> (\<forall>x \<in> set v. x < 2))
                         \<and> (\<forall>v \<in> S. \<forall>w \<in> S. xor_word v w \<in> S)"

lemma xor_word_bits: "\<forall>x \<in> set (xor_word v w). x < 2"
  by (auto simp: xor_word_def set_zip)

theorem subspace_code_distance:
  assumes S: "subspace_code m S" and fin: "finite S" and two: "\<exists>v \<in> S. \<exists>w \<in> S. v \<noteq> w"
  shows "code_distance S = Min {hamming_weight v | v. v \<in> S \<and> v \<noteq> zero_word m}"
proof -
  have len: "\<And>v. v \<in> S \<Longrightarrow> length v = m" and bits: "\<And>v. v \<in> S \<Longrightarrow> \<forall>x \<in> set v. x < 2"
    and cl: "\<And>v w. v \<in> S \<Longrightarrow> w \<in> S \<Longrightarrow> xor_word v w \<in> S" using S unfolding subspace_code_def by blast+
  obtain v0 where v0: "v0 \<in> S" using two by blast
  have z: "zero_word m \<in> S" using cl[OF v0 v0] xor_word_self[of v0] len[OF v0] by simp
  have "{hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w} = {hamming_weight v | v. v \<in> S \<and> v \<noteq> zero_word m}"
  proof (intro equalityI subsetI)
    fix d assume "d \<in> {hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w}"
    then obtain v w where vw: "v \<in> S" "w \<in> S" "v \<noteq> w" and d: "d = hamming_dist v w" by blast
    have "xor_word v w \<noteq> zero_word m"
      using xor_word_eq_zero_iff[of v w] len[OF vw(1)] len[OF vw(2)] bits[OF vw(1)] bits[OF vw(2)] vw(3) by simp
    thus "d \<in> {hamming_weight v | v. v \<in> S \<and> v \<noteq> zero_word m}"
      using cl[OF vw(1,2)] unfolding d hamming_dist_xor by blast
  next
    fix d assume "d \<in> {hamming_weight v | v. v \<in> S \<and> v \<noteq> zero_word m}"
    then obtain v where v: "v \<in> S" "v \<noteq> zero_word m" and d: "d = hamming_weight v" by blast
    have "hamming_dist v (zero_word m) = hamming_weight v"
      unfolding hamming_dist_xor using xor_word_zero[OF bits[OF v(1)]] len[OF v(1)] by simp
    thus "d \<in> {hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w}" using v z d by force
  qed
  thus ?thesis using two unfolding code_distance_def by simp
qed

text \<open>A code of distance at least $2t+1$ corrects $t$ errors: a received word is within distance
$t$ of at most one code word.\<close>

theorem corrects_errors_unique_decoding:
  assumes ce: "corrects_errors S t" and fin: "finite S"
      and S: "\<forall>v \<in> S. length v = m \<and> (\<forall>x \<in> set v. x < 2)"
      and r: "length r = m" "\<forall>x \<in> set r. x < 2"
      and c: "c \<in> S" "hamming_dist r c \<le> t" and c': "c' \<in> S" "hamming_dist r c' \<le> t"
  shows "c = c'"
proof (rule ccontr)
  assume ne: "c \<noteq> c'"
  have lc: "length c = m" "length c' = m" and bc: "\<forall>x \<in> set c. x < 2" "\<forall>x \<in> set c'. x < 2"
    using S c(1) c'(1) by auto
  have "hamming_dist c c' \<le> hamming_dist c r + hamming_dist r c'"
    by (rule hamming_dist_triangle) (use lc r bc in auto)
  also have "hamming_dist c r = hamming_dist r c" by (rule hamming_dist_symm) (use lc r in simp)
  finally have le: "hamming_dist c c' \<le> 2 * t" using c(2) c'(2) by simp
  have fin2: "finite {hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w}"
  proof -
    have "{hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w} \<subseteq> (\<lambda>(v, w). hamming_dist v w) ` (S \<times> S)" by auto
    thus ?thesis using fin by (rule finite_subset[OF _ finite_imageI[OF finite_cartesian_product]]) (rule fin)
  qed
  have "code_distance S \<le> hamming_dist c c'"
    unfolding code_distance_def using c(1) c'(1) ne fin2 by (auto intro!: Min_le)
  thus False using ce le unfolding corrects_errors_def by simp
qed

end
