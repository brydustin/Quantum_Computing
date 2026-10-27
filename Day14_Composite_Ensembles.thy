theory Day14_Composite_Ensembles
  imports Day13_Density_Matrices
begin

section \<open>Day 14: composite ensembles (D14-5)\<close>

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

end
