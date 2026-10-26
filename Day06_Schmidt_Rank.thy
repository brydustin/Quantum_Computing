theory Day06_Schmidt_Rank
  imports Day06_Tensor_Coordinates Quantum_Computing_by_VP.Day09_POVMs_Entanglement
begin

section \<open>Day 6: the Schmidt rank (D6-4)\<close>

text \<open>The notes define the Schmidt rank $\operatorname{rank}_S(u)$ of $u\in X\otimes Y$ as the least
number of elementary tensors in an expression for $u$, and use on Day 10 that a two-photon state
$\psi$ is a product $\psi_1\otimes\psi_2$ iff $\operatorname{rank}_S(\psi)=1$; otherwise it is entangled.
Here: every $u\in\C^n\otimes\C^m$ has an expression of length $n$, so the least length exists;
$\operatorname{rank}_S(u)=0$ iff $u=0$; for $u\ne0$, $\operatorname{rank}_S(u)=1$ iff $u$ is a product
and $u$ is entangled iff $\operatorname{rank}_S(u)>1$; the Bell state has Schmidt rank $2$.\<close>


text \<open>A representation of $u\in\C^n\otimes\C^m$ by $k$ elementary tensors.\<close>

definition schmidt_repr :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> nat \<Rightarrow> bool" where
  "schmidt_repr n m u k \<longleftrightarrow> (\<exists>vs ws. length vs = k \<and> length ws = k \<and>
     (\<forall>i < k. dim_vec (vs ! i) = n) \<and> (\<forall>i < k. dim_vec (ws ! i) = m) \<and>
     u = tensor_combination (n * m) vs ws)"

lemma schmidt_rank_eq:
  assumes u: "dim_vec u = n * m" and m: "0 < m"
  shows "schmidt_rank u m = (LEAST k. schmidt_repr n m u k)"
proof -
  have "dim_vec u div m = n" using u m by simp
  thus ?thesis unfolding schmidt_rank_def schmidt_repr_def tensor_combination_def using u by simp
qed

text \<open>Every $u$ is a sum of $n$ elementary tensors, $u=\sum_ie_i\otimes u_i$ with
$u_i=(u_{im+j})_j$, so the least length exists.\<close>

lemma schmidt_repr_exists:
  assumes u: "dim_vec u = n * m"
  shows "schmidt_repr n m u n"
proof -
  define vs :: "complex Matrix.vec list" where "vs = map (unit_vec n) [0..<n]"
  define ws where "ws = map (\<lambda>i. Matrix.vec m (\<lambda>j. u $ (i * m + j))) [0..<n]"
  have vsd: "\<forall>x \<in> set vs. dim_vec x = n" and wsd: "\<forall>y \<in> set ws. dim_vec y = m" by (auto simp: vs_def ws_def)
  have len: "length vs = length ws" by (simp add: vs_def ws_def)
  have "u = tensor_combination (n * m) vs ws"
  proof (rule eq_vecI)
    fix p assume "p < dim_vec (tensor_combination (n * m) vs ws)"
    hence p: "p < n * m" by simp
    have m: "0 < m" using p by (cases m) auto
    have pd: "p div m < n" using p by (simp add: less_mult_imp_div_less)
    have "tensor_combination (n * m) vs ws $ p = (\<Sum>j<n. vs ! j $ (p div m) * ws ! j $ (p mod m))"
      using tensor_combination_index[OF vsd wsd len p] by (simp add: vs_def)
    also have "\<dots> = (\<Sum>j<n. if j = p div m then u $ (j * m + p mod m) else 0)"
      by (rule sum.cong) (use m pd in \<open>auto simp: vs_def ws_def unit_vec_def\<close>)
    also have "\<dots> = u $ (p div m * m + p mod m)" using pd by simp
    also have "\<dots> = u $ p" by simp
    finally show "u $ p = tensor_combination (n * m) vs ws $ p" ..
  qed (use u in simp)
  thus ?thesis unfolding schmidt_repr_def using vsd wsd len
    by (intro exI[of _ vs] exI[of _ ws]) (auto simp: vs_def ws_def)
qed

lemma schmidt_rank_repr:
  assumes u: "dim_vec u = n * m" and m: "0 < m"
  shows "schmidt_repr n m u (schmidt_rank u m)" and "\<And>k. schmidt_repr n m u k \<Longrightarrow> schmidt_rank u m \<le> k"
proof -
  show "schmidt_repr n m u (schmidt_rank u m)"
    unfolding schmidt_rank_eq[OF u m] by (rule LeastI[where P = "schmidt_repr n m u", OF schmidt_repr_exists[OF u]])
  show "\<And>k. schmidt_repr n m u k \<Longrightarrow> schmidt_rank u m \<le> k"
    unfolding schmidt_rank_eq[OF u m] by (rule Least_le)
qed

lemma schmidt_repr_0: "schmidt_repr n m u 0 \<longleftrightarrow> u = 0\<^sub>v (n * m)"
  by (simp add: schmidt_repr_def tensor_combination_def)

lemma schmidt_repr_1:
  "schmidt_repr n m u 1 \<longleftrightarrow> (\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w)"
proof
  assume "schmidt_repr n m u 1"
  then obtain vs ws where l: "length vs = 1" "length ws = 1" and d: "dim_vec (vs ! 0) = n" "dim_vec (ws ! 0) = m"
    and u: "u = tensor_combination (n * m) vs ws" unfolding schmidt_repr_def by auto
  obtain v w where vs: "vs = [v]" and ws: "ws = [w]" using l by (cases vs; cases ws) auto
  have d': "dim_vec v = n" "dim_vec w = m" using d vs ws by simp_all
  have "u = tensor_vec v w + 0\<^sub>v (n * m)" using u by (simp add: vs ws tensor_combination_def)
  also have "\<dots> = tensor_vec v w" by (rule right_zero_vec[OF carrier_vecI[OF tensor_vec_dim[OF d']]])
  finally show "\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w" using d' by auto
next
  assume "\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w"
  then obtain v w where d: "dim_vec v = n" "dim_vec w = m" and u: "u = tensor_vec v w" by blast
  have "tensor_combination (n * m) [v] [w] = tensor_vec v w"
    using right_zero_vec[OF carrier_vecI[OF tensor_vec_dim[OF d]]] by (simp add: tensor_combination_def)
  thus "schmidt_repr n m u 1" unfolding schmidt_repr_def using d u
    by (intro exI[of _ "[v]"] exI[of _ "[w]"]) simp
qed

theorem schmidt_rank_zero_iff:
  assumes u: "dim_vec u = n * m" and m: "0 < m"
  shows "schmidt_rank u m = 0 \<longleftrightarrow> u = 0\<^sub>v (n * m)"
proof
  assume "schmidt_rank u m = 0"
  thus "u = 0\<^sub>v (n * m)" using schmidt_rank_repr(1)[OF u m] schmidt_repr_0 by simp
next
  assume "u = 0\<^sub>v (n * m)"
  hence "schmidt_repr n m u 0" using schmidt_repr_0 by simp
  thus "schmidt_rank u m = 0" using schmidt_rank_repr(2)[OF u m] by fastforce
qed

text \<open>The notes: $\psi=\psi_1\otimes\psi_2$ iff $\operatorname{rank}_S(\psi)=1$ (for $\psi\ne0$).\<close>

theorem schmidt_rank_one_iff_product:
  assumes u: "dim_vec u = n * m" and m: "0 < m" and u0: "u \<noteq> 0\<^sub>v (n * m)"
  shows "schmidt_rank u m = 1 \<longleftrightarrow> (\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w)"
proof
  assume "schmidt_rank u m = 1"
  thus "\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w"
    using schmidt_rank_repr(1)[OF u m] schmidt_repr_1 by simp
next
  assume "\<exists>v w. dim_vec v = n \<and> dim_vec w = m \<and> u = tensor_vec v w"
  hence "schmidt_rank u m \<le> 1" using schmidt_rank_repr(2)[OF u m] schmidt_repr_1 by blast
  moreover have "schmidt_rank u m \<noteq> 0" using schmidt_rank_zero_iff[OF u m] u0 by simp
  ultimately show "schmidt_rank u m = 1" by simp
qed

corollary entangled_iff_schmidt_rank:
  assumes u: "dim_vec u = n * m" and m: "0 < m" and u0: "u \<noteq> 0\<^sub>v (n * m)"
  shows "entangled n m u \<longleftrightarrow> 1 < schmidt_rank u m"
proof -
  have "schmidt_rank u m \<noteq> 0" using schmidt_rank_zero_iff[OF u m] u0 by simp
  thus ?thesis using schmidt_rank_one_iff_product[OF u m u0] u unfolding entangled_def by auto
qed

corollary schmidt_rank_bell_state: "schmidt_rank bell_state 2 = 2"
proof -
  have d: "dim_vec bell_state = 2 * 2" using bell_state_is_quantum_state unfolding quantum_state_def by simp
  have ne: "bell_state \<noteq> 0\<^sub>v (2 * 2)"
  proof
    assume z: "bell_state = 0\<^sub>v (2 * 2)"
    have "\<parallel>bell_state\<parallel> = 1" using bell_state_is_quantum_state unfolding quantum_state_def by simp
    moreover have "\<parallel>bell_state\<parallel> = 0" using cpx_vec_length_zero_iff[of bell_state] z d by simp
    ultimately show False by simp
  qed
  have "1 < schmidt_rank bell_state 2" using entangled_iff_schmidt_rank[OF d _ ne] bell_state_entangled by simp
  moreover have "schmidt_rank bell_state 2 \<le> 2" by (rule schmidt_rank_repr(2)[OF d _ schmidt_repr_exists[OF d]]) simp
  ultimately show ?thesis by simp
qed

end
