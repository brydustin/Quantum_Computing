theory Day22_Kraus_Independence
  imports QC_Prelims "Jordan_Normal_Form.DL_Rank"
begin

section \<open>Day 22: linear independence bounds the number of Kraus operators (D22-6)\<close>

text \<open>A linearly independent list of vectors in $\mathbb C^n$ has at most $n$ members.
The bridge is to JNF's @{locale vec_space}: kernel-triviality of \<open>mat_of_cols\<close> is
JNF's \<open>lin_indpt\<close> (via \<open>vec_space.lin_depE\<close>), and \<open>li_le_dim\<close> bounds the cardinality.\<close>

lemma lin_indep_vecs_distinct:
  assumes li: "lin_indep_vecs n vs"
  shows "distinct vs"
proof (rule ccontr)
  assume "\<not> distinct vs"
  then obtain i j where i: "i < length vs" and j: "j < length vs" and ij: "i \<noteq> j"
    and eq: "vs ! i = vs ! j" by (auto simp: distinct_conv_nth)
  have vsd: "\<forall>v \<in> set vs. dim_vec v = n" using li by (simp add: lin_indep_vecs_def)
  let ?m = "length vs"
  define x :: "complex Matrix.vec" where
    "x = Matrix.vec ?m (\<lambda>k. if k = i then 1 else if k = j then -1 else 0)"
  have xc: "x \<in> carrier_vec ?m" by (simp add: x_def)
  have xi: "x $ i = 1" using i ij by (simp add: x_def)
  have xnz: "x \<noteq> 0\<^sub>v ?m" using xi i by (metis index_zero_vec(1) one_neq_zero)
  have "mat_of_cols n vs *\<^sub>v x = 0\<^sub>v n"
  proof (rule eq_vecI)
    fix r assume "r < dim_vec (0\<^sub>v n :: complex Matrix.vec)"
    hence r: "r < n" by simp
    have "(mat_of_cols n vs *\<^sub>v x) $ r = (\<Sum>k = 0..<?m. mat_of_cols n vs $$ (r,k) * x $ k)"
      using r carrier_vecD[OF xc] by (simp add: scalar_prod_def)
    also have "\<dots> = (\<Sum>k = 0..<?m. (if k = i then vs ! i $ r else 0) - (if k = j then vs ! j $ r else 0))"
      using r ij by (intro sum.cong refl) (simp add: x_def mat_of_cols_index)
    also have "\<dots> = vs ! i $ r - vs ! j $ r"
      using i j by (simp add: sum_subtractf)
    also have "\<dots> = 0" using eq by simp
    finally show "(mat_of_cols n vs *\<^sub>v x) $ r = (0\<^sub>v n :: complex Matrix.vec) $ r" using r by simp
  qed simp
  hence "x = 0\<^sub>v ?m" using li xc by (simp add: lin_indep_vecs_def)
  thus False using xnz by simp
qed

lemma lin_indep_vecs_length_le:
  assumes li: "lin_indep_vecs n vs"
  shows "length vs \<le> n"
proof -
  interpret V: vec_space "TYPE(complex)" n .
  have vsd: "\<forall>v \<in> set vs. dim_vec v = n" using li by (simp add: lin_indep_vecs_def)
  have vsc: "set vs \<subseteq> carrier_vec n" using vsd by auto
  have dist: "distinct vs" by (rule lin_indep_vecs_distinct[OF li])
  let ?A = "mat_of_cols n vs"
  have Ac: "?A \<in> carrier_mat n (length vs)" by simp
  have cols: "cols ?A = vs" using vsc by simp
  have indpt: "V.lin_indpt (set vs)"
  proof
    assume dep: "V.lin_dep (set vs)"
    obtain x where xc: "x \<in> carrier_vec (length vs)" and xnz: "x \<noteq> 0\<^sub>v (length vs)"
      and Ax: "?A *\<^sub>v x = 0\<^sub>v n"
      using V.lin_depE[OF Ac, of thesis] dep dist cols by auto
    have "x = 0\<^sub>v (length vs)" using li xc Ax by (simp add: lin_indep_vecs_def)
    thus False using xnz by simp
  qed
  have "card (set vs) \<le> V.dim"
    using V.li_le_dim(2)[OF V.fin_dim _ indpt] vsc by simp
  thus ?thesis using V.dim_is_n distinct_card[OF dist] by simp
qed

text \<open>Flattening a matrix into a vector carries \<open>mat_lin_indep_complex\<close> to
\<open>lin_indep_vecs\<close>, so a linearly independent family in $M_n$ has at most $n^2$ members.\<close>

definition flatten_mat :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec" where
  "flatten_mat n B = Matrix.vec (n*n) (\<lambda>k. B $$ (k div n, k mod n))"

lemma flatten_mat_dim [simp]: "dim_vec (flatten_mat n B) = n*n"
  by (simp add: flatten_mat_def)

lemma flatten_mat_index:
  assumes "i < n" and "j < n"
  shows "flatten_mat n B $ (i*n + j) = B $$ (i,j)"
proof -
  have "i*n + j < n*n" using assms by (rule mult_index_lt)
  moreover have "(i*n + j) div n = i" and "(i*n + j) mod n = j" using assms by simp_all
  ultimately show ?thesis by (simp add: flatten_mat_def)
qed

lemma mat_lin_indep_complex_flatten:
  assumes li: "mat_lin_indep_complex n Bs"
  shows "lin_indep_vecs (n*n) (map (flatten_mat n) Bs)"
proof (unfold lin_indep_vecs_def, intro conjI allI impI)
  show "\<forall>v \<in> set (map (flatten_mat n) Bs). dim_vec v = n*n" by simp
next
  fix x :: "complex Matrix.vec"
  let ?m = "length (map (flatten_mat n) Bs)"
  let ?A = "mat_of_cols (n*n) (map (flatten_mat n) Bs)"
  assume xc: "x \<in> carrier_vec ?m" and Ax: "?A *\<^sub>v x = 0\<^sub>v (n*n)"
  have Bc: "\<forall>B \<in> set Bs. B \<in> carrier_mat n n" using li by (simp add: mat_lin_indep_complex_def)
  have len: "?m = length Bs" by simp
  let ?f = "\<lambda>k. x $ k \<cdot>\<^sub>m (Bs!k)"
  have fc: "\<forall>k \<in> set [0..<length Bs]. ?f k \<in> carrier_mat n n" using Bc by auto
  have comb0: "foldr (\<lambda>k acc. x $ k \<cdot>\<^sub>m (Bs!k) + acc) [0..<length Bs] (0\<^sub>m n n) = 0\<^sub>m n n"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (0\<^sub>m n n :: complex Matrix.mat)" "j < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
    hence i: "i < n" and j: "j < n" by simp_all
    have "foldr (\<lambda>k acc. ?f k + acc) [0..<length Bs] (0\<^sub>m n n) $$ (i,j)
            = sum_list (map (\<lambda>k. ?f k $$ (i,j)) [0..<length Bs])"
      by (rule foldr_add_mat_index[OF fc i j])
    also have "\<dots> = (\<Sum>k = 0..<length Bs. (x $ k \<cdot>\<^sub>m (Bs!k)) $$ (i,j))"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>k = 0..<length Bs. x $ k * Bs!k $$ (i,j))"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {0..<length Bs}"
      hence "Bs ! k \<in> carrier_mat n n" using Bc by (auto dest: nth_mem)
      thus "(x $ k \<cdot>\<^sub>m (Bs!k)) $$ (i,j) = x $ k * Bs!k $$ (i,j)" using i j by simp
    qed
    also have "\<dots> = (\<Sum>k = 0..<length Bs. ?A $$ (i*n + j, k) * x $ k)"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {0..<length Bs}"
      hence k: "k < length Bs" by simp
      have "?A $$ (i*n + j, k) = flatten_mat n (Bs ! k) $ (i*n + j)"
        using mult_index_lt[OF i j] k by (simp add: mat_of_cols_index)
      also have "\<dots> = Bs ! k $$ (i,j)" by (rule flatten_mat_index[OF i j])
      finally show "x $ k * Bs ! k $$ (i,j) = ?A $$ (i*n + j, k) * x $ k" by (simp add: mult.commute)
    qed
    also have "\<dots> = (?A *\<^sub>v x) $ (i*n + j)"
    proof -
      have lt: "i*n + j < n*n" using i j by (rule mult_index_lt)
      show ?thesis using lt xc by (simp add: scalar_prod_def)
    qed
    also have "\<dots> = 0" using Ax mult_index_lt[OF i j] by simp
    finally show "foldr (\<lambda>k acc. ?f k + acc) [0..<length Bs] (0\<^sub>m n n) $$ (i,j) = (0\<^sub>m n n :: complex Matrix.mat) $$ (i,j)"
      using i j by simp
  qed (use foldr_add_mat_carrier[OF fc] in auto)
  have "\<forall>k < length Bs. x $ k = 0" using li comb0 by (simp add: mat_lin_indep_complex_def)
  thus "x = 0\<^sub>v ?m" using xc by (intro eq_vecI) auto
qed

lemma mat_lin_indep_complex_length_le:
  assumes "mat_lin_indep_complex n Bs"
  shows "length Bs \<le> n*n"
  using lin_indep_vecs_length_le[OF mat_lin_indep_complex_flatten[OF assms]] by simp

text \<open>Corollary to Choi's Theorem 3 (D22-6): an extreme CPTP map $M_n\to M_d$ with a minimal
Kraus representation $(V_i)_{i<r}$ has $r^2\le n^2$, i.e.\ $\mathrm{cr}(\Phi)\le n$.\<close>

corollary extreme_CPTP_kraus_length_le:
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep: "cptp_kraus_rep n d \<Phi> Vs"
      and minimal: "lin_indep_complex_mat d n Vs"
      and ext: "extreme_CPTP_carrier n d \<Phi>"
  shows "length Vs \<le> n"
proof -
  have "mat_lin_indep_complex n (kraus_products Vs)"
    using choi_theorem_3_cptp_iff[OF npos dpos \<Phi>_in rep minimal] ext by simp
  hence "length Vs * length Vs \<le> n * n"
    using mat_lin_indep_complex_length_le length_kraus_products by metis
  thus ?thesis using power2_le_imp_le[of "length Vs" n] by (simp add: power2_eq_square)
qed

corollary extreme_CPTP_choi_rank_le:
  assumes npos: "0 < n" and dpos: "0 < d"
      and \<Phi>_in: "\<Phi> \<in> CPTP n d"
      and rep: "cptp_kraus_rep n d \<Phi> Vs"
      and minimal: "lin_indep_complex_mat d n Vs"
      and ext: "extreme_CPTP_carrier n d \<Phi>"
  shows "choi_rank n d \<Phi> \<le> n"
proof -
  have Vc: "\<forall>A \<in> set Vs. A \<in> carrier_mat d n" and Vr: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Vs X"
    using rep by (auto simp: cptp_kraus_rep_def kraus_operators_def)
  have "length Vs \<in> { length As | As :: complex Matrix.mat list.
             (\<forall>A \<in> set As. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X) }"
    using Vc Vr by blast
  hence "choi_rank n d \<Phi> \<le> length Vs"
    unfolding choi_rank_def by (intro cInf_lower) (auto intro: bdd_belowI[of _ 0])
  thus ?thesis using extreme_CPTP_kraus_length_le[OF assms] by simp
qed

end
