theory Day02_Projection_Basis
  imports Quantum_Computing_by_VP.Day03_Unitary_Matrices
begin

section \<open>Day 2: the projection does not depend on the orthonormal basis\<close>

definition col_span :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.vec set" where
  "col_span n vs = {mat_of_cols n vs *\<^sub>v c | c. dim_vec c = length vs}"

lemma outer_sum_fixes_col_span:
  assumes orth: "orthonormal_list n vs" and w: "w \<in> col_span n vs"
  shows "outer_sum n vs *\<^sub>v w = w"
proof -
  let ?k = "length vs" and ?V = "mat_of_cols n vs"
  obtain c where c: "dim_vec c = ?k" and wc: "w = ?V *\<^sub>v c" using w unfolding col_span_def by blast
  have Vc: "?V \<in> carrier_mat n ?k" by simp
  have Vdc: "?V\<^sup>\<dagger> \<in> carrier_mat ?k n" by (rule dagger_carrier[OF Vc])
  have cc: "c \<in> carrier_vec ?k" by (rule carrier_vecI[OF c])
  have VdV: "(?V\<^sup>\<dagger>) * ?V = 1\<^sub>m ?k" by (rule cols_mat_dagger_left[OF orth])
  have "outer_sum n vs *\<^sub>v w = ?V *\<^sub>v ((?V\<^sup>\<dagger>) *\<^sub>v (?V *\<^sub>v c))"
    unfolding outer_sum_def wc by (rule assoc_mult_mat_vec[OF Vc Vdc mult_mat_vec_carrier[OF Vc cc]])
  also have "(?V\<^sup>\<dagger>) *\<^sub>v (?V *\<^sub>v c) = c"
    using assoc_mult_mat_vec[OF Vdc Vc cc] unfolding VdV using cc by simp
  finally show ?thesis unfolding wc .
qed

lemma mem_col_span_self:
  assumes "\<forall>v \<in> set vs. dim_vec v = n" and j: "j < length vs"
  shows "vs ! j \<in> col_span n vs"
proof -
  have Vc: "mat_of_cols n vs \<in> carrier_mat n (length vs)" by simp
  have vj: "vs ! j \<in> carrier_vec n" using assms(1) j by (auto intro!: carrier_vecI)
  have "mat_of_cols n vs *\<^sub>v unit_vec (length vs) j = Matrix.col (mat_of_cols n vs) j"
    by (rule eq_vecI) (use Vc j in auto)
  also have "\<dots> = vs ! j" by (rule col_mat_of_cols[OF j vj])
  finally have "mat_of_cols n vs *\<^sub>v unit_vec (length vs) j = vs ! j" .
  thus ?thesis unfolding col_span_def
    by (intro CollectI exI[of _ "unit_vec (length vs) j"]) simp
qed

lemma outer_sum_absorbs:
  assumes ov: "orthonormal_list n vs" and ow: "orthonormal_list n ws"
      and sub: "set ws \<subseteq> col_span n vs"
  shows "outer_sum n vs * outer_sum n ws = outer_sum n ws"
proof -
  let ?V = "mat_of_cols n vs" and ?W = "mat_of_cols n ws" and ?P = "outer_sum n vs"
  have wd: "\<And>j. j < length ws \<Longrightarrow> ws ! j \<in> carrier_vec n"
    using ow unfolding orthonormal_list_def by (auto intro: carrier_vecI)
  have Pc: "?P \<in> carrier_mat n n" by (simp add: carrier_matI)
  have Wc: "?W \<in> carrier_mat n (length ws)" by simp
  have Wdc: "?W\<^sup>\<dagger> \<in> carrier_mat (length ws) n" by (rule dagger_carrier[OF Wc])
  have PW: "?P * ?W = ?W"
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row ?W" and j': "j < dim_col ?W"
    have j: "j < length ws" using j' by simp
    have "(?P * ?W) $$ (i,j) = (?P *\<^sub>v Matrix.col ?W j) $ i" using i j Pc by (simp add: scalar_prod_def atLeast0LessThan)
    also have "Matrix.col ?W j = ws ! j" by (rule col_mat_of_cols[OF j wd[OF j]])
    also have "?P *\<^sub>v ws ! j = ws ! j" by (rule outer_sum_fixes_col_span[OF ov subsetD[OF sub nth_mem[OF j]]])
    finally show "(?P * ?W) $$ (i,j) = ?W $$ (i,j)" using i j wd[OF j] by (simp add: mat_of_cols_def)
  qed (use Pc in simp_all)
  have "?P * outer_sum n ws = (?P * ?W) * (?W\<^sup>\<dagger>)"
    unfolding outer_sum_def[of n ws] by (rule assoc_mult_mat[OF Pc Wc Wdc, symmetric])
  thus ?thesis unfolding PW outer_sum_def[of n ws] .
qed

text \<open>D2-8: two orthonormal bases of the same subspace give the same projection.\<close>

theorem outer_sum_basis_independent:
  assumes ov: "orthonormal_list n vs" and ow: "orthonormal_list n ws"
      and span: "col_span n vs = col_span n ws"
  shows "outer_sum n vs = outer_sum n ws"
proof -
  let ?P = "outer_sum n vs" and ?Q = "outer_sum n ws"
  have vd: "\<forall>v \<in> set vs. dim_vec v = n" and wd: "\<forall>v \<in> set ws. dim_vec v = n"
    using ov ow unfolding orthonormal_list_def by auto
  have subw: "set ws \<subseteq> col_span n vs"
    using mem_col_span_self[OF wd] span by (auto simp: in_set_conv_nth)
  have subv: "set vs \<subseteq> col_span n ws"
    using mem_col_span_self[OF vd] span by (auto simp: in_set_conv_nth)
  have PQ: "?P * ?Q = ?Q" by (rule outer_sum_absorbs[OF ov ow subw])
  have QP: "?Q * ?P = ?P" by (rule outer_sum_absorbs[OF ow ov subv])
  have Pc: "?P \<in> carrier_mat n n" and Qc: "?Q \<in> carrier_mat n n" by (simp_all add: carrier_matI)
  have "?Q = (?P * ?Q)\<^sup>\<dagger>" unfolding PQ outer_sum_hermitian ..
  also have "\<dots> = (?Q\<^sup>\<dagger>) * (?P\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Pc Qc in simp)
  also have "\<dots> = ?P" unfolding outer_sum_hermitian QP ..
  finally show ?thesis ..
qed

end
