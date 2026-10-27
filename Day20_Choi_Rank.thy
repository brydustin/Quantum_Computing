theory Day20_Choi_Rank
  imports Day22_Kraus_Independence Day22_Minimal_Kraus
begin

section \<open>Day 20: Choi's rank theorem $\mathrm{cr}(\Phi)=\operatorname{rank}P_\Phi$ (D20-4)\<close>

text \<open>Rank is JNF's \<open>vec_space.rank\<close>, the dimension of the column space.\<close>

abbreviation mat_rank :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat" where
  "mat_rank m A \<equiv> vec_space.rank m A"

subsection \<open>$\operatorname{rank}(\sum_{l<L}w_lw_l^*)\le L$\<close>

lemma rank_outer_prod_le_1:
  assumes vd: "dim_vec v = m"
  shows "mat_rank m (v \<oslash> v) \<le> 1"
proof -
  interpret V: vec_space "TYPE(complex)" m .
  have c: "v \<oslash> v \<in> carrier_mat m m" by (rule outer_prod_carrier[OF vd vd])
  show ?thesis
  proof (rule V.rank_le_1_product_entries[OF c, of "\<lambda>r. v $ r" "\<lambda>c. cnj (v $ c)"])
    fix r c assume "r < dim_row (v \<oslash> v)" "c < dim_col (v \<oslash> v)"
    hence r: "r < m" and cc: "c < m" using carrier_matD[OF c] by auto
    have "r < dim_vec v" and "c < dim_vec v" using r cc vd by simp_all
    thus "(v \<oslash> v) $$ (r, c) = v $ r * cnj (v $ c)" by (rule outer_prod_index)
  qed
qed

lemma rank_foldr_outer_le:
  assumes vsd: "\<forall>v \<in> set vs. dim_vec v = m"
  shows "mat_rank m (foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m m m)) \<le> length vs"
  using vsd
proof (induction vs)
  case Nil
  interpret V: vec_space "TYPE(complex)" m .
  show ?case using V.rank_0I by simp
next
  case (Cons v vs)
  interpret V: vec_space "TYPE(complex)" m .
  have vd: "dim_vec v = m" and rest: "\<forall>v \<in> set vs. dim_vec v = m" using Cons.prems by auto
  have rc: "foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m m m) \<in> carrier_mat m m"
    using rest by (induction vs) (auto simp: outer_prod_carrier)
  have "mat_rank m (v \<oslash> v + foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m m m))
        \<le> mat_rank m (v \<oslash> v) + mat_rank m (foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m m m))"
    by (rule V.rank_subadditive[OF outer_prod_carrier[OF vd vd] rc])
  also have "\<dots> \<le> 1 + length vs" using rank_outer_prod_le_1[OF vd] Cons.IH[OF rest] by simp
  finally show ?case by simp
qed

lemma rank_outer_sum_le:
  assumes vsd: "\<forall>v \<in> set vs. dim_vec v = m"
  shows "mat_rank m (outer_sum m vs) \<le> length vs"
  unfolding outer_sum_as_foldr[OF vsd] by (rule rank_foldr_outer_le[OF vsd])

subsection \<open>Independent vectors inside the column space bound the rank from below\<close>

lemma mult_mat_vec_in_span:
  assumes Ac: "A \<in> carrier_mat m k" and xc: "x \<in> carrier_vec k"
  shows "A *\<^sub>v x \<in> module.span class_ring (module_vec TYPE(complex) m) (set (cols A))"
proof -
  interpret V: vec_space "TYPE(complex)" m .
  have cd: "\<forall>w \<in> set (cols A). dim_vec w = m" using Ac by (auto simp: cols_def)
  have cc: "set (cols A) \<subseteq> carrier_vec m" using cd by auto
  have A_eq: "mat_of_cols m (cols A) = A" using mat_of_cols_cols[of A] Ac by simp
  have x_eq: "Matrix.vec (length (cols A)) (\<lambda>i. (x :: complex Matrix.vec) $ i) = x" using Ac xc by (intro eq_vecI) auto
  have "A *\<^sub>v x = V.lincomb_list (\<lambda>i. x $ i) (cols A)"
    unfolding V.lincomb_list_as_mat_mult[OF cd] A_eq x_eq ..
  also have "\<dots> \<in> V.span_list (cols A)" by (rule V.in_span_listI) auto
  also have "V.span_list (cols A) = V.span (set (cols A))" by (rule V.span_list_as_span[OF cc])
  finally show ?thesis .
qed

lemma rank_ge_indep_in_colspace:
  assumes Ac: "A \<in> carrier_mat m k" and li: "lin_indep_vecs m ws"
      and insp: "\<And>w. w \<in> set ws \<Longrightarrow> w \<in> module.span class_ring (module_vec TYPE(complex) m) (set (cols A))"
  shows "length ws \<le> mat_rank m A"
proof -
  interpret V: vec_space "TYPE(complex)" m .
  define SS where "SS = set (cols A)"
  have Sc: "SS \<subseteq> carrier_vec m" unfolding SS_def using Ac by (auto simp: cols_def)
  have finS: "finite SS" by (simp add: SS_def)
  have wsc: "set ws \<subseteq> carrier_vec m" using li by (auto simp: lin_indep_vecs_def)
  have dist: "distinct ws" by (rule lin_indep_vecs_distinct[OF li])
  \<comment> \<open>independence in \<open>V\<close>, as in \<open>lin_indep_vecs_length_le\<close>\<close>
  have indpt: "V.lin_indpt (set ws)"
  proof
    assume dep: "V.lin_dep (set ws)"
    have Wc: "mat_of_cols m ws \<in> carrier_mat m (length ws)" by simp
    have cols: "cols (mat_of_cols m ws) = ws" using wsc by simp
    obtain x where xc: "x \<in> carrier_vec (length ws)" and xnz: "x \<noteq> 0\<^sub>v (length ws)"
      and Ax: "mat_of_cols m ws *\<^sub>v x = 0\<^sub>v m"
      using V.lin_depE[OF Wc, of thesis] dep dist cols by auto
    have "x = 0\<^sub>v (length ws)" using li xc Ax by (simp add: lin_indep_vecs_def)
    thus False using xnz by simp
  qed
  \<comment> \<open>pass to the subspace \<open>span S\<close>\<close>
  have sub: "VectorSpace.subspace class_ring (V.span SS) V.V" by (rule V.span_is_subspace[OF Sc])
  interpret Sp: VectorSpace.vectorspace class_ring "V.vs (V.span SS)" by (rule V.subspace_is_vs[OF sub])
  have sub_md: "submodule class_ring (V.span SS) V.V" using sub by (simp add: VectorSpace.subspace_def)
  have wsS: "set ws \<subseteq> V.span SS" unfolding SS_def using insp by auto
  have indpt_S: "Sp.lin_indpt (set ws)"
    using V.span_li_not_depend(2)[OF wsS sub_md] indpt by simp
  have Sc': "SS \<subseteq> carrier V.V" using Sc by (simp add: module_vec_simps)
  have fd: "Sp.fin_dim" using V.fin_dim_span[OF finS Sc'] by simp
  have "card (set ws) \<le> Sp.dim" using Sp.li_le_dim(2)[OF fd _ indpt_S] wsS by simp
  thus ?thesis using distinct_card[OF dist] unfolding V.rank_def by (simp add: SS_def)
qed

subsection \<open>The theorem\<close>

lemma choi_rank_attained:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp:     "completely_positive n d \<Phi>"
      and npos:   "0 < n" and dpos: "0 < d"
  shows "\<exists>As :: complex Matrix.mat list. length As = choi_rank n d \<Phi> \<and>
           (\<forall>A \<in> set As. A \<in> carrier_mat d n) \<and>
           (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X)"
proof -
  let ?K = "{ length As | As :: complex Matrix.mat list.
             (\<forall>A \<in> set As. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X) }"
  have "?K \<noteq> {}" using kraus_rank_bound[OF linear smult range cp npos dpos] by blast
  hence "Inf ?K \<in> ?K" by (rule Inf_nat_def1)
  then obtain As :: "complex Matrix.mat list" where e: "Inf ?K = length As"
    and c: "\<forall>A \<in> set As. A \<in> carrier_mat d n" and eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X"
    unfolding mem_Collect_eq by blast
  show ?thesis unfolding choi_rank_def by (intro exI[of _ As] conjI, rule e[symmetric], rule c, rule eq)
qed

theorem choi_rank_eq_rank:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp:     "completely_positive n d \<Phi>"
      and npos:   "0 < n" and dpos: "0 < d"
  shows "choi_rank n d \<Phi> = mat_rank (n*d) (choi_matrix n d \<Phi>)"
proof -
  obtain As :: "complex Matrix.mat list" where len: "length As = choi_rank n d \<Phi>"
    and As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
    and rep: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X"
    using choi_rank_attained[OF assms] by blast
  let ?ws = "map (vec_of_kraus d n) As"
  have wsd: "\<forall>w \<in> set ?ws. dim_vec w = n*d" by simp
  have choi: "choi_matrix n d \<Phi> = outer_sum (n*d) ?ws"
    using choi_matrix_cong[of n \<Phi> "kraus_map_dim d As" d] rep choi_matrix_kraus_eq[OF As_c npos dpos] by simp
  \<comment> \<open>\<open>rank P\<^sub>\<Phi> \<le> cr \<Phi>\<close>\<close>
  have le1: "mat_rank (n*d) (choi_matrix n d \<Phi>) \<le> choi_rank n d \<Phi>"
    unfolding choi using rank_outer_sum_le[OF wsd] len by simp
  \<comment> \<open>\<open>cr \<Phi> \<le> rank P\<^sub>\<Phi>\<close>: the minimal representation is independent (D22-1), so its Kraus vectors are
      independent vectors in the column space of \<open>P\<^sub>\<Phi> = W W\<^sup>\<dagger>\<close>.\<close>
  have minimal: "choi_rank n d (kraus_map_dim d As) = length As"
  proof -
    have "\<And>Bs :: complex Matrix.mat list.
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim d As X = kraus_map_dim d Bs X)
            \<longleftrightarrow> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Bs X)"
      using rep by simp
    hence "{length Bs | Bs :: complex Matrix.mat list. (\<forall>A \<in> set Bs. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim d As X = kraus_map_dim d Bs X)}
           = {length Bs | Bs :: complex Matrix.mat list. (\<forall>A \<in> set Bs. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Bs X)}" by simp
    thus ?thesis unfolding choi_rank_def using len unfolding choi_rank_def by simp
  qed
  have liA: "lin_indep_complex_mat d n As" by (rule minimal_kraus_rep_lin_indep[OF npos dpos As_c minimal])
  have liw: "lin_indep_vecs (n*d) ?ws" by (rule lin_indep_complex_mat_vec_of_kraus[OF liA dpos])
  let ?W = "mat_of_cols (n*d) ?ws"
  have Wc: "?W \<in> carrier_mat (n*d) (length As)" using mat_of_cols_carrier[of "n*d" ?ws] by simp
  have Wdc: "?W\<^sup>\<dagger> \<in> carrier_mat (length As) (n*d)" using dagger_carrier[OF Wc] .
  have Pc: "choi_matrix n d \<Phi> \<in> carrier_mat (n*d) (n*d)" unfolding choi outer_sum_def using Wc Wdc by auto
  obtain B where Bc: "B \<in> carrier_mat (length As) (length As)"
    and GB: "((?W\<^sup>\<dagger>) * ?W) * B = 1\<^sub>m (length As)" using gram_inverse[OF liw] by auto
  have insp: "\<And>w. w \<in> set ?ws \<Longrightarrow> w \<in> module.span class_ring (module_vec TYPE(complex) (n*d)) (set (cols (choi_matrix n d \<Phi>)))"
  proof -
    fix w assume "w \<in> set ?ws"
    then obtain l where l: "l < length As" and wl: "w = ?ws ! l" by (metis in_set_conv_nth length_map)
    have wc: "w \<in> carrier_vec (n*d)" unfolding wl using l by (intro carrier_vecI) simp
    \<comment> \<open>\<open>w = col W l = (W W\<^sup>\<dagger>) (W B e\<^sub>l)\<close>\<close>
    let ?x = "?W *\<^sub>v (B *\<^sub>v unit_vec (length As) l)"
    have xc: "?x \<in> carrier_vec (n*d)" using Wc Bc by simp
    let ?e = "unit_vec (length As) l"
    have ec: "?e \<in> carrier_vec (length As)" by simp
    have Bec: "B *\<^sub>v ?e \<in> carrier_vec (length As)" using Bc by simp
    have "choi_matrix n d \<Phi> *\<^sub>v ?x = (?W * (?W\<^sup>\<dagger>)) *\<^sub>v (?W *\<^sub>v (B *\<^sub>v ?e))" unfolding choi outer_sum_def ..
    also have "\<dots> = ((?W * (?W\<^sup>\<dagger>)) * ?W) *\<^sub>v (B *\<^sub>v ?e)"
      by (rule assoc_mult_mat_vec[OF mult_carrier_mat[OF Wc Wdc] Wc Bec, symmetric])
    also have "\<dots> = (((?W * (?W\<^sup>\<dagger>)) * ?W) * B) *\<^sub>v ?e"
      by (rule assoc_mult_mat_vec[OF mult_carrier_mat[OF mult_carrier_mat[OF Wc Wdc] Wc] Bc ec, symmetric])
    also have "((?W * (?W\<^sup>\<dagger>)) * ?W) * B = ?W * ((?W\<^sup>\<dagger>) * ?W * B)"
      by (simp only: assoc_mult_mat[OF Wc Wdc Wc] assoc_mult_mat[OF Wc mult_carrier_mat[OF Wdc Wc] Bc])
    also have "?W * ((?W\<^sup>\<dagger>) * ?W * B) = ?W" by (simp only: GB right_mult_one_mat[OF Wc])
    also have "?W *\<^sub>v ?e = Matrix.col ?W l"
    proof (rule eq_vecI)
      fix i assume "i < dim_vec (Matrix.col ?W l)"
      hence i: "i < n*d" using carrier_matD[OF Wc] by simp
      have "(?W *\<^sub>v ?e) $ i = (\<Sum>j<length As. ?W $$ (i,j) * ?e $ j)"
        using i carrier_matD[OF Wc] by (simp add: scalar_prod_def atLeast0LessThan)
      also have "\<dots> = (\<Sum>j<length As. if j = l then ?W $$ (i,j) else 0)"
        by (intro sum.cong refl) (simp add: unit_vec_def)
      also have "\<dots> = ?W $$ (i,l)" by (simp only: sum.delta[OF finite_lessThan]) (simp add: l)
      also have "\<dots> = Matrix.col ?W l $ i" using i carrier_matD[OF Wc] by (simp add: Matrix.col_def)
      finally show "(?W *\<^sub>v ?e) $ i = Matrix.col ?W l $ i" .
    qed (simp add: carrier_matD[OF Wc])
    also have "Matrix.col ?W l = ?ws ! l" using l wc[unfolded wl] by (intro col_mat_of_cols) simp_all
    finally have "choi_matrix n d \<Phi> *\<^sub>v ?x = w" unfolding wl .
    thus "w \<in> module.span class_ring (module_vec TYPE(complex) (n*d)) (set (cols (choi_matrix n d \<Phi>)))"
      using mult_mat_vec_in_span[OF Pc xc] by simp
  qed
  have ge1: "choi_rank n d \<Phi> \<le> mat_rank (n*d) (choi_matrix n d \<Phi>)"
    using rank_ge_indep_in_colspace[OF Pc liw insp] len by simp
  show ?thesis using le1 ge1 by simp
qed


end
