theory Day21_Unitary_Freedom
  imports Day23_ChoiExtremeUCP
begin

section \<open>Day 21: unitary freedom of rank-one decompositions and Kraus representations (D21-3, D21-5, D21-6)\<close>

subsection \<open>The Gram matrix of an independent list is invertible; dual vectors\<close>

lemma gram_det_nonzero:
  assumes li: "lin_indep_vecs n vs"
  shows "det ((mat_of_cols n vs)\<^sup>\<dagger> * mat_of_cols n vs) \<noteq> 0"
proof
  let ?k = "length vs" and ?V = "mat_of_cols n vs"
  let ?G = "?V\<^sup>\<dagger> * ?V"
  have Vc: "?V \<in> carrier_mat n ?k" by simp
  have Vd_c: "?V\<^sup>\<dagger> \<in> carrier_mat ?k n" using dagger_carrier[OF Vc] .
  have Gc: "?G \<in> carrier_mat ?k ?k" using Vc Vd_c by auto
  have inj: "\<And>x :: complex Matrix.vec. x \<in> carrier_vec ?k \<Longrightarrow> ?V *\<^sub>v x = 0\<^sub>v n \<Longrightarrow> x = 0\<^sub>v ?k"
    using li unfolding lin_indep_vecs_def by auto
  assume "det ?G = 0"
  then obtain x :: "complex Matrix.vec"
    where xc: "x \<in> carrier_vec ?k" and xnz: "x \<noteq> 0\<^sub>v ?k" and Gx: "?G *\<^sub>v x = 0\<^sub>v ?k"
    using det_0_iff_vec_prod_zero_field[OF Gc] by auto
  have xd: "dim_vec x = ?k" using xc by auto
  have Vx: "dim_vec (?V *\<^sub>v x) = n" using Vc xd by auto
  have "\<langle>?V *\<^sub>v x | ?V *\<^sub>v x\<rangle> = \<langle>(?V\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | ?V *\<^sub>v x\<rangle>"
    by (simp add: dagger_of_dagger_is_id)
  also have "\<dots> = \<langle>x | ?V\<^sup>\<dagger> *\<^sub>v (?V *\<^sub>v x)\<rangle>"
    using inner_prod_adjoint_swap[OF Vd_c xd Vx] by simp
  also have "\<dots> = \<langle>x | ?G *\<^sub>v x\<rangle>" by (simp only: assoc_mult_mat_vec[OF Vd_c Vc xc])
  also have "\<dots> = 0" unfolding inner_prod_def using Gx xd by simp
  finally have "?V *\<^sub>v x = 0\<^sub>v n" using Vx inner_prod_self_eq_zero_iff[of "?V *\<^sub>v x"] by simp
  with inj[OF xc] xnz show False by simp
qed

lemma gram_inverse:
  assumes li: "lin_indep_vecs n vs"
  obtains B where "B \<in> carrier_mat (length vs) (length vs)"
    and "((mat_of_cols n vs)\<^sup>\<dagger> * mat_of_cols n vs) * B = 1\<^sub>m (length vs)"
    and "B * ((mat_of_cols n vs)\<^sup>\<dagger> * mat_of_cols n vs) = 1\<^sub>m (length vs)"
    and "B\<^sup>\<dagger> = B"
proof -
  let ?k = "length vs" and ?V = "mat_of_cols n vs"
  let ?G = "?V\<^sup>\<dagger> * ?V"
  have Vc: "?V \<in> carrier_mat n ?k" by simp
  have Gc: "?G \<in> carrier_mat ?k ?k" using Vc dagger_carrier[OF Vc] by auto
  have Gh: "?G\<^sup>\<dagger> = ?G" by (simp add: dagger_of_prod dagger_of_dagger_is_id)
  obtain B :: "complex Matrix.mat"
    where Bc: "B \<in> carrier_mat ?k ?k" and GB: "?G * B = 1\<^sub>m ?k" and BG: "B * ?G = 1\<^sub>m ?k"
    using det_non_zero_imp_unit[OF Gc gram_det_nonzero[OF li], of "()"]
    by (auto simp: Units_def ring_mat_def)
  have Bdc: "B\<^sup>\<dagger> \<in> carrier_mat ?k ?k" using dagger_carrier[OF Bc] .
  have "B\<^sup>\<dagger> * ?G = (?G * B)\<^sup>\<dagger>"
    using dagger_of_prod[of ?G B] Gc Bc Gh by auto
  also have "\<dots> = 1\<^sub>m ?k" unfolding GB by (rule eq_matI) (auto simp: dagger_def)
  finally have BdG: "B\<^sup>\<dagger> * ?G = 1\<^sub>m ?k" .
  have "B\<^sup>\<dagger> = B\<^sup>\<dagger> * (?G * B)" unfolding GB by (rule right_mult_one_mat[OF Bdc, symmetric])
  also have "\<dots> = (B\<^sup>\<dagger> * ?G) * B" using assoc_mult_mat[OF Bdc Gc Bc] by simp
  also have "\<dots> = B" unfolding BdG using Bc by simp
  finally have "B\<^sup>\<dagger> = B" .
  with Bc GB BG show thesis by (rule that)
qed

text \<open>Dual vectors (the notes' ``$T^*$ is onto''): for independent $v_1,\dots,v_k$ there are
$\varphi_1,\dots,\varphi_k$ with $\langle\varphi_i|v_j\rangle=\delta_{ij}$.\<close>

lemma dual_vectors_exist:
  assumes li: "lin_indep_vecs n vs"
  shows "\<exists>\<phi>s :: complex Matrix.vec list. length \<phi>s = length vs \<and>
           (\<forall>\<phi> \<in> set \<phi>s. dim_vec \<phi> = n) \<and>
           (\<forall>i < length vs. \<forall>j < length vs. \<langle>\<phi>s ! i | vs ! j\<rangle> = (if i = j then 1 else 0))"
proof -
  let ?k = "length vs" and ?V = "mat_of_cols n vs"
  let ?G = "?V\<^sup>\<dagger> * ?V"
  have vsd: "\<forall>v \<in> set vs. dim_vec v = n" using li by (simp add: lin_indep_vecs_def)
  have Vc: "?V \<in> carrier_mat n ?k" by simp
  have Vd_c: "?V\<^sup>\<dagger> \<in> carrier_mat ?k n" using dagger_carrier[OF Vc] .
  have Gc: "?G \<in> carrier_mat ?k ?k" using Vc Vd_c by auto
  obtain B where Bc: "B \<in> carrier_mat ?k ?k" and GB: "?G * B = 1\<^sub>m ?k"
    and BG: "B * ?G = 1\<^sub>m ?k" and Bh: "B\<^sup>\<dagger> = B"
    by (rule gram_inverse[OF li])
  let ?P = "?V * B"
  have Pc: "?P \<in> carrier_mat n ?k" using Vc Bc by auto
  have Pd_c: "?P\<^sup>\<dagger> \<in> carrier_mat ?k n" using dagger_carrier[OF Pc] .
  let ?\<phi>s = "cols ?P"
  have \<phi>len: "length ?\<phi>s = ?k" using carrier_matD(2)[OF Pc] by simp
  have \<phi>d: "\<forall>\<phi> \<in> set ?\<phi>s. dim_vec \<phi> = n" using Pc by (auto simp: cols_def)
  have P_eq: "mat_of_cols n ?\<phi>s = ?P" using Pc mat_of_cols_cols[of ?P] by auto
  have BdG: "B\<^sup>\<dagger> * ?G = 1\<^sub>m ?k" using Bh BG by simp
  have dual: "\<And>i j. i < ?k \<Longrightarrow> j < ?k \<Longrightarrow> \<langle>?\<phi>s ! i | vs ! j\<rangle> = (if i = j then 1 else 0)"
  proof -
    fix i j assume i: "i < ?k" and j: "j < ?k"
    have vjd: "dim_vec (vs ! j) = n" using vsd j by simp
    have "\<langle>?\<phi>s ! i | vs ! j\<rangle> = (((mat_of_cols n ?\<phi>s)\<^sup>\<dagger>) *\<^sub>v (vs ! j)) $ i"
      using mat_of_cols_dagger_mult_vec_index[OF vjd \<phi>d, of i] \<phi>len i by simp
    also have "\<dots> = ((?P\<^sup>\<dagger>) *\<^sub>v Matrix.col ?V j) $ i"
      using P_eq col_mat_of_cols[of j vs n] j vjd by auto
    also have "(?P\<^sup>\<dagger>) *\<^sub>v Matrix.col ?V j = Matrix.col ((?P\<^sup>\<dagger>) * ?V) j"
      using col_mult2[OF Pd_c Vc j] by simp
    also have "Matrix.col ((?P\<^sup>\<dagger>) * ?V) j $ i = ((?P\<^sup>\<dagger>) * ?V) $$ (i, j)"
    proof -
      have PV_c: "(?P\<^sup>\<dagger>) * ?V \<in> carrier_mat ?k ?k" using Pd_c Vc by auto
      thus ?thesis using i j carrier_matD[OF PV_c] by (simp add: Matrix.col_def)
    qed
    also have "(?P\<^sup>\<dagger>) * ?V = B\<^sup>\<dagger> * ?G"
    proof -
      have "?P\<^sup>\<dagger> = (B\<^sup>\<dagger>) * (?V\<^sup>\<dagger>)" using dagger_of_prod[of ?V B] Vc Bc by auto
      hence "(?P\<^sup>\<dagger>) * ?V = ((B\<^sup>\<dagger>) * (?V\<^sup>\<dagger>)) * ?V" by simp
      also have "\<dots> = (B\<^sup>\<dagger>) * ((?V\<^sup>\<dagger>) * ?V)"
        using assoc_mult_mat[OF dagger_carrier[OF Bc] Vd_c Vc] .
      finally show ?thesis .
    qed
    also have "\<dots> = 1\<^sub>m ?k" by (rule BdG)
    finally show "\<langle>?\<phi>s ! i | vs ! j\<rangle> = (if i = j then 1 else 0)" using i j by simp
  qed
  show ?thesis using \<phi>len \<phi>d dual by blast
qed

subsection \<open>D21-3: independent vectors give independent rank-one matrices\<close>

definition outer_prods :: "complex Matrix.vec list \<Rightarrow> complex Matrix.mat list" where
  "outer_prods vs = map (\<lambda>k. vs ! (k div length vs) \<oslash> vs ! (k mod length vs)) [0..<length vs * length vs]"

lemma length_outer_prods [simp]: "length (outer_prods vs) = length vs * length vs"
  by (simp add: outer_prods_def)

lemma outer_prods_nth:
  assumes "k < length vs * length vs"
  shows "outer_prods vs ! k = vs ! (k div length vs) \<oslash> vs ! (k mod length vs)"
  using assms by (simp add: outer_prods_def)

lemma inner_prod_cnj_delta:
  assumes "dim_vec \<phi> = n" and "dim_vec v = n" and "\<langle>\<phi> | v\<rangle> = (if P then 1 else 0)"
  shows "\<langle>v | \<phi>\<rangle> = (if P then 1 else 0)"
  using inner_prod_cnj[of \<phi> v] assms by simp

proposition outer_prods_lin_indep:
  assumes li: "lin_indep_vecs n vs"
  shows "lin_indep_complex_mat n n (outer_prods vs)"
proof -
  let ?r = "length vs"
  have vsd: "\<forall>v \<in> set vs. dim_vec v = n" using li by (simp add: lin_indep_vecs_def)
  have vd: "\<And>a. a < ?r \<Longrightarrow> dim_vec (vs ! a) = n" using vsd by simp
  obtain \<phi>s :: "complex Matrix.vec list"
    where \<phi>len: "length \<phi>s = ?r" and \<phi>d: "\<forall>\<phi> \<in> set \<phi>s. dim_vec \<phi> = n"
      and dual: "\<forall>i < ?r. \<forall>j < ?r. \<langle>\<phi>s ! i | vs ! j\<rangle> = (if i = j then 1 else 0)"
    using dual_vectors_exist[OF li] by blast
  have \<phi>dm: "\<And>m. m < ?r \<Longrightarrow> dim_vec (\<phi>s ! m) = n" using \<phi>d \<phi>len by simp
  have Bc: "\<forall>B \<in> set (outer_prods vs). B \<in> carrier_mat n n"
  proof
    fix B assume "B \<in> set (outer_prods vs)"
    then obtain J where J: "J < ?r * ?r" and B: "B = vs ! (J div ?r) \<oslash> vs ! (J mod ?r)"
      unfolding outer_prods_def set_map by auto
    have r0: "0 < ?r" using J by (cases ?r) auto
    have "J div ?r < ?r" by (rule less_mult_imp_div_less[OF J])
    moreover have "J mod ?r < ?r" by (rule mod_less_divisor[OF r0])
    ultimately show "B \<in> carrier_mat n n" unfolding B by (intro outer_prod_carrier vd)
  qed
  show ?thesis
  proof (unfold lin_indep_complex_mat_def, intro conjI allI impI)
    show "\<forall>B \<in> set (outer_prods vs). B \<in> carrier_mat n n" by (rule Bc)
  next
    fix c :: "nat \<Rightarrow> complex"
    let ?M = "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (outer_prods vs ! k) + acc) [0..<length (outer_prods vs)] (0\<^sub>m n n)"
    assume M0: "?M = 0\<^sub>m n n"
    have fc: "\<forall>k \<in> set [0..<length (outer_prods vs)]. c k \<cdot>\<^sub>m (outer_prods vs ! k) \<in> carrier_mat n n"
      using Bc by auto
    have Mij: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
        ?M $$ (i,j) = (\<Sum>k < ?r * ?r. c k * (vs ! (k div ?r) $ i * cnj (vs ! (k mod ?r) $ j)))"
    proof -
      fix i j assume i: "i < n" and j: "j < n"
      have "?M $$ (i,j) = sum_list (map (\<lambda>k. (c k \<cdot>\<^sub>m (outer_prods vs ! k)) $$ (i,j)) [0..<length (outer_prods vs)])"
        by (rule foldr_add_mat_index[OF fc i j])
      also have "\<dots> = (\<Sum>k < ?r * ?r. (c k \<cdot>\<^sub>m (outer_prods vs ! k)) $$ (i,j))"
        by (simp add: sum_list_sum_nth atLeast0LessThan)
      also have "\<dots> = (\<Sum>k < ?r * ?r. c k * (vs ! (k div ?r) $ i * cnj (vs ! (k mod ?r) $ j)))"
      proof (rule sum.cong[OF refl])
        fix k assume "k \<in> {..<?r * ?r}"
        hence k: "k < ?r * ?r" by simp
        have a: "k div ?r < ?r" using k by (simp add: less_mult_imp_div_less)
        have b: "k mod ?r < ?r" using k by (cases ?r) auto
        have Bk: "outer_prods vs ! k \<in> carrier_mat n n" using Bc nth_mem[of k "outer_prods vs"] k by simp
        have "(c k \<cdot>\<^sub>m (outer_prods vs ! k)) $$ (i,j) = c k * (outer_prods vs ! k) $$ (i,j)"
          using carrier_matD[OF Bk] i j by simp
        also have "(outer_prods vs ! k) $$ (i,j) = vs ! (k div ?r) $ i * cnj (vs ! (k mod ?r) $ j)"
          unfolding outer_prods_nth[OF k] using vd[OF a] vd[OF b] i j by (intro outer_prod_index) auto
        finally show "(c k \<cdot>\<^sub>m (outer_prods vs ! k)) $$ (i,j) = c k * (vs ! (k div ?r) $ i * cnj (vs ! (k mod ?r) $ j))" .
      qed
      finally show "?M $$ (i,j) = (\<Sum>k < ?r * ?r. c k * (vs ! (k div ?r) $ i * cnj (vs ! (k mod ?r) $ j)))" .
    qed
    \<comment> \<open>Apply \<open>?M\<close> to the dual vector \<open>\<phi>\<^sub>m\<close>: only the terms with \<open>k mod r = m\<close> survive.\<close>
    have key: "\<And>m i. m < ?r \<Longrightarrow> i < n \<Longrightarrow> (\<Sum>a < ?r. c (a * ?r + m) * vs ! a $ i) = 0"
    proof -
      fix m i assume m: "m < ?r" and i: "i < n"
      have rpos: "0 < ?r" using m by (cases vs) auto
      have "(?M *\<^sub>v \<phi>s ! m) $ i = (\<Sum>j = 0..<n. ?M $$ (i,j) * \<phi>s ! m $ j)"
        using i \<phi>dm[OF m] carrier_matD[OF foldr_add_mat_carrier[OF fc]] by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>j = 0..<n. \<Sum>k < ?r * ?r. c k * (vs ! (k div ?r) $ i * (cnj (vs ! (k mod ?r) $ j) * \<phi>s ! m $ j)))"
      proof (intro sum.cong refl)
        fix j assume "j \<in> {0..<n}"
        hence j: "j < n" by simp
        show "?M $$ (i,j) * \<phi>s ! m $ j
              = (\<Sum>k < ?r * ?r. c k * (vs ! (k div ?r) $ i * (cnj (vs ! (k mod ?r) $ j) * \<phi>s ! m $ j)))"
          unfolding Mij[OF i j] by (simp add: sum_distrib_right mult_ac(1))
      qed
      also have "\<dots> = (\<Sum>k < ?r * ?r. c k * (vs ! (k div ?r) $ i * (\<Sum>j = 0..<n. cnj (vs ! (k mod ?r) $ j) * \<phi>s ! m $ j)))"
        by (subst sum.swap) (simp add: sum_distrib_left)
      also have "\<dots> = (\<Sum>k < ?r * ?r. c k * (vs ! (k div ?r) $ i * (if k mod ?r = m then 1 else 0)))"
      proof (rule sum.cong[OF refl])
        fix k assume "k \<in> {..<?r * ?r}"
        hence k: "k < ?r * ?r" by simp
        have b: "k mod ?r < ?r" using k by (cases ?r) auto
        have "(\<Sum>j = 0..<n. cnj (vs ! (k mod ?r) $ j) * \<phi>s ! m $ j) = \<langle>vs ! (k mod ?r) | \<phi>s ! m\<rangle>"
          by (rule inner_prod_sum[OF vd[OF b] \<phi>dm[OF m], symmetric])
        also have "\<dots> = (if k mod ?r = m then 1 else 0)"
        proof -
          have "\<langle>\<phi>s ! m | vs ! (k mod ?r)\<rangle> = (if m = k mod ?r then 1 else 0)" using dual m b by blast
          hence "\<langle>\<phi>s ! m | vs ! (k mod ?r)\<rangle> = (if k mod ?r = m then 1 else 0)" by (simp only: eq_commute)
          thus ?thesis by (rule inner_prod_cnj_delta[OF \<phi>dm[OF m] vd[OF b]])
        qed
        finally show "c k * (vs ! (k div ?r) $ i * (\<Sum>j = 0..<n. cnj (vs ! (k mod ?r) $ j) * \<phi>s ! m $ j))
                      = c k * (vs ! (k div ?r) $ i * (if k mod ?r = m then 1 else 0))" by simp
      qed
      also have "\<dots> = (\<Sum>k \<in> {k. k < ?r * ?r \<and> k mod ?r = m}. c k * vs ! (k div ?r) $ i)"
      proof -
        have "(\<Sum>k < ?r * ?r. c k * (vs ! (k div ?r) $ i * (if k mod ?r = m then 1 else 0)))
              = (\<Sum>k \<in> {..<?r * ?r}. if k \<in> {k. k mod ?r = m} then c k * vs ! (k div ?r) $ i else 0)"
          by (intro sum.cong refl) simp
        also have "\<dots> = (\<Sum>k \<in> {..<?r * ?r} \<inter> {k. k mod ?r = m}. c k * vs ! (k div ?r) $ i)"
          by (rule sum.inter_restrict[symmetric]) simp
        also have "{..<?r * ?r} \<inter> {k. k mod ?r = m} = {k. k < ?r * ?r \<and> k mod ?r = m}" by auto
        finally show ?thesis .
      qed
      also have "\<dots> = (\<Sum>a < ?r. c (a * ?r + m) * vs ! a $ i)"
      proof -
        have bij: "bij_betw (\<lambda>a. a * ?r + m) {..<?r} {k. k < ?r * ?r \<and> k mod ?r = m}"
        proof (rule bij_betwI[of _ _ _ "\<lambda>k. k div ?r"])
          show "(\<lambda>a. a * ?r + m) \<in> {..<?r} \<rightarrow> {k. k < ?r * ?r \<and> k mod ?r = m}"
          proof
            fix a assume "a \<in> {..<?r}"
            hence a: "a < ?r" by simp
            have "a * ?r + m < a * ?r + ?r" using m by simp
            also have "\<dots> = (a + 1) * ?r" by (simp add: distrib_right)
            also have "\<dots> \<le> ?r * ?r" using a by (intro mult_le_mono1) simp
            finally have "a * ?r + m < ?r * ?r" .
            moreover have "(a * ?r + m) mod ?r = m" using m by simp
            ultimately show "a * ?r + m \<in> {k. k < ?r * ?r \<and> k mod ?r = m}" by simp
          qed
          show "(\<lambda>k. k div ?r) \<in> {k. k < ?r * ?r \<and> k mod ?r = m} \<rightarrow> {..<?r}"
            by (auto simp: less_mult_imp_div_less)
          show "\<And>a. a \<in> {..<?r} \<Longrightarrow> (a * ?r + m) div ?r = a" using m by simp
          show "\<And>k. k \<in> {k. k < ?r * ?r \<and> k mod ?r = m} \<Longrightarrow> k div ?r * ?r + m = k"
            by auto
        qed
        have "(\<Sum>k \<in> {k. k < ?r * ?r \<and> k mod ?r = m}. c k * vs ! (k div ?r) $ i)
              = (\<Sum>a < ?r. c (a * ?r + m) * vs ! ((a * ?r + m) div ?r) $ i)"
          by (rule sum.reindex_bij_betw[OF bij, of "\<lambda>k. c k * vs ! (k div ?r) $ i", symmetric])
        also have "\<dots> = (\<Sum>a < ?r. c (a * ?r + m) * vs ! a $ i)"
        proof (intro sum.cong refl)
          fix a assume "a \<in> {..<?r}"
          have "(a * ?r + m) div ?r = a" using m by simp
          thus "c (a * ?r + m) * vs ! ((a * ?r + m) div ?r) $ i = c (a * ?r + m) * vs ! a $ i" by simp
        qed
        finally show ?thesis .
      qed
      finally have "(?M *\<^sub>v \<phi>s ! m) $ i = (\<Sum>a < ?r. c (a * ?r + m) * vs ! a $ i)" .
      moreover have "(?M *\<^sub>v \<phi>s ! m) $ i = 0"
        unfolding M0 using i carrier_vecI[OF \<phi>dm[OF m]] by (simp add: scalar_prod_left_zero)
      ultimately show "(\<Sum>a < ?r. c (a * ?r + m) * vs ! a $ i) = 0" by simp
    qed
    \<comment> \<open>So each slice \<open>a \<mapsto> c (a r + m)\<close> is in the kernel of \<open>mat_of_cols n vs\<close>.\<close>
    have slice: "\<And>m. m < ?r \<Longrightarrow> \<forall>a < ?r. c (a * ?r + m) = 0"
    proof -
      fix m assume m: "m < ?r"
      define x :: "complex Matrix.vec" where "x = Matrix.vec ?r (\<lambda>a. c (a * ?r + m))"
      have xc: "x \<in> carrier_vec ?r" by (simp add: x_def)
      have "mat_of_cols n vs *\<^sub>v x = 0\<^sub>v n"
      proof (rule eq_vecI)
        fix i assume "i < dim_vec (0\<^sub>v n :: complex Matrix.vec)"
        hence i: "i < n" by simp
        have "(mat_of_cols n vs *\<^sub>v x) $ i = (\<Sum>a = 0..<?r. mat_of_cols n vs $$ (i,a) * x $ a)"
          using i by (simp add: scalar_prod_def x_def)
        also have "\<dots> = (\<Sum>a < ?r. c (a * ?r + m) * vs ! a $ i)"
          using i by (intro sum.cong) (auto simp: x_def mat_of_cols_index mult.commute)
        also have "\<dots> = 0" by (rule key[OF m i])
        finally show "(mat_of_cols n vs *\<^sub>v x) $ i = (0\<^sub>v n :: complex Matrix.vec) $ i" using i by simp
      qed simp
      hence x0: "x = 0\<^sub>v ?r" using li xc by (simp add: lin_indep_vecs_def)
      show "\<forall>a < ?r. c (a * ?r + m) = 0"
      proof (intro allI impI)
        fix a assume a: "a < ?r"
        have "x $ a = (0\<^sub>v ?r :: complex Matrix.vec) $ a" unfolding x0 ..
        thus "c (a * ?r + m) = 0" unfolding x_def using a by simp
      qed
    qed
    fix k assume "k < length (outer_prods vs)"
    hence k: "k < ?r * ?r" by simp
    have a: "k div ?r < ?r" using k by (simp add: less_mult_imp_div_less)
    have b: "k mod ?r < ?r" using k by (cases ?r) auto
    have "c (k div ?r * ?r + k mod ?r) = 0" using slice[OF b] a by blast
    thus "c k = 0" unfolding div_mult_mod_eq .
  qed
qed

subsection \<open>Isometric mixing of columns preserves $VV^*$\<close>

lemma dagger_transpose_mult:
  assumes Uc: "U \<in> carrier_mat m r" and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m r"
  shows "transpose_mat U * ((transpose_mat U)\<^sup>\<dagger>) = 1\<^sub>m r"
proof (rule eq_matI)
  fix j k assume "j < dim_row (1\<^sub>m r :: complex Matrix.mat)" "k < dim_col (1\<^sub>m r :: complex Matrix.mat)"
  hence j: "j < r" and k: "k < r" by simp_all
  have "(transpose_mat U * ((transpose_mat U)\<^sup>\<dagger>)) $$ (j,k) = (\<Sum>l<m. U $$ (l,j) * cnj (U $$ (l,k)))"
    using j k Uc by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>l<m. cnj (U $$ (l,k)) * U $$ (l,j))" by (simp add: mult.commute)
  also have "\<dots> = ((U\<^sup>\<dagger>) * U) $$ (k,j)" using j k Uc by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = (1\<^sub>m r :: complex Matrix.mat) $$ (j,k)" unfolding UU using j k by auto
  finally show "(transpose_mat U * ((transpose_mat U)\<^sup>\<dagger>)) $$ (j,k) = (1\<^sub>m r :: complex Matrix.mat) $$ (j,k)" .
qed (use Uc in \<open>auto simp: dagger_def\<close>)

lemma isometry_mix_outer:
  assumes Vc: "V \<in> carrier_mat n r" and Uc: "U \<in> carrier_mat m r" and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m r"
  shows "(V * transpose_mat U) * ((V * transpose_mat U)\<^sup>\<dagger>) = V * (V\<^sup>\<dagger>)"
proof -
  let ?T = "transpose_mat U"
  have Tc: "?T \<in> carrier_mat r m" using Uc by simp
  have Tdc: "?T\<^sup>\<dagger> \<in> carrier_mat m r" using dagger_carrier[OF Tc] .
  have Vdc: "V\<^sup>\<dagger> \<in> carrier_mat r n" using dagger_carrier[OF Vc] .
  have dag: "(V * ?T)\<^sup>\<dagger> = (?T\<^sup>\<dagger>) * (V\<^sup>\<dagger>)"
    using dagger_of_prod[of V ?T] Vc Tc by auto
  have "(V * ?T) * ((V * ?T)\<^sup>\<dagger>) = (V * ?T) * ((?T\<^sup>\<dagger>) * (V\<^sup>\<dagger>))" by (simp only: dag)
  also have "\<dots> = V * (?T * ((?T\<^sup>\<dagger>) * (V\<^sup>\<dagger>)))"
    by (rule assoc_mult_mat[OF Vc Tc mult_carrier_mat[OF Tdc Vdc]])
  also have "\<dots> = V * ((?T * (?T\<^sup>\<dagger>)) * (V\<^sup>\<dagger>))" by (simp only: assoc_mult_mat[OF Tc Tdc Vdc])
  also have "\<dots> = V * (1\<^sub>m r * (V\<^sup>\<dagger>))" by (simp only: dagger_transpose_mult[OF Uc UU])
  also have "\<dots> = V * (V\<^sup>\<dagger>)" by (simp only: left_mult_one_mat[OF Vdc])
  finally show ?thesis .
qed

lemma dagger_mult_zero_imp_zero:
  fixes Y :: "complex Matrix.mat"
  assumes Yc: "Y \<in> carrier_mat p q" and YY: "(Y\<^sup>\<dagger>) * Y = 0\<^sub>m q q"
  shows "Y = 0\<^sub>m p q"
proof (rule eq_matI)
  fix i j assume "i < dim_row (0\<^sub>m p q :: complex Matrix.mat)" "j < dim_col (0\<^sub>m p q :: complex Matrix.mat)"
  hence i: "i < p" and j: "j < q" by simp_all
  have "\<langle>Matrix.col Y j | Matrix.col Y j\<rangle> = ((Y\<^sup>\<dagger>) * Y) $$ (j,j)"
    by (rule dagger_mult_diag_inner[OF Yc j, symmetric])
  also have "\<dots> = 0" unfolding YY using j by simp
  finally have z: "Matrix.col Y j = 0\<^sub>v p"
    using inner_prod_self_eq_zero_iff[of "Matrix.col Y j"] carrier_matD(1)[OF Yc] by simp
  have "Y $$ (i,j) = Matrix.col Y j $ i" using i carrier_matD(1)[OF Yc] by (simp add: Matrix.col_def)
  also have "\<dots> = 0" unfolding z using i by simp
  finally show "Y $$ (i,j) = (0\<^sub>m p q :: complex Matrix.mat) $$ (i,j)" using i j by simp
qed (use carrier_matD[OF Yc] in simp_all)

subsection \<open>D21-5: two rank-one decompositions are related by an isometry\<close>

text \<open>If $P=\sum_{j<r}v_jv_j^*=\sum_{l<m}w_lw_l^*$ with $v_1,\dots,v_r$ linearly independent
(the notes assume $\operatorname{rank}P=r$, which is equivalent), then $w_l=\sum_j\alpha_{lj}v_j$
with $U=(\alpha_{lj})$ an $m\times r$ isometry, $U^*U=I_r$.  Matrix form: $W=VU^{t}$.\<close>

theorem rank_one_decomp_isometry:
  assumes li: "lin_indep_vecs n vs"
      and wsd: "\<forall>w \<in> set ws. dim_vec w = n"
      and same: "outer_sum n vs = outer_sum n ws"
  shows "\<exists>U :: complex Matrix.mat. U \<in> carrier_mat (length ws) (length vs) \<and>
           (U\<^sup>\<dagger>) * U = 1\<^sub>m (length vs) \<and>
           mat_of_cols n ws = mat_of_cols n vs * transpose_mat U"
proof -
  let ?r = "length vs" and ?m = "length ws"
  let ?V = "mat_of_cols n vs" and ?W = "mat_of_cols n ws"
  let ?G = "?V\<^sup>\<dagger> * ?V"
  have Vc: "?V \<in> carrier_mat n ?r" and Wc: "?W \<in> carrier_mat n ?m" by simp_all
  have Vdc: "?V\<^sup>\<dagger> \<in> carrier_mat ?r n" and Wdc: "?W\<^sup>\<dagger> \<in> carrier_mat ?m n"
    using dagger_carrier[OF Vc] dagger_carrier[OF Wc] .
  have Gc: "?G \<in> carrier_mat ?r ?r" using Vc Vdc by auto
  obtain B where Bc: "B \<in> carrier_mat ?r ?r" and GB: "?G * B = 1\<^sub>m ?r"
    and BG: "B * ?G = 1\<^sub>m ?r" and Bh: "B\<^sup>\<dagger> = B"
    by (rule gram_inverse[OF li])
  have VV: "?V * (?V\<^sup>\<dagger>) = ?W * (?W\<^sup>\<dagger>)" using same by (simp add: outer_sum_def)
  \<comment> \<open>\<open>Q = V B V\<^sup>\<dagger>\<close> is the projection onto the span of the \<open>v\<^sub>j\<close>; the kernel argument gives \<open>Q W = W\<close>.\<close>
  let ?Q = "?V * B * (?V\<^sup>\<dagger>)"
  have Qc: "?Q \<in> carrier_mat n n" using Vc Bc Vdc by auto
  have QW: "?Q * ?W = ?W"
  proof -
    let ?X = "?W - ?Q * ?W"
    have Xc: "?X \<in> carrier_mat n ?m" using Wc Qc by auto
    have VdQ: "(?V\<^sup>\<dagger>) * ?Q = ?V\<^sup>\<dagger>"
    proof -
      have "(?V\<^sup>\<dagger>) * ?Q = ((?V\<^sup>\<dagger>) * (?V * B)) * (?V\<^sup>\<dagger>)"
        by (rule assoc_mult_mat[OF Vdc mult_carrier_mat[OF Vc Bc] Vdc, symmetric])
      also have "\<dots> = ((?V\<^sup>\<dagger>) * ?V * B) * (?V\<^sup>\<dagger>)"
        by (simp only: assoc_mult_mat[OF Vdc Vc Bc, symmetric])
      also have "\<dots> = ?V\<^sup>\<dagger>" unfolding GB by (rule left_mult_one_mat[OF Vdc])
      finally show ?thesis .
    qed
    have VdX: "(?V\<^sup>\<dagger>) * ?X = 0\<^sub>m ?r ?m"
    proof -
      have "(?V\<^sup>\<dagger>) * ?X = (?V\<^sup>\<dagger>) * ?W - (?V\<^sup>\<dagger>) * (?Q * ?W)"
        by (rule mult_minus_distrib_mat[OF Vdc Wc mult_carrier_mat[OF Qc Wc]])
      also have "(?V\<^sup>\<dagger>) * (?Q * ?W) = ((?V\<^sup>\<dagger>) * ?Q) * ?W"
        using assoc_mult_mat[OF Vdc Qc Wc] by simp
      also have "\<dots> = (?V\<^sup>\<dagger>) * ?W" unfolding VdQ ..
      finally show ?thesis using Vdc Wc by simp
    qed
    \<comment> \<open>\<open>W\<^sup>\<dagger> X = 0\<close> because \<open>W W\<^sup>\<dagger> X = V V\<^sup>\<dagger> X = 0\<close> and \<open>(W\<^sup>\<dagger>X)\<^sup>\<dagger>(W\<^sup>\<dagger>X) = X\<^sup>\<dagger> W W\<^sup>\<dagger> X = 0\<close>.\<close>
    have WWX: "?W * (?W\<^sup>\<dagger>) * ?X = 0\<^sub>m n ?m"
    proof -
      have "?W * (?W\<^sup>\<dagger>) * ?X = ?V * ((?V\<^sup>\<dagger>) * ?X)"
        unfolding VV[symmetric] using assoc_mult_mat[OF Vc Vdc Xc] by simp
      also have "\<dots> = 0\<^sub>m n ?m" unfolding VdX using Vc by simp
      finally show ?thesis .
    qed
    have WdX: "(?W\<^sup>\<dagger>) * ?X = 0\<^sub>m ?m ?m"
    proof -
      let ?Y = "(?W\<^sup>\<dagger>) * ?X"
      have Yc: "?Y \<in> carrier_mat ?m ?m" using Wdc Xc by auto
      have "(?Y\<^sup>\<dagger>) * ?Y = (?X\<^sup>\<dagger>) * (?W * (?W\<^sup>\<dagger>) * ?X)"
      proof -
        have Yd: "?Y\<^sup>\<dagger> = (?X\<^sup>\<dagger>) * ?W" using dagger_of_prod[of "?W\<^sup>\<dagger>" ?X] Wdc Xc
          by (simp add: dagger_of_dagger_is_id)
        have "(?Y\<^sup>\<dagger>) * ?Y = ((?X\<^sup>\<dagger>) * ?W) * ((?W\<^sup>\<dagger>) * ?X)" by (simp only: Yd)
        also have "\<dots> = (?X\<^sup>\<dagger>) * (?W * ((?W\<^sup>\<dagger>) * ?X))"
          by (rule assoc_mult_mat[OF dagger_carrier[OF Xc] Wc mult_carrier_mat[OF Wdc Xc]])
        also have "\<dots> = (?X\<^sup>\<dagger>) * (?W * (?W\<^sup>\<dagger>) * ?X)"
          by (simp only: assoc_mult_mat[OF Wc Wdc Xc, symmetric])
        finally show ?thesis .
      qed
      also have "\<dots> = 0\<^sub>m ?m ?m" unfolding WWX using dagger_carrier[OF Xc] by simp
      finally have YY: "(?Y\<^sup>\<dagger>) * ?Y = 0\<^sub>m ?m ?m" .
      show ?thesis by (rule dagger_mult_zero_imp_zero[OF Yc YY])
    qed
    \<comment> \<open>Hence \<open>X\<^sup>\<dagger> X = X\<^sup>\<dagger> W - X\<^sup>\<dagger> Q W = 0\<close>, as \<open>X\<^sup>\<dagger> W = (W\<^sup>\<dagger> X)\<^sup>\<dagger> = 0\<close> and \<open>X\<^sup>\<dagger> Q = (Q X)\<^sup>\<dagger>\<close> with \<open>Q X = V B (V\<^sup>\<dagger> X) = 0\<close>.\<close>
    have XdW: "(?X\<^sup>\<dagger>) * ?W = 0\<^sub>m ?m ?m"
    proof -
      have "(?X\<^sup>\<dagger>) * ?W = ((?W\<^sup>\<dagger>) * ?X)\<^sup>\<dagger>"
        using dagger_of_prod[of "?W\<^sup>\<dagger>" ?X] Wdc Xc by (simp add: dagger_of_dagger_is_id)
      also have "\<dots> = 0\<^sub>m ?m ?m" unfolding WdX by (rule eq_matI) (auto simp: dagger_def)
      finally show ?thesis .
    qed
    have QX: "?Q * ?X = 0\<^sub>m n ?m"
    proof -
      have "?Q * ?X = ?V * B * ((?V\<^sup>\<dagger>) * ?X)"
        by (rule assoc_mult_mat[OF mult_carrier_mat[OF Vc Bc] Vdc Xc])
      also have "\<dots> = 0\<^sub>m n ?m" unfolding VdX using Vc Bc by simp
      finally show ?thesis .
    qed
    have XdQW: "(?X\<^sup>\<dagger>) * (?Q * ?W) = 0\<^sub>m ?m ?m"
    proof -
      have Qh: "?Q\<^sup>\<dagger> = ?Q"
      proof -
        have "?Q\<^sup>\<dagger> = ((?V\<^sup>\<dagger>)\<^sup>\<dagger>) * ((?V * B)\<^sup>\<dagger>)"
          by (rule dagger_of_prod) (simp only: carrier_matD[OF mult_carrier_mat[OF Vc Bc]] carrier_matD[OF Vdc])
        also have "(?V * B)\<^sup>\<dagger> = (B\<^sup>\<dagger>) * (?V\<^sup>\<dagger>)"
          by (rule dagger_of_prod) (simp only: carrier_matD[OF Vc] carrier_matD[OF Bc])
        also have "(?V\<^sup>\<dagger>)\<^sup>\<dagger> = ?V" by (simp add: dagger_of_dagger_is_id)
        finally have F: "?Q\<^sup>\<dagger> = ?V * ((B\<^sup>\<dagger>) * (?V\<^sup>\<dagger>))" .
        show ?thesis unfolding F Bh by (rule assoc_mult_mat[OF Vc Bc Vdc, symmetric])
      qed
      have d1: "(?Q * ?X)\<^sup>\<dagger> = (?X\<^sup>\<dagger>) * (?Q\<^sup>\<dagger>)"
        by (rule dagger_of_prod) (simp only: carrier_matD[OF Qc] carrier_matD[OF Xc])
      have "(?X\<^sup>\<dagger>) * (?Q * ?W) = ((?X\<^sup>\<dagger>) * ?Q) * ?W"
        by (rule assoc_mult_mat[OF dagger_carrier[OF Xc] Qc Wc, symmetric])
      also have "(?X\<^sup>\<dagger>) * ?Q = (?Q * ?X)\<^sup>\<dagger>" unfolding d1 Qh ..
      also have "\<dots> = 0\<^sub>m ?m n" unfolding QX by (rule eq_matI) (auto simp: dagger_def)
      finally show ?thesis by (simp only: left_mult_zero_mat[OF Wc])
    qed
    have XX: "(?X\<^sup>\<dagger>) * ?X = 0\<^sub>m ?m ?m"
    proof -
      have "(?X\<^sup>\<dagger>) * ?X = (?X\<^sup>\<dagger>) * ?W - (?X\<^sup>\<dagger>) * (?Q * ?W)"
        by (rule mult_minus_distrib_mat[OF dagger_carrier[OF Xc] Wc mult_carrier_mat[OF Qc Wc]])
      thus ?thesis unfolding XdW XdQW by simp
    qed
    have "?X = 0\<^sub>m n ?m" by (rule dagger_mult_zero_imp_zero[OF Xc XX])
    hence X0: "?W - ?Q * ?W = 0\<^sub>m n ?m" .
    have "\<And>i j. i < n \<Longrightarrow> j < ?m \<Longrightarrow> (?Q * ?W) $$ (i,j) = ?W $$ (i,j)"
    proof -
      fix i j assume i: "i < n" and j: "j < ?m"
      have "(?W - ?Q * ?W) $$ (i,j) = ?W $$ (i,j) - (?Q * ?W) $$ (i,j)" using i j Wc Qc by simp
      thus "(?Q * ?W) $$ (i,j) = ?W $$ (i,j)" using X0 i j by simp
    qed
    thus ?thesis using Wc Qc by (intro eq_matI) auto
  qed
  \<comment> \<open>The coefficient matrix \<open>C = B V\<^sup>\<dagger> W\<close> (\<open>r \<times> m\<close>); \<open>U = C\<^sup>t\<close>.\<close>
  let ?C = "B * (?V\<^sup>\<dagger> * ?W)"
  have Cc: "?C \<in> carrier_mat ?r ?m" using Bc Vdc Wc by auto
  define U where "U = transpose_mat ?C"
  have Uc: "U \<in> carrier_mat ?m ?r" using Cc by (simp add: U_def)
  have UT: "transpose_mat U = ?C" by (simp add: U_def)
  have W_eq: "?W = ?V * transpose_mat U"
  proof -
    have "?V * transpose_mat U = ?V * B * ((?V\<^sup>\<dagger>) * ?W)" unfolding UT
      by (rule assoc_mult_mat[OF Vc Bc mult_carrier_mat[OF Vdc Wc], symmetric])
    also have "\<dots> = ?Q * ?W"
      by (rule assoc_mult_mat[OF mult_carrier_mat[OF Vc Bc] Vdc Wc, symmetric])
    also have "\<dots> = ?W" by (rule QW)
    finally show ?thesis ..
  qed
  have CC: "?C * (?C\<^sup>\<dagger>) = 1\<^sub>m ?r"
  proof -
    have Cd: "?C\<^sup>\<dagger> = (?W\<^sup>\<dagger>) * ?V * B"
    proof -
      have "?C\<^sup>\<dagger> = (((?V\<^sup>\<dagger>) * ?W)\<^sup>\<dagger>) * (B\<^sup>\<dagger>)"
        by (rule dagger_of_prod) (simp only: carrier_matD[OF Bc] carrier_matD[OF mult_carrier_mat[OF Vdc Wc]])
      also have "((?V\<^sup>\<dagger>) * ?W)\<^sup>\<dagger> = (?W\<^sup>\<dagger>) * ((?V\<^sup>\<dagger>)\<^sup>\<dagger>)"
        by (rule dagger_of_prod) (simp only: carrier_matD[OF Vdc] carrier_matD[OF Wc])
      also have "(?V\<^sup>\<dagger>)\<^sup>\<dagger> = ?V" by (simp add: dagger_of_dagger_is_id)
      finally show ?thesis unfolding Bh .
    qed
    let ?Vd = "?V\<^sup>\<dagger>" and ?Wd = "?W\<^sup>\<dagger>"
    have "?C * (?C\<^sup>\<dagger>) = (B * (?Vd * ?W)) * ((?Wd * ?V) * B)" unfolding Cd ..
    also have "\<dots> = B * ((?Vd * ?W) * ((?Wd * ?V) * B))"
      by (rule assoc_mult_mat[OF Bc mult_carrier_mat[OF Vdc Wc] mult_carrier_mat[OF mult_carrier_mat[OF Wdc Vc] Bc]])
    also have "\<dots> = B * (?Vd * (?W * ((?Wd * ?V) * B)))"
      by (simp only: assoc_mult_mat[OF Vdc Wc mult_carrier_mat[OF mult_carrier_mat[OF Wdc Vc] Bc]])
    also have "\<dots> = B * (?Vd * (?W * (?Wd * (?V * B))))"
      by (simp only: assoc_mult_mat[OF Wdc Vc Bc])
    also have "\<dots> = B * (?Vd * ((?W * ?Wd) * (?V * B)))"
      by (simp only: assoc_mult_mat[OF Wc Wdc mult_carrier_mat[OF Vc Bc], symmetric])
    also have "\<dots> = B * (?Vd * ((?V * ?Vd) * (?V * B)))" by (simp only: VV[symmetric])
    also have "\<dots> = B * (?Vd * (?V * (?Vd * (?V * B))))"
      by (simp only: assoc_mult_mat[OF Vc Vdc mult_carrier_mat[OF Vc Bc]])
    also have "\<dots> = B * ((?Vd * ?V) * (?Vd * (?V * B)))"
      by (simp only: assoc_mult_mat[OF Vdc Vc mult_carrier_mat[OF Vdc mult_carrier_mat[OF Vc Bc]], symmetric])
    also have "\<dots> = B * ((?Vd * ?V) * ((?Vd * ?V) * B))"
      by (simp only: assoc_mult_mat[OF Vdc Vc Bc, symmetric])
    also have "\<dots> = (B * ?G) * (?G * B)"
      by (rule assoc_mult_mat[OF Bc Gc mult_carrier_mat[OF Gc Bc], symmetric])
    also have "\<dots> = 1\<^sub>m ?r" unfolding BG GB by simp
    finally show ?thesis .
  qed
  have UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m ?r"
  proof (rule eq_matI)
    fix j k assume "j < dim_row (1\<^sub>m ?r :: complex Matrix.mat)" "k < dim_col (1\<^sub>m ?r :: complex Matrix.mat)"
    hence j: "j < ?r" and k: "k < ?r" by simp_all
    have "((U\<^sup>\<dagger>) * U) $$ (j,k) = (\<Sum>l<?m. cnj (?C $$ (j,l)) * ?C $$ (k,l))"
      using j k carrier_matD[OF Uc] carrier_matD[OF Cc] by (simp add: scalar_prod_def dagger_def U_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>l<?m. ?C $$ (k,l) * cnj (?C $$ (j,l)))" by (simp add: mult.commute)
    also have "\<dots> = (?C * (?C\<^sup>\<dagger>)) $$ (k,j)"
      using j k carrier_matD[OF Cc] by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
    also have "\<dots> = (1\<^sub>m ?r :: complex Matrix.mat) $$ (j,k)" unfolding CC using j k by auto
    finally show "((U\<^sup>\<dagger>) * U) $$ (j,k) = (1\<^sub>m ?r :: complex Matrix.mat) $$ (j,k)" .
  qed (use Uc in \<open>auto simp: dagger_def\<close>)
  show ?thesis using Uc UU W_eq by blast
qed

corollary rank_one_decomp_isometry_cols:
  assumes li: "lin_indep_vecs n vs"
      and wsd: "\<forall>w \<in> set ws. dim_vec w = n"
      and same: "outer_sum n vs = outer_sum n ws"
  shows "\<exists>U :: complex Matrix.mat. U \<in> carrier_mat (length ws) (length vs) \<and>
           (U\<^sup>\<dagger>) * U = 1\<^sub>m (length vs) \<and>
           (\<forall>l < length ws. ws ! l = mat_of_cols n vs *\<^sub>v Matrix.row U l)"
proof -
  obtain U :: "complex Matrix.mat" where Uc: "U \<in> carrier_mat (length ws) (length vs)"
    and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m (length vs)"
    and W_eq: "mat_of_cols n ws = mat_of_cols n vs * transpose_mat U"
    using rank_one_decomp_isometry[OF li wsd same] by blast
  have Vc: "mat_of_cols n vs \<in> carrier_mat n (length vs)" by simp
  have Tc: "transpose_mat U \<in> carrier_mat (length vs) (length ws)" using Uc by simp
  have "\<And>l. l < length ws \<Longrightarrow> ws ! l = mat_of_cols n vs *\<^sub>v Matrix.row U l"
  proof -
    fix l assume l: "l < length ws"
    have wl: "ws ! l \<in> carrier_vec n" by (rule carrier_vecI[OF bspec[OF wsd nth_mem[OF l]]])
    have "ws ! l = Matrix.col (mat_of_cols n ws) l" by (rule col_mat_of_cols[OF l wl, symmetric])
    also have "\<dots> = mat_of_cols n vs *\<^sub>v Matrix.col (transpose_mat U) l"
      unfolding W_eq by (rule col_mult2[OF Vc Tc l])
    also have "Matrix.col (transpose_mat U) l = Matrix.row U l"
      by (rule col_transpose) (simp add: carrier_matD(1)[OF Uc] l)
    finally show "ws ! l = mat_of_cols n vs *\<^sub>v Matrix.row U l" .
  qed
  thus ?thesis using Uc UU by blast
qed

subsection \<open>D21-6 (Choi 2): unitary freedom of Kraus representations\<close>

lemma vec_of_kraus_mat_of_cols_index:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and dpos: "0 < d"
      and i: "i < d" and a: "a < n" and k: "k < length Vs"
  shows "mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) $$ (a*d + i, k) = Vs ! k $$ (i, a)"
proof -
  have lt: "a*d + i < n*d" using a i by (rule mult_index_lt)
  have "mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) $$ (a*d + i, k) = vec_of_kraus d n (Vs ! k) $ (a*d + i)"
    using lt k by (simp add: mat_of_cols_index)
  also have "\<dots> = Vs ! k $$ (i, a)"
    using vec_of_kraus_combined_index[of "Vs ! k" d n a i] Vs_c k a i dpos by simp
  finally show ?thesis .
qed

lemma lin_indep_complex_mat_vec_of_kraus:
  assumes li: "lin_indep_complex_mat d n Vs" and dpos: "0 < d"
  shows "lin_indep_vecs (n*d) (map (vec_of_kraus d n) Vs)"
proof (unfold lin_indep_vecs_def, intro conjI allI impI)
  show "\<forall>v \<in> set (map (vec_of_kraus d n) Vs). dim_vec v = n*d" by simp
next
  fix x :: "complex Matrix.vec"
  let ?M = "mat_of_cols (n*d) (map (vec_of_kraus d n) Vs)"
  assume xc: "x \<in> carrier_vec (length (map (vec_of_kraus d n) Vs))" and Mx: "?M *\<^sub>v x = 0\<^sub>v (n*d)"
  have Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" using li by (simp add: lin_indep_complex_mat_def)
  have xd: "dim_vec x = length Vs" using xc by simp
  let ?f = "\<lambda>k. x $ k \<cdot>\<^sub>m (Vs ! k)"
  have fc: "\<forall>k \<in> set [0..<length Vs]. ?f k \<in> carrier_mat d n" using Vs_c by auto
  have comb0: "foldr (\<lambda>k acc. x $ k \<cdot>\<^sub>m (Vs ! k) + acc) [0..<length Vs] (0\<^sub>m d n) = 0\<^sub>m d n"
  proof (rule eq_matI)
    fix i a assume "i < dim_row (0\<^sub>m d n :: complex Matrix.mat)" "a < dim_col (0\<^sub>m d n :: complex Matrix.mat)"
    hence i: "i < d" and a: "a < n" by simp_all
    have lt: "a*d + i < n*d" using a i by (rule mult_index_lt)
    have "foldr (\<lambda>k acc. ?f k + acc) [0..<length Vs] (0\<^sub>m d n) $$ (i,a)
            = sum_list (map (\<lambda>k. ?f k $$ (i,a)) [0..<length Vs])"
      by (rule foldr_add_mat_index_rect[OF fc i a])
    also have "\<dots> = (\<Sum>k<length Vs. (x $ k \<cdot>\<^sub>m Vs ! k) $$ (i,a))"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>k<length Vs. x $ k * Vs ! k $$ (i,a))"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {..<length Vs}"
      hence Vk: "Vs ! k \<in> carrier_mat d n" using Vs_c nth_mem[of k Vs] by auto
      show "(x $ k \<cdot>\<^sub>m Vs ! k) $$ (i,a) = x $ k * Vs ! k $$ (i,a)" using carrier_matD[OF Vk] i a by simp
    qed
    also have "\<dots> = (\<Sum>k<length Vs. ?M $$ (a*d + i, k) * x $ k)"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {..<length Vs}"
      hence k: "k < length Vs" by simp
      show "x $ k * Vs ! k $$ (i,a) = ?M $$ (a*d + i, k) * x $ k"
        unfolding vec_of_kraus_mat_of_cols_index[OF Vs_c dpos i a k] by (rule mult.commute)
    qed
    also have "\<dots> = (?M *\<^sub>v x) $ (a*d + i)" using lt xd by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = 0" using Mx lt by simp
    finally show "foldr (\<lambda>k acc. ?f k + acc) [0..<length Vs] (0\<^sub>m d n) $$ (i,a) = (0\<^sub>m d n :: complex Matrix.mat) $$ (i,a)"
      using i a by simp
  qed (use carrier_matD[OF foldr_add_mat_carrier_rect[OF fc]] in simp_all)
  have A: "\<forall>c :: nat \<Rightarrow> complex.
        foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (Vs!k) + acc) [0..<length Vs] (0\<^sub>m d n) = 0\<^sub>m d n \<longrightarrow> (\<forall>k < length Vs. c k = 0)"
    using li unfolding lin_indep_complex_mat_def by (rule conjunct2)
  have B: "\<And>k. k < length Vs \<Longrightarrow> x $ k = 0" using A[rule_format, of "\<lambda>k. x $ k", OF comb0] .
  have "\<forall>k < length Vs. x $ k = 0" using B by blast
  thus "x = 0\<^sub>v (length (map (vec_of_kraus d n) Vs))" using xd by (intro eq_vecI) auto
qed

text \<open>Choi's Theorem 2: if $\Phi(X)=\sum_{j<r}V_jXV_j^*=\sum_{l<m}W_lXW_l^*$ with $V_1,\dots,V_r$
linearly independent (the notes: $r=\mathrm{cr}(\Phi)$), then $W_l=\sum_j\alpha_{lj}V_j$ with
$U=(\alpha_{lj})$ an isometry, $U^*U=I_r$.\<close>

theorem choi_2_unitary_freedom:
  assumes npos: "0 < n" and dpos: "0 < d"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and li: "lin_indep_complex_mat d n Vs"
      and same: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim d Vs X = kraus_map_dim d Ws X"
  shows "\<exists>U :: complex Matrix.mat. U \<in> carrier_mat (length Ws) (length Vs) \<and>
           (U\<^sup>\<dagger>) * U = 1\<^sub>m (length Vs) \<and>
           (\<forall>l < length Ws. Ws ! l =
              foldr (\<lambda>j acc. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<length Vs] (0\<^sub>m d n))"
proof -
  let ?vs = "map (vec_of_kraus d n) Vs" and ?ws = "map (vec_of_kraus d n) Ws"
  let ?r = "length Vs" and ?m = "length Ws"
  have Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" using li by (simp add: lin_indep_complex_mat_def)
  have choi: "choi_matrix n d (kraus_map_dim d Vs) = choi_matrix n d (kraus_map_dim d Ws)"
    using same by (intro choi_matrix_cong) simp
  have os: "outer_sum (n*d) ?vs = outer_sum (n*d) ?ws"
    using choi choi_matrix_kraus_eq[OF Vs_c npos dpos] choi_matrix_kraus_eq[OF Ws_c npos dpos] by simp
  have lv: "lin_indep_vecs (n*d) ?vs" by (rule lin_indep_complex_mat_vec_of_kraus[OF li dpos])
  have wsd: "\<forall>w \<in> set ?ws. dim_vec w = n*d" by simp
  obtain U :: "complex Matrix.mat" where Uc: "U \<in> carrier_mat ?m ?r"
    and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m ?r"
    and W_eq: "mat_of_cols (n*d) ?ws = mat_of_cols (n*d) ?vs * transpose_mat U"
    using rank_one_decomp_isometry[OF lv wsd os] by auto
  have Mv_c: "mat_of_cols (n*d) ?vs \<in> carrier_mat (n*d) ?r" using mat_of_cols_carrier[of "n*d" ?vs] by simp
  have Tc: "transpose_mat U \<in> carrier_mat ?r ?m" using Uc by simp
  have back_eq: "\<And>l. l < ?m \<Longrightarrow> Ws ! l = foldr (\<lambda>j acc. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<?r] (0\<^sub>m d n)"
  proof -
    fix l assume l: "l < ?m"
    have Wl_c: "Ws ! l \<in> carrier_mat d n" using Ws_c l by simp
    let ?f = "\<lambda>j. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)"
    have fc: "\<forall>j \<in> set [0..<?r]. ?f j \<in> carrier_mat d n" using Vs_c by auto
    show "Ws ! l = foldr (\<lambda>j acc. ?f j + acc) [0..<?r] (0\<^sub>m d n)"
    proof (rule eq_matI)
      fix i a assume "i < dim_row (foldr (\<lambda>j acc. ?f j + acc) [0..<?r] (0\<^sub>m d n))"
                     "a < dim_col (foldr (\<lambda>j acc. ?f j + acc) [0..<?r] (0\<^sub>m d n))"
      hence i: "i < d" and a: "a < n" using carrier_matD[OF foldr_add_mat_carrier_rect[OF fc]] by auto
      have lt: "a*d + i < n*d" using a i by (rule mult_index_lt)
      have "Ws ! l $$ (i,a) = mat_of_cols (n*d) ?ws $$ (a*d + i, l)"
        using vec_of_kraus_mat_of_cols_index[OF Ws_c dpos i a l] by simp
      also have "\<dots> = (mat_of_cols (n*d) ?vs * transpose_mat U) $$ (a*d + i, l)" unfolding W_eq ..
      also have "\<dots> = (\<Sum>j<?r. mat_of_cols (n*d) ?vs $$ (a*d + i, j) * U $$ (l,j))"
        using lt l carrier_matD[OF Uc] by (simp add: scalar_prod_def atLeast0LessThan)
      also have "\<dots> = (\<Sum>j<?r. U $$ (l,j) * Vs ! j $$ (i,a))"
      proof (intro sum.cong refl)
        fix j assume "j \<in> {..<?r}"
        hence j: "j < ?r" by simp
        show "mat_of_cols (n*d) ?vs $$ (a*d + i, j) * U $$ (l,j) = U $$ (l,j) * Vs ! j $$ (i,a)"
          unfolding vec_of_kraus_mat_of_cols_index[OF Vs_c dpos i a j] by (rule mult.commute)
      qed
      also have "\<dots> = (\<Sum>j<?r. ?f j $$ (i,a))"
      proof (intro sum.cong refl)
        fix j assume "j \<in> {..<?r}"
        hence Vj: "Vs ! j \<in> carrier_mat d n" using Vs_c nth_mem[of j Vs] by auto
        show "U $$ (l,j) * Vs ! j $$ (i,a) = ?f j $$ (i,a)" using carrier_matD[OF Vj] i a by simp
      qed
      also have "\<dots> = sum_list (map (\<lambda>j. ?f j $$ (i,a)) [0..<?r])"
        by (simp add: sum_list_sum_nth atLeast0LessThan)
      also have "\<dots> = foldr (\<lambda>j acc. ?f j + acc) [0..<?r] (0\<^sub>m d n) $$ (i,a)"
        by (rule foldr_add_mat_index_rect[OF fc i a, symmetric])
      finally show "Ws ! l $$ (i,a) = foldr (\<lambda>j acc. ?f j + acc) [0..<?r] (0\<^sub>m d n) $$ (i,a)" .
    qed (use Wl_c foldr_add_mat_carrier_rect[OF fc] in auto)
  qed
  show ?thesis using Uc UU back_eq by blast
qed

end
