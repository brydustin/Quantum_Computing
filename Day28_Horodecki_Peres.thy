theory Day28_Horodecki_Peres
  imports QC_Prelims
begin

section \<open>Day 28: the Horodecki--Peres criterion for two qubits (D28-5)\<close>

text \<open>Entries of the partial transpose $\Phi^{(2)}(X)$ of a $4\times4$ matrix.\<close>

lemma partial_transpose_2_index:
  fixes M :: "complex Matrix.mat"
  assumes i: "i < 4" and j: "j < 4"
  shows "amplification 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) M $$ (i,j)
         = M $$ ((i div 2) * 2 + j mod 2, (j div 2) * 2 + i mod 2)"
proof -
  have "amplification 2 2 2 transpose_mat M $$ (i,j)
        = transpose_mat (block_of_mat 2 M (i div 2) (j div 2)) $$ (i mod 2, j mod 2)"
    using i j by (simp add: amplification_def)
  also have "\<dots> = block_of_mat 2 M (i div 2) (j div 2) $$ (j mod 2, i mod 2)"
    by (simp add: block_of_mat_def)
  also have "\<dots> = M $$ ((i div 2) * 2 + j mod 2, (j div 2) * 2 + i mod 2)"
    by (simp add: block_of_mat_def)
  finally show ?thesis .
qed

lemma product_vec_iff_det_zero:
  fixes v :: "complex Matrix.vec"
  assumes vd: "dim_vec v = 4"
  shows "(\<exists>\<alpha> \<beta>. dim_vec \<alpha> = 2 \<and> dim_vec \<beta> = 2 \<and> v = tensor_vec \<alpha> \<beta>)
         \<longleftrightarrow> v $ 0 * v $ 3 - v $ 1 * v $ 2 = 0"
proof
  assume "\<exists>\<alpha> \<beta>. dim_vec \<alpha> = 2 \<and> dim_vec \<beta> = 2 \<and> v = tensor_vec \<alpha> \<beta>"
  then obtain \<alpha> \<beta> where ad: "dim_vec \<alpha> = 2" and bd: "dim_vec \<beta> = 2" and v: "v = tensor_vec \<alpha> \<beta>" by blast
  have e: "\<And>k. k < 4 \<Longrightarrow> v $ k = \<alpha> $ (k div 2) * \<beta> $ (k mod 2)"
    unfolding v using tensor_vec_index[OF ad bd] by simp
  show "v $ 0 * v $ 3 - v $ 1 * v $ 2 = 0" using e[of 0] e[of 1] e[of 2] e[of 3] by simp
next
  assume det0: "v $ 0 * v $ 3 - v $ 1 * v $ 2 = 0"
  let ?a = "v $ 0" and ?b = "v $ 1" and ?c = "v $ 2" and ?d = "v $ 3"
  have idx: "\<And>k :: nat. k < 4 \<Longrightarrow> k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3" by auto
  show "\<exists>\<alpha> \<beta>. dim_vec \<alpha> = 2 \<and> dim_vec \<beta> = 2 \<and> v = tensor_vec \<alpha> \<beta>"
  proof (cases "?a = 0")
    case False
    let ?\<alpha> = "Matrix.vec 2 (\<lambda>k. if k = 0 then 1 else ?c / ?a)"
    let ?\<beta> = "Matrix.vec 2 (\<lambda>k. if k = 0 then ?a else ?b)"
    have "v = tensor_vec ?\<alpha> ?\<beta>"
    proof (rule eq_vecI)
      fix k assume "k < dim_vec (tensor_vec ?\<alpha> ?\<beta>)"
      hence k: "k < 4" by (simp add: tensor_vec_dim)
      have d: "?d = ?b * ?c / ?a" using det0 False by (simp add: field_simps)
      show "v $ k = tensor_vec ?\<alpha> ?\<beta> $ k"
        using tensor_vec_index[of ?\<alpha> 2 ?\<beta> 2 k] k idx[OF k] d False by auto
    qed (simp add: vd tensor_vec_dim)
    thus ?thesis by (intro exI[of _ ?\<alpha>] exI[of _ ?\<beta>]) simp
  next
    case True
    hence bc: "?b = 0 \<or> ?c = 0" using det0 by simp
    show ?thesis
    proof (cases "?b = 0")
      case True
      \<comment> \<open>$v=(0,0,c,d)=e_1\otimes(c,d)$\<close>
      let ?\<alpha> = "Matrix.vec 2 (\<lambda>k. if k = 0 then 0 else 1) :: complex Matrix.vec"
      let ?\<beta> = "Matrix.vec 2 (\<lambda>k. if k = 0 then ?c else ?d)"
      have "v = tensor_vec ?\<alpha> ?\<beta>"
      proof (rule eq_vecI)
        fix k assume "k < dim_vec (tensor_vec ?\<alpha> ?\<beta>)"
        hence k: "k < 4" by (simp add: tensor_vec_dim)
        show "v $ k = tensor_vec ?\<alpha> ?\<beta> $ k"
          using tensor_vec_index[of ?\<alpha> 2 ?\<beta> 2 k] k idx[OF k] \<open>?a = 0\<close> True by auto
      qed (simp add: vd tensor_vec_dim)
      thus ?thesis by (intro exI[of _ ?\<alpha>] exI[of _ ?\<beta>]) simp
    next
      case False
      hence c0: "?c = 0" using bc by simp
      \<comment> \<open>$v=(0,b,0,d)=(b,d)\otimes e_1$\<close>
      let ?\<alpha> = "Matrix.vec 2 (\<lambda>k. if k = 0 then ?b else ?d)"
      let ?\<beta> = "Matrix.vec 2 (\<lambda>k. if k = 0 then 0 else 1) :: complex Matrix.vec"
      have "v = tensor_vec ?\<alpha> ?\<beta>"
      proof (rule eq_vecI)
        fix k assume "k < dim_vec (tensor_vec ?\<alpha> ?\<beta>)"
        hence k: "k < 4" by (simp add: tensor_vec_dim)
        show "v $ k = tensor_vec ?\<alpha> ?\<beta> $ k"
          using tensor_vec_index[of ?\<alpha> 2 ?\<beta> 2 k] k idx[OF k] \<open>?a = 0\<close> c0 by auto
      qed (simp add: vd tensor_vec_dim)
      thus ?thesis by (intro exI[of _ ?\<alpha>] exI[of _ ?\<beta>]) simp
    qed
  qed
qed

text \<open>The notes' witness $w=(-\overline{v_2},\overline{v_1})$ gives
$\langle w|\Phi^{(2)}(|v\rangle\langle v|)w\rangle=-2|v_0v_3-v_1v_2|^2$
($=2|\langle v_2|v_1\rangle|^2-2\|v_1\|^2\|v_2\|^2$ by Lagrange's identity).\<close>

lemma partial_transpose_witness_value:
  fixes v :: "complex Matrix.vec"
  assumes vd: "dim_vec v = 4"
  defines "w \<equiv> Matrix.vec 4 (\<lambda>k. if k = 0 then - cnj (v $ 2) else if k = 1 then - cnj (v $ 3)
                                    else if k = 2 then cnj (v $ 0) else cnj (v $ 1))"
  shows "\<langle>w | amplification 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) (v \<oslash> v) *\<^sub>v w\<rangle>
         = - 2 * cnj (v $ 0 * v $ 3 - v $ 1 * v $ 2) * (v $ 0 * v $ 3 - v $ 1 * v $ 2)"
proof -
  let ?Y = "amplification 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) (v \<oslash> v)"
  have Yc: "?Y \<in> carrier_mat 4 4" by (simp add: amplification_def)
  have wd: "dim_vec w = 4" by (simp add: w_def)
  have Yent: "\<And>i j :: nat. i < 4 \<Longrightarrow> j < 4 \<Longrightarrow>
      ?Y $$ (i,j) = v $ ((i div 2) * 2 + j mod 2) * cnj (v $ ((j div 2) * 2 + i mod 2))"
  proof -
    fix i j :: nat assume i: "i < 4" and j: "j < 4"
    have "?Y $$ (i,j) = (v \<oslash> v) $$ ((i div 2) * 2 + j mod 2, (j div 2) * 2 + i mod 2)"
      by (rule partial_transpose_2_index[OF i j])
    also have "\<dots> = v $ ((i div 2) * 2 + j mod 2) * cnj (v $ ((j div 2) * 2 + i mod 2))"
      using i j vd by (intro outer_prod_index) (auto dest!: set_4_disj)
    finally show "?Y $$ (i,j) = v $ ((i div 2) * 2 + j mod 2) * cnj (v $ ((j div 2) * 2 + i mod 2))" .
  qed
  \<comment> \<open>Name the four entries: simp diverges on goals with many distinct \<open>v $ k\<close> subterms.\<close>
  define a b c d where abcd: "a = v $ 0" "b = v $ 1" "c = v $ 2" "d = v $ 3"
  define \<delta> where "\<delta> = a * d - b * c"
  define u :: "complex Matrix.vec" where
    "u = Matrix.vec 4 (\<lambda>k. if k = 0 then - b else if k = 1 then a else if k = 2 then - d else c)"
  have s4: "{0..<(4::nat)} = {0,1,2,3}" by auto
  have sum4: "\<And>f :: nat \<Rightarrow> complex. (\<Sum>j\<in>{0,1,2,3}. f j) = f 0 + f 1 + f 2 + f 3"
    by (simp add: add.assoc)
  have Y00: "?Y $$ (0,0) = a * cnj a" using Yent[of 0 0] by (simp add: abcd)
  have Y01: "?Y $$ (0,1) = b * cnj a" using Yent[of 0 1] by (simp add: abcd)
  have Y02: "?Y $$ (0,2) = a * cnj c" using Yent[of 0 2] by (simp add: abcd)
  have Y03: "?Y $$ (0,3) = b * cnj c" using Yent[of 0 3] by (simp add: abcd)
  have Y10: "?Y $$ (1,0) = a * cnj b" using Yent[of 1 0] by (simp add: abcd)
  have Y11: "?Y $$ (1,1) = b * cnj b" using Yent[of 1 1] by (simp add: abcd)
  have Y12: "?Y $$ (1,2) = a * cnj d" using Yent[of 1 2] by (simp add: abcd)
  have Y13: "?Y $$ (1,3) = b * cnj d" using Yent[of 1 3] by (simp add: abcd)
  have Y20: "?Y $$ (2,0) = c * cnj a" using Yent[of 2 0] by (simp add: abcd)
  have Y21: "?Y $$ (2,1) = d * cnj a" using Yent[of 2 1] by (simp add: abcd)
  have Y22: "?Y $$ (2,2) = c * cnj c" using Yent[of 2 2] by (simp add: abcd)
  have Y23: "?Y $$ (2,3) = d * cnj c" using Yent[of 2 3] by (simp add: abcd)
  have Y30: "?Y $$ (3,0) = c * cnj b" using Yent[of 3 0] by (simp add: abcd)
  have Y31: "?Y $$ (3,1) = d * cnj b" using Yent[of 3 1] by (simp add: abcd)
  have Y32: "?Y $$ (3,2) = c * cnj d" using Yent[of 3 2] by (simp add: abcd)
  have Y33: "?Y $$ (3,3) = d * cnj d" using Yent[of 3 3] by (simp add: abcd)
  have w0: "w $ 0 = - cnj c" by (simp add: w_def abcd)
  have w1: "w $ 1 = - cnj d" by (simp add: w_def abcd)
  have w2: "w $ 2 = cnj a" by (simp add: w_def abcd)
  have w3: "w $ 3 = cnj b" by (simp add: w_def abcd)
  have u0: "u $ 0 = - b" by (simp add: u_def)
  have u1: "u $ 1 = a" by (simp add: u_def)
  have u2: "u $ 2 = - d" by (simp add: u_def)
  have u3: "u $ 3 = c" by (simp add: u_def)
  have r0: "(\<Sum>j\<in>{0,1,2,3}. ?Y $$ (0,j) * w $ j) = cnj \<delta> * u $ 0"
    unfolding sum4 Y00 Y01 Y02 Y03 w0 w1 w2 w3 u0 \<delta>_def by (simp add: algebra_simps)
  have r1: "(\<Sum>j\<in>{0,1,2,3}. ?Y $$ (1,j) * w $ j) = cnj \<delta> * u $ 1"
    unfolding sum4 Y10 Y11 Y12 Y13 w0 w1 w2 w3 u1 \<delta>_def by (simp add: algebra_simps)
  have r2: "(\<Sum>j\<in>{0,1,2,3}. ?Y $$ (2,j) * w $ j) = cnj \<delta> * u $ 2"
    unfolding sum4 Y20 Y21 Y22 Y23 w0 w1 w2 w3 u2 \<delta>_def by (simp add: algebra_simps)
  have r3: "(\<Sum>j\<in>{0,1,2,3}. ?Y $$ (3,j) * w $ j) = cnj \<delta> * u $ 3"
    unfolding sum4 Y30 Y31 Y32 Y33 w0 w1 w2 w3 u3 \<delta>_def by (simp add: algebra_simps)
  \<comment> \<open>\<open>Y w = cnj \<delta> \<cdot> (-b, a, -d, c)\<close>, entry by entry\<close>
  have Yw: "?Y *\<^sub>v w = cnj \<delta> \<cdot>\<^sub>v u"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (cnj \<delta> \<cdot>\<^sub>v u)"
    hence i: "i < 4" by (simp add: u_def)
    have "(?Y *\<^sub>v w) $ i = (\<Sum>j\<in>{0,1,2,3}. ?Y $$ (i,j) * w $ j)"
      using i Yc wd carrier_matD[OF Yc] by (simp add: scalar_prod_def s4)
    also have "\<dots> = cnj \<delta> * u $ i"
      using set_4_disj[OF i] r0 r1 r2 r3 by (elim disjE) simp_all
    finally show "(?Y *\<^sub>v w) $ i = (cnj \<delta> \<cdot>\<^sub>v u) $ i" using i by (simp add: u_def)
  qed (simp add: u_def Yc[THEN carrier_matD(1)])
  have "\<langle>w | ?Y *\<^sub>v w\<rangle> = cnj \<delta> * \<langle>w | u\<rangle>" unfolding Yw by (rule inner_prod_right_smult')
  also have "\<langle>w | u\<rangle> = (\<Sum>i\<in>{0,1,2,3}. cnj (w $ i) * u $ i)"
    using inner_prod_sum[of w 4 u] wd by (simp add: u_def s4)
  also have "\<dots> = - (\<delta> + \<delta>)"
    unfolding sum4 w0 w1 w2 w3 u0 u1 u2 u3 \<delta>_def by (simp add: algebra_simps)
  finally have "\<langle>w | ?Y *\<^sub>v w\<rangle> = cnj \<delta> * (- (\<delta> + \<delta>))" .
  also have "\<dots> = - 2 * cnj \<delta> * \<delta>" by (simp add: algebra_simps)
  finally show ?thesis unfolding \<delta>_def abcd .
qed

theorem horodecki_peres_two_qubits:
  fixes v :: "complex Matrix.vec"
  assumes vd: "dim_vec v = 4"
  shows "psd (amplification 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) (v \<oslash> v))
         \<longleftrightarrow> (\<exists>\<alpha> \<beta>. dim_vec \<alpha> = 2 \<and> dim_vec \<beta> = 2 \<and> v = tensor_vec \<alpha> \<beta>)"
proof
  let ?Y = "amplification 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) (v \<oslash> v)"
  have Yc: "?Y \<in> carrier_mat 4 4" by (simp add: amplification_def)
  assume pos: "psd ?Y"
  define w where "w = Matrix.vec 4 (\<lambda>k. if k = 0 then - cnj (v $ 2) else if k = 1 then - cnj (v $ 3)
                                    else if k = 2 then cnj (v $ 0) else cnj (v $ 1))"
  have wd: "dim_vec w = 4" by (simp add: w_def)
  let ?\<delta> = "v $ 0 * v $ 3 - v $ 1 * v $ 2"
  have val: "\<langle>w | ?Y *\<^sub>v w\<rangle> = - 2 * cnj ?\<delta> * ?\<delta>"
    unfolding w_def by (rule partial_transpose_witness_value[OF vd])
  have "0 \<le> Re (\<langle>w | ?Y *\<^sub>v w\<rangle>)" using pos Yc wd by (simp add: psd_def)
  moreover have val': "\<langle>w | ?Y *\<^sub>v w\<rangle> = complex_of_real (- 2 * (cmod ?\<delta>)\<^sup>2)"
  proof -
    have "- 2 * cnj ?\<delta> * ?\<delta> = - 2 * (cnj ?\<delta> * ?\<delta>)" by (simp only: mult_ac(1))
    also have "cnj ?\<delta> * ?\<delta> = complex_of_real ((cmod ?\<delta>)\<^sup>2)" by (rule cnj_mult_self_cmod)
    also have "- 2 * complex_of_real ((cmod ?\<delta>)\<^sup>2) = complex_of_real (- 2 * (cmod ?\<delta>)\<^sup>2)" by simp
    finally show ?thesis unfolding val .
  qed
  ultimately have "0 \<le> - 2 * (cmod ?\<delta>)\<^sup>2" by simp
  hence "(cmod ?\<delta>)\<^sup>2 \<le> 0" by simp
  hence "(cmod ?\<delta>)\<^sup>2 = 0" using zero_le_power2[of "cmod ?\<delta>"] by (rule order_antisym)
  hence "cmod ?\<delta> = 0" by simp
  hence "?\<delta> = 0" by simp
  thus "\<exists>\<alpha> \<beta>. dim_vec \<alpha> = 2 \<and> dim_vec \<beta> = 2 \<and> v = tensor_vec \<alpha> \<beta>"
    using product_vec_iff_det_zero[OF vd] by simp
next
  assume "\<exists>\<alpha> \<beta>. dim_vec \<alpha> = 2 \<and> dim_vec \<beta> = 2 \<and> v = tensor_vec \<alpha> \<beta>"
  then obtain \<alpha> \<beta> where ad: "dim_vec \<alpha> = 2" and bd: "dim_vec \<beta> = 2" and v: "v = tensor_vec \<alpha> \<beta>" by blast
  let ?Y = "amplification 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) (v \<oslash> v)"
  have Yc: "?Y \<in> carrier_mat 4 4" by (simp add: amplification_def)
  define \<beta>' where "\<beta>' = Matrix.vec 2 (\<lambda>k. cnj (\<beta> $ k))"
  let ?u = "tensor_vec \<alpha> \<beta>'"
  have b'd: "dim_vec \<beta>' = 2" by (simp add: \<beta>'_def)
  have ud: "dim_vec ?u = 4" using ad b'd by (simp add: tensor_vec_dim)
  have e: "\<And>k. k < 4 \<Longrightarrow> v $ k = \<alpha> $ (k div 2) * \<beta> $ (k mod 2)"
    unfolding v using tensor_vec_index[OF ad bd] by simp
  have eu: "\<And>k. k < 4 \<Longrightarrow> ?u $ k = \<alpha> $ (k div 2) * cnj (\<beta> $ (k mod 2))"
    using tensor_vec_index[OF ad b'd] by (simp add: \<beta>'_def)
  have "?Y = ?u \<oslash> ?u"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (?u \<oslash> ?u)" "j < dim_col (?u \<oslash> ?u)"
    hence i: "i < 4" and j: "j < 4" using carrier_matD[OF outer_prod_carrier[OF ud ud]] by auto
    have p: "(i div 2) * 2 + j mod 2 < 4" using set_4_disj[OF i] set_4_disj[OF j] by (elim disjE) simp_all
    have q: "(j div 2) * 2 + i mod 2 < 4" using set_4_disj[OF i] set_4_disj[OF j] by (elim disjE) simp_all
    have "?Y $$ (i,j) = (v \<oslash> v) $$ ((i div 2) * 2 + j mod 2, (j div 2) * 2 + i mod 2)"
      by (rule partial_transpose_2_index[OF i j])
    also have "\<dots> = v $ ((i div 2) * 2 + j mod 2) * cnj (v $ ((j div 2) * 2 + i mod 2))"
      using p q vd by (intro outer_prod_index) auto
    also have "\<dots> = \<alpha> $ (i div 2) * \<beta> $ (j mod 2) * cnj (\<alpha> $ (j div 2) * \<beta> $ (i mod 2))"
      using e[OF p] e[OF q] i j by simp
    also have "\<dots> = ?u $ i * cnj (?u $ j)"
      using eu[OF i] eu[OF j] by simp
    also have "\<dots> = (?u \<oslash> ?u) $$ (i,j)"
      using i j ud by (intro outer_prod_index[symmetric]) auto
    finally show "?Y $$ (i,j) = (?u \<oslash> ?u) $$ (i,j)" .
  next
    show "dim_row ?Y = dim_row (?u \<oslash> ?u)"
      using carrier_matD[OF Yc] carrier_matD[OF outer_prod_carrier[OF ud ud]] by simp
    show "dim_col ?Y = dim_col (?u \<oslash> ?u)"
      using carrier_matD[OF Yc] carrier_matD[OF outer_prod_carrier[OF ud ud]] by simp
  qed
  thus "psd ?Y" using outer_prod_self_psd[OF ud] by simp
qed

corollary horodecki_peres_entangled:
  fixes v :: "complex Matrix.vec"
  assumes vd: "dim_vec v = 4"
  shows "entangled 2 2 v \<longleftrightarrow>
         \<not> psd (amplification 2 2 2 (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) (v \<oslash> v))"
  using horodecki_peres_two_qubits[OF vd] vd by (simp add: entangled_def)

end
