theory Day34_Knill_Laflamme
  imports Day22_Minimal_Kraus Quantum_Channels
begin

section \<open>Day 34: the Knill--Laflamme conditions (D34-1, D34-2, D34-3)\<close>

subsection \<open>Vectors in the range of a projection; rank-one decompositions inside $V$\<close>

lemma projection_fixed_of_orth_kernel:
  assumes P: "projection n P" and vd: "dim_vec v = n"
      and orth: "\<And>x. dim_vec x = n \<Longrightarrow> P *\<^sub>v x = 0\<^sub>v n \<Longrightarrow> \<langle>v | x\<rangle> = 0"
  shows "P *\<^sub>v v = v"
proof -
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" and PP: "P * P = P"
    using P by (auto simp: projection_def hermitian_def)
  let ?x = "v - P *\<^sub>v v"
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF vd])
  have Pvd: "dim_vec (P *\<^sub>v v) = n" using carrier_matD(1)[OF Pc] by simp
  have xd: "dim_vec ?x = n" using vd carrier_matD(1)[OF Pc] by simp
  have Px: "P *\<^sub>v ?x = 0\<^sub>v n"
  proof -
    have "P *\<^sub>v ?x = P *\<^sub>v v - P *\<^sub>v (P *\<^sub>v v)" using Pc vc Pvd by (simp add: mult_minus_distrib_mat_vec)
    also have "P *\<^sub>v (P *\<^sub>v v) = P *\<^sub>v v" using projection_fixes_range[OF P vd] .
    finally show ?thesis using carrier_matD(1)[OF Pc] by (intro eq_vecI) auto
  qed
  have "\<langle>?x | ?x\<rangle> = \<langle>v | ?x\<rangle> - \<langle>P *\<^sub>v v | ?x\<rangle>"
    using inner_prod_left_minus'[of v "P *\<^sub>v v" ?x] vd Pvd by simp
  also have "\<langle>v | ?x\<rangle> = 0" by (rule orth[OF xd Px])
  also have "\<langle>P *\<^sub>v v | ?x\<rangle> = \<langle>v | P *\<^sub>v ?x\<rangle>"
    using inner_prod_adjoint_swap[OF Pc vd xd] Ph by simp
  also have "\<dots> = 0" unfolding Px using inner_prod_sum[of v n "0\<^sub>v n"] vd by simp
  finally have "\<langle>?x | ?x\<rangle> = 0" by simp
  hence x0: "?x = 0\<^sub>v n" using inner_prod_self_eq_zero_iff[of ?x] xd by simp
  have "\<And>i. i < n \<Longrightarrow> v $ i = (P *\<^sub>v v) $ i"
  proof -
    fix i assume i: "i < n"
    have "(v - P *\<^sub>v v) $ i = v $ i - (P *\<^sub>v v) $ i" using i Pvd by simp
    thus "v $ i = (P *\<^sub>v v) $ i" using x0 i by simp
  qed
  thus ?thesis using vd Pvd by (intro eq_vecI) auto
qed

lemma outer_sum_Nil: "outer_sum n [] = 0\<^sub>m n n"
  by (rule eq_matI) (auto simp: outer_sum_def scalar_prod_def)

lemma outer_sum_singleton_eq:
  assumes vd: "dim_vec v = n"
  shows "outer_sum n [v] = v \<oslash> v"
proof (rule eq_matI)
  have c: "v \<oslash> v \<in> carrier_mat n n" by (rule outer_prod_carrier[OF vd vd])
  fix i j assume "i < dim_row (v \<oslash> v)" "j < dim_col (v \<oslash> v)"
  hence i: "i < n" and j: "j < n" using carrier_matD[OF c] by auto
  show "outer_sum n [v] $$ (i,j) = (v \<oslash> v) $$ (i,j)"
    unfolding outer_sum_singleton_index[OF i j] using i j vd by (simp add: outer_prod_index)
qed (use carrier_matD[OF outer_prod_carrier[OF vd vd]] in auto)

lemma outer_sum_as_foldr:
  assumes "\<forall>v \<in> set vs. dim_vec v = n"
  shows "outer_sum n vs = foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)"
  using assms
proof (induction vs)
  case Nil show ?case by (simp add: outer_sum_Nil)
next
  case (Cons v vs)
  have "outer_sum n (v # vs) = outer_sum n [v] + outer_sum n vs"
    using Cons.prems by (intro outer_sum_Cons_split) simp
  also have "outer_sum n [v] = v \<oslash> v" using Cons.prems by (intro outer_sum_singleton_eq) simp
  finally show ?case using Cons by simp
qed

text \<open>For $X\ge0$ the matrix $PXP$ is a sum of $|\psi_l\rangle\langle\psi_l|$ with $\psi_l\in V$
(the notes: ``non-zero eigenvectors of $PXP$ are all in $V$'').\<close>

lemma psd_PXP_decomp_in_range:
  assumes P: "projection n P" and Xc: "M \<in> carrier_mat n n" and Xpsd: "psd M"
  shows "\<exists>vs :: complex Matrix.vec list. (\<forall>v \<in> set vs. dim_vec v = n \<and> P *\<^sub>v v = v) \<and>
           P * M * P = foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)"
proof -
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" using P by (auto simp: projection_def hermitian_def)
  let ?Y = "P * M * P"
  have Yc: "?Y \<in> carrier_mat n n" using Pc Xc by auto
  have Ypsd: "psd ?Y"
  proof -
    have "kraus_map_dim n [P] M = P * M * (P\<^sup>\<dagger>) + 0\<^sub>m n n" by simp
    also have "\<dots> = ?Y" unfolding Ph using Yc by simp
    finally show ?thesis using kraus_map_dim_psd[of "[P]" n n M] Pc Xc Xpsd by simp
  qed
  obtain vs :: "complex Matrix.vec list" where vsd: "\<forall>v \<in> set vs. dim_vec v = n" and Yvs: "outer_sum n vs = ?Y"
    using psd_kraus_decomp[OF Yc Ypsd] by blast
  have inV: "\<And>v. v \<in> set vs \<Longrightarrow> P *\<^sub>v v = v"
  proof -
    fix v assume v: "v \<in> set vs"
    then obtain l where l: "l < length vs" and vl: "v = vs ! l" by (metis in_set_conv_nth)
    show "P *\<^sub>v v = v"
    proof (rule projection_fixed_of_orth_kernel[OF P])
      show "dim_vec v = n" using vsd v by simp
    next
      fix x :: "complex Matrix.vec" assume xd: "dim_vec x = n" and Px: "P *\<^sub>v x = 0\<^sub>v n"
      have xc: "x \<in> carrier_vec n" by (rule carrier_vecI[OF xd])
      have "?Y *\<^sub>v x = P * M *\<^sub>v (P *\<^sub>v x)" by (rule assoc_mult_mat_vec[OF mult_carrier_mat[OF Pc Xc] Pc xc])
      also have "\<dots> = 0\<^sub>v n" unfolding Px by (rule mult_mat_vec_zero_vec[OF mult_carrier_mat[OF Pc Xc]])
      finally have Yx: "outer_sum n vs *\<^sub>v x = 0\<^sub>v n" unfolding Yvs .
      let ?M = "mat_of_cols n vs"
      have "\<langle>(?M\<^sup>\<dagger>) *\<^sub>v x | (?M\<^sup>\<dagger>) *\<^sub>v x\<rangle> = \<langle>x | outer_sum n vs *\<^sub>v x\<rangle>"
        by (rule inner_prod_outer_sum_general[OF xd vsd, symmetric])
      also have "\<dots> = 0" unfolding Yx using inner_prod_sum[of x n "0\<^sub>v n"] xd by simp
      finally have "(?M\<^sup>\<dagger>) *\<^sub>v x = 0\<^sub>v (length vs)"
        using inner_prod_self_eq_zero_iff[of "(?M\<^sup>\<dagger>) *\<^sub>v x"] by (simp add: dagger_def)
      hence "((?M\<^sup>\<dagger>) *\<^sub>v x) $ l = 0" using l by simp
      thus "\<langle>v | x\<rangle> = 0" unfolding vl using mat_of_cols_dagger_mult_vec_index[OF xd vsd l] by simp
    qed
  qed
  show ?thesis using vsd inV outer_sum_as_foldr[OF vsd] Yvs by (intro exI[of _ vs]) auto
qed

subsection \<open>Linearity facts for the composite map $\mathcal R\circ\mathbb E$\<close>


definition RE :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "RE n As Es M = kraus_map_dim n As (kraus_map_dim n Es M)"

lemma RE_carrier: assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and M: "M \<in> carrier_mat n n" shows "RE n As Es M \<in> carrier_mat n n"
  unfolding RE_def by (rule kraus_map_dim_carrier[OF As_c kraus_map_dim_carrier[OF Es_c M]])

lemma RE_add: assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and M: "M \<in> carrier_mat n n" and N: "N \<in> carrier_mat n n" shows "RE n As Es (M + N) = RE n As Es M + RE n As Es N"
  unfolding RE_def kraus_map_dim_add[OF M N Es_c]
  by (rule kraus_map_dim_add[OF kraus_map_dim_carrier[OF Es_c M] kraus_map_dim_carrier[OF Es_c N] As_c])

lemma RE_smult: assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and M: "M \<in> carrier_mat n n" shows "RE n As Es (c \<cdot>\<^sub>m M) = c \<cdot>\<^sub>m RE n As Es M"
  unfolding RE_def kraus_map_dim_smult[OF M Es_c]
  by (rule kraus_map_dim_smult[OF kraus_map_dim_carrier[OF Es_c M] As_c])

lemma RE_minus:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n"
      and Xc: "M \<in> carrier_mat n n" and Yc: "N \<in> carrier_mat n n"
  shows "RE n As Es (M - N) = RE n As Es M - RE n As Es N"
proof -
  have "M - N = M + (-1) \<cdot>\<^sub>m N" using Xc Yc by (intro eq_matI) auto
  hence "RE n As Es (M - N) = RE n As Es M + (-1) \<cdot>\<^sub>m RE n As Es N" using RE_add[OF As_c Es_c Xc] RE_smult[OF As_c Es_c Yc] Yc by simp
  thus ?thesis using RE_carrier[OF As_c Es_c Xc] RE_carrier[OF As_c Es_c Yc] by (intro eq_matI) auto
qed

lemma RE_foldr:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and "\<forall>v \<in> set vs. dim_vec v = n"
  shows "RE n As Es (foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)) = foldr (\<lambda>v acc. RE n As Es (v \<oslash> v) + acc) vs (0\<^sub>m n n)"
  using assms(3)
proof (induction vs)
  case Nil
  have "RE n As Es (0\<^sub>m n n) = 0\<^sub>m n n" unfolding RE_def using As_c Es_c by (simp add: kraus_map_dim_zero)
  thus ?case by simp
next
  case (Cons v vs)
  have vd: "dim_vec v = n" and rest: "\<forall>v \<in> set vs. dim_vec v = n" using Cons.prems by auto
  have rc: "foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n) \<in> carrier_mat n n"
    using rest by (induction vs) (auto simp: outer_prod_carrier)
  show ?case using RE_add[OF As_c Es_c outer_prod_carrier[OF vd vd] rc] Cons.IH[OF rest] by simp
qed

text \<open>D34-1: $\mathcal R\circ\mathbb E$ fixes $|\psi\rangle\langle\psi|$ for all $\psi\in V$ iff it
fixes $PXP$ for all $X$.\<close>

proposition recovery_states_iff_PXP:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and P: "projection n P"
  shows "(\<forall>\<psi>. dim_vec \<psi> = n \<longrightarrow> P *\<^sub>v \<psi> = \<psi> \<longrightarrow> RE n As Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>)
         \<longleftrightarrow> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> RE n As Es (P * X * P) = P * X * P)"
proof
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" using P by (auto simp: projection_def hermitian_def)
  assume H: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> RE n As Es (P * X * P) = P * X * P"
  show "\<forall>\<psi>. dim_vec \<psi> = n \<longrightarrow> P *\<^sub>v \<psi> = \<psi> \<longrightarrow> RE n As Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>"
  proof (intro allI impI)
    fix \<psi> :: "complex Matrix.vec" assume \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>"
    have "P * (\<psi> \<oslash> \<psi>) * P = (P *\<^sub>v \<psi>) \<oslash> (P *\<^sub>v \<psi>)"
      using conj_outer_prod[OF Pc \<psi>d] Ph by simp
    hence e: "P * (\<psi> \<oslash> \<psi>) * P = \<psi> \<oslash> \<psi>" unfolding \<psi>V .
    have "RE n As Es (P * (\<psi> \<oslash> \<psi>) * P) = P * (\<psi> \<oslash> \<psi>) * P"
      using H outer_prod_carrier[OF \<psi>d \<psi>d] by blast
    thus "RE n As Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>" unfolding e .
  qed
next
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" using P by (auto simp: projection_def hermitian_def)
  assume H: "\<forall>\<psi>. dim_vec \<psi> = n \<longrightarrow> P *\<^sub>v \<psi> = \<psi> \<longrightarrow> RE n As Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>"
  have psd_case: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> psd X \<Longrightarrow> RE n As Es (P * X * P) = P * X * P"
  proof -
    fix X :: "complex Matrix.mat" assume Xc: "X \<in> carrier_mat n n" and Xpsd: "psd X"
    obtain vs :: "complex Matrix.vec list" where vsV: "\<forall>v \<in> set vs. dim_vec v = n \<and> P *\<^sub>v v = v"
      and dec: "P * X * P = foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)"
      using psd_PXP_decomp_in_range[OF P Xc Xpsd] by blast
    have vsd: "\<forall>v \<in> set vs. dim_vec v = n" using vsV by simp
    have "RE n As Es (P * X * P) = foldr (\<lambda>v acc. RE n As Es (v \<oslash> v) + acc) vs (0\<^sub>m n n)"
      unfolding dec by (rule RE_foldr[OF As_c Es_c vsd])
    also have "\<dots> = foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)"
      by (rule foldr_add_mat_cong) (use H vsV in auto)
    finally show "RE n As Es (P * X * P) = P * X * P" unfolding dec .
  qed
  show "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> RE n As Es (P * X * P) = P * X * P"
  proof (intro allI impI)
    fix X :: "complex Matrix.mat" assume Xc: "X \<in> carrier_mat n n"
    obtain P1 P2 P3 P4 :: "complex Matrix.mat"
      where Ps: "\<forall>i \<in> {0..3}. [P1,P2,P3,P4] ! i \<in> carrier_mat n n \<and> psd ([P1,P2,P3,P4] ! i)"
        and Xd: "X = (P1 - P2) + \<i> \<cdot>\<^sub>m (P3 - P4)"
      using matrix_decomp_psd[OF Xc] by blast
    have P1: "P1 \<in> carrier_mat n n \<and> psd P1" using Ps[rule_format, of 0] by simp
    have P2: "P2 \<in> carrier_mat n n \<and> psd P2" using Ps[rule_format, of 1] by simp
    have P3: "P3 \<in> carrier_mat n n \<and> psd P3" using Ps[rule_format, of 2] by simp
    have P4: "P4 \<in> carrier_mat n n \<and> psd P4" using Ps[rule_format, of 3] by simp
    let ?c = "\<lambda>Y. P * Y * P"
    have cc: "\<And>Y. Y \<in> carrier_mat n n \<Longrightarrow> ?c Y \<in> carrier_mat n n" using Pc by auto
    have c_minus: "\<And>Y Z. Y \<in> carrier_mat n n \<Longrightarrow> Z \<in> carrier_mat n n \<Longrightarrow> ?c (Y - Z) = ?c Y - ?c Z"
    proof -
      fix Y Z :: "complex Matrix.mat" assume Yc: "Y \<in> carrier_mat n n" and Zc: "Z \<in> carrier_mat n n"
      have "P * (Y - Z) * P = (P * Y - P * Z) * P" by (simp only: mult_minus_distrib_mat[OF Pc Yc Zc])
      also have "\<dots> = P * Y * P - P * Z * P"
        by (rule minus_mult_distrib_mat[OF mult_carrier_mat[OF Pc Yc] mult_carrier_mat[OF Pc Zc] Pc])
      finally show "?c (Y - Z) = ?c Y - ?c Z" .
    qed
    have c_add: "\<And>Y Z. Y \<in> carrier_mat n n \<Longrightarrow> Z \<in> carrier_mat n n \<Longrightarrow> ?c (Y + Z) = ?c Y + ?c Z"
    proof -
      fix Y Z :: "complex Matrix.mat" assume Yc: "Y \<in> carrier_mat n n" and Zc: "Z \<in> carrier_mat n n"
      have "P * (Y + Z) * P = (P * Y + P * Z) * P" by (simp only: mult_add_distrib_mat[OF Pc Yc Zc])
      also have "\<dots> = P * Y * P + P * Z * P"
        by (rule add_mult_distrib_mat[OF mult_carrier_mat[OF Pc Yc] mult_carrier_mat[OF Pc Zc] Pc])
      finally show "?c (Y + Z) = ?c Y + ?c Z" .
    qed
    have c_smult: "\<And>Y c. Y \<in> carrier_mat n n \<Longrightarrow> ?c (c \<cdot>\<^sub>m Y) = c \<cdot>\<^sub>m ?c Y"
    proof -
      fix Y :: "complex Matrix.mat" and c :: complex assume Yc: "Y \<in> carrier_mat n n"
      show "?c (c \<cdot>\<^sub>m Y) = c \<cdot>\<^sub>m ?c Y"
        by (simp only: mult_smult_distrib[OF Pc Yc] mult_smult_assoc_mat[OF mult_carrier_mat[OF Pc Yc] Pc])
    qed
    have c12: "P1 - P2 \<in> carrier_mat n n" and c34: "P3 - P4 \<in> carrier_mat n n" using P1 P2 P3 P4 by auto
    have PXP: "?c X = (?c P1 - ?c P2) + \<i> \<cdot>\<^sub>m (?c P3 - ?c P4)"
      unfolding Xd using c_add[OF c12] c34 c_smult[OF c34] c_minus P1 P2 P3 P4 by simp
    have c1: "?c P1 \<in> carrier_mat n n" and c2: "?c P2 \<in> carrier_mat n n"
      and c3: "?c P3 \<in> carrier_mat n n" and c4: "?c P4 \<in> carrier_mat n n"
      using cc P1 P2 P3 P4 by blast+
    have "RE n As Es (?c X) = RE n As Es ((?c P1 - ?c P2) + \<i> \<cdot>\<^sub>m (?c P3 - ?c P4))" unfolding PXP ..
    also have "\<dots> = RE n As Es (?c P1 - ?c P2) + RE n As Es (\<i> \<cdot>\<^sub>m (?c P3 - ?c P4))"
      by (rule RE_add[OF As_c Es_c minus_carrier_mat[OF c2] smult_carrier_mat[OF minus_carrier_mat[OF c4]]])
    also have "RE n As Es (?c P1 - ?c P2) = RE n As Es (?c P1) - RE n As Es (?c P2)"
      by (rule RE_minus[OF As_c Es_c c1 c2])
    also have "RE n As Es (\<i> \<cdot>\<^sub>m (?c P3 - ?c P4)) = \<i> \<cdot>\<^sub>m RE n As Es (?c P3 - ?c P4)"
      by (rule RE_smult[OF As_c Es_c minus_carrier_mat[OF c4]])
    also have "RE n As Es (?c P3 - ?c P4) = RE n As Es (?c P3) - RE n As Es (?c P4)"
      by (rule RE_minus[OF As_c Es_c c3 c4])
    also have "(RE n As Es (?c P1) - RE n As Es (?c P2)) + \<i> \<cdot>\<^sub>m (RE n As Es (?c P3) - RE n As Es (?c P4))
               = (?c P1 - ?c P2) + \<i> \<cdot>\<^sub>m (?c P3 - ?c P4)"
      by (simp only: psd_case[OF conjunct1[OF P1] conjunct2[OF P1]] psd_case[OF conjunct1[OF P2] conjunct2[OF P2]]
                     psd_case[OF conjunct1[OF P3] conjunct2[OF P3]] psd_case[OF conjunct1[OF P4] conjunct2[OF P4]])
    finally show "RE n As Es (?c X) = ?c X" unfolding PXP .
  qed
qed

subsection \<open>Knill--Laflamme, Theorem 1, necessity: $PE_i^*E_jP=\alpha_{ij}P$\<close>

lemma lin_indep_complex_mat_single:
  assumes Pc: "P \<in> carrier_mat d n" and Pnz: "P \<noteq> 0\<^sub>m d n"
  shows "lin_indep_complex_mat d n [P]"
proof (unfold lin_indep_complex_mat_def, intro conjI allI impI)
  fix c :: "nat \<Rightarrow> complex" and k :: nat
  assume "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m ([P] ! k) + acc) [0..<length [P]] (0\<^sub>m d n) = 0\<^sub>m d n"
     and k: "k < length [P]"
  hence c0: "c 0 \<cdot>\<^sub>m P = 0\<^sub>m d n" using Pc by simp
  have "c 0 = 0"
  proof (rule ccontr)
    assume "c 0 \<noteq> 0"
    hence "P = (1 / c 0) \<cdot>\<^sub>m (c 0 \<cdot>\<^sub>m P)" unfolding smult_smult_mat using Pc by (intro eq_matI) auto
    also have "\<dots> = 0\<^sub>m d n" unfolding c0 by (intro eq_matI) auto
    finally show False using Pnz by simp
  qed
  thus "c k = 0" using k by simp
qed (use Pc in simp)

text \<open>The core of the necessity proof: by Choi's Theorem 2 applied to the two Kraus
representations $\{P\}$ and $\{A_lE_iP\}$ of $X\mapsto PXP$, every $A_lE_iP$ is a multiple of $P$.\<close>

lemma kl_kraus_scalars:
  assumes P: "projection n P" and Pnz: "P \<noteq> 0\<^sub>m n n" and npos: "0 < n"
      and As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n"
      and corr: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow>
                   kraus_map_dim n As (kraus_map_dim n Es (P * X * P)) = P * X * P"
  shows "\<exists>\<beta> :: nat \<Rightarrow> nat \<Rightarrow> complex. \<forall>l < length As. \<forall>i < length Es.
           As ! l * Es ! i * P = \<beta> l i \<cdot>\<^sub>m P"
proof -
  let ?m = "length As" and ?r = "length Es"
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" and PP: "P * P = P"
    using P by (auto simp: projection_def hermitian_def)
  let ?Cs = "kraus_compose As Es"
  let ?Fs = "map (\<lambda>W. W * P) ?Cs"
  have Cs_c: "\<forall>W \<in> set ?Cs. W \<in> carrier_mat n n" by (rule kraus_compose_carrier[OF As_c Es_c])
  have Fs_c: "\<forall>W \<in> set ?Fs. W \<in> carrier_mat n n" using Cs_c Pc by auto
  \<comment> \<open>Two Kraus representations of \<open>X \<mapsto> P X P\<close>.\<close>
  have same: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim n [P] X = kraus_map_dim n ?Fs X"
  proof (intro allI impI)
    fix X :: "complex Matrix.mat" assume Xc: "X \<in> carrier_mat n n"
    have "kraus_map_dim n ?Fs X = kraus_map_dim n ?Cs (P * X * (P\<^sup>\<dagger>))"
      by (rule kraus_map_dim_map_mult_right[OF Cs_c Pc Xc])
    also have "\<dots> = kraus_map_dim n As (kraus_map_dim n Es (P * X * P))"
      unfolding Ph using kraus_map_dim_compose[OF As_c Es_c, of "P * X * P"] Pc Xc by simp
    also have "\<dots> = P * X * P" using corr Xc by simp
    also have "\<dots> = kraus_map_dim n [P] X" using Pc Xc Ph by simp
    finally show "kraus_map_dim n [P] X = kraus_map_dim n ?Fs X" ..
  qed
  obtain U :: "complex Matrix.mat" where Uc: "U \<in> carrier_mat (length ?Fs) 1"
    and rep: "\<forall>k < length ?Fs. ?Fs ! k = foldr (\<lambda>j acc. U $$ (k,j) \<cdot>\<^sub>m ([P] ! j) + acc) [0..<1] (0\<^sub>m n n)"
    using choi_2_unitary_freedom[OF npos npos Fs_c lin_indep_complex_mat_single[OF Pc Pnz] same] by auto
  define \<beta> :: "nat \<Rightarrow> nat \<Rightarrow> complex" where "\<beta> = (\<lambda>l i. U $$ (i * ?m + l, 0))"
  have AEP: "\<And>l i. l < ?m \<Longrightarrow> i < ?r \<Longrightarrow> As ! l * Es ! i * P = \<beta> l i \<cdot>\<^sub>m P"
  proof -
    fix l i assume l: "l < ?m" and i: "i < ?r"
    have k: "i * ?m + l < length ?Fs"
      using mult_index_lt[OF i l] by (simp add: length_kraus_compose)
    have "?Fs ! (i * ?m + l) = (As ! l * Es ! i) * P"
      using kraus_compose_nth[OF i l] k by (simp add: length_kraus_compose)
    moreover have "?Fs ! (i * ?m + l) = U $$ (i * ?m + l, 0) \<cdot>\<^sub>m P"
      using rep k Pc by simp
    ultimately show "As ! l * Es ! i * P = \<beta> l i \<cdot>\<^sub>m P" by (simp add: \<beta>_def)
  qed
  thus ?thesis by blast
qed

theorem knill_laflamme_necessity:
  assumes P: "projection n P" and Pnz: "P \<noteq> 0\<^sub>m n n" and npos: "0 < n"
      and As: "kraus_operators n n As" and Es: "kraus_operators n n Es"
      and corr: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow>
                   kraus_map_dim n As (kraus_map_dim n Es (P * X * P)) = P * X * P"
  shows "\<exists>\<alpha> :: nat \<Rightarrow> nat \<Rightarrow> complex. \<forall>i < length Es. \<forall>j < length Es.
           P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P"
proof -
  let ?m = "length As" and ?r = "length Es"
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" and PP: "P * P = P"
    using P by (auto simp: projection_def hermitian_def)
  have As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and As_tp: "sum_wdag_w n As = 1\<^sub>m n"
    using As by (auto simp: kraus_operators_altdef)
  have Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" using Es by (simp add: kraus_operators_altdef)
  obtain \<beta> :: "nat \<Rightarrow> nat \<Rightarrow> complex"
    where AEP: "\<And>l i. l < ?m \<Longrightarrow> i < ?r \<Longrightarrow> As ! l * Es ! i * P = \<beta> l i \<cdot>\<^sub>m P"
    using kl_kraus_scalars[OF P Pnz npos As_c Es_c corr] by blast
  define \<alpha> :: "nat \<Rightarrow> nat \<Rightarrow> complex" where "\<alpha> = (\<lambda>i j. \<Sum>l < ?m. cnj (\<beta> l i) * \<beta> l j)"
  have "\<And>i j. i < ?r \<Longrightarrow> j < ?r \<Longrightarrow> P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P"
  proof -
    fix i j assume i: "i < ?r" and j: "j < ?r"
    have Eic: "Es ! i \<in> carrier_mat n n" and Ejc: "Es ! j \<in> carrier_mat n n" using Es_c i j by auto
    have Eidc: "(Es ! i)\<^sup>\<dagger> \<in> carrier_mat n n" using dagger_carrier[OF Eic] .
    let ?L = "P * ((Es ! i)\<^sup>\<dagger>)" and ?R = "Es ! j * P"
    have Lc: "?L \<in> carrier_mat n n" and Rc: "?R \<in> carrier_mat n n" using Pc Eidc Ejc by auto
    let ?g = "\<lambda>A :: complex Matrix.mat. (A\<^sup>\<dagger>) * A"
    have gc: "\<forall>l \<in> set [0..<?m]. ?g (As ! l) \<in> carrier_mat n n"
    proof
      fix l assume "l \<in> set [0..<?m]"
      hence Alc: "As ! l \<in> carrier_mat n n" using As_c by simp
      show "?g (As ! l) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF dagger_carrier[OF Alc] Alc])
    qed
    have "P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = ?L * ?R"
    proof -
      have "?L * ?R = P * (((Es ! i)\<^sup>\<dagger>) * (Es ! j * P))"
        by (rule assoc_mult_mat[OF Pc Eidc mult_carrier_mat[OF Ejc Pc]])
      also have "\<dots> = P * ((((Es ! i)\<^sup>\<dagger>) * Es ! j) * P)" by (simp only: assoc_mult_mat[OF Eidc Ejc Pc])
      also have "\<dots> = P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P"
        by (rule assoc_mult_mat[OF Pc mult_carrier_mat[OF Eidc Ejc] Pc, symmetric])
      finally show ?thesis ..
    qed
    also have "\<dots> = ?L * 1\<^sub>m n * ?R" by (simp only: right_mult_one_mat[OF Lc])
    also have "1\<^sub>m n = foldr (\<lambda>l acc. ?g (As ! l) + acc) [0..<?m] (0\<^sub>m n n)"
      using As_tp unfolding sum_wdag_w_def by (simp add: foldr_list_as_index[of ?g As])
    also have "?L * foldr (\<lambda>l acc. ?g (As ! l) + acc) [0..<?m] (0\<^sub>m n n) * ?R
               = foldr (\<lambda>l acc. ?L * ?g (As ! l) * ?R + acc) [0..<?m] (0\<^sub>m n n)"
    proof -
      have gc': "\<forall>l \<in> set [0..<?m]. ?L * ?g (As ! l) \<in> carrier_mat n n"
      proof
        fix l assume "l \<in> set [0..<?m]"
        hence "?g (As ! l) \<in> carrier_mat n n" using gc by blast
        thus "?L * ?g (As ! l) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Lc])
      qed
      show ?thesis unfolding foldr_add_mat_mult_left[OF Lc gc] by (rule foldr_add_mat_mult_right[OF Rc gc'])
    qed
    also have "\<dots> = foldr (\<lambda>l acc. (cnj (\<beta> l i) * \<beta> l j) \<cdot>\<^sub>m P + acc) [0..<?m] (0\<^sub>m n n)"
    proof (rule foldr_add_mat_cong)
      fix l assume "l \<in> set [0..<?m]"
      hence l: "l < ?m" by simp
      have Alc: "As ! l \<in> carrier_mat n n" using As_c l by simp
      have AEPi: "(As ! l * Es ! i * P)\<^sup>\<dagger> = cnj (\<beta> l i) \<cdot>\<^sub>m P"
        unfolding AEP[OF l i] by (simp only: dagger_of_smult Ph)
      let ?A = "As ! l" and ?Ad = "(As ! l)\<^sup>\<dagger>" and ?Ei = "Es ! i" and ?Eid = "(Es ! i)\<^sup>\<dagger>" and ?Ej = "Es ! j"
      have Adc: "?Ad \<in> carrier_mat n n" by (rule dagger_carrier[OF Alc])
      have "?L * ?g ?A * ?R = ((As ! l * Es ! i * P)\<^sup>\<dagger>) * (As ! l * Es ! j * P)"
      proof -
        have d1: "(?A * ?Ei * P)\<^sup>\<dagger> = (P\<^sup>\<dagger>) * ((?A * ?Ei)\<^sup>\<dagger>)"
          by (rule dagger_of_prod) (simp only: carrier_matD[OF mult_carrier_mat[OF Alc Eic]] carrier_matD[OF Pc])
        have d2: "(?A * ?Ei)\<^sup>\<dagger> = ?Eid * ?Ad"
          by (rule dagger_of_prod) (simp only: carrier_matD[OF Alc] carrier_matD[OF Eic])
        have dag: "(?A * ?Ei * P)\<^sup>\<dagger> = P * (?Eid * ?Ad)" unfolding d1 d2 Ph ..
        have "?L * ?g ?A * ?R = (P * ?Eid) * ((?Ad * ?A) * (?Ej * P))"
          by (rule assoc_mult_mat[OF mult_carrier_mat[OF Pc Eidc] mult_carrier_mat[OF Adc Alc] mult_carrier_mat[OF Ejc Pc]])
        also have "\<dots> = (P * ?Eid) * (?Ad * (?A * (?Ej * P)))"
          by (simp only: assoc_mult_mat[OF Adc Alc mult_carrier_mat[OF Ejc Pc]])
        also have "\<dots> = P * (?Eid * (?Ad * (?A * (?Ej * P))))"
          by (rule assoc_mult_mat[OF Pc Eidc mult_carrier_mat[OF Adc mult_carrier_mat[OF Alc mult_carrier_mat[OF Ejc Pc]]]])
        also have "\<dots> = P * ((?Eid * ?Ad) * (?A * (?Ej * P)))"
          by (simp only: assoc_mult_mat[OF Eidc Adc mult_carrier_mat[OF Alc mult_carrier_mat[OF Ejc Pc]], symmetric])
        also have "\<dots> = (P * (?Eid * ?Ad)) * (?A * (?Ej * P))"
          by (rule assoc_mult_mat[OF Pc mult_carrier_mat[OF Eidc Adc] mult_carrier_mat[OF Alc mult_carrier_mat[OF Ejc Pc]], symmetric])
        also have "\<dots> = (P * (?Eid * ?Ad)) * ((?A * ?Ej) * P)" by (simp only: assoc_mult_mat[OF Alc Ejc Pc])
        finally show ?thesis unfolding dag .
      qed
      also have "\<dots> = (cnj (\<beta> l i) \<cdot>\<^sub>m P) * (\<beta> l j \<cdot>\<^sub>m P)" unfolding AEPi AEP[OF l j] ..
      also have "\<dots> = (cnj (\<beta> l i) * \<beta> l j) \<cdot>\<^sub>m P"
        by (simp only: mult_smult_assoc_mat[OF Pc smult_carrier_mat[OF Pc]] mult_smult_distrib[OF Pc Pc] smult_smult_mat PP)
      finally show "?L * ?g (As ! l) * ?R = (cnj (\<beta> l i) * \<beta> l j) \<cdot>\<^sub>m P" .
    qed
    also have "\<dots> = sum_list (map (\<lambda>l. cnj (\<beta> l i) * \<beta> l j) [0..<?m]) \<cdot>\<^sub>m P"
      by (rule foldr_add_mat_smult_pull[OF _ Pc]) simp
    also have "sum_list (map (\<lambda>l. cnj (\<beta> l i) * \<beta> l j) [0..<?m]) = \<alpha> i j"
      unfolding \<alpha>_def by (simp add: sum_list_sum_nth atLeast0LessThan)
    finally show "P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P" .
  qed
  thus ?thesis by blast
qed

subsection \<open>Kraus lists consisting of multiples of one operator\<close>

lemma kraus_map_dim_scalar_list:
  assumes Pc: "P \<in> carrier_mat n n" and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim n (map (\<lambda>\<gamma>. \<gamma> \<cdot>\<^sub>m P) gs) M
         = sum_list (map (\<lambda>\<gamma>. cnj \<gamma> * \<gamma>) gs) \<cdot>\<^sub>m (P * M * (P\<^sup>\<dagger>))"
proof (induction gs)
  case Nil show ?case using Pc Xc dagger_carrier[OF Pc] by (intro eq_matI) auto
next
  case (Cons \<gamma> gs)
  have Pd: "P\<^sup>\<dagger> \<in> carrier_mat n n" using dagger_carrier[OF Pc] .
  have PXP: "P * M * (P\<^sup>\<dagger>) \<in> carrier_mat n n" using Pc Xc Pd by auto
  have "(\<gamma> \<cdot>\<^sub>m P) * M * ((\<gamma> \<cdot>\<^sub>m P)\<^sup>\<dagger>) = (\<gamma> \<cdot>\<^sub>m P) * M * (cnj \<gamma> \<cdot>\<^sub>m (P\<^sup>\<dagger>))"
    by (simp only: dagger_of_smult)
  also have "\<dots> = (\<gamma> \<cdot>\<^sub>m (P * M)) * (cnj \<gamma> \<cdot>\<^sub>m (P\<^sup>\<dagger>))" by (simp only: mult_smult_assoc_mat[OF Pc Xc])
  also have "\<dots> = \<gamma> \<cdot>\<^sub>m ((P * M) * (cnj \<gamma> \<cdot>\<^sub>m (P\<^sup>\<dagger>)))"
    by (rule mult_smult_assoc_mat[OF mult_carrier_mat[OF Pc Xc] smult_carrier_mat[OF Pd]])
  also have "\<dots> = \<gamma> \<cdot>\<^sub>m (cnj \<gamma> \<cdot>\<^sub>m (P * M * (P\<^sup>\<dagger>)))"
    by (simp only: mult_smult_distrib[OF mult_carrier_mat[OF Pc Xc] Pd])
  also have "\<dots> = (cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m (P * M * (P\<^sup>\<dagger>))" by (simp only: smult_smult_mat mult.commute)
  finally have "(\<gamma> \<cdot>\<^sub>m P) * M * ((\<gamma> \<cdot>\<^sub>m P)\<^sup>\<dagger>) = (cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m (P * M * (P\<^sup>\<dagger>))" .
  thus ?case using Cons.IH PXP by (simp add: add_smult_distrib_right_mat)
qed

lemma sum_wdag_w_scalar_list:
  assumes Pc: "P \<in> carrier_mat n n"
  shows "sum_wdag_w n (map (\<lambda>\<gamma>. \<gamma> \<cdot>\<^sub>m P) gs) = sum_list (map (\<lambda>\<gamma>. cnj \<gamma> * \<gamma>) gs) \<cdot>\<^sub>m ((P\<^sup>\<dagger>) * P)"
proof (induction gs)
  case Nil show ?case using Pc dagger_carrier[OF Pc] by (intro eq_matI) auto
next
  case (Cons \<gamma> gs)
  have Pd: "P\<^sup>\<dagger> \<in> carrier_mat n n" using dagger_carrier[OF Pc] .
  have PP: "(P\<^sup>\<dagger>) * P \<in> carrier_mat n n" using Pc Pd by auto
  have "((\<gamma> \<cdot>\<^sub>m P)\<^sup>\<dagger>) * (\<gamma> \<cdot>\<^sub>m P) = (cnj \<gamma> \<cdot>\<^sub>m (P\<^sup>\<dagger>)) * (\<gamma> \<cdot>\<^sub>m P)"
    by (simp only: dagger_of_smult)
  also have "\<dots> = cnj \<gamma> \<cdot>\<^sub>m ((P\<^sup>\<dagger>) * (\<gamma> \<cdot>\<^sub>m P))" by (rule mult_smult_assoc_mat[OF Pd smult_carrier_mat[OF Pc]])
  also have "\<dots> = cnj \<gamma> \<cdot>\<^sub>m (\<gamma> \<cdot>\<^sub>m ((P\<^sup>\<dagger>) * P))" by (simp only: mult_smult_distrib[OF Pd Pc])
  also have "\<dots> = (cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m ((P\<^sup>\<dagger>) * P)" by (simp only: smult_smult_mat)
  finally have "((\<gamma> \<cdot>\<^sub>m P)\<^sup>\<dagger>) * (\<gamma> \<cdot>\<^sub>m P) = (cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m ((P\<^sup>\<dagger>) * P)" .
  thus ?case using Cons.IH PP by (simp add: sum_wdag_w_Cons add_smult_distrib_right_mat)
qed

lemma smult_eq_self_imp_one:
  fixes P :: "complex Matrix.mat"
  assumes Pc: "P \<in> carrier_mat n n" and Pnz: "P \<noteq> 0\<^sub>m n n" and eq: "s \<cdot>\<^sub>m P = P"
  shows "s = 1"
proof -
  obtain i j where i: "i < n" and j: "j < n" and Pij: "P $$ (i,j) \<noteq> 0"
  proof -
    have "\<exists>i j. i < n \<and> j < n \<and> P $$ (i,j) \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> (\<exists>i j. i < n \<and> j < n \<and> P $$ (i,j) \<noteq> 0)"
      hence "P = 0\<^sub>m n n" using Pc by (intro eq_matI) auto
      thus False using Pnz by simp
    qed
    thus ?thesis using that by blast
  qed
  have "s * P $$ (i,j) = P $$ (i,j)" using arg_cong[OF eq, of "\<lambda>M. M $$ (i,j)"] i j carrier_matD[OF Pc] by simp
  hence "(s - 1) * P $$ (i,j) = 0" by (simp add: left_diff_distrib)
  hence "s - 1 = 0" using Pij by simp
  thus ?thesis by simp
qed

subsection \<open>Theorem 2\<close>

text \<open>If $\mathcal R\circ\mathbb E$ fixes $PXP$ and $G_i=\sum_jg_{ij}E_j$ with $\sum_iG_i^*G_i=I$,
then $\mathcal R\circ\mathbb G$ fixes $PXP$ as well (same $\mathcal R$).\<close>

theorem knill_laflamme_closure:
  assumes P: "projection n P" and Pnz: "P \<noteq> 0\<^sub>m n n" and npos: "0 < n"
      and As: "kraus_operators n n As"
      and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n"
      and corr: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow>
                   kraus_map_dim n As (kraus_map_dim n Es (P * X * P)) = P * X * P"
      and Gc: "G \<in> carrier_mat t (length Es)"
      and Gs_tp: "sum_wdag_w n (kraus_mix n n G Es) = 1\<^sub>m n"
  shows "\<forall>X. X \<in> carrier_mat n n \<longrightarrow>
           kraus_map_dim n As (kraus_map_dim n (kraus_mix n n G Es) (P * X * P)) = P * X * P"
proof -
  let ?m = "length As" and ?r = "length Es"
  let ?Gs = "kraus_mix n n G Es"
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" and PP: "P * P = P"
    using P by (auto simp: projection_def hermitian_def)
  have As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and As_tp: "sum_wdag_w n As = 1\<^sub>m n"
    using As by (auto simp: kraus_operators_altdef)
  have Gs_c: "\<forall>W \<in> set ?Gs. W \<in> carrier_mat n n" by (rule kraus_mix_carrier[OF Es_c])
  have Gs_len: "length ?Gs = t" using Gc by simp
  obtain \<beta> :: "nat \<Rightarrow> nat \<Rightarrow> complex"
    where AEP: "\<And>l j. l < ?m \<Longrightarrow> j < ?r \<Longrightarrow> As ! l * Es ! j * P = \<beta> l j \<cdot>\<^sub>m P"
    using kl_kraus_scalars[OF P Pnz npos As_c Es_c corr] by blast
  \<comment> \<open>\<open>A\<^sub>l G\<^sub>i P = \<gamma>\<^sub>l\<^sub>i P\<close>.\<close>
  define \<gamma> :: "nat \<Rightarrow> nat \<Rightarrow> complex" where "\<gamma> = (\<lambda>l i. \<Sum>j = 0..<?r. G $$ (i,j) * \<beta> l j)"
  have AGP: "\<And>l i. l < ?m \<Longrightarrow> i < t \<Longrightarrow> As ! l * ?Gs ! i * P = \<gamma> l i \<cdot>\<^sub>m P"
  proof -
    fix l i assume l: "l < ?m" and i: "i < t"
    have Alc: "As ! l \<in> carrier_mat n n" using As_c l by simp
    have fc: "\<forall>j \<in> set [0..<?r]. G $$ (i,j) \<cdot>\<^sub>m (Es ! j) \<in> carrier_mat n n" using Es_c by auto
    have "As ! l * ?Gs ! i * P = As ! l * foldr (\<lambda>j acc. G $$ (i,j) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n) * P"
      using kraus_mix_nth[of i G n n Es] i Gc by simp
    also have "\<dots> = foldr (\<lambda>j acc. As ! l * (G $$ (i,j) \<cdot>\<^sub>m (Es ! j)) * P + acc) [0..<?r] (0\<^sub>m n n)"
    proof -
      have fc': "\<forall>j \<in> set [0..<?r]. As ! l * (G $$ (i,j) \<cdot>\<^sub>m (Es ! j)) \<in> carrier_mat n n"
      proof
        fix j assume "j \<in> set [0..<?r]"
        hence "G $$ (i,j) \<cdot>\<^sub>m (Es ! j) \<in> carrier_mat n n" using fc by blast
        thus "As ! l * (G $$ (i,j) \<cdot>\<^sub>m (Es ! j)) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Alc])
      qed
      show ?thesis unfolding foldr_add_mat_mult_left[OF Alc fc] by (rule foldr_add_mat_mult_right[OF Pc fc'])
    qed
    also have "\<dots> = foldr (\<lambda>j acc. (G $$ (i,j) * \<beta> l j) \<cdot>\<^sub>m P + acc) [0..<?r] (0\<^sub>m n n)"
    proof (rule foldr_add_mat_cong)
      fix j assume "j \<in> set [0..<?r]"
      hence j: "j < ?r" by simp
      have Ejc: "Es ! j \<in> carrier_mat n n" using Es_c j by simp
      have "As ! l * (G $$ (i,j) \<cdot>\<^sub>m (Es ! j)) * P = G $$ (i,j) \<cdot>\<^sub>m (As ! l * Es ! j * P)"
        by (simp only: mult_smult_distrib[OF Alc Ejc] mult_smult_assoc_mat[OF mult_carrier_mat[OF Alc Ejc] Pc])
      also have "\<dots> = (G $$ (i,j) * \<beta> l j) \<cdot>\<^sub>m P" unfolding AEP[OF l j] smult_smult_mat ..
      finally show "As ! l * (G $$ (i,j) \<cdot>\<^sub>m (Es ! j)) * P = (G $$ (i,j) * \<beta> l j) \<cdot>\<^sub>m P" .
    qed
    also have "\<dots> = sum_list (map (\<lambda>j. G $$ (i,j) * \<beta> l j) [0..<?r]) \<cdot>\<^sub>m P"
      by (rule foldr_add_mat_smult_pull[OF _ Pc]) simp
    also have "sum_list (map (\<lambda>j. G $$ (i,j) * \<beta> l j) [0..<?r]) = \<gamma> l i"
      unfolding \<gamma>_def by (simp add: sum_list_sum_nth atLeast0LessThan)
    finally show "As ! l * ?Gs ! i * P = \<gamma> l i \<cdot>\<^sub>m P" .
  qed
  \<comment> \<open>The Kraus operators of \<open>X \<mapsto> R(G(PXP))\<close> are the \<open>\<gamma>\<^sub>l\<^sub>i P\<close>.\<close>
  let ?Cs = "kraus_compose As ?Gs"
  let ?Fs = "map (\<lambda>W. W * P) ?Cs"
  define gs :: "complex list" where "gs = map (\<lambda>k. \<gamma> (k mod ?m) (k div ?m)) [0..<t * ?m]"
  have Cs_c: "\<forall>W \<in> set ?Cs. W \<in> carrier_mat n n" by (rule kraus_compose_carrier[OF As_c Gs_c])
  have Fs_eq: "?Fs = map (\<lambda>\<gamma>. \<gamma> \<cdot>\<^sub>m P) gs"
  proof (rule nth_equalityI)
    show "length ?Fs = length (map (\<lambda>\<gamma>. \<gamma> \<cdot>\<^sub>m P) gs)" using Gs_len by (simp add: gs_def length_kraus_compose)
  next
    fix k assume "k < length ?Fs"
    hence k: "k < t * ?m" using Gs_len by (simp add: length_kraus_compose)
    have mpos: "0 < ?m" using k by (cases ?m) auto
    have i: "k div ?m < t" using k by (simp add: less_mult_imp_div_less)
    have l: "k mod ?m < ?m" using mpos by simp
    have k_eq: "k = (k div ?m) * ?m + k mod ?m" by simp
    have "?Fs ! k = (As ! (k mod ?m) * ?Gs ! (k div ?m)) * P"
      using kraus_compose_nth[of "k div ?m" ?Gs "k mod ?m" As] i l Gs_len k
      by (subst k_eq) (simp add: length_kraus_compose)
    also have "\<dots> = \<gamma> (k mod ?m) (k div ?m) \<cdot>\<^sub>m P" by (rule AGP[OF l i])
    also have "\<dots> = map (\<lambda>\<gamma>. \<gamma> \<cdot>\<^sub>m P) gs ! k" using k by (simp add: gs_def)
    finally show "?Fs ! k = map (\<lambda>\<gamma>. \<gamma> \<cdot>\<^sub>m P) gs ! k" .
  qed
  \<comment> \<open>Trace preservation forces \<open>\<Sum> |\<gamma>|\<^sup>2 = 1\<close>.\<close>
  have "sum_wdag_w n ?Fs = (P\<^sup>\<dagger>) * sum_wdag_w n ?Cs * P"
    by (rule sum_wdag_w_map_mult_right[OF Cs_c Pc])
  also have "\<dots> = (P\<^sup>\<dagger>) * sum_wdag_w n ?Gs * P" by (simp only: sum_wdag_w_compose[OF As_c Gs_c As_tp])
  also have "\<dots> = (P\<^sup>\<dagger>) * 1\<^sub>m n * P" by (simp only: Gs_tp)
  also have "\<dots> = P" unfolding Ph by (simp only: right_mult_one_mat[OF Pc] PP)
  finally have "sum_wdag_w n ?Fs = P" .
  moreover have "sum_wdag_w n ?Fs = sum_list (map (\<lambda>\<gamma>. cnj \<gamma> * \<gamma>) gs) \<cdot>\<^sub>m P"
    unfolding Fs_eq sum_wdag_w_scalar_list[OF Pc] Ph PP ..
  ultimately have norm1: "sum_list (map (\<lambda>\<gamma>. cnj \<gamma> * \<gamma>) gs) = 1"
    using smult_eq_self_imp_one[OF Pc Pnz] by simp
  show ?thesis
  proof (intro allI impI)
    fix X :: "complex Matrix.mat" assume Xc: "X \<in> carrier_mat n n"
    have "kraus_map_dim n As (kraus_map_dim n ?Gs (P * X * P)) = kraus_map_dim n ?Cs (P * X * (P\<^sup>\<dagger>))"
      unfolding Ph using kraus_map_dim_compose[OF As_c Gs_c, of "P * X * P"] Pc Xc by simp
    also have "\<dots> = kraus_map_dim n ?Fs X" by (rule kraus_map_dim_map_mult_right[OF Cs_c Pc Xc, symmetric])
    also have "\<dots> = sum_list (map (\<lambda>\<gamma>. cnj \<gamma> * \<gamma>) gs) \<cdot>\<^sub>m (P * X * (P\<^sup>\<dagger>))"
      unfolding Fs_eq by (rule kraus_map_dim_scalar_list[OF Pc Xc])
    also have "\<dots> = P * X * P" unfolding norm1 Ph using Pc Xc by (intro eq_matI) auto
    finally show "kraus_map_dim n As (kraus_map_dim n ?Gs (P * X * P)) = P * X * P" .
  qed
qed


end
