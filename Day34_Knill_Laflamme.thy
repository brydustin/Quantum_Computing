(*  Title:   Day34_Knill_Laflamme.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 18 November 2011 (Day 34)
*)

theory Day34_Knill_Laflamme
  imports Day32_Recovery_Proposition
begin

section \<open>Day 34 (18 November 2011): the Knill--Laflamme conditions\<close>

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
    then obtain l where l: "l < length vs" and vl: "v = vs ! l" by (auto simp: in_set_conv_nth)
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

definition recover_after :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "recover_after n As Es M = kraus_map_dim n As (kraus_map_dim n Es M)"

lemma recover_after_carrier: assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and M: "M \<in> carrier_mat n n" shows "recover_after n As Es M \<in> carrier_mat n n"
  unfolding recover_after_def by (rule kraus_map_dim_carrier[OF As_c kraus_map_dim_carrier[OF Es_c M]])

lemma recover_after_add: assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and M: "M \<in> carrier_mat n n" and N: "N \<in> carrier_mat n n" shows "recover_after n As Es (M + N) = recover_after n As Es M + recover_after n As Es N"
  unfolding recover_after_def kraus_map_dim_add[OF M N Es_c]
  by (rule kraus_map_dim_add[OF kraus_map_dim_carrier[OF Es_c M] kraus_map_dim_carrier[OF Es_c N] As_c])

lemma recover_after_smult: assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and M: "M \<in> carrier_mat n n" shows "recover_after n As Es (c \<cdot>\<^sub>m M) = c \<cdot>\<^sub>m recover_after n As Es M"
  unfolding recover_after_def kraus_map_dim_smult[OF M Es_c]
  by (rule kraus_map_dim_smult[OF kraus_map_dim_carrier[OF Es_c M] As_c])

lemma recover_after_minus:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n"
      and Xc: "M \<in> carrier_mat n n" and Yc: "N \<in> carrier_mat n n"
  shows "recover_after n As Es (M - N) = recover_after n As Es M - recover_after n As Es N"
proof -
  have "M - N = M + (-1) \<cdot>\<^sub>m N" using Xc Yc by (intro eq_matI) auto
  hence "recover_after n As Es (M - N) = recover_after n As Es M + (-1) \<cdot>\<^sub>m recover_after n As Es N" using recover_after_add[OF As_c Es_c Xc] recover_after_smult[OF As_c Es_c Yc] Yc by simp
  thus ?thesis using recover_after_carrier[OF As_c Es_c Xc] recover_after_carrier[OF As_c Es_c Yc] by (intro eq_matI) auto
qed

lemma recover_after_foldr:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and "\<forall>v \<in> set vs. dim_vec v = n"
  shows "recover_after n As Es (foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)) = foldr (\<lambda>v acc. recover_after n As Es (v \<oslash> v) + acc) vs (0\<^sub>m n n)"
  using assms(3)
proof (induction vs)
  case Nil
  have "recover_after n As Es (0\<^sub>m n n) = 0\<^sub>m n n" unfolding recover_after_def using As_c Es_c by (simp add: kraus_map_dim_zero)
  thus ?case by simp
next
  case (Cons v vs)
  have vd: "dim_vec v = n" and rest: "\<forall>v \<in> set vs. dim_vec v = n" using Cons.prems by auto
  have rc: "foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n) \<in> carrier_mat n n"
    using rest by (induction vs) (auto simp: outer_prod_carrier)
  show ?case using recover_after_add[OF As_c Es_c outer_prod_carrier[OF vd vd] rc] Cons.IH[OF rest] by simp
qed

text \<open>D34-1: $\mathcal R\circ\mathbb E$ fixes $|\psi\rangle\langle\psi|$ for all $\psi\in V$ iff it
fixes $PXP$ for all $X$.\<close>

proposition recovery_states_iff_PXP:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat n n" and Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and P: "projection n P"
  shows "(\<forall>\<psi>. dim_vec \<psi> = n \<longrightarrow> P *\<^sub>v \<psi> = \<psi> \<longrightarrow> recover_after n As Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>)
         \<longleftrightarrow> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> recover_after n As Es (P * X * P) = P * X * P)"
proof
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" using P by (auto simp: projection_def hermitian_def)
  assume H: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> recover_after n As Es (P * X * P) = P * X * P"
  show "\<forall>\<psi>. dim_vec \<psi> = n \<longrightarrow> P *\<^sub>v \<psi> = \<psi> \<longrightarrow> recover_after n As Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>"
  proof (intro allI impI)
    fix \<psi> :: "complex Matrix.vec" assume \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>"
    have "P * (\<psi> \<oslash> \<psi>) * P = (P *\<^sub>v \<psi>) \<oslash> (P *\<^sub>v \<psi>)"
      using conj_outer_prod[OF Pc \<psi>d] Ph by simp
    hence e: "P * (\<psi> \<oslash> \<psi>) * P = \<psi> \<oslash> \<psi>" unfolding \<psi>V .
    have "recover_after n As Es (P * (\<psi> \<oslash> \<psi>) * P) = P * (\<psi> \<oslash> \<psi>) * P"
      using H outer_prod_carrier[OF \<psi>d \<psi>d] by blast
    thus "recover_after n As Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>" unfolding e .
  qed
next
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" using P by (auto simp: projection_def hermitian_def)
  assume H: "\<forall>\<psi>. dim_vec \<psi> = n \<longrightarrow> P *\<^sub>v \<psi> = \<psi> \<longrightarrow> recover_after n As Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>"
  have psd_case: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> psd X \<Longrightarrow> recover_after n As Es (P * X * P) = P * X * P"
  proof -
    fix X :: "complex Matrix.mat" assume Xc: "X \<in> carrier_mat n n" and Xpsd: "psd X"
    obtain vs :: "complex Matrix.vec list" where vsV: "\<forall>v \<in> set vs. dim_vec v = n \<and> P *\<^sub>v v = v"
      and dec: "P * X * P = foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)"
      using psd_PXP_decomp_in_range[OF P Xc Xpsd] by blast
    have vsd: "\<forall>v \<in> set vs. dim_vec v = n" using vsV by simp
    have "recover_after n As Es (P * X * P) = foldr (\<lambda>v acc. recover_after n As Es (v \<oslash> v) + acc) vs (0\<^sub>m n n)"
      unfolding dec by (rule recover_after_foldr[OF As_c Es_c vsd])
    also have "\<dots> = foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)"
      by (rule foldr_add_mat_cong) (use H vsV in auto)
    finally show "recover_after n As Es (P * X * P) = P * X * P" unfolding dec .
  qed
  show "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> recover_after n As Es (P * X * P) = P * X * P"
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
    have "recover_after n As Es (?c X) = recover_after n As Es ((?c P1 - ?c P2) + \<i> \<cdot>\<^sub>m (?c P3 - ?c P4))" unfolding PXP ..
    also have "\<dots> = recover_after n As Es (?c P1 - ?c P2) + recover_after n As Es (\<i> \<cdot>\<^sub>m (?c P3 - ?c P4))"
      by (rule recover_after_add[OF As_c Es_c minus_carrier_mat[OF c2] smult_carrier_mat[OF minus_carrier_mat[OF c4]]])
    also have "recover_after n As Es (?c P1 - ?c P2) = recover_after n As Es (?c P1) - recover_after n As Es (?c P2)"
      by (rule recover_after_minus[OF As_c Es_c c1 c2])
    also have "recover_after n As Es (\<i> \<cdot>\<^sub>m (?c P3 - ?c P4)) = \<i> \<cdot>\<^sub>m recover_after n As Es (?c P3 - ?c P4)"
      by (rule recover_after_smult[OF As_c Es_c minus_carrier_mat[OF c4]])
    also have "recover_after n As Es (?c P3 - ?c P4) = recover_after n As Es (?c P3) - recover_after n As Es (?c P4)"
      by (rule recover_after_minus[OF As_c Es_c c3 c4])
    also have "(recover_after n As Es (?c P1) - recover_after n As Es (?c P2)) + \<i> \<cdot>\<^sub>m (recover_after n As Es (?c P3) - recover_after n As Es (?c P4))
               = (?c P1 - ?c P2) + \<i> \<cdot>\<^sub>m (?c P3 - ?c P4)"
      by (simp only: psd_case[OF conjunct1[OF P1] conjunct2[OF P1]] psd_case[OF conjunct1[OF P2] conjunct2[OF P2]]
                     psd_case[OF conjunct1[OF P3] conjunct2[OF P3]] psd_case[OF conjunct1[OF P4] conjunct2[OF P4]])
    finally show "recover_after n As Es (?c X) = ?c X" unfolding PXP .
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

subsection \<open>Sufficiency of the Knill--Laflamme conditions (D34-2)\<close>

text \<open>D34-2, sufficiency: if $PE_i^*E_jP=\alpha_{ij}P$ then a recovery channel exists.  Diagonalise
$(\alpha_{ij})=u\,\mathrm{diag}(d)\,u^*$; the errors $F_k=\sum_iu_{ik}E_i$ give the same channel and
satisfy $PF_k^*F_lP=\delta_{kl}d_kP$, so the $F_k/\sqrt{d_k}$ with $d_k>0$ satisfy the hypotheses of
the recovery proposition (\<open>recovery_setting\<close>).\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{tikzpicture}[font=\small, >=Stealth, sp/.style={draw, rounded corners, minimum width=2.2cm, minimum height=0.8cm, align=center}]
\draw[rounded corners, gray] (-1.6,-3.3) rectangle (8.6,2.1);
\node[gray, anchor=north east] at (8.5,2.05) {$\C^n$};
\node[sp, fill=gray!15] (v) at (0,0) {$V=\mathrm{ran}\,P$};
\node[sp] (f1) at (6,1.4) {$F_1V$};
\node[sp] (f2) at (6,0) {$F_2V$};
\node[sp] (f3) at (6,-1.4) {$F_3V$};
\draw[->] (v) to[bend left=12] node[above, sloped] {$F_1$} (f1.west);
\draw[->] (v) -- node[above] {$F_2$} (f2.west);
\draw[->] (v) to[bend right=12] node[above, sloped] {$F_3$} (f3.west);
\node[font=\footnotesize, rotate=90] at (7.6,0) {pairwise orthogonal};
\draw[->, dashed] (f3.south) to[out=-120, in=-70] node[pos=0.5, fill=white, inner sep=2pt] {$\mathcal R$: find $k$, apply $(F_k/\sqrt{d_k})^*$} (v.south);
\end{tikzpicture}\\[0.4em]
{\small Why the conditions suffice.  Diagonalising $(\alpha_{ij})=u\,\mathrm{diag}(d)\,u^*$ gives errors
$F_k=\sum_iu_{ik}E_i$ with the same channel and $PF_k^*F_lP=\delta_{kl}d_kP$: each $F_k/\sqrt{d_k}$ is an
isometry on $V$, and the images $F_kV$ are pairwise orthogonal.  The recovery measures which image the
state lies in and maps it back (\isa{recovery\_setting}).}
\end{center}
\<close>

lemma smult_cancel_nonzero:
  fixes P :: "complex Matrix.mat"
  assumes Pc: "P \<in> carrier_mat n n" and Pnz: "P \<noteq> 0\<^sub>m n n" and eq: "c \<cdot>\<^sub>m P = d \<cdot>\<^sub>m P"
  shows "c = d"
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
  have "c * P $$ (i,j) = d * P $$ (i,j)" using arg_cong[OF eq, of "\<lambda>M. M $$ (i,j)"] i j carrier_matD[OF Pc] by simp
  thus ?thesis using Pij by simp
qed

lemma outer_prod_smult_vec:
  fixes v :: "complex Matrix.vec"
  shows "(s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v) = (s * cnj s) \<cdot>\<^sub>m (v \<oslash> v)"
proof (rule eq_matI)
  have c1: "(s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v) \<in> carrier_mat (dim_vec v) (dim_vec v)" by (rule outer_prod_carrier) simp_all
  have c2: "v \<oslash> v \<in> carrier_mat (dim_vec v) (dim_vec v)" by (rule outer_prod_carrier) simp_all
  show "dim_row ((s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v)) = dim_row ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v))"
    using carrier_matD[OF c1] carrier_matD[OF c2] by simp
  show "dim_col ((s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v)) = dim_col ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v))"
    using carrier_matD[OF c1] carrier_matD[OF c2] by simp
  fix i j assume "i < dim_row ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v))" "j < dim_col ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v))"
  hence i: "i < dim_vec v" and j: "j < dim_vec v" using carrier_matD[OF c2] by simp_all
  have "((s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v)) $$ (i,j) = (s \<cdot>\<^sub>v v) $ i * cnj ((s \<cdot>\<^sub>v v) $ j)"
    by (rule outer_prod_index) (simp_all add: i j)
  also have "\<dots> = (s * cnj s) * (v $ i * cnj (v $ j))" using i j by simp
  also have "v $ i * cnj (v $ j) = (v \<oslash> v) $$ (i,j)" by (rule outer_prod_index[symmetric, OF i j])
  finally show "((s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v)) $$ (i,j) = ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v)) $$ (i,j)"
    using i j carrier_matD[OF c2] by simp
qed

lemma kraus_map_dim_foldr_add:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat n n" and fc: "\<forall>k \<in> set xs. f k \<in> carrier_mat n n"
  shows "kraus_map_dim n Ws (foldr (\<lambda>k acc. f k + acc) xs (0\<^sub>m n n))
         = foldr (\<lambda>k acc. kraus_map_dim n Ws (f k) + acc) xs (0\<^sub>m n n)"
  using fc
proof (induction xs)
  case Nil show ?case using Ws_c by (simp add: kraus_map_dim_zero)
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat n n" and rest: "\<forall>k \<in> set xs. f k \<in> carrier_mat n n" using Cons.prems by auto
  have rc: "foldr (\<lambda>k acc. f k + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n" by (rule foldr_add_carrier_dn[OF rest])
  show ?case using kraus_map_dim_add[OF fx rc Ws_c] Cons.IH[OF rest] by simp
qed

lemma kraus_map_dim_outer_as_foldr:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat n n" and \<psi>d: "dim_vec \<psi> = n"
  shows "kraus_map_dim n Ws (\<psi> \<oslash> \<psi>)
         = foldr (\<lambda>k acc. (Ws ! k *\<^sub>v \<psi>) \<oslash> (Ws ! k *\<^sub>v \<psi>) + acc) [0..<length Ws] (0\<^sub>m n n)"
proof -
  have "kraus_map_dim n Ws (\<psi> \<oslash> \<psi>) = foldr (\<lambda>k acc. Ws ! k * (\<psi> \<oslash> \<psi>) * ((Ws ! k)\<^sup>\<dagger>) + acc) [0..<length Ws] (0\<^sub>m n n)"
    unfolding kraus_map_dim_def by (rule foldr_list_as_index)
  also have "\<dots> = foldr (\<lambda>k acc. (Ws ! k *\<^sub>v \<psi>) \<oslash> (Ws ! k *\<^sub>v \<psi>) + acc) [0..<length Ws] (0\<^sub>m n n)"
  proof (rule foldr_add_mat_cong)
    fix k assume "k \<in> set [0..<length Ws]"
    hence "Ws ! k \<in> carrier_mat n n" using Ws_c by simp
    thus "Ws ! k * (\<psi> \<oslash> \<psi>) * ((Ws ! k)\<^sup>\<dagger>) = (Ws ! k *\<^sub>v \<psi>) \<oslash> (Ws ! k *\<^sub>v \<psi>)" by (rule conj_outer_prod[OF _ \<psi>d])
  qed
  finally show ?thesis .
qed

lemma foldr_smult_sandwich:
  fixes V :: "nat \<Rightarrow> complex Matrix.mat"
  assumes Mc: "M \<in> carrier_mat n n" and Nc: "N \<in> carrier_mat n n" and Pc: "P \<in> carrier_mat n n"
      and Vc: "\<forall>j < r. V j \<in> carrier_mat n n" and h: "\<forall>j < r. M * V j * N = \<beta> j \<cdot>\<^sub>m P"
  shows "M * foldr (\<lambda>j acc. b j \<cdot>\<^sub>m V j + acc) [0..<r] (0\<^sub>m n n) * N = (\<Sum>j<r. b j * \<beta> j) \<cdot>\<^sub>m P"
proof -
  have fc: "\<forall>j \<in> set [0..<r]. b j \<cdot>\<^sub>m V j \<in> carrier_mat n n" using Vc by auto
  have fc': "\<forall>j \<in> set [0..<r]. M * (b j \<cdot>\<^sub>m V j) \<in> carrier_mat n n"
  proof
    fix j assume "j \<in> set [0..<r]"
    hence "b j \<cdot>\<^sub>m V j \<in> carrier_mat n n" using fc by blast
    thus "M * (b j \<cdot>\<^sub>m V j) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Mc])
  qed
  have "M * foldr (\<lambda>j acc. b j \<cdot>\<^sub>m V j + acc) [0..<r] (0\<^sub>m n n) * N
        = foldr (\<lambda>j acc. M * (b j \<cdot>\<^sub>m V j) * N + acc) [0..<r] (0\<^sub>m n n)"
    unfolding foldr_add_mat_mult_left[OF Mc fc] by (rule foldr_add_mat_mult_right[OF Nc fc'])
  also have "\<dots> = foldr (\<lambda>j acc. (b j * \<beta> j) \<cdot>\<^sub>m P + acc) [0..<r] (0\<^sub>m n n)"
  proof (rule foldr_add_mat_cong)
    fix j assume "j \<in> set [0..<r]"
    hence j: "j < r" by simp
    have Vjc: "V j \<in> carrier_mat n n" using Vc j by simp
    have "M * (b j \<cdot>\<^sub>m V j) * N = b j \<cdot>\<^sub>m (M * V j * N)"
      by (simp only: mult_smult_distrib[OF Mc Vjc] mult_smult_assoc_mat[OF mult_carrier_mat[OF Mc Vjc] Nc])
    also have "\<dots> = (b j * \<beta> j) \<cdot>\<^sub>m P" using h j by (simp only: smult_smult_mat)
    finally show "M * (b j \<cdot>\<^sub>m V j) * N = (b j * \<beta> j) \<cdot>\<^sub>m P" .
  qed
  also have "\<dots> = sum_list (map (\<lambda>j. b j * \<beta> j) [0..<r]) \<cdot>\<^sub>m P"
    by (rule foldr_add_mat_smult_pull[OF _ Pc]) simp
  also have "sum_list (map (\<lambda>j. b j * \<beta> j) [0..<r]) = (\<Sum>j<r. b j * \<beta> j)"
    by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
  finally show ?thesis .
qed

lemma foldr_smult_dagger:
  fixes V :: "nat \<Rightarrow> complex Matrix.mat"
  assumes Vc: "\<forall>j < r. V j \<in> carrier_mat n n"
  shows "(foldr (\<lambda>j acc. b j \<cdot>\<^sub>m V j + acc) [0..<r] (0\<^sub>m n n))\<^sup>\<dagger>
         = foldr (\<lambda>j acc. cnj (b j) \<cdot>\<^sub>m ((V j)\<^sup>\<dagger>) + acc) [0..<r] (0\<^sub>m n n)"
proof -
  have fc: "\<forall>j \<in> set [0..<r]. b j \<cdot>\<^sub>m V j \<in> carrier_mat n n" using Vc by auto
  show ?thesis unfolding foldr_add_mat_dagger[OF fc]
    by (rule foldr_add_mat_cong) (simp only: dagger_of_smult)
qed

text \<open>The bracket $P\,(\sum_ia_iE_i)^*(\sum_jb_jE_j)\,P$ under the Knill--Laflamme conditions.\<close>

lemma kl_mix_bracket:
  assumes Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and Pc: "P \<in> carrier_mat n n"
      and kl: "\<forall>i < length Es. \<forall>j < length Es. P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P"
      and r: "r = length Es"
  shows "P * (((foldr (\<lambda>i acc. a i \<cdot>\<^sub>m (Es ! i) + acc) [0..<r] (0\<^sub>m n n))\<^sup>\<dagger>)
              * foldr (\<lambda>j acc. b j \<cdot>\<^sub>m (Es ! j) + acc) [0..<r] (0\<^sub>m n n)) * P
         = (\<Sum>j<r. b j * (\<Sum>i<r. cnj (a i) * \<alpha> i j)) \<cdot>\<^sub>m P"
proof -
  define Fa where "Fa = foldr (\<lambda>i acc. a i \<cdot>\<^sub>m (Es ! i) + acc) [0..<r] (0\<^sub>m n n)"
  define Fb where "Fb = foldr (\<lambda>j acc. b j \<cdot>\<^sub>m (Es ! j) + acc) [0..<r] (0\<^sub>m n n)"
  have Ec: "\<forall>j < r. Es ! j \<in> carrier_mat n n" using Es_c r by auto
  have Edc: "\<forall>j < r. (Es ! j)\<^sup>\<dagger> \<in> carrier_mat n n" using Ec by (auto intro: dagger_carrier)
  have Fac: "Fa \<in> carrier_mat n n" unfolding Fa_def by (rule foldr_add_carrier_dn) (use Ec in auto)
  have Fbc: "Fb \<in> carrier_mat n n" unfolding Fb_def by (rule foldr_add_carrier_dn) (use Ec in auto)
  have Fadc: "Fa\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Fac])
  have PFc: "P * (Fa\<^sup>\<dagger>) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Pc Fadc])
  have step1: "\<forall>j < r. (P * (Fa\<^sup>\<dagger>)) * Es ! j * P = (\<Sum>i<r. cnj (a i) * \<alpha> i j) \<cdot>\<^sub>m P"
  proof (intro allI impI)
    fix j assume j: "j < r"
    have Ejc: "Es ! j \<in> carrier_mat n n" using Ec j by simp
    have EPc: "Es ! j * P \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Ejc Pc])
    have h: "\<forall>i < r. P * ((Es ! i)\<^sup>\<dagger>) * (Es ! j * P) = \<alpha> i j \<cdot>\<^sub>m P"
    proof (intro allI impI)
      fix i assume i: "i < r"
      have Eidc: "(Es ! i)\<^sup>\<dagger> \<in> carrier_mat n n" using Edc i by simp
      have "P * ((Es ! i)\<^sup>\<dagger>) * (Es ! j * P) = (P * ((Es ! i)\<^sup>\<dagger>) * Es ! j) * P"
        by (rule assoc_mult_mat[OF mult_carrier_mat[OF Pc Eidc] Ejc Pc, symmetric])
      also have "\<dots> = P * ((Es ! i)\<^sup>\<dagger> * Es ! j) * P" by (simp only: assoc_mult_mat[OF Pc Eidc Ejc])
      also have "\<dots> = \<alpha> i j \<cdot>\<^sub>m P" using kl i j r by simp
      finally show "P * ((Es ! i)\<^sup>\<dagger>) * (Es ! j * P) = \<alpha> i j \<cdot>\<^sub>m P" .
    qed
    have "P * foldr (\<lambda>i acc. cnj (a i) \<cdot>\<^sub>m ((Es ! i)\<^sup>\<dagger>) + acc) [0..<r] (0\<^sub>m n n) * (Es ! j * P)
          = (\<Sum>i<r. cnj (a i) * \<alpha> i j) \<cdot>\<^sub>m P"
      by (rule foldr_smult_sandwich[OF Pc EPc Pc Edc h])
    hence "P * (Fa\<^sup>\<dagger>) * (Es ! j * P) = (\<Sum>i<r. cnj (a i) * \<alpha> i j) \<cdot>\<^sub>m P"
      unfolding Fa_def foldr_smult_dagger[OF Ec] .
    thus "(P * (Fa\<^sup>\<dagger>)) * Es ! j * P = (\<Sum>i<r. cnj (a i) * \<alpha> i j) \<cdot>\<^sub>m P"
      by (simp only: assoc_mult_mat[OF PFc Ejc Pc])
  qed
  have "(P * (Fa\<^sup>\<dagger>)) * Fb * P = (\<Sum>j<r. b j * (\<Sum>i<r. cnj (a i) * \<alpha> i j)) \<cdot>\<^sub>m P"
    unfolding Fb_def by (rule foldr_smult_sandwich[OF PFc Pc Pc Ec step1])
  thus ?thesis unfolding Fa_def[symmetric] Fb_def[symmetric] by (simp only: assoc_mult_mat[OF Pc Fadc Fbc])
qed

lemma dagger_sandwich:
  assumes Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" and Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n"
  shows "(P * ((A\<^sup>\<dagger>) * B) * P)\<^sup>\<dagger> = P * ((B\<^sup>\<dagger>) * A) * P"
proof -
  have Adc: "A\<^sup>\<dagger> \<in> carrier_mat n n" and Bdc: "B\<^sup>\<dagger> \<in> carrier_mat n n" using Ac Bc by (auto intro: dagger_carrier)
  have Yc: "(A\<^sup>\<dagger>) * B \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Adc Bc])
  have PYc: "P * ((A\<^sup>\<dagger>) * B) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Pc Yc])
  have "(P * ((A\<^sup>\<dagger>) * B) * P)\<^sup>\<dagger> = (P\<^sup>\<dagger>) * ((P * ((A\<^sup>\<dagger>) * B))\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp only: carrier_matD[OF PYc] carrier_matD[OF Pc])
  also have "(P * ((A\<^sup>\<dagger>) * B))\<^sup>\<dagger> = (((A\<^sup>\<dagger>) * B)\<^sup>\<dagger>) * (P\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp only: carrier_matD[OF Yc] carrier_matD[OF Pc])
  also have "((A\<^sup>\<dagger>) * B)\<^sup>\<dagger> = (B\<^sup>\<dagger>) * A"
    by (subst dagger_of_prod) (simp_all only: carrier_matD[OF Adc] carrier_matD[OF Bc] dagger_of_dagger_is_id)
  finally show ?thesis unfolding Ph
    by (simp only: assoc_mult_mat[OF Pc mult_carrier_mat[OF Bdc Ac] Pc])
qed

lemma smult_bracket:
  assumes Pc: "P \<in> carrier_mat n n" and Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n"
  shows "P * (((x \<cdot>\<^sub>m A)\<^sup>\<dagger>) * (y \<cdot>\<^sub>m B)) * P = (cnj x * y) \<cdot>\<^sub>m (P * ((A\<^sup>\<dagger>) * B) * P)"
proof -
  have Adc: "A\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Ac])
  have Yc: "(A\<^sup>\<dagger>) * B \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Adc Bc])
  have "((x \<cdot>\<^sub>m A)\<^sup>\<dagger>) * (y \<cdot>\<^sub>m B) = (cnj x * y) \<cdot>\<^sub>m ((A\<^sup>\<dagger>) * B)"
    by (simp only: dagger_of_smult mult_smult_assoc_mat[OF Adc smult_carrier_mat[OF Bc]]
          mult_smult_distrib[OF Adc Bc] smult_smult_mat)
  thus ?thesis
    by (simp only: mult_smult_distrib[OF Pc Yc] mult_smult_assoc_mat[OF mult_carrier_mat[OF Pc Yc] Pc])
qed

theorem knill_laflamme_sufficiency:
  assumes P: "projection n P" and Pnz: "P \<noteq> 0\<^sub>m n n" and npos: "0 < n"
      and Es: "kraus_operators n n Es"
      and kl: "\<forall>i < length Es. \<forall>j < length Es. P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P"
  shows "\<exists>As. kraus_operators n n As \<and>
           (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim n As (kraus_map_dim n Es (P * X * P)) = P * X * P)"
proof -
  let ?r = "length Es"
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" and PP: "P * P = P"
    using P by (auto simp: projection_def hermitian_def)
  have Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and Es_tp: "sum_wdag_w n Es = 1\<^sub>m n"
    using Es by (auto simp: kraus_operators_altdef)
  have Ec: "\<forall>j < ?r. Es ! j \<in> carrier_mat n n" using Es_c by auto
  \<comment> \<open>\<open>\<alpha>\<close> is Hermitian.\<close>
  have herm: "\<And>i j. i < ?r \<Longrightarrow> j < ?r \<Longrightarrow> cnj (\<alpha> j i) = \<alpha> i j"
  proof -
    fix i j assume i: "i < ?r" and j: "j < ?r"
    have "cnj (\<alpha> j i) \<cdot>\<^sub>m P = (\<alpha> j i \<cdot>\<^sub>m P)\<^sup>\<dagger>" by (simp only: dagger_of_smult Ph)
    also have "\<dots> = (P * (((Es ! j)\<^sup>\<dagger>) * Es ! i) * P)\<^sup>\<dagger>" using kl i j by simp
    also have "\<dots> = P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P"
      by (rule dagger_sandwich[OF Pc Ph]) (use Ec i j in simp_all)
    also have "\<dots> = \<alpha> i j \<cdot>\<^sub>m P" using kl i j by simp
    finally show "cnj (\<alpha> j i) = \<alpha> i j" by (rule smult_cancel_nonzero[OF Pc Pnz])
  qed
  define A where "A = Matrix.mat ?r ?r (\<lambda>(i,j). \<alpha> i j)"
  have Ac: "A \<in> carrier_mat ?r ?r" unfolding A_def by simp
  have Ah: "hermitian A" unfolding hermitian_def
    by (rule eq_matI) (auto simp: A_def dagger_def herm)
  obtain u :: "complex Matrix.mat" and D :: "real list"
    where uc: "u \<in> carrier_mat ?r ?r" and uu: "unitary u" and Dl: "length D = ?r"
      and spec: "(u\<^sup>\<dagger>) * A * u = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF Ac Ah] by blast
  have uud: "u * (u\<^sup>\<dagger>) = 1\<^sub>m ?r" using uu uc unfolding unitary_def by simp
  have udc: "u\<^sup>\<dagger> \<in> carrier_mat ?r ?r" by (rule dagger_carrier[OF uc])
  define G where "G = transpose_mat u"
  have Gc: "G \<in> carrier_mat ?r ?r" unfolding G_def using uc by simp
  have GG: "(G\<^sup>\<dagger>) * G = 1\<^sub>m ?r" unfolding G_def by (rule transpose_unitary_isometry[OF uc uud])
  define Fs where "Fs = kraus_mix n n G Es"
  have Fs_len: "length Fs = ?r" unfolding Fs_def using Gc by simp
  have Fs_nth: "\<And>k. k < ?r \<Longrightarrow> Fs ! k = foldr (\<lambda>j acc. u $$ (j,k) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n)"
  proof -
    fix k assume k: "k < ?r"
    have "Fs ! k = foldr (\<lambda>j acc. G $$ (k,j) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n)"
      unfolding Fs_def using kraus_mix_nth[of k G n n Es] k Gc by simp
    also have "\<dots> = foldr (\<lambda>j acc. u $$ (j,k) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n)"
      by (rule foldr_add_mat_cong) (use k uc in \<open>simp add: G_def\<close>)
    finally show "Fs ! k = foldr (\<lambda>j acc. u $$ (j,k) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n)" .
  qed
  have Fs_c: "\<forall>F \<in> set Fs. F \<in> carrier_mat n n" unfolding Fs_def by (rule kraus_mix_carrier[OF Es_c])
  have Fkc: "\<And>k. k < ?r \<Longrightarrow> Fs ! k \<in> carrier_mat n n" using Fs_c Fs_len by auto
  have same: "\<And>M. M \<in> carrier_mat n n \<Longrightarrow> kraus_map_dim n Fs M = kraus_map_dim n Es M"
    unfolding Fs_def by (rule kraus_mix_same_map[OF npos npos Es_c Gc GG])
  \<comment> \<open>\<open>PF\<^sub>k\<^sup>*F\<^sub>lP = \<delta>\<^sub>k\<^sub>l d\<^sub>k P\<close>.\<close>
  have bracket: "\<And>k l. k < ?r \<Longrightarrow> l < ?r \<Longrightarrow>
      P * (((Fs ! k)\<^sup>\<dagger>) * Fs ! l) * P = (if k = l then complex_of_real (D ! k) else 0) \<cdot>\<^sub>m P"
  proof -
    fix k l assume k: "k < ?r" and l: "l < ?r"
    have "P * (((Fs ! k)\<^sup>\<dagger>) * Fs ! l) * P
          = (\<Sum>j<?r. u $$ (j,l) * (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)) \<cdot>\<^sub>m P"
      unfolding Fs_nth[OF k] Fs_nth[OF l] by (rule kl_mix_bracket[OF Es_c Pc kl refl])
    also have "(\<Sum>j<?r. u $$ (j,l) * (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)) = ((u\<^sup>\<dagger>) * A * u) $$ (k,l)"
    proof -
      have uA: "(u\<^sup>\<dagger>) * A \<in> carrier_mat ?r ?r" by (rule mult_carrier_mat[OF udc Ac])
      have e1: "\<And>j. j < ?r \<Longrightarrow> ((u\<^sup>\<dagger>) * A) $$ (k,j) = (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)"
      proof -
        fix j assume j: "j < ?r"
        have "((u\<^sup>\<dagger>) * A) $$ (k,j) = (\<Sum>i<?r. (u\<^sup>\<dagger>) $$ (k,i) * A $$ (i,j))" by (rule mat_mult_entry[OF udc Ac k j])
        also have "\<dots> = (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)"
          by (rule sum.cong) (use k j uc in \<open>auto simp: A_def dagger_def\<close>)
        finally show "((u\<^sup>\<dagger>) * A) $$ (k,j) = (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)" .
      qed
      have "((u\<^sup>\<dagger>) * A * u) $$ (k,l) = (\<Sum>j<?r. ((u\<^sup>\<dagger>) * A) $$ (k,j) * u $$ (j,l))" by (rule mat_mult_entry[OF uA uc k l])
      also have "\<dots> = (\<Sum>j<?r. u $$ (j,l) * (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j))"
        by (rule sum.cong) (simp_all add: e1 mult.commute)
      finally show ?thesis by simp
    qed
    also have "((u\<^sup>\<dagger>) * A * u) $$ (k,l) = (if k = l then complex_of_real (D ! k) else 0)"
      unfolding spec diag_mat_of_real_def mat_diag_def using k l Dl by simp
    finally show "P * (((Fs ! k)\<^sup>\<dagger>) * Fs ! l) * P = (if k = l then complex_of_real (D ! k) else 0) \<cdot>\<^sub>m P" .
  qed
  define d where "d = (\<lambda>k. D ! k)"
  \<comment> \<open>\<open>\<Sum>\<^sub>k d\<^sub>k = 1\<close>: both sides are \<open>Tr \<alpha>\<close>.\<close>
  have sum_alpha: "(\<Sum>j<?r. \<alpha> j j) = 1"
  proof -
    let ?V = "\<lambda>j. ((Es ! j)\<^sup>\<dagger>) * Es ! j"
    have Vc: "\<forall>j < ?r. ?V j \<in> carrier_mat n n" using Ec by (auto intro: mult_carrier_mat dagger_carrier)
    have h: "\<forall>j < ?r. P * ?V j * P = \<alpha> j j \<cdot>\<^sub>m P" using kl by simp
    have "sum_wdag_w n Es = foldr (\<lambda>j acc. ?V j + acc) [0..<?r] (0\<^sub>m n n)"
      unfolding sum_wdag_w_def by (rule foldr_list_as_index)
    also have "\<dots> = foldr (\<lambda>j acc. 1 \<cdot>\<^sub>m ?V j + acc) [0..<?r] (0\<^sub>m n n)"
      by (rule foldr_add_mat_cong) (simp only: one_smult_mat)
    finally have sw: "sum_wdag_w n Es = foldr (\<lambda>j acc. 1 \<cdot>\<^sub>m ?V j + acc) [0..<?r] (0\<^sub>m n n)" .
    have "P * sum_wdag_w n Es * P = (\<Sum>j<?r. 1 * \<alpha> j j) \<cdot>\<^sub>m P"
      unfolding sw by (rule foldr_smult_sandwich[OF Pc Pc Pc Vc h])
    moreover have "P * sum_wdag_w n Es * P = P" unfolding Es_tp by (simp only: right_mult_one_mat[OF Pc] PP)
    ultimately have "(\<Sum>j<?r. \<alpha> j j) \<cdot>\<^sub>m P = P" by simp
    thus ?thesis by (rule smult_eq_self_imp_one[OF Pc Pnz])
  qed
  have sum_d: "(\<Sum>k<?r. complex_of_real (d k)) = 1"
  proof -
    have "Tr ((u\<^sup>\<dagger>) * A * u) = Tr A" by (rule Tr_unitary_conjugation[OF uu]) (use Ac uc in simp_all)
    moreover have "Tr ((u\<^sup>\<dagger>) * A * u) = (\<Sum>k<?r. complex_of_real (d k))"
      unfolding spec Tr_def diag_mat_of_real_def mat_diag_def d_def using Dl by simp
    moreover have "Tr A = (\<Sum>j<?r. \<alpha> j j)" unfolding Tr_def A_def by simp
    ultimately show ?thesis using sum_alpha by simp
  qed
  \<comment> \<open>Each \<open>d\<^sub>k \<ge> 0\<close>, and \<open>d\<^sub>k = 0\<close> forces \<open>F\<^sub>kP = 0\<close>.\<close>
  have FPFP: "\<And>k. k < ?r \<Longrightarrow> ((Fs ! k * P)\<^sup>\<dagger>) * (Fs ! k * P) = complex_of_real (d k) \<cdot>\<^sub>m P"
  proof -
    fix k assume k: "k < ?r"
    have Fc: "Fs ! k \<in> carrier_mat n n" by (rule Fkc[OF k])
    have Fdc: "(Fs ! k)\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Fc])
    have "(Fs ! k * P)\<^sup>\<dagger> = P * ((Fs ! k)\<^sup>\<dagger>)"
      by (subst dagger_of_prod) (simp_all only: carrier_matD[OF Fc] carrier_matD[OF Pc] Ph)
    hence "((Fs ! k * P)\<^sup>\<dagger>) * (Fs ! k * P) = (P * ((Fs ! k)\<^sup>\<dagger>)) * (Fs ! k * P)" by simp
    also have "\<dots> = (P * ((Fs ! k)\<^sup>\<dagger>) * Fs ! k) * P"
      by (rule assoc_mult_mat[OF mult_carrier_mat[OF Pc Fdc] Fc Pc, symmetric])
    also have "\<dots> = P * (((Fs ! k)\<^sup>\<dagger>) * Fs ! k) * P" by (simp only: assoc_mult_mat[OF Pc Fdc Fc])
    also have "\<dots> = complex_of_real (d k) \<cdot>\<^sub>m P" using bracket[OF k k] by (simp add: d_def)
    finally show "((Fs ! k * P)\<^sup>\<dagger>) * (Fs ! k * P) = complex_of_real (d k) \<cdot>\<^sub>m P" .
  qed
  have TrP: "0 < Re (Tr P)"
  proof -
    have Ppsd: "psd P" using psd_MdagM[OF Pc] unfolding Ph PP .
    have "Tr P \<noteq> 0" using psd_Tr_zero_imp_zero[OF Pc Ppsd] Pnz by blast
    moreover have "complex_of_real (Re (Tr P)) = Tr P"
      by (rule Tr_hermitian_real[OF Pc, symmetric]) (simp add: hermitian_def Ph)
    ultimately have "Re (Tr P) \<noteq> 0" unfolding of_real_eq_0_iff[where 'a = complex, symmetric] by simp
    thus ?thesis using Tr_psd_Re_nonneg[OF Ppsd Pc] by simp
  qed
  have d_nonneg: "\<And>k. k < ?r \<Longrightarrow> 0 \<le> d k"
  proof -
    fix k assume k: "k < ?r"
    have FPc: "Fs ! k * P \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Fkc[OF k] Pc])
    have "psd (complex_of_real (d k) \<cdot>\<^sub>m P)" using psd_MdagM[OF FPc] unfolding FPFP[OF k] .
    hence "0 \<le> Re (Tr (complex_of_real (d k) \<cdot>\<^sub>m P))" by (rule Tr_psd_Re_nonneg[where n=n]) (use Pc in simp)
    hence "0 \<le> d k * Re (Tr P)" by (simp add: Tr_smult)
    thus "0 \<le> d k" using TrP by (simp add: zero_le_mult_iff)
  qed
  have kill: "\<And>k. k < ?r \<Longrightarrow> d k = 0 \<Longrightarrow> Fs ! k * P = 0\<^sub>m n n"
  proof -
    fix k assume k: "k < ?r" and d0: "d k = 0"
    have FPc: "Fs ! k * P \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Fkc[OF k] Pc])
    have "((Fs ! k * P)\<^sup>\<dagger>) * (Fs ! k * P) = 0\<^sub>m n n" unfolding FPFP[OF k] d0 of_real_0 by (rule zero_smult_mat_carrier[OF Pc])
    thus "Fs ! k * P = 0\<^sub>m n n" by (rule dagger_mult_zero_imp_zero[OF FPc])
  qed
  \<comment> \<open>The rescaled errors with \<open>d\<^sub>k > 0\<close>.\<close>
  define ks where "ks = filter (\<lambda>k. 0 < d k) [0..<?r]"
  define c where "c = (\<lambda>k. complex_of_real (1 / sqrt (d k)))"
  define Us where "Us = map (\<lambda>k. c k \<cdot>\<^sub>m Fs ! k) ks"
  have ks_dist: "distinct ks" unfolding ks_def by simp
  have ks_nth: "\<And>a. a < length ks \<Longrightarrow> ks ! a < ?r \<and> 0 < d (ks ! a)"
  proof -
    fix a assume "a < length ks"
    hence "ks ! a \<in> set ks" by (rule nth_mem)
    thus "ks ! a < ?r \<and> 0 < d (ks ! a)" unfolding ks_def by simp
  qed
  have Us_len: "length Us = length ks" unfolding Us_def by simp
  have Us_nth: "\<And>a. a < length ks \<Longrightarrow> Us ! a = c (ks ! a) \<cdot>\<^sub>m Fs ! (ks ! a)" unfolding Us_def by simp
  have S: "recovery_setting n P Us"
    unfolding recovery_setting_def
  proof (intro conjI ballI allI impI)
    show "projection n P" by (rule P)
  next
    fix U assume "U \<in> set Us"
    then obtain a where a: "a < length ks" and "U = Us ! a" unfolding Us_len[symmetric] by (auto simp: in_set_conv_nth)
    thus "U \<in> carrier_mat n n" using Us_nth[OF a] Fkc ks_nth[OF a] by simp
  next
    fix a b assume a: "a < length Us" and b: "b < length Us"
    have a': "a < length ks" and b': "b < length ks" using a b Us_len by simp_all
    let ?k = "ks ! a" and ?l = "ks ! b"
    have k: "?k < ?r" and dk: "0 < d ?k" and l: "?l < ?r" using ks_nth[OF a'] ks_nth[OF b'] by simp_all
    have "P * (((Us ! a)\<^sup>\<dagger>) * Us ! b) * P = (cnj (c ?k) * c ?l) \<cdot>\<^sub>m (P * (((Fs ! ?k)\<^sup>\<dagger>) * Fs ! ?l) * P)"
      unfolding Us_nth[OF a'] Us_nth[OF b'] by (rule smult_bracket[OF Pc Fkc[OF k] Fkc[OF l]])
    also have "\<dots> = (cnj (c ?k) * c ?l * (if ?k = ?l then complex_of_real (D ! ?k) else 0)) \<cdot>\<^sub>m P"
      unfolding bracket[OF k l] smult_smult_mat ..
    also have "\<dots> = (if a = b then P else 0\<^sub>m n n)"
    proof (cases "a = b")
      case True
      have e1: "cnj (c ?k) * c ?k * complex_of_real (D ! ?k)
            = complex_of_real ((1 / sqrt (d ?k)) * (1 / sqrt (d ?k)) * d ?k)"
        by (simp only: c_def d_def complex_cnj_complex_of_real of_real_mult)
      have ss: "sqrt (d ?k) * sqrt (d ?k) = d ?k" using dk by simp
      have r1: "(1 / sqrt (d ?k)) * (1 / sqrt (d ?k)) * d ?k = d ?k / (sqrt (d ?k) * sqrt (d ?k))" by simp
      have r2: "(1 / sqrt (d ?k)) * (1 / sqrt (d ?k)) * d ?k = 1" using r1 unfolding ss using dk by simp
      have "cnj (c ?k) * c ?k * complex_of_real (D ! ?k) = 1" using e1 r2 by simp
      thus ?thesis using True by (simp add: one_smult_mat)
    next
      case False
      hence "?k \<noteq> ?l" using nth_eq_iff_index_eq[OF ks_dist a' b'] by simp
      thus ?thesis using False by (simp add: zero_smult_mat_carrier[OF Pc])
    qed
    finally show "P * (((Us ! a)\<^sup>\<dagger>) * Us ! b) * P = (if a = b then P else 0\<^sub>m n n)" .
  qed
  define Rs where "Rs = recovery_ops n P Us"
  have Rs: "kraus_operators n n Rs" unfolding Rs_def by (rule recovery_ops_kraus_operators[OF S])
  have Rs_c: "\<forall>R \<in> set Rs. R \<in> carrier_mat n n" using Rs by (auto simp: kraus_operators_altdef)
  \<comment> \<open>Each error term is recovered up to the weight \<open>d\<^sub>k\<close>.\<close>
  have rec_term: "\<And>\<psi> k. dim_vec \<psi> = n \<Longrightarrow> P *\<^sub>v \<psi> = \<psi> \<Longrightarrow> k < ?r \<Longrightarrow>
      kraus_map_dim n Rs ((Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)) = complex_of_real (d k) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
  proof -
    fix \<psi> :: "complex Matrix.vec" and k
    assume \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>" and k: "k < ?r"
    have \<psi>c: "\<psi> \<in> carrier_vec n" by (rule carrier_vecI[OF \<psi>d])
    have oc: "\<psi> \<oslash> \<psi> \<in> carrier_mat n n" by (rule outer_prod_carrier[OF \<psi>d \<psi>d])
    show "kraus_map_dim n Rs ((Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)) = complex_of_real (d k) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
    proof (cases "0 < d k")
      case True
      have "k \<in> set ks" unfolding ks_def using k True by simp
      then obtain a where a: "a < length ks" and ka: "ks ! a = k" by (auto simp: in_set_conv_nth)
      have aU: "a < length Us" using a Us_len by simp
      have Ua: "Us ! a = c k \<cdot>\<^sub>m Fs ! k" using Us_nth[OF a] ka by simp
      have Fk: "Fs ! k = complex_of_real (sqrt (d k)) \<cdot>\<^sub>m (Us ! a)"
        unfolding Ua smult_smult_mat c_def using True
        by (simp add: of_real_mult[symmetric] one_smult_mat del: of_real_mult)
      have "Fs ! k *\<^sub>v \<psi> = complex_of_real (sqrt (d k)) \<cdot>\<^sub>v (Us ! a *\<^sub>v \<psi>)"
        unfolding Fk by (rule smult_mat_mult_vec[OF carrier_matI[OF refl refl] carrier_vecI]) (use rec_Uc[OF S aU] \<psi>d in simp)
      hence "(Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)
             = (complex_of_real (sqrt (d k)) * cnj (complex_of_real (sqrt (d k))))
               \<cdot>\<^sub>m ((Us ! a *\<^sub>v \<psi>) \<oslash> (Us ! a *\<^sub>v \<psi>))"
        by (simp only: outer_prod_smult_vec)
      moreover have "complex_of_real (sqrt (d k)) * cnj (complex_of_real (sqrt (d k))) = complex_of_real (d k)"
      proof -
        have "sqrt (d k) * sqrt (d k) = d k" using True by simp
        thus ?thesis by (simp only: complex_cnj_complex_of_real of_real_mult[symmetric])
      qed
      ultimately have "(Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)
             = complex_of_real (d k) \<cdot>\<^sub>m ((Us ! a *\<^sub>v \<psi>) \<oslash> (Us ! a *\<^sub>v \<psi>))" by simp
      moreover have "(Us ! a *\<^sub>v \<psi>) \<oslash> (Us ! a *\<^sub>v \<psi>) \<in> carrier_mat n n"
        by (rule outer_prod_carrier) (use rec_Uc[OF S aU] in simp_all)
      ultimately show ?thesis
        unfolding Rs_def using kraus_map_dim_smult[OF _ Rs_c[unfolded Rs_def]]
          recovery_single_error[OF S \<psi>d \<psi>V aU] by simp
    next
      case False
      hence d0: "d k = 0" using d_nonneg[OF k] by simp
      have "Fs ! k *\<^sub>v \<psi> = (Fs ! k * P) *\<^sub>v \<psi>"
        by (simp only: assoc_mult_mat_vec[OF Fkc[OF k] Pc \<psi>c] \<psi>V)
      also have "\<dots> = 0\<^sub>v n" unfolding kill[OF k d0] by (rule zero_mat_mult_vec[OF \<psi>d])
      finally have "Fs ! k *\<^sub>v \<psi> = 0\<^sub>v n" .
      thus ?thesis using d0 Rs_c by (simp add: outer_prod_zero_vec kraus_map_dim_zero zero_smult_mat_carrier[OF oc])
    qed
  qed
  have pure: "\<forall>\<psi>. dim_vec \<psi> = n \<longrightarrow> P *\<^sub>v \<psi> = \<psi> \<longrightarrow> recover_after n Rs Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>"
  proof (intro allI impI)
    fix \<psi> :: "complex Matrix.vec" assume \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>"
    have oc: "\<psi> \<oslash> \<psi> \<in> carrier_mat n n" by (rule outer_prod_carrier[OF \<psi>d \<psi>d])
    have tc: "\<forall>k \<in> set [0..<?r]. (Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>) \<in> carrier_mat n n"
    proof
      fix k assume "k \<in> set [0..<?r]"
      hence "Fs ! k \<in> carrier_mat n n" using Fkc by simp
      thus "(Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>) \<in> carrier_mat n n" by (intro outer_prod_carrier) simp_all
    qed
    have "recover_after n Rs Es (\<psi> \<oslash> \<psi>) = kraus_map_dim n Rs (kraus_map_dim n Fs (\<psi> \<oslash> \<psi>))"
      unfolding recover_after_def same[OF oc] ..
    also have "kraus_map_dim n Fs (\<psi> \<oslash> \<psi>)
               = foldr (\<lambda>k acc. (Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>) + acc) [0..<?r] (0\<^sub>m n n)"
      using kraus_map_dim_outer_as_foldr[OF Fs_c \<psi>d] unfolding Fs_len .
    also have "kraus_map_dim n Rs \<dots>
               = foldr (\<lambda>k acc. kraus_map_dim n Rs ((Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)) + acc) [0..<?r] (0\<^sub>m n n)"
      by (rule kraus_map_dim_foldr_add[OF Rs_c tc])
    also have "\<dots> = sum_list (map (\<lambda>k. complex_of_real (d k)) [0..<?r]) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
      by (rule foldr_add_mat_smult_pull[OF _ oc]) (use rec_term[OF \<psi>d \<psi>V] in simp)
    also have "sum_list (map (\<lambda>k. complex_of_real (d k)) [0..<?r]) = 1"
      using sum_d by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
    finally show "recover_after n Rs Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>" by (simp only: one_smult_mat)
  qed
  have "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> recover_after n Rs Es (P * X * P) = P * X * P"
    using recovery_states_iff_PXP[OF Rs_c Es_c P] pure by blast
  thus ?thesis using Rs unfolding recover_after_def by blast
qed

text \<open>D34-2 (Theorem 1): the code is correctable iff $PE_i^*E_jP=\alpha_{ij}P$.\<close>

theorem knill_laflamme:
  assumes P: "projection n P" and Pnz: "P \<noteq> 0\<^sub>m n n" and npos: "0 < n"
      and Es: "kraus_operators n n Es"
  shows "(\<exists>As. kraus_operators n n As \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim n As (kraus_map_dim n Es (P * X * P)) = P * X * P))
         \<longleftrightarrow> (\<exists>\<alpha> :: nat \<Rightarrow> nat \<Rightarrow> complex. \<forall>i < length Es. \<forall>j < length Es.
                P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P)"
  using knill_laflamme_necessity[OF P Pnz npos _ Es] knill_laflamme_sufficiency[OF P Pnz npos Es] by blast

end
