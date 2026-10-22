theory Day23_Choi3_UCP
  imports Day22_Adjoint_Maps
begin

section \<open>Day 23: Choi's Theorem 3 for unital maps (D23-1)\<close>

text \<open>The notes state Choi's Theorem 3 for UCP maps; @{thm [source] choi_theorem_3_cptp_iff} proves
the CPTP form.  The UCP form follows by the duality of Day 22: $\Gamma(\Phi)=\Phi^*$ maps midpoint
decompositions of a UCP map to midpoint decompositions of its adjoint and back
(\<open>extreme_UCP_iff_adjoint\<close>), and the Kraus operators of $\Phi^*$ are the adjoints $W_i^*$,
which are linearly independent with the $W_i$.  Extremality is the carrier-point notion used for
CPTP maps.\<close>

text \<open>The UCP-side midpoint relation and extremality, mirroring \<^const>\<open>cptp_pair_mid\<close> and
\<^const>\<open>extreme_CPTP_carrier\<close>.\<close>

definition ucp_pair_mid ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat)
     \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "ucp_pair_mid n d \<Phi> \<Phi>\<^sub>1 \<Phi>\<^sub>2 \<equiv>
     \<Phi>\<^sub>1 \<in> UCP n d \<and> \<Phi>\<^sub>2 \<in> UCP n d \<and>
     (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>\<^sub>1 X \<in> carrier_mat d d) \<and>
     (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>\<^sub>2 X \<in> carrier_mat d d) \<and>
     lin_on_carrier n \<Phi>\<^sub>1 \<and> lin_on_carrier n \<Phi>\<^sub>2 \<and>
     (\<exists>X\<^sub>1 \<in> carrier_mat n n. \<Phi>\<^sub>1 X\<^sub>1 \<noteq> \<Phi> X\<^sub>1) \<and>
     (\<exists>X\<^sub>2 \<in> carrier_mat n n. \<Phi> X\<^sub>2 \<noteq> \<Phi>\<^sub>2 X\<^sub>2) \<and>
     (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>\<^sub>2 X)"

definition extreme_UCP_carrier :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "extreme_UCP_carrier n d \<Phi> \<equiv> \<Phi> \<in> UCP n d \<and> \<not> (\<exists>\<Phi>\<^sub>1 \<Phi>\<^sub>2. ucp_pair_mid n d \<Phi> \<Phi>\<^sub>1 \<Phi>\<^sub>2)"

lemma lin_on_from_carrier:
  assumes "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X \<in> carrier_mat d d" "lin_on_carrier n \<Phi>"
  shows "lin_on n d (carrier_mat n n) \<Phi>"
  unfolding lin_on_def
proof (intro conjI ballI allI)
  fix A B :: "complex Matrix.mat" assume "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  thus "\<Phi> (A + B) = \<Phi> A + \<Phi> B" using assms(2) unfolding lin_on_carrier_def by blast
next
  fix A :: "complex Matrix.mat" and c :: complex assume "A \<in> carrier_mat n n"
  thus "\<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A" using assms(2) unfolding lin_on_carrier_def by blast
next
  fix A :: "complex Matrix.mat" assume "A \<in> carrier_mat n n"
  thus "\<Phi> A \<in> carrier_mat d d" using assms(1) by blast
qed

lemma lin_on_carrier_from_lin_on: "lin_on n d (carrier_mat n n) \<Phi> \<Longrightarrow> lin_on_carrier n \<Phi>"
  unfolding lin_on_def lin_on_carrier_def by blast

lemma map_adjoint_half:
  assumes L1: "lin_on n d (carrier_mat n n) \<Phi>1" and L2: "lin_on n d (carrier_mat n n) \<Phi>2" and Y: "Y \<in> carrier_mat d d"
  shows "map_adjoint n d (\<lambda>X. (1/2 :: complex) \<cdot>\<^sub>m \<Phi>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>2 X) Y
         = (1/2 :: complex) \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + (1/2 :: complex) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y"
  using map_adjoint_affine[OF L1 L2 Y, of "1/2"] by simp

text \<open>$\Gamma$ carries midpoint decompositions to midpoint decompositions, in both directions.\<close>

lemma ucp_mid_imp_cptp_mid:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and mid: "ucp_pair_mid n d \<Phi> \<Phi>1 \<Phi>2" and n: "0 < n" and d: "0 < d"
  shows "cptp_pair_mid d n (map_adjoint n d \<Phi>) (map_adjoint n d \<Phi>1) (map_adjoint n d \<Phi>2)"
proof -
  have U1: "\<Phi>1 \<in> UCP n d" and U2: "\<Phi>2 \<in> UCP n d"
    and L1: "lin_on n d (carrier_mat n n) \<Phi>1" and L2: "lin_on n d (carrier_mat n n) \<Phi>2"
    and x1: "\<exists>X1 \<in> carrier_mat n n. \<Phi>1 X1 \<noteq> \<Phi> X1" and x2: "\<exists>X2 \<in> carrier_mat n n. \<Phi> X2 \<noteq> \<Phi>2 X2"
    and m: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>2 X"
  proof -
    note md = mid[unfolded ucp_pair_mid_def]
    show "\<Phi>1 \<in> UCP n d" "\<Phi>2 \<in> UCP n d" using md by simp_all
    show "lin_on n d (carrier_mat n n) \<Phi>1" by (rule lin_on_from_carrier) (use md in simp_all)
    show "lin_on n d (carrier_mat n n) \<Phi>2" by (rule lin_on_from_carrier) (use md in simp_all)
    show "\<exists>X1 \<in> carrier_mat n n. \<Phi>1 X1 \<noteq> \<Phi> X1" using md by blast
    show "\<exists>X2 \<in> carrier_mat n n. \<Phi> X2 \<noteq> \<Phi>2 X2" using md by blast
    show "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m \<Phi>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>2 X" using md by simp
  qed
  have diff: "\<exists>Y \<in> carrier_mat d d. map_adjoint n d \<Psi> Y \<noteq> map_adjoint n d \<Phi> Y"
    if L\<Psi>: "lin_on n d (carrier_mat n n) \<Psi>" and x: "\<exists>X \<in> carrier_mat n n. \<Psi> X \<noteq> \<Phi> X" for \<Psi>
  proof (rule ccontr)
    assume "\<not> (\<exists>Y \<in> carrier_mat d d. map_adjoint n d \<Psi> Y \<noteq> map_adjoint n d \<Phi> Y)"
    hence "map_adjoint d n (map_adjoint n d \<Psi>) = map_adjoint d n (map_adjoint n d \<Phi>)"
      by (intro map_adjoint_cong) blast
    hence "\<forall>X \<in> carrier_mat n n. \<Psi> X = \<Phi> X"
      using map_adjoint_adjoint[OF L\<Psi>] map_adjoint_adjoint[OF L] by metis
    thus False using x by blast
  qed
  have "map_adjoint n d \<Phi> Y = (1/2 :: complex) \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + (1/2 :: complex) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y"
    if Y: "Y \<in> carrier_mat d d" for Y
  proof -
    have "map_adjoint n d \<Phi> = map_adjoint n d (\<lambda>X. (1/2 :: complex) \<cdot>\<^sub>m \<Phi>1 X + (1/2 :: complex) \<cdot>\<^sub>m \<Phi>2 X)"
      by (rule map_adjoint_cong) (rule m)
    thus ?thesis using map_adjoint_half[OF L1 L2 Y] by simp
  qed
  moreover have "\<exists>Y \<in> carrier_mat d d. map_adjoint n d \<Phi> Y \<noteq> map_adjoint n d \<Phi>2 Y"
    using diff[OF L2] x2 by metis
  ultimately show ?thesis
    unfolding cptp_pair_mid_def
    using adjoint_ucp_imp_cptp[OF L1 U1 n d] adjoint_ucp_imp_cptp[OF L2 U2 n d] diff[OF L1 x1]
          lin_on_carrier_from_lin_on[OF map_adjoint_lin] by auto
qed

lemma cptp_mid_imp_ucp_mid:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and mid: "cptp_pair_mid d n (map_adjoint n d \<Phi>) \<Psi>1 \<Psi>2"
      and n: "0 < n" and d: "0 < d"
  shows "ucp_pair_mid n d \<Phi> (map_adjoint d n \<Psi>1) (map_adjoint d n \<Psi>2)"
proof -
  have C1: "\<Psi>1 \<in> CPTP d n" and C2: "\<Psi>2 \<in> CPTP d n"
    and L1: "lin_on d n (carrier_mat d d) \<Psi>1" and L2: "lin_on d n (carrier_mat d d) \<Psi>2"
    and y1: "\<exists>Y1 \<in> carrier_mat d d. \<Psi>1 Y1 \<noteq> map_adjoint n d \<Phi> Y1"
    and y2: "\<exists>Y2 \<in> carrier_mat d d. map_adjoint n d \<Phi> Y2 \<noteq> \<Psi>2 Y2"
    and m: "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> map_adjoint n d \<Phi> Y = (1/2 :: complex) \<cdot>\<^sub>m \<Psi>1 Y + (1/2 :: complex) \<cdot>\<^sub>m \<Psi>2 Y"
  proof -
    note md = mid[unfolded cptp_pair_mid_def]
    show "\<Psi>1 \<in> CPTP d n" "\<Psi>2 \<in> CPTP d n" using md by simp_all
    show "lin_on d n (carrier_mat d d) \<Psi>1" by (rule lin_on_from_carrier) (use md in simp_all)
    show "lin_on d n (carrier_mat d d) \<Psi>2" by (rule lin_on_from_carrier) (use md in simp_all)
    show "\<exists>Y1 \<in> carrier_mat d d. \<Psi>1 Y1 \<noteq> map_adjoint n d \<Phi> Y1" using md by blast
    show "\<exists>Y2 \<in> carrier_mat d d. map_adjoint n d \<Phi> Y2 \<noteq> \<Psi>2 Y2" using md by blast
    show "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> map_adjoint n d \<Phi> Y = (1/2 :: complex) \<cdot>\<^sub>m \<Psi>1 Y + (1/2 :: complex) \<cdot>\<^sub>m \<Psi>2 Y" using md by simp
  qed
  have diff: "\<exists>X \<in> carrier_mat n n. map_adjoint d n \<Psi> X \<noteq> \<Phi> X"
    if L\<Psi>: "lin_on d n (carrier_mat d d) \<Psi>" and y: "\<exists>Y \<in> carrier_mat d d. \<Psi> Y \<noteq> map_adjoint n d \<Phi> Y" for \<Psi>
  proof (rule ccontr)
    assume "\<not> (\<exists>X \<in> carrier_mat n n. map_adjoint d n \<Psi> X \<noteq> \<Phi> X)"
    hence "map_adjoint n d (map_adjoint d n \<Psi>) = map_adjoint n d \<Phi>" by (intro map_adjoint_cong) blast
    hence "\<forall>Y \<in> carrier_mat d d. \<Psi> Y = map_adjoint n d \<Phi> Y" using map_adjoint_adjoint[OF L\<Psi>] by metis
    thus False using y by blast
  qed
  have "\<Phi> X = (1/2 :: complex) \<cdot>\<^sub>m map_adjoint d n \<Psi>1 X + (1/2 :: complex) \<cdot>\<^sub>m map_adjoint d n \<Psi>2 X"
    if X: "X \<in> carrier_mat n n" for X
  proof -
    have "\<Phi> X = map_adjoint d n (map_adjoint n d \<Phi>) X" using map_adjoint_adjoint[OF L X] by simp
    also have "map_adjoint d n (map_adjoint n d \<Phi>) = map_adjoint d n (\<lambda>Y. (1/2 :: complex) \<cdot>\<^sub>m \<Psi>1 Y + (1/2 :: complex) \<cdot>\<^sub>m \<Psi>2 Y)"
      by (rule map_adjoint_cong) (rule m)
    finally show ?thesis using map_adjoint_half[OF L1 L2 X] by simp
  qed
  moreover have "\<exists>X \<in> carrier_mat n n. \<Phi> X \<noteq> map_adjoint d n \<Psi>2 X"
  proof -
    have "\<exists>Y \<in> carrier_mat d d. \<Psi>2 Y \<noteq> map_adjoint n d \<Phi> Y" using y2 by metis
    thus ?thesis using diff[OF L2] by metis
  qed
  ultimately show ?thesis
    unfolding ucp_pair_mid_def
    using adjoint_cptp_imp_ucp[OF L1 C1 n d] adjoint_cptp_imp_ucp[OF L2 C2 n d] diff[OF L1 y1]
          lin_on_carrier_from_lin_on[OF map_adjoint_lin] by auto
qed

theorem extreme_UCP_iff_adjoint:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and U: "\<Phi> \<in> UCP n d" and n: "0 < n" and d: "0 < d"
  shows "extreme_UCP_carrier n d \<Phi> \<longleftrightarrow> extreme_CPTP_carrier d n (map_adjoint n d \<Phi>)"
  unfolding extreme_UCP_carrier_def extreme_CPTP_carrier_def
  using U adjoint_ucp_imp_cptp[OF L U n d] ucp_mid_imp_cptp_mid[OF L _ n d] cptp_mid_imp_ucp_mid[OF L _ n d] by blast

text \<open>Linear independence passes to the adjoints: $\sum_kc_kW_k^*=0$ gives $\sum_k\bar c_kW_k=0$.\<close>

lemma lin_indep_complex_mat_dagger:
  assumes li: "lin_indep_complex_mat d n Ws"
  shows "lin_indep_complex_mat n d (map (\<lambda>W. W\<^sup>\<dagger>) Ws)"
  unfolding lin_indep_complex_mat_def
proof (intro conjI allI impI)
  have Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" using li unfolding lin_indep_complex_mat_def by blast
  show "\<forall>W \<in> set (map (\<lambda>W. W\<^sup>\<dagger>) Ws). W \<in> carrier_mat n d" using Wc by (auto intro: dagger_carrier)
  fix c :: "nat \<Rightarrow> complex"
  assume z: "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (map (\<lambda>W. W\<^sup>\<dagger>) Ws ! k) + acc) [0..<length (map (\<lambda>W. W\<^sup>\<dagger>) Ws)] (0\<^sub>m n d) = 0\<^sub>m n d"
  let ?L = "length Ws"
  have kc: "\<And>k. k < ?L \<Longrightarrow> Ws ! k \<in> carrier_mat d n" using Wc by simp
  have fz: "foldr (\<lambda>k acc. cnj (c k) \<cdot>\<^sub>m (Ws ! k) + acc) [0..<?L] (0\<^sub>m d n) = 0\<^sub>m d n"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (0\<^sub>m d n :: complex Matrix.mat)" "j < dim_col (0\<^sub>m d n :: complex Matrix.mat)"
    hence i: "i < d" and j: "j < n" by simp_all
    have "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (map (\<lambda>W. W\<^sup>\<dagger>) Ws ! k) + acc) [0..<?L] (0\<^sub>m n d) $$ (j, i)
          = (\<Sum>k\<leftarrow>[0..<?L]. (c k \<cdot>\<^sub>m (map (\<lambda>W. W\<^sup>\<dagger>) Ws ! k)) $$ (j, i))"
      by (rule foldr_add_mat_index_rect) (use kc i j in \<open>auto intro!: smult_carrier_mat dagger_carrier\<close>)
    also have "\<dots> = (\<Sum>k\<leftarrow>[0..<?L]. c k * cnj (Ws ! k $$ (i, j)))"
    proof (rule arg_cong[where f = sum_list], rule map_cong[OF refl])
      fix k assume "k \<in> set [0..<?L]"
      hence k: "k < ?L" by simp
      show "(c k \<cdot>\<^sub>m (map (\<lambda>W. W\<^sup>\<dagger>) Ws ! k)) $$ (j, i) = c k * cnj (Ws ! k $$ (i, j))"
        using carrier_matD[OF kc[OF k]] i j k by (simp add: dagger_def)
    qed
    finally have "(\<Sum>k\<leftarrow>[0..<?L]. c k * cnj (Ws ! k $$ (i, j))) = 0" using z i j by simp
    hence "cnj (\<Sum>k\<leftarrow>[0..<?L]. c k * cnj (Ws ! k $$ (i, j))) = 0" by simp
    hence s0: "(\<Sum>k\<leftarrow>[0..<?L]. cnj (c k) * Ws ! k $$ (i, j)) = 0"
      by (simp add: sum_list_distinct_conv_sum_set)
    have "foldr (\<lambda>k acc. cnj (c k) \<cdot>\<^sub>m (Ws ! k) + acc) [0..<?L] (0\<^sub>m d n) $$ (i, j)
          = (\<Sum>k\<leftarrow>[0..<?L]. (cnj (c k) \<cdot>\<^sub>m (Ws ! k)) $$ (i, j))"
      by (rule foldr_add_mat_index_rect) (use kc i j in auto)
    also have "\<dots> = (\<Sum>k\<leftarrow>[0..<?L]. cnj (c k) * Ws ! k $$ (i, j))"
    proof (rule arg_cong[where f = sum_list], rule map_cong[OF refl])
      fix k assume "k \<in> set [0..<?L]"
      hence k: "k < ?L" by simp
      show "(cnj (c k) \<cdot>\<^sub>m (Ws ! k)) $$ (i, j) = cnj (c k) * Ws ! k $$ (i, j)"
        using carrier_matD[OF kc[OF k]] i j by simp
    qed
    finally show "foldr (\<lambda>k acc. cnj (c k) \<cdot>\<^sub>m (Ws ! k) + acc) [0..<?L] (0\<^sub>m d n) $$ (i, j) = 0\<^sub>m d n $$ (i, j)"
      using s0 i j by simp
  next
    show "dim_row (foldr (\<lambda>k acc. cnj (c k) \<cdot>\<^sub>m (Ws ! k) + acc) [0..<?L] (0\<^sub>m d n)) = dim_row (0\<^sub>m d n :: complex Matrix.mat)"
         "dim_col (foldr (\<lambda>k acc. cnj (c k) \<cdot>\<^sub>m (Ws ! k) + acc) [0..<?L] (0\<^sub>m d n)) = dim_col (0\<^sub>m d n :: complex Matrix.mat)"
      using carrier_matD[OF foldr_add_mat_carrier_rect[of "[0..<?L]" "\<lambda>k. cnj (c k) \<cdot>\<^sub>m (Ws ! k)" d n]] kc by auto
  qed
  have all: "\<And>c'. foldr (\<lambda>k acc. c' k \<cdot>\<^sub>m (Ws ! k) + acc) [0..<?L] (0\<^sub>m d n) = 0\<^sub>m d n \<Longrightarrow> \<forall>k < ?L. c' k = 0"
    using li unfolding lin_indep_complex_mat_def by blast
  have c0: "\<forall>k < ?L. cnj (c k) = 0" by (rule all[OF fz])
  fix k assume "k < length (map (\<lambda>W. W\<^sup>\<dagger>) Ws)"
  thus "c k = 0" using c0 by simp
qed

lemma kraus_operators_dagger_of_unital:
  assumes Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and un: "kraus_map_dim d Ws (1\<^sub>m n) = 1\<^sub>m d"
  shows "kraus_operators d n (map (\<lambda>W. W\<^sup>\<dagger>) Ws)"
  unfolding kraus_operators_def
proof
  show "\<forall>W \<in> set (map (\<lambda>W. W\<^sup>\<dagger>) Ws). W \<in> carrier_mat n d" using Wc by (auto intro: dagger_carrier)
  have "foldr (\<lambda>W acc. W\<^sup>\<dagger> * W + acc) (map (\<lambda>W. W\<^sup>\<dagger>) Ws) (0\<^sub>m d d)
        = foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d)"
    by (simp add: foldr_map comp_def dagger_of_dagger_is_id)
  also have "\<dots> = 1\<^sub>m d" using un kraus_map_dim_one[OF Wc] by simp
  finally show "foldr (\<lambda>W acc. W\<^sup>\<dagger> * W + acc) (map (\<lambda>W. W\<^sup>\<dagger>) Ws) (0\<^sub>m d d) = 1\<^sub>m d" .
qed

text \<open>Choi's Theorem 3: a unital CP map $\Phi(X)=\sum_iW_iXW_i^*$ with linearly independent $W_i$ is
extreme iff the products $W_jW_i^*$ are linearly independent (\<^const>\<open>kraus_products\<close> of the
adjoints, whose entries are $(W_j^*)^*W_i^*=W_jW_i^*$).  The notes write $\Phi(X)=\sum_iV_i^*XV_i$,
i.e.\ $V_i=W_i^*$, and the products $V_i^*V_j$.\<close>

theorem choi_theorem_3_ucp:
  assumes n: "0 < n" and d: "0 < d" and U: "\<Phi> \<in> UCP n d"
      and Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and rep: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Ws X"
      and li: "lin_indep_complex_mat d n Ws"
  shows "extreme_UCP_carrier n d \<Phi> \<longleftrightarrow> mat_lin_indep_complex d (kraus_products (map (\<lambda>W. W\<^sup>\<dagger>) Ws))"
proof -
  have L: "lin_on n d (carrier_mat n n) \<Phi>"
    using kraus_lin_on[OF Wc] rep unfolding lin_on_def by (simp add: add_carrier_mat smult_carrier_mat)
  let ?A = "map_adjoint n d \<Phi>" and ?Vs = "map (\<lambda>W. W\<^sup>\<dagger>) Ws"
  have adj: "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> ?A Y = kraus_map_dim n ?Vs Y"
  proof -
    fix Y :: "complex Matrix.mat" assume Y: "Y \<in> carrier_mat d d"
    have "?A = map_adjoint n d (kraus_map_dim d Ws)" by (rule map_adjoint_cong) (rule rep)
    hence "?A Y = kraus_adjoint_dim n Ws Y" using map_adjoint_kraus[OF Wc Y] by simp
    thus "?A Y = kraus_map_dim n ?Vs Y" using kraus_adjoint_dim_as_kraus_map_dim[OF Wc Y] by simp
  qed
  have un: "kraus_map_dim d Ws (1\<^sub>m n) = 1\<^sub>m d" using U rep[of "1\<^sub>m n"] by (simp add: UCP_def unital_map_def)
  have krep: "cptp_kraus_rep d n ?A ?Vs"
    unfolding cptp_kraus_rep_def using kraus_operators_dagger_of_unital[OF Wc un] adj by blast
  have "extreme_CPTP_carrier d n ?A \<longleftrightarrow> mat_lin_indep_complex d (kraus_products ?Vs)"
    by (rule choi_theorem_3_cptp_iff[OF d n adjoint_ucp_imp_cptp[OF L U n d] krep lin_indep_complex_mat_dagger[OF li]])
  thus ?thesis using extreme_UCP_iff_adjoint[OF L U n d] by simp
qed

end
