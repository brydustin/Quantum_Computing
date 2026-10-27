(*  Title:   Day23_Extremality_Examples.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 19 October 2011 (Day 23)
*)

theory Day23_Extremality_Examples
  imports Day23_Choi_Extreme_Points
begin

subsection \<open>Extreme and non-extreme maps (D23-4)\<close>

text \<open>Day 23, examples after Choi's Theorem 3, in the CPTP form and with the Kraus convention
$\Phi(X)=\sum_iW_iXW_i^*$ of the formalisation (the notes write $U^*XU$; replace $U$ by $U^*$).\<close>

subsubsection \<open>Linear dependence tests\<close>

lemma not_indep_of_dup:
  assumes a: "a < length Bs" and b: "b < length Bs" and ab: "a \<noteq> b" and eq: "Bs ! a = Bs ! b"
  shows "\<not> lin_indep_complex_mat n n Bs"
proof
  assume ind: "lin_indep_complex_mat n n Bs"
  hence Bs: "\<forall>B \<in> set Bs. B \<in> carrier_mat n n" unfolding lin_indep_complex_mat_def by simp
  let ?c = "\<lambda>k. if k = a then 1 else if k = b then -1 else (0::complex)"
  have z: "foldr (\<lambda>k acc. ?c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n n) = 0\<^sub>m n n"
  proof (rule eq_matI)
    fix r s assume "r < dim_row (0\<^sub>m n n :: complex Matrix.mat)" "s < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
    hence r: "r < n" and s: "s < n" by simp_all
    have "(\<Sum>k<length Bs. ?c k * Bs ! k $$ (r,s))
        = (\<Sum>k<length Bs. (if k = a then Bs ! a $$ (r,s) else 0) - (if k = b then Bs ! b $$ (r,s) else 0))"
      by (intro sum.cong refl) (use ab in auto)
    also have "\<dots> = 0" using a b eq by (simp add: sum_subtractf)
    finally show "foldr (\<lambda>k acc. ?c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n n) $$ (r,s) = 0\<^sub>m n n $$ (r,s)"
      using foldr_smult_index[OF Bs r s] r s by simp
  next
    show "dim_row (foldr (\<lambda>k acc. ?c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n n)) = dim_row (0\<^sub>m n n :: complex Matrix.mat)"
      "dim_col (foldr (\<lambda>k acc. ?c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n n)) = dim_col (0\<^sub>m n n :: complex Matrix.mat)"
      using foldr_add_mat_carrier_rect[of "[0..<length Bs]" "\<lambda>k. ?c k \<cdot>\<^sub>m (Bs ! k)" n n] Bs by auto
  qed
  have "?c a = 0" by (rule conjunct2[OF ind[unfolded lin_indep_complex_mat_def], rule_format, OF z a])
  thus False by simp
qed

lemma not_indep_of_zero:
  assumes a: "a < length Bs" and z: "Bs ! a = 0\<^sub>m n n"
  shows "\<not> lin_indep_complex_mat n n Bs"
proof
  assume ind: "lin_indep_complex_mat n n Bs"
  hence Bs: "\<forall>B \<in> set Bs. B \<in> carrier_mat n n" unfolding lin_indep_complex_mat_def by simp
  let ?c = "\<lambda>k. if k = a then 1 else (0::complex)"
  have z: "foldr (\<lambda>k acc. ?c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n n) = 0\<^sub>m n n"
  proof (rule eq_matI)
    fix r s assume "r < dim_row (0\<^sub>m n n :: complex Matrix.mat)" "s < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
    hence r: "r < n" and s: "s < n" by simp_all
    have "(\<Sum>k<length Bs. ?c k * Bs ! k $$ (r,s)) = (\<Sum>k<length Bs. if k = a then Bs ! a $$ (r,s) else 0)"
      by (intro sum.cong refl) auto
    also have "\<dots> = 0" using a z r s by simp
    finally show "foldr (\<lambda>k acc. ?c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n n) $$ (r,s) = 0\<^sub>m n n $$ (r,s)"
      using foldr_smult_index[OF Bs r s] r s by simp
  next
    show "dim_row (foldr (\<lambda>k acc. ?c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n n)) = dim_row (0\<^sub>m n n :: complex Matrix.mat)"
      "dim_col (foldr (\<lambda>k acc. ?c k \<cdot>\<^sub>m (Bs ! k) + acc) [0..<length Bs] (0\<^sub>m n n)) = dim_col (0\<^sub>m n n :: complex Matrix.mat)"
      using foldr_add_mat_carrier_rect[of "[0..<length Bs]" "\<lambda>k. ?c k \<cdot>\<^sub>m (Bs ! k)" n n] Bs by auto
  qed
  have "?c a = 0" by (rule conjunct2[OF ind[unfolded lin_indep_complex_mat_def], rule_format, OF z a])
  thus False by simp
qed

lemma single_lin_indep:
  assumes W: "W \<in> carrier_mat d n" and r: "r < d" and s: "s < n" and nz: "W $$ (r,s) \<noteq> 0"
  shows "lin_indep_complex_mat d n [W]"
  unfolding lin_indep_complex_mat_def
proof (intro conjI allI impI)
  show "\<forall>A \<in> set [W]. A \<in> carrier_mat d n" using W by simp
  fix c :: "nat \<Rightarrow> complex" and k
  assume "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m ([W] ! k) + acc) [0..<length [W]] (0\<^sub>m d n) = 0\<^sub>m d n" and k: "k < length [W]"
  hence "(c 0 \<cdot>\<^sub>m W + 0\<^sub>m d n) $$ (r,s) = 0\<^sub>m d n $$ (r,s)" by simp
  hence "c 0 * W $$ (r,s) = 0" using W r s by simp
  thus "c k = 0" using nz k by simp
qed

lemma single_mat_lin_indep:
  assumes B: "B \<in> carrier_mat n n" and r: "r < n" and s: "s < n" and nz: "B $$ (r,s) \<noteq> 0"
  shows "lin_indep_complex_mat n n [B]"
  unfolding lin_indep_complex_mat_def
proof (intro conjI allI impI)
  show "\<forall>A \<in> set [B]. A \<in> carrier_mat n n" using B by simp
  fix c :: "nat \<Rightarrow> complex" and k
  assume "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m ([B] ! k) + acc) [0..<length [B]] (0\<^sub>m n n) = 0\<^sub>m n n" and k: "k < length [B]"
  hence "(c 0 \<cdot>\<^sub>m B + 0\<^sub>m n n) $$ (r,s) = 0\<^sub>m n n $$ (r,s)" by simp
  hence "c 0 * B $$ (r,s) = 0" using B r s by simp
  thus "c k = 0" using nz k by simp
qed

subsubsection \<open>Example 1: unitary conjugation is extreme\<close>

theorem unitary_conjugation_extreme:
  assumes U: "U \<in> carrier_mat n n" and Uu: "unitary U" and n: "0 < n"
  shows "extreme_CPTP n n (kraus_map_dim n [U])"
proof -
  have UdU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n" using Uu U unfolding unitary_def by simp
  have K: "kraus_operators n n [U]" unfolding kraus_operators_def using U UdU by simp
  have nz: "U $$ (r,0) \<noteq> 0" if "False" for r using that by simp
  have "U \<noteq> 0\<^sub>m n n"
  proof
    assume "U = 0\<^sub>m n n"
    hence "(U\<^sup>\<dagger>) * U = 0\<^sub>m n n" by (simp add: dagger_def)
    hence "(1\<^sub>m n :: complex Matrix.mat) $$ (0,0) = 0\<^sub>m n n $$ (0,0)" using UdU by simp
    thus False using n by simp
  qed
  then obtain r s where rs: "r < n" "s < n" "U $$ (r,s) \<noteq> 0" by (rule nonzero_entry[OF U])
  have min: "lin_indep_complex_mat n n [U]" by (rule single_lin_indep[OF U rs])
  have kp: "kraus_products [U] = [1\<^sub>m n]" unfolding kraus_products_def using UdU by simp
  have ind: "lin_indep_complex_mat n n (kraus_products [U])"
    unfolding kp by (rule single_mat_lin_indep[of _ n 0 0]) (use n in simp_all)
  have rep: "cptp_kraus_rep n n (kraus_map_dim n [U]) [U]" unfolding cptp_kraus_rep_def using K by simp
  show ?thesis
    using choi_theorem_3_cptp_iff[OF n n kraus_is_cptp[OF K n n] rep min] ind by simp
qed

subsubsection \<open>Example 2: an average of two unitary conjugations\<close>

definition avg2 :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "avg2 U1 U2 = [(1 / csqrt 2) \<cdot>\<^sub>m U1, (1 / csqrt 2) \<cdot>\<^sub>m U2]"

lemma half_sq: "cnj (1 / csqrt 2) * (1 / csqrt 2) = 1/2"
proof -
  have e: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2" by (simp flip: of_real_mult)
  show ?thesis by (simp add: e)
qed

lemma smult_prod:
  fixes A B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat m k" "B \<in> carrier_mat k l"
  shows "(a \<cdot>\<^sub>m A) * (b \<cdot>\<^sub>m B) = (a * b) \<cdot>\<^sub>m (A * B)"
  using mult_smult_assoc_mat[OF assms(1) smult_carrier_mat[OF assms(2)]] mult_smult_distrib[OF assms]
  by (simp add: smult_smult_mat)

lemma smult_triple:
  fixes A X B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat m k" "X \<in> carrier_mat k k" "B \<in> carrier_mat k l"
  shows "(a \<cdot>\<^sub>m A) * X * (b \<cdot>\<^sub>m B) = (a * b) \<cdot>\<^sub>m (A * X * B)"
  using mult_smult_assoc_mat[OF assms(1,2)] smult_prod[OF mult_carrier_mat[OF assms(1,2)] assms(3), of a b]
  by simp

text \<open>The average of two unitary conjugations has the Kraus operators $W_k=\tfrac1{\sqrt2}U_k$:
$\sum_kW_kXW_k^*=\tfrac12(U_1XU_1^*+U_2XU_2^*)$, and $\sum_kW_k^*W_k=\tfrac12(I+I)=I$.\<close>

lemma avg2_products:
  assumes U1: "U1 \<in> carrier_mat n n" "unitary U1" and U2: "U2 \<in> carrier_mat n n" "unitary U2"
  shows "(avg2 U1 U2 ! 0)\<^sup>\<dagger> * avg2 U1 U2 ! 0 = (1/2) \<cdot>\<^sub>m 1\<^sub>m n"
    and "(avg2 U1 U2 ! 1)\<^sup>\<dagger> * avg2 U1 U2 ! 1 = (1/2) \<cdot>\<^sub>m 1\<^sub>m n"
proof -
  have e: "\<And>U. U \<in> carrier_mat n n \<Longrightarrow> unitary U \<Longrightarrow> ((1 / csqrt 2) \<cdot>\<^sub>m U)\<^sup>\<dagger> * ((1 / csqrt 2) \<cdot>\<^sub>m U) = (1/2) \<cdot>\<^sub>m 1\<^sub>m n"
  proof -
    fix U :: "complex Matrix.mat" assume Uc: "U \<in> carrier_mat n n" and Uu: "unitary U"
    have UdU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n" using Uu Uc unfolding unitary_def by simp
    have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Uc])
    have "((1 / csqrt 2) \<cdot>\<^sub>m U)\<^sup>\<dagger> * ((1 / csqrt 2) \<cdot>\<^sub>m U) = (cnj (1 / csqrt 2) * (1 / csqrt 2)) \<cdot>\<^sub>m ((U\<^sup>\<dagger>) * U)"
      unfolding dagger_of_smult by (rule smult_prod[OF Ud Uc])
    thus "((1 / csqrt 2) \<cdot>\<^sub>m U)\<^sup>\<dagger> * ((1 / csqrt 2) \<cdot>\<^sub>m U) = (1/2) \<cdot>\<^sub>m 1\<^sub>m n" unfolding UdU half_sq .
  qed
  show "(avg2 U1 U2 ! 0)\<^sup>\<dagger> * avg2 U1 U2 ! 0 = (1/2) \<cdot>\<^sub>m 1\<^sub>m n" using e[OF U1] by (simp add: avg2_def)
  show "(avg2 U1 U2 ! 1)\<^sup>\<dagger> * avg2 U1 U2 ! 1 = (1/2) \<cdot>\<^sub>m 1\<^sub>m n" using e[OF U2] by (simp add: avg2_def)
qed

lemma avg2_kraus:
  assumes U1: "U1 \<in> carrier_mat n n" "unitary U1" and U2: "U2 \<in> carrier_mat n n" "unitary U2"
  shows "kraus_operators n n (avg2 U1 U2)"
proof -
  have "(1/2) \<cdot>\<^sub>m 1\<^sub>m n + ((1/2) \<cdot>\<^sub>m 1\<^sub>m n + 0\<^sub>m n n) = (1\<^sub>m n :: complex Matrix.mat)"
    by (rule eq_matI) auto
  thus ?thesis unfolding kraus_operators_def using avg2_products[OF U1 U2] U1(1) U2(1)
    by (simp add: avg2_def)
qed

lemma avg2_map:
  assumes U1: "U1 \<in> carrier_mat n n" and U2: "U2 \<in> carrier_mat n n" and M: "M \<in> carrier_mat n n"
  shows "kraus_map_dim n (avg2 U1 U2) M = (1/2) \<cdot>\<^sub>m (U1 * M * (U1\<^sup>\<dagger>) + U2 * M * (U2\<^sup>\<dagger>))"
proof -
  have t: "\<And>U. U \<in> carrier_mat n n \<Longrightarrow>
      ((1 / csqrt 2) \<cdot>\<^sub>m U) * M * (((1 / csqrt 2) \<cdot>\<^sub>m U)\<^sup>\<dagger>) = (1/2) \<cdot>\<^sub>m (U * M * (U\<^sup>\<dagger>))"
  proof -
    fix U :: "complex Matrix.mat" assume Uc: "U \<in> carrier_mat n n"
    have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Uc])
    have "((1 / csqrt 2) \<cdot>\<^sub>m U) * M * (((1 / csqrt 2) \<cdot>\<^sub>m U)\<^sup>\<dagger>)
        = ((1 / csqrt 2) * cnj (1 / csqrt 2)) \<cdot>\<^sub>m (U * M * (U\<^sup>\<dagger>))"
      unfolding dagger_of_smult by (rule smult_triple[OF Uc M Ud])
    also have "(1 / csqrt 2) * cnj (1 / csqrt 2) = 1/2" using half_sq by (simp add: mult.commute)
    finally show "((1 / csqrt 2) \<cdot>\<^sub>m U) * M * (((1 / csqrt 2) \<cdot>\<^sub>m U)\<^sup>\<dagger>) = (1/2) \<cdot>\<^sub>m (U * M * (U\<^sup>\<dagger>))" .
  qed
  have c: "U1 * M * (U1\<^sup>\<dagger>) \<in> carrier_mat n n" "U2 * M * (U2\<^sup>\<dagger>) \<in> carrier_mat n n"
    using U1 U2 M by auto
  show ?thesis unfolding kraus_map_dim_def avg2_def using t[OF U1] t[OF U2] c
    by (simp add: add_smult_distrib_left_mat[OF c])
qed

text \<open>The notes' claim needs $U_1,U_2$ linearly independent: then the products
$V_i^*V_j$ contain $\tfrac12I$ twice and $\Phi$ is not extreme.\<close>

theorem avg2_not_extreme:
  assumes U1: "U1 \<in> carrier_mat n n" "unitary U1" and U2: "U2 \<in> carrier_mat n n" "unitary U2"
      and n: "0 < n" and ind: "lin_indep_complex_mat n n (avg2 U1 U2)"
  shows "\<not> extreme_CPTP n n (kraus_map_dim n (avg2 U1 U2))"
proof -
  have K: "kraus_operators n n (avg2 U1 U2)" by (rule avg2_kraus[OF U1 U2])
  have rep: "cptp_kraus_rep n n (kraus_map_dim n (avg2 U1 U2)) (avg2 U1 U2)"
    unfolding cptp_kraus_rep_def using K by simp
  have l: "length (avg2 U1 U2) = 2" by (simp add: avg2_def)
  have kp: "kraus_products (avg2 U1 U2) ! 0 = (avg2 U1 U2 ! 0)\<^sup>\<dagger> * avg2 U1 U2 ! 0"
           "kraus_products (avg2 U1 U2) ! 3 = (avg2 U1 U2 ! 1)\<^sup>\<dagger> * avg2 U1 U2 ! 1"
           "length (kraus_products (avg2 U1 U2)) = 4"
    unfolding kraus_products_def l by (simp_all add: upt_rec)
  have "\<not> lin_indep_complex_mat n n (kraus_products (avg2 U1 U2))"
    by (rule not_indep_of_dup[of 0 _ 3]) (use kp avg2_products[OF U1 U2] in simp_all)
  thus ?thesis using choi_theorem_3_cptp_iff[OF n n kraus_is_cptp[OF K n n] rep ind] by simp
qed

text \<open>Without that hypothesis the claim fails: for $U_2=\lambda U_1$ with $|\lambda|=1$ the map is
$X\mapsto U_1XU_1^*$, which is extreme.\<close>

theorem avg2_proportional_extreme:
  assumes U1: "U1 \<in> carrier_mat n n" "unitary U1" and lam: "cmod z = 1" and n: "0 < n"
  shows "extreme_CPTP n n (kraus_map_dim n (avg2 U1 (z \<cdot>\<^sub>m U1)))"
proof -
  have U2: "z \<cdot>\<^sub>m U1 \<in> carrier_mat n n" using U1 by simp
  have ll: "cnj z * z = 1" using lam by (metis complex_norm_square mult.commute of_real_1 power_one)
  have U1d: "U1\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U1(1)])
  have U2u: "unitary (z \<cdot>\<^sub>m U1)"
  proof -
    have "(cnj z \<cdot>\<^sub>m (U1\<^sup>\<dagger>)) * (z \<cdot>\<^sub>m U1) = (cnj z * z) \<cdot>\<^sub>m ((U1\<^sup>\<dagger>) * U1)" by (rule smult_prod[OF U1d U1(1)])
    moreover have "(z \<cdot>\<^sub>m U1) * (cnj z \<cdot>\<^sub>m (U1\<^sup>\<dagger>)) = (z * cnj z) \<cdot>\<^sub>m (U1 * (U1\<^sup>\<dagger>))" by (rule smult_prod[OF U1(1) U1d])
    ultimately show ?thesis using U1 ll unfolding unitary_def dagger_of_smult by (simp add: mult.commute one_smult_mat)
  qed
  have K: "kraus_operators n n (avg2 U1 (z \<cdot>\<^sub>m U1))" by (rule avg2_kraus[OF U1 U2 U2u])
  have eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim n (avg2 U1 (z \<cdot>\<^sub>m U1)) X = kraus_map_dim n [U1] X"
  proof (intro allI impI)
    fix X :: "complex Matrix.mat" assume X: "X \<in> carrier_mat n n"
    have c: "U1 * X * (U1\<^sup>\<dagger>) \<in> carrier_mat n n" using U1 X by auto
    have "(z \<cdot>\<^sub>m U1) * X * ((z \<cdot>\<^sub>m U1)\<^sup>\<dagger>) = (z * cnj z) \<cdot>\<^sub>m (U1 * X * (U1\<^sup>\<dagger>))"
      unfolding dagger_of_smult by (rule smult_triple[OF U1(1) X U1d])
    hence "(z \<cdot>\<^sub>m U1) * X * ((z \<cdot>\<^sub>m U1)\<^sup>\<dagger>) = U1 * X * (U1\<^sup>\<dagger>)" using ll c by (simp add: mult.commute one_smult_mat)
    hence "kraus_map_dim n (avg2 U1 (z \<cdot>\<^sub>m U1)) X = (1/2) \<cdot>\<^sub>m (U1 * X * (U1\<^sup>\<dagger>) + U1 * X * (U1\<^sup>\<dagger>))"
      using avg2_map[OF U1(1) U2 X] by simp
    also have "\<dots> = U1 * X * (U1\<^sup>\<dagger>)" by (rule eq_matI) (use c in auto)
    also have "\<dots> = kraus_map_dim n [U1] X" using c by (simp add: kraus_map_dim_def)
    finally show "kraus_map_dim n (avg2 U1 (z \<cdot>\<^sub>m U1)) X = kraus_map_dim n [U1] X" .
  qed
  have K1: "kraus_operators n n [U1]" unfolding kraus_operators_def using U1 unfolding unitary_def by simp
  have rep: "cptp_kraus_rep n n (kraus_map_dim n (avg2 U1 (z \<cdot>\<^sub>m U1))) [U1]"
    unfolding cptp_kraus_rep_def using K1 eq by simp
  have UdU: "(U1\<^sup>\<dagger>) * U1 = 1\<^sub>m n" using U1 unfolding unitary_def by simp
  have "U1 \<noteq> 0\<^sub>m n n"
  proof
    assume "U1 = 0\<^sub>m n n"
    hence "(U1\<^sup>\<dagger>) * U1 = 0\<^sub>m n n" by (simp add: dagger_def)
    hence "(1\<^sub>m n :: complex Matrix.mat) $$ (0,0) = 0\<^sub>m n n $$ (0,0)" using UdU by simp
    thus False using n by simp
  qed
  then obtain r s where rs: "r < n" "s < n" "U1 $$ (r,s) \<noteq> 0" by (rule nonzero_entry[OF U1(1)])
  have min: "lin_indep_complex_mat n n [U1]" by (rule single_lin_indep[OF U1(1) rs])
  have kp: "kraus_products [U1] = [1\<^sub>m n]" unfolding kraus_products_def using UdU by simp
  have ind: "lin_indep_complex_mat n n (kraus_products [U1])"
    unfolding kp by (rule single_mat_lin_indep[of _ n 0 0]) (use n in simp_all)
  show ?thesis using choi_theorem_3_cptp_iff[OF n n kraus_is_cptp[OF K n n] rep min] ind by simp
qed

subsubsection \<open>Example 3: $X\mapsto\Tr(X)\,I_d$\<close>

text \<open>As written, $\Phi(X)=\Tr(X)I_d$ is neither unital ($\Phi(I_n)=nI_d$) nor trace preserving
($\Tr\Phi(X)=d\Tr X$) unless $n=1$ resp.\ $d=1$.  The CPTP normalisation is
$\Phi(X)=\Tr(X)I_d/d$, with the $nd$ Kraus operators $E_{ab}/\sqrt d$; these are linearly
independent, so $\crk(\Phi)=nd>n$ for $d\ge2$ and $\Phi$ is not extreme (D22-6).\<close>

definition tr_kraus :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "tr_kraus n d = map (\<lambda>(a,b). complex_of_real (1 / sqrt (real d)) \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>) (List.product [0..<d] [0..<n])"

lemma tr_kraus_carrier: "\<forall>W \<in> set (tr_kraus n d). W \<in> carrier_mat d n"
  by (auto simp: tr_kraus_def mat_unit_def)

lemma tr_kraus_length: "length (tr_kraus n d) = d * n"
  by (simp add: tr_kraus_def)

lemma tr_scalar:
  assumes d: "0 < d"
  shows "cnj (complex_of_real (1 / sqrt (real d))) * complex_of_real (1 / sqrt (real d)) = 1 / of_nat d"
    and "complex_of_real (1 / sqrt (real d)) * cnj (complex_of_real (1 / sqrt (real d))) = 1 / of_nat d"
proof -
  have "(1 / sqrt (real d)) * (1 / sqrt (real d)) = 1 / real d"
    by (simp add: power2_eq_square[symmetric] power_divide)
  hence "complex_of_real (1 / sqrt (real d)) * complex_of_real (1 / sqrt (real d)) = 1 / of_nat d"
    by (metis of_real_mult of_real_divide of_real_1 of_real_of_nat_eq)
  thus "cnj (complex_of_real (1 / sqrt (real d))) * complex_of_real (1 / sqrt (real d)) = 1 / of_nat d"
       "complex_of_real (1 / sqrt (real d)) * cnj (complex_of_real (1 / sqrt (real d))) = 1 / of_nat d"
    by simp_all
qed

lemma tr_kraus_operators:
  assumes d: "0 < d"
  shows "kraus_operators n d (tr_kraus n d)"
  unfolding kraus_operators_def
proof (intro conjI)
  show "\<forall>W \<in> set (tr_kraus n d). W \<in> carrier_mat d n" by (rule tr_kraus_carrier)
  let ?c = "complex_of_real (1 / sqrt (real d))"
  have c: "\<forall>W \<in> set (tr_kraus n d). (W\<^sup>\<dagger>) * W \<in> carrier_mat n n"
  proof
    fix W assume "W \<in> set (tr_kraus n d)"
    hence Wc: "W \<in> carrier_mat d n" using tr_kraus_carrier by blast
    show "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n" using Wc dagger_carrier[OF Wc] by simp
  qed
  show "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) (tr_kraus n d) (0\<^sub>m n n) = 1\<^sub>m n"
  proof (rule eq_matI)
    fix r s assume "r < dim_row (1\<^sub>m n :: complex Matrix.mat)" "s < dim_col (1\<^sub>m n :: complex Matrix.mat)"
    hence r: "r < n" and s: "s < n" by simp_all
    have e: "\<And>a b. a < d \<Longrightarrow> b < n \<Longrightarrow>
        (((?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>)\<^sup>\<dagger>) * (?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>)) $$ (r,s) = (if r = b \<and> s = b then 1 / of_nat d else 0)"
    proof -
      fix a b assume a: "a < d" and b: "b < n"
      have u: "E\<lbrakk>a,b ; d,n\<rbrakk> \<in> carrier_mat d n" "E\<lbrakk>b,a ; n,d\<rbrakk> \<in> carrier_mat n d" by (simp_all add: mat_unit_def)
      have "((?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>)\<^sup>\<dagger>) * (?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>) = (1 / of_nat d) \<cdot>\<^sub>m (E\<lbrakk>b,a ; n,d\<rbrakk> * E\<lbrakk>a,b ; d,n\<rbrakk>)"
        unfolding dagger_of_smult mat_unit_dagger smult_prod[OF u(2) u(1)] tr_scalar[OF d] ..
      thus "(((?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>)\<^sup>\<dagger>) * (?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>)) $$ (r,s) = (if r = b \<and> s = b then 1 / of_nat d else 0)"
        using unit_mult_left_entry[OF u(1) r s a] r s b a by simp
    qed
    have "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) (tr_kraus n d) (0\<^sub>m n n) $$ (r,s) = (\<Sum>W\<leftarrow>tr_kraus n d. ((W\<^sup>\<dagger>) * W) $$ (r,s))"
      by (rule foldr_add_mat_index_rect[OF c r s])
    also have "\<dots> = (\<Sum>a<d. \<Sum>b<n. if r = b \<and> s = b then 1 / of_nat d else 0)"
      unfolding tr_kraus_def map_map comp_def sum_list_product_upt
      by (intro sum.cong refl) (simp only: case_prod_conv lessThan_iff; rule e; assumption)
    also have "\<dots> = (\<Sum>a<d. if r = s then 1 / of_nat d else 0)"
      by (intro sum.cong refl) (use r in \<open>auto simp: sum.delta\<close>)
    also have "\<dots> = (if r = s then 1 else 0)" using d by simp
    finally show "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) (tr_kraus n d) (0\<^sub>m n n) $$ (r,s) = 1\<^sub>m n $$ (r,s)"
      using r s by simp
  qed (use foldr_add_mat_carrier_rect[OF c] in auto)
qed

text \<open>$X\mapsto\frac{\Tr X}{d}I_d$ has the $dn$ Kraus operators $\frac1{\sqrt d}E_{ab}$:
\[ \frac1d\sum_{a,b}E_{ab}XE_{ba}=\frac1d\sum_a\Bigl(\sum_bx_{bb}\Bigr)E_{aa}=\frac{\Tr X}{d}\,I_d. \]\<close>

lemma tr_kraus_map:
  assumes d: "0 < d" and M: "M \<in> carrier_mat n n"
  shows "kraus_map_dim d (tr_kraus n d) M = (Tr M / of_nat d) \<cdot>\<^sub>m 1\<^sub>m d"
proof (rule eq_matI)
  let ?c = "complex_of_real (1 / sqrt (real d))"
  have c: "\<forall>W \<in> set (tr_kraus n d). W * M * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
  proof
    fix W assume "W \<in> set (tr_kraus n d)"
    hence Wc: "W \<in> carrier_mat d n" using tr_kraus_carrier by blast
    show "W * M * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using Wc M dagger_carrier[OF Wc] by simp
  qed
  fix r s assume "r < dim_row ((Tr M / of_nat d) \<cdot>\<^sub>m 1\<^sub>m d)" "s < dim_col ((Tr M / of_nat d) \<cdot>\<^sub>m 1\<^sub>m d)"
  hence r: "r < d" and s: "s < d" by simp_all
  have e: "\<And>a b. a < d \<Longrightarrow> b < n \<Longrightarrow>
      ((?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>) * M * ((?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>)\<^sup>\<dagger>)) $$ (r,s)
        = (if r = a \<and> s = a then M $$ (b,b) / of_nat d else 0)"
  proof -
    fix a b assume a: "a < d" and b: "b < n"
    have u: "E\<lbrakk>a,b ; d,n\<rbrakk> \<in> carrier_mat d n" "E\<lbrakk>b,a ; n,d\<rbrakk> \<in> carrier_mat n d" by (simp_all add: mat_unit_def)
    have um: "E\<lbrakk>a,b ; d,n\<rbrakk> * M \<in> carrier_mat d n" by (rule mult_carrier_mat[OF u(1) M])
    have "(?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>) * M * ((?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>)\<^sup>\<dagger>) = (1 / of_nat d) \<cdot>\<^sub>m (E\<lbrakk>a,b ; d,n\<rbrakk> * M * E\<lbrakk>b,a ; n,d\<rbrakk>)"
      unfolding dagger_of_smult mat_unit_dagger smult_triple[OF u(1) M u(2)] tr_scalar[OF d] ..
    moreover have "(E\<lbrakk>a,b ; d,n\<rbrakk> * M * E\<lbrakk>b,a ; n,d\<rbrakk>) $$ (r,s) = (if s = a then (if r = a then M $$ (b,b) else 0) else 0)"
      unfolding unit_mult_right_entry[OF um r s b] using unit_mult_left_entry[OF M r b b] by simp
    ultimately show "((?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>) * M * ((?c \<cdot>\<^sub>m E\<lbrakk>a,b ; d,n\<rbrakk>)\<^sup>\<dagger>)) $$ (r,s)
        = (if r = a \<and> s = a then M $$ (b,b) / of_nat d else 0)"
      using r s M by auto
  qed
  have "kraus_map_dim d (tr_kraus n d) M $$ (r,s) = (\<Sum>W\<leftarrow>tr_kraus n d. (W * M * (W\<^sup>\<dagger>)) $$ (r,s))"
    unfolding kraus_map_dim_def by (rule foldr_add_mat_index_rect[OF c r s])
  also have "\<dots> = (\<Sum>a<d. \<Sum>b<n. if r = a \<and> s = a then M $$ (b,b) / of_nat d else 0)"
    unfolding tr_kraus_def map_map comp_def sum_list_product_upt
      by (intro sum.cong refl) (simp only: case_prod_conv lessThan_iff; rule e; assumption)
  also have "\<dots> = (\<Sum>a<d. if r = a \<and> s = a then (\<Sum>b<n. M $$ (b,b)) / of_nat d else 0)"
  proof (intro sum.cong refl)
    fix a
    show "(\<Sum>b<n. if r = a \<and> s = a then M $$ (b,b) / of_nat d else 0)
        = (if r = a \<and> s = a then (\<Sum>b<n. M $$ (b,b)) / of_nat d else 0)"
    proof (cases "r = a \<and> s = a")
      case True thus ?thesis by (simp add: sum_divide_distrib)
    next
      case False thus ?thesis by (simp only: if_not_P[OF False] if_False sum.neutral_const)
    qed
  qed
  also have "\<dots> = (if r = s then (\<Sum>b<n. M $$ (b,b)) / of_nat d else 0)"
  proof (cases "r = s")
    case True thus ?thesis using r by (simp add: sum.delta)
  next
    case False
    have "\<forall>a \<in> {..<d}. (if r = a \<and> s = a then (\<Sum>b<n. M $$ (b,b)) / of_nat d else 0) = 0" using False by auto
    hence "(\<Sum>a<d. if r = a \<and> s = a then (\<Sum>b<n. M $$ (b,b)) / of_nat d else 0) = 0" by (rule sum.neutral)
    thus ?thesis using False by simp
  qed
  also have "(\<Sum>b<n. M $$ (b,b)) = Tr M" using M by (simp add: Tr_def)
  finally show "kraus_map_dim d (tr_kraus n d) M $$ (r,s) = ((Tr M / of_nat d) \<cdot>\<^sub>m 1\<^sub>m d) $$ (r,s)"
    using r s by simp
next
  have c: "\<forall>W \<in> set (tr_kraus n d). W * M * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
  proof
    fix W assume "W \<in> set (tr_kraus n d)"
    hence Wc: "W \<in> carrier_mat d n" using tr_kraus_carrier by blast
    show "W * M * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using Wc M dagger_carrier[OF Wc] by simp
  qed
  show "dim_row (kraus_map_dim d (tr_kraus n d) M) = dim_row ((Tr M / of_nat d) \<cdot>\<^sub>m 1\<^sub>m d)"
       "dim_col (kraus_map_dim d (tr_kraus n d) M) = dim_col ((Tr M / of_nat d) \<cdot>\<^sub>m 1\<^sub>m d)"
    using foldr_add_mat_carrier_rect[OF c] unfolding kraus_map_dim_def by auto
qed

lemma tr_kraus_lin_indep:
  assumes d: "0 < d" and n: "0 < n"
  shows "lin_indep_complex_mat d n (tr_kraus n d)"
  unfolding lin_indep_complex_mat_def
proof (intro conjI allI impI)
  show "\<forall>W \<in> set (tr_kraus n d). W \<in> carrier_mat d n" by (rule tr_kraus_carrier)
  fix c :: "nat \<Rightarrow> complex" and k
  assume z: "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (tr_kraus n d ! k) + acc) [0..<length (tr_kraus n d)] (0\<^sub>m d n) = 0\<^sub>m d n"
     and k: "k < length (tr_kraus n d)"
  have kdn: "k < d * n" using k by (simp add: tr_kraus_length)
  let ?a = "k div n" and ?b = "k mod n"
  have a: "?a < d" using kdn by (simp add: less_mult_imp_div_less)
  have b: "?b < n" using n by simp
  have nth: "\<And>k'. k' < d * n \<Longrightarrow> tr_kraus n d ! k' = complex_of_real (1 / sqrt (real d)) \<cdot>\<^sub>m E\<lbrakk>(k' div n),(k' mod n) ; d,n\<rbrakk>"
  proof -
    fix k' assume k': "k' < d * n"
    have "k' div n < d" using k' by (simp add: less_mult_imp_div_less)
    moreover have "k' mod n < n" using n by simp
    ultimately show "tr_kraus n d ! k' = complex_of_real (1 / sqrt (real d)) \<cdot>\<^sub>m E\<lbrakk>(k' div n),(k' mod n) ; d,n\<rbrakk>"
      using k' by (simp add: tr_kraus_def product_nth)
  qed
  have "0 = foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (tr_kraus n d ! k) + acc) [0..<length (tr_kraus n d)] (0\<^sub>m d n) $$ (?a, ?b)"
    unfolding z using a b by simp
  also have "\<dots> = (\<Sum>k'<d * n. c k' * tr_kraus n d ! k' $$ (?a, ?b))"
    using foldr_smult_index[OF tr_kraus_carrier a b] by (simp add: tr_kraus_length)
  also have "\<dots> = (\<Sum>k'<d * n. if k' = k then c k * complex_of_real (1 / sqrt (real d)) else 0)"
  proof (intro sum.cong refl)
    fix k' assume "k' \<in> {..<d * n}"
    hence k': "k' < d * n" by simp
    have "k' div n = k div n \<and> k' mod n = k mod n \<longleftrightarrow> k' = k" by (metis div_mult_mod_eq)
    thus "c k' * tr_kraus n d ! k' $$ (?a, ?b) = (if k' = k then c k * complex_of_real (1 / sqrt (real d)) else 0)"
      unfolding nth[OF k'] using a b by (auto simp: mat_unit_def)
  qed
  also have "\<dots> = c k * complex_of_real (1 / sqrt (real d))" using kdn by simp
  finally show "c k = 0" using d by simp
qed

theorem tr_map_not_extreme:
  assumes n: "0 < n" and d: "2 \<le> d"
  shows "\<not> extreme_CPTP n d (kraus_map_dim d (tr_kraus n d))"
proof
  assume ext: "extreme_CPTP n d (kraus_map_dim d (tr_kraus n d))"
  have d0: "0 < d" using d by simp
  have K: "kraus_operators n d (tr_kraus n d)" by (rule tr_kraus_operators[OF d0])
  have rep: "cptp_kraus_rep n d (kraus_map_dim d (tr_kraus n d)) (tr_kraus n d)"
    unfolding cptp_kraus_rep_def using K by simp
  have "length (tr_kraus n d) \<le> n"
    by (rule extreme_CPTP_kraus_length_le[OF n d0 kraus_is_cptp[OF K n d0] rep tr_kraus_lin_indep[OF d0 n] ext])
  hence "d * n \<le> 1 * n" by (simp add: tr_kraus_length)
  hence "d \<le> 1" using n by (simp only: mult_le_cancel2)
  thus False using d by simp
qed

subsubsection \<open>Example 4: the diagonal map\<close>

definition diag_kraus :: "nat \<Rightarrow> complex Matrix.mat list" where
  "diag_kraus n = map (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n]"

lemma diag_kraus_carrier: "\<forall>W \<in> set (diag_kraus n). W \<in> carrier_mat n n"
  by (auto simp: diag_kraus_def mat_unit_def)

text \<open>The diagonal map has the Kraus operators $E_{ii}$, and $\sum_iE_{ii}XE_{ii}=\diag(x_{11},\dots,x_{nn})$.
The $E_{ii}$ are independent, but for $n\ge2$ the products $E_{ii}^*E_{jj}=\delta_{ij}E_{ii}$ include
$0$, so they are dependent and the map is not extreme.\<close>

lemma diag_kraus_map:
  assumes M: "M \<in> carrier_mat n n"
  shows "kraus_map_dim n (diag_kraus n) M = Matrix.mat n n (\<lambda>(r,s). if r = s then M $$ (r,r) else 0)"
proof (rule eq_matI)
  have c: "\<forall>W \<in> set (diag_kraus n). W * M * (W\<^sup>\<dagger>) \<in> carrier_mat n n"
  proof
    fix W assume "W \<in> set (diag_kraus n)"
    hence Wc: "W \<in> carrier_mat n n" using diag_kraus_carrier by blast
    show "W * M * (W\<^sup>\<dagger>) \<in> carrier_mat n n" using Wc M dagger_carrier[OF Wc] by simp
  qed
  fix r s assume "r < dim_row (Matrix.mat n n (\<lambda>(r,s). if r = s then M $$ (r,r) else (0::complex)))"
                 "s < dim_col (Matrix.mat n n (\<lambda>(r,s). if r = s then M $$ (r,r) else (0::complex)))"
  hence r: "r < n" and s: "s < n" by simp_all
  have e: "\<And>i. i < n \<Longrightarrow> (E\<lbrakk>i,i ; n,n\<rbrakk> * M * (E\<lbrakk>i,i ; n,n\<rbrakk>\<^sup>\<dagger>)) $$ (r,s) = (if r = i \<and> s = i then M $$ (i,i) else 0)"
  proof -
    fix i assume i: "i < n"
    have c: "E\<lbrakk>i,i ; n,n\<rbrakk> * M \<in> carrier_mat n n" by (rule mult_carrier_mat[OF mat_unit_carrier M])
    show "(E\<lbrakk>i,i ; n,n\<rbrakk> * M * (E\<lbrakk>i,i ; n,n\<rbrakk>\<^sup>\<dagger>)) $$ (r,s) = (if r = i \<and> s = i then M $$ (i,i) else 0)"
      unfolding mat_unit_dagger unit_mult_right_entry[OF c r s i] using unit_mult_left_entry[OF M r i i] by auto
  qed
  have "kraus_map_dim n (diag_kraus n) M $$ (r,s) = (\<Sum>W\<leftarrow>diag_kraus n. (W * M * (W\<^sup>\<dagger>)) $$ (r,s))"
    unfolding kraus_map_dim_def by (rule foldr_add_mat_index_rect[OF c r s])
  also have "\<dots> = (\<Sum>i<n. if r = i \<and> s = i then M $$ (i,i) else 0)"
    by (simp add: diag_kraus_def comp_def e interv_sum_list_conv_sum_set_nat atLeast0LessThan)
  also have "\<dots> = (if r = s then M $$ (r,r) else 0)"
  proof (cases "r = s")
    case True thus ?thesis using r by (simp add: sum.delta)
  next
    case False
    have "\<forall>i \<in> {..<n}. (if r = i \<and> s = i then M $$ (i,i) else 0) = 0" using False by auto
    hence "(\<Sum>i<n. if r = i \<and> s = i then M $$ (i,i) else 0) = 0" by (rule sum.neutral)
    thus ?thesis using False by simp
  qed
  finally show "kraus_map_dim n (diag_kraus n) M $$ (r,s) = Matrix.mat n n (\<lambda>(r,s). if r = s then M $$ (r,r) else 0) $$ (r,s)"
    using r s by simp
next
  have c: "\<forall>W \<in> set (diag_kraus n). W * M * (W\<^sup>\<dagger>) \<in> carrier_mat n n"
  proof
    fix W assume "W \<in> set (diag_kraus n)"
    hence Wc: "W \<in> carrier_mat n n" using diag_kraus_carrier by blast
    show "W * M * (W\<^sup>\<dagger>) \<in> carrier_mat n n" using Wc M dagger_carrier[OF Wc] by simp
  qed
  show "dim_row (kraus_map_dim n (diag_kraus n) M) = dim_row (Matrix.mat n n (\<lambda>(r,s). if r = s then M $$ (r,r) else (0::complex)))"
       "dim_col (kraus_map_dim n (diag_kraus n) M) = dim_col (Matrix.mat n n (\<lambda>(r,s). if r = s then M $$ (r,r) else (0::complex)))"
    using foldr_add_mat_carrier_rect[OF c] unfolding kraus_map_dim_def by auto
qed

lemma diag_kraus_operators: "kraus_operators n n (diag_kraus n)"
  unfolding kraus_operators_def
proof (intro conjI)
  show "\<forall>W \<in> set (diag_kraus n). W \<in> carrier_mat n n" by (rule diag_kraus_carrier)
  have c: "\<forall>W \<in> set (diag_kraus n). (W\<^sup>\<dagger>) * W \<in> carrier_mat n n"
  proof
    fix W assume "W \<in> set (diag_kraus n)"
    hence Wc: "W \<in> carrier_mat n n" using diag_kraus_carrier by blast
    show "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n" using Wc dagger_carrier[OF Wc] by simp
  qed
  show "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) (diag_kraus n) (0\<^sub>m n n) = 1\<^sub>m n"
  proof (rule eq_matI)
    fix r s assume "r < dim_row (1\<^sub>m n :: complex Matrix.mat)" "s < dim_col (1\<^sub>m n :: complex Matrix.mat)"
    hence r: "r < n" and s: "s < n" by simp_all
    have e: "\<And>i. i < n \<Longrightarrow> ((E\<lbrakk>i,i ; n,n\<rbrakk>\<^sup>\<dagger>) * E\<lbrakk>i,i ; n,n\<rbrakk>) $$ (r,s) = (if r = i \<and> s = i then 1 else 0)"
    proof -
      fix i assume i: "i < n"
      show "((E\<lbrakk>i,i ; n,n\<rbrakk>\<^sup>\<dagger>) * E\<lbrakk>i,i ; n,n\<rbrakk>) $$ (r,s) = (if r = i \<and> s = i then 1 else 0)"
        unfolding mat_unit_dagger unit_mult_left_entry[OF mat_unit_carrier r s i] using r s by auto
    qed
    have "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) (diag_kraus n) (0\<^sub>m n n) $$ (r,s) = (\<Sum>W\<leftarrow>diag_kraus n. ((W\<^sup>\<dagger>) * W) $$ (r,s))"
      by (rule foldr_add_mat_index_rect[OF c r s])
    also have "\<dots> = (\<Sum>i<n. if r = i \<and> s = i then 1 else 0)"
      by (simp add: diag_kraus_def comp_def e interv_sum_list_conv_sum_set_nat atLeast0LessThan)
    also have "\<dots> = (if r = s then 1 else 0)" using r by (auto simp: sum.delta)
    finally show "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) (diag_kraus n) (0\<^sub>m n n) $$ (r,s) = 1\<^sub>m n $$ (r,s)"
      using r s by simp
  qed (use foldr_add_mat_carrier_rect[OF c] in auto)
qed

lemma diag_kraus_lin_indep: "lin_indep_complex_mat n n (diag_kraus n)"
  unfolding lin_indep_complex_mat_def
proof (intro conjI allI impI)
  show "\<forall>W \<in> set (diag_kraus n). W \<in> carrier_mat n n" by (rule diag_kraus_carrier)
  fix c :: "nat \<Rightarrow> complex" and k
  assume z: "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (diag_kraus n ! k) + acc) [0..<length (diag_kraus n)] (0\<^sub>m n n) = 0\<^sub>m n n"
     and k: "k < length (diag_kraus n)"
  hence kn: "k < n" by (simp add: diag_kraus_def)
  have "0 = foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (diag_kraus n ! k) + acc) [0..<length (diag_kraus n)] (0\<^sub>m n n) $$ (k,k)"
    unfolding z using kn by simp
  also have "\<dots> = (\<Sum>k'<n. c k' * diag_kraus n ! k' $$ (k,k))"
    using foldr_smult_index[OF diag_kraus_carrier kn kn] by (simp add: diag_kraus_def)
  also have "\<dots> = (\<Sum>k'<n. if k' = k then c k else 0)"
    by (intro sum.cong refl) (use kn in \<open>auto simp: diag_kraus_def\<close>)
  also have "\<dots> = c k" using kn by simp
  finally show "c k = 0" by simp
qed

theorem diag_not_extreme:
  assumes n: "2 \<le> n"
  shows "\<not> extreme_CPTP n n (kraus_map_dim n (diag_kraus n))"
proof -
  have n0: "0 < n" using n by simp
  have K: "kraus_operators n n (diag_kraus n)" by (rule diag_kraus_operators)
  have rep: "cptp_kraus_rep n n (kraus_map_dim n (diag_kraus n)) (diag_kraus n)"
    unfolding cptp_kraus_rep_def using K by simp
  have l: "length (diag_kraus n) = n" by (simp add: diag_kraus_def)
  have k1: "kraus_products (diag_kraus n) ! 1 = (diag_kraus n ! 1)\<^sup>\<dagger> * diag_kraus n ! 0"
  proof -
    have "[0..<n] = 0 # 1 # [2..<n]" using n by (simp add: upt_conv_Cons numeral_2_eq_2)
    thus ?thesis unfolding kraus_products_def l by simp
  qed
  have d: "diag_kraus n ! 1 = E\<lbrakk>1,1 ; n,n\<rbrakk>" "diag_kraus n ! 0 = E\<lbrakk>0,0 ; n,n\<rbrakk>"
    using n by (simp_all add: diag_kraus_def)
  have "(diag_kraus n ! 1)\<^sup>\<dagger> * diag_kraus n ! 0 = 0\<^sub>m n n"
  proof (rule eq_matI)
    fix r s assume "r < dim_row (0\<^sub>m n n :: complex Matrix.mat)" "s < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
    hence r: "r < n" and s: "s < n" by simp_all
    show "((diag_kraus n ! 1)\<^sup>\<dagger> * diag_kraus n ! 0) $$ (r,s) = 0\<^sub>m n n $$ (r,s)"
      unfolding d mat_unit_dagger unit_mult_left_entry[OF mat_unit_carrier r s] using r s n by simp
  qed (simp_all add: d d[unfolded One_nat_def] mat_unit_def)
  hence z: "kraus_products (diag_kraus n) ! 1 = 0\<^sub>m n n" using k1 by simp
  have "1 < length (kraus_products (diag_kraus n))" using n l length_kraus_products[of "diag_kraus n"]
    using mult_le_mono[OF n n] by simp
  hence "\<not> lin_indep_complex_mat n n (kraus_products (diag_kraus n))" by (rule not_indep_of_zero[OF _ z])
  thus ?thesis using choi_theorem_3_cptp_iff[OF n0 n0 kraus_is_cptp[OF K n0 n0] rep diag_kraus_lin_indep] by simp
qed

end
