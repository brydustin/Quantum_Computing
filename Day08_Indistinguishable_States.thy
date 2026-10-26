theory Day08_Indistinguishable_States
  imports Quantum_Computing_by_VP.Day07_Postulates
begin

section \<open>Day 8: non-orthogonal states cannot be distinguished\<close>

lemma meas_sum_norm:
  assumes ms: "measurement_system n Ms" and v: "dim_vec v = n"
  shows "(\<Sum>l<length Ms. \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2) = \<parallel>v\<parallel>\<^sup>2"
proof (cases "\<parallel>v\<parallel> = 0")
  case True
  hence v0: "v = 0\<^sub>v n" using v cpx_vec_length_zero_iff by fastforce
  have Mc: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have z: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l *\<^sub>v v = 0\<^sub>v n"
  proof -
    fix l assume "l < length Ms"
    hence M: "Ms ! l \<in> carrier_mat n n" by (rule Mc)
    show "Ms ! l *\<^sub>v v = 0\<^sub>v n" by (rule eq_vecI) (use M in \<open>auto simp: v0 scalar_prod_def\<close>)
  qed
  show ?thesis using True by (simp add: z cpx_vec_length_def)
next
  case False
  let ?c = "complex_of_real (1 / \<parallel>v\<parallel>)"
  have st: "quantum_state n (?c \<cdot>\<^sub>v v)"
  proof -
    have "\<parallel>v\<parallel> \<ge> 0" unfolding cpx_vec_length_def by (simp add: sum_nonneg)
    thus ?thesis unfolding quantum_state_def using v False by (simp add: cpx_vec_length_smult norm_divide)
  qed
  have Mc: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
  have tm: "\<And>l. l < length Ms \<Longrightarrow> meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v) = \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2 / \<parallel>v\<parallel>\<^sup>2"
  proof -
    fix l assume l: "l < length Ms"
    have vn: "\<parallel>v\<parallel> \<ge> 0" unfolding cpx_vec_length_def by (simp add: sum_nonneg)
    show "meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v) = \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2 / \<parallel>v\<parallel>\<^sup>2"
      unfolding meas_prob_def mult_mat_vec[OF Mc[OF l] vc]
      by (simp add: cpx_vec_length_smult norm_divide abs_of_nonneg[OF vn] power_mult_distrib power_divide)
  qed
  have "1 = (\<Sum>M \<leftarrow> Ms. meas_prob M (?c \<cdot>\<^sub>v v))" by (rule measurement_probs_sum_one[OF ms st, symmetric])
  also have "\<dots> = (\<Sum>l<length Ms. meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = (\<Sum>l<length Ms. \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2) / \<parallel>v\<parallel>\<^sup>2"
    unfolding sum_divide_distrib by (rule sum.cong[OF refl], rule tm, simp)
  finally show ?thesis using False by (simp add: field_simps)
qed

lemma inner_minus_smult:
  assumes d1: "dim_vec u = n" and d2: "dim_vec w = n"
  shows "\<langle>w - a \<cdot>\<^sub>v u | w - a \<cdot>\<^sub>v u\<rangle> = \<langle>w|w\<rangle> - a * \<langle>w|u\<rangle> - cnj a * \<langle>u|w\<rangle> + a * cnj a * \<langle>u|u\<rangle>"
  unfolding inner_prod_def using d1 d2
  by (simp add: sum.distrib sum_subtractf sum_distrib_left algebra_simps)

lemma norm_sq_minus_component:
  assumes d1: "dim_vec u = n" and d2: "dim_vec w = n" and u: "\<parallel>u\<parallel> = 1"
  shows "\<parallel>w - \<langle>u|w\<rangle> \<cdot>\<^sub>v u\<parallel>\<^sup>2 = \<parallel>w\<parallel>\<^sup>2 - (cmod \<langle>u|w\<rangle>)\<^sup>2"
proof -
  let ?a = "\<langle>u|w\<rangle>"
  have uu: "\<langle>u|u\<rangle> = 1" using u cpx_vec_length_inner_prod[of u] by simp
  have wu: "\<langle>w|u\<rangle> = cnj ?a" by (rule inner_prod_cnj) (use d1 d2 in simp)
  have e: "\<langle>w - ?a \<cdot>\<^sub>v u | w - ?a \<cdot>\<^sub>v u\<rangle> = \<langle>w|w\<rangle> - ?a * \<langle>w|u\<rangle> - cnj ?a * ?a + ?a * cnj ?a * \<langle>u|u\<rangle>"
    by (rule inner_minus_smult[OF d1 d2])
  have "complex_of_real (\<parallel>w - ?a \<cdot>\<^sub>v u\<parallel>\<^sup>2) = complex_of_real (\<parallel>w\<parallel>\<^sup>2) - ?a * cnj ?a"
    unfolding cpx_vec_length_inner_prod e wu uu by simp
  also have "?a * cnj ?a = complex_of_real ((cmod ?a)\<^sup>2)" using complex_norm_square[of ?a] by simp
  finally show ?thesis by (metis of_real_diff of_real_eq_iff)
qed

text \<open>D8-2: if outcome $i$ certainly occurs on $\psi_1$, it occurs on $\psi_2$ with probability
at least $|\langle\psi_1|\psi_2\rangle|^2$.\<close>

theorem nonorthogonal_outcome_prob:
  assumes ms: "measurement_system n Ms" and q1: "quantum_state n \<psi>1" and q2: "quantum_state n \<psi>2"
      and i: "i < length Ms" and p1: "meas_prob (Ms ! i) \<psi>1 = 1"
  shows "(cmod \<langle>\<psi>1|\<psi>2\<rangle>)\<^sup>2 \<le> meas_prob (Ms ! i) \<psi>2"
proof -
  let ?N = "length Ms" and ?a = "\<langle>\<psi>1|\<psi>2\<rangle>"
  let ?g = "\<psi>2 - ?a \<cdot>\<^sub>v \<psi>1"
  have d1: "dim_vec \<psi>1 = n" and n1: "\<parallel>\<psi>1\<parallel> = 1" and d2: "dim_vec \<psi>2 = n" and n2: "\<parallel>\<psi>2\<parallel> = 1"
    using q1 q2 unfolding quantum_state_def by auto
  have Mc: "\<And>l. l < ?N \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have rem: "\<And>f :: nat \<Rightarrow> real. (\<Sum>l<?N. f l) = f i + (\<Sum>l\<in>{..<?N} - {i}. f l)"
    by (rule sum.remove) (use i in simp_all)
  have S1: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2) = 1" using meas_sum_norm[OF ms d1] n1 by simp
  have rest0: "(\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2) = 0"
    using S1 rem[of "\<lambda>l. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2"] p1 unfolding meas_prob_def by simp
  have z: "\<And>l. l < ?N \<Longrightarrow> l \<noteq> i \<Longrightarrow> Ms ! l *\<^sub>v \<psi>1 = 0\<^sub>v n"
  proof -
    fix l assume l: "l < ?N" "l \<noteq> i"
    have "\<forall>x\<in>{..<?N} - {i}. \<parallel>Ms ! x *\<^sub>v \<psi>1\<parallel>\<^sup>2 = 0"
      using rest0 by (subst (asm) sum_nonneg_eq_0_iff) auto
    hence "\<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2 = 0" using l by auto
    hence "\<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel> = 0" by simp
    thus "Ms ! l *\<^sub>v \<psi>1 = 0\<^sub>v n" using cpx_vec_length_zero_iff Mc[OF l(1)] by fastforce
  qed
  have gd: "dim_vec ?g = n" using d1 d2 by simp
  have Mg: "\<And>l. l < ?N \<Longrightarrow> l \<noteq> i \<Longrightarrow> Ms ! l *\<^sub>v \<psi>2 = Ms ! l *\<^sub>v ?g"
  proof -
    fix l assume l: "l < ?N" "l \<noteq> i"
    have c1: "\<psi>1 \<in> carrier_vec n" by (rule carrier_vecI[OF d1])
    have c2: "\<psi>2 \<in> carrier_vec n" by (rule carrier_vecI[OF d2])
    have "Ms ! l *\<^sub>v ?g = Ms ! l *\<^sub>v \<psi>2 - ?a \<cdot>\<^sub>v (Ms ! l *\<^sub>v \<psi>1)"
      using mult_minus_distrib_mat_vec[OF Mc[OF l(1)] c2 smult_carrier_vec[THEN iffD2, OF c1]] mult_mat_vec[OF Mc[OF l(1)] c1] by simp
    thus "Ms ! l *\<^sub>v \<psi>2 = Ms ! l *\<^sub>v ?g" using z[OF l] Mc[OF l(1)] by auto
  qed
  have S2: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2) = 1" using meas_sum_norm[OF ms d2] n2 by simp
  have Sg: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2) = 1 - (cmod ?a)\<^sup>2"
    using meas_sum_norm[OF ms gd] norm_sq_minus_component[OF d1 d2 n1] n2 by simp
  have "(\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2) = (\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2)"
    by (rule sum.cong) (simp_all add: Mg)
  also have "\<dots> \<le> (\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2)" by (rule sum_mono2) auto
  finally show ?thesis using S2 Sg rem[of "\<lambda>l. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2"] unfolding meas_prob_def by linarith
qed

corollary nonorthogonal_not_distinguishable:
  assumes ms: "measurement_system n Ms" and q1: "quantum_state n \<psi>1" and q2: "quantum_state n \<psi>2"
      and no: "\<langle>\<psi>1|\<psi>2\<rangle> \<noteq> 0" and i: "i < length Ms" and p1: "meas_prob (Ms ! i) \<psi>1 = 1"
  shows "meas_prob (Ms ! i) \<psi>2 > 0"
  using nonorthogonal_outcome_prob[OF ms q1 q2 i p1] no
  by (smt (verit) zero_less_power norm_eq_zero zero_less_norm_iff)

end
