theory Prep_Rounded
  imports Simulation_Oracles
begin

section \<open>State preparation with rounded angles\<close>

text \<open>The cascade of \<open>state_prep\<close> rotates qubit $j$ by an angle that depends on the first $j$
qubits.  With every angle rounded to $b$ bits, each level moves by at most $2\pi/2^b$, so the
prepared state is $k\cdot 2\pi/2^b$-close to the target.\<close>

subsection \<open>Closeness tools\<close>

lemma Rot_dmat: "Rot s = Qm * dmat 2 (\<lambda>a. if a = 0 then - s else s) * (Qm\<^sup>\<dagger>)"
proof -
  have h: "complex_of_real (1 / sqrt 2) * complex_of_real (1 / sqrt 2) = 1 / 2" by (simp flip: of_real_mult)
  have h2: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2" by (simp flip: of_real_mult)
  show ?thesis
    by (rule eq_matI) (auto simp: Qm_eq Rot_def dmat_def mat_diag_def dagger_def scalar_prod_def atLeast0LessThan
        sumof2 less_Suc_eq numeral_2_eq_2 h h2 cis.ctr complex_eq_iff algebra_simps)
qed

lemma rot_close:
  assumes e: "cmod (cis \<theta> - cis \<theta>') \<le> e"
  shows "Rot \<theta> \<approx>\<^bsub>e\<^esub> Rot \<theta>'"
proof -
  have Qc: "Qm \<in> carrier_mat 2 2" and Qu: "Quantum.unitary Qm" by (simp_all add: Qm_unitary)
  have Qd: "Qm\<^sup>\<dagger> \<in> carrier_mat 2 2" by (rule dagger_carrier[OF Qc])
  have QQ: "Qm * (Qm\<^sup>\<dagger>) = 1\<^sub>m 2" using Qu carrier_matD[OF Phase_S_carrier] by (simp add: Quantum.unitary_def)
  note r = Rot_dmat
  have d: "dmat 2 (\<lambda>a. if a = 0 then - \<theta> else \<theta>) \<approx>\<^bsub>e\<^esub> dmat 2 (\<lambda>a. if a = 0 then - \<theta>' else \<theta>')"
    by (rule dmat_close) (use e in \<open>auto simp: cis_neg_dist intro: order_trans[OF norm_ge_zero]\<close>)
  have "Qm * dmat 2 (\<lambda>a. if a = 0 then - \<theta> else \<theta>) \<approx>\<^bsub>e\<^esub> Qm * dmat 2 (\<lambda>a. if a = 0 then - \<theta>' else \<theta>')"
    by (rule op_close_mult_left[OF Qc Qu dmat_carrier dmat_carrier d])
  hence "Qm * dmat 2 (\<lambda>a. if a = 0 then - \<theta> else \<theta>) * (Qm\<^sup>\<dagger>) \<approx>\<^bsub>e\<^esub> Qm * dmat 2 (\<lambda>a. if a = 0 then - \<theta>' else \<theta>') * (Qm\<^sup>\<dagger>)"
    by (rule op_close_mult_right[OF Qd unitary_dagger[OF Qu] mult_carrier_mat[OF Qc dmat_carrier] mult_carrier_mat[OF Qc dmat_carrier]])
  thus ?thesis unfolding r[symmetric] .
qed

lemma op_close_tensor_pow:
  assumes M1: "M1 \<in> carrier_mat n n" and M2: "M2 \<in> carrier_mat n n" and c: "M1 \<approx>\<^bsub>\<eta>\<^esub> M2" and e: "0 \<le> \<eta>"
  shows "M1 \<Otimes> 1\<^sub>m (2 ^ q) \<approx>\<^bsub>\<eta>\<^esub> M2 \<Otimes> 1\<^sub>m (2 ^ q)"
proof (induction q)
  case 0
  show ?case using c M1 M2 by (simp add: right_tensor_id[unfolded One_nat_def])
next
  case (Suc q)
  have a: "M \<Otimes> 1\<^sub>m (2 ^ Suc q) = (M \<Otimes> 1\<^sub>m (2 ^ q)) \<Otimes> 1\<^sub>m 2" for M :: "complex Matrix.mat"
    using tensor_mat_is_assoc[of M "1\<^sub>m (2 ^ q)" "1\<^sub>m 2"] tensor_mat_id[of "2 ^ q" 2] by (simp add: ac_simps)
  show ?case unfolding a by (rule op_close_tensor_one2[where n = "n * 2 ^ q", OF _ _ Suc e]) (use M1 M2 in simp_all)
qed

text \<open>The errors of a product of unitaries add up.\<close>

lemma circuit_close:
  assumes "list_all2 (\<lambda>U V. U \<in> carrier_mat N N \<and> V \<in> carrier_mat N N \<and> Quantum.unitary U \<and> Quantum.unitary V
      \<and> U \<approx>\<^bsub>e\<^esub> V) Us Vs" and e: "0 \<le> e"
  shows "circuit_mat N Us \<approx>\<^bsub>real (length Us) * e\<^esub> circuit_mat N Vs \<and> circuit_mat N Us \<in> carrier_mat N N
    \<and> circuit_mat N Vs \<in> carrier_mat N N \<and> Quantum.unitary (circuit_mat N Us) \<and> Quantum.unitary (circuit_mat N Vs)"
  using assms(1)
proof (induction rule: list_all2_induct)
  case Nil
  have "(1\<^sub>m N :: complex Matrix.mat) \<approx>\<^bsub>0\<^esub> 1\<^sub>m N" by (rule op_close_refl[where n = N]) simp_all
  thus ?case by (simp add: id_is_unitary)
next
  case (Cons U Us V Vs)
  let ?A = "circuit_mat N Us" and ?B = "circuit_mat N Vs"
  have Ac: "?A \<in> carrier_mat N N" and Bc: "?B \<in> carrier_mat N N" and Au: "Quantum.unitary ?A"
    and Bu: "Quantum.unitary ?B" and cl: "?A \<approx>\<^bsub>real (length Us) * e\<^esub> ?B" using Cons.IH by blast+
  have Uc: "U \<in> carrier_mat N N" and Vc: "V \<in> carrier_mat N N" and Uu: "Quantum.unitary U" and Vu: "Quantum.unitary V"
    and cU: "U \<approx>\<^bsub>e\<^esub> V" using Cons.hyps by blast+
  have c1: "?A * U \<approx>\<^bsub>real (length Us) * e\<^esub> ?B * U" by (rule op_close_mult_right[OF Uc Uu Ac Bc cl])
  have c2: "?B * U \<approx>\<^bsub>e\<^esub> ?B * V" by (rule op_close_mult_left[OF Bc Bu Uc Vc cU])
  have "?A * U \<approx>\<^bsub>real (length Us) * e + e\<^esub> ?B * V"
    by (rule op_close_trans[OF c1 c2 mult_carrier_mat[OF Ac Uc] mult_carrier_mat[OF Bc Uc] mult_carrier_mat[OF Bc Vc]])
  moreover have "real (length Us) * e + e = real (length (U # Us)) * e" by (simp add: algebra_simps)
  ultimately show ?case
    using mult_carrier_mat[OF Ac Uc] mult_carrier_mat[OF Bc Vc] unitary_mult[OF Au Uu Ac Uc] unitary_mult[OF Bu Vu Bc Vc] by simp
qed

subsection \<open>The rounded cascade\<close>

definition prep_code :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prep_code b k a j c = (if pnorm k a j c = 0 then 0 else near_bits b (pangle k a j c))"

text \<open>On a prefix of weight zero the angle is $0$ and so is its code.\<close>

lemma prep_code_lt: "prep_code b k a j c < 2 ^ b" by (simp add: prep_code_def near_bits)

lemma prep_code_close: "cmod (cis (pangle k a j c) - cis (ang b (prep_code b k a j c))) \<le> 2 * pi / 2 ^ b"
proof (cases "pnorm k a j c = 0")
  case True
  thus ?thesis by (simp add: prep_code_def pangle_def ang_def pi_ge_zero)
next
  case False
  thus ?thesis by (simp add: prep_code_def near_bits)
qed

lemmas prep_code = prep_code_lt prep_code_close

definition lev_rnd :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "lev_rnd b k a j = ctrl_blocks (2 ^ j) (2 * 2 ^ (k - Suc j)) (\<lambda>c. Rot (ang b (prep_code b k a j c)) \<Otimes> 1\<^sub>m (2 ^ (k - Suc j)))"

lemma lev_rnd_facts:
  assumes j: "j < k"
  shows "lev_rnd b k a j \<in> carrier_mat (2 ^ k) (2 ^ k)" "Quantum.unitary (lev_rnd b k a j)"
    "lev k a j \<in> carrier_mat (2 ^ k) (2 ^ k)" "Quantum.unitary (lev k a j)"
    "lev k a j \<approx>\<^bsub>2 * pi / 2 ^ b\<^esub> lev_rnd b k a j"
proof -
  let ?h = "2 ^ (k - Suc j) :: nat"
  have K: "2 ^ j * (2 * ?h) = (2::nat) ^ k" by (rule lev_dim[OF j])
  have bc: "Rot s \<Otimes> 1\<^sub>m ?h \<in> carrier_mat (2 * ?h) (2 * ?h)" for s by simp
  have bu: "Quantum.unitary (Rot s \<Otimes> 1\<^sub>m ?h)" for s by (intro tensor_mat_unitary Rot_unitary id_is_unitary)
  show "lev_rnd b k a j \<in> carrier_mat (2 ^ k) (2 ^ k)" unfolding lev_rnd_def K[symmetric] by (rule ctrl_blocks_carrier)
  show "lev k a j \<in> carrier_mat (2 ^ k) (2 ^ k)" by (rule lev_carrier[OF j])
  show "Quantum.unitary (lev_rnd b k a j)" unfolding lev_rnd_def by (rule ctrl_blocks_unitary[OF bc bu])
  show "Quantum.unitary (lev k a j)" unfolding lev_def by (rule ctrl_blocks_unitary[OF bc bu])
  have "Rot (pangle k a j c) \<Otimes> 1\<^sub>m ?h \<approx>\<^bsub>2 * pi / 2 ^ b\<^esub> Rot (ang b (prep_code b k a j c)) \<Otimes> 1\<^sub>m ?h" for c
    by (rule op_close_tensor_pow[OF Rot_carrier Rot_carrier rot_close]) (simp_all add: prep_code)
  thus "lev k a j \<approx>\<^bsub>2 * pi / 2 ^ b\<^esub> lev_rnd b k a j"
    unfolding lev_def lev_rnd_def by (intro ctrl_blocks_op_close bc)
qed

theorem rounded_prep:
  assumes n: "(\<Sum>x<2 ^ k. (a x)\<^sup>2) = 1" and a: "\<And>x. x < 2 ^ k \<Longrightarrow> 0 \<le> a x"
  shows "\<parallel>circuit_mat (2 ^ k) (map (lev_rnd b k a) [0..<k]) *\<^sub>v unit_vec (2 ^ k) 0 - Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))\<parallel>
    \<le> real k * (2 * pi / 2 ^ b)"
proof -
  let ?U = "circuit_mat (2 ^ k) (map (lev k a) [0..<k])" and ?V = "circuit_mat (2 ^ k) (map (lev_rnd b k a) [0..<k])"
  have "list_all2 (\<lambda>U V. U \<in> carrier_mat (2 ^ k) (2 ^ k) \<and> V \<in> carrier_mat (2 ^ k) (2 ^ k) \<and> Quantum.unitary U
      \<and> Quantum.unitary V \<and> U \<approx>\<^bsub>2 * pi / 2 ^ b\<^esub> V) (map (lev k a) [0..<k]) (map (lev_rnd b k a) [0..<k])"
    by (auto simp: list_all2_map1 list_all2_map2 list_all2_same lev_rnd_facts)
  note C = circuit_close[OF this, simplified]
  have Uc: "?U \<in> carrier_mat (2 ^ k) (2 ^ k)" and cl: "?U \<approx>\<^bsub>real k * (2 * pi / 2 ^ b)\<^esub> ?V" using C by auto
  have "\<parallel>?U *\<^sub>v unit_vec (2 ^ k) 0 - ?V *\<^sub>v unit_vec (2 ^ k) 0\<parallel> \<le> real k * (2 * pi / 2 ^ b) * \<parallel>unit_vec (2 ^ k) 0\<parallel>"
    by (rule op_closeD[OF cl Uc]) simp
  moreover have "\<parallel>unit_vec (2 ^ k) (0::nat)\<parallel> = 1"
  proof -
    have "(\<Sum>i::nat<2 ^ k. (cmod (if i = 0 then 1 else 0 :: complex))\<^sup>2) = (\<Sum>i::nat<2 ^ k. if i = 0 then 1 else (0::real))"
      by (rule sum.cong) auto
    thus ?thesis by (simp add: cpx_vec_length_def unit_vec_def)
  qed
  ultimately have bnd: "\<parallel>?U *\<^sub>v unit_vec (2 ^ k) 0 - ?V *\<^sub>v unit_vec (2 ^ k) 0\<parallel> \<le> real k * (2 * pi / 2 ^ b)" by simp
  have u: "?U *\<^sub>v unit_vec (2 ^ k) 0 = Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))" by (rule cascade_prepares[OF n a])
  have Vc: "?V \<in> carrier_mat (2 ^ k) (2 ^ k)" using C by blast
  have b1: "\<parallel>Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x)) - ?V *\<^sub>v unit_vec (2 ^ k) 0\<parallel> \<le> real k * (2 * pi / 2 ^ b)"
    using bnd unfolding u .
  have "\<parallel>?V *\<^sub>v unit_vec (2 ^ k) 0 - Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))\<parallel>
      = \<parallel>Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x)) - ?V *\<^sub>v unit_vec (2 ^ k) 0\<parallel>"
    by (rule vnorm_minus_commute) (use Vc in simp)
  thus ?thesis using b1 by simp
qed

end
