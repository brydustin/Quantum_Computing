theory HHL_Laplacian_Sparse
  imports HHL_Laplacian
begin

section \<open>The whole pipeline with the sparse preparation of $\ket b$\<close>

lemma circuit_qunitary:
  "(\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K \<and> Quantum.unitary U)
    \<Longrightarrow> circuit_mat K Us \<in> carrier_mat K K \<and> Quantum.unitary (circuit_mat K Us)"
proof (induction Us)
  case Nil
  show ?case by (simp add: id_is_unitary)
next
  case (Cons U Us)
  have U: "U \<in> carrier_mat K K" "Quantum.unitary U" and IH: "circuit_mat K Us \<in> carrier_mat K K" "Quantum.unitary (circuit_mat K Us)"
    using Cons by auto
  show ?case using unitary_mult[OF IH(2) U(2) IH(1) U(1)] IH(1) U(1) by simp
qed

lemma sprep_facts:
  fixes bb :: nat
  assumes sp: "supp k av xs"
  defines "Ub \<equiv> circuit_mat (2 ^ k) (map (lev_rnd bb k av) [0..<k])"
  shows "stands_for (2 ^ (bb + k)) (2 ^ k) (circuit_mat (2 ^ (k + (bb + k))) (sprep_gates bb k av xs)) Ub"
    "Ub \<in> carrier_mat (2 ^ k) (2 ^ k)" "Quantum.unitary Ub"
proof -
  let ?KL = "k + (bb + k)" and ?A = "2 ^ k * 2 ^ bb :: nat"
  have lc: "U \<in> carrier_mat (2 ^ ?KL) (2 ^ ?KL)" if Us: "Us \<in> set (map (lev_sgates bb k av xs) [0..<k])" "U \<in> set Us" for Us U
  proof -
    obtain j where j: "j < k" and U: "U \<in> set (lev_sgates bb k av xs j)" using Us by auto
    show ?thesis using lev_sgates_props(2)[OF sp j] U elementary_carrier by blast
  qed
  have cU: "circuit_mat (2 ^ ?KL) (sprep_gates bb k av xs)
      = circuit_mat (2 ^ ?KL) (map (\<lambda>j. circuit_mat (2 ^ ?KL) (lev_sgates bb k av xs j)) [0..<k])"
  proof -
    have "circuit_mat (2 ^ ?KL) (sprep_gates bb k av xs)
        = circuit_mat (2 ^ ?KL) (map (circuit_mat (2 ^ ?KL)) (map (lev_sgates bb k av xs) [0..<k]))"
      unfolding sprep_gates_def by (rule circuit_mat_concat) (rule lc)
    thus ?thesis by (simp only: map_map comp_def)
  qed
  have KA: "?A * 2 ^ k = (2::nat) ^ ?KL" by (simp add: power_add ac_simps)
  have "list_all2 (stands_for ?A (2 ^ k)) (map (\<lambda>j. circuit_mat (2 ^ ?KL) (lev_sgates bb k av xs j)) [0..<k]) (map (lev_rnd bb k av) [0..<k])"
    by (auto simp: list_all2_map1 list_all2_map2 list_all2_same lev_sgates_props(1)[OF sp])
  hence "stands_for ?A (2 ^ k) (circuit_mat (?A * 2 ^ k) (map (\<lambda>j. circuit_mat (2 ^ ?KL) (lev_sgates bb k av xs j)) [0..<k])) Ub"
    unfolding Ub_def by (rule stands_for_circuit)
  moreover have "?A = 2 ^ (bb + k)" by (simp add: power_add ac_simps)
  ultimately show "stands_for (2 ^ (bb + k)) (2 ^ k) (circuit_mat (2 ^ ?KL) (sprep_gates bb k av xs)) Ub"
    unfolding cU KA by simp
  have "Ub \<in> carrier_mat (2 ^ k) (2 ^ k) \<and> Quantum.unitary Ub"
    unfolding Ub_def by (rule circuit_qunitary) (auto simp: lev_rnd_facts)
  thus "Ub \<in> carrier_mat (2 ^ k) (2 ^ k)" "Quantum.unitary Ub" by simp_all
qed

text \<open>The $s$-sparse right-hand side with nonnegative amplitudes \<open>av\<close> (supported on \<open>xs\<close>) is
prepared to within $m\cdot 2\pi/2^{b}$ by \<open>sparse_prep_gates\<close>, with $b$ bits per angle; HHL then
runs on the prepared state $b'$.\<close>

corollary hhl_lap_sparse:
  fixes av :: "nat \<Rightarrow> real" and xs :: "nat list" and m k a bb r :: nat and \<mu> t0 C \<theta> lmin \<epsilon> :: real
  assumes m: "2 \<le> m" and k: "1 \<le> k" and am: "bb + 2 * m \<le> a" and r: "0 < r" and mu: "0 \<le> \<mu>"
    and av: "(\<Sum>x<2 ^ m. (av x)\<^sup>2) = 1" "\<And>x. x < 2 ^ m \<Longrightarrow> 0 \<le> av x" and sp: "supp m av xs"
    and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin" "lmin \<le> \<mu>"
    and tb: "t0 * (4 + \<mu>) \<le> pi / 2" and e: "0 < \<epsilon>"
    and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real (2 ^ k)"
    and small: "\<epsilon> + 2 * real (2 ^ k - 1) * (18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r) \<le> C * t0 / pi"
  defines "K \<equiv> Suc (m + k) + a"
    and "Bs \<equiv> sprep_gates bb m av xs"
    and "Ub \<equiv> circuit_mat (2 ^ m) (map (lev_rnd bb m av) [0..<m])"
    and "b' \<equiv> circuit_mat (2 ^ m) (map (lev_rnd bb m av) [0..<m]) *\<^sub>v unit_vec (2 ^ m) 0"
    and "out \<equiv> sem (2 ^ k) (2 ^ m * 2) (evolution_product (2 ^ m) (t0 / real r) (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m))) ^\<^sub>m r \<Otimes> 1\<^sub>m 2)
                (hhl_full_prog (slap (2 ^ m) \<mu>) t0 (2 ^ k) C (win_prep_mat k (2 ^ m) (circuit_mat (2 ^ m) (map (lev_rnd bb m av) [0..<m]))))
                *\<^sub>v unit_vec (2 ^ k * (2 ^ m * 2)) 0"
    and "x \<equiv> herm_inv (slap (2 ^ m) \<mu>) *\<^sub>v (circuit_mat (2 ^ m) (map (lev_rnd bb m av) [0..<m]) *\<^sub>v unit_vec (2 ^ m) 0)"
  shows "\<parallel>b' - Matrix.vec (2 ^ m) (\<lambda>i. complex_of_real (av i))\<parallel> \<le> real m * (2 * pi / 2 ^ bb)"
    "\<forall>U \<in> set (hhl_lap_gates m k a (bb + m) \<mu> t0 r C Bs). elementary (2 ^ K) U"
    "circuit_mat (2 ^ K) (hhl_lap_gates m k a (bb + m) \<mu> t0 r C Bs) *\<^sub>v unit_vec (2 ^ K) 0 = anc (2 ^ a) (2 ^ Suc (m + k)) *\<^sub>v out"
    "C * t0 / pi \<le> \<parallel>post1 out\<parallel>"
    "\<parallel>complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out
       - tensor_vec (win_state (2 ^ k)) (tensor_vec (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x) (unit_vec 2 1))\<parallel>
      \<le> 2 * (\<epsilon> + 2 * real (2 ^ k - 1) * (18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r)) / (C * \<parallel>x\<parallel>)"
    "length (hhl_lap_gates m k a (bb + m) \<mu> t0 r C Bs) \<le> k * (1 + 2 ^ k * (2 * k + 1))
      + m * (2 * (length xs * (4 * m + 2 + bb) * (6 * (m + (bb + m)) + 7)) + (bb * (2 * (bb + m) + 1) + 2)) * (4 * K + 1)
      + 2 * ((2 ^ k - 1) * (r * (2 * (m * (m + 2) * (6 * K + 7)) + 3 * (4 * K + 1))))
      + 2 * (k ^ 3 + 2 * k) + (2 * m + 1) * (1 + 2 ^ k * (2 * k + 1))"
proof -
  note SF = sprep_facts[OF sp, where bb = bb, folded Ub_def]
  note SP = sparse_prep_gates[OF av sp, where b = bb]
  have SB: "stands_for (2 ^ (bb + m)) (2 ^ m) (circuit_mat (2 ^ (m + (bb + m))) Bs) Ub" using SF(1) unfolding Bs_def .
  have EB: "\<forall>U \<in> set Bs. elementary (2 ^ (m + (bb + m))) U" using SP(2) unfolding Bs_def .
  have Uu: "Ub *\<^sub>v unit_vec (2 ^ m) 0 = b'" unfolding Ub_def b'_def ..
  have bd: "dim_vec b' = 2 ^ m" using SF(2) unfolding Uu[symmetric] by simp
  have bn: "\<parallel>b'\<parallel> = 1" unfolding Uu[symmetric] using unitary_vnorm[OF SF(2,3), of "unit_vec (2 ^ m) 0"] by simp
  have ap: "bb + m \<le> a" using am by simp
  have am': "m \<le> a" using am by simp
  note H = hhl_lap_gates_correct[OF m k am' ap r mu EB SB SF(3) Uu bd bn t0 C th lmin tb e NQ small,
      folded K_def, unfolded Ub_def b'_def, folded out_def x_def]
  show "\<parallel>b' - Matrix.vec (2 ^ m) (\<lambda>i. complex_of_real (av i))\<parallel> \<le> real m * (2 * pi / 2 ^ bb)"
    unfolding b'_def by (rule rounded_prep[OF av])
  show "\<forall>U \<in> set (hhl_lap_gates m k a (bb + m) \<mu> t0 r C Bs). elementary (2 ^ K) U" by (rule H(1))
  show "circuit_mat (2 ^ K) (hhl_lap_gates m k a (bb + m) \<mu> t0 r C Bs) *\<^sub>v unit_vec (2 ^ K) 0 = anc (2 ^ a) (2 ^ Suc (m + k)) *\<^sub>v out"
    by (rule H(2))
  show "C * t0 / pi \<le> \<parallel>post1 out\<parallel>" by (rule H(3))
  show "\<parallel>complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out
       - tensor_vec (win_state (2 ^ k)) (tensor_vec (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x) (unit_vec 2 1))\<parallel>
      \<le> 2 * (\<epsilon> + 2 * real (2 ^ k - 1) * (18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r)) / (C * \<parallel>x\<parallel>)" by (rule H(4))
  have lB: "length Bs \<le> m * (2 * (length xs * (4 * m + 2 + bb) * (6 * (m + (bb + m)) + 7)) + (bb * (2 * (bb + m) + 1) + 2))"
    using SP(3) unfolding Bs_def .
  show "length (hhl_lap_gates m k a (bb + m) \<mu> t0 r C Bs) \<le> k * (1 + 2 ^ k * (2 * k + 1))
      + m * (2 * (length xs * (4 * m + 2 + bb) * (6 * (m + (bb + m)) + 7)) + (bb * (2 * (bb + m) + 1) + 2)) * (4 * K + 1)
      + 2 * ((2 ^ k - 1) * (r * (2 * (m * (m + 2) * (6 * K + 7)) + 3 * (4 * K + 1))))
      + 2 * (k ^ 3 + 2 * k) + (2 * m + 1) * (1 + 2 ^ k * (2 * k + 1))"
    using H(5) mult_le_mono1[OF lB, of "4 * K + 1"] by linarith
qed

end
