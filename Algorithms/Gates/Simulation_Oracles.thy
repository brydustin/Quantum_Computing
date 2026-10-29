theory Simulation_Oracles
  imports Simulation_Rounded
begin

section \<open>The sparse simulation from oracles and elementary gates\<close>

subsection \<open>Isometries\<close>

text \<open>A matrix whose columns are distinct unit vectors preserves norms.\<close>

lemma select_norm:
  assumes f: "\<And>c. c < n \<Longrightarrow> f c < m" "inj_on f {..<n}" and v: "dim_vec v = n"
  shows "\<parallel>Matrix.mat m n (\<lambda>(r, c). if r = f c then 1 else 0) *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
proof -
  let ?M = "Matrix.mat m n (\<lambda>(r, c). if r = f c then 1 else 0) :: complex Matrix.mat"
  have e: "(?M *\<^sub>v v) $ r = (\<Sum>c<n. (if r = f c then 1 else 0) * v $ c)" if "r < m" for r
    using that v by (simp add: scalar_prod_def atLeast0LessThan)
  have s: "(\<Sum>r<m. (cmod ((?M *\<^sub>v v) $ r))\<^sup>2) = (\<Sum>c<n. (cmod (v $ c))\<^sup>2)"
  proof -
    have "(\<Sum>r<m. (cmod ((?M *\<^sub>v v) $ r))\<^sup>2) = (\<Sum>r \<in> f ` {..<n}. (cmod ((?M *\<^sub>v v) $ r))\<^sup>2)"
    proof (rule sum.mono_neutral_right)
      show "f ` {..<n} \<subseteq> {..<m}" using f(1) by auto
      show "\<forall>r \<in> {..<m} - f ` {..<n}. (cmod ((?M *\<^sub>v v) $ r))\<^sup>2 = 0"
      proof
        fix r assume "r \<in> {..<m} - f ` {..<n}"
        hence "r < m" "\<And>c. c < n \<Longrightarrow> r \<noteq> f c" by auto
        thus "(cmod ((?M *\<^sub>v v) $ r))\<^sup>2 = 0" using e by simp
      qed
    qed simp
    also have "\<dots> = (\<Sum>c<n. (cmod ((?M *\<^sub>v v) $ f c))\<^sup>2)" by (rule sum.reindex_cong[OF f(2) refl]) simp
    also have "\<dots> = (\<Sum>c<n. (cmod (v $ c))\<^sup>2)"
    proof (rule sum.cong[OF refl])
      fix c assume c: "c \<in> {..<n}"
      have "(\<Sum>c'<n. (if f c = f c' then 1 else 0) * v $ c') = (\<Sum>c'<n. if c' = c then v $ c' else 0)"
        using f(2) c by (intro sum.cong) (auto simp: inj_on_def)
      also have "\<dots> = v $ c" using c by simp
      finally show "(cmod ((?M *\<^sub>v v) $ f c))\<^sup>2 = (cmod (v $ c))\<^sup>2" using e[of "f c"] f(1) c by simp
    qed
    finally show ?thesis .
  qed
  thus ?thesis using v by (simp add: cpx_vec_length_def)
qed

lemma anc_norm: "dim_vec w = N \<Longrightarrow> 0 < A \<Longrightarrow> \<parallel>anc A N *\<^sub>v w\<parallel> = \<parallel>w\<parallel>"
  unfolding anc_def by (rule select_norm[where f = id, simplified]) (auto simp: less_le_trans[OF _ mult_le_mono1[of 1 A]])

lemma emb_norm: "dim_vec v = n \<Longrightarrow> \<parallel>emb n *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
  unfolding emb_def
proof (rule select_norm)
  show "\<And>c. c < n \<Longrightarrow> enc n c 0 0 < n * n * 2" by (rule enc_lt) simp_all
  show "inj_on (\<lambda>c. enc n c 0 0) {..<n}" by (rule inj_onI) (simp add: enc_def)
qed

text \<open>Closeness passes through isometries on either side.\<close>

lemma op_close_isom:
  assumes M1: "M1 \<in> carrier_mat N N" and M2: "M2 \<in> carrier_mat N N" and c: "M1 \<approx>\<^bsub>\<epsilon>\<^esub> M2"
    and P: "P \<in> carrier_mat M N" "\<And>w. dim_vec w = N \<Longrightarrow> \<parallel>P *\<^sub>v w\<parallel> = \<parallel>w\<parallel>"
    and Q: "Q \<in> carrier_mat N k" "\<And>v. dim_vec v = k \<Longrightarrow> \<parallel>Q *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
  shows "P * M1 * Q \<approx>\<^bsub>\<epsilon>\<^esub> P * M2 * Q"
proof (rule op_closeI[OF mult_carrier_mat[OF mult_carrier_mat[OF P(1) M1] Q(1)]])
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = k"
  have vc: "v \<in> carrier_vec k" by (rule carrier_vecI[OF v])
  let ?u = "Q *\<^sub>v v"
  have u: "dim_vec ?u = N" using Q(1) by simp
  have uc: "?u \<in> carrier_vec N" using u by (rule carrier_vecI)
  have "P * M1 * Q *\<^sub>v v - P * M2 * Q *\<^sub>v v = P *\<^sub>v (M1 *\<^sub>v ?u - M2 *\<^sub>v ?u)"
  proof -
    have a: "P * M1 * Q *\<^sub>v v = P *\<^sub>v (M1 *\<^sub>v ?u)"
      using assoc_mult_mat_vec[OF mult_carrier_mat[OF P(1) M1] Q(1) vc] assoc_mult_mat_vec[OF P(1) M1 uc] by simp
    have b: "P * M2 * Q *\<^sub>v v = P *\<^sub>v (M2 *\<^sub>v ?u)"
      using assoc_mult_mat_vec[OF mult_carrier_mat[OF P(1) M2] Q(1) vc] assoc_mult_mat_vec[OF P(1) M2 uc] by simp
    have d: "P *\<^sub>v (M1 *\<^sub>v ?u - M2 *\<^sub>v ?u) = P *\<^sub>v (M1 *\<^sub>v ?u) - P *\<^sub>v (M2 *\<^sub>v ?u)"
      by (rule mult_minus_distrib_mat_vec[OF P(1)]) (use M1 M2 uc in auto)
    show ?thesis unfolding a b d ..
  qed
  also have "\<parallel>\<dots>\<parallel> = \<parallel>M1 *\<^sub>v ?u - M2 *\<^sub>v ?u\<parallel>" by (rule P(2)) (use M1 M2 in simp)
  also have "\<dots> \<le> \<epsilon> * \<parallel>?u\<parallel>" by (rule op_closeD[OF c M1 u])
  also have "\<parallel>?u\<parallel> = \<parallel>v\<parallel>" by (rule Q(2)[OF v])
  finally show "\<parallel>P * M1 * Q *\<^sub>v v - P * M2 * Q *\<^sub>v v\<parallel> \<le> \<epsilon> * \<parallel>v\<parallel>" .
qed

subsection \<open>One workspace for all gates\<close>

lemma pow_split: "w \<le> Wt \<Longrightarrow> (2::nat) ^ (Wt - w) * 2 ^ w = 2 ^ Wt"
  by (simp flip: power_add)

lemma lift_stands_for:
  assumes s: "stands_for (2 ^ w) N (circuit_mat (2 ^ w * N) L) G"
    and L: "\<And>U. U \<in> set L \<Longrightarrow> U \<in> carrier_mat (2 ^ w * N) (2 ^ w * N)" and w: "w \<le> Wt" and N: "0 < N"
  shows "stands_for (2 ^ Wt) N (circuit_mat (2 ^ Wt * N) (map (\<lambda>U. 1\<^sub>m (2 ^ (Wt - w)) \<Otimes> U) L)) G"
proof -
  have e: "circuit_mat (2 ^ (Wt - w) * (2 ^ w * N)) (map (\<lambda>U. 1\<^sub>m (2 ^ (Wt - w)) \<Otimes> U) L) = 1\<^sub>m (2 ^ (Wt - w)) \<Otimes> circuit_mat (2 ^ w * N) L"
    by (rule circuit_mat_tensor_left[OF L]) (simp_all add: N)
  have d: "(2::nat) ^ (Wt - w) * (2 ^ w * N) = 2 ^ Wt * N" using pow_split[OF w] by (simp add: Groups.mult.assoc[symmetric])
  have "stands_for (2 ^ (Wt - w) * 2 ^ w) N (1\<^sub>m (2 ^ (Wt - w)) \<Otimes> circuit_mat (2 ^ w * N) L) G"
    by (rule stands_for_extend[OF s]) simp
  thus ?thesis unfolding pow_split[OF w] e[unfolded d, symmetric] .
qed


subsection \<open>The gates of each simulation step\<close>

text \<open>With $b$-bit angles the workspace above the data has $\max(2m+5, 2b)$ wires: the
comparator's scratch wires and the entry register share them.\<close>

definition wsp :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "wsp m b = max (2 * m + 5) (2 * b)"

definition blk :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> sgate \<Rightarrow> complex Matrix.mat list" where
  "blk m b d A Os g = (let Wt = wsp m b in
     if g = Cmp then map (\<lambda>U. 1\<^sub>m (2 ^ (Wt - (2 * m + 5))) \<Otimes> U) (compile (4 * m + 6) (sort_flag m))
     else if g = Ent then map (\<lambda>U. 1\<^sub>m (2 ^ (Wt - 2 * b)) \<Otimes> U) (ent_gates b (2 * m) (ent_code b (2 ^ m) d A))
     else if g = DiagQ then map (\<lambda>U. 1\<^sub>m (2 ^ (Wt - b)) \<Otimes> U) (dia_gates b (2 * m) (dia_code b (2 ^ m) d A))
     else [1\<^sub>m (2 ^ Wt) \<Otimes> sgate_mat (2 ^ m) d A Os g])"

lemma data_pow: "(2::nat) ^ (2 * m) = 2 ^ m * 2 ^ m" by (simp add: mult_2 power_add)

lemma blk_stands_for:
  fixes m b :: nat
  defines "N \<equiv> 2 ^ m * 2 ^ m * 2 :: nat" and "Wt \<equiv> wsp m b"
  assumes g: "gate_ok K g" and Oc: "\<And>c. c < K \<Longrightarrow> Os c \<in> carrier_mat N N"
  shows "stands_for (2 ^ Wt) N (circuit_mat (2 ^ Wt * N) (blk m b d A Os g)) (sgate_rnd b (2 ^ m) d A Os g)"
    "\<And>U. U \<in> set (blk m b d A Os g) \<Longrightarrow> U \<in> carrier_mat (2 ^ Wt * N) (2 ^ Wt * N)"
proof -
  have N0: "0 < N" unfolding N_def by simp
  have nnN: "(2::nat) ^ (2 * m) * 2 = N" unfolding N_def data_pow ..
  have wc: "2 * m + 5 \<le> Wt" and we: "2 * b \<le> Wt" and wd: "b \<le> Wt" unfolding Wt_def wsp_def by simp_all
  have lift_car: "1\<^sub>m (2 ^ (Wt - w)) \<Otimes> U \<in> carrier_mat (2 ^ Wt * N) (2 ^ Wt * N)"
    if "U \<in> carrier_mat (2 ^ w * N) (2 ^ w * N)" "w \<le> Wt" for U w
  proof -
    have "1\<^sub>m (2 ^ (Wt - w)) \<Otimes> U \<in> carrier_mat (2 ^ (Wt - w) * (2 ^ w * N)) (2 ^ (Wt - w) * (2 ^ w * N))"
      using that(1) by simp
    moreover have "(2::nat) ^ (Wt - w) * (2 ^ w * N) = 2 ^ Wt * N" using pow_split[OF that(2)] by (simp add: Groups.mult.assoc[symmetric])
    ultimately show ?thesis by simp
  qed
  have "stands_for (2 ^ Wt) N (circuit_mat (2 ^ Wt * N) (blk m b d A Os g)) (sgate_rnd b (2 ^ m) d A Os g)
      \<and> (\<forall>U \<in> set (blk m b d A Os g). U \<in> carrier_mat (2 ^ Wt * N) (2 ^ Wt * N))"
  proof (cases "g = Cmp")
    case True
    let ?L = "compile (4 * m + 6) (sort_flag m)"
    have dc: "(2::nat) ^ (4 * m + 6) = 2 ^ (2 * m + 5) * N" unfolding N_def by (rule anc_size)
    have Lc: "\<And>U. U \<in> set ?L \<Longrightarrow> U \<in> carrier_mat (2 ^ (2 * m + 5) * N) (2 ^ (2 * m + 5) * N)"
      using sort_flag_gates(1)[of m] elementary_carrier unfolding dc by blast
    have s: "stands_for (2 ^ (2 * m + 5)) N (circuit_mat (2 ^ (2 * m + 5) * N) ?L) (cmp_gate (2 ^ m))"
      using cmp_compiled_stands_for[of m] unfolding dc N_def .
    show ?thesis using lift_stands_for[OF s Lc wc N0] lift_car Lc wc True
      by (auto simp: blk_def Wt_def[symmetric] sgate_rnd_def)
  next
    case nC: False
    show ?thesis
    proof (cases "g = Ent")
      case True
      let ?f = "ent_code b (2 ^ m) d A"
      have f: "\<And>k. k < 2 ^ (2 * m) \<Longrightarrow> ?f k < 2 ^ (2 * b)" by (rule ent_code_parts(3))
      have E1: "stands_for (2 ^ (2 * b)) (2 ^ (2 * m) * 2) (circuit_mat (2 ^ (2 * m + 1 + 2 * b)) (ent_gates b (2 * m) ?f))
          (ent_rounded b (2 ^ (2 * m)) ?f)" by (rule ent_gates_props(1)) (rule f)
      have E2: "elementary (2 ^ (2 * m + 1 + 2 * b)) U \<or> U = ent_oracle (2 * b) (2 ^ (2 * m)) ?f"
        if "U \<in> set (ent_gates b (2 * m) ?f)" for U by (rule ent_gates_props(2)) (use f that in auto)
      have de: "(2::nat) ^ (2 * m + 1 + 2 * b) = 2 ^ (2 * b) * N" unfolding nnN[symmetric] by (simp add: power_add ac_simps)
      have Ec: "\<And>U. U \<in> set (ent_gates b (2 * m) ?f) \<Longrightarrow> U \<in> carrier_mat (2 ^ (2 * b) * N) (2 ^ (2 * b) * N)"
      proof -
        fix U assume U: "U \<in> set (ent_gates b (2 * m) ?f)"
        have "ent_oracle (2 * b) (2 ^ (2 * m)) ?f \<in> carrier_mat (2 ^ (2 * b) * 2 ^ (2 * m) * 2) (2 ^ (2 * b) * 2 ^ (2 * m) * 2)"
          unfolding ent_oracle_def by simp
        hence "ent_oracle (2 * b) (2 ^ (2 * m)) ?f \<in> carrier_mat (2 ^ (2 * b) * N) (2 ^ (2 * b) * N)"
          unfolding nnN[symmetric] Groups.mult.assoc .
        thus "U \<in> carrier_mat (2 ^ (2 * b) * N) (2 ^ (2 * b) * N)" using E2[OF U] elementary_carrier unfolding de by blast
      qed
      have s0: "stands_for (2 ^ (2 * b)) N (circuit_mat (2 ^ (2 * b) * N) (ent_gates b (2 * m) ?f)) (ent_rounded b (2 ^ (2 * m)) ?f)"
        using E1 unfolding de nnN .
      have s: "stands_for (2 ^ (2 * b)) N (circuit_mat (2 ^ (2 * b) * N) (ent_gates b (2 * m) ?f)) (ent_rounded b (2 ^ m * 2 ^ m) ?f)"
        using s0 unfolding data_pow[of m] .
      show ?thesis using lift_stands_for[OF s Ec we N0] lift_car Ec we True
        by (auto simp: blk_def Wt_def[symmetric] sgate_rnd_def)
    next
      case nE: False
      show ?thesis
      proof (cases "g = DiagQ")
        case True
        let ?f = "dia_code b (2 ^ m) d A"
        have f: "\<And>k. k < 2 ^ (2 * m) \<Longrightarrow> ?f k < 2 ^ b" by (simp add: dia_code_def near_bits)
        have D1: "stands_for (2 ^ b) (2 ^ (2 * m) * 2) (circuit_mat (2 ^ (2 * m + 1 + b)) (dia_gates b (2 * m) ?f))
            (dia_rounded b (2 ^ (2 * m)) ?f)" by (rule dia_gates_props(1)) (rule f)
        have D2: "elementary (2 ^ (2 * m + 1 + b)) U \<or> U = ent_oracle b (2 ^ (2 * m)) ?f"
          if "U \<in> set (dia_gates b (2 * m) ?f)" for U by (rule dia_gates_props(2)) (use f that in auto)
        have dd: "(2::nat) ^ (2 * m + 1 + b) = 2 ^ b * N" unfolding nnN[symmetric] by (simp add: power_add ac_simps)
        have Dc: "\<And>U. U \<in> set (dia_gates b (2 * m) ?f) \<Longrightarrow> U \<in> carrier_mat (2 ^ b * N) (2 ^ b * N)"
        proof -
          fix U assume U: "U \<in> set (dia_gates b (2 * m) ?f)"
          have "ent_oracle b (2 ^ (2 * m)) ?f \<in> carrier_mat (2 ^ b * 2 ^ (2 * m) * 2) (2 ^ b * 2 ^ (2 * m) * 2)"
            unfolding ent_oracle_def by simp
          hence "ent_oracle b (2 ^ (2 * m)) ?f \<in> carrier_mat (2 ^ b * N) (2 ^ b * N)"
            unfolding nnN[symmetric] Groups.mult.assoc .
          thus "U \<in> carrier_mat (2 ^ b * N) (2 ^ b * N)" using D2[OF U] elementary_carrier unfolding dd by blast
        qed
        have s0: "stands_for (2 ^ b) N (circuit_mat (2 ^ b * N) (dia_gates b (2 * m) ?f)) (dia_rounded b (2 ^ (2 * m)) ?f)"
          using D1 unfolding dd nnN .
        have s: "stands_for (2 ^ b) N (circuit_mat (2 ^ b * N) (dia_gates b (2 * m) ?f)) (dia_rounded b (2 ^ m * 2 ^ m) ?f)"
          using s0 unfolding data_pow[of m] .
        show ?thesis using lift_stands_for[OF s Dc wd N0] lift_car Dc wd True
          by (auto simp: blk_def Wt_def[symmetric] sgate_rnd_def)
      next
        case nD: False
        have G: "sgate_mat (2 ^ m) d A Os g \<in> carrier_mat N N"
          unfolding N_def by (rule sgate_carrier[where K = K]) (use Oc g in \<open>auto simp: N_def\<close>)
        have c: "1\<^sub>m (2 ^ Wt) \<Otimes> sgate_mat (2 ^ m) d A Os g \<in> carrier_mat (2 ^ Wt * N) (2 ^ Wt * N)" using G by simp
        have "stands_for (2 ^ Wt) N (1\<^sub>m (2 ^ Wt) \<Otimes> sgate_mat (2 ^ m) d A Os g) (sgate_mat (2 ^ m) d A Os g)"
          by (rule stands_for_lift[OF G]) simp
        thus ?thesis using nC nE nD c left_mult_one_mat[OF c]
          by (simp add: blk_def Wt_def[symmetric] sgate_rnd_def)
      qed
    qed
  qed
  thus "stands_for (2 ^ Wt) N (circuit_mat (2 ^ Wt * N) (blk m b d A Os g)) (sgate_rnd b (2 ^ m) d A Os g)"
    "\<And>U. U \<in> set (blk m b d A Os g) \<Longrightarrow> U \<in> carrier_mat (2 ^ Wt * N) (2 ^ Wt * N)" by blast+
qed


theorem sim_blk_stands_for:
  fixes m b :: nat
  defines "N \<equiv> 2 ^ m * 2 ^ m * 2 :: nat" and "Wt \<equiv> wsp m b"
  assumes sl: "\<And>g. g \<in> set sl \<Longrightarrow> gate_ok K g" and Oc: "\<And>c. c < K \<Longrightarrow> Os c \<in> carrier_mat N N"
  shows "stands_for (2 ^ Wt) N (circuit_mat (2 ^ Wt * N) (concat (map (blk m b d A Os) sl)))
      (circuit_mat N (map (sgate_rnd b (2 ^ m) d A Os) sl))"
proof -
  note B = blk_stands_for[where m = m and b = b and K = K and Os = Os and d = d and A = A, folded N_def Wt_def]
  have car: "U \<in> carrier_mat (2 ^ Wt * N) (2 ^ Wt * N)" if "Us \<in> set (map (blk m b d A Os) sl)" "U \<in> set Us" for Us U
    using that B(2)[OF sl Oc] by auto
  have "circuit_mat (2 ^ Wt * N) (concat (map (blk m b d A Os) sl))
      = circuit_mat (2 ^ Wt * N) (map (circuit_mat (2 ^ Wt * N)) (map (blk m b d A Os) sl))"
    by (rule circuit_mat_concat) (rule car)
  moreover have "list_all2 (stands_for (2 ^ Wt) N) (map (circuit_mat (2 ^ Wt * N)) (map (blk m b d A Os) sl))
      (map (sgate_rnd b (2 ^ m) d A Os) sl)"
    using sl by (auto simp: list_all2_map1 list_all2_map2 list_all2_same intro!: B(1)[OF _ Oc])
  ultimately show ?thesis using stands_for_circuit[where A = "2 ^ Wt" and N = N] by simp
qed

lemma op_close_trans_rect:
  assumes "M1 \<approx>\<^bsub>a\<^esub> M2" "M2 \<approx>\<^bsub>c\<^esub> M3" "M1 \<in> carrier_mat M k" "M2 \<in> carrier_mat M k" "M3 \<in> carrier_mat M k"
  shows "M1 \<approx>\<^bsub>a + c\<^esub> M3"
proof (rule op_closeI[OF assms(3)])
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = k"
  have "\<parallel>M1 *\<^sub>v v - M3 *\<^sub>v v\<parallel> \<le> \<parallel>M1 *\<^sub>v v - M2 *\<^sub>v v\<parallel> + \<parallel>M2 *\<^sub>v v - M3 *\<^sub>v v\<parallel>"
    by (rule vnorm_diff_le[where n = M]) (use assms(3-5) in simp_all)
  also have "\<dots> \<le> a * \<parallel>v\<parallel> + c * \<parallel>v\<parallel>"
    using op_closeD[OF assms(1,3) v] op_closeD[OF assms(2,4) v] by linarith
  finally show "\<parallel>M1 *\<^sub>v v - M3 *\<^sub>v v\<parallel> \<le> (a + c) * \<parallel>v\<parallel>" by (simp add: algebra_simps)
qed

subsection \<open>The simulation theorem\<close>

text \<open>For an $s$-sparse Hermitian $A$ on $m$ qubits with entries bounded by $L$, colour oracles
for a $(2s-1)$-colouring, and $b$-bit angles: with the $\max(2m+5, 2b)$ workspace wires clear,
the circuit of elementary gates and oracle queries started in $\ket x\ket0\ket0$ is
$\bigl(8(sLt)^2/r + r((2s-1)\,6\pi/2^b + 2\pi/2^b)\bigr)$-close to $e^{itA}\ket x$.\<close>

definition in0 :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "in0 m b = anc (2 ^ wsp m b) (2 ^ m * 2 ^ m * 2) * emb (2 ^ m)"

theorem sparse_simulation_gates:
  fixes m s r b :: nat and t L :: real and A :: "complex Matrix.mat" and Os :: "nat \<Rightarrow> complex Matrix.mat"
    and p :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  defines "n \<equiv> 2 ^ m" and "N \<equiv> 2 ^ m * 2 ^ m * 2 :: nat" and "Wt \<equiv> wsp m b"
    and "C \<equiv> concat (map (blk m b (t / real r) A Os) (sim_gates (2 * s - 1) r))"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and s: "1 \<le> s"
      and L: "0 \<le> L" and Lb: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (A $$ (i, j)) \<le> L"
      and cov: "edge_cover n (2 * s - 1) p (edges n A)"
      and Os: "\<And>c. c < 2 * s - 1 \<Longrightarrow> colour_oracle n (p c) (Os c)" and r: "0 < r"
  shows "circuit_mat (2 ^ Wt * N) C * in0 m b
    \<approx>\<^bsub>8 * (real s * L * t)\<^sup>2 / real r + real r * (real (2 * s - 1) * (6 * pi / 2 ^ b) + 2 * pi / 2 ^ b)\<^esub> in0 m b * evolution A t"
proof -
  have in0e: "in0 m b = anc (2 ^ Wt) N * emb (2 ^ m)" unfolding in0_def Wt_def N_def ..
  let ?d = "t / real r" and ?sl = "sim_gates (2 * s - 1) r"
  note S = sparse_simulation_circuit[OF A[unfolded n_def] s L Lb[unfolded n_def] cov[unfolded n_def] Os[unfolded n_def] r]
  have Oc: "\<And>c. c < 2 * s - 1 \<Longrightarrow> Os c \<in> carrier_mat N N" using Os unfolding colour_oracle_def n_def N_def by blast
  let ?P = "circuit_mat (2 ^ Wt * N) C" and ?a = "anc (2 ^ Wt) N" and ?e = "emb (2 ^ m)"
  let ?Rr = "circuit_mat N (map (sgate_rnd b (2 ^ m) ?d A Os) ?sl)" and ?R = "sg_run (2 ^ m) ?d A Os ?sl"
  let ?V = "sim_mat (2 ^ m) ?d A (2 * s - 1) p r" and ?E = "evolution A t"
  have st: "stands_for (2 ^ Wt) N ?P ?Rr" unfolding C_def N_def Wt_def
    by (rule sim_blk_stands_for) (use sim_gates_ok Oc in \<open>auto simp: N_def\<close>)
  have Pc: "?P \<in> carrier_mat (2 ^ Wt * N) (2 ^ Wt * N)" and Rrc: "?Rr \<in> carrier_mat N N"
    and Pa: "?P * ?a = ?a * ?Rr" using st by (simp_all add: stands_for_def)
  have cl0: "?R \<approx>\<^bsub>sum_list (map (gate_err b) ?sl)\<^esub> circuit_mat (2 ^ m * 2 ^ m * 2) (map (sgate_rnd b (2 ^ m) ?d A Os) ?sl)"
    by (rule sim_rounded_close[where K = "2 * s - 1" and q = p]) (use Os[unfolded n_def] sim_gates_ok in auto)
  have cl: "?R \<approx>\<^bsub>real r * (real (2 * s - 1) * (6 * pi / 2 ^ b) + 2 * pi / 2 ^ b)\<^esub> ?Rr"
    using cl0 unfolding sim_gates_err N_def .
  have Rc: "?R \<in> carrier_mat N N" unfolding N_def by (rule sg_run_carrier[where K = "2 * s - 1"]) (use Oc sim_gates_ok in \<open>auto simp: N_def\<close>)
  have cl': "?Rr \<approx>\<^bsub>real r * (real (2 * s - 1) * (6 * pi / 2 ^ b) + 2 * pi / 2 ^ b)\<^esub> ?R" by (rule op_close_sym[OF cl Rc Rrc])
  have ac: "?a \<in> carrier_mat (2 ^ Wt * N) N" by simp
  have ec: "?e \<in> carrier_mat N (2 ^ m)" unfolding N_def by simp
  have an: "\<And>w. dim_vec w = N \<Longrightarrow> \<parallel>?a *\<^sub>v w\<parallel> = \<parallel>w\<parallel>" by (rule anc_norm) simp_all
  have en: "\<And>v. dim_vec v = 2 ^ m \<Longrightarrow> \<parallel>?e *\<^sub>v v\<parallel> = \<parallel>v\<parallel>" by (rule emb_norm)
  have Vc: "?V \<in> carrier_mat (2 ^ m) (2 ^ m)" using S(2) by (simp add: n_def)
  have Ec: "?E \<in> carrier_mat (2 ^ m) (2 ^ m)" by (rule evolution_carrier) (use A in \<open>simp_all add: n_def\<close>)
  \<comment> \<open>the compiled circuit on clean ancillas is the rounded simulation\<close>
  have e1: "?P * in0 m b = ?a * ?Rr * ?e"
  proof -
    have "?P * (?a * ?e) = ?P * ?a * ?e" by (rule assoc_mult_mat[OF Pc ac ec, symmetric])
    thus ?thesis unfolding in0e Pa .
  qed
  have c1: "?a * ?Rr * ?e \<approx>\<^bsub>real r * (real (2 * s - 1) * (6 * pi / 2 ^ b) + 2 * pi / 2 ^ b)\<^esub> ?a * ?R * ?e"
    by (rule op_close_isom[OF Rrc Rc cl' ac an ec en])
  \<comment> \<open>the exact simulation is the simulated evolution\<close>
  have e2: "?a * ?R * ?e = in0 m b * ?V"
  proof -
    have "?a * ?R * ?e = ?a * (?R * ?e)" by (rule assoc_mult_mat[OF ac Rc ec])
    also have "?R * ?e = ?e * ?V" using S(1) by (simp add: n_def)
    also have "?a * (?e * ?V) = ?a * ?e * ?V" by (rule assoc_mult_mat[OF ac ec Vc, symmetric])
    finally show ?thesis unfolding in0e .
  qed
  have Ic: "in0 m b \<in> carrier_mat (2 ^ Wt * N) (2 ^ m)" unfolding in0e by (rule mult_carrier_mat[OF ac ec])
  have In: "\<And>v. dim_vec v = 2 ^ m \<Longrightarrow> \<parallel>in0 m b *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
  proof -
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = 2 ^ m"
    have "in0 m b *\<^sub>v v = ?a *\<^sub>v (?e *\<^sub>v v)" 
      unfolding in0e by (rule assoc_mult_mat_vec[OF ac ec], simp add: carrier_dim_vec v) 
    thus "\<parallel>in0 m b *\<^sub>v v\<parallel> = \<parallel>v\<parallel>" using an[of "?e *\<^sub>v v"] en[OF v] ec by simp
  qed
  have S4: "?V \<approx>\<^bsub>8 * (real s * L * t)\<^sup>2 / real r\<^esub> ?E" using S(4) by (simp add: n_def)
  have c2': "in0 m b * ?V \<approx>\<^bsub>8 * (real s * L * t)\<^sup>2 / real r\<^esub> in0 m b * ?E"
  proof (rule op_closeI[OF mult_carrier_mat[OF Ic Vc]])
    fix v :: "complex Matrix.vec" assume v: "dim_vec v = 2 ^ m"
    have vc: "v \<in> carrier_vec (2 ^ m)" by (rule carrier_vecI[OF v])
    have a: "in0 m b * ?V *\<^sub>v v = in0 m b *\<^sub>v (?V *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF Ic Vc vc])
    have b: "in0 m b * ?E *\<^sub>v v = in0 m b *\<^sub>v (?E *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF Ic Ec vc])
    have Vv: "?V *\<^sub>v v \<in> carrier_vec (2 ^ m)" and Ev: "?E *\<^sub>v v \<in> carrier_vec (2 ^ m)"
      by (rule mult_mat_vec_carrier[OF Vc vc], rule mult_mat_vec_carrier[OF Ec vc])
    have d: "in0 m b *\<^sub>v (?V *\<^sub>v v - ?E *\<^sub>v v) = in0 m b *\<^sub>v (?V *\<^sub>v v) - in0 m b *\<^sub>v (?E *\<^sub>v v)"
      by (rule mult_minus_distrib_mat_vec[OF Ic Vv Ev])
    have "\<parallel>in0 m b * ?V *\<^sub>v v - in0 m b * ?E *\<^sub>v v\<parallel> = \<parallel>?V *\<^sub>v v - ?E *\<^sub>v v\<parallel>"
      unfolding a b d[symmetric] by (rule In) (use Vv Ec in simp)
    also have "\<dots> \<le> 8 * (real s * L * t)\<^sup>2 / real r * \<parallel>v\<parallel>" by (rule op_closeD[OF S4 Vc v])
    finally show "\<parallel>in0 m b * ?V *\<^sub>v v - in0 m b * ?E *\<^sub>v v\<parallel> \<le> 8 * (real s * L * t)\<^sup>2 / real r * \<parallel>v\<parallel>" .
  qed
  have "?a * ?Rr * ?e \<approx>\<^bsub>real r * (real (2 * s - 1) * (6 * pi / 2 ^ b) + 2 * pi / 2 ^ b) + 8 * (real s * L * t)\<^sup>2 / real r\<^esub> in0 m b * ?E"
    by (rule op_close_trans_rect[OF c1[unfolded e2] c2' mult_carrier_mat[OF mult_carrier_mat[OF ac Rrc] ec]
        mult_carrier_mat[OF Ic Vc] mult_carrier_mat[OF Ic Ec]])
  thus ?thesis unfolding e1 by (simp add: add.commute)
qed

end
