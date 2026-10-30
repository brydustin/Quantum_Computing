theory HHL_Stage_Counts
  imports Gate_List_Placement
begin

section \<open>The other HHL stages as counted gate lists\<close>

subsection \<open>Counting the uniformly controlled rotation\<close>

lemma length_parity_chain: "length (parity_chain ms) \<le> length ms"
  by (induction ms) auto

lemma count_masks: "length (masks k) = 2 ^ k"
  unfolding masks_def by (induction k) (simp_all add: length_concat comp_def sum_list_triv)

lemma count_nzmasks: "length (nzmasks k) \<le> 2 ^ k"
  unfolding nzmasks_def using length_filter_le[of _ "masks k"] count_masks[of k] by simp

lemma length_ucr_gates: "length (ucr_gates k n \<theta>) \<le> 1 + 2 ^ k * (2 * k + 1)"
proof -
  let ?f = "\<lambda>ms. pblock k n ms (- 2 * walsh k \<theta> ms)"
  have "length (concat (map ?f (nzmasks k))) = sum_list (map (length \<circ> ?f) (nzmasks k))" by (simp add: length_concat)
  also have "\<dots> \<le> sum_list (map (\<lambda>_. 2 * k + 1) (nzmasks k))"
  proof (rule sum_list_mono)
    fix ms assume "ms \<in> set (nzmasks k)"
    hence "length ms = k" by (simp add: nzmasks_def length_masks)
    thus "(length \<circ> ?f) ms \<le> 2 * k + 1" using length_parity_chain[of ms] by (simp add: pblock_def)
  qed
  also have "\<dots> = length (nzmasks k) * (2 * k + 1)" by (simp add: sum_list_triv)
  also have "\<dots> \<le> 2 ^ k * (2 * k + 1)" by (rule mult_le_mono1[OF count_nzmasks])
  finally show ?thesis by (simp add: ucr_gates_def)
qed

subsection \<open>The rotation stage\<close>

definition rs_ref :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "rs_ref k s U = (if \<exists>a. U = cv0 k (2 ^ s) (Rot a) then route k s U else [U])"

definition rs_gates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list" where
  "rs_gates k s \<theta> = concat (map (rs_ref k s) (ucr_gates k (2 ^ s) \<theta>))"

theorem rs_gates_props:
  assumes k: "1 \<le> k"
  shows "circuit_mat (2 ^ k * (2 ^ s * 2)) (rs_gates k s \<theta>) = ctrl_blocks (2 ^ k) (2 ^ s * 2) (\<lambda>c. 1\<^sub>m (2 ^ s) \<Otimes> Rot (\<theta> c))"
    "\<forall>U \<in> set (rs_gates k s \<theta>). elementary (2 ^ k * (2 ^ s * 2)) U"
    "length (rs_gates k s \<theta>) \<le> (2 * s + 1) * (1 + 2 ^ k * (2 * k + 1))"
proof -
  let ?K = "2 ^ k * (2 ^ s * 2)" and ?Us = "ucr_gates k (2 ^ s) \<theta>"
  have n0: "0 < (2::nat) ^ s" by simp
  have each: "circuit_mat ?K (rs_ref k s U) = U \<and> (\<forall>V \<in> set (rs_ref k s U). elementary ?K V) \<and> length (rs_ref k s U) \<le> 2 * s + 1"
    if U: "U \<in> set ?Us" for U
  proof (cases "\<exists>a. U = cv0 k (2 ^ s) (Rot a)")
    case True
    then obtain a where a: "U = cv0 k (2 ^ s) (Rot a)" by blast
    note R = route_cv0[OF k Rot_carrier[of a] Rot_unitary[of a], where s = s]
    have "length (route k s U) = 2 * s + 1" by (simp add: route_def up_ops_def)
    thus ?thesis using R True a by (simp add: rs_ref_def)
  next
    case False
    have "U \<in> carrier_mat ?K ?K" using ucr_gates_ok[OF U n0] by simp
    moreover have "elementary ?K U" using ucr_gate_kinds[OF U n0] False by simp
    ultimately show ?thesis using False by (simp add: rs_ref_def)
  qed
  have el: "\<forall>V \<in> set (rs_gates k s \<theta>). elementary ?K V" using each by (auto simp: rs_gates_def)
  thus "\<forall>U \<in> set (rs_gates k s \<theta>). elementary ?K U" .
  have "circuit_mat ?K (rs_gates k s \<theta>) = circuit_mat ?K (map (circuit_mat ?K) (map (rs_ref k s) ?Us))"
    unfolding rs_gates_def by (rule circuit_mat_concat) (use each elementary_unitary(1) in fastforce)
  also have "map (circuit_mat ?K) (map (rs_ref k s) ?Us) = ?Us" by (rule nth_equalityI) (use each in auto)
  finally show "circuit_mat ?K (rs_gates k s \<theta>) = ctrl_blocks (2 ^ k) (2 ^ s * 2) (\<lambda>c. 1\<^sub>m (2 ^ s) \<Otimes> Rot (\<theta> c))"
    using ucr_circuit[OF n0, of k \<theta>] by simp
  have "length (rs_gates k s \<theta>) = sum_list (map (length \<circ> rs_ref k s) ?Us)" by (simp add: rs_gates_def length_concat)
  also have "\<dots> \<le> sum_list (map (\<lambda>_. 2 * s + 1) ?Us)" by (rule sum_list_mono) (use each in simp)
  also have "\<dots> = length ?Us * (2 * s + 1)" by (simp add: sum_list_triv)
  also have "\<dots> \<le> (1 + 2 ^ k * (2 * k + 1)) * (2 * s + 1)" by (rule mult_le_mono1[OF length_ucr_gates])
  finally show "length (rs_gates k s \<theta>) \<le> (2 * s + 1) * (1 + 2 ^ k * (2 * k + 1))" by (simp add: ac_simps)
qed

subsection \<open>The clock window and the Fourier transform\<close>

lemma length_prep_gates: "length (prep_gates k a) \<le> k * (1 + 2 ^ k * (2 * k + 1))"
proof -
  have "length (prep_gates k a) = sum_list (map (length \<circ> lev_gates k a) [0..<k])" by (simp add: prep_gates_def length_concat)
  also have "\<dots> \<le> sum_list (map (\<lambda>_. 1 + 2 ^ k * (2 * k + 1)) [0..<k])"
  proof (rule sum_list_mono)
    fix j assume "j \<in> set [0..<k]"
    hence j: "j \<le> k" by simp
    have "length (ucr_gates j 1 (pangle k a j)) \<le> 1 + 2 ^ j * (2 * j + 1)" by (rule length_ucr_gates)
    also have "\<dots> \<le> 1 + 2 ^ k * (2 * k + 1)" using j by (intro add_left_mono mult_mono power_increasing) simp_all
    finally show "(length \<circ> lev_gates k a) j \<le> 1 + 2 ^ k * (2 * k + 1)" by (simp add: lev_gates_def)
  qed
  finally show ?thesis by (simp add: sum_list_triv)
qed

lemma length_qft: "length (qft_circuit k) \<le> k ^ 3 + 2 * k"
  using length_qft_circuit[of k] by simp

end
