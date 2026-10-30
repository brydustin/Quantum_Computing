theory Gate_List_Placement
  imports Phase_Estimation_Gates
begin

section \<open>Gate lists on other wires\<close>

lemma pow2_dvd: "b dvd (2::nat) ^ n \<Longrightarrow> \<exists>w. b = 2 ^ w"
proof (induction n arbitrary: b)
  case 0
  thus ?case by (intro exI[of _ 0]) simp
next
  case (Suc n)
  show ?case
  proof (cases "even b")
    case True
    then obtain c where c: "b = 2 * c" by (rule evenE)
    have "2 * c dvd 2 * 2 ^ n" using Suc.prems c by simp
    hence "c dvd 2 ^ n" by simp
    then obtain w where "c = 2 ^ w" using Suc.IH by blast
    thus ?thesis using c by (intro exI[of _ "Suc w"]) simp
  next
    case False
    hence "coprime b 2" by simp
    hence "b dvd 2 ^ n" using Suc.prems coprime_dvd_mult_left_iff[of b 2 "2 ^ n"] by (simp add: ac_simps)
    thus ?thesis by (rule Suc.IH)
  qed
qed

text \<open>An elementary gate on $K$ wires is a wire gate on one or two adjacent wires.\<close>

lemma elementary_wg:
  assumes E: "elementary (2 ^ K) U"
  shows "\<exists>w q G. q \<in> {1, 2} \<and> w + q \<le> K \<and> G \<in> carrier_mat (2 ^ q) (2 ^ q) \<and> Quantum.unitary G \<and> U = wg K [w..<w + q] G"
proof -
  obtain a b q G where G: "q \<in> {1, 2}" "G \<in> carrier_mat (2 ^ q) (2 ^ q)" "Quantum.unitary G" "0 < a" "0 < b"
      and K: "(2::nat) ^ K = a * (2 ^ q * b)" and U: "U = 1\<^sub>m a \<Otimes> (G \<Otimes> 1\<^sub>m b)"
    using E unfolding elementary_def by blast
  have "a dvd 2 ^ K" unfolding K by simp
  then obtain v where v: "a = 2 ^ v" using pow2_dvd by blast
  have "b dvd 2 ^ K" unfolding K by (rule dvd_mult) simp
  then obtain w where w: "b = 2 ^ w" using pow2_dvd by blast
  have "(2::nat) ^ K = 2 ^ (v + q + w)" using K v w by (simp add: power_add)
  hence Kv: "K = v + q + w" by simp
  have "U = wg (v + q + w) [w..<w + q] G" unfolding U v w by (rule tensor_wg[OF G(2)])
  thus ?thesis using G Kv by (intro exI[of _ w] exI[of _ q] exI[of _ G]) simp
qed

definition relab1 :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "relab1 K K' vs U = (let (w, q, G) = (SOME (w, q, G). q \<in> {1, 2} \<and> w + q \<le> K \<and> G \<in> carrier_mat (2 ^ q) (2 ^ q)
       \<and> Quantum.unitary G \<and> U = wg K [w..<w + q] G) in wg_gates K' (map ((!) vs) [w..<w + q]) G)"

lemma relab1_props:
  assumes E: "elementary (2 ^ K) U" and vs: "distinct vs" "\<And>v. v \<in> set vs \<Longrightarrow> v < K'" "length vs = K"
  shows "circuit_mat (2 ^ K') (relab1 K K' vs U) = wg K' vs U"
    "\<forall>V \<in> set (relab1 K K' vs U). elementary (2 ^ K') V" "length (relab1 K K' vs U) \<le> 4 * K' + 1"
proof -
  let ?P = "\<lambda>(w, q, G). q \<in> {1, 2} \<and> w + q \<le> K \<and> G \<in> carrier_mat (2 ^ q) (2 ^ q) \<and> Quantum.unitary G \<and> U = wg K [w..<w + q] G"
  obtain w q G where wqG: "(SOME x. ?P x) = (w, q, G)" by (cases "SOME x. ?P x") auto
  have "\<exists>x. ?P x" using elementary_wg[OF E] by auto
  hence "?P (SOME x. ?P x)" by (rule someI_ex)
  hence P: "q \<in> {1, 2}" "w + q \<le> K" "G \<in> carrier_mat (2 ^ q) (2 ^ q)" "Quantum.unitary G" "U = wg K [w..<w + q] G"
    unfolding wqG by simp_all
  have r: "relab1 K K' vs U = wg_gates K' (map ((!) vs) [w..<w + q]) G" unfolding relab1_def wqG by simp
  let ?ws = "map ((!) vs) [w..<w + q]"
  have d: "distinct ?ws" using vs(1,3) P(2) by (auto simp: distinct_map inj_on_def nth_eq_iff_index_eq)
  have b: "\<And>v. v \<in> set ?ws \<Longrightarrow> v < K'" using vs(2,3) P(2) by auto
  have l: "length ?ws \<in> {1, 2}" using P(1) by simp
  have Gc: "G \<in> carrier_mat (2 ^ length ?ws) (2 ^ length ?ws)" using P(3) by simp
  note W = wg_gates_props[OF d b l Gc P(4)]
  have "wg K' vs U = wg K' ?ws G" unfolding P(5) by (rule wg_wg[OF vs]) (use P(2) in auto)
  thus "circuit_mat (2 ^ K') (relab1 K K' vs U) = wg K' vs U" by (simp only: r W(1))
  show "\<forall>V \<in> set (relab1 K K' vs U). elementary (2 ^ K') V" unfolding r by (rule W(2))
  show "length (relab1 K K' vs U) \<le> 4 * K' + 1" unfolding r by (rule W(3))
qed

definition relab :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "relab K K' vs Us = concat (map (relab1 K K' vs) Us)"

theorem relab_props:
  assumes E: "\<forall>U \<in> set Us. elementary (2 ^ K) U" and vs: "distinct vs" "\<And>v. v \<in> set vs \<Longrightarrow> v < K'" "length vs = K"
  shows "circuit_mat (2 ^ K') (relab K K' vs Us) = wg K' vs (circuit_mat (2 ^ K) Us)"
    "\<forall>V \<in> set (relab K K' vs Us). elementary (2 ^ K') V" "length (relab K K' vs Us) \<le> length Us * (4 * K' + 1)"
proof -
  have "circuit_mat (2 ^ K') (relab K K' vs Us) = wg K' vs (circuit_mat (2 ^ K) Us)
      \<and> (\<forall>V \<in> set (relab K K' vs Us). elementary (2 ^ K') V) \<and> length (relab K K' vs Us) \<le> length Us * (4 * K' + 1)"
    using E
  proof (induction Us)
    case Nil
    have "wg K' vs (1\<^sub>m (2 ^ K)) = 1\<^sub>m (2 ^ K')" using wg_one[of vs K'] vs by simp
    thus ?case by (simp add: relab_def)
  next
    case (Cons U Us)
    have EU: "elementary (2 ^ K) U" and IH: "circuit_mat (2 ^ K') (relab K K' vs Us) = wg K' vs (circuit_mat (2 ^ K) Us)"
      "\<forall>V \<in> set (relab K K' vs Us). elementary (2 ^ K') V" "length (relab K K' vs Us) \<le> length Us * (4 * K' + 1)"
      using Cons by auto
    note R = relab1_props[OF EU vs]
    have e: "relab K K' vs (U # Us) = relab1 K K' vs U @ relab K K' vs Us" by (simp add: relab_def)
    have Uc: "U \<in> carrier_mat (2 ^ length vs) (2 ^ length vs)" using elementary_unitary(1)[OF EU] vs(3) by simp
    have Cc: "circuit_mat (2 ^ K) Us \<in> carrier_mat (2 ^ length vs) (2 ^ length vs)"
      using circuit_mat_carrier[of Us "2 ^ K"] Cons.prems elementary_unitary(1) vs(3) by auto
    have "circuit_mat (2 ^ K') (relab K K' vs (U # Us)) = circuit_mat (2 ^ K') (relab K K' vs Us) * circuit_mat (2 ^ K') (relab1 K K' vs U)"
      unfolding e by (rule circuit_mat_append) (use R(2) IH(2) elementary_unitary(1) in auto)
    also have "\<dots> = wg K' vs (circuit_mat (2 ^ K) Us) * wg K' vs U" by (simp only: IH(1) R(1))
    also have "\<dots> = wg K' vs (circuit_mat (2 ^ K) (U # Us))" using wg_mult[OF vs(1,2) Cc Uc] by simp
    finally show ?case using R(2,3) IH(2,3) e by auto
  qed
  thus "circuit_mat (2 ^ K') (relab K K' vs Us) = wg K' vs (circuit_mat (2 ^ K) Us)"
    "\<forall>V \<in> set (relab K K' vs Us). elementary (2 ^ K') V" "length (relab K K' vs Us) \<le> length Us * (4 * K' + 1)" by auto
qed

end
