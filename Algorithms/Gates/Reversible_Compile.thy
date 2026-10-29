theory Reversible_Compile
  imports Gate_Routing Toffoli_Gates
begin

section \<open>Reversible circuits as elementary gates\<close>

subsection \<open>Permutations of the low wires\<close>

lemma digit_eq:
  fixes r q x b :: nat
  assumes x: "x < b"
  shows "r = q * b + x \<longleftrightarrow> r div b = q \<and> r mod b = x"
proof
  have b: "b \<noteq> 0" using x by simp
  assume "r = q * b + x"
  thus "r div b = q \<and> r mod b = x" using x b by simp
next
  assume "r div b = q \<and> r mod b = x"
  thus "r = q * b + x" using div_mult_mod_eq[of r b] by simp
qed

lemma pmat_cong: "(\<And>t. t < N \<Longrightarrow> f t = g t) \<Longrightarrow> pmat N f = pmat N g"
  by (rule eq_matI) (auto simp: pmat_def)

lemma pmat_low:
  assumes g: "\<And>t. t < b \<Longrightarrow> g t < b" and f: "\<And>c. c < a * b \<Longrightarrow> f c = c div b * b + g (c mod b)"
    and a: "0 < a" and b: "0 < b"
  shows "pmat (a * b) f = 1\<^sub>m a \<Otimes> pmat b g"
proof (rule eq_matI)
  fix r c assume "r < dim_row (1\<^sub>m a \<Otimes> pmat b g)" "c < dim_col (1\<^sub>m a \<Otimes> pmat b g)"
  hence r: "r < a * b" and c: "c < a * b" by simp_all
  have i: "(1\<^sub>m a \<Otimes> pmat b g) $$ (r, c) = 1\<^sub>m a $$ (r div b, c div b) * pmat b g $$ (r mod b, c mod b)"
    using index_tensor_mat[of "1\<^sub>m a" a a "pmat b g" b b r c] r c a b by simp
  have rd: "r div b < a" "c div b < a" using r c b by (simp_all add: div_less_iff_less_mult)
  have gm: "g (c mod b) < b" using g b by simp
  show "pmat (a * b) f $$ (r, c) = (1\<^sub>m a \<Otimes> pmat b g) $$ (r, c)"
    unfolding i using r c rd b digit_eq[OF gm, of r "c div b"] by (simp add: pmat_def f)
qed simp_all

text \<open>A gate on the wires below $w$ acts on the low $w$ bits only.\<close>

lemma bit_mod_div: "bit n i \<longleftrightarrow> (if i < w then bit (n mod 2 ^ w) i else bit (n div 2 ^ w) (i - w))" for n :: nat
  by (simp add: bit_take_bit_iff bit_drop_bit_eq flip: take_bit_eq_mod drop_bit_eq_div)

lemma rg_low:
  assumes ok: "rg_ok w g"
  shows "rg g c = c div 2 ^ w * 2 ^ w + rg g (c mod 2 ^ w)"
proof (rule bit_eqI)
  fix i
  let ?l = "c mod 2 ^ w" and ?h = "c div 2 ^ w"
  have l: "rg g ?l < 2 ^ w" by (rule rg_lt[OF ok]) simp
  have lo: "q < w \<Longrightarrow> bit ?l q \<longleftrightarrow> bit c q" for q by (simp add: bit_take_bit_iff flip: take_bit_eq_mod)
  have act: "active g ?l \<longleftrightarrow> active g c" using ok by (cases g) (simp_all add: lo)
  have tw: "targ g < w" using ok by (cases g) simp_all
  have s: "(?h * 2 ^ w + rg g ?l) mod 2 ^ w = rg g ?l" "(?h * 2 ^ w + rg g ?l) div 2 ^ w = ?h"
    using l by simp_all
  show "bit (rg g c) i \<longleftrightarrow> bit (?h * 2 ^ w + rg g ?l) i"
  proof (cases "i < w")
    case True
    have "bit (?h * 2 ^ w + rg g ?l) i \<longleftrightarrow> bit (rg g ?l) i"
      using bit_mod_div[of "?h * 2 ^ w + rg g ?l" i w] True unfolding s by simp
    also have "\<dots> \<longleftrightarrow> bit (rg g c) i" unfolding bit_rg act using lo[OF True] by (cases "i = targ g") simp_all
    finally show ?thesis by simp
  next
    case False
    have "bit (?h * 2 ^ w + rg g ?l) i \<longleftrightarrow> bit ?h (i - w)"
      using bit_mod_div[of "?h * 2 ^ w + rg g ?l" i w] False unfolding s by simp
    also have "\<dots> \<longleftrightarrow> bit c i" using bit_mod_div[of c i w] False by simp
    also have "\<dots> \<longleftrightarrow> bit (rg g c) i" using tw False by (simp add: bit_rg del: rg.simps)
    finally show ?thesis by simp
  qed
qed

lemma pmat_core:
  assumes ok: "rg_ok w h" and w: "w \<le> K"
  shows "pmat (2 ^ K) (rg h) = 1\<^sub>m (2 ^ (K - w)) \<Otimes> pmat (2 ^ w) (rg h)"
proof -
  have e: "(2::nat) ^ K = 2 ^ (K - w) * 2 ^ w" using w by (simp flip: power_add)
  show ?thesis unfolding e by (rule pmat_low[where g = "rg h"]) (auto intro: rg_lt[OF ok] rg_low[OF ok])
qed

subsection \<open>The three core gates\<close>

lemma pmat_not0: "pmat 2 (rg (NOT 0)) = notm"
  unfolding notm_def by (rule pmat_cong) (auto simp: less_2_cases_iff flip_bit_0)

lemma ctrl_pmat:
  assumes h: "\<And>c t. t < 2 \<Longrightarrow> h c t < 2"
  shows "ctrl_blocks N 2 (\<lambda>c. pmat 2 (h c)) = pmat (N * 2) (\<lambda>r. r div 2 * 2 + h (r div 2) (r mod 2))"
proof (rule eq_matI)
  fix r c assume "r < dim_row (pmat (N * 2) (\<lambda>r. r div 2 * 2 + h (r div 2) (r mod 2)))"
    "c < dim_col (pmat (N * 2) (\<lambda>r. r div 2 * 2 + h (r div 2) (r mod 2)))"
  hence r: "r < N * 2" and c: "c < N * 2" by simp_all
  have hm: "h (c div 2) (c mod 2) < 2" using h by simp
  show "ctrl_blocks N 2 (\<lambda>c. pmat 2 (h c)) $$ (r, c) = pmat (N * 2) (\<lambda>r. r div 2 * 2 + h (r div 2) (r mod 2)) $$ (r, c)"
    using r c digit_eq[OF hm, of r "c div 2"] by (auto simp: ctrl_blocks_index pmat_def)
qed simp_all

lemma pmat_tof: "pmat 8 (rg (TOF 2 1 0)) = tof8"
proof -
  let ?h = "\<lambda>c :: nat. if c = 3 then (\<lambda>t :: nat. 1 - t) else id"
  have "tof8 = ctrl_blocks 4 2 (\<lambda>c. pmat 2 (?h c))"
    unfolding tof8_def notm_def by (rule ctrl_blocks_cong) (simp add: pmat_id)
  also have "\<dots> = pmat (4 * 2) (\<lambda>r. r div 2 * 2 + ?h (r div 2) (r mod 2))" by (rule ctrl_pmat) auto
  also have "\<dots> = pmat 8 (rg (TOF 2 1 0))"
  proof -
    have c8: "t = 0 \<or> t = 1 \<or> t = 2 \<or> t = 3 \<or> t = 4 \<or> t = 5 \<or> t = 6 \<or> t = 7" if "t < 8" for t :: nat
      using that by auto
    have "t div 2 * 2 + ?h (t div 2) (t mod 2) = rg (TOF 2 1 0) t" if "t < 8" for t
      using c8[OF that] by (elim disjE) (simp_all add: bit_iff_odd)
    hence "pmat 8 (\<lambda>r. r div 2 * 2 + ?h (r div 2) (r mod 2)) = pmat 8 (rg (TOF 2 1 0))" by (rule pmat_cong)
    thus ?thesis by simp
  qed
  finally show ?thesis by simp
qed

definition core :: "nat \<Rightarrow> rgate \<Rightarrow> complex Matrix.mat list" where
  "core K h = (if h = NOT 0 then [1\<^sub>m (2 ^ (K - 1)) \<Otimes> notm] else if h = CNOT 1 0 then [cgate K 1 (True, 0)]
     else map (\<lambda>U. 1\<^sub>m (2 ^ (K - 3)) \<Otimes> U) tof_gates)"

lemma notm_unitary: "notm \<in> carrier_mat 2 2" "Quantum.unitary notm"
  unfolding notm_def by (simp, rule pmat_unitary_invol) auto

lemma core_props:
  assumes h: "h \<in> {NOT 0, CNOT 1 0, TOF 2 1 0}" and ok: "rg_ok K h"
  shows "circuit_mat (2 ^ K) (core K h) = pmat (2 ^ K) (rg h)"
    "\<forall>U \<in> set (core K h). elementary (2 ^ K) U" "length (core K h) \<le> 7"
proof -
  consider "h = NOT 0" | "h = CNOT 1 0" | "h = TOF 2 1 0" using h by blast
  hence "circuit_mat (2 ^ K) (core K h) = pmat (2 ^ K) (rg h) \<and> (\<forall>U \<in> set (core K h). elementary (2 ^ K) U)"
  proof cases
    case 1
    have K: "2 ^ K = 2 ^ (K - 1) * (2::nat)" using ok 1 by (cases K) simp_all
    have g: "gate 1 notm" using notm_unitary by (simp add: gate_def square_mat.simps)
    have e: "elementary (2 ^ (K - 1) * 2) (1\<^sub>m (2 ^ (K - 1)) \<Otimes> notm)"
      using elementary_left[OF elementary_gate[OF g], of "2 ^ (K - 1)"] by simp
    have c: "1\<^sub>m (2 ^ (K - 1)) \<Otimes> notm \<in> carrier_mat (2 ^ K) (2 ^ K)" unfolding K using notm_unitary(1) by simp
    have p: "pmat (2 ^ K) (rg h) = 1\<^sub>m (2 ^ (K - 1)) \<Otimes> notm"
      using pmat_core[of 1 h K] ok 1 by (simp add: pmat_not0)
    have s: "circuit_mat (2 ^ K) (core K h) = 1\<^sub>m (2 ^ (K - 1)) \<Otimes> notm"
      unfolding 1 core_def using left_mult_one_mat[OF c] by simp
    have "elementary (2 ^ K) (1\<^sub>m (2 ^ (K - 1)) \<Otimes> notm)" unfolding K by (rule e)
    thus ?thesis using 1 s p by (simp add: core_def)
  next
    case 2
    have K: "0 + 2 \<le> K" using ok 2 by simp
    have f: "opf (True, 0) = rg h" using 2 by (intro ext) (simp add: cx_op)
    have p: "pmat (2 ^ K) (opf (True, 0)) = pmat (2 ^ K) (rg h)" by (simp only: f)
    have "cgate K 1 (True, 0) = pmat (2 ^ K) (rg h)"
      unfolding cgate_def p by (simp add: right_tensor_id[OF pmat_carrier, unfolded One_nat_def])
    moreover have "elementary (2 ^ K) (cgate K 1 (True, 0))" using cgate_elementary[OF K, of 1 True] by simp
    ultimately show ?thesis using 2 by (simp add: core_def)
  next
    case 3
    have k3: "K = (K - 3) + 3" using ok 3 by simp
    have K: "2 ^ K = 2 ^ (K - 3) * (8::nat)" by (subst (1) k3) (simp add: power_add)
    have c8: "\<And>U. U \<in> set tof_gates \<Longrightarrow> U \<in> carrier_mat 8 8" by (rule gates8_carrier)
    have "circuit_mat (2 ^ (K - 3) * 8) (map (\<lambda>U. 1\<^sub>m (2 ^ (K - 3)) \<Otimes> U) tof_gates) = 1\<^sub>m (2 ^ (K - 3)) \<Otimes> tof8"
      using circuit_mat_tensor_left[where Us = tof_gates and K = 8 and m = "2 ^ (K - 3)", OF c8] by (simp add: tof_circuit)
    moreover have "pmat (2 ^ K) (rg h) = 1\<^sub>m (2 ^ (K - 3)) \<Otimes> tof8"
      using pmat_core[of 3 h K] ok 3 by (simp add: pmat_tof[unfolded One_nat_def])
    moreover have "\<forall>U \<in> set (map (\<lambda>U. 1\<^sub>m (2 ^ (K - 3)) \<Otimes> U) tof_gates). elementary (2 ^ (K - 3) * 8) U"
      using elementary_left[OF tof_gates_elementary] by auto
    ultimately show ?thesis using 3 K by (simp add: core_def)
  qed
  thus "circuit_mat (2 ^ K) (core K h) = pmat (2 ^ K) (rg h)" "\<forall>U \<in> set (core K h). elementary (2 ^ K) U" by simp_all
  show "length (core K h) \<le> 7" using h by (auto simp: core_def length_tof_gates)
qed

subsection \<open>Compiling a circuit\<close>

lemma three_lt: "a \<noteq> b \<Longrightarrow> a \<noteq> p \<Longrightarrow> b \<noteq> p \<Longrightarrow> a < K \<Longrightarrow> b < K \<Longrightarrow> p < K \<Longrightarrow> 2 < (K :: nat)"
  by presburger

lemma route_ok: "rg_ok K g \<Longrightarrow> rg_ok K (snd (gate_route g))"
  by (cases g) (auto dest: three_lt)

definition compile1 :: "nat \<Rightarrow> rgate \<Rightarrow> complex Matrix.mat list" where
  "compile1 K g = map (cgate K 1) (swops (fst (gate_route g))) @ core K (snd (gate_route g))
     @ map (cgate K 1) (swops (rev (fst (gate_route g))))"

definition compile :: "nat \<Rightarrow> rgate list \<Rightarrow> complex Matrix.mat list" where
  "compile K rs = concat (map (compile1 K) rs)"

lemma elementary_carrier: "elementary K U \<Longrightarrow> U \<in> carrier_mat K K" by (rule elementary_unitary(1))

lemma swops_circuit:
  assumes js: "\<And>j. j \<in> set js \<Longrightarrow> j + 2 \<le> K"
  shows "circuit_mat (2 ^ K) (map (cgate K 1) (swops js)) = pmat (2 ^ K) (apply_ops (swops js))"
    "\<forall>U \<in> set (map (cgate K 1) (swops js)). elementary (2 ^ K) U"
proof -
  have "circuit_mat (2 ^ K * 1) (map (cgate K 1) (swops js)) = pmat (2 ^ K) (apply_ops (swops js)) \<Otimes> 1\<^sub>m 1"
    by (rule circuit_cgates) (use js in auto)
  thus "circuit_mat (2 ^ K) (map (cgate K 1) (swops js)) = pmat (2 ^ K) (apply_ops (swops js))"
    by (simp add: right_tensor_id[OF pmat_carrier, unfolded One_nat_def])
  show "\<forall>U \<in> set (map (cgate K 1) (swops js)). elementary (2 ^ K) U"
    using cgate_elementary[of _ K 1] js by auto
qed

theorem compile1_props:
  assumes ok: "rg_ok K g"
  shows "circuit_mat (2 ^ K) (compile1 K g) = pmat (2 ^ K) (rg g)"
    "\<forall>U \<in> set (compile1 K g). elementary (2 ^ K) U" "length (compile1 K g) \<le> 6 * K + 7"
proof -
  obtain js h where r: "gate_route g = (js, h)" by (cases "gate_route g")
  have rj: "\<And>j. j \<in> set js \<Longrightarrow> j + 2 \<le> K" using route_range[OF ok r] .
  have rj': "\<And>j. j \<in> set (rev js) \<Longrightarrow> j + 2 \<le> K" using rj by simp
  have hok: "rg_ok K h" using route_ok[OF ok] r by simp
  have hc: "h \<in> {NOT 0, CNOT 1 0, TOF 2 1 0}" using route_core[of g] r by simp
  note A = swops_circuit[OF rj] and C = swops_circuit[OF rj'] and B = core_props[OF hc hok]
  have el: "\<forall>U \<in> set (compile1 K g). elementary (2 ^ K) U"
    using A(2) B(2) C(2) r by (auto simp: compile1_def)
  thus "\<forall>U \<in> set (compile1 K g). elementary (2 ^ K) U" .
  have car: "\<And>Us. \<forall>U \<in> set Us. elementary (2 ^ K) U \<Longrightarrow> (\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ K) (2 ^ K))"
    using elementary_carrier by blast
  have lt1: "\<And>t. t < 2 ^ K \<Longrightarrow> apply_ops (swops js) t < 2 ^ K"
    by (rule apply_ops_lt) (use rj in auto)
  have lt2: "\<And>t. t < 2 ^ K \<Longrightarrow> rg h t < 2 ^ K" by (rule rg_lt[OF hok])
  have "circuit_mat (2 ^ K) (compile1 K g)
      = (pmat (2 ^ K) (apply_ops (swops (rev js))) * pmat (2 ^ K) (rg h)) * pmat (2 ^ K) (apply_ops (swops js))"
  proof -
    let ?A = "map (cgate K 1) (swops js)" and ?B = "core K h" and ?C = "map (cgate K 1) (swops (rev js))"
    have e1: "circuit_mat (2 ^ K) (?A @ ?B @ ?C) = circuit_mat (2 ^ K) (?B @ ?C) * circuit_mat (2 ^ K) ?A"
      by (rule circuit_mat_append) (use A(2) B(2) C(2) elementary_carrier in auto)
    have e2: "circuit_mat (2 ^ K) (?B @ ?C) = circuit_mat (2 ^ K) ?C * circuit_mat (2 ^ K) ?B"
      by (rule circuit_mat_append) (use B(2) C(2) elementary_carrier in auto)
    have "circuit_mat (2 ^ K) (compile1 K g) = circuit_mat (2 ^ K) ?C * circuit_mat (2 ^ K) ?B * circuit_mat (2 ^ K) ?A"
      unfolding compile1_def r fst_conv snd_conv e1 e2 ..
    thus ?thesis by (simp only: A(1) B(1) C(1))
  qed
  also have "\<dots> = pmat (2 ^ K) (rg g)"
    by (simp add: pmat_mult lt1 lt2 comp_def route_correct[OF ok r])
  finally show "circuit_mat (2 ^ K) (compile1 K g) = pmat (2 ^ K) (rg g)" .
  show "length (compile1 K g) \<le> 6 * K + 7"
    using route_length[OF ok r] B(3) r by (simp add: compile1_def)
qed

theorem compile_props:
  assumes ok: "\<forall>g \<in> set rs. rg_ok K g"
  shows "circuit_mat (2 ^ K) (compile K rs) = pmat (2 ^ K) (rcirc rs)"
    "\<forall>U \<in> set (compile K rs). elementary (2 ^ K) U" "length (compile K rs) \<le> length rs * (6 * K + 7)"
proof -
  have car: "\<And>Us. \<forall>U \<in> set Us. elementary (2 ^ K) U \<Longrightarrow> (\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ K) (2 ^ K))"
    using elementary_carrier by blast
  have "circuit_mat (2 ^ K) (compile K rs) = pmat (2 ^ K) (rcirc rs) \<and> (\<forall>U \<in> set (compile K rs). elementary (2 ^ K) U)
      \<and> length (compile K rs) \<le> length rs * (6 * K + 7)"
    using ok
  proof (induction rs)
    case Nil
    show ?case by (simp add: compile_def pmat_id[unfolded id_def, symmetric] rcirc_def)
  next
    case (Cons g rs)
    have okg: "rg_ok K g" using Cons.prems by simp
    note IH = Cons.IH[OF conjunct2[OF Cons.prems[unfolded list.set ball_simps]]] and G = compile1_props[OF okg]
    have e: "compile K (g # rs) = compile1 K g @ compile K rs" by (simp add: compile_def)
    have rc: "rcirc (g # rs) = (\<lambda>x. rcirc rs (rg g x))" by (rule ext) simp
    have ap: "circuit_mat (2 ^ K) (compile1 K g @ compile K rs) = circuit_mat (2 ^ K) (compile K rs) * circuit_mat (2 ^ K) (compile1 K g)"
      by (rule circuit_mat_append) (use G(2) IH elementary_carrier in auto)
    have "circuit_mat (2 ^ K) (compile K (g # rs)) = pmat (2 ^ K) (rcirc rs) * pmat (2 ^ K) (rg g)"
      unfolding e ap G(1) IH[THEN conjunct1] ..
    also have "\<dots> = pmat (2 ^ K) (rcirc (g # rs))" by (simp add: pmat_mult rg_lt[OF okg] comp_def rc)
    finally show ?case using IH G e rc by auto
  qed
  thus "circuit_mat (2 ^ K) (compile K rs) = pmat (2 ^ K) (rcirc rs)" "\<forall>U \<in> set (compile K rs). elementary (2 ^ K) U"
    "length (compile K rs) \<le> length rs * (6 * K + 7)" by simp_all
qed

end
