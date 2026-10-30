theory Controlled_Laplacian
  imports Wire_Placement Shifted_Laplacian
begin

section \<open>The controlled Laplacian step\<close>

subsection \<open>Controlled gates\<close>

text \<open>\<open>ctl B\<close> applies $B$ when the new top wire is set.\<close>

definition ctl :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "ctl B = ctrl_blocks 2 (dim_row B) (\<lambda>i. if i = 1 then B else 1\<^sub>m (dim_row B))"

lemma ctl_carrier: "B \<in> carrier_mat n n \<Longrightarrow> ctl B \<in> carrier_mat (2 * n) (2 * n)"
  by (simp add: ctl_def)

lemma ctl_alt:
  assumes "B \<in> carrier_mat n n"
  shows "ctl B = ctrl_blocks 2 n (\<lambda>i. if i = 1 then B else 1\<^sub>m n)"
  unfolding ctl_def carrier_matD(1)[OF assms] ..

lemma ctl_mult:
  assumes B: "B \<in> carrier_mat n n" and B2: "B2 \<in> carrier_mat n n"
  shows "ctl B * ctl B2 = ctl (B * B2)"
proof -
  have "ctl B * ctl B2 = ctrl_blocks 2 n (\<lambda>i. (if i = 1 then B else 1\<^sub>m n) * (if i = 1 then B2 else 1\<^sub>m n))"
    unfolding ctl_alt[OF B] ctl_alt[OF B2] using B B2 by (simp add: ctrl_blocks_mult)
  also have "\<dots> = ctl (B * B2)" unfolding ctl_alt[OF mult_carrier_mat[OF B B2]] using B B2 by (intro ctrl_blocks_cong) simp
  finally show ?thesis .
qed

lemma ctl_conj:
  assumes P: "P \<in> carrier_mat n n" and Q: "Q \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
    and PQ: "P * Q = 1\<^sub>m n" and n: "0 < n"
  shows "(1\<^sub>m 2 \<Otimes> P) * ctl B * (1\<^sub>m 2 \<Otimes> Q) = ctl (P * B * Q)"
proof -
  have "(1\<^sub>m 2 \<Otimes> P) * ctl B * (1\<^sub>m 2 \<Otimes> Q)
      = ctrl_blocks 2 n (\<lambda>_. P) * ctrl_blocks 2 n (\<lambda>i. if i = 1 then B else 1\<^sub>m n) * ctrl_blocks 2 n (\<lambda>_. Q)"
    unfolding ctl_alt[OF B] ctrl_const[OF P n] ctrl_const[OF Q n] ..
  also have "\<dots> = ctrl_blocks 2 n (\<lambda>i. P * (if i = 1 then B else 1\<^sub>m n) * Q)"
    using P Q B by (simp add: ctrl_blocks_mult)
  also have "\<dots> = ctl (P * B * Q)" unfolding ctl_alt[OF mult_carrier_mat[OF mult_carrier_mat[OF P B] Q]]
    using P Q B PQ by (intro ctrl_blocks_cong) simp
  finally show ?thesis .
qed

lemma ctl_unitary: "B \<in> carrier_mat n n \<Longrightarrow> Quantum.unitary B \<Longrightarrow> Quantum.unitary (ctl B)"
  unfolding ctl_def by (rule ctrl_blocks_unitary) auto

lemma ctl_pow:
  assumes B: "B \<in> carrier_mat n n"
  shows "ctl (B ^\<^sub>m r) = ctl B ^\<^sub>m r"
proof (induction r)
  case 0
  have "ctl (1\<^sub>m n) = 1\<^sub>m (2 * n)" unfolding ctl_alt[OF one_carrier_mat] using ctrl_blocks_one[of 2 n] by simp
  moreover have "dim_row B = n" "dim_row (ctl B) = 2 * n" using B ctl_carrier[OF B] by auto
  ultimately show ?case by simp
next
  case (Suc r)
  have "ctl (B ^\<^sub>m Suc r) = ctl (B ^\<^sub>m r) * ctl B" using ctl_mult[OF pow_carrier_mat[OF B, of r] B] by simp
  thus ?case using Suc.IH by simp
qed

subsection \<open>Controlled wire gates\<close>

lemma dig_upt0: "dig [0..<w] x = x mod 2 ^ w"
  by (rule bit_eqI) (auto simp: bit_dig simp flip: take_bit_eq_mod simp add: bit_take_bit_iff)

lemma dig_single: "dig [n] x = of_bool (bit x n)" by simp

lemma mod_eq_dig:
  assumes ws: "\<And>w. w \<in> set ws \<Longrightarrow> w < n"
  shows "x mod 2 ^ n = y mod 2 ^ n \<longleftrightarrow> (\<forall>i<n. i \<notin> set ws \<longrightarrow> bit x i = bit y i) \<and> dig ws x = dig ws y"
proof
  assume e: "x mod 2 ^ n = y mod 2 ^ n"
  hence b: "\<forall>i<n. bit x i = bit y i" by (simp add: mod_eq_bits)
  have "dig ws x = dig ws y" by (rule bit_eqI) (use b ws in \<open>auto simp: bit_dig\<close>)
  thus "(\<forall>i<n. i \<notin> set ws \<longrightarrow> bit x i = bit y i) \<and> dig ws x = dig ws y" using b by simp
next
  assume h: "(\<forall>i<n. i \<notin> set ws \<longrightarrow> bit x i = bit y i) \<and> dig ws x = dig ws y"
  have "\<forall>i<n. bit x i = bit y i"
  proof (intro allI impI)
    fix i assume i: "i < n"
    show "bit x i = bit y i"
    proof (cases "i \<in> set ws")
      case True
      then obtain l where l: "l < length ws" "ws ! l = i" by (auto simp: in_set_conv_nth)
      have "bit (dig ws x) l = bit (dig ws y) l" using h by simp
      thus ?thesis using l by (simp add: bit_dig)
    qed (use h i in simp)
  qed
  thus "x mod 2 ^ n = y mod 2 ^ n" by (simp add: mod_eq_bits)
qed

lemma dig_mod: "(\<And>w. w \<in> set ws \<Longrightarrow> w < n) \<Longrightarrow> dig ws (x mod 2 ^ n) = dig ws x"
  by (rule bit_eqI) (auto simp: bit_dig simp flip: take_bit_eq_mod simp add: bit_take_bit_iff)

lemma div_pow_bit: "x < 2 * 2 ^ n \<Longrightarrow> x div 2 ^ n = of_bool (bit x n)" for x :: nat
proof -
  assume x: "x < 2 * 2 ^ n"
  have "x div 2 ^ n < 2" using x by (simp add: div_less_iff_less_mult ac_simps)
  moreover have "odd (x div 2 ^ n) \<longleftrightarrow> bit x n" by (simp add: bit_iff_odd)
  ultimately show ?thesis by (cases "bit x n") (auto simp: less_2_cases_iff)
qed

theorem wg_ctl:
  assumes ws: "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < n" and Q: "Q \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)"
  shows "wg (Suc n) (ws @ [n]) (ctl Q) = ctl (wg n ws Q)"
proof (rule eq_matI)
  let ?q = "length ws"
  fix x y assume "x < dim_row (ctl (wg n ws Q))" "y < dim_col (ctl (wg n ws Q))"
  hence x: "x < 2 * 2 ^ n" and y: "y < 2 * 2 ^ n" by (simp_all add: ctl_def)
  have x': "x < 2 ^ Suc n" and y': "y < 2 ^ Suc n" using x y by simp_all
  have du: "dig (ws @ [n]) z = dig ws z + 2 ^ ?q * of_bool (bit z n)" for z by (simp add: dig_append)
  have ud: "dig (ws @ [n]) z div 2 ^ ?q = of_bool (bit z n)" "dig (ws @ [n]) z mod 2 ^ ?q = dig ws z" for z
    unfolding du using dig_lt[of ws z] by simp_all
  have dl: "dig (ws @ [n]) z < 2 * 2 ^ ?q" for z using dig_lt[of "ws @ [n]" z] by simp
  have L: "wg (Suc n) (ws @ [n]) (ctl Q) $$ (x, y) = (if \<forall>i<Suc n. i \<notin> set (ws @ [n]) \<longrightarrow> bit x i = bit y i
      then (if bit x n = bit y n then (if bit x n then Q else 1\<^sub>m (2 ^ ?q)) $$ (dig ws x, dig ws y) else 0) else 0)"
    unfolding wg_index[OF x' y'] ctl_alt[OF Q] using Q dl[of x] dl[of y] by (auto simp: ctrl_blocks_index ud)
  have R: "ctl (wg n ws Q) $$ (x, y) = (if bit x n = bit y n
      then (if bit x n then wg n ws Q else 1\<^sub>m (2 ^ n)) $$ (x mod 2 ^ n, y mod 2 ^ n) else 0)"
    unfolding ctl_alt[OF wg_carrier] using x y by (simp add: ctrl_blocks_index div_pow_bit)
  have c: "(\<forall>i<Suc n. i \<notin> set (ws @ [n]) \<longrightarrow> bit x i = bit y i) \<longleftrightarrow> (\<forall>i<n. i \<notin> set ws \<longrightarrow> bit x i = bit y i)"
    using ws(2) by (auto simp: less_Suc_eq)
  have c': "(\<forall>i<n. i \<notin> set ws \<longrightarrow> bit (x mod 2 ^ n) i = bit (y mod 2 ^ n) i) \<longleftrightarrow> (\<forall>i<n. i \<notin> set ws \<longrightarrow> bit x i = bit y i)"
    by (auto simp flip: take_bit_eq_mod simp: bit_take_bit_iff)
  have xm: "x mod 2 ^ n < 2 ^ n" "y mod 2 ^ n < 2 ^ n" by simp_all
  show "wg (Suc n) (ws @ [n]) (ctl Q) $$ (x, y) = ctl (wg n ws Q) $$ (x, y)"
    unfolding L R c using Q dig_lt[of ws] mod_eq_dig[of ws n x y, OF ws(2)]
    by (auto simp: wg_index[OF xm] c' dig_mod[OF ws(2)])
qed (use Q in \<open>simp_all add: ctl_def\<close>)

theorem ctrl_bit_wg:
  assumes j: "j < k" and G: "G \<in> carrier_mat (2 ^ w) (2 ^ w)"
  shows "ctrl_bit (2 ^ k) (2 ^ w) j G = wg (w + k) ([0..<w] @ [w + j]) (ctl G)"
proof (rule eq_matI)
  fix x y assume "x < dim_row (wg (w + k) ([0..<w] @ [w + j]) (ctl G))" "y < dim_col (wg (w + k) ([0..<w] @ [w + j]) (ctl G))"
  hence x: "x < 2 ^ (w + k)" and y: "y < 2 ^ (w + k)" by simp_all
  have x': "x < 2 ^ k * 2 ^ w" and y': "y < 2 ^ k * 2 ^ w" using x y by (simp_all add: power_add ac_simps)
  have du: "dig ([0..<w] @ [w + j]) z = z mod 2 ^ w + 2 ^ w * of_bool (bit z (w + j))" for z
    by (simp add: dig_append dig_upt0)
  have ud: "dig ([0..<w] @ [w + j]) z div 2 ^ w = of_bool (bit z (w + j))"
    "dig ([0..<w] @ [w + j]) z mod 2 ^ w = z mod 2 ^ w" for z
    unfolding du by simp_all
  have dl: "dig ([0..<w] @ [w + j]) z < 2 * 2 ^ w" for z using dig_lt[of "[0..<w] @ [w + j]" z] by simp
  have od: "odd (z div 2 ^ w div 2 ^ j) \<longleftrightarrow> bit z (w + j)" for z :: nat
    by (simp add: bit_iff_odd[symmetric] bit_div_pow)
  have dv: "x div 2 ^ w = y div 2 ^ w \<longleftrightarrow>
      (\<forall>i<w + k. i \<notin> set ([0..<w] @ [w + j]) \<longrightarrow> bit x i = bit y i) \<and> bit x (w + j) = bit y (w + j)"
  proof -
    have "x div 2 ^ w = y div 2 ^ w \<longleftrightarrow> (\<forall>i\<ge>w. bit x i = bit y i)" by (rule div_eq_bits)
    also have "\<dots> \<longleftrightarrow> (\<forall>i. w \<le> i \<and> i < w + k \<longrightarrow> bit x i = bit y i)"
    proof
      assume h: "\<forall>i. w \<le> i \<and> i < w + k \<longrightarrow> bit x i = bit y i"
      show "\<forall>i\<ge>w. bit x i = bit y i"
      proof (intro allI impI)
        fix i assume i: "w \<le> i"
        show "bit x i = bit y i"
        proof (cases "i < w + k")
          case False
          thus ?thesis using bit_above[OF x, of i] bit_above[OF y, of i] by simp
        qed (use h i in simp)
      qed
    qed simp
    also have "\<dots> \<longleftrightarrow> (\<forall>i<w + k. i \<notin> set ([0..<w] @ [w + j]) \<longrightarrow> bit x i = bit y i) \<and> bit x (w + j) = bit y (w + j)"
      using j by auto
    finally show ?thesis .
  qed
  have L0: "ctrl_bit (2 ^ k) (2 ^ w) j G $$ (x, y) = (if x div 2 ^ w = y div 2 ^ w
      then (if odd (x div 2 ^ w div 2 ^ j) then G else 1\<^sub>m (2 ^ w)) $$ (x mod 2 ^ w, y mod 2 ^ w) else 0)"
    unfolding ctrl_bit_def using x' y' ctrl_blocks_index[OF x' y'] by simp
  have L: "ctrl_bit (2 ^ k) (2 ^ w) j G $$ (x, y) = (if x div 2 ^ w = y div 2 ^ w
      then (if bit x (w + j) then G else 1\<^sub>m (2 ^ w)) $$ (x mod 2 ^ w, y mod 2 ^ w) else 0)"
    using L0 unfolding od .
  show "ctrl_bit (2 ^ k) (2 ^ w) j G $$ (x, y) = wg (w + k) ([0..<w] @ [w + j]) (ctl G) $$ (x, y)"
    unfolding L wg_index[OF x y] ctl_alt[OF G] dv using G dl[of x] dl[of y] by (auto simp: ctrl_blocks_index ud)
qed (simp_all add: power_add ac_simps)

lemma stands_for_one: "G \<in> carrier_mat N N \<Longrightarrow> stands_for 1 N G G"
  using stands_for_iff[of G 1 N G] by simp

corollary stands_for_wg_plain:
  assumes ws: "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < Kr" and Q: "Q \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)"
  shows "stands_for (2 ^ a) (2 ^ Kr) (wg (Kr + a) ws Q) (wg Kr ws Q)"
proof -
  have "stands_for (2 ^ 0) (2 ^ length ws) Q Q" using stands_for_one[OF Q] by simp
  from stands_for_wg[OF this ws(1)] show ?thesis using ws(2) by simp
qed

subsection \<open>Phases\<close>

definition gph1 :: "real \<Rightarrow> complex Matrix.mat" where "gph1 t = cis t \<cdot>\<^sub>m 1\<^sub>m 1"

lemma gph1_carrier [simp]: "gph1 t \<in> carrier_mat 1 1" by (simp add: gph1_def)

lemma gph1_unitary: "Quantum.unitary (gph1 t)"
proof -
  have d: "(gph1 t)\<^sup>\<dagger> = cis (- t) \<cdot>\<^sub>m 1\<^sub>m 1"
    by (rule eq_matI) (auto simp: gph1_def dagger_def cis_cnj)
  have "cis (- t) * cis t = 1" "cis t * cis (- t) = 1" by (simp_all add: cis_mult)
  thus ?thesis unfolding Quantum.unitary_def d by (auto simp: gph1_def intro!: eq_matI simp: scalar_prod_def)
qed

lemma wg_scalar:
  assumes ws: "\<And>w. w \<in> set ws \<Longrightarrow> w < K"
  shows "wg K ws (z \<cdot>\<^sub>m 1\<^sub>m (2 ^ length ws)) = z \<cdot>\<^sub>m 1\<^sub>m (2 ^ K)"
proof -
  have "wg K ws (z \<cdot>\<^sub>m 1\<^sub>m (2 ^ length ws)) = z \<cdot>\<^sub>m wg K ws (1\<^sub>m (2 ^ length ws))"
    by (rule eq_matI) (auto simp: wg_index dig_lt)
  thus ?thesis using wg_one[OF ws] by simp
qed

lemma qw_gph: "0 < m \<Longrightarrow> qw m 0 (gph t) = cis t \<cdot>\<^sub>m 1\<^sub>m (2 ^ m)"
  using qw_wg[of 0 m "gph t"] wg_scalar[of "[0]" m "cis t"] by (simp add: gph_def)

subsection \<open>The step on the HHL register\<close>

text \<open>Register wires: the flag $0$, the system $1, \dots, m$, the clock $m+1, \dots, m+k$; the
ancillas above.  The Laplacian's own wires (system, then its $m$ ancillas) sit at \<open>lap_vs m k\<close>.\<close>

definition lap_vs :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "lap_vs m k = [1..<Suc m] @ [Suc (m + k)..<Suc (m + k) + m]"

lemma lap_vs:
  assumes a: "m \<le> a"
  shows "distinct (lap_vs m k)" "length (lap_vs m k) = m + m" "\<And>v. v \<in> set (lap_vs m k) \<Longrightarrow> v < Suc (m + k) + a"
    "take m (lap_vs m k) = [1..<Suc m]" "\<And>l. l < m \<Longrightarrow> lap_vs m k ! l < Suc (m + k)"
    "\<And>l. l < m \<Longrightarrow> Suc (m + k) \<le> lap_vs m k ! (m + l) \<and> lap_vs m k ! (m + l) < Suc (m + k) + a"
  using a by (auto simp: lap_vs_def nth_append)

lemma incr_stands:
  assumes m: "0 < m"
  shows "stands_for (2 ^ m) (2 ^ m) (pmat (2 ^ (m + m)) (rcirc (incr_gates m m))) (pmat (2 ^ m) (inc_f (2 ^ m)))"
    "stands_for (2 ^ m) (2 ^ m) (pmat (2 ^ (m + m)) (rcirc (rev (incr_gates m m)))) (pmat (2 ^ m) (dec_f (2 ^ m)))"
proof -
  let ?n = "2 ^ m :: nat" and ?g = "incr_gates m m"
  have n0: "0 < ?n" by simp
  have KK: "(2::nat) ^ (m + m) = ?n * ?n" by (simp add: power_add)
  have ok: "\<forall>g \<in> set ?g. rg_ok (2 * m) g" by (rule incr_rg_ok) simp
  have inc: "rcirc ?g z = inc_f ?n z" if "z < ?n" for z using incr_rcirc[OF that] by (simp add: inc_f_def)
  have dec: "rcirc (rev ?g) z = dec_f ?n z" if z: "z < ?n" for z
  proof -
    have dz: "dec_f ?n z < ?n" by (rule inc_dec_lt(2)[OF n0])
    have "inc_f ?n (dec_f ?n z) = z" using z by (cases z) (simp_all add: inc_f_def dec_f_def)
    hence "rcirc ?g (dec_f ?n z) = z" using inc[OF dz] by simp
    hence "rcirc (rev ?g) z = rcirc (rev ?g) (rcirc ?g (dec_f ?n z))" by simp
    also have "\<dots> = dec_f ?n z" by (rule rcirc_rev[OF ok])
    finally show ?thesis .
  qed
  show "stands_for ?n ?n (pmat (2 ^ (m + m)) (rcirc ?g)) (pmat ?n (inc_f ?n))"
    unfolding KK by (rule stands_for_pmat) (simp_all add: inc inc_dec_lt)
  show "stands_for ?n ?n (pmat (2 ^ (m + m)) (rcirc (rev ?g))) (pmat ?n (dec_f ?n))"
    unfolding KK by (rule stands_for_pmat) (simp_all add: dec inc_dec_lt)
qed

theorem ctrl_lap_reg:
  assumes m: "2 \<le> m" and j: "j < k" and mu: "0 \<le> \<mu>"
  shows "wg (Suc (m + k)) [Suc (m + j)] (ctl (gph1 ((2 + \<mu>) * d))) * wg (Suc (m + k)) [1, Suc (m + j)] (ctl (xrot d))
      * wg (Suc (m + k)) [1..<Suc m] (pmat (2 ^ m) (inc_f (2 ^ m))) * wg (Suc (m + k)) [1, Suc (m + j)] (ctl (xrot d))
      * wg (Suc (m + k)) [1..<Suc m] (pmat (2 ^ m) (dec_f (2 ^ m)))
    = ctrl_bit (2 ^ k) (2 ^ m * 2) j (evolution_product (2 ^ m) d (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m))) \<Otimes> 1\<^sub>m 2)"
proof -
  let ?R = "Suc (m + k)" and ?c = "Suc (m + j)" and ?n = "2 ^ m :: nat"
  let ?Dc = "[1..<Suc m] @ [Suc (m + j)]"
  let ?A = "qw m 0 (xrot d)" and ?B = "qw m 0 (gph ((2 + \<mu>) * d))"
  let ?P = "pmat ?n (inc_f ?n)" and ?Q = "pmat ?n (dec_f ?n)"
  let ?E = "evolution_product ?n d (sparse_parts ?n (slap ?n \<mu>) 2 (lp ?n))"
  note n = pow_facts[OF m]
  have Dd: "distinct ?Dc" and DR: "\<And>v. v \<in> set ?Dc \<Longrightarrow> v < ?R" and Dl: "length ?Dc = Suc m" using j by auto
  have Dn: "\<And>i. i < m \<Longrightarrow> ?Dc ! i = Suc i" "?Dc ! m = ?c" by (simp_all add: nth_append del: upt_Suc)
  have Ac: "?A \<in> carrier_mat ?n ?n" and Bc: "?B \<in> carrier_mat ?n ?n"
    by (rule qw_carrier, simp, use n(3) in simp)+
  have Pc: "?P \<in> carrier_mat ?n ?n" and Qc: "?Q \<in> carrier_mat ?n ?n" by simp_all
  have two: "(2::nat) ^ length ?Dc = 2 * ?n" using Dl by simp
  have lift: "wg ?R [1..<Suc m] M = wg ?R ?Dc (1\<^sub>m 2 \<Otimes> M)" if M: "M \<in> carrier_mat ?n ?n" for M
  proof -
    have t: "1\<^sub>m (2 ^ 1) \<Otimes> (M \<Otimes> 1\<^sub>m (2 ^ 0)) = wg (1 + m + 0) [0..<0 + m] M" by (rule tensor_wg[OF M])
    have "M \<Otimes> 1\<^sub>m 1 = M" by (rule right_tensor_id[OF M])
    hence t': "1\<^sub>m 2 \<Otimes> M = wg (Suc m) [0..<m] M" using t by simp
    have mp: "map ((!) ?Dc) [0..<m] = [1..<Suc m]" by (rule nth_equalityI) (simp_all add: nth_append del: upt_Suc)
    have w: "wg ?R ?Dc (wg (Suc m) [0..<m] M) = wg ?R (map ((!) ?Dc) [0..<m]) M" by (rule wg_wg[OF Dd DR Dl]) auto
    show ?thesis unfolding t' w mp ..
  qed
  have liftX: "wg ?R [1, ?c] (ctl (xrot d)) = wg ?R ?Dc (ctl ?A)"
  proof -
    have "wg (Suc m) ([0] @ [m]) (ctl (xrot d)) = ctl (wg m [0] (xrot d))"
      by (rule wg_ctl) (use n(3) in simp_all)
    hence e: "wg (Suc m) [0, m] (ctl (xrot d)) = ctl ?A" using qw_wg[of 0 m "xrot d"] n(3) by simp
    have mp: "map ((!) ?Dc) [0, m] = [1, ?c]" using Dn(1)[of 0] Dn(2) n(3) by simp
    have w: "wg ?R ?Dc (wg (Suc m) [0, m] (ctl (xrot d))) = wg ?R (map ((!) ?Dc) [0, m]) (ctl (xrot d))"
      by (rule wg_wg[OF Dd DR Dl]) auto
    show ?thesis using w[unfolded e mp] by (rule sym)
  qed
  have liftB: "wg ?R [?c] (ctl (gph1 ((2 + \<mu>) * d))) = wg ?R ?Dc (ctl ?B)"
  proof -
    have "wg (Suc m) ([] @ [m]) (ctl (gph1 ((2 + \<mu>) * d))) = ctl (wg m [] (gph1 ((2 + \<mu>) * d)))" by (rule wg_ctl) (simp_all add: gph1_carrier[unfolded One_nat_def])
    moreover have "wg m [] (gph1 ((2 + \<mu>) * d)) = ?B"
      using wg_scalar[of "[]" m "cis ((2 + \<mu>) * d)"] qw_gph[OF n(3)] by (simp add: gph1_def)
    ultimately have e: "wg (Suc m) [m] (ctl (gph1 ((2 + \<mu>) * d))) = ctl ?B" by simp
    have mp: "map ((!) ?Dc) [m] = [?c]" using Dn(2) by simp
    have w: "wg ?R ?Dc (wg (Suc m) [m] (ctl (gph1 ((2 + \<mu>) * d)))) = wg ?R (map ((!) ?Dc) [m]) (ctl (gph1 ((2 + \<mu>) * d)))"
      by (rule wg_wg[OF Dd DR Dl]) auto
    show ?thesis using w[unfolded e mp] by (rule sym)
  qed
  have cA: "ctl ?A \<in> carrier_mat (2 ^ length ?Dc) (2 ^ length ?Dc)" unfolding two by (rule ctl_carrier[OF Ac])
  have cB: "ctl ?B \<in> carrier_mat (2 ^ length ?Dc) (2 ^ length ?Dc)" unfolding two by (rule ctl_carrier[OF Bc])
  have cP: "1\<^sub>m 2 \<Otimes> ?P \<in> carrier_mat (2 ^ length ?Dc) (2 ^ length ?Dc)" unfolding two by simp
  have cQ: "1\<^sub>m 2 \<Otimes> ?Q \<in> carrier_mat (2 ^ length ?Dc) (2 ^ length ?Dc)" unfolding two by simp
  have W: "\<And>Q Q2. Q \<in> carrier_mat (2 ^ length ?Dc) (2 ^ length ?Dc) \<Longrightarrow> Q2 \<in> carrier_mat (2 ^ length ?Dc) (2 ^ length ?Dc)
      \<Longrightarrow> wg ?R ?Dc Q * wg ?R ?Dc Q2 = wg ?R ?Dc (Q * Q2)"
    by (rule wg_mult) (use Dd DR in \<open>auto simp del: upt_Suc\<close>)
  have "wg ?R [?c] (ctl (gph1 ((2 + \<mu>) * d))) * wg ?R [1, ?c] (ctl (xrot d)) * wg ?R [1..<Suc m] ?P
      * wg ?R [1, ?c] (ctl (xrot d)) * wg ?R [1..<Suc m] ?Q
      = wg ?R ?Dc (ctl ?B * ctl ?A * (1\<^sub>m 2 \<Otimes> ?P) * ctl ?A * (1\<^sub>m 2 \<Otimes> ?Q))"
    unfolding liftB liftX lift[OF Pc] lift[OF Qc]
    by (simp only: W[OF cB cA] W[OF mult_carrier_mat[OF cB cA] cP] W[OF mult_carrier_mat[OF mult_carrier_mat[OF cB cA] cP] cA]
        W[OF mult_carrier_mat[OF mult_carrier_mat[OF mult_carrier_mat[OF cB cA] cP] cA] cQ])
  also have "ctl ?B * ctl ?A * (1\<^sub>m 2 \<Otimes> ?P) * ctl ?A * (1\<^sub>m 2 \<Otimes> ?Q) = ctl ?E"
  proof -
    have c2: "ctl ?B * ctl ?A \<in> carrier_mat (2 * ?n) (2 * ?n)" using cA cB two by simp
    have cP': "1\<^sub>m 2 \<Otimes> ?P \<in> carrier_mat (2 * ?n) (2 * ?n)" and cQ': "1\<^sub>m 2 \<Otimes> ?Q \<in> carrier_mat (2 * ?n) (2 * ?n)" by simp_all
    have cA': "ctl ?A \<in> carrier_mat (2 * ?n) (2 * ?n)" by (rule ctl_carrier[OF Ac])
    have "ctl ?B * ctl ?A * (1\<^sub>m 2 \<Otimes> ?P) * ctl ?A * (1\<^sub>m 2 \<Otimes> ?Q)
        = (ctl ?B * ctl ?A) * ((1\<^sub>m 2 \<Otimes> ?P) * ctl ?A) * (1\<^sub>m 2 \<Otimes> ?Q)"
      by (simp only: assoc_mult_mat[OF c2 cP' cA'])
    also have "\<dots> = (ctl ?B * ctl ?A) * ((1\<^sub>m 2 \<Otimes> ?P) * ctl ?A * (1\<^sub>m 2 \<Otimes> ?Q))"
      by (rule assoc_mult_mat[OF c2 mult_carrier_mat[OF cP' cA'] cQ'])
    also have "\<dots> = ctl (?B * ?A) * ctl (?P * ?A * ?Q)"
      using ctl_conj[OF Pc Qc Ac inc_dec_pmat] ctl_mult[OF Bc Ac] by simp
    also have "\<dots> = ctl (?B * ?A * (?P * ?A * ?Q))"
      by (rule ctl_mult[where n = "2 ^ m"]) (use Ac Bc in \<open>simp_all add: mult_carrier_mat[OF mult_carrier_mat[OF pmat_carrier Ac] pmat_carrier]\<close>)
    also have "?B * ?A * (?P * ?A * ?Q) = ?E"
      unfolding slap_factors[OF m mu] by (rule assoc_mult_mat[OF Bc Ac mult_carrier_mat[OF mult_carrier_mat[OF pmat_carrier Ac] pmat_carrier]])
    finally show ?thesis .
  qed
  also have "wg ?R ?Dc (ctl ?E) = ctrl_bit (2 ^ k) (?n * 2) j (?E \<Otimes> 1\<^sub>m 2)"
  proof -
    have Ec: "?E \<in> carrier_mat ?n ?n" unfolding slap_factors[OF m mu] by (rule mult_carrier_mat[OF Bc mult_carrier_mat[OF Ac mult_carrier_mat[OF mult_carrier_mat[OF pmat_carrier Ac] pmat_carrier]]])
    have t: "1\<^sub>m (2 ^ 0) \<Otimes> (?E \<Otimes> 1\<^sub>m (2 ^ 1)) = wg (0 + m + 1) [1..<1 + m] ?E" by (rule tensor_wg[OF Ec])
    have "1\<^sub>m 1 \<Otimes> (?E \<Otimes> 1\<^sub>m 2) = ?E \<Otimes> 1\<^sub>m 2" using left_tensor_id[of "?E \<Otimes> 1\<^sub>m 2" "?n * 2" "?n * 2"] Ec by simp
    hence t': "?E \<Otimes> 1\<^sub>m 2 = wg (Suc m) [1..<Suc m] ?E" using t by simp
    have c: "ctl (wg (Suc m) [1..<Suc m] ?E) = wg (Suc (Suc m)) ([1..<Suc m] @ [Suc m]) (ctl ?E)"
      by (rule wg_ctl[symmetric]) (use Ec in \<open>simp_all del: upt_Suc\<close>)
    have G: "?E \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (2 ^ Suc m) (2 ^ Suc m)" by (rule carrier_matI) (use Ec in simp_all)
    have cb: "ctrl_bit (2 ^ k) (2 ^ Suc m) j (?E \<Otimes> 1\<^sub>m 2) = wg (Suc m + k) ([0..<Suc m] @ [Suc m + j]) (ctl (?E \<Otimes> 1\<^sub>m 2))"
      by (rule ctrl_bit_wg[OF j G])
    let ?F = "[0..<Suc m] @ [Suc m + j]"
    have Fd: "distinct ?F" and FR: "\<And>v. v \<in> set ?F \<Longrightarrow> v < Suc m + k" and Fl: "length ?F = Suc (Suc m)" using j by auto
    have mp: "map ((!) ?F) ([1..<Suc m] @ [Suc m]) = ?Dc" by (rule nth_equalityI) (auto simp: nth_append)
    have "ctrl_bit (2 ^ k) (?n * 2) j (?E \<Otimes> 1\<^sub>m 2) = wg (Suc m + k) ?F (wg (Suc (Suc m)) ([1..<Suc m] @ [Suc m]) (ctl ?E))"
      using cb unfolding t'[symmetric] c[symmetric] by (simp add: ac_simps)
    also have "\<dots> = wg (Suc m + k) (map ((!) ?F) ([1..<Suc m] @ [Suc m])) (ctl ?E)"
      by (rule wg_wg[OF Fd FR Fl]) (auto simp del: upt_Suc)
    also have "\<dots> = wg (Suc m + k) ?Dc (ctl ?E)" unfolding mp ..
    finally show ?thesis by simp
  qed
  finally show ?thesis by (simp add: ac_simps)
qed

subsection \<open>The step as gates\<close>

text \<open>Decrement, controlled rotation of system wire $1$, increment, controlled rotation, controlled
phase; the control is clock wire $m+1+j$.  The phase $(2+\mu)d$ is the diagonal of $L+\mu I$.\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{quantikz}[row sep=0.3cm, column sep=0.35cm]
\lstick{clock wire $m+1+j$} & \qw & \ctrl{2} & \qw & \ctrl{2} & \gate{\mathrm{diag}(1, e^{i(2+\mu)d})} & \qw \\
\lstick{system $2,\dots,m$} & \gate[3]{\mathrm{Dec}}\qwbundle{} & \qw & \gate[3]{\mathrm{Inc}} & \qw & \qw & \qw \\
\lstick{system $1$} & & \gate{e^{-idX}} & & \gate{e^{-idX}} & \qw & \qw \\
\lstick{ancillas $\ket{0}^m$} & \qwbundle{} & \qw & & \qw & \qw & \qw
\end{quantikz} \\[0.3em]
{\small One controlled Trotter step: colour $1$ is colour $0$ conjugated by the incrementer, so only
the rotations and the phase need the control.}
\end{center}
\<close>

definition clap_step :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "clap_step m k a j \<mu> d = concat
     [compile (Suc (m + k) + a) (map (rename ((!) (lap_vs m k))) (rev (incr_gates m m))),
      wg_gates (Suc (m + k) + a) [1, Suc (m + j)] (ctl (xrot d)),
      compile (Suc (m + k) + a) (map (rename ((!) (lap_vs m k))) (incr_gates m m)),
      wg_gates (Suc (m + k) + a) [1, Suc (m + j)] (ctl (xrot d)),
      wg_gates (Suc (m + k) + a) [Suc (m + j)] (ctl (gph1 ((2 + \<mu>) * d)))]"

theorem clap_step_props:
  assumes m: "2 \<le> m" and a: "m \<le> a" and j: "j < k" and mu: "0 \<le> \<mu>"
  shows "stands_for (2 ^ a) (2 ^ Suc (m + k)) (circuit_mat (2 ^ (Suc (m + k) + a)) (clap_step m k a j \<mu> d))
      (ctrl_bit (2 ^ k) (2 ^ m * 2) j (evolution_product (2 ^ m) d (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m))) \<Otimes> 1\<^sub>m 2))"
    "\<forall>U \<in> set (clap_step m k a j \<mu> d). elementary (2 ^ (Suc (m + k) + a)) U"
    "length (clap_step m k a j \<mu> d) \<le> 2 * (m * (m + 2) * (6 * (Suc (m + k) + a) + 7)) + 3 * (4 * (Suc (m + k) + a) + 1)"
proof -
  let ?R = "Suc (m + k)" and ?K = "Suc (m + k) + a" and ?c = "Suc (m + j)" and ?n = "2 ^ m :: nat"
  let ?vs = "lap_vs m k" and ?g = "incr_gates m m"
  note V = lap_vs[OF a, where k = k]
  have m0: "0 < m" using m by simp
  have okg: "\<forall>g \<in> set ?g. rg_ok (length ?vs) g" using incr_rg_ok[of m m] V(2) by (simp add: mult_2)
  have okr: "\<forall>g \<in> set (rev ?g). rg_ok (length ?vs) g" using okg by simp
  note CI = compile_rename[OF V(1,3) okg] and CD = compile_rename[OF V(1,3) okr]
  have twoL: "length ?vs = m + m" by (rule V(2))
  note SI = incr_stands[OF m0]
  have TI: "stands_for (2 ^ a) (2 ^ ?R) (wg ?K ?vs (pmat (2 ^ length ?vs) (rcirc ?g))) (wg ?R [1..<Suc m] (pmat ?n (inc_f ?n)))"
    using stands_for_wg[OF SI(1) V(1) V(2) V(5) V(6)] V(4) unfolding twoL by simp
  have TD: "stands_for (2 ^ a) (2 ^ ?R) (wg ?K ?vs (pmat (2 ^ length ?vs) (rcirc (rev ?g)))) (wg ?R [1..<Suc m] (pmat ?n (dec_f ?n)))"
    using stands_for_wg[OF SI(2) V(1) V(2) V(5) V(6)] V(4) unfolding twoL by simp
  have Xd: "distinct [1, ?c]" and XK: "\<And>w. w \<in> set [1, ?c] \<Longrightarrow> w < ?K" and XR: "\<And>w. w \<in> set [1, ?c] \<Longrightarrow> w < ?R"
    using m j by auto
  have Xc: "ctl (xrot d) \<in> carrier_mat (2 ^ length [1, ?c]) (2 ^ length [1, ?c])" using ctl_carrier[OF xrot_carrier] by simp
  have Xu: "Quantum.unitary (ctl (xrot d))" by (rule ctl_unitary[OF xrot_carrier xrot_unitary])
  note WX = wg_gates_props[OF Xd XK _ Xc Xu]
  have TX: "stands_for (2 ^ a) (2 ^ ?R) (wg ?K [1, ?c] (ctl (xrot d))) (wg ?R [1, ?c] (ctl (xrot d)))"
    by (rule stands_for_wg_plain[OF Xd XR Xc])
  have Pd: "distinct [?c]" and PK: "\<And>w. w \<in> set [?c] \<Longrightarrow> w < ?K" and PR: "\<And>w. w \<in> set [?c] \<Longrightarrow> w < ?R"
    using j by auto
  have Pc: "ctl (gph1 ((2 + \<mu>) * d)) \<in> carrier_mat (2 ^ length [?c]) (2 ^ length [?c])" using ctl_carrier[OF gph1_carrier] by simp
  have Pu: "Quantum.unitary (ctl (gph1 ((2 + \<mu>) * d)))" by (rule ctl_unitary[OF gph1_carrier gph1_unitary])
  note WP = wg_gates_props[OF Pd PK _ Pc Pu]
  have TP: "stands_for (2 ^ a) (2 ^ ?R) (wg ?K [?c] (ctl (gph1 ((2 + \<mu>) * d)))) (wg ?R [?c] (ctl (gph1 ((2 + \<mu>) * d))))"
    by (rule stands_for_wg_plain[OF Pd PR Pc])
  let ?Ls = "[compile ?K (map (rename ((!) ?vs)) (rev ?g)), wg_gates ?K [1, ?c] (ctl (xrot d)),
      compile ?K (map (rename ((!) ?vs)) ?g), wg_gates ?K [1, ?c] (ctl (xrot d)), wg_gates ?K [?c] (ctl (gph1 ((2 + \<mu>) * d)))]"
  have el: "\<forall>U \<in> set (concat ?Ls). elementary (2 ^ ?K) U" using CI(2) CD(2) WX(2) WP(2) by auto
  thus "\<forall>U \<in> set (clap_step m k a j \<mu> d). elementary (2 ^ ?K) U" by (simp add: clap_step_def)
  have "circuit_mat (2 ^ ?K) (concat ?Ls) = circuit_mat (2 ^ ?K) (map (circuit_mat (2 ^ ?K)) ?Ls)"
    by (rule circuit_mat_concat) (use el elementary_unitary(1) in auto)
  also have "map (circuit_mat (2 ^ ?K)) ?Ls = [wg ?K ?vs (pmat (2 ^ length ?vs) (rcirc (rev ?g))), wg ?K [1, ?c] (ctl (xrot d)),
      wg ?K ?vs (pmat (2 ^ length ?vs) (rcirc ?g)), wg ?K [1, ?c] (ctl (xrot d)), wg ?K [?c] (ctl (gph1 ((2 + \<mu>) * d)))]"
    using CI(1) CD(1) WX(1) WP(1) by simp
  finally have C: "circuit_mat (2 ^ ?K) (clap_step m k a j \<mu> d) = circuit_mat (2 ^ ?K) [wg ?K ?vs (pmat (2 ^ length ?vs) (rcirc (rev ?g))),
      wg ?K [1, ?c] (ctl (xrot d)), wg ?K ?vs (pmat (2 ^ length ?vs) (rcirc ?g)), wg ?K [1, ?c] (ctl (xrot d)),
      wg ?K [?c] (ctl (gph1 ((2 + \<mu>) * d)))]" by (simp add: clap_step_def)
  have KK: "(2::nat) ^ ?K = 2 ^ a * 2 ^ ?R" by (simp add: power_add)
  have S: "stands_for (2 ^ a) (2 ^ ?R) (circuit_mat (2 ^ a * 2 ^ ?R) [wg ?K ?vs (pmat (2 ^ length ?vs) (rcirc (rev ?g))),
      wg ?K [1, ?c] (ctl (xrot d)), wg ?K ?vs (pmat (2 ^ length ?vs) (rcirc ?g)), wg ?K [1, ?c] (ctl (xrot d)),
      wg ?K [?c] (ctl (gph1 ((2 + \<mu>) * d)))])
      (circuit_mat (2 ^ ?R) [wg ?R [1..<Suc m] (pmat ?n (dec_f ?n)), wg ?R [1, ?c] (ctl (xrot d)),
      wg ?R [1..<Suc m] (pmat ?n (inc_f ?n)), wg ?R [1, ?c] (ctl (xrot d)), wg ?R [?c] (ctl (gph1 ((2 + \<mu>) * d)))])"
    by (rule stands_for_circuit) (simp only: list_all2_Cons list_all2_Nil, intro conjI TD TX TI TP refl)
  have reg: "circuit_mat (2 ^ ?R) [wg ?R [1..<Suc m] (pmat ?n (dec_f ?n)), wg ?R [1, ?c] (ctl (xrot d)),
      wg ?R [1..<Suc m] (pmat ?n (inc_f ?n)), wg ?R [1, ?c] (ctl (xrot d)), wg ?R [?c] (ctl (gph1 ((2 + \<mu>) * d)))]
      = wg ?R [?c] (ctl (gph1 ((2 + \<mu>) * d))) * wg ?R [1, ?c] (ctl (xrot d)) * wg ?R [1..<Suc m] (pmat ?n (inc_f ?n))
        * wg ?R [1, ?c] (ctl (xrot d)) * wg ?R [1..<Suc m] (pmat ?n (dec_f ?n))"
    by (simp del: upt_Suc)
  show "stands_for (2 ^ a) (2 ^ ?R) (circuit_mat (2 ^ ?K) (clap_step m k a j \<mu> d))
      (ctrl_bit (2 ^ k) (2 ^ m * 2) j (evolution_product (2 ^ m) d (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m))) \<Otimes> 1\<^sub>m 2))"
    using S unfolding C unfolding KK reg ctrl_lap_reg[OF m j mu] .
  have l1: "length (compile ?K (map (rename ((!) ?vs)) (rev ?g))) \<le> m * (m + 2) * (6 * ?K + 7)"
    using CD(3) by (simp add: length_incr)
  have l2: "length (compile ?K (map (rename ((!) ?vs)) ?g)) \<le> m * (m + 2) * (6 * ?K + 7)"
    using CI(3) by (simp add: length_incr)
  have l3: "length (wg_gates ?K [1, ?c] (ctl (xrot d))) \<le> 4 * ?K + 1" and l4: "length (wg_gates ?K [?c] (ctl (gph1 ((2 + \<mu>) * d)))) \<le> 4 * ?K + 1"
    using WX(3) WP(3) by simp_all
  show "length (clap_step m k a j \<mu> d) \<le> 2 * (m * (m + 2) * (6 * ?K + 7)) + 3 * (4 * ?K + 1)"
    using l1 l2 l3 l4 by (simp add: clap_step_def)
qed

end
