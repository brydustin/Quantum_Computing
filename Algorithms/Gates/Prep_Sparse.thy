theory Prep_Sparse
  imports Prep_Angle_Oracle Multi_Controlled_NOT
begin

section \<open>Sparse state preparation from elementary gates\<close>

text \<open>If $a$ vanishes outside a list $xs$ of $s$ indices, level $j$ of the cascade has at most
$s$ prefixes of nonzero weight, and the angle oracle is a table with $s$ entries.  Built from
Toffoli ladders on $k$ clean ancillas, the table makes the whole preparation elementary.\<close>

subsection \<open>Clean ancillas\<close>

lemma anc_anc:
  assumes B: "0 < B"
  shows "anc A (B * M) * anc B M = anc (A * B) M"
proof (rule eq_matI)
  fix r c assume "r < dim_row (anc (A * B) M)" "c < dim_col (anc (A * B) M)"
  hence r: "r < A * (B * M)" and c: "c < M" by (simp_all add: Groups.mult.assoc)
  have "M \<le> B * M" using B by simp
  hence cB: "c < B * M" using c by linarith
  have col: "Matrix.col (anc B M) c = unit_vec (B * M) c" using c cB by (intro eq_vecI) (auto simp: anc_def unit_vec_def)
  have "(anc A (B * M) * anc B M) $$ (r, c) = Matrix.row (anc A (B * M)) r \<bullet> Matrix.col (anc B M) c"
    by (rule index_mult_mat(1)) (use r c in simp_all)
  also have "\<dots> = Matrix.row (anc A (B * M)) r \<bullet> unit_vec (B * M) c" unfolding col ..
  also have "\<dots> = anc A (B * M) $$ (r, c)" using scalar_prod_right_unit[OF cB] r cB by simp
  also have "\<dots> = anc (A * B) M $$ (r, c)" using r c cB by (simp add: anc_def Groups.mult.assoc)
  finally show "(anc A (B * M) * anc B M) $$ (r, c) = anc (A * B) M $$ (r, c)" .
qed (simp_all add: Groups.mult.assoc)

lemma stands_for_trans:
  assumes u: "stands_for A (B * M) U Ga" and g: "stands_for B M Ga Gb" and B: "0 < B"
  shows "stands_for (A * B) M U Gb"
proof -
  have Uc: "U \<in> carrier_mat (A * (B * M)) (A * (B * M))" and Gac: "Ga \<in> carrier_mat (B * M) (B * M)"
    and UGa: "U * anc A (B * M) = anc A (B * M) * Ga" using u by (simp_all add: stands_for_def)
  have Gbc: "Gb \<in> carrier_mat M M" and GGb: "Ga * anc B M = anc B M * Gb" using g by (simp_all add: stands_for_def)
  have "U * anc (A * B) M = U * anc A (B * M) * anc B M"
    unfolding anc_anc[OF B, symmetric] by (rule assoc_mult_mat[OF Uc anc_carrier anc_carrier, symmetric])
  also have "\<dots> = anc A (B * M) * Ga * anc B M" unfolding UGa ..
  also have "\<dots> = anc A (B * M) * (Ga * anc B M)" by (rule assoc_mult_mat[OF anc_carrier Gac anc_carrier])
  also have "\<dots> = anc A (B * M) * anc B M * Gb" unfolding GGb by (rule assoc_mult_mat[OF anc_carrier anc_carrier Gbc, symmetric])
  also have "\<dots> = anc (A * B) M * Gb" unfolding anc_anc[OF B] ..
  finally show ?thesis using Uc Gbc unfolding stands_for_def by (simp add: Groups.mult.assoc)
qed

lemma stands_for_apply:
  assumes s: "stands_for A N U G" and v: "v \<in> carrier_vec N"
  shows "U *\<^sub>v (anc A N *\<^sub>v v) = anc A N *\<^sub>v (G *\<^sub>v v)"
proof -
  have Uc: "U \<in> carrier_mat (A * N) (A * N)" and Gc: "G \<in> carrier_mat N N" and UG: "U * anc A N = anc A N * G"
    using s by (simp_all add: stands_for_def)
  have "U *\<^sub>v (anc A N *\<^sub>v v) = (U * anc A N) *\<^sub>v v" by (rule assoc_mult_mat_vec[OF Uc anc_carrier v, symmetric])
  also have "\<dots> = (anc A N * G) *\<^sub>v v" unfolding UG ..
  also have "\<dots> = anc A N *\<^sub>v (G *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF anc_carrier Gc v])
  finally show ?thesis .
qed

lemma stands_for_dist:
  assumes s: "stands_for A N U G" and v: "v \<in> carrier_vec N" and w: "w \<in> carrier_vec N" and A: "0 < A"
  shows "\<parallel>U *\<^sub>v (anc A N *\<^sub>v v) - anc A N *\<^sub>v w\<parallel> = \<parallel>G *\<^sub>v v - w\<parallel>"
proof -
  have Gc: "G \<in> carrier_mat N N" using s by (simp add: stands_for_def)
  have Gv: "G *\<^sub>v v \<in> carrier_vec N" by (rule mult_mat_vec_carrier[OF Gc v])
  have "U *\<^sub>v (anc A N *\<^sub>v v) - anc A N *\<^sub>v w = anc A N *\<^sub>v (G *\<^sub>v v - w)"
    unfolding stands_for_apply[OF s v] by (rule mult_minus_distrib_mat_vec[OF anc_carrier Gv w, symmetric])
  thus ?thesis using Gv w A by (simp add: anc_norm carrier_vecD)
qed

lemma elementary_lift:
  assumes U: "elementary K U" and m: "0 < m"
  shows "elementary (m * K) (1\<^sub>m m \<Otimes> U)"
proof -
  obtain a b q G where q: "q \<in> {1, 2}" and G: "G \<in> carrier_mat (2 ^ q) (2 ^ q)" "Quantum.unitary G"
    and ab: "0 < a" "0 < b" and K: "K = a * (2 ^ q * b)" and e: "U = 1\<^sub>m a \<Otimes> (G \<Otimes> 1\<^sub>m b)"
    using U unfolding elementary_def by blast
  have e2: "1\<^sub>m m \<Otimes> U = 1\<^sub>m (m * a) \<Otimes> (G \<Otimes> 1\<^sub>m b)"
    unfolding e using tensor_mat_is_assoc[of "1\<^sub>m m" "1\<^sub>m a" "G \<Otimes> 1\<^sub>m b"] tensor_mat_id[of m a] m ab by simp
  show ?thesis unfolding elementary_def
    by (rule exI[of _ "m * a"], rule exI[of _ b], rule exI[of _ q], rule exI[of _ G]) (use q in \<open>simp add: e2 G ab m K Groups.mult.assoc\<close>)
qed

subsection \<open>Permutations\<close>

lemma pmat_high:
  assumes f: "\<And>t. t < a \<Longrightarrow> f t < a" and b: "0 < b"
  shows "pmat a f \<Otimes> 1\<^sub>m b = pmat (a * b) (\<lambda>c. f (c div b) * b + c mod b)"
proof (rule eq_matI)
  fix r c assume "r < dim_row (pmat (a * b) (\<lambda>c. f (c div b) * b + c mod b))" "c < dim_col (pmat (a * b) (\<lambda>c. f (c div b) * b + c mod b))"
  hence r: "r < a * b" and c: "c < a * b" by (simp_all add: pmat_def)
  have a: "0 < a" using r by (cases a) auto
  have i: "(pmat a f \<Otimes> 1\<^sub>m b) $$ (r, c) = pmat a f $$ (r div b, c div b) * 1\<^sub>m b $$ (r mod b, c mod b)"
    using index_tensor_mat[of "pmat a f" a a "1\<^sub>m b" b b r c] r c a b by simp
  have rd: "r div b < a" "c div b < a" using r c b by (simp_all add: div_less_iff_less_mult)
  show "(pmat a f \<Otimes> 1\<^sub>m b) $$ (r, c) = pmat (a * b) (\<lambda>c. f (c div b) * b + c mod b) $$ (r, c)"
    unfolding i using r c rd b digit_eq[of "c mod b" b r "f (c div b)"] by (simp add: pmat_def)
qed (simp_all add: pmat_def)

lemma bit_lt_pow: "u < 2 ^ b \<Longrightarrow> b \<le> n \<Longrightarrow> \<not> bit (u :: nat) n"
proof -
  assume u: "u < 2 ^ b" and n: "b \<le> n"
  have "u < 2 ^ n" using less_le_trans[OF u power_increasing[OF n, of "2::nat"]] by simp
  thus ?thesis by (simp add: bit_iff_odd)
qed

lemma bits_eq_lt:
  assumes p: "p < 2 ^ n" and c: "c < 2 ^ n"
  shows "(\<forall>l<n. bit p l = bit c l) \<longleftrightarrow> p = (c :: nat)"
proof
  assume h: "\<forall>l<n. bit p l = bit c l"
  show "p = c"
  proof (rule bit_eqI)
    fix l show "bit p l \<longleftrightarrow> bit c l"
    proof (cases "l < n")
      case True thus ?thesis using h by simp
    next
      case False thus ?thesis using bit_lt_pow[OF p, of l] bit_lt_pow[OF c, of l] by simp
    qed
  qed
qed simp

subsection \<open>Writing the code into the register\<close>

definition code_wires :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "code_wires k b u = map (\<lambda>i. k + i) (filter (bit u) [0..<b])"

lemma flips_code_wires:
  assumes u: "u < 2 ^ b"
  shows "flips (code_wires k b u) z = xor (z div 2 ^ k) u * 2 ^ k + z mod 2 ^ k"
proof (rule bit_eqI)
  fix q
  let ?R = "xor (z div 2 ^ k) u * 2 ^ k + z mod 2 ^ k"
  have d: "distinct (code_wires k b u)" by (simp add: code_wires_def distinct_map inj_on_def)
  have m: "q \<in> set (code_wires k b u) \<longleftrightarrow> k \<le> q \<and> bit u (q - k)"
  proof
    assume "q \<in> set (code_wires k b u)"
    thus "k \<le> q \<and> bit u (q - k)" by (auto simp: code_wires_def)
  next
    assume h: "k \<le> q \<and> bit u (q - k)"
    have "q - k < b" using bit_lt_pow[OF u, of "q - k"] h by (cases "b \<le> q - k") auto
    hence "q - k \<in> set (filter (bit u) [0..<b])" using h by simp
    moreover have "q = k + (q - k)" using h by simp
    ultimately show "q \<in> set (code_wires k b u)" unfolding code_wires_def set_map by (rule rev_image_eqI)
  qed
  have lo: "?R mod 2 ^ k = z mod 2 ^ k" and hi: "?R div 2 ^ k = xor (z div 2 ^ k) u" by simp_all
  show "bit (flips (code_wires k b u) z) q \<longleftrightarrow> bit ?R q"
    unfolding bit_flips[OF d] m bit_mod_div[of ?R q k] lo hi
    by (cases "q < k") (simp_all add: bit_xor_iff bit_mod_div[of z q k])
qed

lemma xor_shift_lt:
  assumes z: "z < 2 ^ (b + k)" and u: "u < 2 ^ b"
  shows "xor (z div 2 ^ k) u * 2 ^ k + z mod 2 ^ k < (2::nat) ^ (b + k)"
proof -
  have "z div 2 ^ k < 2 ^ b" using z by (simp add: div_less_iff_less_mult power_add)
  hence x: "xor (z div 2 ^ k) u < 2 ^ b" by (rule xor_lt[OF _ u])
  have "xor (z div 2 ^ k) u * 2 ^ k + z mod 2 ^ k < (xor (z div 2 ^ k) u + 1) * 2 ^ k" by simp
  also have "\<dots> \<le> 2 ^ b * 2 ^ k" using x by (intro mult_le_mono1) simp
  finally show ?thesis by (simp add: power_add)
qed

text \<open>The angle oracle of level $j$, as a permutation of $b + k$ wires.\<close>

lemma lev_oracle_pmat:
  assumes j: "j < k"
  shows "lev_oracle b k a j
    = pmat (2 ^ (b + k)) (\<lambda>z. xor (z div 2 ^ k) (prep_code b k a j (z div 2 ^ (k - j) mod 2 ^ j)) * 2 ^ k + z mod 2 ^ k)"
proof -
  define M :: nat where "M = 2 * 2 ^ (k - Suc j)"
  let ?f = "prep_code b k a j"
  have M2: "M = 2 ^ (k - j)" unfolding M_def using j by (simp flip: power_Suc add: Suc_diff_Suc)
  have MK: "M * 2 ^ j = 2 ^ k" unfolding M2 using j by (simp flip: power_add)
  have M0: "0 < M" by (simp add: M_def)
  have X: "\<And>t. t < 2 ^ b * 2 ^ j \<Longrightarrow> xreg (2 ^ j) ?f t < 2 ^ b * 2 ^ j" by (rule xreg_props(1)) (rule prep_code_lt)
  have NB: "2 ^ b * 2 ^ j * M = (2::nat) ^ (b + k)" unfolding power_add MK[symmetric] by (simp only: ac_simps)
  have E: "xreg (2 ^ j) ?f (z div M) * M + z mod M = xor (z div 2 ^ k) (?f (z div 2 ^ (k - j) mod 2 ^ j)) * 2 ^ k + z mod 2 ^ k"
    for z
  proof -
    have d: "z div M div 2 ^ j = z div 2 ^ k" by (simp only: div_mult2_eq[symmetric] MK)
    have m: "z mod 2 ^ k = M * (z div M mod 2 ^ j) + z mod M" unfolding MK[symmetric] by (rule mod_mult2_eq)
    have "xreg (2 ^ j) ?f (z div M) * M + z mod M
        = xor (z div M div 2 ^ j) (?f (z div M mod 2 ^ j)) * (M * 2 ^ j) + (M * (z div M mod 2 ^ j) + z mod M)"
      by (simp add: xreg_def algebra_simps)
    also have "\<dots> = xor (z div 2 ^ k) (?f (z div M mod 2 ^ j)) * 2 ^ k + z mod 2 ^ k"
      unfolding d MK m[symmetric] ..
    finally show ?thesis unfolding M2 .
  qed
  have "lev_oracle b k a j = pmat (2 ^ b * 2 ^ j) (xreg (2 ^ j) ?f) \<Otimes> 1\<^sub>m M"
    by (simp add: lev_oracle_def oracle_m_def M_def)
  also have "\<dots> = pmat (2 ^ b * 2 ^ j * M) (\<lambda>z. xreg (2 ^ j) ?f (z div M) * M + z mod M)" by (rule pmat_high[OF X M0])
  also have "\<dots> = pmat (2 ^ (b + k)) (\<lambda>z. xor (z div 2 ^ k) (?f (z div 2 ^ (k - j) mod 2 ^ j)) * 2 ^ k + z mod 2 ^ k)"
    unfolding NB by (rule pmat_cong) (rule E)
  finally show ?thesis .
qed

subsection \<open>The table\<close>

definition pref_list :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "pref_list k xs j = remdups (map (\<lambda>x. x div 2 ^ (k - j)) xs)"

definition supp :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat list \<Rightarrow> bool" where
  "supp k a xs \<longleftrightarrow> (\<forall>x \<in> set xs. x < 2 ^ k) \<and> (\<forall>x < 2 ^ k. x \<notin> set xs \<longrightarrow> a x = 0)"

text \<open>Controls: the top $j$ data wires; targets: the register; ancillas: above the register.\<close>

definition lev_table :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> rgate list" where
  "lev_table b k a xs j = lookup (\<lambda>l. k - j + l) (\<lambda>i. b + k + i) j (pref_list k xs j) (\<lambda>c. code_wires k b (prep_code b k a j c))"

lemma lev_table_wires:
  assumes j: "j < k"
  shows "ladder_ok (k + (b + k)) (\<lambda>l. k - j + l) (\<lambda>i. b + k + i) j" "inj_on (\<lambda>l. k - j + l) {..<j}"
    "targets_ok (k + (b + k)) (\<lambda>l. k - j + l) (\<lambda>i. b + k + i) j (code_wires k b u)"
  using j by (auto simp: ladder_ok_def inj_on_def targets_ok_def code_wires_def)

lemma prep_code_off:
  assumes sp: "supp k a xs" and j: "j < k" and p: "p < 2 ^ j" and np: "p \<notin> set (pref_list k xs j)"
  shows "prep_code b k a j p = 0"
proof -
  have z: "a (p * 2 ^ (k - j) + x) = 0" if x: "x < 2 ^ (k - j)" for x
  proof -
    let ?y = "p * 2 ^ (k - j) + x"
    have yd: "?y div 2 ^ (k - j) = p" using x by simp
    have "?y < (p + 1) * 2 ^ (k - j)" using x by simp
    also have "\<dots> \<le> 2 ^ j * 2 ^ (k - j)" using p by (intro mult_le_mono1) simp
    also have "\<dots> = 2 ^ k" using j by (simp flip: power_add)
    finally have yk: "?y < 2 ^ k" .
    have "?y \<notin> set xs"
    proof
      assume "?y \<in> set xs"
      hence "?y div 2 ^ (k - j) \<in> set (pref_list k xs j)" unfolding pref_list_def set_remdups set_map by (rule imageI)
      thus False using np yd by simp
    qed
    thus ?thesis using sp yk by (simp add: supp_def)
  qed
  have "(\<Sum>x<2 ^ (k - j). (a (p * 2 ^ (k - j) + x))\<^sup>2) = 0" by (rule sum.neutral) (simp add: z)
  hence "pnorm k a j p = 0" by (simp add: pnorm_def)
  thus ?thesis by (simp add: prep_code_def)
qed

lemma concat_if_eq: "distinct cs \<Longrightarrow> concat (map (\<lambda>c. if c = p then f c else []) cs) = (if p \<in> set cs then f p else [])"
  by (induction cs) auto

theorem lev_table_rcirc:
  assumes sp: "supp k a xs" and j: "j < k" and z: "z < 2 ^ (b + k)"
  shows "rcirc (lev_table b k a xs j) z
      = xor (z div 2 ^ k) (prep_code b k a j (z div 2 ^ (k - j) mod 2 ^ j)) * 2 ^ k + z mod 2 ^ k"
proof -
  let ?cw = "\<lambda>l. k - j + l" and ?cs = "pref_list k xs j"
  let ?ts = "\<lambda>c. code_wires k b (prep_code b k a j c)" and ?p = "z div 2 ^ (k - j) mod 2 ^ j"
  note W = lev_table_wires[OF j]
  have x: "\<And>i. i \<le> j \<Longrightarrow> \<not> bit z (b + k + i)" using bit_lt_pow[OF z] by simp
  have t: "\<And>c. c \<in> set ?cs \<Longrightarrow> targets_ok (k + (b + k)) ?cw (\<lambda>i. b + k + i) j (?ts c)" by (rule W(3))
  have L: "rcirc (lev_table b k a xs j) z = flips (concat (map (\<lambda>c. if spells ?cw j z c then ?ts c else []) ?cs)) z"
    unfolding lev_table_def by (rule lookup_rcirc[OF W(1) W(2) x t])
  have cs: "c < 2 ^ j" if cin: "c \<in> set ?cs" for c
  proof -
    obtain y where y: "y \<in> set xs" "c = y div 2 ^ (k - j)" using cin by (auto simp: pref_list_def)
    have "y < 2 ^ k" using sp y(1) by (simp add: supp_def)
    hence "y < 2 ^ j * 2 ^ (k - j)" using j by (simp flip: power_add)
    thus ?thesis using y(2) by (simp add: div_less_iff_less_mult)
  qed
  have pl: "?p < 2 ^ j" by simp
  have bp: "bit ?p l \<longleftrightarrow> bit z (k - j + l)" if "l < j" for l
    using that by (simp add: bit_take_bit_iff bit_drop_bit_eq flip: take_bit_eq_mod drop_bit_eq_div)
  have sp_eq: "spells ?cw j z c \<longleftrightarrow> c = ?p" if "c \<in> set ?cs" for c
  proof -
    have "spells ?cw j z c \<longleftrightarrow> (\<forall>l<j. bit ?p l = bit c l)" using bp by (simp add: spells_def)
    also have "\<dots> \<longleftrightarrow> ?p = c" by (rule bits_eq_lt[OF pl cs[OF that]])
    finally show ?thesis by auto
  qed
  have "concat (map (\<lambda>c. if spells ?cw j z c then ?ts c else []) ?cs) = concat (map (\<lambda>c. if c = ?p then ?ts c else []) ?cs)"
    by (rule arg_cong[where f = concat], rule map_cong) (simp_all add: sp_eq)
  also have "\<dots> = ?ts ?p"
  proof (cases "?p \<in> set ?cs")
    case True
    thus ?thesis by (simp add: concat_if_eq pref_list_def)
  next
    case False
    have "prep_code b k a j ?p = 0" by (rule prep_code_off[OF sp j pl False])
    thus ?thesis using False by (simp add: concat_if_eq pref_list_def code_wires_def)
  qed
  finally have C: "concat (map (\<lambda>c. if spells ?cw j z c then ?ts c else []) ?cs) = ?ts ?p" .
  show ?thesis unfolding L C by (rule flips_code_wires[OF prep_code_lt])
qed

lemma lev_table_props:
  assumes j: "j < k"
  shows "\<forall>g \<in> set (lev_table b k a xs j). rg_ok (k + (b + k)) g"
    "length (lev_table b k a xs j) \<le> length xs * (4 * k + 2 + b)"
proof -
  note W = lev_table_wires[OF j]
  show "\<forall>g \<in> set (lev_table b k a xs j). rg_ok (k + (b + k)) g"
    unfolding lev_table_def by (rule lookup_rg_ok[OF W(1)]) (rule W(3))
  have "length (lev_table b k a xs j) \<le> length (pref_list k xs j) * (4 * j + 2 + b)"
    unfolding lev_table_def by (rule length_lookup) (use length_filter_le[of _ "[0..<b]"] in \<open>simp add: code_wires_def\<close>)
  also have "\<dots> \<le> length xs * (4 * k + 2 + b)"
    using length_remdups_leq[of "map (\<lambda>x. x div 2 ^ (k - j)) xs"] j by (intro mult_le_mono) (simp_all add: pref_list_def)
  finally show "length (lev_table b k a xs j) \<le> length xs * (4 * k + 2 + b)" .
qed

subsection \<open>One level\<close>

definition lev_sgates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "lev_sgates b k a xs j = compile (k + (b + k)) (lev_table b k a xs j)
     @ map (\<lambda>U. 1\<^sub>m (2 ^ k) \<Otimes> U) (lev_mid b k j) @ compile (k + (b + k)) (lev_table b k a xs j)"

theorem lev_sgates_props:
  assumes sp: "supp k a xs" and j: "j < k"
  shows "stands_for (2 ^ k * 2 ^ b) (2 ^ k) (circuit_mat (2 ^ (k + (b + k))) (lev_sgates b k a xs j)) (lev_rnd b k a j)"
    "\<forall>U \<in> set (lev_sgates b k a xs j). elementary (2 ^ (k + (b + k))) U"
    "length (lev_sgates b k a xs j)
      \<le> 2 * (length xs * (4 * k + 2 + b) * (6 * (k + (b + k)) + 7)) + (b * (2 * (b + k) + 1) + 2)"
proof -
  let ?KL = "k + (b + k)" and ?N = "2 ^ (b + k) :: nat" and ?T = "lev_table b k a xs j"
  let ?C = "compile ?KL ?T" and ?M = "map (\<lambda>U. 1\<^sub>m (2 ^ k) \<Otimes> U) (lev_mid b k j)" and ?O = "lev_oracle b k a j"
  note T = lev_table_props[OF j, where b = b and a = a and xs = xs]
  note C = compile_props[OF T(1)]
  note Q = lev_qgates_props[OF j, where b = b and a = a]
  note Mi = lev_mid_props[OF j, of b]
  have KL: "(2::nat) ^ ?KL = 2 ^ k * ?N" by (rule power_add)
  have NN: "(2::nat) ^ (b + k) = 2 ^ b * 2 ^ k" by (rule power_add)
  have Mel: "\<forall>U \<in> set ?M. elementary (2 ^ ?KL) U" unfolding KL using Mi(2) by (auto intro!: elementary_lift)
  have midc: "\<And>U. U \<in> set (lev_mid b k j) \<Longrightarrow> U \<in> carrier_mat ?N ?N" using Mi(2) elementary_carrier by blast
  have mc: "circuit_mat ?N (lev_mid b k j) \<in> carrier_mat ?N ?N" by (rule circuit_mat_carrier) (use midc in auto)
  have cM: "circuit_mat (2 ^ ?KL) ?M = 1\<^sub>m (2 ^ k) \<Otimes> circuit_mat ?N (lev_mid b k j)"
    unfolding KL by (rule circuit_mat_tensor_left[OF midc]) simp_all
  have Cc: "circuit_mat (2 ^ ?KL) ?C \<in> carrier_mat (2 ^ ?KL) (2 ^ ?KL)" unfolding C(1) by simp
  have Mc: "circuit_mat (2 ^ ?KL) ?M \<in> carrier_mat (2 ^ ?KL) (2 ^ ?KL)" unfolding cM unfolding KL using mc by simp
  have SC: "stands_for (2 ^ k) ?N (circuit_mat (2 ^ ?KL) ?C) ?O"
  proof -
    have "stands_for (2 ^ k) ?N (pmat (2 ^ k * ?N) (rcirc ?T))
        (pmat ?N (\<lambda>z. xor (z div 2 ^ k) (prep_code b k a j (z div 2 ^ (k - j) mod 2 ^ j)) * 2 ^ k + z mod 2 ^ k))"
      by (rule stands_for_pmat) (simp_all add: lev_table_rcirc[OF sp j] xor_shift_lt prep_code_lt)
    thus ?thesis unfolding C(1) unfolding KL lev_oracle_pmat[OF j] .
  qed
  have SM: "stands_for (2 ^ k) ?N (circuit_mat (2 ^ ?KL) ?M) (circuit_mat ?N (lev_mid b k j))"
    unfolding cM by (rule stands_for_lift[OF mc]) simp
  have e: "circuit_mat (2 ^ ?KL) (lev_sgates b k a xs j) = circuit_mat (2 ^ ?KL) ?C * (circuit_mat (2 ^ ?KL) ?M * circuit_mat (2 ^ ?KL) ?C)"
  proof -
    have Cl: "\<And>U. U \<in> set ?C \<Longrightarrow> U \<in> carrier_mat (2 ^ ?KL) (2 ^ ?KL)" using C(2) elementary_carrier by blast
    have Ml: "\<And>U. U \<in> set ?M \<Longrightarrow> U \<in> carrier_mat (2 ^ ?KL) (2 ^ ?KL)" using Mel elementary_carrier by blast
    have a1: "circuit_mat (2 ^ ?KL) (?C @ ?M @ ?C) = circuit_mat (2 ^ ?KL) (?M @ ?C) * circuit_mat (2 ^ ?KL) ?C"
      by (rule circuit_mat_append) (use Cl Ml in auto)
    have a2: "circuit_mat (2 ^ ?KL) (?M @ ?C) = circuit_mat (2 ^ ?KL) ?C * circuit_mat (2 ^ ?KL) ?M"
      by (rule circuit_mat_append) (use Cl Ml in auto)
    show ?thesis unfolding lev_sgates_def a1 a2 by (rule assoc_mult_mat[OF Cc Mc Cc])
  qed
  have S1: "stands_for (2 ^ k) ?N (circuit_mat (2 ^ ?KL) (lev_sgates b k a xs j)) (?O * (circuit_mat ?N (lev_mid b k j) * ?O))"
    unfolding e by (intro stands_for_mult SC SM)
  have Oc: "?O \<in> carrier_mat ?N ?N" by (rule lev_oracle_carrier[OF j])
  have eQ: "?O * (circuit_mat ?N (lev_mid b k j) * ?O) = circuit_mat ?N (lev_qgates b k a j)"
    unfolding Q(4) by (rule assoc_mult_mat[OF Oc mc Oc, symmetric])
  have T1: "stands_for (2 ^ k) (2 ^ b * 2 ^ k) (circuit_mat (2 ^ ?KL) (lev_sgates b k a xs j)) (circuit_mat (2 ^ b * 2 ^ k) (lev_qgates b k a j))"
    using S1 unfolding eQ unfolding NN .
  have T2: "stands_for (2 ^ b) (2 ^ k) (circuit_mat (2 ^ b * 2 ^ k) (lev_qgates b k a j)) (lev_rnd b k a j)"
    using Q(1) unfolding NN .
  show "stands_for (2 ^ k * 2 ^ b) (2 ^ k) (circuit_mat (2 ^ ?KL) (lev_sgates b k a xs j)) (lev_rnd b k a j)"
    by (rule stands_for_trans[OF T1 T2]) simp
  show "\<forall>U \<in> set (lev_sgates b k a xs j). elementary (2 ^ ?KL) U" using C(2) Mel by (auto simp: lev_sgates_def)
  have lC: "length ?C \<le> length xs * (4 * k + 2 + b) * (6 * ?KL + 7)"
    using C(3) mult_le_mono1[OF T(2), of "6 * ?KL + 7"] by linarith
  have "length (lev_sgates b k a xs j) = 2 * length ?C + length (lev_mid b k j)" by (simp add: lev_sgates_def)
  thus "length (lev_sgates b k a xs j) \<le> 2 * (length xs * (4 * k + 2 + b) * (6 * ?KL + 7)) + (b * (2 * (b + k) + 1) + 2)"
    using lC Mi(3) by linarith
qed

subsection \<open>The sparse preparation\<close>

definition sprep_gates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat list \<Rightarrow> complex Matrix.mat list" where
  "sprep_gates b k a xs = concat (map (lev_sgates b k a xs) [0..<k])"

text \<open>With $s$ = \<open>length xs\<close> nonzero entries and $K = 2k + b$ wires, of which $k + b$ start clean:
$O(k\,s\,(k + b)\,K)$ elementary gates, no oracle, error at most $k \cdot 2\pi/2^b$.\<close>

theorem sparse_prep_gates:
  assumes n: "(\<Sum>x<2 ^ k. (a x)\<^sup>2) = 1" and a: "\<And>x. x < 2 ^ k \<Longrightarrow> 0 \<le> a x" and sp: "supp k a xs"
  shows "\<parallel>circuit_mat (2 ^ (k + (b + k))) (sprep_gates b k a xs) *\<^sub>v (anc (2 ^ k * 2 ^ b) (2 ^ k) *\<^sub>v unit_vec (2 ^ k) 0)
      - anc (2 ^ k * 2 ^ b) (2 ^ k) *\<^sub>v Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))\<parallel> \<le> real k * (2 * pi / 2 ^ b)"
    "\<forall>U \<in> set (sprep_gates b k a xs). elementary (2 ^ (k + (b + k))) U"
    "length (sprep_gates b k a xs)
      \<le> k * (2 * (length xs * (4 * k + 2 + b) * (6 * (k + (b + k)) + 7)) + (b * (2 * (b + k) + 1) + 2))"
proof -
  let ?KL = "k + (b + k)" and ?A = "2 ^ k * 2 ^ b :: nat" and ?G = "circuit_mat (2 ^ k) (map (lev_rnd b k a) [0..<k])"
  have lc: "U \<in> carrier_mat (2 ^ ?KL) (2 ^ ?KL)" if Us: "Us \<in> set (map (lev_sgates b k a xs) [0..<k])" "U \<in> set Us" for Us U
  proof -
    obtain j where j: "j < k" and U: "U \<in> set (lev_sgates b k a xs j)" using Us by auto
    show ?thesis using lev_sgates_props(2)[OF sp j] U elementary_carrier by blast
  qed
  have cU: "circuit_mat (2 ^ ?KL) (sprep_gates b k a xs)
      = circuit_mat (2 ^ ?KL) (map (\<lambda>j. circuit_mat (2 ^ ?KL) (lev_sgates b k a xs j)) [0..<k])"
  proof -
    have "circuit_mat (2 ^ ?KL) (sprep_gates b k a xs)
        = circuit_mat (2 ^ ?KL) (map (circuit_mat (2 ^ ?KL)) (map (lev_sgates b k a xs) [0..<k]))"
      unfolding sprep_gates_def by (rule circuit_mat_concat) (rule lc)
    thus ?thesis by (simp only: map_map comp_def)
  qed
  have KA: "?A * 2 ^ k = (2::nat) ^ ?KL" by (simp add: power_add ac_simps)
  have S: "stands_for ?A (2 ^ k) (circuit_mat (2 ^ ?KL) (sprep_gates b k a xs)) ?G"
  proof -
    have "list_all2 (stands_for ?A (2 ^ k)) (map (\<lambda>j. circuit_mat (2 ^ ?KL) (lev_sgates b k a xs j)) [0..<k]) (map (lev_rnd b k a) [0..<k])"
      by (auto simp: list_all2_map1 list_all2_map2 list_all2_same lev_sgates_props(1)[OF sp])
    hence "stands_for ?A (2 ^ k) (circuit_mat (?A * 2 ^ k) (map (\<lambda>j. circuit_mat (2 ^ ?KL) (lev_sgates b k a xs j)) [0..<k])) ?G"
      by (rule stands_for_circuit)
    thus ?thesis unfolding cU KA .
  qed
  have "\<parallel>circuit_mat (2 ^ ?KL) (sprep_gates b k a xs) *\<^sub>v (anc ?A (2 ^ k) *\<^sub>v unit_vec (2 ^ k) 0)
      - anc ?A (2 ^ k) *\<^sub>v Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))\<parallel>
      = \<parallel>?G *\<^sub>v unit_vec (2 ^ k) 0 - Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))\<parallel>"
    by (rule stands_for_dist[OF S]) simp_all
  thus "\<parallel>circuit_mat (2 ^ ?KL) (sprep_gates b k a xs) *\<^sub>v (anc ?A (2 ^ k) *\<^sub>v unit_vec (2 ^ k) 0)
      - anc ?A (2 ^ k) *\<^sub>v Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))\<parallel> \<le> real k * (2 * pi / 2 ^ b)"
    using rounded_prep[OF n a, of b] by simp
  show "\<forall>U \<in> set (sprep_gates b k a xs). elementary (2 ^ ?KL) U"
    using lev_sgates_props(2)[OF sp] by (auto simp: sprep_gates_def)
  have "length (sprep_gates b k a xs) = (\<Sum>j\<leftarrow>[0..<k]. length (lev_sgates b k a xs j))"
    by (simp add: sprep_gates_def length_concat comp_def)
  also have "\<dots> \<le> (\<Sum>j\<leftarrow>[0..<k]. 2 * (length xs * (4 * k + 2 + b) * (6 * ?KL + 7)) + (b * (2 * (b + k) + 1) + 2))"
    by (rule sum_list_mono) (rule lev_sgates_props(3)[OF sp], simp)
  finally show "length (sprep_gates b k a xs)
      \<le> k * (2 * (length xs * (4 * k + 2 + b) * (6 * ?KL + 7)) + (b * (2 * (b + k) + 1) + 2))"
    by (simp add: sum_list_triv)
qed

end
