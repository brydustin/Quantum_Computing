theory Rotation_Stage_Gates
  imports Distant_Diagonals
begin

section \<open>The rotation stage in elementary gates\<close>

text \<open>With $n^2 = 2^q$ the data lie on wires $0..q$ (the ancilla on wire 0) and the register on
wires $q+1..q+2p$: the angle bits first, then the phase bits.  A register angle
$\sum_j 2^j u_j \cdot 2\pi/2^p$ is a sum of one phase per bit, so each diagonal stage is $p$
two-qubit diagonal gates.\<close>

lemma take_bit_real_sum: "real (take_bit p r) = (\<Sum>j<p. of_bool (bit r j) * 2 ^ j)" for r :: nat
proof -
  have "take_bit p r = (\<Sum>j = 0..<p. of_bool (bit r j) * 2 ^ j)"
    using horner_sum_bit_eq_take_bit[of r p] by (simp add: horner_sum_eq_sum)
  thus ?thesis by (simp add: atLeast0LessThan)
qed

lemma dmat_sum_circ: "circuit_mat N (map (\<lambda>j. dmat N (g j)) [0..<k]) = dmat N (\<lambda>z. \<Sum>j<k. g j z)"
proof (induction k)
  case 0
  show ?case by (simp add: dmat_zero)
next
  case (Suc k)
  have "circuit_mat N (map (\<lambda>j. dmat N (g j)) [0..<Suc k])
      = circuit_mat N [dmat N (g k)] * circuit_mat N (map (\<lambda>j. dmat N (g j)) [0..<k])"
    by (simp only: upt_Suc_append[OF le0] map_append list.map, rule circuit_mat_append) auto
  also have "\<dots> = dmat N (g k) * dmat N (\<lambda>z. \<Sum>j<k. g j z)" unfolding Suc circuit_mat_single[OF dmat_carrier] ..
  also have "\<dots> = dmat N (\<lambda>z. \<Sum>j<Suc k. g j z)" unfolding dmat_mult by (simp add: add.commute)
  finally show ?case .
qed

lemma ctrl_blocks_const:
  assumes B: "B \<in> carrier_mat m m" and m: "0 < m"
  shows "ctrl_blocks N m (\<lambda>_. B) = 1\<^sub>m N \<Otimes> B"
proof (rule eq_matI)
  fix r t assume "r < dim_row (1\<^sub>m N \<Otimes> B)" "t < dim_col (1\<^sub>m N \<Otimes> B)"
  hence rt: "r < N * m" "t < N * m" using B by simp_all
  have N: "0 < N" using rt by (cases N) auto
  have "(1\<^sub>m N \<Otimes> B) $$ (r, t) = 1\<^sub>m N $$ (r div m, t div m) * B $$ (r mod m, t mod m)"
    using index_tensor_mat[of "1\<^sub>m N" N N B m m r t] rt B m N by simp
  thus "ctrl_blocks N m (\<lambda>_. B) $$ (r, t) = (1\<^sub>m N \<Otimes> B) $$ (r, t)"
    using rt m by (simp add: ctrl_blocks_index div_less_iff_less_mult)
qed (use B in simp_all)

subsection \<open>Register bits\<close>

lemma reg_bits:
  assumes z: "z < 2 ^ (q + 1 + 2 * p)"
  shows "real (z div 2 div 2 ^ q mod 2 ^ p) = (\<Sum>j<p. of_bool (bit z (q + 1 + j)) * 2 ^ j)"
    "real (z div 2 div 2 ^ q div 2 ^ p) = (\<Sum>j<p. of_bool (bit z (q + 1 + p + j)) * 2 ^ j)"
proof -
  have r: "z div 2 div 2 ^ q = drop_bit (q + 1) z" by (simp add: drop_bit_eq_div div_mult2_eq power_add ac_simps)
  show "real (z div 2 div 2 ^ q mod 2 ^ p) = (\<Sum>j<p. of_bool (bit z (q + 1 + j)) * 2 ^ j)"
    unfolding r take_bit_eq_mod[symmetric] take_bit_real_sum by (simp add: bit_drop_bit_eq)
  have "drop_bit (q + 1) z div 2 ^ p = drop_bit p (drop_bit (q + 1) z)" by (simp only: drop_bit_eq_div)
  also have "\<dots> = drop_bit (q + 1 + p) z" by (simp add: ac_simps)
  finally have u: "z div 2 div 2 ^ q div 2 ^ p = drop_bit (q + 1 + p) z" unfolding r .
  have "drop_bit (q + 1 + p) z < 2 ^ p"
  proof -
    have e: "q + 1 + 2 * p = (q + 1 + p) + p" by simp
    have "z < 2 ^ ((q + 1 + p) + p)" using z unfolding e .
    hence "z < 2 ^ (q + 1 + p) * 2 ^ p" by (simp only: power_add)
    thus ?thesis by (simp add: drop_bit_eq_div div_less_iff_less_mult ac_simps)
  qed
  hence "take_bit p (drop_bit (q + 1 + p) z) = drop_bit (q + 1 + p) z" by (rule take_bit_nat_eq_self)
  thus "real (z div 2 div 2 ^ q div 2 ^ p) = (\<Sum>j<p. of_bool (bit z (q + 1 + p + j)) * 2 ^ j)"
    unfolding u using take_bit_real_sum[of p "drop_bit (q + 1 + p) z"] by (simp add: bit_drop_bit_eq ac_simps)
qed

subsection \<open>Phase layers\<close>

definition phase_gates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "phase_gates K w \<psi> p = concat (map (\<lambda>j. dgate_gates K (w + j) (\<psi> j)) [0..<p])"

lemma phase_gates_props:
  assumes w: "1 \<le> w" "w + p \<le> K"
  shows "circuit_mat (2 ^ K) (phase_gates K w \<psi> p) = dmat (2 ^ K) (\<lambda>z. \<Sum>j<p. \<psi> j (bit z (w + j)) (bit z 0))"
    "\<forall>U \<in> set (phase_gates K w \<psi> p). elementary (2 ^ K) U" "length (phase_gates K w \<psi> p) \<le> p * (2 * K + 1)"
proof -
  have D: "j < p \<Longrightarrow> circuit_mat (2 ^ K) (dgate_gates K (w + j) (\<psi> j)) = dgate K (w + j) (\<psi> j)
      \<and> (\<forall>U \<in> set (dgate_gates K (w + j) (\<psi> j)). elementary (2 ^ K) U) \<and> length (dgate_gates K (w + j) (\<psi> j)) \<le> 2 * K + 1" for j
    using dgate_gates_props[of "w + j" K "\<psi> j"] w by simp
  have car: "\<And>Us U. Us \<in> set (map (\<lambda>j. dgate_gates K (w + j) (\<psi> j)) [0..<p]) \<Longrightarrow> U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ K) (2 ^ K)"
    using D elementary_unitary(1) by auto
  have "circuit_mat (2 ^ K) (phase_gates K w \<psi> p)
      = circuit_mat (2 ^ K) (map (circuit_mat (2 ^ K)) (map (\<lambda>j. dgate_gates K (w + j) (\<psi> j)) [0..<p]))"
    unfolding phase_gates_def by (rule circuit_mat_concat) (rule car)
  also have "map (circuit_mat (2 ^ K)) (map (\<lambda>j. dgate_gates K (w + j) (\<psi> j)) [0..<p])
      = map (\<lambda>j. dmat (2 ^ K) (\<lambda>z. \<psi> j (bit z (w + j)) (bit z 0))) [0..<p]"
    using D by (auto simp: dgate_def)
  finally show "circuit_mat (2 ^ K) (phase_gates K w \<psi> p) = dmat (2 ^ K) (\<lambda>z. \<Sum>j<p. \<psi> j (bit z (w + j)) (bit z 0))"
    by (simp add: dmat_sum_circ)
  show "\<forall>U \<in> set (phase_gates K w \<psi> p). elementary (2 ^ K) U" using D by (auto simp: phase_gates_def)
  have "length (phase_gates K w \<psi> p) = (\<Sum>j\<leftarrow>[0..<p]. length (dgate_gates K (w + j) (\<psi> j)))"
    by (simp add: phase_gates_def length_concat comp_def)
  also have "\<dots> \<le> (\<Sum>j\<leftarrow>[0..<p]. 2 * K + 1)" by (rule sum_list_mono) (use D in simp)
  finally show "length (phase_gates K w \<psi> p) \<le> p * (2 * K + 1)" by (simp add: sum_list_triv)
qed


subsection \<open>The rotation stage\<close>

lemma zp_carrier [simp]: "zp t \<in> carrier_mat 2 2" and pp_carrier [simp]: "pp t \<in> carrier_mat 2 2"
  by (simp_all add: zp_def pp_def)

lemma rblock_left: "rblock \<theta> \<phi> = pp \<phi> * Hadamard * zp \<theta> * Hadamard * pp (- \<phi>)"
proof -
  note H = hadamard_facts(1)
  have "pp \<phi> * (Hadamard * zp \<theta> * Hadamard) = pp \<phi> * (Hadamard * zp \<theta>) * Hadamard"
    by (rule assoc_mult_mat[OF pp_carrier mult_carrier_mat[OF H zp_carrier] H, symmetric])
  also have "pp \<phi> * (Hadamard * zp \<theta>) = pp \<phi> * Hadamard * zp \<theta>"
    by (rule assoc_mult_mat[OF pp_carrier H zp_carrier, symmetric])
  finally show ?thesis unfolding rblock_def by simp
qed

text \<open>The angle and the phase of register value $c$.\<close>

definition th :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where "th p nn c = ang p (c div nn mod 2 ^ p)"
definition ph :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where "ph p nn c = ang p (c div nn div 2 ^ p)"

lemma ent_mid_layers:
  "ent_mid p nn = ctrl_blocks (2 ^ (2 * p) * nn) 2 (\<lambda>c. pp (ph p nn c)) * ctrl_blocks (2 ^ (2 * p) * nn) 2 (\<lambda>_. Hadamard)
     * ctrl_blocks (2 ^ (2 * p) * nn) 2 (\<lambda>c. zp (th p nn c)) * ctrl_blocks (2 ^ (2 * p) * nn) 2 (\<lambda>_. Hadamard)
     * ctrl_blocks (2 ^ (2 * p) * nn) 2 (\<lambda>c. pp (- ph p nn c))"
proof -
  note H = hadamard_facts(1)
  have c1: "pp a * Hadamard \<in> carrier_mat 2 2" for a by (rule mult_carrier_mat[OF pp_carrier H])
  have c2: "pp a * Hadamard * zp b \<in> carrier_mat 2 2" for a b by (rule mult_carrier_mat[OF c1 zp_carrier])
  have c3: "pp a * Hadamard * zp b * Hadamard \<in> carrier_mat 2 2" for a b by (rule mult_carrier_mat[OF c2 H])
  show ?thesis unfolding ent_mid_def rblock_left th_def[symmetric] ph_def[symmetric]
    by (simp add: ctrl_blocks_mult c1 c2 c3 H)
qed

definition hw :: "nat \<Rightarrow> complex Matrix.mat" where "hw K = 1\<^sub>m (2 ^ (K - 1)) \<Otimes> Hadamard"

text \<open>Applied in time order: $P(-\varphi)$, $H$, $Z(\theta)$, $H$, $P(\varphi)$.\<close>

definition mid_gates :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "mid_gates p q = (let K = q + 1 + 2 * p in
     phase_gates K (q + 1 + p) (\<lambda>j a b. if a \<and> \<not> b then - ang p (2 ^ j) else 0) p @ [hw K]
     @ phase_gates K (q + 1) (\<lambda>j a b. if a then (if b then - ang p (2 ^ j) else ang p (2 ^ j)) else 0) p @ [hw K]
     @ phase_gates K (q + 1 + p) (\<lambda>j a b. if a \<and> \<not> b then ang p (2 ^ j) else 0) p)"


lemma ang_bits: "u < 2 ^ p \<Longrightarrow> ang p u = (\<Sum>j<p. if bit u j then ang p (2 ^ j) else 0)"
proof -
  assume u: "u < 2 ^ p"
  have "real u = (\<Sum>j<p. of_bool (bit u j) * 2 ^ j)" using take_bit_real_sum[of p u] take_bit_nat_eq_self[OF u] by simp
  hence "ang p u = (\<Sum>j<p. of_bool (bit u j) * 2 ^ j) * (2 * pi / 2 ^ p)" unfolding ang_def by simp
  also have "\<dots> = (\<Sum>j<p. if bit u j then ang p (2 ^ j) else 0)" unfolding sum_distrib_right by (intro sum.cong) (auto simp: ang_def)
  finally show ?thesis .
qed

lemma reg_bit:
  fixes z :: nat
  assumes j: "j < p"
  shows "bit (z div 2 div 2 ^ q mod 2 ^ p) j \<longleftrightarrow> bit z (q + 1 + j)"
    "bit (z div 2 div 2 ^ q div 2 ^ p) j \<longleftrightarrow> bit z (q + 1 + p + j)"
proof -
  have r: "z div 2 div 2 ^ q = drop_bit (q + 1) z" by (simp add: drop_bit_eq_div div_mult2_eq power_add ac_simps)
  show "bit (z div 2 div 2 ^ q mod 2 ^ p) j \<longleftrightarrow> bit z (q + 1 + j)"
    unfolding r take_bit_eq_mod[symmetric] using j by (simp add: bit_take_bit_iff bit_drop_bit_eq)
  have "drop_bit (q + 1) z div 2 ^ p = drop_bit p (drop_bit (q + 1) z)" by (simp only: drop_bit_eq_div)
  thus "bit (z div 2 div 2 ^ q div 2 ^ p) j \<longleftrightarrow> bit z (q + 1 + p + j)" unfolding r by (simp add: bit_drop_bit_eq ac_simps)
qed

lemma reg_hi_lt: "z < 2 ^ (q + 1 + 2 * p) \<Longrightarrow> z div 2 div 2 ^ q div 2 ^ p < (2::nat) ^ p"
proof -
  assume z: "z < 2 ^ (q + 1 + 2 * p)"
  have e: "q + 1 + 2 * p = (q + 1 + p) + p" by simp
  have "z < 2 ^ ((q + 1 + p) + p)" using z unfolding e .
  hence "z < 2 ^ (q + 1 + p) * 2 ^ p" by (simp only: power_add)
  hence "z div 2 ^ (q + 1 + p) < 2 ^ p" by (simp add: div_less_iff_less_mult ac_simps)
  moreover have "z div 2 div 2 ^ q div 2 ^ p = z div 2 ^ (q + 1 + p)"
  proof -
    have r: "z div 2 div 2 ^ q = drop_bit (q + 1) z" by (simp add: drop_bit_eq_div div_mult2_eq power_add ac_simps)
    have "drop_bit (q + 1) z div 2 ^ p = drop_bit p (drop_bit (q + 1) z)" by (simp only: drop_bit_eq_div)
    also have "\<dots> = drop_bit (q + 1 + p) z" by (simp add: ac_simps)
    also have "\<dots> = z div 2 ^ (q + 1 + p)" by (simp only: drop_bit_eq_div)
    finally show ?thesis unfolding r .
  qed
  ultimately show ?thesis by simp
qed

theorem mid_gates_props:
  fixes p q :: nat
  defines "K \<equiv> q + 1 + 2 * p"
  shows "circuit_mat (2 ^ K) (mid_gates p q) = ent_mid p (2 ^ q)"
    "\<forall>U \<in> set (mid_gates p q). elementary (2 ^ K) U" "length (mid_gates p q) \<le> 3 * p * (2 * K + 1) + 2"
proof -
  let ?N = "2 ^ (2 * p) * 2 ^ q :: nat"
  have NK: "?N * 2 = 2 ^ K" unfolding K_def by (simp add: power_add ac_simps)
  have K1: "2 ^ K = 2 ^ (K - 1) * (2::nat)" unfolding K_def by simp
  have NK1: "?N = 2 ^ (K - 1)" using NK K1 by simp
  let ?Pm = "phase_gates K (q + 1 + p) (\<lambda>j a b. if a \<and> \<not> b then - ang p (2 ^ j) else 0) p"
  let ?Z = "phase_gates K (q + 1) (\<lambda>j a b. if a then (if b then - ang p (2 ^ j) else ang p (2 ^ j)) else 0) p"
  let ?Pp = "phase_gates K (q + 1 + p) (\<lambda>j a b. if a \<and> \<not> b then ang p (2 ^ j) else 0) p"
  have w: "1 \<le> q + 1 + p" "q + 1 + p + p \<le> K" "1 \<le> q + 1" "q + 1 + p \<le> K" unfolding K_def by simp_all
  note Pm = phase_gates_props[OF w(1,2)] and Z = phase_gates_props[OF w(3,4)] and Pp = phase_gates_props[OF w(1,2)]
  have eh: "elementary (2 ^ K) (hw K)"
  proof -
    have "gate 1 Hadamard" using H_is_gate by (simp add: Hadamard_def)
    from elementary_left[OF elementary_gate[OF this], of "2 ^ (K - 1)"] show ?thesis unfolding hw_def K1 by simp
  qed
  have hc: "hw K \<in> carrier_mat (2 ^ K) (2 ^ K)" by (rule elementary_unitary(1)[OF eh])
  have car: "\<And>Us. \<forall>U \<in> set Us. elementary (2 ^ K) U \<Longrightarrow> (\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ K) (2 ^ K))"
    using elementary_unitary(1) by blast
  have elall: "\<forall>U \<in> set (mid_gates p q). elementary (2 ^ K) U"
    using Pm(2) Z(2) Pp(2) eh unfolding K_def by (auto simp: mid_gates_def Let_def)
  thus "\<forall>U \<in> set (mid_gates p q). elementary (2 ^ K) U" .
  have "length (mid_gates p q) = length ?Pm + length ?Z + length ?Pp + 2"
    unfolding mid_gates_def Let_def K_def[symmetric] by simp
  moreover have "3 * p * (2 * K + 1) = 3 * (p * (2 * K + 1))" by simp
  ultimately show "length (mid_gates p q) \<le> 3 * p * (2 * K + 1) + 2"
    using Pm(3)[of "\<lambda>j a b. if a \<and> \<not> b then - ang p (2 ^ j) else 0"]
      Z(3)[of "\<lambda>j a b. if a then (if b then - ang p (2 ^ j) else ang p (2 ^ j)) else 0"]
      Pp(3)[of "\<lambda>j a b. if a \<and> \<not> b then ang p (2 ^ j) else 0"] by linarith
  \<comment> \<open>the circuit, layer by layer\<close>
  have "circuit_mat (2 ^ K) (mid_gates p q) = circuit_mat (2 ^ K) ?Pp * hw K * circuit_mat (2 ^ K) ?Z * hw K * circuit_mat (2 ^ K) ?Pm"
  proof -
    have a4: "circuit_mat (2 ^ K) ([hw K] @ ?Pp) = circuit_mat (2 ^ K) ?Pp * hw K"
      using circuit_mat_append[OF _ car[OF Pp(2)], of "[hw K]"] hc by (simp add: circuit_mat_single)
    have a3: "circuit_mat (2 ^ K) (?Z @ [hw K] @ ?Pp) = circuit_mat (2 ^ K) ([hw K] @ ?Pp) * circuit_mat (2 ^ K) ?Z"
      by (rule circuit_mat_append) (use car[OF Z(2)] car[OF Pp(2)] hc in auto)
    have a2: "circuit_mat (2 ^ K) ([hw K] @ ?Z @ [hw K] @ ?Pp) = circuit_mat (2 ^ K) (?Z @ [hw K] @ ?Pp) * hw K"
      using circuit_mat_append[of "[hw K]" "2 ^ K" "?Z @ [hw K] @ ?Pp"] hc car[OF Z(2)] car[OF Pp(2)] by (auto simp: circuit_mat_single)
    have a1: "circuit_mat (2 ^ K) (?Pm @ [hw K] @ ?Z @ [hw K] @ ?Pp) = circuit_mat (2 ^ K) ([hw K] @ ?Z @ [hw K] @ ?Pp) * circuit_mat (2 ^ K) ?Pm"
      by (rule circuit_mat_append) (use car[OF Pm(2)] car[OF Z(2)] car[OF Pp(2)] hc in auto)
    show ?thesis unfolding mid_gates_def Let_def K_def[symmetric] a1 a2 a3 a4 ..
  qed
  also have "\<dots> = ent_mid p (2 ^ q)"
  proof -
    have l1: "ctrl_blocks ?N 2 (\<lambda>c. pp (ph p (2 ^ q) c)) = circuit_mat (2 ^ K) ?Pp"
    proof -
      have "ctrl_blocks ?N 2 (\<lambda>c. pp (ph p (2 ^ q) c)) = dmat (2 ^ K) (\<lambda>x. if x mod 2 = 0 then ph p (2 ^ q) (x div 2) else 0)"
        unfolding pp_def ctrl_dmat NK by (rule dmat_cong) simp
      also have "\<dots> = circuit_mat (2 ^ K) ?Pp" unfolding Pp(1)
      proof (rule dmat_cong)
        fix x :: nat assume x: "x < 2 ^ K"
        show "(if x mod 2 = 0 then ph p (2 ^ q) (x div 2) else 0)
            = (\<Sum>j<p. if bit x (q + 1 + p + j) \<and> \<not> bit x 0 then ang p (2 ^ j) else 0)"
          using reg_hi_lt[of x q p] x unfolding K_def
          by (auto simp: ph_def ang_bits reg_bit bit_0 even_iff_mod_2_eq_zero intro!: sum.cong)
      qed
      finally show ?thesis .
    qed
    have l2: "ctrl_blocks ?N 2 (\<lambda>c. zp (th p (2 ^ q) c)) = circuit_mat (2 ^ K) ?Z"
    proof -
      have "ctrl_blocks ?N 2 (\<lambda>c. zp (th p (2 ^ q) c)) = dmat (2 ^ K) (\<lambda>x. if x mod 2 = 0 then th p (2 ^ q) (x div 2) else - th p (2 ^ q) (x div 2))"
        unfolding zp_def ctrl_dmat NK by (rule dmat_cong) simp
      also have "\<dots> = circuit_mat (2 ^ K) ?Z" unfolding Z(1)
      proof (rule dmat_cong)
        fix x :: nat assume x: "x < 2 ^ K"
        show "(if x mod 2 = 0 then th p (2 ^ q) (x div 2) else - th p (2 ^ q) (x div 2))
            = (\<Sum>j<p. if bit x (q + 1 + j) then (if bit x 0 then - ang p (2 ^ j) else ang p (2 ^ j)) else 0)"
          by (auto simp: th_def ang_bits reg_bit bit_0 even_iff_mod_2_eq_zero sum_negf[symmetric] intro!: sum.cong)
      qed
      finally show ?thesis .
    qed
    have l3: "ctrl_blocks ?N 2 (\<lambda>c. pp (- ph p (2 ^ q) c)) = circuit_mat (2 ^ K) ?Pm"
    proof -
      have "ctrl_blocks ?N 2 (\<lambda>c. pp (- ph p (2 ^ q) c)) = dmat (2 ^ K) (\<lambda>x. if x mod 2 = 0 then - ph p (2 ^ q) (x div 2) else 0)"
        unfolding pp_def ctrl_dmat NK by (rule dmat_cong) simp
      also have "\<dots> = circuit_mat (2 ^ K) ?Pm" unfolding Pm(1)
      proof (rule dmat_cong)
        fix x :: nat assume x: "x < 2 ^ K"
        show "(if x mod 2 = 0 then - ph p (2 ^ q) (x div 2) else 0)
            = (\<Sum>j<p. if bit x (q + 1 + p + j) \<and> \<not> bit x 0 then - ang p (2 ^ j) else 0)"
          using reg_hi_lt[of x q p] x unfolding K_def
          by (auto simp: ph_def ang_bits reg_bit bit_0 even_iff_mod_2_eq_zero sum_negf[symmetric] intro!: sum.cong)
      qed
      finally show ?thesis .
    qed
    have lh: "ctrl_blocks ?N 2 (\<lambda>_. Hadamard) = hw K"
      unfolding hw_def NK1[symmetric] by (rule ctrl_blocks_const) (simp_all add: hadamard_facts)
    show ?thesis unfolding ent_mid_layers l1 l2 l3 lh ..
  qed
  finally show "circuit_mat (2 ^ K) (mid_gates p q) = ent_mid p (2 ^ q)" .
qed

end
