theory Prep_Angle_Oracle
  imports Prep_Rounded
begin

section \<open>State preparation from an angle oracle\<close>

subsection \<open>Oracles above larger blocks\<close>

definition oracle_m :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "oracle_m q nn M f = pmat (2 ^ q * nn) (xreg nn f) \<Otimes> 1\<^sub>m M"

lemma oracle_m_stands_for:
  assumes f: "\<And>k. k < nn \<Longrightarrow> f k < 2 ^ q" and B: "\<And>r. B r \<in> carrier_mat M M" and M: "0 < M"
  shows "stands_for (2 ^ q) (nn * M)
    (oracle_m q nn M f * ctrl_blocks (2 ^ q * nn) M (\<lambda>c. B (c div nn)) * oracle_m q nn M f)
    (ctrl_blocks nn M (\<lambda>k. B (f k)))"
proof -
  let ?R = "2 ^ q :: nat"
  have e: "oracle_m q nn M f * ctrl_blocks (?R * nn) M (\<lambda>c. B (c div nn)) * oracle_m q nn M f
      = ctrl_blocks (?R * nn) M (\<lambda>c. B (xreg nn f c div nn))"
    unfolding oracle_m_def by (rule ctrl_conj) (simp_all add: xreg_props[OF f] B)
  have U: "ctrl_blocks (?R * nn) M (\<lambda>c. B (xreg nn f c div nn)) \<in> carrier_mat (?R * (nn * M)) (?R * (nn * M))"
    using ctrl_blocks_carrier[of "?R * nn" M] by (simp only: Groups.mult.assoc)
  have G: "ctrl_blocks nn M (\<lambda>k. B (f k)) \<in> carrier_mat (nn * M) (nn * M)" by (rule ctrl_blocks_carrier)
  have xk: "xreg nn f k div nn = f k" if "k < nn" for k using that by (simp add: xreg_def)
  have "ctrl_blocks (?R * nn) M (\<lambda>c. B (xreg nn f c div nn)) $$ (r, c) = (if r < nn * M then ctrl_blocks nn M (\<lambda>k. B (f k)) $$ (r, c) else 0)"
    if "r < ?R * (nn * M)" "c < nn * M" for r c
  proof -
    have k: "c div M < nn" using that(2) M by (simp add: div_less_iff_less_mult)
    have rc: "r < ?R * nn * M" using that(1) by (simp only: Groups.mult.assoc)
    have "nn * M \<le> ?R * (nn * M)" using mult_le_mono1[of 1 ?R "nn * M"] by simp
    hence "c < ?R * (nn * M)" using that(2) by linarith
    hence cR: "c < ?R * nn * M" by (simp only: Groups.mult.assoc)
    show ?thesis
    proof (cases "r < nn * M")
      case True
      thus ?thesis using that k xk[OF k] rc cR by (auto simp: ctrl_blocks_index)
    next
      case False
      hence "nn \<le> r div M" using M by (simp add: less_eq_div_iff_mult_less_eq not_less)
      hence "r div M \<noteq> c div M" using k by auto
      thus ?thesis using False that rc cR by (simp add: ctrl_blocks_index)
    qed
  qed
  hence "stands_for ?R (nn * M) (ctrl_blocks (?R * nn) M (\<lambda>c. B (xreg nn f c div nn))) (ctrl_blocks nn M (\<lambda>k. B (f k)))"
    using stands_for_iff[OF U G] by simp
  thus ?thesis unfolding e .
qed

subsection \<open>Two-qubit diagonal gates on any two wires\<close>

definition dgate2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> real) \<Rightarrow> complex Matrix.mat" where
  "dgate2 K c w \<psi> = dmat (2 ^ K) (\<lambda>z. \<psi> (bit z c) (bit z w))"

definition dgate2_gates :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list" where
  "dgate2_gates K c w \<psi> = map (cgate K 1) (swops (dn c (w + 1)))
     @ [1\<^sub>m (2 ^ (K - (w + 2))) \<Otimes> (dmat 4 (\<lambda>d. \<psi> (bit d 1) (bit d 0)) \<Otimes> 1\<^sub>m (2 ^ w))]
     @ map (cgate K 1) (swops (rev (dn c (w + 1))))"

lemma dmat_tensor_one_gen:
  assumes h: "0 < h"
  shows "dmat N \<alpha> \<Otimes> 1\<^sub>m h = dmat (N * h) (\<lambda>x. \<alpha> (x div h))"
proof (rule eq_matI)
  fix r t assume "r < dim_row (dmat (N * h) (\<lambda>x. \<alpha> (x div h)))" "t < dim_col (dmat (N * h) (\<lambda>x. \<alpha> (x div h)))"
  hence rt: "r < N * h" "t < N * h" by (simp_all add: dmat_def mat_diag_def)
  have N0: "0 < N" using rt by (cases N) auto
  have q: "r = t \<longleftrightarrow> r div h = t div h \<and> r mod h = t mod h"
  proof
    assume e: "r div h = t div h \<and> r mod h = t mod h"
    have "r = r div h * h + r mod h" by simp
    also have "\<dots> = t div h * h + t mod h" using e by simp
    also have "\<dots> = t" by simp
    finally show "r = t" .
  qed simp
  have "(dmat N \<alpha> \<Otimes> 1\<^sub>m h) $$ (r, t) = dmat N \<alpha> $$ (r div h, t div h) * 1\<^sub>m h $$ (r mod h, t mod h)"
    using index_tensor_mat[of "dmat N \<alpha>" N N "1\<^sub>m h" h h r t] rt N0 h by (simp add: dmat_def mat_diag_def)
  also have "\<dots> = dmat (N * h) (\<lambda>x. \<alpha> (x div h)) $$ (r, t)"
    using rt q h by (auto simp: dmat_def mat_diag_def div_less_iff_less_mult)
  finally show "(dmat N \<alpha> \<Otimes> 1\<^sub>m h) $$ (r, t) = dmat (N * h) (\<lambda>x. \<alpha> (x div h)) $$ (r, t)" .
qed (simp_all add: dmat_def mat_diag_def)

theorem dgate2_gates_props:
  assumes c: "w < c" "c < K"
  shows "circuit_mat (2 ^ K) (dgate2_gates K c w \<psi>) = dgate2 K c w \<psi>"
    "\<forall>U \<in> set (dgate2_gates K c w \<psi>). elementary (2 ^ K) U" "length (dgate2_gates K c w \<psi>) \<le> 2 * K + 1"
proof -
  let ?js = "dn c (w + 1)" and ?\<psi>' = "\<lambda>d :: nat. \<psi> (bit d 1) (bit d 0)" and ?h = "2 ^ w :: nat"
  have rj: "\<And>j. j \<in> set ?js \<Longrightarrow> j + 2 \<le> K" using c by (auto simp: dn_def)
  have rj': "\<And>j. j \<in> set (rev ?js) \<Longrightarrow> j + 2 \<le> K" using rj by simp
  note A = swops_circuit[OF rj] and C = swops_circuit[OF rj']
  have K4: "(2::nat) ^ K = 2 ^ (K - (w + 2)) * (4 * 2 ^ w)"
  proof -
    have k2: "K = (K - (w + 2)) + (w + 2)" using c by simp
    have "(2::nat) ^ K = 2 ^ (K - (w + 2)) * 2 ^ (w + 2)" by (subst (1) k2) (rule power_add)
    thus ?thesis by (simp add: power_add ac_simps)
  qed
  let ?D = "1\<^sub>m (2 ^ (K - (w + 2))) \<Otimes> (dmat 4 ?\<psi>' \<Otimes> 1\<^sub>m ?h)"
  have D: "?D = dmat (2 ^ K) (\<lambda>z. ?\<psi>' (z div ?h mod 4))"
  proof -
    have "?D = 1\<^sub>m (2 ^ (K - (w + 2))) \<Otimes> dmat (4 * ?h) (\<lambda>x. ?\<psi>' (x div ?h))" by (simp add: dmat_tensor_one_gen)
    also have "\<dots> = dmat (2 ^ (K - (w + 2)) * (4 * ?h)) (\<lambda>z. ?\<psi>' (z mod (4 * ?h) div ?h))" by (rule one_tensor_dmat) simp_all
    also have "\<dots> = dmat (2 ^ K) (\<lambda>z. ?\<psi>' (z div ?h mod 4))"
    proof -
      have md: "x mod (4 * ?h) div ?h = x div ?h mod 4" for x :: nat
      proof -
        have "x mod (?h * 4) = ?h * (x div ?h mod 4) + x mod ?h" by (rule mod_mult2_eq)
        hence "x mod (4 * ?h) = ?h * (x div ?h mod 4) + x mod ?h" by (simp only: Groups.mult.commute[of 4 ?h])
        thus ?thesis by simp
      qed
      show ?thesis unfolding K4[symmetric] by (rule dmat_cong) (simp only: md)
    qed
    finally show ?thesis .
  qed
  have Dc: "?D \<in> carrier_mat (2 ^ K) (2 ^ K)" unfolding D by (rule dmat_carrier)
  have eD: "elementary (2 ^ K) ?D"
  proof -
    show ?thesis unfolding elementary_def K4
      by (rule exI[of _ "2 ^ (K - (w + 2))"], rule exI[of _ ?h], rule exI[of _ 2], rule exI[of _ "dmat 4 ?\<psi>'"]) (simp add: dmat_unitary)
  qed
  let ?f = "apply_ops (swops ?js)" and ?g = "apply_ops (swops (rev ?js))"
  have f: "\<And>t. t < 2 ^ K \<Longrightarrow> ?f t < 2 ^ K" by (rule apply_ops_lt) (use rj in auto)
  have g: "\<And>t. t < 2 ^ K \<Longrightarrow> ?g t < 2 ^ K" by (rule apply_ops_lt) (use rj' in auto)
  have gf: "\<And>t. ?g (?f t) = t" using apply_ops_rev[of "swops ?js"] by (simp add: rev_map)
  have bits: "?\<psi>' (?f z div ?h mod 4) = \<psi> (bit z c) (bit z w)" for z
  proof -
    have "pm ?js (w + 1) = c" "pm ?js w = w" using c by (simp_all add: pm_dn)
    moreover have "bit (?f z div ?h mod 4) 1 \<longleftrightarrow> bit (?f z) (w + 1)" "bit (?f z div ?h mod 4) 0 \<longleftrightarrow> bit (?f z) w"
      using bit_digit[of 1 "?f z" w] bit_digit[of 0 "?f z" w] by simp_all
    ultimately show ?thesis by (simp add: bit_swops)
  qed
  have e1: "circuit_mat (2 ^ K) (dgate2_gates K c w \<psi>)
      = circuit_mat (2 ^ K) (map (cgate K 1) (swops (rev ?js))) * ?D * circuit_mat (2 ^ K) (map (cgate K 1) (swops ?js))"
  proof -
    have a1: "circuit_mat (2 ^ K) (map (cgate K 1) (swops ?js) @ [?D] @ map (cgate K 1) (swops (rev ?js)))
        = circuit_mat (2 ^ K) ([?D] @ map (cgate K 1) (swops (rev ?js))) * circuit_mat (2 ^ K) (map (cgate K 1) (swops ?js))"
      by (rule circuit_mat_append) (use A(2) C(2) Dc elementary_carrier in auto)
    have a2: "circuit_mat (2 ^ K) ([?D] @ map (cgate K 1) (swops (rev ?js)))
        = circuit_mat (2 ^ K) (map (cgate K 1) (swops (rev ?js))) * circuit_mat (2 ^ K) [?D]"
      by (rule circuit_mat_append) (use C(2) Dc elementary_carrier in auto)
    show ?thesis unfolding dgate2_gates_def a1 a2 circuit_mat_single[OF Dc] ..
  qed
  have e2: "circuit_mat (2 ^ K) (dgate2_gates K c w \<psi>) = pmat (2 ^ K) ?g * ?D * pmat (2 ^ K) ?f"
    unfolding e1 by (simp only: A(1) C(1))
  have "pmat (2 ^ K) ?g * dmat (2 ^ K) (\<lambda>z. ?\<psi>' (z div ?h mod 4)) * pmat (2 ^ K) ?f
      = dmat (2 ^ K) (\<lambda>t. ?\<psi>' (?f t div ?h mod 4))" by (rule pmat_dmat_conj[OF f g gf])
  also have "\<dots> = dmat (2 ^ K) (\<lambda>z. \<psi> (bit z c) (bit z w))" by (simp only: bits)
  finally show "circuit_mat (2 ^ K) (dgate2_gates K c w \<psi>) = dgate2 K c w \<psi>" unfolding e2 D dgate2_def .
  show "\<forall>U \<in> set (dgate2_gates K c w \<psi>). elementary (2 ^ K) U" using A(2) C(2) eD by (auto simp: dgate2_gates_def)
  show "length (dgate2_gates K c w \<psi>) \<le> 2 * K + 1" using c by (simp add: dgate2_gates_def)
qed

subsection \<open>One level of the cascade\<close>

text \<open>Level $j$ rotates data wire $w = k - 1 - j$ by the angle that the oracle writes into a
$b$-bit register above the $k$ data wires.  Since $\mathrm{Rot}(\theta) = Q\,\mathrm{diag}(-\theta, \theta)\,Q^\dagger$,
the rotation is a one-wire gate, a diagonal, and a one-wire gate; the diagonal splits into one
two-wire phase per register bit.\<close>

definition qw :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "qw K w G = 1\<^sub>m (2 ^ (K - Suc w)) \<Otimes> (G \<Otimes> 1\<^sub>m (2 ^ w))"

lemma qw_elementary:
  assumes w: "w < K" and G: "G \<in> carrier_mat 2 2" "Quantum.unitary G"
  shows "elementary (2 ^ K) (qw K w G)"
proof -
  have "(2::nat) ^ (K - Suc w) * (2 ^ 1 * 2 ^ w) = 2 ^ (K - Suc w + (1 + w))" by (simp only: power_add)
  also have "K - Suc w + (1 + w) = K" using w by simp
  finally have e: "(2::nat) ^ K = 2 ^ (K - Suc w) * (2 ^ 1 * 2 ^ w)" ..
  show ?thesis unfolding elementary_def qw_def
    by (rule exI[of _ "2 ^ (K - Suc w)"], rule exI[of _ "2 ^ w"], rule exI[of _ 1], rule exI[of _ G]) (simp add: G e)
qed

lemma ctrl_dmat_gen:
  assumes M: "0 < M"
  shows "ctrl_blocks N M (\<lambda>c. dmat M (\<psi> c)) = dmat (N * M) (\<lambda>x. \<psi> (x div M) (x mod M))"
proof (rule eq_matI)
  fix r t assume "r < dim_row (dmat (N * M) (\<lambda>x. \<psi> (x div M) (x mod M)))" "t < dim_col (dmat (N * M) (\<lambda>x. \<psi> (x div M) (x mod M)))"
  hence rt: "r < N * M" "t < N * M" by (simp_all add: dmat_def mat_diag_def)
  have q: "r = t \<longleftrightarrow> r div M = t div M \<and> r mod M = t mod M"
  proof
    assume e: "r div M = t div M \<and> r mod M = t mod M"
    have "r = r div M * M + r mod M" by simp
    also have "\<dots> = t div M * M + t mod M" using e by simp
    also have "\<dots> = t" by simp
    finally show "r = t" .
  qed simp
  show "ctrl_blocks N M (\<lambda>c. dmat M (\<psi> c)) $$ (r, t) = dmat (N * M) (\<lambda>x. \<psi> (x div M) (x mod M)) $$ (r, t)"
    using rt q M by (auto simp: ctrl_blocks_index dmat_def mat_diag_def)
qed (simp_all add: dmat_def mat_diag_def)

definition rot_phase :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> real" where
  "rot_phase b i r t = (if t then 1 else - 1) * (if r then ang b (2 ^ i) else 0)"

lemma lev_phase:
  fixes z :: nat
  assumes z: "z < 2 ^ (b + k)"
  shows "(\<Sum>i<b. rot_phase b i (bit z (k + i)) (bit z w)) = (if bit z w then 1 else - 1) * ang b (z div 2 ^ k)"
proof -
  have r: "z div 2 ^ k = drop_bit k z" by (simp add: drop_bit_eq_div)
  have "z < 2 ^ k * 2 ^ b" using z by (simp add: power_add ac_simps)
  hence lt: "drop_bit k z < 2 ^ b" by (simp add: drop_bit_eq_div div_less_iff_less_mult ac_simps)
  show ?thesis unfolding r ang_bits[OF lt] rot_phase_def by (simp add: sum_distrib_left bit_drop_bit_eq)
qed

definition lev_mid :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "lev_mid b k j = [qw (b + k) (k - Suc j) (Qm\<^sup>\<dagger>)]
     @ concat (map (\<lambda>i. dgate2_gates (b + k) (k + i) (k - Suc j) (rot_phase b i)) [0..<b])
     @ [qw (b + k) (k - Suc j) Qm]"

lemma lev_mid_props:
  assumes j: "j < k"
  shows "circuit_mat (2 ^ (b + k)) (lev_mid b k j)
      = ctrl_blocks (2 ^ b * 2 ^ j) (2 * 2 ^ (k - Suc j)) (\<lambda>c. Rot (ang b (c div 2 ^ j)) \<Otimes> 1\<^sub>m (2 ^ (k - Suc j)))"
    "\<forall>U \<in> set (lev_mid b k j). elementary (2 ^ (b + k)) U" "length (lev_mid b k j) \<le> b * (2 * (b + k) + 1) + 2"
proof -
  let ?K = "b + k" and ?w = "k - Suc j" and ?N = "2 ^ b * 2 ^ j :: nat" and ?h = "2 ^ (k - Suc j) :: nat"
  let ?L = "concat (map (\<lambda>i. dgate2_gates ?K (k + i) ?w (rot_phase b i)) [0..<b])"
  have D: "i < b \<Longrightarrow> circuit_mat (2 ^ ?K) (dgate2_gates ?K (k + i) ?w (rot_phase b i)) = dgate2 ?K (k + i) ?w (rot_phase b i)
      \<and> (\<forall>U \<in> set (dgate2_gates ?K (k + i) ?w (rot_phase b i)). elementary (2 ^ ?K) U)
      \<and> length (dgate2_gates ?K (k + i) ?w (rot_phase b i)) \<le> 2 * ?K + 1" for i
    using dgate2_gates_props[of ?w "k + i" ?K "rot_phase b i"] j by simp
  have Lc: "\<And>U. U \<in> set ?L \<Longrightarrow> U \<in> carrier_mat (2 ^ ?K) (2 ^ ?K)" using D elementary_carrier by auto
  have L: "circuit_mat (2 ^ ?K) ?L = dmat (2 ^ ?K) (\<lambda>z. \<Sum>i<b. rot_phase b i (bit z (k + i)) (bit z ?w))"
  proof -
    have "circuit_mat (2 ^ ?K) ?L
        = circuit_mat (2 ^ ?K) (map (circuit_mat (2 ^ ?K)) (map (\<lambda>i. dgate2_gates ?K (k + i) ?w (rot_phase b i)) [0..<b]))"
      by (rule circuit_mat_concat) (use D elementary_carrier in auto)
    also have "map (circuit_mat (2 ^ ?K)) (map (\<lambda>i. dgate2_gates ?K (k + i) ?w (rot_phase b i)) [0..<b])
        = map (\<lambda>i. dmat (2 ^ ?K) (\<lambda>z. rot_phase b i (bit z (k + i)) (bit z ?w))) [0..<b]"
      using D by (auto simp: dgate2_def)
    finally show ?thesis by (simp add: dmat_sum_circ)
  qed
  have Qc: "Qm \<in> carrier_mat 2 2" and Qu: "Quantum.unitary Qm" by (simp_all add: Qm_unitary)
  have Qd: "Qm\<^sup>\<dagger> \<in> carrier_mat 2 2" "Quantum.unitary (Qm\<^sup>\<dagger>)" by (rule dagger_carrier[OF Qc]) (rule unitary_dagger[OF Qu])
  have w: "?w < ?K" using j by simp
  have h0: "0 < ?h" by simp
  have KN: "(2::nat) ^ ?K = ?N * (2 * ?h)"
  proof -
    have "(2::nat) ^ ?K = 2 ^ b * (2 ^ j * (2 * ?h))" unfolding lev_dim[OF j] by (simp only: power_add)
    thus ?thesis by (simp only: Groups.mult.assoc)
  qed
  have q: "qw ?K ?w G = 1\<^sub>m ?N \<Otimes> (G \<Otimes> 1\<^sub>m ?h)" for G
  proof -
    have "?K - Suc ?w = b + j" using j by simp
    thus ?thesis unfolding qw_def by (simp add: power_add)
  qed
  have T: "G \<in> carrier_mat 2 2 \<Longrightarrow> G \<Otimes> 1\<^sub>m ?h \<in> carrier_mat (2 * ?h) (2 * ?h)" for G by simp
  have qc: "G \<in> carrier_mat 2 2 \<Longrightarrow> qw ?K ?w G \<in> carrier_mat (2 ^ ?K) (2 ^ ?K)" for G unfolding q KN by simp
  let ?D = "\<lambda>c. dmat 2 (\<lambda>a. if a = 0 then - ang b (c div 2 ^ j) else ang b (c div 2 ^ j))"
  have I: "1\<^sub>m ?h * 1\<^sub>m ?h = (1\<^sub>m ?h :: complex Matrix.mat)" by (rule left_mult_one_mat[OF one_carrier_mat])
  have blk: "Rot (ang b (c div 2 ^ j)) \<Otimes> 1\<^sub>m ?h = (Qm \<Otimes> 1\<^sub>m ?h) * (?D c \<Otimes> 1\<^sub>m ?h) * (Qm\<^sup>\<dagger> \<Otimes> 1\<^sub>m ?h)" for c
  proof -
    have x1: "dim_col (Qm * ?D c) = 2" by (simp only: index_mult_mat(3) carrier_matD(2)[OF dmat_carrier])
    note dd = x1 carrier_matD[OF Qc] carrier_matD[OF Qd(1)] carrier_matD[OF dmat_carrier] index_one_mat(2,3)
    have t1: "(Qm * ?D c * (Qm\<^sup>\<dagger>)) \<Otimes> (1\<^sub>m ?h * 1\<^sub>m ?h) = ((Qm * ?D c) \<Otimes> 1\<^sub>m ?h) * (Qm\<^sup>\<dagger> \<Otimes> 1\<^sub>m ?h)"
      by (rule mult_distr_tensor) (unfold dd, simp_all)
    have t2: "(Qm * ?D c) \<Otimes> (1\<^sub>m ?h * 1\<^sub>m ?h) = (Qm \<Otimes> 1\<^sub>m ?h) * (?D c \<Otimes> 1\<^sub>m ?h)"
      by (rule mult_distr_tensor) (unfold dd, simp_all)
    show ?thesis unfolding Rot_dmat t1[unfolded I] t2[unfolded I] ..
  qed
  have A: "Qm \<Otimes> 1\<^sub>m ?h \<in> carrier_mat (2 * ?h) (2 * ?h)" by (rule T[OF Qc])
  have B: "?D c \<Otimes> 1\<^sub>m ?h \<in> carrier_mat (2 * ?h) (2 * ?h)" for c by (rule T[OF dmat_carrier])
  have C: "Qm\<^sup>\<dagger> \<Otimes> 1\<^sub>m ?h \<in> carrier_mat (2 * ?h) (2 * ?h)" by (rule T[OF Qd(1)])
  have AB: "(Qm \<Otimes> 1\<^sub>m ?h) * (?D c \<Otimes> 1\<^sub>m ?h) \<in> carrier_mat (2 * ?h) (2 * ?h)" for c by (rule mult_carrier_mat[OF A B])
  have m1: "ctrl_blocks ?N (2 * ?h) (\<lambda>_. Qm \<Otimes> 1\<^sub>m ?h) * ctrl_blocks ?N (2 * ?h) (\<lambda>c. ?D c \<Otimes> 1\<^sub>m ?h)
      = ctrl_blocks ?N (2 * ?h) (\<lambda>c. (Qm \<Otimes> 1\<^sub>m ?h) * (?D c \<Otimes> 1\<^sub>m ?h))"
    by (rule ctrl_blocks_mult) (simp_all only: A B)
  have m2: "ctrl_blocks ?N (2 * ?h) (\<lambda>c. (Qm \<Otimes> 1\<^sub>m ?h) * (?D c \<Otimes> 1\<^sub>m ?h)) * ctrl_blocks ?N (2 * ?h) (\<lambda>_. Qm\<^sup>\<dagger> \<Otimes> 1\<^sub>m ?h)
      = ctrl_blocks ?N (2 * ?h) (\<lambda>c. (Qm \<Otimes> 1\<^sub>m ?h) * (?D c \<Otimes> 1\<^sub>m ?h) * (Qm\<^sup>\<dagger> \<Otimes> 1\<^sub>m ?h))"
    by (rule ctrl_blocks_mult) (simp_all only: AB C)
  have c1: "ctrl_blocks ?N (2 * ?h) (\<lambda>_. G \<Otimes> 1\<^sub>m ?h) = qw ?K ?w G" if "G \<in> carrier_mat 2 2" for G
    unfolding q by (rule ctrl_blocks_const[OF T[OF that]]) simp
  have d: "z div (2 * ?h) div 2 ^ j = z div 2 ^ k" for z :: nat
  proof -
    have "2 * ?h * 2 ^ j = (2::nat) ^ k" using lev_dim[OF j] by (simp only: Groups.mult.commute[of "2 * ?h" "2 ^ j"])
    thus ?thesis by (simp only: div_mult2_eq[symmetric])
  qed
  have m: "z mod (2 * ?h) div ?h = 0 \<longleftrightarrow> \<not> bit z ?w" for z :: nat
  proof -
    have "z mod (?h * 2) = ?h * (z div ?h mod 2) + z mod ?h" by (rule mod_mult2_eq)
    hence "z mod (2 * ?h) = ?h * (z div ?h mod 2) + z mod ?h" by (simp only: Groups.mult.commute[of 2 ?h])
    hence "z mod (2 * ?h) div ?h = z div ?h mod 2" by simp
    thus ?thesis by (simp add: bit_iff_odd even_iff_mod_2_eq_zero)
  qed
  have c2: "ctrl_blocks ?N (2 * ?h) (\<lambda>c. ?D c \<Otimes> 1\<^sub>m ?h) = dmat (2 ^ ?K) (\<lambda>z. \<Sum>i<b. rot_phase b i (bit z (k + i)) (bit z ?w))"
  proof -
    have "ctrl_blocks ?N (2 * ?h) (\<lambda>c. ?D c \<Otimes> 1\<^sub>m ?h)
        = ctrl_blocks ?N (2 * ?h) (\<lambda>c. dmat (2 * ?h) (\<lambda>x. if x div ?h = 0 then - ang b (c div 2 ^ j) else ang b (c div 2 ^ j)))"
      by (simp only: dmat_tensor_one_gen[OF h0])
    also have "\<dots> = dmat (?N * (2 * ?h)) (\<lambda>z. if z mod (2 * ?h) div ?h = 0 then - ang b (z div (2 * ?h) div 2 ^ j)
        else ang b (z div (2 * ?h) div 2 ^ j))"
      by (rule ctrl_dmat_gen) simp
    also have "\<dots> = dmat (2 ^ ?K) (\<lambda>z. \<Sum>i<b. rot_phase b i (bit z (k + i)) (bit z ?w))"
      unfolding KN[symmetric] by (rule dmat_cong) (simp only: d m, simp add: lev_phase)
    finally show ?thesis .
  qed
  have e: "circuit_mat (2 ^ ?K) (lev_mid b k j) = qw ?K ?w Qm * circuit_mat (2 ^ ?K) ?L * qw ?K ?w (Qm\<^sup>\<dagger>)"
  proof -
    have a1: "circuit_mat (2 ^ ?K) ([qw ?K ?w (Qm\<^sup>\<dagger>)] @ ?L @ [qw ?K ?w Qm])
        = circuit_mat (2 ^ ?K) (?L @ [qw ?K ?w Qm]) * qw ?K ?w (Qm\<^sup>\<dagger>)"
      using circuit_mat_append[of "[qw ?K ?w (Qm\<^sup>\<dagger>)]" "2 ^ ?K" "?L @ [qw ?K ?w Qm]"] qc[OF Qc] qc[OF Qd(1)] Lc
      by (auto simp: circuit_mat_single)
    have a2: "circuit_mat (2 ^ ?K) (?L @ [qw ?K ?w Qm]) = qw ?K ?w Qm * circuit_mat (2 ^ ?K) ?L"
      using circuit_mat_append[of ?L "2 ^ ?K" "[qw ?K ?w Qm]"] qc[OF Qc] Lc by (auto simp: circuit_mat_single)
    show ?thesis unfolding lev_mid_def a1 a2 ..
  qed
  have "ctrl_blocks ?N (2 * ?h) (\<lambda>c. Rot (ang b (c div 2 ^ j)) \<Otimes> 1\<^sub>m ?h)
      = ctrl_blocks ?N (2 * ?h) (\<lambda>_. Qm \<Otimes> 1\<^sub>m ?h) * ctrl_blocks ?N (2 * ?h) (\<lambda>c. ?D c \<Otimes> 1\<^sub>m ?h)
        * ctrl_blocks ?N (2 * ?h) (\<lambda>_. Qm\<^sup>\<dagger> \<Otimes> 1\<^sub>m ?h)"
    unfolding blk m1 m2 ..
  also have "\<dots> = circuit_mat (2 ^ ?K) (lev_mid b k j)" unfolding c1[OF Qc] c1[OF Qd(1)] c2 e L ..
  finally show "circuit_mat (2 ^ (b + k)) (lev_mid b k j)
      = ctrl_blocks ?N (2 * ?h) (\<lambda>c. Rot (ang b (c div 2 ^ j)) \<Otimes> 1\<^sub>m ?h)" by (rule sym)
  show "\<forall>U \<in> set (lev_mid b k j). elementary (2 ^ (b + k)) U"
    using D qw_elementary[OF w Qc Qu] qw_elementary[OF w Qd] by (auto simp: lev_mid_def)
  have "length ?L = (\<Sum>i\<leftarrow>[0..<b]. length (dgate2_gates ?K (k + i) ?w (rot_phase b i)))"
    by (simp add: length_concat comp_def)
  also have "\<dots> \<le> (\<Sum>i\<leftarrow>[0..<b]. 2 * ?K + 1)" by (rule sum_list_mono) (use D in simp)
  finally show "length (lev_mid b k j) \<le> b * (2 * (b + k) + 1) + 2" by (simp add: lev_mid_def sum_list_triv)
qed

text \<open>A level: query the rounded angle, rotate, query again.\<close>

definition lev_oracle :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "lev_oracle b k a j = oracle_m b (2 ^ j) (2 * 2 ^ (k - Suc j)) (prep_code b k a j)"

definition lev_qgates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "lev_qgates b k a j = [lev_oracle b k a j] @ lev_mid b k j @ [lev_oracle b k a j]"

lemma lev_oracle_carrier:
  assumes j: "j < k"
  shows "lev_oracle b k a j \<in> carrier_mat (2 ^ (b + k)) (2 ^ (b + k))"
proof -
  have K: "(2::nat) ^ (b + k) = 2 ^ b * 2 ^ j * (2 * 2 ^ (k - Suc j))"
  proof -
    have "(2::nat) ^ (b + k) = 2 ^ b * (2 ^ j * (2 * 2 ^ (k - Suc j)))" unfolding lev_dim[OF j] by (simp only: power_add)
    thus ?thesis by (simp only: Groups.mult.assoc)
  qed
  show ?thesis unfolding lev_oracle_def oracle_m_def K by simp
qed

theorem lev_qgates_props:
  assumes j: "j < k"
  shows "stands_for (2 ^ b) (2 ^ k) (circuit_mat (2 ^ (b + k)) (lev_qgates b k a j)) (lev_rnd b k a j)"
    "U \<in> set (lev_qgates b k a j) \<Longrightarrow> elementary (2 ^ (b + k)) U \<or> U = lev_oracle b k a j"
    "length (lev_qgates b k a j) \<le> b * (2 * (b + k) + 1) + 4"
    "circuit_mat (2 ^ (b + k)) (lev_qgates b k a j) = lev_oracle b k a j * circuit_mat (2 ^ (b + k)) (lev_mid b k j) * lev_oracle b k a j"
proof -
  let ?h = "2 ^ (k - Suc j) :: nat" and ?O = "lev_oracle b k a j"
  note M = lev_mid_props[OF j, of b]
  have Oc: "?O \<in> carrier_mat (2 ^ (b + k)) (2 ^ (b + k))" by (rule lev_oracle_carrier[OF j])
  have lc: "\<And>U. U \<in> set (lev_mid b k j) \<Longrightarrow> U \<in> carrier_mat (2 ^ (b + k)) (2 ^ (b + k))"
    using M(2) elementary_carrier by blast
  have e: "circuit_mat (2 ^ (b + k)) (lev_qgates b k a j) = ?O * circuit_mat (2 ^ (b + k)) (lev_mid b k j) * ?O"
  proof -
    have a1: "circuit_mat (2 ^ (b + k)) ([?O] @ lev_mid b k j @ [?O]) = circuit_mat (2 ^ (b + k)) (lev_mid b k j @ [?O]) * ?O"
      using circuit_mat_append[of "[?O]" "2 ^ (b + k)" "lev_mid b k j @ [?O]"] Oc lc by (auto simp: circuit_mat_single)
    have a2: "circuit_mat (2 ^ (b + k)) (lev_mid b k j @ [?O]) = ?O * circuit_mat (2 ^ (b + k)) (lev_mid b k j)"
      using circuit_mat_append[of "lev_mid b k j" "2 ^ (b + k)" "[?O]"] Oc lc by (auto simp: circuit_mat_single)
    show ?thesis unfolding lev_qgates_def a1 a2 ..
  qed
  have "stands_for (2 ^ b) (2 ^ j * (2 * ?h))
      (?O * ctrl_blocks (2 ^ b * 2 ^ j) (2 * ?h) (\<lambda>c. Rot (ang b (c div 2 ^ j)) \<Otimes> 1\<^sub>m ?h) * ?O)
      (ctrl_blocks (2 ^ j) (2 * ?h) (\<lambda>c. Rot (ang b (prep_code b k a j c)) \<Otimes> 1\<^sub>m ?h))"
    unfolding lev_oracle_def
    by (rule oracle_m_stands_for[where B = "\<lambda>r. Rot (ang b r) \<Otimes> 1\<^sub>m ?h"]) (simp_all add: prep_code)
  thus "stands_for (2 ^ b) (2 ^ k) (circuit_mat (2 ^ (b + k)) (lev_qgates b k a j)) (lev_rnd b k a j)"
    unfolding e M(1) lev_rnd_def lev_dim[OF j] .
  show "U \<in> set (lev_qgates b k a j) \<Longrightarrow> elementary (2 ^ (b + k)) U \<or> U = ?O" using M(2) by (auto simp: lev_qgates_def)
  show "length (lev_qgates b k a j) \<le> b * (2 * (b + k) + 1) + 4" using M(3) by (simp add: lev_qgates_def)
  show "circuit_mat (2 ^ (b + k)) (lev_qgates b k a j) = ?O * circuit_mat (2 ^ (b + k)) (lev_mid b k j) * ?O" by (rule e)
qed

subsection \<open>The preparation circuit\<close>

definition prep_qgates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list" where
  "prep_qgates b k a = concat (map (lev_qgates b k a) [0..<k])"

text \<open>On a clean $b$-bit register the circuit prepares $\sum_x a_x\ket x$ to within $k\cdot 2\pi/2^b$,
with $2k$ oracle queries and $O(k\,b\,(b + k))$ elementary gates.\<close>

theorem prep_qgates_props:
  assumes n: "(\<Sum>x<2 ^ k. (a x)\<^sup>2) = 1" and a: "\<And>x. x < 2 ^ k \<Longrightarrow> 0 \<le> a x"
  shows "\<parallel>circuit_mat (2 ^ (b + k)) (prep_qgates b k a) *\<^sub>v (anc (2 ^ b) (2 ^ k) *\<^sub>v unit_vec (2 ^ k) 0)
      - anc (2 ^ b) (2 ^ k) *\<^sub>v Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))\<parallel> \<le> real k * (2 * pi / 2 ^ b)"
    "U \<in> set (prep_qgates b k a) \<Longrightarrow> elementary (2 ^ (b + k)) U \<or> (\<exists>j<k. U = lev_oracle b k a j)"
    "length (prep_qgates b k a) \<le> k * (b * (2 * (b + k) + 1) + 4)"
proof -
  let ?K = "b + k" and ?A = "anc (2 ^ b) (2 ^ k)" and ?G = "circuit_mat (2 ^ k) (map (lev_rnd b k a) [0..<k])"
  let ?U = "circuit_mat (2 ^ ?K) (prep_qgates b k a)" and ?t = "Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))"
  let ?e = "unit_vec (2 ^ k) 0"
  have lc: "U \<in> carrier_mat (2 ^ ?K) (2 ^ ?K)" if Us: "Us \<in> set (map (lev_qgates b k a) [0..<k])" "U \<in> set Us" for Us U
  proof -
    obtain j where j: "j < k" and U: "U \<in> set (lev_qgates b k a j)" using Us by auto
    show ?thesis using lev_qgates_props(2)[OF j U] elementary_carrier lev_oracle_carrier[OF j] by blast
  qed
  have cU: "?U = circuit_mat (2 ^ ?K) (map (\<lambda>j. circuit_mat (2 ^ ?K) (lev_qgates b k a j)) [0..<k])"
  proof -
    have "?U = circuit_mat (2 ^ ?K) (map (circuit_mat (2 ^ ?K)) (map (lev_qgates b k a) [0..<k]))"
      unfolding prep_qgates_def by (rule circuit_mat_concat) (rule lc)
    thus ?thesis by (simp only: map_map comp_def)
  qed
  have S: "stands_for (2 ^ b) (2 ^ k) ?U ?G"
  proof -
    have "list_all2 (stands_for (2 ^ b) (2 ^ k)) (map (\<lambda>j. circuit_mat (2 ^ ?K) (lev_qgates b k a j)) [0..<k]) (map (lev_rnd b k a) [0..<k])"
      by (auto simp: list_all2_map1 list_all2_map2 list_all2_same lev_qgates_props(1))
    hence "stands_for (2 ^ b) (2 ^ k) (circuit_mat (2 ^ b * 2 ^ k) (map (\<lambda>j. circuit_mat (2 ^ ?K) (lev_qgates b k a j)) [0..<k])) ?G"
      by (rule stands_for_circuit)
    thus ?thesis unfolding cU by (simp only: power_add)
  qed
  have Uc: "?U \<in> carrier_mat (2 ^ b * 2 ^ k) (2 ^ b * 2 ^ k)" and Gc: "?G \<in> carrier_mat (2 ^ k) (2 ^ k)"
    and UA: "?U * ?A = ?A * ?G" using S unfolding stands_for_def by blast+
  have e0: "?e \<in> carrier_vec (2 ^ k)" by simp
  have Ge: "?G *\<^sub>v ?e \<in> carrier_vec (2 ^ k)" by (rule mult_mat_vec_carrier[OF Gc e0])
  have tc: "?t \<in> carrier_vec (2 ^ k)" by simp
  have "?U *\<^sub>v (?A *\<^sub>v ?e) = (?U * ?A) *\<^sub>v ?e" by (rule assoc_mult_mat_vec[OF Uc anc_carrier e0, symmetric])
  also have "\<dots> = (?A * ?G) *\<^sub>v ?e" unfolding UA ..
  also have "\<dots> = ?A *\<^sub>v (?G *\<^sub>v ?e)" by (rule assoc_mult_mat_vec[OF anc_carrier Gc e0])
  finally have "?U *\<^sub>v (?A *\<^sub>v ?e) - ?A *\<^sub>v ?t = ?A *\<^sub>v (?G *\<^sub>v ?e - ?t)"
    using mult_minus_distrib_mat_vec[OF anc_carrier Ge tc] by simp
  moreover have "\<parallel>?A *\<^sub>v (?G *\<^sub>v ?e - ?t)\<parallel> = \<parallel>?G *\<^sub>v ?e - ?t\<parallel>" by (rule anc_norm) (use Ge in simp_all)
  ultimately show "\<parallel>?U *\<^sub>v (?A *\<^sub>v ?e) - ?A *\<^sub>v ?t\<parallel> \<le> real k * (2 * pi / 2 ^ b)"
    using rounded_prep[OF n a, of b] by simp
  show "U \<in> set (prep_qgates b k a) \<Longrightarrow> elementary (2 ^ (b + k)) U \<or> (\<exists>j<k. U = lev_oracle b k a j)"
    using lev_qgates_props(2) by (fastforce simp: prep_qgates_def)
  have "length (prep_qgates b k a) = (\<Sum>j\<leftarrow>[0..<k]. length (lev_qgates b k a j))" by (simp add: prep_qgates_def length_concat comp_def)
  also have "\<dots> \<le> (\<Sum>j\<leftarrow>[0..<k]. b * (2 * (b + k) + 1) + 4)" by (rule sum_list_mono) (rule lev_qgates_props(3), simp)
  finally show "length (prep_qgates b k a) \<le> k * (b * (2 * (b + k) + 1) + 4)" by (simp add: sum_list_triv)
qed

end
