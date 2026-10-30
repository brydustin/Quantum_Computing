theory Diagonal_Oracle
  imports Entry_Gates
begin

section \<open>The diagonal phase from an oracle\<close>

text \<open>Query a register value $f(k)$, apply blocks that depend on the register only, query again:
on a clear register this is the block family $B(f(k))$.\<close>

lemma oracle_blocks_stands_for:
  assumes f: "\<And>k. k < nn \<Longrightarrow> f k < 2 ^ q" and B: "\<And>r. B r \<in> carrier_mat 2 2"
  shows "stands_for (2 ^ q) (nn * 2)
    (ent_oracle q nn f * ctrl_blocks (2 ^ q * nn) 2 (\<lambda>c. B (c div nn)) * ent_oracle q nn f)
    (ctrl_blocks nn 2 (\<lambda>k. B (f k)))"
proof -
  let ?R = "2 ^ q :: nat"
  have e: "ent_oracle q nn f * ctrl_blocks (?R * nn) 2 (\<lambda>c. B (c div nn)) * ent_oracle q nn f
      = ctrl_blocks (?R * nn) 2 (\<lambda>c. B (xreg nn f c div nn))"
    unfolding ent_oracle_def by (rule ctrl_conj) (simp_all add: xreg_props[OF f] B)
  have U: "ctrl_blocks (?R * nn) 2 (\<lambda>c. B (xreg nn f c div nn)) \<in> carrier_mat (?R * (nn * 2)) (?R * (nn * 2))"
    using ctrl_blocks_carrier[of "?R * nn" 2] by (simp only: Groups.mult.assoc)
  have G: "ctrl_blocks nn 2 (\<lambda>k. B (f k)) \<in> carrier_mat (nn * 2) (nn * 2)" by (rule ctrl_blocks_carrier)
  have xk: "xreg nn f k div nn = f k" if "k < nn" for k using that by (simp add: xreg_def)
  have "ctrl_blocks (?R * nn) 2 (\<lambda>c. B (xreg nn f c div nn)) $$ (r, c) = (if r < nn * 2 then ctrl_blocks nn 2 (\<lambda>k. B (f k)) $$ (r, c) else 0)"
    if "r < ?R * (nn * 2)" "c < nn * 2" for r c
  proof -
    have k: "c div 2 < nn" using that(2) by simp
    have rc: "r < ?R * nn * 2" using that(1) by (simp only: Groups.mult.assoc)
    have "nn * 2 \<le> ?R * (nn * 2)" using mult_le_mono1[of 1 ?R "nn * 2"] by simp
    hence "c < ?R * (nn * 2)" using that(2) by linarith
    hence cR: "c < ?R * nn * 2" by (simp only: Groups.mult.assoc)
    show ?thesis
    proof (cases "r < nn * 2")
      case True
      thus ?thesis using that k xk[OF k] rc cR by (auto simp: ctrl_blocks_index)
    next
      case False
      hence "r div 2 \<noteq> c div 2" using k by auto
      thus ?thesis using False that rc cR by (simp add: ctrl_blocks_index)
    qed
  qed
  hence "stands_for ?R (nn * 2) (ctrl_blocks (?R * nn) 2 (\<lambda>c. B (xreg nn f c div nn))) (ctrl_blocks nn 2 (\<lambda>k. B (f k)))"
    using stands_for_iff[OF U G] by simp
  thus ?thesis unfolding e .
qed

subsection \<open>The diagonal query\<close>

lemma dia_gate_dmat: "dia_gate n d A = dmat (n * n * 2) (\<lambda>j. d * Re (A $$ (j div 2 div n, j div 2 div n)))"
  by (rule eq_matI) (auto simp: dia_gate_def one_sparse_def dmat_def mat_diag_def)

definition dia_code :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> nat" where
  "dia_code p n d A k = near_bits p (d * Re (A $$ (k div n, k div n)))"

definition dia_rounded :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "dia_rounded p nn f = ctrl_blocks nn 2 (\<lambda>k. dmat 2 (\<lambda>_. ang p (f k)))"

theorem dia_gate_rounded: "dia_gate n d A \<approx>\<^bsub>2 * pi / 2 ^ p\<^esub> dia_rounded p (n * n) (dia_code p n d A)"
proof -
  have "dia_rounded p (n * n) (dia_code p n d A) = dmat (n * n * 2) (\<lambda>j. ang p (dia_code p n d A (j div 2)))"
    unfolding dia_rounded_def ctrl_dmat ..
  thus ?thesis unfolding dia_gate_dmat
    by (simp, intro dmat_close) (auto simp: dia_code_def near_bits)
qed


subsection \<open>The diagonal query as gates\<close>

definition dia_gates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat list" where
  "dia_gates p q f = [ent_oracle p (2 ^ q) f]
     @ phase_gates (q + 1 + p) (q + 1) (\<lambda>j a b. if a then ang p (2 ^ j) else 0) p @ [ent_oracle p (2 ^ q) f]"

lemma dia_phase:
  fixes z :: nat
  assumes z: "z < 2 ^ (q + 1 + p)"
  shows "ang p (z div 2 div 2 ^ q) = (\<Sum>j<p. if bit z (q + 1 + j) then ang p (2 ^ j) else 0)"
proof -
  have r: "z div 2 div 2 ^ q = drop_bit (q + 1) z" by (simp add: drop_bit_eq_div div_mult2_eq power_add ac_simps)
  have "z < 2 ^ (q + 1) * 2 ^ p" using z by (simp add: power_add)
  hence lt: "drop_bit (q + 1) z < 2 ^ p" by (simp add: drop_bit_eq_div div_less_iff_less_mult ac_simps)
  show ?thesis unfolding r ang_bits[OF lt] by (simp add: bit_drop_bit_eq)
qed

theorem dia_gates_props:
  fixes p q :: nat
  defines "K \<equiv> q + 1 + p"
  assumes f: "\<And>k. k < 2 ^ q \<Longrightarrow> f k < 2 ^ p"
  shows "stands_for (2 ^ p) (2 ^ q * 2) (circuit_mat (2 ^ K) (dia_gates p q f)) (dia_rounded p (2 ^ q) f)"
    "U \<in> set (dia_gates p q f) \<Longrightarrow> elementary (2 ^ K) U \<or> U = ent_oracle p (2 ^ q) f"
    "length (dia_gates p q f) \<le> p * (2 * K + 1) + 2"
proof -
  let ?L = "phase_gates K (q + 1) (\<lambda>j a b. if a then ang p (2 ^ j) else 0) p"
  have w: "1 \<le> q + 1" "q + 1 + p \<le> K" unfolding K_def by simp_all
  note P = phase_gates_props[OF w, of "\<lambda>j a b. if a then ang p (2 ^ j) else 0"]
  have KN: "(2::nat) ^ K = 2 ^ p * 2 ^ q * 2" unfolding K_def by (simp add: power_add ac_simps)
  let ?O = "ent_oracle p (2 ^ q) f"
  have Oc: "?O \<in> carrier_mat (2 ^ K) (2 ^ K)" unfolding ent_oracle_def KN by simp
  have lc: "\<And>U. U \<in> set ?L \<Longrightarrow> U \<in> carrier_mat (2 ^ K) (2 ^ K)" using P(2) elementary_unitary(1) by blast
  have mid: "circuit_mat (2 ^ K) ?L = ctrl_blocks (2 ^ p * 2 ^ q) 2 (\<lambda>c. dmat 2 (\<lambda>_. ang p (c div 2 ^ q)))"
  proof -
    have "ctrl_blocks (2 ^ p * 2 ^ q) 2 (\<lambda>c. dmat 2 (\<lambda>_. ang p (c div 2 ^ q))) = dmat (2 ^ K) (\<lambda>z. ang p (z div 2 div 2 ^ q))"
      unfolding ctrl_dmat KN ..
    also have "\<dots> = circuit_mat (2 ^ K) ?L" unfolding P(1)
      by (rule dmat_cong) (simp add: dia_phase K_def)
    finally show ?thesis ..
  qed
  have "circuit_mat (2 ^ K) (dia_gates p q f) = ?O * circuit_mat (2 ^ K) ?L * ?O"
  proof -
    have a1: "circuit_mat (2 ^ K) ([?O] @ ?L @ [?O]) = circuit_mat (2 ^ K) (?L @ [?O]) * ?O"
      using circuit_mat_append[of "[?O]" "2 ^ K" "?L @ [?O]"] Oc lc by (auto simp: circuit_mat_single)
    have a2: "circuit_mat (2 ^ K) (?L @ [?O]) = ?O * circuit_mat (2 ^ K) ?L"
      using circuit_mat_append[of ?L "2 ^ K" "[?O]"] Oc lc by (auto simp: circuit_mat_single)
    show ?thesis unfolding dia_gates_def K_def[symmetric] a1 a2 ..
  qed
  also have "\<dots> = ?O * ctrl_blocks (2 ^ p * 2 ^ q) 2 (\<lambda>c. dmat 2 (\<lambda>_. ang p (c div 2 ^ q))) * ?O" unfolding mid ..
  finally have e: "circuit_mat (2 ^ K) (dia_gates p q f) = ?O * ctrl_blocks (2 ^ p * 2 ^ q) 2 (\<lambda>c. dmat 2 (\<lambda>_. ang p (c div 2 ^ q))) * ?O" .
  show "stands_for (2 ^ p) (2 ^ q * 2) (circuit_mat (2 ^ K) (dia_gates p q f)) (dia_rounded p (2 ^ q) f)"
    unfolding e dia_rounded_def by (rule oracle_blocks_stands_for) (auto simp: f)
  show "U \<in> set (dia_gates p q f) \<Longrightarrow> elementary (2 ^ K) U \<or> U = ?O" using P(2) by (auto simp: dia_gates_def K_def)
  show "length (dia_gates p q f) \<le> p * (2 * K + 1) + 2" using P(3) by (simp add: dia_gates_def K_def)
qed

end
