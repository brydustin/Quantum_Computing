theory Entry_Gates
  imports Rotation_Stage_Gates
begin

section \<open>The entry gate as queries and elementary gates\<close>

definition ent_gates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat list" where
  "ent_gates p q f = [ent_oracle (2 * p) (2 ^ q) f] @ mid_gates p q @ [ent_oracle (2 * p) (2 ^ q) f]"

theorem ent_gates_props:
  fixes p q :: nat
  defines "K \<equiv> q + 1 + 2 * p"
  assumes f: "\<And>k. k < 2 ^ q \<Longrightarrow> f k < 2 ^ (2 * p)"
  shows "stands_for (2 ^ (2 * p)) (2 ^ q * 2) (circuit_mat (2 ^ K) (ent_gates p q f)) (ent_rounded p (2 ^ q) f)"
    "U \<in> set (ent_gates p q f) \<Longrightarrow> elementary (2 ^ K) U \<or> U = ent_oracle (2 * p) (2 ^ q) f"
    "length (ent_gates p q f) \<le> 3 * p * (2 * K + 1) + 4"
proof -
  note M = mid_gates_props[of p q, folded K_def]
  have KN: "(2::nat) ^ K = 2 ^ (2 * p) * 2 ^ q * 2" unfolding K_def by (simp add: power_add ac_simps)
  let ?O = "ent_oracle (2 * p) (2 ^ q) f"
  have Oc: "?O \<in> carrier_mat (2 ^ K) (2 ^ K)" unfolding ent_oracle_def KN by simp
  have mc: "\<And>U. U \<in> set (mid_gates p q) \<Longrightarrow> U \<in> carrier_mat (2 ^ K) (2 ^ K)" using M(2) elementary_carrier by blast
  have "circuit_mat (2 ^ K) (ent_gates p q f) = ?O * circuit_mat (2 ^ K) (mid_gates p q) * ?O"
  proof -
    have a1: "circuit_mat (2 ^ K) ([?O] @ mid_gates p q @ [?O]) = circuit_mat (2 ^ K) (mid_gates p q @ [?O]) * ?O"
      using circuit_mat_append[of "[?O]" "2 ^ K" "mid_gates p q @ [?O]"] Oc mc by (auto simp: circuit_mat_single)
    have a2: "circuit_mat (2 ^ K) (mid_gates p q @ [?O]) = ?O * circuit_mat (2 ^ K) (mid_gates p q)"
      using circuit_mat_append[of "mid_gates p q" "2 ^ K" "[?O]"] Oc mc by (auto simp: circuit_mat_single)
    show ?thesis unfolding ent_gates_def a1 a2 ..
  qed
  also have "\<dots> = ?O * ent_mid p (2 ^ q) * ?O" unfolding K_def by (simp only: mid_gates_props(1))
  finally have e: "circuit_mat (2 ^ K) (ent_gates p q f) = ?O * ent_mid p (2 ^ q) * ?O" .
  have "stands_for (2 ^ (2 * p)) (2 ^ q * 2) (?O * ent_mid p (2 ^ q) * ?O) (ent_rounded p (2 ^ q) f)"
    by (rule ent_stands_for) (rule f)
  thus "stands_for (2 ^ (2 * p)) (2 ^ q * 2) (circuit_mat (2 ^ K) (ent_gates p q f)) (ent_rounded p (2 ^ q) f)"
    unfolding e .
  show "U \<in> set (ent_gates p q f) \<Longrightarrow> elementary (2 ^ K) U \<or> U = ?O" using M(2) by (auto simp: ent_gates_def)
  show "length (ent_gates p q f) \<le> 3 * p * (2 * K + 1) + 4" using M(3) by (simp add: ent_gates_def)
qed

subsection \<open>Sharing the workspace\<close>

text \<open>A gate that stands for $G$ on its own clean ancillas still does so with more clean wires above.\<close>

lemma stands_for_extend:
  assumes s: "stands_for A N U G" and B: "0 < B"
  shows "stands_for (B * A) N (1\<^sub>m B \<Otimes> U) G"
proof -
  have U: "U \<in> carrier_mat (A * N) (A * N)" and G: "G \<in> carrier_mat N N" using s by (simp_all add: stands_for_def)
  show ?thesis
  proof (cases "A * N = 0")
    case True
    hence "A = 0 \<or> N = 0" by simp
    thus ?thesis using s True U G by (auto simp: stands_for_def anc_def)
  next
    case False
    hence A: "0 < A" and N: "0 < N" by simp_all
    have "1\<^sub>m B \<Otimes> U \<in> carrier_mat (B * (A * N)) (B * (A * N))" using U by simp
    hence U': "1\<^sub>m B \<Otimes> U \<in> carrier_mat (B * A * N) (B * A * N)" unfolding Groups.mult.assoc .
    have e: "U $$ (r, c) = (if r < N then G $$ (r, c) else 0)" if "r < A * N" "c < N" for r c
      using s stands_for_iff[OF U G A] that by blast
    have "(1\<^sub>m B \<Otimes> U) $$ (r, c) = (if r < N then G $$ (r, c) else 0)" if "r < B * A * N" "c < N" for r c
    proof -
      have rB: "r < B * (A * N)" using that(1) by (simp only: Groups.mult.assoc)
      have NA: "N \<le> A * N" using mult_le_mono1[of 1 A N] A by simp
      hence cA: "c < A * N" using that(2) by linarith
      have "A * N \<le> B * (A * N)" using mult_le_mono1[of 1 B "A * N"] B by simp
      hence cB: "c < B * (A * N)" using cA by linarith
      have "(1\<^sub>m B \<Otimes> U) $$ (r, c) = 1\<^sub>m B $$ (r div (A * N), c div (A * N)) * U $$ (r mod (A * N), c mod (A * N))"
        using index_tensor_mat[of "1\<^sub>m B" B B U "A * N" "A * N" r c] rB cB U B A N cA by simp
      also have "\<dots> = (if r < N then G $$ (r, c) else 0)"
      proof (cases "r < A * N")
        case True
        thus ?thesis using e[OF True that(2)] cA B by simp
      next
        case False
        hence "r div (A * N) \<noteq> 0" using A N by (simp add: div_eq_0_iff)
        moreover have "r div (A * N) < B" using that(1) A N by (simp add: div_less_iff_less_mult ac_simps)
        moreover have "\<not> r < N" using False NA by linarith
        ultimately show ?thesis using cA B by auto
      qed
      finally show ?thesis .
    qed
    thus ?thesis using stands_for_iff[OF U' G] B A by (simp add: ac_simps)
  qed
qed

end
