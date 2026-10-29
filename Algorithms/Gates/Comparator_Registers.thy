theory Comparator_Registers
  imports Bennett_Uncompute
begin


section \<open>Registers as numbers\<close>

definition xv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "xv m z = take_bit m (drop_bit (m + 1) z)"
definition yv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "yv m z = take_bit m (drop_bit 1 z)"

lemma xv_lt: "xv m z < 2 ^ m" and yv_lt: "yv m z < 2 ^ m"
  by (simp_all add: xv_def yv_def take_bit_nat_less_exp)

lemma bit_xv: "j < m \<Longrightarrow> bit (xv m z) j \<longleftrightarrow> bit z (xw m j)"
  and bit_yv: "j < m \<Longrightarrow> bit (yv m z) j \<longleftrightarrow> bit z (yw j)"
  by (simp_all add: xv_def yv_def bit_take_bit_iff bit_drop_bit_eq pos_defs ac_simps)

text \<open>The scratch bits of the comparator, all clear.\<close>

definition clean :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "clean m z \<longleftrightarrow> (\<forall>k\<le>m. \<not> bit z (ew m k)) \<and> (\<forall>k<m. \<not> bit z (tw m k)) \<and> \<not> bit z (rw m)"

section \<open>The clean comparator\<close>

text \<open>$q \mathrel{\oplus}= [y<x]$ on a bit $q$ outside the layout, every other bit restored.\<close>

definition cmpq :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where "cmpq m q = cmp_circ m @ [CNOT (rw m) q] @ rev (cmp_circ m)"

lemma length_cmpq: "length (cmpq m q) = 10 * m + 3" by (simp add: cmpq_def length_comp)

lemma comp_ok: "\<forall>g \<in> set (cmp_circ m). rg_ok (4 * m + 3) g"
proof -
  have "\<forall>g \<in> set (cscan m i). rg_ok (4 * m + 3) g" if "i \<le> m" for i
    using that by (induction i) (auto simp: cstep_def pos_defs)
  from this[of m] show ?thesis by (simp add: cmp_circ_def pos_defs)
qed

lemma comp_wires: "g \<in> set (cmp_circ m) \<Longrightarrow> w \<in> wires g \<Longrightarrow> w \<le> (rw m)"
proof -
  have "\<forall>g \<in> set (cscan m i). \<forall>w \<in> wires g. w \<le> (rw m)" if "i \<le> m" for i
    using that by (induction i) (auto simp: cstep_def pos_defs)
  thus "g \<in> set (cmp_circ m) \<Longrightarrow> w \<in> wires g \<Longrightarrow> w \<le> (rw m)" by (auto simp: cmp_circ_def pos_defs)
qed

lemma cmpq_correct:
  assumes c: "clean m z" and q: "(rw m) < q"
  shows "rcirc (cmpq m q) z = (if yv m z < xv m z then flip_bit q z else z)"
proof -
  have nq: "\<forall>g \<in> set (cmp_circ m). q \<notin> wires g" using comp_wires q by fastforce
  have "bit (rcirc (cmp_circ m) z) (rw m) \<longleftrightarrow> yv m z < xv m z"
    by (rule comp_correct[OF xv_lt yv_lt]) (use c in \<open>simp_all add: bit_xv bit_yv clean_def\<close>)
  thus ?thesis unfolding cmpq_def using compute_copy_uncompute[OF comp_ok nq] q by simp
qed


end
