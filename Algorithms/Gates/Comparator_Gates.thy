theory Comparator_Gates
  imports Comparator_Permutation Reversible_Compile
begin

section \<open>The comparator in elementary gates\<close>

lemma rg_ok_mono: "rg_ok K g \<Longrightarrow> K \<le> K' \<Longrightarrow> rg_ok K' g" by (cases g) auto

lemma sort_flag_ok: "g \<in> set (sort_flag m) \<Longrightarrow> rg_ok (4 * m + 6) g"
proof -
  have c: "g \<in> set (cmp_circ m) \<Longrightarrow> rg_ok (4 * m + 6) g" for g
    using comp_ok[of m] rg_ok_mono[of "4 * m + 3" g "4 * m + 6"] by auto
  have s: "i \<le> m \<Longrightarrow> g \<in> set (swp m i) \<Longrightarrow> rg_ok (4 * m + 6) g" for i g
    by (induction i) (auto simp: sw3_def pos_defs)
  have f: "i \<le> m \<Longrightarrow> g \<in> set (cswp m i) \<Longrightarrow> rg_ok (4 * m + 6) g" for i g
    by (induction i) (auto simp: fred_def pos_defs dw_def)
  assume "g \<in> set (sort_flag m)"
  thus ?thesis using c s[of m] f[of m]
    by (auto simp: sort_flag_def sortB_def cmpq_def flagG_def pos_defs c1w_def c2w_def dw_def)
qed

text \<open>On $K = 4m+6$ wires the sort-and-flag comparator compiles to $O(m^2)$ elementary gates, and on
every data basis state with clear ancillas it is the simulation's \<open>cmp_perm\<close>.\<close>

theorem sort_flag_gates:
  fixes m :: nat
  defines "K \<equiv> 4 * m + 6"
  shows "\<forall>U \<in> set (compile K (sort_flag m)). elementary (2 ^ K) U"
    and "length (compile K (sort_flag m)) \<le> (107 * m + 33) * (24 * m + 43)"
    and "j < 2 ^ m * 2 ^ m * 2 \<Longrightarrow>
      circuit_mat (2 ^ K) (compile K (sort_flag m)) *\<^sub>v unit_vec (2 ^ K) j = unit_vec (2 ^ K) (cmp_perm (2 ^ m) j)"
proof -
  have ok: "\<forall>g \<in> set (sort_flag m). rg_ok K g" using sort_flag_ok unfolding K_def by blast
  note P = compile_props[OF ok]
  show "\<forall>U \<in> set (compile K (sort_flag m)). elementary (2 ^ K) U" by (rule P(2))
  show "length (compile K (sort_flag m)) \<le> (107 * m + 33) * (24 * m + 43)"
    using P(3) unfolding length_S K_def by (simp add: algebra_simps)
  assume j: "j < 2 ^ m * 2 ^ m * 2"
  have "j < 2 ^ (2 * m + 1)" using j unfolding data_size .
  also have "(2::nat) ^ (2 * m + 1) \<le> 2 ^ K" unfolding K_def by (rule power_increasing) simp_all
  finally have jK: "j < 2 ^ K" .
  have sK: "rcirc (sort_flag m) j < 2 ^ K" by (rule rcirc_lt[OF ok jK])
  show "circuit_mat (2 ^ K) (compile K (sort_flag m)) *\<^sub>v unit_vec (2 ^ K) j = unit_vec (2 ^ K) (cmp_perm (2 ^ m) j)"
    unfolding P(1) pmat_unit[where f = "rcirc (sort_flag m)", OF jK sK] S_cmp_perm[OF j] ..
qed

end
