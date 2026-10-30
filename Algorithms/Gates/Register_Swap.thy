theory Register_Swap
  imports Comparator_Registers
begin


section \<open>Swapping the two registers\<close>

definition sw3 :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where
  "sw3 m i = [CX (xw m i) (yw i), CX (yw i) (xw m i), CX (xw m i) (yw i)]"

fun swp :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where
  "swp m 0 = []"
| "swp m (Suc i) = swp m i @ sw3 m i"

lemma length_swp: "length (swp m i) = 3 * i" by (induction i) (simp_all add: sw3_def)

lemma bit_swp:
  assumes "i \<le> m"
  shows "bit (rcirc (swp m i) z) q \<longleftrightarrow>
    (if \<exists>j<i. q = xw m j then bit z (q - m) else if \<exists>j<i. q = yw j then bit z (m + q) else bit z q)"
  using assms
proof (induction i arbitrary: q)
  case 0 thus ?case by simp
next
  case (Suc i)
  let ?w = "rcirc (swp m i) z"
  have "bit (rcirc (sw3 m i) ?w) q \<longleftrightarrow> (if q = xw m i then bit ?w (yw i) else if q = yw i then bit ?w (xw m i) else bit ?w q)"
    using Suc.prems by (auto simp: sw3_def bit_flip_bit_iff pos_defs)
  thus ?case using Suc.IH[of q] Suc.IH[of "yw i"] Suc.IH[of "xw m i"] Suc.prems
    by (auto simp: rcirc_append less_Suc_eq pos_defs)
qed

lemma swp_values: "xv m (rcirc (swp m m) z) = yv m z" "yv m (rcirc (swp m m) z) = xv m z"
  by (auto intro!: bit_eqI simp: xv_def yv_def bit_take_bit_iff bit_drop_bit_eq bit_swp pos_defs ac_simps)

lemma swp_other: "(rw m) < q \<Longrightarrow> bit (rcirc (swp m m) z) q \<longleftrightarrow> bit z q"
  and swp_clean: "clean m (rcirc (swp m m) z) \<longleftrightarrow> clean m z"
  by (auto simp: bit_swp clean_def pos_defs)


end
