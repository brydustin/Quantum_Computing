theory Sort_Flag
  imports Two_Comparisons
begin


section \<open>Sorting the pair and flagging the swap\<close>

definition dw :: "nat \<Rightarrow> nat" where "dw m = rw m + 3"

text \<open>$d \mathrel{\oplus}= (c_1\wedge\neg b)\oplus(c_2\wedge b)$, with the flag $b$ at bit $0$.\<close>

definition flagG :: "nat \<Rightarrow> rgate list" where "flagG m = [NOT 0, TOF (c1w m) 0 (dw m), NOT 0, TOF (c2w m) 0 (dw m)]"

lemma Gd_correct: "rcirc (flagG m) w = fif ((bit w (c1w m) \<and> \<not> bit w 0) \<noteq> (bit w (c2w m) \<and> bit w 0)) (dw m) w"
  by (auto simp: flagG_def fif_def bit_flip_bit_iff pos_defs c1w_def c2w_def dw_def flip_bit_commute)

text \<open>Controlled on $d$, swap the registers (Fredkin gates).\<close>

definition fred :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where
  "fred m i = [CNOT (yw i) (xw m i), TOF (dw m) (xw m i) (yw i), CNOT (yw i) (xw m i)]"

fun cswp :: "nat \<Rightarrow> nat \<Rightarrow> rgate list" where
  "cswp m 0 = []"
| "cswp m (Suc i) = cswp m i @ fred m i"

lemma length_cswp: "length (cswp m i) = 3 * i" by (induction i) (simp_all add: fred_def)

lemma bit_cswp:
  assumes "i \<le> m"
  shows "bit (rcirc (cswp m i) w) q \<longleftrightarrow>
    (if bit w (dw m) \<and> (\<exists>j<i. q = xw m j) then bit w (q - m) else if bit w (dw m) \<and> (\<exists>j<i. q = yw j) then bit w (m + q) else bit w q)"
  using assms
proof (induction i arbitrary: q)
  case 0 thus ?case by simp
next
  case (Suc i)
  let ?w = "rcirc (cswp m i) w"
  have dD: "bit ?w (dw m) \<longleftrightarrow> bit w (dw m)" using Suc.IH[of "dw m"] Suc.prems by (auto simp: pos_defs dw_def)
  have "bit (rcirc (fred m i) ?w) q \<longleftrightarrow>
        (if bit ?w (dw m) \<and> q = xw m i then bit ?w (yw i) else if bit ?w (dw m) \<and> q = yw i then bit ?w (xw m i) else bit ?w q)"
    using Suc.prems by (auto simp: fred_def bit_flip_bit_iff pos_defs dw_def)
  thus ?case using Suc.IH[of q] Suc.IH[of "yw i"] Suc.IH[of "xw m i"] Suc.prems dD
    by (auto simp: rcirc_append less_Suc_eq pos_defs)
qed

lemma cswp_swp: "rcirc (cswp m m) w = (if bit w (dw m) then rcirc (swp m m) w else w)"
  by (auto intro!: bit_eqI simp: bit_cswp bit_swp)

definition sort_flag :: "nat \<Rightarrow> rgate list" where
  "(sort_flag m) = (sortB m) @ (flagG m) @ (sortB m) @ cswp m m @ [CNOT (dw m) 0] @ (sortB m) @ (flagG m) @ (sortB m)"

lemma length_S: "length (sort_flag m) = 4 * (26 * m + 6) + 8 + 3 * m + 1"
  by (simp add: sort_flag_def length_B length_cswp flagG_def)


end
