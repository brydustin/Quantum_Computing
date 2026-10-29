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
  have im: "i \<le> m" "i < m" using Suc.prems by simp_all
  note IH = Suc.IH[OF im(1)]
  have dD: "bit ?w (dw m) \<longleftrightarrow> bit w (dw m)" using IH[of "dw m"] im by (auto simp: pos_defs dw_def)
  have step: "bit (rcirc (fred m i) ?w) q \<longleftrightarrow>
        (if bit ?w (dw m) \<and> q = xw m i then bit ?w (yw i) else if bit ?w (dw m) \<and> q = yw i then bit ?w (xw m i) else bit ?w q)"
    using Suc.prems by (auto simp: fred_def bit_flip_bit_iff pos_defs dw_def)
  text \<open>Bits $i$ of the two registers are untouched by the first $i$ Fredkin gates.\<close>
  have cy: "(\<exists>j<i. yw i = xw m j) = False" "(\<exists>j<i. yw i = yw j) = False" using im by (auto simp: yw_def xw_def)
  have cx: "(\<exists>j<i. xw m i = xw m j) = False" "(\<exists>j<i. xw m i = yw j) = False" using im by (auto simp: yw_def xw_def)
  have Iy: "bit ?w (yw i) \<longleftrightarrow> bit w (yw i)" using IH[of "yw i"] unfolding cy by simp
  have Ix: "bit ?w (xw m i) \<longleftrightarrow> bit w (xw m i)" using IH[of "xw m i"] unfolding cx by simp
  have ex: "(\<exists>j<Suc i. q = xw m j) \<longleftrightarrow> (\<exists>j<i. q = xw m j) \<or> q = xw m i"
    "(\<exists>j<Suc i. q = yw j) \<longleftrightarrow> (\<exists>j<i. q = yw j) \<or> q = yw i" by (auto simp: less_Suc_eq)
  have xy: "xw m i \<noteq> yw i" "xw m i - m = yw i" "m + yw i = xw m i" using im by (simp_all add: xw_def yw_def)
  have e: "rcirc (cswp m (Suc i)) w = rcirc (fred m i) ?w" by (simp add: rcirc_append)
  show ?case
  proof (cases "q = xw m i")
    case qx: True
    show ?thesis unfolding e step ex unfolding qx cx using dD Ix Iy xy by simp
  next
    case qx: False
    show ?thesis
    proof (cases "q = yw i")
      case qy: True
      show ?thesis unfolding e step ex unfolding qy cy using dD Ix Iy xy by simp
    next
      case False
      have f: "(q = xw m i) = False" "(q = yw i) = False" using qx False by simp_all
      show ?thesis unfolding e step ex f dD IH[of q] by (simp only: simp_thms if_False)
    qed
  qed
qed

lemma cswp_swp: "rcirc (cswp m m) w = (if bit w (dw m) then rcirc (swp m m) w else w)"
  by (auto intro!: bit_eqI simp: bit_cswp bit_swp)

definition sort_flag :: "nat \<Rightarrow> rgate list" where
  "(sort_flag m) = (sortB m) @ (flagG m) @ (sortB m) @ cswp m m @ [CNOT (dw m) 0] @ (sortB m) @ (flagG m) @ (sortB m)"

lemma length_S: "length (sort_flag m) = 4 * (26 * m + 6) + 8 + 3 * m + 1"
  by (simp add: sort_flag_def length_B length_cswp flagG_def)


end
