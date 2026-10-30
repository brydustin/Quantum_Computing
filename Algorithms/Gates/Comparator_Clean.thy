theory Comparator_Clean
  imports Sort_Flag
begin

section \<open>The sort-and-flag circuit on clean states\<close>

lemma fif_twice [simp]: "fif c p (fif c p w) = w" by (simp add: fif_def)
lemma fif_commute: "fif c p (fif c' p' w) = fif c' p' (fif c p w)" by (simp add: fif_def flip_bit_commute)
lemma bit_fif: "bit (fif c p w) q \<longleftrightarrow> (if q = p \<and> c then \<not> bit w q else bit w q)"
  by (simp add: fif_def bit_flip_bit_iff)
lemma fif_False [simp]: "fif False p w = w" and fif_True: "fif True p w = flip_bit p w"
  by (simp_all add: fif_def)
lemma fif_cancel: "fif a p (fif b q (fif a p (fif b q w))) = w"
  by (subst fif_commute[of b q a p]) simp


lemma pos_distinct [simp]: "(c1w m) \<noteq> (c2w m)" "(c2w m) \<noteq> (c1w m)" "(c1w m) \<noteq> (dw m)" "(dw m) \<noteq> (c1w m)" "(c2w m) \<noteq> (dw m)" "(dw m) \<noteq> (c2w m)"
  "(c1w m) \<noteq> 0" "(c2w m) \<noteq> 0" "(dw m) \<noteq> 0" "(rw m) < (c1w m)" "(rw m) < (c2w m)" "(rw m) < (dw m)"
  by (simp_all add: c1w_def c2w_def dw_def)

lemma xv_flip0: "xv m (fif c 0 w) = xv m w" and yv_flip0: "yv m (fif c 0 w) = yv m w"
  by (auto intro!: bit_eqI simp: fif_def xv_def yv_def bit_take_bit_iff bit_drop_bit_eq bit_flip_bit_iff)

lemma clean_flip0: "clean m (fif c 0 w) \<longleftrightarrow> clean m w"
  by (auto simp: fif_def clean_def bit_flip_bit_iff pos_defs)

lemma swp_flip0: "rcirc (swp m m) (fif c 0 w) = fif c 0 (rcirc (swp m m) w)"
proof -
  have "\<forall>g \<in> set (swp m m). 0 \<notin> wires g"
  proof -
    have "g \<in> set (swp m i) \<Longrightarrow> 0 \<notin> wires g" for i g by (induction i) (auto simp: sw3_def pos_defs)
    thus ?thesis by blast
  qed
  thus ?thesis by (simp add: fif_def rcirc_flip_other)
qed

lemma bit0_swp: "bit (rcirc (swp m m) w) 0 \<longleftrightarrow> bit w 0"
  by (simp add: bit_swp pos_defs)

text \<open>B leaves a clean state with given $c_1,c_2$ bits in a clean state with toggled ones.\<close>

theorem S_correct:
  assumes c: "clean m z" and z0: "\<not> bit z (c1w m)" "\<not> bit z (c2w m)" "\<not> bit z (dw m)"
  defines "d \<equiv> (yv m z < xv m z \<and> \<not> bit z 0) \<or> (xv m z < yv m z \<and> bit z 0)"
  shows "rcirc (sort_flag m) z = (if d then flip_bit 0 (rcirc (swp m m) z) else z)"
proof -
  let ?c1 = "yv m z < xv m z" and ?c2 = "xv m z < yv m z" and ?b = "bit z 0"
  let ?w = "fif d 0 (if d then rcirc (swp m m) z else z)"
  have Gd_d: "(bit w (c1w m) \<and> \<not> bit w 0) \<noteq> (bit w (c2w m) \<and> bit w 0) \<longleftrightarrow> d'"
    if "bit w (c1w m) \<longleftrightarrow> c1" "bit w (c2w m) \<longleftrightarrow> c2" "bit w 0 \<longleftrightarrow> b" "\<not> (c1 \<and> c2)"
       "d' \<longleftrightarrow> (c1 \<and> \<not> b) \<or> (c2 \<and> b)" for w c1 c2 b d' using that by auto
  \<comment> \<open>first half: $d$ into $D$, scratch cleared\<close>
  have h1: "rcirc ((sortB m) @ (flagG m) @ (sortB m)) z = fif d (dw m) z"
  proof -
    let ?z1 = "fif ?c2 (c2w m) (fif ?c1 (c1w m) z)"
    have z1: "rcirc (sortB m) z = ?z1" by (rule B_correct[OF c])
    have g: "rcirc (flagG m) ?z1 = fif d (dw m) ?z1"
      unfolding Gd_correct by (rule arg_cong[where f = "\<lambda>c. fif c (dw m) ?z1"], rule Gd_d)
        (use z0 in \<open>auto simp: bit_fif d_def\<close>)
    have cz: "clean m (fif d (dw m) ?z1)" using c by (simp add: clean_fif)
    have "rcirc (sortB m) (fif d (dw m) ?z1) = fif d (dw m) z"
      unfolding B_correct[OF cz] xv_fif[OF pos_distinct(12)] yv_fif[OF pos_distinct(12)]
        xv_fif[OF pos_distinct(10)] yv_fif[OF pos_distinct(10)] xv_fif[OF pos_distinct(11)] yv_fif[OF pos_distinct(11)]
      by (cases "xv m z < yv m z"; cases "yv m z < xv m z"; cases d) (simp_all add: fif_def flip_bit_commute)
    thus ?thesis unfolding rcirc_append z1 g .
  qed
  \<comment> \<open>middle: swap and flag, controlled on $D$\<close>
  have h2: "rcirc (cswp m m @ [CX (dw m) 0]) (fif d (dw m) z) = fif d (dw m) ?w"
  proof (cases d)
    case True
    have sD: "rcirc (swp m m) (flip_bit (dw m) z) = flip_bit (dw m) (rcirc (swp m m) z)"
      using swp_fif[OF pos_distinct(12), where c = True and z = z] by (simp add: fif_True)
    have "bit (rcirc (swp m m) (flip_bit (dw m) z)) (dw m)" using z0 by (simp add: swp_other bit_flip_bit_iff)
    thus ?thesis using True z0 unfolding rcirc_append cswp_swp
      by (simp add: fif_True bit_flip_bit_iff sD flip_bit_commute[of 0 "dw m"])
  next
    case False
    thus ?thesis using z0 unfolding rcirc_append cswp_swp by simp
  qed
  \<comment> \<open>second half: the same $d$ is recomputed from the new state and cleared\<close>
  have h3: "rcirc ((sortB m) @ (flagG m) @ (sortB m)) (fif d (dw m) ?w) = ?w"
  proof -
    have cw: "clean m ?w" using c by (cases d) (simp_all add: clean_flip0 swp_clean)
    have bw: "\<not> bit ?w (c1w m)" "\<not> bit ?w (c2w m)" "bit ?w (dw m) \<longleftrightarrow> False"
      using z0 by (cases d; simp add: bit_fif fif_def bit_flip_bit_iff swp_other)+
    have vals: "(yv m ?w < xv m ?w \<and> \<not> bit ?w 0) \<or> (xv m ?w < yv m ?w \<and> bit ?w 0) \<longleftrightarrow> d"
      unfolding d_def by (cases d) (auto simp: xv_flip0 yv_flip0 swp_values bit_fif bit0_swp)
    let ?w1 = "fif (xv m ?w < yv m ?w) (c2w m) (fif (yv m ?w < xv m ?w) (c1w m) ?w)"
    have cD: "clean m (fif d (dw m) ?w)" using cw by (simp add: clean_fif)
    have z1: "rcirc (sortB m) (fif d (dw m) ?w) = fif d (dw m) ?w1"
      unfolding B_correct[OF cD] by (simp add: xv_fif[OF pos_distinct(12)] yv_fif[OF pos_distinct(12)] xv_flip0 yv_flip0 fif_commute)
    have g: "rcirc (flagG m) (fif d (dw m) ?w1) = ?w1"
    proof -
      have "rcirc (flagG m) (fif d (dw m) ?w1) = fif d (dw m) (fif d (dw m) ?w1)"
        unfolding Gd_correct by (rule arg_cong[where f = "\<lambda>c. fif c (dw m) (fif d (dw m) ?w1)"], rule Gd_d[OF _ _ _ _ vals[symmetric]])
          (use bw in \<open>auto simp: bit_fif\<close>)
      thus ?thesis by simp
    qed
    have cw1: "clean m ?w1" using cw by (simp add: clean_fif)
    have v1: "xv m ?w1 = xv m ?w" "yv m ?w1 = yv m ?w" by (simp_all add: xv_fif yv_fif)
    have "rcirc (sortB m) ?w1 = ?w" unfolding B_correct[OF cw1] v1 by (rule fif_cancel)
    thus ?thesis unfolding rcirc_append z1 g .
  qed
  have "rcirc (sort_flag m) z = ?w"
    unfolding sort_flag_def append_assoc[symmetric] rcirc_append
    using h1 h2 h3 by (simp add: rcirc_append)
  thus ?thesis by (simp add: fif_def)
qed


end
