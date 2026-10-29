theory Two_Comparisons
  imports Register_Swap
begin

definition fif :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fif c p z = (if c then flip_bit p z else z)"


section \<open>Recording both comparisons\<close>

lemma xv_fif: "(rw m) < p \<Longrightarrow> xv m (fif c p z) = xv m z" and yv_fif: "(rw m) < p \<Longrightarrow> yv m (fif c p z) = yv m z"
  by (auto intro!: bit_eqI simp: fif_def xv_def yv_def bit_take_bit_iff bit_drop_bit_eq bit_flip_bit_iff pos_defs)

lemma clean_fif: "(rw m) < p \<Longrightarrow> clean m (fif c p z) \<longleftrightarrow> clean m z"
  by (auto simp: fif_def clean_def bit_flip_bit_iff pos_defs)

lemma swp_twice: "rcirc (swp m m) (rcirc (swp m m) z) = z"
  by (rule bit_eqI) (auto simp: bit_swp pos_defs)

lemma swp_wires: "i \<le> m \<Longrightarrow> g \<in> set (swp m i) \<Longrightarrow> w \<in> wires g \<Longrightarrow> w \<le> (rw m)"
  by (induction i) (auto simp: sw3_def pos_defs)

lemma swp_fif:
  assumes "(rw m) < p"
  shows "rcirc (swp m m) (fif c p z) = fif c p (rcirc (swp m m) z)"
proof -
  have "\<forall>g \<in> set (swp m m). p \<notin> wires g" using swp_wires[of m m] assms by fastforce
  thus ?thesis by (simp add: fif_def rcirc_flip_other)
qed

definition c1w :: "nat \<Rightarrow> nat" where "c1w m = rw m + 1"
definition c2w :: "nat \<Rightarrow> nat" where "c2w m = rw m + 2"

text \<open>$c_1 \mathrel{\oplus}= [y<x]$ and $c_2 \mathrel{\oplus}= [x<y]$, the second by comparing the swapped
registers.\<close>

definition sortB :: "nat \<Rightarrow> rgate list" where "sortB m = cmpq m (c1w m) @ swp m m @ cmpq m (c2w m) @ swp m m"

lemma length_B: "length (sortB m) = 26 * m + 6" by (simp add: sortB_def length_cmpq length_swp)

lemma B_correct:
  assumes c: "clean m z"
  shows "rcirc (sortB m) z = fif (xv m z < yv m z) (c2w m) (fif (yv m z < xv m z) (c1w m) z)"
proof -
  let ?z1 = "fif (yv m z < xv m z) (c1w m) z"
  let ?s = "rcirc (swp m m) z"
  have R1: "(rw m) < (c1w m)" and R2: "(rw m) < (c2w m)" by (simp_all add: c1w_def c2w_def)
  have s1: "rcirc (cmpq m (c1w m)) z = ?z1" using cmpq_correct[OF c R1] by (simp add: fif_def)
  have s2: "rcirc (swp m m) ?z1 = fif (yv m z < xv m z) (c1w m) ?s" by (rule swp_fif[OF R1])
  have cs: "clean m (fif (yv m z < xv m z) (c1w m) ?s)" using c by (simp add: clean_fif[OF R1] swp_clean)
  have s3: "rcirc (cmpq m (c2w m)) (fif (yv m z < xv m z) (c1w m) ?s) = fif (xv m z < yv m z) (c2w m) (fif (yv m z < xv m z) (c1w m) ?s)"
    using cmpq_correct[OF cs R2] unfolding xv_fif[OF R1] yv_fif[OF R1] swp_values by (simp add: fif_def)
  show ?thesis
    unfolding sortB_def rcirc_append s1 s2 s3 swp_fif[OF R2] swp_fif[OF R1] swp_twice ..
qed


end
