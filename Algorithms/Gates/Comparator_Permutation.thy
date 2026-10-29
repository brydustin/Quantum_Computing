theory Comparator_Permutation
  imports Comparator_Clean HHL_Algorithm.HHL_Sparse_Circuit
begin

section \<open>The comparator is the simulation's comparison permutation\<close>

lemma bit_above: "(z :: nat) < 2 ^ k \<Longrightarrow> k \<le> q \<Longrightarrow> \<not> bit z q"
proof -
  assume z: "z < 2 ^ k" and q: "k \<le> q"
  have "\<not> bit (take_bit k z) q" using q by (simp add: bit_take_bit_iff)
  thus ?thesis using take_bit_nat_eq_self[OF z] by simp
qed


lemma data_size: "2 ^ (2 * m + 1) = 2 ^ m * 2 ^ m * (2 :: nat)"
  unfolding mult_2 power_add by simp

text \<open>The registers read off an encoded basis state.\<close>

lemma enc_regs:
  assumes x: "x < 2 ^ m" and y: "y < 2 ^ m" and b: "b < 2"
  shows "xv m (enc (2 ^ m) x y b) = x" "yv m (enc (2 ^ m) x y b) = y" "bit (enc (2 ^ m) x y b) 0 \<longleftrightarrow> b = 1"
proof -
  have d: "drop_bit 1 (enc (2 ^ m) x y b) = x * 2 ^ m + y" using enc_div[OF b] by (simp add: drop_bit_eq_div)
  have "drop_bit m (drop_bit 1 (enc (2 ^ m) x y b)) = x" using y unfolding d by (simp add: drop_bit_eq_div)
  hence "drop_bit (m + 1) (enc (2 ^ m) x y b) = x" by simp
  thus "xv m (enc (2 ^ m) x y b) = x" using x by (simp add: xv_def take_bit_nat_eq_self)
  show "yv m (enc (2 ^ m) x y b) = y" unfolding yv_def d using y by (simp add: take_bit_eq_mod)
  show "bit (enc (2 ^ m) x y b) 0 \<longleftrightarrow> b = 1" using enc_mod[OF b] b by (auto simp: bit_0 odd_iff_mod_2_eq_one)
qed

text \<open>A state with nothing above the data wires is the encoding of its registers.\<close>

lemma enc_of_regs:
  assumes z: "z < 2 ^ (2 * m + 1)"
  shows "z = enc (2 ^ m) (xv m z) (yv m z) (z mod 2)"
proof -
  have k: "z div 2 div 2 ^ m < 2 ^ m" using z unfolding data_size by (simp add: div_less_iff_less_mult)
  have xz: "xv m z = z div 2 div 2 ^ m"
    using k by (simp add: xv_def drop_bit_eq_div take_bit_nat_eq_self div_mult2_eq)
  have yz: "yv m z = z div 2 mod 2 ^ m" by (simp add: yv_def drop_bit_eq_div take_bit_eq_mod)
  have "enc (2 ^ m) (xv m z) (yv m z) (z mod 2) = z div 2 * 2 + z mod 2"
    unfolding enc_def xz yz div_mult_mod_eq ..
  thus ?thesis by simp
qed

lemma low_clean:
  assumes "z < 2 ^ (2 * m + 1)"
  shows "clean m z" "\<not> bit z (c1w m)" "\<not> bit z (c2w m)" "\<not> bit z (dw m)"
  using bit_above[OF assms] by (auto simp: clean_def pos_defs c1w_def c2w_def dw_def)

lemma swp_low:
  assumes "z < 2 ^ (2 * m + 1)"
  shows "rcirc (swp m m) z < 2 ^ (2 * m + 1)"
proof -
  have "g \<in> set (swp m i) \<Longrightarrow> i \<le> m \<Longrightarrow> rg_ok (2 * m + 1) g" for i g
    by (induction i) (auto simp: sw3_def pos_defs)
  thus ?thesis by (intro rcirc_lt[OF _ assms] ballI) blast
qed

text \<open>The circuit is the simulation's comparator on every basis state.\<close>

theorem S_cmp_perm:
  assumes j: "j < 2 ^ m * 2 ^ m * 2"
  shows "rcirc (sort_flag m) j = cmp_perm (2 ^ m) j"
proof -
  let ?n = "2 ^ m :: nat"
  obtain x y b where x: "x < ?n" and y: "y < ?n" and b: "b < 2" and je: "j = enc ?n x y b"
    using enc_decode[OF j] by blast
  have jl: "j < 2 ^ (2 * m + 1)" using j unfolding data_size .
  note r = enc_regs[OF x y b]
  let ?w = "rcirc (swp m m) j"
  have "odd ?w \<longleftrightarrow> b = 1" using bit0_swp[of m j] r(3) unfolding je by (simp add: bit_0)
  hence m2: "?w mod 2 = b" using b by (cases "b = 1") (auto simp: odd_iff_mod_2_eq_one even_iff_mod_2_eq_zero)
  have "?w = enc ?n (xv m ?w) (yv m ?w) (?w mod 2)" by (rule enc_of_regs[OF swp_low[OF jl]])
  also have "\<dots> = enc ?n y x b" unfolding m2 swp_values unfolding je r ..
  finally have w: "?w = enc ?n y x b" .
  have flip: "flip_bit 0 (enc ?n y x b) = enc ?n y x (1 - b)"
    using b by (cases b) (simp_all add: enc_def flip_bit_0)
  have c: "cmp_perm ?n j = (if (y < x \<and> b = 0) \<or> (x < y \<and> b = 1) then enc ?n y x (1 - b) else j)"
    unfolding je by (rule cmp_perm_enc[OF x y b])
  have d: "(yv m j < xv m j \<and> \<not> bit j 0) \<or> (xv m j < yv m j \<and> bit j 0) \<longleftrightarrow> (y < x \<and> b = 0) \<or> (x < y \<and> b = 1)"
    unfolding je r using b by auto
  show ?thesis unfolding S_correct[OF low_clean[OF jl]] c d w flip ..
qed


end
