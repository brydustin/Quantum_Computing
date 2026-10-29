theory Entry_Oracle
  imports Entry_Rotation
begin

section \<open>The entry gate from an entry oracle\<close>

text \<open>The entry oracle XORs a $2p$-bit value $f(k)$ into a register above the data $\ket k\ket b$:
the low $p$ bits encode the angle $d|a|$, the high $p$ bits the phase $\arg a$, both in units of
$2\pi/2^p$.  Query, rotate the ancilla by the encoded angles, query again.\<close>

definition ang :: "nat \<Rightarrow> nat \<Rightarrow> real" where "ang p u = 2 * pi * real u / 2 ^ p"

lemma xor_lt: "a < 2 ^ n \<Longrightarrow> b < 2 ^ n \<Longrightarrow> xor a b < (2::nat) ^ n"
proof -
  assume "a < 2 ^ n" "b < 2 ^ n"
  hence "take_bit n (xor a b) = xor a b" by (simp add: take_bit_nat_eq_self)
  thus ?thesis using take_bit_nat_less_exp[of n "xor a b"] by simp
qed

lemma xor_xor: "xor (xor a b) b = (a :: nat)"
  by (rule bit_eqI) (auto simp: bit_xor_iff)

text \<open>Register $r$ and data pair $k < n^2$ form the index $r n^2 + k$.\<close>

definition xreg :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "xreg nn f c = (xor (c div nn) (f (c mod nn))) * nn + c mod nn"

lemma xreg_props:
  assumes f: "\<And>k. k < nn \<Longrightarrow> f k < 2 ^ q" and c: "c < 2 ^ q * nn"
  shows "xreg nn f c < 2 ^ q * nn" "xreg nn f (xreg nn f c) = c"
proof -
  have nn: "0 < nn" using c by (cases nn) auto
  have r: "c div nn < 2 ^ q" using c nn by (simp add: div_less_iff_less_mult)
  have k: "c mod nn < nn" using nn by simp
  have x: "xor (c div nn) (f (c mod nn)) < 2 ^ q" by (rule xor_lt[OF r f[OF k]])
  have "(xor (c div nn) (f (c mod nn))) * nn + c mod nn < (xor (c div nn) (f (c mod nn)) + 1) * nn" using k by simp
  also have "\<dots> \<le> 2 ^ q * nn" using x by (intro mult_le_mono1) simp
  finally show "xreg nn f c < 2 ^ q * nn" unfolding xreg_def .
  have d: "xreg nn f c div nn = xor (c div nn) (f (c mod nn))" "xreg nn f c mod nn = c mod nn"
    unfolding xreg_def using k by simp_all
  show "xreg nn f (xreg nn f c) = c" unfolding xreg_def[of nn f "xreg nn f c"] d xor_xor by simp
qed

definition ent_oracle :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "ent_oracle q nn f = pmat (2 ^ q * nn) (xreg nn f) \<Otimes> 1\<^sub>m 2"

definition ent_mid :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "ent_mid p nn = ctrl_blocks (2 ^ (2 * p) * nn) 2 (\<lambda>c. rblock (ang p (c div nn mod 2 ^ p)) (ang p (c div nn div 2 ^ p)))"

definition ent_rounded :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "ent_rounded p nn f = ctrl_blocks nn 2 (\<lambda>k. rblock (ang p (f k mod 2 ^ p)) (ang p (f k div 2 ^ p)))"

lemma rblock_carrier [simp]: "rblock \<theta> \<phi> \<in> carrier_mat 2 2" by (simp add: rblock_explicit)

lemma ent_conj:
  assumes f: "\<And>k. k < nn \<Longrightarrow> f k < 2 ^ (2 * p)"
  shows "ent_oracle (2 * p) nn f * ent_mid p nn * ent_oracle (2 * p) nn f =
    ctrl_blocks (2 ^ (2 * p) * nn) 2 (\<lambda>c. rblock (ang p (xreg nn f c div nn mod 2 ^ p)) (ang p (xreg nn f c div nn div 2 ^ p)))"
  unfolding ent_oracle_def ent_mid_def by (rule ctrl_conj) (simp_all add: xreg_props[OF f])

text \<open>On a clear register the circuit is the entry gate with the encoded angles.\<close>

theorem ent_stands_for:
  assumes f: "\<And>k. k < nn \<Longrightarrow> f k < 2 ^ (2 * p)"
  shows "stands_for (2 ^ (2 * p)) (nn * 2) (ent_oracle (2 * p) nn f * ent_mid p nn * ent_oracle (2 * p) nn f) (ent_rounded p nn f)"
proof -
  let ?R = "2 ^ (2 * p) :: nat"
  let ?B = "\<lambda>c. rblock (ang p (xreg nn f c div nn mod 2 ^ p)) (ang p (xreg nn f c div nn div 2 ^ p))"
  have e: "?R * (nn * 2) = ?R * nn * 2" by simp
  have U: "ctrl_blocks (?R * nn) 2 ?B \<in> carrier_mat (?R * (nn * 2)) (?R * (nn * 2))"
    unfolding e by (rule ctrl_blocks_carrier)
  have G: "ent_rounded p nn f \<in> carrier_mat (nn * 2) (nn * 2)" unfolding ent_rounded_def by (rule ctrl_blocks_carrier)
  have xk: "xreg nn f k div nn = f k" if "k < nn" for k
    using that by (simp add: xreg_def)
  have "ctrl_blocks (?R * nn) 2 ?B $$ (r, c) = (if r < nn * 2 then ent_rounded p nn f $$ (r, c) else 0)"
    if "r < ?R * (nn * 2)" "c < nn * 2" for r c
  proof -
    have k: "c div 2 < nn" using that(2) by simp
    have rc: "r < ?R * nn * 2" using that(1) by simp
    have "nn * 2 \<le> ?R * (nn * 2)" using mult_le_mono1[of 1 ?R "nn * 2"] by simp
    hence "c < ?R * (nn * 2)" using that(2) by linarith
    hence cR: "c < ?R * nn * 2" by (simp only: Groups.mult.assoc)
    show ?thesis
    proof (cases "r < nn * 2")
      case True
      thus ?thesis using that k xk[OF k] rc cR by (auto simp: ctrl_blocks_index ent_rounded_def)
    next
      case False
      hence "r div 2 \<noteq> c div 2" using k by auto
      thus ?thesis using False that rc cR by (simp add: ctrl_blocks_index)
    qed
  qed
  hence "stands_for ?R (nn * 2) (ctrl_blocks (?R * nn) 2 ?B) (ent_rounded p nn f)"
    using stands_for_iff[OF U G] by simp
  thus ?thesis by (simp only: ent_conj[OF f])
qed

subsection \<open>Rounding the angles\<close>

lemma cis_dist: "cmod (cis s - cis t) \<le> \<bar>s - t\<bar>"
proof -
  have "cis s - cis t = cis t * (cis (s - t) - 1)" by (simp add: right_diff_distrib cis_mult)
  hence "cmod (cis s - cis t) = cmod (cis (s - t) - 1)" by (simp add: norm_mult)
  thus ?thesis using cis_minus_one[of "s - t"] by simp
qed

text \<open>Every angle is within $2\pi/2^p$ of a $p$-bit one, modulo $2\pi$.\<close>

lemma round_angle: "\<exists>u < 2 ^ p. cmod (cis t - cis (ang p u)) \<le> 2 * pi / 2 ^ p"
proof -
  let ?q = "2 ^ p :: nat"
  define k where "k = \<lfloor>t * ?q / (2 * pi)\<rfloor>"
  define u where "u = nat (k mod int ?q)"
  have u: "u < ?q" unfolding u_def by (simp add: nat_less_iff)
  have r1: "real u = real_of_int (k mod int ?q)" unfolding u_def by (rule of_nat_nat) simp
  have "k mod int ?q = k - k div int ?q * int ?q" using div_mult_mod_eq[of k "int ?q"] by linarith
  hence ku: "real u = real_of_int k - real ?q * real_of_int (k div int ?q)" unfolding r1 by simp
  have c: "cis (ang p u) = cis (2 * pi * real_of_int k / ?q)"
  proof -
    have "ang p u = 2 * pi * real_of_int k / ?q - 2 * pi * real_of_int (k div int ?q)"
      unfolding ang_def ku by (simp add: field_simps)
    thus ?thesis by (simp add: cis_divide[symmetric] cis_multiple_2pi)
  qed
  have "\<bar>t - 2 * pi * real_of_int k / ?q\<bar> = 2 * pi / ?q * \<bar>t * ?q / (2 * pi) - real_of_int k\<bar>"
    by (simp add: field_simps abs_mult[symmetric])
  also have "\<dots> \<le> 2 * pi / ?q * 1"
    unfolding k_def by (intro mult_left_mono) (simp_all add: abs_le_iff, linarith)
  finally have "cmod (cis t - cis (ang p u)) \<le> 2 * pi / ?q" unfolding c using cis_dist order_trans by fastforce
  thus ?thesis using u by auto
qed


subsection \<open>What the entry oracle returns\<close>

text \<open>For the pair $k = (x, y)$ the oracle returns a $p$-bit angle near $d|A_{xy}|$ and a $p$-bit
phase near $\arg A_{xy}$, both modulo $2\pi$ and within $2\pi/2^p$.\<close>

definition near_bits :: "nat \<Rightarrow> real \<Rightarrow> nat" where
  "near_bits p t = (SOME u. u < 2 ^ p \<and> cmod (cis t - cis (ang p u)) \<le> 2 * pi / 2 ^ p)"

lemma near_bits: "near_bits p t < 2 ^ p" "cmod (cis t - cis (ang p (near_bits p t))) \<le> 2 * pi / 2 ^ p"
  using someI_ex[OF round_angle[of p t]] unfolding near_bits_def by blast+

definition ent_code :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> nat" where
  "ent_code p n d A k = (let a = (if k div n = k mod n then 0 else A $$ (k div n, k mod n))
     in near_bits p (d * cmod a) + 2 ^ p * near_bits p (Arg a))"

lemma ent_code_parts:
  fixes A :: "complex Matrix.mat" and n p k :: nat and d :: real
  defines "a \<equiv> \<lambda>k. if k div n = k mod n then 0 else A $$ (k div n, k mod n)"
  shows "ent_code p n d A k mod 2 ^ p = near_bits p (d * cmod (a k))"
    "ent_code p n d A k div 2 ^ p = near_bits p (Arg (a k))"
    "ent_code p n d A k < 2 ^ (2 * p)"
proof -
  have u: "near_bits p (d * cmod (a k)) < 2 ^ p" and w: "near_bits p (Arg (a k)) < 2 ^ p" by (simp_all add: near_bits)
  have e: "ent_code p n d A k = near_bits p (d * cmod (a k)) + 2 ^ p * near_bits p (Arg (a k))"
    by (simp add: ent_code_def a_def Let_def)
  show "ent_code p n d A k mod 2 ^ p = near_bits p (d * cmod (a k))" unfolding e using u by simp
  show "ent_code p n d A k div 2 ^ p = near_bits p (Arg (a k))" unfolding e using u by simp
  have "near_bits p (d * cmod (a k)) + 2 ^ p * near_bits p (Arg (a k)) < 2 ^ p + 2 ^ p * near_bits p (Arg (a k))"
    using u by simp
  also have "\<dots> = 2 ^ p * (near_bits p (Arg (a k)) + 1)" by simp
  also have "\<dots> \<le> 2 ^ p * 2 ^ p" using w by (intro mult_le_mono2) simp
  also have "\<dots> = 2 ^ (2 * p)" by (simp add: power_add[symmetric] mult_2)
  finally show "ent_code p n d A k < 2 ^ (2 * p)" unfolding e .
qed

text \<open>The rounded entry gate is $6\pi/2^p$-close to the exact one.\<close>

theorem ent_gate_rounded: "ent_gate n d A \<approx>\<^bsub>6 * pi / 2 ^ p\<^esub> ent_rounded p (n * n) (ent_code p n d A)"
proof -
  let ?e = "2 * pi / 2 ^ p :: real"
  have "ent_block d A (k div n) (k mod n) \<approx>\<^bsub>?e + ?e + ?e\<^esub>
      rblock (ang p (ent_code p n d A k mod 2 ^ p)) (ang p (ent_code p n d A k div 2 ^ p))" for k
    unfolding ent_block_rblock ent_code_parts by (rule rblock_close) (simp_all add: near_bits)
  moreover have "?e + ?e + ?e = 6 * pi / 2 ^ p" by simp
  ultimately show ?thesis unfolding ent_gate_def ent_rounded_def
    by (intro ctrl_blocks_op_close) (simp_all add: ent_block_carrier)
qed

end
