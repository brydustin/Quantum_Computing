theory Day29_Subspace_Codes
  imports Day29_Classical_Codes
begin

section \<open>Day 29: Hamming distance and subspace codes (D29-4)\<close>

lemma hamming_dist_xor: "hamming_dist v w = hamming_weight (xor_word v w)"
  by (simp add: hamming_dist_def xor_word_def)

text \<open>The triangle inequality for words of bits of equal length.\<close>

lemma hamming_dist_triangle:
  assumes "length u = length v" "length v = length w"
      and "\<forall>x \<in> set u. x < 2" "\<forall>x \<in> set v. x < 2" "\<forall>x \<in> set w. x < 2"
  shows "hamming_dist u w \<le> hamming_dist u v + hamming_dist v w"
  using assms
proof (induction u arbitrary: v w)
  case Nil thus ?case by simp
next
  case (Cons a u)
  then obtain b v' c w' where v: "v = b # v'" and w: "w = c # w'"
    by (cases v; cases w) auto
  have IH: "hamming_dist u w' \<le> hamming_dist u v' + hamming_dist v' w'"
    using Cons.IH[of v' w'] Cons.prems v w by simp
  have abc: "a < 2" "b < 2" "c < 2" using Cons.prems v w by auto
  show ?case unfolding v w hamming_dist_Cons using IH abc
    by (auto simp: less_2_cases_iff)
qed

text \<open>For a subspace code (closed under addition mod 2) the distance is the least weight of a
nonzero code word.\<close>

definition zero_word :: "nat \<Rightarrow> nat list" where
  "zero_word m = replicate m 0"

text \<open>Words add coordinatewise mod $2$: $v+v=0$, $v+0=v$, and $v+w=0$ iff $v=w$.  For a code closed
under $+$ the distance is therefore the least weight of a non-zero code word,
\[ d(S)=\min_{v\ne w\in S}\mathrm{wt}(v+w)=\min_{0\ne u\in S}\mathrm{wt}(u). \]\<close>

lemma xor_word_self: "xor_word v v = zero_word (length v)"
  by (induction v) (simp_all add: xor_word_def zero_word_def)

lemma xor_word_zero: "\<forall>x \<in> set v. x < 2 \<Longrightarrow> xor_word v (zero_word (length v)) = v"
  by (induction v) (auto simp: xor_word_def zero_word_def)

lemma xor_word_eq_zero_iff:
  assumes "length v = length w" "\<forall>x \<in> set v. x < 2" "\<forall>x \<in> set w. x < 2"
  shows "xor_word v w = zero_word (length v) \<longleftrightarrow> v = w"
  using assms
proof (induction v arbitrary: w)
  case Nil thus ?case by (simp add: xor_word_def zero_word_def)
next
  case (Cons a v)
  then obtain b w' where w: "w = b # w'" by (cases w) auto
  have ab: "a < 2" "b < 2" using Cons.prems w by auto
  have IH: "xor_word v w' = zero_word (length v) \<longleftrightarrow> v = w'" using Cons.IH[of w'] Cons.prems w by simp
  show ?case using IH ab unfolding w by (auto simp: xor_word_def zero_word_def less_2_cases_iff)
qed

lemma hamming_weight_zero_word [simp]: "hamming_weight (zero_word m) = 0"
  by (simp add: hamming_weight_def zero_word_def)

lemma hamming_weight_eq_zero_iff: "\<forall>x \<in> set v. x < 2 \<Longrightarrow> hamming_weight v = 0 \<longleftrightarrow> v = zero_word (length v)"
  by (induction v) (auto simp: hamming_weight_def zero_word_def)

definition subspace_code :: "nat \<Rightarrow> nat list set \<Rightarrow> bool" where
  "subspace_code m S \<longleftrightarrow> (\<forall>v \<in> S. length v = m \<and> (\<forall>x \<in> set v. x < 2))
                         \<and> (\<forall>v \<in> S. \<forall>w \<in> S. xor_word v w \<in> S)"

lemma xor_word_bits: "\<forall>x \<in> set (xor_word v w). x < 2"
  by (auto simp: xor_word_def set_zip)

theorem subspace_code_distance:
  assumes S: "subspace_code m S" and fin: "finite S" and two: "\<exists>v \<in> S. \<exists>w \<in> S. v \<noteq> w"
  shows "code_distance S = Min {hamming_weight v | v. v \<in> S \<and> v \<noteq> zero_word m}"
proof -
  have len: "\<And>v. v \<in> S \<Longrightarrow> length v = m" and bits: "\<And>v. v \<in> S \<Longrightarrow> \<forall>x \<in> set v. x < 2"
    and cl: "\<And>v w. v \<in> S \<Longrightarrow> w \<in> S \<Longrightarrow> xor_word v w \<in> S" using S unfolding subspace_code_def by blast+
  obtain v0 where v0: "v0 \<in> S" using two by blast
  have z: "zero_word m \<in> S" using cl[OF v0 v0] xor_word_self[of v0] len[OF v0] by simp
  have "{hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w} = {hamming_weight v | v. v \<in> S \<and> v \<noteq> zero_word m}"
  proof (intro equalityI subsetI)
    fix d assume "d \<in> {hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w}"
    then obtain v w where vw: "v \<in> S" "w \<in> S" "v \<noteq> w" and d: "d = hamming_dist v w" by blast
    have "xor_word v w \<noteq> zero_word m"
      using xor_word_eq_zero_iff[of v w] len[OF vw(1)] len[OF vw(2)] bits[OF vw(1)] bits[OF vw(2)] vw(3) by simp
    thus "d \<in> {hamming_weight v | v. v \<in> S \<and> v \<noteq> zero_word m}"
      using cl[OF vw(1,2)] unfolding d hamming_dist_xor by blast
  next
    fix d assume "d \<in> {hamming_weight v | v. v \<in> S \<and> v \<noteq> zero_word m}"
    then obtain v where v: "v \<in> S" "v \<noteq> zero_word m" and d: "d = hamming_weight v" by blast
    have "hamming_dist v (zero_word m) = hamming_weight v"
      unfolding hamming_dist_xor using xor_word_zero[OF bits[OF v(1)]] len[OF v(1)] by simp
    thus "d \<in> {hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w}" using v z d by force
  qed
  thus ?thesis using two unfolding code_distance_def by simp
qed

text \<open>A code of distance at least $2t+1$ corrects $t$ errors: a received word is within distance
$t$ of at most one code word.\<close>

theorem corrects_errors_unique_decoding:
  assumes ce: "corrects_errors S t" and fin: "finite S"
      and S: "\<forall>v \<in> S. length v = m \<and> (\<forall>x \<in> set v. x < 2)"
      and r: "length r = m" "\<forall>x \<in> set r. x < 2"
      and c: "c \<in> S" "hamming_dist r c \<le> t" and c': "c' \<in> S" "hamming_dist r c' \<le> t"
  shows "c = c'"
proof (rule ccontr)
  assume ne: "c \<noteq> c'"
  have lc: "length c = m" "length c' = m" and bc: "\<forall>x \<in> set c. x < 2" "\<forall>x \<in> set c'. x < 2"
    using S c(1) c'(1) by auto
  have "hamming_dist c c' \<le> hamming_dist c r + hamming_dist r c'"
    by (rule hamming_dist_triangle) (use lc r bc in auto)
  also have "hamming_dist c r = hamming_dist r c" by (rule hamming_dist_symm) (use lc r in simp)
  finally have le: "hamming_dist c c' \<le> 2 * t" using c(2) c'(2) by simp
  have fin2: "finite {hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w}"
  proof -
    have "{hamming_dist v w | v w. v \<in> S \<and> w \<in> S \<and> v \<noteq> w} \<subseteq> (\<lambda>(v, w). hamming_dist v w) ` (S \<times> S)" by auto
    thus ?thesis using fin by (rule finite_subset[OF _ finite_imageI[OF finite_cartesian_product]]) (rule fin)
  qed
  have "code_distance S \<le> hamming_dist c c'"
    unfolding code_distance_def using c(1) c'(1) ne fin2 by (auto intro!: Min_le)
  thus False using ce le unfolding corrects_errors_def by simp
qed

end
