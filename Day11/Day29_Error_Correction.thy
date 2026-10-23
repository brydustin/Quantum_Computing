(*  Title:   Day29_Error_Correction.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 7 November 2011 (Day 29)
*)

theory Day29_Error_Correction
  imports Day22_Convex_Sets
begin

section \<open>Day 29 (7 November 2011): classical error detection and correction\<close>

text \<open>To transmit $v\in\Z_2^n$ through a channel that may flip bits ($+1$ in $\Z_2$), one encodes
$v\mapsto\phi(v)\in\Z_2^{n+k}$, transmits, and decodes.  Examples: repetition $v\mapsto(v,v)$
detects one error but corrects none and doubles the cost; the parity check
$(a_1,\dots,a_n)\mapsto(a_1,\dots,a_n;a_1+\cdots+a_n)$ detects one error cheaply; the Hamming
$[7,1,3]$ code detects and corrects one error (theory Day29\_Classical\_Codes: the code as
written detects one error but cannot correct it; the $[7,4,3]$ code corrects one).
\begin{notesdef}
The \emph{Hamming weight} $\norm w$ of $w\in\Z_2^m$ is its number of non-zero entries; the
weight of a code $S\subseteq\Z_2^m$ is $\min\{\norm{v-w}:v\neq w\in S\}$, the least number of
errors turning one code word into another; for a subspace code it is $\min\{\norm v:0\neq v\in S\}$.
\end{notesdef}
Decoding amounts to choosing a left inverse of $\phi$ (different left inverses correct
differently); the best binary codes are cyclic codes, ideals in $\Z_2[x]/\langle x^m-1\rangle$
(not formalised).\<close>

subsection \<open>Binary strings, Hamming weight and distance\<close>

definition hamming_weight :: "nat list \<Rightarrow> nat" where
  "hamming_weight v \<equiv> length (filter (\<lambda>b. b \<noteq> 0) v)"

definition hamming_dist :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "hamming_dist v w \<equiv> hamming_weight (map2 (\<lambda>a b. (a + b) mod 2) v w)"

lemma hamming_weight_Nil [simp]: "hamming_weight [] = 0"
  by (simp add: hamming_weight_def)

lemma hamming_weight_Cons:
  "hamming_weight (a # v)
     = (if a \<noteq> 0 then Suc (hamming_weight v) else hamming_weight v)"
  by (simp add: hamming_weight_def)

lemma hamming_dist_Nil [simp]:
  "hamming_dist [] [] = 0"
  by (simp add: hamming_dist_def)

lemma hamming_dist_Cons:
  "hamming_dist (a # v) (b # w)
     = (if (a + b) mod 2 \<noteq> 0
        then Suc (hamming_dist v w)
        else hamming_dist v w)"
  by (simp add: hamming_dist_def hamming_weight_Cons)

text \<open>The weight counts the ones, and $d(v,w)=\mathrm{wt}(v+w)$ counts the positions where $v$ and $w$
differ: $d(0110,1100)=\mathrm{wt}(1010)=2$.\<close>

lemma hamming_dist_symm:
  assumes "length v = length w"
  shows "hamming_dist v w = hamming_dist w v"
  using assms
proof (induction v arbitrary: w)
  case Nil thus ?case by (cases w) simp_all
next
  case (Cons a v)
  then obtain b ws where w_eq: "w = b # ws"
    by (cases w) auto
  with Cons.prems have len_eq: "length v = length ws" by simp
  show ?case
    using Cons.IH[OF len_eq] w_eq
    by (simp add: hamming_dist_Cons add.commute)
qed

lemma hamming_dist_zero:
  assumes lenw:   "length v = length w"
      and bits_v: "\<forall>x \<in> set v. x < 2"
      and bits_w: "\<forall>x \<in> set w. x < 2"
  shows "hamming_dist v w = 0 \<longleftrightarrow> v = w"
  using lenw bits_v bits_w
proof (induction v arbitrary: w)
  case Nil
  hence "w = []" by (cases w) auto
  thus ?case by simp
next
  case (Cons a v)
  obtain b ws where w_eq: "w = b # ws"
    using Cons.prems(1) by (cases w) auto
  have len_eq: "length v = length ws"
    using Cons.prems(1) w_eq by simp
  have a_lt: "a < 2" using Cons.prems(2) by simp
  have b_lt: "b < 2" using Cons.prems(3) w_eq by simp
  have bits_v': "\<forall>x \<in> set v. x < 2" using Cons.prems(2) by simp
  have bits_ws: "\<forall>x \<in> set ws. x < 2" using Cons.prems(3) w_eq by simp
  have bit_eq_iff_mod: "((a + b) mod 2 = 0) \<longleftrightarrow> a = b"
    using a_lt b_lt by arith
  have IH: "hamming_dist v ws = 0 \<longleftrightarrow> v = ws"
    using Cons.IH[OF len_eq bits_v' bits_ws] .
  show ?case
    using w_eq bit_eq_iff_mod IH
    by (auto simp: hamming_dist_Cons)
qed

lemma hamming_dist_self [simp]:
  "hamming_dist v v = 0"
  by (induction v, auto simp: hamming_dist_Cons)


subsection \<open>Code distance\<close>

text \<open>A code of distance at least $2t+1$ can correct $t$ errors (recorded as the definition
\<open>corrects_errors\<close>; the decoding theorem itself is not formalised).\<close>

definition code_distance :: "nat list set \<Rightarrow> nat" where
  "code_distance code \<equiv>
     if (\<exists>v \<in> code. \<exists>w \<in> code. v \<noteq> w)
     then Min {hamming_dist v w | v w. v \<in> code \<and> w \<in> code \<and> v \<noteq> w}
     else 0"

definition corrects_errors :: "nat list set \<Rightarrow> nat \<Rightarrow> bool" where
  "corrects_errors code t \<equiv> code_distance code \<ge> 2*t + 1"


subsection \<open>The parity-check and repetition codes\<close>

text \<open>Parity check: append the sum of the bits; any single error changes the code word.
Repetition doubles Hamming distances.\<close>

definition parity_bit :: "nat list \<Rightarrow> nat" where
  "parity_bit v \<equiv> foldr (\<lambda>a b. (a + b) mod 2) v 0"

definition parity_check_encode :: "nat list \<Rightarrow> nat list" where
  "parity_check_encode v \<equiv> v @ [parity_bit v]"

lemma length_parity_check_encode [simp]:
  "length (parity_check_encode v) = length v + 1"
  by (simp add: parity_check_encode_def)

lemma hamming_weight_pos_iff:
  "0 < hamming_weight v \<longleftrightarrow> (\<exists>x \<in> set v. x \<noteq> 0)"
  by (induction v, auto simp: hamming_weight_Cons)

lemma hamming_dist_pos_iff:
  assumes lenw:   "length v = length w"
      and bits_v: "\<forall>x \<in> set v. x < 2"
      and bits_w: "\<forall>x \<in> set w. x < 2"
  shows "0 < hamming_dist v w \<longleftrightarrow> v \<noteq> w"
  using hamming_dist_zero[OF lenw bits_v bits_w] by linarith

lemma parity_bit_lt_2: "parity_bit v < 2"
  by (induction v, auto simp: parity_bit_def)

lemma parity_check_encode_binary:
  assumes "\<forall>x \<in> set v. x < 2"
  shows "\<forall>x \<in> set (parity_check_encode v). x < 2"
  using assms parity_bit_lt_2
  by (auto simp: parity_check_encode_def)


text \<open>The parity check $v\mapsto(v,\sum_iv_i)$ produces words of even weight; one flipped bit makes
the weight odd, so a single error is detected, though not located.\<close>

lemma parity_check_detects_one_error:
  assumes lenE:   "length e = length v + 1"
      and bits_v: "\<forall>x \<in> set v. x < 2"
      and bits_e: "\<forall>x \<in> set e. x < 2"
      and weight: "hamming_weight e = 1"
  shows "parity_check_encode v
           \<noteq> map2 (\<lambda>a b. (a + b) mod 2) (parity_check_encode v) e"
proof
  let ?c = "parity_check_encode v"
  let ?d = "map2 (\<lambda>a b. (a + b) mod 2) ?c e"
  assume eq: "?c = ?d"

  have len_c: "length ?c = length v + 1" by simp

  (* The error is binary with exactly one nonzero entry, hence e ! i = 1 there. *)
  have "0 < hamming_weight e" using weight by simp
  hence "\<exists>x \<in> set e. x \<noteq> 0" by (simp add: hamming_weight_pos_iff)
  then obtain x where x_in: "x \<in> set e" and x_nz: "x \<noteq> 0" by blast
  from x_in obtain i where i_lt: "i < length e" and x_eq: "e ! i = x"
    by (metis in_set_conv_nth)
  from x_in bits_e have x_lt: "x < 2" by simp
  from x_nz x_lt x_eq have ei_one: "e ! i = 1" by linarith

  have i_lt_c: "i < length ?c" using i_lt lenE by simp

  (* The codeword is binary, so its i-th entry is in {0,1}. *)
  have ci_bin: "?c ! i < 2"
  proof -
    have "?c ! i \<in> set ?c"
      using i_lt_c by (rule nth_mem)
    thus ?thesis
      using parity_check_encode_binary[OF bits_v] by blast
  qed

  (* The XOR'ed word at index i is (?c ! i + e ! i) mod 2. *)
  have d_at_i: "?d ! i = (?c ! i + e ! i) mod 2"
    using i_lt i_lt_c lenE by simp

  have eq_i: "?c ! i = (?c ! i + 1) mod 2"
    using eq d_at_i ei_one by simp
  thus False using ci_bin by presburger
qed


definition repetition_encode :: "nat list \<Rightarrow> nat list" where
  "repetition_encode v \<equiv> v @ v"

text \<open>Repetition $v\mapsto(v,v)$ doubles every distance, $d((v,v),(w,w))=2\,d(v,w)$.\<close>

lemma length_repetition_encode [simp]:
  "length (repetition_encode v) = 2 * length v"
  by (simp add: repetition_encode_def)

lemma hamming_dist_repetition_doubles:
  assumes "length v = length w"
  shows "hamming_dist (repetition_encode v) (repetition_encode w)
           = 2 * hamming_dist v w"
  using assms
  unfolding repetition_encode_def hamming_dist_def hamming_weight_def
  by (simp add: zip_append1 zip_append2 mult_2)

end
