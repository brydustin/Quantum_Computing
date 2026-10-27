(*  Title:   Day29_Error_Correction.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 7 November 2011 (Day 29)
*)

theory Day29_Error_Correction
  imports Essential_Functional_Analysis.Matrix_Lemmas
begin

section \<open>Day 29 (7 November 2011): classical error detection and correction\<close>

text \<open>To transmit $v\in\Z_2^n$ through a channel that may flip bits ($+1$ in $\Z_2$), one encodes
$v\mapsto\phi(v)\in\Z_2^{n+k}$, transmits, and decodes.  Examples: repetition $v\mapsto(v,v)$
detects one error but corrects none and doubles the cost; the parity check
$(a_1,\dots,a_n)\mapsto(a_1,\dots,a_n;a_1+\cdots+a_n)$ detects one error cheaply; the Hamming
$[7,1,3]$ code detects and corrects one error (below: the code as written detects one error
but cannot correct it; the $[7,4,3]$ code corrects one).
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

lemma hamming_dist_repetition_doubles:
  assumes "length v = length w"
  shows "hamming_dist (repetition_encode v) (repetition_encode w)
           = 2 * hamming_dist v w"
  using assms
  unfolding repetition_encode_def hamming_dist_def hamming_weight_def
  by (simp add: zip_append1 zip_append2 mult_2)

subsection \<open>More on the repetition code\<close>

lemma hamming_weight_append:
  "hamming_weight (xs @ ys) = hamming_weight xs + hamming_weight ys"
  by (simp add: hamming_weight_def)

lemma hamming_weight_repetition_encode:
  "hamming_weight (repetition_encode v) = 2 * hamming_weight v"
  by (simp add: repetition_encode_def hamming_weight_append)

subsection \<open>Classical codes over $\mathbb Z_2$\<close>

text \<open>Days 29--30: classical codes over $\mathbb Z_2$.  Words are lists over $\{0,1\}$; all
finite checks are decided by \<open>code_simp\<close> (proof-producing evaluation, no oracle).\<close>

definition bin_words :: "nat \<Rightarrow> nat list set" where
  "bin_words n = set (List.n_lists n [0, 1])"

definition xor_word :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "xor_word v w = map2 (\<lambda>a b. (a + b) mod 2) v w"

subsubsection \<open>The notes' ``Hamming [7,1,3]'' code does not correct one error\<close>

text \<open>The notes encode $(a_1,\dots,a_7)\mapsto(a_1,\dots,a_7;\,a_1+a_2+a_3+a_4;\,a_1+a_2+a_5+a_6;
\,a_1+a_3+a_5+a_7)$ and claim it detects and corrects one error.  It detects one error, but two
codewords are at distance $2$: the word $e_4$ is at distance $1$ from the codewords of $0$ and
of $e_4$, so no decoder corrects every single error.\<close>

definition notes_hamming_encode :: "nat list \<Rightarrow> nat list" where
  "notes_hamming_encode a = a @ [(a!0 + a!1 + a!2 + a!3) mod 2, (a!0 + a!1 + a!4 + a!5) mod 2, (a!0 + a!2 + a!4 + a!6) mod 2]"

definition notes_hamming_code :: "nat list set" where
  "notes_hamming_code = notes_hamming_encode ` bin_words 7"

definition flip_at :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "flip_at i w = w[i := (w!i + 1) mod 2]"

lemma notes_hamming_code_iff:
  "w \<in> notes_hamming_code \<longleftrightarrow> take 7 w \<in> bin_words 7 \<and> w = notes_hamming_encode (take 7 w)"
proof
  assume "w \<in> notes_hamming_code"
  then obtain a where a: "a \<in> bin_words 7" and w: "w = notes_hamming_encode a" unfolding notes_hamming_code_def by blast
  have "length a = 7" using a unfolding bin_words_def by (simp add: set_n_lists)
  hence "take 7 w = a" unfolding w notes_hamming_encode_def by simp
  thus "take 7 w \<in> bin_words 7 \<and> w = notes_hamming_encode (take 7 w)" using a w by simp
next
  assume "take 7 w \<in> bin_words 7 \<and> w = notes_hamming_encode (take 7 w)"
  thus "w \<in> notes_hamming_code" unfolding notes_hamming_code_def by (metis image_eqI)
qed

lemma bin_words_iff: "w \<in> bin_words n \<longleftrightarrow> length w = n \<and> set w \<subseteq> {0, 1}"
  unfolding bin_words_def by (simp add: set_n_lists)

lemma bin_nth_lt2: "set v \<subseteq> {0,1} \<Longrightarrow> k < length v \<Longrightarrow> v ! k < (2::nat)"
proof -
  assume "set v \<subseteq> {0,1}" "k < length v"
  hence "v ! k \<in> {0,1}" using nth_mem by blast
  thus ?thesis by auto
qed

lemma xor_word_length [simp]: "length (xor_word v w) = min (length v) (length w)"
  by (simp add: xor_word_def)

lemma xor_word_nth: "k < length v \<Longrightarrow> k < length w \<Longrightarrow> xor_word v w ! k = (v ! k + w ! k) mod 2"
  by (simp add: xor_word_def)

lemma xor_word_cancel:
  assumes "length c = length v" "length c = length w" "set v \<subseteq> {0,1}" "set w \<subseteq> {0,1}"
  shows "xor_word c v = xor_word c w \<longleftrightarrow> v = w"
proof
  assume e: "xor_word c v = xor_word c w"
  show "v = w"
  proof (rule nth_equalityI)
    show "length v = length w" using assms by simp
    fix k assume k: "k < length v"
    have "(c ! k + v ! k) mod 2 = (c ! k + w ! k) mod 2"
      using arg_cong[OF e, of "\<lambda>x. x ! k"] k assms by (simp add: xor_word_nth)
    moreover have "v ! k < 2" "w ! k < 2" using bin_nth_lt2 assms k by auto
    ultimately show "v ! k = w ! k" by presburger
  qed
qed simp

lemma mod2_eq_iff: "(p::nat) mod 2 = q mod 2 \<longleftrightarrow> (even p \<longleftrightarrow> even q)"
  by (metis even_iff_mod_2_eq_zero mod2_eq_if)

text \<open>The encoding is linear over $\mathbb Z_2$.\<close>

lemma notes_hamming_encode_xor:
  assumes "length a = 7" "length b = 7"
  shows "notes_hamming_encode (xor_word a b) = xor_word (notes_hamming_encode a) (notes_hamming_encode b)"
proof (rule nth_equalityI)
  show "length (notes_hamming_encode (xor_word a b)) = length (xor_word (notes_hamming_encode a) (notes_hamming_encode b))"
    using assms by (simp add: notes_hamming_encode_def)
  fix k assume "k < length (notes_hamming_encode (xor_word a b))"
  hence k: "k < 10" using assms by (simp add: notes_hamming_encode_def)
  have "k < 7 \<or> k = 7 \<or> k = 8 \<or> k = 9" using k by auto
  thus "notes_hamming_encode (xor_word a b) ! k = xor_word (notes_hamming_encode a) (notes_hamming_encode b) ! k"
    using assms by (elim disjE; simp add: notes_hamming_encode_def xor_word_nth nth_append mod2_eq_iff even_add; argo?)
qed

lemma flip_at_xor:
  assumes "set c \<subseteq> {0,1}" "i < length c"
  shows "flip_at i c = xor_word c ((replicate (length c) 0)[i := 1])"
proof (rule nth_equalityI)
  fix k assume "k < length (flip_at i c)"
  hence k: "k < length c" by (simp add: flip_at_def)
  have "c ! k < 2" using bin_nth_lt2[OF assms(1) k] .
  thus "flip_at i c ! k = xor_word c ((replicate (length c) 0)[i := 1]) ! k"
    using k assms(2) by (cases "k = i") (simp_all add: flip_at_def xor_word_nth)
qed (simp add: flip_at_def)

theorem notes_hamming_detects_one_error:
  "\<forall>c \<in> notes_hamming_code. \<forall>i < 10. flip_at i c \<notin> notes_hamming_code"
proof (intro ballI allI impI)
  fix c i assume c: "c \<in> notes_hamming_code" and i: "i < (10::nat)"
  then obtain a where a: "a \<in> bin_words 7" and ce: "c = notes_hamming_encode a" unfolding notes_hamming_code_def by blast
  have al: "length a = 7" and ab: "set a \<subseteq> {0,1}" using a unfolding bin_words_iff by blast+
  have cl: "length c = 10" and cb: "set c \<subseteq> {0,1}" using al ab unfolding ce notes_hamming_encode_def by auto
  define e where "e = (replicate 10 (0::nat))[i := 1]"
  have el: "length e = 10" and eb: "set e \<subseteq> {0,1}" unfolding e_def using set_update_subset_insert by fastforce+
  have te: "take 7 e \<in> bin_words 7" using eb el unfolding bin_words_iff by (auto dest: in_set_takeD)
  have unit: "e \<noteq> notes_hamming_encode (take 7 e)"
  proof -
    have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9" using i by auto
    thus ?thesis unfolding e_def notes_hamming_encode_def by (elim disjE; hypsubst; code_simp)
  qed
  have fe: "flip_at i c = xor_word c e" unfolding e_def using flip_at_xor[OF cb] i cl by simp
  have tk: "take 7 (xor_word c e) = xor_word a (take 7 e)"
    unfolding ce xor_word_def notes_hamming_encode_def using al by (simp add: take_map take_zip)
  have "notes_hamming_encode (take 7 (flip_at i c)) = xor_word c (notes_hamming_encode (take 7 e))"
    unfolding fe tk using notes_hamming_encode_xor[OF al, of "take 7 e"] el ce by simp
  moreover have "set (notes_hamming_encode (take 7 e)) \<subseteq> {0,1}" "length (notes_hamming_encode (take 7 e)) = 10"
    using te unfolding bin_words_iff notes_hamming_encode_def by auto
  ultimately have "flip_at i c = notes_hamming_encode (take 7 (flip_at i c)) \<longleftrightarrow> e = notes_hamming_encode (take 7 e)"
    unfolding fe using xor_word_cancel[OF _ _ eb] cl el by simp
  thus "flip_at i c \<notin> notes_hamming_code" using unit notes_hamming_code_iff by blast
qed

theorem notes_hamming_ambiguous_word:
  defines "w \<equiv> [0,0,0,1,0,0,0,0,0,0]"
  shows "notes_hamming_encode (replicate 7 0) \<in> notes_hamming_code"
    and "notes_hamming_encode [0,0,0,1,0,0,0] \<in> notes_hamming_code"
    and "notes_hamming_encode (replicate 7 0) \<noteq> notes_hamming_encode [0,0,0,1,0,0,0]"
    and "hamming_dist (notes_hamming_encode (replicate 7 0)) w = 1"
    and "hamming_dist (notes_hamming_encode [0,0,0,1,0,0,0]) w = 1"
  unfolding w_def notes_hamming_code_def bin_words_def by code_simp+

theorem notes_hamming_not_correcting: "\<not> corrects_errors notes_hamming_code 1"
proof -
  let ?D = "{hamming_dist v w | v w. v \<in> notes_hamming_code \<and> w \<in> notes_hamming_code \<and> v \<noteq> w}"
  let ?c0 = "notes_hamming_encode (replicate 7 0)" and ?c4 = "notes_hamming_encode [0,0,0,1,0,0,0]"
  have mem: "?c0 \<in> notes_hamming_code" "?c4 \<in> notes_hamming_code" "?c0 \<noteq> ?c4"
    using notes_hamming_ambiguous_word by simp_all
  have d2: "hamming_dist ?c0 ?c4 = 2" by code_simp
  have fin: "finite notes_hamming_code" unfolding notes_hamming_code_def bin_words_def by simp
  have "finite ?D"
  proof -
    have "?D \<subseteq> (\<lambda>(v, w). hamming_dist v w) ` (notes_hamming_code \<times> notes_hamming_code)" by auto
    moreover have "finite ((\<lambda>(v, w). hamming_dist v w) ` (notes_hamming_code \<times> notes_hamming_code))" using fin by simp
    ultimately show ?thesis by (rule finite_subset)
  qed
  moreover have "2 \<in> ?D" using mem d2 by force
  ultimately have "Min ?D \<le> 2" by (rule Min_le)
  hence "code_distance notes_hamming_code \<le> 2" unfolding code_distance_def using mem by auto
  thus ?thesis unfolding corrects_errors_def by simp
qed

subsubsection \<open>The Hamming [7,4,3] code corrects one error\<close>

definition hamming74_encode :: "nat list \<Rightarrow> nat list" where
  "hamming74_encode a = a @ [(a!0 + a!1 + a!3) mod 2, (a!0 + a!2 + a!3) mod 2, (a!1 + a!2 + a!3) mod 2]"

definition hamming74_code :: "nat list set" where
  "hamming74_code = hamming74_encode ` bin_words 4"

lemma ex1_in_set: "(\<exists>!c. c \<in> set xs \<and> P c) \<longleftrightarrow> card (set (filter P xs)) = 1"
proof
  assume "\<exists>!c. c \<in> set xs \<and> P c"
  then obtain c where c: "c \<in> set xs" "P c" and u: "\<And>y. y \<in> set xs \<Longrightarrow> P y \<Longrightarrow> y = c" by blast
  have "set (filter P xs) = {c}"
  proof
    show "set (filter P xs) \<subseteq> {c}" by (auto dest: u)
    show "{c} \<subseteq> set (filter P xs)" using c by simp
  qed
  thus "card (set (filter P xs)) = 1" by simp
next
  assume "card (set (filter P xs)) = 1"
  then obtain x where eq: "set (filter P xs) = {x}" by (auto simp: card_1_singleton_iff)
  show "\<exists>!c. c \<in> set xs \<and> P c"
    by (rule ex1I[of _ x]) (use eq in \<open>auto simp: set_eq_iff\<close>)
qed

theorem hamming74_unique_decoding:
  "\<forall>w \<in> bin_words 7. \<exists>!c. c \<in> hamming74_code \<and> hamming_dist c w \<le> 1"
  unfolding hamming74_code_def bin_words_def set_map[symmetric] ex1_in_set by code_simp

theorem hamming74_corrects_one_error: "corrects_errors hamming74_code 1"
proof -
  let ?D = "{hamming_dist v w | v w. v \<in> hamming74_code \<and> w \<in> hamming74_code \<and> v \<noteq> w}"
  have ge3: "\<forall>v \<in> hamming74_code. \<forall>w \<in> hamming74_code. v \<noteq> w \<longrightarrow> 3 \<le> hamming_dist v w"
    unfolding hamming74_code_def bin_words_def set_map[symmetric] by code_simp
  have mem: "hamming74_encode [0,0,0,0] \<in> hamming74_code" "hamming74_encode [0,0,0,1] \<in> hamming74_code"
    unfolding hamming74_code_def bin_words_def set_map[symmetric] by code_simp+
  have ne: "hamming74_encode [0,0,0,0] \<noteq> hamming74_encode [0,0,0,1]" by code_simp
  have fin: "finite hamming74_code" unfolding hamming74_code_def bin_words_def by simp
  have "finite ?D"
  proof -
    have "?D \<subseteq> (\<lambda>(v, w). hamming_dist v w) ` (hamming74_code \<times> hamming74_code)" by auto
    moreover have "finite ((\<lambda>(v, w). hamming_dist v w) ` (hamming74_code \<times> hamming74_code))" using fin by simp
    ultimately show ?thesis by (rule finite_subset)
  qed
  moreover have "?D \<noteq> {}" using mem ne by blast
  moreover have "\<forall>x \<in> ?D. 3 \<le> x" using ge3 by blast
  ultimately have "3 \<le> Min ?D" by simp
  thus ?thesis unfolding corrects_errors_def code_distance_def using mem ne by auto
qed

subsection \<open>Hamming distance and subspace codes (D29-4)\<close>

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

lemma hamming_weight_eq_zero_iff: "\<forall>x \<in> set v. x < 2 \<Longrightarrow> hamming_weight v = 0 \<longleftrightarrow> v = zero_word (length v)"
  by (induction v) (auto simp: hamming_weight_def zero_word_def)

definition subspace_code :: "nat \<Rightarrow> nat list set \<Rightarrow> bool" where
  "subspace_code m S \<longleftrightarrow> (\<forall>v \<in> S. length v = m \<and> (\<forall>x \<in> set v. x < 2))
                         \<and> (\<forall>v \<in> S. \<forall>w \<in> S. xor_word v w \<in> S)"

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
