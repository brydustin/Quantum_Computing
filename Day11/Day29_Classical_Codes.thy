theory Day29_Classical_Codes
  imports Quantum_Computing11
begin

text \<open>Days 29--30: classical codes over $\mathbb Z_2$.  Words are lists over $\{0,1\}$; all
finite checks are decided by \<open>code_simp\<close> (proof-producing evaluation, no oracle).\<close>

definition bin_words :: "nat \<Rightarrow> nat list set" where
  "bin_words n = set (List.n_lists n [0, 1])"

definition xor_word :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "xor_word v w = map2 (\<lambda>a b. (a + b) mod 2) v w"

subsection \<open>The notes' ``Hamming [7,1,3]'' code does not correct one error\<close>

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

subsection \<open>The Hamming [7,4,3] code corrects one error\<close>

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

subsection \<open>Probabilities of undetected and uncorrected errors (Day 30)\<close>

text \<open>Each bit flips independently with probability $p$; an error pattern $e$ of weight $k$ on
$n$ bits has probability $p^k(1-p)^{n-k}$.  An error is undetected when it turns the sent
codeword into another codeword.\<close>

definition word_prob :: "real \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> real" where
  "word_prob p n e = p ^ hamming_weight e * (1 - p) ^ (n - hamming_weight e)"

definition err_prob :: "real \<Rightarrow> nat \<Rightarrow> nat list set \<Rightarrow> real" where
  "err_prob p n ES = (\<Sum>e \<in> ES. word_prob p n e)"

lemma err_prob_list: "distinct es \<Longrightarrow> err_prob p n (set es) = (\<Sum>e\<leftarrow>es. word_prob p n e)"
  unfolding err_prob_def by (simp add: sum_list_distinct_conv_sum_set)

definition rep_code :: "nat list set" where "rep_code = repetition_encode ` bin_words 3"
definition par_code :: "nat list set" where "par_code = parity_check_encode ` bin_words 3"

lemma rep_code_list: "rep_code = set (map repetition_encode (List.n_lists 3 [0, 1]))"
  unfolding rep_code_def bin_words_def by simp

lemma par_code_list: "par_code = set (map parity_check_encode (List.n_lists 3 [0, 1]))"
  unfolding par_code_def bin_words_def by simp

definition undetected :: "nat list set \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list set" where
  "undetected C n c = {e \<in> bin_words n. e \<noteq> replicate n 0 \<and> xor_word c e \<in> C}"

lemma set_filter_bin: "{e \<in> bin_words n. P e} = set (filter P (List.n_lists n [0, 1]))"
  unfolding bin_words_def by auto

text \<open>Repetition on three bits: $3p^2(1-p)^4+3p^4(1-p)^2+p^6$.\<close>

theorem repetition_undetected_prob:
  assumes c: "c \<in> rep_code"
  shows "err_prob p 6 (undetected rep_code 6 c) = 3 * p^2 * (1 - p)^4 + 3 * p^4 * (1 - p)^2 + p^6"
proof -
  let ?L = "[[1,0,0,1,0,0], [0,1,0,0,1,0], [0,0,1,0,0,1], [1,1,0,1,1,0], [1,0,1,1,0,1], [0,1,1,0,1,1], [1,1,1,1,1,1]] :: nat list list"
  have "\<forall>c \<in> rep_code. undetected rep_code 6 c = set ?L"
    unfolding rep_code_list undetected_def set_filter_bin by code_simp
  hence eqs: "undetected rep_code 6 c = set ?L" using c by blast
  have e: "err_prob p 6 (set ?L) = (\<Sum>e\<leftarrow>?L. word_prob p 6 e)" by (rule err_prob_list) code_simp
  show ?thesis unfolding eqs e by (simp add: word_prob_def hamming_weight_def eval_nat_numeral algebra_simps)
qed

text \<open>Parity on three bits: $\binom42p^2(1-p)^2+p^4$.\<close>

theorem parity_undetected_prob:
  assumes c: "c \<in> par_code"
  shows "err_prob p 4 (undetected par_code 4 c) = 6 * p^2 * (1 - p)^2 + p^4"
proof -
  let ?L = "[[1,1,0,0], [1,0,1,0], [1,0,0,1], [0,1,1,0], [0,1,0,1], [0,0,1,1], [1,1,1,1]] :: nat list list"
  have "\<forall>c \<in> par_code. undetected par_code 4 c = set ?L"
    unfolding par_code_list undetected_def set_filter_bin parity_check_encode_def parity_bit_def by code_simp
  hence eqs: "undetected par_code 4 c = set ?L" using c by blast
  have e: "err_prob p 4 (set ?L) = (\<Sum>e\<leftarrow>?L. word_prob p 4 e)" by (rule err_prob_list) code_simp
  show ?thesis unfolding eqs e by (simp add: word_prob_def hamming_weight_def eval_nat_numeral algebra_simps)
qed

text \<open>The notes compare the two for $p<\frac12$; the inequality in fact holds for all $0<p<1$.\<close>

theorem repetition_better_than_parity:
  assumes p0: "0 < p" and p1: "p < 1"
  shows "3 * p^2 * (1 - p)^4 + 3 * p^4 * (1 - p)^2 + p^6 < 6 * p^2 * (1 - p)^2 + (p::real)^4"
proof -
  define q where "q = 1 - p"
  have q0: "0 < q" and q1: "q < 1" using p0 p1 unfolding q_def by simp_all
  have "6 * p^2 * q^2 + p^4 - (3 * p^2 * q^4 + 3 * p^4 * q^2 + p^6)
        = p^2 * (3 * q^2 * (1 - q^2) + 3 * q^2 * (1 - p^2) + p^2 * (1 - p^2))"
    by (simp add: eval_nat_numeral algebra_simps)
  moreover have "0 < p^2 * (3 * q^2 * (1 - q^2) + 3 * q^2 * (1 - p^2) + p^2 * (1 - p^2))"
  proof -
    have "0 < q^2 * (1 - q^2)" using q0 q1 by (simp add: power_less_one_iff)
    moreover have "0 \<le> q^2 * (1 - p^2)" using p0 p1 by (simp add: power_le_one)
    moreover have "0 \<le> p^2 * (1 - p^2)" using p0 p1 by (simp add: power_le_one)
    ultimately show ?thesis using p0 by (intro mult_pos_pos) simp_all
  qed
  ultimately show ?thesis unfolding q_def by simp
qed

corollary repetition_better_than_parity_notes:
  "0 < p \<Longrightarrow> p < 1/2 \<Longrightarrow> 3 * p^2 * (1 - p)^4 + 3 * p^4 * (1 - p)^2 + p^6 < 6 * p^2 * (1 - p)^2 + (p::real)^4"
  by (rule repetition_better_than_parity) simp_all

text \<open>Majority rule $0\mapsto000$, $1\mapsto111$: decoding fails with probability $3p^2(1-p)+p^3$.\<close>

definition maj_decode :: "nat list \<Rightarrow> nat" where
  "maj_decode w = (if 2 \<le> sum_list w then 1 else 0)"

theorem majority_uncorrected_prob:
  assumes b: "b \<in> {0, 1}"
  shows "err_prob p 3 {e \<in> bin_words 3. maj_decode (xor_word (replicate 3 b) e) \<noteq> b}
         = 3 * p^2 * (1 - p) + p^3"
proof -
  let ?L = "[[1,1,0], [1,0,1], [0,1,1], [1,1,1]] :: nat list list"
  have "\<forall>b \<in> {0, 1::nat}. {e \<in> bin_words 3. maj_decode (xor_word (replicate 3 b) e) \<noteq> b} = set ?L"
    unfolding set_filter_bin maj_decode_def by code_simp
  hence eqs: "{e \<in> bin_words 3. maj_decode (xor_word (replicate 3 b) e) \<noteq> b} = set ?L" using b by blast
  have e: "err_prob p 3 (set ?L) = (\<Sum>e\<leftarrow>?L. word_prob p 3 e)" by (rule err_prob_list) code_simp
  show ?thesis unfolding eqs e by (simp add: word_prob_def hamming_weight_def eval_nat_numeral algebra_simps)
qed

end
