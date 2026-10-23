theory HHL_Search_Bound
  imports Compressed_Oracles.Find_Zero
begin

section \<open>The quantum search lower bound behind Theorem 4(2)\<close>

text \<open>Theorem 4(2) of the HHL paper ends with a polynomial-query quantum algorithm for a search
problem on $N=2^n$ inputs, which is impossible.  The bound is not reproved: it is
\<open>zero_finding_is_hard\<close> of the AFP entry \<open>Compressed_Oracles\<close>, stated there for a random
function $h$ and any valid oracle program with $q$ queries.  We restate it as $sN\le(5q+11)^2$
for a program finding a zero with average success $s$, the hypothesis of
\<open>search_speedup_impossible\<close> in \<open>HHL_Optimality\<close>.  The second part shows that exhaustive
search, the computation the iteration speeds up, succeeds with probability at least $1/2$ when
$|X|=|Y|=N$.\<close>

context compressed_oracle begin

theorem search_query_bound:
  fixes program :: \<open>('mem, 'x, 'y) program\<close> and adv_output :: \<open>'x update \<Rightarrow> 'mem update\<close> and s :: real
  assumes \<open>valid_program program\<close> and \<open>norm initial_state = 1\<close> and \<open>register adv_output\<close>
    and succ: \<open>s \<le> (\<Sum>h\<in>UNIV. \<Sum>x|h x = 0. measurement_probability adv_output (exec_program h program initial_state) x) / CARD('x \<Rightarrow> 'y)\<close>
  shows \<open>s * N \<le> (5 * real (query_count program) + 11)\<^sup>2\<close>
proof -
  have \<open>s \<le> (5 * real (query_count program) + 11)\<^sup>2 / N\<close>
    using succ zero_finding_is_hard[OF assms(1-3)] by linarith
  moreover have \<open>0 < real N\<close> using Nneq0 by (simp only: of_nat_0_less_iff gr0I)
  ultimately show ?thesis by (simp add: pos_le_divide_eq)
qed

end

text \<open>Exhaustive search finds a zero unless $h$ has none: $(N-1)^{|X|}$ of the $N^{|X|}$ functions.\<close>

lemma card_zero_free: \<open>card {h :: 'x::finite \<Rightarrow> 'y::{finite,zero}. \<forall>x. h x \<noteq> 0} = (CARD('y) - 1) ^ CARD('x)\<close>
proof -
  have \<open>{h :: 'x \<Rightarrow> 'y. \<forall>x. h x \<noteq> 0} = PiE UNIV (\<lambda>_. UNIV - {0})\<close> by (auto simp: PiE_UNIV_domain)
  moreover have \<open>card (PiE (UNIV :: 'x set) (\<lambda>_. UNIV - {0 :: 'y})) = (CARD('y) - 1) ^ CARD('x)\<close>
    by (simp add: card_PiE card_Diff_singleton)
  ultimately show ?thesis by simp
qed

lemma no_zero_rare:
  fixes N :: nat assumes \<open>1 \<le> N\<close>
  shows \<open>(1 - 1 / real N) ^ N \<le> 1 / 2\<close>
proof -
  have \<open>(1 - 1 / real N) ^ N \<le> exp (- 1 / real N) ^ N\<close>
    using exp_ge_add_one_self[of \<open>- 1 / real N\<close>] assms by (intro power_mono) simp_all
  also have \<open>\<dots> = exp (- 1)\<close> using assms by (simp add: exp_of_nat_mult[symmetric])
  also have \<open>exp (- 1) \<le> (1 / 2 :: real)\<close>
    using exp_ge_add_one_self[of 1] by (simp add: exp_minus field_simps)
  finally show ?thesis .
qed


lemma exhaustive_success:
  assumes N: \<open>CARD('x::finite) = CARD('y::{finite,zero})\<close>
  shows \<open>1 / 2 \<le> card {h :: 'x \<Rightarrow> 'y. \<exists>x. h x = 0} / CARD('x \<Rightarrow> 'y)\<close>
proof -
  let ?N = \<open>CARD('y)\<close>
  have N1: \<open>1 \<le> ?N\<close> by (simp add: Suc_leI)
  have all: \<open>CARD('x \<Rightarrow> 'y) = ?N ^ ?N\<close> using N by (simp add: card_fun)
  have split: \<open>card {h :: 'x \<Rightarrow> 'y. \<exists>x. h x = 0} + card {h :: 'x \<Rightarrow> 'y. \<forall>x. h x \<noteq> 0} = CARD('x \<Rightarrow> 'y)\<close>
  proof -
    have \<open>{h :: 'x \<Rightarrow> 'y. \<exists>x. h x = 0} \<union> {h. \<forall>x. h x \<noteq> 0} = UNIV\<close> by auto
    moreover have \<open>{h :: 'x \<Rightarrow> 'y. \<exists>x. h x = 0} \<inter> {h. \<forall>x. h x \<noteq> 0} = {}\<close> by auto
    ultimately show ?thesis using card_Un_disjoint[of \<open>{h :: 'x \<Rightarrow> 'y. \<exists>x. h x = 0}\<close> \<open>{h. \<forall>x. h x \<noteq> 0}\<close>] by simp
  qed
  have Npos: \<open>0 < real ?N ^ ?N\<close> using N1 by simp
  let ?c = \<open>card {h :: 'x \<Rightarrow> 'y. \<exists>x. h x = 0}\<close> and ?a = \<open>(?N - 1) ^ ?N\<close>
  have \<open>?c + ?a = ?N ^ ?N\<close> using split card_zero_free[where 'x = 'x and 'y = 'y] N all by simp
  hence \<open>real (?c + ?a) = real (?N ^ ?N)\<close> by (rule arg_cong)
  hence \<open>real ?c = real ?N ^ ?N - real ?a\<close> unfolding of_nat_add of_nat_power by linarith
  hence \<open>real ?c / CARD('x \<Rightarrow> 'y) = 1 - real ?a / real ?N ^ ?N\<close> using all Npos by (simp add: field_simps)
  also have \<open>real ((?N - 1) ^ ?N) / real ?N ^ ?N = (1 - 1 / real ?N) ^ ?N\<close>
    using N1 by (simp add: of_nat_diff power_divide field_simps)
  finally show ?thesis using no_zero_rare[OF N1] by linarith
qed

end
