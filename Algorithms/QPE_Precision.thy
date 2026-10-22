theory QPE_Precision
  imports HHL_Approximate
begin

section \<open>The precision of phase estimation\<close>

text \<open>The error of outcome $j$ is the distance from $j/N$ to $\varphi$ on the circle
$\mathbb R/\mathbb Z$.  The outcomes more than $e/N$ away have total probability at most
$1/(2(e-1))$ (Nielsen and Chuang, Eq.~(5.34)), so $t=n+\lceil\log_2(2+1/(2\varepsilon))\rceil$
clock qubits give $\varphi$ to within $2^{-n}$ with probability at least $1-\varepsilon$.\<close>

definition circ_dist :: "real \<Rightarrow> real \<Rightarrow> real" where
  "circ_dist x y = \<bar>(x - y) - of_int (round (x - y))\<bar>"

lemma circ_dist_le: "circ_dist x y \<le> 1 / 2"
proof -
  have "x - y - 1 / 2 \<le> of_int (round (x - y))" "of_int (round (x - y)) \<le> x - y + 1 / 2"
    by (rule of_int_round_ge, rule of_int_round_le)
  thus ?thesis unfolding circ_dist_def abs_le_iff by linarith
qed

lemma pe_amp_int: "pe_amp N (\<phi> + of_int z) j = pe_amp N \<phi> j"
proof -
  have "cis (2 * pi * real k * (\<phi> + of_int z - real j / real N)) = cis (2 * pi * real k * (\<phi> - real j / real N))" for k
  proof -
    have e: "2 * pi * real k * (\<phi> + of_int z - real j / real N) = 2 * pi * real k * (\<phi> - real j / real N) + 2 * pi * of_int (int k * z)"
      by (simp add: algebra_simps)
    have "cis (2 * pi * of_int (int k * z)) = 1" by (rule cis_multiple_2pi) simp
    thus ?thesis unfolding e cis_mult[symmetric] by simp
  qed
  thus ?thesis unfolding pe_amp_def by simp
qed

lemma pe_amp_circ: "pe_amp N \<phi> j = pe_amp N (\<phi> - of_int (round (\<phi> - real j / real N))) j"
  using pe_amp_int[of N "\<phi> - of_int (round (\<phi> - real j / real N))" "round (\<phi> - real j / real N)" j] by simp

lemma pe_amp_circ_tail:
  assumes N: "0 < N" and d0: "0 < circ_dist \<phi> (real j / real N)"
  shows "(cmod (pe_amp N \<phi> j))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * (circ_dist \<phi> (real j / real N))\<^sup>2)"
proof -
  define \<psi> where "\<psi> = \<phi> - of_int (round (\<phi> - real j / real N))"
  have c: "circ_dist \<phi> (real j / real N) = \<bar>\<psi> - real j / real N\<bar>" unfolding circ_dist_def \<psi>_def by simp
  have d: "\<bar>\<psi> - real j / real N\<bar> \<le> 1 / 2" using circ_dist_le[of \<phi> "real j / real N"] c by simp
  have ne: "\<psi> \<noteq> real j / real N" using d0 c by auto
  have "(cmod (pe_amp N \<phi> j))\<^sup>2 = (cmod (pe_amp N \<psi> j))\<^sup>2" unfolding \<psi>_def by (simp only: pe_amp_circ[symmetric])
  also have "\<dots> \<le> 1 / (4 * (real N)\<^sup>2 * (\<psi> - real j / real N)\<^sup>2)" by (rule pe_amp_tail_sq[OF N d ne])
  also have "(\<psi> - real j / real N)\<^sup>2 = (circ_dist \<phi> (real j / real N))\<^sup>2" unfolding c by simp
  finally show ?thesis .
qed

text \<open>The nearest grid value: $j=\mathrm{round}(N\varphi)\bmod N$ is within $\frac1{2N}$ of
$\varphi$ on the circle, and is observed with probability at least $4/\pi^2$.\<close>

definition pe_round :: "nat \<Rightarrow> real \<Rightarrow> nat" where
  "pe_round N \<phi> = nat (round (real N * \<phi>) mod int N)"

lemma circ_dist_int: "circ_dist x y \<le> \<bar>x - y - of_int z\<bar>"
  unfolding circ_dist_def by (rule round_diff_minimal)

lemma pe_round_lt: "0 < N \<Longrightarrow> pe_round N \<phi> < N"
  unfolding pe_round_def by (simp add: nat_less_iff)

lemma pe_round_dist:
  assumes N: "0 < N"
  shows "circ_dist \<phi> (real (pe_round N \<phi>) / real N) \<le> 1 / (2 * real N)"
proof -
  define r where "r = round (real N * \<phi>)"
  have j: "real (pe_round N \<phi>) = of_int r - real N * of_int (r div int N)"
  proof -
    have "0 \<le> r mod int N" using N by simp
    hence "real (pe_round N \<phi>) = of_int (r mod int N)" unfolding pe_round_def r_def by simp
    also have "r mod int N = r - int N * (r div int N)" by (simp add: minus_div_mult_eq_mod[symmetric] mult.commute)
    finally show ?thesis by simp
  qed
  have "circ_dist \<phi> (real (pe_round N \<phi>) / real N) \<le> \<bar>\<phi> - real (pe_round N \<phi>) / real N - of_int (r div int N)\<bar>"
    by (rule circ_dist_int)
  also have "\<phi> - real (pe_round N \<phi>) / real N - of_int (r div int N) = (real N * \<phi> - of_int r) / real N"
    unfolding j using N by (simp add: field_simps)
  also have "\<bar>(real N * \<phi> - of_int r) / real N\<bar> \<le> (1 / 2) / real N"
  proof -
    have a: "\<bar>real N * \<phi> - of_int r\<bar> \<le> 1 / 2"
      using of_int_round_ge[of "real N * \<phi>"] of_int_round_le[of "real N * \<phi>"] unfolding r_def abs_le_iff by linarith
    have "\<bar>(real N * \<phi> - of_int r) / real N\<bar> = \<bar>real N * \<phi> - of_int r\<bar> / real N" by (simp add: abs_div)
    also have "\<dots> \<le> (1 / 2) / real N" by (rule divide_right_mono[OF a]) simp
    finally show ?thesis .
  qed
  finally show ?thesis by simp
qed

lemma pe_amp_near:
  assumes N: "0 < N" and d: "circ_dist \<phi> (real j / real N) \<le> 1 / (2 * real N)"
  shows "4 / pi\<^sup>2 \<le> (cmod (pe_amp N \<phi> j))\<^sup>2"
proof -
  define \<psi> where "\<psi> = \<phi> - of_int (round (\<phi> - real j / real N))"
  have c: "circ_dist \<phi> (real j / real N) = \<bar>\<psi> - real j / real N\<bar>" unfolding circ_dist_def \<psi>_def by simp
  have "4 / pi\<^sup>2 \<le> (cmod (pe_amp N \<psi> j))\<^sup>2" by (rule phase_estimation_bound[OF N]) (use d c in simp)
  thus ?thesis unfolding \<psi>_def by (simp only: pe_amp_circ[symmetric])
qed

subsection \<open>Sums over well-separated points\<close>

lemma sum_inv_sq_tele:
  assumes e: "1 < e"
  shows "(\<Sum>m\<in>{1..M}. 1 / (e + real m - 1)\<^sup>2) \<le> 1 / (e - 1) - 1 / (e + real M - 1)"
proof (induction M)
  case 0
  show ?case by simp
next
  case (Suc M)
  have p: "0 < e + real M - 1" using e by simp
  have "1 / (e + real M)\<^sup>2 \<le> 1 / ((e + real M - 1) * (e + real M))"
    by (rule divide_left_mono) (use p in \<open>simp_all add: power2_eq_square\<close>)
  also have "\<dots> = 1 / (e + real M - 1) - 1 / (e + real M)" using p by (simp add: field_simps)
  finally have step: "1 / (e + real M)\<^sup>2 \<le> 1 / (e + real M - 1) - 1 / (e + real M)" .
  have "(\<Sum>m\<in>{1..Suc M}. 1 / (e + real m - 1)\<^sup>2) = (\<Sum>m\<in>{1..M}. 1 / (e + real m - 1)\<^sup>2) + 1 / (e + real M)\<^sup>2"
    by (simp add: algebra_simps)
  thus ?case using Suc step by (simp add: algebra_simps)
qed

text \<open>Points above $e>1$ at mutual distance at least $1$: $\sum 1/y^2\le1/(e-1)$.\<close>

lemma sum_inv_sq_spaced:
  fixes y :: "nat \<Rightarrow> real"
  assumes J: "finite J" and e: "1 < e" and big: "\<And>j. j \<in> J \<Longrightarrow> e < y j"
      and sep: "\<And>i j. i \<in> J \<Longrightarrow> j \<in> J \<Longrightarrow> i \<noteq> j \<Longrightarrow> 1 \<le> \<bar>y i - y j\<bar>"
  shows "(\<Sum>j\<in>J. 1 / (y j)\<^sup>2) \<le> 1 / (e - 1)"
proof -
  define g where "g j = nat \<lceil>y j - e\<rceil>" for j
  define h where "h m = 1 / (e + real m - 1)\<^sup>2" for m :: nat
  have cg: "of_int \<lceil>y j - e\<rceil> - 1 < y j - e" "y j - e \<le> of_int \<lceil>y j - e\<rceil>" for j
    using ceiling_correct[of "y j - e"] by linarith+
  have g1: "1 \<le> g j" and gr: "real (g j) = of_int \<lceil>y j - e\<rceil>" if j: "j \<in> J" for j
  proof -
    have c: "0 < \<lceil>y j - e\<rceil>" using big[OF j] by simp
    have "0 < g j" unfolding g_def using c by (simp only: zero_less_nat_eq)
    thus "1 \<le> g j" by simp
    show "real (g j) = of_int \<lceil>y j - e\<rceil>" unfolding g_def using c by simp
  qed
  have inj: "inj_on g J"
  proof (rule inj_onI)
    fix i j assume i: "i \<in> J" and j: "j \<in> J" and gij: "g i = g j"
    have "of_int \<lceil>y i - e\<rceil> = (of_int \<lceil>y j - e\<rceil> :: real)" using gij gr[OF i] gr[OF j] by simp
    hence "\<bar>y i - y j\<bar> < 1" using cg[of i] cg[of j] unfolding abs_less_iff by linarith
    thus "i = j" using sep[OF i j] by force
  qed
  define M where "M = (\<Sum>j\<in>J. g j)"
  have sub: "g ` J \<subseteq> {1..M}" using g1 member_le_sum[of _ J g] J unfolding M_def by fastforce
  have "(\<Sum>j\<in>J. 1 / (y j)\<^sup>2) \<le> (\<Sum>j\<in>J. h (g j))"
  proof (rule sum_mono)
    fix j assume j: "j \<in> J"
    have p: "0 < e + real (g j) - 1" using e g1[OF j] by simp
    have lt: "e + real (g j) - 1 < y j" using cg[of j] gr[OF j] by linarith
    show "1 / (y j)\<^sup>2 \<le> h (g j)" unfolding h_def
      by (rule divide_left_mono) (use p lt in \<open>auto intro!: power_mono\<close>)
  qed
  also have "\<dots> = (\<Sum>m\<in>g ` J. h m)" by (rule sum.reindex[OF inj, symmetric, unfolded comp_def])
  also have "\<dots> \<le> (\<Sum>m\<in>{1..M}. h m)" by (rule sum_mono2[OF finite_atLeastAtMost sub]) (simp add: h_def)
  also have "\<dots> \<le> 1 / (e - 1) - 1 / (e + real M - 1)" unfolding h_def by (rule sum_inv_sq_tele[OF e])
  also have "\<dots> \<le> 1 / (e - 1)" using e by simp
  finally show ?thesis .
qed

subsection \<open>The tail bound\<close>

text \<open>The signed errors $N(\varphi-j/N)$, reduced mod $N$, are distinct points of $N\varphi+\mathbb Z$.\<close>

lemma pe_err_sep:
  fixes \<phi> :: real
  assumes N: "0 < N" and i: "i < N" and j: "j < N" and ij: "i \<noteq> j"
  defines "y \<equiv> \<lambda>j. real N * ((\<phi> - real j / real N) - of_int (round (\<phi> - real j / real N)))"
  shows "1 \<le> \<bar>y i - y j\<bar>"
proof -
  define R where "R j = round (\<phi> - real j / real N)" for j
  define z where "z = int j - int i + int N * (R j - R i)"
  have yz: "y i - y j = of_int z" unfolding y_def z_def R_def using N by (simp add: field_simps)
  have "z \<noteq> 0"
  proof
    assume z0: "z = 0"
    have D: "int N * (R i - R j) = int j - int i" using z0 unfolding z_def by (simp add: algebra_simps)
    have "\<bar>int j - int i\<bar> < int N" using i j by linarith
    hence "int N * \<bar>R i - R j\<bar> < int N * 1" using D by (simp add: abs_mult)
    hence "\<bar>R i - R j\<bar> < 1" using N by (simp only: mult_less_cancel_left)
    hence "R i = R j" by linarith
    thus False using D ij by simp
  qed
  hence "1 \<le> \<bar>z\<bar>" by linarith
  hence "(1::real) \<le> of_int \<bar>z\<bar>" by linarith
  thus ?thesis unfolding yz by simp
qed

theorem pe_tail_bound:
  assumes N: "0 < N" and e: "1 < e"
  shows "(\<Sum>j | j < N \<and> e < real N * circ_dist \<phi> (real j / real N). (cmod (pe_amp N \<phi> j))\<^sup>2) \<le> 1 / (2 * (e - 1))"
proof -
  define y where "y j = real N * ((\<phi> - real j / real N) - of_int (round (\<phi> - real j / real N)))" for j
  have cy: "real N * circ_dist \<phi> (real j / real N) = \<bar>y j\<bar>" for j
    unfolding circ_dist_def y_def using N by (simp add: abs_mult)
  define S where "S = {j. j < N \<and> e < real N * circ_dist \<phi> (real j / real N)}"
  define Sp where "Sp = {j \<in> S. 0 < y j}"
  define Sm where "Sm = {j \<in> S. y j < 0}"
  have fin: "finite S" unfolding S_def by simp
  have finp: "finite Sp" and finm: "finite Sm" using fin unfolding Sp_def Sm_def by simp_all
  have Sy: "e < \<bar>y j\<bar>" if "j \<in> S" for j using that cy unfolding S_def by simp
  have split: "S = Sp \<union> Sm" unfolding Sp_def Sm_def using Sy e by fastforce
  have disj: "Sp \<inter> Sm = {}" unfolding Sp_def Sm_def by auto
  have amp: "(cmod (pe_amp N \<phi> j))\<^sup>2 \<le> 1 / 4 * (1 / (y j)\<^sup>2)" if j: "j \<in> S" for j
  proof -
    have "0 < real N * circ_dist \<phi> (real j / real N)" using Sy[OF j] e cy[of j] by linarith
    hence c0: "0 < circ_dist \<phi> (real j / real N)" using N by (simp add: zero_less_mult_iff)
    have "(cmod (pe_amp N \<phi> j))\<^sup>2 \<le> 1 / (4 * (real N)\<^sup>2 * (circ_dist \<phi> (real j / real N))\<^sup>2)"
      by (rule pe_amp_circ_tail[OF N c0])
    also have "4 * (real N)\<^sup>2 * (circ_dist \<phi> (real j / real N))\<^sup>2 = 4 * (real N * circ_dist \<phi> (real j / real N))\<^sup>2"
      by (simp add: power_mult_distrib)
    also have "(real N * circ_dist \<phi> (real j / real N))\<^sup>2 = (y j)\<^sup>2" unfolding cy by simp
    finally show ?thesis by simp
  qed
  have sep: "1 \<le> \<bar>y i - y j\<bar>" if "i \<in> S" "j \<in> S" "i \<noteq> j" for i j
    using pe_err_sep[OF N _ _ that(3), of \<phi>] that unfolding S_def y_def by simp
  have bp: "(\<Sum>j\<in>Sp. 1 / (y j)\<^sup>2) \<le> 1 / (e - 1)"
  proof (rule sum_inv_sq_spaced[OF finp e])
    fix j assume "j \<in> Sp"
    hence "j \<in> S" "0 < y j" unfolding Sp_def by auto
    thus "e < y j" using Sy[of j] by simp
  next
    fix i j assume "i \<in> Sp" "j \<in> Sp" "i \<noteq> j"
    thus "1 \<le> \<bar>y i - y j\<bar>" using sep unfolding Sp_def by blast
  qed
  have bm: "(\<Sum>j\<in>Sm. 1 / (- y j)\<^sup>2) \<le> 1 / (e - 1)"
  proof (rule sum_inv_sq_spaced[OF finm e])
    fix j assume "j \<in> Sm"
    hence "j \<in> S" "y j < 0" unfolding Sm_def by auto
    thus "e < - y j" using Sy[of j] by simp
  next
    fix i j assume "i \<in> Sm" "j \<in> Sm" "i \<noteq> j"
    hence "1 \<le> \<bar>y i - y j\<bar>" using sep unfolding Sm_def by blast
    thus "1 \<le> \<bar>- y i - - y j\<bar>" by linarith
  qed
  have "(\<Sum>j\<in>S. (cmod (pe_amp N \<phi> j))\<^sup>2) \<le> (\<Sum>j\<in>S. 1 / 4 * (1 / (y j)\<^sup>2))" by (rule sum_mono) (rule amp)
  also have "\<dots> = 1 / 4 * (\<Sum>j\<in>Sp. 1 / (y j)\<^sup>2) + 1 / 4 * (\<Sum>j\<in>Sm. 1 / (y j)\<^sup>2)"
    unfolding split sum.union_disjoint[OF finp finm disj] by (simp add: sum_distrib_left)
  also have "\<dots> \<le> 1 / 4 * (1 / (e - 1)) + 1 / 4 * (1 / (e - 1))"
  proof -
    have "(\<Sum>j\<in>Sm. 1 / (y j)\<^sup>2) \<le> 1 / (e - 1)" using bm by simp
    thus ?thesis using bp by linarith
  qed
  also have "\<dots> = 1 / (2 * (e - 1))" using e by (simp add: field_simps)
  finally show ?thesis unfolding S_def .
qed

subsection \<open>The number of clock qubits\<close>

text \<open>Outcomes within $e/N$ of $\varphi$ have probability at least $1-1/(2(e-1))$.\<close>

theorem pe_tail_good:
  assumes N: "0 < N" and e: "1 < e"
  shows "1 - 1 / (2 * (e - 1)) \<le> (\<Sum>j | j < N \<and> real N * circ_dist \<phi> (real j / real N) \<le> e. (cmod (pe_amp N \<phi> j))\<^sup>2)"
proof -
  let ?f = "\<lambda>j. (cmod (pe_amp N \<phi> j))\<^sup>2"
  let ?G = "{j. j < N \<and> real N * circ_dist \<phi> (real j / real N) \<le> e}"
  let ?B = "{j. j < N \<and> e < real N * circ_dist \<phi> (real j / real N)}"
  have UB: "{..<N} = ?G \<union> ?B" and GB: "?G \<inter> ?B = {}" by auto
  have "1 = (\<Sum>j<N. ?f j)" by (rule pe_amp_sum_sq[OF N, symmetric])
  also have "\<dots> = sum ?f ?G + sum ?f ?B" unfolding UB by (rule sum.union_disjoint) (use GB in simp_all)
  finally have "sum ?f ?G = 1 - sum ?f ?B" by simp
  thus ?thesis using pe_tail_bound[OF N e, of \<phi>] by simp
qed

text \<open>The complementary bound: with $e=2^p$, $p=t-n$, outcomes within $2^{-n}$ of $\varphi$ have
probability at least $1-1/(2(2^p-1))$, and $2^p\ge2+1/(2\varepsilon)$ makes this $\ge1-\varepsilon$.\<close>

theorem pe_precision:
  assumes eps: "0 < \<epsilon>" and t: "t = n + nat \<lceil>log 2 (2 + 1 / (2 * \<epsilon>))\<rceil>"
  shows "1 - \<epsilon> \<le> (\<Sum>j | j < 2 ^ t \<and> circ_dist \<phi> (real j / 2 ^ t) \<le> 1 / 2 ^ n. (cmod (pe_amp (2 ^ t) \<phi> j))\<^sup>2)"
proof -
  define x where "x = 2 + 1 / (2 * \<epsilon>)"
  define p where "p = nat \<lceil>log 2 x\<rceil>"
  define e :: real where "e = 2 ^ p"
  have x2: "2 < x" unfolding x_def using eps by simp
  have xe: "x \<le> e"
  proof -
    have "log 2 x \<le> real p" unfolding p_def by linarith
    hence "2 powr log 2 x \<le> 2 powr real p" by (rule powr_mono) simp
    thus ?thesis unfolding e_def using x2 by (simp add: powr_realpow)
  qed
  have e1: "1 < e" using xe x2 by simp
  have tp: "t = n + p" unfolding t p_def x_def ..
  have mul: "(2::real) ^ t * c = e * (2 ^ n * c)" for c unfolding e_def tp by (simp add: power_add mult_ac)
  have iff: "circ_dist \<phi> (real j / 2 ^ t) \<le> 1 / 2 ^ n \<longleftrightarrow> 2 ^ t * circ_dist \<phi> (real j / 2 ^ t) \<le> e" for j
    unfolding mul using e1 by (simp add: field_simps)
  have sets: "{j. j < 2 ^ t \<and> circ_dist \<phi> (real j / 2 ^ t) \<le> 1 / 2 ^ n}
              = {j. j < 2 ^ t \<and> real (2 ^ t :: nat) * circ_dist \<phi> (real j / real (2 ^ t :: nat)) \<le> e}"
    by (simp add: iff)
  have "1 / (2 * (e - 1)) \<le> \<epsilon>"
  proof -
    have "1 / (2 * \<epsilon>) \<le> e - 1" using xe unfolding x_def by simp
    thus ?thesis using eps e1 by (simp add: field_simps)
  qed
  thus ?thesis unfolding sets using pe_tail_good[of "2 ^ t" e \<phi>] e1 by simp
qed

subsection \<open>The circuit\<close>

text \<open>Measuring the clock after phase estimation on a unit eigenvector.\<close>

lemma pe_reg_prob:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat m m" and u: "dim_vec u = m" and unit: "(\<Sum>i<m. (cmod (u $ i))\<^sup>2) = 1"
      and ev: "U *\<^sub>v u = cis (2 * pi * \<phi>) \<cdot>\<^sub>v u" and j: "j < N"
  shows "reg_prob m ((((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec (uniform_state N) u)) j
         = (cmod (pe_amp N \<phi> j))\<^sup>2"
  unfolding phase_estimation[OF U u ev] using reg_prob_tensor[OF _ u j unit, of "Matrix.vec N (pe_amp N \<phi>)"] j by simp

theorem phase_estimation_tail:
  fixes U :: "complex Matrix.mat"
  assumes N: "0 < N" and U: "U \<in> carrier_mat m m" and u: "dim_vec u = m" and unit: "(\<Sum>i<m. (cmod (u $ i))\<^sup>2) = 1"
      and ev: "U *\<^sub>v u = cis (2 * pi * \<phi>) \<cdot>\<^sub>v u" and e: "1 < e"
  shows "(\<Sum>j | j < N \<and> e < real N * circ_dist \<phi> (real j / real N).
           reg_prob m ((((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec (uniform_state N) u)) j)
         \<le> 1 / (2 * (e - 1))"
proof -
  have "(\<Sum>j | j < N \<and> e < real N * circ_dist \<phi> (real j / real N).
           reg_prob m ((((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m U *\<^sub>v tensor_vec (uniform_state N) u)) j)
        = (\<Sum>j | j < N \<and> e < real N * circ_dist \<phi> (real j / real N). (cmod (pe_amp N \<phi> j))\<^sup>2)"
    by (rule sum.cong[OF refl]) (simp add: pe_reg_prob[OF U u unit ev])
  also have "\<dots> \<le> 1 / (2 * (e - 1))" by (rule pe_tail_bound[OF N e])
  finally show ?thesis .
qed

theorem phase_estimation_precision:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat m m" and u: "dim_vec u = m" and unit: "(\<Sum>i<m. (cmod (u $ i))\<^sup>2) = 1"
      and ev: "U *\<^sub>v u = cis (2 * pi * \<phi>) \<cdot>\<^sub>v u"
      and eps: "0 < \<epsilon>" and t: "t = n + nat \<lceil>log 2 (2 + 1 / (2 * \<epsilon>))\<rceil>"
  shows "1 - \<epsilon> \<le> (\<Sum>j | j < 2 ^ t \<and> circ_dist \<phi> (real j / 2 ^ t) \<le> 1 / 2 ^ n.
           reg_prob m ((((fourier (2 ^ t))\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow (2 ^ t) m U *\<^sub>v tensor_vec (uniform_state (2 ^ t)) u)) j)"
proof -
  have "(\<Sum>j | j < 2 ^ t \<and> circ_dist \<phi> (real j / 2 ^ t) \<le> 1 / 2 ^ n.
           reg_prob m ((((fourier (2 ^ t))\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow (2 ^ t) m U *\<^sub>v tensor_vec (uniform_state (2 ^ t)) u)) j)
        = (\<Sum>j | j < 2 ^ t \<and> circ_dist \<phi> (real j / 2 ^ t) \<le> 1 / 2 ^ n. (cmod (pe_amp (2 ^ t) \<phi> j))\<^sup>2)"
    by (rule sum.cong[OF refl]) (simp add: pe_reg_prob[OF U u unit ev])
  thus ?thesis using pe_precision[OF eps t, of \<phi>] by simp
qed

end
