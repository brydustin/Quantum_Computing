theory Shifted_Laplacian
  imports Cycle_Laplacian
begin

section \<open>The shifted cycle Laplacian\<close>

text \<open>HHL needs a spectrum bounded away from $0$, and $L$ has the eigenvalue $0$.  The shift
$L + \mu I$ has the same edges and colour parts as $L$; only the diagonal phase changes.\<close>

definition slap :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "slap n \<mu> = Matrix.mat n n (\<lambda>(i, j). if i = j then complex_of_real (2 + \<mu>) else if cyc_adj n i j then - 1 else 0)"

lemma slap_carrier [simp]: "slap n \<mu> \<in> carrier_mat n n" by (simp add: slap_def)
lemma dim_slap [simp]: "dim_row (slap n \<mu>) = n" "dim_col (slap n \<mu>) = n" by (simp_all add: slap_def)

lemma slap_hermitian: "hermitian (slap n \<mu>)"
  unfolding hermitian_dagger
proof (rule eq_matI)
  fix i j assume "i < dim_row (slap n \<mu>)" "j < dim_col (slap n \<mu>)"
  hence i: "i < n" and j: "j < n" by (simp_all add: slap_def)
  show "(slap n \<mu>)\<^sup>\<dagger> $$ (i, j) = slap n \<mu> $$ (i, j)" using i j cyc_adj_sym[of n i j] by (simp add: dagger_def slap_def)
qed (simp_all add: dagger_def slap_def)

lemma slap_bound: "0 \<le> \<mu> \<Longrightarrow> i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (slap n \<mu> $$ (i, j)) \<le> 2 + \<mu>"
  by (cases "i = j") (simp_all add: slap_def del: of_real_add)

lemma slap_sym: "x < n \<Longrightarrow> y < n \<Longrightarrow> slap n \<mu> $$ (x, y) = 0 \<longleftrightarrow> slap n \<mu> $$ (y, x) = 0"
  using cyc_adj_sym[of n x y] by (simp add: slap_def)

lemma slap_edges: "0 \<le> \<mu> \<Longrightarrow> edges n (slap n \<mu>) = edges n (lap n)"
  by (auto simp: edges_def slap_def lap_def)

lemma slap_cover: "0 \<le> \<mu> \<Longrightarrow> even n \<Longrightarrow> 4 \<le> n \<Longrightarrow> edge_cover n 2 (lp n) (edges n (slap n \<mu>))"
  using lp_cover[of n] slap_edges[of \<mu> n] by simp

theorem slap_trotter:
  assumes mu: "0 \<le> \<mu>" and n: "even n" "4 \<le> n" and r: "0 < r"
  shows "evolution_product n (t / real r) (sparse_parts n (slap n \<mu>) 2 (lp n)) ^\<^sub>m r
      \<approx>\<^bsub>18 * (2 + \<mu>)\<^sup>2 * t\<^sup>2 / real r\<^esub> evolution (slap n \<mu>) t"
proof -
  have pinv: "\<And>c. c < 2 \<Longrightarrow> invol n (lp n c)" using lp_invol[OF n(1)] by blast
  have L: "0 \<le> 2 + \<mu>" using mu by simp
  have len: "length (sparse_parts n (slap n \<mu>) 2 (lp n)) = 3" by (simp add: sparse_parts_def)
  have sum: "hamiltonian_sum n (sparse_parts n (slap n \<mu>) 2 (lp n)) = slap n \<mu>"
    by (rule sparse_parts_sum[OF slap_carrier slap_sym slap_cover[OF mu n]])
  have c: "evolution_product n (t / real r) (sparse_parts n (slap n \<mu>) 2 (lp n)) ^\<^sub>m r
      \<approx>\<^bsub>2 * (real (length (sparse_parts n (slap n \<mu>) 2 (lp n))) * (2 + \<mu>) * t)\<^sup>2 / real r\<^esub>
      evolution (hamiltonian_sum n (sparse_parts n (slap n \<mu>) 2 (lp n))) t"
    by (rule trotter[OF sparse_parts_bounded[OF slap_carrier slap_hermitian pinv L slap_bound[OF mu]] r])
  have e: "2 * (real 3 * (2 + \<mu>) * t)\<^sup>2 / real r = 18 * (2 + \<mu>)\<^sup>2 * t\<^sup>2 / real r"
    by (simp add: power2_eq_square algebra_simps)
  show ?thesis using c unfolding len sum e .
qed

subsection \<open>The parts as gates\<close>

lemma lp_lt:
  assumes n: "even n" and x: "x < n"
  shows "lp n c x < n"
proof (rule ccontr)
  assume "\<not> lp n c x < n"
  hence ge: "n \<le> lp n c x" by simp
  have inv: "\<forall>x. lp n c (lp n c x) = x" "\<forall>x. n \<le> x \<longrightarrow> lp n c x = x"
    using lp_invol[OF n, of c] by (simp_all add: invol_def)
  have "lp n c (lp n c x) = lp n c x" using inv(2) ge by blast
  moreover have "lp n c (lp n c x) = x" using inv(1) by blast
  ultimately show False using x ge by simp
qed

lemma slap_colour: "0 \<le> \<mu> \<Longrightarrow> even n \<Longrightarrow> colour_part n (slap n \<mu>) (lp n c) = colour_part n (lap n) (lp n c)"
  by (rule eq_matI) (auto simp: colour_part_def one_sparse_def slap_def lap_def lp_lt)

theorem evo_diag_slap:
  assumes m: "2 \<le> m"
  shows "evolution (diag_part (2 ^ m) (slap (2 ^ m) \<mu>)) d = qw m 0 (gph ((2 + \<mu>) * d))"
proof -
  let ?n = "2 ^ m :: nat"
  note n = pow_facts[OF m]
  have qc: "qw m 0 (gph ((2 + \<mu>) * d)) \<in> carrier_mat ?n ?n" by (rule qw_carrier[OF gph_carrier n(3)])
  have "evolution (diag_part ?n (slap ?n \<mu>)) d = dia_evo ?n d (slap ?n \<mu>)"
    by (rule evolution_diag_part[OF slap_carrier slap_hermitian])
  also have "\<dots> = qw m 0 (gph ((2 + \<mu>) * d))"
  proof (rule eq_matI)
    fix r c assume "r < dim_row (qw m 0 (gph ((2 + \<mu>) * d)))" "c < dim_col (qw m 0 (gph ((2 + \<mu>) * d)))"
    hence r: "r < ?n" and c: "c < ?n" using qc by auto
    note rc = div2_eq[of r c]
    show "dia_evo ?n d (slap ?n \<mu>) $$ (r, c) = qw m 0 (gph ((2 + \<mu>) * d)) $$ (r, c)"
      unfolding qw0_index[OF n(3) gph_carrier r c] using r c rc
      by (auto simp: dia_evo_def one_sparse_def slap_def gph_def mult.commute[of d])
  qed (use qc in \<open>simp_all add: dia_evo_def one_sparse_def\<close>)
  finally show ?thesis .
qed

theorem slap_factors:
  assumes m: "2 \<le> m" and mu: "0 \<le> \<mu>"
  shows "evolution_product (2 ^ m) d (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m)))
    = qw m 0 (gph ((2 + \<mu>) * d)) * (qw m 0 (xrot d) * (pmat (2 ^ m) (inc_f (2 ^ m)) * qw m 0 (xrot d) * pmat (2 ^ m) (dec_f (2 ^ m))))"
proof -
  note n = pow_facts[OF m]
  have u: "[0..<2] = [0::nat, 1]" by (simp add: upt_rec)
  have Ac: "qw m 0 (xrot d) \<in> carrier_mat (2 ^ m) (2 ^ m)" and Bc: "qw m 0 (gph ((2 + \<mu>) * d)) \<in> carrier_mat (2 ^ m) (2 ^ m)"
    by (rule qw_carrier, simp, use n(3) in simp)+
  show ?thesis using Ac Bc
    by (simp add: sparse_parts_def u evo_diag_slap[OF m] slap_colour[OF mu n(1)] evo_colour0[OF m] evo_colour1[OF m, unfolded One_nat_def])
qed

subsection \<open>The spectrum\<close>

text \<open>Gershgorin: an eigenvalue lies within $2$ of the diagonal $2+\mu$, since each row has at most
two off-diagonal entries $-1$.\<close>

lemma cyc_nbrs: "{j. j < n \<and> j \<noteq> i \<and> cyc_adj n i j} \<subseteq> {if i + 1 < n then i + 1 else 0, if 0 < i then i - 1 else n - 1}"
  by (auto simp: cyc_adj_def)

theorem slap_spectrum:
  assumes l: "l \<in> herm_spectrum (slap n \<mu>)"
  shows "\<mu> \<le> l \<and> l \<le> 4 + \<mu>"
proof -
  obtain v where v: "dim_vec v = n" "v \<noteq> 0\<^sub>v n" "slap n \<mu> *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    using l by (auto simp: herm_spectrum_iff)
  define f where "f j = cmod (v $ j)" for j
  obtain j0 where j0: "j0 < n" "v $ j0 \<noteq> 0"
  proof -
    have "\<not> (\<forall>j<n. v $ j = 0)"
    proof
      assume "\<forall>j<n. v $ j = 0"
      hence "v = 0\<^sub>v n" using v(1) by (intro eq_vecI) simp_all
      thus False using v(2) by simp
    qed
    thus ?thesis using that by blast
  qed
  have ne: "image f {..<n} \<noteq> {}" using j0 by auto
  have "Lattices_Big.Max (image f {..<n}) \<in> image f {..<n}" by (rule Lattices_Big.Max_in) (use ne in simp_all)
  then obtain i where i: "i < n" "f i = Lattices_Big.Max (image f {..<n})" by auto
  have fmax: "f j \<le> f i" if "j < n" for j using i(2) that by simp
  have "0 < f j0" using j0(2) by (simp add: f_def)
  hence fi: "0 < f i" using fmax[OF j0(1)] by linarith
  let ?S = "{j. j < n \<and> j \<noteq> i \<and> cyc_adj n i j}"
  have row: "(slap n \<mu> *\<^sub>v v) $ i = (\<Sum>j<n. slap n \<mu> $$ (i, j) * v $ j)"
    using i(1) v(1) by (simp add: scalar_prod_def atLeast0LessThan)
  have split: "(\<Sum>j<n. slap n \<mu> $$ (i, j) * v $ j) = complex_of_real (2 + \<mu>) * v $ i - (\<Sum>j\<in>?S. v $ j)"
  proof -
    have "(\<Sum>j<n. slap n \<mu> $$ (i, j) * v $ j) = slap n \<mu> $$ (i, i) * v $ i + (\<Sum>j\<in>{..<n} - {i}. slap n \<mu> $$ (i, j) * v $ j)"
      using i(1) by (simp add: sum.remove)
    also have "(\<Sum>j\<in>{..<n} - {i}. slap n \<mu> $$ (i, j) * v $ j) = (\<Sum>j\<in>{..<n} - {i}. if cyc_adj n i j then - v $ j else 0)"
      using i(1) by (intro sum.cong) (auto simp: slap_def)
    also have "\<dots> = (\<Sum>j\<in>{j \<in> {..<n} - {i}. cyc_adj n i j}. - v $ j)"
      by (rule sum.inter_filter[symmetric]) simp
    also have "{j \<in> {..<n} - {i}. cyc_adj n i j} = ?S" by auto
    also have "(\<Sum>j\<in>?S. - v $ j) = - (\<Sum>j\<in>?S. v $ j)" by (rule sum_negf)
    finally show ?thesis using i(1) by (simp add: slap_def)
  qed
  have "(slap n \<mu> *\<^sub>v v) $ i = (complex_of_real l \<cdot>\<^sub>v v) $ i" using v(3) by simp
  also have "\<dots> = complex_of_real l * v $ i" using i(1) v(1) by simp
  finally have e1: "complex_of_real (2 + \<mu>) * v $ i - (\<Sum>j\<in>?S. v $ j) = complex_of_real l * v $ i"
    unfolding row split .
  have "(\<Sum>j\<in>?S. v $ j) = complex_of_real (2 + \<mu>) * v $ i - complex_of_real l * v $ i"
    by (simp add: e1[symmetric])
  hence eq: "(complex_of_real (2 + \<mu>) - complex_of_real l) * v $ i = (\<Sum>j\<in>?S. v $ j)"
    by (simp add: left_diff_distrib)
  have c2: "card {if i + 1 < n then i + 1 else 0, if 0 < i then i - 1 else n - 1} \<le> 2"
    by (cases "(if i + 1 < n then i + 1 else 0) = (if 0 < i then i - 1 else n - 1)") simp_all
  have cS: "card ?S \<le> 2" using card_mono[OF _ cyc_nbrs[of n i]] c2 by simp
  have cr: "complex_of_real (2 + \<mu>) - complex_of_real l = complex_of_real (2 + \<mu> - l)" by simp
  have "\<bar>2 + \<mu> - l\<bar> * f i = cmod (\<Sum>j\<in>?S. v $ j)" unfolding eq[symmetric] cr f_def
    by (simp only: norm_mult norm_of_real)
  also have "\<dots> \<le> (\<Sum>j\<in>?S. f j)" unfolding f_def by (rule norm_sum)
  also have "\<dots> \<le> (\<Sum>j\<in>?S. f i)" by (rule sum_mono) (simp add: fmax)
  also have "\<dots> = real (card ?S) * f i" by simp
  also have "\<dots> \<le> 2 * f i" using cS fi by (simp add: mult_right_mono)
  finally have "\<bar>2 + \<mu> - l\<bar> \<le> 2" using fi by simp
  thus ?thesis by linarith
qed

end
