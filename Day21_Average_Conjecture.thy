theory Day21_Average_Conjecture
  imports Day19_Choi_Theorem
begin

section \<open>Day 21: the conjecture on averages of unital maps (D21-2)\<close>

text \<open>The notes ask whether every unital completely positive $\Phi:M_n\to M_d$ is the average of $n$
unital completely positive maps of Choi rank at most $d$ (\<open>average_conjecture\<close>).  This is the strong
Ruskai--Audenaert conjecture for the dual channel, open in general.  Proved here: Fourier mixing
settles every map whose Kraus operators split into $n$ groups with vanishing cross sums
(\<open>fourier_split\<close>); this covers measurement maps (\<open>ra_measurement\<close>), and Horn's lemma
(\<open>horn_lemma\<close>, the case $d=1$) covers maps with diagonal values (\<open>ra_cq\<close>).  The notes' form (i)
is false as written (\<open>notes_form_i_false\<close>).\<close>

lemma conj_entry:
  assumes W: "W \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n" and a: "a < d" and b: "b < d"
  shows "(W * X * (W\<^sup>\<dagger>)) $$ (a, b) = (\<Sum>p<n. \<Sum>q<n. W $$ (a, p) * X $$ (p, q) * cnj (W $$ (b, q)))"
proof -
  have WX: "W * X \<in> carrier_mat d n" using W X by simp
  have "(W * X * (W\<^sup>\<dagger>)) $$ (a, b) = (\<Sum>q<n. (W * X) $$ (a, q) * cnj (W $$ (b, q)))"
    using WX W X a b by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def carrier_matD[OF WX] carrier_matD[OF W] carrier_matD[OF X])
  also have "\<dots> = (\<Sum>q<n. \<Sum>p<n. W $$ (a, p) * X $$ (p, q) * cnj (W $$ (b, q)))"
    using W X a by (simp add: scalar_prod_def atLeast0LessThan sum_distrib_right Matrix.row_def carrier_matD[OF W] carrier_matD[OF X])
  finally show ?thesis by (rule trans) (rule sum.swap)
qed

lemma sum_list_concat_upt:
  "sum_list (map f (concat (map (\<lambda>m. map (g m) [0..<d]) [0..<n]))) = (\<Sum>m<n. \<Sum>j<d. f (g m j))"
proof (induction n)
  case (Suc n)
  have "sum_list (map f (map (g n) [0..<d])) = (\<Sum>j<d. f (g n j))"
    by (simp add: comp_def sum_set_upt_conv_sum_list_nat[symmetric] atLeast0LessThan)
  thus ?case using Suc by simp
qed simp

text \<open>Characters of $\mathbb Z_n$.\<close>

definition omega_pow :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "omega_pow n l m = cis (2 * pi * real l * real m / real n)"

text \<open>With $\omega=e^{2\pi i/n}$, \<open>omega_pow n l m\<close> is $\omega^{lm}$.  The characters are orthogonal,
\[ \sum_{l<n}\omega^{lm}\,\overline{\omega^{lm'}}=n\,\delta_{mm'}, \]
so the Fourier mixing $x\mapsto\bigl(\sum_m\omega^{lm}x_m\bigr)_l$ multiplies inner products by $n$.\<close>

lemma omega_pow_norm [simp]: "omega_pow n l m * cnj (omega_pow n l m) = 1"
  by (simp add: omega_pow_def cis_cnj cis_mult)

lemma omega_pow_orth:
  assumes m: "m < n" and m': "m' < n"
  shows "(\<Sum>l<n. omega_pow n l m * cnj (omega_pow n l m')) = (if m = m' then of_nat n else 0)"
proof (cases "m = m'")
  case True thus ?thesis by simp
next
  case False
  let ?z = "cis (2 * pi * (real m - real m') / real n)"
  have n0: "0 < n" using m by simp
  have e: "omega_pow n l m * cnj (omega_pow n l m') = ?z ^ l" for l
  proof -
    have "omega_pow n l m * cnj (omega_pow n l m') = cis (2 * pi * real l * real m / real n - 2 * pi * real l * real m' / real n)"
      by (simp add: omega_pow_def cis_cnj cis_mult)
    also have "\<dots> = cis (real l * (2 * pi * (real m - real m') / real n))"
      by (rule arg_cong[where f = cis]) (simp add: algebra_simps diff_divide_distrib)
    also have "\<dots> = ?z ^ l" by (simp add: DeMoivre)
    finally show ?thesis .
  qed
  have zn: "?z ^ n = 1"
  proof -
    have "?z ^ n = cis (real n * (2 * pi * (real m - real m') / real n))" by (simp add: DeMoivre)
    also have "real n * (2 * pi * (real m - real m') / real n) = 2 * pi * (real m - real m')" using n0 by simp
    finally have "?z ^ n = cis (2 * pi * (real m - real m'))" .
    moreover have "cis (2 * pi * (real m - real m')) = 1"
      by (rule cis_multiple_2pi) (simp add: Ints_diff)
    ultimately show ?thesis by simp
  qed
  have z1: "?z \<noteq> 1"
  proof
    assume "?z = 1"
    hence "cos (2 * pi * (real m - real m') / real n) = 1" by (metis cis.sel(1) one_complex.sel(1))
    then obtain j :: int where "2 * pi * (real m - real m') / real n = of_int j * 2 * pi"
      unfolding cos_one_2pi_int by auto
    hence j: "2 * pi * (real m - real m') / real n = 2 * pi * of_int j" by simp
    hence "2 * pi * ((real m - real m') / real n) = 2 * pi * of_int j" by simp
    hence "(real m - real m') / real n = of_int j" using pi_neq_zero mult_cancel_left[of "2 * pi" "(real m - real m') / real n" "of_int j"] by (simp only: times_divide_eq_right) simp
    hence "real m - real m' = real n * of_int j" using n0 by (simp add: field_simps)
    hence "real_of_int (int m - int m') = real_of_int (int n * j)" by simp
    hence eq: "int m - int m' = int n * j" by (simp only: of_int_eq_iff)
    have lt: "\<bar>int m - int m'\<bar> < int n" using m m' by linarith
    have "j = 0"
    proof (rule ccontr)
      assume "j \<noteq> 0"
      hence "1 \<le> \<bar>j\<bar>" by simp
      hence "int n \<le> int n * \<bar>j\<bar>" using mult_left_mono[of 1 "\<bar>j\<bar>" "int n"] by simp
      also have "\<dots> = \<bar>int m - int m'\<bar>" unfolding eq by (simp add: abs_mult)
      finally show False using lt by simp
    qed
    thus False using eq False by simp
  qed
  have "(\<Sum>l<n. omega_pow n l m * cnj (omega_pow n l m')) = (\<Sum>l<n. ?z ^ l)" by (simp add: e)
  also have "\<dots> = 0" using z1 zn by (simp add: geometric_sum)
  finally show ?thesis using False by simp
qed

lemma omega_pow_mix:
  "(\<Sum>l<n. (\<Sum>m<n. omega_pow n l m * x m) * cnj (\<Sum>m<n. omega_pow n l m * y m)) = of_nat n * (\<Sum>m<n. x m * cnj (y m))"
proof -
  have "(\<Sum>l<n. (\<Sum>m<n. omega_pow n l m * x m) * cnj (\<Sum>m<n. omega_pow n l m * y m))
        = (\<Sum>l<n. \<Sum>m<n. \<Sum>m'<n. (omega_pow n l m * cnj (omega_pow n l m')) * (x m * cnj (y m')))"
    by (simp add: cnj_sum sum_distrib_left sum_distrib_right algebra_simps) (rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. \<Sum>l<n. (omega_pow n l m * cnj (omega_pow n l m')) * (x m * cnj (y m')))"
    by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. (\<Sum>l<n. omega_pow n l m * cnj (omega_pow n l m')) * (x m * cnj (y m')))"
    by (simp only: sum_distrib_right)
  also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. (if m = m' then of_nat n else 0) * (x m * cnj (y m')))"
    by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: omega_pow_orth)
  also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. if m' = m then of_nat n * (x m * cnj (y m)) else 0)"
    by (rule sum.cong[OF refl], rule sum.cong[OF refl]) auto
  also have "\<dots> = of_nat n * (\<Sum>m<n. x m * cnj (y m))" by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

lemma kraus_concat_entry:
  assumes g: "\<And>m j. m < k \<Longrightarrow> j < d \<Longrightarrow> g m j \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n" and a: "a < d" and b: "b < d"
  shows "kraus_map_dim d (concat (map (\<lambda>m. map (g m) [0..<d]) [0..<k])) X $$ (a, b) = (\<Sum>m<k. \<Sum>j<d. (g m j * X * ((g m j)\<^sup>\<dagger>)) $$ (a, b))"
proof -
  have c: "\<forall>W \<in> set (concat (map (\<lambda>m. map (g m) [0..<d]) [0..<k])). W \<in> carrier_mat d n" using g by auto
  show ?thesis unfolding kraus_map_dim_entry_sum_list[OF c X a b] by (rule sum_list_concat_upt)
qed

lemma kraus_concat_carrier:
  assumes g: "\<And>m j. m < k \<Longrightarrow> j < d \<Longrightarrow> g m j \<in> carrier_mat d n" and X: "X \<in> carrier_mat n n"
  shows "kraus_map_dim d (concat (map (\<lambda>m. map (g m) [0..<d]) [0..<k])) X \<in> carrier_mat d d"
  by (rule kraus_map_dim_carrier[OF _ X]) (use g in auto)

lemma prod_dagger_entry:
  assumes A: "A \<in> carrier_mat d n" and B: "B \<in> carrier_mat d n" and a: "a < d" and b: "b < d"
  shows "(A * (B\<^sup>\<dagger>)) $$ (a, b) = (\<Sum>p<n. A $$ (a, p) * cnj (B $$ (b, p)))"
  using A B a b by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)

text \<open>D21-2 in the notes' main form: a unital $\Phi:M_n\to M_d$ is the average of $n$ unital
completely positive maps of Choi rank at most $d$.\<close>

definition ucp_average_split :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "ucp_average_split n d \<Phi> \<longleftrightarrow> (\<exists>Bs. length Bs = n \<and> (\<forall>l<n. length (Bs ! l) \<le> d \<and> (\<forall>B \<in> set (Bs ! l). B \<in> carrier_mat d n)
      \<and> kraus_map_dim d (Bs ! l) (1\<^sub>m n) = 1\<^sub>m d) \<and> (\<forall>X \<in> carrier_mat n n. \<Phi> X = (1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X))"

text \<open>The conjecture itself, for maps given by Kraus operators (every completely positive map
is one).  It is the strong Ruskai--Audenaert conjecture for the dual channel $M_d\to M_n$, open in
general; the cases below are the ones settled in the literature by direct constructions.\<close>

definition average_conjecture :: bool where
  "average_conjecture \<longleftrightarrow> (\<forall>n d As. 0 < n \<longrightarrow> (\<forall>A \<in> set As. A \<in> carrier_mat d n) \<longrightarrow> kraus_map_dim d As (1\<^sub>m n) = 1\<^sub>m d
     \<longrightarrow> ucp_average_split n d (kraus_map_dim d As))"

definition fourier_mix :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "fourier_mix n d A l j = Matrix.mat d n (\<lambda>(a, p). \<Sum>m<n. omega_pow n l m * A m j $$ (a, p))"

lemma fourier_mix_carrier [simp]: "fourier_mix n d A l j \<in> carrier_mat d n" by (simp add: fourier_mix_def)

lemma fourier_mix_index: "a < d \<Longrightarrow> p < n \<Longrightarrow> fourier_mix n d A l j $$ (a, p) = (\<Sum>m<n. omega_pow n l m * A m j $$ (a, p))"
  by (simp add: fourier_mix_def)

text \<open>If the Kraus operators fall into $n$ groups of $d$ with $\sum_jA_{mj}A_{m'j}^*=0$ for $m\ne m'$,
Fourier mixing $B_{lj}=\sum_m\omega^{lm}A_{mj}$ gives the decomposition.\<close>

theorem fourier_split:
  assumes n: "0 < n" and A: "\<And>m j. m < n \<Longrightarrow> j < d \<Longrightarrow> A m j \<in> carrier_mat d n"
    and u: "kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])) (1\<^sub>m n) = 1\<^sub>m d"
    and orth: "\<And>m m' a b. m < n \<Longrightarrow> m' < n \<Longrightarrow> m \<noteq> m' \<Longrightarrow> a < d \<Longrightarrow> b < d \<Longrightarrow> (\<Sum>j<d. (A m j * ((A m' j)\<^sup>\<dagger>)) $$ (a, b)) = 0"
  shows "ucp_average_split n d (kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])))"
proof -
  let ?B = "fourier_mix n d A"
  define Bs where "Bs = map (\<lambda>l. map (?B l) [0..<d]) [0..<n]"
  have one: "1\<^sub>m n \<in> carrier_mat n n" by simp
  have e1: "(W * 1\<^sub>m n * (W\<^sup>\<dagger>)) $$ (a, b) = (W * (W\<^sup>\<dagger>)) $$ (a, b)" if "W \<in> carrier_mat d n" for W a b
    using that by simp
  have unit: "kraus_map_dim d (Bs ! l) (1\<^sub>m n) = 1\<^sub>m d" if l: "l < n" for l
  proof (rule eq_matI)
    have c: "\<forall>W \<in> set (map (?B l) [0..<d]). W \<in> carrier_mat d n" by auto
    have cB: "kraus_map_dim d (map (?B l) [0..<d]) (1\<^sub>m n) \<in> carrier_mat d d" by (rule kraus_map_dim_carrier[OF c one])
    show "dim_row (kraus_map_dim d (Bs ! l) (1\<^sub>m n)) = dim_row (1\<^sub>m d)" "dim_col (kraus_map_dim d (Bs ! l) (1\<^sub>m n)) = dim_col (1\<^sub>m d)"
      using cB l by (simp_all add: Bs_def)
    fix a b assume "a < dim_row (1\<^sub>m d)" "b < dim_col (1\<^sub>m d)"
    hence a: "a < d" and b: "b < d" by simp_all
    have "kraus_map_dim d (Bs ! l) (1\<^sub>m n) $$ (a, b) = (\<Sum>j<d. (?B l j * ((?B l j)\<^sup>\<dagger>)) $$ (a, b))"
    proof -
      have Bl: "Bs ! l = map (?B l) [0..<d]" using l by (simp add: Bs_def)
      show ?thesis unfolding Bl kraus_map_dim_entry_sum_list[OF c one a b]
        by (simp add: e1 comp_def sum_set_upt_conv_sum_list_nat[symmetric] atLeast0LessThan)
    qed
    also have "\<dots> = (\<Sum>j<d. \<Sum>p<n. (\<Sum>m<n. omega_pow n l m * A m j $$ (a, p)) * cnj (\<Sum>m<n. omega_pow n l m * A m j $$ (b, p)))"
      by (rule sum.cong[OF refl]) (simp add: prod_dagger_entry[OF fourier_mix_carrier fourier_mix_carrier a b] fourier_mix_index a b)
    also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. omega_pow n l m * cnj (omega_pow n l m') * (\<Sum>j<d. (A m j * ((A m' j)\<^sup>\<dagger>)) $$ (a, b)))"
    proof -
      have "(\<Sum>j<d. \<Sum>p<n. (\<Sum>m<n. omega_pow n l m * A m j $$ (a, p)) * cnj (\<Sum>m<n. omega_pow n l m * A m j $$ (b, p)))
          = (\<Sum>j<d. \<Sum>p<n. \<Sum>m<n. \<Sum>m'<n. omega_pow n l m * cnj (omega_pow n l m') * (A m j $$ (a, p) * cnj (A m' j $$ (b, p))))"
        by (simp add: cnj_sum sum_distrib_left sum_distrib_right algebra_simps) (rule sum.cong[OF refl], rule sum.cong[OF refl], rule sum.swap)
      also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. \<Sum>j<d. \<Sum>p<n. omega_pow n l m * cnj (omega_pow n l m') * (A m j $$ (a, p) * cnj (A m' j $$ (b, p))))"
        by (subst sum.swap, subst (2) sum.swap, rule sum.cong[OF refl], subst sum.swap,
            rule sum.cong[OF refl], subst sum.swap, rule refl)
      also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. omega_pow n l m * cnj (omega_pow n l m') * (\<Sum>j<d. (A m j * ((A m' j)\<^sup>\<dagger>)) $$ (a, b)))"
        by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: sum_distrib_left prod_dagger_entry[OF A A a b])
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. if m' = m then (\<Sum>j<d. (A m j * ((A m j)\<^sup>\<dagger>)) $$ (a, b)) else 0)"
      by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (auto simp: orth a b)
    also have "\<dots> = kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])) (1\<^sub>m n) $$ (a, b)"
      using kraus_concat_entry[OF A one a b] by (simp add: e1 A)
    finally show "kraus_map_dim d (Bs ! l) (1\<^sub>m n) $$ (a, b) = 1\<^sub>m d $$ (a, b)" unfolding u .
  qed
  have avg: "kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])) X = (1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X"
    if X: "X \<in> carrier_mat n n" for X
  proof (rule eq_matI)
    have cA: "kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])) X \<in> carrier_mat d d"
      by (rule kraus_concat_carrier[OF A X])
    have cB: "kraus_map_dim d (concat Bs) X \<in> carrier_mat d d" unfolding Bs_def by (rule kraus_concat_carrier[OF _ X]) simp
    show "dim_row (kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])) X) = dim_row ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X)"
      "dim_col (kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])) X) = dim_col ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X)"
      using cA cB by simp_all
    fix a b assume "a < dim_row ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X)" "b < dim_col ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X)"
    hence a: "a < d" and b: "b < d" using cB by simp_all
    have "((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X) $$ (a, b) = (1 / of_nat n) * (\<Sum>l<n. \<Sum>j<d. (?B l j * X * ((?B l j)\<^sup>\<dagger>)) $$ (a, b))"
      using cB a b unfolding Bs_def by (simp add: kraus_concat_entry[OF _ X a b])
    also have "\<dots> = (1 / of_nat n) * (\<Sum>j<d. \<Sum>p<n. \<Sum>q<n. X $$ (p, q) *
        (\<Sum>l<n. (\<Sum>m<n. omega_pow n l m * A m j $$ (a, p)) * cnj (\<Sum>m<n. omega_pow n l m * A m j $$ (b, q))))"
    proof -
      have "(\<Sum>l<n. \<Sum>j<d. (?B l j * X * ((?B l j)\<^sup>\<dagger>)) $$ (a, b))
          = (\<Sum>l<n. \<Sum>j<d. \<Sum>p<n. \<Sum>q<n. X $$ (p, q) * ((\<Sum>m<n. omega_pow n l m * A m j $$ (a, p)) * cnj (\<Sum>m<n. omega_pow n l m * A m j $$ (b, q))))"
        by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: conj_entry[OF fourier_mix_carrier X a b] fourier_mix_index a b algebra_simps)
      also have "\<dots> = (\<Sum>j<d. \<Sum>p<n. \<Sum>q<n. \<Sum>l<n. X $$ (p, q) * ((\<Sum>m<n. omega_pow n l m * A m j $$ (a, p)) * cnj (\<Sum>m<n. omega_pow n l m * A m j $$ (b, q))))"
        by (subst sum.swap, rule sum.cong[OF refl], subst sum.swap, rule sum.cong[OF refl], subst sum.swap, rule refl)
      finally show ?thesis by (simp add: sum_distrib_left)
    qed
    also have "\<dots> = (\<Sum>m<n. \<Sum>j<d. \<Sum>p<n. \<Sum>q<n. A m j $$ (a, p) * X $$ (p, q) * cnj (A m j $$ (b, q)))"
    proof -
      have "(1 / of_nat n) * (\<Sum>j<d. \<Sum>p<n. \<Sum>q<n. X $$ (p, q) * (of_nat n * (\<Sum>m<n. A m j $$ (a, p) * cnj (A m j $$ (b, q)))))
          = (\<Sum>j<d. \<Sum>p<n. \<Sum>q<n. \<Sum>m<n. A m j $$ (a, p) * X $$ (p, q) * cnj (A m j $$ (b, q)))"
        using n by (simp add: sum_distrib_left algebra_simps)
      also have "\<dots> = (\<Sum>m<n. \<Sum>j<d. \<Sum>p<n. \<Sum>q<n. A m j $$ (a, p) * X $$ (p, q) * cnj (A m j $$ (b, q)))"
        by (subst (2) sum.swap, subst (3) sum.swap, subst sum.swap, rule refl)
      finally show ?thesis by (simp only: omega_pow_mix)
    qed
    also have "\<dots> = kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])) X $$ (a, b)"
      by (simp add: kraus_concat_entry[OF A X a b] conj_entry[OF A X a b])
    finally show "kraus_map_dim d (concat (map (\<lambda>m. map (A m) [0..<d]) [0..<n])) X $$ (a, b) = ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X) $$ (a, b)" ..
  qed
  show ?thesis unfolding ucp_average_split_def
    by (rule exI[of _ Bs]) (use unit avg in \<open>auto simp: Bs_def\<close>)
qed

subsection \<open>Positive matrices as sums of $d$ rank-one terms\<close>

lemma udu_entry:
  assumes U: "U \<in> carrier_mat d d" and D: "length D = d" and a: "a < d" and b: "b < d"
  shows "(U * diag_mat_of_real D * (U\<^sup>\<dagger>)) $$ (a, b) = (\<Sum>k<d. U $$ (a, k) * complex_of_real (D ! k) * cnj (U $$ (b, k)))"
proof -
  have UD: "U * diag_mat_of_real D \<in> carrier_mat d d" using mult_carrier_mat[OF U diag_mat_of_real_carrier[of D, unfolded D]] by simp
  have e: "(U * diag_mat_of_real D) $$ (a, k) = U $$ (a, k) * complex_of_real (D ! k)" if k: "k < d" for k
  proof -
    have "(U * diag_mat_of_real D) $$ (a, k) = (\<Sum>u<d. U $$ (a, u) * (if u = k then complex_of_real (D ! u) else 0))"
      using U D a k by (simp add: scalar_prod_def atLeast0LessThan Matrix.row_def)
    also have "\<dots> = (\<Sum>u<d. if u = k then U $$ (a, k) * complex_of_real (D ! k) else 0)" by (rule sum.cong) auto
    finally show ?thesis using k by simp
  qed
  show ?thesis unfolding prod_dagger_entry[OF UD U a b] using e by simp
qed

lemma psd_eig:
  assumes Q: "Q \<in> carrier_mat d d" "psd Q"
  shows "\<exists>U D. U \<in> carrier_mat d d \<and> length D = d \<and> (\<forall>k<d. 0 \<le> D ! k) \<and> (U\<^sup>\<dagger>) * U = 1\<^sub>m d
     \<and> (\<forall>a<d. \<forall>b<d. Q $$ (a, b) = (\<Sum>k<d. U $$ (a, k) * complex_of_real (D ! k) * cnj (U $$ (b, k))))"
proof -
  obtain U :: "complex Matrix.mat" and D :: "real list" where Uc: "U \<in> carrier_mat d d" and Uu: "unitary U"
    and D: "length D = d" and spec: "U\<^sup>\<dagger> * Q * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF Q(1) psd_hermitian[OF Q(2)]] by blast
  have Qe: "Q = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF Uc Q(1) Uu spec])
  have Dnn: "0 \<le> D ! k" if k: "k < d" for k
  proof -
    let ?u = "Matrix.col U k"
    have du: "dim_vec ?u = d" using Uc by simp
    have "complex_of_real (D ! k) = (U\<^sup>\<dagger> * Q * U) $$ (k, k)" using spec k D by simp
    also have "\<dots> = (\<Sum>a<d. cnj (U $$ (a, k)) * (Q * U) $$ (a, k))"
    proof -
      have "(U\<^sup>\<dagger> * Q * U) $$ (k, k) = (\<Sum>c<d. (\<Sum>a<d. cnj (U $$ (a, k)) * Q $$ (a, c)) * U $$ (c, k))"
        using Uc Q(1) k by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
      also have "\<dots> = (\<Sum>c<d. \<Sum>a<d. cnj (U $$ (a, k)) * Q $$ (a, c) * U $$ (c, k))" by (simp add: sum_distrib_right)
      also have "\<dots> = (\<Sum>a<d. \<Sum>c<d. cnj (U $$ (a, k)) * Q $$ (a, c) * U $$ (c, k))" by (rule sum.swap)
      also have "\<dots> = (\<Sum>a<d. cnj (U $$ (a, k)) * (Q * U) $$ (a, k))"
        using Uc Q(1) k by (simp add: scalar_prod_def atLeast0LessThan Matrix.row_def sum_distrib_left algebra_simps)
      finally show ?thesis .
    qed
    also have "\<dots> = \<langle>?u | Q *\<^sub>v ?u\<rangle>"
      using Uc Q(1) k by (simp add: inner_prod_def scalar_prod_def atLeast0LessThan Matrix.row_def)
    finally have "complex_of_real (D ! k) = \<langle>?u | Q *\<^sub>v ?u\<rangle>" .
    moreover have "Re \<langle>?u | Q *\<^sub>v ?u\<rangle> \<ge> 0" using Q du unfolding psd_def by auto
    ultimately show ?thesis by (metis Re_complex_of_real)
  qed
  have UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m d" using Uu Uc unfolding unitary_def by auto
  have "\<forall>a<d. \<forall>b<d. Q $$ (a, b) = (\<Sum>k<d. U $$ (a, k) * complex_of_real (D ! k) * cnj (U $$ (b, k)))"
    using udu_entry[OF Uc D] by (simp flip: Qe)
  thus ?thesis using Uc D Dnn UU by blast
qed

lemma psd_vecs:
  assumes Q: "Q \<in> carrier_mat d d" "psd Q"
  shows "\<exists>q. \<forall>a<d. \<forall>b<d. Q $$ (a, b) = (\<Sum>k<d. q k a * cnj (q k b))"
proof -
  obtain U D where Uc: "U \<in> carrier_mat d d" and D: "length D = d" and Dnn: "\<And>k. k < d \<Longrightarrow> 0 \<le> D ! k"
    and Qe: "\<And>a b. a < d \<Longrightarrow> b < d \<Longrightarrow> Q $$ (a, b) = (\<Sum>k<d. U $$ (a, k) * complex_of_real (D ! k) * cnj (U $$ (b, k)))"
    using psd_eig[OF Q] by blast
  define q where "q k a = complex_of_real (sqrt (D ! k)) * U $$ (a, k)" for k a
  have "Q $$ (a, b) = (\<Sum>k<d. q k a * cnj (q k b))" if a: "a < d" and b: "b < d" for a b
    unfolding Qe[OF a b]
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<d}"
    hence k: "k < d" by simp
    have "complex_of_real (sqrt (D ! k)) * complex_of_real (sqrt (D ! k)) = complex_of_real (D ! k)"
      using Dnn[OF k] by (simp flip: of_real_mult)
    thus "U $$ (a, k) * complex_of_real (D ! k) * cnj (U $$ (b, k)) = q k a * cnj (q k b)"
      unfolding q_def by (simp add: algebra_simps)
  qed
  thus ?thesis by blast
qed

lemma ucp_average_split_cong: "(\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = \<Psi> X) \<Longrightarrow> ucp_average_split n d \<Psi> \<Longrightarrow> ucp_average_split n d \<Phi>"
  unfolding ucp_average_split_def by metis

lemma delta_sum2:
  fixes n i :: nat
  assumes i: "i < n"
  shows "(\<Sum>p<n. \<Sum>p'<n. (if p = i then x else 0) * f p p' * cnj (if p' = i then y else 0)) = x * f i i * cnj (y :: complex)"
proof -
  have inner: "(\<Sum>p'<n. (if p = i then x else 0) * f p p' * cnj (if p' = i then y else 0)) = (if p = i then x * f i i * cnj y else 0)" for p
  proof (cases "p = i")
    case True
    have "(\<Sum>p'<n. (if p = i then x else 0) * f p p' * cnj (if p' = i then y else 0)) = (\<Sum>p'<n. if p' = i then x * f i i * cnj y else 0)"
      by (rule sum.cong[OF refl]) (simp add: True)
    thus ?thesis using i True by (simp add: sum.delta')
  qed simp
  show ?thesis unfolding inner using i by (simp add: sum.delta')
qed

subsection \<open>Measurement maps\<close>

text \<open>$\Phi(X)=\sum_iX_{ii}Q_i$ with $Q_i\ge0$, $\sum_iQ_i=I$ (dual to a channel with classical
output): D21-2 holds.\<close>

definition povm_map :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "povm_map n d Q X = Matrix.mat d d (\<lambda>(a, b). \<Sum>i<n. X $$ (i, i) * Q i $$ (a, b))"

theorem ra_measurement:
  assumes n: "0 < n" and Q: "\<And>i. i < n \<Longrightarrow> Q i \<in> carrier_mat d d \<and> psd (Q i)"
    and QI: "\<And>a b. a < d \<Longrightarrow> b < d \<Longrightarrow> (\<Sum>i<n. Q i $$ (a, b)) = 1\<^sub>m d $$ (a, b)"
  shows "ucp_average_split n d (povm_map n d Q)"
proof -
  have "\<forall>i. \<exists>qi. i < n \<longrightarrow> (\<forall>a<d. \<forall>b<d. Q i $$ (a, b) = (\<Sum>k<d. qi k a * cnj (qi k b)))"
    using psd_vecs Q by blast
  then obtain q where q0: "\<forall>i. i < n \<longrightarrow> (\<forall>a<d. \<forall>b<d. Q i $$ (a, b) = (\<Sum>k<d. q i k a * cnj (q i k b)))"
    by (rule choice[THEN exE])
  have q: "\<And>i a b. i < n \<Longrightarrow> a < d \<Longrightarrow> b < d \<Longrightarrow> Q i $$ (a, b) = (\<Sum>k<d. q i k a * cnj (q i k b))"
    using q0 by blast
  define A where "A i k = Matrix.mat d n (\<lambda>(a, p). if p = i then q i k a else 0)" for i k
  have Ac: "\<And>i k. A i k \<in> carrier_mat d n" by (simp add: A_def)
  have Ai: "\<And>i k a p. a < d \<Longrightarrow> p < n \<Longrightarrow> A i k $$ (a, p) = (if p = i then q i k a else 0)" by (simp add: A_def)
  have ent: "(A i k * X * ((A i k)\<^sup>\<dagger>)) $$ (a, b) = q i k a * X $$ (i, i) * cnj (q i k b)"
    if X: "X \<in> carrier_mat n n" and i: "i < n" and a: "a < d" and b: "b < d" for i k a b X
  proof -
    have "(A i k * X * ((A i k)\<^sup>\<dagger>)) $$ (a, b) = (\<Sum>p<n. \<Sum>p'<n. (if p = i then q i k a else 0) * X $$ (p, p') * cnj (if p' = i then q i k b else 0))"
      unfolding conj_entry[OF Ac X a b] by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: Ai a b)
    also have "\<dots> = q i k a * X $$ (i, i) * cnj (q i k b)" by (rule delta_sum2[OF i])
    finally show ?thesis .
  qed
  have km: "kraus_map_dim d (concat (map (\<lambda>i. map (A i) [0..<d]) [0..<n])) X = povm_map n d Q X" if X: "X \<in> carrier_mat n n" for X
  proof (rule eq_matI)
    have c: "kraus_map_dim d (concat (map (\<lambda>i. map (A i) [0..<d]) [0..<n])) X \<in> carrier_mat d d"
      by (rule kraus_concat_carrier[OF _ X]) (rule Ac)
    show "dim_row (kraus_map_dim d (concat (map (\<lambda>i. map (A i) [0..<d]) [0..<n])) X) = dim_row (povm_map n d Q X)"
      "dim_col (kraus_map_dim d (concat (map (\<lambda>i. map (A i) [0..<d]) [0..<n])) X) = dim_col (povm_map n d Q X)"
      using c by (simp_all add: povm_map_def)
    fix a b assume "a < dim_row (povm_map n d Q X)" "b < dim_col (povm_map n d Q X)"
    hence a: "a < d" and b: "b < d" by (simp_all add: povm_map_def)
    show "kraus_map_dim d (concat (map (\<lambda>i. map (A i) [0..<d]) [0..<n])) X $$ (a, b) = povm_map n d Q X $$ (a, b)"
      unfolding kraus_concat_entry[OF Ac X a b] using a b
      by (simp add: ent[OF X _ a b] povm_map_def q sum_distrib_left algebra_simps)
  qed
  have orth: "(\<Sum>k<d. (A i k * ((A i' k)\<^sup>\<dagger>)) $$ (a, b)) = 0" if "i \<noteq> i'" "a < d" "b < d" for i i' a b
    using that by (simp add: prod_dagger_entry[OF Ac Ac] Ai)
  have u: "kraus_map_dim d (concat (map (\<lambda>i. map (A i) [0..<d]) [0..<n])) (1\<^sub>m n) = 1\<^sub>m d"
  proof -
    have "povm_map n d Q (1\<^sub>m n) = 1\<^sub>m d"
      by (rule eq_matI) (use n in \<open>simp_all add: povm_map_def QI\<close>)
    thus ?thesis using km[of "1\<^sub>m n"] by simp
  qed
  have "ucp_average_split n d (kraus_map_dim d (concat (map (\<lambda>i. map (A i) [0..<d]) [0..<n])))"
    by (rule fourier_split[OF n _ u]) (simp_all add: Ac orth)
  thus ?thesis by (rule ucp_average_split_cong[rotated]) (simp add: km)
qed

subsection \<open>The case $d=1$: Horn's lemma\<close>

text \<open>Every density matrix on $\mathbb C^n$ is the average of $n$ pure states (Fourier mixing of
an eigenbasis).\<close>

theorem horn_lemma:
  assumes \<rho>: "density_matrix n \<rho>" and n: "0 < n"
  shows "\<exists>\<phi>. (\<forall>l<n. dim_vec (\<phi> l) = n \<and> \<parallel>\<phi> l\<parallel> = 1)
           \<and> (\<forall>a<n. \<forall>b<n. \<rho> $$ (a, b) = (1 / of_nat n) * (\<Sum>l<n. \<phi> l $ a * cnj (\<phi> l $ b)))"
proof -
  have rc: "\<rho> \<in> carrier_mat n n" and rp: "psd \<rho>" and rt: "Tr \<rho> = 1" using \<rho> unfolding density_matrix_def by auto
  obtain U D where Uc: "U \<in> carrier_mat n n" and D: "length D = n" and Dnn: "\<And>k. k < n \<Longrightarrow> 0 \<le> D ! k"
    and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n"
    and re: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> \<rho> $$ (a, b) = (\<Sum>k<n. U $$ (a, k) * complex_of_real (D ! k) * cnj (U $$ (b, k)))"
    using psd_eig[OF rc rp] by blast
  define s where "s k a = complex_of_real (sqrt (D ! k)) * U $$ (a, k)" for k a
  define \<phi> where "\<phi> l = Matrix.vec n (\<lambda>a. \<Sum>m<n. omega_pow n l m * s m a)" for l
  have ss: "s k a * cnj (s k b) = U $$ (a, k) * complex_of_real (D ! k) * cnj (U $$ (b, k))" if k: "k < n" for k a b
  proof -
    have "complex_of_real (sqrt (D ! k)) * complex_of_real (sqrt (D ! k)) = complex_of_real (D ! k)"
      using Dnn[OF k] by (simp flip: of_real_mult)
    thus ?thesis unfolding s_def by (simp add: algebra_simps)
  qed
  have avg: "\<rho> $$ (a, b) = (1 / of_nat n) * (\<Sum>l<n. \<phi> l $ a * cnj (\<phi> l $ b))" if a: "a < n" and b: "b < n" for a b
  proof -
    have "(\<Sum>l<n. \<phi> l $ a * cnj (\<phi> l $ b)) = of_nat n * (\<Sum>m<n. s m a * cnj (s m b))"
      using a b omega_pow_mix[of n "\<lambda>m. s m a" "\<lambda>m. s m b"] by (simp add: \<phi>_def)
    thus ?thesis using n by (simp add: re[OF a b] ss)
  qed
  have UUe: "(\<Sum>a<n. U $$ (a, m) * cnj (U $$ (a, m'))) = (if m = m' then 1 else 0)" if "m < n" "m' < n" for m m'
  proof -
    have "(U\<^sup>\<dagger> * U) $$ (m', m) = (\<Sum>a<n. cnj (U $$ (a, m')) * U $$ (a, m))"
      using Uc that by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    hence "(if m' = m then 1 else 0) = (\<Sum>a<n. U $$ (a, m) * cnj (U $$ (a, m')))" using UU that by (simp add: Groups.mult.commute[of "cnj _"])
    thus ?thesis by (cases "m = m'") auto
  qed
  have trD: "(\<Sum>k<n. complex_of_real (D ! k)) = 1"
  proof -
    have "1 = (\<Sum>a<n. \<rho> $$ (a, a))" using rt rc by (simp add: Tr_def)
    also have "\<dots> = (\<Sum>a<n. \<Sum>k<n. complex_of_real (D ! k) * (U $$ (a, k) * cnj (U $$ (a, k))))"
      by (rule sum.cong[OF refl]) (simp add: re algebra_simps)
    also have "\<dots> = (\<Sum>k<n. complex_of_real (D ! k) * (\<Sum>a<n. U $$ (a, k) * cnj (U $$ (a, k))))"
      by (subst sum.swap) (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>k<n. complex_of_real (D ! k))" by (rule sum.cong[OF refl]) (simp add: UUe)
    finally show ?thesis by simp
  qed
  have nrm: "\<parallel>\<phi> l\<parallel> = 1" if l: "l < n" for l
  proof -
    have "(\<Sum>a<n. \<phi> l $ a * cnj (\<phi> l $ a)) = (\<Sum>m<n. \<Sum>m'<n. omega_pow n l m * cnj (omega_pow n l m') * (\<Sum>a<n. s m a * cnj (s m' a)))"
    proof -
      have "(\<Sum>a<n. \<phi> l $ a * cnj (\<phi> l $ a)) = (\<Sum>a<n. \<Sum>m<n. \<Sum>m'<n. omega_pow n l m * cnj (omega_pow n l m') * (s m a * cnj (s m' a)))"
        by (rule sum.cong[OF refl]) (simp add: \<phi>_def cnj_sum sum_distrib_left sum_distrib_right algebra_simps, rule sum.swap)
      also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. \<Sum>a<n. omega_pow n l m * cnj (omega_pow n l m') * (s m a * cnj (s m' a)))"
        by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
      finally show ?thesis by (simp add: sum_distrib_left)
    qed
    also have "\<dots> = (\<Sum>m<n. \<Sum>m'<n. if m' = m then complex_of_real (D ! m) else 0)"
    proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
      fix m m' assume "m \<in> {..<n}" "m' \<in> {..<n}"
      hence mm: "m < n" "m' < n" by simp_all
      have "(\<Sum>a<n. s m a * cnj (s m' a)) = complex_of_real (sqrt (D ! m)) * complex_of_real (sqrt (D ! m')) * (if m = m' then 1 else 0)"
        unfolding s_def UUe[OF mm, symmetric] by (simp add: sum_distrib_left algebra_simps)
      moreover have "complex_of_real (sqrt (D ! m)) * complex_of_real (sqrt (D ! m)) = complex_of_real (D ! m)"
        using Dnn[OF mm(1)] by (simp flip: of_real_mult)
      ultimately show "omega_pow n l m * cnj (omega_pow n l m') * (\<Sum>a<n. s m a * cnj (s m' a)) = (if m' = m then complex_of_real (D ! m) else 0)"
        by auto
    qed
    also have "\<dots> = 1" using trD by simp
    finally have e: "(\<Sum>a<n. \<phi> l $ a * cnj (\<phi> l $ a)) = 1" .
    have "complex_of_real (\<Sum>a<n. (cmod (\<phi> l $ a))\<^sup>2) = (\<Sum>a<n. \<phi> l $ a * cnj (\<phi> l $ a))"
      by (simp add: complex_mult_cnj cmod_power2 del: of_real_power)
    hence "(\<Sum>a<n. (cmod (\<phi> l $ a))\<^sup>2) = 1" using e by (metis of_real_eq_1_iff)
    thus ?thesis by (simp add: cpx_vec_length_def \<phi>_def)
  qed
  show ?thesis using avg nrm by (intro exI[of _ \<phi>]) (simp add: \<phi>_def)
qed

lemma delta_pair:
  fixes c c' d :: nat
  assumes "c < d"
  shows "(\<Sum>a<d. if c = a \<and> c' = a then f a else 0) = (if c = c' then f c else (0::complex))"
proof (cases "c = c'")
  case True
  have "(\<Sum>a<d. if c = a \<and> c' = a then f a else 0) = (\<Sum>a<d. if a = c then f c else 0)"
    by (rule sum.cong[OF refl]) (auto simp: True)
  thus ?thesis using assms True by simp
qed (auto intro: sum.neutral)

subsection \<open>Maps with diagonal values\<close>

text \<open>$\Phi(X)=\operatorname{diag}(\operatorname{tr}(R_1X),\dots,\operatorname{tr}(R_dX))$ with density
matrices $R_a$ (dual to a channel with classical input): D21-2 holds, by Horn's lemma for each
$R_a$.\<close>

definition cq_map :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "cq_map n d Rh X = Matrix.mat d d (\<lambda>(a, b). if a = b then (\<Sum>p<n. \<Sum>q<n. Rh a $$ (q, p) * X $$ (p, q)) else 0)"

theorem ra_cq:
  assumes n: "0 < n" and Rh: "\<And>a. a < d \<Longrightarrow> density_matrix n (Rh a)"
  shows "ucp_average_split n d (cq_map n d Rh)"
proof -
  have "\<forall>a. \<exists>\<phi>. a < d \<longrightarrow> (\<forall>l<n. dim_vec (\<phi> l) = n \<and> \<parallel>\<phi> l\<parallel> = 1)
           \<and> (\<forall>p<n. \<forall>q<n. Rh a $$ (p, q) = (1 / of_nat n) * (\<Sum>l<n. \<phi> l $ p * cnj (\<phi> l $ q)))"
    using horn_lemma[OF Rh n] by blast
  then obtain \<phi> where \<phi>: "\<forall>a. a < d \<longrightarrow> (\<forall>l<n. dim_vec (\<phi> a l) = n \<and> \<parallel>\<phi> a l\<parallel> = 1)
           \<and> (\<forall>p<n. \<forall>q<n. Rh a $$ (p, q) = (1 / of_nat n) * (\<Sum>l<n. \<phi> a l $ p * cnj (\<phi> a l $ q)))"
    by (rule choice[THEN exE])
  have \<phi>n: "\<And>a l. a < d \<Longrightarrow> l < n \<Longrightarrow> dim_vec (\<phi> a l) = n \<and> \<parallel>\<phi> a l\<parallel> = 1" using \<phi> by blast
  have \<phi>R: "\<And>a p q. a < d \<Longrightarrow> p < n \<Longrightarrow> q < n \<Longrightarrow> Rh a $$ (p, q) = (1 / of_nat n) * (\<Sum>l<n. \<phi> a l $ p * cnj (\<phi> a l $ q))"
    using \<phi> by blast
  define B where "B l a = Matrix.mat d n (\<lambda>(c, p). if c = a then cnj (\<phi> a l $ p) else 0)" for l a
  define Bs where "Bs = map (\<lambda>l. map (B l) [0..<d]) [0..<n]"
  have Bc: "\<And>l a. B l a \<in> carrier_mat d n" by (simp add: B_def)
  have ent: "(B l a * X * ((B l a)\<^sup>\<dagger>)) $$ (c, c') = (if c = a \<and> c' = a then (\<Sum>p<n. \<Sum>q<n. cnj (\<phi> a l $ p) * X $$ (p, q) * \<phi> a l $ q) else 0)"
    if X: "X \<in> carrier_mat n n" and c: "c < d" and c': "c' < d" for l a c c' X
    unfolding conj_entry[OF Bc X c c'] using c c' by (auto simp: B_def)
  have sq: "(\<Sum>p<n. cnj (\<phi> a l $ p) * \<phi> a l $ p) = 1" if a: "a < d" and l: "l < n" for a l
  proof -
    have "complex_of_real (\<Sum>p<n. (cmod (\<phi> a l $ p))\<^sup>2) = (\<Sum>p<n. cnj (\<phi> a l $ p) * \<phi> a l $ p)"
      by (simp add: complex_mult_cnj cmod_power2 Groups.mult.commute[of "cnj _"] del: of_real_power)
    moreover have "(\<Sum>p<n. (cmod (\<phi> a l $ p))\<^sup>2) = 1"
      using \<phi>n[OF a l] unfolding cpx_vec_length_def by (metis (no_types, lifting) real_sqrt_eq_1_iff)
    ultimately show ?thesis by simp
  qed
  have unit: "kraus_map_dim d (Bs ! l) (1\<^sub>m n) = 1\<^sub>m d" if l: "l < n" for l
  proof (rule eq_matI)
    have c: "\<forall>W \<in> set (map (B l) [0..<d]). W \<in> carrier_mat d n" using Bc by auto
    have Bl: "Bs ! l = map (B l) [0..<d]" using l by (simp add: Bs_def)
    have cB: "kraus_map_dim d (map (B l) [0..<d]) (1\<^sub>m n) \<in> carrier_mat d d" by (rule kraus_map_dim_carrier[OF c]) simp
    show "dim_row (kraus_map_dim d (Bs ! l) (1\<^sub>m n)) = dim_row (1\<^sub>m d)" "dim_col (kraus_map_dim d (Bs ! l) (1\<^sub>m n)) = dim_col (1\<^sub>m d)"
      using cB unfolding Bl by simp_all
    fix c c' assume "c < dim_row (1\<^sub>m d)" "c' < dim_col (1\<^sub>m d)"
    hence cc: "c < d" "c' < d" by simp_all
    have "kraus_map_dim d (Bs ! l) (1\<^sub>m n) $$ (c, c') = (\<Sum>a<d. (B l a * 1\<^sub>m n * ((B l a)\<^sup>\<dagger>)) $$ (c, c'))"
      unfolding Bl kraus_map_dim_entry_sum_list[OF c one_carrier_mat cc] by (simp add: comp_def sum_set_upt_conv_sum_list_nat[symmetric] atLeast0LessThan)
    also have "\<dots> = (\<Sum>a<d. if c = a \<and> c' = a then (\<Sum>p<n. cnj (\<phi> a l $ p) * \<phi> a l $ p) else 0)"
    proof (rule sum.cong[OF refl])
      fix a assume "a \<in> {..<d}"
      have "(\<Sum>p<n. \<Sum>q<n. cnj (\<phi> a l $ p) * 1\<^sub>m n $$ (p, q) * \<phi> a l $ q) = (\<Sum>p<n. cnj (\<phi> a l $ p) * \<phi> a l $ p)"
      proof (rule sum.cong[OF refl])
        fix p assume "p \<in> {..<n}"
        hence p: "p < n" by simp
        have "(\<Sum>q<n. cnj (\<phi> a l $ p) * 1\<^sub>m n $$ (p, q) * \<phi> a l $ q) = (\<Sum>q<n. if q = p then cnj (\<phi> a l $ p) * \<phi> a l $ p else 0)"
          by (rule sum.cong[OF refl]) (use p in auto)
        thus "(\<Sum>q<n. cnj (\<phi> a l $ p) * 1\<^sub>m n $$ (p, q) * \<phi> a l $ q) = cnj (\<phi> a l $ p) * \<phi> a l $ p" using p by simp
      qed
      thus "(B l a * 1\<^sub>m n * ((B l a)\<^sup>\<dagger>)) $$ (c, c') = (if c = a \<and> c' = a then (\<Sum>p<n. cnj (\<phi> a l $ p) * \<phi> a l $ p) else 0)"
        unfolding ent[OF one_carrier_mat cc] by simp
    qed
    also have "\<dots> = 1\<^sub>m d $$ (c, c')" using cc l by (auto simp: sq)
    finally show "kraus_map_dim d (Bs ! l) (1\<^sub>m n) $$ (c, c') = 1\<^sub>m d $$ (c, c')" .
  qed
  have avg: "cq_map n d Rh X = (1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X" if X: "X \<in> carrier_mat n n" for X
  proof (rule eq_matI)
    have cB: "kraus_map_dim d (concat Bs) X \<in> carrier_mat d d" unfolding Bs_def by (rule kraus_concat_carrier[OF _ X]) (rule Bc)
    show "dim_row (cq_map n d Rh X) = dim_row ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X)"
      "dim_col (cq_map n d Rh X) = dim_col ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X)" using cB by (simp_all add: cq_map_def)
    fix c c' assume "c < dim_row ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X)" "c' < dim_col ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X)"
    hence cc: "c < d" "c' < d" using cB by simp_all
    have "((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X) $$ (c, c') = (1 / of_nat n) * (\<Sum>l<n. \<Sum>a<d. (B l a * X * ((B l a)\<^sup>\<dagger>)) $$ (c, c'))"
    proof -
      have "kraus_map_dim d (concat Bs) X $$ (c, c') = (\<Sum>l<n. \<Sum>a<d. (B l a * X * ((B l a)\<^sup>\<dagger>)) $$ (c, c'))"
        unfolding Bs_def by (rule kraus_concat_entry[OF _ X cc]) (rule Bc)
      thus ?thesis using cB cc by simp
    qed
    also have "\<dots> = (1 / of_nat n) * (\<Sum>l<n. if c = c' then (\<Sum>p<n. \<Sum>q<n. cnj (\<phi> c l $ p) * X $$ (p, q) * \<phi> c l $ q) else 0)"
      by (simp add: ent[OF X cc] delta_pair[OF cc(1)])
    also have "\<dots> = cq_map n d Rh X $$ (c, c')"
    proof (cases "c = c'")
      case True
      have "(1 / of_nat n) * (\<Sum>l<n. \<Sum>p<n. \<Sum>q<n. cnj (\<phi> c l $ p) * X $$ (p, q) * \<phi> c l $ q)
            = (\<Sum>p<n. \<Sum>q<n. ((1 / of_nat n) * (\<Sum>l<n. \<phi> c l $ q * cnj (\<phi> c l $ p))) * X $$ (p, q))"
      proof -
        have "(\<Sum>l<n. \<Sum>p<n. \<Sum>q<n. cnj (\<phi> c l $ p) * X $$ (p, q) * \<phi> c l $ q)
            = (\<Sum>p<n. \<Sum>q<n. \<Sum>l<n. cnj (\<phi> c l $ p) * X $$ (p, q) * \<phi> c l $ q)"
          by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
        thus ?thesis by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
      qed
      also have "\<dots> = (\<Sum>p<n. \<Sum>q<n. Rh c $$ (q, p) * X $$ (p, q))"
        by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: \<phi>R cc)
      finally show ?thesis using True cc by (simp add: cq_map_def)
    qed (use cc in \<open>simp add: cq_map_def\<close>)
    finally show "cq_map n d Rh X $$ (c, c') = ((1 / of_nat n) \<cdot>\<^sub>m kraus_map_dim d (concat Bs) X) $$ (c, c')" ..
  qed
  show ?thesis unfolding ucp_average_split_def
    by (rule exI[of _ Bs]) (use unit avg in \<open>auto simp: Bs_def Bc\<close>)
qed

subsection \<open>The notes' form (i) is false as written\<close>

text \<open>Form (i) asks for $n$ trace-preserving maps $M_n\to M_d$ of Choi rank at most $d$.  For $n=2$,
$d=1$ there is no trace-preserving map $M_2\to\mathbb C$ of Choi rank at most one, while the trace
is trace preserving.  (The equivalent dual form has the dimensions exchanged: maps $M_d\to M_n$.)\<close>

lemma no_tp_rank_one: "length Ws \<le> 1 \<Longrightarrow> \<not> kraus_operators 2 1 Ws"
proof
  assume l: "length Ws \<le> 1" and k: "kraus_operators 2 1 Ws"
  show False
  proof (cases Ws)
    case Nil
    hence "0\<^sub>m 2 2 = (1\<^sub>m 2 :: complex Matrix.mat)" using k by (simp add: kraus_operators_def)
    hence "(0\<^sub>m 2 2 :: complex Matrix.mat) $$ (0, 0) = 1\<^sub>m 2 $$ (0, 0)" by simp
    thus False by simp
  next
    case (Cons W Vs)
    hence Ws: "Ws = [W]" using l by simp
    have Wc: "W \<in> carrier_mat 1 2" and e0: "W\<^sup>\<dagger> * W + 0\<^sub>m 2 2 = 1\<^sub>m 2"
      using k unfolding kraus_operators_def Ws by auto
    have "W\<^sup>\<dagger> * W \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF dagger_carrier[OF Wc] Wc])
    hence e: "W\<^sup>\<dagger> * W = 1\<^sub>m 2" using e0 by simp
    have ent: "(W\<^sup>\<dagger> * W) $$ (i, j) = cnj (W $$ (0, i)) * W $$ (0, j)" if "i < 2" "j < 2" for i j
      using Wc that by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    have "cnj (W $$ (0, 0)) * W $$ (0, 0) = 1" "cnj (W $$ (0, 1)) * W $$ (0, 1) = 1" "cnj (W $$ (0, 0)) * W $$ (0, 1) = 0"
      using ent[of 0 0] ent[of 1 1] ent[of 0 1] e by simp_all
    thus False by auto
  qed
qed

theorem notes_form_i_false:
  "\<not> (\<forall>Ws. kraus_operators 2 1 Ws \<longrightarrow> (\<exists>Bs. length Bs = 2 \<and> (\<forall>l<2. length (Bs ! l) \<le> 1 \<and> kraus_operators 2 1 (Bs ! l))
      \<and> (\<forall>X \<in> carrier_mat 2 2. kraus_map_dim 1 Ws X = (1 / 2) \<cdot>\<^sub>m kraus_map_dim 1 (concat Bs) X)))"
proof
  assume h: "\<forall>Ws. kraus_operators 2 1 Ws \<longrightarrow> (\<exists>Bs. length Bs = 2 \<and> (\<forall>l<2. length (Bs ! l) \<le> 1 \<and> kraus_operators 2 1 (Bs ! l))
      \<and> (\<forall>X \<in> carrier_mat 2 2. kraus_map_dim 1 Ws X = (1 / 2) \<cdot>\<^sub>m kraus_map_dim 1 (concat Bs) X))"
  let ?e = "\<lambda>k. Matrix.mat 1 2 (\<lambda>(i, j). if j = k then 1 else 0) :: complex Matrix.mat"
  have "kraus_operators 2 1 [?e 0, ?e 1]"
    unfolding kraus_operators_def
    by (auto intro!: eq_matI simp: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def less_Suc_eq numeral_2_eq_2)
  then obtain Bs where "\<forall>l<2. length (Bs ! l) \<le> 1 \<and> kraus_operators 2 1 (Bs ! l)" using h by blast
  hence "length (Bs ! 0) \<le> 1 \<and> kraus_operators 2 1 (Bs ! 0)" by simp
  thus False using no_tp_rank_one by blast
qed

end
