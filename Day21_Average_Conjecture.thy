(*  Title:   Day21_Average_Conjecture.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 14 October 2011 (Day 21)
*)

theory Day21_Average_Conjecture
  imports Day17_Quantum_Noise
begin

subsection \<open>The conjecture on averages of unital maps (D21-2)\<close>

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
    hence "cos (2 * pi * (real m - real m') / real n) = 1"
      using cis.sel(1)[of "2 * pi * (real m - real m') / real n"] by simp
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

subsubsection \<open>Positive matrices as sums of $d$ rank-one terms\<close>

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
    finally have "D ! k = Re \<langle>?u | Q *\<^sub>v ?u\<rangle>" by (rule Re_of_real_eq)
    thus ?thesis using Q du unfolding psd_def by auto
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
  unfolding ucp_average_split_def by simp

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

subsubsection \<open>Measurement maps\<close>

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

subsubsection \<open>The case $d=1$: Horn's lemma\<close>

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
    have "(\<Sum>a<n. (cmod (\<phi> l $ a))\<^sup>2) = 1" using e unfolding cmod_sq_sum[symmetric] of_real_eq_1_iff .
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

subsubsection \<open>Maps with diagonal values\<close>

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
    have "(\<Sum>p<n. (cmod (\<phi> a l $ p))\<^sup>2) = 1"
      using \<phi>n[OF a l] unfolding cpx_vec_length_def by (auto simp: real_sqrt_eq_1_iff)
    thus ?thesis unfolding cmod_sq_sum'[symmetric] of_real_eq_1_iff .
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

subsubsection \<open>The notes' form (i) is false as written\<close>

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

subsection \<open>The conjecture D21-2 for $n=2$\<close>

text \<open>Every unital completely positive $\Phi:M_2\to M_d$ is the average of two unital maps of Choi
rank at most $d$ (\<open>ra_two\<close>; Bacon, Smolin and Wolf).  The off-diagonal block of the Choi matrix is
$R_1KR_2^*$ with $R_iR_i^*$ the diagonal blocks and $K$ a contraction (\<open>wide_factor\<close>,
\<open>bessel_rows\<close>), and a contraction is the average of two unitaries (\<open>contraction_avg\<close>, through a
singular value decomposition, \<open>svd_square\<close>).\<close>

subsubsection \<open>Completing an orthonormal family to an orthonormal basis\<close>

lemma onb_complete:
  fixes d :: nat and J :: "nat set" and w :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  assumes J: "J \<subseteq> {..<d}"
    and on: "\<And>k k'. k \<in> J \<Longrightarrow> k' \<in> J \<Longrightarrow> (\<Sum>a<d. cnj (w k a) * w k' a) = (if k = k' then 1 else 0)"
  shows "\<exists>W. W \<in> carrier_mat d d \<and> (W\<^sup>\<dagger>) * W = 1\<^sub>m d \<and> (\<forall>k\<in>J. \<forall>a<d. W $$ (a, k) = w k a)"
proof -
  have fJ: "finite J" using J finite_subset by blast
  define Pi where "Pi a b = (\<Sum>k\<in>J. w k a * cnj (w k b))" for a b
  define E where "E = Matrix.mat d d (\<lambda>(a, b). (if a = b then 1 else 0) - Pi a b)"
  have Ec: "E \<in> carrier_mat d d" by (simp add: E_def)
  have Eh: "hermitian E"
    unfolding hermitian_def by (rule eq_matI) (auto simp: E_def dagger_def Pi_def cnj_sum Groups.mult.commute)
  have PP: "(\<Sum>c<d. Pi a c * Pi c b) = Pi a b" for a b
  proof -
    have "(\<Sum>c<d. Pi a c * Pi c b) = (\<Sum>c<d. \<Sum>k\<in>J. \<Sum>k'\<in>J. w k a * cnj (w k' b) * (cnj (w k c) * w k' c))"
      by (simp add: Pi_def sum_distrib_left sum_distrib_right algebra_simps)
    also have "\<dots> = (\<Sum>k\<in>J. \<Sum>k'\<in>J. w k a * cnj (w k' b) * (\<Sum>c<d. cnj (w k c) * w k' c))"
      by (subst sum.swap, rule sum.cong[OF refl], subst sum.swap) (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>k\<in>J. \<Sum>k'\<in>J. if k' = k then w k a * cnj (w k b) else 0)"
      by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (auto simp: on)
    also have "\<dots> = Pi a b" using fJ by (simp add: Pi_def)
    finally show ?thesis .
  qed
  have EE: "E * E = E"
  proof (rule eq_matI)
    fix a b assume "a < dim_row E" "b < dim_col E"
    hence ab: "a < d" "b < d" by (simp_all add: E_def)
    have "(E * E) $$ (a, b) = (\<Sum>c<d. ((if a = c then 1 else 0) - Pi a c) * ((if c = b then 1 else 0) - Pi c b))"
      using ab by (simp add: E_def scalar_prod_def atLeast0LessThan Matrix.row_def)
    also have "\<dots> = (\<Sum>c<d. (if c = a then (if a = b then 1 else 0) else 0) - (if c = a then Pi c b else 0)
                    - (if c = b then Pi a c else 0) + Pi a c * Pi c b)"
      by (rule sum.cong[OF refl]) (auto simp: algebra_simps)
    also have "\<dots> = (if a = b then 1 else 0) - Pi a b - Pi a b + Pi a b"
      using ab by (simp add: sum.distrib sum_subtractf PP)
    also have "\<dots> = E $$ (a, b)" using ab by (simp add: E_def)
    finally show "(E * E) $$ (a, b) = E $$ (a, b)" .
  qed (simp_all add: E_def)
  obtain U :: "complex Matrix.mat" and \<mu> :: "real list" where Uc: "U \<in> carrier_mat d d" and Uu: "unitary U"
    and \<mu>l: "length \<mu> = d" and spec: "U\<^sup>\<dagger> * E * U = diag_mat_of_real \<mu>"
    using hermitian_spectral_decomp[OF Ec Eh] by blast
  have UU: "U\<^sup>\<dagger> * U = 1\<^sub>m d" "U * (U\<^sup>\<dagger>) = 1\<^sub>m d" using Uu Uc unfolding unitary_def by auto
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat d d" by (rule dagger_carrier[OF Uc])
  have EU: "E * U = U * diag_mat_of_real \<mu>" by (rule hermitian_spectral_decomp_right[OF Uc Ec Uu spec])
  have \<mu>01: "\<mu> ! i = 0 \<or> \<mu> ! i = 1" if i: "i < d" for i
  proof -
    have "diag_mat_of_real \<mu> * diag_mat_of_real \<mu> = U\<^sup>\<dagger> * E * (U * (U\<^sup>\<dagger>)) * E * U"
      unfolding spec[symmetric] using Uc Ud Ec by (simp add: assoc_mult_mat[of _ d d _ d _ d])
    also have "\<dots> = U\<^sup>\<dagger> * (E * E) * U" using Uc Ud Ec UU by (simp add: assoc_mult_mat[of _ d d _ d _ d])
    also have "\<dots> = diag_mat_of_real \<mu>" by (simp add: EE spec)
    finally have "(diag_mat_of_real \<mu> * diag_mat_of_real \<mu>) $$ (i, i) = diag_mat_of_real \<mu> $$ (i, i)" by simp
    moreover have "(diag_mat_of_real \<mu> * diag_mat_of_real \<mu>) $$ (i, i) = complex_of_real (\<mu> ! i * \<mu> ! i)"
    proof -
      have "(diag_mat_of_real \<mu> * diag_mat_of_real \<mu>) $$ (i, i) = (\<Sum>c<d. (if i = c then complex_of_real (\<mu> ! i) else 0) * (if c = i then complex_of_real (\<mu> ! c) else 0))"
        using i \<mu>l by (simp add: scalar_prod_def atLeast0LessThan Matrix.row_def)
      also have "\<dots> = (\<Sum>c<d. if c = i then complex_of_real (\<mu> ! i * \<mu> ! i) else 0)" by (rule sum.cong) auto
      finally show ?thesis using i by simp
    qed
    ultimately have "\<mu> ! i * \<mu> ! i = \<mu> ! i" using i \<mu>l by (simp del: of_real_mult)
    thus ?thesis by auto
  qed
  have orth: "(\<Sum>a<d. cnj (w k a) * U $$ (a, i)) = 0" if k: "k \<in> J" and i: "i < d" and m1: "\<mu> ! i = 1" for k i
  proof -
    have z: "(\<Sum>c<d. Pi a c * U $$ (c, i)) = 0" if a: "a < d" for a
    proof -
      have "(E * U) $$ (a, i) = U $$ (a, i)"
      proof -
        have "(U * diag_mat_of_real \<mu>) $$ (a, i) = (\<Sum>c<d. U $$ (a, c) * (if c = i then complex_of_real (\<mu> ! c) else 0))"
          using a i \<mu>l Uc by (simp add: scalar_prod_def atLeast0LessThan Matrix.row_def)
        also have "\<dots> = U $$ (a, i)" using i m1 by (simp add: if_distrib cong: if_cong)
        finally show ?thesis unfolding EU .
      qed
      moreover have "(E * U) $$ (a, i) = U $$ (a, i) - (\<Sum>c<d. Pi a c * U $$ (c, i))"
      proof -
        have "(E * U) $$ (a, i) = (\<Sum>c<d. ((if a = c then 1 else 0) - Pi a c) * U $$ (c, i))"
          using a i Uc by (simp add: E_def scalar_prod_def atLeast0LessThan Matrix.row_def)
        also have "\<dots> = (\<Sum>c<d. if c = a then U $$ (a, i) else 0) - (\<Sum>c<d. Pi a c * U $$ (c, i))"
          by (subst sum_subtractf[symmetric], rule sum.cong[OF refl]) (auto simp: algebra_simps)
        finally show ?thesis using a by simp
      qed
      ultimately show ?thesis by simp
    qed
    have "0 = (\<Sum>a<d. cnj (w k a) * (\<Sum>c<d. Pi a c * U $$ (c, i)))" using z by simp
    also have "\<dots> = (\<Sum>c<d. U $$ (c, i) * (\<Sum>k'\<in>J. (\<Sum>a<d. cnj (w k a) * w k' a) * cnj (w k' c)))"
      by (simp add: Pi_def sum_distrib_left sum_distrib_right algebra_simps, subst sum.swap, rule sum.cong[OF refl],
          subst sum.swap, simp add: sum_distrib_left sum_distrib_right algebra_simps)
    also have "\<dots> = (\<Sum>c<d. U $$ (c, i) * cnj (w k c))"
    proof (rule sum.cong[OF refl])
      fix c assume "c \<in> {..<d}"
      have "(\<Sum>k'\<in>J. (\<Sum>a<d. cnj (w k a) * w k' a) * cnj (w k' c)) = (\<Sum>k'\<in>J. if k' = k then cnj (w k c) else 0)"
        by (rule sum.cong[OF refl]) (auto simp: on k)
      also have "\<dots> = cnj (w k c)" using fJ k by simp
      finally show "U $$ (c, i) * (\<Sum>k'\<in>J. (\<Sum>a<d. cnj (w k a) * w k' a) * cnj (w k' c)) = U $$ (c, i) * cnj (w k c)" by simp
    qed
    finally show ?thesis by (simp add: Groups.mult.commute)
  qed
  have tr1: "(\<Sum>i<d. complex_of_real (\<mu> ! i)) = (\<Sum>a<d. E $$ (a, a))"
  proof -
    have "(\<Sum>i<d. complex_of_real (\<mu> ! i)) = (\<Sum>i<d. (U\<^sup>\<dagger> * E * U) $$ (i, i))" using \<mu>l by (simp add: spec)
    also have "\<dots> = (\<Sum>i<d. \<Sum>c<d. \<Sum>a<d. cnj (U $$ (a, i)) * E $$ (a, c) * U $$ (c, i))"
      using Uc Ec by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def sum_distrib_right)
    also have "\<dots> = (\<Sum>a<d. \<Sum>c<d. E $$ (a, c) * (\<Sum>i<d. U $$ (c, i) * cnj (U $$ (a, i))))"
      by (subst sum.swap, subst (2) sum.swap, rule sum.cong[OF refl], rule sum.swap[THEN trans])
         (simp add: sum_distrib_left algebra_simps)
    also have "\<dots> = (\<Sum>a<d. \<Sum>c<d. E $$ (a, c) * (U * (U\<^sup>\<dagger>)) $$ (c, a))"
      using Uc by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    also have "\<dots> = (\<Sum>a<d. E $$ (a, a))"
    proof (rule sum.cong[OF refl])
      fix a assume a: "a \<in> {..<d}"
      have "(\<Sum>c<d. E $$ (a, c) * (U * (U\<^sup>\<dagger>)) $$ (c, a)) = (\<Sum>c<d. if c = a then E $$ (a, a) else 0)"
        by (rule sum.cong[OF refl]) (use a in \<open>auto simp: UU\<close>)
      thus "(\<Sum>c<d. E $$ (a, c) * (U * (U\<^sup>\<dagger>)) $$ (c, a)) = E $$ (a, a)" using a by simp
    qed
    finally show ?thesis .
  qed
  have tr2: "(\<Sum>a<d. E $$ (a, a)) = of_nat d - of_nat (card J)"
  proof -
    have "(\<Sum>a<d. Pi a a) = (\<Sum>a<d. \<Sum>k\<in>J. cnj (w k a) * w k a)"
      by (simp add: Pi_def Groups.mult.commute)
    also have "\<dots> = (\<Sum>k\<in>J. \<Sum>a<d. cnj (w k a) * w k a)" by (rule sum.swap)
    also have "\<dots> = of_nat (card J)" by (simp add: on)
    finally show ?thesis by (simp add: E_def sum_subtractf)
  qed
  define I1 where "I1 = {i. i < d \<and> \<mu> ! i = 1}"
  have cI1: "card I1 = d - card J"
  proof -
    have "(\<Sum>i<d. \<mu> ! i) = (\<Sum>i<d. if \<mu> ! i = 1 then 1 else 0)"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..<d}"
      thus "\<mu> ! i = (if \<mu> ! i = 1 then 1 else 0)" using \<mu>01[of i] by auto
    qed
    also have "\<dots> = real (card I1)"
    proof -
      have "I1 = {..<d} \<inter> {i. \<mu> ! i = 1}" by (auto simp: I1_def)
      thus ?thesis by (simp add: sum.If_cases)
    qed
    finally have "(\<Sum>i<d. \<mu> ! i) = real (card I1)" .
    moreover have "complex_of_real (\<Sum>i<d. \<mu> ! i) = (\<Sum>i<d. complex_of_real (\<mu> ! i))" by (simp only: of_real_sum)
    ultimately have "complex_of_real (real (card I1)) = (\<Sum>i<d. complex_of_real (\<mu> ! i))" by simp
    hence "complex_of_real (real (card I1)) = of_nat d - of_nat (card J)" using tr1 tr2 by simp
    moreover have "card J \<le> d" using J card_mono[of "{..<d}" J] by simp
    ultimately have "(of_nat (card I1) :: complex) = of_nat (d - card J)" by (simp add: of_nat_diff)
    thus ?thesis by (simp only: of_nat_eq_iff)
  qed
  have cJc: "card ({..<d} - J) = d - card J" using fJ J by (simp add: card_Diff_subset)
  have fI1: "finite I1" by (simp add: I1_def)
  obtain g where g: "bij_betw g ({..<d} - J) I1"
    using finite_same_card_bij[of "{..<d} - J" I1] fI1 cI1 cJc by auto
  have gI: "k < d \<Longrightarrow> k \<notin> J \<Longrightarrow> g k < d \<and> \<mu> ! (g k) = 1" for k
    using bij_betwE[OF g] by (auto simp: I1_def)
  have ginj: "k < d \<Longrightarrow> k \<notin> J \<Longrightarrow> k' < d \<Longrightarrow> k' \<notin> J \<Longrightarrow> g k = g k' \<Longrightarrow> k = k'" for k k'
    using bij_betw_imp_inj_on[OF g] by (auto dest: inj_onD)
  define W where "W = Matrix.mat d d (\<lambda>(a, k). if k \<in> J then w k a else U $$ (a, g k))"
  have Wc: "W \<in> carrier_mat d d" by (simp add: W_def)
  have Wi: "a < d \<Longrightarrow> k < d \<Longrightarrow> W $$ (a, k) = (if k \<in> J then w k a else U $$ (a, g k))" for a k
    by (simp add: W_def)
  have Ws: "k < d \<Longrightarrow> k' < d \<Longrightarrow> (\<Sum>a<d. cnj (W $$ (a, k)) * W $$ (a, k'))
     = (\<Sum>a<d. cnj (if k \<in> J then w k a else U $$ (a, g k)) * (if k' \<in> J then w k' a else U $$ (a, g k')))" for k k'
    by (rule sum.cong[OF refl]) (simp add: Wi)
  have UUi: "(\<Sum>a<d. cnj (U $$ (a, i)) * U $$ (a, j)) = (if i = j then 1 else 0)" if "i < d" "j < d" for i j
  proof -
    have "(U\<^sup>\<dagger> * U) $$ (i, j) = (\<Sum>a<d. cnj (U $$ (a, i)) * U $$ (a, j))"
      using Uc that by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    thus ?thesis using UU that by simp
  qed
  have WW: "(W\<^sup>\<dagger>) * W = 1\<^sub>m d"
  proof (rule eq_matI)
    fix k k' assume "k < dim_row (1\<^sub>m d)" "k' < dim_col (1\<^sub>m d)"
    hence kk: "k < d" "k' < d" by simp_all
    have e: "((W\<^sup>\<dagger>) * W) $$ (k, k') = (\<Sum>a<d. cnj (W $$ (a, k)) * W $$ (a, k'))"
      using Wc kk by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    show "((W\<^sup>\<dagger>) * W) $$ (k, k') = 1\<^sub>m d $$ (k, k')"
    proof (cases "k \<in> J"; cases "k' \<in> J")
      assume "k \<in> J" "k' \<in> J" thus ?thesis using e kk by (simp add: Ws on)
    next
      assume a: "k \<in> J" "k' \<notin> J"
      hence "(\<Sum>a<d. cnj (W $$ (a, k)) * W $$ (a, k')) = (\<Sum>a<d. cnj (w k a) * U $$ (a, g k'))" using kk by (simp add: Ws)
      also have "\<dots> = 0" by (rule orth) (use a gI[OF kk(2)] in auto)
      finally show ?thesis using e kk a by auto
    next
      assume a: "k \<notin> J" "k' \<in> J"
      hence "(\<Sum>a<d. cnj (W $$ (a, k)) * W $$ (a, k')) = cnj (\<Sum>a<d. cnj (w k' a) * U $$ (a, g k))"
        unfolding Ws[OF kk] using a by (simp add: cnj_sum Groups.mult.commute)
      also have "\<dots> = 0" using orth[of k' "g k"] a gI[OF kk(1)] by simp
      finally show ?thesis using e kk a by auto
    next
      assume a: "k \<notin> J" "k' \<notin> J"
      hence "(\<Sum>a<d. cnj (W $$ (a, k)) * W $$ (a, k')) = (if g k = g k' then 1 else 0)"
        using UUi gI kk by (simp add: Ws)
      also have "\<dots> = 1\<^sub>m d $$ (k, k')" using ginj a kk by auto
      finally show ?thesis using e by simp
    qed
  qed (simp_all add: W_def)
  have "\<forall>k\<in>J. \<forall>a<d. W $$ (a, k) = w k a" using J Wi by auto
  thus ?thesis using Wc WW by blast
qed

subsubsection \<open>Singular value decomposition\<close>

lemma unitary_sq_right: "V \<in> carrier_mat d d \<Longrightarrow> (V\<^sup>\<dagger>) * V = 1\<^sub>m d \<Longrightarrow> V * (V\<^sup>\<dagger>) = 1\<^sub>m d"
  using mat_mult_left_right_inverse[of "V\<^sup>\<dagger>" d V] by (simp add: dagger_carrier)

lemma svd_square:
  assumes Km: "Km \<in> carrier_mat d d"
  shows "\<exists>W V. W \<in> carrier_mat d d \<and> (W\<^sup>\<dagger>) * W = 1\<^sub>m d \<and> V \<in> carrier_mat d d \<and> (V\<^sup>\<dagger>) * V = 1\<^sub>m d
     \<and> (\<forall>a<d. \<forall>b<d. Km $$ (a, b) = (\<Sum>k<d. W $$ (a, k) * complex_of_real (sqrt (\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2)) * cnj (V $$ (b, k))))"
proof -
  let ?G = "Km\<^sup>\<dagger> * Km"
  have Gc: "?G \<in> carrier_mat d d" by (rule mult_carrier_mat[OF dagger_carrier[OF Km] Km])
  obtain V D where Vc: "V \<in> carrier_mat d d" and Dl: "length D = d" and Dnn: "\<And>k. k < d \<Longrightarrow> 0 \<le> D ! k"
    and VV: "(V\<^sup>\<dagger>) * V = 1\<^sub>m d"
    and Ge: "\<And>a b. a < d \<Longrightarrow> b < d \<Longrightarrow> ?G $$ (a, b) = (\<Sum>k<d. V $$ (a, k) * complex_of_real (D ! k) * cnj (V $$ (b, k)))"
    using psd_eig[OF Gc psd_MdagM[OF Km]] by blast
  have VVr: "V * (V\<^sup>\<dagger>) = 1\<^sub>m d" by (rule unitary_sq_right[OF Vc VV])
  have Vd: "V\<^sup>\<dagger> \<in> carrier_mat d d" using Vc by (rule dagger_carrier)
  have Gm: "?G = V * diag_mat_of_real D * (V\<^sup>\<dagger>)"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (V * diag_mat_of_real D * (V\<^sup>\<dagger>))" "b < dim_col (V * diag_mat_of_real D * (V\<^sup>\<dagger>))"
    hence ab: "a < d" "b < d" using Vc by simp_all
    show "?G $$ (a, b) = (V * diag_mat_of_real D * (V\<^sup>\<dagger>)) $$ (a, b)" by (simp add: Ge ab udu_entry[OF Vc Dl ab])
  qed (use Gc Vc Km in simp_all)
  have KV: "Km * V \<in> carrier_mat d d" using Km Vc by simp
  have gram: "(Km * V)\<^sup>\<dagger> * (Km * V) = diag_mat_of_real D"
  proof -
    have "(Km * V)\<^sup>\<dagger> * (Km * V) = V\<^sup>\<dagger> * ?G * V"
    proof -
      have kd: "Km\<^sup>\<dagger> \<in> carrier_mat d d" by (rule dagger_carrier[OF Km])
      have "(Km * V)\<^sup>\<dagger> = V\<^sup>\<dagger> * (Km\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Km Vc in simp)
      hence "(Km * V)\<^sup>\<dagger> * (Km * V) = V\<^sup>\<dagger> * (Km\<^sup>\<dagger> * (Km * V))" by (simp add: assoc_mult_mat[OF Vd kd KV])
      also have "\<dots> = V\<^sup>\<dagger> * ?G * V" by (simp add: assoc_mult_mat[OF Vd Gc Vc] assoc_mult_mat[OF kd Km Vc])
      finally show ?thesis .
    qed
    also have "\<dots> = diag_mat_of_real D"
    proof -
      have Dc: "diag_mat_of_real D \<in> carrier_mat d d" using diag_mat_of_real_carrier[of D] unfolding Dl .
      have VD: "V * diag_mat_of_real D \<in> carrier_mat d d" using Vc Dc by simp
      have "V\<^sup>\<dagger> * (V * diag_mat_of_real D * (V\<^sup>\<dagger>)) = (V\<^sup>\<dagger> * V) * diag_mat_of_real D * (V\<^sup>\<dagger>)"
        by (simp add: assoc_mult_mat[OF Vd VD Vd, symmetric] assoc_mult_mat[OF Vd Vc Dc, symmetric])
      also have "\<dots> = diag_mat_of_real D * (V\<^sup>\<dagger>)" using VV by (simp add: left_mult_one_mat[OF Dc])
      finally have "V\<^sup>\<dagger> * (V * diag_mat_of_real D * (V\<^sup>\<dagger>)) * V = diag_mat_of_real D * (V\<^sup>\<dagger>) * V" by simp
      also have "\<dots> = diag_mat_of_real D" using VV by (simp add: assoc_mult_mat[OF Dc Vd Vc] right_mult_one_mat[OF Dc])
      finally show ?thesis unfolding Gm .
    qed
    finally show ?thesis .
  qed
  have gram_e: "(\<Sum>c<d. cnj ((Km * V) $$ (c, j)) * (Km * V) $$ (c, k)) = (if j = k then complex_of_real (D ! k) else 0)"
    if jk: "j < d" "k < d" for j k
  proof -
    have "((Km * V)\<^sup>\<dagger> * (Km * V)) $$ (j, k) = (\<Sum>c<d. cnj ((Km * V) $$ (c, j)) * (Km * V) $$ (c, k))"
      using KV Km Vc jk by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    hence "(\<Sum>c<d. cnj ((Km * V) $$ (c, j)) * (Km * V) $$ (c, k)) = (if j = k then complex_of_real (D ! j) else 0)" using gram jk Dl by simp
    thus ?thesis by simp
  qed
  define \<sigma> where "\<sigma> k = sqrt (\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2)" for k
  have \<sigma>D: "\<sigma> k = sqrt (D ! k)" if k: "k < d" for k
  proof -
    have "(\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2) = D ! k"
      using gram_e[OF k k] unfolding cmod_sq_sum'[symmetric] if_P[OF refl] of_real_eq_iff .
    thus ?thesis by (simp add: \<sigma>_def)
  qed
  define J where "J = {k. k < d \<and> 0 < D ! k}"
  define w where "w k a = (Km * V) $$ (a, k) / complex_of_real (\<sigma> k)" for k a
  have on: "(\<Sum>a<d. cnj (w k a) * w k' a) = (if k = k' then 1 else 0)" if "k \<in> J" "k' \<in> J" for k k'
  proof -
    have kk: "k < d" "k' < d" "0 < D ! k" "0 < D ! k'" using that by (auto simp: J_def)
    have "(\<Sum>a<d. cnj (w k a) * w k' a) = (\<Sum>a<d. cnj ((Km * V) $$ (a, k)) * (Km * V) $$ (a, k')) / (complex_of_real (\<sigma> k) * complex_of_real (\<sigma> k'))"
      by (simp add: w_def sum_divide_distrib)
    also have "\<dots> = (if k = k' then 1 else 0)"
      using gram_e[OF kk(1,2)] kk by (auto simp: \<sigma>D simp flip: of_real_mult)
    finally show ?thesis .
  qed
  have JJ: "J \<subseteq> {..<d}" by (auto simp: J_def)
  obtain W where Wc: "W \<in> carrier_mat d d" and WW: "(W\<^sup>\<dagger>) * W = 1\<^sub>m d" and Ww0: "\<forall>k\<in>J. \<forall>a<d. W $$ (a, k) = w k a"
    using onb_complete[OF JJ on] by blast
  have Ww: "\<And>k a. k \<in> J \<Longrightarrow> a < d \<Longrightarrow> W $$ (a, k) = w k a" using Ww0 by blast
  have KVW: "(Km * V) $$ (a, k) = W $$ (a, k) * complex_of_real (\<sigma> k)" if ak: "a < d" "k < d" for a k
  proof (cases "k \<in> J")
    case True
    have "\<sigma> k \<noteq> 0" using True \<sigma>D[OF ak(2)] by (simp add: J_def)
    thus ?thesis using True ak by (simp add: Ww w_def)
  next
    case False
    hence D0: "D ! k = 0" using Dnn[OF ak(2)] ak by (auto simp: J_def)
    have "(\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2) = 0" using \<sigma>D[OF ak(2)] D0 by (simp add: \<sigma>_def)
    hence "(cmod ((Km * V) $$ (a, k)))\<^sup>2 = 0" using ak by (simp add: sum_nonneg_eq_0_iff)
    thus ?thesis using \<sigma>D[OF ak(2)] D0 by simp
  qed
  have "Km $$ (a, b) = (\<Sum>k<d. W $$ (a, k) * complex_of_real (\<sigma> k) * cnj (V $$ (b, k)))" if ab: "a < d" "b < d" for a b
  proof -
    have "Km = Km * V * (V\<^sup>\<dagger>)" using Km Vc Vd VVr by (simp add: assoc_mult_mat[of _ d d _ d _ d])
    hence "Km $$ (a, b) = (Km * V * (V\<^sup>\<dagger>)) $$ (a, b)" by simp
    also have "\<dots> = (\<Sum>k<d. (Km * V) $$ (a, k) * cnj (V $$ (b, k)))"
      using KV Km Vc ab by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    finally show ?thesis using ab by (simp add: KVW)
  qed
  thus ?thesis using Wc WW Vc VV unfolding \<sigma>_def by blast
qed

subsubsection \<open>A contraction is the average of two unitaries\<close>

definition phase_diag :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat" where
  "phase_diag d \<theta> = Matrix.mat d d (\<lambda>(i, j). if i = j then cis (\<theta> i) else 0)"

lemma phase_diag_carrier [simp]: "phase_diag d \<theta> \<in> carrier_mat d d" by (simp add: phase_diag_def)

text \<open>A contraction is the average of two unitaries.  Write $K=W\Sigma V^*$ with $W,V$ unitary and
$\Sigma=\diag(\sigma_i)$, $0\le\sigma_i\le1$, and $\sigma_i=\cos\theta_i=\tfrac12(e^{i\theta_i}+e^{-i\theta_i})$.  Then
\[ K=\tfrac12\bigl(WD_{\theta}V^*+WD_{-\theta}V^*\bigr),\qquad D_\theta=\diag(e^{i\theta_1},\dots,e^{i\theta_d}), \]
and both $WD_{\pm\theta}V^*$ are unitary.\<close>

lemma phase_diag_unitary: "(phase_diag d \<theta>)\<^sup>\<dagger> * phase_diag d \<theta> = 1\<^sub>m d"
proof (rule eq_matI)
  fix i j assume "i < dim_row (1\<^sub>m d)" "j < dim_col (1\<^sub>m d)"
  hence ij: "i < d" "j < d" by simp_all
  have "((phase_diag d \<theta>)\<^sup>\<dagger> * phase_diag d \<theta>) $$ (i, j) = (\<Sum>c<d. cnj (if c = i then cis (\<theta> c) else 0) * (if c = j then cis (\<theta> c) else 0))"
    using ij by (simp add: phase_diag_def scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
  also have "\<dots> = (\<Sum>c<d. if c = i then (if i = j then 1 else 0) else 0)"
    by (rule sum.cong[OF refl]) (auto simp: cis_cnj cis_mult)
  finally show "((phase_diag d \<theta>)\<^sup>\<dagger> * phase_diag d \<theta>) $$ (i, j) = 1\<^sub>m d $$ (i, j)" using ij by simp
qed (simp_all add: phase_diag_def)

lemma wdv_entry:
  assumes W: "W \<in> carrier_mat d d" and V: "V \<in> carrier_mat d d" and a: "a < d" and b: "b < d"
  shows "(W * phase_diag d \<theta> * (V\<^sup>\<dagger>)) $$ (a, b) = (\<Sum>k<d. W $$ (a, k) * cis (\<theta> k) * cnj (V $$ (b, k)))"
proof -
  have WD: "W * phase_diag d \<theta> \<in> carrier_mat d d" using W by simp
  have e: "(W * phase_diag d \<theta>) $$ (a, k) = W $$ (a, k) * cis (\<theta> k)" if k: "k < d" for k
  proof -
    have "(W * phase_diag d \<theta>) $$ (a, k) = (\<Sum>u<d. W $$ (a, u) * (if u = k then cis (\<theta> u) else 0))"
      using W a k by (simp add: phase_diag_def scalar_prod_def atLeast0LessThan Matrix.row_def)
    also have "\<dots> = (\<Sum>u<d. if u = k then W $$ (a, k) * cis (\<theta> k) else 0)" by (rule sum.cong) auto
    finally show ?thesis using k by simp
  qed
  show ?thesis unfolding prod_dagger_entry[OF WD V a b] using e by simp
qed

lemma unitary_triple:
  assumes W: "W \<in> carrier_mat d d" "(W\<^sup>\<dagger>) * W = 1\<^sub>m d" and V: "V \<in> carrier_mat d d" "(V\<^sup>\<dagger>) * V = 1\<^sub>m d"
    and D: "D \<in> carrier_mat d d" "(D\<^sup>\<dagger>) * D = 1\<^sub>m d"
  shows "(W * D * (V\<^sup>\<dagger>))\<^sup>\<dagger> * (W * D * (V\<^sup>\<dagger>)) = 1\<^sub>m d"
proof -
  have Wd: "W\<^sup>\<dagger> \<in> carrier_mat d d" and Vd: "V\<^sup>\<dagger> \<in> carrier_mat d d" and Dd: "D\<^sup>\<dagger> \<in> carrier_mat d d"
    using W V D by (simp_all add: dagger_carrier)
  have VVr: "V * (V\<^sup>\<dagger>) = 1\<^sub>m d" by (rule unitary_sq_right[OF V])
  have WD: "W * D \<in> carrier_mat d d" using W D by simp
  have "(W * D * (V\<^sup>\<dagger>))\<^sup>\<dagger> = V * ((W * D)\<^sup>\<dagger>)"
    using dagger_of_prod[of "W * D" "V\<^sup>\<dagger>"] WD Vd D V by (simp add: dagger_of_dagger_is_id)
  also have "(W * D)\<^sup>\<dagger> = D\<^sup>\<dagger> * (W\<^sup>\<dagger>)" using dagger_of_prod[of W D] W D by simp
  finally have e: "(W * D * (V\<^sup>\<dagger>))\<^sup>\<dagger> = V * (D\<^sup>\<dagger> * (W\<^sup>\<dagger>))" .
  have Yc: "W * D * (V\<^sup>\<dagger>) \<in> carrier_mat d d" using WD Vd by simp
  have Xc: "D\<^sup>\<dagger> * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using Dd Wd by simp
  have "W\<^sup>\<dagger> * (W * D * (V\<^sup>\<dagger>)) = D * (V\<^sup>\<dagger>)"
    using assoc_mult_mat[OF Wd WD Vd, symmetric] assoc_mult_mat[OF Wd W(1) D(1), symmetric] W(2) D(1)
    by (simp add: left_mult_one_mat[OF D(1)])
  hence "D\<^sup>\<dagger> * (W\<^sup>\<dagger>) * (W * D * (V\<^sup>\<dagger>)) = V\<^sup>\<dagger>"
    using assoc_mult_mat[OF Dd Wd Yc] assoc_mult_mat[OF Dd D(1) Vd, symmetric] D(2) by (simp add: left_mult_one_mat[OF Vd])
  hence "V * (D\<^sup>\<dagger> * (W\<^sup>\<dagger>)) * (W * D * (V\<^sup>\<dagger>)) = 1\<^sub>m d"
    using assoc_mult_mat[OF V(1) Xc Yc] VVr by simp
  thus ?thesis unfolding e .
qed

theorem contraction_avg:
  assumes Km: "Km \<in> carrier_mat d d" and ct: "\<And>x. dim_vec x = d \<Longrightarrow> \<parallel>Km *\<^sub>v x\<parallel> \<le> \<parallel>x\<parallel>"
  shows "\<exists>U1 U2. U1 \<in> carrier_mat d d \<and> U2 \<in> carrier_mat d d \<and> (U1\<^sup>\<dagger>) * U1 = 1\<^sub>m d \<and> (U2\<^sup>\<dagger>) * U2 = 1\<^sub>m d
     \<and> (\<forall>a<d. \<forall>b<d. Km $$ (a, b) = (U1 $$ (a, b) + U2 $$ (a, b)) / 2)"
proof -
  obtain W V where Wc: "W \<in> carrier_mat d d" and WW: "(W\<^sup>\<dagger>) * W = 1\<^sub>m d" and Vc: "V \<in> carrier_mat d d" and VV: "(V\<^sup>\<dagger>) * V = 1\<^sub>m d"
    and Ke: "\<And>a b. a < d \<Longrightarrow> b < d \<Longrightarrow> Km $$ (a, b) = (\<Sum>k<d. W $$ (a, k) * complex_of_real (sqrt (\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2)) * cnj (V $$ (b, k)))"
    using svd_square[OF Km] by blast
  define \<sigma> where "\<sigma> k = sqrt (\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2)" for k
  have \<sigma>1: "0 \<le> \<sigma> k \<and> \<sigma> k \<le> 1" if k: "k < d" for k
  proof -
    let ?v = "Matrix.col V k"
    have dv: "dim_vec ?v = d" using Vc by simp
    have "\<sigma> k = \<parallel>Km *\<^sub>v ?v\<parallel>"
    proof -
      have "(Km *\<^sub>v ?v) $ c = (Km * V) $$ (c, k)" if "c < d" for c
        using Km Vc k that by (simp add: scalar_prod_def atLeast0LessThan Matrix.row_def)
      thus ?thesis using Km by (simp add: \<sigma>_def cpx_vec_length_def)
    qed
    moreover have "\<parallel>?v\<parallel> = 1"
    proof -
      have "(V\<^sup>\<dagger> * V) $$ (k, k) = (\<Sum>a<d. cnj (V $$ (a, k)) * V $$ (a, k))"
        using Vc k by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
      hence "(\<Sum>a<d. cnj (V $$ (a, k)) * V $$ (a, k)) = 1" using VV k by simp
      hence "(\<Sum>a<d. (cmod (V $$ (a, k)))\<^sup>2) = 1" unfolding cmod_sq_sum'[symmetric] of_real_eq_1_iff .
      thus ?thesis using Vc k by (simp add: cpx_vec_length_def)
    qed
    ultimately show ?thesis using ct[OF dv] by (simp add: \<sigma>_def cpx_vec_length_def sum_nonneg)
  qed
  define U where "U s = W * phase_diag d (\<lambda>k. s * arccos (\<sigma> k)) * (V\<^sup>\<dagger>)" for s :: real
  have Uc: "U s \<in> carrier_mat d d" for s unfolding U_def by (rule mult_carrier_mat[OF mult_carrier_mat[OF Wc phase_diag_carrier] dagger_carrier[OF Vc]])
  have Uu: "(U s)\<^sup>\<dagger> * U s = 1\<^sub>m d" for s
    unfolding U_def by (rule unitary_triple[OF Wc WW Vc VV phase_diag_carrier phase_diag_unitary])
  have avg: "Km $$ (a, b) = (U 1 $$ (a, b) + U (- 1) $$ (a, b)) / 2" if ab: "a < d" "b < d" for a b
  proof -
    have "U 1 $$ (a, b) + U (- 1) $$ (a, b) = (\<Sum>k<d. W $$ (a, k) * (cis (arccos (\<sigma> k)) + cis (- arccos (\<sigma> k))) * cnj (V $$ (b, k)))"
      unfolding U_def wdv_entry[OF Wc Vc ab] sum.distrib[symmetric] by (rule sum.cong[OF refl]) (simp add: algebra_simps)
    also have "\<dots> = (\<Sum>k<d. 2 * (W $$ (a, k) * complex_of_real (\<sigma> k) * cnj (V $$ (b, k))))"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {..<d}"
      hence k: "k < d" by simp
      have "cis (arccos (\<sigma> k)) + cis (- arccos (\<sigma> k)) = 2 * complex_of_real (cos (arccos (\<sigma> k)))"
        by (simp add: complex_eq_iff)
      also have "\<dots> = 2 * complex_of_real (\<sigma> k)" using \<sigma>1[OF k] by (simp add: cos_arccos)
      finally show "W $$ (a, k) * (cis (arccos (\<sigma> k)) + cis (- arccos (\<sigma> k))) * cnj (V $$ (b, k))
          = 2 * (W $$ (a, k) * complex_of_real (\<sigma> k) * cnj (V $$ (b, k)))" by simp
    qed
    also have "\<dots> = 2 * Km $$ (a, b)" using Ke[OF ab] by (simp add: \<sigma>_def sum_distrib_left)
    finally have "U 1 $$ (a, b) + U (- 1) $$ (a, b) = 2 * Km $$ (a, b)" .
    thus ?thesis by simp
  qed
  show ?thesis using Uc Uu avg by blast
qed

subsubsection \<open>Bessel's inequality for rows that are orthonormal or zero\<close>

lemma bessel_rows:
  fixes s :: "nat \<Rightarrow> nat \<Rightarrow> complex" and y :: "nat \<Rightarrow> complex" and d K :: nat
  assumes on: "\<And>j j'. j < d \<Longrightarrow> j' < d \<Longrightarrow> (\<Sum>k<K. s j k * cnj (s j' k)) = (if j = j' \<and> j \<in> J then 1 else 0)"
  shows "(\<Sum>j<d. (cmod (\<Sum>k<K. s j k * y k))\<^sup>2) \<le> (\<Sum>k<K. (cmod (y k))\<^sup>2)"
proof -
  define c where "c j = (\<Sum>k<K. s j k * y k)" for j
  define r where "r k = y k - (\<Sum>j<d. cnj (s j k) * c j)" for k
  have cz: "c j = 0" if "j < d" "j \<notin> J" for j
  proof -
    have "(\<Sum>k<K. (cmod (s j k))\<^sup>2) = 0"
    proof -
      have "complex_of_real (\<Sum>k<K. (cmod (s j k))\<^sup>2) = (\<Sum>k<K. s j k * cnj (s j k))" by (rule cmod_sq_sum)
      hence "complex_of_real (\<Sum>k<K. (cmod (s j k))\<^sup>2) = 0" using on[of j j] that by simp
      thus ?thesis by (simp only: of_real_eq_0_iff)
    qed
    hence "\<forall>k<K. s j k = 0" by (simp add: sum_nonneg_eq_0_iff)
    thus ?thesis by (simp add: c_def)
  qed
  have cross: "(\<Sum>k<K. y k * cnj (\<Sum>j<d. cnj (s j k) * c j)) = (\<Sum>j<d. c j * cnj (c j))"
  proof -
    have "(\<Sum>k<K. y k * cnj (\<Sum>j<d. cnj (s j k) * c j)) = (\<Sum>j<d. (\<Sum>k<K. s j k * y k) * cnj (c j))"
      by (simp add: cnj_sum sum_distrib_left sum_distrib_right algebra_simps, rule sum.swap)
    thus ?thesis by (simp add: c_def)
  qed
  have quad: "(\<Sum>k<K. (\<Sum>j<d. cnj (s j k) * c j) * cnj (\<Sum>j<d. cnj (s j k) * c j)) = (\<Sum>j<d. c j * cnj (c j))"
  proof -
    have "(\<Sum>k<K. (\<Sum>j<d. cnj (s j k) * c j) * cnj (\<Sum>j<d. cnj (s j k) * c j))
        = (\<Sum>j<d. \<Sum>j'<d. c j * cnj (c j') * cnj (\<Sum>k<K. s j k * cnj (s j' k)))"
    proof -
      have "(\<Sum>k<K. (\<Sum>j<d. cnj (s j k) * c j) * cnj (\<Sum>j<d. cnj (s j k) * c j))
          = (\<Sum>k<K. \<Sum>j<d. \<Sum>j'<d. c j * cnj (c j') * (cnj (s j k) * s j' k))"
        by (simp add: cnj_sum sum_distrib_left sum_distrib_right algebra_simps) (rule sum.cong[OF refl], rule sum.swap)
      also have "\<dots> = (\<Sum>j<d. \<Sum>j'<d. \<Sum>k<K. c j * cnj (c j') * (cnj (s j k) * s j' k))"
        by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
      also have "\<dots> = (\<Sum>j<d. \<Sum>j'<d. c j * cnj (c j') * cnj (\<Sum>k<K. s j k * cnj (s j' k)))"
        by (simp add: cnj_sum sum_distrib_left)
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>j<d. \<Sum>j'<d. if j' = j then c j * cnj (c j) else 0)"
      by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (auto simp: on cz)
    finally show ?thesis by simp
  qed
  have "0 \<le> (\<Sum>k<K. (cmod (r k))\<^sup>2)" by (simp add: sum_nonneg)
  moreover have "complex_of_real (\<Sum>k<K. (cmod (r k))\<^sup>2) = complex_of_real (\<Sum>k<K. (cmod (y k))\<^sup>2) - complex_of_real (\<Sum>j<d. (cmod (c j))\<^sup>2)"
  proof -
    have "complex_of_real (\<Sum>k<K. (cmod (r k))\<^sup>2) = (\<Sum>k<K. y k * cnj (y k)) - (\<Sum>k<K. y k * cnj (\<Sum>j<d. cnj (s j k) * c j))
        - cnj (\<Sum>k<K. y k * cnj (\<Sum>j<d. cnj (s j k) * c j)) + (\<Sum>k<K. (\<Sum>j<d. cnj (s j k) * c j) * cnj (\<Sum>j<d. cnj (s j k) * c j))"
    proof -
      define z where "z k = (\<Sum>j<d. cnj (s j k) * c j)" for k
      have pt: "r k * cnj (r k) = y k * cnj (y k) - y k * cnj (z k) - cnj (y k * cnj (z k)) + z k * cnj (z k)" for k
      proof -
        have rz: "r k = y k - z k" by (simp add: r_def z_def)
        show ?thesis unfolding rz by (simp add: algebra_simps)
      qed
      have "complex_of_real (\<Sum>k<K. (cmod (r k))\<^sup>2) = (\<Sum>k<K. y k * cnj (y k) - y k * cnj (z k) - cnj (y k * cnj (z k)) + z k * cnj (z k))"
        unfolding cmod_sq_sum pt ..
      also have "\<dots> = (\<Sum>k<K. y k * cnj (y k)) - (\<Sum>k<K. y k * cnj (z k)) - cnj (\<Sum>k<K. y k * cnj (z k)) + (\<Sum>k<K. z k * cnj (z k))"
        by (simp only: sum.distrib sum_subtractf cnj_sum)
      finally show ?thesis by (simp only: z_def)
    qed
    also have "\<dots> = (\<Sum>k<K. y k * cnj (y k)) - (\<Sum>j<d. c j * cnj (c j))"
    proof -
      have rc: "cnj (\<Sum>j<d. c j * cnj (c j)) = (\<Sum>j<d. c j * cnj (c j))"
        unfolding cmod_sq_sum[symmetric] by simp
      show ?thesis unfolding cross quad rc by simp
    qed
    finally show ?thesis unfolding cmod_sq_sum .
  qed
  moreover have "complex_of_real (\<Sum>k<K. (cmod (y k))\<^sup>2) - complex_of_real (\<Sum>j<d. (cmod (c j))\<^sup>2)
      = complex_of_real ((\<Sum>k<K. (cmod (y k))\<^sup>2) - (\<Sum>j<d. (cmod (c j))\<^sup>2))" by (rule of_real_diff[symmetric])
  ultimately have "(\<Sum>j<d. (cmod (c j))\<^sup>2) \<le> (\<Sum>k<K. (cmod (y k))\<^sup>2)"
    by (simp only: of_real_eq_iff)
  thus ?thesis by (simp add: c_def)
qed

subsubsection \<open>Factoring a wide matrix\<close>

text \<open>$M=RS$ with $RR^*=MM^*$ and the rows of $S$ orthonormal or zero.\<close>

lemma wide_factor:
  fixes m :: "nat \<Rightarrow> nat \<Rightarrow> complex" and d Kn :: nat
  shows "\<exists>R S J. R \<in> carrier_mat d d
     \<and> (\<forall>k<Kn. \<forall>a<d. m k a = (\<Sum>j<d. R $$ (a, j) * S j k))
     \<and> (\<forall>a<d. \<forall>b<d. (\<Sum>j<d. R $$ (a, j) * cnj (R $$ (b, j))) = (\<Sum>k<Kn. m k a * cnj (m k b)))
     \<and> (\<forall>j<d. \<forall>j'<d. (\<Sum>k<Kn. S j k * cnj (S j' k)) = (if j = j' \<and> j \<in> J then 1 else 0))"
proof -
  define N where "N = Matrix.mat Kn d (\<lambda>(k, a). cnj (m k a))"
  define P where "P = Matrix.mat d d (\<lambda>(a, b). \<Sum>k<Kn. m k a * cnj (m k b))"
  have Nc: "N \<in> carrier_mat Kn d" by (simp add: N_def)
  have PN: "P = N\<^sup>\<dagger> * N"
    by (rule eq_matI) (auto simp: P_def N_def dagger_def scalar_prod_def atLeast0LessThan Matrix.row_def Groups.mult.commute)
  have Pc: "P \<in> carrier_mat d d" by (simp add: P_def)
  have Pp: "psd P" unfolding PN by (rule psd_MdagM[OF Nc])
  obtain U ev where Uc: "U \<in> carrier_mat d d" and evl: "length ev = d" and ev0: "\<And>j. j < d \<Longrightarrow> 0 \<le> ev ! j"
    and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m d"
    and Pe: "\<And>a b. a < d \<Longrightarrow> b < d \<Longrightarrow> P $$ (a, b) = (\<Sum>j<d. U $$ (a, j) * complex_of_real (ev ! j) * cnj (U $$ (b, j)))"
    using psd_eig[OF Pc Pp] by blast
  have UUr: "U * (U\<^sup>\<dagger>) = 1\<^sub>m d" by (rule unitary_sq_right[OF Uc UU])
  have UUe: "(\<Sum>a<d. cnj (U $$ (a, j)) * U $$ (a, l)) = (if j = l then 1 else 0)" if "j < d" "l < d" for j l
  proof -
    have "(U\<^sup>\<dagger> * U) $$ (j, l) = (\<Sum>a<d. cnj (U $$ (a, j)) * U $$ (a, l))"
      using Uc that by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    thus ?thesis using UU that by simp
  qed
  have UUre: "(\<Sum>j<d. U $$ (a, j) * cnj (U $$ (c, j))) = (if a = c then 1 else 0)" if "a < d" "c < d" for a c
  proof -
    have "(U * (U\<^sup>\<dagger>)) $$ (a, c) = (\<Sum>j<d. U $$ (a, j) * cnj (U $$ (c, j)))"
      using Uc that by (simp add: scalar_prod_def dagger_def atLeast0LessThan Matrix.row_def)
    thus ?thesis using UUr that by simp
  qed
  define t where "t j k = (\<Sum>a<d. cnj (U $$ (a, j)) * m k a)" for j k
  have tg: "(\<Sum>k<Kn. t j k * cnj (t j' k)) = (if j = j' then complex_of_real (ev ! j) else 0)" if jj: "j < d" "j' < d" for j j'
  proof -
    have "(\<Sum>k<Kn. t j k * cnj (t j' k)) = (\<Sum>a<d. \<Sum>b<d. cnj (U $$ (a, j)) * U $$ (b, j') * (\<Sum>k<Kn. m k a * cnj (m k b)))"
    proof -
      have "(\<Sum>k<Kn. t j k * cnj (t j' k)) = (\<Sum>k<Kn. \<Sum>a<d. \<Sum>b<d. cnj (U $$ (a, j)) * U $$ (b, j') * (m k a * cnj (m k b)))"
        by (simp add: t_def cnj_sum sum_distrib_left sum_distrib_right algebra_simps) (rule sum.cong[OF refl], rule sum.swap)
      also have "\<dots> = (\<Sum>a<d. \<Sum>b<d. \<Sum>k<Kn. cnj (U $$ (a, j)) * U $$ (b, j') * (m k a * cnj (m k b)))"
        by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
      finally show ?thesis by (simp add: sum_distrib_left)
    qed
    also have "\<dots> = (\<Sum>a<d. \<Sum>b<d. cnj (U $$ (a, j)) * U $$ (b, j') * (\<Sum>l<d. U $$ (a, l) * complex_of_real (ev ! l) * cnj (U $$ (b, l))))"
      by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: Pe[symmetric] P_def)
    also have "\<dots> = (\<Sum>l<d. complex_of_real (ev ! l) * (\<Sum>a<d. cnj (U $$ (a, j)) * U $$ (a, l)) * (\<Sum>b<d. cnj (U $$ (b, l)) * U $$ (b, j')))"
    proof -
      have "(\<Sum>a<d. \<Sum>b<d. cnj (U $$ (a, j)) * U $$ (b, j') * (\<Sum>l<d. U $$ (a, l) * complex_of_real (ev ! l) * cnj (U $$ (b, l))))
          = (\<Sum>a<d. \<Sum>b<d. \<Sum>l<d. complex_of_real (ev ! l) * (cnj (U $$ (a, j)) * U $$ (a, l)) * (cnj (U $$ (b, l)) * U $$ (b, j')))"
        by (simp add: sum_distrib_left algebra_simps)
      also have "\<dots> = (\<Sum>l<d. \<Sum>a<d. \<Sum>b<d. complex_of_real (ev ! l) * (cnj (U $$ (a, j)) * U $$ (a, l)) * (cnj (U $$ (b, l)) * U $$ (b, j')))"
        by (subst (2) sum.swap, subst sum.swap, rule refl)
      also have "\<dots> = (\<Sum>l<d. complex_of_real (ev ! l) * (\<Sum>a<d. cnj (U $$ (a, j)) * U $$ (a, l)) * (\<Sum>b<d. cnj (U $$ (b, l)) * U $$ (b, j')))"
        by (rule sum.cong[OF refl]) (simp add: sum_distrib_left sum_distrib_right algebra_simps)
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>l<d. if l = j then (if j = j' then complex_of_real (ev ! j) else 0) else 0)"
      by (rule sum.cong[OF refl]) (use jj in \<open>auto simp: UUe\<close>)
    finally show ?thesis using jj by simp
  qed
  define J where "J = {j. 0 < ev ! j}"
  define S where "S j k = (if 0 < ev ! j then t j k / complex_of_real (sqrt (ev ! j)) else 0)" for j k
  define R where "R = Matrix.mat d d (\<lambda>(a, j). U $$ (a, j) * complex_of_real (sqrt (ev ! j)))"
  have Rc: "R \<in> carrier_mat d d" by (simp add: R_def)
  have t0: "t j k = 0" if "j < d" "\<not> 0 < ev ! j" "k < Kn" for j k
  proof -
    have l0: "ev ! j = 0" using that ev0[of j] by simp
    have "complex_of_real (\<Sum>k<Kn. (cmod (t j k))\<^sup>2) = 0" unfolding cmod_sq_sum using tg[of j j] that l0 by simp
    hence "(\<Sum>k<Kn. (cmod (t j k))\<^sup>2) = 0" by (simp only: of_real_eq_0_iff)
    thus ?thesis using that by (simp add: sum_nonneg_eq_0_iff)
  qed
  have fac: "m k a = (\<Sum>j<d. R $$ (a, j) * S j k)" if k: "k < Kn" and a: "a < d" for k a
  proof -
    have "(\<Sum>j<d. R $$ (a, j) * S j k) = (\<Sum>j<d. U $$ (a, j) * t j k)"
    proof (rule sum.cong[OF refl])
      fix j assume "j \<in> {..<d}"
      hence j: "j < d" by simp
      show "R $$ (a, j) * S j k = U $$ (a, j) * t j k"
      proof (cases "0 < ev ! j")
        case True
        hence "complex_of_real (sqrt (ev ! j)) \<noteq> 0" by simp
        thus ?thesis using True a j by (simp add: R_def S_def)
      qed (use t0 j k in \<open>simp add: S_def\<close>)
    qed
    also have "\<dots> = (\<Sum>c<d. (\<Sum>j<d. U $$ (a, j) * cnj (U $$ (c, j))) * m k c)"
      by (simp add: t_def sum_distrib_left sum_distrib_right algebra_simps, rule sum.swap)
    also have "\<dots> = (\<Sum>c<d. if c = a then m k a else 0)" by (rule sum.cong[OF refl]) (auto simp: UUre a)
    also have "\<dots> = m k a" using a by simp
    finally show ?thesis by simp
  qed
  have RR: "(\<Sum>j<d. R $$ (a, j) * cnj (R $$ (b, j))) = (\<Sum>k<Kn. m k a * cnj (m k b))" if ab: "a < d" "b < d" for a b
  proof -
    have "(\<Sum>j<d. R $$ (a, j) * cnj (R $$ (b, j))) = (\<Sum>j<d. U $$ (a, j) * complex_of_real (ev ! j) * cnj (U $$ (b, j)))"
    proof (rule sum.cong[OF refl])
      fix j assume "j \<in> {..<d}"
      hence j: "j < d" by simp
      have "complex_of_real (sqrt (ev ! j)) * complex_of_real (sqrt (ev ! j)) = complex_of_real (ev ! j)"
        using ev0[OF j] by (simp flip: of_real_mult)
      thus "R $$ (a, j) * cnj (R $$ (b, j)) = U $$ (a, j) * complex_of_real (ev ! j) * cnj (U $$ (b, j))"
        using ab j by (simp add: R_def algebra_simps)
    qed
    also have "\<dots> = P $$ (a, b)" using Pe[OF ab] by simp
    finally show ?thesis using ab by (simp add: P_def)
  qed
  have on: "(\<Sum>k<Kn. S j k * cnj (S j' k)) = (if j = j' \<and> j \<in> J then 1 else 0)" if jj: "j < d" "j' < d" for j j'
  proof (cases "0 < ev ! j \<and> 0 < ev ! j'")
    case True
    have "(\<Sum>k<Kn. S j k * cnj (S j' k)) = (\<Sum>k<Kn. t j k * cnj (t j' k)) / (complex_of_real (sqrt (ev ! j)) * complex_of_real (sqrt (ev ! j')))"
      using True by (simp add: S_def sum_divide_distrib)
    also have "\<dots> = (if j = j' then 1 else 0)"
      using tg[OF jj] True by (auto simp flip: of_real_mult)
    finally show ?thesis using True by (simp add: J_def)
  qed (auto simp: S_def J_def)
  show ?thesis using Rc fac RR on by blast
qed

subsubsection \<open>The case $n=2$\<close>

definition kraus_gram :: "complex Matrix.mat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "kraus_gram Fs p q i i' = (\<Sum>k<length Fs. Fs ! k $$ (i, p) * cnj (Fs ! k $$ (i', q)))"

lemma kraus2_entry:
  assumes F: "\<forall>A \<in> set Fs. A \<in> carrier_mat d 2" and X: "X \<in> carrier_mat 2 2" and i: "i < d" and i': "i' < d"
  shows "kraus_map_dim d Fs X $$ (i, i') = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * kraus_gram Fs p q i i')"
proof -
  have "kraus_map_dim d Fs X $$ (i, i') = (\<Sum>k<length Fs. (Fs ! k * X * ((Fs ! k)\<^sup>\<dagger>)) $$ (i, i'))"
    unfolding kraus_map_dim_entry_sum_list[OF F X i i'] by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = (\<Sum>k<length Fs. \<Sum>p<2. \<Sum>q<2. X $$ (p, q) * (Fs ! k $$ (i, p) * cnj (Fs ! k $$ (i', q))))"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<length Fs}"
    hence Fk: "Fs ! k \<in> carrier_mat d 2" using F by auto
    show "(Fs ! k * X * ((Fs ! k)\<^sup>\<dagger>)) $$ (i, i') = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * (Fs ! k $$ (i, p) * cnj (Fs ! k $$ (i', q))))"
      unfolding conj_entry[OF Fk X i i'] by (simp add: algebra_simps)
  qed
  also have "\<dots> = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * kraus_gram Fs p q i i')"
    unfolding kraus_gram_def sum_distrib_left by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
  finally show ?thesis .
qed

lemma kraus_gram_map:
  "kraus_gram (map f [0..<d]) p q i i' = (\<Sum>j<d. f j $$ (i, p) * cnj (f j $$ (i', q)))"
  by (simp add: kraus_gram_def)

lemma mult_entry3:
  assumes A: "A \<in> carrier_mat d d" and B: "B \<in> carrier_mat d d" and C: "C \<in> carrier_mat d d" and i: "i < d" and i': "i' < d"
  shows "(A * B * (C\<^sup>\<dagger>)) $$ (i, i') = (\<Sum>j<d. \<Sum>m<d. A $$ (i, j) * B $$ (j, m) * cnj (C $$ (i', m)))"
proof -
  have AB: "A * B \<in> carrier_mat d d" using A B by simp
  have e: "(A * B) $$ (i, m) = (\<Sum>j<d. A $$ (i, j) * B $$ (j, m))" if "m < d" for m
    using A B i that by (simp add: scalar_prod_def atLeast0LessThan Matrix.row_def)
  have "(A * B * (C\<^sup>\<dagger>)) $$ (i, i') = (\<Sum>m<d. (A * B) $$ (i, m) * cnj (C $$ (i', m)))"
    by (rule prod_dagger_entry[OF AB C i i'])
  also have "\<dots> = (\<Sum>m<d. \<Sum>j<d. A $$ (i, j) * B $$ (j, m) * cnj (C $$ (i', m)))"
    by (rule sum.cong[OF refl]) (simp add: e sum_distrib_right)
  finally show ?thesis by (subst (asm) sum.swap)
qed

text \<open>Every unital $\Phi:M_2\to M_d$ is the average of two unital maps of Choi rank at most $d$
(Bacon--Smolin--Wolf): the off-diagonal Choi block is $R_1KR_2^*$ with $K$ a contraction, and
$K=\frac12(U_1+U_2)$.\<close>

theorem ra_two:
  assumes As: "\<forall>A \<in> set As. A \<in> carrier_mat d 2" and u: "kraus_map_dim d As (1\<^sub>m 2) = 1\<^sub>m d"
  shows "ucp_average_split 2 d (kraus_map_dim d As)"
proof -
  let ?K = "length As"
  define a where "a k i = As ! k $$ (i, 0)" for k i
  define b where "b k i = As ! k $$ (i, 1)" for k i
  obtain R1 S1 J1 where R1c: "R1 \<in> carrier_mat d d" and fac1: "\<forall>k<?K. \<forall>i<d. a k i = (\<Sum>j<d. R1 $$ (i, j) * S1 j k)"
    and RR1: "\<forall>i<d. \<forall>i'<d. (\<Sum>j<d. R1 $$ (i, j) * cnj (R1 $$ (i', j))) = (\<Sum>k<?K. a k i * cnj (a k i'))"
    and on1: "\<forall>j<d. \<forall>j'<d. (\<Sum>k<?K. S1 j k * cnj (S1 j' k)) = (if j = j' \<and> j \<in> J1 then 1 else 0)"
    using wide_factor[of d ?K a] by blast
  obtain R2 S2 J2 where R2c: "R2 \<in> carrier_mat d d" and fac2: "\<forall>k<?K. \<forall>i<d. b k i = (\<Sum>j<d. R2 $$ (i, j) * S2 j k)"
    and RR2: "\<forall>i<d. \<forall>i'<d. (\<Sum>j<d. R2 $$ (i, j) * cnj (R2 $$ (i', j))) = (\<Sum>k<?K. b k i * cnj (b k i'))"
    and on2: "\<forall>j<d. \<forall>j'<d. (\<Sum>k<?K. S2 j k * cnj (S2 j' k)) = (if j = j' \<and> j \<in> J2 then 1 else 0)"
    using wide_factor[of d ?K b] by blast
  define Kc where "Kc = Matrix.mat d d (\<lambda>(j, j'). \<Sum>k<?K. S1 j k * cnj (S2 j' k))"
  have Kcc: "Kc \<in> carrier_mat d d" by (simp add: Kc_def)
  have ct: "\<parallel>Kc *\<^sub>v x\<parallel> \<le> \<parallel>x\<parallel>" if dx: "dim_vec x = d" for x
  proof -
    define z where "z k = (\<Sum>j'<d. cnj (S2 j' k) * x $ j')" for k
    have Kx: "(Kc *\<^sub>v x) $ j = (\<Sum>k<?K. S1 j k * z k)" if j: "j < d" for j
    proof -
      have "(Kc *\<^sub>v x) $ j = (\<Sum>j'<d. (\<Sum>k<?K. S1 j k * cnj (S2 j' k)) * x $ j')"
        using j dx by (simp add: Kc_def scalar_prod_def atLeast0LessThan Matrix.row_def)
      also have "\<dots> = (\<Sum>k<?K. S1 j k * z k)"
        by (simp add: z_def sum_distrib_left sum_distrib_right algebra_simps, rule sum.swap)
      finally show ?thesis .
    qed
    have b1: "(\<Sum>j<d. (cmod ((Kc *\<^sub>v x) $ j))\<^sup>2) \<le> (\<Sum>k<?K. (cmod (z k))\<^sup>2)"
    proof -
      have "(\<Sum>j<d. (cmod ((Kc *\<^sub>v x) $ j))\<^sup>2) = (\<Sum>j<d. (cmod (\<Sum>k<?K. S1 j k * z k))\<^sup>2)" by (simp add: Kx)
      also have "\<dots> \<le> (\<Sum>k<?K. (cmod (z k))\<^sup>2)" by (rule bessel_rows) (use on1 in blast)
      finally show ?thesis .
    qed
    have b2: "(\<Sum>k<?K. (cmod (z k))\<^sup>2) \<le> (\<Sum>j<d. (cmod (x $ j))\<^sup>2)"
    proof -
      have "complex_of_real (\<Sum>k<?K. (cmod (z k))\<^sup>2) = (\<Sum>j'<d. \<Sum>j''<d. x $ j' * cnj (x $ j'') * cnj (\<Sum>k<?K. S2 j' k * cnj (S2 j'' k)))"
      proof -
        have "complex_of_real (\<Sum>k<?K. (cmod (z k))\<^sup>2) = (\<Sum>k<?K. \<Sum>j'<d. \<Sum>j''<d. x $ j' * cnj (x $ j'') * (cnj (S2 j' k) * S2 j'' k))"
          unfolding cmod_sq_sum by (simp add: z_def cnj_sum sum_distrib_left sum_distrib_right algebra_simps) (rule sum.cong[OF refl], rule sum.swap)
        also have "\<dots> = (\<Sum>j'<d. \<Sum>j''<d. \<Sum>k<?K. x $ j' * cnj (x $ j'') * (cnj (S2 j' k) * S2 j'' k))"
          by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
        finally show ?thesis by (simp add: cnj_sum sum_distrib_left)
      qed
      also have "\<dots> = (\<Sum>j'<d. if j' \<in> J2 then x $ j' * cnj (x $ j') else 0)"
      proof (rule sum.cong[OF refl])
        fix j' assume j': "j' \<in> {..<d}"
        have "(\<Sum>j''<d. x $ j' * cnj (x $ j'') * cnj (\<Sum>k<?K. S2 j' k * cnj (S2 j'' k)))
            = (\<Sum>j''<d. if j'' = j' then (if j' \<in> J2 then x $ j' * cnj (x $ j') else 0) else 0)"
          by (rule sum.cong[OF refl]) (use j' on2 in auto)
        thus "(\<Sum>j''<d. x $ j' * cnj (x $ j'') * cnj (\<Sum>k<?K. S2 j' k * cnj (S2 j'' k))) = (if j' \<in> J2 then x $ j' * cnj (x $ j') else 0)"
          using j' by simp
      qed
      also have "\<dots> = complex_of_real (\<Sum>j'<d. if j' \<in> J2 then (cmod (x $ j'))\<^sup>2 else 0)"
        unfolding of_real_sum by (rule sum.cong[OF refl]) (simp only: if_distrib[of complex_of_real] of_real_0 complex_norm_square)
      finally have "(\<Sum>k<?K. (cmod (z k))\<^sup>2) = (\<Sum>j'<d. if j' \<in> J2 then (cmod (x $ j'))\<^sup>2 else 0)"
        by (simp only: of_real_eq_iff)
      also have "\<dots> \<le> (\<Sum>j<d. (cmod (x $ j))\<^sup>2)" by (rule sum_mono) simp
      finally show ?thesis .
    qed
    have "(\<Sum>j<d. (cmod ((Kc *\<^sub>v x) $ j))\<^sup>2) \<le> (\<Sum>j<d. (cmod (x $ j))\<^sup>2)" using b1 b2 by linarith
    thus ?thesis using dx Kcc by (simp add: cpx_vec_length_def real_sqrt_le_mono)
  qed
  obtain U1 U2 where U1c: "U1 \<in> carrier_mat d d" and U2c: "U2 \<in> carrier_mat d d"
    and U1u: "(U1\<^sup>\<dagger>) * U1 = 1\<^sub>m d" and U2u: "(U2\<^sup>\<dagger>) * U2 = 1\<^sub>m d"
    and Kav: "\<forall>j<d. \<forall>m<d. Kc $$ (j, m) = (U1 $$ (j, m) + U2 $$ (j, m)) / 2"
    using contraction_avg[OF Kcc ct] by blast
  define U where "U l = (if l = (0::nat) then U1 else U2)" for l
  have Uc: "U l \<in> carrier_mat d d" and Uu: "(U l)\<^sup>\<dagger> * U l = 1\<^sub>m d" for l using U1c U2c U1u U2u by (simp_all add: U_def)
  define Y where "Y l = R2 * ((U l)\<^sup>\<dagger>)" for l
  define C where "C l j = Matrix.mat d 2 (\<lambda>(i, c). if c = 0 then R1 $$ (i, j) else Y l $$ (i, j))" for l j
  define L where "L l = map (C l) [0..<d]" for l
  have Cc: "C l j \<in> carrier_mat d 2" for l j by (simp add: C_def)
  have Lc: "\<forall>A \<in> set (L l). A \<in> carrier_mat d 2" for l by (auto simp: L_def Cc)
  have Ydag: "(Y l)\<^sup>\<dagger> = U l * (R2\<^sup>\<dagger>)" for l
    using dagger_of_prod[of R2 "(U l)\<^sup>\<dagger>"] R2c Uc[of l] by (simp add: Y_def dagger_of_dagger_is_id)
  have g00: "kraus_gram (L l) 0 0 i i' = kraus_gram As 0 0 i i'" if "i < d" "i' < d" for l i i'
    using RR1 that by (simp add: L_def kraus_gram_map C_def kraus_gram_def a_def)
  have g11: "kraus_gram (L l) 1 1 i i' = kraus_gram As 1 1 i i'" if ii: "i < d" "i' < d" for l i i'
  proof -
    have Yc: "Y l \<in> carrier_mat d d" using R2c Uc by (simp add: Y_def dagger_carrier)
    have "kraus_gram (L l) 1 1 i i' = (\<Sum>j<d. Y l $$ (i, j) * cnj (Y l $$ (i', j)))" using ii by (simp add: L_def kraus_gram_map C_def)
    also have "\<dots> = (Y l * ((Y l)\<^sup>\<dagger>)) $$ (i, i')" by (rule prod_dagger_entry[OF Yc Yc ii, symmetric])
    also have "Y l * ((Y l)\<^sup>\<dagger>) = R2 * (R2\<^sup>\<dagger>)"
    proof -
      have Ud: "(U l)\<^sup>\<dagger> \<in> carrier_mat d d" using Uc by (rule dagger_carrier)
      have R2d: "R2\<^sup>\<dagger> \<in> carrier_mat d d" using R2c by (rule dagger_carrier)
      have "Y l * ((Y l)\<^sup>\<dagger>) = R2 * (((U l)\<^sup>\<dagger> * U l) * (R2\<^sup>\<dagger>))"
        unfolding Ydag unfolding Y_def by (simp only: assoc_mult_mat[OF R2c Ud mult_carrier_mat[OF Uc R2d]] assoc_mult_mat[OF Ud Uc R2d])
      thus ?thesis using Uu R2d by (simp add: left_mult_one_mat[OF R2d])
    qed
    also have "(R2 * (R2\<^sup>\<dagger>)) $$ (i, i') = (\<Sum>j<d. R2 $$ (i, j) * cnj (R2 $$ (i', j)))" by (rule prod_dagger_entry[OF R2c R2c ii])
    finally show ?thesis using RR2 ii by (simp add: kraus_gram_def b_def)
  qed
  have g01l: "kraus_gram (L l) 0 1 i i' = (\<Sum>j<d. \<Sum>m<d. R1 $$ (i, j) * U l $$ (j, m) * cnj (R2 $$ (i', m)))" if ii: "i < d" "i' < d" for l i i'
  proof -
    have Yc: "Y l \<in> carrier_mat d d" using R2c Uc by (simp add: Y_def dagger_carrier)
    have "kraus_gram (L l) 0 1 i i' = (\<Sum>j<d. R1 $$ (i, j) * cnj (Y l $$ (i', j)))" using ii by (simp add: L_def kraus_gram_map C_def)
    also have "\<dots> = (R1 * ((Y l)\<^sup>\<dagger>)) $$ (i, i')" by (rule prod_dagger_entry[OF R1c Yc ii, symmetric])
    also have "R1 * ((Y l)\<^sup>\<dagger>) = R1 * U l * (R2\<^sup>\<dagger>)" unfolding Ydag using R1c Uc R2c by (simp add: assoc_mult_mat[of _ d d _ d _ d] dagger_carrier)
    finally show ?thesis by (simp add: mult_entry3[OF R1c Uc R2c ii])
  qed
  have g01: "(kraus_gram (L 0) 0 1 i i' + kraus_gram (L 1) 0 1 i i') / 2 = kraus_gram As 0 1 i i'" if ii: "i < d" "i' < d" for i i'
  proof -
    have "kraus_gram (L 0) 0 1 i i' + kraus_gram (L 1) 0 1 i i' = (\<Sum>j<d. \<Sum>m<d. 2 * (R1 $$ (i, j) * Kc $$ (j, m) * cnj (R2 $$ (i', m))))"
      unfolding g01l[OF ii] sum.distrib[symmetric]
    proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
      fix j m assume "j \<in> {..<d}" "m \<in> {..<d}"
      hence "Kc $$ (j, m) = (U1 $$ (j, m) + U2 $$ (j, m)) / 2" using Kav by simp
      thus "R1 $$ (i, j) * U 0 $$ (j, m) * cnj (R2 $$ (i', m)) + R1 $$ (i, j) * U 1 $$ (j, m) * cnj (R2 $$ (i', m))
          = 2 * (R1 $$ (i, j) * Kc $$ (j, m) * cnj (R2 $$ (i', m)))" unfolding \<open>Kc $$ (j, m) = (U1 $$ (j, m) + U2 $$ (j, m)) / 2\<close> by (simp add: U_def algebra_simps)
    qed
    hence "(kraus_gram (L 0) 0 1 i i' + kraus_gram (L 1) 0 1 i i') / 2 = (\<Sum>j<d. \<Sum>m<d. R1 $$ (i, j) * Kc $$ (j, m) * cnj (R2 $$ (i', m)))"
      by (simp only: sum_distrib_left[symmetric]) simp
    also have "\<dots> = (\<Sum>k<?K. a k i * cnj (b k i'))"
    proof -
      have "(\<Sum>k<?K. a k i * cnj (b k i')) = (\<Sum>k<?K. (\<Sum>j<d. R1 $$ (i, j) * S1 j k) * cnj (\<Sum>m<d. R2 $$ (i', m) * S2 m k))"
        using fac1 fac2 ii by simp
      also have "\<dots> = (\<Sum>k<?K. \<Sum>j<d. \<Sum>m<d. R1 $$ (i, j) * cnj (R2 $$ (i', m)) * (S1 j k * cnj (S2 m k)))"
        by (simp add: cnj_sum sum_distrib_left sum_distrib_right algebra_simps) (rule sum.cong[OF refl], rule sum.swap)
      also have "\<dots> = (\<Sum>j<d. \<Sum>m<d. \<Sum>k<?K. R1 $$ (i, j) * cnj (R2 $$ (i', m)) * (S1 j k * cnj (S2 m k)))"
        by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
      also have "\<dots> = (\<Sum>j<d. \<Sum>m<d. R1 $$ (i, j) * Kc $$ (j, m) * cnj (R2 $$ (i', m)))"
        by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: Kc_def sum_distrib_left algebra_simps)
      finally show ?thesis ..
    qed
    finally show ?thesis by (simp add: kraus_gram_def a_def b_def)
  qed
  have gsym: "kraus_gram Fs 1 0 i i' = cnj (kraus_gram Fs 0 1 i' i)" for Fs i i'
    unfolding kraus_gram_def cnj_sum by (rule sum.cong[OF refl]) simp
  have gav: "(kraus_gram (L 0) p q i i' + kraus_gram (L 1) p q i i') / 2 = kraus_gram As p q i i'" if pq: "p < 2" "q < 2" and ii: "i < d" "i' < d" for p q i i'
  proof -
    have "p = 0 \<and> q = 0 \<or> p = 1 \<and> q = 1 \<or> p = 0 \<and> q = 1 \<or> p = 1 \<and> q = 0" using pq by auto
    thus ?thesis
    proof (elim disjE)
      assume "p = 1 \<and> q = 0"
      hence "(kraus_gram (L 0) p q i i' + kraus_gram (L 1) p q i i') / 2 = cnj ((kraus_gram (L 0) 0 1 i' i + kraus_gram (L 1) 0 1 i' i) / 2)"
        by (simp add: gsym gsym[unfolded One_nat_def])
      also have "\<dots> = kraus_gram As p q i i'" using \<open>p = 1 \<and> q = 0\<close> g01[OF ii(2,1)] by (simp add: gsym gsym[unfolded One_nat_def])
      finally show ?thesis .
    qed (use g00 g11 g01 ii in auto)
  qed
  have unit: "kraus_map_dim d (L l) (1\<^sub>m 2) = 1\<^sub>m d" for l
  proof (rule eq_matI)
    have c: "kraus_map_dim d (L l) (1\<^sub>m 2) \<in> carrier_mat d d" by (rule kraus_map_dim_carrier[OF Lc]) simp
    show "dim_row (kraus_map_dim d (L l) (1\<^sub>m 2)) = dim_row (1\<^sub>m d)" "dim_col (kraus_map_dim d (L l) (1\<^sub>m 2)) = dim_col (1\<^sub>m d)"
      using c by simp_all
    fix i i' assume "i < dim_row (1\<^sub>m d)" "i' < dim_col (1\<^sub>m d)"
    hence ii: "i < d" "i' < d" by simp_all
    have e: "kraus_map_dim d Fs (1\<^sub>m 2) $$ (i, i') = kraus_gram Fs 0 0 i i' + kraus_gram Fs 1 1 i i'" if "\<forall>A \<in> set Fs. A \<in> carrier_mat d 2" for Fs
      unfolding kraus2_entry[OF that one_carrier_mat ii] by (simp add: numeral_2_eq_2)
    have "kraus_map_dim d (L l) (1\<^sub>m 2) $$ (i, i') = kraus_map_dim d As (1\<^sub>m 2) $$ (i, i')"
      unfolding e[OF Lc] e[OF As] using g00[OF ii] g11[OF ii] by simp
    thus "kraus_map_dim d (L l) (1\<^sub>m 2) $$ (i, i') = 1\<^sub>m d $$ (i, i')" unfolding u .
  qed
  have avg: "kraus_map_dim d As X = (1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X" if X: "X \<in> carrier_mat 2 2" for X
  proof (rule eq_matI)
    have c0: "kraus_map_dim d (L 0) X \<in> carrier_mat d d" and c1: "kraus_map_dim d (L 1) X \<in> carrier_mat d d"
      by (rule kraus_map_dim_carrier[OF Lc X])+
    have cA: "kraus_map_dim d As X \<in> carrier_mat d d" by (rule kraus_map_dim_carrier[OF As X])
    have app: "kraus_map_dim d (concat [L 0, L 1]) X = kraus_map_dim d (L 0) X + kraus_map_dim d (L 1) X"
      using kraus_map_dim_append[OF Lc Lc X] by simp
    show "dim_row (kraus_map_dim d As X) = dim_row ((1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X)"
      "dim_col (kraus_map_dim d As X) = dim_col ((1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X)"
      using cA c0 c1 unfolding app by simp_all
    fix i i' assume "i < dim_row ((1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X)"
      "i' < dim_col ((1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X)"
    hence ii: "i < d" "i' < d" using c0 c1 unfolding app by simp_all
    have "((1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X) $$ (i, i')
        = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * ((kraus_gram (L 0) p q i i' + kraus_gram (L 1) p q i i') / 2))"
    proof -
      have "((1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X) $$ (i, i')
          = (1 / 2) * (kraus_map_dim d (L 0) X $$ (i, i') + kraus_map_dim d (L 1) X $$ (i, i'))"
        unfolding app using c0 c1 ii by simp
      also have "\<dots> = (1 / 2) * ((\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * kraus_gram (L 0) p q i i') + (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * kraus_gram (L 1) p q i i'))"
        unfolding kraus2_entry[OF Lc X ii] ..
      also have "\<dots> = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * ((kraus_gram (L 0) p q i i' + kraus_gram (L 1) p q i i') / 2))"
        unfolding sum.distrib[symmetric] sum_distrib_left
        by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: algebra_simps)
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * kraus_gram As p q i i')"
    proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
      fix p q :: nat assume "p \<in> {..<2}" "q \<in> {..<2}"
      hence pq: "p < 2" "q < 2" by simp_all
      show "X $$ (p, q) * ((kraus_gram (L 0) p q i i' + kraus_gram (L 1) p q i i') / 2) = X $$ (p, q) * kraus_gram As p q i i'"
        unfolding gav[OF pq ii] ..
    qed
    also have "\<dots> = kraus_map_dim d As X $$ (i, i')" by (rule kraus2_entry[OF As X ii, symmetric])
    finally show "kraus_map_dim d As X $$ (i, i') = ((1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X) $$ (i, i')" ..
  qed
  have lenL: "length (L l) = d" for l by (simp add: L_def)
  have B: "\<forall>l<2. length ([L 0, L 1] ! l) \<le> d \<and> (\<forall>B \<in> set ([L 0, L 1] ! l). B \<in> carrier_mat d 2)
      \<and> kraus_map_dim d ([L 0, L 1] ! l) (1\<^sub>m 2) = 1\<^sub>m d"
  proof (intro allI impI)
    fix l :: nat assume "l < 2"
    hence "[L 0, L 1] ! l = L l" by (cases l) (auto simp: less_Suc_eq)
    thus "length ([L 0, L 1] ! l) \<le> d \<and> (\<forall>B \<in> set ([L 0, L 1] ! l). B \<in> carrier_mat d 2)
      \<and> kraus_map_dim d ([L 0, L 1] ! l) (1\<^sub>m 2) = 1\<^sub>m d" using lenL Lc unit by simp
  qed
  show ?thesis unfolding ucp_average_split_def using B avg by (intro exI[of _ "[L 0, L 1]"]) simp
qed

end
