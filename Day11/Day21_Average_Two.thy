theory Day21_Average_Two
  imports Day21_Average_Conjecture
begin

section \<open>D21-2 for $n=2$\<close>

text \<open>Every unital completely positive $\Phi:M_2\to M_d$ is the average of two unital maps of Choi
rank at most $d$ (\<open>ra_two\<close>; Bacon, Smolin and Wolf).  The off-diagonal block of the Choi matrix is
$R_1KR_2^*$ with $R_iR_i^*$ the diagonal blocks and $K$ a contraction (\<open>wide_factor\<close>,
\<open>bessel_rows\<close>), and a contraction is the average of two unitaries (\<open>contraction_avg\<close>, through a
singular value decomposition, \<open>svd_square\<close>).\<close>

subsection \<open>Completing an orthonormal family to an orthonormal basis\<close>

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
    thus ?thesis by (metis mult_cancel_right1 mult_eq_0_iff)
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

subsection \<open>Singular value decomposition\<close>

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
    have "complex_of_real (\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2) = (\<Sum>c<d. cnj ((Km * V) $$ (c, k)) * (Km * V) $$ (c, k))"
      by (simp add: complex_mult_cnj cmod_power2 Groups.mult.commute[of "cnj _"] del: of_real_power)
    hence "(\<Sum>c<d. (cmod ((Km * V) $$ (c, k)))\<^sup>2) = D ! k" using gram_e[OF k k] by (metis of_real_eq_iff)
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

subsection \<open>A contraction is the average of two unitaries\<close>

definition phase_diag :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat" where
  "phase_diag d \<theta> = Matrix.mat d d (\<lambda>(i, j). if i = j then cis (\<theta> i) else 0)"

lemma phase_diag_carrier [simp]: "phase_diag d \<theta> \<in> carrier_mat d d" by (simp add: phase_diag_def)

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
      moreover have "complex_of_real (\<Sum>a<d. (cmod (V $$ (a, k)))\<^sup>2) = (\<Sum>a<d. cnj (V $$ (a, k)) * V $$ (a, k))"
        by (simp add: complex_mult_cnj cmod_power2 Groups.mult.commute[of "cnj _"] del: of_real_power)
      ultimately have "(\<Sum>a<d. (cmod (V $$ (a, k)))\<^sup>2) = 1" by (metis of_real_eq_1_iff)
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

subsection \<open>Bessel's inequality for rows that are orthonormal or zero\<close>

lemma cmod_sq_cnj: "complex_of_real ((cmod z)\<^sup>2) = z * cnj z"
  by (simp add: complex_mult_cnj cmod_power2 del: of_real_power)

lemma cmod_sq_sum: "complex_of_real (\<Sum>k\<in>A. (cmod (f k))\<^sup>2) = (\<Sum>k\<in>A. f k * cnj (f k))"
  by (simp only: of_real_sum cmod_sq_cnj)

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
        using cmod_sq_sum[of c "{..<d}"] by (metis complex_cnj_complex_of_real)
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

subsection \<open>Factoring a wide matrix\<close>

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

subsection \<open>The case $n=2$\<close>

definition gk :: "complex Matrix.mat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "gk Fs p q i i' = (\<Sum>k<length Fs. Fs ! k $$ (i, p) * cnj (Fs ! k $$ (i', q)))"

lemma kraus2_entry:
  assumes F: "\<forall>A \<in> set Fs. A \<in> carrier_mat d 2" and X: "X \<in> carrier_mat 2 2" and i: "i < d" and i': "i' < d"
  shows "kraus_map_dim d Fs X $$ (i, i') = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * gk Fs p q i i')"
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
  also have "\<dots> = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * gk Fs p q i i')"
    unfolding gk_def sum_distrib_left by (subst sum.swap, rule sum.cong[OF refl], rule sum.swap)
  finally show ?thesis .
qed

lemma gk_map:
  "gk (map f [0..<d]) p q i i' = (\<Sum>j<d. f j $$ (i, p) * cnj (f j $$ (i', q)))"
  by (simp add: gk_def)

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
  shows "ra_split 2 d (kraus_map_dim d As)"
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
        unfolding of_real_sum by (rule sum.cong[OF refl]) (simp only: if_distrib[of complex_of_real] of_real_0 cmod_sq_cnj)
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
  have g00: "gk (L l) 0 0 i i' = gk As 0 0 i i'" if "i < d" "i' < d" for l i i'
    using RR1 that by (simp add: L_def gk_map C_def gk_def a_def)
  have g11: "gk (L l) 1 1 i i' = gk As 1 1 i i'" if ii: "i < d" "i' < d" for l i i'
  proof -
    have Yc: "Y l \<in> carrier_mat d d" using R2c Uc by (simp add: Y_def dagger_carrier)
    have "gk (L l) 1 1 i i' = (\<Sum>j<d. Y l $$ (i, j) * cnj (Y l $$ (i', j)))" using ii by (simp add: L_def gk_map C_def)
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
    finally show ?thesis using RR2 ii by (simp add: gk_def b_def)
  qed
  have g01l: "gk (L l) 0 1 i i' = (\<Sum>j<d. \<Sum>m<d. R1 $$ (i, j) * U l $$ (j, m) * cnj (R2 $$ (i', m)))" if ii: "i < d" "i' < d" for l i i'
  proof -
    have Yc: "Y l \<in> carrier_mat d d" using R2c Uc by (simp add: Y_def dagger_carrier)
    have "gk (L l) 0 1 i i' = (\<Sum>j<d. R1 $$ (i, j) * cnj (Y l $$ (i', j)))" using ii by (simp add: L_def gk_map C_def)
    also have "\<dots> = (R1 * ((Y l)\<^sup>\<dagger>)) $$ (i, i')" by (rule prod_dagger_entry[OF R1c Yc ii, symmetric])
    also have "R1 * ((Y l)\<^sup>\<dagger>) = R1 * U l * (R2\<^sup>\<dagger>)" unfolding Ydag using R1c Uc R2c by (simp add: assoc_mult_mat[of _ d d _ d _ d] dagger_carrier)
    finally show ?thesis by (simp add: mult_entry3[OF R1c Uc R2c ii])
  qed
  have g01: "(gk (L 0) 0 1 i i' + gk (L 1) 0 1 i i') / 2 = gk As 0 1 i i'" if ii: "i < d" "i' < d" for i i'
  proof -
    have "gk (L 0) 0 1 i i' + gk (L 1) 0 1 i i' = (\<Sum>j<d. \<Sum>m<d. 2 * (R1 $$ (i, j) * Kc $$ (j, m) * cnj (R2 $$ (i', m))))"
      unfolding g01l[OF ii] sum.distrib[symmetric]
    proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
      fix j m assume "j \<in> {..<d}" "m \<in> {..<d}"
      hence "Kc $$ (j, m) = (U1 $$ (j, m) + U2 $$ (j, m)) / 2" using Kav by simp
      thus "R1 $$ (i, j) * U 0 $$ (j, m) * cnj (R2 $$ (i', m)) + R1 $$ (i, j) * U 1 $$ (j, m) * cnj (R2 $$ (i', m))
          = 2 * (R1 $$ (i, j) * Kc $$ (j, m) * cnj (R2 $$ (i', m)))" unfolding \<open>Kc $$ (j, m) = (U1 $$ (j, m) + U2 $$ (j, m)) / 2\<close> by (simp add: U_def algebra_simps)
    qed
    hence "(gk (L 0) 0 1 i i' + gk (L 1) 0 1 i i') / 2 = (\<Sum>j<d. \<Sum>m<d. R1 $$ (i, j) * Kc $$ (j, m) * cnj (R2 $$ (i', m)))"
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
    finally show ?thesis by (simp add: gk_def a_def b_def)
  qed
  have gsym: "gk Fs 1 0 i i' = cnj (gk Fs 0 1 i' i)" for Fs i i'
    unfolding gk_def cnj_sum by (rule sum.cong[OF refl]) simp
  have gav: "(gk (L 0) p q i i' + gk (L 1) p q i i') / 2 = gk As p q i i'" if pq: "p < 2" "q < 2" and ii: "i < d" "i' < d" for p q i i'
  proof -
    have "p = 0 \<and> q = 0 \<or> p = 1 \<and> q = 1 \<or> p = 0 \<and> q = 1 \<or> p = 1 \<and> q = 0" using pq by auto
    thus ?thesis
    proof (elim disjE)
      assume "p = 1 \<and> q = 0"
      hence "(gk (L 0) p q i i' + gk (L 1) p q i i') / 2 = cnj ((gk (L 0) 0 1 i' i + gk (L 1) 0 1 i' i) / 2)"
        by (simp add: gsym gsym[unfolded One_nat_def])
      also have "\<dots> = gk As p q i i'" using \<open>p = 1 \<and> q = 0\<close> g01[OF ii(2,1)] by (simp add: gsym gsym[unfolded One_nat_def])
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
    have e: "kraus_map_dim d Fs (1\<^sub>m 2) $$ (i, i') = gk Fs 0 0 i i' + gk Fs 1 1 i i'" if "\<forall>A \<in> set Fs. A \<in> carrier_mat d 2" for Fs
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
        = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * ((gk (L 0) p q i i' + gk (L 1) p q i i') / 2))"
    proof -
      have "((1 / of_nat 2) \<cdot>\<^sub>m kraus_map_dim d (concat [L 0, L 1]) X) $$ (i, i')
          = (1 / 2) * (kraus_map_dim d (L 0) X $$ (i, i') + kraus_map_dim d (L 1) X $$ (i, i'))"
        unfolding app using c0 c1 ii by simp
      also have "\<dots> = (1 / 2) * ((\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * gk (L 0) p q i i') + (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * gk (L 1) p q i i'))"
        unfolding kraus2_entry[OF Lc X ii] ..
      also have "\<dots> = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * ((gk (L 0) p q i i' + gk (L 1) p q i i') / 2))"
        unfolding sum.distrib[symmetric] sum_distrib_left
        by (rule sum.cong[OF refl], rule sum.cong[OF refl]) (simp add: algebra_simps)
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>p<2. \<Sum>q<2. X $$ (p, q) * gk As p q i i')"
    proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
      fix p q :: nat assume "p \<in> {..<2}" "q \<in> {..<2}"
      hence pq: "p < 2" "q < 2" by simp_all
      show "X $$ (p, q) * ((gk (L 0) p q i i' + gk (L 1) p q i i') / 2) = X $$ (p, q) * gk As p q i i'"
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
  show ?thesis unfolding ra_split_def using B avg by (intro exI[of _ "[L 0, L 1]"]) simp
qed

end
