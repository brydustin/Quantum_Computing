theory HHL_Sparse_Split
  imports HHL_Simulation
begin

section \<open>Splitting a sparse Hermitian matrix into 1-sparse parts\<close>

definition invol :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "invol n q \<longleftrightarrow> (\<forall>x. q (q x) = x) \<and> (\<forall>x. n \<le> x \<longrightarrow> q x = x)"

lemma invol_lt: "invol n q \<Longrightarrow> x < n \<Longrightarrow> q x < n"
  unfolding invol_def by (metis not_le)

lemma invol_eq: "invol n q \<Longrightarrow> q x = y \<longleftrightarrow> q y = x"
  unfolding invol_def by metis

text \<open>\<open>edge_cover n K p F\<close>: the involutions \<open>p c\<close>, \<open>c < K\<close>, are matchings whose edges lie in
$F$, and every edge of $F$ belongs to exactly one of them.\<close>

definition edge_cover :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool" where
  "edge_cover n K p F \<longleftrightarrow> (\<forall>c<K. invol n (p c)) \<and>
     (\<forall>c<K. \<forall>x. p c x \<noteq> x \<longrightarrow> (min x (p c x), max x (p c x)) \<in> F) \<and>
     (\<forall>x y. (x, y) \<in> F \<longrightarrow> card {c. c < K \<and> p c x = y} = 1)"

definition edges :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<times> nat) set" where
  "edges n A = {(x, y). x < y \<and> y < n \<and> A $$ (x, y) \<noteq> 0}"

definition nbrs :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> nat set" where
  "nbrs n A x = {y. y < n \<and> y \<noteq> x \<and> A $$ (x, y) \<noteq> 0}"

definition sparse :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "sparse n s A \<longleftrightarrow> (\<forall>x<n. card (nbrs n A x) \<le> s)"


lemma finite_edges: "finite (edges n A)"
proof -
  have "edges n A \<subseteq> {..<n} \<times> {..<n}" unfolding edges_def by auto
  thus ?thesis by (rule finite_subset) simp
qed

text \<open>Greedy colouring: an edge $\{a,b\}$ meets at most $s-1$ other edges at each end, so one of
$2s-1$ colours is free at both ends.\<close>

lemma greedy_cover:
  assumes sym: "\<And>x y. x < n \<Longrightarrow> y < n \<Longrightarrow> A $$ (x, y) = 0 \<longleftrightarrow> A $$ (y, x) = 0"
      and sp: "sparse n s A" and K: "2 * s \<le> K + 1"
      and F: "F \<subseteq> edges n A"
  shows "\<exists>p. edge_cover n K p F"
proof -
  have "finite F" using F finite_edges by (rule finite_subset)
  thus ?thesis using F
  proof (induction F rule: finite_induct)
    case empty
    have "edge_cover n K (\<lambda>c x. x) {}" unfolding edge_cover_def invol_def by simp
    thus ?case by blast
  next
    case (insert e F)
    obtain a b where e: "e = (a, b)" by (cases e)
    have ab: "a < b" "b < n" "A $$ (a, b) \<noteq> 0" using insert.prems e by (auto simp: edges_def)
    have eF: "(a, b) \<notin> F" using insert.hyps(2) e by simp
    have FE: "F \<subseteq> edges n A" using insert.prems by simp
    obtain p where p: "edge_cover n K p F" using insert.IH[OF FE] by blast
    have pinv: "\<And>c. c < K \<Longrightarrow> invol n (p c)"
      and pcov: "\<And>c x. c < K \<Longrightarrow> p c x \<noteq> x \<Longrightarrow> (min x (p c x), max x (p c x)) \<in> F"
      and pone: "\<And>x y. (x, y) \<in> F \<Longrightarrow> card {c. c < K \<and> p c x = y} = 1"
      using p unfolding edge_cover_def by blast+
    have Flt: "x < y" "y < n" "A $$ (x, y) \<noteq> 0" if "(x, y) \<in> F" for x y
      using that FE by (auto simp: edges_def)
    have used: "card {c. c < K \<and> p c z \<noteq> z} \<le> s - 1" if z: "z = a \<or> z = b" for z
    proof -
      define w where "w = (if z = a then b else a)"
      have zn: "z < n" using z ab by auto
      have wz: "w \<in> nbrs n A z"
        using z ab sym[of a b] unfolding w_def nbrs_def by auto
      let ?C = "{c. c < K \<and> p c z \<noteq> z}"
      have img: "(\<lambda>c. p c z) ` ?C \<subseteq> nbrs n A z - {w}"
      proof
        fix y assume "y \<in> (\<lambda>c. p c z) ` ?C"
        then obtain c where c: "c < K" "p c z \<noteq> z" "y = p c z" by auto
        have m: "(min z y, max z y) \<in> F" using pcov[OF c(1,2)] c(3) by simp
        have yn: "y < n" using Flt(2)[OF m] zn by (auto simp: min_def max_def split: if_splits)
        have nz: "A $$ (z, y) \<noteq> 0"
          using Flt(3)[OF m] sym[OF zn yn] by (auto simp: min_def max_def split: if_splits)
        have "y \<noteq> w"
        proof
          assume "y = w"
          hence "(min z y, max z y) = (a, b)" using z ab(1) unfolding w_def by auto
          thus False using m eF by simp
        qed
        thus "y \<in> nbrs n A z - {w}" using yn nz c by (auto simp: nbrs_def)
      qed
      have inj: "inj_on (\<lambda>c. p c z) ?C"
      proof (rule inj_onI)
        fix c c' assume c: "c \<in> ?C" and c': "c' \<in> ?C" and eq: "p c z = p c' z"
        define y where "y = p c z"
        have m: "(min z y, max z y) \<in> F" using pcov c unfolding y_def by auto
        have mem: "d \<in> {c. c < K \<and> p c (min z y) = max z y}" if d: "d < K" "p d z = y" for d
        proof -
          have "p d y = z" using invol_eq[OF pinv[OF d(1)]] d(2) by blast
          thus ?thesis using d by (auto simp: min_def max_def)
        qed
        have "card {c. c < K \<and> p c (min z y) = max z y} = 1" by (rule pone[OF m])
        then obtain d where "{c. c < K \<and> p c (min z y) = max z y} = {d}" by (rule card_1_singletonE)
        thus "c = c'" using mem[of c] mem[of c'] c c' eq unfolding y_def by auto
      qed
      have "card ?C = card ((\<lambda>c. p c z) ` ?C)" by (rule card_image[OF inj, symmetric])
      also have "\<dots> \<le> card (nbrs n A z - {w})"
        by (rule card_mono[OF _ img]) (simp add: nbrs_def)
      also have "\<dots> = card (nbrs n A z) - 1" using wz by (simp add: nbrs_def)
      also have "\<dots> \<le> s - 1" using sp zn unfolding sparse_def by (simp add: diff_le_mono)
      finally show ?thesis .
    qed
    have s1: "1 \<le> s"
    proof -
      have "b \<in> nbrs n A a" using ab by (simp add: nbrs_def)
      hence "0 < card (nbrs n A a)" by (auto simp: nbrs_def card_gt_0_iff)
      thus ?thesis using sp ab unfolding sparse_def by (metis le_trans less_one not_le order.strict_trans)
    qed
    let ?Ca = "{c. c < K \<and> p c a \<noteq> a}" and ?Cb = "{c. c < K \<and> p c b \<noteq> b}"
    have "card (?Ca \<union> ?Cb) \<le> card ?Ca + card ?Cb" by (rule card_Un_le)
    also have "\<dots> \<le> (s - 1) + (s - 1)" using used[of a] used[of b] by simp
    also have "\<dots> < K" using K s1 by simp
    finally have lt: "card (?Ca \<union> ?Cb) < K" .
    obtain c where c: "c < K" "p c a = a" "p c b = b"
    proof -
      have "\<not> {..<K} \<subseteq> ?Ca \<union> ?Cb"
      proof
        assume "{..<K} \<subseteq> ?Ca \<union> ?Cb"
        hence "card {..<K} \<le> card (?Ca \<union> ?Cb)" by (rule card_mono[rotated]) simp
        thus False using lt by simp
      qed
      then obtain c where "c < K" "c \<notin> ?Ca \<union> ?Cb" by auto
      thus ?thesis using that by auto
    qed
    have nab: "p c x \<noteq> a" "p c x \<noteq> b" if "x \<noteq> a" "x \<noteq> b" for x
      using that c invol_eq[OF pinv[OF c(1)]] by metis+
    define p' where "p' = p(c := (p c)(a := b, b := a))"
    have p'c: "p' c = ((p c)(a := b, b := a))" and p'o: "\<And>d. d \<noteq> c \<Longrightarrow> p' d = p d" unfolding p'_def by simp_all
    have inv': "invol n (p' d)" if d: "d < K" for d
    proof (cases "d = c")
      case True
      have "\<forall>x. ((p c)(a := b, b := a)) (((p c)(a := b, b := a)) x) = x"
        using c nab invol_eq[OF pinv[OF c(1)]] ab by auto
      moreover have "\<forall>x. n \<le> x \<longrightarrow> ((p c)(a := b, b := a)) x = x"
        using ab pinv[OF c(1)] by (auto simp: invol_def)
      ultimately show ?thesis using True p'c unfolding invol_def by simp
    next
      case False
      thus ?thesis using p'o pinv d by simp
    qed
    have cov': "(min x (p' d x), max x (p' d x)) \<in> insert e F" if d: "d < K" and x: "p' d x \<noteq> x" for d x
    proof (cases "d = c")
      case True
      show ?thesis
      proof (cases "x = a \<or> x = b")
        case True
        thus ?thesis using \<open>d = c\<close> p'c e ab(1) by auto
      next
        case False
        hence "p' d x = p c x" using \<open>d = c\<close> p'c by auto
        thus ?thesis using pcov[OF c(1)] x by simp
      qed
    next
      case False
      thus ?thesis using p'o pcov d x by simp
    qed
    have one': "card {d. d < K \<and> p' d x = y} = 1" if xy: "(x, y) \<in> insert e F" for x y
    proof (cases "(x, y) = (a, b)")
      case True
      have "{d. d < K \<and> p' d x = y} = {c}"
      proof (rule equalityI)
        show "{d. d < K \<and> p' d x = y} \<subseteq> {c}"
        proof
          fix d assume "d \<in> {d. d < K \<and> p' d x = y}"
          hence d: "d < K" "p' d a = b" using True by auto
          show "d \<in> {c}"
          proof (rule ccontr)
            assume "d \<notin> {c}"
            hence "p d a = b" using d p'o by simp
            moreover have "p d a \<noteq> a" using \<open>p d a = b\<close> ab(1) by simp
            ultimately have "(min a (p d a), max a (p d a)) \<in> F" using pcov[OF d(1)] by blast
            thus False using eF \<open>p d a = b\<close> ab(1) by simp
          qed
        qed
        show "{c} \<subseteq> {d. d < K \<and> p' d x = y}" using True c p'c by auto
      qed
      thus ?thesis by simp
    next
      case False
      hence xyF: "(x, y) \<in> F" using xy e by blast
      have "{d. d < K \<and> p' d x = y} = {d. d < K \<and> p d x = y}"
      proof (rule Set.set_eqI)
        fix d
        show "d \<in> {d. d < K \<and> p' d x = y} \<longleftrightarrow> d \<in> {d. d < K \<and> p d x = y}"
        proof (cases "d = c")
          case True
          have "p' c x = y \<longleftrightarrow> p c x = y"
          proof (cases "x = a \<or> x = b")
            case True
            have "x < y" using Flt(1)[OF xyF] .
            hence "\<not> p' c x = y" "\<not> p c x = y" using True c p'c ab(1) xyF eF by auto
            thus ?thesis by simp
          next
            case False
            thus ?thesis using p'c by auto
          qed
          thus ?thesis using True by simp
        next
          case False
          thus ?thesis using p'o by simp
        qed
      qed
      thus ?thesis using pone[OF xyF] by simp
    qed
    have "edge_cover n K p' (insert e F)" unfolding edge_cover_def using inv' cov' one' by blast
    thus ?case by blast
  qed
qed

subsection \<open>1-sparse matrices\<close>

text \<open>\<open>one_sparse n q h\<close> has the single entry $h(i)$ in row $i$, column $q(i)$.\<close>

definition one_sparse :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> complex Matrix.mat" where
  "one_sparse n q h = Matrix.mat n n (\<lambda>(i, j). if j = q i then h i else 0)"

lemma one_sparse_carrier [simp]: "one_sparse n q h \<in> carrier_mat n n"
  by (simp add: one_sparse_def)

lemma one_sparse_index:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> one_sparse n q h $$ (i, j) = (if j = q i then h i else 0)"
  by (simp add: one_sparse_def)

lemma one_sparse_mult_vec:
  assumes q: "invol n q" and v: "dim_vec v = n"
  shows "one_sparse n q h *\<^sub>v v = Matrix.vec n (\<lambda>i. h i * v $ q i)"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (Matrix.vec n (\<lambda>i. h i * v $ q i))"
  hence i: "i < n" by simp
  have "(one_sparse n q h *\<^sub>v v) $ i = (\<Sum>j = 0..<n. (if j = q i then h i else 0) * v $ j)"
    using i v by (simp add: one_sparse_def mult_mat_vec_def scalar_prod_def)
  also have "\<dots> = (\<Sum>j = 0..<n. if j = q i then h i * v $ j else 0)" by (rule sum.cong) auto
  also have "\<dots> = h i * v $ q i" using invol_lt[OF q i] by simp
  finally show "(one_sparse n q h *\<^sub>v v) $ i = Matrix.vec n (\<lambda>i. h i * v $ q i) $ i" using i by simp
qed (simp add: one_sparse_def)

lemma invol_bij: "invol n q \<Longrightarrow> bij_betw q {..<n} {..<n}"
  by (rule bij_betwI[where g = q]) (auto simp: invol_lt, auto simp: invol_def)

lemma one_sparse_bound:
  assumes q: "invol n q" and L: "0 \<le> L" and h: "\<And>i. i < n \<Longrightarrow> cmod (h i) \<le> L" and v: "dim_vec v = n"
  shows "\<parallel>one_sparse n q h *\<^sub>v v\<parallel> \<le> L * \<parallel>v\<parallel>"
proof -
  have "\<parallel>one_sparse n q h *\<^sub>v v\<parallel>\<^sup>2 = (\<Sum>i<n. (cmod (h i * v $ q i))\<^sup>2)"
    unfolding one_sparse_mult_vec[OF q v] vnorm_sq by simp
  also have "\<dots> \<le> (\<Sum>i<n. L\<^sup>2 * (cmod (v $ q i))\<^sup>2)"
  proof (rule sum_mono)
    fix i assume "i \<in> {..<n}"
    hence "(cmod (h i))\<^sup>2 \<le> L\<^sup>2" using h by (intro power_mono) simp_all
    thus "(cmod (h i * v $ q i))\<^sup>2 \<le> L\<^sup>2 * (cmod (v $ q i))\<^sup>2"
      by (simp add: norm_mult power_mult_distrib mult_right_mono)
  qed
  also have "\<dots> = L\<^sup>2 * (\<Sum>i<n. (cmod (v $ q i))\<^sup>2)" by (simp add: sum_distrib_left)
  also have "(\<Sum>i<n. (cmod (v $ q i))\<^sup>2) = (\<Sum>i<n. (cmod (v $ i))\<^sup>2)"
    by (rule sum.reindex_bij_betw[OF invol_bij[OF q]])
  also have "L\<^sup>2 * \<dots> = (L * \<parallel>v\<parallel>)\<^sup>2" by (simp add: vnorm_sq v power_mult_distrib)
  finally show ?thesis by (rule power2_le_imp_le) (simp add: L vnorm_ge0)
qed

subsection \<open>The parts\<close>

definition colour_part :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "colour_part n A q = one_sparse n q (\<lambda>i. if q i = i then 0 else A $$ (i, q i))"

definition diag_part :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "diag_part n A = one_sparse n (\<lambda>i. i) (\<lambda>i. A $$ (i, i))"

definition sparse_parts :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat list" where
  "sparse_parts n A K p = diag_part n A # map (\<lambda>c. colour_part n A (p c)) [0..<K]"

lemma invol_id: "invol n (\<lambda>i. i)"
  by (simp add: invol_def)

lemma colour_part_hermitian:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and q: "invol n q"
  shows "hermitian (colour_part n A q)"
  unfolding hermitian_dagger
proof (rule eq_matI)
  fix i j assume i: "i < dim_row (colour_part n A q)" and j: "j < dim_col (colour_part n A q)"
  hence i: "i < n" and j: "j < n" by (simp_all add: colour_part_def one_sparse_def)
  have e: "i = q j \<longleftrightarrow> j = q i" using invol_eq[OF q] by metis
  show "(colour_part n A q)\<^sup>\<dagger> $$ (i, j) = colour_part n A q $$ (i, j)"
    using i j e hermitian_index_cnj[OF A(2), of i j] carrier_matD[OF A(1)]
    by (auto simp: dagger_def colour_part_def one_sparse_def)
qed (simp_all add: dagger_def colour_part_def one_sparse_def)

lemma diag_part_hermitian:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "hermitian (diag_part n A)"
  unfolding hermitian_dagger
proof (rule eq_matI)
  fix i j assume i: "i < dim_row (diag_part n A)" and j: "j < dim_col (diag_part n A)"
  hence i: "i < n" and j: "j < n" by (simp_all add: diag_part_def one_sparse_def)
  show "(diag_part n A)\<^sup>\<dagger> $$ (i, j) = diag_part n A $$ (i, j)"
    using i j hermitian_index_cnj[OF A(2), of i i] carrier_matD[OF A(1)] by (auto simp: dagger_def diag_part_def one_sparse_def)
qed (simp_all add: dagger_def diag_part_def one_sparse_def)

lemma sparse_parts_bounded:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and p: "\<And>c. c < K \<Longrightarrow> invol n (p c)"
      and L: "0 \<le> L" and Lb: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (A $$ (i, j)) \<le> L"
  shows "\<And>H. H \<in> set (sparse_parts n A K p) \<Longrightarrow> herm_bounded n L H"
proof -
  fix H assume "H \<in> set (sparse_parts n A K p)"
  hence "H = diag_part n A \<or> (\<exists>c<K. H = colour_part n A (p c))" by (auto simp: sparse_parts_def)
  thus "herm_bounded n L H"
  proof
    assume H: "H = diag_part n A"
    show ?thesis unfolding herm_bounded_def H
      using diag_part_hermitian[OF A] one_sparse_bound[OF invol_id L] Lb by (simp add: diag_part_def)
  next
    assume "\<exists>c<K. H = colour_part n A (p c)"
    then obtain c where c: "c < K" and H: "H = colour_part n A (p c)" by blast
    have hb: "cmod (if p c i = i then 0 else A $$ (i, p c i)) \<le> L" if "i < n" for i
      using Lb[OF that invol_lt[OF p[OF c] that]] L by simp
    show ?thesis unfolding herm_bounded_def H
      using colour_part_hermitian[OF A p[OF c]] one_sparse_bound[OF p[OF c] L] hb by (simp add: colour_part_def)
  qed
qed

lemma hamiltonian_sum_index:
  "(\<And>H. H \<in> set Hs \<Longrightarrow> H \<in> carrier_mat n n) \<Longrightarrow> i < n \<Longrightarrow> j < n \<Longrightarrow>
   hamiltonian_sum n Hs $$ (i, j) = (\<Sum>H\<leftarrow>Hs. H $$ (i, j))"
proof (induction Hs)
  case (Cons H Hs)
  have "H \<in> carrier_mat n n" "hamiltonian_sum n Hs \<in> carrier_mat n n"
    using Cons.prems(1) hamiltonian_sum_carrier[of Hs n] by auto
  thus ?case using Cons by simp
qed simp

text \<open>The diagonal and the colour classes add up to $A$: each nonzero off-diagonal entry lies in
exactly one class.\<close>

lemma sparse_parts_sum:
  assumes A: "A \<in> carrier_mat n n"
      and sym: "\<And>x y. x < n \<Longrightarrow> y < n \<Longrightarrow> A $$ (x, y) = 0 \<longleftrightarrow> A $$ (y, x) = 0"
      and cov: "edge_cover n K p (edges n A)"
  shows "hamiltonian_sum n (sparse_parts n A K p) = A"
proof (rule eq_matI)
  have pinv: "\<And>c. c < K \<Longrightarrow> invol n (p c)"
    and pone: "\<And>x y. (x, y) \<in> edges n A \<Longrightarrow> card {c. c < K \<and> p c x = y} = 1"
    using cov unfolding edge_cover_def by blast+
  have carr: "\<And>H. H \<in> set (sparse_parts n A K p) \<Longrightarrow> H \<in> carrier_mat n n"
    by (auto simp: sparse_parts_def colour_part_def diag_part_def)
  have S: "hamiltonian_sum n (sparse_parts n A K p) \<in> carrier_mat n n" by (rule hamiltonian_sum_carrier[OF carr])
  show "dim_row (hamiltonian_sum n (sparse_parts n A K p)) = dim_row A" "dim_col (hamiltonian_sum n (sparse_parts n A K p)) = dim_col A"
    using S A by simp_all
  fix i j assume i: "i < dim_row A" and j: "j < dim_col A"
  hence i: "i < n" and j: "j < n" using A by auto
  have "hamiltonian_sum n (sparse_parts n A K p) $$ (i, j) = (\<Sum>H\<leftarrow>sparse_parts n A K p. H $$ (i, j))"
    by (rule hamiltonian_sum_index) (use carr i j in auto)
  also have "\<dots> = diag_part n A $$ (i, j) + (\<Sum>c\<leftarrow>[0..<K]. colour_part n A (p c) $$ (i, j))"
    by (simp add: sparse_parts_def o_def)
  also have "(\<Sum>c\<leftarrow>[0..<K]. colour_part n A (p c) $$ (i, j)) = (\<Sum>c\<in>{0..<K}. colour_part n A (p c) $$ (i, j))"
    using sum_set_upt_conv_sum_list_nat[of "\<lambda>c. colour_part n A (p c) $$ (i, j)" 0 K] by simp
  also have "\<dots> = (\<Sum>c\<in>{0..<K}. if p c i = j \<and> i \<noteq> j then A $$ (i, j) else 0)"
    by (rule sum.cong) (auto simp: colour_part_def one_sparse_index i j)
  also have "\<dots> = (\<Sum>c\<in>{c \<in> {0..<K}. p c i = j \<and> i \<noteq> j}. A $$ (i, j))"
    by (rule sum.inter_filter[symmetric]) simp
  also have "\<dots> = of_nat (card {c \<in> {0..<K}. p c i = j \<and> i \<noteq> j}) * A $$ (i, j)" by simp
  finally have e: "hamiltonian_sum n (sparse_parts n A K p) $$ (i, j) =
      diag_part n A $$ (i, j) + of_nat (card {c \<in> {0..<K}. p c i = j \<and> i \<noteq> j}) * A $$ (i, j)" .
  show "hamiltonian_sum n (sparse_parts n A K p) $$ (i, j) = A $$ (i, j)"
  proof (cases "i = j")
    case True
    thus ?thesis unfolding e using i by (simp add: diag_part_def one_sparse_index)
  next
    case False
    have d: "diag_part n A $$ (i, j) = 0" using False i j by (simp add: diag_part_def one_sparse_index)
    show ?thesis
    proof (cases "A $$ (i, j) = 0")
      case True
      thus ?thesis unfolding e d by simp
    next
      case nz: False
      define x where "x = min i j"
      define y where "y = max i j"
      have xy: "(x, y) \<in> edges n A"
        using False nz sym[OF i j] i j unfolding x_def y_def edges_def by (auto simp: min_def max_def)
      have "{c \<in> {0..<K}. p c i = j \<and> i \<noteq> j} = {c. c < K \<and> p c x = y}"
      proof (rule Set.set_eqI)
        fix c
        show "c \<in> {c \<in> {0..<K}. p c i = j \<and> i \<noteq> j} \<longleftrightarrow> c \<in> {c. c < K \<and> p c x = y}"
        proof (cases "c < K")
          case True
          have "p c i = j \<longleftrightarrow> p c j = i" by (rule invol_eq[OF pinv[OF True]])
          thus ?thesis using True False unfolding x_def y_def by (auto simp: min_def max_def)
        qed simp
      qed
      hence "card {c \<in> {0..<K}. p c i = j \<and> i \<noteq> j} = 1" using pone[OF xy] by simp
      thus ?thesis unfolding e d by simp
    qed
  qed
qed

lemma hermitian_zero_sym:
  fixes A :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "\<And>x y. x < n \<Longrightarrow> y < n \<Longrightarrow> A $$ (x, y) = 0 \<longleftrightarrow> A $$ (y, x) = 0"
  using hermitian_index_cnj[OF A(2)] carrier_matD[OF A(1)] by (metis complex_cnj_zero_iff)

text \<open>Every $s$-sparse Hermitian matrix is the sum of its diagonal and $2s-1$ Hermitian
1-sparse matrices.\<close>

theorem sparse_split:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and sp: "sparse n s A" and s: "1 \<le> s"
  shows "\<exists>p. edge_cover n (2 * s - 1) p (edges n A) \<and>
           length (sparse_parts n A (2 * s - 1) p) = 2 * s \<and> hamiltonian_sum n (sparse_parts n A (2 * s - 1) p) = A"
proof -
  obtain p where p: "edge_cover n (2 * s - 1) p (edges n A)"
    using greedy_cover[OF hermitian_zero_sym[OF A] sp _ subset_refl] s by force
  have "length (sparse_parts n A (2 * s - 1) p) = 2 * s" using s by (simp add: sparse_parts_def)
  thus ?thesis using p sparse_parts_sum[OF A(1) hermitian_zero_sym[OF A] p] by blast
qed

text \<open>Trotter for a sparse matrix: $r$ rounds of the $2s$ part evolutions approximate
$e^{itA}$ within $8(sLt)^2/r$, where $L$ bounds the entries of $A$.\<close>

theorem sparse_trotter:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and s: "1 \<le> s"
      and L: "0 \<le> L" and Lb: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (A $$ (i, j)) \<le> L"
      and cov: "edge_cover n (2 * s - 1) p (edges n A)" and r: "0 < r"
  shows "op_close n (8 * (real s * L * t)\<^sup>2 / real r)
           (evolution_product n (t / real r) (sparse_parts n A (2 * s - 1) p) ^\<^sub>m r) (evolution A t)"
proof -
  have pinv: "\<And>c. c < 2 * s - 1 \<Longrightarrow> invol n (p c)" using cov unfolding edge_cover_def by blast
  have len: "length (sparse_parts n A (2 * s - 1) p) = 2 * s" using s by (simp add: sparse_parts_def)
  have sum: "hamiltonian_sum n (sparse_parts n A (2 * s - 1) p) = A"
    by (rule sparse_parts_sum[OF A(1) hermitian_zero_sym[OF A] cov])
  have c: "op_close n (2 * (real (length (sparse_parts n A (2 * s - 1) p)) * L * t)\<^sup>2 / real r)
      (evolution_product n (t / real r) (sparse_parts n A (2 * s - 1) p) ^\<^sub>m r) (evolution (hamiltonian_sum n (sparse_parts n A (2 * s - 1) p)) t)"
    by (rule trotter[OF sparse_parts_bounded[OF A pinv L Lb] r])
  have e: "2 * (real (2 * s) * L * t)\<^sup>2 / real r = 8 * (real s * L * t)\<^sup>2 / real r"
    by (simp add: power2_eq_square algebra_simps)
  show ?thesis using c unfolding len sum e .
qed

end
