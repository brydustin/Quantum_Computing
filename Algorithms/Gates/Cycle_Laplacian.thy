theory Cycle_Laplacian
  imports Prep_Sparse Incrementer
begin

section \<open>The cycle Laplacian without oracles\<close>

text \<open>For the Laplacian of the $n$-cycle every black box of the sparse simulation is a small
circuit: the two edge colours are $x \mapsto x \oplus 1$ and its conjugate by the incrementer, and
all entries are constant.\<close>

subsection \<open>The matrix and its edge colouring\<close>

definition cyc_adj :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cyc_adj n i j \<longleftrightarrow> j = i + 1 \<or> i = j + 1 \<or> (i = 0 \<and> j = n - 1) \<or> (j = 0 \<and> i = n - 1)"

definition lap :: "nat \<Rightarrow> complex Matrix.mat" where
  "lap n = Matrix.mat n n (\<lambda>(i, j). if i = j then 2 else if cyc_adj n i j then - 1 else 0)"

text \<open>Colour $0$ pairs $2k$ with $2k+1$; colour $1$ pairs $2k+1$ with $2k+2$, cyclically.\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{tikzpicture}[scale=1.3]
  \foreach \i in {0,...,7} { \node[circle,draw,fill=white,inner sep=1.5pt,minimum size=17pt] (v\i) at ({90-45*\i}:1.4) {\small $\i$}; }
  \foreach \i/\j in {0/1,2/3,4/5,6/7} { \draw[very thick, blue!70!black] (v\i) -- (v\j); }
  \foreach \i/\j in {1/2,3/4,5/6,7/0} { \draw[very thick, orange!85!black, dashed] (v\i) -- (v\j); }
  \node[anchor=west] at (2.0,0.45) {\textcolor{blue!70!black}{\rule[0.5ex]{1.2em}{1.2pt}}\; colour $0$: $2k \leftrightarrow 2k+1$};
  \node[anchor=west] at (2.0,-0.05) {\textcolor{orange!85!black}{- - -}\; colour $1$: $2k+1 \leftrightarrow 2k+2$};
  \node[anchor=west] at (2.0,-0.55) {$L = 2I - \text{adjacency}$, here $n = 8$};
\end{tikzpicture}
\end{center}
\<close>

definition lp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lp n c x = (if n \<le> x then x else if c = 0 then (if even x then x + 1 else x - 1)
     else if even x then (if x = 0 then n - 1 else x - 1) else (if x + 1 = n then 0 else x + 1))"

lemma lap_carrier [simp]: "lap n \<in> carrier_mat n n" by (simp add: lap_def)

lemma cyc_adj_sym: "cyc_adj n i j \<longleftrightarrow> cyc_adj n j i" by (auto simp: cyc_adj_def)

lemma lap_hermitian: "hermitian (lap n)"
  unfolding hermitian_dagger
proof (rule eq_matI)
  fix i j assume "i < dim_row (lap n)" "j < dim_col (lap n)"
  hence i: "i < n" and j: "j < n" by (simp_all add: lap_def)
  show "(lap n)\<^sup>\<dagger> $$ (i, j) = lap n $$ (i, j)" using i j cyc_adj_sym[of n i j] by (simp add: dagger_def lap_def)
qed (simp_all add: dagger_def lap_def)

lemma lap_bound: "i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (lap n $$ (i, j)) \<le> 2"
  by (simp add: lap_def)

lemma lap_sym: "x < n \<Longrightarrow> y < n \<Longrightarrow> lap n $$ (x, y) = 0 \<longleftrightarrow> lap n $$ (y, x) = 0"
  using cyc_adj_sym[of n x y] by (simp add: lap_def)

lemma lp_invol:
  assumes n: "even n"
  shows "invol n (lp n c)"
  unfolding invol_def
proof (intro conjI allI impI)
  fix x
  have n1: "odd (n - 1)" if "0 < n" using n that by simp
  show "lp n c (lp n c x) = x"
  proof (cases "n \<le> x")
    case True thus ?thesis by (simp add: lp_def)
  next
    case False
    hence x: "x < n" by simp
    have "even x \<Longrightarrow> x + 1 < n" using n x by (cases "x + 1 = n") auto
    thus ?thesis using x n n1 by (cases "c = 0"; cases "even x") (auto simp: lp_def)
  qed
  show "n \<le> x \<Longrightarrow> lp n c x = x" for x by (simp add: lp_def)
qed

lemma lap_edges: "edges n (lap n) = {(x, y). x < y \<and> y < n \<and> cyc_adj n x y}"
  by (auto simp: edges_def lap_def split: if_splits)

lemma lp_edge:
  assumes n: "even n" "4 \<le> n" and ne: "lp n c x \<noteq> x"
  shows "min x (lp n c x) < max x (lp n c x) \<and> max x (lp n c x) < n \<and> cyc_adj n (min x (lp n c x)) (max x (lp n c x))"
proof -
  have x: "x < n" using ne by (cases "n \<le> x") (auto simp: lp_def)
  have e1: "even x \<Longrightarrow> x + 1 < n" using n x by (cases "x + 1 = n") auto
  have o1: "odd x \<Longrightarrow> 1 \<le> x" by (cases x) auto
  show ?thesis using x e1 o1 n by (cases "c = 0"; cases "even x") (auto simp: lp_def cyc_adj_def)
qed

lemma lp_unique:
  assumes n: "even n" "4 \<le> n" and xy: "x < y" "y < n" "cyc_adj n x y"
  shows "card {c. c < 2 \<and> lp n c x = y} = 1"
proof -
  define c0 where "c0 = (if x = 0 \<and> y = n - 1 then 1 else if even x then 0 else (1::nat))"
  have "lp n c x = y \<longleftrightarrow> c = c0" if "c < 2" for c
    using that xy n by (cases "c = 0") (auto simp: c0_def lp_def cyc_adj_def)
  moreover have "c0 < 2" by (simp add: c0_def)
  ultimately have "{c. c < 2 \<and> lp n c x = y} = {c0}" by blast
  thus ?thesis by simp
qed

lemma lp_cover:
  assumes n: "even n" "4 \<le> n"
  shows "edge_cover n 2 (lp n) (edges n (lap n))"
proof -
  have A: "\<forall>c<2. invol n (lp n c)" using lp_invol[OF n(1)] by blast
  have B: "\<forall>c<2. \<forall>x. lp n c x \<noteq> x \<longrightarrow> (min x (lp n c x), max x (lp n c x)) \<in> edges n (lap n)"
    using lp_edge[OF n] by (auto simp: lap_edges)
  have C: "\<forall>x y. (x, y) \<in> edges n (lap n) \<longrightarrow> card {c. c < 2 \<and> lp n c x = y} = 1"
    using lp_unique[OF n] by (auto simp: lap_edges)
  show ?thesis unfolding edge_cover_def using A B C by blast
qed

text \<open>Three parts (diagonal, two colours), entries bounded by $2$: the Trotter error is $72t^2/r$.\<close>

theorem lap_trotter:
  assumes n: "even n" "4 \<le> n" and r: "0 < r"
  shows "evolution_product n (t / real r) (sparse_parts n (lap n) 2 (lp n)) ^\<^sub>m r \<approx>\<^bsub>72 * t\<^sup>2 / real r\<^esub> evolution (lap n) t"
proof -
  have pinv: "\<And>c. c < 2 \<Longrightarrow> invol n (lp n c)" using lp_invol[OF n(1)] by blast
  have L2: "0 \<le> (2::real)" by simp
  have len: "length (sparse_parts n (lap n) 2 (lp n)) = 3" by (simp add: sparse_parts_def)
  have sum: "hamiltonian_sum n (sparse_parts n (lap n) 2 (lp n)) = lap n"
    by (rule sparse_parts_sum[OF lap_carrier lap_sym lp_cover[OF n]])
  have c: "evolution_product n (t / real r) (sparse_parts n (lap n) 2 (lp n)) ^\<^sub>m r
      \<approx>\<^bsub>2 * (real (length (sparse_parts n (lap n) 2 (lp n))) * 2 * t)\<^sup>2 / real r\<^esub>
      evolution (hamiltonian_sum n (sparse_parts n (lap n) 2 (lp n))) t"
    by (rule trotter[OF sparse_parts_bounded[OF lap_carrier lap_hermitian pinv L2 lap_bound] r])
  have e: "2 * (real 3 * 2 * t)\<^sup>2 / real r = 72 * t\<^sup>2 / real r" by (simp add: power2_eq_square algebra_simps)
  show ?thesis using c unfolding len sum e .
qed

subsection \<open>The parts as one-qubit gates\<close>

lemma qw_carrier:
  assumes G: "G \<in> carrier_mat 2 2" and w: "w < K"
  shows "qw K w G \<in> carrier_mat (2 ^ K) (2 ^ K)"
proof -
  have "(2::nat) ^ (K - Suc w) * (2 * 2 ^ w) = 2 ^ (K - Suc w + Suc w)" by (simp add: power_add)
  also have "K - Suc w + Suc w = K" using w by simp
  finally have e: "(2::nat) ^ (K - Suc w) * (2 * 2 ^ w) = 2 ^ K" .
  show ?thesis unfolding qw_def e[symmetric] using G by simp
qed

lemma qw0_index:
  assumes m: "0 < m" and G: "G \<in> carrier_mat 2 2" and r: "r < 2 ^ m" and c: "c < 2 ^ m"
  shows "qw m 0 G $$ (r, c) = (if r div 2 = c div 2 then G $$ (r mod 2, c mod 2) else 0)"
proof -
  have e: "qw m 0 G = 1\<^sub>m (2 ^ (m - 1)) \<Otimes> G" unfolding qw_def by (simp add: right_tensor_id[OF G, unfolded One_nat_def])
  have N: "(2::nat) ^ m = 2 ^ (m - 1) * 2" using m by (simp flip: power_Suc2)
  have rc: "r < 2 ^ (m - 1) * 2" "c < 2 ^ (m - 1) * 2" using r c N by simp_all
  have d: "r div 2 < 2 ^ (m - 1)" "c div 2 < 2 ^ (m - 1)" using rc by (simp_all add: div_less_iff_less_mult)
  show ?thesis unfolding e
    using index_tensor_mat[of "1\<^sub>m (2 ^ (m - 1))" "2 ^ (m - 1)" "2 ^ (m - 1)" G 2 2 r c] rc d G by auto
qed

lemma lp0_iff:
  assumes n: "even n" and r: "r < n" and c: "c < n"
  shows "r = lp n 0 c \<longleftrightarrow> r div 2 = c div 2 \<and> r \<noteq> c"
proof (cases "even c")
  case True
  hence "lp n 0 c = c + 1" using c by (simp add: lp_def)
  thus ?thesis using True by presburger
next
  case False
  hence "lp n 0 c = c - 1" using c by (simp add: lp_def)
  thus ?thesis using False by presburger
qed

lemma lp_moves:
  assumes n: "even n" "4 \<le> n" and x: "x < n"
  shows "lp n c x \<noteq> x"
proof -
  have "even x \<Longrightarrow> x + 1 < n" using n x by (cases "x + 1 = n") auto
  moreover have "odd x \<Longrightarrow> 0 < x" by (cases x) auto
  ultimately show ?thesis using n x by (cases "c = 0"; cases "even x") (auto simp: lp_def)
qed

lemma colour_h_lap:
  assumes n: "even n" "4 \<le> n" and i: "i < n"
  shows "colour_h (lap n) (lp n c) i = - 1"
proof -
  have ne: "lp n c i \<noteq> i" by (rule lp_moves[OF n i])
  have q: "lp n c i < n" by (rule invol_lt[OF lp_invol[OF n(1)] i])
  have "cyc_adj n i (lp n c i)"
  proof (cases "i < lp n c i")
    case True thus ?thesis using lp_edge[OF n ne] by (simp add: min_def max_def)
  next
    case False
    hence "lp n c i < i" using ne by simp
    thus ?thesis using lp_edge[OF n ne] cyc_adj_sym[of n "lp n c i" i] by (simp add: min_def max_def)
  qed
  thus ?thesis using ne q i by (simp add: colour_h_def lap_def)
qed

lemma pair_evo_const:
  assumes q: "invol n q" and h: "\<And>i. i < n \<Longrightarrow> h i = - 1"
  shows "pair_evo n q h d = complex_of_real (cos d) \<cdot>\<^sub>m 1\<^sub>m n + (- \<i> * complex_of_real (sin d)) \<cdot>\<^sub>m pmat n q"
proof (rule eq_matI)
  fix i j assume "i < dim_row (complex_of_real (cos d) \<cdot>\<^sub>m 1\<^sub>m n + (- \<i> * complex_of_real (sin d)) \<cdot>\<^sub>m pmat n q)"
    "j < dim_col (complex_of_real (cos d) \<cdot>\<^sub>m 1\<^sub>m n + (- \<i> * complex_of_real (sin d)) \<cdot>\<^sub>m pmat n q)"
  hence i: "i < n" and j: "j < n" by (simp_all add: pmat_def)
  have e: "i = q j \<longleftrightarrow> j = q i" using invol_eq[OF q, of j i] by auto
  show "pair_evo n q h d $$ (i, j)
      = (complex_of_real (cos d) \<cdot>\<^sub>m 1\<^sub>m n + (- \<i> * complex_of_real (sin d)) \<cdot>\<^sub>m pmat n q) $$ (i, j)"
    using i j e h[OF i] by (auto simp: pair_evo_def one_sparse_def pmat_def)
qed (simp_all add: pair_evo_def one_sparse_def pmat_def)

lemma div2_eq: "r = c \<longleftrightarrow> r div 2 = c div 2 \<and> r mod 2 = (c :: nat) mod 2"
proof
  assume e: "r div 2 = c div 2 \<and> r mod 2 = c mod 2"
  have "r = r div 2 * 2 + r mod 2" by simp
  also have "\<dots> = c div 2 * 2 + c mod 2" using e by simp
  also have "\<dots> = c" by simp
  finally show "r = c" .
qed simp

definition xrot :: "real \<Rightarrow> complex Matrix.mat" where
  "xrot d = Matrix.mat 2 2 (\<lambda>(r, c). if r = c then complex_of_real (cos d) else - \<i> * complex_of_real (sin d))"

lemma xrot_carrier [simp]: "xrot d \<in> carrier_mat 2 2" by (simp add: xrot_def)

lemma pow_facts:
  assumes m: "2 \<le> m"
  shows "even ((2::nat) ^ m)" "4 \<le> (2::nat) ^ m" "0 < m"
proof -
  show "even ((2::nat) ^ m)" using m by simp
  show "4 \<le> (2::nat) ^ m" using power_increasing[OF m, of "2::nat"] by simp
  show "0 < m" using m by simp
qed

theorem evo_colour0:
  assumes m: "2 \<le> m"
  shows "evolution (colour_part (2 ^ m) (lap (2 ^ m)) (lp (2 ^ m) 0)) d = qw m 0 (xrot d)"
proof -
  let ?n = "2 ^ m :: nat"
  note n = pow_facts[OF m]
  have q: "invol ?n (lp ?n 0)" by (rule lp_invol[OF n(1)])
  have "evolution (colour_part ?n (lap ?n) (lp ?n 0)) d = pair_evo ?n (lp ?n 0) (colour_h (lap ?n) (lp ?n 0)) d"
    by (rule evolution_colour_part[OF lap_carrier lap_hermitian q])
  also have "\<dots> = complex_of_real (cos d) \<cdot>\<^sub>m 1\<^sub>m ?n + (- \<i> * complex_of_real (sin d)) \<cdot>\<^sub>m pmat ?n (lp ?n 0)"
    by (rule pair_evo_const[OF q colour_h_lap[OF n(1,2)]])
  also have "\<dots> = qw m 0 (xrot d)"
  proof (rule eq_matI)
    have qc: "qw m 0 (xrot d) \<in> carrier_mat ?n ?n" by (rule qw_carrier[OF xrot_carrier n(3)])
    fix r c assume "r < dim_row (qw m 0 (xrot d))" "c < dim_col (qw m 0 (xrot d))"
    hence r: "r < ?n" and c: "c < ?n" using qc by auto
    note rc = div2_eq[of r c]
    show "(complex_of_real (cos d) \<cdot>\<^sub>m 1\<^sub>m ?n + (- \<i> * complex_of_real (sin d)) \<cdot>\<^sub>m pmat ?n (lp ?n 0)) $$ (r, c)
        = qw m 0 (xrot d) $$ (r, c)"
      unfolding qw0_index[OF n(3) xrot_carrier r c] using r c lp0_iff[OF n(1) r c] rc
      by (auto simp: pmat_def xrot_def)
  next
    show "dim_row (complex_of_real (cos d) \<cdot>\<^sub>m 1\<^sub>m ?n + (- \<i> * complex_of_real (sin d)) \<cdot>\<^sub>m pmat ?n (lp ?n 0))
        = dim_row (qw m 0 (xrot d))" by (simp add: pmat_def carrier_matD[OF qw_carrier[OF xrot_carrier[of d] n(3)]])
    show "dim_col (complex_of_real (cos d) \<cdot>\<^sub>m 1\<^sub>m ?n + (- \<i> * complex_of_real (sin d)) \<cdot>\<^sub>m pmat ?n (lp ?n 0))
        = dim_col (qw m 0 (xrot d))" by (simp add: pmat_def carrier_matD[OF qw_carrier[OF xrot_carrier[of d] n(3)]])
  qed
  finally show ?thesis .
qed

definition gph :: "real \<Rightarrow> complex Matrix.mat" where "gph d = cis d \<cdot>\<^sub>m 1\<^sub>m 2"

lemma gph_carrier [simp]: "gph d \<in> carrier_mat 2 2" by (simp add: gph_def)

theorem evo_diag:
  assumes m: "2 \<le> m"
  shows "evolution (diag_part (2 ^ m) (lap (2 ^ m))) d = qw m 0 (gph (2 * d))"
proof -
  let ?n = "2 ^ m :: nat"
  note n = pow_facts[OF m]
  have qc: "qw m 0 (gph (2 * d)) \<in> carrier_mat ?n ?n" by (rule qw_carrier[OF gph_carrier n(3)])
  have "evolution (diag_part ?n (lap ?n)) d = dia_evo ?n d (lap ?n)"
    by (rule evolution_diag_part[OF lap_carrier lap_hermitian])
  also have "\<dots> = qw m 0 (gph (2 * d))"
  proof (rule eq_matI)
    fix r c assume "r < dim_row (qw m 0 (gph (2 * d)))" "c < dim_col (qw m 0 (gph (2 * d)))"
    hence r: "r < ?n" and c: "c < ?n" using qc by auto
    note rc = div2_eq[of r c]
    show "dia_evo ?n d (lap ?n) $$ (r, c) = qw m 0 (gph (2 * d)) $$ (r, c)"
      unfolding qw0_index[OF n(3) gph_carrier r c] using r c rc
      by (auto simp: dia_evo_def one_sparse_def lap_def gph_def mult.commute[of d 2])
  qed (use qc in \<open>simp_all add: dia_evo_def one_sparse_def\<close>)
  finally show ?thesis .
qed

subsection \<open>Colour $1$ is colour $0$ conjugated by the incrementer\<close>

definition inc_f :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "inc_f n x = (x + 1) mod n"
definition dec_f :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "dec_f n x = (x + n - 1) mod n"

lemma inc_f_eq: "x < n \<Longrightarrow> inc_f n x = (if x + 1 = n then 0 else x + 1)"
  by (simp add: inc_f_def)

lemma dec_f_eq: "x < n \<Longrightarrow> dec_f n x = (if x = 0 then n - 1 else x - 1)"
  by (cases x) (simp_all add: dec_f_def)

lemma inc_dec_lt: "0 < n \<Longrightarrow> inc_f n x < n" "0 < n \<Longrightarrow> dec_f n x < n"
  by (simp_all add: inc_f_def dec_f_def)

lemma lp1_conj:
  assumes n: "even n" "4 \<le> n" and x: "x < n"
  shows "lp n 1 x = inc_f n (lp n 0 (dec_f n x))"
proof -
  have e1: "even x \<Longrightarrow> x + 1 < n" using n x by (cases "x + 1 = n") auto
  have o1: "odd x \<Longrightarrow> 0 < x" by (cases x) auto
  have n1: "odd (n - 1)" using n by simp
  show ?thesis
  proof (cases "even x")
    case True
    show ?thesis
    proof (cases "x = 0")
      case True
      thus ?thesis using n n1 by (auto simp: dec_f_eq inc_f_eq lp_def)
    next
      case False
      have x2: "2 \<le> x" using False \<open>even x\<close> by (cases x) (auto elim: oddE)
      thus ?thesis using \<open>even x\<close> x by (auto simp: dec_f_eq inc_f_eq lp_def)
    qed
  next
    case False
    thus ?thesis using x o1 n(1) by (auto simp: dec_f_eq inc_f_eq lp_def)
  qed
qed

lemma lp1_pmat:
  assumes n: "even n" "4 \<le> n"
  shows "pmat n (lp n 1) = pmat n (inc_f n) * pmat n (lp n 0) * pmat n (dec_f n)"
proof -
  have n0: "0 < n" using n by simp
  have l0: "\<And>t. t < n \<Longrightarrow> lp n 0 t < n" by (rule invol_lt[OF lp_invol[OF n(1)]])
  have "pmat n (inc_f n) * pmat n (lp n 0) * pmat n (dec_f n) = pmat n (inc_f n \<circ> lp n 0) * pmat n (dec_f n)"
    by (simp only: pmat_mult[OF l0])
  also have "\<dots> = pmat n (inc_f n \<circ> lp n 0 \<circ> dec_f n)" by (rule pmat_mult) (rule inc_dec_lt(2)[OF n0])
  also have "\<dots> = pmat n (lp n 1)" by (rule pmat_cong) (simp add: lp1_conj[OF n, unfolded One_nat_def])
  finally show ?thesis ..
qed

lemma inc_dec_pmat:
  assumes n0: "0 < n"
  shows "pmat n (inc_f n) * pmat n (dec_f n) = 1\<^sub>m n"
proof -
  have "pmat n (inc_f n) * pmat n (dec_f n) = pmat n (inc_f n \<circ> dec_f n)" by (rule pmat_mult) (rule inc_dec_lt(2)[OF n0])
  also have "\<dots> = pmat n id"
  proof (rule pmat_cong)
    fix t assume t: "t < n"
    show "(inc_f n \<circ> dec_f n) t = id t" using t n0 by (cases t) (simp_all add: inc_f_def dec_f_def)
  qed
  finally show ?thesis by (simp only: pmat_id)
qed

theorem evo_colour1:
  assumes m: "2 \<le> m"
  shows "evolution (colour_part (2 ^ m) (lap (2 ^ m)) (lp (2 ^ m) 1)) d
    = pmat (2 ^ m) (inc_f (2 ^ m)) * qw m 0 (xrot d) * pmat (2 ^ m) (dec_f (2 ^ m))"
proof -
  let ?n = "2 ^ m :: nat" and ?c = "complex_of_real (cos d)" and ?a = "- \<i> * complex_of_real (sin d)"
  let ?P = "pmat ?n (inc_f ?n)" and ?Q = "pmat ?n (dec_f ?n)" and ?Z = "pmat ?n (lp ?n 0)" and ?I = "1\<^sub>m ?n :: complex Matrix.mat"
  note n = pow_facts[OF m]
  have n0: "0 < ?n" by simp
  have q0: "invol ?n (lp ?n 0)" and q1: "invol ?n (lp ?n 1)" by (rule lp_invol[OF n(1)])+
  have E0: "?c \<cdot>\<^sub>m ?I + ?a \<cdot>\<^sub>m ?Z = qw m 0 (xrot d)"
    using evolution_colour_part[OF lap_carrier lap_hermitian q0, where d = d] evo_colour0[OF m, where d = d]
      pair_evo_const[OF q0 colour_h_lap[OF n(1,2)], where d = d] by simp
  have Pc: "?P \<in> carrier_mat ?n ?n" and Qc: "?Q \<in> carrier_mat ?n ?n" and P0c: "?Z \<in> carrier_mat ?n ?n" by simp_all
  have Ic: "?I \<in> carrier_mat ?n ?n" by simp
  have "?P * (?c \<cdot>\<^sub>m ?I + ?a \<cdot>\<^sub>m ?Z) = ?P * (?c \<cdot>\<^sub>m ?I) + ?P * (?a \<cdot>\<^sub>m ?Z)"
    by (rule mult_add_distrib_mat[OF Pc smult_carrier_mat[OF Ic] smult_carrier_mat[OF P0c]])
  also have "\<dots> = ?c \<cdot>\<^sub>m ?P + ?a \<cdot>\<^sub>m (?P * ?Z)"
    by (simp only: mult_smult_distrib[OF Pc Ic] mult_smult_distrib[OF Pc P0c] right_mult_one_mat[OF Pc])
  finally have s1: "?P * (?c \<cdot>\<^sub>m ?I + ?a \<cdot>\<^sub>m ?Z) = ?c \<cdot>\<^sub>m ?P + ?a \<cdot>\<^sub>m (?P * ?Z)" .
  have PP0: "?P * ?Z \<in> carrier_mat ?n ?n" by (rule mult_carrier_mat[OF Pc P0c])
  have PQ: "?P * ?Q = ?I" by (rule inc_dec_pmat[OF n0])
  have PP0Q: "?P * ?Z * ?Q = pmat ?n (lp ?n 1)" by (rule lp1_pmat[OF n(1,2), symmetric])
  have "(?c \<cdot>\<^sub>m ?P + ?a \<cdot>\<^sub>m (?P * ?Z)) * ?Q = (?c \<cdot>\<^sub>m ?P) * ?Q + (?a \<cdot>\<^sub>m (?P * ?Z)) * ?Q"
    by (rule add_mult_distrib_mat[OF smult_carrier_mat[OF Pc] smult_carrier_mat[OF PP0] Qc])
  also have "\<dots> = ?c \<cdot>\<^sub>m (?P * ?Q) + ?a \<cdot>\<^sub>m (?P * ?Z * ?Q)"
    by (simp only: mult_smult_assoc_mat[OF Pc Qc] mult_smult_assoc_mat[OF PP0 Qc])
  also have "\<dots> = ?c \<cdot>\<^sub>m ?I + ?a \<cdot>\<^sub>m pmat ?n (lp ?n 1)" unfolding PQ PP0Q ..
  finally have s2: "(?c \<cdot>\<^sub>m ?P + ?a \<cdot>\<^sub>m (?P * ?Z)) * ?Q = ?c \<cdot>\<^sub>m ?I + ?a \<cdot>\<^sub>m pmat ?n (lp ?n 1)" .
  have "evolution (colour_part ?n (lap ?n) (lp ?n 1)) d = pair_evo ?n (lp ?n 1) (colour_h (lap ?n) (lp ?n 1)) d"
    by (rule evolution_colour_part[OF lap_carrier lap_hermitian q1])
  also have "\<dots> = ?c \<cdot>\<^sub>m ?I + ?a \<cdot>\<^sub>m pmat ?n (lp ?n 1)" by (rule pair_evo_const[OF q1 colour_h_lap[OF n(1,2)]])
  also have "\<dots> = ?P * qw m 0 (xrot d) * ?Q" unfolding E0[symmetric] s1 s2 ..
  finally show ?thesis .
qed

subsection \<open>The circuit\<close>

lemma xrot_unitary: "Quantum.unitary (xrot d)"
proof -
  have "cos d * cos d + sin d * sin d = 1" using sin_cos_squared_add[of d] by (simp add: power2_eq_square)
  hence c: "complex_of_real (cos d) * complex_of_real (cos d) + complex_of_real (sin d) * complex_of_real (sin d) = 1"
    by (simp flip: of_real_mult of_real_add)
  have "(xrot d)\<^sup>\<dagger> * xrot d = 1\<^sub>m 2" "xrot d * ((xrot d)\<^sup>\<dagger>) = 1\<^sub>m 2"
    by (rule eq_matI, auto simp: xrot_def dagger_def scalar_prod_def atLeast0LessThan sumof2 less_Suc_eq numeral_2_eq_2 c
        algebra_simps)+
  thus ?thesis by (simp add: Quantum.unitary_def xrot_def)
qed

lemma gph_unitary: "Quantum.unitary (gph d)"
proof -
  have c: "cnj (cis d) * cis d = 1" by (simp add: cis_cnj cis_mult)
  have c2: "cis d * cnj (cis d) = 1" by (simp add: cis_cnj cis_mult)
  have "(gph d)\<^sup>\<dagger> * gph d = 1\<^sub>m 2" "gph d * ((gph d)\<^sup>\<dagger>) = 1\<^sub>m 2"
    by (rule eq_matI, auto simp: gph_def dagger_def scalar_prod_def atLeast0LessThan sumof2 less_Suc_eq numeral_2_eq_2 c c2)+
  thus ?thesis by (simp add: Quantum.unitary_def gph_def)
qed

lemma qw0_lift:
  assumes m: "0 < m"
  shows "qw (2 * m) 0 G = 1\<^sub>m (2 ^ m) \<Otimes> qw m 0 G"
proof -
  have e: "(2::nat) ^ m * 2 ^ (m - Suc 0) = 2 ^ (2 * m - Suc 0)" using m by (simp flip: power_add)
  show ?thesis unfolding qw_def tensor_mat_is_assoc tensor_mat_id e ..
qed

lemma stands_for_pow:
  assumes s: "stands_for A N U G"
  shows "stands_for A N (U ^\<^sub>m r) (G ^\<^sub>m r)"
proof (induction r)
  case 0
  have d: "dim_row U = A * N" "dim_row G = N" using s unfolding stands_for_def by auto
  have "stands_for A N (circuit_mat (A * N) []) (circuit_mat N [])" by (rule stands_for_circuit) simp
  thus ?case using d by simp
next
  case (Suc r)
  show ?case using stands_for_mult[OF s Suc.IH] by simp
qed

text \<open>One Trotter step, in time order: decrement, rotate wire $0$, increment (colour $1$);
rotate wire $0$ (colour $0$); the global phase of the diagonal.\<close>

definition lap_step :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "lap_step m d = compile (2 * m) (rev (incr_gates m m)) @ [qw (2 * m) 0 (xrot d)]
     @ compile (2 * m) (incr_gates m m) @ [qw (2 * m) 0 (xrot d), qw (2 * m) 0 (gph (2 * d))]"

lemma lap_step_props:
  assumes m: "2 \<le> m"
  shows "stands_for (2 ^ m) (2 ^ m) (circuit_mat (2 ^ (2 * m)) (lap_step m d))
      (evolution_product (2 ^ m) d (sparse_parts (2 ^ m) (lap (2 ^ m)) 2 (lp (2 ^ m))))"
    "\<forall>U \<in> set (lap_step m d). elementary (2 ^ (2 * m)) U"
    "length (lap_step m d) \<le> 2 * (m * (m + 2) * (12 * m + 7)) + 3"
proof -
  let ?n = "2 ^ m :: nat" and ?K = "2 * m" and ?g = "incr_gates m m"
  let ?X = "qw ?K 0 (xrot d)" and ?Y = "qw ?K 0 (gph (2 * d))"
  let ?A = "qw m 0 (xrot d)" and ?B = "qw m 0 (gph (2 * d))"
  let ?P = "pmat ?n (inc_f ?n)" and ?Q = "pmat ?n (dec_f ?n)"
  note n = pow_facts[OF m]
  have n0: "0 < ?n" by simp
  have KK: "(2::nat) ^ ?K = ?n * ?n" by (simp add: mult_2 power_add)
  have ok: "\<forall>g \<in> set ?g. rg_ok ?K g" by (rule incr_rg_ok) simp
  have okr: "\<forall>g \<in> set (rev ?g). rg_ok ?K g" using ok by simp
  note CI = compile_props[OF ok] and CD = compile_props[OF okr]
  have inc: "rcirc ?g z = inc_f ?n z" if "z < ?n" for z using incr_rcirc[OF that] by (simp add: inc_f_def)
  have dec: "rcirc (rev ?g) z = dec_f ?n z" if z: "z < ?n" for z
  proof -
    have dz: "dec_f ?n z < ?n" by (rule inc_dec_lt(2)[OF n0])
    have "inc_f ?n (dec_f ?n z) = z" using z by (cases z) (simp_all add: inc_f_def dec_f_def)
    hence "rcirc ?g (dec_f ?n z) = z" using inc[OF dz] by simp
    hence "rcirc (rev ?g) z = rcirc (rev ?g) (rcirc ?g (dec_f ?n z))" by simp
    also have "\<dots> = dec_f ?n z" by (rule rcirc_rev[OF ok])
    finally show ?thesis .
  qed
  have SI: "stands_for ?n ?n (circuit_mat (2 ^ ?K) (compile ?K ?g)) ?P"
    unfolding CI(1) unfolding KK by (rule stands_for_pmat) (simp_all add: inc inc_dec_lt)
  have SD: "stands_for ?n ?n (circuit_mat (2 ^ ?K) (compile ?K (rev ?g))) ?Q"
    unfolding CD(1) unfolding KK by (rule stands_for_pmat) (simp_all add: dec inc_dec_lt)
  have SX: "stands_for ?n ?n ?X ?A"
    unfolding qw0_lift[OF n(3)] by (rule stands_for_lift[OF qw_carrier[OF xrot_carrier n(3)]]) simp
  have SY: "stands_for ?n ?n ?Y ?B"
    unfolding qw0_lift[OF n(3)] by (rule stands_for_lift[OF qw_carrier[OF gph_carrier n(3)]]) simp
  have Xc: "?X \<in> carrier_mat (2 ^ ?K) (2 ^ ?K)" and Yc: "?Y \<in> carrier_mat (2 ^ ?K) (2 ^ ?K)"
    by (rule qw_carrier, simp, use n(3) in simp)+
  have Cl: "\<And>U. U \<in> set (compile ?K ?g) \<Longrightarrow> U \<in> carrier_mat (2 ^ ?K) (2 ^ ?K)" using CI(2) elementary_unitary(1) by blast
  have Dl: "\<And>U. U \<in> set (compile ?K (rev ?g)) \<Longrightarrow> U \<in> carrier_mat (2 ^ ?K) (2 ^ ?K)" using CD(2) elementary_unitary(1) by blast
  have a1: "circuit_mat (2 ^ ?K) (lap_step m d)
      = circuit_mat (2 ^ ?K) ([?X] @ compile ?K ?g @ [?X, ?Y]) * circuit_mat (2 ^ ?K) (compile ?K (rev ?g))"
    unfolding lap_step_def by (rule circuit_mat_append) (use Cl Dl Xc Yc in auto)
  have a2: "circuit_mat (2 ^ ?K) ([?X] @ compile ?K ?g @ [?X, ?Y])
      = circuit_mat (2 ^ ?K) (compile ?K ?g @ [?X, ?Y]) * ?X" by simp
  have a3: "circuit_mat (2 ^ ?K) (compile ?K ?g @ [?X, ?Y]) = circuit_mat (2 ^ ?K) [?X, ?Y] * circuit_mat (2 ^ ?K) (compile ?K ?g)"
    by (rule circuit_mat_append) (use Cl Xc Yc in auto)
  have a4: "circuit_mat (2 ^ ?K) [?X, ?Y] = ?Y * ?X" using Yc by simp
  have S: "stands_for ?n ?n (circuit_mat (2 ^ ?K) (lap_step m d)) (?B * ?A * ?P * ?A * ?Q)"
    unfolding a1 a2 a3 a4 by (intro stands_for_mult SD SX SI SY)
  have Ac: "?A \<in> carrier_mat ?n ?n" and Bc: "?B \<in> carrier_mat ?n ?n"
    by (rule qw_carrier, simp, use n(3) in simp)+
  have Pc: "?P \<in> carrier_mat ?n ?n" and Qc: "?Q \<in> carrier_mat ?n ?n" by simp_all
  have E: "evolution_product ?n d (sparse_parts ?n (lap ?n) 2 (lp ?n)) = ?B * ?A * ?P * ?A * ?Q"
  proof -
    have u: "[0..<2] = [0::nat, 1]" by (simp add: upt_rec)
    have BA: "?B * ?A \<in> carrier_mat ?n ?n" by (rule mult_carrier_mat[OF Bc Ac])
    have BAP: "?B * ?A * ?P \<in> carrier_mat ?n ?n" by (rule mult_carrier_mat[OF BA Pc])
    have AQ: "?A * ?Q \<in> carrier_mat ?n ?n" by (rule mult_carrier_mat[OF Ac Qc])
    have PAQ: "?P * (?A * ?Q) \<in> carrier_mat ?n ?n" by (rule mult_carrier_mat[OF Pc AQ])
    have "evolution_product ?n d (sparse_parts ?n (lap ?n) 2 (lp ?n)) = ?B * (?A * (?P * ?A * ?Q))"
      using Ac Bc Pc Qc by (simp add: sparse_parts_def u evo_diag[OF m] evo_colour0[OF m] evo_colour1[OF m, unfolded One_nat_def])
    also have "\<dots> = ?B * ?A * ?P * ?A * ?Q"
      by (simp only: assoc_mult_mat[OF BAP Ac Qc] assoc_mult_mat[OF BA Pc AQ] assoc_mult_mat[OF Bc Ac PAQ]
          assoc_mult_mat[OF Pc Ac Qc])
    finally show ?thesis .
  qed
  show "stands_for ?n ?n (circuit_mat (2 ^ ?K) (lap_step m d)) (evolution_product ?n d (sparse_parts ?n (lap ?n) 2 (lp ?n)))"
    unfolding E by (rule S)
  have eX: "elementary (2 ^ ?K) ?X" and eY: "elementary (2 ^ ?K) ?Y"
    by (rule qw_elementary, use n(3) in simp, simp, rule xrot_unitary)
      (rule qw_elementary, use n(3) in simp, simp, rule gph_unitary)
  show "\<forall>U \<in> set (lap_step m d). elementary (2 ^ ?K) U" using CI(2) CD(2) eX eY by (auto simp: lap_step_def)
  have l: "length (compile ?K ?g) \<le> m * (m + 2) * (12 * m + 7)" "length (compile ?K (rev ?g)) \<le> m * (m + 2) * (12 * m + 7)"
    using CI(3) CD(3) by (simp_all add: length_incr)
  have "length (lap_step m d) = length (compile ?K (rev ?g)) + length (compile ?K ?g) + 3" by (simp add: lap_step_def)
  thus "length (lap_step m d) \<le> 2 * (m * (m + 2) * (12 * m + 7)) + 3" using l by linarith
qed

definition lap_gates :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "lap_gates m t r = concat (replicate r (lap_step m (t / real r)))"

text \<open>The headline: on $m$ clean ancillas, $r$ Trotter steps of elementary gates, $O(r\,m^3)$ of
them and no oracle, implement $e^{itL}$ of the $2^m$-cycle Laplacian within $72t^2/r$.\<close>

theorem laplacian_gates:
  assumes m: "2 \<le> m" and r: "0 < r" and v: "dim_vec v = 2 ^ m"
  shows "\<parallel>circuit_mat (2 ^ (2 * m)) (lap_gates m t r) *\<^sub>v (anc (2 ^ m) (2 ^ m) *\<^sub>v v)
      - anc (2 ^ m) (2 ^ m) *\<^sub>v (evolution (lap (2 ^ m)) t *\<^sub>v v)\<parallel> \<le> 72 * t\<^sup>2 / real r * \<parallel>v\<parallel>"
    "\<forall>U \<in> set (lap_gates m t r). elementary (2 ^ (2 * m)) U"
    "length (lap_gates m t r) \<le> r * (2 * (m * (m + 2) * (12 * m + 7)) + 3)"
proof -
  let ?n = "2 ^ m :: nat" and ?d = "t / real r"
  let ?E = "evolution_product ?n ?d (sparse_parts ?n (lap ?n) 2 (lp ?n))"
  note S = lap_step_props[OF m, where d = ?d]
  note n = pow_facts[OF m]
  have stepc: "\<And>U. U \<in> set (lap_step m ?d) \<Longrightarrow> U \<in> carrier_mat (2 ^ (2 * m)) (2 ^ (2 * m))"
    using S(2) elementary_unitary(1) by blast
  have C: "circuit_mat (2 ^ (2 * m)) (lap_gates m t r) = circuit_mat (2 ^ (2 * m)) (lap_step m ?d) ^\<^sub>m r"
    unfolding lap_gates_def by (rule circuit_mat_concat_replicate[OF stepc])
  have SP: "stands_for ?n ?n (circuit_mat (2 ^ (2 * m)) (lap_gates m t r)) (?E ^\<^sub>m r)"
    unfolding C by (rule stands_for_pow[OF S(1)])
  have T: "?E ^\<^sub>m r \<approx>\<^bsub>72 * t\<^sup>2 / real r\<^esub> evolution (lap ?n) t" by (rule lap_trotter[OF n(1,2) r])
  have Ec: "?E ^\<^sub>m r \<in> carrier_mat ?n ?n" using SP by (simp add: stands_for_def)
  have vc: "v \<in> carrier_vec ?n" by (rule carrier_vecI[OF v])
  have wc: "evolution (lap ?n) t *\<^sub>v v \<in> carrier_vec ?n"
    by (rule mult_mat_vec_carrier[OF evolution_carrier[OF lap_carrier lap_hermitian] vc])
  have "\<parallel>circuit_mat (2 ^ (2 * m)) (lap_gates m t r) *\<^sub>v (anc ?n ?n *\<^sub>v v) - anc ?n ?n *\<^sub>v (evolution (lap ?n) t *\<^sub>v v)\<parallel>
      = \<parallel>?E ^\<^sub>m r *\<^sub>v v - evolution (lap ?n) t *\<^sub>v v\<parallel>" by (rule stands_for_dist[OF SP vc wc]) simp
  also have "\<dots> \<le> 72 * t\<^sup>2 / real r * \<parallel>v\<parallel>" by (rule op_closeD[OF T Ec v])
  finally show "\<parallel>circuit_mat (2 ^ (2 * m)) (lap_gates m t r) *\<^sub>v (anc ?n ?n *\<^sub>v v)
      - anc ?n ?n *\<^sub>v (evolution (lap ?n) t *\<^sub>v v)\<parallel> \<le> 72 * t\<^sup>2 / real r * \<parallel>v\<parallel>" .
  show "\<forall>U \<in> set (lap_gates m t r). elementary (2 ^ (2 * m)) U" using S(2) by (auto simp: lap_gates_def)
  have "length (lap_gates m t r) = r * length (lap_step m ?d)" by (simp add: lap_gates_def length_concat sum_list_replicate)
  thus "length (lap_gates m t r) \<le> r * (2 * (m * (m + 2) * (12 * m + 7)) + 3)" using mult_le_mono2[OF S(3)] by simp
qed

end
