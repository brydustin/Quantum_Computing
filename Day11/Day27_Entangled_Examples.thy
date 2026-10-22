theory Day27_Entangled_Examples
  imports Day18_Positive_Maps Day27_Positive_Map_Criterion
begin

section \<open>Day 27: entangled matrices detected by the transpose (D27-2)\<close>

text \<open>For $f:\{0,\dots,r-1\}\to\{0,\dots,n-1\}$ the block matrix $(E_{f(a)f(b)})_{a,b}\in M_r(M_n)$.
The notes' examples are $f=(i,j)$ with $r=2$, giving $\begin{pmatrix}E_{ii}&E_{ij}\\E_{ji}&E_{jj}\end{pmatrix}$,
and $f=\mathrm{id}$ with $r=n$, giving $(E_{ij})$.\<close>

definition unit_blocks :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.mat" where
  "unit_blocks r n f = Matrix.mat (r * n) (r * n)
     (\<lambda>(x, y). if x mod n = f (x div n) \<and> y mod n = f (y div n) then 1 else 0)"

lemma unit_blocks_carrier [simp]: "unit_blocks r n f \<in> carrier_mat (r * n) (r * n)"
  by (simp add: unit_blocks_def)

lemma unit_blocks_block:
  assumes "a < r" "b < r" "f a < n" "f b < n"
  shows "block_of_mat n (unit_blocks r n f) a b = mat_unit (f a) (f b) n n"
proof (rule eq_matI)
  fix k l assume "k < dim_row (mat_unit (f a) (f b) n n)" "l < dim_col (mat_unit (f a) (f b) n n)"
  hence k: "k < n" and l: "l < n" by (simp_all add: mat_unit_def)
  have x: "a * n + k < r * n" and y: "b * n + l < r * n"
    using mult_index_lt assms k l by simp_all
  show "block_of_mat n (unit_blocks r n f) a b $$ (k, l) = mat_unit (f a) (f b) n n $$ (k, l)"
    using k l x y by (auto simp: block_of_mat_def unit_blocks_def mat_unit_def)
qed (simp_all add: block_of_mat_def mat_unit_def)

definition unit_blocks_vec :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex Matrix.vec" where
  "unit_blocks_vec r n f = Matrix.vec (r * n) (\<lambda>x. if x mod n = f (x div n) then 1 else 0)"

lemma unit_blocks_outer: "unit_blocks r n f = unit_blocks_vec r n f \<oslash> unit_blocks_vec r n f"
proof (rule eq_matI)
  let ?v = "unit_blocks_vec r n f"
  have vd: "dim_vec ?v = r * n" by (simp add: unit_blocks_vec_def)
  fix x y assume "x < dim_row (?v \<oslash> ?v)" "y < dim_col (?v \<oslash> ?v)"
  hence x: "x < r * n" and y: "y < r * n" using carrier_matD[OF outer_prod_carrier[OF vd vd]] by auto
  show "unit_blocks r n f $$ (x, y) = (?v \<oslash> ?v) $$ (x, y)"
    using outer_prod_index[of x ?v y ?v] x y vd by (simp add: unit_blocks_def unit_blocks_vec_def)
qed (use carrier_matD[OF outer_prod_carrier[of "unit_blocks_vec r n f" "r * n" "unit_blocks_vec r n f" "r * n"]]
     in \<open>simp_all add: unit_blocks_def unit_blocks_vec_def\<close>)

lemma unit_blocks_psd: "psd (unit_blocks r n f)"
  unfolding unit_blocks_outer by (rule outer_prod_self_psd) (simp add: unit_blocks_vec_def)

lemma sum_two_support:
  fixes g :: "nat \<Rightarrow> complex"
  assumes "p \<noteq> q" "p < m" "q < m" "\<And>x. x < m \<Longrightarrow> x \<noteq> p \<Longrightarrow> x \<noteq> q \<Longrightarrow> g x = 0"
  shows "(\<Sum>x = 0..<m. g x) = g p + g q"
proof -
  have "(\<Sum>x = 0..<m. g x) = (\<Sum>x \<in> {p, q}. g x)"
    by (rule sum.mono_neutral_right) (use assms in auto)
  thus ?thesis using assms(1) by simp
qed

lemma transpose_lin_on: "lin_on n n (carrier_mat n n) (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat)"
  unfolding lin_on_def by (auto intro!: eq_matI)

text \<open>The partial transpose of $(E_{f(a)f(b)})$ is $(E_{f(b)f(a)})$; its quadratic form at
$e_0\otimes e_{f(1)}-e_1\otimes e_{f(0)}$ is $-2$.\<close>

lemma unit_blocks_partial_transpose_not_psd:
  assumes r: "2 \<le> r" and f: "f 0 < n" "f 1 < n" "f 0 \<noteq> f 1"
  shows "\<not> psd (amplification n n r (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) (unit_blocks r n f))"
proof
  let ?M = "unit_blocks r n f"
  let ?Y = "amplification n n r (transpose_mat :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) ?M"
  assume ps: "psd ?Y"
  define p q where "p = f 1" and "q = n + f 0"
  have n: "0 < n" using f by simp
  have rn: "2 * n \<le> r * n" using r by simp
  have pq: "p \<noteq> q" "p < r * n" "q < r * n" using f rn unfolding p_def q_def by linarith+
  have Yc: "?Y \<in> carrier_mat (r * n) (r * n)" by (simp add: amplification_def)
  have Ye: "?Y $$ (x, y) = (if y mod n = f (x div n) \<and> x mod n = f (y div n) then 1 else 0)"
    if x: "x < r * n" and y: "y < r * n" for x y
  proof -
    have xd: "x div n < r" "y div n < r" using x y by (simp_all add: less_mult_imp_div_less)
    have "(x div n) * n + y mod n < r * n" "(y div n) * n + x mod n < r * n"
      using mult_index_lt xd n by simp_all
    thus ?thesis using x y n by (simp add: amplification_def block_of_mat_def unit_blocks_def)
  qed
  define h :: "complex Matrix.vec" where "h = Matrix.vec (r * n) (\<lambda>x. if x = p then 1 else if x = q then -1 else 0)"
  have hd: "dim_vec h = r * n" by (simp add: h_def)
  have pdiv: "p div n = 0" "p mod n = f 1" "q div n = 1" "q mod n = f 0"
    using f unfolding p_def q_def by simp_all
  have Yh: "(?Y *\<^sub>v h) $ x = ?Y $$ (x, p) - ?Y $$ (x, q)" if x: "x < r * n" for x
  proof -
    have "(?Y *\<^sub>v h) $ x = (\<Sum>y = 0..<r * n. ?Y $$ (x, y) * h $ y)"
      using x carrier_matD[OF Yc] hd by (simp add: scalar_prod_def)
    also have "\<dots> = ?Y $$ (x, p) * h $ p + ?Y $$ (x, q) * h $ q"
      by (rule sum_two_support[OF pq]) (simp add: h_def)
    finally show ?thesis using pq by (simp add: h_def)
  qed
  have "\<langle>h | ?Y *\<^sub>v h\<rangle> = (\<Sum>x = 0..<r * n. cnj (h $ x) * (?Y *\<^sub>v h) $ x)"
    using inner_prod_sum[of h "r * n" "?Y *\<^sub>v h"] hd carrier_matD[OF Yc] by simp
  also have "\<dots> = cnj (h $ p) * (?Y *\<^sub>v h) $ p + cnj (h $ q) * (?Y *\<^sub>v h) $ q"
    by (rule sum_two_support[OF pq]) (simp add: h_def)
  also have "\<dots> = (?Y $$ (p, p) - ?Y $$ (p, q)) - (?Y $$ (q, p) - ?Y $$ (q, q))"
    using pq Yh[of p] Yh[of q] by (simp add: h_def)
  also have "\<dots> = -2" using pq f by (simp add: Ye pdiv)
  finally have "Re \<langle>h | ?Y *\<^sub>v h\<rangle> = -2" by simp
  moreover have "\<forall>x. dim_vec x = dim_row ?Y \<longrightarrow> Re \<langle>x | ?Y *\<^sub>v x\<rangle> \<ge> 0"
    using ps unfolding psd_def by blast
  hence "0 \<le> Re \<langle>h | ?Y *\<^sub>v h\<rangle>" using hd carrier_matD(1)[OF Yc] by (rule_tac allE, auto)
  ultimately show False by simp
qed

theorem unit_blocks_entangled:
  fixes R :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes R: "unwrap_lm R = unit_blocks CARD('m) CARD('p) f"
      and r: "2 \<le> CARD('m)" and f: "f 0 < CARD('p)" "f 1 < CARD('p)" "f 0 \<noteq> f 1"
  shows "psd (unwrap_lm R) \<and> R \<notin> separable_cone_lmat"
proof
  show "psd (unwrap_lm R)" unfolding R by (rule unit_blocks_psd)
  show "R \<notin> separable_cone_lmat"
  proof
    assume sep: "R \<in> separable_cone_lmat"
    have "psd (amplification CARD('p) CARD('p) CARD('m) transpose_mat (unwrap_lm R))"
      by (rule positive_map_separable[OF transpose_lin_on transpose_positive_map _ sep]) simp
    thus False using unit_blocks_partial_transpose_not_psd[OF r f] unfolding R by simp
  qed
qed

text \<open>The notes' first example: $\begin{pmatrix}E_{ii}&E_{ij}\\E_{ji}&E_{jj}\end{pmatrix}\in M_2(M_n)$, $i\ne j$.\<close>

corollary entangled_example_2:
  fixes R :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes m: "CARD('m) = 2" and ij: "i < CARD('p)" "j < CARD('p)" "i \<noteq> j"
      and R: "unwrap_lm R = unit_blocks 2 CARD('p) (\<lambda>a. if a = 0 then i else j)"
  shows "block_of_mat CARD('p) (unwrap_lm R) 0 0 = E\<lbrakk>i,i ; CARD('p),CARD('p)\<rbrakk>"
    and "block_of_mat CARD('p) (unwrap_lm R) 0 1 = E\<lbrakk>i,j ; CARD('p),CARD('p)\<rbrakk>"
    and "block_of_mat CARD('p) (unwrap_lm R) 1 0 = E\<lbrakk>j,i ; CARD('p),CARD('p)\<rbrakk>"
    and "block_of_mat CARD('p) (unwrap_lm R) 1 1 = E\<lbrakk>j,j ; CARD('p),CARD('p)\<rbrakk>"
    and "psd (unwrap_lm R) \<and> R \<notin> separable_cone_lmat"
proof -
  let ?f = "\<lambda>a::nat. if a = 0 then i else j"
  show "block_of_mat CARD('p) (unwrap_lm R) 0 0 = E\<lbrakk>i,i ; CARD('p),CARD('p)\<rbrakk>"
    using unit_blocks_block[of 0 2 0 ?f "CARD('p)"] ij unfolding R by simp
  show "block_of_mat CARD('p) (unwrap_lm R) 0 1 = E\<lbrakk>i,j ; CARD('p),CARD('p)\<rbrakk>"
    using unit_blocks_block[of 0 2 1 ?f "CARD('p)"] ij unfolding R by simp
  show "block_of_mat CARD('p) (unwrap_lm R) 1 0 = E\<lbrakk>j,i ; CARD('p),CARD('p)\<rbrakk>"
    using unit_blocks_block[of 1 2 0 ?f "CARD('p)"] ij unfolding R by simp
  show "block_of_mat CARD('p) (unwrap_lm R) 1 1 = E\<lbrakk>j,j ; CARD('p),CARD('p)\<rbrakk>"
    using unit_blocks_block[of 1 2 1 ?f "CARD('p)"] ij unfolding R by simp
  show "psd (unwrap_lm R) \<and> R \<notin> separable_cone_lmat"
    by (rule unit_blocks_entangled[where f = ?f]) (use m ij R in simp_all)
qed

text \<open>The second: $(E_{ij})\in M_n(M_n)$, $n\ge2$, which is \<^const>\<open>choi_seed\<close>.\<close>

lemma choi_seed_unit_blocks: "choi_seed n = unit_blocks n n id"
proof (rule eq_matI)
  fix x y assume "x < dim_row (unit_blocks n n id)" "y < dim_col (unit_blocks n n id)"
  hence x: "x < n * n" and y: "y < n * n" by (simp_all add: unit_blocks_def)
  have "x div n < n" "y div n < n" "x mod n < n" "y mod n < n"
    using x y by (simp_all add: less_mult_imp_div_less) (cases n; simp)+
  thus "choi_seed n $$ (x, y) = unit_blocks n n id $$ (x, y)"
    using x y by (simp add: choi_seed_def unit_blocks_def)
qed (simp_all add: choi_seed_def unit_blocks_def)

corollary entangled_example_choi_seed:
  fixes R :: "(complex, 'p :: finite \<times> 'p, 'p \<times> 'p) lmat"
  assumes n: "2 \<le> CARD('p)" and R: "unwrap_lm R = choi_seed CARD('p)"
  shows "psd (unwrap_lm R) \<and> R \<notin> separable_cone_lmat"
  by (rule unit_blocks_entangled[where f = id]) (use n R in \<open>simp_all add: choi_seed_unit_blocks\<close>)

end
