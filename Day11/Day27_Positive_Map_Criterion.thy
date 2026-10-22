theory Day27_Positive_Map_Criterion
  imports Day26_Arveson_Extension Day34_Knill_Laflamme
begin

text \<open>Days 27--28: positive maps detect entanglement.  For $R\in M_r(M_n)$ (block size $n$),
$\Phi^{(r)}(R)\ge0$ for every positive $\Phi$ when $R$ is separable (D27-1); a functional $f$ on
$M_r(M_n)$ is nonnegative on the separable matrices iff $\Phi_f$ is positive (D27-3); and with
the entanglement witnesses of \<open>Separable_Cone\<close> this gives the positive-map criterion (D28-3).\<close>

subsection \<open>Tensor products with a matrix in the first factor\<close>

lemma tensor_add_first:
  fixes A B P :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat r r" and B: "B \<in> carrier_mat r r" and P: "P \<in> carrier_mat n n" and n: "0 < n"
  shows "Tensor.tensor_mat (A + B) P = Tensor.tensor_mat A P + Tensor.tensor_mat B P"
proof (rule eq_matI)
  fix x y assume "x < dim_row (Tensor.tensor_mat A P + Tensor.tensor_mat B P)"
    "y < dim_col (Tensor.tensor_mat A P + Tensor.tensor_mat B P)"
  hence x: "x < r * n" and y: "y < r * n" using A B P by simp_all
  have r: "0 < r" using x by (cases r) auto
  have xd: "x div n < r" "y div n < r" using x y n by (simp_all add: less_mult_imp_div_less mult.commute)
  have e: "\<And>M. M \<in> carrier_mat r r \<Longrightarrow> Tensor.tensor_mat M P $$ (x,y) = M $$ (x div n, y div n) * P $$ (x mod n, y mod n)"
    by (rule index_tensor_mat) (use x y P r n in simp_all)
  show "Tensor.tensor_mat (A + B) P $$ (x,y) = (Tensor.tensor_mat A P + Tensor.tensor_mat B P) $$ (x,y)"
    using e[OF add_carrier_mat[OF B]] e[OF A] e[OF B] x y xd A B P by (simp add: distrib_right)
qed (use A B P in simp_all)

lemma tensor_zero_first:
  fixes P :: "complex Matrix.mat"
  assumes P: "P \<in> carrier_mat n n" and n: "0 < n"
  shows "Tensor.tensor_mat (0\<^sub>m r r) P = 0\<^sub>m (r * n) (r * n)"
proof (rule eq_matI)
  fix x y assume "x < dim_row (0\<^sub>m (r * n) (r * n) :: complex Matrix.mat)" "y < dim_col (0\<^sub>m (r * n) (r * n) :: complex Matrix.mat)"
  hence x: "x < r * n" and y: "y < r * n" by simp_all
  have r: "0 < r" using x by (cases r) auto
  have xd: "x div n < r" "y div n < r" using x y n by (simp_all add: less_mult_imp_div_less mult.commute)
  have "Tensor.tensor_mat (0\<^sub>m r r) P $$ (x,y) = (0\<^sub>m r r :: complex Matrix.mat) $$ (x div n, y div n) * P $$ (x mod n, y mod n)"
    by (rule index_tensor_mat) (use x y P r n in simp_all)
  thus "Tensor.tensor_mat (0\<^sub>m r r) P $$ (x,y) = (0\<^sub>m (r * n) (r * n) :: complex Matrix.mat) $$ (x,y)" using x y xd by simp
qed (use P in simp_all)

lemma tensor_msum_first:
  fixes P :: "complex Matrix.mat"
  assumes g: "\<forall>x \<in> set xs. g x \<in> carrier_mat r r" and P: "P \<in> carrier_mat n n" and n: "0 < n"
  shows "Tensor.tensor_mat (msum r r g xs) P = msum (r * n) (r * n) (\<lambda>x. Tensor.tensor_mat (g x) P) xs"
  using g
proof (induction xs)
  case Nil show ?case using tensor_zero_first[OF P n] by simp
next
  case (Cons x xs)
  have gx: "g x \<in> carrier_mat r r" and rest: "\<forall>x \<in> set xs. g x \<in> carrier_mat r r" using Cons.prems by auto
  show ?case using tensor_add_first[OF gx msum_carrier[OF rest] P n] Cons.IH[OF rest] by simp
qed

subsection \<open>The quadratic form of $\Phi_f$\<close>

definition rank1 :: "complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "rank1 w = Matrix.mat (dim_vec w) (dim_vec w) (\<lambda>(i,j). cnj (w $ i) * w $ j)"

lemma rank1_carrier [simp]: "rank1 w \<in> carrier_mat (dim_vec w) (dim_vec w)"
  by (simp add: rank1_def)

lemma rank1_dims [simp]: "dim_row (rank1 w) = dim_vec w" "dim_col (rank1 w) = dim_vec w"
  by (simp_all add: rank1_def)

lemma rank1_outer: "rank1 (conjugate u) = u \<oslash> u"
proof -
  define Ou where "Ou = u \<oslash> u"
  have c: "Ou \<in> carrier_mat (dim_vec u) (dim_vec u)" unfolding Ou_def by (rule outer_prod_carrier) simp_all
  have "rank1 (conjugate u) = Ou"
  proof (rule eq_matI)
    fix i j assume "i < dim_row Ou" "j < dim_col Ou"
    hence i: "i < dim_vec u" and j: "j < dim_vec u" using c by simp_all
    show "rank1 (conjugate u) $$ (i,j) = Ou $$ (i,j)"
      unfolding Ou_def using outer_prod_index[OF i j] i j by (simp add: rank1_def)
  qed (use c in \<open>simp_all add: rank1_def\<close>)
  thus ?thesis unfolding Ou_def .
qed

lemma rank1_psd: "psd (rank1 w)"
proof -
  have "rank1 w = rank1 (conjugate (conjugate w))" by simp
  also have "\<dots> = conjugate w \<oslash> conjugate w" by (rule rank1_outer)
  finally show ?thesis using outer_prod_self_psd[of "conjugate w" "dim_vec w"] by simp
qed

lemma quad_arveson_map:
  fixes f :: "complex Matrix.mat \<Rightarrow> complex" and w :: "complex Matrix.vec"
  assumes f: "lin_fun_on (carrier_mat (r * n) (r * n)) f" and w: "dim_vec w = r" and P: "P \<in> carrier_mat n n" and n: "0 < n"
  shows "\<langle>w | arveson_map n r f P *\<^sub>v w\<rangle> = of_nat r * f (Tensor.tensor_mat (rank1 w) P)"
proof -
  let ?Phi = "arveson_map n r f P"
  let ?c = "\<lambda>i j. cnj (w $ i) * w $ j"
  let ?g = "\<lambda>(i,j). ?c i j \<cdot>\<^sub>m unit_block r n i j P"
  have TS: "operator_system (r * n) (carrier_mat (r * n) (r * n))" by (rule operator_system_full)
  have gc: "\<forall>x \<in> set (List.product [0..<r] [0..<r]). ?g x \<in> carrier_mat (r * n) (r * n)" by auto
  have Pw: "dim_vec (?Phi *\<^sub>v w) = r" by simp
  have "\<langle>w | ?Phi *\<^sub>v w\<rangle> = (\<Sum>i<r. cnj (w $ i) * (?Phi *\<^sub>v w) $ i)"
    unfolding inner_prod_sum[OF w Pw] atLeast0LessThan ..
  also have "\<dots> = (\<Sum>i<r. \<Sum>j<r. of_nat r * f (?c i j \<cdot>\<^sub>m unit_block r n i j P))"
  proof (rule sum.cong[OF refl])
    fix i assume "i \<in> {..<r}"
    hence i: "i < r" by simp
    have "(?Phi *\<^sub>v w) $ i = (\<Sum>j<r. ?Phi $$ (i,j) * w $ j)" using i w by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>j<r. of_nat r * f (unit_block r n i j P) * w $ j)"
      by (rule sum.cong[OF refl]) (simp add: arveson_map_index i)
    finally have "cnj (w $ i) * (?Phi *\<^sub>v w) $ i = (\<Sum>j<r. cnj (w $ i) * (of_nat r * f (unit_block r n i j P) * w $ j))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>j<r. of_nat r * f (?c i j \<cdot>\<^sub>m unit_block r n i j P))"
    proof (rule sum.cong[OF refl])
      fix j
      have "f (?c i j \<cdot>\<^sub>m unit_block r n i j P) = ?c i j * f (unit_block r n i j P)"
        using f unit_block_carrier[of r n i j P] unfolding lin_fun_on_def by blast
      thus "cnj (w $ i) * (of_nat r * f (unit_block r n i j P) * w $ j) = of_nat r * f (?c i j \<cdot>\<^sub>m unit_block r n i j P)"
        by (simp add: mult_ac)
    qed
    finally show "cnj (w $ i) * (?Phi *\<^sub>v w) $ i = (\<Sum>j<r. of_nat r * f (?c i j \<cdot>\<^sub>m unit_block r n i j P))" .
  qed
  also have "\<dots> = of_nat r * (\<Sum>x\<leftarrow>List.product [0..<r] [0..<r]. f (?g x))"
    by (simp add: sum_list_product_upt sum_distrib_left split_beta)
  also have "(\<Sum>x\<leftarrow>List.product [0..<r] [0..<r]. f (?g x)) = f (msum (r * n) (r * n) ?g (List.product [0..<r] [0..<r]))"
    by (rule lin_fun_msum[OF TS f gc, symmetric])
  also have "msum (r * n) (r * n) ?g (List.product [0..<r] [0..<r]) = Tensor.tensor_mat (rank1 w) P"
  proof (rule eq_matI)
    fix x y assume "x < dim_row (Tensor.tensor_mat (rank1 w) P)" "y < dim_col (Tensor.tensor_mat (rank1 w) P)"
    hence x: "x < r * n" and y: "y < r * n" using P w by simp_all
    have r: "0 < r" using x by (cases r) auto
    have xd: "x div n < r" and yd: "y div n < r" using x y n by (simp_all add: less_mult_imp_div_less mult.commute)
    have "msum (r * n) (r * n) ?g (List.product [0..<r] [0..<r]) $$ (x,y)
          = (\<Sum>i<r. \<Sum>j<r. if i = x div n \<and> j = y div n then ?c (x div n) (y div n) * P $$ (x mod n, y mod n) else 0)"
      unfolding msum_index[OF gc x y] sum_list_product_upt
      by (intro sum.cong refl) (auto simp: unit_block_def x y)
    also have "\<dots> = ?c (x div n) (y div n) * P $$ (x mod n, y mod n)" by (rule sum_delta2[OF xd yd])
    also have "\<dots> = Tensor.tensor_mat (rank1 w) P $$ (x,y)"
      by (subst index_tensor_mat[where rA=r and cA=r and rB=n and cB=n]) (use x y w P r n xd yd in \<open>simp_all add: rank1_def\<close>)
    finally show "msum (r * n) (r * n) ?g (List.product [0..<r] [0..<r]) $$ (x,y) = Tensor.tensor_mat (rank1 w) P $$ (x,y)" .
  qed (use msum_carrier[OF gc] P w in simp_all)
  finally show ?thesis .
qed

subsection \<open>Proposition (Day 27): $f(\mathrm{Sep})\ge0$ iff $\Phi_f$ is positive\<close>

theorem positive_map_iff_sep_nonneg:
  fixes f :: "complex Matrix.mat \<Rightarrow> complex"
  assumes f: "lin_fun_on (carrier_mat (r * n) (r * n)) f" and r: "0 < r" and n: "0 < n"
  shows "positive_map n r (arveson_map n r f)
         \<longleftrightarrow> (\<forall>Q P. Q \<in> carrier_mat r r \<longrightarrow> psd Q \<longrightarrow> P \<in> carrier_mat n n \<longrightarrow> psd P
               \<longrightarrow> 0 \<le> f (Tensor.tensor_mat Q P))"
proof
  assume pos: "positive_map n r (arveson_map n r f)"
  show "\<forall>Q P. Q \<in> carrier_mat r r \<longrightarrow> psd Q \<longrightarrow> P \<in> carrier_mat n n \<longrightarrow> psd P \<longrightarrow> 0 \<le> f (Tensor.tensor_mat Q P)"
  proof (intro allI impI)
    fix Q P :: "complex Matrix.mat" assume Qc: "Q \<in> carrier_mat r r" and Qp: "psd Q" and Pc: "P \<in> carrier_mat n n" and Pp: "psd P"
    have PhiP: "psd (arveson_map n r f P)" using pos Pc Pp unfolding positive_map_def by blast
    obtain us where usd: "\<forall>u \<in> set us. dim_vec u = r" and Qe: "outer_sum r us = Q"
      using psd_kraus_decomp[OF Qc Qp] by blast
    have uc: "\<forall>u \<in> set us. u \<oslash> u \<in> carrier_mat r r" using usd by (auto intro: outer_prod_carrier)
    have Qm: "Q = msum r r (\<lambda>u. u \<oslash> u) us" unfolding Qe[symmetric] outer_sum_as_foldr[OF usd] msum_def ..
    have tc: "\<forall>u \<in> set us. Tensor.tensor_mat (u \<oslash> u) P \<in> carrier_mat (r * n) (r * n)" using uc Pc by auto
    have "f (Tensor.tensor_mat Q P) = (\<Sum>u\<leftarrow>us. f (Tensor.tensor_mat (u \<oslash> u) P))"
      unfolding Qm tensor_msum_first[OF uc Pc n] by (rule lin_fun_msum[OF operator_system_full f tc])
    also have "0 \<le> \<dots>"
    proof (rule sum_list_nonneg)
      fix z assume "z \<in> set (map (\<lambda>u. f (Tensor.tensor_mat (u \<oslash> u) P)) us)"
      then obtain u where u: "u \<in> set us" and z: "z = f (Tensor.tensor_mat (u \<oslash> u) P)" by auto
      have cu: "dim_vec (conjugate u) = r" using usd u by simp
      have q: "\<langle>conjugate u | arveson_map n r f P *\<^sub>v conjugate u\<rangle> = of_nat r * z"
        unfolding z rank1_outer[symmetric] by (rule quad_arveson_map[OF f cu Pc n])
      have "\<langle>conjugate u | arveson_map n r f P *\<^sub>v conjugate u\<rangle> \<in> \<real> \<and> 0 \<le> Re \<langle>conjugate u | arveson_map n r f P *\<^sub>v conjugate u\<rangle>"
        using PhiP psd_iff_quad_form_nonneg[of "arveson_map n r f P" r] cu by simp
      hence "Im (of_nat r * z) = 0" "0 \<le> Re (of_nat r * z)" unfolding q by (simp_all add: complex_is_Real_iff)
      thus "0 \<le> z" using r by (simp add: less_eq_complex_def zero_le_mult_iff)
    qed
    finally show "0 \<le> f (Tensor.tensor_mat Q P)" .
  qed
next
  assume sep: "\<forall>Q P. Q \<in> carrier_mat r r \<longrightarrow> psd Q \<longrightarrow> P \<in> carrier_mat n n \<longrightarrow> psd P \<longrightarrow> 0 \<le> f (Tensor.tensor_mat Q P)"
  show "positive_map n r (arveson_map n r f)" unfolding positive_map_def
  proof (intro conjI allI impI)
    fix P :: "complex Matrix.mat" assume Pc: "P \<in> carrier_mat n n" and Pp: "psd P"
    show "psd (arveson_map n r f P)"
      unfolding psd_iff_quad_form_nonneg[OF arveson_map_carrier]
    proof (intro allI impI)
      fix v :: "complex Matrix.vec" assume v: "dim_vec v = r"
      have "0 \<le> f (Tensor.tensor_mat (rank1 v) P)" using sep rank1_carrier[of v] rank1_psd Pc Pp v by auto
      hence "Im (f (Tensor.tensor_mat (rank1 v) P)) = 0" "0 \<le> Re (f (Tensor.tensor_mat (rank1 v) P))"
        by (simp_all add: less_eq_complex_def)
      thus "\<langle>v | arveson_map n r f P *\<^sub>v v\<rangle> \<in> \<real> \<and> 0 \<le> Re \<langle>v | arveson_map n r f P *\<^sub>v v\<rangle>"
        unfolding quad_arveson_map[OF f v Pc n] by (simp add: complex_is_Real_iff)
    qed
  qed simp
qed

subsection \<open>Proposition (Day 27): positive maps keep separable matrices positive\<close>

lemma block_tensor:
  fixes Q P :: "complex Matrix.mat"
  assumes Q: "Q \<in> carrier_mat r r" and P: "P \<in> carrier_mat n n" and a: "a < r" and b: "b < r"
  shows "block_of_mat n (Tensor.tensor_mat Q P) a b = Q $$ (a,b) \<cdot>\<^sub>m P"
proof (rule eq_matI)
  fix k l assume "k < dim_row (Q $$ (a,b) \<cdot>\<^sub>m P)" "l < dim_col (Q $$ (a,b) \<cdot>\<^sub>m P)"
  hence k: "k < n" and l: "l < n" using P by simp_all
  have "Tensor.tensor_mat Q P $$ (a * n + k, b * n + l)
        = Q $$ ((a * n + k) div n, (b * n + l) div n) * P $$ ((a * n + k) mod n, (b * n + l) mod n)"
  proof -
    have r0: "0 < r" using a by simp
    show ?thesis by (rule index_tensor_mat[where rA=r and cA=r and rB=n and cB=n]) (use Q P mult_index_lt[OF a k] mult_index_div_mod[OF k] mult_index_lt[OF b l] mult_index_div_mod[OF l] a k r0 in simp_all)
  qed
  thus "block_of_mat n (Tensor.tensor_mat Q P) a b $$ (k,l) = (Q $$ (a,b) \<cdot>\<^sub>m P) $$ (k,l)"
    using mult_index_lt[OF a k] mult_index_div_mod[OF k] mult_index_lt[OF b l] mult_index_div_mod[OF l] k l P by (simp add: block_of_mat_index)
qed (use P in simp_all)

lemma amplification_tensor:
  fixes Q P :: "complex Matrix.mat" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and Q: "Q \<in> carrier_mat r r" and P: "P \<in> carrier_mat n n"
      and d: "0 < d" and n: "0 < n"
  shows "amplification n d r \<Phi> (Tensor.tensor_mat Q P) = Tensor.tensor_mat Q (\<Phi> P)"
proof (rule eq_matI)
  have PhiP: "\<Phi> P \<in> carrier_mat d d" using L P unfolding lin_on_def by blast
  show "dim_row (amplification n d r \<Phi> (Tensor.tensor_mat Q P)) = dim_row (Tensor.tensor_mat Q (\<Phi> P))"
    "dim_col (amplification n d r \<Phi> (Tensor.tensor_mat Q P)) = dim_col (Tensor.tensor_mat Q (\<Phi> P))"
    using Q PhiP carrier_matD[OF amplification_carrier[of n d r \<Phi> "Tensor.tensor_mat Q P"]] by simp_all
  fix x y assume "x < dim_row (Tensor.tensor_mat Q (\<Phi> P))" "y < dim_col (Tensor.tensor_mat Q (\<Phi> P))"
  hence x: "x < r * d" and y: "y < r * d" using Q PhiP by simp_all
  have xd: "x div d < r" "y div d < r" using x y d by (simp_all add: less_mult_imp_div_less mult.commute)
  have xm: "x mod d < d" "y mod d < d" using d by simp_all
  have "\<Phi> (Q $$ (x div d, y div d) \<cdot>\<^sub>m P) = Q $$ (x div d, y div d) \<cdot>\<^sub>m \<Phi> P" using L P unfolding lin_on_def by blast
  hence "amplification n d r \<Phi> (Tensor.tensor_mat Q P) $$ (x,y) = Q $$ (x div d, y div d) * \<Phi> P $$ (x mod d, y mod d)"
    using x y xm PhiP by (simp add: amplification_def block_tensor[OF Q P xd])
  also have "\<dots> = Tensor.tensor_mat Q (\<Phi> P) $$ (x,y)"
    by (rule index_tensor_mat[where rA=r and cA=r and rB=d and cB=d, symmetric]) (use Q PhiP x y d xd in simp_all)
  finally show "amplification n d r \<Phi> (Tensor.tensor_mat Q P) $$ (x,y) = Tensor.tensor_mat Q (\<Phi> P) $$ (x,y)" .
qed

lemma amplification_lin:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and A: "A \<in> carrier_mat (p * n) (p * n)" and B: "B \<in> carrier_mat (p * n) (p * n)"
  shows "amplification n d p \<Phi> (A + B) = amplification n d p \<Phi> A + amplification n d p \<Phi> B"
    and "amplification n d p \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m amplification n d p \<Phi> A"
proof -
  have Pc: "\<And>M. M \<in> carrier_mat n n \<Longrightarrow> \<Phi> M \<in> carrier_mat d d" using L unfolding lin_on_def by blast
  have Padd: "\<And>M M'. M \<in> carrier_mat n n \<Longrightarrow> M' \<in> carrier_mat n n \<Longrightarrow> \<Phi> (M + M') = \<Phi> M + \<Phi> M'"
    using L unfolding lin_on_def by blast
  have Psm: "\<And>M k. M \<in> carrier_mat n n \<Longrightarrow> \<Phi> (k \<cdot>\<^sub>m M) = k \<cdot>\<^sub>m \<Phi> M"
    using L unfolding lin_on_def by blast
  show "amplification n d p \<Phi> (A + B) = amplification n d p \<Phi> A + amplification n d p \<Phi> B"
  proof (rule eq_matI)
    fix x y assume "x < dim_row (amplification n d p \<Phi> A + amplification n d p \<Phi> B)"
      "y < dim_col (amplification n d p \<Phi> A + amplification n d p \<Phi> B)"
    hence x: "x < p * d" and y: "y < p * d" by (simp_all add: amplification_def)
    have d: "0 < d" using x by (cases d) auto
    have xd: "x div d < p" "y div d < p" using x y d by (simp_all add: less_mult_imp_div_less mult.commute)
    have "\<Phi> (block_of_mat n (A + B) (x div d) (y div d)) = \<Phi> (block_of_mat n A (x div d) (y div d)) + \<Phi> (block_of_mat n B (x div d) (y div d))"
      unfolding block_of_mat_add[OF A B xd] by (rule Padd) simp_all
    thus "amplification n d p \<Phi> (A + B) $$ (x,y) = (amplification n d p \<Phi> A + amplification n d p \<Phi> B) $$ (x,y)"
      using x y d Pc[of "block_of_mat n A (x div d) (y div d)"] Pc[of "block_of_mat n B (x div d) (y div d)"]
      by (simp add: amplification_def)
  qed (simp_all add: amplification_def)
  show "amplification n d p \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m amplification n d p \<Phi> A"
  proof (rule eq_matI)
    fix x y assume "x < dim_row (c \<cdot>\<^sub>m amplification n d p \<Phi> A)" "y < dim_col (c \<cdot>\<^sub>m amplification n d p \<Phi> A)"
    hence x: "x < p * d" and y: "y < p * d" by (simp_all add: amplification_def)
    have d: "0 < d" using x by (cases d) auto
    have xd: "x div d < p" "y div d < p" using x y d by (simp_all add: less_mult_imp_div_less mult.commute)
    have "\<Phi> (block_of_mat n (c \<cdot>\<^sub>m A) (x div d) (y div d)) = c \<cdot>\<^sub>m \<Phi> (block_of_mat n A (x div d) (y div d))"
      unfolding block_of_mat_smult[OF A xd] by (rule Psm) simp
    thus "amplification n d p \<Phi> (c \<cdot>\<^sub>m A) $$ (x,y) = (c \<cdot>\<^sub>m amplification n d p \<Phi> A) $$ (x,y)"
      using x y d Pc[of "block_of_mat n A (x div d) (y div d)"] by (simp add: amplification_def)
  qed (simp_all add: amplification_def)
qed

lemma unwrap_lm_scaleR_mat:
  fixes R :: "(complex, 'k :: finite, 'k) lmat"
  shows "unwrap_lm (u *\<^sub>R R) = complex_of_real u \<cdot>\<^sub>m unwrap_lm R"
  by (rule eq_matI) (auto simp: scaleR_conv_of_real)

theorem positive_map_separable:
  fixes R :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes L: "lin_on CARD('p) d (carrier_mat CARD('p) CARD('p)) \<Phi>" and pos: "positive_map CARD('p) d \<Phi>"
      and d: "0 < d" and R: "R \<in> separable_cone_lmat"
  shows "psd (amplification CARD('p) d CARD('m) \<Phi> (unwrap_lm R))"
proof -
  let ?n = "CARD('p)" and ?r = "CARD('m)"
  define C where "C = {R :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat. psd (amplification ?n d ?r \<Phi> (unwrap_lm R))}"
  have Rc: "\<And>R :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat. unwrap_lm R \<in> carrier_mat (?r * ?n) (?r * ?n)"
  proof -
    fix R :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat"
    have "unwrap_lm R \<in> carrier_mat CARD('m \<times> 'p) CARD('m \<times> 'p)" by (rule unwrap_lm_carrier)
    thus "unwrap_lm R \<in> carrier_mat (?r * ?n) (?r * ?n)" by (simp only: card_prod)
  qed
  have ac: "\<And>A. amplification ?n d ?r \<Phi> A \<in> carrier_mat (?r * d) (?r * d)" by (rule amplification_carrier)
  have gen: "separable_lmat_gen \<subseteq> C"
  proof
    fix x :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat" assume "x \<in> separable_lmat_gen"
    then obtain \<sigma> :: "(complex, 'm, 'm) lmat" and \<tau> :: "(complex, 'p, 'p) lmat"
      where x: "x = tensor_lmat \<sigma> \<tau>" and ps: "psd (unwrap_lm \<sigma>)" and pt: "psd (unwrap_lm \<tau>)"
      unfolding separable_lmat_gen_def by auto
    have sc: "unwrap_lm \<sigma> \<in> carrier_mat ?r ?r" and tc: "unwrap_lm \<tau> \<in> carrier_mat ?n ?n" by simp_all
    have "amplification ?n d ?r \<Phi> (unwrap_lm x) = Tensor.tensor_mat (unwrap_lm \<sigma>) (\<Phi> (unwrap_lm \<tau>))"
      unfolding x unwrap_lm_tensor_lmat by (rule amplification_tensor[OF L sc tc d]) simp
    moreover have "psd (Tensor.tensor_mat (unwrap_lm \<sigma>) (\<Phi> (unwrap_lm \<tau>)))"
      using psd_tensor[OF sc _ ps, of "\<Phi> (unwrap_lm \<tau>)" d] pos tc pt unfolding positive_map_def by blast
    ultimately show "x \<in> C" unfolding C_def by simp
  qed
  have cc: "convex_cone C"
    unfolding convex_cone_def convex_def conic_def
  proof (intro conjI ballI allI impI)
    have z0: "unwrap_lm (0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat) = 0\<^sub>m (?r * ?n) (?r * ?n)"
      by (simp add: card_prod)
    have zb: "\<And>a b. a < ?r \<Longrightarrow> b < ?r \<Longrightarrow> block_of_mat ?n (0\<^sub>m (?r * ?n) (?r * ?n)) a b = 0\<^sub>m ?n ?n"
    proof -
      fix a b assume a: "a < ?r" and b: "b < ?r"
      show "block_of_mat ?n (0\<^sub>m (?r * ?n) (?r * ?n)) a b = 0\<^sub>m ?n ?n"
      proof (rule eq_matI)
        fix k l assume "k < dim_row (0\<^sub>m ?n ?n :: complex Matrix.mat)" "l < dim_col (0\<^sub>m ?n ?n :: complex Matrix.mat)"
        hence k: "k < ?n" and l: "l < ?n" by simp_all
        show "block_of_mat ?n (0\<^sub>m (?r * ?n) (?r * ?n)) a b $$ (k,l) = (0\<^sub>m ?n ?n :: complex Matrix.mat) $$ (k,l)"
          using mult_index_lt[OF a k] mult_index_lt[OF b l] k l by (simp add: block_of_mat_index)
      qed simp_all
    qed
    have Phi0: "\<Phi> (0\<^sub>m ?n ?n) = 0\<^sub>m d d" by (rule lin_on_zero[OF operator_system_full L])
    have "amplification ?n d ?r \<Phi> (unwrap_lm (0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)) = 0\<^sub>m (?r * d) (?r * d)"
    proof (rule eq_matI)
      fix x y assume "x < dim_row (0\<^sub>m (?r * d) (?r * d) :: complex Matrix.mat)" "y < dim_col (0\<^sub>m (?r * d) (?r * d) :: complex Matrix.mat)"
      hence x: "x < ?r * d" and y: "y < ?r * d" by simp_all
      have xd: "x div d < ?r" "y div d < ?r" using x y d by (simp_all add: less_mult_imp_div_less mult.commute)
      show "amplification ?n d ?r \<Phi> (unwrap_lm (0 :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat)) $$ (x,y) = (0\<^sub>m (?r * d) (?r * d) :: complex Matrix.mat) $$ (x,y)"
        unfolding z0 using x y d zb[OF xd] Phi0 by (simp add: amplification_def)
    qed (simp_all add: amplification_def)
    hence "0 \<in> C" unfolding C_def by simp
    thus "C \<noteq> {}" by blast
  next
    fix x y :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat" and u v :: real
    assume x: "x \<in> C" and y: "y \<in> C" and u: "0 \<le> u" and v: "0 \<le> v" and uv: "u + v = 1"
    have "amplification ?n d ?r \<Phi> (unwrap_lm (u *\<^sub>R x + v *\<^sub>R y))
          = complex_of_real u \<cdot>\<^sub>m amplification ?n d ?r \<Phi> (unwrap_lm x) + complex_of_real v \<cdot>\<^sub>m amplification ?n d ?r \<Phi> (unwrap_lm y)"
      unfolding unwrap_lm_plus unwrap_lm_scaleR_mat
        amplification_lin(1)[OF L smult_carrier_mat[OF Rc] smult_carrier_mat[OF Rc]]
        amplification_lin(2)[OF L Rc Rc] ..
    moreover have "psd (complex_of_real u \<cdot>\<^sub>m amplification ?n d ?r \<Phi> (unwrap_lm x) + complex_of_real v \<cdot>\<^sub>m amplification ?n d ?r \<Phi> (unwrap_lm y))"
    proof -
      have px: "psd (amplification ?n d ?r \<Phi> (unwrap_lm x))" and py: "psd (amplification ?n d ?r \<Phi> (unwrap_lm y))"
        using x y unfolding C_def by simp_all
      show ?thesis
        by (rule psd_add_psd[OF psd_smult_nonneg[OF u px ac] psd_smult_nonneg[OF v py ac] smult_carrier_mat[OF ac] smult_carrier_mat[OF ac]])
    qed
    ultimately show "u *\<^sub>R x + v *\<^sub>R y \<in> C" unfolding C_def by simp
  next
    fix x :: "(complex, 'm \<times> 'p, 'm \<times> 'p) lmat" and c :: real assume x: "x \<in> C" and c: "0 \<le> c"
    have "amplification ?n d ?r \<Phi> (unwrap_lm (c *\<^sub>R x)) = complex_of_real c \<cdot>\<^sub>m amplification ?n d ?r \<Phi> (unwrap_lm x)"
      unfolding unwrap_lm_scaleR_mat by (rule amplification_lin(2)[OF L Rc Rc])
    moreover have "psd (complex_of_real c \<cdot>\<^sub>m amplification ?n d ?r \<Phi> (unwrap_lm x))"
      using x unfolding C_def by (intro psd_smult_nonneg[OF c _ ac]) simp
    ultimately show "c *\<^sub>R x \<in> C" unfolding C_def by simp
  qed
  have "separable_cone_lmat \<subseteq> C" unfolding separable_cone_lmat_def by (rule hull_minimal[where S=convex_cone, OF gen cc])
  thus ?thesis using R unfolding C_def by blast
qed

subsection \<open>Theorem (Day 28): the positive-map criterion\<close>

text \<open>A Hermitian $R\in M_r(M_n)$ is separable iff $\Phi^{(r)}(R)\ge0$ for every positive
$\Phi:M_n\to M_r$.\<close>

theorem separable_iff_positive_maps:
  fixes R :: "(complex, 'm :: finite \<times> 'p :: finite, 'm \<times> 'p) lmat"
  assumes Rh: "hermitian (unwrap_lm R)"
  shows "R \<in> separable_cone_lmat \<longleftrightarrow>
         (\<forall>\<Phi>. lin_on CARD('p) CARD('m) (carrier_mat CARD('p) CARD('p)) \<Phi> \<longrightarrow> positive_map CARD('p) CARD('m) \<Phi>
              \<longrightarrow> psd (amplification CARD('p) CARD('m) CARD('m) \<Phi> (unwrap_lm R)))"
proof
  assume "R \<in> separable_cone_lmat"
  thus "\<forall>\<Phi>. lin_on CARD('p) CARD('m) (carrier_mat CARD('p) CARD('p)) \<Phi> \<longrightarrow> positive_map CARD('p) CARD('m) \<Phi>
              \<longrightarrow> psd (amplification CARD('p) CARD('m) CARD('m) \<Phi> (unwrap_lm R))"
    using positive_map_separable[where d="CARD('m)" and R=R] by simp
next
  let ?n = "CARD('p)" and ?r = "CARD('m)"
  assume all: "\<forall>\<Phi>. lin_on ?n ?r (carrier_mat ?n ?n) \<Phi> \<longrightarrow> positive_map ?n ?r \<Phi>
              \<longrightarrow> psd (amplification ?n ?r ?r \<Phi> (unwrap_lm R))"
  show "R \<in> separable_cone_lmat"
  proof (rule ccontr)
    assume nR: "R \<notin> separable_cone_lmat"
    then obtain W where Wc: "W \<in> carrier_mat CARD('m \<times> 'p) CARD('m \<times> 'p)" and Wh: "hermitian W"
      and Wsep: "\<forall>\<sigma> :: (complex, 'm \<times> 'p, 'm \<times> 'p) lmat. \<sigma> \<in> separable_cone_lmat \<longrightarrow> 0 \<le> Re (Tr (W * unwrap_lm \<sigma>))"
      and WR: "\<not> 0 \<le> Re (Tr (W * unwrap_lm R))"
      using separable_iff_witness[OF Rh] by blast
    have Wc': "W \<in> carrier_mat (?r * ?n) (?r * ?n)" using Wc by (simp add: card_prod)
    define f where "f = (\<lambda>A. Tr (W * A))"
    have f: "lin_fun_on (carrier_mat (?r * ?n) (?r * ?n)) f"
      unfolding lin_fun_on_def f_def
    proof (intro conjI ballI allI)
      fix A B :: "complex Matrix.mat" assume A: "A \<in> carrier_mat (?r * ?n) (?r * ?n)" and B: "B \<in> carrier_mat (?r * ?n) (?r * ?n)"
      show "Tr (W * (A + B)) = Tr (W * A) + Tr (W * B)"
        unfolding mult_add_distrib_mat[OF Wc' A B] by (rule Tr_add) (use Wc' A B in simp_all)
    next
      fix A :: "complex Matrix.mat" and c :: complex assume A: "A \<in> carrier_mat (?r * ?n) (?r * ?n)"
      show "Tr (W * (c \<cdot>\<^sub>m A)) = c * Tr (W * A)" unfolding mult_smult_distrib[OF Wc' A] Tr_smult ..
    qed
    have r0: "0 < ?r" and n0: "0 < ?n" by simp_all
    define \<Phi> where "\<Phi> = arveson_map ?n ?r f"
    have Lphi: "lin_on ?n ?r (carrier_mat ?n ?n) \<Phi>"
      unfolding \<Phi>_def by (rule arveson_map_lin[OF operator_system_full]) (use f in \<open>simp add: Mp_full\<close>)
    have pphi: "positive_map ?n ?r \<Phi>"
      unfolding \<Phi>_def positive_map_iff_sep_nonneg[OF f r0 n0]
    proof (intro allI impI)
      fix Q P :: "complex Matrix.mat" assume Qc: "Q \<in> carrier_mat ?r ?r" and Qp: "psd Q" and Pc: "P \<in> carrier_mat ?n ?n" and Pp: "psd P"
      define \<sigma> where "\<sigma> = (wrap_lm Q :: (complex, 'm, 'm) lmat)"
      define \<tau> where "\<tau> = (wrap_lm P :: (complex, 'p, 'p) lmat)"
      have us: "unwrap_lm \<sigma> = Q" and ut: "unwrap_lm \<tau> = P" unfolding \<sigma>_def \<tau>_def
        using Qc Pc by (simp_all add: wrap_lm_inverse)
      have "tensor_lmat \<sigma> \<tau> \<in> separable_lmat_gen" unfolding separable_lmat_gen_def using us ut Qp Pp by auto
      hence "tensor_lmat \<sigma> \<tau> \<in> separable_cone_lmat" unfolding separable_cone_lmat_def by (rule hull_inc)
      hence re: "0 \<le> Re (f (Tensor.tensor_mat Q P))" using Wsep unfolding f_def by (metis unwrap_lm_tensor_lmat us ut)
      have tc: "Tensor.tensor_mat Q P \<in> carrier_mat (?r * ?n) (?r * ?n)" using Qc Pc by simp
      have "hermitian (Tensor.tensor_mat Q P)" by (rule psd_hermitian[OF psd_tensor[OF Qc Pc Qp Pp]])
      hence "f (Tensor.tensor_mat Q P) \<in> \<real>" unfolding f_def by (rule Tr_herm_mult_real[OF Wc' tc Wh])
      thus "0 \<le> f (Tensor.tensor_mat Q P)" using re by (simp add: less_eq_complex_def complex_is_Real_iff)
    qed
    have psdR: "psd (amplification ?n ?r ?r \<Phi> (unwrap_lm R))" using all Lphi pphi by blast
    have "unwrap_lm R \<in> carrier_mat CARD('m \<times> 'p) CARD('m \<times> 'p)" by (rule unwrap_lm_carrier)
    hence Rc: "unwrap_lm R \<in> carrier_mat (?r * ?n) (?r * ?n)" by (simp only: card_prod)
    define v where "v = Matrix.vec (?r * ?r) (\<lambda>x. if x div ?r = x mod ?r then 1 else (0::complex))"
    have vd: "dim_vec v = ?r * ?r" unfolding v_def by simp
    have "\<langle>v | amplification ?n ?r ?r \<Phi> (unwrap_lm R) *\<^sub>v v\<rangle> = (\<Sum>i<?r. \<Sum>j<?r. \<Phi> (block_of_mat ?n (unwrap_lm R) i j) $$ (i,j))"
      unfolding v_def by (rule diag_quad_amplification)
    also have "\<dots> = of_nat ?r * arveson_functional ?n ?r \<Phi> (unwrap_lm R)" unfolding arveson_functional_def by simp
    also have "arveson_functional ?n ?r \<Phi> (unwrap_lm R) = f (unwrap_lm R)"
      unfolding \<Phi>_def by (rule arveson_functional_of_map[OF operator_system_full]) (use f Rc in \<open>simp_all add: Mp_full\<close>)
    finally have q: "\<langle>v | amplification ?n ?r ?r \<Phi> (unwrap_lm R) *\<^sub>v v\<rangle> = of_nat ?r * Tr (W * unwrap_lm R)" unfolding f_def .
    have "0 \<le> Re (\<langle>v | amplification ?n ?r ?r \<Phi> (unwrap_lm R) *\<^sub>v v\<rangle>)"
      using psdR psd_iff_quad_form_nonneg[OF amplification_carrier] vd by blast
    hence "0 \<le> Re (Tr (W * unwrap_lm R))" unfolding q by (simp add: zero_le_mult_iff)
    thus False using WR by simp
  qed
qed

end
