(*  Title:   Day27_Detecting_Entanglement.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 31 October 2011 (Day 27)
*)

theory Day27_Detecting_Entanglement
  imports Day25_Arveson_Correspondence Day26_Separability
begin

section \<open>Day 27 (31 October 2011): positive maps detect entanglement; convex cones\<close>

text \<open>For $R\in M_r(M_n)$ (block size $n$), $\Phi^{(r)}(R)\ge0$ for every positive $\Phi$ when $R$
is separable (D27-1), so a positive map with $\Phi^{(r)}(R)\not\ge0$ shows that $R$ is
entangled; the transpose does so for the notes' examples (D27-2).  A functional $f$ on
$M_r(M_n)$ is non-negative on the separable matrices iff $\Phi_f$ is positive (D27-3).  That
every entangled $R$ is detected by some positive map needs convex cones:
\begin{notestheorem}
Let $V$ be a finite-dimensional real vector space, $K\subseteq V$ closed and convex, $y\notin K$.
Then there is a linear $f:V\to\R$ and $\alpha\in\R$ with $f(y)<\alpha\le f(K)$; if $C$ is a closed
cone and $w\notin C$ there is $f$ with $f(w)<0\le f(C)$.
\end{notestheorem}
This is HOL-Analysis' \<open>separating_hyperplane_closed_point\<close>; Day 28 applies it to the separable
cone, once the cone is shown to be closed.\<close>

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

text \<open>\<open>rank1 w\<close> has entries $\overline{w_i}\,w_j$: it is $\ketbra uu$ for $u=\overline w$, hence positive.\<close>

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

subsection \<open>$f(\mathrm{Sep})\ge0$ iff $\Phi_f$ is positive (D27-3)\<close>

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

subsection \<open>Positive maps keep separable matrices positive (D27-1)\<close>

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

subsection \<open>Entangled matrices detected by the transpose (D27-2)\<close>

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

corollary entangled_example_choi_seed:
  fixes R :: "(complex, 'p :: finite \<times> 'p, 'p \<times> 'p) lmat"
  assumes n: "2 \<le> CARD('p)" and R: "unwrap_lm R = choi_seed CARD('p)"
  shows "psd (unwrap_lm R) \<and> R \<notin> separable_cone_lmat"
  by (rule unit_blocks_entangled[where f = id]) (use n R in \<open>simp_all add: choi_seed_unit_blocks\<close>)

end
