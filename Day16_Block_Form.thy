theory Day16_Block_Form
  imports Day25_Arveson_Correspondence Day06_Tensor_Coordinates
begin

section \<open>Day 16: $H_A\otimes H_B\cong H_A^{(p)}$ and $L(H_A\otimes H_B)\cong M_p(L(H_A))$ (D16-2)\<close>

text \<open>The notes identify $H_A\otimes H_B$ with $p$ copies of $H_A$ through
$\sum_ih_i\otimes f_i\leftrightarrow(h_1,\dots,h_p)$, with $\|v\|^2=\sum_i\|h_i\|^2$, and an operator $X$ with
its block matrix $(X_{ij})$ over $L(H_A)$, acting by $(h_j)\mapsto(\sum_jX_{ij}h_j)$, so that
$X=\sum_{i,j}X_{ij}\otimes E_{ij}$, $\tr_B(X)=X_{11}+\dots+X_{pp}$ and $\tr_A(X)=(\Tr X_{ij})$.  Here
$f_i=e_i$, and indices are A-major as everywhere in the development.\<close>

text \<open>With $H_A=\C^m$, $H_B=\C^p$ and A-major indices $a p+i$, the part of $v$ along $e_i$ is
$h_i=(v_{ap+i})_a\in H_A$, the $i$-th column of \<^term>\<open>vec_to_mat m p v\<close>: for $m=2$, $p=3$,
$h_0=(v_0,v_3)$, $h_1=(v_1,v_4)$ and $h_2=(v_2,v_5)$.\<close>

text \<open>Likewise an operator $X$ on $\C^{mp}$ has the blocks $X_{ij}=(X_{ap+i,\,bp+j})_{a,b}\in L(H_A)$:
the rows of $X$ with second index $i$ and its columns with second index $j$.  For $m=p=2$ the
indices $0,2$ have second index $0$ and $1,3$ have second index $1$, so
\[
  X=\begin{pmatrix}x_{00}&x_{01}&x_{02}&x_{03}\\ x_{10}&x_{11}&x_{12}&x_{13}\\
    x_{20}&x_{21}&x_{22}&x_{23}\\ x_{30}&x_{31}&x_{32}&x_{33}\end{pmatrix},\qquad
  X_{00}=\begin{pmatrix}x_{00}&x_{02}\\ x_{20}&x_{22}\end{pmatrix},\quad
  X_{01}=\begin{pmatrix}x_{01}&x_{03}\\ x_{21}&x_{23}\end{pmatrix}.
\]
The blocks interleave because the second index runs fastest.  $X_{ij}$ carries the part of $v$
along $e_j$ to the part of $Xv$ along $e_i$.\<close>

definition block :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "block m p X i j = Matrix.mat m m (\<lambda>(a, b). X $$ (a * p + i, b * p + j))"

lemma block_carrier [simp]: "block m p X i j \<in> carrier_mat m m"
  by (simp add: block_def)

lemma block_dims [simp]: "dim_row (block m p X i j) = m" "dim_col (block m p X i j) = m"
  by (simp_all add: block_def)

lemma sum_mp_reindex:
  fixes f :: "nat \<Rightarrow> complex"
  shows "(\<Sum>r<m * p. f r) = (\<Sum>b<m. \<Sum>j<p. f (b * p + j))"
proof -
  have bij: "bij_betw (\<lambda>(b, j). b * p + j) ({..<m} \<times> {..<p}) {..<m * p}"
  proof (rule bij_betwI[where g = "\<lambda>r. (r div p, r mod p)"])
    show "(\<lambda>(b, j). b * p + j) \<in> {..<m} \<times> {..<p} \<rightarrow> {..<m * p}" using mult_index_lt by auto
    show "(\<lambda>r. (r div p, r mod p)) \<in> {..<m * p} \<rightarrow> {..<m} \<times> {..<p}"
    proof
      fix r assume "r \<in> {..<m * p}"
      hence r: "r < m * p" by simp
      hence p: "0 < p" by (cases p) auto
      show "(r div p, r mod p) \<in> {..<m} \<times> {..<p}" using r p by (simp add: less_mult_imp_div_less)
    qed
    show "\<And>x. x \<in> {..<m} \<times> {..<p} \<Longrightarrow> (\<lambda>r. (r div p, r mod p)) ((\<lambda>(b, j). b * p + j) x) = x"
      by (auto simp: mult_index_div_mod)
    show "\<And>y. y \<in> {..<m * p} \<Longrightarrow> (\<lambda>(b, j). b * p + j) ((\<lambda>r. (r div p, r mod p)) y) = y" by simp
  qed
  have "(\<Sum>r<m * p. f r) = (\<Sum>x \<in> {..<m} \<times> {..<p}. f ((\<lambda>(b, j). b * p + j) x))"
    using sum.reindex_bij_betw[OF bij, of f] by simp
  also have "\<dots> = (\<Sum>b<m. \<Sum>j<p. f (b * p + j))" by (simp add: sum.cartesian_product split_def)
  finally show ?thesis .
qed

text \<open>$H_A\otimes H_B\cong H_A^{(p)}$ isometrically: $\langle v|w\rangle=\sum_i\langle h_i|k_i\rangle$.\<close>

theorem vec_to_mat_cols_inner_prod:
  assumes v: "dim_vec v = m * p" and w: "dim_vec w = m * p"
  shows "Quantum.inner_prod v w = (\<Sum>i<p. Quantum.inner_prod (Matrix.col (vec_to_mat m p v) i) (Matrix.col (vec_to_mat m p w) i))"
proof -
  have "Quantum.inner_prod v w = (\<Sum>r<m * p. cnj (v $ r) * w $ r)" using w by (simp add: Quantum.inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>b<m. \<Sum>i<p. cnj (v $ (b * p + i)) * w $ (b * p + i))" by (rule sum_mp_reindex)
  also have "\<dots> = (\<Sum>i<p. \<Sum>b<m. cnj (v $ (b * p + i)) * w $ (b * p + i))" by (rule sum.swap)
  also have "\<dots> = (\<Sum>i<p. Quantum.inner_prod (Matrix.col (vec_to_mat m p v) i) (Matrix.col (vec_to_mat m p w) i))"
    by (rule sum.cong) (simp_all add: Quantum.inner_prod_def col_vec_to_mat atLeast0LessThan)
  finally show ?thesis .
qed

text \<open>$v=\sum_ih_i\otimes e_i$.\<close>

theorem vec_to_mat_cols_expansion:
  assumes v: "dim_vec v = m * p"
  shows "v = tensor_combination (m * p) (cols (vec_to_mat m p v)) (map (unit_vec p) [0..<p])"
proof (rule eq_vecI)
  have xs: "\<forall>x \<in> set (cols (vec_to_mat m p v)). dim_vec x = m" by (auto simp: cols_def)
  have ys: "\<forall>y \<in> set (map (unit_vec p) [0..<p] :: complex Matrix.vec list). dim_vec y = p" by simp
  fix r assume "r < dim_vec (tensor_combination (m * p) (cols (vec_to_mat m p v)) (map (unit_vec p) [0..<p]))"
  hence r: "r < m * p" by simp
  have p: "0 < p" using r by (cases p) auto
  have rd: "r div p < m" using r by (simp add: less_mult_imp_div_less mult.commute)
  have "tensor_combination (m * p) (cols (vec_to_mat m p v)) (map (unit_vec p) [0..<p]) $ r
        = (\<Sum>j<p. Matrix.col (vec_to_mat m p v) j $ (r div p) * unit_vec p j $ (r mod p))"
    using tensor_combination_index[OF xs ys _ r] by simp
  also have "\<dots> = (\<Sum>j<p. if j = r mod p then v $ (r div p * p + j) else 0)"
    by (rule sum.cong) (use p rd in \<open>auto simp: col_vec_to_mat unit_vec_def\<close>)
  also have "\<dots> = v $ r" using p by simp
  finally show "v $ r = tensor_combination (m * p) (cols (vec_to_mat m p v)) (map (unit_vec p) [0..<p]) $ r" ..
qed (use v in simp)

text \<open>The block action: the $i$-th coordinate of $Xv$ is $\sum_jX_{ij}h_j$.\<close>

theorem block_action:
  assumes X: "X \<in> carrier_mat (m * p) (m * p)" and v: "dim_vec v = m * p" and i: "i < p"
  shows "Matrix.col (vec_to_mat m p (X *\<^sub>v v)) i = Matrix.vec m (\<lambda>a. \<Sum>j<p. (block m p X i j *\<^sub>v Matrix.col (vec_to_mat m p v) j) $ a)"
proof (rule eq_vecI)
  fix a assume "a < dim_vec (Matrix.vec m (\<lambda>a. \<Sum>j<p. (block m p X i j *\<^sub>v Matrix.col (vec_to_mat m p v) j) $ a))"
  hence a: "a < m" by simp
  have r: "a * p + i < m * p" by (rule mult_index_lt[OF a i])
  have "Matrix.col (vec_to_mat m p (X *\<^sub>v v)) i $ a = (\<Sum>s<m * p. X $$ (a * p + i, s) * v $ s)"
    using X v r a by (simp add: col_vec_to_mat[OF i] scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>b<m. \<Sum>j<p. X $$ (a * p + i, b * p + j) * v $ (b * p + j))" by (rule sum_mp_reindex)
  also have "\<dots> = (\<Sum>j<p. \<Sum>b<m. X $$ (a * p + i, b * p + j) * v $ (b * p + j))" by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<p. (block m p X i j *\<^sub>v Matrix.col (vec_to_mat m p v) j) $ a)"
    using a by (intro sum.cong[OF refl]) (simp add: block_def col_vec_to_mat scalar_prod_def atLeast0LessThan)
  finally show "Matrix.col (vec_to_mat m p (X *\<^sub>v v)) i $ a = Matrix.vec m (\<lambda>a. \<Sum>j<p. (block m p X i j *\<^sub>v Matrix.col (vec_to_mat m p v) j) $ a) $ a"
    using a by simp
qed simp

text \<open>$L(H_A\otimes H_B)\cong M_p(L(H_A))$: $X=\sum_{i,j}X_{ij}\otimes E_{ij}$, and the blocks are unique.\<close>

lemma double_delta:
  fixes c :: complex and a b p q :: nat
  assumes "a < p" "b < q"
  shows "(\<Sum>i<p. \<Sum>j<q. if i = a \<and> j = b then c else 0) = c"
proof -
  have "\<And>i. (\<Sum>j<q. if i = a \<and> j = b then c else 0) = (if i = a then c else 0)"
    using assms(2) by (case_tac "i = a") simp_all
  thus ?thesis using assms(1) by simp
qed

lemma mat_unit_tensor_index:
  assumes A: "A \<in> carrier_mat m m" and r: "r < m * p" and s: "s < m * p" and i: "i < p" and j: "j < p"
  shows "(A \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) $$ (r, s) = (if r mod p = i \<and> s mod p = j then A $$ (r div p, s div p) else 0)"
proof -
  have p: "0 < p" using i by simp
  have m: "0 < m" using r by (cases m) auto
  have "(A \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) $$ (r, s) = A $$ (r div p, s div p) * E\<lbrakk>i,j ; p,p\<rbrakk> $$ (r mod p, s mod p)"
    by (rule index_tensor_mat[of _ m m _ p p]) (use A r s p m in simp_all)
  thus ?thesis using p by simp
qed

theorem tensor_block_decomposition:
  assumes X: "X \<in> carrier_mat (m * p) (m * p)"
  shows "X = msum (m * p) (m * p) (\<lambda>(i, j). block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) (List.product [0..<p] [0..<p])"
proof -
  have tc: "\<forall>x \<in> set (List.product [0..<p] [0..<p]). (\<lambda>(i, j). block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) x \<in> carrier_mat (m * p) (m * p)"
    by (auto intro!: carrier_matI)
  have Mc: "msum (m * p) (m * p) (\<lambda>(i, j). block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) (List.product [0..<p] [0..<p]) \<in> carrier_mat (m * p) (m * p)"
    by (rule msum_carrier[OF tc])
  show ?thesis
  proof (rule eq_matI)
  fix r s assume "r < dim_row (msum (m * p) (m * p) (\<lambda>(i, j). block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) (List.product [0..<p] [0..<p]))"
    "s < dim_col (msum (m * p) (m * p) (\<lambda>(i, j). block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) (List.product [0..<p] [0..<p]))"
  hence r: "r < m * p" and s: "s < m * p" using carrier_matD[OF Mc] by simp_all
  have p: "0 < p" using r by (cases p) auto
  have rd: "r div p < m" "s div p < m" using r s by (simp_all add: less_mult_imp_div_less mult.commute)
  have "msum (m * p) (m * p) (\<lambda>(i, j). block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) (List.product [0..<p] [0..<p]) $$ (r, s)
        = (\<Sum>x\<leftarrow>List.product [0..<p] [0..<p]. ((\<lambda>(i, j). block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) x) $$ (r, s))"
    by (rule msum_index[OF tc r s])
  also have "\<dots> = (\<Sum>i<p. \<Sum>j<p. (block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) $$ (r, s))"
    by (simp add: sum_list_product_upt)
  also have "\<dots> = (\<Sum>i<p. \<Sum>j<p. if i = r mod p \<and> j = s mod p then X $$ (r, s) else 0)"
  proof (intro sum.cong refl)
    fix i j assume "i \<in> {..<p}" "j \<in> {..<p}"
    hence i: "i < p" and j: "j < p" by simp_all
    show "(block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) $$ (r, s) = (if i = r mod p \<and> j = s mod p then X $$ (r, s) else 0)"
      unfolding mat_unit_tensor_index[OF block_carrier r s i j] using rd by (auto simp: block_def)
  qed
  also have "\<dots> = X $$ (r, s)" by (rule double_delta) (use p in simp_all)
  finally show "X $$ (r, s) = msum (m * p) (m * p) (\<lambda>(i, j). block m p X i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) (List.product [0..<p] [0..<p]) $$ (r, s)" ..
  qed (use carrier_matD[OF X] carrier_matD[OF Mc] in simp_all)
qed

theorem tensor_block_decomposition_unique:
  assumes Y: "\<And>i j. Y i j \<in> carrier_mat m m"
      and X: "X = msum (m * p) (m * p) (\<lambda>(i, j). Y i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) (List.product [0..<p] [0..<p])"
      and i: "i < p" and j: "j < p"
  shows "Y i j = block m p X i j"
proof (rule eq_matI)
  have tc: "\<forall>x \<in> set (List.product [0..<p] [0..<p]). (\<lambda>(i, j). Y i j \<Otimes> E\<lbrakk>i,j ; p,p\<rbrakk>) x \<in> carrier_mat (m * p) (m * p)"
    using Y by (auto intro!: carrier_matI simp: carrier_matD[OF Y])
  fix a b assume "a < dim_row (block m p X i j)" "b < dim_col (block m p X i j)"
  hence a: "a < m" and b: "b < m" by simp_all
  have r: "a * p + i < m * p" and s: "b * p + j < m * p" using mult_index_lt a b i j by auto
  have "block m p X i j $$ (a, b) = X $$ (a * p + i, b * p + j)" using a b by (simp add: block_def)
  also have "\<dots> = (\<Sum>k<p. \<Sum>l<p. (Y k l \<Otimes> E\<lbrakk>k,l ; p,p\<rbrakk>) $$ (a * p + i, b * p + j))"
    unfolding X by (simp add: msum_index[OF tc r s] sum_list_product_upt)
  also have "\<dots> = (\<Sum>k<p. \<Sum>l<p. if k = i \<and> l = j then Y i j $$ (a, b) else 0)"
  proof (intro sum.cong refl)
    fix k l assume "k \<in> {..<p}" "l \<in> {..<p}"
    hence k: "k < p" and l: "l < p" by simp_all
    show "(Y k l \<Otimes> E\<lbrakk>k,l ; p,p\<rbrakk>) $$ (a * p + i, b * p + j) = (if k = i \<and> l = j then Y i j $$ (a, b) else 0)"
      unfolding mat_unit_tensor_index[OF Y r s k l] using i j by (auto simp: mult_index_div_mod)
  qed
  also have "\<dots> = Y i j $$ (a, b)" by (rule double_delta[OF i j])
  finally show "Y i j $$ (a, b) = block m p X i j $$ (a, b)" ..
qed (use Y in auto)

text \<open>The partial traces in block form (the definitions, restated): $\tr_B(X)=\sum_iX_{ii}$,
$\tr_A(X)=(\Tr X_{ij})_{ij}$.\<close>

lemma partial_trace_B_blocks:
  "partial_trace_B m p X = msum m m (\<lambda>i. block m p X i i) [0..<p]"
proof (rule eq_matI)
  fix a b assume "a < dim_row (msum m m (\<lambda>i. block m p X i i) [0..<p])" "b < dim_col (msum m m (\<lambda>i. block m p X i i) [0..<p])"
  hence a: "a < m" and b: "b < m" using carrier_matD[OF msum_carrier[of "[0..<p]" "\<lambda>i. block m p X i i" m m]] by auto
  show "partial_trace_B m p X $$ (a, b) = msum m m (\<lambda>i. block m p X i i) [0..<p] $$ (a, b)"
    using a b by (simp add: partial_trace_B_def msum_index block_def sum_list_distinct_conv_sum_set atLeast0LessThan)
qed (use carrier_matD[OF msum_carrier[of "[0..<p]" "\<lambda>i. block m p X i i" m m]] in \<open>simp_all add: partial_trace_B_def\<close>)

lemma partial_trace_A_blocks:
  "partial_trace_A m p X = Matrix.mat p p (\<lambda>(i, j). Tr (block m p X i j))"
  by (rule eq_matI) (simp_all add: partial_trace_A_def Tr_def block_def)

end
