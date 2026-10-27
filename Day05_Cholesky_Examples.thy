theory Day05_Cholesky_Examples
  imports Day05_Positivity_Tests
begin

section \<open>Day 5: Cholesky's algorithm on the notes' two examples (D5-3)\<close>

subsection \<open>One step of Cholesky's algorithm\<close>

text \<open>For $P=(p_{ij})$ with $p_{11}\ne0$ the notes subtract
$R=\bigl(\tfrac{p_{i1}p_{1j}}{p_{11}}\bigr)_{ij}$; $P-R$ vanishes in the first row and column, and
what remains is the $(n-1)\times(n-1)$ matrix \<open>chol_next P\<close>.\<close>

definition chol_R :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "chol_R P = Matrix.mat (dim_row P) (dim_row P) (\<lambda>(i, j). P $$ (i, 0) * P $$ (0, j) / P $$ (0, 0))"

definition chol_next :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "chol_next P = Matrix.mat (dim_row P - 1) (dim_row P - 1) (\<lambda>(i, j). (P - chol_R P) $$ (i + 1, j + 1))"

lemma chol_R_carrier [simp]: "chol_R P \<in> carrier_mat (dim_row P) (dim_row P)"
  by (simp add: chol_R_def)

lemma hermitian_entry:
  assumes "hermitian P" "P \<in> carrier_mat n n" "i < n" "j < n"
  shows "P $$ (i, j) = cnj (P $$ (j, i))"
proof -
  have "P $$ (i, j) = P\<^sup>\<dagger> $$ (i, j)" using assms(1) by (simp add: hermitian_def)
  also have "\<dots> = cnj (P $$ (j, i))" using assms(2-4) by (simp add: dagger_def)
  finally show ?thesis .
qed

text \<open>The test: for $P=P^*$ with $p_{11}>0$, $P\ge0$ iff the next matrix is $\ge0$
(from @{thm [source] cholesky_reduction}).\<close>

lemma chol_test:
  assumes P: "P \<in> carrier_mat n n" and h: "hermitian P" and n: "0 < n" and p: "P $$ (0, 0) > 0"
  shows "psd P \<longleftrightarrow> psd (chol_next P)"
proof -
  have "chol_next P = Matrix.mat (n - 1) (n - 1)
          (\<lambda>(i, j). P $$ (i + 1, j + 1) - P $$ (i + 1, 0) * cnj (P $$ (j + 1, 0)) / P $$ (0, 0))"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Matrix.mat (n - 1) (n - 1)
          (\<lambda>(i, j). P $$ (i + 1, j + 1) - P $$ (i + 1, 0) * cnj (P $$ (j + 1, 0)) / P $$ (0, 0)))"
      "j < dim_col (Matrix.mat (n - 1) (n - 1)
          (\<lambda>(i, j). P $$ (i + 1, j + 1) - P $$ (i + 1, 0) * cnj (P $$ (j + 1, 0)) / P $$ (0, 0)))"
    hence i: "i + 1 < n" and j: "j + 1 < n" by simp_all
    have "P $$ (0, j + 1) = cnj (P $$ (j + 1, 0))" by (rule hermitian_entry[OF h P n j])
    thus "chol_next P $$ (i, j) = Matrix.mat (n - 1) (n - 1)
          (\<lambda>(i, j). P $$ (i + 1, j + 1) - P $$ (i + 1, 0) * cnj (P $$ (j + 1, 0)) / P $$ (0, 0)) $$ (i, j)"
      using i j P by (simp add: chol_next_def chol_R_def)
  qed (use P in \<open>simp_all add: chol_next_def\<close>)
  thus ?thesis using cholesky_reduction[OF P h n p] by simp
qed

subsection \<open>Small matrices entry by entry\<close>

lemma mat3_eqI:
  assumes "A \<in> carrier_mat 3 3" "B \<in> carrier_mat 3 3"
      and "\<And>i j. i \<in> {0, 1, 2} \<Longrightarrow> j \<in> {0, 1, 2} \<Longrightarrow> A $$ (i, j) = B $$ (i, j)"
  shows "A = B"
proof (rule eq_matI)
  fix i j assume "i < dim_row B" "j < dim_col B"
  hence "i \<in> {0, 1, 2}" "j \<in> {0, 1, 2}" using assms(2) by auto
  thus "A $$ (i, j) = B $$ (i, j)" by (rule assms(3))
qed (use assms(1,2) in auto)

lemma mat2_eqI:
  assumes "A \<in> carrier_mat 2 2" "B \<in> carrier_mat 2 2"
      and "\<And>i j. i \<in> {0, 1} \<Longrightarrow> j \<in> {0, 1} \<Longrightarrow> A $$ (i, j) = B $$ (i, j)"
  shows "A = B"
proof (rule eq_matI)
  fix i j assume "i < dim_row B" "j < dim_col B"
  hence "i \<in> {0, 1}" "j \<in> {0, 1}" using assms(2) by auto
  thus "A $$ (i, j) = B $$ (i, j)" by (rule assms(3))
qed (use assms(1,2) in auto)

subsection \<open>Example 1: a matrix that is not positive\<close>

text \<open>The notes: for $P=\begin{pmatrix}1&2&3\\2&4&5\\3&5&7\end{pmatrix}$,
$R=\begin{pmatrix}1&2&3\\2&4&6\\3&6&9\end{pmatrix}$ and
$P-R=\begin{pmatrix}0&0&0\\0&0&-1\\0&-1&-2\end{pmatrix}$, so $P\not\ge0$.  Each matrix is checked
below; the last step is the test vector $(1,1)$ for the remaining $2\times2$ block.\<close>

definition notes_P1 :: "complex Matrix.mat" where
  "notes_P1 = mat_of_rows_list 3 [[1, 2, 3], [2, 4, 5], [3, 5, 7]]"

lemma notes_P1_carrier: "notes_P1 \<in> carrier_mat 3 3"
  by (simp add: notes_P1_def mat_of_rows_list_def eval_nat_numeral)

lemma notes_P1_hermitian: "hermitian notes_P1"
  unfolding hermitian_def
  by (rule mat3_eqI) (auto simp: notes_P1_def mat_of_rows_list_def dagger_def)

lemma notes_P1_R: "chol_R notes_P1 = mat_of_rows_list 3 [[1, 2, 3], [2, 4, 6], [3, 6, 9]]"
  by (rule mat3_eqI) (auto simp: chol_R_def notes_P1_def mat_of_rows_list_def)

lemma notes_P1_diff: "notes_P1 - chol_R notes_P1 = mat_of_rows_list 3 [[0, 0, 0], [0, 0, -1], [0, -1, -2]]"
  by (rule mat3_eqI) (auto simp: chol_R_def notes_P1_def mat_of_rows_list_def)

lemma notes_P1_next: "chol_next notes_P1 = mat_of_rows_list 2 [[0, -1], [-1, -2]]"
  by (rule mat2_eqI) (auto simp: chol_next_def chol_R_def notes_P1_def mat_of_rows_list_def)

lemma not_psd_witness:
  assumes A: "A \<in> carrier_mat n n" and x: "dim_vec x = n" and neg: "Re (Quantum.inner_prod x (A *\<^sub>v x)) < 0"
  shows "\<not> psd A"
proof
  assume "psd A"
  hence "\<forall>y. dim_vec y = dim_row A \<longrightarrow> 0 \<le> Re (Quantum.inner_prod y (A *\<^sub>v y))" unfolding psd_def by blast
  thus False using x neg carrier_matD(1)[OF A] by force
qed

text \<open>$\begin{pmatrix}0&-1\\-1&-2\end{pmatrix}$ has the value $-4$ at $(1,1)$, so it is not positive.\<close>

lemma notes_P1_next_not_psd: "\<not> psd (mat_of_rows_list 2 [[0, -1], [-1, -2]])"
proof (rule not_psd_witness)
  show "mat_of_rows_list 2 [[0, -1], [-1, -2]] \<in> carrier_mat 2 2"
    by (simp add: mat_of_rows_list_def eval_nat_numeral)
  show "dim_vec (Matrix.vec 2 (\<lambda>_. 1)) = 2" by simp
  show "Re (Quantum.inner_prod (Matrix.vec 2 (\<lambda>_. 1)) (mat_of_rows_list 2 [[0, -1], [-1, -2]] *\<^sub>v Matrix.vec 2 (\<lambda>_. 1))) < 0"
    by (simp add: Quantum.inner_prod_def scalar_prod_def mat_of_rows_list_def eval_nat_numeral)
qed

theorem notes_example_1: "hermitian notes_P1 \<and> \<not> psd notes_P1"
proof
  show "hermitian notes_P1" by (rule notes_P1_hermitian)
  have p: "notes_P1 $$ (0, 0) > 0" by (simp add: notes_P1_def mat_of_rows_list_def less_complex_def)
  show "\<not> psd notes_P1"
    using chol_test[OF notes_P1_carrier notes_P1_hermitian _ p] notes_P1_next notes_P1_next_not_psd by simp
qed

subsection \<open>Example 2: a positive matrix, in two steps\<close>

text \<open>The notes: for $P=\begin{pmatrix}4&2&3\\2&5&6\\3&6&8\end{pmatrix}$,
$R=\tfrac14\begin{pmatrix}16&8&12\\8&4&6\\12&6&9\end{pmatrix}$ and
$P-R=\begin{pmatrix}0&0&0\\0&4&\frac92\\0&\frac92&\frac{23}4\end{pmatrix}$.  Repeating on
$Q=\begin{pmatrix}4&\frac92\\\frac92&\frac{23}4\end{pmatrix}$:
$Q-\tfrac14\begin{pmatrix}4\\\frac92\end{pmatrix}\begin{pmatrix}4&\frac92\end{pmatrix}
=\begin{pmatrix}0&0\\0&\frac{11}{16}\end{pmatrix}$, so $P\ge0$.\<close>

definition notes_P2 :: "complex Matrix.mat" where
  "notes_P2 = mat_of_rows_list 3 [[4, 2, 3], [2, 5, 6], [3, 6, 8]]"

lemma notes_P2_carrier: "notes_P2 \<in> carrier_mat 3 3"
  by (simp add: notes_P2_def mat_of_rows_list_def eval_nat_numeral)

lemma notes_P2_hermitian: "hermitian notes_P2"
  unfolding hermitian_def
  by (rule mat3_eqI) (auto simp: notes_P2_def mat_of_rows_list_def dagger_def)

text \<open>First step: the first column is $c=(4,2,3)^t$ and $p_{11}=4$, and subtracting $\tfrac14cc^t$
clears the first row and column:
\[ P_2-\frac14\begin{pmatrix}4\\2\\3\end{pmatrix}\begin{pmatrix}4&2&3\end{pmatrix}
   =\begin{pmatrix}0&0&0\\0&4&9/2\\0&9/2&23/4\end{pmatrix}. \]\<close>

lemma notes_P2_R: "chol_R notes_P2 = (1/4) \<cdot>\<^sub>m mat_of_rows_list 3 [[16, 8, 12], [8, 4, 6], [12, 6, 9]]"
  by (rule mat3_eqI) (auto simp: chol_R_def notes_P2_def mat_of_rows_list_def)

lemma notes_P2_diff: "notes_P2 - chol_R notes_P2 = mat_of_rows_list 3 [[0, 0, 0], [0, 4, 9/2], [0, 9/2, 23/4]]"
  by (rule mat3_eqI) (auto simp: chol_R_def notes_P2_def mat_of_rows_list_def)

definition notes_Q2 :: "complex Matrix.mat" where
  "notes_Q2 = mat_of_rows_list 2 [[4, 9/2], [9/2, 23/4]]"

lemma notes_P2_next: "chol_next notes_P2 = notes_Q2"
  by (rule mat2_eqI) (auto simp: chol_next_def chol_R_def notes_P2_def notes_Q2_def mat_of_rows_list_def)

lemma notes_Q2_carrier: "notes_Q2 \<in> carrier_mat 2 2"
  by (simp add: notes_Q2_def mat_of_rows_list_def eval_nat_numeral)

lemma notes_Q2_hermitian: "hermitian notes_Q2"
  unfolding hermitian_def
  by (rule mat2_eqI) (auto simp: notes_Q2_def mat_of_rows_list_def dagger_def)

text \<open>Second step, on the remaining block $Q_2$:
\[ Q_2-\frac14\begin{pmatrix}4\\9/2\end{pmatrix}\begin{pmatrix}4&9/2\end{pmatrix}
   =\begin{pmatrix}0&0\\0&11/16\end{pmatrix}, \]
and the last pivot $11/16$ is positive.\<close>

lemma notes_Q2_R: "chol_R notes_Q2 = (1/4) \<cdot>\<^sub>m mat_of_rows_list 2 [[16, 18], [18, 81/4]]"
  by (rule mat2_eqI) (auto simp: chol_R_def notes_Q2_def mat_of_rows_list_def)

lemma notes_Q2_diff: "notes_Q2 - chol_R notes_Q2 = mat_of_rows_list 2 [[0, 0], [0, 11/16]]"
  by (rule mat2_eqI) (auto simp: chol_R_def notes_Q2_def mat_of_rows_list_def)

text \<open>The last matrix is $(\tfrac{11}{16})=\tfrac{11}{16}\,|e\rangle\langle e|$, which is positive.\<close>

lemma notes_Q2_next: "chol_next notes_Q2 = complex_of_real (11/16) \<cdot>\<^sub>m (Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. 1))"
proof (rule eq_matI)
  have oc: "Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. (1::complex)) \<in> carrier_mat 1 1"
    by (rule outer_prod_carrier) simp_all
  fix i j assume "i < dim_row (complex_of_real (11/16) \<cdot>\<^sub>m (Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. (1::complex))))"
    "j < dim_col (complex_of_real (11/16) \<cdot>\<^sub>m (Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. (1::complex))))"
  hence ij: "i = 0" "j = 0" using carrier_matD[OF oc] by auto
  show "chol_next notes_Q2 $$ (i, j) = (complex_of_real (11/16) \<cdot>\<^sub>m (Matrix.vec 1 (\<lambda>_. 1) \<oslash> Matrix.vec 1 (\<lambda>_. 1))) $$ (i, j)"
    using ij carrier_matD[OF oc] outer_prod_index[of 0 "Matrix.vec 1 (\<lambda>_. (1::complex))" 0 "Matrix.vec 1 (\<lambda>_. 1)"]
    by (simp add: chol_next_def chol_R_def notes_Q2_def mat_of_rows_list_def)
qed (use carrier_matD[OF outer_prod_carrier[of "Matrix.vec 1 (\<lambda>_. (1::complex))" 1 "Matrix.vec 1 (\<lambda>_. 1)" 1]]
     in \<open>simp_all add: chol_next_def notes_Q2_def mat_of_rows_list_def\<close>)

lemma notes_Q2_next_psd: "psd (chol_next notes_Q2)"
  unfolding notes_Q2_next
  by (rule psd_smult_nonneg[OF _ outer_prod_self_psd outer_prod_carrier]) simp_all

theorem notes_example_2: "hermitian notes_P2 \<and> psd notes_P2"
proof
  show "hermitian notes_P2" by (rule notes_P2_hermitian)
  have q: "notes_Q2 $$ (0, 0) > 0" by (simp add: notes_Q2_def mat_of_rows_list_def less_complex_def)
  have "psd notes_Q2"
    using chol_test[OF notes_Q2_carrier notes_Q2_hermitian _ q] notes_Q2_next_psd by simp
  moreover have p: "notes_P2 $$ (0, 0) > 0" by (simp add: notes_P2_def mat_of_rows_list_def less_complex_def)
  ultimately show "psd notes_P2"
    using chol_test[OF notes_P2_carrier notes_P2_hermitian _ p] notes_P2_next by simp
qed

text \<open>The notes' remark: the algorithm writes $P$ as a sum of rank-one matrices,
$P=\tfrac14|v_1\rangle\langle v_1|+\tfrac14|v_2\rangle\langle v_2|+\tfrac{11}{16}|e_3\rangle\langle e_3|$ with
$v_1=(4,2,3)$, $v_2=(0,4,\tfrac92)$, $e_3=(0,0,1)$ (the first columns of $P$, of $P-R$ and of the
last step).\<close>

lemma outer_prod_of_list:
  "vec_of_list l \<oslash> vec_of_list l = Matrix.mat (length l) (length l) (\<lambda>(i, j). l ! i * cnj (l ! j))"
proof -
  have d: "dim_vec (vec_of_list l) = length l" by simp
  have c: "vec_of_list l \<oslash> vec_of_list l \<in> carrier_mat (length l) (length l)" by (rule outer_prod_carrier[OF d d])
  show ?thesis
  proof (rule eq_matI)
    fix i j assume "i < dim_row (Matrix.mat (length l) (length l) (\<lambda>(i, j). l ! i * cnj (l ! j)))"
      "j < dim_col (Matrix.mat (length l) (length l) (\<lambda>(i, j). l ! i * cnj (l ! j)))"
    hence i: "i < length l" and j: "j < length l" by simp_all
    have "(vec_of_list l \<oslash> vec_of_list l) $$ (i, j) = vec_of_list l $ i * cnj (vec_of_list l $ j)"
      by (rule outer_prod_index) (use i j in simp_all)
    thus "(vec_of_list l \<oslash> vec_of_list l) $$ (i, j) = Matrix.mat (length l) (length l) (\<lambda>(i, j). l ! i * cnj (l ! j)) $$ (i, j)"
      using i j by (simp add: vec_of_list_index)
  qed (use carrier_matD[OF c] in simp_all)
qed

lemma notes_P2_rank_one_sum:
  "notes_P2 = complex_of_real (1/4) \<cdot>\<^sub>m (vec_of_list [4, 2, 3] \<oslash> vec_of_list [4, 2, 3])
            + complex_of_real (1/4) \<cdot>\<^sub>m (vec_of_list [0, 4, 9/2] \<oslash> vec_of_list [0, 4, 9/2])
            + complex_of_real (11/16) \<cdot>\<^sub>m (vec_of_list [0, 0, 1] \<oslash> vec_of_list [0, 0, 1])"
  unfolding outer_prod_of_list
  by (rule mat3_eqI[OF notes_P2_carrier]) (auto simp: notes_P2_def mat_of_rows_list_def eval_nat_numeral)

end
