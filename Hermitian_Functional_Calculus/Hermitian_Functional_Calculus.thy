theory Hermitian_Functional_Calculus
  imports "HOL-Analysis.L2_Norm" QHLProver.Complex_Matrix Isabelle_Marries_Dirac.Quantum
begin

hide_const (open) Quantum.X Quantum.Y Quantum.Z Quantum.H Quantum.S Quantum.T

section \<open>Functional calculus for Hermitian matrices\<close>

text \<open>For Hermitian $A$ and $g:\mathbb R\to\mathbb C$, $g(A)$ is the matrix that acts on every
eigenvector $v$ of $A$ with eigenvalue $\lambda$ as multiplication by $g(\lambda)$.  The
eigenvectors span $\C^n$, so this determines $g(A)$; for a spectral decomposition
$A=U\,\mathrm{diag}(D)\,U^*$ it is $U\,\mathrm{diag}(g\circ D)\,U^*$.\<close>

text \<open>$\diag(x_1,\dots,x_n)$, the diagonal matrix with the entries of a list.\<close>

definition diag_matrix :: "complex list \<Rightarrow> complex Matrix.mat" where
  "diag_matrix xs = mat_diag (length xs) (\<lambda>i. xs ! i)"

lemma diag_matrix_carrier [simp]: "diag_matrix xs \<in> carrier_mat (length xs) (length xs)"
  by (simp add: diag_matrix_def mat_diag_def)

lemma dim_diag_matrix [simp]: "dim_row (diag_matrix xs) = length xs" "dim_col (diag_matrix xs) = length xs"
  by (simp_all add: diag_matrix_def mat_diag_def)

text \<open>It scales coordinates, $\diag(x)\,w=(x_iw_i)_i$; multiplying a matrix on the right by
$\diag(x)$ scales its $j$-th column by $x_j$; and $\diag(x)^*=\diag(\overline x)$.\<close>

lemma diag_matrix_mult_vec:
  assumes "dim_vec w = length xs"
  shows "diag_matrix xs *\<^sub>v w = Matrix.vec (length xs) (\<lambda>i. xs ! i * w $ i)"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (Matrix.vec (length xs) (\<lambda>i. xs ! i * w $ i))"
  hence i: "i < length xs" by simp
  have "(diag_matrix xs *\<^sub>v w) $ i = (\<Sum>k = 0..<length xs. (if i = k then xs ! i else 0) * w $ k)"
    using i assms by (simp add: diag_matrix_def mat_diag_def mult_mat_vec_def scalar_prod_def cong: if_cong)
  also have "\<dots> = (\<Sum>k = 0..<length xs. if k = i then xs ! i * w $ i else 0)"
    by (rule sum.cong) auto
  also have "\<dots> = xs ! i * w $ i" using i by simp
  finally show "(diag_matrix xs *\<^sub>v w) $ i = Matrix.vec (length xs) (\<lambda>i. xs ! i * w $ i) $ i"
    using i by simp
qed simp

lemma col_mult_diag:
  assumes M: "M \<in> carrier_mat n (length xs)" and j: "j < length xs"
  shows "Matrix.col (M * diag_matrix xs) j = xs ! j \<cdot>\<^sub>v Matrix.col M j"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (xs ! j \<cdot>\<^sub>v Matrix.col M j)"
  hence i: "i < n" using M by simp
  have "Matrix.col (M * diag_matrix xs) j $ i = (\<Sum>k = 0..<length xs. M $$ (i, k) * (if k = j then xs ! k else 0))"
    using M i j by (simp add: diag_matrix_def mat_diag_def scalar_prod_def atLeast0LessThan cong: if_cong)
  also have "\<dots> = (\<Sum>k = 0..<length xs. if k = j then M $$ (i, j) * xs ! j else 0)"
    by (rule sum.cong) auto
  also have "\<dots> = M $$ (i, j) * xs ! j" using j by simp
  finally show "Matrix.col (M * diag_matrix xs) j $ i = (xs ! j \<cdot>\<^sub>v Matrix.col M j) $ i"
    using M i j by (simp add: mult.commute)
qed (use M in simp)

lemma diag_matrix_dagger: "(diag_matrix xs)\<^sup>\<dagger> = diag_matrix (map cnj xs)"
  by (rule eq_matI) (auto simp: diag_matrix_def mat_diag_def dagger_def)

subsection \<open>Adjoints\<close>

text \<open>QHLProver's \<^const>\<open>hermitian\<close> and Schur decomposition, with IMD's adjoint $M^\dagger$,
\<^const>\<open>unitary\<close> and norm $\norm v$.\<close>

lemma dagger_adjoint: "M\<^sup>\<dagger> = Complex_Matrix.adjoint M"
  by (rule eq_matI) (simp_all add: dagger_def adjoint_eval)

lemma hermitian_dagger: "hermitian A \<longleftrightarrow> A\<^sup>\<dagger> = A"
  by (simp add: hermitian_def dagger_adjoint)

lemma dagger_carrier: "M \<in> carrier_mat m n \<Longrightarrow> M\<^sup>\<dagger> \<in> carrier_mat n m"
  by (simp add: dagger_def)

lemma unitary_dagger: "unitary A \<Longrightarrow> unitary (A\<^sup>\<dagger>)"
  unfolding unitary_def by (simp add: dagger_of_dagger_is_id)

lemma unitary_from_complex_unitary:
  assumes "P \<in> carrier_mat n n" "Complex_Matrix.unitary P"
  shows "unitary P"
  using assms unfolding unitary_def dagger_adjoint by simp

lemma one_smult_mat: "(1::complex) \<cdot>\<^sub>m M = M"
  by (rule eq_matI, simp_all)

lemma diag_conj_carrier:
  assumes U: "U \<in> carrier_mat n n" and xs: "length xs = n"
  shows "U * diag_matrix xs * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
proof -
  have "diag_matrix xs \<in> carrier_mat n n" using diag_matrix_carrier[of xs] xs by simp
  thus ?thesis using mult_carrier_mat[OF mult_carrier_mat[OF U] dagger_carrier[OF U]] by blast
qed

subsection \<open>Vector norms\<close>

lemma cpx_vec_length_smult: "\<parallel>a \<cdot>\<^sub>v v\<parallel> = cmod a * \<parallel>v\<parallel>"
proof -
  have "(\<Sum>i<dim_vec v. (cmod (a * v $ i))\<^sup>2) = (cmod a)\<^sup>2 * (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
    by (simp add: norm_mult power_mult_distrib sum_distrib_left)
  thus ?thesis by (simp add: cpx_vec_length_def real_sqrt_mult)
qed

text \<open>The Euclidean norm $\norm v=\bigl(\sum_i|v_i|^2\bigr)^{1/2}$, with $\norm v^2=\mathrm{Re}\braket vv$, is
positive for $v\ne0$.\<close>

lemma vnorm_L2: "\<parallel>v\<parallel> = L2_set (\<lambda>i. cmod (v $ i)) {..<dim_vec v}"
  by (simp add: cpx_vec_length_def L2_set_def)

lemma vnorm_ge0: "0 \<le> \<parallel>v\<parallel>"
  by (simp add: cpx_vec_length_def sum_nonneg)

lemma vnorm_pos:
  assumes v: "dim_vec v = n" "v \<noteq> 0\<^sub>v n"
  shows "0 < \<parallel>v\<parallel>"
proof -
  obtain i where i: "i < n" "v $ i \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> thesis"
    hence "v = 0\<^sub>v n" using that v(1) by (intro eq_vecI) auto
    thus False using v(2) by simp
  qed
  have "0 < (cmod (v $ i))\<^sup>2" using i by simp
  also have "\<dots> \<le> (\<Sum>j<dim_vec v. (cmod (v $ j))\<^sup>2)" using i v by (intro member_le_sum) auto
  finally show ?thesis by (simp add: cpx_vec_length_def)
qed

lemma vnorm_sq: "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
  by (simp add: cpx_vec_length_def sum_nonneg)

lemma vnorm_Re_inner: "Re \<langle>v|v\<rangle> = \<parallel>v\<parallel>\<^sup>2"
  unfolding cpx_vec_length_inner_prod[symmetric] by simp

text \<open>The triangle inequality, in the forms used later, and its reverse
$\bigl|\norm a-\norm b\bigr|\le\norm{a-b}$:\<close>

lemma vnorm_add_le:
  assumes "dim_vec a = dim_vec b"
  shows "\<parallel>a + b\<parallel> \<le> \<parallel>a\<parallel> + \<parallel>b\<parallel>"
proof -
  have "\<parallel>a + b\<parallel> = L2_set (\<lambda>i. cmod (a $ i + b $ i)) {..<dim_vec b}"
    unfolding vnorm_L2 using assms by (intro L2_set_cong) simp_all
  also have "\<dots> \<le> L2_set (\<lambda>i. cmod (a $ i) + cmod (b $ i)) {..<dim_vec b}"
    by (rule L2_set_mono) (simp_all add: norm_triangle_ineq)
  also have "\<dots> \<le> L2_set (\<lambda>i. cmod (a $ i)) {..<dim_vec b} + L2_set (\<lambda>i. cmod (b $ i)) {..<dim_vec b}"
    by (rule L2_set_triangle_ineq)
  finally show ?thesis unfolding vnorm_L2 assms .
qed

lemma vnorm_minus_commute:
  assumes "dim_vec a = dim_vec b"
  shows "\<parallel>a - b\<parallel> = \<parallel>b - a\<parallel>"
  using assms by (simp add: cpx_vec_length_def norm_minus_commute)

lemma vnorm_diff_le:
  assumes a: "dim_vec a = n" and b: "dim_vec b = n" and c: "dim_vec c = n"
  shows "\<parallel>a - c\<parallel> \<le> \<parallel>a - b\<parallel> + \<parallel>b - c\<parallel>"
proof -
  have "a - c = (a - b) + (b - c)" using a b c by (intro eq_vecI) simp_all
  thus ?thesis using vnorm_add_le[of "a - b" "b - c"] a b c by simp
qed

lemma vnorm_le_diff_add:
  assumes "dim_vec a = dim_vec b"
  shows "\<parallel>a\<parallel> \<le> \<parallel>a - b\<parallel> + \<parallel>b\<parallel>"
proof -
  have "(a - b) + b = a" using assms by (intro eq_vecI) simp_all
  thus ?thesis using vnorm_add_le[of "a - b" b] assms by simp
qed

lemma vnorm_reverse:
  assumes "dim_vec a = dim_vec b"
  shows "\<bar>\<parallel>a\<parallel> - \<parallel>b\<parallel>\<bar> \<le> \<parallel>a - b\<parallel>"
  using vnorm_le_diff_add[OF assms] vnorm_le_diff_add[of b a] assms vnorm_minus_commute[OF assms] by simp

lemma vnorm_zero_vec: "\<parallel>0\<^sub>v m\<parallel> = 0"
  by (simp add: cpx_vec_length_def)

text \<open>Unitaries preserve the norm, $\norm{Wy}=\norm y$, and products and powers of unitaries are
unitary.\<close>

lemma unitary_vnorm:
  assumes W: "W \<in> carrier_mat K K" "unitary W" and y: "dim_vec y = K"
  shows "\<parallel>W *\<^sub>v y\<parallel> = \<parallel>y\<parallel>"
proof -
  have "Matrix.col (W * |y\<rangle>) 0 = W *\<^sub>v y"
    using W(1) y by (intro eq_vecI) (auto simp: ket_vec_def scalar_prod_def)
  thus ?thesis using unitary_is_length_preserving[OF W(2), of y] W(1) y by simp
qed

lemma unitary_mult:
  assumes "unitary A" "unitary B" "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "unitary (A * B)"
proof -
  have d: "A\<^sup>\<dagger> \<in> carrier_mat n n" "B\<^sup>\<dagger> \<in> carrier_mat n n" using assms(3,4) by (simp_all add: dagger_carrier)
  have u: "A\<^sup>\<dagger> * A = 1\<^sub>m n" "A * (A\<^sup>\<dagger>) = 1\<^sub>m n" "B\<^sup>\<dagger> * B = 1\<^sub>m n" "B * (B\<^sup>\<dagger>) = 1\<^sub>m n"
    using assms unfolding unitary_def by auto
  have "(A * B)\<^sup>\<dagger> = (B\<^sup>\<dagger>) * (A\<^sup>\<dagger>)" using assms(3,4) by (simp add: dagger_of_prod)
  moreover have "(B\<^sup>\<dagger>) * (A\<^sup>\<dagger>) * (A * B) = (B\<^sup>\<dagger>) * ((A\<^sup>\<dagger>) * A) * B"
      "A * B * ((B\<^sup>\<dagger>) * (A\<^sup>\<dagger>)) = A * (B * (B\<^sup>\<dagger>)) * (A\<^sup>\<dagger>)"
    using assms(3,4) d by (mat_assoc n)+
  ultimately show ?thesis unfolding unitary_def using u assms(3,4) d by simp
qed

lemma unitary_pow:
  assumes U: "U \<in> carrier_mat m m" and u: "unitary U"
  shows "unitary (U ^\<^sub>m k)"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have "unitary (U ^\<^sub>m k * U)" by (rule unitary_mult[OF Suc u pow_carrier_mat[OF U] U])
  thus ?case by simp
qed

subsection \<open>Spectral decompositions\<close>

text \<open>\<open>spectral_decomp A U D\<close>: $U$ unitary and $U^*AU=\mathrm{diag}(D)$.\<close>

definition spectral_decomp :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real list \<Rightarrow> bool" where
  "spectral_decomp A U D \<longleftrightarrow> U \<in> carrier_mat (dim_row A) (dim_row A) \<and> unitary U \<and>
     length D = dim_row A \<and> U\<^sup>\<dagger> * A * U = diag_matrix (map complex_of_real D)"

text \<open>The spectral theorem, from QHLProver's Schur decomposition of Hermitian matrices.\<close>

lemma spectral_decomp_exists:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "\<exists>U D. spectral_decomp A U D"
proof -
  obtain es where c: "char_poly A = (\<Prod>e\<leftarrow>es. [:- e, 1:])"
    using complex_mat_char_poly_factorizable[OF A(1)] by blast
  obtain B P Q where s: "unitary_schur_decomposition A es = (B, P, Q)"
    by (cases "unitary_schur_decomposition A es") auto
  have h: "similar_mat_wit A B P (Complex_Matrix.adjoint P)" "diagonal_mat B" "Complex_Matrix.unitary P"
      "\<forall>i<n. B $$ (i, i) \<in> \<real>"
    using hermitian_eigenvalue_real[OF A c s] by auto
  have P: "P \<in> carrier_mat n n" "B \<in> carrier_mat n n" "A = P * B * Complex_Matrix.adjoint P"
    using h(1) A(1) unfolding similar_mat_wit_def Let_def by auto
  have u: "unitary P" by (rule unitary_from_complex_unitary[OF P(1) h(3)])
  hence PP: "P\<^sup>\<dagger> * P = 1\<^sub>m n" using P(1) unfolding unitary_def by simp
  define D where "D = map (\<lambda>i. Re (B $$ (i, i))) [0..<n]"
  have BD: "B = diag_matrix (map complex_of_real D)"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (diag_matrix (map complex_of_real D))" "j < dim_col (diag_matrix (map complex_of_real D))"
    hence ij: "i < n" "j < n" by (simp_all add: D_def)
    show "B $$ (i, j) = diag_matrix (map complex_of_real D) $$ (i, j)"
      using h(2,4) ij P(2) by (cases "i = j") (auto simp: diag_matrix_def mat_diag_def D_def diagonal_mat_def)
  qed (use P(2) in \<open>simp_all add: D_def\<close>)
  have Pd: "P\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF P(1)])
  have "P\<^sup>\<dagger> * A * P = (P\<^sup>\<dagger> * P) * B * (P\<^sup>\<dagger> * P)"
    unfolding P(3) dagger_adjoint[symmetric] using P(1,2) Pd by (mat_assoc n)
  hence "P\<^sup>\<dagger> * A * P = B" unfolding PP using P(2) by simp
  hence "spectral_decomp A P D" unfolding spectral_decomp_def BD using P(1) A(1) u by (simp add: D_def)
  thus ?thesis by blast
qed

text \<open>Unpacking a spectral decomposition: $UU^*=U^*U=I$ and $A=U\,\diag(D)\,U^*$.\<close>

lemma spectral_decompD:
  assumes A: "A \<in> carrier_mat n n" and sd: "spectral_decomp A U D"
  shows "U \<in> carrier_mat n n" "unitary U" "length D = n" "U\<^sup>\<dagger> * U = 1\<^sub>m n" "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    "A = U * diag_matrix (map complex_of_real D) * (U\<^sup>\<dagger>)" "A * U = U * diag_matrix (map complex_of_real D)"
proof -
  show U: "U \<in> carrier_mat n n" and u: "unitary U" and D: "length D = n"
    using sd A unfolding spectral_decomp_def by auto
  show UU: "U\<^sup>\<dagger> * U = 1\<^sub>m n" and UU': "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using u U unfolding unitary_def by auto
  have e: "U\<^sup>\<dagger> * A * U = diag_matrix (map complex_of_real D)" using sd unfolding spectral_decomp_def by auto
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have "U * diag_matrix (map complex_of_real D) * (U\<^sup>\<dagger>) = (U * (U\<^sup>\<dagger>)) * A * (U * (U\<^sup>\<dagger>))"
    unfolding e[symmetric] using U Ud A by (mat_assoc n)
  thus "A = U * diag_matrix (map complex_of_real D) * (U\<^sup>\<dagger>)" unfolding UU' using A by simp
  have "U * diag_matrix (map complex_of_real D) = (U * (U\<^sup>\<dagger>)) * A * U"
    unfolding e[symmetric] using U Ud A by (mat_assoc n)
  thus "A * U = U * diag_matrix (map complex_of_real D)" unfolding UU' using A by simp
qed

text \<open>The columns of $U$ are eigenvectors: $Au_j=D_ju_j$.\<close>

lemma spectral_decomp_col:
  assumes A: "A \<in> carrier_mat n n" and sd: "spectral_decomp A U D" and j: "j < n"
  shows "A *\<^sub>v Matrix.col U j = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j"
proof -
  note d = spectral_decompD[OF A sd]
  have "A *\<^sub>v Matrix.col U j = Matrix.col (A * U) j" by (rule col_mult2[OF A d(1) j, symmetric])
  also have "\<dots> = Matrix.col (U * diag_matrix (map complex_of_real D)) j" using d(7) by simp
  also have "\<dots> = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j"
    using col_mult_diag[of U n "map complex_of_real D" j] d(1,3) j by simp
  finally show ?thesis .
qed

subsection \<open>The definition\<close>

text \<open>$B$ acts as $g$ on the eigenvectors of $A$ if $Av=\lambda v$ implies $Bv=g(\lambda)\,v$.  The matrix
$g(A)$ is the $n\times n$ matrix with this property; it exists and is unique (below).\<close>

definition acts_on_eigenvectors :: "complex Matrix.mat \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "acts_on_eigenvectors A g B \<longleftrightarrow> (\<forall>v l. dim_vec v = dim_row A \<longrightarrow>
     A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v \<longrightarrow> B *\<^sub>v v = g l \<cdot>\<^sub>v v)"

definition mat_fun :: "(real \<Rightarrow> complex) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "mat_fun g A = (SOME B. B \<in> carrier_mat (dim_row A) (dim_row A) \<and> acts_on_eigenvectors A g B)"

text \<open>The spectrum: the real eigenvalues (JNF's \<open>eigenvalue\<close>).\<close>

definition herm_spectrum :: "complex Matrix.mat \<Rightarrow> real set" where
  "herm_spectrum A = {l. eigenvalue A (complex_of_real l)}"

lemma herm_spectrum_iff:
  "l \<in> herm_spectrum A \<longleftrightarrow> (\<exists>v. dim_vec v = dim_row A \<and> v \<noteq> 0\<^sub>v (dim_row A) \<and> A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v)"
  unfolding herm_spectrum_def mem_Collect_eq eigenvalue_def eigenvector_def carrier_vec_def by simp

text \<open>Each $D_j$ of a spectral decomposition is an eigenvalue of $A$.\<close>

lemma spectral_decomp_eig_in_spectrum:
  assumes A: "A \<in> carrier_mat n n" and sd: "spectral_decomp A U D" and j: "j < n"
  shows "D ! j \<in> herm_spectrum A"
proof -
  note d = spectral_decompD[OF A sd]
  have cd: "dim_vec (Matrix.col U j) = n" using d(1) by simp
  have nz: "Matrix.col U j \<noteq> 0\<^sub>v n"
  proof
    assume z: "Matrix.col U j = 0\<^sub>v n"
    have "(U\<^sup>\<dagger> * U) $$ (j, j) = Matrix.row (U\<^sup>\<dagger>) j \<bullet> Matrix.col U j"
      by (rule index_mult_mat(1)) (use d(1) j in simp_all)
    also have "\<dots> = 0" unfolding z by (rule scalar_prod_right_zero) (use d(1) j in \<open>simp add: dagger_def\<close>)
    finally show False using d(4) j by simp
  qed
  show ?thesis unfolding herm_spectrum_iff
    using spectral_decomp_col[OF A sd j] cd nz A by (intro exI[of _ "Matrix.col U j"]) simp
qed

lemma acts_on_eigenvectorsD:
  "acts_on_eigenvectors A g B \<Longrightarrow> dim_vec v = dim_row A \<Longrightarrow> A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v \<Longrightarrow>
   B *\<^sub>v v = g l \<cdot>\<^sub>v v"
  unfolding acts_on_eigenvectors_def by blast

text \<open>$U\,\mathrm{diag}(g\circ D)\,U^*$ acts correctly on eigenvectors: if $Av=\lambda v$ then
$w=U^*v$ has $D_iw_i=\lambda w_i$, so $g(D_i)w_i=g(\lambda)w_i$.\<close>

lemma spectral_decomp_acts_on_eigenvectors:
  assumes A: "A \<in> carrier_mat n n" and sd: "spectral_decomp A U D"
  shows "acts_on_eigenvectors A g (U * diag_matrix (map g D) * (U\<^sup>\<dagger>))"
  unfolding acts_on_eigenvectors_def
proof (intro allI impI)
  fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  note d = spectral_decompD[OF A sd]
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI) (use v A in simp)
  have Uc: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF d(1)])
  define w where "w = U\<^sup>\<dagger> *\<^sub>v v"
  have wc: "w \<in> carrier_vec n" unfolding w_def using Uc vc by simp
  have Uw: "U *\<^sub>v w = v"
    unfolding w_def using assoc_mult_mat_vec[OF d(1) Uc vc, symmetric] d(5) vc by simp
  have "diag_matrix (map complex_of_real D) *\<^sub>v w = (U\<^sup>\<dagger> * A * U) *\<^sub>v w"
    using sd unfolding spectral_decomp_def by simp
  also have "\<dots> = U\<^sup>\<dagger> *\<^sub>v (A *\<^sub>v (U *\<^sub>v w))"
    using Uc A d(1) wc by (simp add: assoc_mult_mat_vec[of _ n n _ n])
  also have "\<dots> = complex_of_real l \<cdot>\<^sub>v w"
    unfolding Uw ev unfolding w_def by (rule mult_mat_vec[OF Uc vc])
  finally have Dw: "diag_matrix (map complex_of_real D) *\<^sub>v w = complex_of_real l \<cdot>\<^sub>v w" .
  have wi: "w $ i = 0 \<or> D ! i = l" if i: "i < n" for i
  proof -
    have "(diag_matrix (map complex_of_real D) *\<^sub>v w) $ i = complex_of_real (D ! i) * w $ i"
      using diag_matrix_mult_vec[of w "map complex_of_real D"] wc d(3) i by simp
    hence "complex_of_real (D ! i) * w $ i = complex_of_real l * w $ i"
      using Dw i wc by (metis carrier_vecD index_smult_vec(1))
    thus ?thesis by auto
  qed
  have gw: "diag_matrix (map g D) *\<^sub>v w = g l \<cdot>\<^sub>v w"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (g l \<cdot>\<^sub>v w)"
    hence i: "i < n" using wc by simp
    show "(diag_matrix (map g D) *\<^sub>v w) $ i = (g l \<cdot>\<^sub>v w) $ i"
      using diag_matrix_mult_vec[of w "map g D"] wc d(3) i wi[OF i] by auto
  qed (use wc d(3) in simp)
  have gc: "diag_matrix (map g D) \<in> carrier_mat n n" using d(3) diag_matrix_carrier by (metis length_map)
  have "(U * diag_matrix (map g D) * (U\<^sup>\<dagger>)) *\<^sub>v v = U *\<^sub>v (diag_matrix (map g D) *\<^sub>v w)"
    unfolding w_def assoc_mult_mat_vec[OF mult_carrier_mat[OF d(1) gc] Uc vc]
    by (rule assoc_mult_mat_vec[OF d(1) gc mult_mat_vec_carrier[OF Uc vc]])
  also have "\<dots> = g l \<cdot>\<^sub>v (U *\<^sub>v w)" unfolding gw using d(1) wc by (rule mult_mat_vec)
  also note Uw
  finally show "(U * diag_matrix (map g D) * (U\<^sup>\<dagger>)) *\<^sub>v v = g l \<cdot>\<^sub>v v" .
qed

text \<open>Two matrices that agree on every eigenvector of a Hermitian $A$ agree on its eigenbasis $U$, hence
are equal.\<close>

lemma eigvec_mat_eqI:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and B1: "B1 \<in> carrier_mat K n" and B2: "B2 \<in> carrier_mat K n"
      and eq: "\<And>v l. dim_vec v = n \<Longrightarrow> A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v \<Longrightarrow> B1 *\<^sub>v v = B2 *\<^sub>v v"
  shows "B1 = B2"
proof -
  obtain U D where sd: "spectral_decomp A U D" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have BU: "B1 * U = B2 * U"
  proof (rule Matrix.mat_col_eqI)
    fix j assume "j < dim_col (B2 * U)"
    hence j: "j < n" using d(1) by simp
    have cU: "dim_vec (Matrix.col U j) = n" using d(1) by simp
    have "Matrix.col (B1 * U) j = B1 *\<^sub>v Matrix.col U j" by (rule col_mult2[OF B1 d(1) j])
    also have "\<dots> = B2 *\<^sub>v Matrix.col U j" by (rule eq[OF cU spectral_decomp_col[OF A(1) sd j]])
    also have "\<dots> = Matrix.col (B2 * U) j" by (rule col_mult2[OF B2 d(1) j, symmetric])
    finally show "Matrix.col (B1 * U) j = Matrix.col (B2 * U) j" .
  qed (use B1 B2 d(1) in simp_all)
  have "B1 = (B1 * U) * (U\<^sup>\<dagger>)"
    using assoc_mult_mat[OF B1 d(1) dagger_carrier[OF d(1)]] d(5) B1 by simp
  also have "\<dots> = (B2 * U) * (U\<^sup>\<dagger>)" by (simp only: BU)
  also have "\<dots> = B2"
    using assoc_mult_mat[OF B2 d(1) dagger_carrier[OF d(1)]] d(5) B2 by simp
  finally show ?thesis .
qed

text \<open>Hence $g(A)$ is well defined: an $n\times n$ matrix acting as $g$ on the eigenvectors.\<close>

lemma
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows mat_fun_carrier [simp]: "mat_fun g A \<in> carrier_mat n n"
    and mat_fun_acts_on_eigenvectors: "acts_on_eigenvectors A g (mat_fun g A)"
proof -
  obtain U D where sd: "spectral_decomp A U D" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have "U * diag_matrix (map g D) * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    by (rule diag_conj_carrier) (use d(1,3) in simp_all)
  hence ex: "\<exists>B. B \<in> carrier_mat (dim_row A) (dim_row A) \<and> acts_on_eigenvectors A g B"
    using spectral_decomp_acts_on_eigenvectors[OF A(1) sd] A(1) by auto
  have "mat_fun g A \<in> carrier_mat (dim_row A) (dim_row A) \<and> acts_on_eigenvectors A g (mat_fun g A)"
    unfolding mat_fun_def by (rule someI_ex[OF ex])
  thus "mat_fun g A \<in> carrier_mat n n" "acts_on_eigenvectors A g (mat_fun g A)" using A(1) by auto
qed

text \<open>\[ Av=\lambda v\quad\Longrightarrow\quad g(A)\,v=g(\lambda)\,v. \]\<close>

theorem mat_fun_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and v: "dim_vec v = n" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  shows "mat_fun g A *\<^sub>v v = g l \<cdot>\<^sub>v v"
  using acts_on_eigenvectorsD[OF mat_fun_acts_on_eigenvectors[OF A] _ ev] v A(1) by simp

text \<open>Uniqueness: every $n\times n$ matrix acting as $g$ on the eigenvectors is $g(A)$.\<close>

lemma mat_fun_eqI:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and B: "B \<in> carrier_mat n n" "acts_on_eigenvectors A g B"
  shows "mat_fun g A = B"
proof (rule eigvec_mat_eqI[OF A mat_fun_carrier[OF A] B(1)])
  fix v l assume v: "dim_vec v = n" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  show "mat_fun g A *\<^sub>v v = B *\<^sub>v v"
    using acts_on_eigenvectorsD[OF mat_fun_acts_on_eigenvectors[OF A] _ ev] acts_on_eigenvectorsD[OF B(2) _ ev] v A(1) by simp
qed

text \<open>So for every spectral decomposition of $A$,
\[ g(A)=U\,\diag\bigl(g(D_1),\dots,g(D_n)\bigr)\,U^*. \]\<close>

theorem mat_fun_decomp:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and sd: "spectral_decomp A U D"
  shows "mat_fun g A = U * diag_matrix (map g D) * (U\<^sup>\<dagger>)"
proof (rule mat_fun_eqI[OF A])
  note d = spectral_decompD[OF A(1) sd]
  show "U * diag_matrix (map g D) * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    by (rule diag_conj_carrier) (use d(1,3) in simp_all)
  show "acts_on_eigenvectors A g (U * diag_matrix (map g D) * (U\<^sup>\<dagger>))"
    by (rule spectral_decomp_acts_on_eigenvectors[OF A(1) sd])
qed

text \<open>Only the values of $g$ on the spectrum matter.\<close>

lemma mat_fun_cong:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and gh: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> g l = h l"
  shows "mat_fun g A = mat_fun h A"
proof (rule mat_fun_eqI[OF A mat_fun_carrier[OF A]])
  show "acts_on_eigenvectors A g (mat_fun h A)" unfolding acts_on_eigenvectors_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have hv: "mat_fun h A *\<^sub>v v = h l \<cdot>\<^sub>v v" using mat_fun_eigen[OF A _ ev] v A(1) by simp
    show "mat_fun h A *\<^sub>v v = g l \<cdot>\<^sub>v v"
    proof (cases "v = 0\<^sub>v (dim_row A)")
      case True
      thus ?thesis using hv by (auto intro!: eq_vecI)
    next
      case False
      hence "l \<in> herm_spectrum A" unfolding herm_spectrum_iff using v ev by blast
      thus ?thesis using hv gh by simp
    qed
  qed
qed

subsection \<open>Algebra\<close>

text \<open>The identity function gives $A$, a constant $c$ gives $cI$:\<close>

lemma mat_fun_id: "A \<in> carrier_mat n n \<Longrightarrow> hermitian A \<Longrightarrow> mat_fun complex_of_real A = A"
  by (rule mat_fun_eqI) (auto simp: acts_on_eigenvectors_def)

lemma mat_fun_const:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "mat_fun (\<lambda>_. c) A = c \<cdot>\<^sub>m 1\<^sub>m n"
proof (rule mat_fun_eqI[OF A])
  show "acts_on_eigenvectors A (\<lambda>_. c) (c \<cdot>\<^sub>m 1\<^sub>m n)" unfolding acts_on_eigenvectors_def
    using A(1) by (auto simp: smult_mat_mult_mat_vec_assoc[of "1\<^sub>m n" n n])
qed simp

lemma mat_fun_one: "A \<in> carrier_mat n n \<Longrightarrow> hermitian A \<Longrightarrow> mat_fun (\<lambda>_. 1) A = 1\<^sub>m n"
  using mat_fun_const[of A n 1] by (auto intro!: eq_matI)

text \<open>The calculus is multiplicative and respects adjoints:
\[ g(A)\,h(A)=(gh)(A),\qquad g(A)^*=\overline g(A). \]\<close>

theorem mat_fun_mult:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "mat_fun g A * mat_fun h A = mat_fun (\<lambda>x. g x * h x) A"
proof (rule mat_fun_eqI[OF A, symmetric])
  show "mat_fun g A * mat_fun h A \<in> carrier_mat n n" by (rule mult_carrier_mat[OF mat_fun_carrier[OF A] mat_fun_carrier[OF A]])
  show "acts_on_eigenvectors A (\<lambda>x. g x * h x) (mat_fun g A * mat_fun h A)" unfolding acts_on_eigenvectors_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vn: "dim_vec v = n" using v A(1) by simp
    have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF vn])
    have "(mat_fun g A * mat_fun h A) *\<^sub>v v = mat_fun g A *\<^sub>v (mat_fun h A *\<^sub>v v)"
      by (rule assoc_mult_mat_vec[OF mat_fun_carrier[OF A] mat_fun_carrier[OF A] vc])
    also have "\<dots> = mat_fun g A *\<^sub>v (h l \<cdot>\<^sub>v v)" by (simp only: mat_fun_eigen[OF A vn ev])
    also have "\<dots> = h l \<cdot>\<^sub>v (mat_fun g A *\<^sub>v v)" by (rule mult_mat_vec[OF mat_fun_carrier[OF A] vc])
    also have "\<dots> = (g l * h l) \<cdot>\<^sub>v v" by (simp add: mat_fun_eigen[OF A vn ev] smult_smult_assoc mult.commute)
    finally show "(mat_fun g A * mat_fun h A) *\<^sub>v v = (g l * h l) \<cdot>\<^sub>v v" .
  qed
qed

theorem mat_fun_dagger:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "(mat_fun g A)\<^sup>\<dagger> = mat_fun (\<lambda>x. cnj (g x)) A"
proof -
  obtain U D where sd: "spectral_decomp A U D" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have gc: "diag_matrix (map g D) \<in> carrier_mat n n" using d(3) diag_matrix_carrier by (metis length_map)
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF d(1)])
  have cg: "diag_matrix (map (\<lambda>x. cnj (g x)) D) \<in> carrier_mat n n"
    using diag_matrix_carrier[of "map (\<lambda>x. cnj (g x)) D"] d(3) by simp
  have Ug: "U * diag_matrix (map g D) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF d(1) gc])
  have "(U * diag_matrix (map g D) * (U\<^sup>\<dagger>))\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * diag_matrix (map g D))\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use d(1,3) in simp)
  also have "\<dots> = U * (((diag_matrix (map g D))\<^sup>\<dagger>) * (U\<^sup>\<dagger>))"
    using dagger_of_prod[of U "diag_matrix (map g D)"] d(1,3) gc by (simp add: dagger_of_dagger_is_id)
  also have "\<dots> = U * (diag_matrix (map (\<lambda>x. cnj (g x)) D) * (U\<^sup>\<dagger>))"
    by (simp add: diag_matrix_dagger o_def)
  also have "\<dots> = U * diag_matrix (map (\<lambda>x. cnj (g x)) D) * (U\<^sup>\<dagger>)"
    by (rule assoc_mult_mat[OF d(1) cg Ud, symmetric])
  finally show ?thesis using mat_fun_decomp[OF A sd] by simp
qed

text \<open>Hence $f(A)$ is Hermitian for real $f$, and $g(A)$ is unitary when $|g|=1$ on the spectrum, since
$g(A)^*g(A)=|g|^2(A)=I$.\<close>

lemma mat_fun_hermitian:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "hermitian (mat_fun (\<lambda>x. complex_of_real (f x)) A)"
  unfolding hermitian_dagger by (simp add: mat_fun_dagger[OF A])

theorem mat_fun_unitary:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and g: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> cmod (g l) = 1"
  shows "unitary (mat_fun g A)"
proof -
  have c: "mat_fun (\<lambda>x. cnj (g x) * g x) A = 1\<^sub>m n" "mat_fun (\<lambda>x. g x * cnj (g x)) A = 1\<^sub>m n"
  proof -
    have e: "cnj (g l) * g l = 1" "g l * cnj (g l) = 1" if "l \<in> herm_spectrum A" for l
    proof -
      have "g l * cnj (g l) = complex_of_real ((cmod (g l))\<^sup>2)" by (rule complex_norm_square[symmetric])
      thus "g l * cnj (g l) = 1" "cnj (g l) * g l = 1" using g[OF that] by (simp_all add: mult.commute)
    qed
    show "mat_fun (\<lambda>x. cnj (g x) * g x) A = 1\<^sub>m n"
      using mat_fun_cong[OF A, of "\<lambda>x. cnj (g x) * g x" "\<lambda>_. 1"] e(1) mat_fun_one[OF A] by simp
    show "mat_fun (\<lambda>x. g x * cnj (g x)) A = 1\<^sub>m n"
      using mat_fun_cong[OF A, of "\<lambda>x. g x * cnj (g x)" "\<lambda>_. 1"] e(2) mat_fun_one[OF A] by simp
  qed
  show ?thesis unfolding unitary_def
    using c mat_fun_mult[OF A] mat_fun_dagger[OF A] carrier_matD[OF mat_fun_carrier[OF A, of g]] by simp
qed

text \<open>Powers: $G^{i+j}=G^iG^j$, and $Uu=zu$ implies $U^ku=z^ku$.\<close>

lemma pow_mat_add: "G \<in> carrier_mat m m \<Longrightarrow> G ^\<^sub>m (i + j) = G ^\<^sub>m i * G ^\<^sub>m j"
proof (induction j)
  case 0
  show ?case using 0 by simp
next
  case (Suc j)
  have "G ^\<^sub>m (i + Suc j) = G ^\<^sub>m i * G ^\<^sub>m j * G" using Suc by simp
  also have "\<dots> = G ^\<^sub>m i * (G ^\<^sub>m j * G)" by (rule assoc_mult_mat) (use Suc.prems in auto)
  finally show ?case by simp
qed

lemma pow_eigen:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat m m" and u: "dim_vec u = m" and ev: "U *\<^sub>v u = z \<cdot>\<^sub>v u"
  shows "(U ^\<^sub>m k) *\<^sub>v u = z ^ k \<cdot>\<^sub>v u"
proof (induction k)
  case 0
  have "u \<in> carrier_vec m" using u by (rule carrier_vecI)
  thus ?case using carrier_matD(1)[OF U] by (auto intro!: eq_vecI)
next
  case (Suc k)
  have uc: "u \<in> carrier_vec m" using u by (rule carrier_vecI)
  have "(U ^\<^sub>m Suc k) *\<^sub>v u = (U ^\<^sub>m k) *\<^sub>v (U *\<^sub>v u)"
    using assoc_mult_mat_vec[OF pow_carrier_mat[OF U] U uc, of k] by simp
  also have "\<dots> = z \<cdot>\<^sub>v ((U ^\<^sub>m k) *\<^sub>v u)" unfolding ev by (rule mult_mat_vec[OF pow_carrier_mat[OF U] uc])
  also have "\<dots> = z ^ Suc k \<cdot>\<^sub>v u" unfolding Suc by (simp add: smult_smult_assoc)
  finally show ?case .
qed

subsection \<open>Time evolution\<close>

text \<open>$e^{itA}$, the evolution under the Hamiltonian $A$.\<close>

definition evolution :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "evolution A t = mat_fun (\<lambda>x. cis (t * x)) A"

context
  fixes A :: "complex Matrix.mat" and n :: nat
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
begin

text \<open>$e^{itA}$ is unitary, acts on an eigenvector by $e^{itA}v=e^{it\lambda}v$, and is a one-parameter group:
\[ e^{i0A}=I,\qquad e^{i(s+t)A}=e^{isA}e^{itA},\qquad \bigl(e^{itA}\bigr)^k=e^{iktA}. \]\<close>

lemma evolution_carrier [simp]: "evolution A t \<in> carrier_mat n n"
  unfolding evolution_def using A by simp

lemma evolution_eigen:
  "dim_vec v = n \<Longrightarrow> A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v \<Longrightarrow> evolution A t *\<^sub>v v = cis (t * l) \<cdot>\<^sub>v v"
  unfolding evolution_def by (rule mat_fun_eigen[OF A])

lemma evolution_unitary: "unitary (evolution A t)"
  unfolding evolution_def by (rule mat_fun_unitary[OF A]) simp

lemma evolution_zero: "evolution A 0 = 1\<^sub>m n"
  unfolding evolution_def using mat_fun_one[OF A] by simp

lemma evolution_add: "evolution A (s + t) = evolution A s * evolution A t"
  unfolding evolution_def mat_fun_mult[OF A] by (simp add: cis_mult distrib_right)

lemma evolution_pow: "evolution A t ^\<^sub>m k = evolution A (real k * t)"
proof (induction k)
  case 0
  show ?case using evolution_zero carrier_matD(1)[OF evolution_carrier] by simp
next
  case (Suc k)
  have "evolution A t ^\<^sub>m Suc k = evolution A (real k * t) * evolution A t" using Suc by simp
  also have "\<dots> = evolution A (real (Suc k) * t)" by (simp add: evolution_add[symmetric] distrib_right add.commute)
  finally show ?case .
qed

end

subsection \<open>The inverse\<close>

text \<open>$A^{-1}=g(A)$ for $g(x)=1/x$; since $1/0=0$ in HOL this is the pseudo-inverse in general.\<close>

definition herm_inv :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "herm_inv A = mat_fun (\<lambda>x. complex_of_real (inverse x)) A"

text \<open>If $0$ is not an eigenvalue, $g(x)=1/x$ gives the inverse: $A^{-1}A=AA^{-1}=I$.\<close>

theorem herm_inv:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and z: "0 \<notin> herm_spectrum A"
  shows "herm_inv A * A = 1\<^sub>m n" "A * herm_inv A = 1\<^sub>m n"
proof -
  have "mat_fun (\<lambda>x. complex_of_real (inverse x) * complex_of_real x) A = mat_fun (\<lambda>_. 1) A"
       "mat_fun (\<lambda>x. complex_of_real x * complex_of_real (inverse x)) A = mat_fun (\<lambda>_. 1) A"
    by (rule mat_fun_cong[OF A], metis z of_real_eq_0_iff left_inverse right_inverse of_real_inverse)+
  thus "herm_inv A * A = 1\<^sub>m n" "A * herm_inv A = 1\<^sub>m n"
    unfolding herm_inv_def using mat_fun_mult[OF A] mat_fun_id[OF A] mat_fun_one[OF A] by metis+
qed

text \<open>So $x=A^{-1}b$ solves $Ax=b$; $A^{-1}$ acts on eigenvectors by $\lambda^{-1}$ and is Hermitian.\<close>

lemma herm_inv_solves:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and z: "0 \<notin> herm_spectrum A" and b: "dim_vec b = n"
  shows "A *\<^sub>v (herm_inv A *\<^sub>v b) = b"
proof -
  have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
  have "A *\<^sub>v (herm_inv A *\<^sub>v b) = (A * herm_inv A) *\<^sub>v b" by (rule assoc_mult_mat_vec[symmetric, OF A(1) Hc]) (use b in auto)
  also have "A * herm_inv A = 1\<^sub>m n" by (rule herm_inv(2)[OF A z])
  finally show ?thesis using b by (simp add: one_mult_mat_vec[OF carrier_vecI[OF b]])
qed

lemma herm_inv_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and v: "dim_vec v = n" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  shows "herm_inv A *\<^sub>v v = complex_of_real (inverse l) \<cdot>\<^sub>v v"
  unfolding herm_inv_def by (rule mat_fun_eigen[OF A v ev])

lemma herm_inv_hermitian: "A \<in> carrier_mat n n \<Longrightarrow> hermitian A \<Longrightarrow> hermitian (herm_inv A)"
  unfolding herm_inv_def by (rule mat_fun_hermitian)

lemma mult_zero_vec_right: "B \<in> carrier_mat K n \<Longrightarrow> B *\<^sub>v 0\<^sub>v n = 0\<^sub>v K"
  by (rule eq_vecI) (auto simp: scalar_prod_def)

text \<open>For a unit vector $b$ and invertible $A$ the solution $A^{-1}b$ is not zero.\<close>

lemma herm_inv_sol_pos:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and z: "0 \<notin> herm_spectrum A" and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1"
  shows "0 < \<parallel>herm_inv A *\<^sub>v b\<parallel>"
proof (rule vnorm_pos)
  have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
  thus "dim_vec (herm_inv A *\<^sub>v b) = n" by simp
  show "herm_inv A *\<^sub>v b \<noteq> 0\<^sub>v n"
  proof
    assume "herm_inv A *\<^sub>v b = 0\<^sub>v n"
    hence "b = 0\<^sub>v n" using herm_inv_solves[OF A z b(1)] mult_zero_vec_right[OF A(1)] by simp
    thus False using b(2) vnorm_zero_vec by simp
  qed
qed

end
