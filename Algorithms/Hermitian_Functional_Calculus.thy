theory Hermitian_Functional_Calculus
  imports Vern_Paulsen_QC_3_10.Quantum_Computing_3_10
begin

section \<open>Functional calculus for Hermitian matrices\<close>

text \<open>For Hermitian $A$ and $g:\mathbb R\to\mathbb C$, $g(A)$ is the matrix that acts on every
eigenvector $v$ of $A$ with eigenvalue $\lambda$ as multiplication by $g(\lambda)$.  The
eigenvectors span $\C^n$, so this determines $g(A)$; for a spectral decomposition
$A=U\,\mathrm{diag}(D)\,U^*$ it is $U\,\mathrm{diag}(g\circ D)\,U^*$.\<close>

definition diag_cmat :: "complex list \<Rightarrow> complex Matrix.mat" where
  "diag_cmat xs = Matrix.mat (length xs) (length xs) (\<lambda>(i,j). if i = j then xs ! i else 0)"

lemma diag_cmat_carrier [simp]: "diag_cmat xs \<in> carrier_mat (length xs) (length xs)"
  by (simp add: diag_cmat_def)

lemma dim_diag_cmat [simp]: "dim_row (diag_cmat xs) = length xs" "dim_col (diag_cmat xs) = length xs"
  by (simp_all add: diag_cmat_def)

lemma diag_mat_of_real_cmat: "diag_mat_of_real D = diag_cmat (map complex_of_real D)"
  by (rule eq_matI) (auto simp: diag_mat_of_real_def diag_cmat_def)

lemma diag_cmat_mult_vec:
  assumes "dim_vec w = length xs"
  shows "diag_cmat xs *\<^sub>v w = Matrix.vec (length xs) (\<lambda>i. xs ! i * w $ i)"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (Matrix.vec (length xs) (\<lambda>i. xs ! i * w $ i))"
  hence i: "i < length xs" by simp
  have "(diag_cmat xs *\<^sub>v w) $ i = (\<Sum>k = 0..<length xs. (if i = k then xs ! i else 0) * w $ k)"
    using i assms by (simp add: diag_cmat_def mult_mat_vec_def scalar_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<length xs. if k = i then xs ! i * w $ i else 0)"
    by (rule sum.cong) auto
  also have "\<dots> = xs ! i * w $ i" using i by simp
  finally show "(diag_cmat xs *\<^sub>v w) $ i = Matrix.vec (length xs) (\<lambda>i. xs ! i * w $ i) $ i"
    using i by simp
qed simp

lemma col_mult_diag:
  assumes M: "M \<in> carrier_mat n (length xs)" and j: "j < length xs"
  shows "Matrix.col (M * diag_cmat xs) j = xs ! j \<cdot>\<^sub>v Matrix.col M j"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (xs ! j \<cdot>\<^sub>v Matrix.col M j)"
  hence i: "i < n" using M by simp
  have "Matrix.col (M * diag_cmat xs) j $ i = (\<Sum>k = 0..<length xs. M $$ (i, k) * (if k = j then xs ! k else 0))"
    using M i j by (simp add: diag_cmat_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k = 0..<length xs. if k = j then M $$ (i, j) * xs ! j else 0)"
    by (rule sum.cong) auto
  also have "\<dots> = M $$ (i, j) * xs ! j" using j by simp
  finally show "Matrix.col (M * diag_cmat xs) j $ i = (xs ! j \<cdot>\<^sub>v Matrix.col M j) $ i"
    using M i j by (simp add: mult.commute)
qed (use M in simp)

lemma diag_cmat_dagger: "(diag_cmat xs)\<^sup>\<dagger> = diag_cmat (map cnj xs)"
  by (rule eq_matI) (auto simp: diag_cmat_def dagger_def)

lemma diag_conj_carrier:
  assumes U: "U \<in> carrier_mat n n" and xs: "length xs = n"
  shows "U * diag_cmat xs * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
proof -
  have "diag_cmat xs \<in> carrier_mat n n" using diag_cmat_carrier[of xs] xs by simp
  thus ?thesis using mult_carrier_mat[OF mult_carrier_mat[OF U] dagger_carrier[OF U]] by blast
qed

subsection \<open>Spectral decompositions\<close>

text \<open>\<open>spectral_decomp A U D\<close>: $U$ unitary and $U^*AU=\mathrm{diag}(D)$.\<close>

definition spectral_decomp :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real list \<Rightarrow> bool" where
  "spectral_decomp A U D \<longleftrightarrow> U \<in> carrier_mat (dim_row A) (dim_row A) \<and> unitary U \<and>
     length D = dim_row A \<and> U\<^sup>\<dagger> * A * U = diag_mat_of_real D"

lemma spectral_decomp_exists:
  assumes "A \<in> carrier_mat n n" "hermitian A"
  shows "\<exists>U D. spectral_decomp A U D"
  using hermitian_spectral_decomp[OF assms] assms(1) unfolding spectral_decomp_def by auto

lemma spectral_decompD:
  assumes A: "A \<in> carrier_mat n n" and sd: "spectral_decomp A U D"
  shows "U \<in> carrier_mat n n" "unitary U" "length D = n" "U\<^sup>\<dagger> * U = 1\<^sub>m n" "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    "A = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" "A * U = U * diag_mat_of_real D"
proof -
  show U: "U \<in> carrier_mat n n" and u: "unitary U" and D: "length D = n"
    using sd A unfolding spectral_decomp_def by auto
  show "U\<^sup>\<dagger> * U = 1\<^sub>m n" "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using u U unfolding unitary_def by auto
  have e: "U\<^sup>\<dagger> * A * U = diag_mat_of_real D" using sd unfolding spectral_decomp_def by auto
  show "A = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF U A u e])
  show "A * U = U * diag_mat_of_real D" by (rule hermitian_spectral_decomp_right[OF U A u e])
qed

text \<open>The columns of $U$ are eigenvectors: $Au_j=D_ju_j$.\<close>

lemma spectral_decomp_col:
  assumes A: "A \<in> carrier_mat n n" and sd: "spectral_decomp A U D" and j: "j < n"
  shows "A *\<^sub>v Matrix.col U j = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j"
proof -
  note d = spectral_decompD[OF A sd]
  have "A *\<^sub>v Matrix.col U j = Matrix.col (A * U) j" by (rule col_mult2[OF A d(1) j, symmetric])
  also have "\<dots> = Matrix.col (U * diag_cmat (map complex_of_real D)) j"
    using d(7) by (simp add: diag_mat_of_real_cmat)
  also have "\<dots> = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j"
    using col_mult_diag[of U n "map complex_of_real D" j] d(1,3) j by simp
  finally show ?thesis .
qed

subsection \<open>The definition\<close>

definition fun_on_eigen :: "complex Matrix.mat \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "fun_on_eigen A g B \<longleftrightarrow> (\<forall>v l. dim_vec v = dim_row A \<longrightarrow>
     A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v \<longrightarrow> B *\<^sub>v v = g l \<cdot>\<^sub>v v)"

definition mat_fun :: "(real \<Rightarrow> complex) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "mat_fun g A = (SOME B. B \<in> carrier_mat (dim_row A) (dim_row A) \<and> fun_on_eigen A g B)"

definition herm_spectrum :: "complex Matrix.mat \<Rightarrow> real set" where
  "herm_spectrum A = {l. \<exists>v. dim_vec v = dim_row A \<and> v \<noteq> 0\<^sub>v (dim_row A) \<and>
     A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v}"

lemma fun_on_eigenD:
  "fun_on_eigen A g B \<Longrightarrow> dim_vec v = dim_row A \<Longrightarrow> A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v \<Longrightarrow>
   B *\<^sub>v v = g l \<cdot>\<^sub>v v"
  unfolding fun_on_eigen_def by blast

text \<open>$U\,\mathrm{diag}(g\circ D)\,U^*$ acts correctly on eigenvectors: if $Av=\lambda v$ then
$w=U^*v$ has $D_iw_i=\lambda w_i$, so $g(D_i)w_i=g(\lambda)w_i$.\<close>

lemma spectral_decomp_fun_on_eigen:
  assumes A: "A \<in> carrier_mat n n" and sd: "spectral_decomp A U D"
  shows "fun_on_eigen A g (U * diag_cmat (map g D) * (U\<^sup>\<dagger>))"
  unfolding fun_on_eigen_def
proof (intro allI impI)
  fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  note d = spectral_decompD[OF A sd]
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI) (use v A in simp)
  have Uc: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF d(1)])
  define w where "w = U\<^sup>\<dagger> *\<^sub>v v"
  have wc: "w \<in> carrier_vec n" unfolding w_def using Uc vc by simp
  have Uw: "U *\<^sub>v w = v"
    unfolding w_def using assoc_mult_mat_vec[OF d(1) Uc vc, symmetric] d(5) vc by simp
  have "diag_mat_of_real D *\<^sub>v w = (U\<^sup>\<dagger> * A * U) *\<^sub>v w"
    using sd unfolding spectral_decomp_def by simp
  also have "\<dots> = U\<^sup>\<dagger> *\<^sub>v (A *\<^sub>v (U *\<^sub>v w))"
    using Uc A d(1) wc by (simp add: assoc_mult_mat_vec[of _ n n _ n])
  also have "\<dots> = complex_of_real l \<cdot>\<^sub>v w"
    unfolding Uw ev unfolding w_def by (rule mult_mat_vec[OF Uc vc])
  finally have Dw: "diag_mat_of_real D *\<^sub>v w = complex_of_real l \<cdot>\<^sub>v w" .
  have wi: "w $ i = 0 \<or> D ! i = l" if i: "i < n" for i
  proof -
    have "(diag_mat_of_real D *\<^sub>v w) $ i = complex_of_real (D ! i) * w $ i"
      using diag_cmat_mult_vec[of w "map complex_of_real D"] wc d(3) i
      by (simp add: diag_mat_of_real_cmat)
    hence "complex_of_real (D ! i) * w $ i = complex_of_real l * w $ i"
      using Dw i wc by (metis carrier_vecD index_smult_vec(1))
    thus ?thesis by auto
  qed
  have gw: "diag_cmat (map g D) *\<^sub>v w = g l \<cdot>\<^sub>v w"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (g l \<cdot>\<^sub>v w)"
    hence i: "i < n" using wc by simp
    show "(diag_cmat (map g D) *\<^sub>v w) $ i = (g l \<cdot>\<^sub>v w) $ i"
      using diag_cmat_mult_vec[of w "map g D"] wc d(3) i wi[OF i] by auto
  qed (use wc d(3) in simp)
  have gc: "diag_cmat (map g D) \<in> carrier_mat n n" using d(3) diag_cmat_carrier by (metis length_map)
  have "(U * diag_cmat (map g D) * (U\<^sup>\<dagger>)) *\<^sub>v v = U *\<^sub>v (diag_cmat (map g D) *\<^sub>v w)"
    unfolding w_def assoc_mult_mat_vec[OF mult_carrier_mat[OF d(1) gc] Uc vc]
    by (rule assoc_mult_mat_vec[OF d(1) gc mult_mat_vec_carrier[OF Uc vc]])
  also have "\<dots> = g l \<cdot>\<^sub>v (U *\<^sub>v w)" unfolding gw using d(1) wc by (rule mult_mat_vec)
  also note Uw
  finally show "(U * diag_cmat (map g D) * (U\<^sup>\<dagger>)) *\<^sub>v v = g l \<cdot>\<^sub>v v" .
qed

text \<open>Uniqueness: two matrices that agree on the eigenvectors $u_j$ agree on $U$, hence are equal.\<close>

lemma fun_on_eigen_unique:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and B1: "B1 \<in> carrier_mat n n" "fun_on_eigen A g B1"
      and B2: "B2 \<in> carrier_mat n n" "fun_on_eigen A g B2"
  shows "B1 = B2"
proof -
  obtain U D where sd: "spectral_decomp A U D" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have cU: "dim_vec (Matrix.col U j) = dim_row A" for j using d(1) A(1) by simp
  have BU: "B1 * U = B2 * U"
  proof (rule Matrix.mat_col_eqI)
    fix j assume "j < dim_col (B2 * U)"
    hence j: "j < n" using d(1) by simp
    have ev: "A *\<^sub>v Matrix.col U j = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j" by (rule spectral_decomp_col[OF A(1) sd j])
    have "Matrix.col (B1 * U) j = B1 *\<^sub>v Matrix.col U j" by (rule col_mult2[OF B1(1) d(1) j])
    also have "\<dots> = g (D ! j) \<cdot>\<^sub>v Matrix.col U j" by (rule fun_on_eigenD[OF B1(2) cU ev])
    also have "\<dots> = B2 *\<^sub>v Matrix.col U j" by (rule fun_on_eigenD[OF B2(2) cU ev, symmetric])
    also have "\<dots> = Matrix.col (B2 * U) j" by (rule col_mult2[OF B2(1) d(1) j, symmetric])
    finally show "Matrix.col (B1 * U) j = Matrix.col (B2 * U) j" .
  qed (use B1(1) B2(1) d(1) in simp_all)
  have "B1 = (B1 * U) * (U\<^sup>\<dagger>)"
    using assoc_mult_mat[OF B1(1) d(1) dagger_carrier[OF d(1)]] d(5) B1(1) by simp
  also have "\<dots> = (B2 * U) * (U\<^sup>\<dagger>)" by (simp only: BU)
  also have "\<dots> = B2"
    using assoc_mult_mat[OF B2(1) d(1) dagger_carrier[OF d(1)]] d(5) B2(1) by simp
  finally show ?thesis .
qed

lemma
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows mat_fun_carrier [simp]: "mat_fun g A \<in> carrier_mat n n"
    and mat_fun_on_eigen: "fun_on_eigen A g (mat_fun g A)"
proof -
  obtain U D where sd: "spectral_decomp A U D" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have "U * diag_cmat (map g D) * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    by (rule diag_conj_carrier) (use d(1,3) in simp_all)
  hence ex: "\<exists>B. B \<in> carrier_mat (dim_row A) (dim_row A) \<and> fun_on_eigen A g B"
    using spectral_decomp_fun_on_eigen[OF A(1) sd] A(1) by auto
  have "mat_fun g A \<in> carrier_mat (dim_row A) (dim_row A) \<and> fun_on_eigen A g (mat_fun g A)"
    unfolding mat_fun_def by (rule someI_ex[OF ex])
  thus "mat_fun g A \<in> carrier_mat n n" "fun_on_eigen A g (mat_fun g A)" using A(1) by auto
qed

theorem mat_fun_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and v: "dim_vec v = n" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  shows "mat_fun g A *\<^sub>v v = g l \<cdot>\<^sub>v v"
  using fun_on_eigenD[OF mat_fun_on_eigen[OF A] _ ev] v A(1) by simp

lemma mat_fun_eqI:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and B: "B \<in> carrier_mat n n" "fun_on_eigen A g B"
  shows "mat_fun g A = B"
  by (rule fun_on_eigen_unique[OF A mat_fun_carrier[OF A] mat_fun_on_eigen[OF A] B])

theorem mat_fun_decomp:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and sd: "spectral_decomp A U D"
  shows "mat_fun g A = U * diag_cmat (map g D) * (U\<^sup>\<dagger>)"
proof (rule mat_fun_eqI[OF A])
  note d = spectral_decompD[OF A(1) sd]
  show "U * diag_cmat (map g D) * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    by (rule diag_conj_carrier) (use d(1,3) in simp_all)
  show "fun_on_eigen A g (U * diag_cmat (map g D) * (U\<^sup>\<dagger>))"
    by (rule spectral_decomp_fun_on_eigen[OF A(1) sd])
qed

text \<open>Only the values of $g$ on the spectrum matter.\<close>

lemma mat_fun_cong:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and gh: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> g l = h l"
  shows "mat_fun g A = mat_fun h A"
proof (rule mat_fun_eqI[OF A mat_fun_carrier[OF A]])
  show "fun_on_eigen A g (mat_fun h A)" unfolding fun_on_eigen_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have hv: "mat_fun h A *\<^sub>v v = h l \<cdot>\<^sub>v v" using mat_fun_eigen[OF A _ ev] v A(1) by simp
    show "mat_fun h A *\<^sub>v v = g l \<cdot>\<^sub>v v"
    proof (cases "v = 0\<^sub>v (dim_row A)")
      case True
      thus ?thesis using hv by (auto intro!: eq_vecI)
    next
      case False
      hence "l \<in> herm_spectrum A" unfolding herm_spectrum_def using v ev by blast
      thus ?thesis using hv gh by simp
    qed
  qed
qed

subsection \<open>Algebra\<close>

lemma mat_fun_id: "A \<in> carrier_mat n n \<Longrightarrow> hermitian A \<Longrightarrow> mat_fun complex_of_real A = A"
  by (rule mat_fun_eqI) (auto simp: fun_on_eigen_def)

lemma mat_fun_const:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "mat_fun (\<lambda>_. c) A = c \<cdot>\<^sub>m 1\<^sub>m n"
proof (rule mat_fun_eqI[OF A])
  show "fun_on_eigen A (\<lambda>_. c) (c \<cdot>\<^sub>m 1\<^sub>m n)" unfolding fun_on_eigen_def
    using A(1) by (auto simp: smult_mat_mult_vec[of "1\<^sub>m n" n n])
qed simp

lemma mat_fun_one: "A \<in> carrier_mat n n \<Longrightarrow> hermitian A \<Longrightarrow> mat_fun (\<lambda>_. 1) A = 1\<^sub>m n"
  using mat_fun_const[of A n 1] by (auto intro!: eq_matI)

theorem mat_fun_mult:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "mat_fun g A * mat_fun h A = mat_fun (\<lambda>x. g x * h x) A"
proof (rule mat_fun_eqI[OF A, symmetric])
  show "mat_fun g A * mat_fun h A \<in> carrier_mat n n" by (rule mult_carrier_mat[OF mat_fun_carrier[OF A] mat_fun_carrier[OF A]])
  show "fun_on_eigen A (\<lambda>x. g x * h x) (mat_fun g A * mat_fun h A)" unfolding fun_on_eigen_def
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
  have gc: "diag_cmat (map g D) \<in> carrier_mat n n" using d(3) diag_cmat_carrier by (metis length_map)
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF d(1)])
  have cg: "diag_cmat (map (\<lambda>x. cnj (g x)) D) \<in> carrier_mat n n"
    using diag_cmat_carrier[of "map (\<lambda>x. cnj (g x)) D"] d(3) by simp
  have Ug: "U * diag_cmat (map g D) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF d(1) gc])
  have "(U * diag_cmat (map g D) * (U\<^sup>\<dagger>))\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * diag_cmat (map g D))\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use d(1,3) in simp)
  also have "\<dots> = U * (((diag_cmat (map g D))\<^sup>\<dagger>) * (U\<^sup>\<dagger>))"
    using dagger_of_prod[of U "diag_cmat (map g D)"] d(1,3) gc by (simp add: dagger_of_dagger_is_id)
  also have "\<dots> = U * (diag_cmat (map (\<lambda>x. cnj (g x)) D) * (U\<^sup>\<dagger>))"
    by (simp add: diag_cmat_dagger o_def)
  also have "\<dots> = U * diag_cmat (map (\<lambda>x. cnj (g x)) D) * (U\<^sup>\<dagger>)"
    by (rule assoc_mult_mat[OF d(1) cg Ud, symmetric])
  finally show ?thesis using mat_fun_decomp[OF A sd] by simp
qed

lemma mat_fun_hermitian:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "hermitian (mat_fun (\<lambda>x. complex_of_real (f x)) A)"
  unfolding hermitian_def by (simp add: mat_fun_dagger[OF A])

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

subsection \<open>Time evolution\<close>

text \<open>$e^{itA}$, the evolution under the Hamiltonian $A$ (phase estimation uses $U=e^{itA}$).\<close>

definition evolution :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "evolution A t = mat_fun (\<lambda>x. cis (t * x)) A"

context
  fixes A :: "complex Matrix.mat" and n :: nat
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
begin

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

lemma herm_inv_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
      and v: "dim_vec v = n" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
  shows "herm_inv A *\<^sub>v v = complex_of_real (inverse l) \<cdot>\<^sub>v v"
  unfolding herm_inv_def by (rule mat_fun_eigen[OF A v ev])

lemma herm_inv_hermitian: "A \<in> carrier_mat n n \<Longrightarrow> hermitian A \<Longrightarrow> hermitian (herm_inv A)"
  unfolding herm_inv_def by (rule mat_fun_hermitian)

end
