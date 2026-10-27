theory Day21_Ranges
  imports Day02_Projection_Basis Day04_Hermitian_Matrices
begin

section \<open>Day 21: ranges of positive matrices (D21-4)\<close>

text \<open>If $A\ge B\ge0$ then $\ker A\subseteq\ker B$: for $Ax=0$,
$0=\braket x{Ax}=\braket x{Bx}+\braket x{(A-B)x}$ with both terms $\ge0$, so $\braket x{Bx}=0$; writing
$B=NN^*$ this is $\norm{N^*x}^2=0$, hence $Bx=N(N^*x)=0$.\<close>

lemma loewner_ker_subset:
  fixes A B :: "complex Matrix.mat" and x :: "complex Matrix.vec"
  assumes A_c: "A \<in> carrier_mat k k"
      and B_c: "B \<in> carrier_mat k k"
      and B_psd: "psd B"
      and diff_psd: "psd (A - B)"
      and x_dim: "dim_vec x = k"
      and Ax_zero: "A *\<^sub>v x = 0\<^sub>v k"
  shows "B *\<^sub>v x = 0\<^sub>v k"
proof -
  have AmB_c: "A - B \<in> carrier_mat k k" using A_c B_c by auto
  have Bx_dim: "dim_vec (B *\<^sub>v x) = k" using B_c x_dim by auto
  have Ax_dim: "dim_vec (A *\<^sub>v x) = k" using A_c x_dim by auto
  have AmBx_dim: "dim_vec ((A - B) *\<^sub>v x) = k" using AmB_c x_dim by auto
  have x_car: "x \<in> carrier_vec k" using x_dim by auto

  \<comment> \<open>Step 1: \<open>\<langle>x | A x\<rangle> = 0\<close> because \<open>A x = 0\<close>.\<close>
  have Ax_inner_zero: "\<langle>x | A *\<^sub>v x\<rangle> = 0"
    using Ax_zero x_dim by (simp add: inner_prod_def)

  \<comment> \<open>Step 2: linearity: \<open>\<langle>x | (A-B) x\<rangle> = \<langle>x | A x\<rangle> - \<langle>x | B x\<rangle>\<close>.\<close>
  have AmBx_eq: "(A - B) *\<^sub>v x = A *\<^sub>v x - B *\<^sub>v x"
    using minus_mult_distrib_mat_vec[OF A_c B_c x_car] .
  have dim_AB_eq: "dim_vec (A *\<^sub>v x) = dim_vec (B *\<^sub>v x)"
    using Ax_dim Bx_dim by simp
  have inner_diff: "\<langle>x | (A - B) *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x\<rangle> - \<langle>x | B *\<^sub>v x\<rangle>"
  proof -
    have "\<langle>x | (A - B) *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x - B *\<^sub>v x\<rangle>"
      using AmBx_eq by simp
    also have "\<dots> = \<langle>x | A *\<^sub>v x\<rangle> - \<langle>x | B *\<^sub>v x\<rangle>"
      by (rule inner_prod_right_minus'[OF dim_AB_eq])
    finally show ?thesis .
  qed

  \<comment> \<open>Step 3: PSD on both sides forces \<open>Re \<langle>x | B x\<rangle> = 0\<close>.\<close>
  have dim_B: "dim_vec x = dim_row B" using x_dim B_c by auto
  have dim_AmB: "dim_vec x = dim_row (A - B)" using x_dim AmB_c by auto
  have Re_B_nn: "Re \<langle>x | B *\<^sub>v x\<rangle> \<ge> 0"
    using B_psd dim_B unfolding psd_def by blast
  have Re_AmB_nn: "Re \<langle>x | (A - B) *\<^sub>v x\<rangle> \<ge> 0"
    using diff_psd dim_AmB unfolding psd_def by blast
  have Re_neg: "Re \<langle>x | (A - B) *\<^sub>v x\<rangle> = - Re \<langle>x | B *\<^sub>v x\<rangle>"
    using inner_diff Ax_inner_zero by simp
  have Re_B_zero: "Re \<langle>x | B *\<^sub>v x\<rangle> = 0"
    using Re_B_nn Re_AmB_nn Re_neg by linarith

  \<comment> \<open>Step 4: Hermiticity of B makes \<open>\<langle>x | B x\<rangle>\<close> real, so it equals 0.\<close>
  have B_herm: "hermitian B" using B_psd by (rule psd_hermitian)
  have B_real: "\<langle>x | B *\<^sub>v x\<rangle> \<in> \<real>"
    using hermitian_iff_real_quad_form[OF B_c] B_herm x_dim by blast
  have B_inner_zero: "\<langle>x | B *\<^sub>v x\<rangle> = 0"
    using B_real Re_B_zero
    by (auto simp: complex_is_Real_iff complex_eq_iff)

  \<comment> \<open>Step 5: PSD-Kraus decomposition gives \<open>B = N N\<^sup>\<dagger>\<close>.\<close>
  obtain vs where vs_len: "length vs = k"
              and vs_dim_all: "\<forall>v \<in> set vs. dim_vec v = k"
              and outer_eq: "outer_sum k vs = B"
    using psd_kraus_decomp[OF B_c B_psd] by blast
  define N where "N \<equiv> mat_of_cols k vs"
  have N_c: "N \<in> carrier_mat k k"
    unfolding N_def using vs_len by auto
  have Ndag_c: "N\<^sup>\<dagger> \<in> carrier_mat k k" using N_c by auto
  have B_eq: "B = N * (N\<^sup>\<dagger>)"
    using outer_eq[symmetric] by (simp add: outer_sum_def N_def)

  \<comment> \<open>Step 6: \<open>\<langle>x | B x\<rangle> = \<langle>N\<^sup>\<dagger> x | N\<^sup>\<dagger> x\<rangle>\<close>.\<close>
  let ?y = "N\<^sup>\<dagger> *\<^sub>v x"
  have y_dim: "dim_vec ?y = k" using Ndag_c x_dim by auto
  have Bx_eq: "B *\<^sub>v x = N *\<^sub>v ?y"
  proof -
    have "B *\<^sub>v x = (N * (N\<^sup>\<dagger>)) *\<^sub>v x" using B_eq by simp
    also have "\<dots> = N *\<^sub>v (N\<^sup>\<dagger> *\<^sub>v x)"
      using N_c Ndag_c x_car by (simp add: assoc_mult_mat_vec)
    finally show ?thesis .
  qed
  have y_inner_eq: "\<langle>x | B *\<^sub>v x\<rangle> = \<langle>?y | ?y\<rangle>"
  proof -
    have "\<langle>x | B *\<^sub>v x\<rangle> = \<langle>x | N *\<^sub>v ?y\<rangle>" using Bx_eq by simp
    also have "\<dots> = \<langle>N\<^sup>\<dagger> *\<^sub>v x | ?y\<rangle>"
      using inner_prod_adjoint_swap[OF N_c x_dim y_dim] .
    finally show ?thesis by simp
  qed

  \<comment> \<open>Step 7: \<open>\<langle>?y | ?y\<rangle> = 0 \<Longrightarrow> ?y = 0\<close>.\<close>
  have y_inner_zero: "\<langle>?y | ?y\<rangle> = 0"
    using y_inner_eq B_inner_zero by simp
  have y_zero: "?y = 0\<^sub>v k"
  proof (rule ccontr)
    assume "?y \<noteq> 0\<^sub>v k"
    hence "?y \<noteq> 0\<^sub>v (dim_vec ?y)" using y_dim by simp
    hence "\<langle>?y | ?y\<rangle> \<noteq> 0"
      by (rule inner_prod_with_itself_nonneg_reals_non0)
    thus False using y_inner_zero by simp
  qed

  \<comment> \<open>Step 8: \<open>B x = N (N\<^sup>\<dagger> x) = N \<cdot> 0 = 0\<close>.\<close>
  have N_zero: "N *\<^sub>v 0\<^sub>v k = 0\<^sub>v k"
  proof (rule eq_vecI)
    show "dim_vec (N *\<^sub>v 0\<^sub>v k) = dim_vec (0\<^sub>v k)" using N_c by simp
  next
    fix i assume i_a: "i < dim_vec (0\<^sub>v k)"
    hence i_lt: "i < k" by simp
    have "(N *\<^sub>v 0\<^sub>v k) $ i = (\<Sum>j = 0..<k. N $$ (i,j) * 0)"
      using N_c i_lt by (simp add: scalar_prod_def)
    also have "\<dots> = 0" by simp
    finally show "(N *\<^sub>v 0\<^sub>v k) $ i = (0\<^sub>v k) $ i" using i_lt by simp
  qed
  have "B *\<^sub>v x = N *\<^sub>v ?y" using Bx_eq .
  also have "\<dots> = N *\<^sub>v 0\<^sub>v k" using y_zero by simp
  also have "\<dots> = 0\<^sub>v k" using N_zero .
  finally show ?thesis .
qed

text \<open>The notes write $R(P)$ for the range of $P$ (here \<open>mat_range k P\<close>) and use two facts: if
$0\le ww^*\le P$ then $w\in R(P)$, and $R(\sum_lw_lw_l^*)=\operatorname{span}\{w_l\}$
(\<open>col_span\<close>).  Both rest on one lemma: for Hermitian $P$, every vector orthogonal to $\ker P$
lies in $R(P)$; it is proved from the spectral decomposition $P=UDU^*$ by inverting the nonzero
eigenvalues.  The audit's earlier formal counterpart was the kernel form
@{thm [source] loewner_ker_subset}.\<close>

definition mat_range :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec set" where
  "mat_range k P = {P *\<^sub>v h | h. dim_vec h = k}"

lemma diag_mat_of_real_mult_vec:
  assumes "length D = k" "dim_vec v = k"
  shows "diag_mat_of_real D *\<^sub>v v = Matrix.vec k (\<lambda>i. complex_of_real (D ! i) * v $ i)"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (Matrix.vec k (\<lambda>i. complex_of_real (D ! i) * v $ i))"
  hence i: "i < k" by simp
  have "(diag_mat_of_real D *\<^sub>v v) $ i = (\<Sum>j<k. (if i = j then complex_of_real (D ! i) else 0) * v $ j)"
    using assms i by (simp add: diag_mat_of_real_def mat_diag_def scalar_prod_def atLeast0LessThan cong: if_cong)
  also have "\<dots> = (\<Sum>j<k. if j = i then complex_of_real (D ! i) * v $ j else 0)" by (rule sum.cong) auto
  also have "\<dots> = complex_of_real (D ! i) * v $ i" using i by simp
  finally show "(diag_mat_of_real D *\<^sub>v v) $ i = Matrix.vec k (\<lambda>i. complex_of_real (D ! i) * v $ i) $ i" using i by simp
qed (use assms in simp)

text \<open>For Hermitian $P$, a vector orthogonal to $\ker P$ lies in the range of $P$.\<close>

lemma hermitian_perp_ker_in_range:
  assumes P: "P \<in> carrier_mat k k" and h: "hermitian P" and w: "dim_vec w = k"
      and perp: "\<And>x. dim_vec x = k \<Longrightarrow> P *\<^sub>v x = 0\<^sub>v k \<Longrightarrow> Quantum.inner_prod x w = 0"
  shows "w \<in> mat_range k P"
proof -
  obtain U D where U: "U \<in> carrier_mat k k" and u: "unitary U" and D: "length D = k"
    and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF P h] by blast
  have Pe: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF U P u spec])
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat k k" by (rule dagger_carrier[OF U])
  have Dc: "diag_mat_of_real D \<in> carrier_mat k k" using D by (intro carrier_matI) simp_all
  have UdU: "U\<^sup>\<dagger> * U = 1\<^sub>m k" and UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m k"
    using u U unfolding unitary_def by (simp_all add: inverts_mat_def)
  have Papp: "P *\<^sub>v (U *\<^sub>v z) = U *\<^sub>v (diag_mat_of_real D *\<^sub>v z)" if z: "dim_vec z = k" for z
  proof -
    have zc: "z \<in> carrier_vec k" using z by (rule carrier_vecI)
    have "P *\<^sub>v (U *\<^sub>v z) = (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) *\<^sub>v (U *\<^sub>v z)" using Pe by simp
    also have "\<dots> = (U * diag_mat_of_real D * (U\<^sup>\<dagger>) * U) *\<^sub>v z"
    proof -
      have Mc: "U * diag_mat_of_real D * (U\<^sup>\<dagger>) \<in> carrier_mat k k" using U Dc Ud by simp
      show ?thesis by (rule assoc_mult_mat_vec[OF Mc U zc, symmetric])
    qed
    also have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) * U = U * diag_mat_of_real D"
    proof -
      have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) * U = U * diag_mat_of_real D * ((U\<^sup>\<dagger>) * U)"
        by (rule assoc_mult_mat[OF mult_carrier_mat[OF U Dc] Ud U])
      thus ?thesis unfolding UdU using right_mult_one_mat[OF mult_carrier_mat[OF U Dc]] by simp
    qed
    also have "(U * diag_mat_of_real D) *\<^sub>v z = U *\<^sub>v (diag_mat_of_real D *\<^sub>v z)"
      using U Dc zc by (simp add: assoc_mult_mat_vec)
    finally show ?thesis .
  qed
  define y where "y = U\<^sup>\<dagger> *\<^sub>v w"
  have yd: "dim_vec y = k" using carrier_matD[OF U] by (simp add: y_def)
  have y0: "y $ i = 0" if i: "i < k" and Di: "D ! i = 0" for i
  proof -
    let ?e = "unit_vec k i :: complex Matrix.vec"
    have "P *\<^sub>v (U *\<^sub>v ?e) = U *\<^sub>v (diag_mat_of_real D *\<^sub>v ?e)" by (rule Papp) simp
    also have "diag_mat_of_real D *\<^sub>v ?e = 0\<^sub>v k"
      using diag_mat_of_real_mult_vec[OF D, of ?e] i Di by (auto simp: unit_vec_def)
    also have "U *\<^sub>v 0\<^sub>v k = 0\<^sub>v k"
      by (rule eq_vecI) (use carrier_matD[OF U] in \<open>simp_all add: scalar_prod_def\<close>)
    finally have "P *\<^sub>v (U *\<^sub>v ?e) = 0\<^sub>v k" .
    hence "Quantum.inner_prod (U *\<^sub>v ?e) w = 0" using perp carrier_matD[OF U] by simp
    moreover have "Quantum.inner_prod (U *\<^sub>v ?e) w = y $ i"
    proof -
      have Ue: "U *\<^sub>v ?e = Matrix.vec k (\<lambda>j. U $$ (j, i))"
      proof (rule eq_vecI)
        fix j assume "j < dim_vec (Matrix.vec k (\<lambda>j. U $$ (j, i)))"
        hence j: "j < k" by simp
        have "(U *\<^sub>v ?e) $ j = (\<Sum>l<k. U $$ (j, l) * (if l = i then 1 else 0))"
          using carrier_matD[OF U] j i by (simp add: scalar_prod_def unit_vec_def atLeast0LessThan)
        also have "\<dots> = (\<Sum>l<k. if l = i then U $$ (j, l) else 0)" by (rule sum.cong) simp_all
        also have "\<dots> = U $$ (j, i)" using i by simp
        finally show "(U *\<^sub>v ?e) $ j = Matrix.vec k (\<lambda>j. U $$ (j, i)) $ j" using j by simp
      qed (use carrier_matD[OF U] in simp)
      have "Quantum.inner_prod (Matrix.vec k (\<lambda>j. U $$ (j, i))) w = (\<Sum>j<k. cnj (U $$ (j, i)) * w $ j)"
        using w by (simp add: Quantum.inner_prod_def atLeast0LessThan)
      also have "\<dots> = y $ i"
        using carrier_matD[OF U] w i by (simp add: y_def scalar_prod_def dagger_def atLeast0LessThan)
      finally show ?thesis unfolding Ue .
    qed
    ultimately show ?thesis by simp
  qed
  define z where "z = Matrix.vec k (\<lambda>i. if D ! i = 0 then 0 else y $ i / complex_of_real (D ! i))"
  have zd: "dim_vec z = k" by (simp add: z_def)
  have Dz: "diag_mat_of_real D *\<^sub>v z = y"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec y" hence i: "i < k" using yd by simp
    show "(diag_mat_of_real D *\<^sub>v z) $ i = y $ i"
      using diag_mat_of_real_mult_vec[OF D zd] i y0[OF i] by (simp add: z_def)
  qed (use D yd in simp)
  have "P *\<^sub>v (U *\<^sub>v z) = U *\<^sub>v y" unfolding Papp[OF zd] Dz ..
  also have "\<dots> = (U * (U\<^sup>\<dagger>)) *\<^sub>v w"
    unfolding y_def by (rule assoc_mult_mat_vec[OF U Ud carrier_vecI[OF w], symmetric])
  also have "\<dots> = w" unfolding UUd by (rule one_mult_mat_vec[OF carrier_vecI[OF w]])
  finally have "w = P *\<^sub>v (U *\<^sub>v z)" ..
  moreover have "dim_vec (U *\<^sub>v z) = k" using carrier_matD[OF U] by simp
  ultimately show ?thesis unfolding mat_range_def by blast
qed

text \<open>The notes: if $0\le ww^*\le P$ then $w\in R(P)$.\<close>

theorem dominated_rank_one_in_range:
  assumes P: "P \<in> carrier_mat k k" and Pp: "psd P" and w: "dim_vec w = k"
      and dom: "psd (P - outer_sum k [w])"
  shows "w \<in> mat_range k P"
proof (rule hermitian_perp_ker_in_range[OF P psd_hermitian[OF Pp] w])
  fix x assume x: "dim_vec x = k" and Px: "P *\<^sub>v x = 0\<^sub>v k"
  have B: "outer_sum k [w] \<in> carrier_mat k k" by (rule outer_sum_carrier)
  have Bp: "psd (outer_sum k [w])" using w by (intro outer_sum_psd) auto
  have Bx: "outer_sum k [w] *\<^sub>v x = 0\<^sub>v k" by (rule loewner_ker_subset[OF P B Bp dom x Px])
  let ?V = "mat_of_cols k [w]"
  have Vc: "?V \<in> carrier_mat k 1" using mat_of_cols_carrier(1)[of k "[w]"] by simp
  have Vd: "?V\<^sup>\<dagger> \<in> carrier_mat 1 k" by (rule dagger_carrier[OF Vc])
  have "Quantum.inner_prod x (outer_sum k [w] *\<^sub>v x) = Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) (?V\<^sup>\<dagger> *\<^sub>v x)"
  proof -
    have "outer_sum k [w] *\<^sub>v x = ?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x)"
      unfolding outer_sum_def by (rule assoc_mult_mat_vec[OF Vc Vd carrier_vecI[OF x]])
    thus ?thesis using inner_prod_adjoint_swap[OF Vc x, of "?V\<^sup>\<dagger> *\<^sub>v x"] carrier_matD[OF Vd] by simp
  qed
  hence "Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) (?V\<^sup>\<dagger> *\<^sub>v x) = 0" using Bx x by (simp add: Quantum.inner_prod_def)
  hence Vx: "?V\<^sup>\<dagger> *\<^sub>v x = 0\<^sub>v 1" using inner_prod_self_eq_zero_iff[of "?V\<^sup>\<dagger> *\<^sub>v x"] carrier_matD[OF Vd] by simp
  have "Quantum.inner_prod x w = Quantum.inner_prod x (?V *\<^sub>v unit_vec 1 0)"
  proof -
    have "?V *\<^sub>v unit_vec 1 0 = w"
      by (rule eq_vecI) (use w in \<open>auto simp: mat_of_cols_def scalar_prod_def unit_vec_def\<close>)
    thus ?thesis by simp
  qed
  also have "\<dots> = Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) (unit_vec 1 0)"
    by (rule inner_prod_adjoint_swap[OF Vc x]) simp
  also have "\<dots> = 0" unfolding Vx by (simp add: Quantum.inner_prod_def)
  finally show "Quantum.inner_prod x w = 0" .
qed

text \<open>The notes: if $P=\sum_l w_lw_l^*$ then $R(P)=\operatorname{span}\{w_1,\dots,w_m\}$.\<close>

theorem outer_sum_range:
  assumes vs: "\<forall>v \<in> set vs. dim_vec v = k"
  shows "mat_range k (outer_sum k vs) = col_span k vs"
proof (intro equalityI subsetI)
  let ?V = "mat_of_cols k vs" and ?m = "length vs"
  have Vc: "?V \<in> carrier_mat k ?m" by (rule mat_of_cols_carrier(1))
  have Vd: "?V\<^sup>\<dagger> \<in> carrier_mat ?m k" by (rule dagger_carrier[OF Vc])
  fix y assume "y \<in> mat_range k (outer_sum k vs)"
  then obtain h where h: "dim_vec h = k" and y: "y = outer_sum k vs *\<^sub>v h" unfolding mat_range_def by blast
  have "y = ?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v h)"
    unfolding y outer_sum_def by (rule assoc_mult_mat_vec[OF Vc Vd carrier_vecI[OF h]])
  moreover have "dim_vec (?V\<^sup>\<dagger> *\<^sub>v h) = ?m" using carrier_matD[OF Vd] by simp
  ultimately show "y \<in> col_span k vs" unfolding col_span_def by blast
next
  let ?V = "mat_of_cols k vs" and ?m = "length vs" and ?P = "outer_sum k vs"
  have Vc: "?V \<in> carrier_mat k ?m" by (rule mat_of_cols_carrier(1))
  have Vd: "?V\<^sup>\<dagger> \<in> carrier_mat ?m k" by (rule dagger_carrier[OF Vc])
  have Pc: "?P \<in> carrier_mat k k" by (rule outer_sum_carrier)
  have Ph: "hermitian ?P" unfolding hermitian_def by (rule outer_sum_hermitian)
  fix y assume "y \<in> col_span k vs"
  then obtain c where c: "dim_vec c = ?m" and y: "y = ?V *\<^sub>v c" unfolding col_span_def by blast
  have yd: "dim_vec y = k" using carrier_matD[OF Vc] y by simp
  show "y \<in> mat_range k ?P"
  proof (rule hermitian_perp_ker_in_range[OF Pc Ph yd])
    fix x assume x: "dim_vec x = k" and Px: "?P *\<^sub>v x = 0\<^sub>v k"
    have "?P *\<^sub>v x = ?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x)"
      unfolding outer_sum_def by (rule assoc_mult_mat_vec[OF Vc Vd carrier_vecI[OF x]])
    hence z: "?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x) = 0\<^sub>v k" using Px by simp
    have "Quantum.inner_prod x (?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x)) = 0" unfolding z by (simp add: Quantum.inner_prod_def)
    moreover have "Quantum.inner_prod x (?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x)) = Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) (?V\<^sup>\<dagger> *\<^sub>v x)"
      by (rule inner_prod_adjoint_swap[OF Vc x]) (use carrier_matD[OF Vd] in simp)
    ultimately have "Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) (?V\<^sup>\<dagger> *\<^sub>v x) = 0" by simp
    hence Vx: "?V\<^sup>\<dagger> *\<^sub>v x = 0\<^sub>v ?m" using inner_prod_self_eq_zero_iff[of "?V\<^sup>\<dagger> *\<^sub>v x"] carrier_matD[OF Vd] by simp
    have "Quantum.inner_prod x y = Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) c"
      unfolding y by (rule inner_prod_adjoint_swap[OF Vc x c])
    also have "\<dots> = 0" unfolding Vx by (simp add: Quantum.inner_prod_def c)
    finally show "Quantum.inner_prod x y = 0" .
  qed
qed

subsection \<open>Day 4 revisited: positive definiteness and spanning (D4-8)\<close>

text \<open>The notes: $P=\sum_i|v_i\rangle\langle v_i|>0$ iff $\operatorname{span}\{v_i\}=\mathbb C^n$.\<close>

theorem pd_iff_span_all:
  assumes vs: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "pd (outer_sum n vs) \<longleftrightarrow> col_span n vs = carrier_vec n"
proof
  let ?P = "outer_sum n vs"
  have Pc: "?P \<in> carrier_mat n n" by (rule outer_sum_carrier)
  assume pd: "pd ?P"
  have Ph: "hermitian ?P" unfolding hermitian_def by (rule outer_sum_hermitian)
  show "col_span n vs = carrier_vec n"
  proof (intro equalityI subsetI)
    fix y assume "y \<in> col_span n vs"
    then obtain c where y: "y = mat_of_cols n vs *\<^sub>v c" unfolding col_span_def by blast
    show "y \<in> carrier_vec n" unfolding y by (intro carrier_vecI) simp
  next
    fix w :: "complex Matrix.vec" assume "w \<in> carrier_vec n"
    hence w: "dim_vec w = n" by simp
    have "w \<in> mat_range n ?P"
    proof (rule hermitian_perp_ker_in_range[OF Pc Ph w])
      fix x assume x: "dim_vec x = n" and Px: "?P *\<^sub>v x = 0\<^sub>v n"
      have "x = 0\<^sub>v n"
      proof (rule ccontr)
        assume "x \<noteq> 0\<^sub>v n"
        hence "0 < Re (Quantum.inner_prod x (?P *\<^sub>v x))" using pd x carrier_matD(1)[OF Pc] unfolding pd_def by auto
        thus False unfolding Px by (simp add: Quantum.inner_prod_def)
      qed
      thus "Quantum.inner_prod x w = 0" using w by (simp add: Quantum.inner_prod_def)
    qed
    thus "w \<in> col_span n vs" using outer_sum_range[OF vs] by simp
  qed
next
  let ?P = "outer_sum n vs" and ?V = "mat_of_cols n vs"
  have Pc: "?P \<in> carrier_mat n n" by (rule outer_sum_carrier)
  assume span: "col_span n vs = carrier_vec n"
  show "pd ?P"
    unfolding pd_iff_spanning[OF Pc refl vs]
  proof (intro allI impI)
    fix x :: "complex Matrix.vec" assume x: "dim_vec x = n" and x0: "x \<noteq> 0\<^sub>v n"
    show "\<exists>v \<in> set vs. Quantum.inner_prod v x \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> (\<exists>v \<in> set vs. Quantum.inner_prod v x \<noteq> 0)"
      hence all: "\<And>v. v \<in> set vs \<Longrightarrow> Quantum.inner_prod v x = 0" by blast
      have Vc: "?V \<in> carrier_mat n (length vs)" by (rule mat_of_cols_carrier(1))
      have Vx: "?V\<^sup>\<dagger> *\<^sub>v x = 0\<^sub>v (length vs)"
      proof (rule eq_vecI)
        fix j assume "j < dim_vec (0\<^sub>v (length vs) :: complex Matrix.vec)"
        hence j: "j < length vs" by simp
        have "(?V\<^sup>\<dagger> *\<^sub>v x) $ j = (\<Sum>i<n. cnj (vs ! j $ i) * x $ i)"
          using j x by (simp add: dagger_def mat_of_cols_def scalar_prod_def atLeast0LessThan)
        also have "\<dots> = Quantum.inner_prod (vs ! j) x"
          using vs j x by (simp add: Quantum.inner_prod_def atLeast0LessThan)
        also have "\<dots> = 0" using all j by simp
        finally show "(?V\<^sup>\<dagger> *\<^sub>v x) $ j = 0\<^sub>v (length vs) $ j" using j by simp
      qed (simp add: dagger_def)
      have "x \<in> col_span n vs" using span carrier_vecI[OF x] by simp
      then obtain c where c: "dim_vec c = length vs" and xc: "x = ?V *\<^sub>v c" unfolding col_span_def by blast
      have "Quantum.inner_prod x x = Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) c"
        using inner_prod_adjoint_swap[OF Vc x c] xc by simp
      also have "\<dots> = 0" unfolding Vx using c by (simp add: Quantum.inner_prod_def)
      finally have "x = 0\<^sub>v (dim_vec x)" using inner_prod_self_eq_zero_iff by blast
      thus False using x0 x by simp
    qed
  qed
qed

end
