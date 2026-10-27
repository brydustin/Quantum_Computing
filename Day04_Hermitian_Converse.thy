theory Day04_Hermitian_Converse
  imports Day04_Hermitian_Matrices
begin

section \<open>Day 4: the converse directions for Hermitian matrices (D4-1)\<close>

lemma unitary_real_diag_imp_hermitian:
  assumes U: "U \<in> carrier_mat n n" and u: "unitary U" and H: "H \<in> carrier_mat n n"
      and D: "length D = n" and spec: "U\<^sup>\<dagger> * H * U = diag_mat_of_real D"
  shows "hermitian H"
proof -
  have He: "H = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF U H u spec])
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using D by (intro carrier_matI) simp_all
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have "(U * diag_mat_of_real D * (U\<^sup>\<dagger>))\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * diag_mat_of_real D)\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use U Dc Ud in auto)
  also have "(U * diag_mat_of_real D)\<^sup>\<dagger> = ((diag_mat_of_real D)\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use U Dc in auto)
  also have "(diag_mat_of_real D)\<^sup>\<dagger> = diag_mat_of_real D"
    by (rule diag_mat_of_real_hermitian[unfolded hermitian_def])
  also have "(U\<^sup>\<dagger>)\<^sup>\<dagger> = U" by (rule dagger_of_dagger_is_id)
  finally have "(U * diag_mat_of_real D * (U\<^sup>\<dagger>))\<^sup>\<dagger> = U * (diag_mat_of_real D * (U\<^sup>\<dagger>))" .
  also have "\<dots> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" using U Dc Ud by (simp add: assoc_mult_mat)
  finally show ?thesis unfolding hermitian_def using He by simp
qed

lemma eigenbasis_real_imp_hermitian:
  assumes H: "H \<in> carrier_mat n n" and orth: "orthonormal_list n vs" and len: "length vs = n"
      and eig: "\<And>i. i < n \<Longrightarrow> H *\<^sub>v vs ! i = complex_of_real (lam ! i) \<cdot>\<^sub>v vs ! i" and lam: "length lam = n"
  shows "hermitian H"
proof -
  let ?U = "mat_of_cols n vs"
  have U: "?U \<in> carrier_mat n n" using mat_of_cols_carrier(1)[of n vs] len by simp
  have u: "unitary ?U" by (rule orthonormal_mat_unitary[OF orth len])
  have vd: "\<And>i. i < n \<Longrightarrow> dim_vec (vs ! i) = n" using orth len unfolding orthonormal_list_def by auto
  have HU: "H * ?U = ?U * diag_mat_of_real lam"
  proof (rule eq_matI)
    fix r c assume "r < dim_row (?U * diag_mat_of_real lam)" "c < dim_col (?U * diag_mat_of_real lam)"
    hence r: "r < n" and c: "c < n" using len lam by simp_all
    have "(H * ?U) $$ (r, c) = (H *\<^sub>v vs ! c) $ r"
      using carrier_matD[OF H] len r c vd[OF c] by (simp add: mat_of_cols_def Matrix.col_def Matrix.row_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = complex_of_real (lam ! c) * vs ! c $ r" using eig[OF c] vd[OF c] r by simp
    also have "\<dots> = (?U * diag_mat_of_real lam) $$ (r, c)"
    proof -
      have "(?U * diag_mat_of_real lam) $$ (r, c) = (\<Sum>k<n. ?U $$ (r, k) * diag_mat_of_real lam $$ (k, c))"
        using carrier_matD[OF U] r c lam by (auto simp: scalar_prod_def atLeast0LessThan intro!: sum.cong)
      also have "\<dots> = (\<Sum>k<n. if k = c then vs ! c $ r * complex_of_real (lam ! c) else 0)"
        by (rule sum.cong) (use r c lam len in \<open>auto simp: diag_mat_of_real_def mat_diag_def mat_of_cols_def\<close>)
      also have "\<dots> = vs ! c $ r * complex_of_real (lam ! c)" using c by simp
      finally show ?thesis by (simp add: mult.commute)
    qed
    finally show "(H * ?U) $$ (r, c) = (?U * diag_mat_of_real lam) $$ (r, c)" .
  qed (use carrier_matD[OF H] len lam in simp_all)
  have Ud: "?U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have UdU: "?U\<^sup>\<dagger> * ?U = 1\<^sub>m n" using u U len unfolding unitary_def by (simp add: inverts_mat_def)
  have "?U\<^sup>\<dagger> * H * ?U = ?U\<^sup>\<dagger> * (H * ?U)" using Ud H U by (simp add: assoc_mult_mat)
  also have "\<dots> = ?U\<^sup>\<dagger> * ?U * diag_mat_of_real lam"
  proof -
    have Dc: "diag_mat_of_real lam \<in> carrier_mat n n" using lam by (intro carrier_matI) simp_all
    show ?thesis unfolding HU by (rule assoc_mult_mat[OF Ud U Dc, symmetric])
  qed
  also have "\<dots> = diag_mat_of_real lam" unfolding UdU using lam by simp
  finally show ?thesis by (rule unitary_real_diag_imp_hermitian[OF U u H lam])
qed

end
