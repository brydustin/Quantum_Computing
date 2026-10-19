theory Day34_KL_Sufficiency
  imports Day34_Knill_Laflamme
begin

text \<open>D34-2, sufficiency: if $PE_i^*E_jP=\alpha_{ij}P$ then a recovery channel exists.  Diagonalise
$(\alpha_{ij})=u\,\mathrm{diag}(d)\,u^*$; the errors $F_k=\sum_iu_{ik}E_i$ give the same channel and
satisfy $PF_k^*F_lP=\delta_{kl}d_kP$, so the $F_k/\sqrt{d_k}$ with $d_k>0$ satisfy the hypotheses of
the recovery proposition (\<open>recovery_setting\<close>).\<close>

lemma smult_cancel_nonzero:
  fixes P :: "complex Matrix.mat"
  assumes Pc: "P \<in> carrier_mat n n" and Pnz: "P \<noteq> 0\<^sub>m n n" and eq: "c \<cdot>\<^sub>m P = d \<cdot>\<^sub>m P"
  shows "c = d"
proof -
  obtain i j where i: "i < n" and j: "j < n" and Pij: "P $$ (i,j) \<noteq> 0"
  proof -
    have "\<exists>i j. i < n \<and> j < n \<and> P $$ (i,j) \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> (\<exists>i j. i < n \<and> j < n \<and> P $$ (i,j) \<noteq> 0)"
      hence "P = 0\<^sub>m n n" using Pc by (intro eq_matI) auto
      thus False using Pnz by simp
    qed
    thus ?thesis using that by blast
  qed
  have "c * P $$ (i,j) = d * P $$ (i,j)" using arg_cong[OF eq, of "\<lambda>M. M $$ (i,j)"] i j carrier_matD[OF Pc] by simp
  thus ?thesis using Pij by simp
qed

lemma one_smult_mat': "(1::complex) \<cdot>\<^sub>m M = M"
  by (rule eq_matI) simp_all

lemma smult_mat_mult_vec':
  fixes A :: "complex Matrix.mat"
  assumes "dim_col A = dim_vec v"
  shows "(k \<cdot>\<^sub>m A) *\<^sub>v v = k \<cdot>\<^sub>v (A *\<^sub>v v)"
  by (rule eq_vecI) (use assms in \<open>auto simp: scalar_prod_def sum_distrib_left mult_ac(1)\<close>)

lemma outer_prod_smult_vec:
  fixes v :: "complex Matrix.vec"
  shows "(s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v) = (s * cnj s) \<cdot>\<^sub>m (v \<oslash> v)"
proof (rule eq_matI)
  have c1: "(s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v) \<in> carrier_mat (dim_vec v) (dim_vec v)" by (rule outer_prod_carrier) simp_all
  have c2: "v \<oslash> v \<in> carrier_mat (dim_vec v) (dim_vec v)" by (rule outer_prod_carrier) simp_all
  show "dim_row ((s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v)) = dim_row ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v))"
    using carrier_matD[OF c1] carrier_matD[OF c2] by simp
  show "dim_col ((s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v)) = dim_col ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v))"
    using carrier_matD[OF c1] carrier_matD[OF c2] by simp
  fix i j assume "i < dim_row ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v))" "j < dim_col ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v))"
  hence i: "i < dim_vec v" and j: "j < dim_vec v" using carrier_matD[OF c2] by simp_all
  have "((s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v)) $$ (i,j) = (s \<cdot>\<^sub>v v) $ i * cnj ((s \<cdot>\<^sub>v v) $ j)"
    by (rule outer_prod_index) (simp_all add: i j)
  also have "\<dots> = (s * cnj s) * (v $ i * cnj (v $ j))" using i j by simp
  also have "v $ i * cnj (v $ j) = (v \<oslash> v) $$ (i,j)" by (rule outer_prod_index[symmetric, OF i j])
  finally show "((s \<cdot>\<^sub>v v) \<oslash> (s \<cdot>\<^sub>v v)) $$ (i,j) = ((s * cnj s) \<cdot>\<^sub>m (v \<oslash> v)) $$ (i,j)"
    using i j carrier_matD[OF c2] by simp
qed

lemma kraus_map_dim_foldr_add:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat n n" and fc: "\<forall>k \<in> set xs. f k \<in> carrier_mat n n"
  shows "kraus_map_dim n Ws (foldr (\<lambda>k acc. f k + acc) xs (0\<^sub>m n n))
         = foldr (\<lambda>k acc. kraus_map_dim n Ws (f k) + acc) xs (0\<^sub>m n n)"
  using fc
proof (induction xs)
  case Nil show ?case using Ws_c by (simp add: kraus_map_dim_zero)
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat n n" and rest: "\<forall>k \<in> set xs. f k \<in> carrier_mat n n" using Cons.prems by auto
  have rc: "foldr (\<lambda>k acc. f k + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n" by (rule foldr_add_mat_carrier'[OF rest])
  show ?case using kraus_map_dim_add[OF fx rc Ws_c] Cons.IH[OF rest] by simp
qed

lemma kraus_map_dim_outer_as_foldr:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat n n" and \<psi>d: "dim_vec \<psi> = n"
  shows "kraus_map_dim n Ws (\<psi> \<oslash> \<psi>)
         = foldr (\<lambda>k acc. (Ws ! k *\<^sub>v \<psi>) \<oslash> (Ws ! k *\<^sub>v \<psi>) + acc) [0..<length Ws] (0\<^sub>m n n)"
proof -
  have "kraus_map_dim n Ws (\<psi> \<oslash> \<psi>) = foldr (\<lambda>k acc. Ws ! k * (\<psi> \<oslash> \<psi>) * ((Ws ! k)\<^sup>\<dagger>) + acc) [0..<length Ws] (0\<^sub>m n n)"
    unfolding kraus_map_dim_def by (rule foldr_list_as_index)
  also have "\<dots> = foldr (\<lambda>k acc. (Ws ! k *\<^sub>v \<psi>) \<oslash> (Ws ! k *\<^sub>v \<psi>) + acc) [0..<length Ws] (0\<^sub>m n n)"
  proof (rule foldr_add_mat_cong)
    fix k assume "k \<in> set [0..<length Ws]"
    hence "Ws ! k \<in> carrier_mat n n" using Ws_c by simp
    thus "Ws ! k * (\<psi> \<oslash> \<psi>) * ((Ws ! k)\<^sup>\<dagger>) = (Ws ! k *\<^sub>v \<psi>) \<oslash> (Ws ! k *\<^sub>v \<psi>)" by (rule conj_outer_prod[OF _ \<psi>d])
  qed
  finally show ?thesis .
qed

lemma foldr_smult_sandwich:
  fixes V :: "nat \<Rightarrow> complex Matrix.mat"
  assumes Mc: "M \<in> carrier_mat n n" and Nc: "N \<in> carrier_mat n n" and Pc: "P \<in> carrier_mat n n"
      and Vc: "\<forall>j < r. V j \<in> carrier_mat n n" and h: "\<forall>j < r. M * V j * N = \<beta> j \<cdot>\<^sub>m P"
  shows "M * foldr (\<lambda>j acc. b j \<cdot>\<^sub>m V j + acc) [0..<r] (0\<^sub>m n n) * N = (\<Sum>j<r. b j * \<beta> j) \<cdot>\<^sub>m P"
proof -
  have fc: "\<forall>j \<in> set [0..<r]. b j \<cdot>\<^sub>m V j \<in> carrier_mat n n" using Vc by auto
  have fc': "\<forall>j \<in> set [0..<r]. M * (b j \<cdot>\<^sub>m V j) \<in> carrier_mat n n"
  proof
    fix j assume "j \<in> set [0..<r]"
    hence "b j \<cdot>\<^sub>m V j \<in> carrier_mat n n" using fc by blast
    thus "M * (b j \<cdot>\<^sub>m V j) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Mc])
  qed
  have "M * foldr (\<lambda>j acc. b j \<cdot>\<^sub>m V j + acc) [0..<r] (0\<^sub>m n n) * N
        = foldr (\<lambda>j acc. M * (b j \<cdot>\<^sub>m V j) * N + acc) [0..<r] (0\<^sub>m n n)"
    unfolding foldr_add_mat_mult_left[OF Mc fc] by (rule foldr_add_mat_mult_right[OF Nc fc'])
  also have "\<dots> = foldr (\<lambda>j acc. (b j * \<beta> j) \<cdot>\<^sub>m P + acc) [0..<r] (0\<^sub>m n n)"
  proof (rule foldr_add_mat_cong)
    fix j assume "j \<in> set [0..<r]"
    hence j: "j < r" by simp
    have Vjc: "V j \<in> carrier_mat n n" using Vc j by simp
    have "M * (b j \<cdot>\<^sub>m V j) * N = b j \<cdot>\<^sub>m (M * V j * N)"
      by (simp only: mult_smult_distrib[OF Mc Vjc] mult_smult_assoc_mat[OF mult_carrier_mat[OF Mc Vjc] Nc])
    also have "\<dots> = (b j * \<beta> j) \<cdot>\<^sub>m P" using h j by (simp only: smult_smult_mat)
    finally show "M * (b j \<cdot>\<^sub>m V j) * N = (b j * \<beta> j) \<cdot>\<^sub>m P" .
  qed
  also have "\<dots> = sum_list (map (\<lambda>j. b j * \<beta> j) [0..<r]) \<cdot>\<^sub>m P"
    by (rule foldr_add_mat_smult_pull[OF _ Pc]) simp
  also have "sum_list (map (\<lambda>j. b j * \<beta> j) [0..<r]) = (\<Sum>j<r. b j * \<beta> j)"
    by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
  finally show ?thesis .
qed

lemma foldr_smult_dagger:
  fixes V :: "nat \<Rightarrow> complex Matrix.mat"
  assumes Vc: "\<forall>j < r. V j \<in> carrier_mat n n"
  shows "(foldr (\<lambda>j acc. b j \<cdot>\<^sub>m V j + acc) [0..<r] (0\<^sub>m n n))\<^sup>\<dagger>
         = foldr (\<lambda>j acc. cnj (b j) \<cdot>\<^sub>m ((V j)\<^sup>\<dagger>) + acc) [0..<r] (0\<^sub>m n n)"
proof -
  have fc: "\<forall>j \<in> set [0..<r]. b j \<cdot>\<^sub>m V j \<in> carrier_mat n n" using Vc by auto
  show ?thesis unfolding foldr_add_mat_dagger[OF fc]
    by (rule foldr_add_mat_cong) (simp only: dagger_of_smult)
qed

text \<open>The bracket $P\,(\sum_ia_iE_i)^*(\sum_jb_jE_j)\,P$ under the Knill--Laflamme conditions.\<close>

lemma kl_mix_bracket:
  assumes Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and Pc: "P \<in> carrier_mat n n"
      and kl: "\<forall>i < length Es. \<forall>j < length Es. P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P"
      and r: "r = length Es"
  shows "P * (((foldr (\<lambda>i acc. a i \<cdot>\<^sub>m (Es ! i) + acc) [0..<r] (0\<^sub>m n n))\<^sup>\<dagger>)
              * foldr (\<lambda>j acc. b j \<cdot>\<^sub>m (Es ! j) + acc) [0..<r] (0\<^sub>m n n)) * P
         = (\<Sum>j<r. b j * (\<Sum>i<r. cnj (a i) * \<alpha> i j)) \<cdot>\<^sub>m P"
proof -
  define Fa where "Fa = foldr (\<lambda>i acc. a i \<cdot>\<^sub>m (Es ! i) + acc) [0..<r] (0\<^sub>m n n)"
  define Fb where "Fb = foldr (\<lambda>j acc. b j \<cdot>\<^sub>m (Es ! j) + acc) [0..<r] (0\<^sub>m n n)"
  have Ec: "\<forall>j < r. Es ! j \<in> carrier_mat n n" using Es_c r by auto
  have Edc: "\<forall>j < r. (Es ! j)\<^sup>\<dagger> \<in> carrier_mat n n" using Ec by (auto intro: dagger_carrier)
  have Fac: "Fa \<in> carrier_mat n n" unfolding Fa_def by (rule foldr_add_mat_carrier') (use Ec in auto)
  have Fbc: "Fb \<in> carrier_mat n n" unfolding Fb_def by (rule foldr_add_mat_carrier') (use Ec in auto)
  have Fadc: "Fa\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Fac])
  have PFc: "P * (Fa\<^sup>\<dagger>) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Pc Fadc])
  have step1: "\<forall>j < r. (P * (Fa\<^sup>\<dagger>)) * Es ! j * P = (\<Sum>i<r. cnj (a i) * \<alpha> i j) \<cdot>\<^sub>m P"
  proof (intro allI impI)
    fix j assume j: "j < r"
    have Ejc: "Es ! j \<in> carrier_mat n n" using Ec j by simp
    have EPc: "Es ! j * P \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Ejc Pc])
    have h: "\<forall>i < r. P * ((Es ! i)\<^sup>\<dagger>) * (Es ! j * P) = \<alpha> i j \<cdot>\<^sub>m P"
    proof (intro allI impI)
      fix i assume i: "i < r"
      have Eidc: "(Es ! i)\<^sup>\<dagger> \<in> carrier_mat n n" using Edc i by simp
      have "P * ((Es ! i)\<^sup>\<dagger>) * (Es ! j * P) = (P * ((Es ! i)\<^sup>\<dagger>) * Es ! j) * P"
        by (rule assoc_mult_mat[OF mult_carrier_mat[OF Pc Eidc] Ejc Pc, symmetric])
      also have "\<dots> = P * ((Es ! i)\<^sup>\<dagger> * Es ! j) * P" by (simp only: assoc_mult_mat[OF Pc Eidc Ejc])
      also have "\<dots> = \<alpha> i j \<cdot>\<^sub>m P" using kl i j r by simp
      finally show "P * ((Es ! i)\<^sup>\<dagger>) * (Es ! j * P) = \<alpha> i j \<cdot>\<^sub>m P" .
    qed
    have "P * foldr (\<lambda>i acc. cnj (a i) \<cdot>\<^sub>m ((Es ! i)\<^sup>\<dagger>) + acc) [0..<r] (0\<^sub>m n n) * (Es ! j * P)
          = (\<Sum>i<r. cnj (a i) * \<alpha> i j) \<cdot>\<^sub>m P"
      by (rule foldr_smult_sandwich[OF Pc EPc Pc Edc h])
    hence "P * (Fa\<^sup>\<dagger>) * (Es ! j * P) = (\<Sum>i<r. cnj (a i) * \<alpha> i j) \<cdot>\<^sub>m P"
      unfolding Fa_def foldr_smult_dagger[OF Ec] .
    thus "(P * (Fa\<^sup>\<dagger>)) * Es ! j * P = (\<Sum>i<r. cnj (a i) * \<alpha> i j) \<cdot>\<^sub>m P"
      by (simp only: assoc_mult_mat[OF PFc Ejc Pc])
  qed
  have "(P * (Fa\<^sup>\<dagger>)) * Fb * P = (\<Sum>j<r. b j * (\<Sum>i<r. cnj (a i) * \<alpha> i j)) \<cdot>\<^sub>m P"
    unfolding Fb_def by (rule foldr_smult_sandwich[OF PFc Pc Pc Ec step1])
  thus ?thesis unfolding Fa_def[symmetric] Fb_def[symmetric] by (simp only: assoc_mult_mat[OF Pc Fadc Fbc])
qed

lemma dagger_sandwich:
  assumes Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" and Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n"
  shows "(P * ((A\<^sup>\<dagger>) * B) * P)\<^sup>\<dagger> = P * ((B\<^sup>\<dagger>) * A) * P"
proof -
  have Adc: "A\<^sup>\<dagger> \<in> carrier_mat n n" and Bdc: "B\<^sup>\<dagger> \<in> carrier_mat n n" using Ac Bc by (auto intro: dagger_carrier)
  have Yc: "(A\<^sup>\<dagger>) * B \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Adc Bc])
  have PYc: "P * ((A\<^sup>\<dagger>) * B) \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Pc Yc])
  have "(P * ((A\<^sup>\<dagger>) * B) * P)\<^sup>\<dagger> = (P\<^sup>\<dagger>) * ((P * ((A\<^sup>\<dagger>) * B))\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp only: carrier_matD[OF PYc] carrier_matD[OF Pc])
  also have "(P * ((A\<^sup>\<dagger>) * B))\<^sup>\<dagger> = (((A\<^sup>\<dagger>) * B)\<^sup>\<dagger>) * (P\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp only: carrier_matD[OF Yc] carrier_matD[OF Pc])
  also have "((A\<^sup>\<dagger>) * B)\<^sup>\<dagger> = (B\<^sup>\<dagger>) * A"
    by (subst dagger_of_prod) (simp_all only: carrier_matD[OF Adc] carrier_matD[OF Bc] dagger_of_dagger_is_id)
  finally show ?thesis unfolding Ph
    by (simp only: assoc_mult_mat[OF Pc mult_carrier_mat[OF Bdc Ac] Pc])
qed

lemma smult_bracket:
  assumes Pc: "P \<in> carrier_mat n n" and Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n"
  shows "P * (((x \<cdot>\<^sub>m A)\<^sup>\<dagger>) * (y \<cdot>\<^sub>m B)) * P = (cnj x * y) \<cdot>\<^sub>m (P * ((A\<^sup>\<dagger>) * B) * P)"
proof -
  have Adc: "A\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Ac])
  have Yc: "(A\<^sup>\<dagger>) * B \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Adc Bc])
  have "((x \<cdot>\<^sub>m A)\<^sup>\<dagger>) * (y \<cdot>\<^sub>m B) = (cnj x * y) \<cdot>\<^sub>m ((A\<^sup>\<dagger>) * B)"
    by (simp only: dagger_of_smult mult_smult_assoc_mat[OF Adc smult_carrier_mat[OF Bc]]
          mult_smult_distrib[OF Adc Bc] smult_smult_mat)
  thus ?thesis
    by (simp only: mult_smult_distrib[OF Pc Yc] mult_smult_assoc_mat[OF mult_carrier_mat[OF Pc Yc] Pc])
qed

theorem knill_laflamme_sufficiency:
  assumes P: "projection n P" and Pnz: "P \<noteq> 0\<^sub>m n n" and npos: "0 < n"
      and Es: "kraus_operators n n Es"
      and kl: "\<forall>i < length Es. \<forall>j < length Es. P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P"
  shows "\<exists>As. kraus_operators n n As \<and>
           (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim n As (kraus_map_dim n Es (P * X * P)) = P * X * P)"
proof -
  let ?r = "length Es"
  have Pc: "P \<in> carrier_mat n n" and Ph: "P\<^sup>\<dagger> = P" and PP: "P * P = P"
    using P by (auto simp: projection_def hermitian_def)
  have Es_c: "\<forall>E \<in> set Es. E \<in> carrier_mat n n" and Es_tp: "sum_wdag_w n Es = 1\<^sub>m n"
    using Es by (auto simp: kraus_operators_altdef)
  have Ec: "\<forall>j < ?r. Es ! j \<in> carrier_mat n n" using Es_c by auto
  \<comment> \<open>\<open>\<alpha>\<close> is Hermitian.\<close>
  have herm: "\<And>i j. i < ?r \<Longrightarrow> j < ?r \<Longrightarrow> cnj (\<alpha> j i) = \<alpha> i j"
  proof -
    fix i j assume i: "i < ?r" and j: "j < ?r"
    have "cnj (\<alpha> j i) \<cdot>\<^sub>m P = (\<alpha> j i \<cdot>\<^sub>m P)\<^sup>\<dagger>" by (simp only: dagger_of_smult Ph)
    also have "\<dots> = (P * (((Es ! j)\<^sup>\<dagger>) * Es ! i) * P)\<^sup>\<dagger>" using kl i j by simp
    also have "\<dots> = P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P"
      by (rule dagger_sandwich[OF Pc Ph]) (use Ec i j in simp_all)
    also have "\<dots> = \<alpha> i j \<cdot>\<^sub>m P" using kl i j by simp
    finally show "cnj (\<alpha> j i) = \<alpha> i j" by (rule smult_cancel_nonzero[OF Pc Pnz])
  qed
  define A where "A = Matrix.mat ?r ?r (\<lambda>(i,j). \<alpha> i j)"
  have Ac: "A \<in> carrier_mat ?r ?r" unfolding A_def by simp
  have Ah: "hermitian A" unfolding hermitian_def
    by (rule eq_matI) (auto simp: A_def dagger_def herm)
  obtain u :: "complex Matrix.mat" and D :: "real list"
    where uc: "u \<in> carrier_mat ?r ?r" and uu: "unitary u" and Dl: "length D = ?r"
      and spec: "(u\<^sup>\<dagger>) * A * u = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF Ac Ah] by blast
  have uud: "u * (u\<^sup>\<dagger>) = 1\<^sub>m ?r" using uu uc unfolding unitary_def by simp
  have udc: "u\<^sup>\<dagger> \<in> carrier_mat ?r ?r" by (rule dagger_carrier[OF uc])
  define G where "G = transpose_mat u"
  have Gc: "G \<in> carrier_mat ?r ?r" unfolding G_def using uc by simp
  have GG: "(G\<^sup>\<dagger>) * G = 1\<^sub>m ?r" unfolding G_def by (rule transpose_unitary_isometry[OF uc uud])
  define Fs where "Fs = kraus_mix n n G Es"
  have Fs_len: "length Fs = ?r" unfolding Fs_def using Gc by simp
  have Fs_nth: "\<And>k. k < ?r \<Longrightarrow> Fs ! k = foldr (\<lambda>j acc. u $$ (j,k) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n)"
  proof -
    fix k assume k: "k < ?r"
    have "Fs ! k = foldr (\<lambda>j acc. G $$ (k,j) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n)"
      unfolding Fs_def using kraus_mix_nth[of k G n n Es] k Gc by simp
    also have "\<dots> = foldr (\<lambda>j acc. u $$ (j,k) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n)"
      by (rule foldr_add_mat_cong) (use k uc in \<open>simp add: G_def\<close>)
    finally show "Fs ! k = foldr (\<lambda>j acc. u $$ (j,k) \<cdot>\<^sub>m (Es ! j) + acc) [0..<?r] (0\<^sub>m n n)" .
  qed
  have Fs_c: "\<forall>F \<in> set Fs. F \<in> carrier_mat n n" unfolding Fs_def by (rule kraus_mix_carrier[OF Es_c])
  have Fkc: "\<And>k. k < ?r \<Longrightarrow> Fs ! k \<in> carrier_mat n n" using Fs_c Fs_len by auto
  have same: "\<And>M. M \<in> carrier_mat n n \<Longrightarrow> kraus_map_dim n Fs M = kraus_map_dim n Es M"
    unfolding Fs_def by (rule kraus_mix_same_map[OF npos npos Es_c Gc GG])
  \<comment> \<open>\<open>PF\<^sub>k\<^sup>*F\<^sub>lP = \<delta>\<^sub>k\<^sub>l d\<^sub>k P\<close>.\<close>
  have bracket: "\<And>k l. k < ?r \<Longrightarrow> l < ?r \<Longrightarrow>
      P * (((Fs ! k)\<^sup>\<dagger>) * Fs ! l) * P = (if k = l then complex_of_real (D ! k) else 0) \<cdot>\<^sub>m P"
  proof -
    fix k l assume k: "k < ?r" and l: "l < ?r"
    have "P * (((Fs ! k)\<^sup>\<dagger>) * Fs ! l) * P
          = (\<Sum>j<?r. u $$ (j,l) * (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)) \<cdot>\<^sub>m P"
      unfolding Fs_nth[OF k] Fs_nth[OF l] by (rule kl_mix_bracket[OF Es_c Pc kl refl])
    also have "(\<Sum>j<?r. u $$ (j,l) * (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)) = ((u\<^sup>\<dagger>) * A * u) $$ (k,l)"
    proof -
      have uA: "(u\<^sup>\<dagger>) * A \<in> carrier_mat ?r ?r" by (rule mult_carrier_mat[OF udc Ac])
      have e1: "\<And>j. j < ?r \<Longrightarrow> ((u\<^sup>\<dagger>) * A) $$ (k,j) = (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)"
      proof -
        fix j assume j: "j < ?r"
        have "((u\<^sup>\<dagger>) * A) $$ (k,j) = (\<Sum>i<?r. (u\<^sup>\<dagger>) $$ (k,i) * A $$ (i,j))" by (rule mat_mult_entry[OF udc Ac k j])
        also have "\<dots> = (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)"
          by (rule sum.cong) (use k j uc in \<open>auto simp: A_def dagger_def\<close>)
        finally show "((u\<^sup>\<dagger>) * A) $$ (k,j) = (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j)" .
      qed
      have "((u\<^sup>\<dagger>) * A * u) $$ (k,l) = (\<Sum>j<?r. ((u\<^sup>\<dagger>) * A) $$ (k,j) * u $$ (j,l))" by (rule mat_mult_entry[OF uA uc k l])
      also have "\<dots> = (\<Sum>j<?r. u $$ (j,l) * (\<Sum>i<?r. cnj (u $$ (i,k)) * \<alpha> i j))"
        by (rule sum.cong) (simp_all add: e1 mult.commute)
      finally show ?thesis by simp
    qed
    also have "((u\<^sup>\<dagger>) * A * u) $$ (k,l) = (if k = l then complex_of_real (D ! k) else 0)"
      unfolding spec diag_mat_of_real_def using k l Dl by simp
    finally show "P * (((Fs ! k)\<^sup>\<dagger>) * Fs ! l) * P = (if k = l then complex_of_real (D ! k) else 0) \<cdot>\<^sub>m P" .
  qed
  define d where "d = (\<lambda>k. D ! k)"
  \<comment> \<open>\<open>\<Sum>\<^sub>k d\<^sub>k = 1\<close>: both sides are \<open>Tr \<alpha>\<close>.\<close>
  have sum_alpha: "(\<Sum>j<?r. \<alpha> j j) = 1"
  proof -
    let ?V = "\<lambda>j. ((Es ! j)\<^sup>\<dagger>) * Es ! j"
    have Vc: "\<forall>j < ?r. ?V j \<in> carrier_mat n n" using Ec by (auto intro: mult_carrier_mat dagger_carrier)
    have h: "\<forall>j < ?r. P * ?V j * P = \<alpha> j j \<cdot>\<^sub>m P" using kl by simp
    have "sum_wdag_w n Es = foldr (\<lambda>j acc. ?V j + acc) [0..<?r] (0\<^sub>m n n)"
      unfolding sum_wdag_w_def by (rule foldr_list_as_index)
    also have "\<dots> = foldr (\<lambda>j acc. 1 \<cdot>\<^sub>m ?V j + acc) [0..<?r] (0\<^sub>m n n)"
      by (rule foldr_add_mat_cong) (simp only: one_smult_mat')
    finally have sw: "sum_wdag_w n Es = foldr (\<lambda>j acc. 1 \<cdot>\<^sub>m ?V j + acc) [0..<?r] (0\<^sub>m n n)" .
    have "P * sum_wdag_w n Es * P = (\<Sum>j<?r. 1 * \<alpha> j j) \<cdot>\<^sub>m P"
      unfolding sw by (rule foldr_smult_sandwich[OF Pc Pc Pc Vc h])
    moreover have "P * sum_wdag_w n Es * P = P" unfolding Es_tp by (simp only: right_mult_one_mat[OF Pc] PP)
    ultimately have "(\<Sum>j<?r. \<alpha> j j) \<cdot>\<^sub>m P = P" by simp
    thus ?thesis by (rule smult_eq_self_imp_one[OF Pc Pnz])
  qed
  have sum_d: "(\<Sum>k<?r. complex_of_real (d k)) = 1"
  proof -
    have "Tr ((u\<^sup>\<dagger>) * A * u) = Tr A" by (rule Tr_unitary_conjugation[OF uu]) (use Ac uc in simp_all)
    moreover have "Tr ((u\<^sup>\<dagger>) * A * u) = (\<Sum>k<?r. complex_of_real (d k))"
      unfolding spec Tr_def diag_mat_of_real_def d_def using Dl by simp
    moreover have "Tr A = (\<Sum>j<?r. \<alpha> j j)" unfolding Tr_def A_def by simp
    ultimately show ?thesis using sum_alpha by simp
  qed
  \<comment> \<open>Each \<open>d\<^sub>k \<ge> 0\<close>, and \<open>d\<^sub>k = 0\<close> forces \<open>F\<^sub>kP = 0\<close>.\<close>
  have FPFP: "\<And>k. k < ?r \<Longrightarrow> ((Fs ! k * P)\<^sup>\<dagger>) * (Fs ! k * P) = complex_of_real (d k) \<cdot>\<^sub>m P"
  proof -
    fix k assume k: "k < ?r"
    have Fc: "Fs ! k \<in> carrier_mat n n" by (rule Fkc[OF k])
    have Fdc: "(Fs ! k)\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Fc])
    have "(Fs ! k * P)\<^sup>\<dagger> = P * ((Fs ! k)\<^sup>\<dagger>)"
      by (subst dagger_of_prod) (simp_all only: carrier_matD[OF Fc] carrier_matD[OF Pc] Ph)
    hence "((Fs ! k * P)\<^sup>\<dagger>) * (Fs ! k * P) = (P * ((Fs ! k)\<^sup>\<dagger>)) * (Fs ! k * P)" by simp
    also have "\<dots> = (P * ((Fs ! k)\<^sup>\<dagger>) * Fs ! k) * P"
      by (rule assoc_mult_mat[OF mult_carrier_mat[OF Pc Fdc] Fc Pc, symmetric])
    also have "\<dots> = P * (((Fs ! k)\<^sup>\<dagger>) * Fs ! k) * P" by (simp only: assoc_mult_mat[OF Pc Fdc Fc])
    also have "\<dots> = complex_of_real (d k) \<cdot>\<^sub>m P" using bracket[OF k k] by (simp add: d_def)
    finally show "((Fs ! k * P)\<^sup>\<dagger>) * (Fs ! k * P) = complex_of_real (d k) \<cdot>\<^sub>m P" .
  qed
  have TrP: "0 < Re (Tr P)"
  proof -
    have Ppsd: "psd P" using psd_MdagM[OF Pc] unfolding Ph PP .
    have "Tr P \<noteq> 0" using psd_Tr_zero_imp_zero[OF Pc Ppsd] Pnz by blast
    moreover have "Tr P = complex_of_real (Re (Tr P))"
      by (rule Tr_hermitian_real[OF Pc]) (simp add: hermitian_def Ph)
    ultimately have "Re (Tr P) \<noteq> 0" by (metis of_real_0)
    thus ?thesis using Tr_psd_Re_nonneg[OF Ppsd Pc] by simp
  qed
  have d_nonneg: "\<And>k. k < ?r \<Longrightarrow> 0 \<le> d k"
  proof -
    fix k assume k: "k < ?r"
    have FPc: "Fs ! k * P \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Fkc[OF k] Pc])
    have "psd (complex_of_real (d k) \<cdot>\<^sub>m P)" using psd_MdagM[OF FPc] unfolding FPFP[OF k] .
    hence "0 \<le> Re (Tr (complex_of_real (d k) \<cdot>\<^sub>m P))" by (rule Tr_psd_Re_nonneg[where n=n]) (use Pc in simp)
    hence "0 \<le> d k * Re (Tr P)" by (simp add: Tr_smult)
    thus "0 \<le> d k" using TrP by (simp add: zero_le_mult_iff)
  qed
  have kill: "\<And>k. k < ?r \<Longrightarrow> d k = 0 \<Longrightarrow> Fs ! k * P = 0\<^sub>m n n"
  proof -
    fix k assume k: "k < ?r" and d0: "d k = 0"
    have FPc: "Fs ! k * P \<in> carrier_mat n n" by (rule mult_carrier_mat[OF Fkc[OF k] Pc])
    have "((Fs ! k * P)\<^sup>\<dagger>) * (Fs ! k * P) = 0\<^sub>m n n" unfolding FPFP[OF k] d0 of_real_0 by (rule zero_smult_mat_carrier[OF Pc])
    thus "Fs ! k * P = 0\<^sub>m n n" by (rule dagger_mult_zero_imp_zero[OF FPc])
  qed
  \<comment> \<open>The rescaled errors with \<open>d\<^sub>k > 0\<close>.\<close>
  define ks where "ks = filter (\<lambda>k. 0 < d k) [0..<?r]"
  define c where "c = (\<lambda>k. complex_of_real (1 / sqrt (d k)))"
  define Us where "Us = map (\<lambda>k. c k \<cdot>\<^sub>m Fs ! k) ks"
  have ks_dist: "distinct ks" unfolding ks_def by simp
  have ks_nth: "\<And>a. a < length ks \<Longrightarrow> ks ! a < ?r \<and> 0 < d (ks ! a)"
  proof -
    fix a assume "a < length ks"
    hence "ks ! a \<in> set ks" by (rule nth_mem)
    thus "ks ! a < ?r \<and> 0 < d (ks ! a)" unfolding ks_def by simp
  qed
  have Us_len: "length Us = length ks" unfolding Us_def by simp
  have Us_nth: "\<And>a. a < length ks \<Longrightarrow> Us ! a = c (ks ! a) \<cdot>\<^sub>m Fs ! (ks ! a)" unfolding Us_def by simp
  have S: "recovery_setting n P Us"
    unfolding recovery_setting_def
  proof (intro conjI ballI allI impI)
    show "projection n P" by (rule P)
  next
    fix U assume "U \<in> set Us"
    then obtain a where a: "a < length ks" and "U = Us ! a" unfolding Us_len[symmetric] by (metis in_set_conv_nth)
    thus "U \<in> carrier_mat n n" using Us_nth[OF a] Fkc ks_nth[OF a] by simp
  next
    fix a b assume a: "a < length Us" and b: "b < length Us"
    have a': "a < length ks" and b': "b < length ks" using a b Us_len by simp_all
    let ?k = "ks ! a" and ?l = "ks ! b"
    have k: "?k < ?r" and dk: "0 < d ?k" and l: "?l < ?r" using ks_nth[OF a'] ks_nth[OF b'] by simp_all
    have "P * (((Us ! a)\<^sup>\<dagger>) * Us ! b) * P = (cnj (c ?k) * c ?l) \<cdot>\<^sub>m (P * (((Fs ! ?k)\<^sup>\<dagger>) * Fs ! ?l) * P)"
      unfolding Us_nth[OF a'] Us_nth[OF b'] by (rule smult_bracket[OF Pc Fkc[OF k] Fkc[OF l]])
    also have "\<dots> = (cnj (c ?k) * c ?l * (if ?k = ?l then complex_of_real (D ! ?k) else 0)) \<cdot>\<^sub>m P"
      unfolding bracket[OF k l] smult_smult_mat ..
    also have "\<dots> = (if a = b then P else 0\<^sub>m n n)"
    proof (cases "a = b")
      case True
      have e1: "cnj (c ?k) * c ?k * complex_of_real (D ! ?k)
            = complex_of_real ((1 / sqrt (d ?k)) * (1 / sqrt (d ?k)) * d ?k)"
        by (simp only: c_def d_def complex_cnj_complex_of_real of_real_mult)
      have ss: "sqrt (d ?k) * sqrt (d ?k) = d ?k" using dk by simp
      have r1: "(1 / sqrt (d ?k)) * (1 / sqrt (d ?k)) * d ?k = d ?k / (sqrt (d ?k) * sqrt (d ?k))" by simp
      have r2: "(1 / sqrt (d ?k)) * (1 / sqrt (d ?k)) * d ?k = 1" using r1 unfolding ss using dk by simp
      have "cnj (c ?k) * c ?k * complex_of_real (D ! ?k) = 1" using e1 r2 by simp
      thus ?thesis using True by (simp add: one_smult_mat')
    next
      case False
      hence "?k \<noteq> ?l" using nth_eq_iff_index_eq[OF ks_dist a' b'] by simp
      thus ?thesis using False by (simp add: zero_smult_mat_carrier[OF Pc])
    qed
    finally show "P * (((Us ! a)\<^sup>\<dagger>) * Us ! b) * P = (if a = b then P else 0\<^sub>m n n)" .
  qed
  define Rs where "Rs = recovery_ops n P Us"
  have Rs: "kraus_operators n n Rs" unfolding Rs_def by (rule recovery_ops_kraus_operators[OF S])
  have Rs_c: "\<forall>R \<in> set Rs. R \<in> carrier_mat n n" using Rs by (auto simp: kraus_operators_altdef)
  \<comment> \<open>Each error term is recovered up to the weight \<open>d\<^sub>k\<close>.\<close>
  have rec_term: "\<And>\<psi> k. dim_vec \<psi> = n \<Longrightarrow> P *\<^sub>v \<psi> = \<psi> \<Longrightarrow> k < ?r \<Longrightarrow>
      kraus_map_dim n Rs ((Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)) = complex_of_real (d k) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
  proof -
    fix \<psi> :: "complex Matrix.vec" and k
    assume \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>" and k: "k < ?r"
    have \<psi>c: "\<psi> \<in> carrier_vec n" by (rule carrier_vecI[OF \<psi>d])
    have oc: "\<psi> \<oslash> \<psi> \<in> carrier_mat n n" by (rule outer_prod_carrier[OF \<psi>d \<psi>d])
    show "kraus_map_dim n Rs ((Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)) = complex_of_real (d k) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
    proof (cases "0 < d k")
      case True
      have "k \<in> set ks" unfolding ks_def using k True by simp
      then obtain a where a: "a < length ks" and ka: "ks ! a = k" by (metis in_set_conv_nth)
      have aU: "a < length Us" using a Us_len by simp
      have Ua: "Us ! a = c k \<cdot>\<^sub>m Fs ! k" using Us_nth[OF a] ka by simp
      have Fk: "Fs ! k = complex_of_real (sqrt (d k)) \<cdot>\<^sub>m (Us ! a)"
        unfolding Ua smult_smult_mat c_def using True
        by (simp add: of_real_mult[symmetric] one_smult_mat' del: of_real_mult)
      have "Fs ! k *\<^sub>v \<psi> = complex_of_real (sqrt (d k)) \<cdot>\<^sub>v (Us ! a *\<^sub>v \<psi>)"
        unfolding Fk by (rule smult_mat_mult_vec') (use rec_Uc[OF S aU] \<psi>d in simp)
      hence "(Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)
             = (complex_of_real (sqrt (d k)) * cnj (complex_of_real (sqrt (d k))))
               \<cdot>\<^sub>m ((Us ! a *\<^sub>v \<psi>) \<oslash> (Us ! a *\<^sub>v \<psi>))"
        by (simp only: outer_prod_smult_vec)
      moreover have "complex_of_real (sqrt (d k)) * cnj (complex_of_real (sqrt (d k))) = complex_of_real (d k)"
      proof -
        have "sqrt (d k) * sqrt (d k) = d k" using True by simp
        thus ?thesis by (simp only: complex_cnj_complex_of_real of_real_mult[symmetric])
      qed
      ultimately have "(Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)
             = complex_of_real (d k) \<cdot>\<^sub>m ((Us ! a *\<^sub>v \<psi>) \<oslash> (Us ! a *\<^sub>v \<psi>))" by simp
      moreover have "(Us ! a *\<^sub>v \<psi>) \<oslash> (Us ! a *\<^sub>v \<psi>) \<in> carrier_mat n n"
        by (rule outer_prod_carrier) (use rec_Uc[OF S aU] in simp_all)
      ultimately show ?thesis
        unfolding Rs_def using kraus_map_dim_smult[OF _ Rs_c[unfolded Rs_def]]
          recovery_single_error[OF S \<psi>d \<psi>V aU] by simp
    next
      case False
      hence d0: "d k = 0" using d_nonneg[OF k] by simp
      have "Fs ! k *\<^sub>v \<psi> = (Fs ! k * P) *\<^sub>v \<psi>"
        by (simp only: assoc_mult_mat_vec[OF Fkc[OF k] Pc \<psi>c] \<psi>V)
      also have "\<dots> = 0\<^sub>v n" unfolding kill[OF k d0] by (rule zero_mat_mult_vec[OF \<psi>d])
      finally have "Fs ! k *\<^sub>v \<psi> = 0\<^sub>v n" .
      thus ?thesis using d0 Rs_c by (simp add: outer_prod_zero_vec kraus_map_dim_zero zero_smult_mat_carrier[OF oc])
    qed
  qed
  have pure: "\<forall>\<psi>. dim_vec \<psi> = n \<longrightarrow> P *\<^sub>v \<psi> = \<psi> \<longrightarrow> RE n Rs Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>"
  proof (intro allI impI)
    fix \<psi> :: "complex Matrix.vec" assume \<psi>d: "dim_vec \<psi> = n" and \<psi>V: "P *\<^sub>v \<psi> = \<psi>"
    have oc: "\<psi> \<oslash> \<psi> \<in> carrier_mat n n" by (rule outer_prod_carrier[OF \<psi>d \<psi>d])
    have tc: "\<forall>k \<in> set [0..<?r]. (Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>) \<in> carrier_mat n n"
    proof
      fix k assume "k \<in> set [0..<?r]"
      hence "Fs ! k \<in> carrier_mat n n" using Fkc by simp
      thus "(Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>) \<in> carrier_mat n n" by (intro outer_prod_carrier) simp_all
    qed
    have "RE n Rs Es (\<psi> \<oslash> \<psi>) = kraus_map_dim n Rs (kraus_map_dim n Fs (\<psi> \<oslash> \<psi>))"
      unfolding RE_def same[OF oc] ..
    also have "kraus_map_dim n Fs (\<psi> \<oslash> \<psi>)
               = foldr (\<lambda>k acc. (Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>) + acc) [0..<?r] (0\<^sub>m n n)"
      using kraus_map_dim_outer_as_foldr[OF Fs_c \<psi>d] unfolding Fs_len .
    also have "kraus_map_dim n Rs \<dots>
               = foldr (\<lambda>k acc. kraus_map_dim n Rs ((Fs ! k *\<^sub>v \<psi>) \<oslash> (Fs ! k *\<^sub>v \<psi>)) + acc) [0..<?r] (0\<^sub>m n n)"
      by (rule kraus_map_dim_foldr_add[OF Rs_c tc])
    also have "\<dots> = sum_list (map (\<lambda>k. complex_of_real (d k)) [0..<?r]) \<cdot>\<^sub>m (\<psi> \<oslash> \<psi>)"
      by (rule foldr_add_mat_smult_pull[OF _ oc]) (use rec_term[OF \<psi>d \<psi>V] in simp)
    also have "sum_list (map (\<lambda>k. complex_of_real (d k)) [0..<?r]) = 1"
      using sum_d by (simp add: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
    finally show "RE n Rs Es (\<psi> \<oslash> \<psi>) = \<psi> \<oslash> \<psi>" by (simp only: one_smult_mat')
  qed
  have "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> RE n Rs Es (P * X * P) = P * X * P"
    using recovery_states_iff_PXP[OF Rs_c Es_c P] pure by blast
  thus ?thesis using Rs unfolding RE_def by blast
qed

text \<open>D34-2 (Theorem 1): the code is correctable iff $PE_i^*E_jP=\alpha_{ij}P$.\<close>

theorem knill_laflamme:
  assumes P: "projection n P" and Pnz: "P \<noteq> 0\<^sub>m n n" and npos: "0 < n"
      and Es: "kraus_operators n n Es"
  shows "(\<exists>As. kraus_operators n n As \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> kraus_map_dim n As (kraus_map_dim n Es (P * X * P)) = P * X * P))
         \<longleftrightarrow> (\<exists>\<alpha> :: nat \<Rightarrow> nat \<Rightarrow> complex. \<forall>i < length Es. \<forall>j < length Es.
                P * (((Es ! i)\<^sup>\<dagger>) * Es ! j) * P = \<alpha> i j \<cdot>\<^sub>m P)"
  using knill_laflamme_necessity[OF P Pnz npos _ Es] knill_laflamme_sufficiency[OF P Pnz npos Es] by blast

end
