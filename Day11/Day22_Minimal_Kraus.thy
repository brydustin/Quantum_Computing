theory Day22_Minimal_Kraus
  imports Day32_Recovery_Proposition
begin

section \<open>Day 22: a minimal Kraus representation is linearly independent (D22-1)\<close>

subsection \<open>Mixing a Kraus list by an isometry does not change the map\<close>

definition kraus_mix :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "kraus_mix d n U Vs =
     map (\<lambda>l. foldr (\<lambda>j acc. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<length Vs] (0\<^sub>m d n)) [0..<dim_row U]"

lemma kraus_mix_length [simp]: "length (kraus_mix d n U Vs) = dim_row U"
  by (simp add: kraus_mix_def)

lemma kraus_mix_nth:
  assumes "l < dim_row U"
  shows "kraus_mix d n U Vs ! l = foldr (\<lambda>j acc. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<length Vs] (0\<^sub>m d n)"
  using assms by (simp add: kraus_mix_def)

lemma kraus_mix_carrier:
  assumes "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "\<forall>W \<in> set (kraus_mix d n U Vs). W \<in> carrier_mat d n"
proof
  fix W assume "W \<in> set (kraus_mix d n U Vs)"
  then obtain l where "W = foldr (\<lambda>j acc. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<length Vs] (0\<^sub>m d n)"
    by (auto simp: kraus_mix_def)
  thus "W \<in> carrier_mat d n" using assms by (auto intro!: foldr_add_carrier_dn)
qed

text \<open>Mixing a Kraus list by a matrix $U=(u_{lj})$ gives $W_l=\sum_ju_{lj}V_j$.  When $U^*U=I$ the two lists
define the same map:
\[ \sum_lW_lXW_l^*=\sum_{j,j'}\Bigl(\sum_l\overline{u_{lj'}}\,u_{lj}\Bigr)V_jXV_{j'}^*=\sum_jV_jXV_j^*. \]\<close>

lemma kraus_mix_entry:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and l: "l < dim_row U" and i: "i < d" and a: "a < n"
  shows "kraus_mix d n U Vs ! l $$ (i,a) = (\<Sum>j = 0..<length Vs. U $$ (l,j) * Vs ! j $$ (i,a))"
proof -
  have fc: "\<forall>j \<in> set [0..<length Vs]. U $$ (l,j) \<cdot>\<^sub>m (Vs ! j) \<in> carrier_mat d n" using Vs_c by auto
  show ?thesis
    unfolding kraus_mix_nth[OF l] foldr_add_mat_index_rect[OF fc i a]
  proof -
    have "(\<Sum>j\<leftarrow>[0..<length Vs]. (U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)) $$ (i,a)) = (\<Sum>j<length Vs. (U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)) $$ (i,a))"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>j<length Vs. U $$ (l,j) * Vs ! j $$ (i,a))"
    proof (intro sum.cong refl)
      fix j assume "j \<in> {..<length Vs}"
      hence Vj: "Vs ! j \<in> carrier_mat d n" using Vs_c nth_mem[of j Vs] by auto
      show "(U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)) $$ (i,a) = U $$ (l,j) * Vs ! j $$ (i,a)" using carrier_matD[OF Vj] i a by simp
    qed
    finally show "(\<Sum>j\<leftarrow>[0..<length Vs]. (U $$ (l,j) \<cdot>\<^sub>m (Vs ! j)) $$ (i,a)) = (\<Sum>j = 0..<length Vs. U $$ (l,j) * Vs ! j $$ (i,a))"
      by (simp add: atLeast0LessThan)
  qed
qed

lemma kraus_mix_mat_of_cols:
  assumes Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" and Uc: "U \<in> carrier_mat m (length Vs)" and dpos: "0 < d"
  shows "mat_of_cols (n*d) (map (vec_of_kraus d n) (kraus_mix d n U Vs))
         = mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U"
proof (rule eq_matI)
  let ?Ws = "kraus_mix d n U Vs"
  have Ws_c: "\<forall>W \<in> set ?Ws. W \<in> carrier_mat d n" by (rule kraus_mix_carrier[OF Vs_c])
  have dimU: "dim_row U = m" using Uc by simp
  fix r l assume "r < dim_row (mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U)"
             and "l < dim_col (mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U)"
  hence r: "r < n*d" and l: "l < m" using Uc by auto
  define a where "a = r div d"
  define i where "i = r mod d"
  have a: "a < n" using r dpos by (simp add: a_def less_mult_imp_div_less)
  have i: "i < d" using dpos by (simp add: i_def)
  have r_eq: "r = a*d + i" unfolding a_def i_def by simp
  have "mat_of_cols (n*d) (map (vec_of_kraus d n) ?Ws) $$ (r, l) = ?Ws ! l $$ (i,a)"
    unfolding r_eq using vec_of_kraus_mat_of_cols_index[OF Ws_c dpos i a] l dimU by simp
  also have "\<dots> = (\<Sum>j = 0..<length Vs. U $$ (l,j) * Vs ! j $$ (i,a))"
    using kraus_mix_entry[OF Vs_c _ i a] l dimU by simp
  also have "\<dots> = (\<Sum>j = 0..<length Vs. mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) $$ (r, j) * transpose_mat U $$ (j, l))"
    unfolding r_eq
  proof (intro sum.cong refl)
    fix j assume "j \<in> {0..<length Vs}"
    hence j: "j < length Vs" by simp
    show "U $$ (l,j) * Vs ! j $$ (i,a) = mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) $$ (a*d + i, j) * transpose_mat U $$ (j, l)"
      unfolding vec_of_kraus_mat_of_cols_index[OF Vs_c dpos i a j] using l j carrier_matD[OF Uc] by (simp add: mult.commute)
  qed
  also have "\<dots> = (mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U) $$ (r, l)"
    using r l carrier_matD[OF Uc] by (simp add: scalar_prod_def atLeast0LessThan)
  finally show "mat_of_cols (n*d) (map (vec_of_kraus d n) ?Ws) $$ (r, l)
                = (mat_of_cols (n*d) (map (vec_of_kraus d n) Vs) * transpose_mat U) $$ (r, l)" .
qed (use Uc in auto)

lemma kraus_mix_same_map:
  assumes npos: "0 < n" and dpos: "0 < d"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Uc: "U \<in> carrier_mat m (length Vs)" and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m (length Vs)"
      and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim d (kraus_mix d n U Vs) M = kraus_map_dim d Vs M"
proof -
  let ?Ws = "kraus_mix d n U Vs"
  let ?V = "mat_of_cols (n*d) (map (vec_of_kraus d n) Vs)"
  have Ws_c: "\<forall>W \<in> set ?Ws. W \<in> carrier_mat d n" by (rule kraus_mix_carrier[OF Vs_c])
  have Vc: "?V \<in> carrier_mat (n*d) (length Vs)" using mat_of_cols_carrier[of "n*d" "map (vec_of_kraus d n) Vs"] by simp
  have "choi_matrix n d (kraus_map_dim d ?Ws) = outer_sum (n*d) (map (vec_of_kraus d n) ?Ws)"
    by (rule choi_matrix_kraus_eq[OF Ws_c npos dpos])
  also have "\<dots> = (?V * transpose_mat U) * ((?V * transpose_mat U)\<^sup>\<dagger>)"
    unfolding outer_sum_def kraus_mix_mat_of_cols[OF Vs_c Uc dpos] ..
  also have "\<dots> = ?V * (?V\<^sup>\<dagger>)" by (rule isometry_mix_outer[OF Vc Uc UU])
  also have "\<dots> = outer_sum (n*d) (map (vec_of_kraus d n) Vs)" unfolding outer_sum_def ..
  also have "\<dots> = choi_matrix n d (kraus_map_dim d Vs)" by (rule choi_matrix_kraus_eq[OF Vs_c npos dpos, symmetric])
  finally have choi: "choi_matrix n d (kraus_map_dim d ?Ws) = choi_matrix n d (kraus_map_dim d Vs)" .
  show ?thesis
    by (rule map_eq_from_choi_when_linear[OF _ _ _ _ _ _ choi npos dpos Xc])
       (auto intro: kraus_map_dim_add[OF _ _ Ws_c] kraus_map_dim_smult[OF _ Ws_c] kraus_map_dim_carrier[OF Ws_c]
                    kraus_map_dim_add[OF _ _ Vs_c] kraus_map_dim_smult[OF _ Vs_c] kraus_map_dim_carrier[OF Vs_c])
qed

subsection \<open>A unitary with a prescribed first row\<close>

lemma mat_mult_entry:
  fixes A B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat r s" "B \<in> carrier_mat s t" "k < r" "j < t"
  shows "(A * B) $$ (k,j) = (\<Sum>l<s. A $$ (k,l) * B $$ (l,j))"
  using assms by (simp add: scalar_prod_def atLeast0LessThan)

lemma transpose_unitary_isometry:
  assumes Mc: "M \<in> carrier_mat r r" and MM: "M * (M\<^sup>\<dagger>) = 1\<^sub>m r"
  shows "((transpose_mat M)\<^sup>\<dagger>) * transpose_mat M = 1\<^sub>m r"
proof (rule eq_matI)
  let ?T = "transpose_mat M"
  have Tc: "?T \<in> carrier_mat r r" using Mc by simp
  have Tdc: "?T\<^sup>\<dagger> \<in> carrier_mat r r" by (rule dagger_carrier[OF Tc])
  have Mdc: "M\<^sup>\<dagger> \<in> carrier_mat r r" by (rule dagger_carrier[OF Mc])
  fix j k assume "j < dim_row (1\<^sub>m r :: complex Matrix.mat)" "k < dim_col (1\<^sub>m r :: complex Matrix.mat)"
  hence j: "j < r" and k: "k < r" by simp_all
  have "((?T\<^sup>\<dagger>) * ?T) $$ (j,k) = (\<Sum>l<r. (?T\<^sup>\<dagger>) $$ (j,l) * ?T $$ (l,k))"
    by (rule mat_mult_entry[OF Tdc Tc j k])
  also have "\<dots> = (\<Sum>l<r. M $$ (k,l) * (M\<^sup>\<dagger>) $$ (l,j))"
    using j k carrier_matD[OF Mc] by (intro sum.cong refl) (simp add: dagger_def)
  also have "\<dots> = (M * (M\<^sup>\<dagger>)) $$ (k,j)" by (rule mat_mult_entry[OF Mc Mdc k j, symmetric])
  also have "\<dots> = (1\<^sub>m r :: complex Matrix.mat) $$ (k,j)" unfolding MM ..
  also have "\<dots> = (1\<^sub>m r :: complex Matrix.mat) $$ (j,k)" using j k by auto
  finally show "((?T\<^sup>\<dagger>) * ?T) $$ (j,k) = (1\<^sub>m r :: complex Matrix.mat) $$ (j,k)" .
qed (use Mc in \<open>auto simp: dagger_def\<close>)

lemma isometry_with_first_row:
  assumes ud: "dim_vec u = r" and un: "\<parallel>u\<parallel> = 1"
  shows "\<exists>U :: complex Matrix.mat. U \<in> carrier_mat r r \<and> (U\<^sup>\<dagger>) * U = 1\<^sub>m r \<and> (\<forall>j < r. U $$ (0,j) = u $ j)"
proof -
  obtain us where orth: "orthonormal_list r us" and len: "length us = r" and us0: "us ! 0 = u"
    using unit_vec_extends_to_onb[of u r] ud un by auto
  let ?M = "mat_of_cols r us"
  have Mc: "?M \<in> carrier_mat r r" using mat_of_cols_carrier[of r us] len by simp
  have Mu: "unitary ?M" by (rule orthonormal_mat_unitary[OF orth len])
  have MM: "?M * (?M\<^sup>\<dagger>) = 1\<^sub>m r" using Mu Mc by (simp add: unitary_def)
  have rpos: "0 < r" using ud un by (cases r) (auto simp: cpx_vec_length_def)
  have row0: "\<And>j. j < r \<Longrightarrow> transpose_mat ?M $$ (0,j) = u $ j"
    using rpos len us0 by (simp add: mat_of_cols_index)
  show ?thesis
    using Mc transpose_unitary_isometry[OF Mc MM] row0 by (intro exI[of _ "transpose_mat ?M"]) auto
qed

subsection \<open>D22-1\<close>

lemma kraus_map_dim_zero_head:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and Xc: "M \<in> carrier_mat n n"
  shows "kraus_map_dim d (0\<^sub>m d n # Ws) M = kraus_map_dim d Ws M"
  using kraus_map_dim_carrier[OF Ws_c Xc] Xc by simp

text \<open>If $\Phi(X)=\sum_{j<r}V_jXV_j^*$ with $r=\mathrm{cr}(\Phi)$, then $V_0,\dots,V_{r-1}$ are linearly
independent: a dependency $\sum_jc_jV_j=0$ would allow a unitary change of representation whose first
Kraus operator is $0$, giving a representation with $r-1$ terms.\<close>

theorem minimal_kraus_rep_lin_indep:
  assumes npos: "0 < n" and dpos: "0 < d"
      and Vs_c: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and minimal: "choi_rank n d (kraus_map_dim d Vs) = length Vs"
  shows "lin_indep_complex_mat d n Vs"
proof (unfold lin_indep_complex_mat_def, intro conjI allI impI)
  show "\<forall>V \<in> set Vs. V \<in> carrier_mat d n" by (rule Vs_c)
next
  fix c :: "nat \<Rightarrow> complex"
  let ?r = "length Vs"
  let ?\<Phi> = "kraus_map_dim d Vs"
  assume dep: "foldr (\<lambda>k acc. c k \<cdot>\<^sub>m (Vs ! k) + acc) [0..<?r] (0\<^sub>m d n) = 0\<^sub>m d n"
  fix k0 assume k0: "k0 < ?r"
  show "c k0 = 0"
  proof (rule ccontr)
    assume ck0: "c k0 \<noteq> 0"
    have rpos: "0 < ?r" using k0 by (cases Vs) auto
    define cv :: "complex Matrix.vec" where "cv = Matrix.vec ?r c"
    have cvd: "dim_vec cv = ?r" by (simp add: cv_def)
    have cvnz: "cv \<noteq> 0\<^sub>v ?r" using k0 ck0 by (auto simp: cv_def dest: arg_cong[where f = "\<lambda>v. v $ k0"])
    define N where "N = \<parallel>cv\<parallel>"
    have Nnz: "N \<noteq> 0" unfolding N_def using cpx_vec_length_zero_iff[of cv] cvnz cvd by simp
    have Nnn: "0 \<le> N" unfolding N_def cpx_vec_length_def by (simp add: sum_nonneg)
    have Npos: "0 < N" using Nnz Nnn by simp
    define u where "u = complex_of_real (1 / N) \<cdot>\<^sub>v cv"
    have ud: "dim_vec u = ?r" by (simp add: u_def cvd)
    have un: "\<parallel>u\<parallel> = 1" unfolding u_def cpx_vec_length_smult N_def[symmetric] using Npos by (simp add: norm_divide)
    obtain U :: "complex Matrix.mat" where Uc: "U \<in> carrier_mat ?r ?r" and UU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m ?r"
      and U0: "\<forall>j < ?r. U $$ (0,j) = u $ j"
      using isometry_with_first_row[OF ud un] by blast
    let ?Ws = "kraus_mix d n U Vs"
    have Ws_c: "\<forall>W \<in> set ?Ws. W \<in> carrier_mat d n" by (rule kraus_mix_carrier[OF Vs_c])
    have Ws_len: "length ?Ws = ?r" using Uc by simp
    have same: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> kraus_map_dim d ?Ws X = ?\<Phi> X"
      by (rule kraus_mix_same_map[OF npos dpos Vs_c Uc UU])
    \<comment> \<open>The first mixed operator vanishes.\<close>
    have W0: "?Ws ! 0 = 0\<^sub>m d n"
    proof -
      have fc: "\<forall>j \<in> set [0..<?r]. U $$ (0,j) \<cdot>\<^sub>m (Vs ! j) \<in> carrier_mat d n" using Vs_c by auto
      have "?Ws ! 0 = foldr (\<lambda>j acc. U $$ (0,j) \<cdot>\<^sub>m (Vs ! j) + acc) [0..<?r] (0\<^sub>m d n)"
        using kraus_mix_nth[of 0 U d n Vs] Uc rpos by simp
      also have "\<dots> = foldr (\<lambda>j acc. complex_of_real (1 / N) \<cdot>\<^sub>m (c j \<cdot>\<^sub>m (Vs ! j)) + acc) [0..<?r] (0\<^sub>m d n)"
        by (rule foldr_add_mat_cong) (simp add: U0 u_def cv_def smult_smult_mat)
      also have "\<dots> = complex_of_real (1 / N) \<cdot>\<^sub>m foldr (\<lambda>j acc. c j \<cdot>\<^sub>m (Vs ! j) + acc) [0..<?r] (0\<^sub>m d n)"
      proof -
        have gen: "\<And>js. (\<forall>j \<in> set js. j < ?r) \<Longrightarrow>
            foldr (\<lambda>j acc. complex_of_real (1 / N) \<cdot>\<^sub>m (c j \<cdot>\<^sub>m (Vs ! j)) + acc) js (0\<^sub>m d n)
            = complex_of_real (1 / N) \<cdot>\<^sub>m foldr (\<lambda>j acc. c j \<cdot>\<^sub>m (Vs ! j) + acc) js (0\<^sub>m d n)"
        proof -
          fix js :: "nat list" assume "\<forall>j \<in> set js. j < ?r"
          thus "foldr (\<lambda>j acc. complex_of_real (1 / N) \<cdot>\<^sub>m (c j \<cdot>\<^sub>m (Vs ! j)) + acc) js (0\<^sub>m d n)
                = complex_of_real (1 / N) \<cdot>\<^sub>m foldr (\<lambda>j acc. c j \<cdot>\<^sub>m (Vs ! j) + acc) js (0\<^sub>m d n)"
          proof (induction js)
            case Nil show ?case by (intro eq_matI) auto
          next
            case (Cons j js)
            have jc: "c j \<cdot>\<^sub>m (Vs ! j) \<in> carrier_mat d n" using Cons.prems Vs_c by auto
            have rc: "foldr (\<lambda>j acc. c j \<cdot>\<^sub>m (Vs ! j) + acc) js (0\<^sub>m d n) \<in> carrier_mat d n"
              using Cons.prems Vs_c by (intro foldr_add_carrier_dn) auto
            show ?case using Cons jc rc by (simp add: add_smult_distrib_left_mat)
          qed
        qed
        show ?thesis by (rule gen) simp
      qed
      also have "\<dots> = 0\<^sub>m d n" unfolding dep by (intro eq_matI) auto
      finally show ?thesis .
    qed
    \<comment> \<open>Dropping it gives a representation with \<open>r - 1\<close> operators.\<close>
    obtain W0 Ws' where Ws_eq: "?Ws = W0 # Ws'" using Ws_len rpos by (cases ?Ws) auto
    have W0z: "W0 = 0\<^sub>m d n" using W0 Ws_eq by simp
    have Ws'_c: "\<forall>W \<in> set Ws'. W \<in> carrier_mat d n" using Ws_c Ws_eq by simp
    have Ws'_len: "length Ws' = ?r - 1" using Ws_len Ws_eq by simp
    have rep': "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> ?\<Phi> X = kraus_map_dim d Ws' X"
    proof (intro allI impI)
      fix X :: "complex Matrix.mat" assume Xc: "X \<in> carrier_mat n n"
      have "?\<Phi> X = kraus_map_dim d (W0 # Ws') X" using same[OF Xc] Ws_eq by simp
      also have "\<dots> = kraus_map_dim d Ws' X" unfolding W0z by (rule kraus_map_dim_zero_head[OF Ws'_c Xc])
      finally show "?\<Phi> X = kraus_map_dim d Ws' X" .
    qed
    have "choi_rank n d ?\<Phi> \<le> length Ws'"
      unfolding choi_rank_def using Ws'_c rep' by (intro cInf_lower) (auto intro: bdd_belowI[of _ 0])
    thus False using minimal Ws'_len rpos by (cases "length Vs") simp_all
  qed
qed


end
