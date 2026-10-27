(*  Title:   Day26_Arveson_Extension.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 28 October 2011 (Day 26)
*)

theory Day26_Arveson_Extension
  imports
    Essential_Functional_Analysis.Lmat_Euclidean
    Day25_Arveson_Correspondence
    "HOL-Analysis.Convex"
    "HOL-Analysis.Convex_Euclidean_Space"
    "HOL-Analysis.Polytope"
    "HOL-Analysis.Starlike"
begin

section \<open>Day 26 (28 October 2011): Arveson's extension theorem; separability\<close>

text \<open>Arveson's extension theorem.  The notes extend the state $S_\Phi$ by Hahn--Banach
(norm one) and use that a unital functional of norm one is positive.  Here the positive
functional $S_\Phi$ on the operator system $M_d(S)$ is extended to a positive functional on
$M_d(M_n)$ directly, by separating the positive definite cone from the kernel of $S_\Phi$
(\<open>separating_hyperplane_set_0\<close> in the Euclidean space of typed matrices); the extension is
$X\mapsto\operatorname{Tr}(DX)$ with $D\ge0$.  Dimensions are cardinalities of finite types,
as in \<open>Day22_UCP_Compact\<close>.\<close>

subsection \<open>Hermitian parts and traces of products\<close>

lemma operator_system_herm_parts:
  assumes OS: "operator_system n OS" and A: "A \<in> OS"
  shows "\<exists>Hp Kp. Hp \<in> OS \<and> Kp \<in> OS \<and> hermitian Hp \<and> hermitian Kp \<and> A = Hp + \<i> \<cdot>\<^sub>m Kp"
proof -
  have Ac: "A \<in> carrier_mat n n" using operator_systemD(1)[OF OS] A by auto
  define Hp where "Hp = (1/2) \<cdot>\<^sub>m (A + (A\<^sup>\<dagger>))"
  define Kp where "Kp = (-\<i>/2) \<cdot>\<^sub>m (A - (A\<^sup>\<dagger>))"
  have Ad: "A\<^sup>\<dagger> \<in> OS" by (rule operator_systemD(3)[OF OS A])
  have "Hp \<in> OS" unfolding Hp_def by (intro operator_systemD(5)[OF OS] operator_systemD(4)[OF OS A Ad])
  moreover have "Kp \<in> OS" unfolding Kp_def by (intro operator_systemD(5)[OF OS] operator_system_diff[OF OS A Ad])
  moreover have "hermitian Hp" unfolding hermitian_def Hp_def using Ac by (intro eq_matI) (auto simp: dagger_def)
  moreover have "hermitian Kp" unfolding hermitian_def Kp_def using Ac by (intro eq_matI) (auto simp: dagger_def algebra_simps)
  moreover have "A = Hp + \<i> \<cdot>\<^sub>m Kp" unfolding Hp_def Kp_def using Ac by (intro eq_matI) (auto simp: dagger_def algebra_simps)
  ultimately show ?thesis by blast
qed

text \<open>Traces of products: $\Tr(WM)\in\R$ for Hermitian $W,M$; $\Tr(A\ketbra vv)=\braket v{Av}$; and for
$D,P\ge0$, writing $P=\sum_kv_kv_k^*$, $\Tr(DP)=\sum_k\braket{v_k}{Dv_k}\ge0$.\<close>

lemma Tr_herm_mult_real:
  assumes Wc: "W \<in> carrier_mat n n" and Mc: "M \<in> carrier_mat n n" and Wh: "hermitian W" and Mh: "hermitian M"
  shows "Tr (W * M) \<in> \<real>"
proof -
  have "(W * M)\<^sup>\<dagger> = (M\<^sup>\<dagger>) * (W\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Wc Mc in simp)
  hence "(W * M)\<^sup>\<dagger> = M * W" using Wh Mh unfolding hermitian_def by simp
  hence "cnj (Tr (W * M)) = Tr (M * W)" using Tr_dagger[of "W * M" n] Wc Mc by simp
  also have "\<dots> = Tr (W * M)" by (rule Tr_cyclic) (use Wc Mc in simp_all)
  finally show ?thesis using Reals_cnj_iff by blast
qed

lemma Tr_mult_outer:
  fixes A :: "complex Matrix.mat" and v :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" and v: "dim_vec v = n"
  shows "Tr (A * (v \<oslash> v)) = \<langle>v | A *\<^sub>v v\<rangle>"
proof -
  define Ov where "Ov = v \<oslash> v"
  have oc: "Ov \<in> carrier_mat n n" unfolding Ov_def by (rule outer_prod_carrier[OF v v])
  have Av: "dim_vec (A *\<^sub>v v) = n" using A by simp
  have "Tr (A * Ov) = (\<Sum>r<n. (A * Ov) $$ (r,r))" using A oc by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>r<n. \<Sum>k<n. A $$ (r,k) * (v $ k * cnj (v $ r)))"
  proof (rule sum.cong[OF refl])
    fix r assume "r \<in> {..<n}"
    hence r: "r < n" by simp
    show "(A * Ov) $$ (r,r) = (\<Sum>k<n. A $$ (r,k) * (v $ k * cnj (v $ r)))"
      unfolding mat_mult_entry[OF A oc r r]
      by (rule sum.cong[OF refl]) (use r v in \<open>simp add: Ov_def outer_prod_index\<close>)
  qed
  also have "\<dots> = (\<Sum>r<n. cnj (v $ r) * (A *\<^sub>v v) $ r)"
    by (rule sum.cong[OF refl]) (use A v in \<open>auto simp: scalar_prod_def sum_distrib_left mult_ac atLeast0LessThan\<close>)
  also have "\<dots> = \<langle>v | A *\<^sub>v v\<rangle>" unfolding inner_prod_sum[OF v Av] atLeast0LessThan ..
  finally show ?thesis unfolding Ov_def .
qed

lemma Tr_psd_mult_nonneg:
  assumes Dc: "D \<in> carrier_mat n n" and Pc: "P \<in> carrier_mat n n" and Dp: "psd D" and Pp: "psd P"
  shows "0 \<le> Tr (D * P)"
proof -
  define Q where "Q = psd_sqrt D"
  have Qc: "Q \<in> carrier_mat n n" and Qp: "psd Q" and QQ: "Q * Q = D" unfolding Q_def using psd_sqrt_props[OF Dc Dp] by blast+
  have Qh: "Q\<^sup>\<dagger> = Q" using psd_hermitian[OF Qp] unfolding hermitian_def .
  have "Tr (D * P) = Tr (Q * (Q * P))" unfolding QQ[symmetric] using Qc Pc by (simp add: assoc_mult_mat[of Q n n Q n P n])
  also have "\<dots> = Tr ((Q * P) * Q)" by (rule Tr_cyclic) (use Qc Pc in simp_all)
  also have "(Q * P) * Q = (Q\<^sup>\<dagger>) * P * Q" unfolding Qh ..
  finally have e: "Tr (D * P) = Tr ((Q\<^sup>\<dagger>) * P * Q)" .
  have pc: "psd ((Q\<^sup>\<dagger>) * P * Q)" by (rule psd_conjugate[OF Pc Pp Qc])
  have cc: "(Q\<^sup>\<dagger>) * P * Q \<in> carrier_mat n n" by (rule mult_carrier_mat[OF mult_carrier_mat[OF dagger_carrier[OF Qc] Pc] Qc])
  have r: "Tr ((Q\<^sup>\<dagger>) * P * Q) = complex_of_real (Re (Tr ((Q\<^sup>\<dagger>) * P * Q)))"
    by (rule Tr_hermitian_real[OF cc psd_hermitian[OF pc]])
  have "Im (Tr ((Q\<^sup>\<dagger>) * P * Q)) = 0" using arg_cong[OF r, of Im] by simp
  moreover have "0 \<le> Re (Tr ((Q\<^sup>\<dagger>) * P * Q))" by (rule Tr_psd_Re_nonneg[OF pc cc])
  ultimately show ?thesis unfolding e by (simp add: less_eq_complex_def)
qed

lemma herm_entry:
  assumes "M \<in> carrier_mat n n" "hermitian M" "i < n" "j < n"
  shows "M $$ (i,j) = cnj (M $$ (j,i))"
proof -
  have "(M\<^sup>\<dagger>) $$ (i,j) = M $$ (i,j)" using assms(2) unfolding hermitian_def by simp
  thus ?thesis using assms by (simp add: dagger_def)
qed

lemma herm_real_comb:
  assumes Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n" and Ah: "hermitian A" and Bh: "hermitian B"
  shows "hermitian (complex_of_real u \<cdot>\<^sub>m A + complex_of_real v \<cdot>\<^sub>m B)"
  unfolding hermitian_def
proof (rule eq_matI)
  fix i j assume "i < dim_row (complex_of_real u \<cdot>\<^sub>m A + complex_of_real v \<cdot>\<^sub>m B)"
    "j < dim_col (complex_of_real u \<cdot>\<^sub>m A + complex_of_real v \<cdot>\<^sub>m B)"
  hence i: "i < n" and j: "j < n" using Ac Bc by auto
  show "((complex_of_real u \<cdot>\<^sub>m A + complex_of_real v \<cdot>\<^sub>m B)\<^sup>\<dagger>) $$ (i,j)
        = (complex_of_real u \<cdot>\<^sub>m A + complex_of_real v \<cdot>\<^sub>m B) $$ (i,j)"
    using herm_entry[OF Ac Ah i j] herm_entry[OF Bc Bh i j] i j Ac Bc by (simp add: dagger_def)
qed (use Ac Bc in simp_all)

text \<open>Two facts about real inequalities: if $c+tb\ge0$ for every $t\in\R$ then $b=0$; if
$x+\epsilon y\ge0$ for every $\epsilon>0$ then $x\ge0$.\<close>

lemma lin_t_zero:
  fixes b c :: real
  assumes "\<forall>t. 0 \<le> c + t * b"
  shows "b = 0"
proof (rule ccontr)
  assume b: "b \<noteq> 0"
  have "0 \<le> c + (-(c + 1) / b) * b" using assms by blast
  thus False using b by simp
qed

lemma eps_nonneg:
  fixes x y :: real
  assumes "\<forall>\<epsilon>>0. 0 \<le> x + \<epsilon> * y"
  shows "0 \<le> x"
proof (rule ccontr)
  assume x: "\<not> 0 \<le> x"
  show False
  proof (cases "0 < y")
    case True
    have "0 \<le> x + (- x / (2 * y)) * y" using assms x True by (intro assms[rule_format]) (simp add: field_simps)
    thus False using x True by (simp add: field_simps)
  next
    case False
    have "0 \<le> x + 1 * y" using assms[rule_format, of 1] by simp
    thus False using x False by simp
  qed
qed

lemma psd_one_mat: "psd (1\<^sub>m n)"
  using psd_MdagM[OF one_carrier_mat[of n]] by simp

subsection \<open>Matrices as points of the Euclidean space \<open>lmat\<close>\<close>

lemma wrap_lm_add:
  fixes M M' :: "complex Matrix.mat"
  assumes M: "M \<in> carrier_mat CARD('k::finite) CARD('k)" and M': "M' \<in> carrier_mat CARD('k) CARD('k)"
  shows "(wrap_lm (M + M') :: (complex, 'k, 'k) lmat) = wrap_lm M + wrap_lm M'"
proof -
  have "M + M' \<in> carrier_mat CARD('k) CARD('k)" using M M' by simp
  hence "unwrap_lm (wrap_lm (M + M') :: (complex, 'k, 'k) lmat) = unwrap_lm (wrap_lm M + wrap_lm M' :: (complex, 'k, 'k) lmat)"
    using unwrap_wrap_lm[OF M] unwrap_wrap_lm[OF M'] unwrap_wrap_lm[of "M + M'"] by simp
  thus ?thesis using unwrap_lm_inject by blast
qed

lemma wrap_lm_scale:
  fixes M :: "complex Matrix.mat"
  assumes M: "M \<in> carrier_mat CARD('k::finite) CARD('k)"
  shows "(wrap_lm (complex_of_real r \<cdot>\<^sub>m M) :: (complex, 'k, 'k) lmat) = r *\<^sub>R wrap_lm M"
proof -
  have c: "complex_of_real r \<cdot>\<^sub>m M \<in> carrier_mat CARD('k) CARD('k)" using M by simp
  have "unwrap_lm (r *\<^sub>R (wrap_lm M :: (complex, 'k, 'k) lmat)) = complex_of_real r \<cdot>\<^sub>m M"
    using unwrap_wrap_lm[OF M] M by (intro eq_matI) (auto simp: scaleR_conv_of_real)
  hence "unwrap_lm (wrap_lm (complex_of_real r \<cdot>\<^sub>m M) :: (complex, 'k, 'k) lmat) = unwrap_lm (r *\<^sub>R (wrap_lm M :: (complex, 'k, 'k) lmat))"
    using unwrap_wrap_lm[OF c] by simp
  thus ?thesis using unwrap_lm_inject by blast
qed

lemma wrap_lm_zero: "(wrap_lm (0\<^sub>m CARD('k::finite) CARD('k)) :: (complex, 'k, 'k) lmat) = 0"
proof -
  have "unwrap_lm (wrap_lm (0\<^sub>m CARD('k) CARD('k)) :: (complex, 'k, 'k) lmat) = unwrap_lm (0 :: (complex, 'k, 'k) lmat)"
    using unwrap_wrap_lm[where 'k='k, of "0\<^sub>m CARD('k) CARD('k)"] by simp
  thus ?thesis using unwrap_lm_inject by blast
qed

subsection \<open>Real functionals on typed matrices and Hermitian matrices\<close>

text \<open>The real inner product on \<open>(complex, 'm, 'n) lmat\<close> is the real
part of the JNF Hilbert-Schmidt inner product on the underlying
matrices.  For square matrices it is also \<open>Re (Tr (M\<^sup>\<dagger> * N))\<close>.\<close>

lemma inner_lmat_eq_re_hs_inner_prod:
  fixes M N :: "(complex, 'm :: finite, 'n :: finite) lmat"
  shows "inner M N = Re \<langle>\<langle> unwrap_lm M | unwrap_lm N \<rangle>\<rangle>"
proof -
  let ?S = "{0..<CARD('m)} \<times> {0..<CARD('n)}"
  have "inner M N
      = (\<Sum>(i, j) \<in> ?S. inner (unwrap_lm M $$ (i, j)) (unwrap_lm N $$ (i, j)))"
    unfolding inner_lmat_def by simp
  also have "\<dots> = (\<Sum>(i, j) \<in> ?S.
                    Re (cnj (unwrap_lm M $$ (i, j)) * unwrap_lm N $$ (i, j)))"
    by (intro sum.cong refl) (auto simp: inner_complex_def split: prod.split)
  also have "\<dots> = Re (\<Sum>(i, j) \<in> ?S.
                       cnj (unwrap_lm M $$ (i, j)) * unwrap_lm N $$ (i, j))"
    by (subst Re_sum) (simp split: prod.split)
  also have "\<dots> = Re (\<Sum>i = 0..<CARD('m). \<Sum>j = 0..<CARD('n).
                       cnj (unwrap_lm M $$ (i, j)) * unwrap_lm N $$ (i, j))"
    by (subst sum.cartesian_product [symmetric]) (simp split: prod.split)
  also have "\<dots> = Re \<langle>\<langle> unwrap_lm M | unwrap_lm N \<rangle>\<rangle>"
    unfolding hs_inner_prod_def by simp
  finally show ?thesis .
qed

text \<open>The inner-product-to-Re-trace bridge for hermitian arguments,
extracted as a separate lemma so we can reuse it for the strict
separation theorem.  This is the same hermitisation construction
that drives \<open>entanglement_witness_hermitian\<close>.\<close>

lemma hermitian_witness_from_lmat:
  fixes a :: "(complex, 'k :: finite, 'k) lmat"
  shows "\<exists>W :: complex Matrix.mat.
           W \<in> carrier_mat (CARD('k)) (CARD('k))
         \<and> hermitian W
         \<and> (\<forall>M :: (complex, 'k, 'k) lmat.
              hermitian (unwrap_lm M)
                \<longrightarrow> Re (Tr (W * unwrap_lm M)) = inner a M)"
proof -
  let ?n = "CARD('k)"
  let ?A = "unwrap_lm a"
  have A_car: "?A \<in> carrier_mat ?n ?n"
    by (rule carrier_matI) auto
  define W :: "complex Matrix.mat"
    where "W = Matrix.mat ?n ?n
                 (\<lambda>(i, j). (1/2 :: complex) *
                            (?A $$ (i, j) + cnj (?A $$ (j, i))))"
  have W_car: "W \<in> carrier_mat ?n ?n"
    unfolding W_def by (intro carrier_matI) auto
  have W_dr: "dim_row W = ?n" using W_car by simp
  have W_dc: "dim_col W = ?n" using W_car by simp
  have W_entry:
    "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow>
      W $$ (i, j) = (1/2 :: complex) *
                    (?A $$ (i, j) + cnj (?A $$ (j, i)))"
    unfolding W_def by simp
  have W_herm: "hermitian W"
  proof -
    have "W\<^sup>\<dagger> = W"
    proof (rule eq_matI)
      show "dim_row (W\<^sup>\<dagger>) = dim_row W"
        using W_dr W_dc by (simp add: dim_row_of_dagger)
      show "dim_col (W\<^sup>\<dagger>) = dim_col W"
        using W_dr W_dc by (simp add: dim_col_of_dagger)
    next
      fix i j
      assume i: "i < dim_row W" and j: "j < dim_col W"
      hence ij: "i < ?n" "j < ?n" using W_dr W_dc by simp_all
      have Wji_eq: "W $$ (j, i) = (1/2 :: complex) *
                                    (?A $$ (j, i) + cnj (?A $$ (i, j)))"
        using W_entry [OF ij(2) ij(1)] .
      have Wij_eq: "W $$ (i, j) = (1/2 :: complex) *
                                    (?A $$ (i, j) + cnj (?A $$ (j, i)))"
        using W_entry [OF ij(1) ij(2)] .
      have "W\<^sup>\<dagger> $$ (i, j) = cnj (W $$ (j, i))"
        unfolding dagger_def using ij W_dr W_dc by simp
      also have "\<dots> = cnj ((1/2 :: complex) *
                            (?A $$ (j, i) + cnj (?A $$ (i, j))))"
        by (rule arg_cong [where f = cnj]) (rule Wji_eq)
      also have "\<dots> = (1/2 :: complex) *
                       (cnj (?A $$ (j, i)) + ?A $$ (i, j))"
        by simp
      also have "\<dots> = (1/2 :: complex) *
                       (?A $$ (i, j) + cnj (?A $$ (j, i)))"
        by (simp add: add.commute)
      also have "\<dots> = W $$ (i, j)" using Wij_eq by simp
      finally show "W\<^sup>\<dagger> $$ (i, j) = W $$ (i, j)" .
    qed
    thus ?thesis by (simp add: hermitian_def)
  qed
  have re_tr_eq_inner:
    "\<And>M :: (complex, 'k, 'k) lmat.
       hermitian (unwrap_lm M)
        \<Longrightarrow> Re (Tr (W * unwrap_lm M)) = inner a M"
  proof -
    fix M :: "(complex, 'k, 'k) lmat"
    assume Mherm: "hermitian (unwrap_lm M)"
    let ?M = "unwrap_lm M"
    have Mcar: "?M \<in> carrier_mat ?n ?n"
      by (rule carrier_matI) auto
    have M_dr: "dim_row ?M = ?n" using Mcar by simp
    have M_dc: "dim_col ?M = ?n" using Mcar by simp
    have M_herm_entry:
      "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow> ?M $$ (j, i) = cnj (?M $$ (i, j))"
    proof -
      fix i j assume i_lt: "i < ?n" and j_lt: "j < ?n"
      have "(?M\<^sup>\<dagger>) $$ (i, j) = cnj (?M $$ (j, i))"
        unfolding dagger_def using i_lt j_lt M_dr M_dc by simp
      hence "?M $$ (i, j) = cnj (?M $$ (j, i))"
        using Mherm by (simp add: hermitian_def)
      thus "?M $$ (j, i) = cnj (?M $$ (i, j))"
        by (metis complex_cnj_cnj)
    qed
    have WM_car: "W * ?M \<in> carrier_mat ?n ?n" using W_car Mcar by simp
    have WM_dr: "dim_row (W * ?M) = ?n" using WM_car carrier_matD by blast
    have WM_dc: "dim_col (W * ?M) = ?n" using WM_car carrier_matD by blast
    have Tr_WM:
      "Tr (W * ?M)
         = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. W $$ (i, j) * ?M $$ (j, i))"
    proof -
      have "Tr (W * ?M)
          = (\<Sum>r < dim_row (W * ?M).
              if r < dim_col (W * ?M) then (W * ?M) $$ (r, r) else 0)"
        unfolding Tr_def by simp
      also have "\<dots>
          = (\<Sum>r < ?n. if r < ?n then (W * ?M) $$ (r, r) else 0)"
        using WM_dr WM_dc by simp
      also have "\<dots> = (\<Sum>r < ?n. (W * ?M) $$ (r, r))"
        by (intro sum.cong refl) auto
      also have "\<dots> = (\<Sum>i = 0..<?n. (W * ?M) $$ (i, i))"
        by (simp add: atLeast0LessThan)
      also have "\<dots> = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
                          W $$ (i, j) * ?M $$ (j, i))"
      proof (intro sum.cong refl)
        fix i assume "i \<in> {0..<?n}"
        hence i_lt: "i < ?n" by simp
        show "(W * ?M) $$ (i, i)
            = (\<Sum>j = 0..<?n. W $$ (i, j) * ?M $$ (j, i))"
          using W_car Mcar i_lt
          by (simp add: scalar_prod_def Matrix.row_def Matrix.col_def
                          lessThan_atLeast0)
      qed
      finally show ?thesis .
    qed
    have HS:
      "\<langle>\<langle> ?A | ?M \<rangle>\<rangle>
         = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
              cnj (?A $$ (i, j)) * ?M $$ (i, j))"
      unfolding hs_inner_prod_def using M_dr M_dc by simp
    have rewrite_entry:
      "\<And>i j. i < ?n \<Longrightarrow> j < ?n
        \<Longrightarrow> W $$ (i, j) * ?M $$ (j, i)
            = (1/2 :: complex) *
              (?A $$ (i, j) * cnj (?M $$ (i, j))
               + cnj (?A $$ (j, i)) * cnj (?M $$ (i, j)))"
    proof -
      fix i j assume i: "i < ?n" and j: "j < ?n"
      have Mji: "?M $$ (j, i) = cnj (?M $$ (i, j))"
        using M_herm_entry [OF i j] .
      have Wij: "W $$ (i, j) = (1/2 :: complex) *
                                (?A $$ (i, j) + cnj (?A $$ (j, i)))"
        using W_entry [OF i j] .
      show "W $$ (i, j) * ?M $$ (j, i)
          = (1/2 :: complex) *
            (?A $$ (i, j) * cnj (?M $$ (i, j))
             + cnj (?A $$ (j, i)) * cnj (?M $$ (i, j)))"
        using Mji Wij by (simp add: ring_distribs)
    qed
    have sum_eq_half_split:
      "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. W $$ (i, j) * ?M $$ (j, i))
       = (1/2 :: complex) *
         ((\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (?M $$ (i, j)))
        + (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (j, i)) * cnj (?M $$ (i, j))))"
    proof -
      have step1:
        "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. W $$ (i, j) * ?M $$ (j, i))
       = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
            (1/2 :: complex) *
              (?A $$ (i, j) * cnj (?M $$ (i, j))
               + cnj (?A $$ (j, i)) * cnj (?M $$ (i, j))))"
      proof (intro sum.cong refl)
        fix i j assume "i \<in> {0..<?n}" "j \<in> {0..<?n}"
        hence "i < ?n" "j < ?n" by simp_all
        thus "W $$ (i, j) * ?M $$ (j, i)
            = (1/2 :: complex) *
              (?A $$ (i, j) * cnj (?M $$ (i, j))
               + cnj (?A $$ (j, i)) * cnj (?M $$ (i, j)))"
          by (rule rewrite_entry)
      qed
      also have "\<dots>
        = (1/2 :: complex) *
          (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n.
            ?A $$ (i, j) * cnj (?M $$ (i, j))
            + cnj (?A $$ (j, i)) * cnj (?M $$ (i, j)))"
        by (simp only: sum_distrib_left)
      also have "\<dots>
        = (1/2 :: complex) *
          ((\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (?M $$ (i, j)))
         + (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (j, i)) * cnj (?M $$ (i, j))))"
        by (simp only: sum.distrib)
      finally show ?thesis .
    qed
    have second_swap:
      "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (j, i)) * cnj (?M $$ (i, j)))
       = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * ?M $$ (i, j))"
    proof -
      have "(\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (j, i)) * cnj (?M $$ (i, j)))
          = (\<Sum>j = 0..<?n. \<Sum>i = 0..<?n. cnj (?A $$ (j, i)) * cnj (?M $$ (i, j)))"
        by (rule sum.swap)
      also have "\<dots>
          = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * ?M $$ (i, j))"
      proof (intro sum.cong refl)
        fix i j assume i_in: "i \<in> {0..<?n}" and j_in: "j \<in> {0..<?n}"
        hence i_lt: "i < ?n" and j_lt: "j < ?n" by simp_all
        have "cnj (?M $$ (j, i)) = ?M $$ (i, j)"
          using M_herm_entry [OF i_lt j_lt] by (metis complex_cnj_cnj)
        thus "cnj (?A $$ (i, j)) * cnj (?M $$ (j, i))
            = cnj (?A $$ (i, j)) * ?M $$ (i, j)"
          by simp
      qed
      finally show ?thesis .
    qed
    define S1 :: complex where
      "S1 = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. ?A $$ (i, j) * cnj (?M $$ (i, j)))"
    define S2 :: complex where
      "S2 = (\<Sum>i = 0..<?n. \<Sum>j = 0..<?n. cnj (?A $$ (i, j)) * ?M $$ (i, j))"
    have Tr_WM_S: "Tr (W * ?M) = (1/2 :: complex) * (S1 + S2)"
      using Tr_WM sum_eq_half_split second_swap
      unfolding S1_def S2_def by simp
    have Re_S_eq: "Re (Tr (W * ?M)) = (1/2) * (Re S1 + Re S2)"
    proof -
      have eq1: "Tr (W * ?M) = (S1 + S2) / 2"
        using Tr_WM_S by simp
      have "Re (Tr (W * ?M)) = Re ((S1 + S2) / 2)"
        by (subst eq1) (rule refl)
      also have "\<dots> = Re (S1 + S2) / 2"
        by (rule Re_divide_numeral)
      also have "\<dots> = (Re S1 + Re S2) / 2" by simp
      also have "\<dots> = (1/2) * (Re S1 + Re S2)" by simp
      finally show ?thesis .
    qed
    have Re_S1_eq_Re_S2: "Re S1 = Re S2"
    proof -
      have "S1 = cnj S2"
        unfolding S1_def S2_def by (simp add: cnj_sum)
      thus ?thesis by simp
    qed
    have Re_S2_eq_HS: "Re S2 = Re \<langle>\<langle> ?A | ?M \<rangle>\<rangle>"
      using HS unfolding S2_def by simp
    have "Re (Tr (W * ?M)) = (1/2) * (Re S1 + Re S2)" by (rule Re_S_eq)
    also have "\<dots> = Re S2" using Re_S1_eq_Re_S2 by simp
    also have "\<dots> = Re \<langle>\<langle> ?A | ?M \<rangle>\<rangle>" by (rule Re_S2_eq_HS)
    also have "\<dots> = inner a M"
      using inner_lmat_eq_re_hs_inner_prod [of a M] by simp
    finally show "Re (Tr (W * ?M)) = inner a M" .
  qed
  show ?thesis using W_car W_herm re_tr_eq_inner by blast
qed

subsection \<open>Extension of positive functionals\<close>

text \<open>A positive functional on an operator system $T\subseteq M_N$ is $X\mapsto\operatorname{Tr}(DX)$
on $T$ for some $D\ge0$; hence it extends to a positive functional on $M_N$.\<close>

theorem positive_functional_extension:
  fixes TS :: "complex Matrix.mat set" and f :: "complex Matrix.mat \<Rightarrow> complex"
  assumes TS: "operator_system CARD('k::finite) TS" and f: "lin_fun_on TS f" and fpos: "positive_fun_on TS f"
  shows "\<exists>D. D \<in> carrier_mat CARD('k) CARD('k) \<and> psd D \<and> (\<forall>A \<in> TS. f A = Tr (D * A))"
proof -
  let ?N = "CARD('k)"
  have I: "1\<^sub>m ?N \<in> TS" by (rule operator_systemD(2)[OF TS])
  have TSc: "\<And>A. A \<in> TS \<Longrightarrow> A \<in> carrier_mat ?N ?N" using operator_systemD(1)[OF TS] by auto
  have fadd: "\<And>A B. A \<in> TS \<Longrightarrow> B \<in> TS \<Longrightarrow> f (A + B) = f A + f B" using f unfolding lin_fun_on_def by blast
  have fsm: "\<And>A c. A \<in> TS \<Longrightarrow> f (c \<cdot>\<^sub>m A) = c * f A" using f unfolding lin_fun_on_def by blast
  have fp: "\<And>A. A \<in> TS \<Longrightarrow> psd A \<Longrightarrow> 0 \<le> f A" using fpos unfolding positive_fun_on_def by blast
  have fdiff: "\<And>A B. A \<in> TS \<Longrightarrow> B \<in> TS \<Longrightarrow> f (A - B) = f A - f B"
  proof -
    fix A B assume A: "A \<in> TS" and B: "B \<in> TS"
    have "A - B = A + (-1) \<cdot>\<^sub>m B" using TSc[OF A] TSc[OF B] by (intro eq_matI) auto
    thus "f (A - B) = f A - f B" using fadd[OF A operator_systemD(5)[OF TS B]] fsm[OF B] by simp
  qed
  have fI0: "0 \<le> f (1\<^sub>m ?N)" by (rule fp[OF I psd_one_mat])
  have fIr: "Im (f (1\<^sub>m ?N)) = 0" and fIp: "0 \<le> Re (f (1\<^sub>m ?N))" using fI0 by (simp_all add: less_eq_complex_def)
  \<comment> \<open>\<open>f\<close> is real on Hermitian elements and bounded by \<open>f(I)\<close>.\<close>
  have fherm: "\<And>Hm. Hm \<in> TS \<Longrightarrow> hermitian Hm \<Longrightarrow>
      \<exists>c\<ge>0. Im (f Hm) = 0 \<and> \<bar>Re (f Hm)\<bar> \<le> c * Re (f (1\<^sub>m ?N))"
  proof -
    fix Hm assume Hm: "Hm \<in> TS" and Hh: "hermitian Hm"
    obtain c :: real where c0: "0 \<le> c" and p1: "psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N - Hm)"
      and p2: "psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N + Hm)" using herm_bound[OF TSc[OF Hm] Hh] by blast
    have cI: "complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N \<in> TS" by (rule operator_systemD(5)[OF TS I])
    have "0 \<le> f (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N - Hm)" by (rule fp[OF operator_system_diff[OF TS cI Hm] p1])
    hence a: "0 \<le> complex_of_real c * f (1\<^sub>m ?N) - f Hm" unfolding fdiff[OF cI Hm] fsm[OF I] .
    have "0 \<le> f (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N + Hm)" by (rule fp[OF operator_systemD(4)[OF TS cI Hm] p2])
    hence b: "0 \<le> complex_of_real c * f (1\<^sub>m ?N) + f Hm" unfolding fadd[OF cI Hm] fsm[OF I] .
    have "Im (f Hm) = 0" using a fIr by (simp add: less_eq_complex_def)
    moreover have "\<bar>Re (f Hm)\<bar> \<le> c * Re (f (1\<^sub>m ?N))" using a b fIr by (auto simp: less_eq_complex_def)
    ultimately show "\<exists>c\<ge>0. Im (f Hm) = 0 \<and> \<bar>Re (f Hm)\<bar> \<le> c * Re (f (1\<^sub>m ?N))" using c0 by blast
  qed
  have freal: "\<And>Hm. Hm \<in> TS \<Longrightarrow> hermitian Hm \<Longrightarrow> f Hm = complex_of_real (Re (f Hm))"
    using fherm by (metis complex_eq_iff Im_complex_of_real Re_complex_of_real)
  show ?thesis
  proof (cases "Re (f (1\<^sub>m ?N)) = 0")
    case True
    \<comment> \<open>\<open>f(I) = 0\<close> forces \<open>f = 0\<close>.\<close>
    have "\<And>A. A \<in> TS \<Longrightarrow> f A = 0"
    proof -
      fix A assume A: "A \<in> TS"
      obtain Hp Kp where Hp: "Hp \<in> TS" and Kp: "Kp \<in> TS" and Hh: "hermitian Hp" and Kh: "hermitian Kp"
        and e: "A = Hp + \<i> \<cdot>\<^sub>m Kp" using operator_system_herm_parts[OF TS A] by blast
      have "f Hp = 0" "f Kp = 0" using fherm[OF Hp Hh] fherm[OF Kp Kh] True
        by (auto simp: complex_eq_iff)
      thus "f A = 0" unfolding e using fadd[OF Hp operator_systemD(5)[OF TS Kp]] fsm[OF Kp] by simp
    qed
    have "\<And>A. A \<in> TS \<Longrightarrow> Tr (0\<^sub>m ?N ?N * A) = 0"
    proof -
      fix A assume "A \<in> TS"
      hence "0\<^sub>m ?N ?N * A = 0\<^sub>m ?N ?N" using TSc by (simp add: left_mult_zero_mat)
      thus "Tr (0\<^sub>m ?N ?N * A) = 0" by simp
    qed
    thus ?thesis using \<open>\<And>A. A \<in> TS \<Longrightarrow> f A = 0\<close> by (intro exI[of _ "0\<^sub>m ?N ?N"]) auto
  next
    case False
    hence fI: "0 < Re (f (1\<^sub>m ?N))" using fIp by simp
    define PD where "PD = {P \<in> carrier_mat ?N ?N. \<exists>\<epsilon>>0. psd (P - complex_of_real \<epsilon> \<cdot>\<^sub>m 1\<^sub>m ?N)}"
    define Kv where "Kv = {K \<in> TS. hermitian K \<and> f K = 0}"
    define Hs where "Hs = {Hm \<in> carrier_mat ?N ?N. hermitian Hm}"
    define Sp where "Sp = {P + K + \<i> \<cdot>\<^sub>m Hm | P K Hm. P \<in> PD \<and> K \<in> Kv \<and> Hm \<in> Hs}"
    define SL where "SL = (wrap_lm :: _ \<Rightarrow> (complex, 'k, 'k) lmat) ` Sp"
    have PDc: "\<And>P. P \<in> PD \<Longrightarrow> P \<in> carrier_mat ?N ?N" unfolding PD_def by blast
    have Kvc: "\<And>K. K \<in> Kv \<Longrightarrow> K \<in> carrier_mat ?N ?N" unfolding Kv_def using TSc by blast
    have Hsc: "\<And>Hm. Hm \<in> Hs \<Longrightarrow> Hm \<in> carrier_mat ?N ?N" unfolding Hs_def by blast
    \<comment> \<open>The set is convex.\<close>
    have conv: "convex SL"
      unfolding convex_def
    proof (intro ballI allI impI)
      fix x y :: "(complex, 'k, 'k) lmat" and u v :: real
      assume x: "x \<in> SL" and y: "y \<in> SL" and u: "0 \<le> u" and v: "0 \<le> v" and uv: "u + v = 1"
      obtain P1 K1 H1 where P1: "P1 \<in> PD" and K1: "K1 \<in> Kv" and H1: "H1 \<in> Hs" and x_eq: "x = wrap_lm (P1 + K1 + \<i> \<cdot>\<^sub>m H1)"
        using x unfolding SL_def Sp_def by blast
      obtain P2 K2 H2 where P2: "P2 \<in> PD" and K2: "K2 \<in> Kv" and H2: "H2 \<in> Hs" and y_eq: "y = wrap_lm (P2 + K2 + \<i> \<cdot>\<^sub>m H2)"
        using y unfolding SL_def Sp_def by blast
      let ?u = "complex_of_real u" and ?v = "complex_of_real v"
      have c1: "P1 + K1 + \<i> \<cdot>\<^sub>m H1 \<in> carrier_mat ?N ?N" and c2: "P2 + K2 + \<i> \<cdot>\<^sub>m H2 \<in> carrier_mat ?N ?N"
        using PDc[OF P1] Kvc[OF K1] Hsc[OF H1] PDc[OF P2] Kvc[OF K2] Hsc[OF H2] by auto
      have comb: "u *\<^sub>R x + v *\<^sub>R y = wrap_lm (?u \<cdot>\<^sub>m (P1 + K1 + \<i> \<cdot>\<^sub>m H1) + ?v \<cdot>\<^sub>m (P2 + K2 + \<i> \<cdot>\<^sub>m H2))"
        unfolding x_eq y_eq wrap_lm_add[OF smult_carrier_mat[OF c1] smult_carrier_mat[OF c2]]
          wrap_lm_scale[OF c1] wrap_lm_scale[OF c2] ..
      have P: "?u \<cdot>\<^sub>m P1 + ?v \<cdot>\<^sub>m P2 \<in> PD"
      proof -
        obtain e1 where e1: "0 < e1" "psd (P1 - complex_of_real e1 \<cdot>\<^sub>m 1\<^sub>m ?N)" using P1 unfolding PD_def by blast
        obtain e2 where e2: "0 < e2" "psd (P2 - complex_of_real e2 \<cdot>\<^sub>m 1\<^sub>m ?N)" using P2 unfolding PD_def by blast
        have "psd (?u \<cdot>\<^sub>m (P1 - complex_of_real e1 \<cdot>\<^sub>m 1\<^sub>m ?N) + ?v \<cdot>\<^sub>m (P2 - complex_of_real e2 \<cdot>\<^sub>m 1\<^sub>m ?N))"
          by (rule psd_add_psd[OF psd_smult_nonneg[OF u e1(2)] psd_smult_nonneg[OF v e2(2)]])
             (use PDc[OF P1] PDc[OF P2] in auto)
        moreover have "?u \<cdot>\<^sub>m (P1 - complex_of_real e1 \<cdot>\<^sub>m 1\<^sub>m ?N) + ?v \<cdot>\<^sub>m (P2 - complex_of_real e2 \<cdot>\<^sub>m 1\<^sub>m ?N)
            = (?u \<cdot>\<^sub>m P1 + ?v \<cdot>\<^sub>m P2) - complex_of_real (u * e1 + v * e2) \<cdot>\<^sub>m 1\<^sub>m ?N"
          using PDc[OF P1] PDc[OF P2] by (intro eq_matI) (auto simp: algebra_simps)
        moreover have "0 < u * e1 + v * e2"
          using u v uv e1(1) e2(1) by (cases "u = 0") (auto intro: add_pos_nonneg add_nonneg_pos)
        ultimately show ?thesis unfolding PD_def using PDc[OF P1] PDc[OF P2] by auto
      qed
      have K: "?u \<cdot>\<^sub>m K1 + ?v \<cdot>\<^sub>m K2 \<in> Kv"
      proof -
        have k1: "K1 \<in> TS" "hermitian K1" "f K1 = 0" and k2: "K2 \<in> TS" "hermitian K2" "f K2 = 0"
          using K1 K2 unfolding Kv_def by blast+
        have mem: "?u \<cdot>\<^sub>m K1 + ?v \<cdot>\<^sub>m K2 \<in> TS"
          by (intro operator_systemD(4)[OF TS] operator_systemD(5)[OF TS] k1(1) k2(1))
        have "hermitian (?u \<cdot>\<^sub>m K1 + ?v \<cdot>\<^sub>m K2)" by (rule herm_real_comb[OF Kvc[OF K1] Kvc[OF K2] k1(2) k2(2)])
        moreover have "f (?u \<cdot>\<^sub>m K1 + ?v \<cdot>\<^sub>m K2) = 0"
          using fadd[OF operator_systemD(5)[OF TS k1(1)] operator_systemD(5)[OF TS k2(1)]] fsm[OF k1(1)] fsm[OF k2(1)] k1(3) k2(3)
          by simp
        ultimately show ?thesis unfolding Kv_def using mem by blast
      qed
      have Hm: "?u \<cdot>\<^sub>m H1 + ?v \<cdot>\<^sub>m H2 \<in> Hs"
        using herm_real_comb[OF Hsc[OF H1] Hsc[OF H2]] H1 H2 Hsc[OF H1] Hsc[OF H2] unfolding Hs_def by auto
      have "?u \<cdot>\<^sub>m (P1 + K1 + \<i> \<cdot>\<^sub>m H1) + ?v \<cdot>\<^sub>m (P2 + K2 + \<i> \<cdot>\<^sub>m H2)
            = (?u \<cdot>\<^sub>m P1 + ?v \<cdot>\<^sub>m P2) + (?u \<cdot>\<^sub>m K1 + ?v \<cdot>\<^sub>m K2) + \<i> \<cdot>\<^sub>m (?u \<cdot>\<^sub>m H1 + ?v \<cdot>\<^sub>m H2)"
        using PDc[OF P1] PDc[OF P2] Kvc[OF K1] Kvc[OF K2] Hsc[OF H1] Hsc[OF H2]
        by (intro eq_matI) (auto simp: algebra_simps)
      thus "u *\<^sub>R x + v *\<^sub>R y \<in> SL" unfolding comb SL_def Sp_def using P K Hm by blast
    qed
    \<comment> \<open>It does not contain \<open>0\<close>.\<close>
    have zero: "0 \<notin> SL"
    proof
      assume "0 \<in> SL"
      then obtain P K Hm where P: "P \<in> PD" and K: "K \<in> Kv" and Hm: "Hm \<in> Hs"
        and z: "(0 :: (complex, 'k, 'k) lmat) = wrap_lm (P + K + \<i> \<cdot>\<^sub>m Hm)" unfolding SL_def Sp_def by blast
      have Pc: "P \<in> carrier_mat ?N ?N" and Kc: "K \<in> carrier_mat ?N ?N" and Hc: "Hm \<in> carrier_mat ?N ?N"
        using PDc[OF P] Kvc[OF K] Hsc[OF Hm] .
      obtain e where e0: "0 < e" and pe: "psd (P - complex_of_real e \<cdot>\<^sub>m 1\<^sub>m ?N)" using P unfolding PD_def by blast
      have Ph: "hermitian P"
      proof -
        have h: "hermitian (P - complex_of_real e \<cdot>\<^sub>m 1\<^sub>m ?N)" by (rule psd_hermitian[OF pe])
        show ?thesis unfolding hermitian_def
        proof (rule eq_matI)
          fix i j assume "i < dim_row P" "j < dim_col P"
          hence i: "i < ?N" and j: "j < ?N" using Pc by auto
          have "(P - complex_of_real e \<cdot>\<^sub>m 1\<^sub>m ?N) $$ (i,j) = cnj ((P - complex_of_real e \<cdot>\<^sub>m 1\<^sub>m ?N) $$ (j,i))"
            by (rule herm_entry[OF minus_carrier_mat[OF smult_carrier_mat[OF one_carrier_mat]] h i j])
          thus "(P\<^sup>\<dagger>) $$ (i,j) = P $$ (i,j)" using i j Pc by (auto simp: dagger_def split: if_splits)
        qed (use Pc in simp_all)
      qed
      have Kh: "hermitian K" and KTS: "K \<in> TS" and fK: "f K = 0" using K unfolding Kv_def by blast+
      have Hh: "hermitian Hm" using Hm unfolding Hs_def by blast
      have z': "P + K + \<i> \<cdot>\<^sub>m Hm = 0\<^sub>m ?N ?N"
      proof -
        have "unwrap_lm (0 :: (complex, 'k, 'k) lmat) = P + K + \<i> \<cdot>\<^sub>m Hm"
          unfolding z by (rule unwrap_wrap_lm) (use Pc Kc Hc in simp)
        thus ?thesis by simp
      qed
      have PK: "P = (-1) \<cdot>\<^sub>m K"
      proof (rule eq_matI)
        fix i j assume "i < dim_row ((-1) \<cdot>\<^sub>m K)" "j < dim_col ((-1) \<cdot>\<^sub>m K)"
        hence i: "i < ?N" and j: "j < ?N" using Kc by auto
        have a1: "P $$ (i,j) + K $$ (i,j) + \<i> * Hm $$ (i,j) = 0"
          using arg_cong[OF z', of "\<lambda>M. M $$ (i,j)"] i j Pc Kc Hc by (simp add: add.assoc)
        have a2: "P $$ (j,i) + K $$ (j,i) + \<i> * Hm $$ (j,i) = 0"
          using arg_cong[OF z', of "\<lambda>M. M $$ (j,i)"] i j Pc Kc Hc by (simp add: add.assoc)
        have "cnj (P $$ (j,i) + K $$ (j,i) + \<i> * Hm $$ (j,i)) = P $$ (i,j) + K $$ (i,j) - \<i> * Hm $$ (i,j)"
          using herm_entry[OF Pc Ph i j] herm_entry[OF Kc Kh i j] herm_entry[OF Hc Hh i j] by simp
        hence a3: "P $$ (i,j) + K $$ (i,j) - \<i> * Hm $$ (i,j) = 0" using a2 by simp
        have "2 * (P $$ (i,j) + K $$ (i,j))
              = (P $$ (i,j) + K $$ (i,j) + \<i> * Hm $$ (i,j)) + (P $$ (i,j) + K $$ (i,j) - \<i> * Hm $$ (i,j))"
          by (simp add: algebra_simps)
        also have "\<dots> = 0" unfolding a1 a3 by simp
        finally have "2 * (P $$ (i,j) + K $$ (i,j)) = 0" .
        hence "P $$ (i,j) + K $$ (i,j) = 0" by (simp only: mult_eq_0_iff) simp
        thus "P $$ (i,j) = ((-1) \<cdot>\<^sub>m K) $$ (i,j)" using i j Kc by (simp add: eq_neg_iff_add_eq_0)
      qed (use Pc Kc in simp_all)
      have PTS: "P \<in> TS" unfolding PK by (rule operator_systemD(5)[OF TS KTS])
      have fP: "f P = 0" unfolding PK fsm[OF KTS] fK by simp
      have eI: "complex_of_real e \<cdot>\<^sub>m 1\<^sub>m ?N \<in> TS" by (rule operator_systemD(5)[OF TS I])
      have "0 \<le> f (P - complex_of_real e \<cdot>\<^sub>m 1\<^sub>m ?N)" by (rule fp[OF operator_system_diff[OF TS PTS eI] pe])
      hence "0 \<le> - (complex_of_real e * f (1\<^sub>m ?N))" unfolding fdiff[OF PTS eI] fP fsm[OF I] by simp
      thus False using mult_pos_pos[OF e0 fI] by (simp add: less_eq_complex_def)
    qed
    obtain a :: "(complex, 'k, 'k) lmat" where a0: "a \<noteq> 0" and sep: "\<forall>x \<in> SL. 0 \<le> inner a x"
      using separating_hyperplane_set_0[OF conv zero] by blast
    define ga where "ga = (\<lambda>M. inner a (wrap_lm M :: (complex, 'k, 'k) lmat))"
    have ga_add: "\<And>M M'. M \<in> carrier_mat ?N ?N \<Longrightarrow> M' \<in> carrier_mat ?N ?N \<Longrightarrow> ga (M + M') = ga M + ga M'"
      unfolding ga_def by (simp add: wrap_lm_add inner_add_right)
    have ga_sc: "\<And>M r. M \<in> carrier_mat ?N ?N \<Longrightarrow> ga (complex_of_real r \<cdot>\<^sub>m M) = r * ga M"
      unfolding ga_def by (simp add: wrap_lm_scale)
    have ga0: "ga (0\<^sub>m ?N ?N) = 0" unfolding ga_def wrap_lm_zero by simp
    have Ic: "1\<^sub>m ?N \<in> carrier_mat ?N ?N" by simp
    have i0: "\<i> \<cdot>\<^sub>m 0\<^sub>m ?N ?N = 0\<^sub>m ?N ?N" by (rule eq_matI) simp_all
    have IPD: "1\<^sub>m ?N \<in> PD"
    proof -
      have "1\<^sub>m ?N - complex_of_real (1/2) \<cdot>\<^sub>m 1\<^sub>m ?N = complex_of_real (1/2) \<cdot>\<^sub>m 1\<^sub>m ?N"
        by (rule eq_matI) simp_all
      moreover have "psd (complex_of_real (1/2) \<cdot>\<^sub>m 1\<^sub>m ?N)" by (rule psd_smult_nonneg[OF _ psd_one_mat Ic]) simp
      ultimately show ?thesis unfolding PD_def using Ic by (intro CollectI conjI exI[of _ "1/2"]) simp_all
    qed
    have z0h: "hermitian (0\<^sub>m ?N ?N :: complex Matrix.mat)" unfolding hermitian_def by (rule eq_matI) (simp_all add: dagger_def)
    have K0: "0\<^sub>m ?N ?N \<in> Kv" unfolding Kv_def using operator_system_zero[OF TS] z0h lin_fun_zero[OF TS f] by blast
    have H0: "0\<^sub>m ?N ?N \<in> Hs" unfolding Hs_def using z0h by simp
    have hyp: "\<And>P K Hm. P \<in> PD \<Longrightarrow> K \<in> Kv \<Longrightarrow> Hm \<in> Hs \<Longrightarrow> 0 \<le> ga P + ga K + ga (\<i> \<cdot>\<^sub>m Hm)"
    proof -
      fix P K Hm assume P: "P \<in> PD" and K: "K \<in> Kv" and Hm: "Hm \<in> Hs"
      have "wrap_lm (P + K + \<i> \<cdot>\<^sub>m Hm) \<in> SL" unfolding SL_def Sp_def using P K Hm by blast
      hence "0 \<le> ga (P + K + \<i> \<cdot>\<^sub>m Hm)" using sep unfolding ga_def by blast
      moreover have "ga (P + K + \<i> \<cdot>\<^sub>m Hm) = ga P + ga K + ga (\<i> \<cdot>\<^sub>m Hm)"
        using ga_add[of "P + K" "\<i> \<cdot>\<^sub>m Hm"] ga_add[of P K] PDc[OF P] Kvc[OF K] Hsc[OF Hm] by simp
      ultimately show "0 \<le> ga P + ga K + ga (\<i> \<cdot>\<^sub>m Hm)" by simp
    qed
    have Kvs: "\<And>K t. K \<in> Kv \<Longrightarrow> complex_of_real t \<cdot>\<^sub>m K \<in> Kv"
    proof -
      fix K t assume K: "K \<in> Kv"
      have k: "K \<in> TS" "hermitian K" "f K = 0" using K unfolding Kv_def by blast+
      show "complex_of_real t \<cdot>\<^sub>m K \<in> Kv" unfolding Kv_def
        using operator_systemD(5)[OF TS k(1)] hermitian_smult_real_mat[OF Kvc[OF K] k(2)] fsm[OF k(1)] k(3) by simp
    qed
    have Hss: "\<And>Hm t. Hm \<in> Hs \<Longrightarrow> complex_of_real t \<cdot>\<^sub>m Hm \<in> Hs"
      unfolding Hs_def using hermitian_smult_real_mat by auto
    have gaK: "\<And>K. K \<in> Kv \<Longrightarrow> ga K = 0"
    proof -
      fix K assume K: "K \<in> Kv"
      have "\<forall>t. 0 \<le> ga (1\<^sub>m ?N) + t * ga K"
      proof
        fix t
        have "0 \<le> ga (1\<^sub>m ?N) + ga (complex_of_real t \<cdot>\<^sub>m K) + ga (\<i> \<cdot>\<^sub>m 0\<^sub>m ?N ?N)" by (rule hyp[OF IPD Kvs[OF K] H0])
        thus "0 \<le> ga (1\<^sub>m ?N) + t * ga K" unfolding ga_sc[OF Kvc[OF K]] i0 ga0 by simp
      qed
      thus "ga K = 0" by (rule lin_t_zero)
    qed
    have gaH: "\<And>Hm. Hm \<in> Hs \<Longrightarrow> ga (\<i> \<cdot>\<^sub>m Hm) = 0"
    proof -
      fix Hm assume Hm: "Hm \<in> Hs"
      have iHc: "\<i> \<cdot>\<^sub>m Hm \<in> carrier_mat ?N ?N" using Hsc[OF Hm] by simp
      have "\<forall>t. 0 \<le> ga (1\<^sub>m ?N) + t * ga (\<i> \<cdot>\<^sub>m Hm)"
      proof
        fix t
        have "0 \<le> ga (1\<^sub>m ?N) + ga (0\<^sub>m ?N ?N) + ga (\<i> \<cdot>\<^sub>m (complex_of_real t \<cdot>\<^sub>m Hm))" by (rule hyp[OF IPD K0 Hss[OF Hm]])
        moreover have "\<i> \<cdot>\<^sub>m (complex_of_real t \<cdot>\<^sub>m Hm) = complex_of_real t \<cdot>\<^sub>m (\<i> \<cdot>\<^sub>m Hm)"
          by (simp add: smult_smult_mat mult.commute)
        ultimately show "0 \<le> ga (1\<^sub>m ?N) + t * ga (\<i> \<cdot>\<^sub>m Hm)" unfolding ga0 using ga_sc[OF iHc, of t] by simp
      qed
      thus "ga (\<i> \<cdot>\<^sub>m Hm) = 0" by (rule lin_t_zero)
    qed
    have gaPD: "\<And>P. P \<in> PD \<Longrightarrow> 0 \<le> ga P" using hyp[OF _ K0 H0] unfolding ga0 i0 by simp
    have gaPSD: "\<And>P. P \<in> carrier_mat ?N ?N \<Longrightarrow> psd P \<Longrightarrow> 0 \<le> ga P"
    proof -
      fix P assume Pc: "P \<in> carrier_mat ?N ?N" and Pp: "psd P"
      have "\<forall>\<epsilon>>0. 0 \<le> ga P + \<epsilon> * ga (1\<^sub>m ?N)"
      proof (intro allI impI)
        fix \<epsilon> :: real assume e: "0 < \<epsilon>"
        have "P + complex_of_real \<epsilon> \<cdot>\<^sub>m 1\<^sub>m ?N - complex_of_real \<epsilon> \<cdot>\<^sub>m 1\<^sub>m ?N = P" using Pc by (intro eq_matI) auto
        hence "P + complex_of_real \<epsilon> \<cdot>\<^sub>m 1\<^sub>m ?N \<in> PD" unfolding PD_def using Pc Pp e by auto
        hence "0 \<le> ga (P + complex_of_real \<epsilon> \<cdot>\<^sub>m 1\<^sub>m ?N)" by (rule gaPD)
        thus "0 \<le> ga P + \<epsilon> * ga (1\<^sub>m ?N)" using ga_add[OF Pc smult_carrier_mat[OF Ic]] ga_sc[OF Ic] by simp
      qed
      thus "0 \<le> ga P" by (rule eps_nonneg)
    qed
    have gaI: "0 < ga (1\<^sub>m ?N)"
    proof -
      have "0 \<le> ga (1\<^sub>m ?N)" by (rule gaPSD[OF Ic psd_one_mat])
      moreover have "ga (1\<^sub>m ?N) \<noteq> 0"
      proof
        assume gI0: "ga (1\<^sub>m ?N) = 0"
        have gaHz: "\<And>Hm. Hm \<in> Hs \<Longrightarrow> ga Hm = 0"
        proof -
          fix Hm assume Hm: "Hm \<in> Hs"
          have Hc: "Hm \<in> carrier_mat ?N ?N" and Hh: "hermitian Hm" using Hm unfolding Hs_def by blast+
          obtain c :: real where p1: "psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N - Hm)"
            and p2: "psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N + Hm)" using herm_bound[OF Hc Hh] by blast
          have e1: "complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N - Hm = complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N + complex_of_real (-1) \<cdot>\<^sub>m Hm"
            using Hc by (intro eq_matI) auto
          have "0 \<le> ga (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N - Hm)" by (rule gaPSD[OF minus_carrier_mat[OF Hc] p1])
          hence "0 \<le> - ga Hm" unfolding e1 ga_add[OF smult_carrier_mat[OF Ic] smult_carrier_mat[OF Hc]]
            ga_sc[OF Ic] ga_sc[OF Hc] gI0 by simp
          moreover have "0 \<le> ga (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m ?N + Hm)" by (rule gaPSD[OF _ p2]) (use Hc in simp)
          hence "0 \<le> ga Hm" unfolding ga_add[OF smult_carrier_mat[OF Ic] Hc] ga_sc[OF Ic] gI0 by simp
          ultimately show "ga Hm = 0" by simp
        qed
        have all0: "\<And>M. M \<in> carrier_mat ?N ?N \<Longrightarrow> ga M = 0"
        proof -
          fix M :: "complex Matrix.mat" assume M: "M \<in> carrier_mat ?N ?N"
          obtain Hp Kp where Hp: "Hp \<in> carrier_mat ?N ?N" and Kp: "Kp \<in> carrier_mat ?N ?N"
            and Hh: "hermitian Hp" and Kh: "hermitian Kp" and e: "M = Hp + \<i> \<cdot>\<^sub>m Kp"
            using operator_system_herm_parts[OF operator_system_full M] by blast
          have "ga M = ga Hp + ga (\<i> \<cdot>\<^sub>m Kp)" unfolding e by (rule ga_add[OF Hp]) (use Kp in simp)
          thus "ga M = 0" using gaHz[of Hp] gaH[of Kp] Hp Kp Hh Kh unfolding Hs_def by simp
        qed
        have "inner a a = ga (unwrap_lm a)" unfolding ga_def unwrap_lm_inverse ..
        also have "\<dots> = 0" by (rule all0) simp
        finally show False using a0 by simp
      qed
      ultimately show ?thesis by simp
    qed
    obtain W where Wc: "W \<in> carrier_mat ?N ?N" and Wh: "hermitian W"
      and Wa: "\<forall>M :: (complex, 'k, 'k) lmat. hermitian (unwrap_lm M) \<longrightarrow> Re (Tr (W * unwrap_lm M)) = inner a M"
      using hermitian_witness_from_lmat[of a] by blast
    have WHs: "\<And>Hm. Hm \<in> Hs \<Longrightarrow> Tr (W * Hm) = complex_of_real (ga Hm)"
    proof -
      fix Hm assume Hm: "Hm \<in> Hs"
      have Hc: "Hm \<in> carrier_mat ?N ?N" and Hh: "hermitian Hm" using Hm unfolding Hs_def by blast+
      have r: "Tr (W * Hm) \<in> \<real>" by (rule Tr_herm_mult_real[OF Wc Hc Wh Hh])
      have "Re (Tr (W * Hm)) = ga Hm"
        using Wa[rule_format, of "wrap_lm Hm"] unwrap_wrap_lm[OF Hc] Hh unfolding ga_def by simp
      thus "Tr (W * Hm) = complex_of_real (ga Hm)" using r by (metis Reals_cases Re_complex_of_real)
    qed
    define lam where "lam = ga (1\<^sub>m ?N) / Re (f (1\<^sub>m ?N))"
    have lam: "0 < lam" unfolding lam_def using gaI fI by simp
    have fga: "\<And>Xm. Xm \<in> TS \<Longrightarrow> hermitian Xm \<Longrightarrow> ga Xm = lam * Re (f Xm)"
    proof -
      fix Xm assume Xm: "Xm \<in> TS" and Xh: "hermitian Xm"
      have Xc: "Xm \<in> carrier_mat ?N ?N" by (rule TSc[OF Xm])
      define r where "r = Re (f Xm) / Re (f (1\<^sub>m ?N))"
      define K where "K = Xm + complex_of_real (- r) \<cdot>\<^sub>m 1\<^sub>m ?N"
      have rI: "complex_of_real (- r) \<cdot>\<^sub>m 1\<^sub>m ?N \<in> TS" by (rule operator_systemD(5)[OF TS I])
      have KTS: "K \<in> TS" unfolding K_def by (rule operator_systemD(4)[OF TS Xm rI])
      have Kh: "hermitian K"
      proof -
        have "K = complex_of_real 1 \<cdot>\<^sub>m Xm + complex_of_real (- r) \<cdot>\<^sub>m 1\<^sub>m ?N" unfolding K_def using Xc by (intro eq_matI) auto
        thus ?thesis using herm_real_comb[OF Xc Ic Xh, of 1 "- r"] hermitian_identity by simp
      qed
      have "f K = f Xm + complex_of_real (- r) * f (1\<^sub>m ?N)" unfolding K_def fadd[OF Xm rI] fsm[OF I] ..
      also have "\<dots> = 0"
      proof -
        define xa where "xa = Re (f Xm)"
        define xb where "xb = Re (f (1\<^sub>m ?N))"
        have fa: "f Xm = complex_of_real xa" unfolding xa_def by (rule freal[OF Xm Xh])
        have fb: "f (1\<^sub>m ?N) = complex_of_real xb" unfolding xb_def by (rule freal[OF I hermitian_identity])
        have b0: "xb \<noteq> 0" using fI unfolding xb_def by simp
        have "complex_of_real xa + complex_of_real (- (xa / xb)) * complex_of_real xb = complex_of_real (xa - xa / xb * xb)"
          by simp
        also have "xa - xa / xb * xb = 0" using b0 by simp
        finally show ?thesis unfolding fa fb r_def xa_def[symmetric] xb_def[symmetric] by simp
      qed
      finally have "K \<in> Kv" unfolding Kv_def using KTS Kh by blast
      hence "ga K = 0" by (rule gaK)
      moreover have "ga K = ga Xm - r * ga (1\<^sub>m ?N)" unfolding K_def ga_add[OF Xc smult_carrier_mat[OF Ic]] ga_sc[OF Ic] by simp
      ultimately show "ga Xm = lam * Re (f Xm)" unfolding lam_def r_def using fI by (simp add: field_simps)
    qed
    define D where "D = complex_of_real (1 / lam) \<cdot>\<^sub>m W"
    have Dc: "D \<in> carrier_mat ?N ?N" unfolding D_def using Wc by simp
    have Wpsd: "psd W"
      unfolding psd_iff_quad_form_nonneg[OF Wc]
    proof (intro allI impI)
      fix v :: "complex Matrix.vec" assume v: "dim_vec v = ?N"
      have oc: "v \<oslash> v \<in> carrier_mat ?N ?N" by (rule outer_prod_carrier[OF v v])
      have op: "psd (v \<oslash> v)" by (rule outer_prod_self_psd[OF v])
      have "v \<oslash> v \<in> Hs" unfolding Hs_def using oc psd_hermitian[OF op] by simp
      hence "\<langle>v | W *\<^sub>v v\<rangle> = complex_of_real (ga (v \<oslash> v))" using WHs Tr_mult_outer[OF Wc v] by simp
      thus "\<langle>v | W *\<^sub>v v\<rangle> \<in> \<real> \<and> 0 \<le> Re (\<langle>v | W *\<^sub>v v\<rangle>)" using gaPSD[OF oc op] by simp
    qed
    have Dpsd: "psd D" unfolding D_def by (rule psd_smult_nonneg[OF _ Wpsd Wc]) (use lam in simp)
    have Dtr: "\<forall>A \<in> TS. f A = Tr (D * A)"
    proof
      fix A assume A: "A \<in> TS"
      obtain Hp Kp where Hp: "Hp \<in> TS" and Kp: "Kp \<in> TS" and Hh: "hermitian Hp" and Kh: "hermitian Kp"
        and e: "A = Hp + \<i> \<cdot>\<^sub>m Kp" using operator_system_herm_parts[OF TS A] by blast
      have Hc: "Hp \<in> carrier_mat ?N ?N" and Kc: "Kp \<in> carrier_mat ?N ?N" using TSc[OF Hp] TSc[OF Kp] .
      have HHs: "Hp \<in> Hs" and KHs: "Kp \<in> Hs" unfolding Hs_def using Hc Kc Hh Kh by simp_all
      have "W * A = W * Hp + \<i> \<cdot>\<^sub>m (W * Kp)" unfolding e
        using Wc Hc Kc by (simp add: mult_add_distrib_mat[of _ ?N ?N] mult_smult_distrib)
      hence "Tr (W * A) = Tr (W * Hp) + \<i> * Tr (W * Kp)"
        using Wc Hc Kc by (simp add: Tr_add Tr_smult)
      also have "\<dots> = complex_of_real (lam * Re (f Hp)) + \<i> * complex_of_real (lam * Re (f Kp))"
        unfolding WHs[OF HHs] WHs[OF KHs] fga[OF Hp Hh] fga[OF Kp Kh] ..
      finally have tw: "Tr (W * A) = complex_of_real lam * (complex_of_real (Re (f Hp)) + \<i> * complex_of_real (Re (f Kp)))"
        by (simp add: algebra_simps)
      have "f A = f Hp + \<i> * f Kp" unfolding e fadd[OF Hp operator_systemD(5)[OF TS Kp]] fsm[OF Kp] ..
      also have "\<dots> = complex_of_real (Re (f Hp)) + \<i> * complex_of_real (Re (f Kp))"
        using freal[OF Hp Hh] freal[OF Kp Kh] by simp
      finally have fa: "f A = complex_of_real (Re (f Hp)) + \<i> * complex_of_real (Re (f Kp))" .
      have "Tr (D * A) = complex_of_real (1 / lam) * Tr (W * A)"
        unfolding D_def mult_smult_assoc_mat[OF Wc TSc[OF A]] Tr_smult ..
      thus "f A = Tr (D * A)" unfolding tw fa using lam by simp
    qed
    show ?thesis using Dc Dpsd Dtr by blast

  qed
qed

subsection \<open>Arveson's extension theorem\<close>

theorem arveson_extension:
  fixes OS :: "complex Matrix.mat set" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes OS: "operator_system CARD('n::finite) OS" and L: "lin_on CARD('n) CARD('d::finite) OS \<Phi>"
      and CP: "cp_on CARD('n) CARD('d) OS \<Phi>"
  shows "\<exists>\<Psi>. lin_on CARD('n) CARD('d) (carrier_mat CARD('n) CARD('n)) \<Psi>
             \<and> completely_positive CARD('n) CARD('d) \<Psi> \<and> (\<forall>M \<in> OS. \<Psi> M = \<Phi> M)"
proof -
  let ?n = "CARD('n)" and ?d = "CARD('d)"
  have d: "0 < ?d" by simp
  let ?TS = "Mp ?d ?n OS"
  have TSos: "operator_system (?d * ?n) ?TS" by (rule Mp_operator_system[OF OS])
  have TSos': "operator_system CARD('d \<times> 'n) ?TS" using TSos by (simp add: card_prod)
  have flin: "lin_fun_on ?TS (arveson_functional ?n ?d \<Phi>)" by (rule arveson_functional_lin[OF OS L])
  have fpos: "positive_fun_on ?TS (arveson_functional ?n ?d \<Phi>)"
    using arveson_correspondence(1)[OF OS d L] CP by blast
  obtain D where Dc: "D \<in> carrier_mat CARD('d \<times> 'n) CARD('d \<times> 'n)" and Dp: "psd D"
    and Dtr: "\<forall>A \<in> ?TS. arveson_functional ?n ?d \<Phi> A = Tr (D * A)"
    using positive_functional_extension[where 'k = "'d \<times> 'n", OF TSos' flin fpos] by blast
  have Dc': "D \<in> carrier_mat (?d * ?n) (?d * ?n)" using Dc by (simp add: card_prod)
  define F where "F = (\<lambda>A. Tr (D * A))"
  have full: "Mp ?d ?n (carrier_mat ?n ?n) = carrier_mat (?d * ?n) (?d * ?n)" by (rule Mp_full)
  have Flin: "lin_fun_on (Mp ?d ?n (carrier_mat ?n ?n)) F"
    unfolding lin_fun_on_def full F_def
  proof (intro conjI ballI allI)
    fix A B :: "complex Matrix.mat" assume A: "A \<in> carrier_mat (?d * ?n) (?d * ?n)" and B: "B \<in> carrier_mat (?d * ?n) (?d * ?n)"
    show "Tr (D * (A + B)) = Tr (D * A) + Tr (D * B)"
      unfolding mult_add_distrib_mat[OF Dc' A B] by (rule Tr_add) (use Dc' A B in simp_all)
  next
    fix A :: "complex Matrix.mat" and c :: complex assume A: "A \<in> carrier_mat (?d * ?n) (?d * ?n)"
    show "Tr (D * (c \<cdot>\<^sub>m A)) = c * Tr (D * A)" unfolding mult_smult_distrib[OF Dc' A] Tr_smult ..
  qed
  have Fpos: "positive_fun_on (Mp ?d ?n (carrier_mat ?n ?n)) F"
    unfolding positive_fun_on_def full F_def using Tr_psd_mult_nonneg[OF Dc' _ Dp] by blast
  define \<Psi> where "\<Psi> = arveson_map ?n ?d F"
  have \<Psi>lin: "lin_on ?n ?d (carrier_mat ?n ?n) \<Psi>" unfolding \<Psi>_def by (rule arveson_map_lin[OF operator_system_full Flin])
  have \<Psi>cp: "completely_positive ?n ?d \<Psi>"
    unfolding cp_on_full[symmetric] \<Psi>_def using arveson_correspondence(2)[OF operator_system_full d Flin] Fpos by blast
  have ext: "\<forall>M \<in> OS. \<Psi> M = \<Phi> M"
  proof
    fix M assume M: "M \<in> OS"
    have "\<Psi> M = arveson_map ?n ?d (arveson_functional ?n ?d \<Phi>) M"
    proof (rule eq_matI)
      fix i j assume "i < dim_row (arveson_map ?n ?d (arveson_functional ?n ?d \<Phi>) M)"
        "j < dim_col (arveson_map ?n ?d (arveson_functional ?n ?d \<Phi>) M)"
      hence i: "i < ?d" and j: "j < ?d" by simp_all
      have "unit_block ?d ?n i j M \<in> ?TS" by (rule unit_block_Mp[OF OS M i j])
      thus "\<Psi> M $$ (i,j) = arveson_map ?n ?d (arveson_functional ?n ?d \<Phi>) M $$ (i,j)"
        unfolding \<Psi>_def using Dtr i j by (simp add: arveson_map_index F_def)
    qed (simp_all add: \<Psi>_def)
    also have "\<dots> = \<Phi> M" by (rule arveson_map_of_functional[OF OS L M d])
    finally show "\<Psi> M = \<Phi> M" .
  qed
  show ?thesis using \<Psi>lin \<Psi>cp ext by blast
qed

text \<open>Corollary: a completely positive map on an operator system has a Kraus form.\<close>

corollary arveson_kraus:
  fixes OS :: "complex Matrix.mat set" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes OS: "operator_system CARD('n::finite) OS" and L: "lin_on CARD('n) CARD('d::finite) OS \<Phi>"
      and CP: "cp_on CARD('n) CARD('d) OS \<Phi>"
  shows "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat CARD('d) CARD('n)) \<and> (\<forall>M \<in> OS. \<Phi> M = kraus_map_dim CARD('d) Ws M)"
proof -
  obtain \<Psi> where \<Psi>lin: "lin_on CARD('n) CARD('d) (carrier_mat CARD('n) CARD('n)) \<Psi>"
    and \<Psi>cp: "completely_positive CARD('n) CARD('d) \<Psi>" and ext: "\<forall>M \<in> OS. \<Psi> M = \<Phi> M"
    using arveson_extension[OF OS L CP] by blast
  have add: "\<And>A B. A \<in> carrier_mat CARD('n) CARD('n) \<Longrightarrow> B \<in> carrier_mat CARD('n) CARD('n) \<Longrightarrow> \<Psi> (A + B) = \<Psi> A + \<Psi> B"
    and sm: "\<And>c A. A \<in> carrier_mat CARD('n) CARD('n) \<Longrightarrow> \<Psi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Psi> A"
    and rg: "\<forall>A. A \<in> carrier_mat CARD('n) CARD('n) \<longrightarrow> \<Psi> A \<in> carrier_mat CARD('d) CARD('d)"
    using \<Psi>lin unfolding lin_on_def by blast+
  have "psd (choi_matrix CARD('n) CARD('d) \<Psi>)" using choi_theorem[OF add sm rg] \<Psi>cp by simp
  then obtain Ws where Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat CARD('d) CARD('n)"
    and Wk: "\<forall>A. A \<in> carrier_mat CARD('n) CARD('n) \<longrightarrow> \<Psi> A = kraus_map_dim CARD('d) Ws A"
    using kraus_rep_of_psd_choi[OF add sm rg] by fastforce
  show ?thesis using Wc Wk ext operator_systemD(1)[OF OS] by (metis subsetD)
qed

subsection \<open>Factoring a CP map through a unital or a trace-preserving one (D26-1)\<close>

text \<open>The $i$-th block embedding $B_i:\mathbb C^n\to\mathbb C^{kn}$.  The $B_i$ are isometries with
orthogonal ranges, $\sum_iB_iB_i^*=I$, so a Kraus representation $\Phi(X)=\sum_iW_iXW_i^*$ gives
$\Phi(X)=V^*\psi(X)V$ with $\psi(X)=\sum_iB_iXB_i^*$ unital and $V=\sum_iB_iW_i^*$.\<close>

definition blk_emb :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "blk_emb k n i = Matrix.mat (k * n) n (\<lambda>(x, y). if x div n = i \<and> x mod n = y then 1 else 0)"

lemma blk_emb_carrier [simp]: "blk_emb k n i \<in> carrier_mat (k * n) n"
  by (simp add: blk_emb_def)

lemma blk_emb_dims [simp]: "dim_row (blk_emb k n i) = k * n" "dim_col (blk_emb k n i) = n"
  by (simp_all add: blk_emb_def)

lemma blk_cond:
  fixes x y i n :: nat
  assumes y: "y < n"
  shows "(x div n = i \<and> x mod n = y) \<longleftrightarrow> x = i * n + y"
proof
  assume "x div n = i \<and> x mod n = y"
  thus "x = i * n + y" using div_mult_mod_eq[of x n] by simp
next
  assume x: "x = i * n + y"
  have n: "0 < n" using y by simp
  show "x div n = i \<and> x mod n = y" unfolding x using y n by simp
qed

text \<open>$J_i=e_i\otimes I_n:\C^n\to\C^k\otimes\C^n$ embeds $\C^n$ as the $i$-th block, and the blocks fill
the space: $\sum_iJ_iJ_i^*=I_{kn}$.\<close>

lemma blk_emb_gram_entry:
  assumes x: "x < k * n" and y: "y < k * n"
  shows "(blk_emb k n i * ((blk_emb k n i)\<^sup>\<dagger>)) $$ (x, y) =
         (if x div n = i \<and> y div n = i \<and> x mod n = y mod n then 1 else 0)"
proof -
  have n: "0 < n" using x by (cases n) auto
  have "(blk_emb k n i * ((blk_emb k n i)\<^sup>\<dagger>)) $$ (x, y) =
        (\<Sum>t<n. blk_emb k n i $$ (x, t) * cnj (blk_emb k n i $$ (y, t)))"
    using x y by (simp add: scalar_prod_def dagger_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>t<n. if t = x mod n then (if x div n = i \<and> y div n = i \<and> x mod n = y mod n then 1 else 0) else 0)"
    by (rule sum.cong) (use x y in \<open>auto simp: blk_emb_def\<close>)
  also have "\<dots> = (if x div n = i \<and> y div n = i \<and> x mod n = y mod n then 1 else 0)"
    using n by simp
  finally show ?thesis .
qed

lemma blk_emb_gram:
  "foldr (\<lambda>B acc. B * (B\<^sup>\<dagger>) + acc) (map (blk_emb k n) [0..<k]) (0\<^sub>m (k * n) (k * n)) = 1\<^sub>m (k * n)"
proof -
  let ?f = "\<lambda>i. blk_emb k n i * ((blk_emb k n i)\<^sup>\<dagger>)"
  let ?F = "foldr (\<lambda>i acc. ?f i + acc) [0..<k] (0\<^sub>m (k * n) (k * n))"
  have fc: "\<forall>i \<in> set [0..<k]. ?f i \<in> carrier_mat (k * n) (k * n)"
    by (auto intro!: mult_carrier_mat dagger_carrier)
  have e: "foldr (\<lambda>B acc. B * (B\<^sup>\<dagger>) + acc) (map (blk_emb k n) [0..<k]) (0\<^sub>m (k * n) (k * n)) = ?F"
    by (simp add: foldr_map o_def)
  have Fc: "?F \<in> carrier_mat (k * n) (k * n)" by (rule foldr_add_mat_carrier_rect[OF fc])
  have "?F = 1\<^sub>m (k * n)"
  proof (rule eq_matI)
    fix x y assume "x < dim_row (1\<^sub>m (k * n))" "y < dim_col (1\<^sub>m (k * n))"
    hence x: "x < k * n" and y: "y < k * n" by simp_all
    have xk: "x div n < k" "y div n < k" using x y by (simp_all add: less_mult_imp_div_less)
    have "?F $$ (x, y) = (\<Sum>i\<leftarrow>[0..<k]. ?f i $$ (x, y))"
      by (rule foldr_add_mat_index_rect[OF fc x y])
    also have "\<dots> = (\<Sum>i<k. ?f i $$ (x, y))" by (simp add: sum_list_distinct_conv_sum_set atLeast0LessThan)
    also have "\<dots> = (\<Sum>i<k. if i = x div n then (if y div n = x div n \<and> x mod n = y mod n then 1 else 0) else 0)"
      by (rule sum.cong) (unfold blk_emb_gram_entry[OF x y], auto)
    also have "\<dots> = (if y div n = x div n \<and> x mod n = y mod n then 1 else 0)" using xk by simp
    also have "\<dots> = 1\<^sub>m (k * n) $$ (x, y)"
    proof -
      have "(y div n = x div n \<and> x mod n = y mod n) \<longleftrightarrow> x = y"
      proof
        assume h: "y div n = x div n \<and> x mod n = y mod n"
        show "x = y" using div_mult_mod_eq[of x n] div_mult_mod_eq[of y n] h by simp
      qed simp
      thus ?thesis using x y by simp
    qed
    finally show "?F $$ (x, y) = 1\<^sub>m (k * n) $$ (x, y)" .
  qed (use Fc in simp_all)
  thus ?thesis unfolding e .
qed

lemma kraus_compose_single: "kraus_compose [A] Es = map (\<lambda>E. A * E) Es"
  by (induction Es) (simp_all add: kraus_compose_Cons)

text \<open>$V$ has the blocks $W_i^*$ stacked vertically, so $V^*B_i=W_i$.\<close>

definition kraus_stack_dag :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "kraus_stack_dag n d Ws = Matrix.mat (length Ws * n) d (\<lambda>(x, c). cnj (Ws ! (x div n) $$ (c, x mod n)))"

lemma kraus_stack_dag_blk:
  assumes Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and i: "i < length Ws"
  shows "(kraus_stack_dag n d Ws)\<^sup>\<dagger> * blk_emb (length Ws) n i = Ws ! i"
proof (rule eq_matI)
  let ?k = "length Ws"
  have Wi: "Ws ! i \<in> carrier_mat d n" using Wc i by simp
  fix c y assume "c < dim_row (Ws ! i)" "y < dim_col (Ws ! i)"
  hence c: "c < d" and y: "y < n" using Wi by auto
  have iy: "i * n + y < ?k * n" by (rule mult_index_lt[OF i y])
  have "((kraus_stack_dag n d Ws)\<^sup>\<dagger> * blk_emb ?k n i) $$ (c, y) =
        (\<Sum>x<?k * n. Ws ! (x div n) $$ (c, x mod n) * blk_emb ?k n i $$ (x, y))"
    using c y by (simp add: scalar_prod_def dagger_def kraus_stack_dag_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>x<?k * n. if x = i * n + y then Ws ! (x div n) $$ (c, x mod n) else 0)"
    by (rule sum.cong) (use y in \<open>auto simp: blk_emb_def blk_cond\<close>)
  also have "\<dots> = Ws ! i $$ (c, y)" using iy y by simp
  finally show "((kraus_stack_dag n d Ws)\<^sup>\<dagger> * blk_emb ?k n i) $$ (c, y) = Ws ! i $$ (c, y)" .
qed (use Wc i in \<open>auto simp: kraus_stack_dag_def\<close>)

text \<open>Proposition (Day 26): a CP map $\Phi:S\to M_d$ on an operator system with $\Phi(I)=P$ is
$\Phi(X)=V^*\psi(X)V$ with $\psi$ unital and completely positive (here even on all of $M_n$) and
$V^*V=P$.  The notes compress $\Phi$ to the range of $P$; here the Kraus form of
@{thm [source] arveson_kraus} is used.\<close>

theorem cp_unital_factor:
  fixes OS :: "complex Matrix.mat set" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes OS: "operator_system CARD('n::finite) OS" and L: "lin_on CARD('n) CARD('d::finite) OS \<Phi>"
      and CP: "cp_on CARD('n) CARD('d) OS \<Phi>"
  shows "\<exists>r V \<psi>. 0 < r \<and> V \<in> carrier_mat r CARD('d) \<and> \<psi> \<in> UCP CARD('n) r
               \<and> lin_on CARD('n) r (carrier_mat CARD('n) CARD('n)) \<psi>
               \<and> (\<forall>X \<in> OS. \<Phi> X = (V\<^sup>\<dagger>) * \<psi> X * V) \<and> (V\<^sup>\<dagger>) * V = \<Phi> (1\<^sub>m CARD('n))"
proof -
  let ?n = "CARD('n)" and ?d = "CARD('d)"
  obtain Ws0 where W0c: "\<forall>W \<in> set Ws0. W \<in> carrier_mat ?d ?n" and W0: "\<forall>M \<in> OS. \<Phi> M = kraus_map_dim ?d Ws0 M"
    using arveson_kraus[OF OS L CP] by blast
  define Ws where "Ws = 0\<^sub>m ?d ?n # Ws0"
  define k where "k = length Ws"
  have Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat ?d ?n" using W0c by (simp add: Ws_def)
  have k: "0 < k" by (simp add: k_def Ws_def)
  have OSc: "\<And>M. M \<in> OS \<Longrightarrow> M \<in> carrier_mat ?n ?n" using operator_systemD(1)[OF OS] by auto
  have W: "\<forall>M \<in> OS. \<Phi> M = kraus_map_dim ?d Ws M"
  proof
    fix M assume M: "M \<in> OS"
    have "kraus_map_dim ?d Ws M = kraus_map_dim ?d Ws0 M"
      unfolding Ws_def by (rule kraus_map_dim_zero_head[OF W0c OSc[OF M]])
    thus "\<Phi> M = kraus_map_dim ?d Ws M" using W0 M by simp
  qed
  define Bs where "Bs = map (blk_emb k ?n) [0..<k]"
  define V where "V = kraus_stack_dag ?n ?d Ws"
  define \<psi> where "\<psi> = kraus_map_dim (k * ?n) Bs"
  have Bc: "\<forall>B \<in> set Bs. B \<in> carrier_mat (k * ?n) ?n" by (auto simp: Bs_def)
  have Vc: "V \<in> carrier_mat (k * ?n) ?d" by (simp add: V_def kraus_stack_dag_def k_def)
  have Vd: "V\<^sup>\<dagger> \<in> carrier_mat ?d (k * ?n)" by (rule dagger_carrier[OF Vc])
  have r: "0 < k * ?n" using k by simp
  have cp: "completely_positive ?n (k * ?n) \<psi>" unfolding \<psi>_def by (rule kraus_cp_no_tp[OF Bc]) (use r in simp_all)
  have un: "\<psi> (1\<^sub>m ?n) = 1\<^sub>m (k * ?n)"
  proof -
    have "\<psi> (1\<^sub>m ?n) = foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Bs (0\<^sub>m (k * ?n) (k * ?n))"
      unfolding \<psi>_def by (rule kraus_map_dim_one[OF Bc])
    also have "\<dots> = 1\<^sub>m (k * ?n)" unfolding Bs_def by (rule blk_emb_gram)
    finally show ?thesis .
  qed
  have comp: "kraus_compose [V\<^sup>\<dagger>] Bs = Ws"
  proof (rule nth_equalityI)
    show "length (kraus_compose [V\<^sup>\<dagger>] Bs) = length Ws" by (simp add: Bs_def k_def)
    fix i assume "i < length (kraus_compose [V\<^sup>\<dagger>] Bs)"
    hence i: "i < k" by (simp add: Bs_def)
    have "kraus_compose [V\<^sup>\<dagger>] Bs ! i = V\<^sup>\<dagger> * blk_emb k ?n i"
      using i by (simp add: kraus_compose_single Bs_def)
    also have "\<dots> = Ws ! i" unfolding V_def k_def by (rule kraus_stack_dag_blk[OF Wc]) (use i in \<open>simp add: k_def\<close>)
    finally show "kraus_compose [V\<^sup>\<dagger>] Bs ! i = Ws ! i" .
  qed
  have fac: "\<Phi> X = (V\<^sup>\<dagger>) * \<psi> X * V" if X: "X \<in> OS" for X
  proof -
    have Xc: "X \<in> carrier_mat ?n ?n" by (rule OSc[OF X])
    have pc: "\<psi> X \<in> carrier_mat (k * ?n) (k * ?n)" unfolding \<psi>_def by (rule kraus_map_dim_carrier[OF Bc Xc])
    have "\<Phi> X = kraus_map_dim ?d (kraus_compose [V\<^sup>\<dagger>] Bs) X" using W X unfolding comp by simp
    also have "\<dots> = kraus_map_dim ?d [V\<^sup>\<dagger>] (\<psi> X)"
      unfolding \<psi>_def by (rule kraus_map_dim_compose) (use Vd Bc Xc in simp_all)
    also have "\<dots> = (V\<^sup>\<dagger>) * \<psi> X * V"
      using right_add_zero_mat[OF mult_carrier_mat[OF mult_carrier_mat[OF Vd pc] Vc]]
      by (simp add: dagger_of_dagger_is_id)
    finally show ?thesis .
  qed
  have one: "1\<^sub>m ?n \<in> OS" using operator_systemD(2)[OF OS] .
  have "(V\<^sup>\<dagger>) * V = \<Phi> (1\<^sub>m ?n)" using fac[OF one] right_mult_one_mat[OF Vd] by (simp add: un)
  moreover have "\<psi> \<in> UCP ?n (k * ?n)" using cp un by (simp add: UCP_def unital_map_def)
  moreover have "lin_on ?n (k * ?n) (carrier_mat ?n ?n) \<psi>" unfolding \<psi>_def by (rule kraus_lin_on[OF Bc])
  ultimately show ?thesis using r Vc fac by blast
qed

text \<open>$V$ with the blocks $W_i$ stacked vertically, so $B_i^*V=W_i$.\<close>

definition kraus_stack :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "kraus_stack n d Ws = Matrix.mat (length Ws * d) n (\<lambda>(x, c). Ws ! (x div d) $$ (x mod d, c))"

lemma kraus_stack_blk:
  assumes Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and i: "i < length Ws"
  shows "(blk_emb (length Ws) d i)\<^sup>\<dagger> * kraus_stack n d Ws = Ws ! i"
proof (rule eq_matI)
  let ?k = "length Ws"
  have Wi: "Ws ! i \<in> carrier_mat d n" using Wc i by simp
  fix a c assume "a < dim_row (Ws ! i)" "c < dim_col (Ws ! i)"
  hence a: "a < d" and c: "c < n" using Wi by auto
  have ia: "i * d + a < ?k * d" by (rule mult_index_lt[OF i a])
  have "((blk_emb ?k d i)\<^sup>\<dagger> * kraus_stack n d Ws) $$ (a, c) =
        (\<Sum>x<?k * d. cnj (blk_emb ?k d i $$ (x, a)) * Ws ! (x div d) $$ (x mod d, c))"
    using a c by (simp add: scalar_prod_def dagger_def kraus_stack_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>x<?k * d. if x = i * d + a then Ws ! (x div d) $$ (x mod d, c) else 0)"
    by (rule sum.cong) (use a in \<open>auto simp: blk_emb_def blk_cond\<close>)
  also have "\<dots> = Ws ! i $$ (a, c)" using ia a by simp
  finally show "((blk_emb ?k d i)\<^sup>\<dagger> * kraus_stack n d Ws) $$ (a, c) = Ws ! i $$ (a, c)" .
qed (use Wc i in \<open>auto simp: kraus_stack_def\<close>)

text \<open>Proposition (Day 26): a CP map $\Phi:M_n\to M_d$ is $\Phi(X)=\psi(VXV^*)$ with $\psi:M_r\to M_d$
completely positive and trace preserving.  The notes dualise the previous proposition; here
$\psi(Y)=\sum_iB_i^*YB_i$ and $V=\sum_iB_iW_i$ directly.\<close>

theorem cp_tp_factor:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes L: "lin_on CARD('n::finite) CARD('d::finite) (carrier_mat CARD('n) CARD('n)) \<Phi>"
      and CP: "completely_positive CARD('n) CARD('d) \<Phi>"
  shows "\<exists>r V \<psi>. 0 < r \<and> V \<in> carrier_mat r CARD('n) \<and> \<psi> \<in> CPTP r CARD('d)
               \<and> lin_on r CARD('d) (carrier_mat r r) \<psi>
               \<and> (\<forall>X \<in> carrier_mat CARD('n) CARD('n). \<Phi> X = \<psi> (V * X * (V\<^sup>\<dagger>)))"
proof -
  let ?n = "CARD('n)" and ?d = "CARD('d)"
  have CP': "cp_on ?n ?d (carrier_mat ?n ?n) \<Phi>" using CP by (simp add: cp_on_full)
  obtain Ws0 where W0c: "\<forall>W \<in> set Ws0. W \<in> carrier_mat ?d ?n"
    and W0: "\<forall>M \<in> carrier_mat ?n ?n. \<Phi> M = kraus_map_dim ?d Ws0 M"
    using arveson_kraus[OF operator_system_full L CP'] by blast
  define Ws where "Ws = 0\<^sub>m ?d ?n # Ws0"
  define k where "k = length Ws"
  have Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat ?d ?n" using W0c by (simp add: Ws_def)
  have k: "0 < k" by (simp add: k_def Ws_def)
  have W: "\<forall>M \<in> carrier_mat ?n ?n. \<Phi> M = kraus_map_dim ?d Ws M"
  proof
    fix M :: "complex Matrix.mat" assume M: "M \<in> carrier_mat ?n ?n"
    have "kraus_map_dim ?d Ws M = kraus_map_dim ?d Ws0 M"
      unfolding Ws_def by (rule kraus_map_dim_zero_head[OF W0c M])
    thus "\<Phi> M = kraus_map_dim ?d Ws M" using W0 M by simp
  qed
  define Cs where "Cs = map (\<lambda>i. (blk_emb k ?d i)\<^sup>\<dagger>) [0..<k]"
  define V where "V = kraus_stack ?n ?d Ws"
  define \<psi> where "\<psi> = kraus_map_dim ?d Cs"
  have Cc: "\<forall>C \<in> set Cs. C \<in> carrier_mat ?d (k * ?d)" by (auto simp: Cs_def intro!: dagger_carrier)
  have Vc: "V \<in> carrier_mat (k * ?d) ?n" by (simp add: V_def kraus_stack_def k_def)
  have r: "0 < k * ?d" using k by simp
  have tp: "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Cs (0\<^sub>m (k * ?d) (k * ?d)) = 1\<^sub>m (k * ?d)"
  proof -
    have "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Cs (0\<^sub>m (k * ?d) (k * ?d)) =
          foldr (\<lambda>B acc. B * (B\<^sup>\<dagger>) + acc) (map (blk_emb k ?d) [0..<k]) (0\<^sub>m (k * ?d) (k * ?d))"
      by (simp add: Cs_def foldr_map o_def dagger_of_dagger_is_id)
    thus ?thesis using blk_emb_gram by simp
  qed
  have ko: "kraus_operators (k * ?d) ?d Cs" unfolding kraus_operators_def using Cc tp by simp
  have "\<psi> \<in> CPTP (k * ?d) ?d"
    unfolding CPTP_def \<psi>_def using kraus_cp_no_tp[OF Cc r] kraus_is_trace_preserving[OF ko] by simp
  moreover have "lin_on (k * ?d) ?d (carrier_mat (k * ?d) (k * ?d)) \<psi>" unfolding \<psi>_def by (rule kraus_lin_on[OF Cc])
  moreover have "\<Phi> X = \<psi> (V * X * (V\<^sup>\<dagger>))" if X: "X \<in> carrier_mat ?n ?n" for X
  proof -
    have mp: "map (\<lambda>C. C * V) Cs = Ws"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>C. C * V) Cs) = length Ws" by (simp add: Cs_def k_def)
      fix i assume "i < length (map (\<lambda>C. C * V) Cs)"
      hence i: "i < k" by (simp add: Cs_def)
      have "map (\<lambda>C. C * V) Cs ! i = (blk_emb k ?d i)\<^sup>\<dagger> * V" using i by (simp add: Cs_def)
      also have "\<dots> = Ws ! i" unfolding V_def k_def by (rule kraus_stack_blk[OF Wc]) (use i in \<open>simp add: k_def\<close>)
      finally show "map (\<lambda>C. C * V) Cs ! i = Ws ! i" .
    qed
    have "\<Phi> X = kraus_map_dim ?d (map (\<lambda>C. C * V) Cs) X" using W X unfolding mp by simp
    also have "\<dots> = \<psi> (V * X * (V\<^sup>\<dagger>))" unfolding \<psi>_def by (rule kraus_map_dim_map_mult_right[OF Cc Vc X])
    finally show ?thesis .
  qed
  ultimately show ?thesis using r Vc by blast
qed

end
