(*  Title:   Unitary_Tensor_Algebra.thy
    Author:  Dustin Bryant, unitary matrices and Kronecker products: the algebra used from Day 3 on
*)

theory Unitary_Tensor_Algebra
  imports Day02_Trace_Projections
begin

section \<open>Unitary algebra\<close>

text \<open>Library-level consequences of unitarity ($U^\dagger U=I$ and $UU^\dagger=I$ in the
library's definition) used throughout; Paulsen's Day 3 characterisations of unitaries are
in theory Day03\_Unitary\_Matrices.\<close>

lemma unitary_square_dim:
  assumes uA: "unitary A"
  shows "dim_row A = dim_col A"
proof -
  let ?m = "dim_row A"
  let ?n = "dim_col A"

  have inv_l: "(A\<^sup>\<dagger>) * A = 1\<^sub>m ?n"
    using uA unfolding unitary_def by auto
  have inv_r: "A * (A\<^sup>\<dagger>) = 1\<^sub>m ?m"
    using uA unfolding unitary_def by auto

  have dim_adj: "dim_row (A\<^sup>\<dagger>) = ?n" "dim_col (A\<^sup>\<dagger>) = ?m"
    by (simp_all add: dagger_def)

  have left_expand:
    "(\<Sum>c=0..<?n. (((A\<^sup>\<dagger>) * A) $$ (c,c))) =
     (\<Sum>c=0..<?n. \<Sum>r=0..<?m. cnj (A $$ (r,c)) * A $$ (r,c))"
  proof (rule sum.cong[OF refl])
    fix c
    assume "c \<in> {0..<dim_col A}"
    then have c_lt: "c < ?n"
      using atLeastLessThan_iff by blast
    have "(((A\<^sup>\<dagger>) * A) $$ (c,c)) =
          (\<Sum>r=0..<?m. (A\<^sup>\<dagger>) $$ (c,r) * A $$ (r,c))"
      by (simp add: atLeast0LessThan c_lt)
    also have "... = (\<Sum>r=0..<?m. cnj (A $$ (r,c)) * A $$ (r,c))"
    proof (rule sum.cong[OF refl])
      fix x 
      assume "x \<in> {0..<dim_row A}"
      then have x_lt: "x < ?m"
        using atLeastLessThan_iff by blast
      show "(A\<^sup>\<dagger>) $$ (c,x) * A $$ (x,c) =
            cnj (A $$ (x,c)) * A $$ (x,c)"
        using c_lt x_lt by (simp add: dagger_def)
    qed
    finally show "(A\<^sup>\<dagger> * A) $$ (c, c) = (\<Sum>r = 0..<dim_row A. cnj (A $$ (r, c)) * A $$ (r, c))" .
  qed

  have right_expand:
    "(\<Sum>r=0..<?m. ((A * (A\<^sup>\<dagger>)) $$ (r,r))) =
     (\<Sum>r=0..<?m. \<Sum>c=0..<?n. A $$ (r,c) * cnj (A $$ (r,c)))"
  proof (rule sum.cong[OF refl])
    fix r
    assume "r \<in> {0..<dim_row A}"
    then have r: "r < ?m"
      using atLeastLessThan_iff by blast
    have "((A * (A\<^sup>\<dagger>)) $$ (r,r)) =
          (\<Sum>c=0..<?n. A $$ (r,c) * (A\<^sup>\<dagger>) $$ (c,r))"
      using r dim_adj atLeast0LessThan
      by (auto simp: scalar_prod_def)
    also have "... = (\<Sum>c=0..<?n. A $$ (r,c) * cnj (A $$ (r,c)))"
    proof (rule sum.cong[OF refl])
      fix c 
      assume "c \<in> {0..<dim_col A}"
      then have c: "c < ?n"
        using atLeast0LessThan by blast
      show "A $$ (r,c) * (A\<^sup>\<dagger>) $$ (c,r) =
            A $$ (r,c) * cnj (A $$ (r,c))"
        using c r by (simp add: dagger_def)
    qed
    finally show "((A * (A\<^sup>\<dagger>)) $$ (r,r)) =
                  (\<Sum>c=0..<?n. A $$ (r,c) * cnj (A $$ (r,c)))" .
  qed
  have left_id: "(\<Sum>c=0..<?n. (((A\<^sup>\<dagger>) * A) $$ (c,c))) = of_nat ?n"
    using inv_l by simp

  have right_id: "(\<Sum>r=0..<?m. ((A * (A\<^sup>\<dagger>)) $$ (r,r))) = of_nat ?m"
    using inv_r by simp
  have "of_nat ?n = (\<Sum>c=0..<?n. \<Sum>r=0..<?m. cnj (A $$ (r,c)) * A $$ (r,c))"
    using left_id left_expand by simp
  also have "... =
        (\<Sum>c=0..<?n. \<Sum>r=0..<?m. A $$ (r,c) * cnj (A $$ (r,c)))"
    by (intro sum.cong[OF refl] sum.cong[OF refl]) (simp add: mult.commute)
  also have "... =
        (\<Sum>r=0..<?m. \<Sum>c=0..<?n. A $$ (r,c) * cnj (A $$ (r,c)))"
    using sum.swap by force
  also have "... = of_nat ?m"
    using right_id right_expand by simp
  finally have "of_nat ?n = of_nat ?m"
    by simp 
  then show "dim_row A = dim_col A"
    by (metis of_nat_eq_iff)
qed

lemma unitary_inv_l_dimcol:
  assumes uA: "unitary A"
  shows "(A\<^sup>\<dagger>) * A = 1\<^sub>m (dim_col A)"
  using uA unfolding unitary_def by auto

lemma unitary_inv_r_dimrow:
  assumes uA: "unitary A"
  shows "A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_row A)"
  using uA unfolding unitary_def by auto

lemma unitary_inv_l_dimrow:
  assumes uA: "unitary A"
  shows "(A\<^sup>\<dagger>) * A = 1\<^sub>m (dim_row A)"
  by (metis uA unitary_def unitary_square_dim)

lemma unitary_inv_r_dimcol:
  assumes uA: "unitary A"
  shows "A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_col A)"
  by (metis uA unitary_def unitary_square_dim)

lemma unitary_carrier_square_col:
  assumes uA: "unitary A"
  shows "A \<in> carrier_mat (dim_col A) (dim_col A)"
  using unitary_square_dim uA by blast 

lemma unitary_carrier_square_row:
  assumes uA: "unitary A"
  shows "A \<in> carrier_mat (dim_row A) (dim_row A)"
  using uA unitary_square_dim by auto

lemma unitary_dagger:
  assumes uA: "unitary A"
  shows "unitary (A\<^sup>\<dagger>)"
proof -
  have "(A\<^sup>\<dagger>)\<^sup>\<dagger> * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_col (A\<^sup>\<dagger>))"
    using dagger_of_dagger_is_id uA unitary_def by force
  moreover have "(A\<^sup>\<dagger>) * ((A\<^sup>\<dagger>)\<^sup>\<dagger>) = 1\<^sub>m (dim_row (A\<^sup>\<dagger>))"
    using dagger_of_dagger_is_id uA unitary_def by auto
  ultimately show ?thesis
    unfolding unitary_def
    by (simp add: dagger_def)
qed

lemma unitary_mult:
  assumes UA: "unitary A"
      and UB: "unitary B"
      and dimA: "A \<in> carrier_mat n n"
      and dimB: "B \<in> carrier_mat n n"
  shows "unitary (A * B)"
  by (smt (verit, best) UA UB assoc_mult_mat carrier_matD(1,2) 
      dagger_of_prod dimA dimB dim_col_of_dagger mult_carrier_mat right_mult_one_mat
      unitary_carrier_square_col unitary_dagger unitary_def)

lemma unitary_mult2:
  assumes UA: "unitary A"
      and UB: "unitary B"
      and dims: "dim_row A = dim_row B"
  shows "unitary (A * B)"
  by (metis UA UB dims unitary_carrier_square_row unitary_mult)


section \<open>Kronecker products\<close>

text \<open>Kronecker products of matrices, \<^term>\<open>A \<Otimes> B\<close>: the tensor of identities, the
adjoint $(R\otimes T)^*=R^*\otimes T^*$, the mixed-product property
$(R_1\otimes T_1)(R_2\otimes T_2)=R_1R_2\otimes T_1T_2$ (both from Day 9), and unitarity of
tensors of unitaries.\<close>

subsection \<open> Tensor of Identities \<close>

lemma tensor_mat_id:
  "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) = 1\<^sub>m (n * m)"
proof (rule eq_matI)
  show "dim_row (Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m)) = dim_row (1\<^sub>m (n * m))"
    by simp
  show "dim_col (Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m)) = dim_col (1\<^sub>m (n * m))"
    by simp
  fix i j
  assume "i < dim_row (1\<^sub>m (n * m))" "j < dim_col (1\<^sub>m (n * m))"
  then have ij: "i < n * m" "j < n * m" by simp_all

  show "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) $$ (i, j) = (1\<^sub>m (n * m)) $$ (i, j)"
  proof (cases "m = 0")
    case True
    then show ?thesis using ij by simp
  next
    case mpos: False
    then have m_pos: "0 < m" by simp
    have div_i: "i div m < n" using ij m_pos by (simp add: less_mult_imp_div_less)
    have div_j: "j div m < n" using ij m_pos by (simp add: less_mult_imp_div_less)
    have mod_i: "i mod m < m" using m_pos by simp
    have mod_j: "j mod m < m" using m_pos by simp

    have "Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m) $$ (i, j) =
          (1\<^sub>m n) $$ (i div m, j div m) * (1\<^sub>m m) $$ (i mod m, j mod m)"
      using ij
      by (metis bot_nat_0.not_eq_extremum div_i index_one_mat(2,3) index_tensor_mat m_pos not_less_zero) 
    also have "\<dots> = (if i div m = j div m then 1 else 0) *
                     (if i mod m = j mod m then 1 else 0)"
      using div_i div_j mod_i mod_j by simp
    also have "\<dots> = (if i div m = j div m \<and> i mod m = j mod m then 1 else 0)"
      by simp
    also have "\<dots> = (if i = j then 1 else 0)"
    proof -
      have "i div m = j div m \<and> i mod m = j mod m \<longleftrightarrow> i = j"
      proof
        assume "i div m = j div m \<and> i mod m = j mod m"
        then have "m * (i div m) + i mod m = m * (j div m) + j mod m"
          by simp
        then show "i = j"
          by (simp add: mult_div_mod_eq[symmetric])
      qed simp
      then show ?thesis by simp
    qed
    also have "\<dots> = (1\<^sub>m (n * m)) $$ (i, j)"
      using ij by simp
    finally show ?thesis.
  qed
qed


subsection \<open> Tensor Adjoint \<close>

subsection \<open> Mixed-Product Property \<close>


lemma tensor_mat_mult:
  assumes dimAC: "dim_col A = dim_row C"
      and dimBD: "dim_col B = dim_row D"
  shows "Tensor.tensor_mat A B * Tensor.tensor_mat C D =
         Tensor.tensor_mat (A * C) (B * D)"
proof (rule eq_matI)
  let ?ra = "dim_row A"  let ?ca = "dim_col A"
  let ?rb = "dim_row B"  let ?cb = "dim_col B"
  let ?rc = "dim_row C"  let ?cc = "dim_col C"
  let ?rd = "dim_row D"  let ?cd = "dim_col D"

  from dimAC have rc: "?rc = ?ca" by simp
  from dimBD have rd: "?rd = ?cb" by simp

  show "dim_row (Tensor.tensor_mat A B * Tensor.tensor_mat C D) =
        dim_row (Tensor.tensor_mat (A * C) (B * D))"
    using rc rd by simp

  show "dim_col (Tensor.tensor_mat A B * Tensor.tensor_mat C D) =
        dim_col (Tensor.tensor_mat (A * C) (B * D))"
    using rc rd by simp
  
  fix i j
  assume ij_bounds:
    "i < dim_row (Tensor.tensor_mat (A * C) (B * D))"
    "j < dim_col (Tensor.tensor_mat (A * C) (B * D))"

  then have ij: "i < ?ra * ?rb" "j < ?cc * ?cd"
    using rc rd by simp_all

  show "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i, j) =
        Tensor.tensor_mat (A * C) (B * D) $$ (i, j)"
  proof (cases "?cb = 0")
    case True
    then have rd0: "?rd = 0" using rd by simp

    have lhs_zero:
      "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i, j) = 0"
    proof -
      have "dim_col (Tensor.tensor_mat A B) = ?ca * ?cb"
        by simp
      then have "dim_col (Tensor.tensor_mat A B) = 0"
        using True by simp
      then show ?thesis
        using ij by (simp add: rc Matrix.col_def rd0)
    qed

    have rhs_zero:
      "Tensor.tensor_mat (A * C) (B * D) $$ (i, j) = 0"
    proof -
      have bd_zero:
        "\<And>r c. r < ?rb \<Longrightarrow> c < ?cd \<Longrightarrow> (B * D) $$ (r, c) = 0"
      proof -
        fix r c assume "r < ?rb" "c < ?cd"
        then have "(B * D) $$ (r, c) =
                   (\<Sum>k=0..<?cb. B $$ (r,k) * D $$ (k,c))"
          using rd by (auto simp: scalar_prod_def atLeast0LessThan)
        also have "\<dots> = 0" using True by simp
        finally show "(B * D) $$ (r, c) = 0" .
      qed
      show ?thesis
        by (metis (mono_tags, lifting) bd_zero ij(1,2) index_mult_mat(2,3)  
            index_tensor_mat mod_less_divisor mult_eq_0_iff not_gr0 not_less_zero)
    qed
    from lhs_zero rhs_zero show ?thesis by simp
  next
    assume "dim_col B \<noteq> 0"
    then have cb_pos: "0 < ?cb" by simp
    show ?thesis
    proof (cases "?rb = 0")
      show "dim_row B = 0 \<Longrightarrow> ((A \<Otimes> B) * (C \<Otimes> D)) $$ (i, j) = (A * C \<Otimes> B * D) $$ (i, j)"
        using ij(1) by presburger
    next
      assume "dim_row B \<noteq> 0"
      then have rb_pos: "0 < ?rb" by simp

      show ?thesis
      proof (cases "?cd = 0")
        show "dim_col D = 0 \<Longrightarrow> ((A \<Otimes> B) * (C \<Otimes> D)) $$ (i, j) = (A * C \<Otimes> B * D) $$ (i, j)"
          using ij(2) by auto
      next
        assume  cd_nonzero: "dim_col D \<noteq> 0"
        then have cd_pos: "0 < ?cd" by simp

        have div_i: "i div ?rb < ?ra"
          using ij rb_pos by (simp add: less_mult_imp_div_less)
        have mod_i: "i mod ?rb < ?rb"
          using rb_pos by simp
        have div_j: "j div ?cd < ?cc"
          using ij cd_pos by (simp add: less_mult_imp_div_less)
        have mod_j: "j mod ?cd < ?cd"
          using cd_pos by simp

        have lhs_sum:
          "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i,j) =
           (\<Sum>k=0..<?ca*?cb.
              Tensor.tensor_mat A B $$ (i, k) *
              Tensor.tensor_mat C D $$ (k, j))"
          using ij rc rd
          by (auto simp: scalar_prod_def atLeast0LessThan)

        have lhs_expand:
          "(Tensor.tensor_mat A B * Tensor.tensor_mat C D) $$ (i,j)
           = (A * C) $$ (i div ?rb, j div ?cd) *
             (B * D) $$ (i mod ?rb, j mod ?cd)"
          by (smt (verit, del_insts) Matrix.col_def assms(1) bot_nat_0.not_eq_extremum cb_pos 
              cd_pos dimBD dim_col_tensor_mat dim_row_tensor_mat div_i
              div_j ij(1,2) index_mult_mat(1,2,3) index_tensor_mat lambda_zero 
              mult_distr_tensor not_less_zero sprod_vec_0)
          have rhs_expand:
          "Tensor.tensor_mat (A * C) (B * D) $$ (i, j)
           = (A * C) $$ (i div ?rb, j div ?cd) *
             (B * D) $$ (i mod ?rb, j mod ?cd)"
            using cd_pos div_j ij(1,2) by fastforce
            from lhs_expand rhs_expand show ?thesis
          by simp
      qed
    qed
  qed
qed


subsection \<open> Corollaries of the Mixed-Product Property \<close>

lemma tensor_adjoint_mult:
  "(Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>)) * (Tensor.tensor_mat A B) =
   Tensor.tensor_mat ((A\<^sup>\<dagger>) * A) ((B\<^sup>\<dagger>) * B)"
  by (rule tensor_mat_mult, simp_all add: dagger_def)

lemma tensor_mult_adjoint:
  "(Tensor.tensor_mat A B) * (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>)) =
   Tensor.tensor_mat (A * (A\<^sup>\<dagger>)) (B * (B\<^sup>\<dagger>))"
  by (rule tensor_mat_mult, simp_all add: dagger_def)


subsection \<open> Tensor Unitarity \<close>

lemma tensor_mat_unitary_carrier:
  assumes dimA: "A \<in> carrier_mat n n"
      and dimB: "B \<in> carrier_mat m m"
      and uA:   "unitary A"
      and uB:   "unitary B"
  shows "unitary (Tensor.tensor_mat A B)"
proof -
  have dA: "dim_row A = n" "dim_col A = n"
    using dimA by auto
  have dB: "dim_row B = m" "dim_col B = m"
    using dimB by auto

  have invA_l: "((A\<^sup>\<dagger>) * A) = 1\<^sub>m n"
    using uA dimA unfolding unitary_def by auto
  have invA_r: "(A * (A\<^sup>\<dagger>)) = 1\<^sub>m n"
    using uA dimA unfolding unitary_def by auto
  have invB_l: "((B\<^sup>\<dagger>) * B) = 1\<^sub>m m"
    using uB dimB unfolding unitary_def by auto
  have invB_r: "(B * (B\<^sup>\<dagger>)) = 1\<^sub>m m"
    using uB dimB unfolding unitary_def by auto

  have lhs:
    "(((Tensor.tensor_mat A B)\<^sup>\<dagger>) * (Tensor.tensor_mat A B))
      = 1\<^sub>m (n * m)"
  proof -
    have "((Tensor.tensor_mat A B)\<^sup>\<dagger>) * (Tensor.tensor_mat A B)
        = (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>))
          * (Tensor.tensor_mat A B)"
      by (simp add: hermite_cnj_of_tensor)
    also have "\<dots> =
         Tensor.tensor_mat ((A\<^sup>\<dagger>) * A) ((B\<^sup>\<dagger>) * B)"
      by (rule tensor_adjoint_mult)
    also have "\<dots> =
         Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m)"
      using invA_l invB_l by simp
    also have "\<dots> = 1\<^sub>m (n * m)"
      by (rule tensor_mat_id)
    finally show ?thesis .
  qed

  have rhs:
    "((Tensor.tensor_mat A B)
       * ((Tensor.tensor_mat A B)\<^sup>\<dagger>))
      = 1\<^sub>m (n * m)"
  proof -
    have "(Tensor.tensor_mat A B)
          * ((Tensor.tensor_mat A B)\<^sup>\<dagger>)
        = (Tensor.tensor_mat A B)
          * (Tensor.tensor_mat (A\<^sup>\<dagger>) (B\<^sup>\<dagger>))"
      by (simp add: hermite_cnj_of_tensor)
    also have "\<dots> =
         Tensor.tensor_mat (A * (A\<^sup>\<dagger>))
                           (B * (B\<^sup>\<dagger>))"
      by (rule tensor_mult_adjoint)
    also have "\<dots> =
         Tensor.tensor_mat (1\<^sub>m n) (1\<^sub>m m)"
      using invA_r invB_r by simp
    also have "\<dots> = 1\<^sub>m (n * m)"
      by (rule tensor_mat_id)
    finally show ?thesis .
  qed

  show "unitary (Tensor.tensor_mat A B)"
    unfolding unitary_def
    using lhs rhs dA dB by auto
qed

lemma tensor_mat_unitary:
  assumes uA: "unitary A"
      and uB: "unitary B"
  shows "unitary (Tensor.tensor_mat A B)"
  using tensor_mat_unitary_carrier uA uB unitary_carrier_square_row by blast

lemma tensor_mat_unitary_one_left [simp]:
  assumes uA: "unitary A"
  shows "unitary (Tensor.tensor_mat (1\<^sub>m n) A)"
  using id_is_unitary tensor_mat_unitary uA by blast

lemma tensor_mat_unitary_one_right [simp]:
  assumes uA: "unitary A"
  shows "unitary (Tensor.tensor_mat A (1\<^sub>m n))"
  using id_is_unitary tensor_mat_unitary uA by blast


lemma one_smult_mat: "(1::complex) \<cdot>\<^sub>m M = M"
  by (rule eq_matI) simp_all


lemma mult_index_lt:
  fixes i j n m :: nat
  assumes "i < n" and "j < m"
  shows "i * m + j < n * m"
proof -
  have "i * m + j < (i + 1) * m" using assms(2) by simp
  also have "\<dots> \<le> n * m" using assms(1) by (intro mult_le_mono1) simp
  finally show ?thesis .
qed

lemma mult_index_div_mod:
  fixes i l m :: nat
  assumes "l < m"
  shows "(i * m + l) div m = i" "(i * m + l) mod m = l"
  using assms by simp_all


lemma hs_inner_prod_left_add:
  assumes "dim_row A1 = dim_row B" and "dim_col A1 = dim_col B"
      and "dim_row A2 = dim_row B" and "dim_col A2 = dim_col B"
  shows "\<langle>\<langle> A1 + A2 | B \<rangle>\<rangle> = \<langle>\<langle> A1 | B \<rangle>\<rangle> + \<langle>\<langle> A2 | B \<rangle>\<rangle>"
proof -
  have dims:
    "dim_row (A1 + A2) = dim_row B" "dim_col (A1 + A2) = dim_col B"
    using assms by auto
  have "\<langle>\<langle> A1 + A2 | B \<rangle>\<rangle> = cnj (\<langle>\<langle> B | A1 + A2 \<rangle>\<rangle>)"
    using dims by (intro hs_inner_prod_cnj) auto
  also have "\<dots> = cnj (\<langle>\<langle> B | A1 \<rangle>\<rangle> + \<langle>\<langle> B | A2 \<rangle>\<rangle>)"
    using assms by (simp add: hs_inner_prod_right_add)
  also have "\<dots> = cnj (\<langle>\<langle> B | A1 \<rangle>\<rangle>) + cnj (\<langle>\<langle> B | A2 \<rangle>\<rangle>)"
    by simp
  also have "\<dots> = \<langle>\<langle> A1 | B \<rangle>\<rangle> + \<langle>\<langle> A2 | B \<rangle>\<rangle>"
    by (metis assms(1,2,3,4) hs_inner_prod_cnj)    
  finally show ?thesis.
qed

end
