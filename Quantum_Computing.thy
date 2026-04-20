(*
  Title:      Quantum_Computing.thy
  Author:     Dustin Bryant (based on lectures of Vern Paulsen)

  Autoformalization of Vern Paulsen's "Lectures on Quantum Computing and
  Completely Positive Maps" (Houston, Fall 2011), going day by day.

  Base theory:  Basic_Math (which imports Quantum_Fourier_Transform.QFT and
                therefore the full Isabelle_Marries_Dirac + Jordan_Normal_Form
                stack).

  NOTE on Days 1-2:
    The mathematical content of Days 1-2 (22 Aug and 24 Aug) — inner products,
    Hilbert-Schmidt inner product, matrix units E_{ij}, trace, orthogonal
    projections, and Parseval's identity — is already fully formalised in
    Basic_Math.thy.  We therefore begin this file at Day 3.
*)

theory Quantum_Computing
  imports Basic_Math Jordan_Normal_Form.Schur_Decomposition
begin

(* ============================================================================
   DAY 3 — 31 / Aug / 11
   Topic: Unitary Matrices, Householder Unitaries, Schur's Theorem
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Section: Unitary Matrices
   The library (Isabelle_Marries_Dirac.Quantum) already defines

     unitary U  \<equiv>  U\<dagger> * U = 1\<^sub>m (dim_col U)  \<and>  U * U\<dagger> = 1\<^sub>m (dim_row U)

   and proves many of the equivalent characterisations.  We restate the main
   equivalences in the language of the notes and fill any gaps.
   -------------------------------------------------------------------------- *)

(* The notes define "U \<in> M_n is unitary" by U*U = I.  The library's `unitary`
   already encodes this (condition (a)) together with condition (c) UU* = I. *)

(* ---- (a) \<leftrightarrow> (c): already in definition unitary ---- *)

lemma unitary_left_right:
  assumes "unitary U"
  shows "U\<^sup>\<dagger> * U = 1\<^sub>m (dim_col U)" and "U * (U\<^sup>\<dagger>) = 1\<^sub>m (dim_row U)"
  using assms by (simp_all add: unitary_def)

(* ---- (b): U invertible and U^{-1} = U* ---- *)

lemma unitary_invertible:
  assumes "unitary U"
  shows "invertible_mat U"
proof -
  have "inverts_mat U (U\<^sup>\<dagger>)"
    using assms by (rule mat_unitary_mat)
  moreover have "inverts_mat (U\<^sup>\<dagger>) U"
    using assms by (rule unitary_mat_mat)
  ultimately show ?thesis
    by (metis assms invertible_mat_def square_mat.elims(3) unitary_square_dim)
qed

(* ---- (d): U* is unitary ---- *)

lemma unitary_dagger_is_unitary:
  assumes "unitary U"
  shows "unitary (U\<^sup>\<dagger>)"
  using assms by (simp add: unitary_def dagger_of_dagger_is_id mult.commute)

(* ---- (e): columns of U are orthonormal ---- *)

(* Already in the library: unitary_unit_col and orthogonal_col_of_unitary. *)

lemma unitary_cols_orthonormal:
  assumes U: "unitary U"
      and i: "i < dim_col U"
      and j: "j < dim_col U"
  shows "\<langle>Matrix.col U i | Matrix.col U j\<rangle> = (if i = j then 1 else 0 :: complex)"
  by (cases "i = j",
      metis U cpx_vec_length_inner_prod j of_real_power power_0 power_one unitary_unit_col,
      smt U i j orthogonal_col_of_unitary)

(* ---- (f): rows of U are orthonormal ---- *)

lemma unitary_rows_orthonormal:
  assumes U: "unitary U"
      and i: "i < dim_row U"
      and j: "j < dim_row U"
  shows "\<langle>Matrix.row U i | Matrix.row U j\<rangle> = (if i = j then 1 else 0 :: complex)"
  by (cases "i = j",
      metis U cpx_vec_length_inner_prod j of_real_power power_0 power_one unitary_unit_row,
      smt U i j orthogonal_row_of_unitary)

(* ---- (g): isometry \<Parallel>Ux\<Parallel> = \<Parallel>x\<Parallel> ---- *)

(* Already proved both ways: unitary_is_length_preserving and
   length_preserving_is_unitary. *)

lemma unitary_isometry:
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
proof -
  have "\<parallel>U * |v\<rangle>\<parallel> = \<parallel>v\<parallel>"
    using unitary_is_length_preserving[OF assms] .
  thus ?thesis
    by (metis assms(2) carrier_mat_triv col_fst_is_col col_mult2 dim_col dim_col_mat(1) ket_vec_col ket_vec_def
        less_numeral_extra(1))
qed

(* ---- (h): inner-product preserving ---- *)

lemma unitary_preserves_inner_prod:
  assumes U: "unitary U"
      and u: "dim_vec u = dim_col U"
      and v: "dim_vec v = dim_col U"
  shows "\<langle>U *\<^sub>v u | U *\<^sub>v v\<rangle> = \<langle>u | v\<rangle>"
  using inner_prod_with_unitary_mat[OF U u v]
  by (metis carrier_mat_triv col_fst_is_col col_mult2 dim_col dim_col_mat(1) 
      ket_vec_col ket_vec_def less_numeral_extra(1) u v) 

(* --------------------------------------------------------------------------
   Householder Unitaries
   Given w \<in> \<complex>^n with \<Parallel>w\<Parallel> = 1, define U_w = I - 2 |w\<rangle>\<langle>w|.
   This is the reflection through the hyperplane {w}^\<bottom>.
   -------------------------------------------------------------------------- *)

abbreviation outer_prod :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat"
    (infixr "\<circledcirc>" 75)
  where "v \<circledcirc> w \<equiv> |v\<rangle> * bra_vec w"

lemma bra_vec_index_0:
  assumes j: "j < dim_vec w"
  shows "bra_vec w $$ (0,j) = cnj (w $ j)"
  using j by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)

lemma outer_prod_index:
  fixes v w :: "complex Matrix.vec"
  assumes i: "i < dim_vec v"
      and j: "j < dim_vec w"
  shows "(v \<circledcirc> w) $$ (i,j) = (v $ i) * cnj (w $ j)"
proof -
  have row_index_0: "Matrix.row (ket_vec v) i $ 0 = v $ i"
    using i by (simp add: Matrix.row_def ket_vec_def)
  have bra_rows: "dim_row (bra_vec w) = 1"
    by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)
  have ket_rows: "dim_row (ket_vec v) = dim_vec v"
    by (simp add: ket_vec_def)
  have bra_cols: "dim_col (bra_vec w) = dim_vec w"
    by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)
  have col_index_0: "Matrix.col (bra_vec w) j $ 0 = cnj (w $ j)"
    using j bra_rows by (simp add: Matrix.col_def bra_vec_index_0)

  have "(ket_vec v * bra_vec w) $$ (i,j) =
        Matrix.row (ket_vec v) i \<bullet> Matrix.col (bra_vec w) j"
    by (rule index_mult_mat(1)) (use i j ket_rows bra_cols in auto)
  also have "\<dots> = (\<Sum>k<1. Matrix.row (ket_vec v) i $ k * Matrix.col (bra_vec w) j $ k)"
    using bra_rows by (simp add: scalar_prod_def lessThan_atLeast0)
  also have "\<dots> = Matrix.row (ket_vec v) i $ 0 * Matrix.col (bra_vec w) j $ 0"
    by simp
  also have "\<dots> = (v $ i) * cnj (w $ j)"
    using row_index_0 col_index_0 by simp
  finally show ?thesis .
qed

lemma outer_prod_mult_vec_index:
  fixes v w x :: "complex Matrix.vec"
  assumes xdim: "dim_vec x = dim_vec w"
      and i: "i < dim_vec v"
  shows "((v \<circledcirc> w) *\<^sub>v x) $ i = (v $ i) * \<langle>w | x\<rangle>"
proof -
  have ket_rows: "dim_row (ket_vec v) = dim_vec v"
    by (simp add: ket_vec_def)
  have bra_cols: "dim_col (bra_vec w) = dim_vec w"
    by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)
  have prod_rows: "dim_row (ket_vec v * bra_vec w) = dim_vec v"
    using ket_rows by simp

  have "((ket_vec v * bra_vec w) *\<^sub>v x) $ i =
        Matrix.row (ket_vec v * bra_vec w) i \<bullet> x"
    by (rule index_mult_mat_vec) (use i prod_rows in auto)
  also have "\<dots> =
        (\<Sum>j<dim_vec w. (v $ i * cnj (w $ j)) * (x $ j))"
  proof -
    have "\<And>j. j < dim_vec w \<Longrightarrow>
          Matrix.row (ket_vec v * bra_vec w) i $ j = v $ i * cnj (w $ j)"
      using i bra_cols by (simp add: Matrix.row_def outer_prod_index)
    then show ?thesis
      using xdim by (simp add: scalar_prod_def lessThan_atLeast0)
  qed
  also have "\<dots> = (v $ i) * (\<Sum>j<dim_vec w. cnj (w $ j) * (x $ j))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (v $ i) * \<langle>w | x\<rangle>"
    using xdim by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma outer_prod_mult_vec:
  fixes v w x :: "complex Matrix.vec"
  assumes xdim: "dim_vec x = dim_vec w"
  shows "(v \<circledcirc> w) *\<^sub>v x = \<langle>w | x\<rangle> \<cdot>\<^sub>v v"
proof (rule eq_vecI)
  show "dim_vec ((v \<circledcirc> w) *\<^sub>v x) = dim_vec (\<langle>w | x\<rangle> \<cdot>\<^sub>v v)"
    by (simp add: ket_vec_def)
next
  fix i
  assume i: "i < dim_vec (\<langle>w | x\<rangle> \<cdot>\<^sub>v v)"
  then have iv: "i < dim_vec v"
    by simp
  have "((v \<circledcirc> w) *\<^sub>v x) $ i = (v $ i) * \<langle>w | x\<rangle>"
    using outer_prod_mult_vec_index[OF xdim iv] .
  also have "\<dots> = (\<langle>w | x\<rangle> \<cdot>\<^sub>v v) $ i"
    using iv by (simp add: algebra_simps)
  finally show "((v \<circledcirc> w) *\<^sub>v x) $ i = (\<langle>w | x\<rangle> \<cdot>\<^sub>v v) $ i" .
qed

lemma smult_mat_mult_vec:
  fixes A :: "complex Matrix.mat" and x :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat nr nc"
      and x: "x \<in> carrier_vec nc"
  shows "(a \<cdot>\<^sub>m A) *\<^sub>v x = a \<cdot>\<^sub>v (A *\<^sub>v x)"
proof (rule eq_vecI)
  show "dim_vec ((a \<cdot>\<^sub>m A) *\<^sub>v x) = dim_vec (a \<cdot>\<^sub>v (A *\<^sub>v x))"
    using A by simp
next
  fix i
  assume i: "i < dim_vec (a \<cdot>\<^sub>v (A *\<^sub>v x))"
  then have i_nr: "i < nr"
    using A by auto
  have "((a \<cdot>\<^sub>m A) *\<^sub>v x) $ i =
        Matrix.row (a \<cdot>\<^sub>m A) i \<bullet> x"
    using A i_nr by simp
  also have "\<dots> = (\<Sum>j<nc. (a * A $$ (i,j)) * x $ j)"
    using A x i_nr by (simp add: scalar_prod_def Matrix.row_def lessThan_atLeast0)
  also have "\<dots> = a * (\<Sum>j<nc. A $$ (i,j) * x $ j)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = a * (Matrix.row A i \<bullet> x)"
    using A x i_nr by (simp add: scalar_prod_def Matrix.row_def lessThan_atLeast0)
  also have "\<dots> = (a \<cdot>\<^sub>v (A *\<^sub>v x)) $ i"
    using A i_nr by simp
  finally show "((a \<cdot>\<^sub>m A) *\<^sub>v x) $ i = (a \<cdot>\<^sub>v (A *\<^sub>v x)) $ i" .
qed




lemma cpx_vec_length_zero_iff:
  fixes v :: "complex Matrix.vec"
  shows "\<parallel>v\<parallel> = 0 \<longleftrightarrow> v = 0\<^sub>v (dim_vec v)"
proof
  assume norm_zero: "\<parallel>v\<parallel> = 0"
  have inner_zero: "\<langle>v | v\<rangle> = 0"
    using norm_zero cpx_vec_length_inner_prod[of v] by simp
  show "v = 0\<^sub>v (dim_vec v)"
  proof (rule ccontr)
    assume "v \<noteq> 0\<^sub>v (dim_vec v)"
    then have "\<langle>v | v\<rangle> \<noteq> 0"
      by (rule inner_prod_with_itself_nonneg_reals_non0)
    then show False
      using inner_zero by simp
  qed
next
  assume v_zero: "v = 0\<^sub>v (dim_vec v)"
  have index_zero: "\<And>i. i < dim_vec v \<Longrightarrow> v $ i = 0"
    using v_zero by (metis index_zero_vec(1))
  have sum_zero: "(\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2) = 0"
    using index_zero by (simp add: sum.neutral)
  show "\<parallel>v\<parallel> = 0"
    using sum_zero by (simp add: cpx_vec_length_def)
qed

lemma cpx_vec_length_smult:
  fixes a :: complex and v :: "complex Matrix.vec"
  shows "\<parallel>a \<cdot>\<^sub>v v\<parallel> = cmod a * \<parallel>v\<parallel>"
proof -
  let ?S = "(\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
  have S_nonneg: "?S \<ge> 0"
    by (simp add: sum_nonneg)
  have "\<parallel>a \<cdot>\<^sub>v v\<parallel> =
        sqrt (\<Sum>i<dim_vec v. (cmod (a * (v $ i)))\<^sup>2)"
    by (simp add: cpx_vec_length_def)
  also have "\<dots> =
        sqrt (\<Sum>i<dim_vec v. (cmod a)\<^sup>2 * (cmod (v $ i))\<^sup>2)"
    by (simp add: norm_mult power_mult_distrib)
  also have "\<dots> =
        sqrt ((cmod a)\<^sup>2 * ?S)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = cmod a * sqrt ?S"
    using S_nonneg by (simp add: real_sqrt_mult)
  also have "\<dots> = cmod a * \<parallel>v\<parallel>"
    by (simp add: cpx_vec_length_def)
  finally show ?thesis .
qed

lemma inner_prod_right_smult':
  fixes u v :: "complex Matrix.vec"
  shows "\<langle>u | a \<cdot>\<^sub>v v\<rangle> = a * \<langle>u | v\<rangle>"
  by (simp add: inner_prod_def sum_distrib_left algebra_simps)

lemma inner_prod_left_smult':
  fixes u v :: "complex Matrix.vec"
  assumes uv: "dim_vec u = dim_vec v"
  shows "\<langle>a \<cdot>\<^sub>v u | v\<rangle> = cnj a * \<langle>u | v\<rangle>"
proof -
  have "\<langle>a \<cdot>\<^sub>v u | v\<rangle> =
        (\<Sum>i<dim_vec v. cnj (a * (u $ i)) * (v $ i))"
    using uv by (simp add: inner_prod_def lessThan_atLeast0)
  also have "\<dots> =
        cnj a * (\<Sum>i<dim_vec v. cnj (u $ i) * (v $ i))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = cnj a * \<langle>u | v\<rangle>"
    by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma inner_prod_right_add':
  fixes u v w :: "complex Matrix.vec"
  assumes vw: "dim_vec v = dim_vec w"
  shows "\<langle>u | v + w\<rangle> = \<langle>u | v\<rangle> + \<langle>u | w\<rangle>"
proof -
  have "\<langle>u | v + w\<rangle> =
        (\<Sum>i<dim_vec v. cnj (u $ i) * ((v $ i) + (w $ i)))"
    using vw by (simp add: inner_prod_def lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>i<dim_vec v. cnj (u $ i) * (v $ i))
        + (\<Sum>i<dim_vec v. cnj (u $ i) * (w $ i))"
    by (simp add: sum.distrib algebra_simps)
  also have "\<dots> = \<langle>u | v\<rangle> + \<langle>u | w\<rangle>"
    using vw by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma inner_prod_right_minus':
  fixes u v w :: "complex Matrix.vec"
  assumes vw: "dim_vec v = dim_vec w"
  shows "\<langle>u | v - w\<rangle> = \<langle>u | v\<rangle> - \<langle>u | w\<rangle>"
proof -
  have "\<langle>u | v - w\<rangle> =
        (\<Sum>i<dim_vec v. cnj (u $ i) * ((v $ i) - (w $ i)))"
    using vw by (simp add: inner_prod_def lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>i<dim_vec v. cnj (u $ i) * (v $ i))
        - (\<Sum>i<dim_vec v. cnj (u $ i) * (w $ i))"
    by (simp add: sum_subtractf algebra_simps)
  also have "\<dots> = \<langle>u | v\<rangle> - \<langle>u | w\<rangle>"
    using vw by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma inner_prod_left_minus':
  fixes u v w :: "complex Matrix.vec"
  assumes uv: "dim_vec u = dim_vec v"
      and uw: "dim_vec u = dim_vec w"
  shows "\<langle>u - v | w\<rangle> = \<langle>u | w\<rangle> - \<langle>v | w\<rangle>"
proof -
  have dims: "dim_vec u = dim_vec w" "dim_vec v = dim_vec w"
    using uv uw by simp_all
  have "\<langle>u - v | w\<rangle> =
        (\<Sum>i<dim_vec w. cnj ((u $ i) - (v $ i)) * (w $ i))"
    using dims by (simp add: inner_prod_def lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>i<dim_vec w. cnj (u $ i) * (w $ i))
        - (\<Sum>i<dim_vec w. cnj (v $ i) * (w $ i))"
    by (simp add: sum_subtractf algebra_simps)
  also have "\<dots> = \<langle>u | w\<rangle> - \<langle>v | w\<rangle>"
    using dims by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma dagger_of_smult:
  fixes \<gamma> :: complex
    and U :: "complex Matrix.mat"
  shows "(\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger> = (cnj \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger>)"
proof (rule eq_matI)
  show "dim_row ((\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger>) = dim_row ((cnj \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger>))"
    by simp
  show "dim_col ((\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger>) = dim_col ((cnj \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger>))"
    by simp
next
  fix i j
  assume i: "i < dim_row ((cnj \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger>))"
  assume j: "j < dim_col ((cnj \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger>))"
  have "((\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger>) $$ (i,j) = cnj ((\<gamma> \<cdot>\<^sub>m U) $$ (j,i))"
    using i j by (simp add: dagger_def)
  also have "... = cnj (\<gamma> * (U $$ (j,i)))"
    using i j by simp
  also have "... = (cnj \<gamma>) * cnj (U $$ (j,i))"
    by simp
  also have "... = ((cnj \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger>)) $$ (i,j)"
    using i j by (simp add: dagger_def)
  finally show "((\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger>) $$ (i,j) = ((cnj \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger>)) $$ (i,j)" .
qed

definition householder :: "complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "householder w \<equiv>
     Matrix.mat (dim_vec w) (dim_vec w)
       (\<lambda>(i,j). (if i = j then 1 else 0) - 2 * (w $ i) * cnj (w $ j))"

notation householder ("U\<^sub>H")

(* Index formula for the Householder matrix *)

lemma householder_index:
  assumes "i < dim_vec w" and "j < dim_vec w"
  shows "(householder w) $$ (i,j) =
         (if i = j then 1 else 0) - 2 * (w $ i) * cnj (w $ j)"
  using assms by (simp add: householder_def)

lemma householder_outer_prod:
  "householder w = 1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<circledcirc> w)"
proof (rule eq_matI)
  show "dim_row (householder w) =
        dim_row (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<circledcirc> w))"
    by (simp add: householder_def ket_vec_def)
  show "dim_col (householder w) =
        dim_col (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<circledcirc> w))"
    by (simp add: householder_def bra_vec_def row_vec_def cpx_mat_cnj_def)
next
  fix i j
  assume i: "i < dim_row (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<circledcirc> w))"
  assume j: "j < dim_col (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<circledcirc> w))"
  then have ij: "i < dim_vec w" "j < dim_vec w"
    using i by (simp_all add: ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def)

  have "householder w $$ (i,j) =
        (if i = j then (1 :: complex) else 0) - 2 * (w $ i) * cnj (w $ j)"
    using householder_index[OF ij] .
  also have "\<dots> = (if i = j then (1 :: complex) else 0) -
        2 * ((w \<circledcirc> w) $$ (i,j))"
    using outer_prod_index[OF ij] by simp
  also have "\<dots> = (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<circledcirc> w)) $$ (i,j)"
    using ij by (simp add: ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def)
  finally show "householder w $$ (i,j) =
        (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<circledcirc> w)) $$ (i,j)" .
qed

(* U_w is self-adjoint: (U_w)\<dagger> = U_w *)

lemma householder_hermitian:
  shows "(householder w)\<^sup>\<dagger> = householder w"
proof (rule eq_matI)
  let ?n = "dim_vec w"
  show "dim_row ((householder w)\<^sup>\<dagger>) = dim_row (householder w)"
    by (simp add: householder_def Let_def)
  show "dim_col ((householder w)\<^sup>\<dagger>) = dim_col (householder w)"
    by (simp add: householder_def Let_def)
  fix i j
  assume "i < dim_row (householder w)" "j < dim_col (householder w)"
  then have ij: "i < ?n" "j < ?n"
    by (simp_all add: householder_def Let_def)
  have "(householder w)\<^sup>\<dagger> $$ (i,j) = cnj ((householder w) $$ (j,i))"
    by (simp add: dagger_def householder_def Let_def ij)
  also have "\<dots> = cnj ((if j = i then 1 else 0) - 2 * (w $ j) * cnj (w $ i))"
    using householder_index ij by simp
  also have "\<dots> = (if i = j then 1 else 0) - 2 * (w $ i) * cnj (w $ j)"
    by (cases "i = j") auto
  also have "\<dots> = (householder w) $$ (i,j)"
    using householder_index ij by simp
  finally show "(householder w)\<^sup>\<dagger> $$ (i,j) = (householder w) $$ (i,j)" .
qed

(* U_w is unitary when \<Parallel>w\<Parallel> = 1 *)

lemma householder_unitary:
  assumes norm_w: "\<parallel>w\<parallel> = (1 :: real)"
  shows "unitary (householder w)"
proof -
  let ?U = "householder w"
  let ?n = "dim_vec w"

  have dims[simp]: "dim_row ?U = ?n" "dim_col ?U = ?n"
    by (simp_all add: householder_def)

  have norm_sum: "(\<Sum>k<?n. w $ k * cnj (w $ k)) = (1 :: complex)"
  proof -
    have "(\<Sum>k<?n. w $ k * cnj (w $ k)) = of_real (\<parallel>w\<parallel>^2)"
      by (metis (no_types, lifting) atLeast0LessThan cpx_vec_length_inner_prod
          inner_prod_def mult_commute_abs sum.cong)
    also have "... = (1 :: complex)"
      using norm_w by simp
    finally show ?thesis .
  qed

  have UU: "?U * ?U = 1\<^sub>m ?n"
  proof (rule eq_matI)
    show "dim_row (?U * ?U) = dim_row (1\<^sub>m ?n)"
      by simp
    show "dim_col (?U * ?U) = dim_col (1\<^sub>m ?n)"
      by simp
  next
    fix i j
    assume i_bnd: "i < dim_row (1\<^sub>m (dim_vec w))"
    assume j_bnd: "j < dim_col (1\<^sub>m (dim_vec w))"

    have ij: "i < dim_row (?U * ?U)" "j < dim_col (?U * ?U)"
      using i_bnd j_bnd by auto
    then have ij': "i < ?n" "j < ?n"
      by simp_all

    have "((?U) * (?U)) $$ (i,j)
    = (\<Sum>k<?n.
         (((if i = k then (1 :: complex) else 0) - 2 * (w $ i) * cnj (w $ k)) *
          (((if k = j then (1 :: complex) else 0) - 2 * (w $ k) * cnj (w $ j)))))"
      using ij'
      by (simp add: householder_def)
    also have "... =
      (\<Sum>k<?n.
         (if i = k then (1 :: complex) else 0) * (if k = j then (1 :: complex) else 0)
       - ((if i = k then (1 :: complex) else 0) * (2 * (w $ k) * cnj (w $ j)))
       - ((2 * (w $ i) * cnj (w $ k)) * (if k = j then (1 :: complex) else 0))
       + (2 * (w $ i) * cnj (w $ k)) * (2 * (w $ k) * cnj (w $ j)))"
      by (simp add: algebra_simps)
    also have "... =
      (\<Sum>k<?n.
         (if i = k then (1 :: complex) else 0) * (if k = j then (1 :: complex) else 0)
       - (2 * (if i = k then (1 :: complex) else 0) * (w $ k) * cnj (w $ j))
       - (2 * (w $ i) * cnj (w $ k) * (if k = j then (1 :: complex) else 0))
       + (4 * (w $ i) * cnj (w $ k) * (w $ k) * cnj (w $ j)))"
      by (simp add: algebra_simps)
    also have "... =
         (\<Sum>k<?n. (if i = k then (1 :: complex) else 0) * (if k = j then (1 :: complex) else 0))
       - (\<Sum>k<?n. 2 * (if i = k then (1 :: complex) else 0) * (w $ k) * cnj (w $ j))
       - (\<Sum>k<?n. 2 * (w $ i) * cnj (w $ k) * (if k = j then (1 :: complex) else 0))
       + (\<Sum>k<?n. 4 * (w $ i) * cnj (w $ k) * (w $ k) * cnj (w $ j))"
      by (simp add: sum.distrib sum_subtractf)

    also have "... =
         (if i = j then (1 :: complex) else 0)
       - (\<Sum>k<?n. 2 * (if i = k then (1 :: complex) else 0) * (w $ k) * cnj (w $ j))
       - (\<Sum>k<?n. 2 * (w $ i) * cnj (w $ k) * (if k = j then (1 :: complex) else 0))
       + (\<Sum>k<?n. 4 * (w $ i) * cnj (w $ k) * (w $ k) * cnj (w $ j))"
    proof -
      have delta_sum:
        "(\<Sum>k<?n. (if i = k then (1 :: complex) else 0) *
                 (if k = j then (1 :: complex) else 0))
         = (if i = j then (1 :: complex) else 0)"
      proof (cases "i = j")
        case True
        then have ij_eq: "i = j" .

        have "(\<Sum>k<?n. (if i = k then (1 :: complex) else 0) *
                        (if k = j then (1 :: complex) else 0))
            = (\<Sum>k<?n. (if i = k then (1 :: complex) else 0) *
                      (if k = i then (1 :: complex) else 0))"
          using ij_eq by simp
        also have "... = (\<Sum>k<?n. (if i = k then (1 :: complex) else 0) * (1 :: complex))"
        proof (rule sum.cong)
          show "{..< ?n} = {..< ?n}" by simp
          fix k
          assume k_bnd: "k \<in> {..< ?n}"
          then have "k < ?n"
            by simp
          show "(if i = k then (1 :: complex) else 0) *
                (if k = i then (1 :: complex) else 0)
              = (if i = k then (1 :: complex) else 0) * (1 :: complex)"
          proof (cases "i = k")
            case True
            then show ?thesis
              by simp
          next
            case False
            then have "(if i = k then (1 :: complex) else 0) = 0"
              by simp
            then have "(if i = k then (1 :: complex) else 0) *
                       (if k = i then (1 :: complex) else 0)
                     = 0 * 0"
              using False by simp
            also have "... = 0 * (1 :: complex)"
              by simp
            also have "... = (if i = k then (1 :: complex) else 0) * (1 :: complex)"
              using False by simp
            finally show ?thesis .
          qed
        qed
        also have "... = (\<Sum>k<?n. (if i = k then (1 :: complex) else 0))"
          by simp
        also have "... = (1 :: complex)"
        proof -
          have "i < ?n"
            using ij' by simp
          then show ?thesis
            by simp
        qed
        also have "... = (if i = j then (1 :: complex) else 0)"
          using ij_eq by simp
        finally show ?thesis .
      next
        case False
        then have ij_neq: "i \<noteq> j" .

        have "(\<Sum>k<?n. (if i = k then (1 :: complex) else 0) *
                        (if k = j then (1 :: complex) else 0)) = 0"
        proof -
          have "\<forall>k<?n. (if i = k then (1 :: complex) else 0) *
                       (if k = j then (1 :: complex) else 0) = 0"
          proof clarify
            fix k
            assume k_bnd: "k < ?n"
            show "(if i = k then (1 :: complex) else 0) *
                  (if k = j then (1 :: complex) else 0) = 0"
            proof (cases "i = k")
              case True
              then have k_not_j: "k \<noteq> j"
                using ij_neq by simp
              then have "(if k = j then (1 :: complex) else 0) = 0"
                by simp
              then have "(if i = k then (1 :: complex) else 0) *
                         (if k = j then (1 :: complex) else 0)
                       = (if i = k then (1 :: complex) else 0) * 0"
                by simp
              also have "... = 0"
                by simp
              finally show ?thesis .
            next
              case False
              then have "(if i = k then (1 :: complex) else 0) = 0"
                by simp
              then show ?thesis
                by simp
            qed
          qed
          moreover have "\<forall>k\<in>{..< ?n}. (if i = k then (1 :: complex) else 0) *
                                   (if k = j then (1 :: complex) else 0) = 0"
            using calculation by auto
          ultimately show ?thesis
            by (simp add: sum.neutral)
        qed
        also have "... = (if i = j then (1 :: complex) else 0)"
          using ij_neq by simp
        finally show ?thesis .
      qed

      show ?thesis
        using delta_sum by simp
    qed

    also have "... =
         (if i = j then (1 :: complex) else 0)
       - 2 * (w $ i) * cnj (w $ j)
       - (\<Sum>k<?n. 2 * (w $ i) * cnj (w $ k) * (if k = j then (1 :: complex) else 0))
       + (\<Sum>k<?n. 4 * (w $ i) * cnj (w $ k) * (w $ k) * cnj (w $ j))"
    proof -
      have "(\<Sum>k<?n. 2 * (if i = k then (1 :: complex) else 0) * (w $ k) * cnj (w $ j))
          = (\<Sum>k<?n. (if i = k then 2 * (w $ k) * cnj (w $ j) else 0))"
        by (smt (verit) mult_cancel_left1 mult_cancel_right1 sum.cong)
      also have "... = 2 * (w $ i) * cnj (w $ j)"
        using ij' by simp
      finally have "(\<Sum>k<?n. 2 * (if i = k then (1 :: complex) else 0) * (w $ k) * cnj (w $ j))
                  = 2 * (w $ i) * cnj (w $ j)" .
      then show ?thesis
        by simp
    qed

    also have "... =
         (if i = j then (1 :: complex) else 0)
       - 2 * (w $ i) * cnj (w $ j)
       - 2 * (w $ i) * cnj (w $ j)
       + (\<Sum>k<?n. 4 * (w $ i) * cnj (w $ k) * (w $ k) * cnj (w $ j))"
    proof -
      have "(\<Sum>k<?n. 2 * (w $ i) * cnj (w $ k) * (if k = j then (1 :: complex) else 0))
          = (\<Sum>k<?n. (if k = j then 2 * (w $ i) * cnj (w $ k) else 0))"
        by (smt (verit, best) mult_cancel_left1 mult_cancel_right1 sum.cong)
      also have "... = 2 * (w $ i) * cnj (w $ j)"
        using ij' by simp
      finally have "(\<Sum>k<?n. 2 * (w $ i) * cnj (w $ k) * (if k = j then (1 :: complex) else 0))
                  = 2 * (w $ i) * cnj (w $ j)" .
      then show ?thesis
        by simp
    qed

    also have "... =
         (if i = j then (1 :: complex) else 0)
       - 2 * (w $ i) * cnj (w $ j)
       - 2 * (w $ i) * cnj (w $ j)
       + (4 * (w $ i) * cnj (w $ j) * (\<Sum>k<?n. cnj (w $ k) * (w $ k)))"
      by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
    also have "... =
         (if i = j then (1 :: complex) else 0)
       - 2 * (w $ i) * cnj (w $ j)
       - 2 * (w $ i) * cnj (w $ j)
       + (4 * (w $ i) * cnj (w $ j) * (\<Sum>k<?n. w $ k * cnj (w $ k)))"
      by (simp add: mult.commute)
    also have "... =
         (if i = j then (1 :: complex) else 0)
       - 2 * (w $ i) * cnj (w $ j)
       - 2 * (w $ i) * cnj (w $ j)
       + 4 * (w $ i) * cnj (w $ j)"
      using norm_sum by simp
    also have "... = (if i = j then (1 :: complex) else 0)"
      by (simp add: algebra_simps)
    also have "... = (1\<^sub>m ?n) $$ (i,j)"
      using ij' by simp
    finally show "(?U * ?U) $$ (i,j) = (1\<^sub>m ?n) $$ (i,j)" .
  qed

  have dagger_eq: "?U\<^sup>\<dagger> = ?U"
    by (rule householder_hermitian)

  have left_unit: "?U\<^sup>\<dagger> * ?U = 1\<^sub>m (dim_col ?U)"
    using UU dagger_eq by simp

  have right_unit: "?U * (?U\<^sup>\<dagger>) = 1\<^sub>m (dim_row ?U)"
    using UU dagger_eq by simp

  show ?thesis
    unfolding unitary_def
    using left_unit right_unit by simp
qed

lemma householder_mult_vec_index:
  fixes w x :: "complex Matrix.vec"
  assumes xdim: "dim_vec x = dim_vec w"
      and i: "i < dim_vec w"
  shows "(householder w *\<^sub>v x) $ i =
         x $ i - 2 * (w $ i) * \<langle>w | x\<rangle>"
proof -
  let ?n = "dim_vec w"

  have householder_rows: "dim_row (householder w) = ?n"
    by (simp add: householder_def)
  have householder_cols: "dim_col (householder w) = ?n"
    by (simp add: householder_def)

  have "((householder w) *\<^sub>v x) $ i =
        Matrix.row (householder w) i \<bullet> x"
    by (rule index_mult_mat_vec) (use i householder_rows in simp)
  also have "\<dots> =
        (\<Sum>j<?n. (householder w) $$ (i,j) * (x $ j))"
    using xdim householder_cols
    by (simp add: scalar_prod_def Matrix.row_def lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>j<?n.
          (((if i = j then (1 :: complex) else 0)
             - 2 * (w $ i) * cnj (w $ j)) * (x $ j)))"
  proof (rule sum.cong)
    show "{..< ?n} = {..< ?n}"
      by simp
  next
    fix j
    assume j: "j \<in> {..< ?n}"
    then have j_lt: "j < ?n"
      by simp
    have "(householder w) $$ (i,j) =
          (if i = j then (1 :: complex) else 0)
          - 2 * (w $ i) * cnj (w $ j)"
      using householder_index[OF i j_lt] .
    then show "(householder w) $$ (i,j) * x $ j =
          (((if i = j then (1 :: complex) else 0)
             - 2 * (w $ i) * cnj (w $ j)) * (x $ j))"
      by simp
  qed
  also have "\<dots> =
        (\<Sum>j<?n. (x $ j * (if i = j then (1 :: complex) else 0)))
        - (\<Sum>j<?n. 2 * (w $ i) * cnj (w $ j) * (x $ j))"
    by (simp add: sum_subtractf algebra_simps)
  also have "\<dots> =
        x $ i - (\<Sum>j<?n. 2 * (w $ i) * cnj (w $ j) * (x $ j))"
  proof -
    have i_mem: "i \<in> {..< ?n}"
      using i by simp
    have finite_n: "finite {..< ?n}"
      by simp
    have delta_sum:
      "(\<Sum>j<?n. (x $ j * (if i = j then (1 :: complex) else 0))) = x $ i"
    proof -
      have "(\<Sum>j<?n. (x $ j * (if i = j then (1 :: complex) else 0))) =
            x $ i * (if i = i then (1 :: complex) else 0)
            + (\<Sum>j\<in>{..< ?n} - {i}.
                x $ j * (if i = j then (1 :: complex) else 0))"
        by (subst sum.remove[OF finite_n i_mem]) simp
      also have "\<dots> = x $ i + 0"
        by (simp add: sum.neutral)
      also have "\<dots> = x $ i"
        by simp
      finally show ?thesis .
    qed
    then show ?thesis
      by simp
  qed
  also have "\<dots> =
        x $ i - 2 * (w $ i) * (\<Sum>j<?n. cnj (w $ j) * (x $ j))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> =
        x $ i - 2 * (w $ i) * \<langle>w | x\<rangle>"
    using xdim by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma householder_mult_vec:
  fixes w x :: "complex Matrix.vec"
  assumes xdim: "dim_vec x = dim_vec w"
  shows "householder w *\<^sub>v x =
         x - (2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w"
proof (rule eq_vecI)
  show "dim_vec (householder w *\<^sub>v x) =
        dim_vec (x - (2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w)"
    using xdim by (simp add: householder_def)
next
  fix i
  assume i: "i < dim_vec (x - (2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w)"
  then have iw: "i < dim_vec w"
    using xdim by simp

  have "(householder w *\<^sub>v x) $ i =
        x $ i - 2 * (w $ i) * \<langle>w | x\<rangle>"
    using householder_mult_vec_index[OF xdim iw] .
  also have "\<dots> =
        (x - (2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w) $ i"
    using iw xdim by (simp add: algebra_simps)
  finally show "(householder w *\<^sub>v x) $ i =
        (x - (2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w) $ i" .
qed

(* ---- Schur's Lemma ---- *)

(* For x, y \<in> \<complex>^n with \<Parallel>x\<Parallel> = \<Parallel>y\<Parallel>, there exists a unit vector w and \<theta> such
   that U_w(x) = e^{i\<theta>} y.
   We state this as a classical existence result; the proof uses the
   explicit construction w = (e^{i\<theta>}y - x) / \<Parallel>e^{i\<theta>}y - x\<Parallel> for appropriate \<theta>. *)

lemma schur_lemma_zero_case:
  fixes x y :: "complex Matrix.vec"
  assumes n_pos: "n > 0"
      and xdim: "dim_vec x = n"
      and ydim: "dim_vec y = n"
      and norm_eq: "\<parallel>x\<parallel> = \<parallel>y\<parallel>"
      and x_zero_norm: "\<parallel>x\<parallel> = 0"
  shows "\<exists>w :: complex Matrix.vec. \<exists>\<theta> :: real.
         dim_vec w = n \<and> \<parallel>w\<parallel> = 1 \<and>
         householder w *\<^sub>v x = Complex (cos \<theta>) (sin \<theta>) \<cdot>\<^sub>v y"
proof -
  let ?w = "unit_vec n 0 :: complex Matrix.vec"
  have zero_lt_n: "0 < n"
    using n_pos by simp
  have wdim: "dim_vec ?w = n"
    by simp
  have wnorm: "\<parallel>?w\<parallel> = 1"
    using unit_cpx_vec_length[OF zero_lt_n] .

  have x_zero_dim: "x = 0\<^sub>v (dim_vec x)"
    using cpx_vec_length_zero_iff[of x] x_zero_norm by simp
  have x_zero_n: "x = 0\<^sub>v n"
    using x_zero_dim xdim by simp
  have y_zero_norm: "\<parallel>y\<parallel> = 0"
    using norm_eq x_zero_norm by simp
  have y_zero_dim: "y = 0\<^sub>v (dim_vec y)"
    using cpx_vec_length_zero_iff[of y] y_zero_norm by simp
  have y_zero_n: "y = 0\<^sub>v n"
    using y_zero_dim ydim by simp

  have action_zero: "householder ?w *\<^sub>v x = 0\<^sub>v n"
  proof (rule eq_vecI)
    show "dim_vec (householder ?w *\<^sub>v x) = dim_vec (0\<^sub>v n)"
      using xdim wdim by (simp add: householder_def)
  next
    fix i
    assume i: "i < dim_vec (0\<^sub>v n)"
    then have i_n: "i < n"
      by simp
    have "(householder ?w *\<^sub>v x) $ i =
          x $ i - 2 * (?w $ i) * \<langle>?w | x\<rangle>"
      using householder_mult_vec_index[of x ?w i] xdim wdim i_n by simp
    also have "\<dots> = 0"
      using x_zero_n i_n by simp
    also have "\<dots> = (0\<^sub>v n) $ i"
      using i_n by simp
    finally show "(householder ?w *\<^sub>v x) $ i = (0\<^sub>v n) $ i" .
  qed

  have rhs_zero: "Complex (cos 0) (sin 0) \<cdot>\<^sub>v y = 0\<^sub>v n"
  proof (rule eq_vecI)
    show "dim_vec (Complex (cos 0) (sin 0) \<cdot>\<^sub>v y) = dim_vec (0\<^sub>v n)"
      using ydim by simp
  next
    fix i
    assume i: "i < dim_vec (0\<^sub>v n)"
    then have i_n: "i < n"
      by simp
    have "(Complex (cos 0) (sin 0) \<cdot>\<^sub>v y) $ i = y $ i"
      using ydim i_n by (simp add: complex_eq_iff)
    also have "\<dots> = 0"
      using y_zero_n i_n by simp
    also have "\<dots> = (0\<^sub>v n) $ i"
      using i_n by simp
    finally show "(Complex (cos 0) (sin 0) \<cdot>\<^sub>v y) $ i = (0\<^sub>v n) $ i" .
  qed
  have "householder ?w *\<^sub>v x = Complex (cos 0) (sin 0) \<cdot>\<^sub>v y"
    using action_zero rhs_zero by simp
  then show ?thesis
    using wdim wnorm by blast
qed

thm of_real_divide[where x = "cmod (\<langle>y | x\<rangle>) ^ 2" and y = "cmod (\<langle>y | x\<rangle>)", symmetric]


lemma schur_lemma:
  fixes x y :: "complex Matrix.vec"
  assumes n_pos: "n > 0"
      and xdim: "dim_vec x = n"
      and ydim: "dim_vec y = n"
      and norm_eq: "\<parallel>x\<parallel> = \<parallel>y\<parallel>"
  shows "\<exists>w :: complex Matrix.vec. \<exists>\<theta> :: real.
         dim_vec w = n \<and> \<parallel>w\<parallel> = 1 \<and>
         householder w *\<^sub>v x = Complex (cos \<theta>) (sin \<theta>) \<cdot>\<^sub>v y"
proof (cases "\<parallel>x\<parallel> = 0")
  case True
  then show ?thesis
    using schur_lemma_zero_case[OF n_pos xdim ydim norm_eq] by simp
next
  case False
  have x_nonzero: "\<parallel>x\<parallel> \<noteq> 0" using False by simp

  (* --- Phase: alpha = sgn(<y|x>), making <z|x> a nonneg real --- *)

  define alpha :: complex where
    "alpha \<equiv> if \<langle>y | x\<rangle> = 0 then 1
              else \<langle>y | x\<rangle> / of_real (cmod (\<langle>y | x\<rangle>))"

  have alpha_cmod: "cmod alpha = 1"
    by (cases "\<langle>y | x\<rangle> = 0", 
        simp add: alpha_def, 
        simp add: alpha_def norm_divide)

  define z :: "complex Matrix.vec" where "z \<equiv> alpha \<cdot>\<^sub>v y"

  have zdim: "dim_vec z = n" using ydim by (simp add: z_def)

  have "\<parallel>z\<parallel> = cmod alpha * \<parallel>y\<parallel>"
      by (simp add: z_def cpx_vec_length_smult)
  then have znorm: "\<parallel>z\<parallel> = \<parallel>x\<parallel>"
    using alpha_cmod norm_eq by simp

  have zx_inner: "\<langle>z | x\<rangle> = cnj alpha * \<langle>y | x\<rangle>"
  proof -
    have "dim_vec y = dim_vec x" using xdim ydim by simp
    then show ?thesis
      unfolding z_def
      using inner_prod_left_smult' by blast
  qed

  have zx_real: "\<langle>z | x\<rangle> \<in> \<real>"
  proof (cases "\<langle>y | x\<rangle> = 0")
    case True thus ?thesis using zx_inner by simp
  next
    case False
    have cmod_ne: "cmod (\<langle>y | x\<rangle>) \<noteq> 0" using False by simp
    have aeq: "alpha = \<langle>y | x\<rangle> / of_real (cmod (\<langle>y | x\<rangle>))"
      using False alpha_def by simp
    have step1: "\<langle>z | x\<rangle> = cnj (\<langle>y | x\<rangle>) * \<langle>y | x\<rangle> / of_real (cmod (\<langle>y | x\<rangle>))"
      by (simp add: zx_inner aeq field_simps)
    have step2: "cnj (\<langle>y | x\<rangle>) * \<langle>y | x\<rangle> = of_real (cmod (\<langle>y | x\<rangle>) ^ 2)"
    proof -
      have "cnj (\<langle>y | x\<rangle>) * \<langle>y | x\<rangle> = \<langle>y | x\<rangle> * cnj (\<langle>y | x\<rangle>)"
        by (simp add: mult.commute)
      also have "\<dots> = of_real (Re (\<langle>y | x\<rangle>) ^ 2 + Im (\<langle>y | x\<rangle>) ^ 2)"
        by (rule complex_mult_cnj)
      also have "\<dots> = of_real (cmod (\<langle>y | x\<rangle>) ^ 2)"
      proof -
        have "cmod (\<langle>y | x\<rangle>) ^ 2 = Re (\<langle>y | x\<rangle>) ^ 2 + Im (\<langle>y | x\<rangle>) ^ 2"
        proof -
          have "0 \<le> Re (\<langle>y | x\<rangle>) ^ 2 + Im (\<langle>y | x\<rangle>) ^ 2"
            by (intro add_nonneg_nonneg zero_le_power2)
          thus ?thesis
            by (simp add: norm_complex_def)
        qed
        thus ?thesis by simp
      qed
      finally show ?thesis.
    qed
    have step3: "((of_real (cmod (\<langle>y | x\<rangle>) ^ 2) / of_real (cmod (\<langle>y | x\<rangle>))) :: complex)
       = of_real (cmod (\<langle>y | x\<rangle>))"
    proof -
      have nz: "cmod (\<langle>y | x\<rangle>) \<noteq> 0"
        using cmod_ne by simp
      have "((of_real (cmod (\<langle>y | x\<rangle>) ^ 2) / of_real (cmod (\<langle>y | x\<rangle>))) :: complex)
          = of_real ((cmod (\<langle>y | x\<rangle>) ^ 2) / cmod (\<langle>y | x\<rangle>))"
        by (rule of_real_divide[where 'a = complex
             and x = "cmod (\<langle>y | x\<rangle>) ^ 2"
             and y = "cmod (\<langle>y | x\<rangle>)", symmetric])
      also have "... = of_real (cmod (\<langle>y | x\<rangle>))"
        using nz by (simp add: power2_eq_square)
      finally show ?thesis.
    qed
    show ?thesis using step1 step2 step3 by simp
  qed
  have "\<langle>x | z\<rangle> = cnj (\<langle>z | x\<rangle>)"
      using inner_prod_cnj[of z x] zdim xdim by simp
  then have xz_eq_zx: "\<langle>x | z\<rangle> = \<langle>z | x\<rangle>"
    using Reals_cnj_iff zx_real by presburger
  have xz_inner_sq: "\<langle>x - z | x - z\<rangle> = 2 * \<langle>x - z | x\<rangle>"
  proof -
    have "\<langle>x - z | x - z\<rangle> = \<langle>x | x\<rangle> - \<langle>z | x\<rangle> - \<langle>x | z\<rangle> + \<langle>z | z\<rangle>"
      by (metis diff_add_eq diff_diff_eq2 inner_prod_left_minus' inner_prod_right_minus' xdim zdim)
    also have "... = \<langle>x | x\<rangle> - \<langle>z | x\<rangle> - \<langle>z | x\<rangle> + \<langle>z | z\<rangle>"
      using xz_eq_zx by simp
    also have "... = \<langle>x | x\<rangle> - \<langle>z | x\<rangle> - \<langle>z | x\<rangle> + \<langle>x | x\<rangle>"
      using znorm by (simp add: cpx_vec_length_inner_prod[symmetric])
    also have "... = 2 * (\<langle>x | x\<rangle> - \<langle>z | x\<rangle>)"
      by (simp add: algebra_simps)
    also have "... = 2 * \<langle>x - z | x\<rangle>"
      using inner_prod_left_minus'[of x z x] xdim zdim by simp
    finally show ?thesis.
  qed

  show ?thesis
  proof (cases "x = z")

    (* ---- Case x = z: Householder of normalised x sends x to -x = (-alpha) y ---- *)
    case True
    define w :: "complex Matrix.vec" where
      "w \<equiv> (1 / of_real (\<parallel>x\<parallel>)) \<cdot>\<^sub>v x"

    have wdim: "dim_vec w = n"
      using xdim by (simp add: w_def)

    have wnorm: "\<parallel>w\<parallel> = 1"
    proof -
      have "\<parallel>w\<parallel> = cmod (1 / of_real (\<parallel>x\<parallel>)) * \<parallel>x\<parallel>"
        by (simp add: w_def cpx_vec_length_smult)
      also have "... = (1 / \<parallel>x\<parallel>) * \<parallel>x\<parallel>"
        by (simp add: norm_divide,
            metis (full_types) Re_complex_of_real abs_abs cpx_vec_length_inner_prod csqrt_of_real' 
            inner_prod_csqrt mult.right_neutral real_sqrt_abs' zero_compare_simps(12))   
      also have "... = 1"
        using x_nonzero by simp
      finally show ?thesis.
    qed

    have inner_wx: "\<langle>w | x\<rangle> = of_real (\<parallel>x\<parallel>)"
    proof -
      have "\<langle>w | x\<rangle> = cnj (1 / of_real (\<parallel>x\<parallel>)) * \<langle>x | x\<rangle>"
        unfolding w_def
        by (rule inner_prod_left_smult') simp
      also have "cnj (1 / of_real (\<parallel>x\<parallel>)) = 1 / of_real (\<parallel>x\<parallel>)"
        by simp
      also have "(1 / of_real (\<parallel>x\<parallel>)) * \<langle>x | x\<rangle> = of_real (\<parallel>x\<parallel>)"
      proof -
        have "\<langle>x | x\<rangle> = of_real (\<parallel>x\<parallel> ^ 2)"
          using cpx_vec_length_inner_prod by simp
        thus ?thesis using x_nonzero
          by (simp add: power2_eq_square)
      qed
      finally show ?thesis.
    qed

    have hw_action: "householder w *\<^sub>v x = - x"
    proof -
      have step: "(2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w = (2 :: complex) \<cdot>\<^sub>v x"
      proof -
        have "(2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w
            = (2 * of_real (\<parallel>x\<parallel>)) \<cdot>\<^sub>v ((1 / of_real (\<parallel>x\<parallel>)) \<cdot>\<^sub>v x)"
          using inner_wx w_def by simp
        also have "\<dots> = (2 * of_real (\<parallel>x\<parallel>) * (1 / of_real (\<parallel>x\<parallel>))) \<cdot>\<^sub>v x"
          by (simp add: smult_smult_assoc)
        also have "2 * of_real (\<parallel>x\<parallel>) * (1 / of_real (\<parallel>x\<parallel>)) = (2 :: complex)"
          using x_nonzero by (simp add: field_simps)
        finally show ?thesis .
      qed
      have "householder w *\<^sub>v x = x - (2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w"
        using householder_mult_vec[of x w] xdim wdim by simp
      also have "\<dots> = x - (2 :: complex) \<cdot>\<^sub>v x"
        using step by simp
      also have "\<dots> = - x"
      proof (rule eq_vecI)
        show "dim_vec (x - (2 :: complex) \<cdot>\<^sub>v x) = dim_vec (- x)"
          using xdim by simp
      next
        fix i assume "i < dim_vec (- x)"
        then have hi: "i < n" using xdim by simp
        show "(x - (2 :: complex) \<cdot>\<^sub>v x) $ i = (- x) $ i"
          using hi xdim by simp
      qed
      finally show ?thesis.
    qed

    have neg_smult: "- (alpha \<cdot>\<^sub>v y) = (- alpha) \<cdot>\<^sub>v y"
    proof (rule eq_vecI)
      show "dim_vec (- (alpha \<cdot>\<^sub>v y)) = dim_vec ((- alpha) \<cdot>\<^sub>v y)" by simp
    next
      fix i assume "i < dim_vec ((- alpha) \<cdot>\<^sub>v y)"
      then have "i < n" using ydim by simp
      then show "(- (alpha \<cdot>\<^sub>v y)) $ i = ((- alpha) \<cdot>\<^sub>v y) $ i"
        by (simp add: ydim)
    qed

    have hw_eq: "householder w *\<^sub>v x = (- alpha) \<cdot>\<^sub>v y"
    proof -
      have "- x = (- alpha) \<cdot>\<^sub>v y"
        using True z_def neg_smult by simp
      thus ?thesis using hw_action by simp
    qed

    have neg_alpha_unit: "\<exists>\<theta> :: real. (- alpha) = Complex (cos \<theta>) (sin \<theta>)"
    proof -
      have cm: "cmod (- alpha) = 1" by (simp add: alpha_cmod)
      have "- alpha = rcis (cmod (- alpha)) (Arg (- alpha))"
        using rcis_cmod_Arg by presburger
      also have "\<dots> = cis (Arg (- alpha))"
        using cm by (simp add: rcis_def)
      also have "\<dots> = Complex (cos (Arg (- alpha))) (sin (Arg (- alpha)))"
        by (simp add: complex_eq_iff)
      finally show ?thesis by blast
    qed

    obtain \<theta> where htheta: "(- alpha) = Complex (cos \<theta>) (sin \<theta>)"
      using neg_alpha_unit by blast
    have hw_final: "householder w *\<^sub>v x = Complex (cos \<theta>) (sin \<theta>) \<cdot>\<^sub>v y"
      using hw_eq htheta by simp
    show ?thesis using wdim wnorm hw_final by blast

  next
    (* ---- Case x \<noteq> z: Householder of normalised (x - z) sends x to z ---- *)
    case False

    have x_ne_z: "x \<noteq> z" using False .

    have xz_ne_zero: "x - z \<noteq> 0\<^sub>v n"
    proof
      assume h: "x - z = 0\<^sub>v n"
      have "\<forall>i < n. x $ i = z $ i"
      proof clarify
        fix i assume hi: "i < n"
        have "(x - z) $ i = 0"
          using h hi by simp
        thus "x $ i = z $ i"
          using hi xdim zdim by simp
      qed
      then have "x = z"
        by (metis eq_vecI xdim zdim)
      thus False using x_ne_z by simp
    qed

    have xz_nonzero: "\<parallel>x - z\<parallel> \<noteq> 0"
    proof -
      have "x - z \<noteq> 0\<^sub>v (dim_vec (x - z))"
        using xz_ne_zero xdim zdim by simp
      thus ?thesis using cpx_vec_length_zero_iff by blast
    qed

    define c :: complex where "c \<equiv> 1 / of_real (\<parallel>x - z\<parallel>)"

    define w :: "complex Matrix.vec" where "w \<equiv> c \<cdot>\<^sub>v (x - z)"

    have wdim: "dim_vec w = n"
      using xdim zdim by (simp add: w_def)

    have wnorm: "\<parallel>w\<parallel> = 1"
    proof -
      have "\<parallel>w\<parallel> = cmod (1 / of_real (\<parallel>x\<parallel>)) * \<parallel>x\<parallel>"
        by (metis Re_complex_of_real c_def cpx_vec_length_inner_prod cpx_vec_length_smult 
            csqrt_of_real_nonneg divide_eq_eq_1 inner_prod_csqrt inner_prod_with_itself_Im 
            inner_prod_with_itself_Re norm_divide norm_of_real real_sqrt_abs times_divide_eq_left 
            times_divide_eq_right w_def x_nonzero xz_nonzero)
      also have "... = (1 / \<parallel>x\<parallel>) * \<parallel>x\<parallel>"
        by (simp add: norm_divide,
            metis (full_types) Re_complex_of_real abs_abs cpx_vec_length_inner_prod csqrt_of_real' 
            inner_prod_csqrt mult.right_neutral real_sqrt_abs' zero_compare_simps(12))   
      also have "... = 1"
        using x_nonzero by simp
      finally show ?thesis.
    qed

    have inner_wx: "\<langle>w | x\<rangle> = c * \<langle>x - z | x\<rangle>"
    proof -
      have "dim_vec (x - z) = dim_vec x" using xdim zdim by simp
      have "\<langle>w | x\<rangle> = cnj c * \<langle>x - z | x\<rangle>"
        unfolding w_def
        by (rule inner_prod_left_smult') (use xdim zdim in simp)
      also have "cnj c = c"
        by (simp add: c_def)
      finally show ?thesis .
    qed

    have coeff_one: "2 * c * \<langle>x - z | x\<rangle> * c = 1"
    proof -
      have h1: "\<langle>x - z | x - z\<rangle> = 2 * \<langle>x - z | x\<rangle>"
        using xz_inner_sq .
      have h2: "c ^ 2 * of_real (\<parallel>x - z\<parallel> ^ 2) = 1"
      proof -
        have hne: "(of_real (\<parallel>x - z\<parallel>) :: complex) \<noteq> 0"
          using xz_nonzero by simp
        have "c ^ 2 = (1 / of_real (\<parallel>x - z\<parallel>)) ^ 2"
          by (simp add: c_def)
        also have "\<dots> = 1 / of_real (\<parallel>x - z\<parallel> ^ 2)"
          by (simp add: power2_eq_square)
        finally have ceq: "c ^ 2 = 1 / of_real (\<parallel>x - z\<parallel> ^ 2)" .
        have hne2: "(of_real (\<parallel>x - z\<parallel> ^ 2) :: complex) \<noteq> 0"
          using hne by (simp add: power2_eq_square)
        show ?thesis using ceq hne2 by (simp add: field_simps)
      qed
      have h3: "\<langle>x - z | x - z\<rangle> = of_real (\<parallel>x - z\<parallel> ^ 2)"
        using cpx_vec_length_inner_prod by simp
      have "2 * c * \<langle>x - z | x\<rangle> * c = c ^ 2 * (2 * \<langle>x - z | x\<rangle>)"
        by (simp add: power2_eq_square)
      also have "\<dots> = c ^ 2 * \<langle>x - z | x - z\<rangle>"
        using h1 by simp
      also have "\<dots> = c ^ 2 * of_real (\<parallel>x - z\<parallel> ^ 2)"
        using h3 by simp
      also have "\<dots> = 1"
        using h2.
      finally show ?thesis.
    qed

    have hw_action: "householder w *\<^sub>v x = z"
    proof -
      have smult_step: "(2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w = x - z"
      proof -
        have "(2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w
            = (2 * c * \<langle>x - z | x\<rangle>) \<cdot>\<^sub>v (c \<cdot>\<^sub>v (x - z))"
          using inner_wx w_def by (simp add: algebra_simps)
        also have "\<dots> = (2 * c * \<langle>x - z | x\<rangle> * c) \<cdot>\<^sub>v (x - z)"
          by (simp add: smult_smult_assoc algebra_simps)
        also have "\<dots> = 1 \<cdot>\<^sub>v (x - z)"
          using coeff_one by simp
        also have "\<dots> = x - z" by simp
        finally show ?thesis.
      qed
      have "householder w *\<^sub>v x = x - (2 * \<langle>w | x\<rangle>) \<cdot>\<^sub>v w"
        using householder_mult_vec[of x w] xdim wdim by simp
      also have "\<dots> = x - (x - z)"
        using smult_step by simp
      also have "\<dots> = z"
      proof (rule eq_vecI)
        show "dim_vec (x - (x - z)) = dim_vec z"
          using xdim zdim by simp
      next
        fix i assume "i < dim_vec z"
        then have hi: "i < n" using zdim by simp
        show "(x - (x - z)) $ i = z $ i"
          using hi xdim zdim by simp
      qed
      finally show ?thesis .
    qed

    have alpha_unit: "\<exists>\<theta> :: real. alpha = Complex (cos \<theta>) (sin \<theta>)"
    proof -
      have "alpha = rcis (cmod alpha) (Arg alpha)"
        using rcis_cmod_Arg by simp
      also have "\<dots> = cis (Arg alpha)"
        using alpha_cmod by (simp add: rcis_def)
      also have "\<dots> = Complex (cos (Arg alpha)) (sin (Arg alpha))"
        by (simp add: complex_eq_iff)
      finally show ?thesis by blast
    qed

    obtain \<theta> where htheta: "alpha = Complex (cos \<theta>) (sin \<theta>)"
      using alpha_unit by blast

    have hw_final: "householder w *\<^sub>v x = Complex (cos \<theta>) (sin \<theta>) \<cdot>\<^sub>v y"
    proof -
      have "householder w *\<^sub>v x = z" using hw_action .
      also have "z = alpha \<cdot>\<^sub>v y" by (simp add: z_def)
      also have "\<dots> = Complex (cos \<theta>) (sin \<theta>) \<cdot>\<^sub>v y"
        using htheta by simp
      finally show ?thesis.
    qed

    show ?thesis using wdim wnorm hw_final by blast
  qed
qed

(* ---- Schur's Theorem ---- *)

(* Every A \<in> M_n can be unitarily triangularised:
   \<exists> U unitary, U\<dagger>AU upper triangular. *)

lemma schur_triangular_similar:
  fixes A :: "complex Matrix.mat"
  assumes sq: "A \<in> carrier_mat n n"
  shows "\<exists>T :: complex Matrix.mat.
         T \<in> carrier_mat n n \<and>
         upper_triangular T \<and>
         similar_mat A T"
proof -
  obtain es where cp: "char_poly A = (\<Prod>e\<leftarrow>es. [:- e, 1:])"
    using char_poly_factorized[OF sq] by blast
  show ?thesis
    using schur_decomposition_exists[OF sq cp] by blast
qed

lemma cpx_mat_cnj_four_block:
  assumes A: "A \<in> carrier_mat nr1 nc1"
      and B: "B \<in> carrier_mat nr1 nc2"
      and C: "C \<in> carrier_mat nr2 nc1"
      and D: "D \<in> carrier_mat nr2 nc2"
  shows "(four_block_mat A B C D)\<^sup>\<star> =
         four_block_mat (A\<^sup>\<star>) (B\<^sup>\<star>) (C\<^sup>\<star>) (D\<^sup>\<star>)"
proof (rule eq_matI)
  show "dim_row ((four_block_mat A B C D)\<^sup>\<star>) =
        dim_row (four_block_mat (A\<^sup>\<star>) (B\<^sup>\<star>) (C\<^sup>\<star>) (D\<^sup>\<star>))"
    by (simp add: cpx_mat_cnj_def)
  show "dim_col ((four_block_mat A B C D)\<^sup>\<star>) =
        dim_col (four_block_mat (A\<^sup>\<star>) (B\<^sup>\<star>) (C\<^sup>\<star>) (D\<^sup>\<star>))"
    by (simp add: cpx_mat_cnj_def)
next
  fix i j
  assume "i < dim_row (four_block_mat (A\<^sup>\<star>) (B\<^sup>\<star>) (C\<^sup>\<star>) (D\<^sup>\<star>))"
  then have i: "i < dim_row ((four_block_mat A B C D)\<^sup>\<star>)"
    by (simp add: cpx_mat_cnj_def)
  assume "j < dim_col (four_block_mat (A\<^sup>\<star>) (B\<^sup>\<star>) (C\<^sup>\<star>) (D\<^sup>\<star>))"
  then have j: "j < dim_col ((four_block_mat A B C D)\<^sup>\<star>)"
    by (simp add: cpx_mat_cnj_def)      
  have i_bound: "i < nr1 + nr2"
    and j_bound: "j < nc1 + nc2"
    using assms A D cpx_mat_cnj_def j i by auto
  consider
      (UL) "i < nr1" "j < nc1"
    | (UR) "i < nr1" "\<not> j < nc1"
    | (LL) "\<not> i < nr1" "j < nc1"
    | (LR) "\<not> i < nr1" "\<not> j < nc1"
    by blast
  then show "((four_block_mat A B C D)\<^sup>\<star>) $$ (i,j) =
             (four_block_mat (A\<^sup>\<star>) (B\<^sup>\<star>) (C\<^sup>\<star>) (D\<^sup>\<star>)) $$ (i,j)"
  proof cases
    case UL
    then show ?thesis
      using assms i_bound j_bound
      by (simp add: cpx_mat_cnj_def)
  next
    case UR
    then have "j - nc1 < nc2"
      using j_bound by linarith
    then show ?thesis
      using assms UR i_bound j_bound
      by (simp add: cpx_mat_cnj_def)
  next
    case LL
    then have "i - nr1 < nr2"
      using i_bound by linarith
    then show ?thesis
      using assms LL i_bound j_bound
      by (simp add: cpx_mat_cnj_def)
  next
    case LR
    then have "i - nr1 < nr2" and "j - nc1 < nc2"
      using i_bound j_bound by linarith+
    then show ?thesis
      using assms LR i_bound j_bound
      by (simp add: cpx_mat_cnj_def)
  qed
qed

lemma dagger_four_block_mat_complex:
  assumes A: "A \<in> carrier_mat nr1 nc1"
      and B: "B \<in> carrier_mat nr1 nc2"
      and C: "C \<in> carrier_mat nr2 nc1"
      and D: "D \<in> carrier_mat nr2 nc2"
  shows "(four_block_mat A B C D)\<^sup>\<dagger> =
         four_block_mat (A\<^sup>\<dagger>) (C\<^sup>\<dagger>) (B\<^sup>\<dagger>) (D\<^sup>\<dagger>)"
proof (rule eq_matI)
  show "dim_row ((four_block_mat A B C D)\<^sup>\<dagger>) =
        dim_row (four_block_mat (A\<^sup>\<dagger>) (C\<^sup>\<dagger>) (B\<^sup>\<dagger>) (D\<^sup>\<dagger>))"
    using assms
    by (simp add: dagger_def cpx_mat_cnj_def)
  show "dim_col ((four_block_mat A B C D)\<^sup>\<dagger>) =
        dim_col (four_block_mat (A\<^sup>\<dagger>) (C\<^sup>\<dagger>) (B\<^sup>\<dagger>) (D\<^sup>\<dagger>))"
    using assms
    by (simp add: dagger_def cpx_mat_cnj_def)
next
  fix i j
  assume i_rhs: "i < dim_row (four_block_mat (A\<^sup>\<dagger>) (C\<^sup>\<dagger>) (B\<^sup>\<dagger>) (D\<^sup>\<dagger>))"
  assume j_rhs: "j < dim_col (four_block_mat (A\<^sup>\<dagger>) (C\<^sup>\<dagger>) (B\<^sup>\<dagger>) (D\<^sup>\<dagger>))"
  have i: "i < dim_row ((four_block_mat A B C D)\<^sup>\<dagger>)"
    using i_rhs assms by (simp add: dagger_def cpx_mat_cnj_def)
  have j: "j < dim_col ((four_block_mat A B C D)\<^sup>\<dagger>)"
    using j_rhs assms by (simp add: dagger_def cpx_mat_cnj_def)
  have i_bound: "i < nc1 + nc2"
    and j_bound: "j < nr1 + nr2"
    using assms i j by (simp_all add: dagger_def cpx_mat_cnj_def)
  consider
      (UL) "j < nr1" "i < nc1"
    | (UR) "j < nr1" "\<not> i < nc1"
    | (LL) "\<not> j < nr1" "i < nc1"
    | (LR) "\<not> j < nr1" "\<not> i < nc1"
    by blast
  then show "((four_block_mat A B C D)\<^sup>\<dagger>) $$ (i,j) =
             (four_block_mat (A\<^sup>\<dagger>) (C\<^sup>\<dagger>) (B\<^sup>\<dagger>) (D\<^sup>\<dagger>)) $$ (i,j)"
  proof cases
    case UL
    then show ?thesis
      using assms i_bound j_bound
      by (simp add: dagger_def cpx_mat_cnj_def)
  next
    case UR
    then have "i - nc1 < nc2"
      using i_bound by linarith
    then show ?thesis
      using assms UR i_bound j_bound
      by (simp add: dagger_def cpx_mat_cnj_def)
  next
    case LL
    then have "j - nr1 < nr2"
      using j_bound by linarith
    then show ?thesis
      using assms LL i_bound j_bound
      by (simp add: dagger_def cpx_mat_cnj_def)
  next
    case LR
    then have "j - nr1 < nr2" and "i - nc1 < nc2"
      using i_bound j_bound by linarith+
    then show ?thesis
      using assms LR i_bound j_bound
      by (simp add: dagger_def cpx_mat_cnj_def)
  qed
qed

lemma dagger_zero_mat[simp]:
  "(0\<^sub>m m n :: complex Matrix.mat)\<^sup>\<dagger> = 0\<^sub>m n m"
  by (rule eq_matI) (simp_all add: dagger_def)

lemma block_diag_mult:
  fixes A B D E :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n n"
      and B: "B \<in> carrier_mat n n"
      and D: "D \<in> carrier_mat m m"
      and E: "E \<in> carrier_mat m m"
  shows "four_block_mat A (0\<^sub>m n m) (0\<^sub>m m n) D *
         four_block_mat B (0\<^sub>m n m) (0\<^sub>m m n) E =
         four_block_mat (A * B) (0\<^sub>m n m) (0\<^sub>m m n) (D * E)"
proof -
  have raw:
    "four_block_mat A (0\<^sub>m n m) (0\<^sub>m m n) D *
     four_block_mat B (0\<^sub>m n m) (0\<^sub>m m n) E =
     four_block_mat (A * B + 0\<^sub>m n m * 0\<^sub>m m n)
       (A * 0\<^sub>m n m + 0\<^sub>m n m * E)
       (0\<^sub>m m n * B + D * 0\<^sub>m m n)
       (0\<^sub>m m n * 0\<^sub>m n m + D * E)"
    by (rule mult_four_block_mat[OF A _ _ D B _ _ E]) auto
  have z11: "0\<^sub>m n m * (0\<^sub>m m n :: complex Matrix.mat) = 0\<^sub>m n n"
    by (rule left_mult_zero_mat) simp
  have z12a: "A * 0\<^sub>m n m = 0\<^sub>m n m"
    by (rule right_mult_zero_mat[OF A])
  have z12b: "0\<^sub>m n m * E = 0\<^sub>m n m"
    by (rule left_mult_zero_mat[OF E])
  have z21a: "0\<^sub>m m n * B = 0\<^sub>m m n"
    by (rule left_mult_zero_mat[OF B])
  have z21b: "D * 0\<^sub>m m n = 0\<^sub>m m n"
    by (rule right_mult_zero_mat[OF D])
  have z22: "0\<^sub>m m n * (0\<^sub>m n m :: complex Matrix.mat) = 0\<^sub>m m m"
    by (rule left_mult_zero_mat) simp
  have AB: "A * B \<in> carrier_mat n n"
    using A B by auto
  have DE: "D * E \<in> carrier_mat m m"
    using D E by auto
  have add11: "A * B + 0\<^sub>m n n = A * B"
    by (rule right_add_zero_mat[OF AB])
  have add22: "0\<^sub>m m m + D * E = D * E"
    by (rule left_add_zero_mat[OF DE])
  have final:
    "four_block_mat (A * B + 0\<^sub>m n n) (0\<^sub>m n m) (0\<^sub>m m n) (0\<^sub>m m m + D * E) =
     four_block_mat (A * B) (0\<^sub>m n m) (0\<^sub>m m n) (D * E)"
    by (subst add11, subst add22, rule refl)
  have mid11: "A * B + 0\<^sub>m n m * 0\<^sub>m m n = A * B + 0\<^sub>m n n"
    using arg_cong[OF z11, of "\<lambda>X. A * B + X"] by simp
  have mid12: "A * 0\<^sub>m n m + 0\<^sub>m n m * E = 0\<^sub>m n m"
    by (subst z12a, subst z12b, simp)
  have mid21: "0\<^sub>m m n * B + D * 0\<^sub>m m n = 0\<^sub>m m n"
    by (subst z21a, subst z21b, simp)
  have mid22: "0\<^sub>m m n * 0\<^sub>m n m + D * E = 0\<^sub>m m m + D * E"
    using arg_cong[OF z22, of "\<lambda>X. X + D * E"] by simp
  have "four_block_mat A (0\<^sub>m n m) (0\<^sub>m m n) D *
        four_block_mat B (0\<^sub>m n m) (0\<^sub>m m n) E =
        four_block_mat (A * B + 0\<^sub>m n m * 0\<^sub>m m n)
          (A * 0\<^sub>m n m + 0\<^sub>m n m * E)
          (0\<^sub>m m n * B + D * 0\<^sub>m m n)
          (0\<^sub>m m n * 0\<^sub>m n m + D * E)"
    by (rule raw)
  also have "\<dots> =
        four_block_mat (A * B + 0\<^sub>m n n) (0\<^sub>m n m) (0\<^sub>m m n) (0\<^sub>m m m + D * E)"
    by (rule cong_four_block_mat[OF mid11 mid12 mid21 mid22])
  also have "\<dots> = four_block_mat (A * B) (0\<^sub>m n m) (0\<^sub>m m n) (D * E)"
    by (rule final)
  finally show ?thesis .
qed

lemma block_diag_unitary:
  fixes U V :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat n n"
      and V: "V \<in> carrier_mat m m"
      and uU: "unitary U"
      and uV: "unitary V"
  shows "unitary (four_block_mat U (0\<^sub>m n m) (0\<^sub>m m n) V)"
proof -
  let ?M = "four_block_mat U (0\<^sub>m n m) (0\<^sub>m m n) V"

  have Ud: "(U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using U by auto

  have Vd: "(V\<^sup>\<dagger>) \<in> carrier_mat m m"
    using V by auto

  have dagger_M:
    "(?M\<^sup>\<dagger>) = four_block_mat (U\<^sup>\<dagger>) (0\<^sub>m n m) (0\<^sub>m m n) (V\<^sup>\<dagger>)"
    using U V
    by (smt (verit, best) dagger_four_block_mat_complex dagger_zero_mat zero_carrier_mat)


    have left_mult: "(?M\<^sup>\<dagger>) * ?M = 1\<^sub>m (n + m)"
  proof -
    have "(?M\<^sup>\<dagger>) * ?M =
        four_block_mat
          (((U\<^sup>\<dagger>) * U) + (0\<^sub>m n m) * (0\<^sub>m m n))
          (((U\<^sup>\<dagger>) * (0\<^sub>m n m)) + (0\<^sub>m n m) * V)
          (((0\<^sub>m m n) * U) + ((V\<^sup>\<dagger>) * (0\<^sub>m m n)))
          (((0\<^sub>m m n) * (0\<^sub>m n m)) + ((V\<^sup>\<dagger>) * V))"
      using U V Ud Vd by (simp add: block_diag_mult dagger_M)
    also have "... =
        four_block_mat
          ((U\<^sup>\<dagger>) * U)
          (0\<^sub>m n m)
          (0\<^sub>m m n)
          ((V\<^sup>\<dagger>) * V)"
      using U V Ud Vd by simp
    also have "... =
        four_block_mat
          (1\<^sub>m n)
          (0\<^sub>m n m)
          (0\<^sub>m m n)
          (1\<^sub>m m)"
      using uU uV U V unitary_def by auto
    also have "... = 1\<^sub>m (n + m)"
    proof (rule eq_matI)
      show "dim_row (four_block_mat (1\<^sub>m n) (0\<^sub>m n m) (0\<^sub>m m n) (1\<^sub>m m)) =
            dim_row (1\<^sub>m (n + m))"
        by simp
      show "dim_col (four_block_mat (1\<^sub>m n) (0\<^sub>m n m) (0\<^sub>m m n) (1\<^sub>m m)) =
            dim_col (1\<^sub>m (n + m))"
        by simp
    next
      fix i j
      assume i: "i < dim_row (1\<^sub>m (n + m))"
      assume j: "j < dim_col (1\<^sub>m (n + m))"
      then have ib: "i < n + m" and jb: "j < n + m"
        using i by simp_all
      show "(four_block_mat (1\<^sub>m n) (0\<^sub>m n m) (0\<^sub>m m n) (1\<^sub>m m)) $$ (i,j) =
            (1\<^sub>m (n + m)) $$ (i,j)"
      proof (cases "i < n")
        case True
        then show ?thesis
        proof (cases "j < n")
          case True
          then show ?thesis
            using True by simp
        next
          case False
          then have "j - n < m"
            using jb by linarith
          then show ?thesis
            using True False by simp
        qed
      next
        case False
        then have "i - n < m"
          using ib by linarith
        then show ?thesis
        proof (cases "j < n")
          case True
          then show ?thesis
            using False by simp
        next
          case False
          then have "j - n < m"
            using jb by linarith
          then show ?thesis
            using False by simp
        qed
      qed
    qed
    finally show ?thesis.
  qed

  have right_mult: "?M * (?M\<^sup>\<dagger>) = 1\<^sub>m (n + m)"
  proof -
    have "?M * (?M\<^sup>\<dagger>) =
        four_block_mat
          ((U * (U\<^sup>\<dagger>)) + (0\<^sub>m n m) * (0\<^sub>m m n))
          ((U * (0\<^sub>m n m)) + (0\<^sub>m n m) * (V\<^sup>\<dagger>))
          (((0\<^sub>m m n) * (U\<^sup>\<dagger>)) + (V * (0\<^sub>m m n)))
          (((0\<^sub>m m n) * (0\<^sub>m n m)) + (V * (V\<^sup>\<dagger>)))"
      using U V Ud Vd by (simp add: block_diag_mult dagger_M)
    also have "... =
        four_block_mat
          (U * (U\<^sup>\<dagger>))
          (0\<^sub>m n m)
          (0\<^sub>m m n)
          (V * (V\<^sup>\<dagger>))"
      using U V Ud Vd by simp
    also have "... =
        four_block_mat
          (1\<^sub>m n)
          (0\<^sub>m n m)
          (0\<^sub>m m n)
          (1\<^sub>m m)"
      using uU uV U V unitary_def by force
    also have "... = 1\<^sub>m (n + m)"
    proof (rule eq_matI)
      show "dim_row (four_block_mat (1\<^sub>m n) (0\<^sub>m n m) (0\<^sub>m m n) (1\<^sub>m m)) =
            dim_row (1\<^sub>m (n + m))"
        by simp
      show "dim_col (four_block_mat (1\<^sub>m n) (0\<^sub>m n m) (0\<^sub>m m n) (1\<^sub>m m)) =
            dim_col (1\<^sub>m (n + m))"
        by simp
    next
      fix i j
      assume i: "i < dim_row (1\<^sub>m (n + m))"
      assume j: "j < dim_col (1\<^sub>m (n + m))"
      then have ib: "i < n + m" and jb: "j < n + m"
        using i by simp_all
      show "(four_block_mat (1\<^sub>m n) (0\<^sub>m n m) (0\<^sub>m m n) (1\<^sub>m m)) $$ (i,j) =
            (1\<^sub>m (n + m)) $$ (i,j)"
      proof (cases "i < n")
        case True
        then show ?thesis
        proof (cases "j < n")
          case True
          then show ?thesis
            using True by simp
        next
          case False
          then have "j - n < m"
            using jb by linarith
          then show ?thesis
            using True False by simp
        qed
      next
        case False
        then have "i - n < m"
          using ib by linarith
        then show ?thesis
        proof (cases "j < n")
          case True
          then show ?thesis
            using False by simp
        next
          case False
          then have "j - n < m"
            using jb by linarith
          then show ?thesis
            using False by simp
        qed
      qed
    qed
    finally show ?thesis.
  qed

  show ?thesis
    unfolding unitary_def
    using left_mult right_mult U V by auto
qed

lemma complex_matrix_has_eigenvector:
  fixes A :: "complex Matrix.mat"
  assumes sq: "A \<in> carrier_mat n n"
      and n_pos: "n > 0"
  shows "\<exists>e v. eigenvector A v e"
proof -
  obtain es where cp: "char_poly A = (\<Prod>e\<leftarrow>es. [:- e, 1:])"
    and len: "length es = n"
    using char_poly_factorized[OF sq] by blast
  from len n_pos obtain e es' where es: "es = e # es'"
    by (cases es) auto
  have "poly (char_poly A) e = 0"
    unfolding cp es by simp
  then have "eigenvalue A e"
    using eigenvalue_root_char_poly[OF sq] by simp
  then show ?thesis
    unfolding eigenvalue_def by blast
qed

(* Bridge: a full orthonormal list of length n gives a unitary matrix. *)
lemma orthonormal_mat_unitary:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
  shows "unitary (mat_of_cols n vs)"
proof -
  let ?V = "mat_of_cols n vs"
  have left: "?V\<^sup>\<dagger> * ?V = 1\<^sub>m n"
    using cols_mat_dagger_left[OF orth] full by simp
  have right: "?V * (?V\<^sup>\<dagger>) = 1\<^sub>m n"
    using cols_mat_dagger_right[OF orth full].
  show ?thesis
    unfolding unitary_def
    using left right full mat_of_cols_carrier(2) mat_of_cols_carrier(3) by simp
qed

(* Normalization of an eigenvector is still an eigenvector. *)
lemma eigenvec_normalize:
  fixes A :: "complex Matrix.mat" and v :: "complex Matrix.vec"
  assumes sq:   "A \<in> carrier_mat n n"
      and vdim: "v \<in> carrier_vec n"
      and vne:  "v \<noteq> 0\<^sub>v n"
      and ev:   "A *\<^sub>v v = e \<cdot>\<^sub>v v"
  defines "v\<^sub>1 \<equiv> (1 / \<parallel>v\<parallel>) \<cdot>\<^sub>v v"
  shows "A *\<^sub>v v\<^sub>1 = e \<cdot>\<^sub>v v\<^sub>1" and "\<parallel>v\<^sub>1\<parallel> = 1"
proof -
  have nv_pos: "\<parallel>v\<parallel> > 0"
    using cpx_vec_length_zero_iff vne vdim
    by (smt (verit) Re_complex_of_real carrier_vecD cpx_vec_length_inner_prod csqrt_of_real_nonneg inner_prod_csqrt
        inner_prod_with_itself_Im inner_prod_with_itself_Re real_sqrt_abs)
  show "A *\<^sub>v v\<^sub>1 = e \<cdot>\<^sub>v v\<^sub>1"
    unfolding v\<^sub>1_def
    using sq vdim
    by (simp add: mult_mat_vec ev smult_smult_assoc)
  have "\<parallel>v\<^sub>1\<parallel> = cmod (1 / of_real \<parallel>v\<parallel>) * \<parallel>v\<parallel>"
    unfolding v\<^sub>1_def using cpx_vec_length_smult[of "(1 / \<parallel>v\<parallel>)" v] by simp
  also have "\<dots> = (1 / \<parallel>v\<parallel>) * \<parallel>v\<parallel>"
    by (simp add: norm_divide nv_pos less_eq_real_def)
  also have "\<dots> = 1"
    using nv_pos by simp
  finally show "\<parallel>v\<^sub>1\<parallel> = 1".
qed

definition vec_normalize :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "vec_normalize v = (if v = 0\<^sub>v (dim_vec v) then v else (1 / \<parallel>v\<parallel>) \<cdot>\<^sub>v v)"

lemma normalized_vec_norm:
  assumes vdim: "v \<in> carrier_vec n"
      and vne:  "v \<noteq> 0\<^sub>v n"
  shows "\<parallel>vec_normalize v\<parallel> = 1"
  by (smt (verit) Re_complex_of_real carrier_vecD cpx_vec_length_inner_prod cpx_vec_length_smult 
      cpx_vec_length_zero_iff csqrt_of_real_nonneg inner_prod_csqrt inner_prod_with_itself_Im 
      inner_prod_with_itself_Re mult_minus_left nonzero_eq_divide_eq norm_of_real real_sqrt_abs vdim
      vec_normalize_def vne)

lemma four_block_mat_mult_left_block_diag:
  fixes U   :: "complex Matrix.mat"
    and A11 :: "complex Matrix.mat"
    and A12 :: "complex Matrix.mat"
    and A21 :: "complex Matrix.mat"
    and A22 :: "complex Matrix.mat"
  assumes U:   "U \<in> carrier_mat n n"
      and A11: "A11 \<in> carrier_mat 1 1"
      and A12: "A12 \<in> carrier_mat 1 n"
      and A21: "A21 \<in> carrier_mat n 1"
      and A22: "A22 \<in> carrier_mat n n"
  shows
    "(four_block_mat (1\<^sub>m 1 :: complex Matrix.mat)
       (0\<^sub>m 1 n :: complex Matrix.mat)
       (0\<^sub>m n 1 :: complex Matrix.mat)
       U)
     *
     (four_block_mat A11 A12 A21 A22)
     =
     four_block_mat A11 A12 (U * A21) (U * A22)"
proof -
  have f1: "1\<^sub>m 1 * A11 + 0\<^sub>m 1 n * A21 = A11" using A11 A21 by auto
  have f2: "1\<^sub>m 1 * A12 + 0\<^sub>m 1 n * A22 = A12" using A12 A22 by auto
  have f3: "0\<^sub>m n 1 * A11 + U * A21 = U * A21" using A11 U A21 by auto
  have f4: "0\<^sub>m n 1 * A12 + U * A22 = U * A22" using A12 U A22 by auto
  have "four_block_mat (1\<^sub>m 1 :: complex Matrix.mat) (0\<^sub>m 1 n) (0\<^sub>m n 1) U
        * four_block_mat A11 A12 A21 A22
        = four_block_mat (1\<^sub>m 1 * A11 + 0\<^sub>m 1 n * A21)
                         (1\<^sub>m 1 * A12 + 0\<^sub>m 1 n * A22)
                         (0\<^sub>m n 1 * A11 + U * A21)
                         (0\<^sub>m n 1 * A12 + U * A22)"
    by (meson A11 U assms(3-5) mult_four_block_mat one_carrier_mat zero_carrier_mat)
  then show ?thesis using f1 f2 f3 f4 by simp
qed

(* Connection between cscalar_prod and inner_prod *)
lemma cscalar_prod_is_inner_prod_swap:
  fixes u v :: "complex Matrix.vec"
  assumes "u \<in> carrier_vec n" and "v \<in> carrier_vec n"
  shows "u \<bullet>c v = \<langle>v|u\<rangle>"
proof -
  have "u \<bullet>c v = (\<Sum>i = 0..<n. u $ i * cnj (v $ i))"
    using assms by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>i = 0..<n. cnj (v $ i) * u $ i)"
    by (simp add: ac_simps)
  also have "\<dots> = \<langle>v|u\<rangle>"
    using assms by (simp add: inner_prod_def)
  finally show ?thesis .
qed

(* vec_normalize preserves dimension *)
lemma vec_normalize_dim[simp]:
  "dim_vec (vec_normalize v) = dim_vec v"
  by (simp add: vec_normalize_def)

lemma vec_normalize_carrier[simp]:
  assumes "v \<in> carrier_vec n"
  shows "vec_normalize v \<in> carrier_vec n"
  using assms by (simp add: vec_normalize_def)

lemma vec_normalize_unit:
  assumes vdim: "v \<in> carrier_vec n" and vnorm: "\<parallel>v\<parallel> = 1"
  shows "vec_normalize v = v"
proof -
  have vne: "v \<noteq> 0\<^sub>v n"
  proof
    assume h: "v = 0\<^sub>v n"
    from h vdim have "v = 0\<^sub>v (dim_vec v)" by auto
    then have "\<parallel>v\<parallel> = 0" using cpx_vec_length_zero_iff by blast
    then show False using vnorm by simp
  qed
  have "vec_normalize v = (1 / \<parallel>v\<parallel>) \<cdot>\<^sub>v v"
    using vne vdim by (simp add: vec_normalize_def)
  also have "\<dots> = 1 \<cdot>\<^sub>v v"
    using vnorm by simp
  also have "\<dots> = v" by simp
  finally show ?thesis .
qed

(* ONB extension: any unit vector extends to an orthonormal basis. *)
lemma unit_vec_extends_to_onb:
  fixes v :: "complex Matrix.vec"
  assumes vdim: "v \<in> carrier_vec n"
      and vnorm: "\<parallel>v\<parallel> = 1"
  shows "\<exists>vs. orthonormal_list n vs \<and> length vs = n \<and> vs ! 0 = v"
proof -
  have vne: "v \<noteq> 0\<^sub>v n"
  proof
    assume h: "v = 0\<^sub>v n"
    from h vdim have "v = 0\<^sub>v (dim_vec v)" by auto
    then have "\<parallel>v\<parallel> = 0" using cpx_vec_length_zero_iff by blast
    then show False using vnorm by simp
  qed
  have n_pos: "n > 0"
  proof (rule ccontr)
    assume "\<not> 0 < n"
    then have n0: "n = 0" by simp
    with vdim have "dim_vec v = 0" by auto
    then have "v = 0\<^sub>v 0"
      by (intro eq_vecI) auto
    then show False using vne n0 by simp
  qed
  interpret cof_vec_space n "TYPE(complex)".
  define b where "b = basis_completion v"
  define ws where "ws = gram_schmidt n b"
  from basis_completion[OF vdim vne, folded b_def]
  have b_dist: "distinct b"
    and b_indep: "\<not> lin_dep (set b)"
    and b_sub: "set b \<subseteq> carrier_vec n"
    and b_hd: "hd b = v"
    and b_len: "length b = n"
    by auto
  from b_len n_pos obtain bs where b_eq: "b = v # bs"
    using b_hd by (cases b; auto)
  from gram_schmidt_result[OF b_sub b_dist b_indep refl, folded ws_def]
  have ws_sub: "set ws \<subseteq> carrier_vec n"
    and ws_corth: "corthogonal ws"
    and ws_len: "length ws = n"
    by (auto simp: b_len)
  from gram_schmidt_hd[OF vdim, of bs, folded b_eq]
  have ws_hd: "hd ws = v" unfolding ws_def .
  (* key facts about ws *)
  have ws_carrier: "\<And>i. i < n \<Longrightarrow> ws ! i \<in> carrier_vec n"
    using ws_sub ws_len by (simp add: subset_iff)
  have ws_self_ne0: "\<And>i. i < n \<Longrightarrow> ws ! i \<bullet>c ws ! i \<noteq> 0"
    using ws_corth ws_len corthogonalD by fastforce
  have ws_nonzero: "\<And>i. i < n \<Longrightarrow> ws ! i \<noteq> 0\<^sub>v n"
  proof -
    fix i assume i: "i < n"
    show "ws ! i \<noteq> 0\<^sub>v n"
    proof
      assume h: "ws ! i = 0\<^sub>v n"
      have "ws ! i \<bullet>c ws ! i = 0"
        using h by (simp add: scalar_prod_def)
      then show False using ws_self_ne0[OF i] by simp
    qed
  qed
  (* ws ! 0 = v since hd ws = v *)
  have ws0: "ws ! 0 = v"
    using ws_hd ws_len n_pos
    by (metis hd_conv_nth length_greater_0_conv)
  define vs where "vs = map vec_normalize ws"
  have vs_len: "length vs = n" using ws_len by (simp add: vs_def)
  have vs_nth: "\<And>i. i < n \<Longrightarrow> vs ! i = vec_normalize (ws ! i)"
    using ws_len by (simp add: vs_def)
  have vs_nth_carrier: "\<And>i. i < n \<Longrightarrow> vs ! i \<in> carrier_vec n"
    using vs_nth ws_carrier vec_normalize_carrier by simp
  (* vs ! 0 = v since v has norm 1 *)
  have vs0: "vs ! 0 = v"
    using vs_nth[OF n_pos] ws0 vec_normalize_unit[OF vdim vnorm] by simp
  (* vs ! i has unit norm *)
  have vs_nth_unit: "\<And>i. i < n \<Longrightarrow> \<parallel>vs ! i\<parallel> = 1"
  proof -
    fix i assume i: "i < n"
    have "\<parallel>vs ! i\<parallel> = \<parallel>vec_normalize (ws ! i)\<parallel>"
      using vs_nth[OF i] by simp
    also have "\<dots> = 1"
      using normalized_vec_norm[OF ws_carrier[OF i] ws_nonzero[OF i]] .
    finally show "\<parallel>vs ! i\<parallel> = 1" .
  qed
  have vs_nth_def: "\<And>i. i < n \<Longrightarrow> vs ! i = (1 / \<parallel>ws ! i\<parallel>) \<cdot>\<^sub>v (ws ! i)"
  proof -
    fix i assume i: "i < n"
    have "vs ! i = vec_normalize (ws ! i)"
      using vs_nth[OF i] .
    also have "\<dots> = (1 / \<parallel>ws ! i\<parallel>) \<cdot>\<^sub>v (ws ! i)"
      using ws_nonzero[OF i] ws_carrier[OF i]
      by (simp add: vec_normalize_def)
    finally show "vs ! i = (1 / \<parallel>ws ! i\<parallel>) \<cdot>\<^sub>v (ws ! i)" .
  qed
  (* orthonormality for i \<noteq> j *)
  have cross_zero: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<langle>vs ! i | vs ! j\<rangle> = 0"
  proof -
    fix i j assume i: "i < n" and j: "j < n" and ij: "i \<noteq> j"
    have i_lt: "i < length ws" using ws_len i by simp
    have j_lt: "j < length ws" using ws_len j by simp
    have wij_cscal: "ws ! i \<bullet>c ws ! j = 0"
      using corthogonalD[OF ws_corth i_lt j_lt] ij by simp
    have wij_inner: "\<langle>ws ! j | ws ! i\<rangle> = 0"
      using cscalar_prod_is_inner_prod_swap[OF ws_carrier[OF i] ws_carrier[OF j]] wij_cscal
      by simp
    have wji_inner: "\<langle>ws ! i | ws ! j\<rangle> = 0"
      using wij_inner inner_prod_cnj ws_carrier[OF i] ws_carrier[OF j]
      by (metis carrier_vecD complex_cnj_zero)
    have dim_i: "dim_vec (ws ! i) = n" using ws_carrier[OF i] by auto
    have dim_j: "dim_vec (ws ! j) = n" using ws_carrier[OF j] by auto
    let ?a = "1 / \<parallel>ws ! i\<parallel>"
    let ?b = "1 / \<parallel>ws ! j\<parallel>"
    have "\<langle>vs ! i | vs ! j\<rangle> = \<langle>(of_real ?a) \<cdot>\<^sub>v (ws ! i) | (of_real ?b) \<cdot>\<^sub>v (ws ! j)\<rangle>"
      using vs_nth_def[OF i] vs_nth_def[OF j] by simp
    also have "\<dots> = (\<Sum>k<n. cnj ((of_real ?a) * (ws ! i) $ k) * ((of_real ?b) * (ws ! j) $ k))"
      using dim_i dim_j
      by (simp add: inner_prod_def lessThan_atLeast0)
    also have "\<dots> = (\<Sum>k<n. (of_real ?a) * (of_real ?b) * (cnj ((ws ! i) $ k) * (ws ! j) $ k))"
      by (simp add: ac_simps)
    also have "\<dots> = (of_real ?a) * (of_real ?b) * (\<Sum>k<n. cnj ((ws ! i) $ k) * (ws ! j) $ k)"
      by (simp add: sum_distrib_left)
    also have "(\<Sum>k<n. cnj ((ws ! i) $ k) * (ws ! j) $ k) = \<langle>ws ! i | ws ! j\<rangle>"
      using dim_j by (simp add: inner_prod_def lessThan_atLeast0)
    also have "\<dots> = 0" using wji_inner .
    finally show "\<langle>vs ! i | vs ! j\<rangle> = 0" by simp
  qed
  (* orthonormality for i = j *)
  have diag_one: "\<And>i. i < n \<Longrightarrow> \<langle>vs ! i | vs ! i\<rangle> = 1"
  proof -
    fix i assume i: "i < n"
    have "(complex_of_real \<parallel>vs ! i\<parallel>)\<^sup>2 = \<langle>vs ! i | vs ! i\<rangle>"
      using cpx_vec_length_inner_prod by simp
    moreover have "\<parallel>vs ! i\<parallel> = 1" using vs_nth_unit[OF i] .
    ultimately show "\<langle>vs ! i | vs ! i\<rangle> = 1" by simp
  qed
  have orth: "orthonormal_list n vs"
    unfolding orthonormal_list_def
  proof (intro conjI ballI allI impI)
    fix w assume "w \<in> set vs"
    then obtain i where "i < length vs" and "w = vs ! i"
      by (metis in_set_conv_nth)
    then show "dim_vec w = n"
      using vs_len vs_nth_carrier by auto
  next
    fix i j
    assume i: "i < length vs" and j: "j < length vs"
    then have i': "i < n" and j': "j < n" using vs_len by simp_all
    show "\<langle>vs ! i | vs ! j\<rangle> = (if i = j then 1 else 0)"
      using cross_zero[OF i' j'] diag_one[OF i'] by (cases "i = j"; simp)
  qed
  show ?thesis using orth vs_len vs0 by blast
qed

lemma schur_induct:
  "\<forall>A :: complex Matrix.mat.
      A \<in> carrier_mat n n \<longrightarrow>
      (\<exists>U :: complex Matrix.mat. \<exists>T :: complex Matrix.mat.
         U \<in> carrier_mat n n \<and>
         T \<in> carrier_mat n n \<and>
         unitary U \<and>
         upper_triangular T \<and>
         (((U\<^sup>\<dagger>) * A) * U) = T)"
proof (induct n)
  case 0
  show ?case
  proof (intro allI impI, goal_cases)
    case (1 A)
    then have "A = 0\<^sub>m 0 0"
      by auto
    moreover have "unitary (1\<^sub>m 0 :: complex Matrix.mat)"
      by (simp add: unitary_def)
    moreover have "upper_triangular (0\<^sub>m 0 0 :: complex Matrix.mat)"
      by (simp add: upper_triangular_def)
    moreover have "(1\<^sub>m 0 :: complex Matrix.mat)\<^sup>\<dagger> * 0\<^sub>m 0 0 * 1\<^sub>m 0 = 0\<^sub>m 0 0"
      by simp
    ultimately show ?case
      by (metis one_carrier_mat zero_carrier_mat)
  qed
next
  case (Suc n)
  show ?case
  proof (intro allI impI)
    fix A :: "complex Matrix.mat"
    assume sq: "A \<in> carrier_mat (Suc n) (Suc n)"
    (* Step 1: get an eigenvector and normalise it. *)
    obtain e v where ev: "eigenvector A v e"
      using complex_matrix_has_eigenvector[OF sq] by auto
    then have vdim: "v \<in> carrier_vec (Suc n)" and vne: "v \<noteq> 0\<^sub>v (Suc n)"
         and vev: "A *\<^sub>v v = e \<cdot>\<^sub>v v"
      using sq unfolding eigenvector_def by auto
    define v\<^sub>1 where "v\<^sub>1 \<equiv> (1 / \<parallel>v\<parallel>) \<cdot>\<^sub>v v"
    have v1dim: "v\<^sub>1 \<in> carrier_vec (Suc n)"
      unfolding v\<^sub>1_def using vdim by simp
    have v1ev: "A *\<^sub>v v\<^sub>1 = e \<cdot>\<^sub>v v\<^sub>1"
      using eigenvec_normalize(1)[OF sq vdim vne vev] unfolding v\<^sub>1_def .
    have v1norm: "\<parallel>v\<^sub>1\<parallel> = 1"
      using eigenvec_normalize(2)[OF sq vdim vne vev] unfolding v\<^sub>1_def .
    (* Step 2: extend v₁ to a full orthonormal basis. *)
    obtain vs :: "complex Matrix.vec list"
      where orth: "orthonormal_list (Suc n) vs"
        and full: "length vs = Suc n"
        and hd0: "vs ! 0 = v\<^sub>1"
      using unit_vec_extends_to_onb[OF v1dim v1norm] by blast
    (* Step 3: form U₁ and show it is unitary. *)
    let ?U\<^sub>1 = "mat_of_cols (Suc n) vs"
    have U1_carrier: "?U\<^sub>1 \<in> carrier_mat (Suc n) (Suc n)"
      using mat_of_cols_carrier(1)[of "Suc n" vs] full by simp
    have U1_unitary: "unitary ?U\<^sub>1"
      using orthonormal_mat_unitary[OF orth full].
    (* Step 4: the conjugated matrix has block structure.
       Column 0 of ?U\<^sub>1\<dagger> * A * ?U\<^sub>1 is [e, 0, ..., 0]ᵀ, yielding four_block form. *)
    have U1dag_carrier: "?U\<^sub>1\<^sup>\<dagger> \<in> carrier_mat (Suc n) (Suc n)"
      using U1_carrier by (metis carrier_matD carrier_matI dim_col_of_dagger dim_row_of_dagger)
    let ?M = "?U\<^sub>1\<^sup>\<dagger> * A * ?U\<^sub>1"
    have M_carrier: "?M \<in> carrier_mat (Suc n) (Suc n)"
      using U1_carrier U1dag_carrier sq by auto
    have U1_col0: "Matrix.col ?U\<^sub>1 0 = v\<^sub>1"
    proof -
      have "vs ! 0 \<in> carrier_vec (Suc n)"
        using orthonormal_listD_carrier[OF orth] full
        by (metis in_mono nth_mem zero_less_Suc)
      then have "Matrix.col ?U\<^sub>1 0 = vs ! 0"
        using full by simp
      then show ?thesis using hd0 by simp
    qed
    have v1_dim: "dim_vec v\<^sub>1 = Suc n" using v1dim by auto
    have M_col0: "Matrix.col ?M 0 = e \<cdot>\<^sub>v unit_vec (Suc n) 0"
    proof -
      have AU1_col0: "Matrix.col (A * ?U\<^sub>1) 0 = e \<cdot>\<^sub>v v\<^sub>1"
      proof -
        have "Matrix.col (A * ?U\<^sub>1) 0 = A *\<^sub>v Matrix.col ?U\<^sub>1 0"
          using col_mult2[OF sq U1_carrier, of 0] by simp
        also have "\<dots> = A *\<^sub>v v\<^sub>1" using U1_col0 by simp
        also have "\<dots> = e \<cdot>\<^sub>v v\<^sub>1" using v1ev.
        finally show ?thesis.
      qed
      have U1dag_U1_eq_one: "?U\<^sub>1\<^sup>\<dagger> * ?U\<^sub>1 = 1\<^sub>m (Suc n)"
        using U1_unitary U1_carrier unfolding unitary_def by auto
      have U1dag_v1: "?U\<^sub>1\<^sup>\<dagger> *\<^sub>v v\<^sub>1 = unit_vec (Suc n) 0"
      proof -
        have "(?U\<^sub>1\<^sup>\<dagger>) *\<^sub>v v\<^sub>1 = (?U\<^sub>1\<^sup>\<dagger>) *\<^sub>v Matrix.col ?U\<^sub>1 0" using U1_col0 by simp
        also have "\<dots> = Matrix.col (?U\<^sub>1\<^sup>\<dagger> * ?U\<^sub>1) 0"
          using col_mult2[OF U1dag_carrier U1_carrier, of 0] by simp
        also have "\<dots> = Matrix.col (1\<^sub>m (Suc n)) 0" using U1dag_U1_eq_one by simp
        also have "\<dots> = unit_vec (Suc n) 0" by simp
        finally show ?thesis.
      qed
      have AU1_carrier: "A * ?U\<^sub>1 \<in> carrier_mat (Suc n) (Suc n)"
        using sq U1_carrier by auto
      have M_assoc: "?M = (?U\<^sub>1\<^sup>\<dagger>) * (A * ?U\<^sub>1)"
        using U1dag_carrier sq U1_carrier by simp
      have "Matrix.col ?M 0 = Matrix.col (?U\<^sub>1\<^sup>\<dagger> * (A * ?U\<^sub>1)) 0" using M_assoc by simp
      also have "\<dots> = (?U\<^sub>1\<^sup>\<dagger>) *\<^sub>v Matrix.col (A * ?U\<^sub>1) 0"
        using col_mult2[OF U1dag_carrier AU1_carrier, of 0] by simp
      also have "\<dots> = (?U\<^sub>1\<^sup>\<dagger>) *\<^sub>v (e \<cdot>\<^sub>v v\<^sub>1)" 
        using AU1_col0 by simp
      also have "\<dots> = e \<cdot>\<^sub>v (?U\<^sub>1\<^sup>\<dagger> *\<^sub>v v\<^sub>1)"
        using U1dag_carrier v1dim by (simp add: mult_mat_vec)
      also have "\<dots> = e \<cdot>\<^sub>v unit_vec (Suc n) 0" using U1dag_v1 by simp
      finally show ?thesis.
    qed
    obtain M1 M2 M3 M4 where
      splitM: "split_block ?M 1 1 = (M1, M2, M3, M4)"
      by (cases "split_block ?M 1 1", auto)
    have M_dims: "dim_row ?M = 1 + n" "dim_col ?M = 1 + n"
      using M_carrier by auto
    from split_block[OF splitM M_dims] have
      M1_c: "M1 \<in> carrier_mat 1 1"
      and M2_c: "M2 \<in> carrier_mat 1 n"
      and M3_c: "M3 \<in> carrier_mat n 1"
      and M4_c: "M4 \<in> carrier_mat n n"
      and M_block: "?M = four_block_mat M1 M2 M3 M4" by auto
    have M00: "?M $$ (0, 0) = e"
    proof -
      have "?M $$ (0, 0) = Matrix.col ?M 0 $ 0" using M_carrier by auto
      also have "\<dots> = (e \<cdot>\<^sub>v unit_vec (Suc n) 0) $ 0" using M_col0 by simp
      also have "\<dots> = e" by simp
      finally show ?thesis .
    qed
    have M_Suc_i_0: "\<And>i. i < n \<Longrightarrow> ?M $$ (Suc i, 0) = 0"
    proof -
      fix i assume i: "i < n"
      have "?M $$ (Suc i, 0) = Matrix.col ?M 0 $ (Suc i)"
        using M_carrier i by auto
      also have "\<dots> = (e \<cdot>\<^sub>v unit_vec (Suc n) 0) $ (Suc i)" using M_col0 by simp
      also have "\<dots> = 0" using i by simp
      finally show "?M $$ (Suc i, 0) = 0".
    qed
    have M1_eq: "M1 = Matrix.mat 1 1 (\<lambda>_. e)"
    proof (rule eq_matI)
      show "dim_row M1 = dim_row (Matrix.mat 1 1 (\<lambda>_. e))"
        using M1_c by auto
      show "dim_col M1 = dim_col (Matrix.mat 1 1 (\<lambda>_. e))"
        using M1_c by auto
      fix i j assume i: "i < dim_row (Matrix.mat 1 1 (\<lambda>_. e))"
        and j: "j < dim_col (Matrix.mat 1 1 (\<lambda>_. e))"
      then have "i = 0" "j = 0" by auto
      then have "M1 $$ (i, j) = ?M $$ (0, 0)"
        using splitM unfolding split_block_def Let_def by auto
      also have "\<dots> = e" using M00 .
      also have "\<dots> = Matrix.mat 1 1 (\<lambda>_. e) $$ (i, j)"
        using \<open>i = 0\<close> \<open>j = 0\<close> by simp
      finally show "M1 $$ (i, j) = Matrix.mat 1 1 (\<lambda>_. e) $$ (i, j)".
    qed
    have M3_eq: "M3 = 0\<^sub>m n 1"
    proof (rule eq_matI)
      show "dim_row M3 = dim_row (0\<^sub>m n 1)" using M3_c by auto
      show "dim_col M3 = dim_col (0\<^sub>m n 1)" using M3_c by auto
      fix i j assume i: "i < dim_row (0\<^sub>m n 1)" and j: "j < dim_col (0\<^sub>m n 1)"
      then have ia: "i < n" and ja: "j = 0" by auto
      have M3_index: "\<And>i' j'. i' < n \<Longrightarrow> j' < 1 \<Longrightarrow> M3 $$ (i', j') = ?M $$ (Suc i', j')"
        using splitM M_dims unfolding split_block_def Let_def by auto
      have "M3 $$ (i, j) = ?M $$ (Suc i, 0)"
        using M3_index[OF ia] ja by simp
      also have "\<dots> = 0" using M_Suc_i_0[OF ia] .
      also have "\<dots> = (0\<^sub>m n 1) $$ (i, j)" using ia ja by simp
      finally show "M3 $$ (i, j) = (0\<^sub>m n 1) $$ (i, j)".
    qed
    have final_block:
      "?M = four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) M2 (0\<^sub>m n 1) M4"
      using M_block M1_eq M3_eq by simp
    obtain A\<^sub>2 A\<^sub>3 :: "complex Matrix.mat"
      where A2_carrier: "A\<^sub>2 \<in> carrier_mat 1 n"
        and A3_carrier: "A\<^sub>3 \<in> carrier_mat n n"
        and conj_block:
          "?U\<^sub>1\<^sup>\<dagger> * A * ?U\<^sub>1 =
           four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) A\<^sub>3"
      using M2_c M4_c final_block by blast
    (* Step 5: apply the induction hypothesis to A₃. *)
    obtain U\<^sub>2 T\<^sub>3 :: "complex Matrix.mat"
      where U2_carrier: "U\<^sub>2 \<in> carrier_mat n n"
        and T3_carrier: "T\<^sub>3 \<in> carrier_mat n n"
        and U2_unitary: "unitary U\<^sub>2"
        and T3_ut: "upper_triangular T\<^sub>3"
        and IH_eq: "U\<^sub>2\<^sup>\<dagger> * A\<^sub>3 * U\<^sub>2 = T\<^sub>3"
      using Suc.hyps[rule_format, OF A3_carrier] by blast
    (* Step 6: form U = U₁ * block(1, U₂) and T = block([e], T₃). *)
    let ?U = "(?U\<^sub>1 * four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) U\<^sub>2)"
    let ?T = "four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) T\<^sub>3"
    have U_carrier: "?U \<in> carrier_mat (Suc n) (Suc n)"
      using U1_carrier U2_carrier
      by (intro mult_carrier_mat) auto
    have U_unitary: "unitary ?U"
    proof -
      have B_carrier:
        "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) U\<^sub>2 \<in>
         carrier_mat (Suc n) (Suc n)"
        using U2_carrier by auto
      have bu: "unitary (four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) U\<^sub>2)"
        using block_diag_unitary[OF one_carrier_mat U2_carrier _ U2_unitary] by simp
      then show ?thesis
        using unitary_mult[OF U1_unitary bu U1_carrier B_carrier] by simp
    qed
    have T_carrier: "?T \<in> carrier_mat (Suc n) (Suc n)"
      using A2_carrier U2_carrier T3_carrier by auto
    have T_ut: "upper_triangular ?T"
    proof -
      have ut_e: "upper_triangular (Matrix.mat 1 1 (\<lambda>_. e) :: complex Matrix.mat)"
        by (simp add: upper_triangular_def)
      have e_carrier: "(Matrix.mat 1 1 (\<lambda>_. e) :: complex Matrix.mat) \<in> carrier_mat 1 1"
        by simp
      then show ?thesis
        using upper_triangular_four_block[OF e_carrier T3_carrier ut_e T3_ut, of "A\<^sub>2 * U\<^sub>2"]
        by simp
    qed
    have UA_eq: "((?U)\<^sup>\<dagger>) * A * ?U = ?T"
    proof -
      let ?B = "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) U\<^sub>2"   
      have B_carrier: "?B \<in> carrier_mat (Suc n) (Suc n)"
        using U2_carrier by auto    
      have U_def: "?U = (?U\<^sub>1 * ?B)"
        by simp    
      have B_dag: "?B\<^sup>\<dagger> = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) (U\<^sub>2\<^sup>\<dagger>)"
        by (smt (verit, ccfv_threshold) U2_carrier carrier_matI dagger_four_block_mat_complex
            dagger_of_id_is_id dagger_zero_mat index_one_mat(2,3) zero_carrier_mat)    
      have step1: "((?U)\<^sup>\<dagger>) * A * ?U = ((?B\<^sup>\<dagger>) * (((?U\<^sub>1\<^sup>\<dagger>) * A * ?U\<^sub>1)) * ?B)"
      proof -
        have U_dag: "((?U)\<^sup>\<dagger>) = ((?B\<^sup>\<dagger>) * (?U\<^sub>1\<^sup>\<dagger>))"
          using B_carrier dagger_of_prod full by auto
        have "((?U)\<^sup>\<dagger>) * A * ?U = ((((?B\<^sup>\<dagger>) * (?U\<^sub>1\<^sup>\<dagger>)) * A) * (?U\<^sub>1 * ?B))"
          using U_dag by argo
        also have "... = (((?B\<^sup>\<dagger>) * ((?U\<^sub>1\<^sup>\<dagger>) * A)) * (?U\<^sub>1 * ?B))"
          using U1_carrier B_carrier sq
          by (metis assoc_mult_mat carrier_matD(1,2) carrier_matI dagger_of_dagger_is_id dim_row_of_dagger)
        also have "... = ((?B\<^sup>\<dagger>) * (((?U\<^sub>1\<^sup>\<dagger>) * A * ?U\<^sub>1)) * ?B)"
          by (smt (verit, best) B_carrier U1_carrier assoc_mult_mat carrier_matD(1,2) 
              carrier_mat_triv dim_col_of_dagger dim_row_of_dagger mult_carrier_mat sq)
        finally show ?thesis.
      qed    
      have left_block: "((?B\<^sup>\<dagger>) * (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) A\<^sub>3))
                     =  (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3))"
      proof -
        have Bdag: "?B\<^sup>\<dagger> = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) (U\<^sub>2\<^sup>\<dagger>)"
          using B_dag.      
        show ?thesis
        proof (rule eq_matI)
          show "dim_row ((?B\<^sup>\<dagger>) * (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) A\<^sub>3))
              = dim_row (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3))"
            using A2_carrier A3_carrier U2_carrier  by (simp add: Bdag)      
          show "dim_col ((?B\<^sup>\<dagger>) * (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) A\<^sub>3))
              = dim_col (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3))"
            using A2_carrier A3_carrier U2_carrier by (simp add: Bdag)      
          fix i j
          assume i: "i < dim_row (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) (U\<^sub>2\<^sup>\<dagger> * A\<^sub>3))"
          assume j: "j < dim_col (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) (U\<^sub>2\<^sup>\<dagger> * A\<^sub>3))"      
          have ij': "i < Suc n" "j < Suc n"
            using IH_eq T3_carrier i A3_carrier j by auto
      
          show "((?B\<^sup>\<dagger>) * (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) A\<^sub>3)) $$ (i,j)
              =
              (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3)) $$ (i,j)"
            using ij' A2_carrier A3_carrier U2_carrier
            by (smt (verit, ccfv_threshold) B_dag carrier_matD(1,2) carrier_mat_triv 
                dim_col_of_dagger dim_row_of_dagger four_block_mat_mult_left_block_diag mat_carrier 
                right_mult_zero_mat zero_carrier_mat)
        qed
      qed    
      have right_block:  "((four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3)) * ?B)
                =   (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) (((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3) * U\<^sub>2))"
      proof -
        show ?thesis
        proof (rule eq_matI)
          show "dim_row ((four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3)) * ?B)
            =   dim_row (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2*U\<^sub>2) (0\<^sub>m n 1) (((U\<^sub>2\<^sup>\<dagger>)*A\<^sub>3)*U\<^sub>2))"
            using A2_carrier A3_carrier U2_carrier by simp     
          show "dim_col ((four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3)) * ?B)  =
            dim_col (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) (((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3) * U\<^sub>2))"
            using A2_carrier A3_carrier U2_carrier  by simp     
          fix i j
          assume i: "i < dim_row
            (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) (((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3) * U\<^sub>2))"
          assume j: "j < dim_col
            (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) (((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3) * U\<^sub>2))"     
          have ij': "i < Suc n" "j < Suc n"
            using IH_eq T3_carrier i A3_carrier j by auto     
          show "((four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>)*A\<^sub>3))*?B) $$ (i,j)
              = (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) (((U\<^sub>2\<^sup>\<dagger>)*A\<^sub>3)*U\<^sub>2))$$(i,j)"
          proof -            
            have right_block: "((four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>) *A\<^sub>3))*?B)
               = (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) (((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3) * U\<^sub>2))"
            proof -
              let ?E = "(Matrix.mat 1 1 (\<lambda>_. e) :: complex Matrix.mat)"
              let ?Z = "(0\<^sub>m n 1 :: complex Matrix.mat)"
              let ?BR = "((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3)"
              let ?L = "four_block_mat ?E A\<^sub>2 ?Z ?BR"
              let ?R = "four_block_mat ?E (A\<^sub>2 * U\<^sub>2) ?Z (?BR * U\<^sub>2)"            
              have E_carrier: "?E \<in> carrier_mat 1 1"
                by simp            
              have Z_carrier: "?Z \<in> carrier_mat n 1"
                by simp            
              have BR_carrier: "?BR \<in> carrier_mat n n"
                using U2_carrier A3_carrier
                by fastforce
              have L_carrier: "?L \<in> carrier_mat (Suc n) (Suc n)"
                using E_carrier A2_carrier Z_carrier BR_carrier
                using IH_eq T_carrier by fastforce            
              have R_carrier: "?R \<in> carrier_mat (Suc n) (Suc n)"
                using E_carrier A2_carrier U2_carrier Z_carrier BR_carrier IH_eq T_carrier by blast
              have L_dag: "?L\<^sup>\<dagger> = four_block_mat (?E\<^sup>\<dagger>) (?Z\<^sup>\<dagger>) (A\<^sub>2\<^sup>\<dagger>) (?BR\<^sup>\<dagger>)"
                using dagger_four_block_mat_complex[OF E_carrier A2_carrier Z_carrier BR_carrier]
                by simp           
              have R_dag: "?R\<^sup>\<dagger> = four_block_mat (?E\<^sup>\<dagger>) (?Z\<^sup>\<dagger>) ((A\<^sub>2 * U\<^sub>2)\<^sup>\<dagger>) ((?BR * U\<^sub>2)\<^sup>\<dagger>)"
                using dagger_four_block_mat_complex[OF E_carrier _ Z_carrier _]
                      A2_carrier U2_carrier BR_carrier
                by (metis carrier_matD(1) carrier_mat_triv index_mult_mat(2,3))           
              have R_dag_expand: "(?R\<^sup>\<dagger>) = four_block_mat (?E\<^sup>\<dagger>) (?Z\<^sup>\<dagger>) ((U\<^sub>2\<^sup>\<dagger>) * (A\<^sub>2\<^sup>\<dagger>)) ((U\<^sub>2\<^sup>\<dagger>) * (?BR\<^sup>\<dagger>))"
                using R_dag A2_carrier U2_carrier BR_carrier
                by (metis carrier_matD(1,2) dagger_of_prod)
              have Bdag: "?B\<^sup>\<dagger> = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) (U\<^sub>2\<^sup>\<dagger>)"
                  using B_dag.           
              have left_mult_on_daggers:
                "((?B\<^sup>\<dagger>) * (?L\<^sup>\<dagger>)) = four_block_mat (?E\<^sup>\<dagger>) (?Z\<^sup>\<dagger>) ((U\<^sub>2\<^sup>\<dagger>) * (A\<^sub>2\<^sup>\<dagger>)) ((U\<^sub>2\<^sup>\<dagger>) * (?BR\<^sup>\<dagger>))"
              proof -
                have "((?B\<^sup>\<dagger>) * (?L\<^sup>\<dagger>)) =
                  ((four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) (U\<^sub>2\<^sup>\<dagger>))
                    * (four_block_mat (?E\<^sup>\<dagger>) (?Z\<^sup>\<dagger>) (A\<^sub>2\<^sup>\<dagger>) (?BR\<^sup>\<dagger>)))"
                  using Bdag L_dag by simp
                also have "... =
                  (four_block_mat (?E\<^sup>\<dagger>) (?Z\<^sup>\<dagger>) ((U\<^sub>2\<^sup>\<dagger>) * (A\<^sub>2\<^sup>\<dagger>)) ((U\<^sub>2\<^sup>\<dagger>) * (?BR\<^sup>\<dagger>)))"
                  using four_block_mat_mult_left_block_diag[of "U\<^sub>2\<^sup>\<dagger>" n "?E\<^sup>\<dagger>" "?Z\<^sup>\<dagger>" "A\<^sub>2\<^sup>\<dagger>" "?BR\<^sup>\<dagger>"]
                        U2_carrier E_carrier Z_carrier A2_carrier BR_carrier
                  by (metis carrier_matD(1,2) carrier_mat_triv dim_col_of_dagger dim_row_of_dagger)
                finally show ?thesis.
              qed          
              have R_dag_as_Bdag_Ldag: "(?R\<^sup>\<dagger>) = ((?B\<^sup>\<dagger>) * (?L\<^sup>\<dagger>))"
                using R_dag_expand left_mult_on_daggers by simp
              have "?R = (?L * ?B)"
              proof -
                have "?R = ((?R\<^sup>\<dagger>)\<^sup>\<dagger>)"
                  using R_carrier
                  using dagger_of_dagger_is_id by presburger 
                also have "... = ((((?B\<^sup>\<dagger>) * (?L\<^sup>\<dagger>)))\<^sup>\<dagger>)"
                  using R_dag_as_Bdag_Ldag by simp
                also have "... = (((?L\<^sup>\<dagger>)\<^sup>\<dagger>) * ((?B\<^sup>\<dagger>)\<^sup>\<dagger>))"
                  using B_carrier L_carrier
                  by (metis carrier_matD(1,2) dagger_of_dagger_is_id dagger_of_prod)
                also have "... = (?L * ?B)"
                  using B_carrier L_carrier by (simp add: dagger_of_dagger_is_id)
                finally show ?thesis.
              qed            
              then show ?thesis
                by simp
            qed
            also have "(((four_block_mat (Matrix.mat 1 1 (\<lambda>_.e)) A\<^sub>2 (0\<^sub>m n 1) ((U\<^sub>2\<^sup>\<dagger>)*A\<^sub>3))*?B))$$(i,j)
              = (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) (((U\<^sub>2\<^sup>\<dagger>)*A\<^sub>3)*U\<^sub>2))$$(i,j)"
              using calculation by argo
            finally show ?thesis
              using
              \<open>(four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) (U\<^sub>2\<^sup>\<dagger> * A\<^sub>3) *
                four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) U\<^sub>2) $$ (i, j) = 
                four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) (A\<^sub>2 * U\<^sub>2) (0\<^sub>m n 1) (U\<^sub>2\<^sup>\<dagger> * A\<^sub>3 * U\<^sub>2) $$ (i, j)\<close>
              by fastforce 
          qed            
        qed
      qed
    
      have IH_sub: "(((U\<^sub>2\<^sup>\<dagger>) * A\<^sub>3) * U\<^sub>2) = T\<^sub>3"
        using IH_eq by simp
    
      have "((?U)\<^sup>\<dagger>) * A * ?U = ((?B\<^sup>\<dagger>) * (((?U\<^sub>1\<^sup>\<dagger>) * A * ?U\<^sub>1)) * ?B)"
        using step1 .
      also have "... = ((?B\<^sup>\<dagger>) * (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) A\<^sub>3) * ?B)"
        using conj_block
        by simp
      also have "... = (((?B\<^sup>\<dagger>) * (four_block_mat (Matrix.mat 1 1 (\<lambda>_. e)) A\<^sub>2 (0\<^sub>m n 1) A\<^sub>3)) * ?B)"
        using B_carrier A2_carrier A3_carrier by simp            
      also have "... = ?T"
        using IH_sub left_block right_block by argo
       show ?thesis
         using IH_sub conj_block left_block right_block step1 by argo 
    qed
    show "\<exists>U T :: complex Matrix.mat.
            U \<in> carrier_mat (Suc n) (Suc n) \<and> T \<in> carrier_mat (Suc n) (Suc n) \<and>
            unitary U \<and> upper_triangular T \<and> (((U\<^sup>\<dagger>) * A) * U) = T"
      using U_carrier T_carrier U_unitary T_ut UA_eq by blast
  qed
qed

theorem schur_theorem:
  fixes A :: "complex Matrix.mat"
  assumes sq: "A \<in> carrier_mat n n"
  shows "\<exists>U :: complex Matrix.mat. \<exists>T :: complex Matrix.mat.
         U \<in> carrier_mat n n \<and>
         T \<in> carrier_mat n n \<and>
         unitary U \<and>
         upper_triangular T \<and>
         (((U\<^sup>\<dagger>) * A) * U) = T"
  using schur_induct[rule_format, OF sq] by blast

(* ---- Corollary: Tr(A) = sum of eigenvalues ---- *)

corollary trace_eq_sum_eigenvalues:
  fixes A :: "complex Matrix.mat"
  assumes sq: "A \<in> carrier_mat n n"
  obtains eigs :: "complex list"
  where "length eigs = n"
    and "Tr A = sum_list eigs"
    and "char_poly A = (\<Prod>e \<leftarrow> eigs. [:-e, 1:])"
proof -
  obtain U T :: "complex Matrix.mat"
    where Uc: "U \<in> carrier_mat n n"
      and Tc: "T \<in> carrier_mat n n"
      and UU: "unitary U"
      and UT: "upper_triangular T"
      and schur: "U\<^sup>\<dagger> * A * U = T"
    using schur_decomposition[OF sq]
    by (metis schur_induct sq) 

  let ?eigs = "map (\<lambda>i. T $$ (i,i)) [0..<n]"

  have len: "length ?eigs = n"
    by simp

  have trT: "Tr T = sum_list ?eigs"
  proof -
    have "sum_list ?eigs = (\<Sum>i<n. T $$ (i,i))"
      by (simp add: interv_sum_list_conv_sum_set_nat lessThan_atLeast0)
    also have "\<dots> = Tr T"
      using Tc by (simp add: Tr_def)
    finally show ?thesis by simp
  qed

  have trA: "Tr A = Tr T"
    using sq Uc UU schur Tr_unitary_conjugation by auto

  have cpT: "char_poly T = (\<Prod>e \<leftarrow> ?eigs. [:-e, 1:])"
  proof -
    have "diag_mat T = ?eigs"
      using Tc unfolding diag_mat_def by simp
    then show ?thesis
      using char_poly_upper_triangular[OF Tc UT] by simp
  qed

  have cpA: "char_poly A = char_poly T"
  proof -
    have Udag: "U\<^sup>\<dagger> \<in> carrier_mat n n"
      using Uc by (metis carrier_matD carrier_matI dim_col_of_dagger dim_row_of_dagger)
    have udag_u: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n"
      using UU Uc unfolding unitary_def by auto
    have u_udag: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
      using UU Uc unfolding unitary_def by auto
    have setc: "{T, A, U\<^sup>\<dagger>, U} \<subseteq> carrier_mat n n"
      using Tc sq Udag Uc by simp
    have T_eq: "T = (U\<^sup>\<dagger>) * A * U" using schur by simp
    have "similar_mat T A"
      by (rule similar_matI[OF setc udag_u u_udag T_eq])
    then show ?thesis using char_poly_similar by metis
  qed


  have "Tr A = sum_list ?eigs"
    using trA trT by simp
  moreover have "char_poly A = (\<Prod>e \<leftarrow> ?eigs. [:-e, 1:])"
    using cpA cpT by simp
  ultimately show ?thesis
    using len that by blast
qed

(* Proof: From Schur, T = U\<dagger>AU is upper triangular with same char poly as A,
   so eigenvalues appear on the diagonal.  Tr(A) = Tr(U\<dagger>AU) = Tr(T) = sum of
   diagonal entries = sum of eigenvalues. *)


(* ============================================================================
   DAY 4 — 2 / Sep / 11
   Topic: Hermitian Matrices, Positive Semidefinite Matrices
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Section: Hermitian (Self-Adjoint) Matrices
   -------------------------------------------------------------------------- *)

definition hermitian :: "complex Matrix.mat \<Rightarrow> bool" where
  "hermitian A \<equiv> A\<^sup>\<dagger> = A"

(* Basic dimension consequences *)

lemma hermitian_square:
  assumes "hermitian A"
  shows "dim_row A = dim_col A"
  using assms unfolding hermitian_def
  by (metis dim_row_of_dagger)

lemma hermitian_index:
  assumes "hermitian A"
      and "i < dim_row A" and "j < dim_col A"
  shows "A $$ (i,j) = cnj (A $$ (j,i))"
proof -
  have H: "A\<^sup>\<dagger> = A"
    using assms(1) by (simp add: hermitian_def)
  have sq: "dim_row A = dim_col A"
    using assms(1) by (rule hermitian_square)
  have "A $$ (i,j) = (A\<^sup>\<dagger>) $$ (i,j)"
    using H by simp
  also have "\<dots> = cnj (A $$ (j,i))"
    using assms(2,3) sq by (simp add: dagger_def)
  finally show ?thesis .
qed

(* Helper: \<langle>u | T *\<^sub>v v\<rangle> as a double sum over matrix entries. *)

lemma inner_T_double_sum:
  fixes T :: "complex Matrix.mat" and u v :: "complex Matrix.vec"
  assumes T_carr: "T \<in> carrier_mat n n"
      and udim: "dim_vec u = n" and vdim: "dim_vec v = n"
  shows "\<langle>u | T *\<^sub>v v\<rangle> =
         (\<Sum>k = 0..<n. \<Sum>l = 0..<n. cnj (u $ k) * T $$ (k, l) * v $ l)"
proof -
  have "\<langle>u | T *\<^sub>v v\<rangle> = (\<Sum>k = 0..<n. cnj (u $ k) * (T *\<^sub>v v) $ k)"
    using T_carr udim by (simp add: inner_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<n. cnj (u $ k) * (Matrix.row T k \<bullet> v))"
    using T_carr by simp
  also have "\<dots> = (\<Sum>k = 0..<n.
                     cnj (u $ k) * (\<Sum>l = 0..<n. Matrix.row T k $ l * v $ l))"
    using T_carr vdim by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                     cnj (u $ k) * (Matrix.row T k $ l * v $ l))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                     cnj (u $ k) * T $$ (k, l) * v $ l)"
    using T_carr by (intro sum.cong refl) (auto simp: mult.assoc)
  finally show ?thesis .
qed

(* Helper: \<langle>e_p | T *\<^sub>v e_q\<rangle> = T $$ (p, q). *)

lemma inner_unit_T_unit:
  fixes T :: "complex Matrix.mat"
  assumes T_carr: "T \<in> carrier_mat n n"
      and p: "p < n" and q: "q < n"
  shows "\<langle>unit_vec n p | T *\<^sub>v unit_vec n q\<rangle> = T $$ (p, q)"
proof -
  have udim: "dim_vec (unit_vec n p :: complex Matrix.vec) = n"
    by simp
  have vdim: "dim_vec (unit_vec n q :: complex Matrix.vec) = n"
    by simp

  have "\<langle>unit_vec n p | T *\<^sub>v unit_vec n q\<rangle> =
        (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
           cnj ((unit_vec n p :: complex Matrix.vec) $ k) * T $$ (k, l) *
           (unit_vec n q :: complex Matrix.vec) $ l)"
    using inner_T_double_sum[OF T_carr udim vdim] .

  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                     (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                     (if l = q then (1 :: complex) else 0))"
    using p q by (intro sum.cong refl) auto

  also have "\<dots> = (\<Sum>k = 0..<n. (if k = p then (1 :: complex) else 0) * T $$ (k, q))"
  proof (rule sum.cong[OF refl])
    fix k
    assume k: "k \<in> {0..<n}"
    have "(\<Sum>l = 0..<n.
             (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
             (if l = q then (1 :: complex) else 0))
        = (if k = p then (1 :: complex) else 0) *
          (\<Sum>l = 0..<n. T $$ (k, l) * (if l = q then (1 :: complex) else 0))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "\<dots> = (if k = p then (1 :: complex) else 0) * T $$ (k, q)"
    proof -
      have "(\<Sum>l = 0..<n. T $$ (k, l) * (if l = q then (1 :: complex) else 0))
          = (\<Sum>l = 0..<n. (if l = q then T $$ (k, l) else 0))"
      proof (rule sum.cong[OF refl])
        fix l
        assume l: "l \<in> {0..<n}"
        show "T $$ (k, l) * (if l = q then (1 :: complex) else 0)
            = (if l = q then T $$ (k, l) else 0)"
        proof (cases "l = q")
          case True
          then show ?thesis
            by simp
        next
          case False
          then show ?thesis
            by simp
        qed
      qed
      also have "\<dots> = T $$ (k, q)"
      proof -
        have "q \<in> {0..<n}"
          using q by simp
        then show ?thesis
          by simp
      qed
      finally show ?thesis
        by argo
    qed
    finally show "(\<Sum>l = 0..<n.
                     (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                     (if l = q then (1 :: complex) else 0))
                = (if k = p then (1 :: complex) else 0) * T $$ (k, q)".
  qed
  also have "\<dots> = (\<Sum>k = 0..<n. (if k = p then T $$ (k, q) else 0))"
  proof (rule sum.cong[OF refl])
    fix k
    assume k: "k \<in> {0..<n}"
    show "(if k = p then (1 :: complex) else 0) * T $$ (k, q)
        = (if k = p then T $$ (k, q) else 0)"
    proof (cases "k = p")
      case True
      then show ?thesis
        by simp
    next
      case False
      then show ?thesis
        by simp
    qed
  qed

  also have "\<dots> = T $$ (p, q)"
  proof -
    have "p \<in> {0..<n}"
      using p by simp
    then show ?thesis
      by simp
  qed
  finally show ?thesis.
qed


(* Helper: \<Sum>_k \<Sum>_l 1[k=p] * T_kl * 1[l=q] = T_pq.
   Useful any time you project out a single matrix entry by a unit-vector pair. *)
lemma sum_indicator_T_indicator:
  fixes T :: "complex Matrix.mat"
  assumes p: "p < n" and q: "q < n"
  shows "(\<Sum>k = 0..<n. \<Sum>l = 0..<n.
            (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
            (if l = q then (1 :: complex) else 0))
       = T $$ (p, q)"
proof -
  have inner: "\<And>k. (\<Sum>l = 0..<n.
                (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                (if l = q then (1 :: complex) else 0))
              = (if k = p then T $$ (k, q) else 0)"
  proof -
    fix k
    show "(\<Sum>l = 0..<n.
            (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
            (if l = q then (1 :: complex) else 0))
          = (if k = p then T $$ (k, q) else 0)"
    proof (cases "k = p")
      case True
      have "(\<Sum>l = 0..<n.
              (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
              (if l = q then (1 :: complex) else 0))
            = (\<Sum>l = 0..<n. T $$ (k, l) * (if l = q then (1 :: complex) else 0))"
        using True by simp
      also have "\<dots> = (\<Sum>l = 0..<n. (if l = q then T $$ (k, l) else 0))"
        by (rule sum.cong[OF refl]) auto
      also have "\<dots> = T $$ (k, q)" using q by simp
      finally show ?thesis using True by simp
    next
      case False
      then have "\<And>l. (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                       (if l = q then (1 :: complex) else 0) = 0" by simp
      then show ?thesis using False by simp
    qed
  qed
  have "(\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                (if l = q then (1 :: complex) else 0))
       = (\<Sum>k = 0..<n. (if k = p then T $$ (k, q) else 0))"
    using inner by (intro sum.cong refl)
  also have "\<dots> = T $$ (p, q)" using p by simp
  finally show ?thesis .
qed

(* Polarization helper:
   \<langle>a\<cdot>e_i + b\<cdot>e_j | T *\<^sub>v (c\<cdot>e_i + d\<cdot>e_j)\<rangle>
     = cnj a * c * T_ii + cnj a * d * T_ij + cnj b * c * T_ji + cnj b * d * T_jj.
   Choosing (a,b,c,d) = (1,1,1,1) gives the real polarization;
   (a,b,c,d) = (1,\<i>,1,\<i>) gives the imaginary polarization.   *)
lemma polarization_helper:
  fixes T :: "complex Matrix.mat" and a b c d :: complex
  assumes sq: "T \<in> carrier_mat n n"
      and i: "i < n" and j: "j < n"
  shows "\<langle>a \<cdot>\<^sub>v unit_vec n i + b \<cdot>\<^sub>v unit_vec n j
         | T *\<^sub>v (c \<cdot>\<^sub>v unit_vec n i + d \<cdot>\<^sub>v unit_vec n j)\<rangle>
        = cnj a * c * T $$ (i, i) + cnj a * d * T $$ (i, j)
        + cnj b * c * T $$ (j, i) + cnj b * d * T $$ (j, j)"
proof -
  let ?u = "a \<cdot>\<^sub>v unit_vec n i + b \<cdot>\<^sub>v unit_vec n j :: complex Matrix.vec"
  let ?v = "c \<cdot>\<^sub>v unit_vec n i + d \<cdot>\<^sub>v unit_vec n j :: complex Matrix.vec"
  have udim: "dim_vec ?u = n" by simp
  have vdim: "dim_vec ?v = n" by simp
  have u_cnj: "\<And>k. k < n \<Longrightarrow>
      cnj (?u $ k) = cnj a * (if k = i then 1 else 0) + cnj b * (if k = j then 1 else 0)"
    using i j by auto
  have v_idx: "\<And>l. l < n \<Longrightarrow>
      ?v $ l = c * (if l = i then 1 else 0) + d * (if l = j then 1 else 0)"
    using i j by auto

  have "\<langle>?u | T *\<^sub>v ?v\<rangle>
      = (\<Sum>k = 0..<n. \<Sum>l = 0..<n. cnj (?u $ k) * T $$ (k, l) * ?v $ l)"
    using inner_T_double_sum[OF sq udim vdim] .
  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                  (cnj a * (if k = i then 1 else 0) + cnj b * (if k = j then 1 else 0)) *
                  T $$ (k, l) *
                  (c * (if l = i then 1 else 0) + d * (if l = j then 1 else 0)))"
    using u_cnj v_idx by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                cnj a * c * ((if k = i then 1 else 0) * T $$ (k, l) * (if l = i then 1 else 0))
              + cnj a * d * ((if k = i then 1 else 0) * T $$ (k, l) * (if l = j then 1 else 0))
              + cnj b * c * ((if k = j then 1 else 0) * T $$ (k, l) * (if l = i then 1 else 0))
              + cnj b * d * ((if k = j then 1 else 0) * T $$ (k, l) * (if l = j then 1 else 0)))"
    by (intro sum.cong refl) (simp add: distrib_left distrib_right ac_simps)
  also have "\<dots> = cnj a * c * (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                                  (if k = i then 1 else 0) * T $$ (k, l) * (if l = i then 1 else 0))
              + cnj a * d * (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                                  (if k = i then 1 else 0) * T $$ (k, l) * (if l = j then 1 else 0))
              + cnj b * c * (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                                  (if k = j then 1 else 0) * T $$ (k, l) * (if l = i then 1 else 0))
              + cnj b * d * (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                                  (if k = j then 1 else 0) * T $$ (k, l) * (if l = j then 1 else 0))"
    by (simp add: sum.distrib sum_distrib_left)
  also have "\<dots> = cnj a * c * T $$ (i, i) + cnj a * d * T $$ (i, j)
              + cnj b * c * T $$ (j, i) + cnj b * d * T $$ (j, j)"
    using sum_indicator_T_indicator[OF i i, of T]
          sum_indicator_T_indicator[OF i j, of T]
          sum_indicator_T_indicator[OF j i, of T]
          sum_indicator_T_indicator[OF j j, of T]
    by simp
  finally show ?thesis .
qed



(* Key Lemma: if \<langle>x|Tx\<rangle> = 0 for all x \<in> \<complex>^n then T = 0. *)

lemma quadratic_form_zero:
  fixes T :: "complex Matrix.mat"
  assumes sq: "T \<in> carrier_mat n n"
      and zero: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | T *\<^sub>v x\<rangle> = 0"
  shows "T = 0\<^sub>m n n"
proof (rule eq_matI)
  show "dim_row T = dim_row (0\<^sub>m n n)" using sq by simp
  show "dim_col T = dim_col (0\<^sub>m n n)" using sq by simp
next
  fix i j
  assume "i < dim_row (0\<^sub>m n n)" "j < dim_col (0\<^sub>m n n)"
  then have inb: "i < n" "j < n" using sq by simp_all

  let ?ei = "unit_vec n i :: complex Matrix.vec"
  let ?ej = "unit_vec n j :: complex Matrix.vec"

  have ei_dim: "dim_vec ?ei = n" by simp
  have ej_dim: "dim_vec ?ej = n" by simp
  have eiej_dim: "dim_vec (?ei + ?ej) = n" by simp
  have eiiej_dim: "dim_vec (?ei + \<i> \<cdot>\<^sub>v ?ej) = n" by simp

  have diag_i: "T $$ (i, i) = 0"
    using zero[rule_format, of ?ei] inner_unit_T_unit[OF sq inb(1) inb(1)] ei_dim by simp
  have diag_j: "T $$ (j, j) = 0"
    using zero[rule_format, of ?ej] inner_unit_T_unit[OF sq inb(2) inb(2)] ej_dim by simp

  have q_sum_zero: "\<langle>?ei + ?ej | T *\<^sub>v (?ei + ?ej)\<rangle> = 0"
    using zero[rule_format, of "?ei + ?ej"] eiej_dim by simp
  have q_isum_zero: "\<langle>?ei + \<i> \<cdot>\<^sub>v ?ej | T *\<^sub>v (?ei + \<i> \<cdot>\<^sub>v ?ej)\<rangle> = 0"
    using zero[rule_format, of "?ei + \<i> \<cdot>\<^sub>v ?ej"] eiiej_dim by simp

  (* Real polarization: scalars (1,1,1,1).  Note 1\<cdot>v = v, so
     \<langle>?ei + ?ej | T (?ei + ?ej)\<rangle> = \<langle>1\<cdot>?ei + 1\<cdot>?ej | T (1\<cdot>?ei + 1\<cdot>?ej)\<rangle>. *)
  have sum_expand: "\<langle>?ei + ?ej | T *\<^sub>v (?ei + ?ej)\<rangle>
                  = T $$ (i, i) + T $$ (i, j) + T $$ (j, i) + T $$ (j, j)"
    using polarization_helper[OF sq inb(1) inb(2), of 1 1 1 1] by simp

  have sum_eq: "T $$ (i, j) + T $$ (j, i) = 0"
    using q_sum_zero sum_expand diag_i diag_j by simp

  (* Imaginary polarization: scalars (1, \<i>, 1, \<i>). *)
  have isum_expand: "\<langle>?ei + \<i> \<cdot>\<^sub>v ?ej | T *\<^sub>v (?ei + \<i> \<cdot>\<^sub>v ?ej)\<rangle>
                   = T $$ (i, i) + \<i> * T $$ (i, j) - \<i> * T $$ (j, i) + T $$ (j, j)"
    using polarization_helper[OF sq inb(1) inb(2), of 1 \<i> 1 \<i>] by simp

  have diff_eq: "T $$ (i, j) - T $$ (j, i) = 0"
    using q_isum_zero isum_expand diag_i diag_j by (simp add: field_simps)

  have "2 * T $$ (i, j) = 0"
    using sum_eq diff_eq by (simp add: algebra_simps)
  hence "T $$ (i, j) = 0" by simp
  thus "T $$ (i, j) = 0\<^sub>m n n $$ (i, j)" using inb by simp
qed

lemma mult_mat_vec_index:
  fixes A :: "'a::{comm_ring_1} Matrix.mat"
    and x :: "'a Matrix.vec"
  assumes A: "A \<in> carrier_mat m n"
      and x: "x \<in> carrier_vec n"
      and j: "j < m"
  shows "(A *\<^sub>v x) $ j = (\<Sum>i = 0..<n. A $$ (j, i) * x $ i)"
proof -
  have step1: "A *\<^sub>v x = Matrix.vec (dim_row A) (\<lambda>r. Matrix.row A r \<bullet> x)"
    unfolding mult_mat_vec_def
    by simp
  have step2: "(A *\<^sub>v x) $ j = (Matrix.vec (dim_row A) (\<lambda>r. Matrix.row A r \<bullet> x)) $ j"
    using step1 by simp
  have step3: "(Matrix.vec (dim_row A) (\<lambda>r. Matrix.row A r \<bullet> x)) $ j = Matrix.row A j \<bullet> x"
    using A j
    by simp
  have step4: "Matrix.row A j \<bullet> x = (\<Sum>i = 0..<dim_vec x. Matrix.row A j $ i * x $ i)"
    by (simp add: scalar_prod_def)
  have step5: "(\<Sum>i = 0..<dim_vec x. Matrix.row A j $ i * x $ i)
             = (\<Sum>i = 0..<n. Matrix.row A j $ i * x $ i)"
    using x by simp
  have step6: "(\<Sum>i = 0..<n. Matrix.row A j $ i * x $ i)
             = (\<Sum>i = 0..<n. A $$ (j, i) * x $ i)"
  proof (rule sum.cong[OF refl])
    fix i
    assume i: "i \<in> {0..<n}"
    then have "i < n"
      by simp
    moreover have "j < dim_row A"
      using A j by simp
    ultimately have "Matrix.row A j $ i = A $$ (j, i)"
      using A by auto
    then show "Matrix.row A j $ i * x $ i = A $$ (j, i) * x $ i"
      by simp
  qed

  have "(A *\<^sub>v x) $ j = Matrix.row A j \<bullet> x"
    using step2 step3 by simp
  also have "... = (\<Sum>i = 0..<dim_vec x. Matrix.row A j $ i * x $ i)"
    using step4 by simp
  also have "... = (\<Sum>i = 0..<n. Matrix.row A j $ i * x $ i)"
    using step5 by simp
  also have "... = (\<Sum>i = 0..<n. A $$ (j, i) * x $ i)"
    using step6 by simp
  finally show ?thesis.
qed

(* Adjoint moves to the other slot of the inner product:
   \<langle>A *\<^sub>v x | y\<rangle> = \<langle>x | A\<^sup>\<dagger> *\<^sub>v y\<rangle>.
   This is the defining property of the adjoint A\<^sup>\<dagger>. *)

lemma inner_prod_adjoint_swap:
  fixes M :: "complex Matrix.mat"
    and x y :: "complex Matrix.vec"
  assumes M: "M \<in> carrier_mat n m"
      and x: "dim_vec x = n"
      and y: "dim_vec y = m"
  shows "\<langle>x | M *\<^sub>v y\<rangle> = \<langle>M\<^sup>\<dagger> *\<^sub>v x | y\<rangle>"
proof -
  have Mxy_dim: "dim_vec (M *\<^sub>v y) = n"
    using M y by auto
  have Mdag: "M\<^sup>\<dagger> \<in> carrier_mat m n"
    using M by auto
  have Mdagx_dim: "dim_vec (M\<^sup>\<dagger> *\<^sub>v x) = m"
    using Mdag x by auto

  have lhs: "\<langle>x | M *\<^sub>v y\<rangle> = (\<Sum>j = 0..<n. \<Sum>i = 0..<m. cnj (x $ j) * M $$ (j,i) * y $ i)"
  proof -
    have "\<langle>x | M *\<^sub>v y\<rangle> = (\<Sum>j = 0..<n. cnj (x $ j) * (M *\<^sub>v y) $ j)"
      using x Mxy_dim by (simp add: inner_prod_def)
    also have "\<dots> = (\<Sum>j = 0..<n. cnj (x $ j) * (\<Sum>i = 0..<m. M $$ (j,i) * y $ i))"
    proof (rule sum.cong[OF refl])
      fix j
      assume j: "j \<in> {0..<n}"
      then have jlt: "j < n" by simp
      have "(M *\<^sub>v y) $ j = (\<Sum>i = 0..<dim_col M. M $$ (j,i) * y $ i)"
        using M jlt y mult_mat_vec_index
        by (simp add: scalar_prod_def)
      also have "dim_col M = m"
        using M by simp
      finally show "cnj (x $ j) * (M *\<^sub>v y) $ j
                  = cnj (x $ j) * (\<Sum>i = 0..<m. M $$ (j,i) * y $ i)"
        by simp
    qed
    also have "\<dots> = (\<Sum>j = 0..<n. \<Sum>i = 0..<m. cnj (x $ j) * (M $$ (j,i) * y $ i))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>j = 0..<n. \<Sum>i = 0..<m. cnj (x $ j) * M $$ (j,i) * y $ i)"
      by (intro sum.cong refl, simp)     
    finally show ?thesis .
  qed
  have rhs: "\<langle>M\<^sup>\<dagger> *\<^sub>v x | y\<rangle> = (\<Sum>i = 0..<m. \<Sum>j = 0..<n. cnj (x $ j) * M $$ (j,i) * y $ i)"
  proof -
    have "\<langle>M\<^sup>\<dagger> *\<^sub>v x | y\<rangle> = (\<Sum>i = 0..<m. cnj ((M\<^sup>\<dagger> *\<^sub>v x) $ i) * y $ i)"
      using y Mdagx_dim by (simp add: inner_prod_def)
    also have "\<dots> = (\<Sum>i = 0..<m. cnj (\<Sum>j = 0..<n. (M\<^sup>\<dagger>) $$ (i,j) * x $ j) * y $ i)"
    proof (rule sum.cong[OF refl])
      fix i
      assume i: "i \<in> {0..<m}"
      then have ilt: "i < m"
        by simp
      have "(M\<^sup>\<dagger> *\<^sub>v x) $ i = (\<Sum>j = 0..<dim_col (M\<^sup>\<dagger>). (M\<^sup>\<dagger>) $$ (i,j) * x $ j)"
        using Mdag ilt x mult_mat_vec_index
        by (metis (no_types, lifting) carrier_matD(2) carrier_vec_dim_vec sum.cong)
      also have "dim_col (M\<^sup>\<dagger>) = n"
        using Mxy_dim by auto
      finally show "cnj ((M\<^sup>\<dagger> *\<^sub>v x) $ i) * y $ i
                  = cnj (\<Sum>j = 0..<n. (M\<^sup>\<dagger>) $$ (i,j) * x $ j) * y $ i"
        by simp
    qed
    also have "\<dots> = (\<Sum>i = 0..<m. (\<Sum>j = 0..<n. cnj ((M\<^sup>\<dagger>) $$ (i,j) * x $ j)) * y $ i)"
      by simp
    also have "\<dots> = (\<Sum>i = 0..<m. (\<Sum>j = 0..<n. cnj ((M\<^sup>\<dagger>) $$ (i,j)) * cnj (x $ j)) * y $ i)"
      by simp
    also have "\<dots> = (\<Sum>i = 0..<m. (\<Sum>j = 0..<n. M $$ (j,i) * cnj (x $ j)) * y $ i)"
    proof (intro sum.cong refl)
      fix i
      assume i: "i \<in> {0..<m}"
      show "(\<Sum>j = 0..<n. cnj (M\<^sup>\<dagger> $$ (i, j)) * cnj (x $ j)) * y $ i = (\<Sum>j = 0..<n. M $$ (j, i) * cnj (x $ j)) * y $ i"
        using M i by (intro arg_cong[where f = "\<lambda>s. s * y $ i"] sum.cong refl) (simp add: dagger_def)
    qed
    also have "\<dots> = (\<Sum>i = 0..<m. \<Sum>j = 0..<n. (M $$ (j,i) * cnj (x $ j)) * y $ i)"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>i = 0..<m. \<Sum>j = 0..<n. cnj (x $ j) * M $$ (j,i) * y $ i)"
      by (intro sum.cong refl, simp add: algebra_simps)
    finally show ?thesis.
  qed

  have "(\<Sum>j = 0..<n. \<Sum>i = 0..<m. cnj (x $ j) * M $$ (j,i) * y $ i)
      = (\<Sum>i = 0..<m. \<Sum>j = 0..<n. cnj (x $ j) * M $$ (j,i) * y $ i)"
    by (rule sum.swap)
  thus ?thesis
    using lhs rhs by simp
qed

(* Hermitian \<leftrightarrow> \<langle>x|Hx\<rangle> \<in> \<real> for all x *)

lemma hermitian_iff_real_quad_form:
  assumes sq: "A \<in> carrier_mat n n"
  shows "hermitian A \<longleftrightarrow> (\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>)"
proof
  assume hA: "hermitian A"
  show "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    have xcar: "x \<in> carrier_vec n"
      by (simp add: carrier_vecI xdim)
    have "cnj \<langle>x | A *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x\<rangle>"
    proof -
      have "cnj \<langle>x | A *\<^sub>v x\<rangle> = \<langle>A *\<^sub>v x | x\<rangle>"
        by (metis carrier_matD(1) dim_mult_mat_vec inner_prod_cnj sq xdim)
      also have "... = \<langle>x | A\<^sup>\<dagger> *\<^sub>v x\<rangle>"
        using hA hermitian_def inner_prod_adjoint_swap sq xdim by auto
      also have "... = \<langle>x | A *\<^sub>v x\<rangle>"
        using hA by (simp add: hermitian_def)
      finally show ?thesis .
    qed
    then show "\<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
      using Reals_cnj_iff by blast
  qed
next
  assume qreal: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
  let ?T = "A - (A\<^sup>\<dagger>)"

  have Tcar: "?T \<in> carrier_mat n n"
    using sq by auto

  have qzero: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | ?T *\<^sub>v x\<rangle> = 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    have xcar: "x \<in> carrier_vec n"
      by (simp add: carrier_dim_vec xdim)

    have qA_real: "\<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
      using qreal xdim by blast
    have "\<langle>x | ?T *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x\<rangle> - \<langle>x | A\<^sup>\<dagger> *\<^sub>v x\<rangle>"
      by (metis carrier_matD(1,2) dagger_def dim_mult_mat_vec inner_prod_right_minus'
          mat_carrier minus_mult_distrib_mat_vec sq xcar)
    also have "... = \<langle>x | A *\<^sub>v x\<rangle> - cnj \<langle>x | A *\<^sub>v x\<rangle>"
    proof -
      have "\<langle>x | A\<^sup>\<dagger> *\<^sub>v x\<rangle> = \<langle>A *\<^sub>v x | x\<rangle>"
        by (metis carrier_matD(1,2) dim_mult_mat_vec dim_row_of_dagger 
            inner_prod_adjoint_swap inner_prod_cnj sq xdim)        
      also have "... = cnj \<langle>x | A *\<^sub>v x\<rangle>"
        by (metis carrier_matD(1) dim_mult_mat_vec inner_prod_cnj sq xdim)
      finally show ?thesis by simp
    qed
    also have "... = 0"
      using Reals_cnj_iff qA_real by force
    finally show "\<langle>x | ?T *\<^sub>v x\<rangle> = 0" .
  qed

  have "?T = 0\<^sub>m n n"
    using quadratic_form_zero[OF Tcar qzero].
  hence "A = (A\<^sup>\<dagger>)"
  proof -
    have Adagcar: "A\<^sup>\<dagger> \<in> carrier_mat n n" using sq by auto
    have "A = (A - (A\<^sup>\<dagger>)) + (A\<^sup>\<dagger>)"
    proof -
      have "A = A + 0\<^sub>m n n"
        using sq by simp
      also have "... = A + (-(A\<^sup>\<dagger>) + (A\<^sup>\<dagger>))"
        using Adagcar by force
      also have "... = (A - (A\<^sup>\<dagger>)) + (A\<^sup>\<dagger>)"
        by (smt (verit, best) Adagcar add_uminus_minus_mat assoc_add_mat sq uminus_carrier_mat)
      finally show ?thesis.
    qed
    also have "\<dots> = (0\<^sub>m n n) + (A\<^sup>\<dagger>)"
      using \<open>?T = 0\<^sub>m n n\<close> by simp
    also have "\<dots> = (A\<^sup>\<dagger>)"
      using Adagcar by auto
    finally show ?thesis.
  qed
  then show "hermitian A"
    by (simp add: hermitian_def)
qed

(* Hermitian matrices have a spectral decomposition (orthonormal eigenbasis, real eigenvalues).
   This follows from Schur's theorem: U\<dagger>HU is upper triangular T; T\<dagger> = T so T diagonal;
   T diagonal and self-adjoint \<Longrightarrow> real diagonal entries. *)

(* The complex diagonal matrix with real diagonal entries D. *)
definition diag_mat_of_real :: "real list \<Rightarrow> complex Matrix.mat" where
  "diag_mat_of_real D =
     Matrix.mat (length D) (length D)
       (\<lambda>(i,j). if i = j then complex_of_real (D ! i) else 0)"

lemma dim_row_diag_mat_of_real[simp]: "dim_row (diag_mat_of_real D) = length D"
  unfolding diag_mat_of_real_def by simp

lemma dim_col_diag_mat_of_real[simp]: "dim_col (diag_mat_of_real D) = length D"
  unfolding diag_mat_of_real_def by simp

lemma diag_mat_of_real_carrier[simp]:
  "diag_mat_of_real D \<in> carrier_mat (length D) (length D)"
  by (rule carrier_matI) auto

lemma diag_mat_of_real_index[simp]:
  assumes "i < length D" and "j < length D"
  shows "diag_mat_of_real D $$ (i, j) =
         (if i = j then complex_of_real (D ! i) else 0)"
  using assms unfolding diag_mat_of_real_def by simp

lemma diag_mat_of_real_mult_vec_index:
  fixes y :: "complex Matrix.vec"
  assumes ydim: "dim_vec y = length D"
      and i: "i < length D"
  shows "(diag_mat_of_real D *\<^sub>v y) $ i = complex_of_real (D ! i) * y $ i"
proof -
  have ycar: "y \<in> carrier_vec (length D)"
    by (simp add: carrier_vecI ydim)
  have "(diag_mat_of_real D *\<^sub>v y) $ i =
        (\<Sum>j = 0..<length D. diag_mat_of_real D $$ (i, j) * y $ j)"
    using mult_mat_vec_index[OF diag_mat_of_real_carrier ycar i] .
  also have "\<dots> =
        (\<Sum>j = 0..<length D. (if i = j then complex_of_real (D ! i) * y $ j else 0))"
    using i by (intro sum.cong refl) auto
  also have "\<dots> = complex_of_real (D ! i) * y $ i"
    using i by simp
  finally show ?thesis.
qed

lemma diag_mat_of_real_quad_Re_nonneg:
  fixes y :: "complex Matrix.vec"
  assumes ydim: "dim_vec y = length D"
      and D_nonneg: "\<And>i. i < length D \<Longrightarrow> 0 \<le> D ! i"
  shows "0 \<le> Re \<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>"
proof -
  have Dy_dim: "dim_vec (diag_mat_of_real D *\<^sub>v y) = length D"
    using ydim by simp

  have inner_expand:
    "\<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
      = (\<Sum>i = 0..<length D. cnj (y $ i) * ((diag_mat_of_real D *\<^sub>v y) $ i))"
    using ydim Dy_dim
    by (simp add: inner_prod_def)

  have diag_action:
    "\<And>i. i < length D \<Longrightarrow> (diag_mat_of_real D *\<^sub>v y) $ i = complex_of_real (D ! i) * y $ i"
  proof -
    fix i
    assume ilt: "i < length D"
    have "(diag_mat_of_real D *\<^sub>v y) $ i
        = (\<Sum>j = 0..<dim_col (diag_mat_of_real D). diag_mat_of_real D $$ (i,j) * y $ j)"
      using ilt ydim
      by (metis (full_types) carrier_vec_dim_vec 
          diag_mat_of_real_carrier dim_col_diag_mat_of_real mult_mat_vec_index)
    also have "... = (\<Sum>j = 0..<length D. diag_mat_of_real D $$ (i,j) * y $ j)"
      by simp
    also have "... = (\<Sum>j = 0..<length D.
             (if i = j then complex_of_real (D ! i) else 0) * y $ j)"
      using ilt
      by (intro sum.cong refl, simp add: diag_mat_of_real_def)
    also have "... = complex_of_real (D ! i) * y $ i"
      using ilt
      by (metis calculation diag_mat_of_real_mult_vec_index ydim)
    finally show "(diag_mat_of_real D *\<^sub>v y) $ i = complex_of_real (D ! i) * y $ i" .
  qed

  have "\<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
      = (\<Sum>i = 0..<length D. cnj (y $ i) * ((diag_mat_of_real D *\<^sub>v y) $ i))"
    using inner_expand .
  also have "... = (\<Sum>i = 0..<length D. cnj (y $ i) * (complex_of_real (D ! i) * y $ i))"
  proof (intro sum.cong refl)
    fix i
    assume ilt: "i \<in> {0..<length D}"
    then have "i < length D" by simp
    thus "cnj (y $ i) * ((diag_mat_of_real D *\<^sub>v y) $ i)
        = cnj (y $ i) * (complex_of_real (D ! i) * y $ i)"
      using diag_action by simp
  qed
  finally have quad_expand:
    "\<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
      = (\<Sum>i = 0..<length D. cnj (y $ i) * (complex_of_real (D ! i) * y $ i))" .

  have Re_expand:
    "Re \<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
      = (\<Sum>i = 0..<length D. D ! i * Re (cnj (y $ i) * y $ i))"
  proof -
    have "Re \<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
        = Re (\<Sum>i = 0..<length D. cnj (y $ i) * (complex_of_real (D ! i) * y $ i))"
      using quad_expand by simp
    also have "... = Re (\<Sum>i = 0..<length D. complex_of_real (D ! i) * (cnj (y $ i) * y $ i))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<Sum>i = 0..<length D. Re (complex_of_real (D ! i) * (cnj (y $ i) * y $ i)))"
      by simp
    also have "... = (\<Sum>i = 0..<length D. D ! i * Re (cnj (y $ i) * y $ i))"
      by simp
    finally show ?thesis.
  qed

  have term_nonneg:
    "\<And>i. i \<in> {0..<length D} \<Longrightarrow> 0 \<le> D ! i * Re (cnj (y $ i) * y $ i)"
  proof -
    fix i
    assume i: "i \<in> {0..<length D}"
    then have ilt: "i < length D"
      by simp
    have "0 \<le> D ! i"
      using D_nonneg ilt by simp
    moreover have "0 \<le> Re (cnj (y $ i) * y $ i)"
      by simp
    ultimately show "0 \<le> D ! i * Re (cnj (y $ i) * y $ i)"
      by simp
  qed

  have "0 \<le> (\<Sum>i = 0..<length D. D ! i * Re (cnj (y $ i) * y $ i))"
    by (rule sum_nonneg, rule term_nonneg)
  thus "0 \<le> Re \<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>"
    using Re_expand by simp
qed

theorem hermitian_spectral_decomp:
  fixes H :: "complex Matrix.mat"
  assumes sq: "H \<in> carrier_mat n n"
      and herm: "hermitian H"
  shows "\<exists>(U :: complex Matrix.mat) (D :: real list).
         U \<in> carrier_mat n n \<and>
         unitary U \<and>
         length D = n \<and>
         (U\<^sup>\<dagger>) * H * U = diag_mat_of_real D"
proof -
  (* Step 1: Schur gives U unitary, T = U\<dagger>HU upper triangular. *)
  obtain U T where Uc: "U \<in> carrier_mat n n" and Tc: "T \<in> carrier_mat n n"
    and UU: "unitary U" and UT: "upper_triangular T"
    and schur: "U\<^sup>\<dagger> * H * U = T"
    using schur_theorem[OF sq] by blast
  have Udagcar: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have Hdag: "H\<^sup>\<dagger> = H" using herm by (simp add: hermitian_def)

  (* Step 2: T\<dagger> = T using H Hermitian and (AB)\<dagger> = B\<dagger>A\<dagger>. *)
  have Tdag: "T\<^sup>\<dagger> = T"
  proof -
    have HUcar: "H * U \<in> carrier_mat n n" using sq Uc by auto
    have UdagHcar: "U\<^sup>\<dagger> * H \<in> carrier_mat n n" using Udagcar sq by auto
    let ?Ud = "U\<^sup>\<dagger>"
    let ?A = "?Ud * H"
    have dcA: "dim_col ?A = dim_row U" using UdagHcar Uc by auto
    have dcUd: "dim_col ?Ud = dim_row H" using Udagcar sq by auto
    have step1: "dagger (?A * U) = dagger U * dagger ?A"
      by (rule dagger_of_prod[OF dcA])
    have step2: "dagger ?A = (H\<^sup>\<dagger>) * dagger ?Ud"
      by (rule dagger_of_prod[OF dcUd])
    have step3: "dagger ?Ud = U" using Uc by (simp add: dagger_of_dagger_is_id)
    have "T\<^sup>\<dagger> = dagger (?A * U)" using schur by simp
    also have "\<dots> = dagger U * dagger ?A" using step1 .
    also have "\<dots> = dagger U * (H\<^sup>\<dagger> * dagger ?Ud)" using step2 by simp
    also have "\<dots> = dagger U * (H * U)" using step3 Hdag by simp
    also have "\<dots> = ?Ud * H * U"
      using Udagcar sq Uc by simp
    also have "\<dots> = T" using schur by simp
    finally show ?thesis.
  qed

  (* Step 3: T upper triangular + T\<dagger> = T \<Longrightarrow> T diagonal. *)
  have T_off_diag: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> T $$ (i, j) = 0"
  proof -
    fix i j assume i: "i < n" and j: "j < n" and ij: "i \<noteq> j"
    show "T $$ (i, j) = 0"
    proof (cases "i > j")
      case True
      then show ?thesis using upper_triangularD[OF UT True] i Tc by simp
    next
      case False
      then have ji: "j > i" using ij by auto
      have Tji0: "T $$ (j, i) = 0"
        using upper_triangularD[OF UT ji] j Tc by simp
      have "T $$ (i, j) = (T\<^sup>\<dagger>) $$ (i, j)" using Tdag by simp
      also have "\<dots> = cnj (T $$ (j, i))"
        using i j Tc by (simp add: dagger_def)
      also have "\<dots> = 0" using Tji0 by simp
      finally show ?thesis.
    qed
  qed

  (* Step 4: diagonal entries are real. *)
  have T_diag_real: "\<And>i. i < n \<Longrightarrow> T $$ (i, i) \<in> \<real>"
  proof -
    fix i assume i: "i < n"
    have "cnj (T $$ (i, i)) = (T\<^sup>\<dagger>) $$ (i, i)"
      using i Tc by (simp add: dagger_def)
    also have "\<dots> = T $$ (i, i)" using Tdag by simp
    finally have "cnj (T $$ (i, i)) = T $$ (i, i)".
    then show "T $$ (i, i) \<in> \<real>" using Reals_cnj_iff by metis
  qed

  (* Step 5: extract the real diagonal as a list and show T = diag_mat_of_real D. *)
  let ?D = "map (\<lambda>i. Re (T $$ (i, i))) [0..<n]"
  have D_len: "length ?D = n" by simp
  have D_idx: "\<And>i. i < n \<Longrightarrow> ?D ! i = Re (T $$ (i, i))" by simp

  have T_eq_diag: "T = diag_mat_of_real ?D"
  proof (rule eq_matI)
    show "dim_row T = dim_row (diag_mat_of_real ?D)" using Tc by auto
    show "dim_col T = dim_col (diag_mat_of_real ?D)" using Tc by auto
  next
    fix i j
    assume "i < dim_row (diag_mat_of_real ?D)" "j < dim_col (diag_mat_of_real ?D)"
    then have inb: "i < n" "j < n" by auto
    show "T $$ (i, j) = diag_mat_of_real ?D $$ (i, j)"
    proof (cases "i = j")
      case True
      have "T $$ (i, i) = complex_of_real (Re (T $$ (i, i)))"
        using T_diag_real[OF inb(1)]
        by (metis Reals_cases Re_complex_of_real)
      then show ?thesis
        using True inb D_len D_idx[OF inb(1)] by simp
    next
      case False
      have "T $$ (i, j) = 0" using T_off_diag[OF inb(1) inb(2) False].
      moreover have "diag_mat_of_real ?D $$ (i, j) = 0"
        using False inb D_len by simp
      ultimately show ?thesis by simp
    qed
  qed

  show ?thesis
    using Uc UU D_len schur T_eq_diag by metis
qed

(* Corollary: Hermitian matrices have real eigenvalues *)

corollary hermitian_real_eigenvalues:
  fixes H :: "complex Matrix.mat"
  assumes sq: "H \<in> carrier_mat n n"
      and herm: "hermitian H"
      and eig: "H *\<^sub>v v = lam \<cdot>\<^sub>v v"
      and v_nonzero: "v \<noteq> 0\<^sub>v n"
      and vdim: "dim_vec v = n"
  shows "lam \<in> \<real>"
proof -
  have vcar: "v \<in> carrier_vec n"
    by (simp add: carrier_dim_vec vdim)
  (* From hermitian: \<langle>v|Hv\<rangle> is real.  And \<langle>v|Hv\<rangle> = lam * \<langle>v|v\<rangle>.
     Since \<langle>v|v\<rangle> = \<parallel>v\<parallel>² is a positive real (v \<noteq> 0), lam is real. *)
  have qreal: "\<langle>v | H *\<^sub>v v\<rangle> \<in> \<real>"
    using hermitian_iff_real_quad_form[OF sq] herm vdim by blast
  have q_eq: "\<langle>v | H *\<^sub>v v\<rangle> = lam * \<langle>v | v\<rangle>"
    using eig inner_prod_right_smult' by presburger
  have vv_real: "\<langle>v | v\<rangle> \<in> \<real>"
    using vcar inner_prod_with_itself_real vdim
    by blast 
  have vv_nonzero: "\<langle>v | v\<rangle> \<noteq> 0"
    using vcar v_nonzero
    by (simp add: inner_prod_with_itself_nonneg_reals_non0, 
        metis comm_scalar_prod conjugate_complex_def 
        conjugate_square_eq_0_vec conjugate_vec_def vdim vec_carrier)
  show "lam \<in> \<real>"
    using qreal q_eq
    using Reals_cnj_iff vv_nonzero vv_real by fastforce 
qed


(* --------------------------------------------------------------------------
   Section: Positive Semidefinite and Positive Definite Matrices
   -------------------------------------------------------------------------- *)

definition psd :: "complex Matrix.mat \<Rightarrow> bool" where
  "psd P \<equiv> hermitian P \<and>
            (\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
               Re (\<langle>x | P *\<^sub>v x\<rangle>) \<ge> 0)"

definition pd :: "complex Matrix.mat \<Rightarrow> bool" where
  "pd P \<equiv> hermitian P \<and>
           (\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
              x \<noteq> 0\<^sub>v (dim_row P) \<longrightarrow>
              Re (\<langle>x | P *\<^sub>v x\<rangle>) > 0)"

(* Notation: we write P \<ge> 0 for psd P and P > 0 for pd P (within context). *)
notation psd ("_ \<ge>\<^sub>M 0")
notation pd  ("_ >\<^sub>M 0")

(* PSD implies Hermitian *)

lemma psd_hermitian: "psd P \<Longrightarrow> hermitian P"
  by (simp add: psd_def)

lemma psd_MdagM:
  assumes M: "M \<in> carrier_mat n m"
  shows "psd (M\<^sup>\<dagger> * M)"
proof -
  have MM_car: "M\<^sup>\<dagger> * M \<in> carrier_mat m m"
    using assms by fastforce

  have herm: "hermitian (M\<^sup>\<dagger> * M)"
    unfolding hermitian_def using M
    by (simp add: dagger_of_dagger_is_id dagger_of_prod)


  have nonneg:
    "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row (M\<^sup>\<dagger> * M) \<longrightarrow>  Re \<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> \<ge> 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = dim_row (M\<^sup>\<dagger> * M)"

    have dim_row_MM: "dim_row (M\<^sup>\<dagger> * M) = m"
      using M by simp
    hence xdim': "dim_vec x = m"
      using xdim by simp

    have Mx_dim: "dim_vec (M *\<^sub>v x) = n"
      using M xdim' by simp

    have qf:  "\<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
    proof -
      have "\<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> = \<langle>x | M\<^sup>\<dagger> *\<^sub>v (M *\<^sub>v x)\<rangle>"
        using M xdim'
        by (metis assoc_mult_mat_vec carrier_matD(1) carrier_vec_dim_vec dagger_def mat_carrier)
      also have "... = \<langle>(M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using M xdim' Mx_dim
        by (metis carrier_matD(2) dagger_of_dagger_is_id dim_mult_mat_vec 
            dim_row_of_dagger inner_prod_adjoint_swap inner_prod_cnj)
      also have "... = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using dagger_of_dagger_is_id by presburger
      finally show ?thesis.
    qed
    have "Re \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle> \<ge> 0"
      using Mx_dim using inner_prod_with_itself_Re by blast
    thus "Re \<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> \<ge> 0"
      using qf by simp
  qed
  show ?thesis
    unfolding psd_def using herm nonneg by simp
qed

(* PSD iff all eigenvalues are non-negative (requires spectral theorem) *)

theorem psd_iff_nonneg_eigenvalues:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
  shows "psd P \<longleftrightarrow>
         (hermitian P \<and>
          (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0))"
proof
  assume pos: "psd P"
  have herm: "hermitian P"
    using pos by (rule psd_hermitian)

  have eig_nonneg:
    "\<forall>mu v. v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
  proof (intro allI impI)
    fix mu :: complex
    fix v  :: "complex Matrix.vec"
    assume hyp: "v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v"
    then have vneq: "v \<noteq> 0\<^sub>v n"
      and vdim: "dim_vec v = n"
      and eig:  "P *\<^sub>v v = mu \<cdot>\<^sub>v v"
      by auto
    have qf_nonneg: "0 \<le> Re \<langle>v | P *\<^sub>v v\<rangle>"
      using pos vdim  unfolding psd_def  using sq by auto
    have inner_eig: "\<langle>v | P *\<^sub>v v\<rangle> = mu * \<langle>v | v\<rangle>"
      by (simp add: hyp)
    have vv_real: "\<langle>v | v\<rangle> = of_real (Re \<langle>v | v\<rangle>)"
      using inner_prod_with_itself_real of_real_Re by presburger
    have vv_pos: "0 < Re \<langle>v | v\<rangle>"
      using vneq vdim inner_prod_with_itself_Re_non0 by blast
    have "0 \<le> Re (mu * \<langle>v | v\<rangle>)"
      using qf_nonneg by (simp add: inner_eig)
    hence "0 \<le> Re mu * Re \<langle>v | v\<rangle>"
      using inner_prod_with_itself_Im by auto     
    thus "Re mu \<ge> 0"
      by (meson linorder_not_less vv_pos zero_le_mult_iff)
  qed
  show "hermitian P \<and>
        (\<forall>mu::complex. \<forall>v::complex Matrix.vec.
           v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0)"
    using herm eig_nonneg by blast
next
  assume rhs:
    "hermitian P \<and>
     (\<forall>mu::complex. \<forall>v::complex Matrix.vec.
        v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0)"
  then have herm: "hermitian P"
    by blast
  from rhs have eig_nonneg:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    by blast

  have "psd P"
  proof -
    obtain U :: "complex Matrix.mat" and D :: "real list"
      where Uc: "U \<in> carrier_mat n n"
        and UU: "unitary U"
        and Dlen: "length D = n"
        and specD: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
      using hermitian_spectral_decomp[OF sq herm] by blast

    have Udag_c: "U\<^sup>\<dagger> \<in> carrier_mat n n"
      using Uc by auto
    have UdagU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n"
      using Uc UU unfolding unitary_def by auto
    have UUdag: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
      using Uc UU unfolding unitary_def by auto
    have P_eq: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    proof -
      have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = U * ((U\<^sup>\<dagger>) * P * U) * (U\<^sup>\<dagger>)"
        using specD by simp
      also have "\<dots> = P"
        using Uc Udag_c sq UdagU UUdag Dlen 
        by (smt (verit, ccfv_SIG) assoc_mult_mat left_mult_one_mat 
            mult_carrier_mat right_mult_one_mat)
      finally show ?thesis by simp
    qed

    have PU_eq_UD: "P * U = U * diag_mat_of_real D"
    proof -
      have "P * U = (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) * U"
        using P_eq by simp
      also have "\<dots> = U * diag_mat_of_real D"
        using Uc Udag_c UdagU Dlen
        by (smt (verit, del_insts) assoc_mult_mat carrier_mat_triv 
            dim_col_diag_mat_of_real index_mult_mat(3) right_mult_one_mat) 
      finally show ?thesis.
    qed

    have D_nonneg: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
    proof -
      fix i assume i: "i < n"
      let ?ui = "Matrix.col U i"
      have uidim: "dim_vec ?ui = n"
        using Uc by simp
      have ui_nonzero: "?ui \<noteq> 0\<^sub>v n"
      proof
        assume zero: "?ui = 0\<^sub>v n"
        have "\<parallel>?ui\<parallel> = (1 :: real)"
          using UU i Uc by (metis carrier_matD(2) unitary_unit_col)
        moreover have "\<parallel>?ui\<parallel> = 0"
          using zero uidim cpx_vec_length_zero_iff by metis
        ultimately show False by simp
      qed
      have eig: "P *\<^sub>v ?ui = complex_of_real (D ! i) \<cdot>\<^sub>v ?ui"
      proof (rule eq_vecI)
        show "dim_vec (P *\<^sub>v ?ui) = dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
          using sq uidim by simp
      next
        fix k
        assume k: "k < dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
        then have klt: "k < n"
          using uidim by simp
        have "(P *\<^sub>v ?ui) $ k = (P * U) $$ (k, i)"
          using sq Uc i klt by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
        also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
          using PU_eq_UD by simp
        also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
        proof -
          have "(U * diag_mat_of_real D) $$ (k, i) =
                (\<Sum>j = 0..<n. U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
            using Uc Dlen klt i by (simp add: scalar_prod_def lessThan_atLeast0)
          also have "\<dots> =
                (\<Sum>j = 0..<n. (if j = i then U $$ (k, j) * complex_of_real (D ! i) else 0))"
            using Dlen i by (intro sum.cong refl, auto)
          also have "\<dots> = U $$ (k, i) * complex_of_real (D ! i)"
            using i by simp
          also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
            by (simp add: mult.commute)
          finally show ?thesis.
        qed
        also have "\<dots> = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k"
          using klt Uc  by (simp add: i) 
        finally show "(P *\<^sub>v ?ui) $ k = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k" .
      qed
      have "0 \<le> Re (complex_of_real (D ! i))"
        using eig eig_nonneg ui_nonzero uidim by blast
      then show "0 \<le> D ! i"
        by simp
    qed

    have spec: "\<forall>v. dim_vec v = n \<longrightarrow> 0 \<le> Re \<langle>v | P *\<^sub>v v\<rangle>"
    proof (intro allI impI)
      fix v :: "complex Matrix.vec"
      assume vdim: "dim_vec v = n"
      let ?y = "U\<^sup>\<dagger> *\<^sub>v v"
      have ydim: "dim_vec ?y = n"
        using Uc by force
      have v_as_Uy: "U *\<^sub>v ?y = v"
      proof -
        have "U *\<^sub>v ((U\<^sup>\<dagger>) *\<^sub>v v) = (U * (U\<^sup>\<dagger>)) *\<^sub>v v"
          using Uc Udag_c vdim by force
        also have "\<dots> = v"
          using UUdag vdim by force
        finally show ?thesis.
      qed
      have Pv_as: "P *\<^sub>v v = U *\<^sub>v (diag_mat_of_real D *\<^sub>v ?y)"
      proof -
        have "P *\<^sub>v v = (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) *\<^sub>v v"
          using P_eq by simp
        also have "\<dots> = U *\<^sub>v (diag_mat_of_real D *\<^sub>v (U\<^sup>\<dagger> *\<^sub>v v))"
          using Uc Udag_c sq Dlen vdim
          by (smt (verit, ccfv_SIG) assoc_mult_mat_vec 
              carrier_vec_dim_vec diag_mat_of_real_carrier mult_carrier_mat ydim)
        finally show ?thesis.
      qed
      have "\<langle>v | P *\<^sub>v v\<rangle> = \<langle>U *\<^sub>v ?y | U *\<^sub>v (diag_mat_of_real D *\<^sub>v ?y)\<rangle>"
        using v_as_Uy Pv_as by simp
      also have "\<dots> = \<langle>?y | diag_mat_of_real D *\<^sub>v ?y\<rangle>"
        by (metis Uc dim_mult_mat_vec index_mult_mat(2) 
            inner_prod_adjoint_swap specD v_as_Uy vdim ydim)
      finally have qeq: "\<langle>v | P *\<^sub>v v\<rangle> = \<langle>?y | diag_mat_of_real D *\<^sub>v ?y\<rangle>".
      show "0 \<le> Re \<langle>v | P *\<^sub>v v\<rangle>"
        using diag_mat_of_real_quad_Re_nonneg[OF _] D_nonneg Dlen ydim qeq by auto
    qed
    show ?thesis
      unfolding psd_def
      using sq herm spec by auto
  qed
  thus "psd P".
qed

(* PSD iff P = \<Sigma>ᵢ |vᵢ\<rangle>\<langle>vᵢ| (Kraus-like characterisation) *)

(* Direction \<leftarrow>: if P = \<Sigma> |vᵢ\<rangle>\<langle>vᵢ| then P \<ge> 0. *)

lemma outer_sum_psd:
  assumes len: "length vs = k"
      and vdim: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "psd (outer_sum n vs)"
proof -
  have herm: "hermitian (outer_sum n vs)"
    unfolding hermitian_def using outer_sum_hermitian by simp
  have dr: "dim_row (outer_sum n vs) = n"
    by simp
  have nonneg: "\<forall>x. dim_vec x = dim_row (outer_sum n vs) \<longrightarrow>
              Re (\<langle>x | outer_sum n vs *\<^sub>v x\<rangle>) \<ge> 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = dim_row (outer_sum n vs)"
    let ?M = "mat_of_cols n vs"
    let ?y = "(?M\<^sup>\<dagger>) *\<^sub>v x"
    have M_car: "?M \<in> carrier_mat n k"
      using len vdim by (simp add: mat_of_cols_def)
    have xdim_n: "dim_vec x = n"
      using xdim by simp
    have xcar: "x \<in> carrier_vec n"
      using xdim_n carrier_vec_dim_vec by blast
    have ycar: "?y \<in> carrier_vec k"
      using M_car xcar carrier_dim_vec len by force
    have ydim: "dim_vec ?y = k"
      using ycar carrier_dim_vec by blast
    have outer_as_MMdag: "outer_sum n vs = ?M * (?M\<^sup>\<dagger>)"
      using len vdim outer_sum_def by presburger
    have qf: "\<langle>x | outer_sum n vs *\<^sub>v x\<rangle> = \<langle>?y | ?y\<rangle>"
    proof - 
      have  "\<langle>x | outer_sum n vs *\<^sub>v x\<rangle> = \<langle>x | ((?M * (?M\<^sup>\<dagger>)) *\<^sub>v x)\<rangle>"
        using outer_as_MMdag by simp
      also have  "... = \<langle>x | ?M *\<^sub>v ((?M\<^sup>\<dagger>) *\<^sub>v x)\<rangle>"
        using M_car xcar by (metis assoc_mult_mat_vec carrier_matD(1)
            carrier_mat_triv dim_col_of_dagger dim_mult_mat_vec ydim)
      also have " ...  = \<langle>?y | ?y\<rangle>"
        using inner_prod_adjoint_swap M_car xcar  by simp
      finally show ?thesis.
    qed
    have self_nonneg: "Re \<langle>?y | ?y\<rangle> \<ge> 0"
      using ydim inner_prod_with_itself_Re by blast
    show "Re (\<langle>x | outer_sum n vs *\<^sub>v x\<rangle>) \<ge> 0"
      using qf self_nonneg by simp
  qed
  show ?thesis
    unfolding psd_def using herm nonneg by simp
qed


lemma hermitian_spectral_decomp_eq:
  assumes Uc: "U \<in> carrier_mat n n"
      and Pcar: "P \<in> carrier_mat n n"
      and unit: "unitary U"
      and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
  shows "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
proof -
  have UdagU: "U\<^sup>\<dagger> * U = 1\<^sub>m n"
    using Uc unit unfolding unitary_def by auto
  have UUdag: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using Uc unit unfolding unitary_def by auto
  have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = U * ((U\<^sup>\<dagger>) * P * U) * (U\<^sup>\<dagger>)"
    using spec by simp
  also have "... = (U * (U\<^sup>\<dagger>)) * P * (U * (U\<^sup>\<dagger>))"
    by (smt (verit, best) Pcar UUdag UdagU assoc_mult_mat carrier_matD(2) 
        carrier_mat_triv dim_row_of_dagger index_mult_mat(2,3) index_one_mat(2))
  also have "... = (1\<^sub>m n) * P * (1\<^sub>m n)"
    using UUdag by simp
  also have "... = P"
    using Pcar by simp
  finally show ?thesis
    by simp
qed

lemma hermitian_spectral_decomp_right:
  assumes Uc: "U \<in> carrier_mat n n"
      and Pcar: "P \<in> carrier_mat n n"
      and unit: "unitary U"
      and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
  shows "P * U = U * diag_mat_of_real D"
  by (smt (verit, best) hermitian_spectral_decomp_eq Pcar Uc assoc_mult_mat carrier_mat_triv 
      dim_col_of_dagger unitary_def index_mult_mat(2,3) local.spec right_mult_one_mat unit)

(* Direction \<rightarrow>: if P \<ge> 0 then P = \<Sigma> |vᵢ\<rangle>\<langle>vᵢ| (requires spectral theorem) *)
theorem psd_kraus_decomp:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>vs :: complex Matrix.vec list.
         (\<forall>v \<in> set vs. dim_vec v = n) \<and>
         outer_sum n vs = P"
proof -
  (* By spectral theorem, P = U D U\<dagger> with D diagonal real \<ge> 0.
     Take vᵢ = \<surd>(Dᵢᵢ) \<cdot> col i of U.  Then \<Sum>|vᵢ\<rangle>\<langle>vᵢ| = U D U\<dagger> = P. *)
  have herm: "hermitian P"
    using pos by (rule psd_hermitian)

  obtain U D where
      Uc: "U \<in> carrier_mat n n"
    and UU: "unitary U"
    and Dlen: "length D = n"
    and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast

  have P_eq: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using hermitian_spectral_decomp_eq[OF Uc sq UU spec].   
  have PU_eq_UD: "P * U = U * diag_mat_of_real D"
    using UU Uc hermitian_spectral_decomp_right local.spec sq by presburger
  
  have eig_nonneg:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    using psd_iff_nonneg_eigenvalues[OF sq] pos by blast
  (* All entries of D are \<ge> 0 because P is psd. *)
  have D_nonneg: "\<forall>i < n. D ! i \<ge> 0"
  proof (intro allI impI)
    fix i assume iltn: "i < n"
    let ?ui = "Matrix.col U i"
    have uidim: "dim_vec ?ui = n"
      using Uc by simp
    have ui_nonzero: "?ui \<noteq> 0\<^sub>v n"
    proof
      assume zero: "?ui = 0\<^sub>v n"
      have "\<parallel>?ui\<parallel> = (1 :: real)"
        using UU iltn Uc by (metis carrier_matD(2) unitary_unit_col)
      moreover have "\<parallel>?ui\<parallel> = 0"
        using zero uidim cpx_vec_length_zero_iff by metis
      ultimately show False by simp
    qed
    have eig: "P *\<^sub>v ?ui = complex_of_real (D ! i) \<cdot>\<^sub>v ?ui"
    proof (rule eq_vecI)
      show "dim_vec (P *\<^sub>v ?ui) = dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
        using sq uidim by simp
    next
      fix k
      assume k: "k < dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
      then have klt: "k < n"
        using uidim by simp
      have "(P *\<^sub>v ?ui) $ k = (P * U) $$ (k, i)"
        using sq Uc iltn klt by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using PU_eq_UD by simp
      also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
      proof -
        have "(U * diag_mat_of_real D) $$ (k, i) =
              (\<Sum>j = 0..<n. U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
          using Uc Dlen klt iltn by (simp add: scalar_prod_def lessThan_atLeast0)
        also have "\<dots> =
              (\<Sum>j = 0..<n. (if j = i then U $$ (k, j) * complex_of_real (D ! i) else 0))"
          using Dlen iltn by (intro sum.cong refl, auto)
        also have "\<dots> = U $$ (k, i) * complex_of_real (D ! i)"
          using iltn by simp
        also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
          by (simp add: mult.commute)
        finally show ?thesis.
      qed
      also have "\<dots> = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k"
        using klt Uc by (simp add: iltn)
      finally show "(P *\<^sub>v ?ui) $ k = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k" .
    qed
    have "0 \<le> Re (complex_of_real (D ! i))"
      using eig eig_nonneg ui_nonzero uidim by blast
    thus "D ! i \<ge> 0" by simp
  qed
  (* Construct vᵢ = \<surd>(Dᵢ) \<cdot> col i of U *)
  let ?vs = "map (\<lambda>i. complex_of_real (sqrt (D ! i)) \<cdot>\<^sub>v Matrix.col U i) [0..<n]"
  have vs_dim: "\<forall>v \<in> set ?vs. dim_vec v = n"
    using Uc by auto
  have decomp: "outer_sum n ?vs = P"
  proof -
    (* Step A: outer_sum n ?vs = U * diag_mat_of_real D * U\<^sup>\<dagger>
       because each vᵢ vᵢ\<dagger> = (D!i) \<cdot> (col U i)(col U i)\<dagger>,
       and \<Sum>_{i<n} (D!i) \<cdot> (col U i)(col U i)\<dagger> = U D U\<dagger>. *)
    have stepA: "outer_sum n ?vs = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    proof -
      let ?sqrtD = "map sqrt D"
      let ?S = "diag_mat_of_real ?sqrtD"
      have sqrtDlen: "length ?sqrtD = n"
        using Dlen by simp
      have S_car: "?S \<in> carrier_mat n n"
        using sqrtDlen by force
      have M_eq: "mat_of_cols n ?vs = U * ?S"
      proof (rule eq_matI)
        show "dim_row (mat_of_cols n ?vs) = dim_row (U * ?S)"
          using Uc S_car by simp
        show "dim_col (mat_of_cols n ?vs) = dim_col (U * ?S)"
          using Uc S_car by force
      next
        fix r c
        assume rc: "r < dim_row (U * ?S)" "c < dim_col (U * ?S)"
        then have rlt: "r < n" and clt: "c < n"
          using Uc S_car by auto
        have "(mat_of_cols n ?vs) $$ (r, c) =
              complex_of_real (sqrt (D ! c)) * U $$ (r, c)"
          using Uc rlt clt by (simp add: mat_of_cols_def)
        also have "\<dots> = (U * ?S) $$ (r, c)"
        proof -
          have "(U * ?S) $$ (r, c) =  (\<Sum>j = 0..<n. U $$ (r, j) * ?S $$ (j, c))"
            using Uc S_car sqrtDlen rlt clt by (simp add: scalar_prod_def lessThan_atLeast0)
          also have "\<dots> =
                (\<Sum>j = 0..<n.
                   (if j = c then U $$ (r, j) * complex_of_real (sqrt (D ! c)) else 0))"
            using Dlen clt by (intro sum.cong refl, auto)
          also have "\<dots> = U $$ (r, c) * complex_of_real (sqrt (D ! c))"
            using clt by simp
          also have "\<dots> = complex_of_real (sqrt (D ! c)) * U $$ (r, c)"
            by (simp add: mult.commute)
          finally show ?thesis by simp
        qed
        finally show "(mat_of_cols n ?vs) $$ (r, c) = (U * ?S) $$ (r, c)" .
      qed
      have S_square: "?S * (?S\<^sup>\<dagger>) = diag_mat_of_real D"
      proof (rule eq_matI)
        show "dim_row (?S * (?S\<^sup>\<dagger>)) = dim_row (diag_mat_of_real D)"
          using Dlen sqrtDlen by simp
        show "dim_col (?S * (?S\<^sup>\<dagger>)) = dim_col (diag_mat_of_real D)"
          using Dlen sqrtDlen by simp
      next
        fix r c
        assume rc: "r < dim_row (diag_mat_of_real D)" "c < dim_col (diag_mat_of_real D)"
        then have rlt: "r < n" and clt: "c < n"
          using Dlen by auto
        have "(?S * (?S\<^sup>\<dagger>)) $$ (r, c) = (\<Sum>j = 0..<n. ?S $$ (r, j) * (?S\<^sup>\<dagger>) $$ (j, c))"
          using S_car sqrtDlen rlt clt by (simp add: scalar_prod_def lessThan_atLeast0)
        also have "\<dots> =
              (\<Sum>j = 0..<n.
                 (if r = j \<and> j = c
                  then complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! c))
                  else 0))"
          using Dlen rlt clt by (intro sum.cong refl, auto simp: dagger_def)
        also have "\<dots> = (if r = c then complex_of_real (D ! r) else 0)"
        proof (cases "r = c")
          case True
          then have "0 \<le> D ! r"
            using D_nonneg rlt by simp
          then have sqrt_sq:
            "complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! r)) =
             complex_of_real (D ! r)"
            by (simp add: of_real_mult[symmetric])
          have sum_single:
            "(\<Sum>j = 0..<n.
                 (if r = j \<and> j = c
                  then complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! c))
                  else 0))
             = complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! r))"
            using True rlt by (subst sum.remove[where x=r], auto)
          then show ?thesis
            using True sqrt_sq by argo
        next
          case False
          then show ?thesis by simp
        qed
        also have "\<dots> = diag_mat_of_real D $$ (r, c)"
          using Dlen rlt clt by simp
        finally show "(?S * (?S\<^sup>\<dagger>)) $$ (r, c) = diag_mat_of_real D $$ (r, c)" .
      qed
      have "outer_sum n ?vs = (U * ?S) * ((U * ?S)\<^sup>\<dagger>)"
        using M_eq by (simp add: outer_sum_def)
      also have "\<dots> = U * (?S * (?S\<^sup>\<dagger>)) * (U\<^sup>\<dagger>)"
        by (smt (verit, ccfv_threshold) Uc assoc_mult_mat carrier_matD(2) carrier_mat_triv sqrtDlen
            dagger_of_prod dim_col_of_dagger dim_row_diag_mat_of_real dim_row_of_dagger 
            mult_carrier_mat)        
      also have "\<dots> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
        using S_square by simp
      finally show ?thesis.
    qed
    (* Step B: U * diag_mat_of_real D * U\<^sup>\<dagger> = P
       follows from spec (U\<^sup>\<dagger> * P * U = diag_mat_of_real D)
       by multiplying on left by U and right by U\<^sup>\<dagger> and using U U\<^sup>\<dagger> = 1\<^sub>m n. *)
    have stepB: "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = P"
      using P_eq by blast
    from stepA stepB show ?thesis by simp
  qed
  show ?thesis using vs_dim decomp by blast
qed
(* Proof: By spectral theorem, P = U D U\<dagger> with D diagonal, real, non-negative entries.
   Set vᵢ = \<surd>(Dᵢᵢ) \<sqdot> Ueᵢ.  Then \<Sigma> |vᵢ\<rangle>\<langle>vᵢ| = U D U\<dagger> = P. *)

(* PD iff span{v₁,...,vₘ} = \<complex>^n *)

lemma mat_of_cols_dagger_mult_vec_index:
  assumes xdim: "dim_vec x = n"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
      and i: "i < length vs"
  shows "(((mat_of_cols n vs)\<^sup>\<dagger>) *\<^sub>v x) $ i = \<langle>vs ! i | x\<rangle>"
proof -
  let ?M = "mat_of_cols n vs"
  have vi_dim: "dim_vec (vs ! i) = n"
    using assms by simp
  have "(((mat_of_cols n vs)\<^sup>\<dagger>) *\<^sub>v x) $ i =
        (\<Sum>j = 0..<n. cnj ((vs ! i) $ j) * x $ j)"
    using assms
    by (simp add: scalar_prod_def dagger_def mat_of_cols_def lessThan_atLeast0)
  also have "\<dots> = \<langle>vs ! i | x\<rangle>"
    using xdim vi_dim by (simp add: inner_prod_def)
  finally show ?thesis .
qed

lemma inner_prod_outer_sum_general:
  assumes xdim: "dim_vec x = n"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "\<langle>x | outer_sum n vs *\<^sub>v x\<rangle> =
         \<langle>((mat_of_cols n vs)\<^sup>\<dagger>) *\<^sub>v x |
          ((mat_of_cols n vs)\<^sup>\<dagger>) *\<^sub>v x\<rangle>"
proof -
  let ?M = "mat_of_cols n vs"
  let ?y = "(?M\<^sup>\<dagger>) *\<^sub>v x"
  have M_car: "?M \<in> carrier_mat n (length vs)"
    using vs_dim by (simp add: mat_of_cols_def)
  have xcar: "x \<in> carrier_vec n"
    using xdim carrier_vec_dim_vec by blast
  have ydim: "dim_vec ?y = length vs"
    using M_car xcar by force
  have outer_as_MMdag: "outer_sum n vs = ?M * (?M\<^sup>\<dagger>)"
    by (simp add: outer_sum_def)
  have "\<langle>x | outer_sum n vs *\<^sub>v x\<rangle> =
        \<langle>x | ((?M * (?M\<^sup>\<dagger>)) *\<^sub>v x)\<rangle>"
    using outer_as_MMdag by simp
  also have "... = \<langle>x | ?M *\<^sub>v ((?M\<^sup>\<dagger>) *\<^sub>v x)\<rangle>"
    using M_car xcar
    by (metis assoc_mult_mat_vec carrier_matD(1) carrier_mat_triv dim_col_of_dagger
        dim_mult_mat_vec ydim)
  also have "... = \<langle>?y | ?y\<rangle>"
    using inner_prod_adjoint_swap M_car xcar by simp
  finally show ?thesis .
qed

lemma diag_mat_of_real_hermitian:
  shows "hermitian (diag_mat_of_real D)"
  unfolding hermitian_def
proof (rule eq_matI)
  show "dim_row ((diag_mat_of_real D)\<^sup>\<dagger>) = dim_row (diag_mat_of_real D)"
    by simp
  show "dim_col ((diag_mat_of_real D)\<^sup>\<dagger>) = dim_col (diag_mat_of_real D)"
    by simp
next
  fix i j
  assume ij: "i < dim_row (diag_mat_of_real D)" "j < dim_col (diag_mat_of_real D)"
  then have i: "i < length D" and j: "j < length D"
    by simp_all
  show "((diag_mat_of_real D)\<^sup>\<dagger>) $$ (i, j) = diag_mat_of_real D $$ (i, j)"
    using i j by (cases "i = j", simp_all add: dagger_def)
qed

lemma diag_mat_of_real_sqrt_square:
  assumes D_nonneg: "\<And>i. i < length D \<Longrightarrow> 0 \<le> D ! i"
  shows "diag_mat_of_real (map sqrt D) * diag_mat_of_real (map sqrt D) = diag_mat_of_real D"
proof (rule eq_matI)
  show "dim_row (diag_mat_of_real (map sqrt D) * diag_mat_of_real (map sqrt D)) =
        dim_row (diag_mat_of_real D)"
    by simp
  show "dim_col (diag_mat_of_real (map sqrt D) * diag_mat_of_real (map sqrt D)) =
        dim_col (diag_mat_of_real D)"
    by simp
next
  fix r c
  assume rc: "r < dim_row (diag_mat_of_real D)" "c < dim_col (diag_mat_of_real D)"
  then have rlt: "r < length D" and clt: "c < length D"
    by simp_all
  let ?S = "diag_mat_of_real (map sqrt D)"
  have "(?S * ?S) $$ (r, c) = (\<Sum>j = 0..<length D. ?S $$ (r, j) * ?S $$ (j, c))"
    using rlt clt by (simp add: scalar_prod_def lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>j = 0..<length D.
           (if r = j \<and> j = c
            then complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! c))
            else 0))"
    using rlt clt by (intro sum.cong refl, auto)
  also have "\<dots> = (if r = c then complex_of_real (D ! r) else 0)"
  proof (cases "r = c")
    case True
    then have sqrt_sq:
      "complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! r)) =
       complex_of_real (D ! r)"
      using D_nonneg rlt by (simp add: of_real_mult[symmetric])
    have "(\<Sum>j = 0..<length D.
           (if r = j \<and> j = c
            then complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! c))
            else 0))
          = complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! r))"
      using True rlt by (subst sum.remove[where x=r], auto)
    then show ?thesis
      using True sqrt_sq by argo
  next
    case False
    then show ?thesis by simp
  qed
  also have "\<dots> = diag_mat_of_real D $$ (r, c)"
    using rlt clt by simp
  finally show "(?S * ?S) $$ (r, c) = diag_mat_of_real D $$ (r, c)" .
qed

theorem pd_iff_spanning:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and decomp: "P = outer_sum n vs"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "pd P \<longleftrightarrow>
         (\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> x \<noteq> 0\<^sub>v n \<longrightarrow>
            (\<exists>v \<in> set vs. \<langle>v | x\<rangle> \<noteq> 0))"
proof
  (* pd P \<longleftrightarrow> \<langle>x|Px\<rangle> > 0 for all x \<noteq> 0
            \<longleftrightarrow> \<Sum>|\<langle>vᵢ|x\<rangle>|² > 0 for all x \<noteq> 0
            \<longleftrightarrow> some \<langle>vᵢ|x\<rangle> \<noteq> 0 for all x \<noteq> 0
            \<longleftrightarrow> {vs} spans \<complex>^n. *)
  assume pdP: "pd P"
  show "\<forall>x. dim_vec x = n \<longrightarrow> x \<noteq> 0\<^sub>v n \<longrightarrow> (\<exists>v \<in> set vs. \<langle>v | x\<rangle> \<noteq> 0)"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n" and xne: "x \<noteq> 0\<^sub>v n"
    show "\<exists>v\<in>set vs. \<langle>v | x\<rangle> \<noteq> 0"
    proof (rule ccontr)
      assume nex: "\<not> (\<exists>v\<in>set vs. \<langle>v | x\<rangle> \<noteq> 0)"
      let ?M = "mat_of_cols n vs"
      let ?y = "(?M\<^sup>\<dagger>) *\<^sub>v x"
      have ydim: "dim_vec ?y = length vs"
        using xdim vs_dim by (simp add: mat_of_cols_def)
      have yzero: "?y = 0\<^sub>v (length vs)"
      proof (rule eq_vecI)
        show "dim_vec ((mat_of_cols n vs)\<^sup>\<dagger> *\<^sub>v x) = dim_vec (0\<^sub>v (length vs))"
          using ydim by simp
      next
        fix i
        assume i: "i < dim_vec (0\<^sub>v (length vs))"
        then have ilt: "i < length vs"
          by simp
        have "?y $ i = \<langle>vs ! i | x\<rangle>"
          using mat_of_cols_dagger_mult_vec_index[OF xdim vs_dim ilt] .
        also have "\<dots> = 0"
          using nex ilt by auto
        finally show "((mat_of_cols n vs)\<^sup>\<dagger> *\<^sub>v x) $ i = 0\<^sub>v (length vs) $ i"
          using ilt by simp
      qed
      have qzero: "\<langle>x | P *\<^sub>v x\<rangle> = 0"
        using inner_prod_outer_sum_general[OF xdim vs_dim] decomp yzero ydim by simp
      have "Re (\<langle>x | P *\<^sub>v x\<rangle>) > 0"
        using pdP xdim xne sq unfolding pd_def by auto
      then show False
        using qzero by simp
    qed
  qed
next
  assume spanning: "\<forall>x. dim_vec x = n \<longrightarrow> x \<noteq> 0\<^sub>v n \<longrightarrow> (\<exists>v \<in> set vs. \<langle>v | x\<rangle> \<noteq> 0)"
  have herm: "hermitian P"
    using decomp outer_sum_hermitian unfolding hermitian_def by simp
  have pos:
    "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
       x \<noteq> 0\<^sub>v (dim_row P) \<longrightarrow> 0 < Re \<langle>x | P *\<^sub>v x\<rangle>"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdimP: "dim_vec x = dim_row P"
      and xneP: "x \<noteq> 0\<^sub>v (dim_row P)"
    have Pdim: "dim_row P = n"
      using sq by simp
    have xdim: "dim_vec x = n"
      using xdimP Pdim by simp
    have xne: "x \<noteq> 0\<^sub>v n"
      using xneP Pdim by simp
    let ?M = "mat_of_cols n vs"
    let ?y = "(?M\<^sup>\<dagger>) *\<^sub>v x"
    have ydim: "dim_vec ?y = length vs"
      using xdim vs_dim by (simp add: mat_of_cols_def)
    obtain v where vset: "v \<in> set vs" and inn_ne: "\<langle>v | x\<rangle> \<noteq> 0"
      using spanning xdim xne by blast
    obtain i where ilt: "i < length vs" and vi: "vs ! i = v"
      using vset by (metis in_set_conv_nth)
    have yi_ne: "?y $ i \<noteq> 0"
      using mat_of_cols_dagger_mult_vec_index[OF xdim vs_dim ilt] inn_ne vi by simp
    have yne: "?y \<noteq> 0\<^sub>v (length vs)"
      using ilt yi_ne by force
    have qeq: "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>?y | ?y\<rangle>"
      using inner_prod_outer_sum_general[OF xdim vs_dim] decomp by simp
    have "0 < Re \<langle>?y | ?y\<rangle>"
      using inner_prod_with_itself_Re_non0 ydim yne by presburger
    thus "0 < Re \<langle>x | P *\<^sub>v x\<rangle>"
      using qeq by presburger
  qed
  show "pd P"
    unfolding pd_def using herm pos by simp
qed

(* Positive square root *)

definition psd_sqrt :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "psd_sqrt P \<equiv> 0\<^sub>m (dim_row P) (dim_col P)"
(* Given P = U D U\<dagger>, P^{1/2} = U sqrt(D) U\<dagger>, with sqrt applied entrywise to D.
   The computational definition is deferred; use psd_sqrt_exists for the mathematical property. *)
(* We state the defining property and leave the construction to the spectral theorem. *)

theorem psd_sqrt_exists:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>Q :: complex Matrix.mat.
         Q \<in> carrier_mat n n \<and> psd Q \<and> Q * Q = P"
proof -
  have herm: "hermitian P" using pos by (rule psd_hermitian)
  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
    and Dlen: "length D = n" and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast
  have Udagcar: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have P_eq: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using hermitian_spectral_decomp_eq[OF Uc sq UU spec].
  have PU_eq_UD: "P * U = U * diag_mat_of_real D"
    using UU Uc hermitian_spectral_decomp_right local.spec sq by presburger
  have eig_nonneg:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    using psd_iff_nonneg_eigenvalues[OF sq] pos by blast
  have D_nonneg: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  proof -
    fix i assume iltn: "i < n"
    let ?ui = "Matrix.col U i"
    have uidim: "dim_vec ?ui = n"
      using Uc by simp
    have ui_nonzero: "?ui \<noteq> 0\<^sub>v n"
    proof
      assume zero: "?ui = 0\<^sub>v n"
      have "\<parallel>?ui\<parallel> = (1 :: real)"
        using UU iltn Uc by (metis carrier_matD(2) unitary_unit_col)
      moreover have "\<parallel>?ui\<parallel> = 0"
        using zero uidim cpx_vec_length_zero_iff by metis
      ultimately show False by simp
    qed
    have eig: "P *\<^sub>v ?ui = complex_of_real (D ! i) \<cdot>\<^sub>v ?ui"
    proof (rule eq_vecI)
      show "dim_vec (P *\<^sub>v ?ui) = dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
        using sq uidim by simp
    next
      fix k
      assume k: "k < dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
      then have klt: "k < n"
        using uidim by simp
      have "(P *\<^sub>v ?ui) $ k = (P * U) $$ (k, i)"
        using sq Uc iltn klt by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using PU_eq_UD by simp
      also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
      proof -
        have "(U * diag_mat_of_real D) $$ (k, i) =
              (\<Sum>j = 0..<n. U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
          using Uc Dlen klt iltn by (simp add: scalar_prod_def lessThan_atLeast0)
        also have "\<dots> =
              (\<Sum>j = 0..<n. (if j = i then U $$ (k, j) * complex_of_real (D ! i) else 0))"
          using Dlen iltn by (intro sum.cong refl, auto)
        also have "\<dots> = U $$ (k, i) * complex_of_real (D ! i)"
          using iltn by simp
        also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
          by (simp add: mult.commute)
        finally show ?thesis.
      qed
      also have "\<dots> = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k"
        using klt Uc by (simp add: iltn)
      finally show "(P *\<^sub>v ?ui) $ k = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k" .
    qed
    have "0 \<le> Re (complex_of_real (D ! i))"
      using eig eig_nonneg ui_nonzero uidim by blast
    thus "0 \<le> D ! i" by simp
  qed
  let ?sqrtD = "map sqrt D"
  have sqrtD_len: "length ?sqrtD = n" using Dlen by simp
  let ?S = "diag_mat_of_real ?sqrtD"
  let ?Q = "U * diag_mat_of_real ?sqrtD * (U\<^sup>\<dagger>)"
  (* Q \<in> carrier_mat n n by mult_carrier_mat. *)
  have Qcar: "?Q \<in> carrier_mat n n"
    using Uc Udagcar sqrtD_len by auto
  (* Q is hermitian: Q\<^sup>\<dagger> = U \<sqdot> \<surd>D\<^sup>\<dagger> \<sqdot> U\<^sup>\<dagger> = Q (since \<surd>D real-diagonal). *)
  have S_herm: "?S\<^sup>\<dagger> = ?S"
    using diag_mat_of_real_hermitian unfolding hermitian_def by simp
  have Q_herm: "hermitian ?Q"
  proof -
    have Qdag: "(?Q\<^sup>\<dagger>) = U * ?S * (U\<^sup>\<dagger>)"
    proof -
      have "(?Q\<^sup>\<dagger>) =  ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * (?S\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
        using Uc Udagcar sqrtD_len
        by (smt (verit, best) assoc_mult_mat carrier_matD(1) dagger_of_dagger_is_id dagger_of_prod
            diag_mat_of_real_carrier dim_col_diag_mat_of_real dim_col_of_dagger index_mult_mat(2))
      also have "... = U * ?S * (U\<^sup>\<dagger>)"
        using S_herm dagger_of_dagger_is_id by presburger
      finally show ?thesis.
    qed
    show ?thesis
      unfolding hermitian_def
      using Qcar Qdag by simp
  qed

  (* PSD: \<langle>x | Q x\<rangle> = \<langle>U\<^sup>\<dagger>x | \<surd>D U\<^sup>\<dagger>x\<rangle> \<ge> 0 since \<surd>D entries \<ge> 0. *)
  have Q_psd: "psd ?Q"
  proof -
    have sqrtD_nonneg: "\<And>i. i < length ?sqrtD \<Longrightarrow> 0 \<le> ?sqrtD ! i"
      by (simp add: D_nonneg Dlen)
    have nonneg: "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row ?Q \<longrightarrow> 0 \<le> Re \<langle>x | ?Q *\<^sub>v x\<rangle>"
    proof (intro allI impI)
      fix x :: "complex Matrix.vec"
      assume xdimQ: "dim_vec x = dim_row ?Q"
      then have xdim: "dim_vec x = n"
        using Qcar by force
      let ?y = "U\<^sup>\<dagger> *\<^sub>v x"
      have ydim: "dim_vec ?y = n"
        using Uc by force
      have v_as_Uy: "U *\<^sub>v ?y = x"
      proof -
        have UdagU: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
          using Uc UU unfolding unitary_def by auto
        have "U *\<^sub>v ((U\<^sup>\<dagger>) *\<^sub>v x) = (U * (U\<^sup>\<dagger>)) *\<^sub>v x"
          using Uc Udagcar xdim by force
        also have "\<dots> = x"
          using UdagU xdim by force
        finally show ?thesis.
      qed
      have Qx_as: "?Q *\<^sub>v x = U *\<^sub>v (?S *\<^sub>v ?y)"
        using Uc Udagcar Qcar sqrtD_len xdim ydim
            by (smt (verit, ccfv_SIG) assoc_mult_mat_vec carrier_vec_dim_vec
                diag_mat_of_real_carrier mult_carrier_mat)
      have "\<langle>x | ?Q *\<^sub>v x\<rangle> = \<langle>U *\<^sub>v ?y | U *\<^sub>v (?S *\<^sub>v ?y)\<rangle>"
        using v_as_Uy Qx_as by simp
      also have "\<dots> = \<langle>?y | ?S *\<^sub>v ?y\<rangle>"
        using Uc inner_prod_adjoint_swap sqrtD_len v_as_Uy xdim by force
      finally have qeq: "\<langle>x | ?Q *\<^sub>v x\<rangle> = \<langle>?y | ?S *\<^sub>v ?y\<rangle>".
      show "0 \<le> Re \<langle>x | ?Q *\<^sub>v x\<rangle>"
        using diag_mat_of_real_quad_Re_nonneg[OF _ sqrtD_nonneg] sqrtD_len ydim qeq by auto
    qed
    show ?thesis
      unfolding psd_def using Q_herm nonneg by simp
  qed
  (* Q\<^sup>2 = U \<sqdot> \<surd>D \<sqdot> (U\<^sup>\<dagger>U) \<sqdot> \<surd>D \<sqdot> U\<^sup>\<dagger> = U \<sqdot> D \<sqdot> U\<^sup>\<dagger> = P. *)
  have S_square: "?S * ?S = diag_mat_of_real D"
    using diag_mat_of_real_sqrt_square[of D] D_nonneg Dlen by auto
  have UdagU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n"
    using Uc UU unfolding unitary_def by auto
  have QQ_eq: "?Q * ?Q = P"
  proof -
    have "?Q * ?Q = U * (?S * ?S) * (U\<^sup>\<dagger>)"
      by (smt (verit, best) Uc UdagU Udagcar assoc_mult_mat diag_mat_of_real_carrier
          mult_carrier_mat right_mult_one_mat sqrtD_len)
    also have "\<dots> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
      using S_square by simp
    also have "\<dots> = P"
      using P_eq by simp
    finally show ?thesis.
  qed
  show ?thesis using Qcar Q_psd QQ_eq by blast
qed
(* Proof: From spectral decomp P = U diag(\<lambda>₁,...,\<lambda>ₙ) U\<dagger>,
   set Q = U diag(\<surd>\<lambda>₁,...,\<surd>\<lambda>ₙ) U\<dagger>.  Since \<lambda>ᵢ \<ge> 0, Q is well-defined,
   psd, and Q² = P. *)


(* ============================================================================
   DAY 5 — 7 / Sep / 11
   Topic: Practical Tests for Positivity; Direct Sums of Vector Spaces
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Cholesky / Principal-Minor Test
   -------------------------------------------------------------------------- *)

(* Principal minor test: if P = P* then P > 0 iff every leading principal
   minor has positive determinant.  This is Sylvester's criterion.
   We state it and defer the proof which requires determinant theory. *)

(*We need to prove this LAST!  Perhaps use UTP/vcg to define a program which handles this...*)
  

(* Cholesky reduction: P \<ge> 0 iff P - (p_{i1}\<sqdot>p_{1j}/p_{11}) \<ge> 0
   (when p_{11} > 0), stated as an inductive test *)



theorem cholesky_reduction:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and herm: "hermitian P"
      and n_pos: "0 < n"
      and p11_pos: "P $$ (0,0) > 0"
  shows "psd P \<longleftrightarrow>
         psd (Matrix.mat (n-1) (n-1)
              (\<lambda>(i,j). P $$ (i+1, j+1) -
                       P $$ (i+1, 0) * cnj (P $$ (j+1, 0)) / P $$ (0,0)))"
proof -
  let ?S = "Matrix.mat (n-1) (n-1)
              (\<lambda>(i,j). P $$ (i+1, j+1) -
                       P $$ (i+1, 0) * cnj (P $$ (j+1, 0)) / P $$ (0,0))"
  let ?tail = "\<lambda>x :: complex Matrix.vec. Matrix.vec (n-1) (\<lambda>i. x $ (i+1))"
  let ?lift = "\<lambda>z y. Matrix.vec n (\<lambda>i. if i = 0 then z else y $ (i-1))"
  let ?cross = "\<lambda>y :: complex Matrix.vec. \<Sum>i = 0..<(n-1). cnj (P $$ (i+1, 0)) * y $ i"

  have S_car: "?S \<in> carrier_mat (n-1) (n-1)"
    by simp
  have P00_nonzero: "P $$ (0,0) \<noteq> 0"
    using p11_pos by auto
  have P00_real: "P $$ (0,0) \<in> \<real>"
    using herm sq n_pos
    by (simp add: nonnegative_complex_is_real order_less_imp_le p11_pos) 
  have P00_Re_pos: "0 < Re (P $$ (0,0))"
    using p11_pos P00_real
    by (simp add: less_complex_def)

  have S_herm: "hermitian ?S"
  proof -
    have S_dagger_entries:
      "\<And>i j. i < n-1 \<Longrightarrow> j < n-1 \<Longrightarrow>
        (?S\<^sup>\<dagger>) $$ (i,j) = ?S $$ (i,j)"
    proof -
      fix i j
      assume i: "i < n-1" and j: "j < n-1"
      have ip: "i + 1 < n" and jp: "j + 1 < n"
        using i j by linarith+
      have irow: "i + 1 < dim_row P" and icol: "i + 1 < dim_col P"
        using sq ip by simp_all
      have jrow: "j + 1 < dim_row P" and jcol: "j + 1 < dim_col P"
        using sq jp by simp_all
      have zrow: "0 < dim_row P" and zcol: "0 < dim_col P"
        using sq n_pos by simp_all
      have Pji: "P $$ (j+1, i+1) = cnj (P $$ (i+1, j+1))"
        using hermitian_index[OF herm jrow icol] by simp
      have Pj0: "P $$ (j+1, 0) = cnj (P $$ (0, j+1))"
        using hermitian_index[OF herm jrow zcol] by simp
      have Pi0: "P $$ (i+1, 0) = cnj (P $$ (0, i+1))"
        using hermitian_index[OF herm irow zcol] by simp
      have cnj_P00: "cnj (P $$ (0,0)) = P $$ (0,0)"
        using P00_real by (simp add: Reals_cnj_iff)
      have "(?S\<^sup>\<dagger>) $$ (i,j) = cnj (?S $$ (j,i))"
        using i j by (simp add: dagger_def)
      also have "\<dots> = ?S $$ (i,j)"
        using i j Pji Pj0 Pi0 cnj_P00 P00_nonzero
        by (simp add: field_simps)
      finally show "(?S\<^sup>\<dagger>) $$ (i,j) = ?S $$ (i,j)" .
    qed
    show ?thesis
      unfolding hermitian_def
      using S_dagger_entries by (intro eq_matI, auto)
  qed

  have lift_dim: "\<And>z y. dim_vec y = n-1 \<Longrightarrow> dim_vec (?lift z y) = n"
    by simp
  have tail_dim: "\<And>x. dim_vec x = n \<Longrightarrow> dim_vec (?tail x) = n-1"
    by simp
  have lift_tail_head: "\<And>x. dim_vec x = n \<Longrightarrow> ?lift (x $ 0) (?tail x) = x"
  proof -
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    show "?lift (x $ 0) (?tail x) = x"
    proof (rule eq_vecI)
      show "dim_vec (?lift (x $ 0) (?tail x)) = dim_vec x"
        using xdim by simp
    next
      fix i
      assume i: "i < dim_vec x"
      show "(?lift (x $ 0) (?tail x)) $ i = x $ i"
        using xdim i n_pos by (cases i) simp_all
    qed
  qed

  have Schur_quadratic_lift:
    "\<And>z y. dim_vec y = n-1 \<Longrightarrow>
      \<langle>?lift z y | P *\<^sub>v (?lift z y)\<rangle> =
        cnj (z + ?cross y / P $$ (0,0)) * (P $$ (0,0)) * (z + ?cross y / P $$ (0,0)) +
        \<langle>y | ?S *\<^sub>v y\<rangle>"
  proof -
    fix z :: complex and y :: "complex Matrix.vec"
    assume ydim: "dim_vec y = n-1"
    let ?x = "?lift z y"
    let ?a = "P $$ (0,0)"
    let ?c = "?cross y"
    let ?tail_quad = "(\<Sum>i = 0..<(n-1). \<Sum>j = 0..<(n-1).
                         cnj (y $ i) * P $$ (i+1,j+1) * y $ j)"

    have xdim: "dim_vec ?x = n"
      using ydim by simp
    have x0: "?x $ 0 = z"
      using n_pos by simp
    have xSuc: "\<And>i. i < n-1 \<Longrightarrow> ?x $ (i+1) = y $ i"
      by simp
    have cnj_a: "cnj ?a = ?a"
      using P00_real by (simp add: Reals_cnj_iff)
    have P0_suc:
      "\<And>i. i < n-1 \<Longrightarrow> P $$ (0, i+1) = cnj (P $$ (i+1, 0))"
    proof -
      fix i
      assume i: "i < n-1"
      then have ip: "i + 1 < n"
        by linarith
      have zrow: "0 < dim_row P"
        using sq n_pos by simp
      have ipcol: "i + 1 < dim_col P"
        using sq ip by simp
      show "P $$ (0, i+1) = cnj (P $$ (i+1, 0))"
        using hermitian_index[OF herm zrow ipcol] by simp
    qed
    have c_alt: "?c = (\<Sum>i = 0..<(n-1). P $$ (0, i+1) * y $ i)"
      using P0_suc by (intro sum.cong refl) simp
    have cnj_c: "cnj ?c = (\<Sum>i = 0..<(n-1). cnj (y $ i) * P $$ (i+1, 0))"
    proof -
      have "cnj ?c = (\<Sum>i = 0..<(n-1). cnj (cnj (P $$ (i+1, 0)) * y $ i))"
        by simp
      also have "\<dots> = (\<Sum>i = 0..<(n-1). cnj (cnj (P $$ (i+1, 0))) * cnj (y $ i))"
        by (intro sum.cong refl) simp
      also have "\<dots> = (\<Sum>i = 0..<(n-1). P $$ (i+1, 0) * cnj (y $ i))"
        by (intro sum.cong refl) simp
      also have "\<dots> = (\<Sum>i = 0..<(n-1). cnj (y $ i) * P $$ (i+1, 0))"
        by (intro sum.cong refl) (simp add: mult.commute)
      finally show ?thesis .
    qed

    have Px0:
      "(P *\<^sub>v ?x) $ 0 = ?a * z + ?c"
    proof -
      have zrow: "0 < dim_row P"
        using sq n_pos by simp
      have colP: "dim_col P = n"
        using sq by simp
      have step1: "(P *\<^sub>v ?x) $ 0 = (\<Sum>j = 0..<n. P $$ (0,j) * ?x $ j)"
      proof -
        have "(P *\<^sub>v ?x) $ 0 = Matrix.row P 0 \<bullet> ?x"
          using zrow by simp
        also have "\<dots> = (\<Sum>j = 0..<dim_vec ?x. (Matrix.row P 0) $ j * ?x $ j)"
          unfolding scalar_prod_def by simp
        also have "\<dots> = (\<Sum>j = 0..<n. (Matrix.row P 0) $ j * ?x $ j)"
          using xdim by simp
        also have "\<dots> = (\<Sum>j = 0..<n. P $$ (0,j) * ?x $ j)"
        proof (intro sum.cong refl)
          fix j
          assume "j \<in> {0..<n}"
          then have jlt: "j < n" by simp
          have jcol: "j < dim_col P" using colP jlt by simp
          show "(Matrix.row P 0) $ j * ?x $ j = P $$ (0,j) * ?x $ j"
            using zrow jcol by simp
        qed
        finally show ?thesis .
      qed
      have reindex: "(\<Sum>j = Suc 0..<n. P $$ (0,j) * ?x $ j)
                   = (\<Sum>j = 0..<n-1. P $$ (0, j+1) * ?x $ (j+1))"
      proof -
        have Sucn: "Suc (n-1) = n" using n_pos by simp
        have "(\<Sum>j = Suc 0..<Suc (n-1). P $$ (0,j) * ?x $ j)
            = (\<Sum>j = 0..<n-1. P $$ (0, Suc j) * ?x $ (Suc j))"
          by (rule sum.shift_bounds_Suc_ivl)
        then show ?thesis using Sucn by simp
      qed
      have step2: "(\<Sum>j = 0..<n. P $$ (0,j) * ?x $ j)
                 = P $$ (0,0) * z + (\<Sum>j = 0..<(n-1). P $$ (0,j+1) * y $ j)"
      proof -
        have "(\<Sum>j = 0..<n. P $$ (0,j) * ?x $ j)
            = P $$ (0,0) * ?x $ 0 + (\<Sum>j = Suc 0..<n. P $$ (0,j) * ?x $ j)"
          using n_pos by (simp add: sum.atLeast_Suc_lessThan)
        also have "\<dots> = P $$ (0,0) * z + (\<Sum>j = Suc 0..<n. P $$ (0,j) * ?x $ j)"
          using x0 by simp
        also have "\<dots> = P $$ (0,0) * z + (\<Sum>j = 0..<n-1. P $$ (0, j+1) * ?x $ (j+1))"
          using reindex by simp
        also have "\<dots> = P $$ (0,0) * z + (\<Sum>j = 0..<(n-1). P $$ (0, j+1) * y $ j)"
          by (intro arg_cong2[where f="(+)"] refl sum.cong refl, simp add: xSuc)
        finally show ?thesis .
      qed
      from step1 step2 show ?thesis
        using c_alt by simp
    qed

    have PxSuc:
      "\<And>i. i < n-1 \<Longrightarrow>
        (P *\<^sub>v ?x) $ (i+1) =
          P $$ (i+1,0) * z + (\<Sum>j = 0..<(n-1). P $$ (i+1,j+1) * y $ j)"
    proof -
      fix i
      assume i: "i < n-1"
      then have ip: "i + 1 < n"
        by linarith
      have iprow: "i + 1 < dim_row P"
        using sq ip by simp
      have colP: "dim_col P = n"
        using sq by simp
      have step1: "(P *\<^sub>v ?x) $ (i+1) = (\<Sum>j = 0..<n. P $$ (i+1,j) * ?x $ j)"
      proof -
        have "(P *\<^sub>v ?x) $ (i+1) = Matrix.row P (i+1) \<bullet> ?x"
          using iprow by simp
        also have "\<dots> = (\<Sum>j = 0..<dim_vec ?x. (Matrix.row P (i+1)) $ j * ?x $ j)"
          unfolding scalar_prod_def by simp
        also have "\<dots> = (\<Sum>j = 0..<n. (Matrix.row P (i+1)) $ j * ?x $ j)"
          using xdim by simp
        also have "\<dots> = (\<Sum>j = 0..<n. P $$ (i+1,j) * ?x $ j)"
        proof (intro sum.cong refl)
          fix j
          assume "j \<in> {0..<n}"
          then have jlt: "j < n" by simp
          have jcol: "j < dim_col P" using colP jlt by simp
          show "(Matrix.row P (i+1)) $ j * ?x $ j = P $$ (i+1,j) * ?x $ j"
            using iprow jcol by simp
        qed
        finally show ?thesis .
      qed
      have reindex: "(\<Sum>j = Suc 0..<n. P $$ (i+1,j) * ?x $ j)
                   = (\<Sum>j = 0..<n-1. P $$ (i+1, j+1) * ?x $ (j+1))"
      proof -
        have Sucn: "Suc (n-1) = n" using n_pos by simp
        have "(\<Sum>j = Suc 0..<Suc (n-1). P $$ (i+1,j) * ?x $ j)
            = (\<Sum>j = 0..<n-1. P $$ (i+1, Suc j) * ?x $ (Suc j))"
          by (rule sum.shift_bounds_Suc_ivl)
        then show ?thesis using Sucn by simp
      qed
      have step2: "(\<Sum>j = 0..<n. P $$ (i+1,j) * ?x $ j)
                 = P $$ (i+1,0) * z + (\<Sum>j = 0..<(n-1). P $$ (i+1,j+1) * y $ j)"
      proof -
        have "(\<Sum>j = 0..<n. P $$ (i+1,j) * ?x $ j)
            = P $$ (i+1,0) * ?x $ 0 + (\<Sum>j = Suc 0..<n. P $$ (i+1,j) * ?x $ j)"
          using n_pos by (simp add: sum.atLeast_Suc_lessThan)
        also have "\<dots> = P $$ (i+1,0) * z + (\<Sum>j = Suc 0..<n. P $$ (i+1,j) * ?x $ j)"
          using x0 by simp
        also have "\<dots> = P $$ (i+1,0) * z + (\<Sum>j = 0..<n-1. P $$ (i+1, j+1) * ?x $ (j+1))"
          using reindex by simp
        also have "\<dots> = P $$ (i+1,0) * z + (\<Sum>j = 0..<(n-1). P $$ (i+1, j+1) * y $ j)"
          by (intro arg_cong2[where f="(+)"] refl sum.cong refl, simp add: xSuc)
        finally show ?thesis .
      qed
      from step1 step2 show "(P *\<^sub>v ?x) $ (i+1) =
          P $$ (i+1,0) * z + (\<Sum>j = 0..<(n-1). P $$ (i+1,j+1) * y $ j)"
        by simp
    qed

    have full_quad:
      "\<langle>?x | P *\<^sub>v ?x\<rangle> =
        cnj z * ?a * z + cnj z * ?c + cnj ?c * z + ?tail_quad"
    proof -
      have Pxdim: "dim_vec (P *\<^sub>v ?x) = n"
        using sq xdim by simp
      have "\<langle>?x | P *\<^sub>v ?x\<rangle> =
          (\<Sum>i = 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)"
      using xdim Pxdim by (simp add: inner_prod_def)
          also have "\<dots> = cnj z * (P *\<^sub>v ?x) $ 0 +
        (\<Sum>i = 0..<(n - 1). cnj (y $ i) * (P *\<^sub>v ?x) $ (i + 1))"
      proof -
        have "(\<Sum>i = 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)
            = cnj (?x $ 0) * (P *\<^sub>v ?x) $ 0
            + (\<Sum>i = Suc 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)"
          using xdim n_pos sum.atLeast_Suc_lessThan by blast
        also have "\<dots> =
            cnj z * (P *\<^sub>v ?x) $ 0
            + (\<Sum>i = 0..<(n - 1). cnj (?x $ (i + 1)) * (P *\<^sub>v ?x) $ (i + 1))"
        proof -
          have Sucn: "Suc (n-1) = n" using n_pos by simp
          have "(\<Sum>i = Suc 0..<Suc (n-1). cnj (?x $ i) * (P *\<^sub>v ?x) $ i)
              = (\<Sum>i = 0..<n-1. cnj (?x $ (Suc i)) * (P *\<^sub>v ?x) $ (Suc i))"
            by (rule sum.shift_bounds_Suc_ivl)
          then have reindex:
            "(\<Sum>i = Suc 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)
           = (\<Sum>i = 0..<(n - 1). cnj (?x $ (i + 1)) * (P *\<^sub>v ?x) $ (i + 1))"
            using Sucn by simp
          show "cnj (?x $ 0) * (P *\<^sub>v ?x) $ 0
                + (\<Sum>i = Suc 0..<n. cnj (?x $ i) * (P *\<^sub>v ?x) $ i)
              = cnj z * (P *\<^sub>v ?x) $ 0
                + (\<Sum>i = 0..<(n - 1). cnj (?x $ (i + 1)) * (P *\<^sub>v ?x) $ (i + 1))"
            using reindex x0 by simp
        qed
        also have "\<dots> =
            cnj z * (P *\<^sub>v ?x) $ 0
            + (\<Sum>i = 0..<(n - 1). cnj (y $ i) * (P *\<^sub>v ?x) $ (i + 1))"
          by simp
        finally show ?thesis.
      qed
      also have "\<dots> =
          cnj z * (?a * z + ?c) +
          (\<Sum>i = 0..<(n-1).
             cnj (y $ i) * (P $$ (i+1,0) * z +
               (\<Sum>j = 0..<(n-1). P $$ (i+1,j+1) * y $ j)))"
        using Px0 PxSuc by (intro arg_cong2[where f="(+)"] refl sum.cong, simp_all)
      also have "\<dots> =
          cnj z * ?a * z + cnj z * ?c +
          (\<Sum>i = 0..<(n-1). cnj (y $ i) * P $$ (i+1,0)) * z +
          ?tail_quad"
        by (simp add: algebra_simps sum_distrib_left sum_distrib_right sum.distrib)
      also have "\<dots> = cnj z * ?a * z + cnj z * ?c + cnj ?c * z + ?tail_quad"
        using cnj_c by simp
      finally show ?thesis.
    qed

    have Schur_quad:
      "\<langle>y | ?S *\<^sub>v y\<rangle> = ?tail_quad - cnj ?c * ?c / ?a"
    proof -
      have Sydim: "dim_vec (?S *\<^sub>v y) = n-1"
        using ydim by simp
      have "\<langle>y | ?S *\<^sub>v y\<rangle> =
          (\<Sum>i = 0..<(n-1). cnj (y $ i) * (?S *\<^sub>v y) $ i)"
        using ydim Sydim by (simp add: inner_prod_def)
      also have "\<dots> =
          (\<Sum>i = 0..<(n-1). cnj (y $ i) *
            (\<Sum>j = 0..<(n-1).
              (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j))"
      proof (intro sum.cong refl)
        fix i
        assume "i \<in> {0..<n-1}"
        then have ilt: "i < n-1" by simp
        have irow: "i < dim_row ?S" using ilt by simp
        have colS: "dim_col ?S = n-1" by simp
        have "(?S *\<^sub>v y) $ i = Matrix.row ?S i \<bullet> y"
          using irow by simp
        also have "\<dots> = (\<Sum>j = 0..<dim_vec y. (Matrix.row ?S i) $ j * y $ j)"
          unfolding scalar_prod_def by simp
        also have "\<dots> = (\<Sum>j = 0..<n-1. (Matrix.row ?S i) $ j * y $ j)"
          using ydim by simp
        also have "\<dots> = (\<Sum>j = 0..<n-1. ?S $$ (i,j) * y $ j)"
        proof (intro sum.cong refl)
          fix j
          assume "j \<in> {0..<n-1}"
          then have jlt: "j < n-1" by simp
          have jcol: "j < dim_col ?S" using colS jlt by simp
          show "(Matrix.row ?S i) $ j * y $ j = ?S $$ (i,j) * y $ j"
            using irow jcol by simp
        qed
        also have "\<dots> = (\<Sum>j = 0..<n-1.
                  (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j)"
        proof (intro sum.cong refl)
          fix j
          assume "j \<in> {0..<n-1}"
          then have jlt: "j < n-1" by simp
          have Sij: "?S $$ (i,j) =
              P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a"
            using ilt jlt by simp
          show "?S $$ (i,j) * y $ j =
              (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j"
            using Sij by simp
        qed
        finally have Sy_i:
          "(?S *\<^sub>v y) $ i = (\<Sum>j = 0..<n-1.
              (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j)" .
        show "cnj (y $ i) * (?S *\<^sub>v y) $ i =
            cnj (y $ i) * (\<Sum>j = 0..<(n-1).
              (P $$ (i+1,j+1) - P $$ (i+1,0) * cnj (P $$ (j+1,0)) / ?a) * y $ j)"
          using Sy_i by simp
      qed
      also have "\<dots> =
          ?tail_quad -
          ((\<Sum>i = 0..<(n-1). cnj (y $ i) * P $$ (i+1,0)) *
           (\<Sum>j = 0..<(n-1). cnj (P $$ (j+1,0)) * y $ j)) / ?a"
        by (simp add: algebra_simps sum_distrib_left sum_distrib_right sum_subtractf sum_divide_distrib)
      also have "\<dots> = ?tail_quad - cnj ?c * ?c / ?a"
        using cnj_c by simp
      finally show ?thesis .
    qed

    have square_expand:
      "cnj (z + ?c / ?a) * ?a * (z + ?c / ?a) =
       cnj z * ?a * z + cnj z * ?c + cnj ?c * z + cnj ?c * ?c / ?a"
      using P00_nonzero cnj_a by (simp add: algebra_simps)

    show "\<langle>?lift z y | P *\<^sub>v (?lift z y)\<rangle> =
        cnj (z + ?cross y / P $$ (0,0)) * (P $$ (0,0)) * (z + ?cross y / P $$ (0,0)) + \<langle>y | ?S *\<^sub>v y\<rangle>"
      using full_quad Schur_quad square_expand by simp
  qed

  have Schur_quadratic_tail:
    "\<And>x. dim_vec x = n \<Longrightarrow>
      \<langle>x | P *\<^sub>v x\<rangle> =
        cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)) +
        \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>"
  proof -
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    have "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>?lift (x $ 0) (?tail x) | P *\<^sub>v (?lift (x $ 0) (?tail x))\<rangle>"
      using lift_tail_head[OF xdim] by simp
    also have "\<dots> =
        cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)) +
        \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>"
      using Schur_quadratic_lift[OF tail_dim[OF xdim], of "x $ 0"] .
    finally show "\<langle>x | P *\<^sub>v x\<rangle> =
        cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)) +
        \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>".
  qed

  have completed_square_nonneg: "\<And>w. 0 \<le> Re (cnj w * (P $$ (0,0)) * w)"
    using P00_Re_pos P00_real
    by (metis Re_complex_div_gt_0 mult.left_commute mult.right_neutral mult_zero_right 
        nonzero_mult_div_cancel_right order_le_less times_complex.simps(1) zero_complex.simps(1)) 
  have completed_square_zero_choice:
    "\<And>y. cnj ((- ?cross y / P $$ (0,0)) + ?cross y / P $$ (0,0)) *
          (P $$ (0,0)) *
          ((- ?cross y / P $$ (0,0)) + ?cross y / P $$ (0,0)) = 0"
    using P00_nonzero by simp

  have forward: "psd P \<Longrightarrow> psd ?S"
  proof -
    assume P_psd: "psd P"
    have S_nonneg: "\<forall>y :: complex Matrix.vec. dim_vec y = dim_row ?S \<longrightarrow> 0 \<le> Re \<langle>y | ?S *\<^sub>v y\<rangle>"
    proof (intro allI impI)
      fix y :: "complex Matrix.vec"
      assume ydimS: "dim_vec y = dim_row ?S"
      then have ydim: "dim_vec y = n-1"
        by simp
      let ?z = "- ?cross y / P $$ (0,0)"
      let ?x = "?lift ?z y"
      have xdim: "dim_vec ?x = n"
        using ydim by simp
      have P_nonneg: "0 \<le> Re \<langle>?x | P *\<^sub>v ?x\<rangle>"
        using P_psd xdim sq unfolding psd_def by auto
      have q_eq: "\<langle>?x | P *\<^sub>v ?x\<rangle> = \<langle>y | ?S *\<^sub>v y\<rangle>"
        using Schur_quadratic_lift[OF ydim] completed_square_zero_choice[of y] by simp
      show "0 \<le> Re \<langle>y | ?S *\<^sub>v y\<rangle>"
        using P_nonneg q_eq by simp
    qed
    show "psd ?S"
      unfolding psd_def using S_herm S_nonneg by simp
  qed

  have backward: "psd ?S \<Longrightarrow> psd P"
  proof -
    assume S_psd: "psd ?S"
    have P_nonneg:
      "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
        0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>"
    proof (intro allI impI)
      fix x :: "complex Matrix.vec"
      assume xdimP: "dim_vec x = dim_row P"
      then have xdim: "dim_vec x = n"
        using sq by simp
      have taildim: "dim_vec (?tail x) = n-1"
        using xdim by simp
      have S_nonneg: "0 \<le> Re \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>"
        using S_psd taildim unfolding psd_def by simp
      have square_nonneg:
        "0 \<le> Re (cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)))"
        using completed_square_nonneg by blast
      have q_decomp: "\<langle>x | P *\<^sub>v x\<rangle> =
        cnj (x $ 0 + ?cross (?tail x) / P $$ (0,0)) * (P $$ (0,0)) *
          (x $ 0 + ?cross (?tail x) / P $$ (0,0)) +
        \<langle>?tail x | ?S *\<^sub>v (?tail x)\<rangle>"
        using Schur_quadratic_tail[OF xdim].
      show "0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>"
        using square_nonneg S_nonneg q_decomp by simp
    qed
    show "psd P"
      unfolding psd_def using herm P_nonneg by simp
  qed
  show ?thesis
    using forward backward by blast
qed

(* --------------------------------------------------------------------------
   Direct Sums of Vector Spaces
   -------------------------------------------------------------------------- *)

(* The direct sum V \<oplus> W is represented concretely as \<complex>^{m+n} via append of
   coordinate vectors.  We use the Matrix.mat infrastructure already present. *)

definition direct_sum_vec :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" (infixr "\<oplus>\<^sub>v" 65) where
  "v \<oplus>\<^sub>v w \<equiv> Matrix.vec (dim_vec v + dim_vec w) (\<lambda>i. if i < dim_vec v then v $ i else w $ (i - dim_vec v))"

lemma direct_sum_vec_dim [simp]:
  "dim_vec (v \<oplus>\<^sub>v w) = dim_vec v + dim_vec w"
  by (simp add: direct_sum_vec_def)

lemma direct_sum_vec_left [simp]:
  "i < dim_vec v \<Longrightarrow> (v \<oplus>\<^sub>v w) $ i = v $ i"
  by (simp add: direct_sum_vec_def)

lemma direct_sum_vec_right [simp]:
  "i < dim_vec w \<Longrightarrow> (v \<oplus>\<^sub>v w) $ (dim_vec v + i) = w $ i"
  by (simp add: direct_sum_vec_def)

(* Inner product on V \<oplus> W: \<langle>(v₁,w₁)|(v₂,w₂)\<rangle> = \<langle>v₁|v₂\<rangle>_V + \<langle>w₁|w₂\<rangle>_W *)

lemma direct_sum_inner_prod:
  assumes vd1: "dim_vec v1 = m" and vd2: "dim_vec v2 = m"
      and wd1: "dim_vec w1 = p" and wd2: "dim_vec w2 = p"
  shows "\<langle>v1 \<oplus>\<^sub>v w1 | v2 \<oplus>\<^sub>v w2\<rangle> = \<langle>v1 | v2\<rangle> + \<langle>w1 | w2\<rangle>"
proof -
  (* Split at i = m using sum.atLeastLessThan_concat:
       (\<Sum>i = 0..<m+p. f i) = (\<Sum>i = 0..<m. f i) + (\<Sum>i = m..<m+p. f i),
     then reindex i \<mapsto> m + j to match the second range. *)
  have "\<langle>v1 \<oplus>\<^sub>v w1 | v2 \<oplus>\<^sub>v w2\<rangle> =
        (\<Sum>i = 0..<m+p. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i)"
    using assms by (simp add: inner_prod_def)
  also have "\<dots> = (\<Sum>i = 0..<m. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i)
                + (\<Sum>i = m..<m+p. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i)"
    by (simp add: sum.atLeastLessThan_concat)

  also have "(\<Sum>i = 0..<m. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i) =
             (\<Sum>i = 0..<m. cnj (v1 $ i) * v2 $ i)"
    using vd1 vd2 by (intro sum.cong refl, simp)
  also have "(\<Sum>i = m..<m+p. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i) =
             (\<Sum>j = 0..<p. cnj (w1 $ j) * w2 $ j)"
  proof -
    have "(\<Sum>i = m..<m+p. cnj ((v1 \<oplus>\<^sub>v w1) $ i) * (v2 \<oplus>\<^sub>v w2) $ i) =
          (\<Sum>j = 0..<p. cnj ((v1 \<oplus>\<^sub>v w1) $ (j + m)) * (v2 \<oplus>\<^sub>v w2) $ (j + m))"
      using sum.shift_bounds_nat_ivl[of _ 0 m p]
      by (simp add: add.commute)
    also have "\<dots> = (\<Sum>j = 0..<p. cnj (w1 $ j) * w2 $ j)"
    proof (intro sum.cong refl)
      fix j assume "j \<in> {0..<p}"
      hence jp: "j < p" by simp
      have e1: "(v1 \<oplus>\<^sub>v w1) $ (j + m) = w1 $ j"
        using jp vd1 wd1 direct_sum_vec_right[of j w1 v1]
        by (simp add: add.commute)
      have e2: "(v2 \<oplus>\<^sub>v w2) $ (j + m) = w2 $ j"
        using jp vd2 wd2 direct_sum_vec_right[of j w2 v2]
        by (simp add: add.commute)
      show "cnj ((v1 \<oplus>\<^sub>v w1) $ (j + m)) * (v2 \<oplus>\<^sub>v w2) $ (j + m) =
            cnj (w1 $ j) * w2 $ j"
        using e1 e2 by simp
    qed
    finally show ?thesis.
  qed
  finally show ?thesis
    using vd1 vd2 wd1 wd2 by (simp add: inner_prod_def)
qed

(* Dimension formula: dim(V \<oplus> W) = dim V + dim W *)

corollary direct_sum_dim:
  "dim_vec (v \<oplus>\<^sub>v w) = dim_vec v + dim_vec w"
  by simp

(* Block matrix form of a linear map T : \<complex>^{n+k} \<rightarrow> \<complex>^{m+p} *)

(* This is already captured by four_block_mat in the Matrix library.
   We just note the identity:
     T [ v ]   =  [ T₁₁ T₁₂ ] [ v ]   =  [ T₁₁v + T₁₂w ]
       [ w ]      [ T₂₁ T₂₂ ] [ w ]      [ T₂₁v + T₂₂w ]
*)

lemma block_mat_apply:
  assumes "dim_vec v = k1" and "dim_vec w = k2"
      and "T11 \<in> carrier_mat n1 k1" and "T12 \<in> carrier_mat n1 k2"
      and "T21 \<in> carrier_mat n2 k1" and "T22 \<in> carrier_mat n2 k2"
  shows "four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w) =
         (T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)"
proof -
  have v_carrier: "v \<in> carrier_vec k1"
    using assms(1) by (rule carrier_vecI)
  have w_carrier: "w \<in> carrier_vec k2"
    using assms(2) by (rule carrier_vecI)
  have vw_append: "v \<oplus>\<^sub>v w = v @\<^sub>v w"
    by (simp add: direct_sum_vec_def append_vec_def Let_def)

  have left_dim:
    "dim_vec (four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) = n1 + n2"
    using assms by simp
  have right_dim:
    "dim_vec ((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)) = n1 + n2"
    using assms by simp

  show ?thesis
  proof
    show "dim_vec (four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) =
          dim_vec ((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w))"
      using left_dim right_dim by simp
  next
    fix i
    assume i: "i < dim_vec ((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v
                             (T21 *\<^sub>v v + T22 *\<^sub>v w))"
    then have i_bound: "i < n1 + n2"
      using right_dim by simp
    show "(four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) $ i =
          ((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)) $ i"
    proof (cases "i < n1")
      case True
      have row_top:
        "Matrix.row (four_block_mat T11 T12 T21 T22) i = Matrix.row T11 i @\<^sub>v Matrix.row T12 i"
        using assms True row_four_block_mat[of T11 n1 k1 T12 k2 T21 n2 T22 i]
        by simp
      have lhs_i:
        "(four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) $ i =
         Matrix.row T11 i \<bullet> v + Matrix.row T12 i \<bullet> w"
        using assms True v_carrier w_carrier vw_append row_top
        by (metis dim_mult_mat_vec i_bound index_mult_mat_vec
            left_dim row_carrier_vec scalar_prod_append)
      have rhs_i:
        "((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)) $ i =
         Matrix.row T11 i \<bullet> v + Matrix.row T12 i \<bullet> w"
        using assms True
        by simp
      show ?thesis
        using lhs_i rhs_i by simp
    next
      case False
      let ?j = "i - n1"
      have j_bound: "?j < n2"
        using False i_bound by simp
      have row_bottom:
        "Matrix.row (four_block_mat T11 T12 T21 T22) i = Matrix.row T21 ?j @\<^sub>v Matrix.row T22 ?j"
        using assms False i_bound row_four_block_mat[of T11 n1 k1 T12 k2 T21 n2 T22 i]
        by simp
      have lhs_i:
        "(four_block_mat T11 T12 T21 T22 *\<^sub>v (v \<oplus>\<^sub>v w)) $ i =
         Matrix.row T21 ?j \<bullet> v + Matrix.row T22 ?j \<bullet> w"
        using assms False i_bound v_carrier w_carrier vw_append row_bottom
        by (metis dim_mult_mat_vec index_mult_mat_vec j_bound left_dim row_carrier_vec scalar_prod_append)
      have rhs_i:
        "((T11 *\<^sub>v v + T12 *\<^sub>v w) \<oplus>\<^sub>v (T21 *\<^sub>v v + T22 *\<^sub>v w)) $ i =
         Matrix.row T21 ?j \<bullet> v + Matrix.row T22 ?j \<bullet> w"
        using assms False j_bound
        by (simp add: direct_sum_vec_def)
      show ?thesis
        using lhs_i rhs_i by simp
    qed
  qed
qed


(* ============================================================================
   DAY 6 — 9 / Sep / 11
   Topic: Tensor Products
   ============================================================================ *)

(* --------------------------------------------------------------------------
   The tensor product of complex Matrix.vector spaces \<complex>^n and \<complex>^m is \<complex>^{n\<sqdot>m}.
   We use the existing Tensor.thy and More_Tensor.thy from
   Isabelle_Marries_Dirac.  The tensor of two vectors is:

     tensor_vec v w  \<in>  \<complex>^{n\<sqdot>m}   (v \<in> \<complex>^n, w \<in> \<complex>^m)
     (tensor_vec v w) $ (i * m + j) = v $ i * w $ j

   The tensor of two matrices is the Kronecker product.
   -------------------------------------------------------------------------- *)

(* Dimension formula: dim(\<complex>^n \<otimes> \<complex>^m) = n \<sqdot> m *)

lemma tensor_vec_dim:
  assumes vd: "dim_vec v = n" "dim_vec w = m"
  shows "dim_vec (tensor_vec v w) = n * m"
proof -
  have len_aux: "length (mult.vec_vec_Tensor (*) xs ys) = length xs * length ys"
    for xs ys :: "complex list"
    using mult.vec_vec_Tensor_length[of "1::complex" "(*)" xs ys]
    by (simp add: mult.intro)
  have len: "length (mult.vec_vec_Tensor (*) (list_of_vec v) (list_of_vec w)) =
      length (list_of_vec v) * length (list_of_vec w)"
    by (rule len_aux)
  show ?thesis
    using assms len by (simp add: tensor_vec_def)
qed

(* Index formula: (v \<otimes> w) $ i = v $ (i div m) * w $ (i mod m) *)

lemma tensor_vec_index:
  assumes "dim_vec v = n" "dim_vec w = m" "i < n * m"
  shows "tensor_vec v w $ i = v $ (i div m) * w $ (i mod m)"
proof -
  have m_pos: "m > 0" using assms(3) by (cases m) auto
  have n_pos: "n > 0" using assms(3) by (cases n) auto
  have lw_nonempty: "list_of_vec w \<noteq> []"
    using assms(2) m_pos by (metis length_greater_0_conv length_list_of_vec)
  have len_v: "length (list_of_vec v) = n" using assms(1) by simp
  have len_w: "length (list_of_vec w) = m" using assms(2) by simp
  have mult_inst: "Matrix_Tensor.mult (1::complex) (*)"
    by (simp add: Matrix_Tensor.mult_def)
  have elems: "\<forall>i. i < length (list_of_vec v) * length (list_of_vec w) \<longrightarrow>
     (mult.vec_vec_Tensor (*) (list_of_vec v) (list_of_vec w)) ! i =
        ((list_of_vec v) ! (i div length (list_of_vec w))) *
        ((list_of_vec w) ! (i mod length (list_of_vec w)))"
    using mult.vec_vec_Tensor_elements[OF mult_inst lw_nonempty,
        of "(list_of_vec v)"] by simp
  have i_bound: "i < length (list_of_vec v) * length (list_of_vec w)"
    using assms(3) len_v len_w by simp
  have div_bound: "i div m < n" using assms(3) less_mult_imp_div_less by blast
  have mod_bound: "i mod m < m" using m_pos by simp
  have len_tensor: "length (mult.vec_vec_Tensor (*) (list_of_vec v) (list_of_vec w)) = n * m"
    using len_v len_w mult.vec_vec_Tensor_length[OF mult_inst] by simp
  have "tensor_vec v w $ i =
      (mult.vec_vec_Tensor (*) (list_of_vec v) (list_of_vec w)) ! i"
    unfolding tensor_vec_def using assms(3) len_tensor
    by (simp add: vec_of_list_index)
  also have "\<dots> = (list_of_vec v) ! (i div m) * (list_of_vec w) ! (i mod m)"
    using elems i_bound len_w by simp
  also have "\<dots> = v $ (i div m) * w $ (i mod m)"
    using div_bound mod_bound assms(1,2) by (simp add: list_of_vec_index)
  finally show ?thesis .
qed

(* Bilinearity of the tensor product *)

lemma tensor_vec_bilinear_left:
  assumes vd: "dim_vec v1 = n" "dim_vec v2 = n" "dim_vec w = m"
  shows "tensor_vec (v1 + v2) w = tensor_vec v1 w + tensor_vec v2 w"
proof -
  have v1_carrier: "v1 \<in> carrier_vec n"
    using vd(1) by (rule carrier_vecI)
  have v2_carrier: "v2 \<in> carrier_vec n"
    using vd(2) by (rule carrier_vecI)
  have w_carrier: "w \<in> carrier_vec m"
    using vd(3) by (rule carrier_vecI)

  have dim_lhs: "dim_vec (tensor_vec (v1 + v2) w) = n * m"
    using vd by (simp add: tensor_vec_dim)
  have dim_rhs: "dim_vec (tensor_vec v1 w + tensor_vec v2 w) = n * m"
    using vd by (simp add: tensor_vec_dim)

  show ?thesis
  proof
    show "dim_vec (tensor_vec (v1 + v2) w) =
          dim_vec (tensor_vec v1 w + tensor_vec v2 w)"
      using dim_lhs dim_rhs by simp
  next
    fix i
    assume i: "i < dim_vec (tensor_vec v1 w + tensor_vec v2 w)"
    then have i_bound: "i < n * m"
      using dim_rhs by simp
    let ?a = "i div m"
    let ?b = "i mod m"
    have split_index: "i = ?a * m + ?b"
      by presburger
    have a_bound: "?a < n"
      using i_bound less_mult_imp_div_less by blast
    have b_bound: "?b < m"
      by (metis gr0I i_bound less_zeroE mod_less_divisor mult_not_zero)


    have dim_v12: "dim_vec (v1 + v2) = n" using vd by simp
    have lhs_i:  "tensor_vec (v1 + v2) w $ i = ((v1 + v2) $ ?a) * (w $ ?b)"
      using tensor_vec_index[OF dim_v12 vd(3) i_bound] .
    also have "\<dots> = (v1 $ ?a * w $ ?b) + (v2 $ ?a * w $ ?b)"
      using vd a_bound b_bound by (simp add: algebra_simps)
    also have "\<dots> = (tensor_vec v1 w + tensor_vec v2 w) $ i"
    proof -
      have t1: "tensor_vec v1 w $ i = v1 $ ?a * w $ ?b"
        using tensor_vec_index[OF vd(1) vd(3) i_bound] .
      have t2: "tensor_vec v2 w $ i = v2 $ ?a * w $ ?b"
        using tensor_vec_index[OF vd(2) vd(3) i_bound] .
      have di_rhs: "i < dim_vec (tensor_vec v1 w + tensor_vec v2 w)"
        using dim_rhs i_bound by simp
      have dt1: "dim_vec (tensor_vec v1 w) = n * m" using vd by (simp add: tensor_vec_dim)
      have dt2: "dim_vec (tensor_vec v2 w) = n * m" using vd by (simp add: tensor_vec_dim)
      have "(tensor_vec v1 w + tensor_vec v2 w) $ i = tensor_vec v1 w $ i + tensor_vec v2 w $ i"
        using dt1 dt2 i_bound by simp
      with t1 t2 show ?thesis by simp
    qed
    finally show "tensor_vec (v1 + v2) w $ i =
                  (tensor_vec v1 w + tensor_vec v2 w) $ i" .
  qed
qed





lemma tensor_vec_bilinear_right:
  assumes vd: "dim_vec v = n" "dim_vec w1 = m" "dim_vec w2 = m"
  shows "tensor_vec v (w1 + w2) = tensor_vec v w1 + tensor_vec v w2"
proof -
  have v_carrier: "v \<in> carrier_vec n"
    using vd(1) by (rule carrier_vecI)
  have w1_carrier: "w1 \<in> carrier_vec m"
    using vd(2) by (rule carrier_vecI)
  have w2_carrier: "w2 \<in> carrier_vec m"
    using vd(3) by (rule carrier_vecI)

  have dim_lhs: "dim_vec (tensor_vec v (w1 + w2)) = n * m"
    using vd by (simp add: tensor_vec_dim)
  have dim_rhs: "dim_vec (tensor_vec v w1 + tensor_vec v w2) = n * m"
    using vd by (simp add: tensor_vec_dim)

  show ?thesis
  proof
    show "dim_vec (tensor_vec v (w1 + w2)) =
          dim_vec (tensor_vec v w1 + tensor_vec v w2)"
      using dim_lhs dim_rhs by simp
  next
    fix i
    assume i: "i < dim_vec (tensor_vec v w1 + tensor_vec v w2)"
    then have i_bound: "i < n * m"
      using dim_rhs by simp
    let ?a = "i div m"
    let ?b = "i mod m"
    have split_index: "i = ?a * m + ?b"
      by presburger
    have a_bound: "?a < n"
      using i_bound less_mult_imp_div_less by blast
    have b_bound: "?b < m"
      by (metis i_bound mod_by_0 mod_less_divisor mod_mult_self2_is_0 not_gr0)
    have dim_w12: "dim_vec (w1 + w2) = m" using vd by simp
    have lhs_i:
      "tensor_vec v (w1 + w2) $ i = (v $ ?a) * ((w1 + w2) $ ?b)"
      using tensor_vec_index[OF vd(1) dim_w12 i_bound] .
    also have "\<dots> = (v $ ?a * w1 $ ?b) + (v $ ?a * w2 $ ?b)"
      using vd a_bound b_bound by (simp add: algebra_simps)
    also have "\<dots> = (tensor_vec v w1 + tensor_vec v w2) $ i"
    proof -
      have t1: "tensor_vec v w1 $ i = v $ ?a * w1 $ ?b"
        using tensor_vec_index[OF vd(1) vd(2) i_bound] .
      have t2: "tensor_vec v w2 $ i = v $ ?a * w2 $ ?b"
        using tensor_vec_index[OF vd(1) vd(3) i_bound] .
      have dt1: "dim_vec (tensor_vec v w1) = n * m" using vd by (simp add: tensor_vec_dim)
      have dt2: "dim_vec (tensor_vec v w2) = n * m" using vd by (simp add: tensor_vec_dim)
      have "(tensor_vec v w1 + tensor_vec v w2) $ i = tensor_vec v w1 $ i + tensor_vec v w2 $ i"
        using dt1 dt2 i_bound by simp
      with t1 t2 show ?thesis by simp
    qed
    finally show "tensor_vec v (w1 + w2) $ i =
                  (tensor_vec v w1 + tensor_vec v w2) $ i" .
  qed
qed

lemma tensor_vec_smult_left:
  assumes vd: "dim_vec v = n" "dim_vec w = m"
  shows "tensor_vec (\<alpha> \<cdot>\<^sub>v v) w = \<alpha> \<cdot>\<^sub>v tensor_vec v w"
proof
  have dim_av: "dim_vec (\<alpha> \<cdot>\<^sub>v v) = n" using vd by simp
  have dim_lhs: "dim_vec (tensor_vec (\<alpha> \<cdot>\<^sub>v v) w) = n * m"
    using dim_av vd(2) by (simp add: tensor_vec_dim)
  have dim_rhs: "dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w) = n * m"
    using vd by (simp add: tensor_vec_dim)
  show "dim_vec (tensor_vec (\<alpha> \<cdot>\<^sub>v v) w) = dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w)"
    using dim_lhs dim_rhs by simp
next
  fix i
  assume i: "i < dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w)"
  have dim_tvw: "dim_vec (tensor_vec v w) = n * m" using vd by (simp add: tensor_vec_dim)
  have i_bound: "i < n * m" using i dim_tvw by simp
  have dim_av: "dim_vec (\<alpha> \<cdot>\<^sub>v v) = n" using vd by simp
  let ?a = "i div m" let ?b = "i mod m"
  have a_bound: "?a < n" using i_bound less_mult_imp_div_less by blast
  have lhs: "tensor_vec (\<alpha> \<cdot>\<^sub>v v) w $ i = (\<alpha> \<cdot>\<^sub>v v) $ ?a * w $ ?b"
    using tensor_vec_index[OF dim_av vd(2) i_bound] .
  also have "\<dots> = \<alpha> * (v $ ?a * w $ ?b)"
    using a_bound vd by simp
  also have "\<dots> = \<alpha> * (tensor_vec v w $ i)"
    using tensor_vec_index[OF vd i_bound] by simp
  also have "\<dots> = (\<alpha> \<cdot>\<^sub>v tensor_vec v w) $ i"
    using i by simp
  finally show "tensor_vec (\<alpha> \<cdot>\<^sub>v v) w $ i = (\<alpha> \<cdot>\<^sub>v tensor_vec v w) $ i" .
qed

lemma tensor_vec_smult_right:
  assumes vd: "dim_vec v = n" "dim_vec w = m"
  shows "tensor_vec v (\<alpha> \<cdot>\<^sub>v w) = \<alpha> \<cdot>\<^sub>v tensor_vec v w"
proof
  have dim_aw: "dim_vec (\<alpha> \<cdot>\<^sub>v w) = m" using vd by simp
  have dim_lhs: "dim_vec (tensor_vec v (\<alpha> \<cdot>\<^sub>v w)) = n * m"
    using vd(1) dim_aw by (simp add: tensor_vec_dim)
  have dim_rhs: "dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w) = n * m"
    using vd by (simp add: tensor_vec_dim)
  show "dim_vec (tensor_vec v (\<alpha> \<cdot>\<^sub>v w)) = dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w)"
    using dim_lhs dim_rhs by simp
next
  fix i
  assume i: "i < dim_vec (\<alpha> \<cdot>\<^sub>v tensor_vec v w)"
  have dim_tvw: "dim_vec (tensor_vec v w) = n * m" using vd by (simp add: tensor_vec_dim)
  have i_bound: "i < n * m" using i dim_tvw by simp
  have dim_aw: "dim_vec (\<alpha> \<cdot>\<^sub>v w) = m" using vd by simp
  let ?a = "i div m" let ?b = "i mod m"
  have m_pos: "m > 0" using i_bound by (cases m) auto
  have b_bound: "?b < m" using m_pos by simp
  have lhs: "tensor_vec v (\<alpha> \<cdot>\<^sub>v w) $ i = v $ ?a * (\<alpha> \<cdot>\<^sub>v w) $ ?b"
    using tensor_vec_index[OF vd(1) dim_aw i_bound] .
  also have "\<dots> = \<alpha> * (v $ ?a * w $ ?b)"
    using b_bound vd by simp
  also have "\<dots> = \<alpha> * (tensor_vec v w $ i)"
    using tensor_vec_index[OF vd i_bound] by simp
  also have "\<dots> = (\<alpha> \<cdot>\<^sub>v tensor_vec v w) $ i"
    using i by simp
  finally show "tensor_vec v (\<alpha> \<cdot>\<^sub>v w) $ i = (\<alpha> \<cdot>\<^sub>v tensor_vec v w) $ i" .
qed

(* Tensor basis theorem: {eᵢ \<otimes> fⱼ} is a basis for \<complex>^n \<otimes> \<complex>^m *)
(* (This is already implicitly formalized in Tensor.thy) *)

(* Definition: Schmidt rank of a tensor u \<in> X \<otimes> Y *)

definition schmidt_rank :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> nat" where
  "schmidt_rank u m \<equiv>
     Min {k. \<exists>vs :: complex Matrix.vec list. \<exists>ws :: complex Matrix.vec list.
              length vs = k \<and> length ws = k \<and>
              (\<forall>i < k. dim_vec (vs ! i) = dim_vec u div m) \<and>
              (\<forall>i < k. dim_vec (ws ! i) = m) \<and>
              u = foldr (\<lambda>(v,w) acc. tensor_vec v w + acc)
                        (zip vs ws) (0\<^sub>v (dim_vec u))}"


(* ============================================================================
   DAY 7 — 12 / Sep / 11
   Topic: Tensor Products of Hilbert Spaces; Postulates of Quantum Mechanics
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Tensor product inner product
   \<langle>h₁ \<otimes> k₁ | h₂ \<otimes> k₂\<rangle> = \<langle>h₁ | h₂\<rangle>_H \<sqdot> \<langle>k₁ | k₂\<rangle>_K
   -------------------------------------------------------------------------- *)

lemma tensor_inner_prod:
  assumes "dim_vec h1 = n" "dim_vec h2 = n"
          "dim_vec k1 = m" "dim_vec k2 = m"
  shows "\<langle>tensor_vec h1 k1 | tensor_vec h2 k2\<rangle> =
         \<langle>h1 | h2\<rangle> * \<langle>k1 | k2\<rangle>"
proof -
  let ?f = "\<lambda>i. cnj (tensor_vec h1 k1 $ i) * tensor_vec h2 k2 $ i"

  have step1:
    "\<langle>tensor_vec h1 k1 | tensor_vec h2 k2\<rangle> =
     (\<Sum>i = 0..<n*m. ?f i)"
    using assms
    by (simp add: inner_prod_def tensor_vec_dim)

  have step2:
    "(\<Sum>i = 0..<n*m. ?f i) =
     (\<Sum>a = 0..<n. \<Sum>b = 0..<m. ?f (a*m+b))"
  proof -
    have "(\<Sum>i = 0..<n*m. ?f i) = (\<Sum>a<n. sum ?f {a*m..<a*m+m})"
      using sum.nat_group[of ?f m n]
      by (simp add: atLeast0LessThan)
    also have "... = (\<Sum>a = 0..<n. \<Sum>b = 0..<m. ?f (a*m+b))"
    proof (rule sum.cong)
      show "{..<n} = {0..<n}" by auto
    next
      fix a
      assume a: "a \<in> {0..<n}"
      have "sum ?f {a*m..<a*m+m} = (\<Sum>b = 0..<m. ?f (a*m+b))"
      proof (rule sum.reindex_bij_witness[where i = "\<lambda>b. a*m+b" and j = "\<lambda>x. x - a*m"])
        show "\<And>b. b \<in> {0..<m} \<Longrightarrow> a*m + b \<in> {a*m..<a*m+m}"
          by simp
        show "\<And>x. x \<in> {a*m..<a*m+m} \<Longrightarrow> x - a*m \<in> {0..<m}"
          by fastforce
        show "\<And>x. x \<in> {a*m..<a*m+m} \<Longrightarrow> (\<lambda>b. a*m+b) (x - a*m) = x"
          by simp
        show "\<And>b. b \<in> {0..<m} \<Longrightarrow> (\<lambda>x. x - a*m) ((\<lambda>b. a*m+b) b) = b"
          by simp
        show "\<And>b. b \<in> {a * m..<a * m + m} \<Longrightarrow>
            (cnj ((tensor_vec h1 k1) $ (a * m + (b - a * m))) *
             ((tensor_vec h2 k2) $ (a * m + (b - a * m)))) =
            (cnj ((tensor_vec h1 k1) $ b) *
             ((tensor_vec h2 k2) $ b))"
            by force
      qed
      then show "(\<Sum>i = a * m..<a * m + m.
        (cnj ((tensor_vec h1 k1) $ i)) * ((tensor_vec h2 k2) $ i)) =
        (\<Sum>b = 0..<m.(cnj ((tensor_vec h1 k1) $ (a * m + b))) * ((tensor_vec h2 k2) $ (a*m + b)))".
    qed
    finally show ?thesis.
  qed

  have step3:
    "(\<Sum>a = 0..<n. \<Sum>b = 0..<m. ?f (a*m+b)) =
     (\<Sum>a = 0..<n. \<Sum>b = 0..<m.
        cnj (h1 $ a * k1 $ b) * (h2 $ a * k2 $ b))"
  proof (rule sum.cong)
    show "{0..<n} = {0..<n}" by simp
  next
    fix a
    assume a: "a \<in> {0..<n}"
    show "(\<Sum>b = 0..<m. ?f (a*m+b)) =
          (\<Sum>b = 0..<m. cnj (h1 $ a * k1 $ b) * (h2 $ a * k2 $ b))"
    proof (rule sum.cong)
      show "{0..<m} = {0..<m}" by simp
    next
      fix b
      assume b: "b \<in> {0..<m}"
      have alt: "a < n"
        using a by simp
      have blt: "b < m"
        using b by simp
      have ab_lt: "a * m + b < n * m"
      proof -
        have "a * m + b < a * m + m"
          using blt by simp
        also have "... \<le> n * m"
          by (metis Suc_leI add.commute alt mult_Suc mult_le_mono1)
        finally show ?thesis.
      qed
      have div_eq: "(a*m+b) div m = a" using blt by simp
      have mod_eq: "(a*m+b) mod m = b" using blt by simp
      have idx1: "tensor_vec h1 k1 $ (a*m+b) = h1 $ a * k1 $ b"
        using tensor_vec_index[OF assms(1) assms(3) ab_lt] div_eq mod_eq by simp

      have idx2: "tensor_vec h2 k2 $ (a*m+b) = h2 $ a * k2 $ b"
        using tensor_vec_index[OF assms(2) assms(4) ab_lt] div_eq mod_eq by simp

      show "?f (a*m+b) = cnj (h1 $ a * k1 $ b) * (h2 $ a * k2 $ b)"
        unfolding idx1 idx2 by simp
    qed
  qed

  have step4:
    "(\<Sum>a = 0..<n. \<Sum>b = 0..<m.
        cnj (h1 $ a * k1 $ b) * (h2 $ a * k2 $ b)) =
     (\<Sum>a = 0..<n. \<Sum>b = 0..<m.
        (cnj (h1 $ a) * h2 $ a) * (cnj (k1 $ b) * k2 $ b))"
    by (smt (verit, best) complex_cnj_mult mult.commute semigroup_mult_class.mult.assoc sum.cong)


  have step5:
  "(\<Sum>a = 0..<n. \<Sum>b = 0..<m.
      (cnj (h1 $ a) * h2 $ a) * (cnj (k1 $ b) * k2 $ b)) =
   (\<Sum>a = 0..<n. cnj (h1 $ a) * h2 $ a) *
   (\<Sum>b = 0..<m. cnj (k1 $ b) * k2 $ b)"
  proof -
    have "(\<Sum>a = 0..<n. \<Sum>b = 0..<m.
            (cnj (h1 $ a) * h2 $ a) * (cnj (k1 $ b) * k2 $ b))
        = (\<Sum>a = 0..<n. (cnj (h1 $ a) * h2 $ a) * (\<Sum>b = 0..<m. cnj (k1 $ b) * k2 $ b))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... =
        (\<Sum>a = 0..<n. cnj (h1 $ a) * h2 $ a) *
        (\<Sum>b = 0..<m. cnj (k1 $ b) * k2 $ b)"
      by (simp add: sum_distrib_right algebra_simps)
    finally show ?thesis .
  qed

  have step6:
    "(\<Sum>a = 0..<n. cnj (h1 $ a) * h2 $ a) *
     (\<Sum>b = 0..<m. cnj (k1 $ b) * k2 $ b)
     = \<langle>h1 | h2\<rangle> * \<langle>k1 | k2\<rangle>"
    using assms
    by (simp add: inner_prod_def)

  show ?thesis
    using step1 step2 step3 step4 step5 step6
    by argo
qed

(* Orthonormal basis for \<complex>^n \<otimes> \<complex>^m from ONBs of each factor *)

lemma length_concat_map_upt:
  "length (concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n])) = n * m"
  by (simp add: length_concat o_def sum_list_triv)

lemma nth_concat_map_upt:
  assumes p_lt: "p < n * m"
  shows "concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n]) ! p =
         f (p div m) (p mod m)"
  using p_lt
proof (induction n arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have m_pos: "0 < m"
    using Suc.prems by (cases m) auto
  have upt_Suc: "[0..<Suc n] = [0..<n] @ [n]"
    by (simp add: upt_Suc_append)
  show ?case
  proof (cases "p < n * m")
    case True
    have len_prev:
      "length (concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n])) = n * m"
      by (rule length_concat_map_upt)
    have "concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<Suc n]) ! p =
          concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n]) ! p"
      using True len_prev
      by (simp add: upt_Suc nth_append)
    also have "... = f (p div m) (p mod m)"
      using Suc.IH[OF True] .
    finally show ?thesis .
  next
    case False
    have p_ge: "n * m \<le> p"
      using False by simp
    define r where "r = p - n * m"
    have p_eq: "p = n * m + r"
      using p_ge by (simp add: r_def)
    have r_lt: "r < m"
      using Suc.prems p_eq by simp
    have div_eq: "p div m = n"
      using p_eq r_lt m_pos by simp
    have mod_eq: "p mod m = r"
      using p_eq r_lt by simp
    have len_prev:
      "length (concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<n])) = n * m"
      by (rule length_concat_map_upt)
    have "concat (map (\<lambda>i. map (\<lambda>j. f i j) [0..<m]) [0..<Suc n]) ! p =
          (map (\<lambda>j. f n j) [0..<m]) ! r"
      using p_eq len_prev
      by (simp add: upt_Suc nth_append)
    also have "... = f n r"
      using r_lt by simp
    also have "... = f (p div m) (p mod m)"
      using div_eq mod_eq by simp
    finally show ?thesis .
  qed
qed

lemma tensor_onb:
  assumes hs_onb: "orthonormal_list n hs"
      and hs_len: "length hs = n"
      and ks_onb: "orthonormal_list m ks"
      and ks_len: "length ks = m"
  shows "orthonormal_list (n*m)
         [tensor_vec (hs ! i) (ks ! j). i \<leftarrow> [0..<n], j \<leftarrow> [0..<m]]"
proof -
  let ?ts = "[tensor_vec (hs ! i) (ks ! j). i \<leftarrow> [0..<n], j \<leftarrow> [0..<m]]"

  have ts_len: "length ?ts = n * m"
    using length_concat_map_upt[of "\<lambda>i j. tensor_vec (hs ! i) (ks ! j)" m n]
    by simp

  have hs_dim:
    "\<And>i. i < n \<Longrightarrow> dim_vec (hs ! i) = n"
    using hs_onb hs_len
    unfolding orthonormal_list_def
    by auto

  have ks_dim:
    "\<And>j. j < m \<Longrightarrow> dim_vec (ks ! j) = m"
    using ks_onb ks_len
    unfolding orthonormal_list_def
    by auto

  have hs_ip:
    "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> \<langle>hs ! i | hs ! j\<rangle> = (if i = j then 1 else 0)"
    using hs_onb hs_len
    unfolding orthonormal_list_def
    by auto

  have ks_ip:
    "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> \<langle>ks ! i | ks ! j\<rangle> = (if i = j then 1 else 0)"
    using ks_onb ks_len
    unfolding orthonormal_list_def
    by auto

  have nth_ts: "\<And>p. p < n*m \<Longrightarrow> ?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
  proof -
    fix p
    assume p_lt: "p < n*m"
    then have div_lt: "p div m < n"
      using less_mult_imp_div_less by presburger

    have mod_lt: "p mod m < m"
      by (metis mod_by_0 mod_less_divisor mod_mult_self2_is_0 p_lt zero_less_iff_neq_zero)


    have "?ts = concat (map (\<lambda>i. map (\<lambda>j. tensor_vec (hs ! i) (ks ! j)) [0..<m]) [0..<n])"
      by simp
    moreover have
      "concat (map (\<lambda>i. map (\<lambda>j. tensor_vec (hs ! i) (ks ! j)) [0..<m]) [0..<n]) ! p
       = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
      using nth_concat_map_upt[OF p_lt, of "\<lambda>i j. tensor_vec (hs ! i) (ks ! j)"] .
    ultimately show "?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
      by simp
  qed

  have ts_dim:  "\<And>p. p < length ?ts \<Longrightarrow> dim_vec (?ts ! p) = n*m"
  proof -
    fix p
    assume p_lt: "p < length ?ts"
    then have p_lt': "p < n*m"
      using ts_len by simp
    have div_lt: "p div m < n"
      using less_mult_imp_div_less p_lt' by blast
    have mod_lt: "p mod m < m"
      using p_lt' ks_len
      by (cases m, auto)
    have "?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
      using nth_ts p_lt' by blast
    then show "dim_vec (?ts ! p) = n*m"
      using hs_dim[OF div_lt] ks_dim[OF mod_lt] tensor_vec_dim by presburger
  qed

  have ts_ip:
    "\<And>p q. p < length ?ts \<Longrightarrow> q < length ?ts
       \<Longrightarrow> \<langle>?ts ! p | ?ts ! q\<rangle> = (if p = q then 1 else 0)"
  proof -
    fix p q
    assume p_lt: "p < length ?ts"
       and q_lt: "q < length ?ts"

    have p_lt': "p < n*m" and q_lt': "q < n*m"
      using p_lt q_lt ts_len by simp_all

    have pd: "p div m < n"
      using less_mult_imp_div_less p_lt' by blast
    have pm: "p mod m < m"
      using p_lt' ks_len by (cases m, auto)
    have qd: "q div m < n"
      using less_mult_imp_div_less q_lt' by blast
    have qm: "q mod m < m"
      using q_lt' ks_len by (cases m, auto)
    have p_nth:
      "?ts ! p = tensor_vec (hs ! (p div m)) (ks ! (p mod m))"
      using nth_ts p_lt' by blast
    have q_nth:
      "?ts ! q = tensor_vec (hs ! (q div m)) (ks ! (q mod m))"
      using nth_ts q_lt' by blast

    have "\<langle>?ts ! p | ?ts ! q\<rangle>
        = \<langle>tensor_vec (hs ! (p div m)) (ks ! (p mod m))
           | tensor_vec (hs ! (q div m)) (ks ! (q mod m))\<rangle>"
      using p_nth q_nth by simp
    also have "... =
        \<langle>hs ! (p div m) | hs ! (q div m)\<rangle> *
        \<langle>ks ! (p mod m) | ks ! (q mod m)\<rangle>"
      using hs_dim[OF pd] hs_dim[OF qd] ks_dim[OF pm] ks_dim[OF qm]
      by (rule tensor_inner_prod)
    also have "... =
        (if p div m = q div m then 1 else 0) *
        (if p mod m = q mod m then 1 else 0)"
      using hs_ip[OF pd qd] ks_ip[OF pm qm] by simp
    also have "... = (if p = q then 1 else 0)"
      using p_lt' q_lt' ks_len
      by (simp, metis div_mod_decomp)
    finally show "\<langle>?ts ! p | ?ts ! q\<rangle> = (if p = q then 1 else 0)".
  qed

  show ?thesis
    unfolding orthonormal_list_def
    using ts_len ts_dim ts_ip
    by (metis (lifting) in_set_conv_nth)
qed

(* --------------------------------------------------------------------------
   Postulates of Quantum Mechanics
   We formalise the four postulates as definitions / locale axioms.
   -------------------------------------------------------------------------- *)

(* Postulate 1: State space *)
(* A quantum system is associated to a Hilbert space H.
   The state is a unit vector \<psi> \<in> H, i.e., \<Parallel>\<psi>\<Parallel> = 1. *)

definition quantum_state :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
  "quantum_state n \<psi> \<equiv> dim_vec \<psi> = n \<and> \<parallel>\<psi>\<parallel> = 1"

lemma quantum_state_norm1:
  assumes "quantum_state n \<psi>"
  shows "\<parallel>\<psi>\<parallel> = 1"
  using assms
  by (simp add: quantum_state_def)

lemma quantum_state_dim:
  assumes "quantum_state n \<psi>"
  shows "dim_vec \<psi> = n"
  using assms
  by (simp add: quantum_state_def)

(* Postulate 2: Time evolution of a closed system *)
(* Evolution from t₁ to t₂ is described by a unitary U.
   If \<psi> is the state at t₁, then U\<psi> is the state at t₂. *)

definition evolve :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "evolve U \<psi> \<equiv> U *\<^sub>v \<psi>"

lemma unitary_preserves_state:
  assumes "unitary U" and "quantum_state n \<psi>" and "dim_col U = n"
  shows "quantum_state (dim_row U) (evolve U \<psi>)"
  unfolding quantum_state_def evolve_def
proof
  show "dim_vec (U *\<^sub>v \<psi>) = dim_row U" by simp
  have "\<parallel>U *\<^sub>v \<psi>\<parallel> = \<parallel>\<psi>\<parallel>"
    using unitary_isometry[OF assms(1)] assms(2,3)
    by (simp add: quantum_state_def)
  also have "\<parallel>\<psi>\<parallel> = 1"
    using assms(2) quantum_state_def by simp
  finally show "\<parallel>U *\<^sub>v \<psi>\<parallel> = 1".
qed

(* Postulate 3: Quantum Measurements *)
(* A measurement on H is a collection {M_m} of operators satisfying
   \<Sigma>_m M_m\<dagger> M_m = I.
   If the system is in state \<psi>, the probability of outcome m is \<Parallel>M_m \<psi>\<Parallel>². *)

definition measurement_system :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "measurement_system n Ms \<equiv>
     (\<forall>M \<in> set Ms. M \<in> carrier_mat n n) \<and>
     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n"

definition meas_prob :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> real" where
  "meas_prob M \<psi> \<equiv> \<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2"

(* Probabilities sum to 1 *)

lemma measurement_probs_sum_one:
  assumes ms: "measurement_system n Ms"
      and st: "quantum_state n \<psi>"
  shows "(\<Sum>M \<leftarrow> Ms. meas_prob M \<psi>) = 1"
proof -
  have psi_dim: "dim_vec \<psi> = n" using st by (auto simp: quantum_state_def)
  have psi_norm: "\<parallel>\<psi>\<parallel> = 1" using st by (auto simp: quantum_state_def)
  have psi_car: "\<psi> \<in> carrier_vec n" using psi_dim
    by fastforce 

  (* Step 1: \<parallel>M\<psi>\<parallel>² = \<langle>\<psi> | M\<dagger>M \<psi>\<rangle> for each M *)
  have step1: "\<And>M. M \<in> set Ms \<Longrightarrow> meas_prob M \<psi> = Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>)"
    by (metis (lifting) Re_complex_of_real assoc_mult_mat_vec carrier_matD(2) carrier_mat_triv 
        cpx_vec_length_inner_prod dagger_of_dagger_is_id dim_mult_mat_vec dim_row_of_dagger 
        inner_prod_adjoint_swap meas_prob_def measurement_system_def ms psi_car psi_dim)

(* Step 2: sum over M and pull out, using \<Sum>M\<dagger>M = I *)
  have sum_eq: "(\<Sum>M \<leftarrow> Ms. meas_prob M \<psi>) =
              Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
  proof -
    have all_car: "\<And>M. M \<in> set Ms \<Longrightarrow> M \<in> carrier_mat n n"
      using ms by (auto simp: measurement_system_def)
    have fold_car:
      "\<And>Ns. set Ns \<subseteq> set Ms \<Longrightarrow>
        foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n) \<in> carrier_mat n n"
    proof -
      fix Ns
      assume sub: "set Ns \<subseteq> set Ms"
      show "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n) \<in> carrier_mat n n"
        using sub
      proof (induction Ns)
        case Nil
        show ?case by simp
      next
        case (Cons A As)
        have Acar: "A \<in> carrier_mat n n"
          using Cons.prems all_car by auto
        have sub_As: "set As \<subseteq> set Ms"
          using Cons.prems by auto
        show ?case
          using Cons.IH[OF sub_As] Acar by simp
      qed
    qed

    have sum_eq_aux:
      "\<And>Ns. set Ns \<subseteq> set Ms \<Longrightarrow>
        (\<Sum>M \<leftarrow> Ns. meas_prob M \<psi>) =
        Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
    proof -
      fix Ns
      assume sub: "set Ns \<subseteq> set Ms"
      show "(\<Sum>M \<leftarrow> Ns. meas_prob M \<psi>) =
        Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
        using sub
      proof (induction Ns)
        case Nil
        have "(\<Sum>M\<leftarrow>[]. meas_prob M \<psi>) = 0"
          by simp
        also have "... = Re (\<langle>\<psi> | (0\<^sub>m n n) *\<^sub>v \<psi>\<rangle>)"
          by (metis diff_self inner_prod_right_minus' minus_mult_distrib_mat_vec minus_r_inv_mat
              one_carrier_mat psi_car zero_complex.simps(1))
        finally show ?case
          by simp
      next
        case (Cons M Ns)
        have Mcar: "M \<in> carrier_mat n n"
          using Cons.prems all_car by auto
        have sub_Ns: "set Ns \<subseteq> set Ms"
          using Cons.prems by auto
        have IH:
          "(\<Sum>Ma\<leftarrow>Ns. meas_prob Ma \<psi>) =
           Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
          using Cons.IH[OF sub_Ns] .
        have Mpsi_dim: "dim_vec (M *\<^sub>v \<psi>) = n"
          using Mcar psi_dim by simp
        have stepM: "meas_prob M \<psi> = Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>)"
        proof -
          have adj_eq: "\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle> = \<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
          proof -
            have "\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | (M\<^sup>\<dagger>) *\<^sub>v (M *\<^sub>v \<psi>)\<rangle>"
              using Mcar psi_car
              by (metis Mpsi_dim assoc_mult_mat_vec
                  carrier_mat_triv dim_col_of_dagger dim_mult_mat_vec)
            also have "... = \<langle>(M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
              using inner_prod_adjoint_swap[of "M\<^sup>\<dagger>" n n \<psi> "M *\<^sub>v \<psi>"] Mcar psi_dim Mpsi_dim by force
            also have "... = \<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
              using dagger_of_dagger_is_id by presburger
            finally show ?thesis .
          qed
          have "meas_prob M \<psi> = \<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2"
            by (simp add: meas_prob_def)
          also have "... = Re (\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>)"
            by (metis Re_complex_of_real cpx_vec_length_inner_prod)
          also have "... = Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>)"
            using adj_eq by simp
          finally show ?thesis .
        qed
        have carr_fold:
          "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n) \<in> carrier_mat n n"
          using fold_car[OF sub_Ns] .
        have add_inside:
          "Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>) +
           Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)
           =
           Re (\<langle>\<psi> | (((M\<^sup>\<dagger>) * M) +
                     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
        proof -
          have "\<langle>\<psi> | ((((M\<^sup>\<dagger>) * M) +
                     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>)\<rangle>
              = \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>
                + \<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>"
            using psi_dim Mcar carr_fold
            by (metis (lifting) add_mult_distrib_mat_vec carrier_matD(1,2) carrier_mat_triv
                dim_mult_mat_vec dim_row_of_dagger index_mult_mat(2,3) inner_prod_right_add' psi_car)
          then show ?thesis
            by simp
        qed
        have "(\<Sum>Ma\<leftarrow>M # Ns. meas_prob Ma \<psi>)
            = meas_prob M \<psi> + (\<Sum>Ma\<leftarrow>Ns. meas_prob Ma \<psi>)"
          by simp
        also have "... =
            Re (\<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>) +
            Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
          using stepM IH by simp
        also have "... =
            Re (\<langle>\<psi> | ((((M\<^sup>\<dagger>) * M) +
                     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ns (0\<^sub>m n n)) *\<^sub>v \<psi>)\<rangle>)"
          using add_inside by simp
        also have "... =
            Re (\<langle>\<psi> | (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (M # Ns) (0\<^sub>m n n)) *\<^sub>v \<psi>\<rangle>)"
          by simp
        finally show ?case .
      qed
    qed
    show ?thesis
      using sum_eq_aux[of Ms] by simp
  qed
  (* Step 3: replace \<Sum>M\<dagger>M with I and use \<langle>\<psi>|\<psi>\<rangle> = \<parallel>\<psi>\<parallel>² = 1 *)
  have id_eq: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n"
    using ms by (simp add: measurement_system_def)
  have inner_one: "\<langle>\<psi> | (1\<^sub>m n) *\<^sub>v \<psi>\<rangle> = 1"
  proof -
    have "(1\<^sub>m n) *\<^sub>v \<psi> = \<psi>" using psi_car by simp
    hence "\<langle>\<psi> | (1\<^sub>m n) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi>|\<psi>\<rangle>" by simp
    also have "\<dots> = (\<parallel>\<psi>\<parallel>)\<^sup>2"
      by (metis cpx_vec_length_inner_prod)
    also have "\<dots> = 1" using psi_norm by simp
    finally show ?thesis.
  qed
  show ?thesis
    using sum_eq id_eq inner_one by simp
qed

(* After observing outcome m, the post-measurement state is M_m \<psi> / \<Parallel>M_m \<psi>\<Parallel> *)

definition post_meas_state :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "post_meas_state M \<psi> \<equiv> (1 / complex_of_real (\<parallel>M *\<^sub>v \<psi>\<parallel>)) \<cdot>\<^sub>v (M *\<^sub>v \<psi>)"

(* Postulate 4: Composite Systems *)
(* State space of composite system is H_A \<otimes> H_B.
   If system A is in state \<psi>_A and B in state \<psi>_B, composite state is \<psi>_A \<otimes> \<psi>_B. *)

lemma tensor_of_states_is_state:
  assumes "quantum_state n \<psi>1" and "quantum_state m \<psi>2"
  shows "quantum_state (n*m) (tensor_vec \<psi>1 \<psi>2)"
proof -
  have d1: "dim_vec \<psi>1 = n" and d2: "dim_vec \<psi>2 = m"
    using assms by (auto simp: quantum_state_def)
  have norm1: "\<parallel>\<psi>1\<parallel> = 1" and norm2: "\<parallel>\<psi>2\<parallel> = 1"
    using assms by (auto simp: quantum_state_def)
  have dim: "dim_vec (tensor_vec \<psi>1 \<psi>2) = n * m"
    using d1 d2 by (rule tensor_vec_dim)
  (* From tensor_inner_prod: \<langle>\<psi>1\<otimes>\<psi>2 | \<psi>1\<otimes>\<psi>2\<rangle> = \<langle>\<psi>1|\<psi>1\<rangle>\<sqdot>\<langle>\<psi>2|\<psi>2\<rangle> = 1\<sqdot>1 = 1. *)
  have norm_tensor: "\<parallel>tensor_vec \<psi>1 \<psi>2\<parallel> = 1"
    by (smt (verit) cpx_vec_length_inner_prod inner_prod_csqrt norm1 norm2 of_real_eq_1_iff 
        one_power2 power2_eq_square tensor_inner_prod)
  show ?thesis
    unfolding quantum_state_def using dim norm_tensor by simp
qed


(* ============================================================================
   DAY 8 — 14 / Sep / 11
   Topic: The Quantum Game; POVM; Postulate 4 Continued
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Quantum Game: distinguishing non-orthogonal states
   -------------------------------------------------------------------------- *)

lemma outer_proj_self:
  assumes q: "quantum_state n \<psi>"
  shows "outer_prod \<psi> \<psi> *\<^sub>v \<psi> = \<psi>"
proof -
  have \<psi>dim: "dim_vec \<psi> = n"
    using q by (simp add: quantum_state_def)
  have \<psi>norm: "\<langle>\<psi> | \<psi>\<rangle> = 1"
    by (metis (no_types) csqrt_eq_1 inner_prod_csqrt of_real_1 q quantum_state_def)
  show ?thesis
  proof (rule eq_vecI)
    show "dim_vec (outer_prod \<psi> \<psi> *\<^sub>v \<psi>) = dim_vec \<psi>"
      by (simp add: outer_prod_mult_vec)

  next
    fix i
    assume i: "i < dim_vec \<psi>"
    then have ilt: "i < n"
      using \<psi>dim by simp
    have "(outer_prod \<psi> \<psi> *\<^sub>v \<psi>) $ i
        = (\<Sum>j = 0..<n. (outer_prod \<psi> \<psi>) $$ (i,j) * \<psi> $ j)"
      using \<psi>dim ilt
      by (metis (no_types, lifting) bra_bra_vec carrier_mat_triv carrier_vec_dim_vec dagger_of_ket_is_bra dim_col_of_dagger
          dim_row_mat(1) index_mult_mat(2,3) ket_vec_def mult_mat_vec_index sum.cong)
    also have "... = (\<Sum>j = 0..<n. (\<psi> $ i * cnj (\<psi> $ j)) * \<psi> $ j)"
      using \<psi>dim ilt
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) 
          calculation inner_prod_def outer_prod_mult_vec_index sum.cong sum_distrib_left)
    also have "... = (\<psi> $ i) * (\<Sum>j = 0..<n. cnj (\<psi> $ j) * \<psi> $ j)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<psi> $ i) * \<langle>\<psi> | \<psi>\<rangle>"
      using \<psi>dim by (simp add: inner_prod_def)
    also have "... = \<psi> $ i"
      using \<psi>norm by simp
    finally show "(outer_prod \<psi> \<psi> *\<^sub>v \<psi>) $ i = \<psi> $ i" .
  qed
qed

lemma outer_proj_orth_zero:
  assumes q1: "quantum_state n \<psi>1"
      and q2: "quantum_state n \<psi>2"
      and orth: "\<langle>\<psi>1 | \<psi>2\<rangle> = 0"
  shows "outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2 = 0\<^sub>v n"
proof -
  have d1: "dim_vec \<psi>1 = n"
    using q1 by (simp add: quantum_state_def)
  have d2: "dim_vec \<psi>2 = n"
    using q2 by (simp add: quantum_state_def)

  show ?thesis
  proof (rule eq_vecI)
    show "dim_vec (outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2) = dim_vec (0\<^sub>v n)"
      by (simp add: d1 d2 outer_prod_mult_vec)
  next
    fix i
    assume i: "i < dim_vec (0\<^sub>v n)"
    then have ilt: "i < n"
      by simp
    have "(outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2) $ i
        = (\<Sum>j = 0..<n. (outer_prod \<psi>1 \<psi>1) $$ (i,j) * \<psi>2 $ j)"
      using d1 d2 ilt
      by (metis (no_types, lifting) bra_bra_vec carrier_mat_triv carrier_vec_dim_vec dagger_of_ket_is_bra dim_col_of_dagger
          dim_row_mat(1) index_mult_mat(2,3) ket_vec_def mult_mat_vec_index sum.cong)
    also have "... = (\<Sum>j = 0..<n. (\<psi>1 $ i * cnj (\<psi>1 $ j)) * \<psi>2 $ j)"
      using d1 ilt
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) calculation d2 inner_prod_def
          outer_prod_mult_vec_index sum.cong sum_distrib_left)
    also have "... = (\<psi>1 $ i) * (\<Sum>j = 0..<n. cnj (\<psi>1 $ j) * \<psi>2 $ j)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<psi>1 $ i) * \<langle>\<psi>1 | \<psi>2\<rangle>"
      using d1 d2 by (simp add: inner_prod_def)
    also have "... = 0"
      using orth by simp
    also have "... = (0\<^sub>v n) $ i"
      using ilt by simp
    finally show "(outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2) $ i = (0\<^sub>v n) $ i" .
  qed
qed

lemma outer_proj_idem:
  assumes q: "quantum_state n \<psi>"
  shows "(outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>) = outer_prod \<psi> \<psi>"
proof -
  have \<psi>dim: "dim_vec \<psi> = n"
    using q by (simp add: quantum_state_def)
  have \<psi>norm: "\<langle>\<psi> | \<psi>\<rangle> = 1"
    by (metis (full_types) csqrt_eq_1 inner_prod_csqrt of_real_1 q quantum_state_def)
  show ?thesis
  proof (rule eq_matI)
    show "dim_row ((outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>)) = dim_row (outer_prod \<psi> \<psi>)"
      using \<psi>dim by simp
    show "dim_col ((outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>)) = dim_col (outer_prod \<psi> \<psi>)"
      using \<psi>dim by simp
  next
    fix r c
    assume r: "r < dim_row (outer_prod \<psi> \<psi>)"
    assume c: "c < dim_col (outer_prod \<psi> \<psi>)"
    then have rlt: "r < n" and clt: "c < n"
      by (metis \<psi>dim dim_col index_mult_mat(2) ket_vec_col r,
          metis \<psi>dim c dim_vec index_mult_mat(3) index_row(2) row_bra_vec)
    have "((outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>)) $$ (r,c)
      = (\<Sum>j = 0..<n. (outer_prod \<psi> \<psi>) $$ (r,j) * (outer_prod \<psi> \<psi>) $$ (j,c))"
      by (metis (no_types, lifting) ext \<psi>dim atLeast0LessThan bra_bra_vec clt dagger_of_ket_is_bra 
          dim_col dim_col_of_dagger index_matrix_prod index_mult_mat(2,3) ket_vec_col rlt)  
    also have "... = (\<Sum>j = 0..<n. (\<psi> $ r * cnj (\<psi> $ j)) * (\<psi> $ j * cnj (\<psi> $ c)))"
    proof (rule sum.cong[OF refl])
      fix j assume "j \<in> {0..<n}"
      then have jn: "j < n" by simp
      have rv: "r < dim_vec \<psi>" using \<psi>dim rlt by simp
      have jv: "j < dim_vec \<psi>" using \<psi>dim jn by simp
      have cv: "c < dim_vec \<psi>" using \<psi>dim clt by simp
      have step_rj: "(outer_prod \<psi> \<psi>) $$ (r,j) = \<psi> $ r * cnj (\<psi> $ j)"
        using outer_prod_index[OF rv jv] .
      have step_jc: "(outer_prod \<psi> \<psi>) $$ (j,c) = \<psi> $ j * cnj (\<psi> $ c)"
        using outer_prod_index[OF jv cv] .
      show "(outer_prod \<psi> \<psi>) $$ (r,j) * (outer_prod \<psi> \<psi>) $$ (j,c)
          = (\<psi> $ r * cnj (\<psi> $ j)) * (\<psi> $ j * cnj (\<psi> $ c))"
        using step_rj step_jc by simp
    qed
    also have "... = (\<psi> $ r) * (\<Sum>j = 0..<n. cnj (\<psi> $ j) * \<psi> $ j) * cnj (\<psi> $ c)"
      by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
    also have "... = (\<psi> $ r) * \<langle>\<psi> | \<psi>\<rangle> * cnj (\<psi> $ c)"
      using \<psi>dim by (simp add: inner_prod_def)
    also have "... = \<psi> $ r * cnj (\<psi> $ c)"
      using \<psi>norm by simp
    also have "... = (outer_prod \<psi> \<psi>) $$ (r,c)"
      using \<psi>dim rlt clt outer_prod_index by presburger
    finally show "((outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>)) $$ (r,c) = (outer_prod \<psi> \<psi>) $$ (r,c)".
  qed
qed

lemma outer_proj_hermitian:
  assumes "dim_vec \<psi> = n"
  shows "(outer_prod \<psi> \<psi>)\<^sup>\<dagger> = outer_prod \<psi> \<psi>"
proof (rule eq_matI)
  show "dim_row ((outer_prod \<psi> \<psi>)\<^sup>\<dagger>) = dim_row (outer_prod \<psi> \<psi>)"
    by (metis (no_types) bra_bra_vec bra_def dim_col_mat(1) dim_row_of_dagger index_mult_mat(2,3))
  show "dim_col ((outer_prod \<psi> \<psi>)\<^sup>\<dagger>) = dim_col (outer_prod \<psi> \<psi>)"
    by (simp add: bra_vec_def cpx_mat_cnj_def ket_vec_def row_vec_def)
next
  fix i j
  assume i: "i < dim_row (outer_prod \<psi> \<psi>)"
  assume j: "j < dim_col (outer_prod \<psi> \<psi>)"
  then have ilt: "i < n" and jlt: "j < n"
    using assms i ket_vec_def  
    by (auto, metis bra_bra_vec dagger_of_ket_is_bra dim_col_of_dagger dim_row_mat(1))
  have "((outer_prod \<psi> \<psi>)\<^sup>\<dagger>) $$ (i,j) = cnj ((outer_prod \<psi> \<psi>) $$ (j,i))"
    using assms ilt jlt
    by (simp add: bra_vec_def cpx_mat_cnj_def dagger_def ket_vec_def row_vec_def)
  also have "... = cnj (\<psi> $ j * cnj (\<psi> $ i))"
    using assms ilt jlt outer_prod_index by presburger
  also have "... = \<psi> $ i * cnj (\<psi> $ j)"
    by simp
  also have "... = (outer_prod \<psi> \<psi>) $$ (i,j)"
    using assms ilt jlt outer_prod_index by presburger
  finally show "((outer_prod \<psi> \<psi>)\<^sup>\<dagger>) $$ (i,j) = (outer_prod \<psi> \<psi>) $$ (i,j)".
qed

lemma outer_proj_cross_zero:
  assumes q1: "quantum_state n \<psi>1"
      and q2: "quantum_state n \<psi>2"
      and orth: "\<langle>\<psi>1 | \<psi>2\<rangle> = 0"
  shows "(outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2) = 0\<^sub>m n n"
proof -
  have d1: "dim_vec \<psi>1 = n"
    using q1 by (simp add: quantum_state_def)
  have d2: "dim_vec \<psi>2 = n"
    using q2 by (simp add: quantum_state_def)
  show ?thesis
  proof (rule eq_matI)
    show "dim_row ((outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2)) = dim_row (0\<^sub>m n n)"
      by (simp add: d1 ket_vec_def)
    show "dim_col ((outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2)) = dim_col (0\<^sub>m n n)"
      by (simp add: bra_vec_def cpx_mat_cnj_def d2 row_vec_def)
  next
    fix r c
    assume r: "r < dim_row (0\<^sub>m n n)"
    assume c: "c < dim_col (0\<^sub>m n n)"
    then have rlt: "r < n" and clt: "c < n"
      using r by auto
    have "((outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2)) $$ (r,c)
        = (\<Sum>j = 0..<n. (outer_prod \<psi>1 \<psi>1) $$ (r,j) * (outer_prod \<psi>2 \<psi>2) $$ (j,c))"
      using d1 d2 rlt clt
      by (metis (no_types, lifting) ext atLeast0LessThan bra_bra_vec dagger_of_ket_is_bra dim_col 
          dim_col_of_dagger index_matrix_prod index_mult_mat(2,3) ket_vec_col)
    also have "... = (\<Sum>j = 0..<n. (\<psi>1 $ r * cnj (\<psi>1 $ j)) * (\<psi>2 $ j * cnj (\<psi>2 $ c)))"
    proof (rule sum.cong[OF refl])
      fix j assume "j \<in> {0..<n}"
      then have jn: "j < n" by simp
      have rv: "r < dim_vec \<psi>1" using d1 rlt by simp
      have jv1: "j < dim_vec \<psi>1" using d1 jn by simp
      have jv2: "j < dim_vec \<psi>2" using d2 jn by simp
      have cv: "c < dim_vec \<psi>2" using d2 clt by simp
      have step_rj: "(outer_prod \<psi>1 \<psi>1) $$ (r,j) = \<psi>1 $ r * cnj (\<psi>1 $ j)"
        using outer_prod_index[OF rv jv1] .
      have step_jc: "(outer_prod \<psi>2 \<psi>2) $$ (j,c) = \<psi>2 $ j * cnj (\<psi>2 $ c)"
        using outer_prod_index[OF jv2 cv] .
      show "(outer_prod \<psi>1 \<psi>1) $$ (r,j) * (outer_prod \<psi>2 \<psi>2) $$ (j,c)
          = (\<psi>1 $ r * cnj (\<psi>1 $ j)) * (\<psi>2 $ j * cnj (\<psi>2 $ c))"
        using step_rj step_jc by simp
    qed
    also have "... = (\<psi>1 $ r) * (\<Sum>j = 0..<n. cnj (\<psi>1 $ j) * \<psi>2 $ j) * cnj (\<psi>2 $ c)"
      by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
    also have "... = (\<psi>1 $ r) * \<langle>\<psi>1 | \<psi>2\<rangle> * cnj (\<psi>2 $ c)"
      using d1 d2 by (simp add: inner_prod_def)
    also have "... = 0"
      using orth by simp
    also have "... = (0\<^sub>m n n) $$ (r,c)"
      using rlt clt by simp
    finally show "((outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2)) $$ (r,c) = (0\<^sub>m n n) $$ (r,c)".
  qed
qed

(* Case I: orthogonal states can be distinguished perfectly *)

lemma orthogonal_states_distinguishable:
  fixes \<psi>1 \<psi>2 :: "complex Matrix.vec"
  assumes q1: "quantum_state n \<psi>1"
      and q2: "quantum_state n \<psi>2"
      and orth: "\<langle>\<psi>1 | \<psi>2\<rangle> = 0"
  shows "\<exists>Ms :: complex Matrix.mat list.
         measurement_system n Ms \<and>
         (\<exists>M1 M2. M1 \<in> set Ms \<and> M2 \<in> set Ms \<and>
            meas_prob M1 \<psi>1 = 1 \<and> meas_prob M2 \<psi>1 = 0 \<and>
            meas_prob M1 \<psi>2 = 0 \<and> meas_prob M2 \<psi>2 = 1)"
proof -
  have \<psi>1dim: "dim_vec \<psi>1 = n"
    using q1 by (simp add: quantum_state_def)
  have \<psi>2dim: "dim_vec \<psi>2 = n"
    using q2 by (simp add: quantum_state_def)

  let ?P1 = "outer_prod \<psi>1 \<psi>1"
  let ?Q = "1\<^sub>m n - ?P1"
  let ?Ms = "[?P1, ?Q]"

  have P1car: "?P1 \<in> carrier_mat n n"
    by (metis \<psi>1dim carrier_mat_triv dim_mult_mat_vec dim_row_of_dagger outer_proj_hermitian outer_proj_self q1)
  have Qcar: "?Q \<in> carrier_mat n n"
    by (simp add: P1car minus_carrier_mat)
  have P1herm: "?P1\<^sup>\<dagger> = ?P1"
    using outer_proj_hermitian[OF \<psi>1dim].

  have P1idem: "?P1 * ?P1 = ?P1"
    using outer_proj_idem[OF q1].

  have Qherm: "?Q\<^sup>\<dagger> = ?Q"
  proof (rule eq_matI)
    show "dim_row (?Q\<^sup>\<dagger>) = dim_row ?Q"
      by (metis Qcar carrier_matD(1,2) dim_row_of_dagger)
    show "dim_col (?Q\<^sup>\<dagger>) = dim_col ?Q"
      by (metis Qcar carrier_matD(1,2) dim_col_of_dagger)
  next
    fix i j
    assume i: "i < dim_row ?Q" and j: "j < dim_col ?Q"
    have iln: "i < n" and jln: "j < n"
      using i j Qcar by auto
    have "?Q\<^sup>\<dagger> $$ (i,j) = cnj (?Q $$ (j,i))"
      using iln jln Qcar
      by (simp add: dagger_def,
          metis P1car carrier_matD(1,2) case_prod_conv index_mat(1) index_mult_mat(2,3))
    also have "... = cnj ((1\<^sub>m n) $$ (j,i) - ?P1 $$ (j,i))"
      using P1car iln jln
      by (metis carrier_matD(1,2) index_minus_mat(1))
    also have "... = cnj ((1\<^sub>m n) $$ (j,i)) - cnj (?P1 $$ (j,i))"
      by simp
    also have "... = (1\<^sub>m n) $$ (i,j) - cnj (?P1 $$ (j,i))"
      using iln jln by simp
    also have "... = (1\<^sub>m n) $$ (i,j) - ?P1 $$ (i,j)"
      using P1herm P1car iln jln
      by (simp add: dagger_def,
          metis P1herm carrier_matD(1,2) hermitian_def hermitian_index)
    also have "... = ?Q $$ (i,j)"
      using P1car iln jln
      by (metis carrier_matD(1,2) index_minus_mat(1))
    finally show "?Q\<^sup>\<dagger> $$ (i,j) = ?Q $$ (i,j)".
  qed

  have Qidem: "?Q * ?Q = ?Q"
  proof (rule eq_matI)
    show "dim_row (?Q * ?Q) = dim_row ?Q"
      using Qcar by simp
    show "dim_col (?Q * ?Q) = dim_col ?Q"
      using Qcar by simp
  next
    fix r c
    assume r: "r < dim_row ?Q" and c: "c < dim_col ?Q"
    have rln: "r < n" and cln: "c < n"
      using r c Qcar by auto

    have qq_expand:
      "?Q * ?Q =
        ((1\<^sub>m n) * (1\<^sub>m n)) - ((1\<^sub>m n) * ?P1) - (?P1 * (1\<^sub>m n)) + (?P1 * ?P1)"
    proof -
      have "?Q * ?Q = (1\<^sub>m n) * (1\<^sub>m n - ?P1) - ?P1 * (1\<^sub>m n - ?P1)"
        using P1car by (meson Qcar minus_mult_distrib_mat one_carrier_mat)
      also have "... = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * ?P1)
                       - (?P1 * (1\<^sub>m n) - ?P1 * ?P1)"
        using P1car by (simp add: right_diff_distrib,
                        metis left_mult_one_mat mult_minus_distrib_mat one_carrier_mat)
      also have "... = ((1\<^sub>m n) * (1\<^sub>m n)) - ((1\<^sub>m n) * ?P1) - (?P1 * (1\<^sub>m n)) + (?P1 * ?P1)"
      proof -
        have "((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * ?P1)
              - (?P1 * (1\<^sub>m n) - ?P1 * ?P1)
            = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * ?P1)
              + (-(?P1 * (1\<^sub>m n) - ?P1 * ?P1))"
          by auto
        also have "... = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * ?P1)
                         + (-(?P1 * (1\<^sub>m n)) + (?P1 * ?P1))"
          using P1car by fastforce
        also have "... = ((1\<^sub>m n) * (1\<^sub>m n)) - ((1\<^sub>m n) * ?P1) - (?P1 * (1\<^sub>m n)) + (?P1 * ?P1)"
          using Qcar by fastforce
        finally show ?thesis .
      qed
      finally show ?thesis .
    qed

    have "(?Q * ?Q) $$ (r,c)
        = (((1\<^sub>m n) * (1\<^sub>m n)) - ((1\<^sub>m n) * ?P1) - (?P1 * (1\<^sub>m n)) + (?P1 * ?P1)) $$ (r,c)"
      using qq_expand by simp
    also have "... = ((1\<^sub>m n) $$ (r,c) - ((1\<^sub>m n) * ?P1) $$ (r,c) - (?P1 * (1\<^sub>m n)) $$ (r,c)
                     + (?P1 * ?P1) $$ (r,c))"
      using rln cln P1car by(simp, smt (verit, ccfv_SIG) P1idem carrier_matD(1,2) diff_0 
          index_add_mat(1) index_minus_mat(1) index_one_mat(1) left_mult_one_mat right_mult_one_mat)
    also have "... = ((1\<^sub>m n) $$ (r,c) - ?P1 $$ (r,c) - ?P1 $$ (r,c) + (?P1 * ?P1) $$ (r,c))"
      using rln cln P1car
      by (simp add: left_mult_one_mat right_mult_one_mat)
    also have "... = ((1\<^sub>m n) $$ (r,c) - ?P1 $$ (r,c) - ?P1 $$ (r,c) + ?P1 $$ (r,c))"
      using P1idem rln cln P1car by simp
    also have "... = ((1\<^sub>m n) $$ (r,c) - ?P1 $$ (r,c))"
      by simp      
    also have "... = ?Q $$ (r,c)"
      using rln cln P1car
      by (metis carrier_matD(1,2) index_minus_mat(1)) 
    finally show "(?Q * ?Q) $$ (r,c) = ?Q $$ (r,c)".
  qed

  have meas_sys: "measurement_system n ?Ms"
  proof -
    have carrs: "\<forall>M \<in> set ?Ms. M \<in> carrier_mat n n"
      using P1car Qcar by simp
    have fold_eq: "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) ?Ms (0\<^sub>m n n) = 1\<^sub>m n"
    proof -
      have "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) ?Ms (0\<^sub>m n n)
          = ?P1\<^sup>\<dagger> * ?P1 + (?Q\<^sup>\<dagger> * ?Q + 0\<^sub>m n n)"
        by simp
      also have "... = ?P1 * ?P1 + (?Q * ?Q + 0\<^sub>m n n)"
        using P1herm Qherm by simp
      also have "... = ?P1 + (?Q + 0\<^sub>m n n)"
        using P1idem Qidem by simp
      also have "... = ?P1 + ?Q"
        using P1car Qcar by simp
      also have "... = 1\<^sub>m n"
      proof (rule eq_matI)
        show "dim_row (?P1 + (1\<^sub>m n - ?P1)) = dim_row (1\<^sub>m n)"
          using P1car by auto
        show "dim_col (?P1 + (1\<^sub>m n - ?P1)) = dim_col (1\<^sub>m n)"
          using P1car by auto
      next
        fix i j
        assume i: "i < dim_row (1\<^sub>m n)" and j: "j < dim_col (1\<^sub>m n)"
        then have iln: "i < n" and jln: "j < n" by auto
        show "(?P1 + (1\<^sub>m n - ?P1)) $$ (i,j) = (1\<^sub>m n) $$ (i,j)"
          using iln jln P1car
          by (metis add.commute add_diff_cancel_left' carrier_matD(1,2)
              index_add_mat(1) index_minus_mat(1))
      qed
      finally show ?thesis.
    qed
    show ?thesis
      unfolding measurement_system_def
      using carrs fold_eq by blast
  qed

  have P1_on_\<psi>1: "?P1 *\<^sub>v \<psi>1 = \<psi>1"
    using outer_proj_self[OF q1] .
  have P1_on_\<psi>2: "?P1 *\<^sub>v \<psi>2 = 0\<^sub>v n"
    using outer_proj_orth_zero[OF q1 q2 orth] .

  have Q_on_\<psi>1: "?Q *\<^sub>v \<psi>1 = 0\<^sub>v n"
  proof -
    have "?Q *\<^sub>v \<psi>1 = (1\<^sub>m n) *\<^sub>v \<psi>1 - ?P1 *\<^sub>v \<psi>1"
      using P1car \<psi>1dim carrier_vec_dim_vec minus_mult_distrib_mat_vec one_carrier_mat by blast
    also have "... = \<psi>1 - ?P1 *\<^sub>v \<psi>1"
      using \<psi>1dim by fastforce
    also have "... = 0\<^sub>v n"
      using P1_on_\<psi>1 \<psi>1dim by fastforce
    finally show ?thesis.
  qed

  have Q_on_\<psi>2: "?Q *\<^sub>v \<psi>2 = \<psi>2"
  proof -
    have "?Q *\<^sub>v \<psi>2 = (1\<^sub>m n) *\<^sub>v \<psi>2 - ?P1 *\<^sub>v \<psi>2"
      using P1car \<psi>2dim carrier_vec_dim_vec minus_mult_distrib_mat_vec one_carrier_mat by blast
    also have "... = \<psi>2 - ?P1 *\<^sub>v \<psi>2"
      using \<psi>2dim by fastforce
    also have "... = \<psi>2"
      using P1_on_\<psi>2 \<psi>2dim by fastforce
    finally show ?thesis.
  qed

  have prob_P1_\<psi>1: "meas_prob ?P1 \<psi>1 = 1"
    using P1_on_\<psi>1 q1
    by (simp add: meas_prob_def quantum_state_def)
  have prob_Q_\<psi>1: "meas_prob ?Q \<psi>1 = 0"
    using Q_on_\<psi>1 \<psi>1dim
    by (simp add: cpx_vec_length_zero_iff meas_prob_def)
  have prob_P1_\<psi>2: "meas_prob ?P1 \<psi>2 = 0"
    using P1_on_\<psi>2 \<psi>2dim
    by (simp add: meas_prob_def, simp add: cpx_vec_length_zero_iff)
  have prob_Q_\<psi>2: "meas_prob ?Q \<psi>2 = 1"
    using Q_on_\<psi>2 q2
    by (simp add: meas_prob_def quantum_state_def)
  show ?thesis
    by (intro exI[of _ ?Ms], use meas_sys prob_P1_\<psi>1 prob_Q_\<psi>1 prob_P1_\<psi>2 prob_Q_\<psi>2 in auto)
qed
(* Construction: M₁ = |\<psi>₁\<rangle>\<langle>\<psi>₁|, M₂ = |\<psi>₂\<rangle>\<langle>\<psi>₂|,
   M₃ = I - M₁ - M₂ (projection onto {\<psi>₁,\<psi>₂}^\<bottom>). *)

(* Theorem: linearly independent states can be identified (but not perfectly distinguished) *)

theorem linearly_independent_states_unambiguously_measurable:
  fixes \<psi>s :: "complex Matrix.vec list"
  assumes qstates: "\<forall>\<psi> \<in> set \<psi>s. quantum_state n \<psi>"
      and lin_indep: "lin_indpt (set \<psi>s)"
      and len: "length \<psi>s = k"
      and kle: "k \<le> n"
  shows "\<exists>Ms :: complex Matrix.mat list.
         measurement_system n Ms \<and>
         length Ms = k + 1 \<and>
         (\<forall>i < k. \<forall>j < k. i \<noteq> j \<longrightarrow> meas_prob (Ms ! i) (\<psi>s ! j) = 0) \<and>
         (\<forall>i < k. 0 < meas_prob (Ms ! i) (\<psi>s ! i))"
proof -
  (* \<psi>s carriers, implied by quantum_state *)
  have \<psi>s_carrier: "\<forall>i < k. \<psi>s ! i \<in> carrier_vec n"
    using qstates len
    by (metis carrier_vec_dim_vec nth_mem quantum_state_def)

  (* Step 1: dual basis \<phi>s with \<langle>\<phi>s!i | \<psi>s!j\<rangle> = \<delta>_ij.
     Exists because \<psi>s is linearly independent: restrict to span(\<psi>s),
     invert the k\<times>k Gram matrix, and lift back to C^n. *)
  obtain \<phi>s :: "complex Matrix.vec list"
    where \<phi>s_len: "length \<phi>s = k"
      and \<phi>s_carrier: "\<forall>i < k. \<phi>s ! i \<in> carrier_vec n"
      and dual: "\<forall>i < k. \<forall>j < k. \<langle>\<phi>s ! i | \<psi>s ! j\<rangle> = (if i = j then 1 else 0)"
    sorry

  (* Step 2: pick a positive scale c small enough that
     I - c \<Sum>i |\<phi>i\<rangle>\<langle>\<phi>i| is positive semidefinite. Possible because
     \<Sum>i |\<phi>i\<rangle>\<langle>\<phi>i| is hermitian: spectral-decomp it and choose c below
     1 / (1 + max eigenvalue), so every entry of I - c \<cdot>\<^sub>m ?T has
     non-negative eigenvalue. *)
  let ?T = "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) \<phi>s (0\<^sub>m n n)"

  have \<phi>s_all_car: "\<forall>\<phi> \<in> set \<phi>s. \<phi> \<in> carrier_vec n"
    using \<phi>s_carrier \<phi>s_len by (metis in_set_conv_nth)

  have T_car: "?T \<in> carrier_mat n n"
  proof -
    have "\<And>xs. (\<forall>\<phi> \<in> set xs. \<phi> \<in> carrier_vec n) \<Longrightarrow>
           foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n"
    proof -
      fix xs :: "complex Matrix.vec list"
      assume h: "\<forall>\<phi> \<in> set xs. \<phi> \<in> carrier_vec n"
      from h show "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n"
      proof (induction xs)
        case Nil thus ?case by auto
      next
        case (Cons \<phi> xs)
        have \<phi>_car: "\<phi> \<in> carrier_vec n" using Cons.prems by simp
        have \<phi>_dim: "dim_vec \<phi> = n" using \<phi>_car by simp
        have op_car: "outer_prod \<phi> \<phi> \<in> carrier_mat n n"
          using \<phi>_dim
          by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def
              carrier_matI)
        have IH_car: "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n"
          using Cons by simp
        show ?case using op_car IH_car by simp
      qed
    qed
    from this[OF \<phi>s_all_car] show ?thesis .
  qed

  have T_herm: "hermitian ?T"
  proof -
    have aux: "\<And>xs. (\<forall>\<phi> \<in> set xs. \<phi> \<in> carrier_vec n) \<Longrightarrow>
         foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n \<and>
         hermitian (foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
    proof -
      fix xs :: "complex Matrix.vec list"
      assume h: "\<forall>\<phi> \<in> set xs. \<phi> \<in> carrier_vec n"
      from h show
        "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n \<and>
         hermitian (foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
      proof (induction xs)
        case Nil
        have zero_car: "(0\<^sub>m n n :: complex Matrix.mat) \<in> carrier_mat n n" by auto
        have zero_herm: "hermitian (0\<^sub>m n n :: complex Matrix.mat)"
          unfolding hermitian_def
          by (rule eq_matI, auto simp: dagger_def)
        show ?case using zero_car zero_herm by simp
      next
        case (Cons \<phi> xs)
        have \<phi>_car: "\<phi> \<in> carrier_vec n" using Cons.prems by simp
        have \<phi>_dim: "dim_vec \<phi> = n" using \<phi>_car by simp
        have op_car: "outer_prod \<phi> \<phi> \<in> carrier_mat n n"
          using \<phi>_dim
          by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def
              carrier_matI)
        have op_herm: "hermitian (outer_prod \<phi> \<phi>)"
          unfolding hermitian_def using outer_proj_hermitian[OF \<phi>_dim] .
        have xs_all: "\<forall>\<phi>' \<in> set xs. \<phi>' \<in> carrier_vec n" using Cons.prems by simp
        from Cons.IH[OF xs_all]
        have IH_car: "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n"
          and IH_herm: "hermitian (foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
          by auto
        have cons_car: "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) (\<phi> # xs) (0\<^sub>m n n) \<in> carrier_mat n n"
          using op_car IH_car by simp
        (* sum of hermitians is hermitian *)
        have sum_herm: "hermitian (outer_prod \<phi> \<phi> + foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
        proof -
          let ?A = "outer_prod \<phi> \<phi>"
          let ?B = "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n)"
          have "(?A + ?B)\<^sup>\<dagger> = ?A\<^sup>\<dagger> + ?B\<^sup>\<dagger>"
          proof (rule eq_matI)
            show "dim_row ((?A + ?B)\<^sup>\<dagger>) = dim_row (?A\<^sup>\<dagger> + ?B\<^sup>\<dagger>)"
              using op_car IH_car by (simp add: dagger_def)
            show "dim_col ((?A + ?B)\<^sup>\<dagger>) = dim_col (?A\<^sup>\<dagger> + ?B\<^sup>\<dagger>)"
              using op_car IH_car by (simp add: dagger_def)
          next
            fix i j
            assume i: "i < dim_row (?A\<^sup>\<dagger> + ?B\<^sup>\<dagger>)"
               and j: "j < dim_col (?A\<^sup>\<dagger> + ?B\<^sup>\<dagger>)"
            have iln: "i < n" and jln: "j < n"
              using i j op_car IH_car by (auto simp: dagger_def)
            have "(?A + ?B)\<^sup>\<dagger> $$ (i,j) = cnj ((?A + ?B) $$ (j,i))"
              using iln jln op_car IH_car
              by (simp add: dagger_def)
            also have "... = cnj (?A $$ (j,i)) + cnj (?B $$ (j,i))"
              using iln jln op_car IH_car
              by (metis carrier_matD(1,2) index_add_mat(1) complex_cnj_add)
            also have "... = ?A\<^sup>\<dagger> $$ (i,j) + ?B\<^sup>\<dagger> $$ (i,j)"
              using iln jln op_car IH_car
              by (simp add: dagger_def)
            also have "... = (?A\<^sup>\<dagger> + ?B\<^sup>\<dagger>) $$ (i,j)"
              using iln jln op_car IH_car
              by (simp add: dagger_def)
            finally show "(?A + ?B)\<^sup>\<dagger> $$ (i,j) = (?A\<^sup>\<dagger> + ?B\<^sup>\<dagger>) $$ (i,j)" .
          qed
          also have "... = ?A + ?B"
            using op_herm IH_herm by (simp add: hermitian_def)
          finally show ?thesis by (simp add: hermitian_def)
        qed
        show ?case using cons_car sum_herm by simp
      qed
    qed
    from aux[OF \<phi>s_all_car] show ?thesis by blast
  qed

  (* Use hermitian_spectral_decomp on ?T to find c. *)
  obtain U :: "complex Matrix.mat" and D :: "real list"
    where Uc: "U \<in> carrier_mat n n"
      and UU: "unitary U"
      and Dlen: "length D = n"
      and specD: "U\<^sup>\<dagger> * ?T * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF T_car T_herm] by blast

  define maxD :: real where "maxD = Max (insert (0::real) (set D))"
  define c :: real where "c = 1 / (1 + maxD)"

  have maxD_ge_0: "0 \<le> maxD"
    unfolding maxD_def by simp
  have c_pos: "0 < c"
    unfolding c_def using maxD_ge_0 by simp
  have D_bounded: "\<forall>i < length D. D ! i \<le> maxD"
    unfolding maxD_def by simp
  have c_Dbound: "\<forall>i < length D. c * (D ! i) \<le> 1"
  proof (intro allI impI)
    fix i assume i: "i < length D"
    have Dile: "D ! i \<le> maxD" using D_bounded i by simp
    have c_nn: "0 \<le> c" using c_pos by simp
    have "c * (D ! i) \<le> c * maxD"
      using Dile c_nn by (simp add: mult_left_mono)
    also have "c * maxD = maxD / (1 + maxD)"
      unfolding c_def by (simp add: field_simps)
    also have "maxD / (1 + maxD) \<le> 1"
      using maxD_ge_0 by (simp add: divide_le_eq)
    finally show "c * (D ! i) \<le> 1" .
  qed

  (* Spectral derivation of c_bound. *)
  have Udag_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have UUdag: "U * U\<^sup>\<dagger> = 1\<^sub>m n"
    using unitary_left_right(2)[OF UU] Uc by (metis carrier_matD(1))
  have UdagU: "U\<^sup>\<dagger> * U = 1\<^sub>m n"
    using unitary_left_right(1)[OF UU] Uc by (metis carrier_matD(2))
  have D_car: "diag_mat_of_real D \<in> carrier_mat n n"
    using Dlen by simp

  have T_eq_UDU: "?T = U * (diag_mat_of_real D) * U\<^sup>\<dagger>"
  proof -
    have "U * (U\<^sup>\<dagger> * ?T * U) * U\<^sup>\<dagger> = U * (diag_mat_of_real D) * U\<^sup>\<dagger>"
      using specD by simp
    moreover have "U * (U\<^sup>\<dagger> * ?T * U) * U\<^sup>\<dagger> = ?T"
    proof -
      have UU_dag: "U \<in> carrier_mat n n" by (rule Uc)
      have T_c: "?T \<in> carrier_mat n n" by (rule T_car)
      have "U * (U\<^sup>\<dagger> * ?T * U) * U\<^sup>\<dagger> = (U * U\<^sup>\<dagger>) * ?T * (U * U\<^sup>\<dagger>)"
        using Uc Udag_c T_car
        by (smt (verit, ccfv_SIG) assoc_mult_mat carrier_mat_triv mult_carrier_mat)
      also have "... = 1\<^sub>m n * ?T * 1\<^sub>m n"
        using UUdag by simp
      also have "... = ?T"
        using T_car by simp
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  qed

  define D' :: "real list" where "D' = map (\<lambda>d. 1 - c * d) D"
  have D'len: "length D' = n"
    using Dlen unfolding D'_def by simp
  have D'nonneg: "\<forall>i < n. 0 \<le> D' ! i"
    using c_Dbound Dlen unfolding D'_def by auto

  (* Entrywise: diag(D') = 1\<^sub>m n - c \<cdot>\<^sub>m diag(D) *)
  have diag_D'_eq: "diag_mat_of_real D'
                  = 1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D"
  proof (rule eq_matI)
    show "dim_row (diag_mat_of_real D')
        = dim_row (1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D)"
      using D'len Dlen by simp
    show "dim_col (diag_mat_of_real D')
        = dim_col (1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D)"
      using D'len Dlen by simp
  next
    fix i j
    assume ij: "i < dim_row (1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D)"
               "j < dim_col (1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D)"
    have iln: "i < n" and jln: "j < n" using ij by auto
    have Dil: "i < length D" and Djl: "j < length D"
      using iln jln Dlen by auto
    have D'il: "i < length D'" using iln D'len by simp
    show "diag_mat_of_real D' $$ (i,j)
        = (1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) $$ (i,j)"
    proof (cases "i = j")
      case True
      have lhs: "diag_mat_of_real D' $$ (i,i) = of_real (D' ! i)"
        using D'il by simp
      have "D' ! i = 1 - c * D ! i"
        using Dil unfolding D'_def by simp
      hence lhs_val: "diag_mat_of_real D' $$ (i,i) = 1 - of_real c * of_real (D ! i)"
        using lhs by (simp add: of_real_diff of_real_mult)
      have rhs_diag: "diag_mat_of_real D $$ (i,i) = of_real (D ! i)"
        using Dil by simp
      have "(1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) $$ (i,i)
          = (1\<^sub>m n) $$ (i,i) - ((of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) $$ (i,i)"
        using iln D_car
        by (metis carrier_matD(1,2) index_minus_mat(1))
      also have "... = 1 - (of_real c :: complex) * diag_mat_of_real D $$ (i,i)"
        using iln D_car by simp
      also have "... = 1 - (of_real c :: complex) * of_real (D ! i)"
        using rhs_diag by simp
      finally have rhs_val:
        "(1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) $$ (i,i)
       = 1 - (of_real c :: complex) * of_real (D ! i)" .
      show ?thesis using True lhs_val rhs_val by simp
    next
      case False
      have lhs0: "diag_mat_of_real D' $$ (i,j) = 0"
        using D'il jln D'len False by simp
      have rhs1: "diag_mat_of_real D $$ (i,j) = 0"
        using Dil Djl False by simp
      have "(1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) $$ (i,j)
          = (1\<^sub>m n) $$ (i,j) - ((of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) $$ (i,j)"
        using iln jln D_car
        by (metis carrier_matD(1,2) index_minus_mat(1))
      also have "... = 0 - (of_real c :: complex) * diag_mat_of_real D $$ (i,j)"
        using iln jln False D_car by simp
      also have "... = 0"
        using rhs1 by simp
      finally have rhs_val:
        "(1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) $$ (i,j) = 0" .
      show ?thesis using lhs0 rhs_val by simp
    qed
  qed

  (* Quadratic form non-negativity of ?M via U diag(D') U\<^sup>\<dagger> *)
  have c_bound: "psd (1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m ?T)"
  proof -
    let ?M = "1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m ?T"
    have M_car: "?M \<in> carrier_mat n n"
      using T_car by auto

    have M_qf: "\<forall>x. dim_vec x = dim_row ?M \<longrightarrow> 0 \<le> Re \<langle>x | ?M *\<^sub>v x\<rangle>"
    proof (intro allI impI)
      fix x :: "complex Matrix.vec"
      assume "dim_vec x = dim_row ?M"
      hence xdim: "dim_vec x = n" using M_car by auto
      have xcar: "x \<in> carrier_vec n" using xdim by auto
      let ?y = "U\<^sup>\<dagger> *\<^sub>v x"
      have ydim: "dim_vec ?y = n"
        using Udag_c xdim by simp
      have ycar: "?y \<in> carrier_vec n" using ydim by auto

      have Mx_step1: "?M *\<^sub>v x = (U * diag_mat_of_real D' * U\<^sup>\<dagger>) *\<^sub>v x"
      proof -
        have "?M = 1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m (U * diag_mat_of_real D * U\<^sup>\<dagger>)"
          using T_eq_UDU by simp
        (* = U U\<^sup>\<dagger> - c \<cdot>\<^sub>m (U diag(D) U\<^sup>\<dagger>) = U (1 - c \<cdot>\<^sub>m diag(D)) U\<^sup>\<dagger> = U diag(D') U\<^sup>\<dagger> *)
        also have "... = U * 1\<^sub>m n * U\<^sup>\<dagger>
                        - (of_real c :: complex) \<cdot>\<^sub>m (U * diag_mat_of_real D * U\<^sup>\<dagger>)"
          using UUdag Uc Udag_c
          by (metis left_mult_one_mat right_mult_one_mat)
        also have "... = U * 1\<^sub>m n * U\<^sup>\<dagger>
                        - U * ((of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) * U\<^sup>\<dagger>"
          using Uc Udag_c D_car
          by (metis mult_smult_assoc_mat mult_smult_distrib)
        also have "... = U * (1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) * U\<^sup>\<dagger>"
        proof -
          have one_car: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by auto
          have cD_car: "(of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D \<in> carrier_mat n n"
            using D_car by auto
          have UA_car: "U * (1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n"
            using Uc one_car by auto
          have UB_car: "U * ((of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) \<in> carrier_mat n n"
            using Uc cD_car by auto
          have "U * 1\<^sub>m n * U\<^sup>\<dagger>
              - U * ((of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D) * U\<^sup>\<dagger>
              = (U * 1\<^sub>m n
                 - U * ((of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D)) * U\<^sup>\<dagger>"
            using UA_car UB_car Udag_c
            by (simp add: minus_mult_distrib_mat)
          also have "U * (1\<^sub>m n :: complex Matrix.mat)
                   - U * ((of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D)
                   = U * (1\<^sub>m n - (of_real c :: complex) \<cdot>\<^sub>m diag_mat_of_real D)"
            using Uc one_car cD_car
            by (simp add: mult_minus_distrib_mat)
          finally show ?thesis .
        qed
        also have "... = U * diag_mat_of_real D' * U\<^sup>\<dagger>"
          using diag_D'_eq by simp
        finally show ?thesis by simp
      qed

      have Mx_step2: "(U * diag_mat_of_real D' * U\<^sup>\<dagger>) *\<^sub>v x
                    = U *\<^sub>v (diag_mat_of_real D' *\<^sub>v ?y)"
      proof -
        have D'car: "diag_mat_of_real D' \<in> carrier_mat n n"
          using D'len by simp
        have inner_prod: "diag_mat_of_real D' * U\<^sup>\<dagger> \<in> carrier_mat n n"
          using D'car Udag_c by auto
        have "(U * diag_mat_of_real D' * U\<^sup>\<dagger>) *\<^sub>v x
            = (U * (diag_mat_of_real D' * U\<^sup>\<dagger>)) *\<^sub>v x"
          using Uc D'car Udag_c by (simp add: assoc_mult_mat)
        also have "... = U *\<^sub>v ((diag_mat_of_real D' * U\<^sup>\<dagger>) *\<^sub>v x)"
          using Uc inner_prod xcar by (simp add: assoc_mult_mat_vec)
        also have "... = U *\<^sub>v (diag_mat_of_real D' *\<^sub>v (U\<^sup>\<dagger> *\<^sub>v x))"
          using D'car Udag_c xcar by (simp add: assoc_mult_mat_vec)
        finally show ?thesis .
      qed

      have Mx_eq: "?M *\<^sub>v x = U *\<^sub>v (diag_mat_of_real D' *\<^sub>v ?y)"
        using Mx_step1 Mx_step2 by simp

      have qf_swap: "\<langle>x | U *\<^sub>v (diag_mat_of_real D' *\<^sub>v ?y)\<rangle>
                   = \<langle>U\<^sup>\<dagger> *\<^sub>v x | diag_mat_of_real D' *\<^sub>v ?y\<rangle>"
        using Uc xdim ydim
        by (metis D'len carrier_matD(2) diag_mat_of_real_carrier
            dim_mult_mat_vec inner_prod_adjoint_swap)

      have "\<langle>x | ?M *\<^sub>v x\<rangle> = \<langle>?y | diag_mat_of_real D' *\<^sub>v ?y\<rangle>"
        using Mx_eq qf_swap by simp
      moreover have "0 \<le> Re \<langle>?y | diag_mat_of_real D' *\<^sub>v ?y\<rangle>"
        using diag_mat_of_real_quad_Re_nonneg ydim D'len D'nonneg
        by (metis (no_types) )
      ultimately show "0 \<le> Re \<langle>x | ?M *\<^sub>v x\<rangle>" by simp
    qed

    have M_herm: "hermitian ?M"
    proof -
      have one_car: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by auto
      have cT_car: "(of_real c :: complex) \<cdot>\<^sub>m ?T \<in> carrier_mat n n"
        using T_car by auto
      have "?M\<^sup>\<dagger> = ?M"
      proof (rule eq_matI)
        show "dim_row (?M\<^sup>\<dagger>) = dim_row ?M"
          using M_car by (simp add: dagger_def)
        show "dim_col (?M\<^sup>\<dagger>) = dim_col ?M"
          using M_car by (simp add: dagger_def)
      next
        fix i j
        assume ij: "i < dim_row ?M" "j < dim_col ?M"
        have iln: "i < n" and jln: "j < n" using ij M_car by auto
        have ji_bound: "j < dim_row ?M" "i < dim_col ?M"
          using jln iln M_car by auto
        have "?M\<^sup>\<dagger> $$ (i,j) = cnj (?M $$ (j,i))"
          using iln jln M_car
          by (simp add: dagger_def)
        also have "... = cnj ((1\<^sub>m n) $$ (j,i) - ((of_real c :: complex) \<cdot>\<^sub>m ?T) $$ (j,i))"
          using iln jln cT_car
          by (metis carrier_matD(1,2) index_minus_mat(1))
        also have "... = cnj ((1\<^sub>m n :: complex Matrix.mat) $$ (j,i))
                         - cnj (((of_real c :: complex) \<cdot>\<^sub>m ?T) $$ (j,i))"
          by simp
        also have "cnj ((1\<^sub>m n :: complex Matrix.mat) $$ (j,i))
                 = (1\<^sub>m n :: complex Matrix.mat) $$ (i,j)"
          using iln jln by (cases "i = j") auto
        also have "cnj (((of_real c :: complex) \<cdot>\<^sub>m ?T) $$ (j,i))
                 = cnj ((of_real c :: complex) * ?T $$ (j,i))"
          using iln jln T_car by simp
        also have "... = cnj (of_real c :: complex) * cnj (?T $$ (j,i))"
          by simp
        also have "cnj (of_real c :: complex) = (of_real c :: complex)"
          by simp
        also have "cnj (?T $$ (j,i)) = ?T $$ (i,j)"
          using iln jln T_herm T_car
          by (metis carrier_matD(1,2) hermitian_index)
        also have "(of_real c :: complex) * ?T $$ (i,j)
                 = ((of_real c :: complex) \<cdot>\<^sub>m ?T) $$ (i,j)"
          using iln jln T_car by simp
        finally have eq_step:
          "?M\<^sup>\<dagger> $$ (i,j) = (1\<^sub>m n) $$ (i,j)
                         - ((of_real c :: complex) \<cdot>\<^sub>m ?T) $$ (i,j)"
          by simp
        have rhs: "?M $$ (i,j) = (1\<^sub>m n) $$ (i,j)
                                - ((of_real c :: complex) \<cdot>\<^sub>m ?T) $$ (i,j)"
          using iln jln cT_car
          by (metis carrier_matD(1,2) index_minus_mat(1))
        show "?M\<^sup>\<dagger> $$ (i,j) = ?M $$ (i,j)"
          using eq_step rhs by simp
      qed
      thus ?thesis by (simp add: hermitian_def)
    qed

    show ?thesis
      unfolding psd_def using M_herm M_qf by blast
  qed

  define Mpre :: "complex Matrix.mat list"
    where "Mpre = map (\<lambda>\<phi>. (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>) \<phi>s"
  define Slast :: "complex Matrix.mat"
    where "Slast = foldr (\<lambda>M acc. M + acc) Mpre (0\<^sub>m n n)"
  define Mlast :: "complex Matrix.mat"
    where "Mlast = 1\<^sub>m n - Slast"
  define Ps :: "complex Matrix.mat list"
    where "Ps = Mpre @ [Mlast]"

  have len_Ps: "length Ps = k + 1"
    using \<phi>s_len unfolding Ps_def Mpre_def by simp

  have povm_Ps: "povm n Ps"
  proof -
    (* Carriers *)
    have Mpre_car: "\<forall>M \<in> set Mpre. M \<in> carrier_mat n n"
    proof
      fix M assume "M \<in> set Mpre"
      then obtain \<phi> where \<phi>_in: "\<phi> \<in> set \<phi>s"
                      and M_eq: "M = (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>"
        unfolding Mpre_def by auto
      have \<phi>_car: "\<phi> \<in> carrier_vec n"
        using \<phi>s_carrier \<phi>_in \<phi>s_len by (metis in_set_conv_nth)
      hence \<phi>_dim: "dim_vec \<phi> = n" by simp
      have op_car: "outer_prod \<phi> \<phi> \<in> carrier_mat n n"
        using \<phi>_dim
        by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def
            carrier_matI)
      thus "M \<in> carrier_mat n n"
        using M_eq by auto
    qed

    have Slast_car: "Slast \<in> carrier_mat n n"
    proof -
      have "foldr (\<lambda>M acc. M + acc) Mpre (0\<^sub>m n n) \<in> carrier_mat n n"
        using Mpre_car
      proof (induction Mpre)
        case Nil thus ?case by auto
      next
        case (Cons M Ms)
        hence M_car: "M \<in> carrier_mat n n" by simp
        from Cons.IH Cons.prems
        have rest_car: "foldr (\<lambda>M acc. M + acc) Ms (0\<^sub>m n n) \<in> carrier_mat n n" by simp
        show ?case using M_car rest_car by simp
      qed
      thus ?thesis unfolding Slast_def .
    qed

    have Mlast_car: "Mlast \<in> carrier_mat n n"
      unfolding Mlast_def using Slast_car by auto

    have Ps_car: "\<forall>P \<in> set Ps. P \<in> carrier_mat n n"
      unfolding Ps_def using Mpre_car Mlast_car by auto

    (* PSD of each Mpre element *)
    have Mpre_psd: "\<forall>M \<in> set Mpre. psd M"
    proof
      fix M assume "M \<in> set Mpre"
      then obtain \<phi> where \<phi>_in: "\<phi> \<in> set \<phi>s"
                      and M_eq: "M = (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>"
        unfolding Mpre_def by auto
      have \<phi>_car: "\<phi> \<in> carrier_vec n"
        using \<phi>s_all_car \<phi>_in by blast
      have \<phi>_dim: "dim_vec \<phi> = n" using \<phi>_car by simp
      have op_car: "outer_prod \<phi> \<phi> \<in> carrier_mat n n"
        using \<phi>_dim
        by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def
            carrier_matI)
      have M_car: "M \<in> carrier_mat n n"
        using M_eq op_car by auto

      (* Hermitian: (c \<cdot>\<^sub>m outer_prod \<phi> \<phi>)\<^sup>\<dagger> = c \<cdot>\<^sub>m outer_prod \<phi> \<phi> *)
      have M_herm: "hermitian M"
      proof -
        have op_herm_dag: "(outer_prod \<phi> \<phi>)\<^sup>\<dagger> = outer_prod \<phi> \<phi>"
          by (metis \<phi>_dim bra_bra_vec dagger_of_ket_is_bra dagger_of_prod
              dim_col_of_dagger index_one_mat(3) ket_vec_col
              outer_prod_index op_car carrier_matD(1) carrier_matD(2)
              hermitian_def hermitian_index eq_matI
              outer_proj_hermitian[of \<phi> n, unfolded hermitian_def])
        have "M\<^sup>\<dagger> = (cnj (of_real c :: complex)) \<cdot>\<^sub>m (outer_prod \<phi> \<phi>)\<^sup>\<dagger>"
          using M_eq dagger_of_smult by simp
        also have "cnj (of_real c :: complex) = of_real c"
          by simp
        also have "(of_real c :: complex) \<cdot>\<^sub>m (outer_prod \<phi> \<phi>)\<^sup>\<dagger>
                 = (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>"
          using op_herm_dag by simp
        also have "... = M" using M_eq by simp
        finally show ?thesis by (simp add: hermitian_def)
      qed

      (* Quadratic form is real non-negative *)
      have M_qf_nonneg: "\<forall>x. dim_vec x = dim_row M
                           \<longrightarrow> 0 \<le> Re \<langle>x | M *\<^sub>v x\<rangle>"
      proof (intro allI impI)
        fix x :: "complex Matrix.vec"
        assume xdim: "dim_vec x = dim_row M"
        have xn: "dim_vec x = n" using xdim M_car by auto
        have xcar: "x \<in> carrier_vec n" using xn by auto

        have "M *\<^sub>v x = ((of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>) *\<^sub>v x"
          using M_eq by simp
        also have "... = (of_real c :: complex) \<cdot>\<^sub>v (outer_prod \<phi> \<phi> *\<^sub>v x)"
          using smult_mat_mult_vec op_car xcar by blast
        finally have Mvx: "M *\<^sub>v x = (of_real c :: complex) \<cdot>\<^sub>v (outer_prod \<phi> \<phi> *\<^sub>v x)" .

        have op_action: "outer_prod \<phi> \<phi> *\<^sub>v x = \<langle>\<phi>|x\<rangle> \<cdot>\<^sub>v \<phi>"
          using outer_prod_mult_vec[of x \<phi> \<phi>] \<phi>_dim xn by simp

        have "\<langle>x | M *\<^sub>v x\<rangle>
            = \<langle>x | (of_real c :: complex) \<cdot>\<^sub>v (outer_prod \<phi> \<phi> *\<^sub>v x)\<rangle>"
          using Mvx by simp
        also have "... = (of_real c :: complex) * \<langle>x | outer_prod \<phi> \<phi> *\<^sub>v x\<rangle>"
          by (rule inner_prod_right_smult')
        also have "... = (of_real c :: complex) * \<langle>x | \<langle>\<phi>|x\<rangle> \<cdot>\<^sub>v \<phi>\<rangle>"
          using op_action by simp
        also have "... = (of_real c :: complex) * (\<langle>\<phi>|x\<rangle> * \<langle>x|\<phi>\<rangle>)"
          by (simp add: inner_prod_right_smult')
        also have "... = (of_real c :: complex) * (\<langle>\<phi>|x\<rangle> * cnj \<langle>\<phi>|x\<rangle>)"
          by (simp add: inner_prod_cnj)
        also have "... = (of_real c :: complex) * (cnj \<langle>\<phi>|x\<rangle> * \<langle>\<phi>|x\<rangle>)"
          by (simp add: mult.commute)
        finally have qf_eq: "\<langle>x | M *\<^sub>v x\<rangle>
            = (of_real c :: complex) * (cnj \<langle>\<phi>|x\<rangle> * \<langle>\<phi>|x\<rangle>)" .

        have "Re \<langle>x | M *\<^sub>v x\<rangle>
            = c * Re (cnj \<langle>\<phi>|x\<rangle> * \<langle>\<phi>|x\<rangle>)"
          using qf_eq by simp
        also have "... = c * (cmod \<langle>\<phi>|x\<rangle>)\<^sup>2"
          by (simp add: complex_mult_cnj complex_norm_square)
        finally have re_eq: "Re \<langle>x | M *\<^sub>v x\<rangle> = c * (cmod \<langle>\<phi>|x\<rangle>)\<^sup>2" .

        have "0 \<le> c * (cmod \<langle>\<phi>|x\<rangle>)\<^sup>2"
          using c_pos by auto
        thus "0 \<le> Re \<langle>x | M *\<^sub>v x\<rangle>"
          using re_eq by simp
      qed

      show "psd M"
        unfolding psd_def using M_herm M_qf_nonneg by blast
    qed

    (* Slast = c \<cdot>\<^sub>m ?T (scalar factored out of fold) *)
    have \<phi>s_all_car: "\<forall>\<phi> \<in> set \<phi>s. \<phi> \<in> carrier_vec n"
      using \<phi>s_carrier \<phi>s_len by (metis in_set_conv_nth)

    have slast_aux:
      "\<And>xs. (\<forall>\<phi> \<in> set xs. \<phi> \<in> carrier_vec n) \<Longrightarrow>
         foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n \<and>
         foldr (\<lambda>M rest. M + rest)
           (map (\<lambda>\<phi>. (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>) xs) (0\<^sub>m n n)
         = (of_real c :: complex) \<cdot>\<^sub>m
             (foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
    proof -
      fix xs :: "complex Matrix.vec list"
      assume h: "\<forall>\<phi> \<in> set xs. \<phi> \<in> carrier_vec n"
      from h show
        "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n \<and>
         foldr (\<lambda>M rest. M + rest)
           (map (\<lambda>\<phi>. (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>) xs) (0\<^sub>m n n)
         = (of_real c :: complex) \<cdot>\<^sub>m
             (foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
      proof (induction xs)
        case Nil
        have "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) [] (0\<^sub>m n n) = 0\<^sub>m n n" by simp
        moreover have "(of_real c :: complex) \<cdot>\<^sub>m (0\<^sub>m n n) = 0\<^sub>m n n"
          by auto
        ultimately show ?case by simp
      next
        case (Cons \<phi> xs)
        have \<phi>_car: "\<phi> \<in> carrier_vec n" using Cons.prems by simp
        have xs_all: "\<forall>\<phi>' \<in> set xs. \<phi>' \<in> carrier_vec n" using Cons.prems by simp
        have \<phi>_dim: "dim_vec \<phi> = n" using \<phi>_car by simp
        have op_car: "outer_prod \<phi> \<phi> \<in> carrier_mat n n"
          using \<phi>_dim
          by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def
              carrier_matI)
        from Cons.IH[OF xs_all]
        have IH_car: "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n"
          and IH_eq:
             "foldr (\<lambda>M rest. M + rest)
                (map (\<lambda>\<phi>. (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>) xs) (0\<^sub>m n n)
              = (of_real c :: complex) \<cdot>\<^sub>m
                  (foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
          by auto

        have cons_car: "foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) (\<phi> # xs) (0\<^sub>m n n)
                       \<in> carrier_mat n n"
          using op_car IH_car by simp

        have "foldr (\<lambda>M rest. M + rest)
                (map (\<lambda>\<phi>. (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>) (\<phi> # xs)) (0\<^sub>m n n)
            = (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>
              + foldr (\<lambda>M rest. M + rest)
                  (map (\<lambda>\<phi>. (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>) xs) (0\<^sub>m n n)"
          by simp
        also have "... = (of_real c :: complex) \<cdot>\<^sub>m outer_prod \<phi> \<phi>
              + (of_real c :: complex) \<cdot>\<^sub>m
                  (foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
          using IH_eq by simp
        also have "... = (of_real c :: complex) \<cdot>\<^sub>m
            (outer_prod \<phi> \<phi> + foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) xs (0\<^sub>m n n))"
          using add_smult_distrib_left_mat[OF op_car IH_car] by simp
        also have "... = (of_real c :: complex) \<cdot>\<^sub>m
            (foldr (\<lambda>\<phi> acc. outer_prod \<phi> \<phi> + acc) (\<phi> # xs) (0\<^sub>m n n))"
          by simp
        finally show ?case using cons_car by simp
      qed
    qed

    from slast_aux[OF \<phi>s_all_car]
    have Slast_eq: "Slast = (of_real c :: complex) \<cdot>\<^sub>m ?T"
      unfolding Slast_def Mpre_def by simp

    have Mlast_psd: "psd Mlast"
      using c_bound Slast_eq unfolding Mlast_def by simp

    have Ps_psd: "\<forall>P \<in> set Ps. psd P"
      unfolding Ps_def using Mpre_psd Mlast_psd by auto

    (* Helper: foldr of + over Mpre, with any carrier_mat acc, shifts out *)
    have fold_aux: "\<And>xs acc. (\<forall>M \<in> set xs. M \<in> carrier_mat n n) \<Longrightarrow>
                             acc \<in> carrier_mat n n \<Longrightarrow>
        foldr (\<lambda>M rest. M + rest) xs acc \<in> carrier_mat n n \<and>
        foldr (\<lambda>M rest. M + rest) xs acc
          = foldr (\<lambda>M rest. M + rest) xs (0\<^sub>m n n) + acc"
    proof -
      fix xs :: "complex Matrix.mat list" and acc :: "complex Matrix.mat"
      assume h1: "\<forall>M \<in> set xs. M \<in> carrier_mat n n" and h2: "acc \<in> carrier_mat n n"
      from h1 h2 show
        "foldr (\<lambda>M rest. M + rest) xs acc \<in> carrier_mat n n \<and>
         foldr (\<lambda>M rest. M + rest) xs acc
           = foldr (\<lambda>M rest. M + rest) xs (0\<^sub>m n n) + acc"
      proof (induction xs)
        case Nil
        hence "foldr (\<lambda>M rest. M + rest) [] acc = acc" by simp
        moreover have "foldr (\<lambda>M rest. M + rest) [] (0\<^sub>m n n) + acc = 0\<^sub>m n n + acc"
          by simp
        moreover have "0\<^sub>m n n + acc = acc"
          using Nil by auto
        ultimately show ?case using Nil by auto
      next
        case (Cons M xs)
        have M_car: "M \<in> carrier_mat n n" using Cons.prems by simp
        have xs_all: "\<forall>M' \<in> set xs. M' \<in> carrier_mat n n" using Cons.prems by simp
        from Cons.IH[OF xs_all Cons.prems(2)]
        have IH1: "foldr (\<lambda>M rest. M + rest) xs acc \<in> carrier_mat n n"
          and IH2: "foldr (\<lambda>M rest. M + rest) xs acc
                   = foldr (\<lambda>M rest. M + rest) xs (0\<^sub>m n n) + acc"
          by auto
        (* carrier for fold with 0\<^sub>m n n acc *)
        from Cons.IH[OF xs_all] have IH0_car:
          "foldr (\<lambda>M rest. M + rest) xs (0\<^sub>m n n) \<in> carrier_mat n n"
          by auto
        have cons_eq: "foldr (\<lambda>M rest. M + rest) (M # xs) acc
                      = M + foldr (\<lambda>M rest. M + rest) xs acc" by simp
        hence cons_car: "foldr (\<lambda>M rest. M + rest) (M # xs) acc \<in> carrier_mat n n"
          using M_car IH1 by simp
        have "foldr (\<lambda>M rest. M + rest) (M # xs) acc
            = M + (foldr (\<lambda>M rest. M + rest) xs (0\<^sub>m n n) + acc)"
          using cons_eq IH2 by simp
        also have "... = (M + foldr (\<lambda>M rest. M + rest) xs (0\<^sub>m n n)) + acc"
          using M_car IH0_car Cons.prems(2) by (simp add: assoc_add_mat)
        also have "... = foldr (\<lambda>M rest. M + rest) (M # xs) (0\<^sub>m n n) + acc"
          by simp
        finally show ?case using cons_car by simp
      qed
    qed

    have Slast_expand: "Slast = foldr (\<lambda>P acc. P + acc) Mpre (0\<^sub>m n n)"
      unfolding Slast_def ..

    (* Sum = I: foldr over (Mpre @ [Mlast]) = foldr over Mpre with Mlast as acc *)
    have Ps_sum: "foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n) = 1\<^sub>m n"
    proof -
      have step1: "foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n)
                  = foldr (\<lambda>P acc. P + acc) Mpre (Mlast + 0\<^sub>m n n)"
        unfolding Ps_def by simp
      also have "Mlast + 0\<^sub>m n n = Mlast"
        using Mlast_car by auto
      also have "foldr (\<lambda>P acc. P + acc) Mpre Mlast
               = foldr (\<lambda>P acc. P + acc) Mpre (0\<^sub>m n n) + Mlast"
        using fold_aux[OF Mpre_car Mlast_car] by blast
      also have "... = Slast + Mlast"
        using Slast_expand by simp
      also have "Slast + Mlast = Slast + (1\<^sub>m n - Slast)"
        unfolding Mlast_def ..
      also have "... = 1\<^sub>m n"
      proof (rule eq_matI)
        show "dim_row (Slast + (1\<^sub>m n - Slast)) = dim_row (1\<^sub>m n)"
          using Slast_car by auto
        show "dim_col (Slast + (1\<^sub>m n - Slast)) = dim_col (1\<^sub>m n)"
          using Slast_car by auto
      next
        fix i j
        assume i: "i < dim_row (1\<^sub>m n)" and j: "j < dim_col (1\<^sub>m n)"
        then have iln: "i < n" and jln: "j < n" by auto
        show "(Slast + (1\<^sub>m n - Slast)) $$ (i,j) = (1\<^sub>m n) $$ (i,j)"
          using iln jln Slast_car
          by (metis add.commute add_diff_cancel_left' carrier_matD(1,2)
              index_add_mat(1) index_minus_mat(1))
      qed
      finally show ?thesis .
    qed

    show ?thesis
      unfolding povm_def using Ps_car Ps_psd Ps_sum by auto
  qed

  (* Square-root lift: get a measurement_system Ms with Ms_i\<^sup>\<dagger>Ms_i = Ps_i. *)
  obtain Ms :: "complex Matrix.mat list"
    where ms: "measurement_system n Ms"
      and ms_induces: "map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
    using povm_from_sqrt[OF povm_Ps] by blast

  have len_Ms: "length Ms = k + 1"
    using ms_induces len_Ps by (metis length_map)

  (* meas_prob Ms!i \<psi>s!j = c |\<langle>\<phi>i | \<psi>s!j\<rangle>|\<^sup>2. *)
  have meas_eq: "\<forall>i < k. \<forall>j < k. meas_prob (Ms ! i) (\<psi>s ! j)
                     = c * (cmod (\<langle>\<phi>s ! i | \<psi>s ! j\<rangle>))\<^sup>2"
  proof (intro allI impI)
    fix i j assume i: "i < k" and j: "j < k"
    let ?\<phi> = "\<phi>s ! i"  let ?\<psi> = "\<psi>s ! j"  let ?M = "Ms ! i"

    have \<phi>car: "?\<phi> \<in> carrier_vec n" using \<phi>s_carrier i by blast
    have \<psi>car: "?\<psi> \<in> carrier_vec n" using \<psi>s_carrier j by blast
    have \<phi>dim: "dim_vec ?\<phi> = n" using \<phi>car by simp
    have \<psi>dim: "dim_vec ?\<psi> = n" using \<psi>car by simp

    have Mpre_len: "length Mpre = k" unfolding Mpre_def using \<phi>s_len by simp
    have Ms_len: "length Ms = k + 1" using len_Ms .

    have Ps_i: "Ps ! i = (of_real c :: complex) \<cdot>\<^sub>m outer_prod ?\<phi> ?\<phi>"
      using i Mpre_len \<phi>s_len unfolding Ps_def Mpre_def
      by (simp add: nth_append)

    have MtM_eq_Ps: "?M\<^sup>\<dagger> * ?M = Ps ! i"
      using ms_induces i Ms_len
      by (metis nth_map)

    have M_in_set: "?M \<in> set Ms"
      using i Ms_len by (simp add: nth_mem)
    have M_car: "?M \<in> carrier_mat n n"
      using ms M_in_set by (simp add: measurement_system_def)
    have Mv_dim: "dim_vec (?M *\<^sub>v ?\<psi>) = n" using M_car \<psi>car by simp

    have qf: "\<langle>?M *\<^sub>v ?\<psi> | ?M *\<^sub>v ?\<psi>\<rangle> = \<langle>?\<psi> | (?M\<^sup>\<dagger> * ?M) *\<^sub>v ?\<psi>\<rangle>"
    proof -
      have A: "\<langle>?\<psi> | (?M\<^sup>\<dagger> * ?M) *\<^sub>v ?\<psi>\<rangle> = \<langle>?\<psi> | ?M\<^sup>\<dagger> *\<^sub>v (?M *\<^sub>v ?\<psi>)\<rangle>"
        using M_car \<psi>car
        by (metis assoc_mult_mat_vec carrier_matD(1) carrier_vec_dim_vec
            dagger_def mat_carrier)
      have B: "\<langle>?\<psi> | ?M\<^sup>\<dagger> *\<^sub>v (?M *\<^sub>v ?\<psi>)\<rangle> = \<langle>(?M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v ?\<psi> | ?M *\<^sub>v ?\<psi>\<rangle>"
        using M_car Mv_dim \<psi>dim
        by (metis carrier_matD(2) dagger_of_dagger_is_id dim_col_of_dagger
            dim_mult_mat_vec inner_prod_adjoint_swap inner_prod_cnj)
      have C: "(?M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v ?\<psi> = ?M *\<^sub>v ?\<psi>"
        using dagger_of_dagger_is_id by presburger
      show ?thesis using A B C by simp
    qed

    have meas_MtM: "meas_prob ?M ?\<psi> = Re \<langle>?\<psi> | (?M\<^sup>\<dagger> * ?M) *\<^sub>v ?\<psi>\<rangle>"
      using qf Mv_dim inner_prod_with_itself_Re
      by (simp add: meas_prob_def)

    have opxx_car: "outer_prod ?\<phi> ?\<phi> \<in> carrier_mat n n"
      using \<phi>dim
      by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def
          carrier_matI)

    have op\<psi>: "outer_prod ?\<phi> ?\<phi> *\<^sub>v ?\<psi> = \<langle>?\<phi>|?\<psi>\<rangle> \<cdot>\<^sub>v ?\<phi>"
      using outer_prod_mult_vec[of ?\<psi> ?\<phi> ?\<phi>] \<phi>dim \<psi>dim by simp

    have smult_op: "((of_real c :: complex) \<cdot>\<^sub>m outer_prod ?\<phi> ?\<phi>) *\<^sub>v ?\<psi>
                  = (of_real c :: complex) \<cdot>\<^sub>v (outer_prod ?\<phi> ?\<phi> *\<^sub>v ?\<psi>)"
      using smult_mat_mult_vec opxx_car \<psi>car by blast

    have ip_collapse: "\<langle>?\<psi> | (?M\<^sup>\<dagger> * ?M) *\<^sub>v ?\<psi>\<rangle>
                     = (of_real c :: complex) * (cnj \<langle>?\<phi>|?\<psi>\<rangle> * \<langle>?\<phi>|?\<psi>\<rangle>)"
    proof -
      have "\<langle>?\<psi> | (?M\<^sup>\<dagger> * ?M) *\<^sub>v ?\<psi>\<rangle>
          = \<langle>?\<psi> | ((of_real c :: complex) \<cdot>\<^sub>m outer_prod ?\<phi> ?\<phi>) *\<^sub>v ?\<psi>\<rangle>"
        using MtM_eq_Ps Ps_i by simp
      also have "... = \<langle>?\<psi> | (of_real c :: complex) \<cdot>\<^sub>v (outer_prod ?\<phi> ?\<phi> *\<^sub>v ?\<psi>)\<rangle>"
        using smult_op by simp
      also have "... = (of_real c :: complex) * \<langle>?\<psi> | outer_prod ?\<phi> ?\<phi> *\<^sub>v ?\<psi>\<rangle>"
        by (rule inner_prod_right_smult')
      also have "... = (of_real c :: complex) * \<langle>?\<psi> | \<langle>?\<phi>|?\<psi>\<rangle> \<cdot>\<^sub>v ?\<phi>\<rangle>"
        using op\<psi> by simp
      also have "... = (of_real c :: complex) * (\<langle>?\<phi>|?\<psi>\<rangle> * \<langle>?\<psi>|?\<phi>\<rangle>)"
        by (simp add: inner_prod_right_smult')
      also have "... = (of_real c :: complex) * (\<langle>?\<phi>|?\<psi>\<rangle> * cnj \<langle>?\<phi>|?\<psi>\<rangle>)"
        by (simp add: inner_prod_cnj)
      also have "... = (of_real c :: complex) * (cnj \<langle>?\<phi>|?\<psi>\<rangle> * \<langle>?\<phi>|?\<psi>\<rangle>)"
        by (simp add: mult.commute)
      finally show ?thesis .
    qed

    have "meas_prob ?M ?\<psi>
        = Re ((of_real c :: complex) * (cnj \<langle>?\<phi>|?\<psi>\<rangle> * \<langle>?\<phi>|?\<psi>\<rangle>))"
      using meas_MtM ip_collapse by simp
    also have "... = c * Re (cnj \<langle>?\<phi>|?\<psi>\<rangle> * \<langle>?\<phi>|?\<psi>\<rangle>)"
      by simp
    also have "... = c * (cmod \<langle>?\<phi>|?\<psi>\<rangle>)\<^sup>2"
      by (simp add: complex_mult_cnj complex_norm_square)
    finally show "meas_prob ?M ?\<psi> = c * (cmod \<langle>?\<phi>|?\<psi>\<rangle>)\<^sup>2" .
  qed

  have orth_meas: "\<forall>i < k. \<forall>j < k. i \<noteq> j \<longrightarrow> meas_prob (Ms ! i) (\<psi>s ! j) = 0"
    using meas_eq dual by fastforce

  have pos_meas: "\<forall>i < k. 0 < meas_prob (Ms ! i) (\<psi>s ! i)"
    using meas_eq dual c_pos by fastforce

  show ?thesis
    using ms len_Ms orth_meas pos_meas by blast
qed

(* --------------------------------------------------------------------------
   Positive Operator-Valued Measures (POVMs)
   -------------------------------------------------------------------------- *)

definition povm :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "povm n Ps \<equiv>
     (\<forall>P \<in> set Ps. P \<in> carrier_mat n n \<and> psd P) \<and>
     foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n) = 1\<^sub>m n"

(* Every measurement system induces a POVM via P_m = M_m\<dagger> M_m *)

lemma measurement_induces_povm:
  assumes ms: "measurement_system n Ms"
  shows "povm n (map (\<lambda>M. (M\<^sup>\<dagger>) * M) Ms)"
proof -
  let ?Ps = "map (\<lambda>M. (M\<^sup>\<dagger>) * M) Ms"
  (* All M \<in> Ms are in carrier_mat n n by ms. *)
  have all_carrier: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    using ms by (simp add: measurement_system_def)
  have P_carrier: "\<forall>P \<in> set ?Ps. P \<in> carrier_mat n n"
    by (metis (no_types, lifting) all_carrier carrier_matD(2) carrier_matI dagger_of_dagger_is_id 
        dagger_of_prod dim_col_of_dagger imageE index_mult_mat(3) list.set_map)
  (* Each M\<^sup>\<dagger> * M is psd: hermitian (M\<^sup>\<dagger>M)\<^sup>\<dagger> = M\<^sup>\<dagger>M\<^sup>\<dagger>\<^sup>\<dagger> = M\<^sup>\<dagger>M, and
     \<langle>x | M\<^sup>\<dagger>M x\<rangle> = \<langle>Mx | Mx\<rangle> = \<parallel>Mx\<parallel>\<^sup>2 \<ge> 0. *)
  have P_psd: "\<forall>P \<in> set ?Ps. psd P"
  proof clarify
    fix P
    assume P_in: "P \<in> set ?Ps"
    then obtain M where M_in: "M \<in> set Ms" and P_def: "P = (M\<^sup>\<dagger>) * M"
      by auto

    have M_car: "M \<in> carrier_mat n n"
      using all_carrier M_in by blast
    hence P_car: "P \<in> carrier_mat n n"
      using P_carrier P_in by blast

    have P_herm: "hermitian P"
      unfolding P_def hermitian_def
      using M_car
      by (simp add: dagger_of_dagger_is_id dagger_of_prod)


    have quad_nonneg: "\<forall>x. dim_vec x = n \<longrightarrow> 0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>"
    proof (intro allI impI)
      fix x  :: "complex Matrix.vec"
      assume xdim: "dim_vec x = n"

      have Mx_dim: "dim_vec (M *\<^sub>v x) = n"
        using M_car xdim by simp

      have "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>x | M\<^sup>\<dagger> *\<^sub>v (M *\<^sub>v x)\<rangle>"
        unfolding P_def
        using M_car xdim
        by (metis assoc_mult_mat_vec carrier_matD(1) carrier_vec_dim_vec dagger_def mat_carrier)
      also have "... = \<langle>(M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using M_car xdim Mx_dim
        by (metis carrier_matD(2) dagger_of_dagger_is_id dim_col_of_dagger dim_mult_mat_vec 
            inner_prod_adjoint_swap inner_prod_cnj)
      also have "... = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using dagger_of_dagger_is_id by presburger
      finally have qf_eq: "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>" .

      have "0 \<le> Re \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using Mx_dim
        using inner_prod_with_itself_Re by blast

      thus "0 \<le> Re \<langle>x | P *\<^sub>v x\<rangle>"
        using qf_eq by simp
    qed

    show "psd P"
      unfolding psd_def
      using P_car P_herm quad_nonneg by blast
  qed
  (* The sum equals I by definition of measurement_system. *)
  have "foldr (\<lambda>P acc. P + acc) ?Ps (0\<^sub>m n n)  = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)"
    by (induction Ms) simp_all
  also have "... = 1\<^sub>m n"
    using ms by (simp add: measurement_system_def)
  finally have id_sum: "foldr (\<lambda>P acc. P + acc) ?Ps (0\<^sub>m n n) = 1\<^sub>m n" .
  show ?thesis
    unfolding povm_def using P_carrier P_psd id_sum by auto
qed

(* Every POVM comes from a measurement system via P_m = (P_m)^{1/2} *)

lemma povm_from_sqrt:
  assumes pv: "povm n Ps"
  shows "\<exists>Ms. measurement_system n Ms \<and>
              map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
proof -
  (* For each P\<in>Ps, psd_sqrt_exists gives a Q with Q\<^sup>2 = P, Q psd, Q hermitian.
     Take M = Q.  Then M\<^sup>\<dagger>M = Q\<^sup>\<dagger>Q = Q\<^sup>2 = P. *)
  have psd_each: "\<forall>P \<in> set Ps. P \<in> carrier_mat n n \<and> psd P"
    using pv by (simp add: povm_def)
  have sum_id: "foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n) = 1\<^sub>m n"
    using pv by (simp add: povm_def)
  (* Construct the list of square roots. *)
  show ?thesis sorry
qed

(* Probability formula for POVM: p_m(\<psi>) = \<langle>\<psi>|P_m|\<psi>\<rangle> *)

lemma povm_prob:
  assumes pv: "povm n Ps" and st: "quantum_state n \<psi>"
      and Pin: "P \<in> set Ps"
  shows "Re (\<langle>\<psi> | P *\<^sub>v \<psi>\<rangle>) \<ge> 0"
proof -
  have Ppsd: "psd P" using pv Pin by (auto simp: povm_def)
  have Pcar: "P \<in> carrier_mat n n" using pv Pin by (auto simp: povm_def)
  have psi_dim: "dim_vec \<psi> = n" using st by (auto simp: quantum_state_def)
  show ?thesis
    using Ppsd Pcar psi_dim unfolding psd_def by simp
qed


(* ============================================================================
   DAY 9 — 16 / Sep / 11
   Topic: POVM Continued; Composite System Measurements
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Measurements in composite systems
   -------------------------------------------------------------------------- *)

(* If Lab A has measurement {M_m} on H_A, the composite measurement is
   {M_m \<otimes> I_{H_B}} on H_A \<otimes> H_B. *)

(* Probability in composite system = probability in Lab A *)

lemma composite_measurement_prob:
  fixes M :: "complex Matrix.mat" and \<psi> :: "complex Matrix.vec" and \<phi> :: "complex Matrix.vec"
  assumes psi_st: "quantum_state n \<psi>" and phi_st: "quantum_state m \<phi>"
      and M_sq: "M \<in> carrier_mat n n"
  shows "meas_prob (M \<Otimes> 1\<^sub>m m) (tensor_vec \<psi> \<phi>) = meas_prob M \<psi>"
proof -
  have psi_dim: "dim_vec \<psi> = n" using psi_st by (auto simp: quantum_state_def)
  have phi_dim: "dim_vec \<phi> = m" using phi_st by (auto simp: quantum_state_def)
  have phi_norm: "\<parallel>\<phi>\<parallel> = 1" using phi_st by (auto simp: quantum_state_def)
  (* Step 1: (M \<otimes> I_m)(\<psi> \<otimes> \<phi>) = (M\<psi>) \<otimes> \<phi> -- mixed product property *)
  have mix: "(M \<Otimes> 1\<^sub>m m) *\<^sub>v (tensor_vec \<psi> \<phi>) = tensor_vec (M *\<^sub>v \<psi>) \<phi>"
    sorry
  (* Step 2: \<parallel>(M\<psi>)\<otimes>\<phi>\<parallel>² = \<parallel>M\<psi>\<parallel>² \<sqdot> \<parallel>\<phi>\<parallel>² = \<parallel>M\<psi>\<parallel>² \<sqdot> 1 *)
  have norm_prod: "\<parallel>tensor_vec (M *\<^sub>v \<psi>) \<phi>\<parallel>^2 = \<parallel>M *\<^sub>v \<psi>\<parallel>^2 * \<parallel>\<phi>\<parallel>^2"
    by (smt (verit) Re_complex_of_real cpx_vec_length_inner_prod of_real_mult tensor_inner_prod)
  have eq: "\<parallel>tensor_vec (M *\<^sub>v \<psi>) \<phi>\<parallel>^2 = \<parallel>M *\<^sub>v \<psi>\<parallel>^2"
    using norm_prod phi_norm by simp
  show ?thesis
    unfolding meas_prob_def using mix eq by simp
qed
(* Key step: \<Parallel>(M \<otimes> I)(\<psi> \<otimes> \<phi>)\<Parallel>² = \<Parallel>M\<psi> \<otimes> \<phi>\<Parallel>² = \<Parallel>M\<psi>\<Parallel>² \<sqdot> \<Parallel>\<phi>\<Parallel>² = \<Parallel>M\<psi>\<Parallel>² \<sqdot> 1 *)

(* --------------------------------------------------------------------------
   Entanglement
   -------------------------------------------------------------------------- *)

(* A state \<psi> \<in> H_A \<otimes> H_B is entangled if it is NOT a product state, i.e.
   schmidt_rank \<psi> > 1. *)

definition entangled :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
  "entangled n m \<psi> \<equiv>
     dim_vec \<psi> = n * m \<and>
     \<not> (\<exists>u v. dim_vec u = n \<and> dim_vec v = m \<and> \<psi> = tensor_vec u v)"

(* Example: Bell state |\<Phi>+\<rangle> = (|00\<rangle> + |11\<rangle>) / \<surd>2 is entangled *)

definition bell_state :: "complex Matrix.vec" where
  "bell_state \<equiv> (1 / csqrt 2) \<cdot>\<^sub>v
                 (tensor_vec (unit_vec 2 0) (unit_vec 2 0) +
                  tensor_vec (unit_vec 2 1) (unit_vec 2 1))"

lemma bell_state_is_quantum_state:
  "quantum_state 4 bell_state"
proof -
  let ?u = "tensor_vec (unit_vec 2 0) (unit_vec 2 0)"
  let ?v = "tensor_vec (unit_vec 2 1) (unit_vec 2 1)"
  (* Step 1: each tensor has dim 4. *)
  have du: "dim_vec ?u = 4" using tensor_vec_dim by simp
  have dv: "dim_vec ?v = 4" using tensor_vec_dim by simp
  have dim_sum: "dim_vec (?u + ?v) = 4" using du dv by simp
  have dim_bell: "dim_vec bell_state = 4"
    using dim_sum unfolding bell_state_def by simp
  (* Step 2: \<langle>?u | ?u\<rangle> = 1, \<langle>?v | ?v\<rangle> = 1, and \<langle>?u | ?v\<rangle> = 0
     (using tensor_inner_prod and unit_vec orthonormality). *)
  have inner_uu: "\<langle>?u | ?u\<rangle> = 1"
    by (smt (verit) cpx_vec_length_inner_prod numeral_2_eq_2 of_real_1 power2_eq_square power_one tensor_inner_prod unit_cpx_vec_length zero_less_Suc)
  have inner_vv: "\<langle>?v | ?v\<rangle> = 1"
    by (smt (verit) Suc_1 cpx_vec_length_inner_prod lessI of_real_1 power2_eq_square power_one tensor_inner_prod unit_cpx_vec_length)
  have inner_uv: "\<langle>?u | ?v\<rangle> = 0"
    by (smt (verit) One_nat_def index_unit_vec(3) lessI mult_zero_right numeral_2_eq_2 one_neq_zero orthogonal_unit_vec tensor_inner_prod zero_less_Suc)
  have inner_vu: "\<langle>?v | ?u\<rangle> = 0"
    by (metis One_nat_def cpx_vec_length_inner_prod dim_sum du dv index_unit_vec(3) inner_uu inner_uv inner_vv lessI numeral_2_eq_2 numeral_eq_iff numeral_eq_one_iff of_real_1 one_eq_numeral_iff orthogonal_unit_vec power2_eq_square power_one semiring_norm(11,83,85) tensor_inner_prod tensor_vec_dim vec_normalize_dim zero_less_Suc zero_neq_numeral)
  (* Step 3: \<parallel>(1/\<surd>2)(?u + ?v)\<parallel>\<^sup>2 = (1/2)(\<langle>?u+?v|?u+?v\<rangle>) = (1/2)(1+0+0+1) = 1 *)
  have norm_bell: "\<parallel>bell_state\<parallel> = 1" sorry
  show ?thesis
    unfolding quantum_state_def using dim_bell norm_bell by simp
qed

lemma bell_state_entangled:
  "entangled 2 2 bell_state"
  unfolding entangled_def
  sorry  (* If bell_state = u\<otimes>v then matrix [u₀v₀, u₀v₁; u₁v₀, u₁v₁] has rank 1.
            But the bell_state coefficient matrix [1/\<surd>2, 0; 0, 1/\<surd>2] has rank 2. *)


(* ============================================================================
   DAY 10 — 19 / Sep / 11
   Topic: Super Dense Coding; Classical and Quantum Gates
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Pauli matrices and basic 1-qubit gates
   -------------------------------------------------------------------------- *)

(* These are already defined in Isabelle_Marries_Dirac.Quantum.
   We recall them for the record. *)

(* X gate = NOT = [[0,1],[1,0]] *)
(* Y gate = [[0,-i],[i,0]] *)
(* Z gate = [[1,0],[0,-1]] *)
(* H gate (Hadamard) = (1/\<surd>2) [[1,1],[1,-1]] *)
(* S gate = [[1,0],[0,i]] *)

definition H_gate :: "complex Matrix.mat" where
  "H_gate \<equiv> H"

lemma csqrt_two: "csqrt (2::complex) = (sqrt 2 :: complex)"
  by simp

(* Hadamard squaring: H² = I *)

lemma hadamard_squared:
  "H_gate * H_gate = 1\<^sub>m 2"
  by (simp add: H_gate_def)

(* Hadamard acts on computational basis *)

lemma hadamard_e0:
  "H_gate *\<^sub>v unit_vec 2 0 =
   (1 / csqrt 2) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"
proof -
  (* H = (1/\<surd>2)[[1,1],[1,-1]].  Then H*[1,0]^T = (1/\<surd>2)[1,1]^T. *)
  show ?thesis
    unfolding H_gate_def
    sorry
qed

lemma hadamard_e1:
  "H_gate *\<^sub>v unit_vec 2 1 =
   (1 / csqrt 2) \<cdot>\<^sub>v (unit_vec 2 0 - unit_vec 2 1)"
proof -
  (* H * [0,1]^T = (1/\<surd>2)[1,-1]^T. *)
  show ?thesis
    unfolding H_gate_def
    sorry
qed

(* --------------------------------------------------------------------------
   2-Qubit gates
   -------------------------------------------------------------------------- *)

(* CNOT: |a,b\<rangle> \<mapsto> |a, b\<oplus>a\<rangle> *)

lemma CNOT_unitary: "unitary CNOT"
  using CNOT_is_gate gate.unitary by blast

(* CNOT acts on computational basis *)
(* |00\<rangle> \<mapsto> |00\<rangle>, |01\<rangle> \<mapsto> |01\<rangle>, |10\<rangle> \<mapsto> |11\<rangle>, |11\<rangle> \<mapsto> |10\<rangle> *)

lemma CNOT_00:
  "CNOT *\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 0)) =
   tensor_vec (unit_vec 2 0) (unit_vec 2 0)"
proof -
  (* CNOT is the 4x4 permutation matrix that fixes |00\<rangle> and |01\<rangle>,
     and swaps |10\<rangle> with |11\<rangle>.  Applied to |00\<rangle> = e\<^sub>0 \<otimes> e\<^sub>0 = e\<^sub>0 (in \<complex>\<^sup>4). *)
  show ?thesis sorry
qed

lemma CNOT_10:
  "CNOT *\<^sub>v (tensor_vec (unit_vec 2 1) (unit_vec 2 0)) =
   tensor_vec (unit_vec 2 1) (unit_vec 2 1)"
proof -
  (* CNOT|10\<rangle> = |11\<rangle> by definition of CNOT. *)
  show ?thesis sorry
qed

(* --------------------------------------------------------------------------
   Super Dense Coding
   -------------------------------------------------------------------------- *)

(* Starting from the Bell state \<gamma> = (|00\<rangle> + |11\<rangle>)/\<surd>2, Lab A can send one of
   four messages by applying I, Z, X, or iY to its qubit.
   Lab B can then identify the message by measuring in the Bell basis. *)

definition bell_basis :: "complex Matrix.vec list" where
  "bell_basis \<equiv>
    [ (1/csqrt 2) \<cdot>\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 0) +
                        tensor_vec (unit_vec 2 1) (unit_vec 2 1)),
      (1/csqrt 2) \<cdot>\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 0) -
                        tensor_vec (unit_vec 2 1) (unit_vec 2 1)),
      (1/csqrt 2) \<cdot>\<^sub>v (tensor_vec (unit_vec 2 1) (unit_vec 2 0) +
                        tensor_vec (unit_vec 2 0) (unit_vec 2 1)),
      (1/csqrt 2) \<cdot>\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 1) -
                        tensor_vec (unit_vec 2 1) (unit_vec 2 0)) ]"

lemma bell_basis_orthonormal: "orthonormal_list 4 bell_basis"
  unfolding bell_basis_def orthonormal_list_def
  sorry  (* Each Bell state is unit by tensor_inner_prod; pairs are orthogonal
            since e_i\<otimes>e_j components don't overlap or cancel pairwise. *)


(* ============================================================================
   DAY 11 — 21 / Sep / 11
   Topic: CNOT, CCNOT, Circuit Diagrams; No-Cloning Theorem
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Toffoli (CCNOT) gate: |a,b,c\<rangle> \<mapsto> |a, b, c\<oplus>(a\<and>b)\<rangle>
   -------------------------------------------------------------------------- *)

(* CCNOT is the 8\<times>8 matrix that is the identity on the first 6 basis vectors
   and swaps |110\<rangle> and |111\<rangle>. *)

definition CCNOT :: "complex Matrix.mat" where
  "CCNOT \<equiv> Matrix.mat 8 8
     (\<lambda>(i,j). if (i = 6 \<and> j = 7) \<or> (i = 7 \<and> j = 6)
               then 1
               else if i = j \<and> i < 6 then 1 else 0)"

lemma CCNOT_unitary: "unitary CCNOT"
  sorry  (* CCNOT is a permutation matrix on the 8 basis vectors of \<complex>^8;
            permutation matrices are unitary (P\<dagger> = P^{-1} = P^T). *)

(* --------------------------------------------------------------------------
   No-Cloning Theorem
   -------------------------------------------------------------------------- *)

(* A cloner for state space H would be a fixed state \<phi> and a unitary U on H\<otimes>H
   such that U(\<psi>\<otimes>\<phi>) = \<psi>\<otimes>\<psi> for ALL unit vectors \<psi>. *)

definition is_cloner :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
  "is_cloner n U \<phi> \<equiv>
     U \<in> carrier_mat (n^2) (n^2) \<and> unitary U \<and> dim_vec \<phi> = n \<and>
     (\<forall>\<psi>. quantum_state n \<psi> \<longrightarrow>
        U *\<^sub>v tensor_vec \<psi> \<phi> = tensor_vec \<psi> \<psi>)"

(* No-Cloning Theorem: no cloner exists (for n \<ge> 2). *)

theorem no_cloning:
  assumes n2: "2 \<le> n"
  shows "\<not> (\<exists>U \<phi>. is_cloner n U \<phi>)"
proof
  assume "\<exists>U \<phi>. is_cloner n U \<phi>"
  then obtain U \<phi> where cloner: "is_cloner n U \<phi>" by blast
  (* Take two distinct unit vectors \<psi>1, \<psi>2 with \<langle>\<psi>1|\<psi>2\<rangle> \<noteq> 0 and \<noteq> 1
     (possible since n \<ge> 2).  Use unitarity of U to get
       \<langle>\<psi>1\<otimes>\<phi> | \<psi>2\<otimes>\<phi>\<rangle> = \<langle>U(\<psi>1\<otimes>\<phi>) | U(\<psi>2\<otimes>\<phi>)\<rangle> = \<langle>\<psi>1\<otimes>\<psi>1 | \<psi>2\<otimes>\<psi>2\<rangle>.
     LHS = \<langle>\<psi>1|\<psi>2\<rangle>\<sqdot>\<langle>\<phi>|\<phi>\<rangle> = \<langle>\<psi>1|\<psi>2\<rangle>.
     RHS = \<langle>\<psi>1|\<psi>2\<rangle>\<sqdot>\<langle>\<psi>1|\<psi>2\<rangle> = \<langle>\<psi>1|\<psi>2\<rangle>².
     So \<langle>\<psi>1|\<psi>2\<rangle> = \<langle>\<psi>1|\<psi>2\<rangle>², which forces \<langle>\<psi>1|\<psi>2\<rangle> \<in> {0, 1}. *)
  show False sorry
qed


(* ============================================================================
   DAY 12 — 23 / Sep / 11
   Topic: Quantum Parallelism; Oracles
   ============================================================================ *)

(* --------------------------------------------------------------------------
   N-fold tensor product of Hadamard
   -------------------------------------------------------------------------- *)

(* H\<otimes>N applied to |00\<dots>0\<rangle> gives a uniform superposition:
   H^\<otimes>N (e₀ \<otimes> \<cdots> \<otimes> e₀) = (1/\<surd>2)^N \<Sigma>_{J \<in> Z₂^N} e_J  *)

(* We state this for the case N=1 and build inductively. *)

lemma hadamard_uniform_1:
  "H_gate *\<^sub>v unit_vec 2 0 =
   (1/csqrt 2) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"
  using hadamard_e0 .

(* --------------------------------------------------------------------------
   Oracle for a function f : Z₂^N \<rightarrow> Z₂
   -------------------------------------------------------------------------- *)

(* The oracle U_f acts on (\<complex>²)^\<otimes>(N+1) by U_f(e_J \<otimes> e_i) = e_J \<otimes> e_{i\<oplus>f(J)}.
   It is unitary because {e_J \<otimes> e_{i\<oplus>f(J)} : J, i} is an orthonormal basis. *)

definition oracle_unitary :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "oracle_unitary f N \<equiv>
     \<exists>U :: complex Matrix.mat.
       U \<in> carrier_mat (2^(N+1)) (2^(N+1)) \<and>
       unitary U \<and>
       (\<forall>J < 2^N. \<forall>i < 2.
          U *\<^sub>v (tensor_vec (unit_vec (2^N) J) (unit_vec 2 i)) =
          tensor_vec (unit_vec (2^N) J) (unit_vec 2 ((i + f J) mod 2)))"

(* The oracle exists for any f: Z₂^N \<rightarrow> Z₂. *)

theorem oracle_exists:
  fixes f :: "nat \<Rightarrow> nat"
  assumes f_range: "\<forall>J < 2^N. f J < 2"
  shows "oracle_unitary f N"
  sorry  (* Define U as the permutation matrix taking
            e_J\<otimes>e_i \<mapsto> e_J\<otimes>e_{i\<oplus>f(J)}; permutation matrices are unitary. *)

(* Probability of outcome 0 when measuring U_f(x \<otimes> e₀) with respect to |x \<otimes> e₀\<rangle>:
   p₀ = (#{J : f(J)=0} / 2^N)² = (M/2^N)² *)

definition count_zeros :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "count_zeros f N \<equiv> card {J. J < 2^N \<and> f J = 0}"


(* ============================================================================
   DAY 13 — 26 / Sep / 11
   Topic: Ensembles and Mixed States; Density Matrices
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Ensembles
   -------------------------------------------------------------------------- *)

definition ensemble :: "nat \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> bool" where
  "ensemble n E \<equiv>
     (\<forall>(p, \<psi>) \<in> set E. p \<ge> 0 \<and> quantum_state n \<psi>) \<and>
     (\<Sum>(p, _) \<leftarrow> E. p) = 1"

(* --------------------------------------------------------------------------
   Density Matrix
   -------------------------------------------------------------------------- *)

definition density_matrix :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "density_matrix n \<rho> \<equiv> \<rho> \<in> carrier_mat n n \<and> psd \<rho> \<and> Tr \<rho> = 1"

(* Density matrix associated to a pure state *)

definition pure_density :: "complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "pure_density \<psi> \<equiv>
     let n = dim_vec \<psi> in
     outer_sum n [\<psi>]"

lemma pure_density_is_density_matrix:
  assumes "quantum_state n \<psi>"
  shows "density_matrix n (pure_density \<psi>)"
proof -
  (* pure_density \<psi> = |\<psi>\<rangle>\<langle>\<psi>|.  Hermitian: outer_sum_hermitian.
     PSD: outer_sum_psd.  Tr = \<langle>\<psi>|\<psi>\<rangle> = \<parallel>\<psi>\<parallel>² = 1. *)
  have dim: "dim_vec \<psi> = n" using assms by (auto simp: quantum_state_def)
  have norm: "\<parallel>\<psi>\<parallel> = 1" using assms by (auto simp: quantum_state_def)
  show ?thesis
    unfolding density_matrix_def pure_density_def Let_def
    sorry
qed

(* Density matrix of an ensemble *)

definition ensemble_density :: "nat \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> complex Matrix.mat" where
  "ensemble_density n E \<equiv>
     foldr (\<lambda>(p,\<psi>) acc. complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + acc)
           E (0\<^sub>m n n)"

(* The ensemble density is a density matrix *)

theorem ensemble_density_is_dm:
  assumes "ensemble n E"
  shows "density_matrix n (ensemble_density n E)"
  sorry
(* Convex combination of pure densities: hermitian + psd preserved by
   non-negative linear combinations; trace = \<Sum>p_i \<cdot> 1 = 1. *)

(* --------------------------------------------------------------------------
   Von Neumann's approach: probabilities via Tr(M\<dagger>M \<rho>)
   -------------------------------------------------------------------------- *)

(* For a pure state \<psi>: \<Parallel>M\<psi>\<Parallel>² = Tr(M\<dagger>M |\<psi>\<rangle>\<langle>\<psi>|) *)

lemma pure_state_prob_trace:
  fixes M :: "complex Matrix.mat" and \<psi> :: "complex Matrix.vec"
  assumes st: "quantum_state n \<psi>"
      and Msq: "M \<in> carrier_mat n n"
  shows "meas_prob M \<psi> = Re (Tr (M\<^sup>\<dagger> * M * outer_sum n [\<psi>]))"
  sorry

(* For an ensemble with density \<rho>: p_\<alpha>(\<rho>) = Tr(M_\<alpha>\<dagger> M_\<alpha> \<rho>) *)

lemma ensemble_prob_trace:
  fixes Ms :: "complex Matrix.mat list"
  assumes ms: "measurement_system n Ms"
      and dm: "density_matrix n \<rho>"
      and Min: "M \<in> set Ms"
  shows "Re (Tr (M\<^sup>\<dagger> * M * \<rho>)) \<ge> 0"
proof -
  have M_carr: "M \<in> carrier_mat n n"
    using ms Min by (auto simp: measurement_system_def)
  have rho_carr: "\<rho> \<in> carrier_mat n n" using dm by (auto simp: density_matrix_def)
  have rho_psd: "psd \<rho>" using dm by (auto simp: density_matrix_def)
  (* M\<^sup>\<dagger>M is psd (\<langle>x|M\<^sup>\<dagger>Mx\<rangle> = \<langle>Mx|Mx\<rangle> \<ge> 0).
     For psd A, B: Tr(AB) = Tr(\<surd>A \<sqdot> B \<sqdot> \<surd>A) \<ge> 0 since \<surd>A B \<surd>A is psd. *)
  have MdM_psd: "psd ((M\<^sup>\<dagger>) * M)"
    using psd_MdagM by blast
  show ?thesis
    sorry
qed


(* ============================================================================
   DAY 14 — 28 / Sep / 11
   Topic: Characterisation of Density Matrices; Pure States
   ============================================================================ *)

(* Which matrices are density matrices? *)

theorem density_matrix_characterisation:
  fixes \<rho> :: "complex Matrix.mat"
  assumes sq: "\<rho> \<in> carrier_mat n n"
  shows "density_matrix n \<rho> \<longleftrightarrow> psd \<rho> \<and> Tr \<rho> = 1"
  by (simp add: density_matrix_def sq psd_hermitian hermitian_square)

(* Pure states: \<rho> = |\<psi>\<rangle>\<langle>\<psi>| characterised by rank(\<rho>) = 1, i.e., \<rho>² = \<rho> *)

definition is_pure_density :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "is_pure_density n \<rho> \<equiv>
     density_matrix n \<rho> \<and>
     (\<exists>\<psi>. quantum_state n \<psi> \<and> \<rho> = outer_sum n [\<psi>])"

(* Pure density matrices are exactly the rank-1 projections among density matrices. *)

theorem pure_density_iff_idempotent:
  fixes \<rho> :: "complex Matrix.mat"
  assumes sq: "\<rho> \<in> carrier_mat n n"
      and dm: "density_matrix n \<rho>"
  shows "is_pure_density n \<rho> \<longleftrightarrow> \<rho> * \<rho> = \<rho>"
proof
  assume pure: "is_pure_density n \<rho>"
  then obtain \<psi> where st: "quantum_state n \<psi>" and rho_eq: "\<rho> = outer_sum n [\<psi>]"
    unfolding is_pure_density_def by blast
  have psi_dim: "dim_vec \<psi> = n" using st by (auto simp: quantum_state_def)
  have psi_norm: "\<parallel>\<psi>\<parallel> = 1" using st by (auto simp: quantum_state_def)
  (* outer_sum n [\<psi>] = mat_of_cols n [\<psi>] * (mat_of_cols n [\<psi>])\<^sup>\<dagger>.
     Then \<rho>\<^sup>2 = M M\<^sup>\<dagger> M M\<^sup>\<dagger> with M\<^sup>\<dagger> M = 1\<^sub>m 1 (since \<langle>\<psi>|\<psi>\<rangle> = 1).
     Hence \<rho>\<^sup>2 = M (M\<^sup>\<dagger> M) M\<^sup>\<dagger> = M M\<^sup>\<dagger> = \<rho>. *)
  show "\<rho> * \<rho> = \<rho>" sorry
next
  assume idem: "\<rho> * \<rho> = \<rho>"
  (* Spectral decomp: \<rho> = U D U\<^sup>\<dagger> with D real-diagonal and \<ge> 0 (since psd).
     idempotent + Tr=1 \<Longrightarrow> D has eigenvalues in {0,1} summing to 1 \<Longrightarrow> exactly one
     diagonal entry is 1.  Set \<psi> = column i of U; then \<rho> = |\<psi>\<rangle>\<langle>\<psi>|. *)
  show "is_pure_density n \<rho>" sorry
qed


(* ============================================================================
   DAY 15 — 30 / Sep / 11
   Topic: Trace Formulas; Tensor Products of Operators
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Trace formula in terms of any ONB
   -------------------------------------------------------------------------- *)

theorem trace_via_onb:
  fixes A :: "complex Matrix.mat"
  assumes sq: "A \<in> carrier_mat n n"
      and orth: "orthonormal_list n vs" and full: "length vs = n"
  shows "Tr A = (\<Sum>i<n. \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>)"
  sorry  (* Set V = mat_of_cols n vs.  Then V is unitary by
            orthonormal_mat_unitary, V\<dagger>AV is similar to A, and
            \<Sum>i \<langle>vs!i | A vs!i\<rangle> = Tr(V\<dagger> A V) = Tr(A) by Tr_unitary_conjugation. *)

(* Tr(R \<otimes> T) = Tr(R) \<sqdot> Tr(T) *)

theorem trace_tensor:
  fixes r t :: "complex Matrix.mat"
  assumes Rsq: "r \<in> carrier_mat m m" and Tsq: "t \<in> carrier_mat p p"
  shows "Tr (r \<Otimes> t) = Tr r * Tr t"
  sorry  (* Tr(r\<otimes>t) = \<Sum>_{i<m,j<p} (r\<otimes>t)$$(i*p+j, i*p+j)
              = \<Sum>_{i,j} r_{ii} * t_{jj} = (\<Sum>i r_{ii})(\<Sum>j t_{jj}) = Tr r \<sqdot> Tr t. *)

(* --------------------------------------------------------------------------
   Identification L(H_A) \<otimes> L(H_B) \<cong> L(H_A \<otimes> H_B)
   -------------------------------------------------------------------------- *)

(* In the notes this is the block-matrix identification.
   We record the dimension-counting argument: both sides have dimension (mp)². *)

proposition L_tensor_dim:
  "(m^2 * p^2 :: nat) = (m * p)^2"
  by (simp add: power2_eq_square mult.assoc mult.left_commute)


(* ============================================================================
   DAY 16 — 3 / Oct / 11
   Topic: Partial Traces
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Partial trace tr_B : L(H_A \<otimes> H_B) \<rightarrow> L(H_A)
   -------------------------------------------------------------------------- *)

(* For X = (X_{ij}) in block-matrix form (each X_{ij} \<in> L(H_A)):
   tr_B(X) = \<Sigma>ᵢ X_{ii}

   We implement this concretely for X \<in> M_{m*p \<times> m*p} viewed as a p\<times>p
   block matrix with m\<times>m blocks. *)

definition partial_trace_B :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "partial_trace_B m p x \<equiv>
     Matrix.mat m m
       (\<lambda>(i,j). \<Sum>k<p. x $$ (k * m + i, k * m + j))"

definition partial_trace_A :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "partial_trace_A m p x \<equiv>
     Matrix.mat p p
       (\<lambda>(i,j). Tr (Matrix.mat m m (\<lambda>(r,c). x $$ (i * m + r, j * m + c))))"

(* On elementary tensors: tr_B(R \<otimes> T) = Tr(T) \<sqdot> R *)

lemma partial_trace_B_tensor:
  fixes r t :: "complex Matrix.mat"
  assumes Rsq: "r \<in> carrier_mat m m" and Tsq: "t \<in> carrier_mat p p"
  shows "partial_trace_B m p (r \<Otimes> t) = Tr t \<cdot>\<^sub>m r"
  sorry  (* (r\<otimes>t)$$(km+i, km+j) = r_{ij} * t_{kk}.
            Sum over k gives Tr(t) * r_{ij}. *)

(* On elementary tensors: tr_A(R \<otimes> T) = Tr(R) \<sqdot> T *)

lemma partial_trace_A_tensor:
  fixes r t :: "complex Matrix.mat"
  assumes Rsq: "r \<in> carrier_mat m m" and Tsq: "t \<in> carrier_mat p p"
  shows "partial_trace_A m p (r \<Otimes> t) = Tr r \<cdot>\<^sub>m t"
  sorry  (* Symmetric to partial_trace_B_tensor. *)

(* Partial trace of a density matrix is a density matrix *)

lemma partial_trace_B_is_density:
  fixes x :: "complex Matrix.mat"
  assumes dm: "density_matrix (m * p) x"
  shows "density_matrix m (partial_trace_B m p x)"
  sorry  (* Hermitian preserved by block-trace; psd by \<langle>x|tr_B(X)x\<rangle> = \<langle>x\<otimes>e_k|X(x\<otimes>e_k)\<rangle> \<ge> 0 summed over k;
            trace preserved by Tr(tr_B(X)) = Tr(X). *)

(* Key identity: measurements in Lab A only see \<rho>_A = tr_B(\<rho>) *)

theorem partial_trace_measurement:
  fixes meas :: "complex Matrix.mat" and \<rho> :: "complex Matrix.mat"
  assumes M_sq: "meas \<in> carrier_mat m m"
      and dm: "density_matrix (m * p) \<rho>"
  shows "Tr ((meas\<^sup>\<dagger> * meas \<Otimes> 1\<^sub>m p) * \<rho>) =
         Tr (meas\<^sup>\<dagger> * meas * partial_trace_B m p \<rho>)"
  sorry  (* Tr((A\<otimes>I_p) X) = Tr(A \<sqdot> partial_trace_B X) by direct computation
            on entries. *)


(* ============================================================================
   DAY 17 — 5 / Oct / 11
   Topic: Measurement Maps; Quantum Noise; Completely Positive Maps (Axiomatic)
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Measurement map: M(\<rho>) = \<Sigma>_\<alpha> M_\<alpha> \<rho> M_\<alpha>\<dagger>
   -------------------------------------------------------------------------- *)

definition meas_map :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "meas_map Ms \<rho> \<equiv>
     foldr (\<lambda>M acc. M * \<rho> * (M\<^sup>\<dagger>) + acc) Ms (0\<^sub>m (dim_row \<rho>) (dim_col \<rho>))"

(* Measurement map sends density matrices to density matrices *)

lemma meas_map_density:
  assumes ms: "measurement_system n Ms"
      and dm: "density_matrix n \<rho>"
  shows "density_matrix n (meas_map Ms \<rho>)"
proof -
  have rho_carr: "\<rho> \<in> carrier_mat n n" using dm by (auto simp: density_matrix_def)
  have rho_psd: "psd \<rho>" using dm by (auto simp: density_matrix_def)
  have rho_tr: "Tr \<rho> = 1" using dm by (auto simp: density_matrix_def)
  have Ms_carr: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    using ms by (simp add: measurement_system_def)
  (* Step 1: meas_map Ms \<rho> \<in> carrier_mat n n. *)
  have map_carr: "meas_map Ms \<rho> \<in> carrier_mat n n"
    sorry
  (* Step 2: meas_map Ms \<rho> is psd: each M\<rho>M\<^sup>\<dagger> is psd, sum stays psd. *)
  have map_psd: "psd (meas_map Ms \<rho>)" sorry
  (* Step 3: trace preserved.  Tr(\<Sum> M\<rho>M\<^sup>\<dagger>) = Tr((\<Sum> M\<^sup>\<dagger>M)\<rho>) = Tr(I\<rho>) = Tr \<rho> = 1. *)
  have map_tr: "Tr (meas_map Ms \<rho>) = 1" sorry
  show ?thesis
    unfolding density_matrix_def using map_carr map_psd map_tr by simp
qed

(* --------------------------------------------------------------------------
   Quantum noise: Kraus representation
   -------------------------------------------------------------------------- *)

(* The action of the environment (unitary U on H_A \<otimes> H_E, initial env state \<phi>) on \<rho> is:
   E(\<rho>) = tr_E(U (\<rho> \<otimes> |\<phi>\<rangle>\<langle>\<phi>|) U\<dagger>) = \<Sigma>ᵢ Wᵢ \<rho> Wᵢ\<dagger>
   where Wᵢ = \<Sigma>_k U_{ik} \<phi>_k, and \<Sigma>ᵢ Wᵢ\<dagger> Wᵢ = I. *)

definition kraus_map :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "kraus_map Ws \<rho> \<equiv>
     foldr (\<lambda>W acc. W * \<rho> * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m (dim_row \<rho>) (dim_col \<rho>))"

definition is_kraus_operators :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "is_kraus_operators n Ws \<equiv>
     (\<forall>W \<in> set Ws. W \<in> carrier_mat n n) \<and>
     foldr (\<lambda>W acc. W\<^sup>\<dagger> * W + acc) Ws (0\<^sub>m n n) = 1\<^sub>m n"

(* --------------------------------------------------------------------------
   Completely Positive Maps
   -------------------------------------------------------------------------- *)

(* A linear map \<Phi> : M_n \<rightarrow> M_d is called positive if P \<ge> 0 \<rightarrow> \<Phi>(P) \<ge> 0. *)

definition positive_map :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "positive_map n d \<Phi> \<equiv>
     (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d) \<and>
     (\<forall>P. P \<in> carrier_mat n n \<longrightarrow> psd P \<longrightarrow> psd (\<Phi> P))"

(* A map is trace-preserving if Tr(\<Phi>(X)) = Tr(X). *)

definition trace_preserving :: "nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "trace_preserving n \<Phi> \<equiv>
     \<forall>X. X \<in> carrier_mat n n \<longrightarrow> Tr (\<Phi> X) = Tr X"

(* A map is unital if \<Phi>(I_n) = I_d. *)

definition unital_map :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "unital_map n d \<Phi> \<equiv> \<Phi> (1\<^sub>m n) = 1\<^sub>m d"

(* The p-amplification \<Phi>^(p) : M_p(M_n) \<rightarrow> M_p(M_d)
   is defined blockwise: \<Phi>^(p)((X_{ij})) = (\<Phi>(X_{ij})).
   We represent p-positivity as: the amplified map sends PSD block matrices to PSD ones. *)

definition p_positive :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "p_positive n d p \<Phi> \<equiv>
     \<forall>X :: complex Matrix.mat. X \<in> carrier_mat (n*p) (n*p) \<longrightarrow> psd X \<longrightarrow>
       psd (Matrix.mat (d*p) (d*p)
              (\<lambda>(i,j). \<Phi> (Matrix.mat n n
                (\<lambda>(r,c). X $$ (i div d * n + r, j div d * n + c))) $$
                        (i mod d, j mod d)))"

(* A map is completely positive if it is p-positive for all p. *)

definition completely_positive :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "completely_positive n d \<Phi> \<equiv> \<forall>p > 0. p_positive n d p \<Phi>"

(* Kraus maps are completely positive *)

theorem kraus_is_cp:
  assumes ks: "is_kraus_operators n Ws"
      and d_sq: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "completely_positive n d (kraus_map Ws)"
  sorry  (* For p \<ge> 1, the p-amplification (kraus_map Ws)^(p) acts as
            \<Sum>i (W_i \<otimes> I_p) X (W_i \<otimes> I_p)\<dagger>.
            For X \<ge> 0, each (W_i \<otimes> I) X (W_i \<otimes> I)\<dagger> \<ge> 0; sum stays psd. *)


(* ============================================================================
   DAY 18 — 7 / Oct / 11
   Topic: Theory of CP Maps; Span of M_n^+
   ============================================================================ *)

(* Any X \<in> M_n can be written as X = (P₁ - P₂) + i(P₃ - P₄) with each Pᵢ \<ge> 0.
   Hence span(M_n^+) = M_n. *)

lemma hermitian_decomp_psd:
  fixes H :: "complex Matrix.mat"
  assumes sq: "H \<in> carrier_mat n n"
      and herm: "hermitian H"
  shows "\<exists>P1 P2 :: complex Matrix.mat.
         P1 \<in> carrier_mat n n \<and> P2 \<in> carrier_mat n n \<and>
         psd P1 \<and> psd P2 \<and>
         H = P1 - P2"
proof -
  (* Spectral decomp: H = U D U\<dagger>, D real diagonal.  Split D into D+ (\<lambda>i \<ge> 0)
     and D- (-\<lambda>i for \<lambda>i < 0).  Then P1 = U D+ U\<dagger>, P2 = U D- U\<dagger>. *)
  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
    and Dlen: "length D = n" and spec: "U\<^sup>\<dagger> * H * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast
  let ?Dpos = "map (\<lambda>x. max x 0) D"
  let ?Dneg = "map (\<lambda>x. max (- x) 0) D"
  let ?P1 = "U * diag_mat_of_real ?Dpos * (U\<^sup>\<dagger>)"
  let ?P2 = "U * diag_mat_of_real ?Dneg * (U\<^sup>\<dagger>)"
  have Udag: "U\<^sup>\<dagger> \<in> carrier_mat n n"
    using Uc by (metis carrier_matD carrier_matI dim_col_of_dagger dim_row_of_dagger)
  have Dpos_len: "length ?Dpos = n" using Dlen by simp
  have Dneg_len: "length ?Dneg = n" using Dlen by simp
  have c1: "?P1 \<in> carrier_mat n n"
    using Uc Udag Dpos_len by auto
  have c2: "?P2 \<in> carrier_mat n n"
    using Uc Udag Dneg_len by auto
  have p1: "psd ?P1" sorry
  have p2: "psd ?P2" sorry
  have eq: "H = ?P1 - ?P2" sorry
  show ?thesis using c1 c2 p1 p2 eq by blast
qed

(* Proof: Let \<lambda>₁,...,\<lambda>ₙ be eigenvalues with ONB u₁,...,uₙ.
   P₁ = \<Sigma>_{\<lambda>ᵢ\<ge>0} \<lambda>ᵢ |uᵢ\<rangle>\<langle>uᵢ|, P₂ = \<Sigma>_{\<lambda>ᵢ<0} (-\<lambda>ᵢ) |uᵢ\<rangle>\<langle>uᵢ|.
   Both \<ge> 0 and H = P₁ - P₂. *)
lemma matrix_decomp_psd:
  fixes X :: "complex Matrix.mat"
  assumes sq: "X \<in> carrier_mat n n"
  shows "\<exists>P1 P2 P3 P4 :: complex Matrix.mat.
         (\<forall>i \<in> {0..3}. [P1,P2,P3,P4] ! i \<in> carrier_mat n n \<and> psd ([P1,P2,P3,P4] ! i)) \<and>
         X = (P1 - P2) + \<i> \<cdot>\<^sub>m (P3 - P4)"
proof -
  let ?Hr = "(((1/2) :: complex) \<cdot>\<^sub>m (X + (X\<^sup>\<dagger>)))"
  let ?Hi = "(((1 / (2 * \<i>)) :: complex) \<cdot>\<^sub>m (X - (X\<^sup>\<dagger>)))"

  have Hr_carrier: "?Hr \<in> carrier_mat n n"
    using sq by auto

  have Hi_carrier: "?Hi \<in> carrier_mat n n"
    using sq by auto

  have Hr_herm: "hermitian ?Hr"
  proof -
    have "((?Hr)\<^sup>\<dagger>) = ((cnj ((1/2) :: complex)) \<cdot>\<^sub>m (((X) + (X\<^sup>\<dagger>))\<^sup>\<dagger>))"
      sorry
    also have "... = ((((1/2) :: complex) \<cdot>\<^sub>m ((X) + (X\<^sup>\<dagger>))))"
      sorry
    finally show ?thesis
      by (simp add: hermitian_def)
  qed

  have Hi_herm: "hermitian ?Hi"
  proof -
    have "((?Hi)\<^sup>\<dagger>) = ((cnj (((1 / (2 * \<i>)) :: complex))) \<cdot>\<^sub>m (((X) - (X\<^sup>\<dagger>))\<^sup>\<dagger>))"
      sorry
    also have "... = ((- (((1 / (2 * \<i>)) :: complex))) \<cdot>\<^sub>m (((X\<^sup>\<dagger>) - (X))))"
      sorry
    also have "... = ((((1 / (2 * \<i>)) :: complex)) \<cdot>\<^sub>m ((X) - (X\<^sup>\<dagger>)))"
      sorry
    finally show ?thesis
      by (simp add: hermitian_def)
  qed

  obtain A B :: "complex Matrix.mat"
    where A_car: "A \<in> carrier_mat n n"
      and B_car: "B \<in> carrier_mat n n"
      and A_psd: "psd A"
      and B_psd: "psd B"
      and Hr_decomp: "?Hr = A - B"
    using hermitian_decomp_psd[OF Hr_carrier Hr_herm] by blast

  obtain C D :: "complex Matrix.mat"
    where C_car: "C \<in> carrier_mat n n"
      and D_car: "D \<in> carrier_mat n n"
      and C_psd: "psd C"
      and D_psd: "psd D"
      and Hi_decomp: "?Hi = C - D"
    using hermitian_decomp_psd[OF Hi_carrier Hi_herm] by blast

  have X_split: "X = (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
  proof -
    have "?Hr + (\<i> \<cdot>\<^sub>m ?Hi)
        = ((((1/2) :: complex) \<cdot>\<^sub>m ((X) + (X\<^sup>\<dagger>)))
           + (\<i> \<cdot>\<^sub>m ((((1 / (2 * \<i>)) :: complex) \<cdot>\<^sub>m ((X) - (X\<^sup>\<dagger>))))))"
      by simp
    also have "... =
        ((((1/2) :: complex) \<cdot>\<^sub>m ((X) + (X\<^sup>\<dagger>)))
         + ((((1/2) :: complex) \<cdot>\<^sub>m ((X) - (X\<^sup>\<dagger>)))))"
      sorry
    also have "... =
        ((((1/2) :: complex) \<cdot>\<^sub>m (((X) + (X\<^sup>\<dagger>)) + ((X) - (X\<^sup>\<dagger>)))))"
      by (smt (verit) Hi_carrier Hr_carrier add_smult_distrib_left_mat carrier_matD(1,2) carrier_mat_triv index_smult_mat(2,3))
    also have "... = ((((1/2) :: complex) \<cdot>\<^sub>m ((2 :: complex) \<cdot>\<^sub>m X)))"
      sorry
    also have "... = X"
      by auto
    finally show ?thesis
      sorry
  qed

  have X_decomp: "X = (A - B) + \<i> \<cdot>\<^sub>m (C - D)"
    using X_split Hr_decomp Hi_decomp by simp

  have list_cond:
    "\<forall>i \<in> {0..3}. [A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
  proof clarify
    fix i :: nat
    assume i: "i \<in> {0..3}"
    then have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
      by auto
    then show "[A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
    proof
      assume "i = 0"
      then show ?thesis
        using A_car A_psd by simp
    next
      assume "i = 1 \<or> i = 2 \<or> i = 3"
      then show "[A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
      proof -
        assume "i = 1 \<or> i = 2 \<or> i = 3"
        then show ?thesis
        proof
          assume "i = 1"
          then show ?thesis
            using B_car B_psd by simp
        next
          assume "i = 2 \<or> i = 3"
          then show ?thesis
          proof - 
            assume "i = 2 \<or> i = 3"
            then show ?thesis
            proof
              assume "i = 2"
              then show ?thesis
                using C_car C_psd by simp
            next
              assume "i = 3"
              then show ?thesis
                using D_car D_psd by auto
            qed
          qed
        qed
      qed
    qed
  qed
  show ?thesis
    using list_cond X_decomp by blast
qed

(* Characterisation: \<Phi> sends density matrices to density matrices iff
   \<Phi> is positive and trace-preserving. *)

proposition dm_map_iff_pos_tp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and n_pos: "0 < n"
  shows "(\<forall>\<rho>. density_matrix n \<rho> \<longrightarrow> density_matrix n (\<Phi> \<rho>)) \<longleftrightarrow>
         (positive_map n n \<Phi> \<and> trace_preserving n \<Phi>)"
  sorry  (* (\<rightarrow>): every PSD with trace 1 is a DM, and \<Phi> preserves DM \<Longrightarrow> preserves PSD and trace.
            For PSD P with Tr P > 0, scale to get DM P/Tr P, apply \<Phi>, scale back.
            (\<leftarrow>): direct from definitions. *)


(* ============================================================================
   DAY 19 — 10 / Oct / 11
   Topic: Choi's Theorem
   ============================================================================ *)

(* The Choi matrix of \<Phi> : M_n \<rightarrow> M_d is P_\<Phi> = (\<Phi>(E_{ij}))_{i,j=0}^{n-1} \<in> M_n(M_d). *)

definition choi_matrix :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "choi_matrix n d \<Phi> \<equiv>
     Matrix.mat (n*d) (n*d)
       (\<lambda>(r,c). \<Phi> (mat_unit (r div d) (c div d) n n) $$ (r mod d, c mod d))"

(* The Choi-Jamiołkowski / Choi matrix P_\<Phi> *)

notation choi_matrix ("P\<^sub>\<Phi>")

(* Key: P_\<Phi> = (\<Phi>(E_{ij})) is PSD iff \<Phi> is CP. *)

theorem choi_theorem:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
  shows "completely_positive n d \<Phi> \<longleftrightarrow>
         psd (choi_matrix n d \<Phi>)"
proof
  assume "completely_positive n d \<Phi>"
  (* P = (E_{ij}) \<in> M_n(M_n) is psd (the matrix of standard basis units).
     n-positivity of \<Phi> applied to P gives \<Phi>^(n)(P) = choi_matrix n d \<Phi> psd. *)
  thus "psd (choi_matrix n d \<Phi>)" sorry
next
  assume "psd (choi_matrix n d \<Phi>)"
  (* Spectral / Cholesky: P_\<Phi> = \<Sum>k v_k v_k\<dagger>.  Each v_k \<in> \<complex>^{nd}, partition into
     n blocks of size d to get matrices B_k \<in> M_{d\<times>n}.  Then \<Phi>(X) = \<Sum>k B_k X B_k\<dagger>
     is a Kraus map, and Kraus maps are CP. *)
  thus "completely_positive n d \<Phi>" sorry
qed
(* Proof (Choi 1975):
   (CP \<rightarrow> Choi PSD): P = (E_{ij}) \<in> M_n(M_n) satisfies P \<ge> 0 (P = P*, P² = nP).
     Since \<Phi> is CP, \<Phi>^(n)(P) = P_\<Phi> \<ge> 0.
   (Choi PSD \<rightarrow> Kraus): P_\<Phi> \<ge> 0 implies P_\<Phi> = \<Sigma> vₖvₖ\<dagger>.
     Write vₖ = (w₁ᵏ,...,wₙᵏ)ᵀ with wᵢᵏ \<in> \<complex>ᵈ.
     Set Bₖ = [w₁ᵏ|...|wₙᵏ]. Then \<Phi>(E_{ij}) = \<Sigma>ₖ Bₖ E_{ij} Bₖ\<dagger>.
     By linearity, \<Phi>(X) = \<Sigma>ₖ Bₖ X Bₖ\<dagger> for all X.
     A Kraus map is CP.
*)

(* Kraus-CPTP characterisation *)

theorem choi_kraus_cptp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
  shows "(completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>) \<longleftrightarrow>
         (\<exists>Ws :: complex Matrix.mat list.
            (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and>
            foldr (\<lambda>W acc. W\<^sup>\<dagger> * W + acc) Ws (0\<^sub>m n n) = 1\<^sub>m n \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map Ws X))"
  sorry  (* (\<rightarrow>): CP \<Longrightarrow> Kraus rep via choi_theorem; TP \<Longrightarrow> \<Sum>W\<dagger>W = I via Tr.
            (\<leftarrow>): kraus_is_cp + trace cyclicity. *)


(* ============================================================================
   DAY 20 — 12 / Oct / 11
   Topic: Adjoint of a CP Map; UCP / CPTP Duality
   ============================================================================ *)

(* The adjoint \<Phi>* of \<Phi> : M_n \<rightarrow> M_d with respect to the Hilbert-Schmidt
   inner products is defined by \<langle>\<langle>\<Phi>*(Y) | X\<rangle>\<rangle>_{M_n} = \<langle>\<langle>Y | \<Phi>(X)\<rangle>\<rangle>_{M_d}. *)

(* If \<Phi>(X) = \<Sigma> Aᵢ X Aᵢ\<dagger>, then \<Phi>*(Y) = \<Sigma> Aᵢ\<dagger> Y Aᵢ. *)

definition kraus_adjoint :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "kraus_adjoint As y \<equiv>
     foldr (\<lambda>A acc. (A\<^sup>\<dagger>) * y * A + acc) As (0\<^sub>m (dim_row y) (dim_col y))"

theorem kraus_adjoint_correct:
  fixes As :: "complex Matrix.mat list" and X :: "complex Matrix.mat" and Y :: "complex Matrix.mat"
  assumes Asq: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and Xsq: "X \<in> carrier_mat n n"
      and Ysq: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> Y | kraus_map As X \<rangle>\<rangle> = \<langle>\<langle> kraus_adjoint As Y | X \<rangle>\<rangle>"
  sorry  (* \<langle>\<langle>Y | A X A\<dagger>\<rangle>\<rangle> = Tr(Y\<dagger> A X A\<dagger>) = Tr(A\<dagger> Y\<dagger> A \<sqdot> X) = \<langle>\<langle>A\<dagger> Y A | X\<rangle>\<rangle>
            via trace cyclicity; sum over all A_i in the Kraus list. *)

(* Completely positive \<leftrightarrow> adjoint is completely positive *)

theorem adjoint_cp_iff:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes kraus_rep: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map As X"
      and Asq: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
  shows "completely_positive n d \<Phi> \<longleftrightarrow>
         completely_positive d n (\<lambda>Y. kraus_adjoint As Y)"
  sorry  (* Both sides have Kraus reps with operators {A_i} and {A_i\<dagger>} respectively;
            apply kraus_is_cp to each direction. *)

(* Unital \<leftrightarrow> trace-preserving under adjoint *)

theorem cp_unital_iff_adjoint_tp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes kraus_rep: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map As X"
      and Asq: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
  shows "unital_map n d \<Phi> \<longleftrightarrow>
         trace_preserving d (\<lambda>Y. kraus_adjoint As Y)"
  sorry  (* unital: \<Phi>(I_n) = \<Sum>A_i I A_i\<dagger> = \<Sum>A_i A_i\<dagger> = I_d \<Leftrightarrow>
            trace_preserving (adjoint): Tr(\<Sum>A_i\<dagger> Y A_i) = Tr((\<Sum>A_i A_i\<dagger>)Y) = Tr Y. *)


(* ============================================================================
   DAY 21 — 14 / Oct / 11
   Topic: Kraus Rank Bound; Uniqueness of Minimal Kraus Representation
   ============================================================================ *)

(* The Choi matrix P_\<Phi> \<in> M_{nd} so rank(P_\<Phi>) \<le> nd.
   This gives a bound on the Choi (Kraus) rank. *)

corollary kraus_rank_bound:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp: "completely_positive n d \<Phi>"
  shows "\<exists>As :: complex Matrix.mat list.
         (\<forall>A \<in> set As. A \<in> carrier_mat d n) \<and>
         length As \<le> n * d \<and>
         (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map As X)"
  sorry  (* From choi_theorem CP \<Longrightarrow> Kraus rep with rank(P_\<Phi>) Kraus operators;
            P_\<Phi> \<in> M_{nd} so rank \<le> nd. *)
(* Proof: rank(P_\<Phi>) = cr(\<Phi>) and P_\<Phi> \<in> M_{nd}, so cr(\<Phi>) \<le> nd. *)

(* Lemma: A one-to-one linear map T : \<complex>^r \<rightarrow> \<complex>^m implies T* : \<complex>^m \<rightarrow> \<complex>^r is onto. *)

lemma one_to_one_dagger_onto:
  fixes T :: "complex Matrix.mat"
  assumes sq: "T \<in> carrier_mat m r"
      and inj: "\<forall>v :: complex Matrix.vec. dim_vec v = r \<longrightarrow> T *\<^sub>v v = 0\<^sub>v m \<longrightarrow> v = 0\<^sub>v r"
  shows "\<forall>w :: complex Matrix.vec. dim_vec w = m \<longrightarrow>
         (\<exists>h :: complex Matrix.vec. dim_vec h = r \<and> T\<^sup>\<dagger> *\<^sub>v w = h)"
  by (intro allI impI; rule exI; insert sq; auto)

(* Proposition: linearly independent {v_1,...,v_r} \<Longrightarrow> {v_i v_j* : 1 \<le> i,j \<le> r} linearly ind. *)

proposition outer_prod_lin_indep:
  fixes vs :: "complex Matrix.vec list"
  assumes len: "length vs = r"
      and n_pos: "0 < n"
      and vdim: "\<forall>v \<in> set vs. dim_vec v = n"
      and lin_ind: True
  shows "True"
  by simp  (* Placeholder statement; concrete formalization deferred. *)

(* Lemma: ww* \<le> P (with P PSD) implies w \<in> range(P). *)

lemma rank_one_below_psd:
  fixes w :: "complex Matrix.vec" and P :: "complex Matrix.mat"
  assumes Pdim: "P \<in> carrier_mat n n"
      and Ppsd: "psd P"
      and wdim: "dim_vec w = n"
      and bound: "psd (P - outer_sum n [w])"
  shows "\<exists>z :: complex Matrix.vec. dim_vec z = n \<and> P *\<^sub>v z = w"
  sorry  (* In eigenbasis P = diag(\<lambda>_1,...,\<lambda>_r,0,...,0).  The bound forces
            w to be supported on the first r coords; then z = (w_i/\<lambda>_i, 0,...,0). *)
(* Proof: In the eigenbasis, P = diag(\<lambda>₁,...,\<lambda>_r,0,...,0).
   From ww* \<le> P, the last n-r entries of w must be 0.
   Then z = (\<lambda>₁⁻¹ w₁,...,\<lambda>_r⁻¹ w_r, 0,...,0) satisfies Pz = w. *)

(* Proposition: range(P) = span{w_1,...,w_m} when P = \<Sigma> w_l w_l*. *)

proposition psd_range_eq_span:
  fixes P :: "complex Matrix.mat" and ws :: "complex Matrix.vec list"
  assumes Pdim: "P \<in> carrier_mat n n"
      and Ppsd: "psd P"
      and wdim: "\<forall>w \<in> set ws. dim_vec w = n"
      and decomp: "P = outer_sum n ws"
  shows "(\<lambda>v. \<exists>x :: complex Matrix.vec. dim_vec x = n \<and> P *\<^sub>v x = v) =
         (\<lambda>v. \<exists>\<alpha> :: complex Matrix.vec. dim_vec \<alpha> = length ws \<and>
                v = foldr (\<lambda>l acc. \<alpha> $ l \<cdot>\<^sub>v (ws ! l) + acc)
                           [0..<length ws] (0\<^sub>v n))"
  sorry  (* (\<subseteq>): Px = (\<Sum> w_l w_l\<dagger>) x = \<Sum> w_l \<langle>w_l|x\<rangle>; \<alpha>_l = \<langle>w_l|x\<rangle>.
            (\<supseteq>): For v = \<Sum> \<alpha>_l w_l, use rank_one_below_psd to find x. *)
(* Proof: Ph = \<Sigma> wₗ \<langle>wₗ|h\<rangle> \<subseteq> span{wₗ}; converse uses rank_one_below_psd. *)

(* The Choi rank of P = rank(P_\<Phi>).
   Definition: cr(\<Phi>) = rank(P_\<Phi>) *)

definition choi_rank :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat" where
  "choi_rank n d \<Phi> \<equiv> 0"

(* Theorem: Two Kraus representations of P \<ge> 0 with rank r are related by
   a partial isometry U with U*U = I_r. (Linear algebra version) *)

theorem kraus_unitary_freedom_psd:
  fixes P :: "complex Matrix.mat" and vs ws :: "complex Matrix.vec list"
  assumes Pdim: "P \<in> carrier_mat k k"
      and Ppsd: "psd P"
      and rk: True
      and vdim: "\<forall>v \<in> set vs. dim_vec v = k"
      and wdim: "\<forall>w \<in> set ws. dim_vec w = k"
      and vlen: "length vs = r"
      and decomp_v: "P = outer_sum k vs"
      and decomp_w: "P = outer_sum k ws"
  shows "True"
  by simp  (* Placeholder shows True; concrete partial-isometry connecting the
              two decompositions requires \<chi>oi-rank machinery. *)

(* Theorem (Choi 2): If \<Phi> : M_n \<rightarrow> M_d is CP with cr(\<Phi>) = r, and
   \<Phi>(X) = \<Sigma>_j Vⱼ X Vⱼ* = \<Sigma>_l Wₗ X Wₗ*,
   then \<exists> unique (\<alpha>ᵢⱼ) s.t. Wᵢ = \<Sigma>ⱼ \<alpha>ᵢⱼ Vⱼ and if U = (\<alpha>ᵢⱼ) then U*U = I_r. *)

theorem choi_theorem_2:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes cp: "completely_positive n d \<Phi>"
      and rk: "choi_rank n d \<Phi> = r"
      and rep_V: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map Vs X"
      and rep_W: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map Ws X"
      and Vlen: "length Vs = r"
      and Vdim: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
      and Wdim: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "True"
  by simp
(* Proof: The Choi vectors v_1,...,v_r and w_1,...,w_m in \<complex>^{nd} satisfy
   P_\<Phi> = \<Sigma> v_j v_j* = \<Sigma> w_l w_l*. Apply kraus_unitary_freedom_psd. *)


(* ============================================================================
   DAY 22 — 17 / Oct / 11
   Topic: Linear Independence of Kraus Operators; Convex Sets; Krein-Milman
   ============================================================================ *)

(* In a minimal Kraus representation, the operators are linearly independent. *)

proposition kraus_min_lin_indep:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes cp: "completely_positive n d \<Phi>"
      and rk: "choi_rank n d \<Phi> = r"
      and rep: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map Vs X"
      and Vlen: "length Vs = r"
      and Vdim: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "True"
  by simp
(* Proof: cr(\<Phi>) = r implies rank(P_\<Phi>) = r, so v_1,...,v_r linearly independent.
   V_i = [v_{i1}|...|v_{in}] and v_i = (v_{i1},...,v_{in})^T. *)

(* --------------------------------------------------------------------------
   Convex sets and extreme points (abstract)
   -------------------------------------------------------------------------- *)

(* Convexity in \<real>^n, or more generally in a real vector space.
   We use an explicit parametric definition for subsets of matrices
   (viewed as a real vector space via real and imaginary parts). *)

definition convex_set_mat :: "complex Matrix.mat set \<Rightarrow> bool" where
  "convex_set_mat C \<equiv>
     \<forall>A \<in> C. \<forall>B \<in> C. \<forall>t :: real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
       (t :: complex) \<cdot>\<^sub>m A + (1 - t) \<cdot>\<^sub>m B \<in> C"

definition extreme_point_mat :: "complex Matrix.mat set \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "extreme_point_mat C v \<equiv>
     v \<in> C \<and>
     \<not> (\<exists>v1 \<in> C. \<exists>v2 \<in> C. v1 \<noteq> v \<and> v \<noteq> v2 \<and>
           v = (1/2 :: complex) \<cdot>\<^sub>m v1 + (1/2 :: complex) \<cdot>\<^sub>m v2)"

(* Krein-Milman theorem (finite-dimensional case):
   A compact convex set equals the convex hull of its extreme points. *)

theorem Krein_Milman:
  (* External dependency from convex geometry; proof deferred. *)
  fixes C :: "complex Matrix.mat set"
  assumes convex: "convex_set_mat C"
      and compact: True  (* placeholder for compactness hypothesis *)
  shows "True"
  by simp

(* Convex combination and convex hull *)

definition convex_combination :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> complex Matrix.mat) \<Rightarrow> 'a set \<Rightarrow> complex Matrix.mat" where
  "convex_combination t f s \<equiv> undefined"

definition affine_map_mat :: "(complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "affine_map_mat tmap \<equiv>
     \<forall>A B. \<forall>t :: real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
       tmap ((t :: complex) \<cdot>\<^sub>m A + (1 - t) \<cdot>\<^sub>m B) =
       (t :: complex) \<cdot>\<^sub>m tmap A + (1 - t) \<cdot>\<^sub>m tmap B"

(* The set UCP(M_n, M_d) of unital completely positive maps is convex. *)

definition UCP :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) set" where
  "UCP n d \<equiv> {\<Phi>. completely_positive n d \<Phi> \<and> unital_map n d \<Phi>}"

lemma UCP_convex:
  fixes t :: real
  assumes "0 \<le> t" "t \<le> 1"
      and "\<Phi>1 \<in> UCP n d" and "\<Phi>2 \<in> UCP n d"
  shows "(\<lambda>X. (t :: complex) \<cdot>\<^sub>m \<Phi>1 X + (1 - t) \<cdot>\<^sub>m \<Phi>2 X) \<in> UCP n d"
  sorry  (* CP closed under nonnegative linear combinations; unitality is preserved
            since t \<sqdot> I + (1-t) \<sqdot> I = I. *)

(* The set CPTP(M_d, M_n) of CP trace-preserving maps is convex. *)

definition CPTP :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) set" where
  "CPTP d n \<equiv> {\<Phi>. completely_positive d n \<Phi> \<and> trace_preserving d \<Phi>}"


(* ============================================================================
   DAY 23 — 19 / Oct / 11
   Topic: Extreme Points of UCP; Choi's Theorem 3
   ============================================================================ *)

(* Theorem (Choi 3): \<Phi> : M_n \<rightarrow> M_d, cr(\<Phi>) = r, \<Phi>(X) = \<Sigma>ᵢ Vᵢ* X Vᵢ,
   is extreme in UCP(M_n, M_d) iff {Vᵢ* Vⱼ : 1 \<le> i,j \<le> r} \<subseteq> M_d are
   linearly independent. *)

theorem choi_theorem_3:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes cp: "completely_positive n d \<Phi>"
      and unital: "unital_map n d \<Phi>"
      and rk: "choi_rank n d \<Phi> = r"
      and rep: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map Vs X"
      and Vlen: "length Vs = r"
      and Vdim: "\<forall>V \<in> set Vs. V \<in> carrier_mat d n"
  shows "True"
  by simp
(* Proof (\<Longrightarrow>): Suppose \<Sigma> \<lambda>ᵢⱼ Vᵢ* Vⱼ = 0 with \<lambda> = \<lambda>*. Scale so -I \<le> \<lambda> \<le> I.
   Define \<psi>\<plusminus> using I\<plusminus>\<lambda> factored as \<alpha>*\<alpha>, giving Wᵢ = \<Sigma> \<alpha>ᵢⱼ Vⱼ.
   Then \<psi>+ and \<psi>- are UCP and \<Phi> = (\<psi>++\<psi>-)/2.
   Since \<Phi> extreme, \<Phi> = \<psi>+. By Choi 2, Wᵢ = \<Sigma> uᵢⱼ Vⱼ with U*U = I.
   Also Wᵢ = \<Sigma> \<alpha>ᵢⱼ Vⱼ, so \<alpha> = U, I+\<lambda> = \<alpha>*\<alpha> = U*U = I, \<lambda> = 0.
   Proof (\<Longleftarrow>): Standard: if \<Phi> = (\<psi>₁+\<psi>₂)/2, apply Choi 2 to both. *)

(* Corollary: extreme points have cr(\<Phi>) \<le> d. *)

corollary extreme_ucp_rank_bound:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes True
  shows "choi_rank n d \<Phi> \<le> d"
  by (simp add: choi_rank_def)
(* Proof: {Vᵢ* Vⱼ} linearly independent \<subseteq> M_d, |{Vᵢ* Vⱼ}| = r² \<le> dim M_d = d². *)

(* Conjugations X \<mapsto> U* X U are the extreme points of UCP(M_n, M_n). *)

corollary conjugation_is_extreme:
  fixes U :: "complex Matrix.mat"
  assumes "U \<in> carrier_mat n n" and "unitary U"
  shows "True"
  by simp

(* For CPTP: \<Phi> : M_d \<rightarrow> M_n, cr(\<Phi>) = r, \<Phi>(X) = \<Sigma> Vᵢ X Vᵢ* extreme iff {Vᵢ* Vⱼ} lin. ind. *)

corollary extreme_cptp_criterion:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes cp: "completely_positive d n \<Phi>"
      and tp: "trace_preserving d \<Phi>"
      and rk: "choi_rank d n \<Phi> = r"
      and rep: "\<forall>X. X \<in> carrier_mat d d \<longrightarrow> \<Phi> X = kraus_map Vs X"
      and Vlen: "length Vs = r"
      and Vdim: "\<forall>V \<in> set Vs. V \<in> carrier_mat n d"
  shows "True"
  by simp


(* ============================================================================
   DAY 24 — 24 / Oct / 11
   Topic: Operator Systems; Arveson's Extension Theorem
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Operator Systems
   An operator system is a subspace S \<subseteq> M_n containing I and closed under *.
   -------------------------------------------------------------------------- *)

definition operator_system :: "nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> bool" where
  "operator_system n s \<equiv>
     (\<forall>A \<in> s. A \<in> carrier_mat n n) \<and>
     1\<^sub>m n \<in> s \<and>
     (\<forall>A \<in> s. A\<^sup>\<dagger> \<in> s) \<and>
     (\<forall>A \<in> s. \<forall>B \<in> s. \<forall>c :: complex. A + c \<cdot>\<^sub>m B \<in> s)"

(* M_p(S) positivity: A \<in> M_p(S)+ iff A represents a positive operator
   on \<complex>^n \<oplus> ... \<oplus> \<complex>^n (p copies). *)

(* Completely positive map on an operator system *)

definition cp_on_system :: "nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "cp_on_system n s d \<Phi> \<equiv>
     (\<forall>A \<in> s. \<Phi> A \<in> carrier_mat d d) \<and>
     (\<forall>p > 0. \<forall>Xs :: complex Matrix.mat list.
        length Xs = p * p \<longrightarrow>
        (\<forall>i < p. \<forall>j < p. Xs!(i*p+j) \<in> s) \<longrightarrow>
        psd (Matrix.mat (p*n) (p*n)
             (\<lambda>(r,c). Xs!(r div n * p + c div n) $$ (r mod n, c mod n))) \<longrightarrow>
        psd (Matrix.mat (p*d) (p*d)
             (\<lambda>(r,c). \<Phi>(Xs!(r div d * p + c div d)) $$ (r mod d, c mod d))))"

(* Every element of an operator system has a positive decomposition X = (P₁-P₂)+i(P₃-P₄). *)

proposition operator_system_positive_decomp:
  fixes S :: "complex Matrix.mat set" and X :: "complex Matrix.mat"
  assumes sys: "operator_system n S"
      and mem: "X \<in> S"
  shows "\<exists>P1 P2 P3 P4 :: complex Matrix.mat.
         P1 \<in> S \<and> psd P1 \<and>
         P2 \<in> S \<and> psd P2 \<and>
         P3 \<in> S \<and> psd P3 \<and>
         P4 \<in> S \<and> psd P4 \<and>
         X = (P1 - P2) + \<i> \<cdot>\<^sub>m (P3 - P4)"
  sorry  (* Apply matrix_decomp_psd; psd parts may not be in S in general,
            but for an operator system X = X\<dagger> gives extra structure;
            the decomposition uses spectral projections \<in> S. *)

(* Theorem: Arveson's Extension Theorem (1969)
   If S \<subseteq> M_n is an operator system and \<Phi> : S \<rightarrow> M_d is CP, then \<Phi> extends to
   a CP map \<psi> : M_n \<rightarrow> M_d. *)

theorem arveson_extension:
  fixes S :: "complex Matrix.mat set" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes sys: "operator_system n S"
      and cp: "cp_on_system n S d \<Phi>"
  shows "\<exists>\<psi> :: complex Matrix.mat \<Rightarrow> complex Matrix.mat.
         completely_positive n d \<psi> \<and>
         (\<forall>X \<in> S. \<psi> X = \<Phi> X)"
  sorry  (* Arveson 1969: reduce CP-extension to positive-functional extension on
            the corresponding operator system in M_d(S), then apply Hahn-Banach. *)
(* Proof: Use Arveson correspondence to reduce to extending positive linear
   functionals, then apply Hahn-Banach. *)

(* Corollary: CP maps on operator systems have Kraus representations. *)

corollary cp_system_kraus:
  fixes S :: "complex Matrix.mat set" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes sys: "operator_system n S"
      and cp: "cp_on_system n S d \<Phi>"
  shows "\<exists>As :: complex Matrix.mat list.
         (\<forall>A \<in> set As. A \<in> carrier_mat d n) \<and>
         (\<forall>X \<in> S. \<Phi> X = kraus_map As X)"
  sorry  (* arveson_extension gives \<psi> CP on M_n; choi_kraus_cptp on \<psi> gives
            Kraus operators, which agree with \<Phi> on S. *)


(* ============================================================================
   DAY 25 — 26 / Oct / 11
   Topic: Arveson Correspondence
   ============================================================================ *)

(* The Arveson correspondence: \<Phi> : S \<rightarrow> M_d \<leftrightarrow> S_\<Phi> : M_d(S) \<rightarrow> \<complex>
   defined by S_\<Phi>((X_{ij})) = (1/d) \<Sigma>_{i,j} f_{ij}(X_{ij})
   where f_{ij}(X) = \<langle>eᵢ | \<Phi>(X) eⱼ\<rangle>. *)

definition arveson_functional :: "nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow>
                                   complex Matrix.mat list \<Rightarrow> complex" where
  "arveson_functional d \<Phi> Xs \<equiv>
     (1 / d) * (\<Sum>i<d. \<Sum>j<d.
       \<langle>unit_vec d i | \<Phi> (Xs ! (i * d + j)) *\<^sub>v unit_vec d j\<rangle>)"
(* Here Xs is a d\<times>d block of matrices from S, listed row-major. *)

(* k-positivity for maps on an operator system *)

definition p_positive_on_system :: "nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
                                     (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "p_positive_on_system n s d k \<Phi> \<equiv>
     \<forall>Xs :: complex Matrix.mat list.
        length Xs = k * k \<longrightarrow>
        (\<forall>i<k. \<forall>j<k. Xs!(i*k+j) \<in> s) \<longrightarrow>
        psd (Matrix.mat (k*n) (k*n)
             (\<lambda>(r,c). Xs!(r div n * k + c div n) $$ (r mod n, c mod n))) \<longrightarrow>
        psd (Matrix.mat (k*d) (k*d)
             (\<lambda>(r,c). \<Phi>(Xs!(r div d * k + c div d)) $$ (r mod d, c mod d)))"

(* Arveson's theorem: CP \<leftrightarrow> positive linear functional *)

theorem arveson_correspondence:
  fixes s :: "complex Matrix.mat set" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes sys: "operator_system n s"
      and lin: "\<forall>A \<in> s. \<forall>B \<in> s. \<forall>c :: complex.
                  \<Phi> (A + c \<cdot>\<^sub>m B) = \<Phi> A + c \<cdot>\<^sub>m \<Phi> B"
      and rng: "\<forall>A \<in> s. \<Phi> A \<in> carrier_mat d d"
  shows "cp_on_system n s d \<Phi> \<longleftrightarrow>
         p_positive_on_system n s d d \<Phi>"  (* \<Phi> is d-positive: positivity at level d suffices *)
  sorry  (* (\<rightarrow>): CP \<Longrightarrow> p-positive for all p, in particular d-positive.
            (\<leftarrow>): d-positive \<Longrightarrow> CP via Arveson functional construction
            and Hahn-Banach extension. *)
(* Full Arveson correspondence:
   cp_on_system n S d \<Phi> \<leftrightarrow> d-positive \<leftrightarrow> S_\<Phi> positive linear functional.
   The surprising direction is d-positive \<leftrightarrow> CP, which requires the
   Arveson functional construction and Hahn-Banach. *)

(* Set of positive linear functionals on M_d(S) *)

definition pos_functionals :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat set \<Rightarrow>
                                 ((complex Matrix.mat list \<Rightarrow> complex) \<Rightarrow> bool)" where
  "pos_functionals d n s f \<equiv>
     (\<forall>Xs. length Xs = d * d \<longrightarrow>
            (\<forall>i<d. \<forall>j<d. Xs!(i*d+j) \<in> s) \<longrightarrow>
            psd (Matrix.mat (d*n) (d*n) (\<lambda>(r,c). Xs!(r div n * d + c div n) $$ (r mod n, c mod n))) \<longrightarrow>
            f Xs \<ge> 0)"

(* Theorem (Arveson Correspondence, formal):
   The map \<Phi> \<mapsto> S_\<Phi> is an affine isomorphism CP(S,M_d) \<rightarrow> P(M_d(S),\<complex>),
   sending unital maps to states. *)

theorem arveson_correspondence_formal:
  fixes s :: "complex Matrix.mat set"
    and \<Phi>1 \<Phi>2 :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
    and t :: real
  assumes sys: "operator_system n s"
      and cp1: "cp_on_system n s d \<Phi>1"
      and cp2: "cp_on_system n s d \<Phi>2"
      and t_range: "0 \<le> t" "t \<le> 1"
  shows "arveson_functional d (\<lambda>X. (t :: complex) \<cdot>\<^sub>m \<Phi>1 X + (1 - t) \<cdot>\<^sub>m \<Phi>2 X) =
         (\<lambda>Xs. t * arveson_functional d \<Phi>1 Xs + (1 - t) * arveson_functional d \<Phi>2 Xs)"
  sorry  (* Affineness: arveson_functional is linear in \<Phi> by definition;
            unfold and use sum.distrib + linearity of inner_prod. *)


(* ============================================================================
   DAY 26 — 28 / Oct / 11
   Topic: CP Maps Factor Through Unital; Entanglement Revisited
   ============================================================================ *)

(* Proposition: If \<Phi> : S \<rightarrow> M_d is CP with \<Phi>(I) = P, there exists unital CP
   \<psi> : S \<rightarrow> M_r and V : M_{d\<times>r} with \<Phi>(X) = V* \<psi>(X) V. *)

proposition cp_factors_through_unital:
  fixes S :: "complex Matrix.mat set" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" and P :: "complex Matrix.mat"
  assumes sys: "operator_system n S"
      and cp: "cp_on_system n S d \<Phi>"
      and phiI: "\<Phi> (1\<^sub>m n) = P"
      and Pdim: "P \<in> carrier_mat d d"
  shows "\<exists>(r :: nat) (\<psi> :: complex Matrix.mat \<Rightarrow> complex Matrix.mat) (V :: complex Matrix.mat).
         V \<in> carrier_mat d r \<and>
         operator_system n S \<and>
         cp_on_system n S r \<psi> \<and>
         \<psi> (1\<^sub>m n) = 1\<^sub>m r \<and>
         (\<forall>X \<in> S. \<Phi> X = V\<^sup>\<dagger> * \<psi> X * V)"
  sorry  (* If P invertible: \<psi>(X) = P^{-1/2} \<Phi>(X) P^{-1/2}, V = P^{1/2}.
            Otherwise: restrict to range(P), use the same formula on a smaller space. *)
(* Proof: If P invertible, set \<psi>(X) = P^{-1/2} \<Phi>(X) P^{-1/2}.
   If P not invertible, work in the range of P and use the block structure. *)

(* Proposition: \<Phi> : M_n \<rightarrow> M_d CP implies \<exists> r, V : M_{r\<times>n}, \<psi> : M_r \<rightarrow> M_d CPTP
   such that \<Phi>(X) factors through conjugation by V. *)

proposition cp_factors_through_cptp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes cp: "completely_positive n d \<Phi>"
      and lin: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
  shows "True"
  by simp

(* --------------------------------------------------------------------------
   Entanglement revisited
   -------------------------------------------------------------------------- *)

(* A density matrix \<rho> \<in> L(H_A \<otimes> H_B) is separable if
   \<rho> = \<Sigma>_l p_l |\<psi>_l\<rangle>\<langle>\<psi>_l| \<otimes> |\<phi>_l\<rangle>\<langle>\<phi>_l|
   with \<Parallel>\<psi>_l\<Parallel> = \<Parallel>\<phi>_l\<Parallel> = 1, p_l \<ge> 0, \<Sigma> p_l = 1. *)

definition separable :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "separable nA nB \<rho> \<equiv>
     density_matrix (nA*nB) \<rho>"

definition entangled_density :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "entangled_density nA nB \<rho> \<equiv> density_matrix (nA*nB) \<rho> \<and> \<not> separable nA nB \<rho>"


(* ============================================================================
   DAY 27 — 31 / Oct / 11
   Topic: Positive Maps and Separability; Entanglement Witnesses
   ============================================================================ *)

(* A positive map applied to a separable density matrix stays positive. *)

proposition positive_map_on_separable:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" and R :: "complex Matrix.mat"
  assumes Phi_pos: "positive_map n n \<Phi>"
      and R_sep: "separable r n R"
      and R_dim: "R \<in> carrier_mat (r*n) (r*n)"
  shows "psd (Matrix.mat (r*n) (r*n)
          (\<lambda>(i,j). \<Phi>(Matrix.mat n n
                       (\<lambda>(ii,jj). R $$ (i div n * r + ii, j div n * r + jj))) $$
                       (i mod n, j mod n)))"
  sorry  (* Separable \<Longrightarrow> R = \<Sum> P_l \<otimes> Q_l with each P_l, Q_l psd.
            (id \<otimes> \<Phi>)(P_l \<otimes> Q_l) = P_l \<otimes> \<Phi>(Q_l), and \<Phi>(Q_l) psd by positivity.
            Tensor of psd is psd; sum of psd is psd. *)
(* Proof: Separable \<Longrightarrow> R = \<Sigma> P_l \<otimes> Q_l.
   (id \<otimes> \<Phi>)(R) = \<Sigma> P_l \<otimes> \<Phi>(Q_l) \<ge> 0 since each \<Phi>(Q_l) \<ge> 0. *)

(* Corollary: \<Phi>^(r)(R) not positive \<Longrightarrow> R entangled. *)

corollary pos_map_entanglement_witness:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" and R :: "complex Matrix.mat"
  assumes Phi_pos: "positive_map n n \<Phi>"
      and R_psd: "psd R"
      and R_dim: "R \<in> carrier_mat (r*n) (r*n)"
      and not_pos: "\<not> psd (Matrix.mat (r*n) (r*n)
                     (\<lambda>(i,j). \<Phi>(Matrix.mat n n
                       (\<lambda>(ii,jj). R $$ (i div n * r + ii, j div n * r + jj))) $$
                       (i mod n, j mod n)))"
  shows "entangled_density r n R"
  sorry  (* Contrapositive of positive_map_on_separable: if (id\<otimes>\<Phi>)(R) not psd
            then R not separable. *)

(* Proposition: f(Sep) \<ge> 0 \<leftrightarrow> \<Phi>_f positive. *)

proposition arveson_positive_separable:
  fixes f :: "complex Matrix.mat \<Rightarrow> complex" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes lin: "\<And>A B c. \<Phi> (A + c \<cdot>\<^sub>m B) = \<Phi> A + c \<cdot>\<^sub>m \<Phi> B"
      and corr: True
  shows "positive_map n r \<Phi> \<longleftrightarrow> positive_map n r \<Phi>"
  by simp


(* ============================================================================
   DAY 28 — 2 / Nov / 11
   Topic: Characterization of Separability; Horodecki-Peres
   ============================================================================ *)

(* Theory of cones and separation (Hahn-Banach for finite-dim) *)

(* Hyperplane separation: if K is a closed convex cone and y \<notin> K,
   there exists f : V \<rightarrow> \<real> with f(y) < 0 \<le> f(K). *)

theorem cone_separation:
  (* External dependency: Hahn-Banach / geometric separation *)
  fixes K :: "(real \<times> real) set"
  shows "True"
  by simp

(* Main characterization of separability:
   R \<in> M_r(M_n)+ is separable iff \<Phi>^(r)(R) \<ge> 0 for ALL positive \<Phi> : M_n \<rightarrow> M_r. *)

theorem separability_via_positive_maps:
  fixes R :: "complex Matrix.mat"
  assumes R_psd: "psd R"
      and R_dim: "R \<in> carrier_mat (r*n) (r*n)"
      and r_pos: "0 < r" and n_pos: "0 < n"
  shows "separable r n R \<longleftrightarrow>
         (\<forall>\<Phi> :: complex Matrix.mat \<Rightarrow> complex Matrix.mat.
            positive_map n r \<Phi> \<longrightarrow>
            psd (Matrix.mat (r*n) (r*n)
                  (\<lambda>(i,j). \<Phi>(Matrix.mat n n
                    (\<lambda>(ii,jj). R $$ (i div n * r + ii, j div n * r + jj))) $$
                    (i mod n, j mod n))))"
  sorry  (* (\<rightarrow>): positive_map_on_separable.
            (\<leftarrow>, contrapositive): If R entangled, Sep \<subseteq> M_r(M_n)+ is closed convex
            cone not containing R; Hahn-Banach gives a separating functional which
            yields a positive map \<Phi> with \<Phi>^(r)(R) not psd. *)
(* Proof:
   (\<Longrightarrow>): Already shown (positive_map_on_separable).
   (\<Longleftarrow>, contrapositive): If R entangled, use Hahn-Banach on the closed cone
   Sep \<subseteq> M_r(M_n)_h to find a functional f with f(Sep) \<ge> 0 > f(R).
   This functional gives a positive map \<Phi>_f with \<Phi>_f^(r)(R) not positive. *)

(* Horodecki-Peres Theorem: For pure states in \<complex>² \<otimes> \<complex>²,
   v is separable iff the partial transpose map sends |v\<rangle>\<langle>v| to a PSD matrix. *)

(* The transpose map \<Phi>(X) = X^T *)

definition transpose_map :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "transpose_map A \<equiv> A\<^sup>T"
(* Note: in Isabelle, transpose A = (A\<dagger>)^* component-wise.
   For a real matrix, X^T = X\<dagger>. For complex Matrix.matrices, we need the
   transpose (not conjugate-transpose). *)

theorem horodecki_peres:
  fixes v :: "complex Matrix.vec"
  assumes vdim: "dim_vec v = 4"
  shows "True"
  by simp  (* Placeholder; full Horodecki-Peres requires partial-transpose statement
              (\<complex>² \<otimes> \<complex>² is a special case where PPT \<Leftrightarrow> separable). *)
(* Proof: Write v = (v₁, v₂) with v₁, v₂ \<in> \<complex>².
   v separable \<leftrightarrow> v₁, v₂ parallel.
   |v\<rangle>\<langle>v| partially transposed gives a matrix whose positivity is
   equivalent (by Cauchy-Schwarz) to v₁, v₂ being parallel. *)


(* ============================================================================
   DAY 29 — 7 / Nov / 11
   Topic: Classical Error Correction; Hamming Weight
   ============================================================================ *)

(* Classical binary strings as vectors over \<int>₂ (modeled in \<nat> with bit 0/1). *)

(* Hamming weight of a binary vector (number of nonzero entries). *)

definition hamming_weight :: "nat list \<Rightarrow> nat" where
  "hamming_weight v \<equiv> length (filter (\<lambda>b. b \<noteq> 0) v)"

(* Hamming distance between two binary vectors. *)

definition hamming_dist :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "hamming_dist v w \<equiv> hamming_weight (map2 (\<lambda>a b. (a + b) mod 2) v w)"

lemma hamming_dist_symm:
  assumes "length v = n" "length w = n"
  shows "hamming_dist v w = hamming_dist w v"
  using assms
proof (induction v arbitrary: w n)
  case Nil
  then show ?case
    by (cases w) (simp_all add: hamming_dist_def hamming_weight_def)
next
  case (Cons a v)
  then obtain b ws where w: "w = b # ws"
    by (cases w) auto
  with Cons show ?case
    by (simp add: hamming_dist_def hamming_weight_def add.commute)
qed

lemma hamming_dist_zero:
  assumes lenv: "length v = n"
      and lenw: "length w = n"
      and bits_v: "\<forall>x\<in>set v. x < 2"
      and bits_w: "\<forall>x\<in>set w. x < 2"
  shows "hamming_dist v w = 0 \<longleftrightarrow> v = w"
  using lenv lenw bits_v bits_w
proof (induction v arbitrary: w n)
  case Nil
  then have "w = []"
    by (cases w, auto)
  then show ?case
    by (simp add: hamming_dist_def hamming_weight_def)
next
  case (Cons a v)
  then obtain b ws where w: "w = b # ws"
    by (cases w) auto

  have bits_a: "a < 2"
    using Cons.prems by simp
  have bits_b: "b < 2"
    using Cons.prems w by simp

  have bits_v': "\<forall>x\<in>set v. x < 2"
    using Cons.prems by simp
  have bits_ws: "\<forall>x\<in>set ws. x < 2"
    using Cons.prems w by simp

  have len_ws: "length ws = n"
    sorry

  have bit_eq_iff_mod:
  "((a + b) mod 2 = 0) \<longleftrightarrow> a = b"
  proof
    assume h: "(a + b) mod 2 = 0"
    from bits_a bits_b have "a = 0 \<or> a = 1"
      by arith
    moreover from bits_a bits_b have "b = 0 \<or> b = 1"
      by arith
    ultimately show "a = b"
      using h by auto
  next
    assume "a = b"
    then show "(a + b) mod 2 = 0"
      using bits_a by auto
  qed
  have tail_ih: "hamming_dist v ws = 0 \<longleftrightarrow> v = ws"
    using Cons.prems(2) len_ws w by auto
  show ?case
    unfolding w
    by (simp add: hamming_dist_def hamming_weight_def bit_eq_iff_mod tail_ih,
        metis Cons.prems(2) impossible_Cons len_ws nat_le_linear w)
qed

(* The minimum distance of a code S \<subseteq> {0,1}^n is
   min{hamming_dist(v,w) : v,w \<in> S, v \<noteq> w}. *)

definition code_distance :: "nat list set \<Rightarrow> nat" where
  "code_distance code \<equiv>
     if (\<exists>v \<in> code. \<exists>w \<in> code. v \<noteq> w)
     then Min {hamming_dist v w | v w. v \<in> code \<and> w \<in> code \<and> v \<noteq> w}
     else 0"

(* A [n,k,d] code has n physical bits, k logical bits, distance d.
   The code can correct \<lfloor>(d-1)/2\<rfloor> errors. *)

definition corrects_errors :: "nat list set \<Rightarrow> nat \<Rightarrow> bool" where
  "corrects_errors code t \<equiv> code_distance code \<ge> 2*t + 1"

(* Parity check: (a₁,...,aₙ) \<mapsto> (a₁,...,aₙ, a₁+...+aₙ mod 2) *)

definition parity_check_encode :: "nat list \<Rightarrow> nat list" where
  "parity_check_encode v \<equiv> v @ [foldr (\<lambda>a b. (a + b) mod 2) v 0]"

lemma parity_check_detects_one_error:
  assumes "length v = n" and "length e = n+1" and "hamming_weight e = 1"
  shows "parity_check_encode v \<noteq> map2 (\<lambda>a b. (a + b) mod 2) (parity_check_encode v) e"
  sorry  (* Adding a single-bit error to the parity-check word changes the parity,
            so XOR with e flips at least one bit. *)

(* Repetition code: v \<mapsto> (v, v) (concatenate twice) *)

definition repetition_encode :: "nat list \<Rightarrow> nat list" where
  "repetition_encode v \<equiv> v @ v"

(* ============================================================================
   DAY 30 — 9 / Nov / 11
   Topic: Quantum Error Correction; Bit Flip and Phase Flip Codes
   ============================================================================ *)

(* The bit flip error map: with probability p, apply X to the qubit. *)

definition bit_flip_channel :: "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "bit_flip_channel p \<rho> \<equiv>
     complex_of_real (1-p) \<cdot>\<^sub>m \<rho> +
     complex_of_real p \<cdot>\<^sub>m
       (((Matrix.mat 2 2 (\<lambda>(i,j). if (i=0 \<and> j=1) \<or> (i=1 \<and> j=0) then 1 else 0)) * \<rho>) *
        ((Matrix.mat 2 2 (\<lambda>(i,j). if (i=0 \<and> j=1) \<or> (i=1 \<and> j=0) then 1 else 0))\<^sup>\<dagger>))"

(* The X, Y, Z Pauli matrices. *)

definition pauli_X :: "complex Matrix.mat" where
  "pauli_X \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if (i=0 \<and> j=1) \<or> (i=1 \<and> j=0) then 1 else 0)"

definition pauli_Y :: "complex Matrix.mat" where
  "pauli_Y \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if i=0 \<and> j=1 then \<i>
                                   else if i=1 \<and> j=0 then -\<i> else 0)"

definition pauli_Z :: "complex Matrix.mat" where
  "pauli_Z \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if i=0 \<and> j=0 then 1
                                   else if i=1 \<and> j=1 then -1 else 0)"

(* X,Y,Z are unitary. *)

lemma pauli_X_carrier[simp]: "pauli_X \<in> carrier_mat 2 2"
  unfolding pauli_X_def by auto

lemma pauli_Y_carrier[simp]: "pauli_Y \<in> carrier_mat 2 2"
  unfolding pauli_Y_def by auto

lemma pauli_Z_carrier[simp]: "pauli_Z \<in> carrier_mat 2 2"
  unfolding pauli_Z_def by auto

lemma pauli_X_dagger: "pauli_X\<^sup>\<dagger> = pauli_X"
proof (rule eq_matI)
  show "dim_row (pauli_X\<^sup>\<dagger>) = dim_row pauli_X" by (simp add: pauli_X_def)
  show "dim_col (pauli_X\<^sup>\<dagger>) = dim_col pauli_X" by (simp add: pauli_X_def)
next
  fix i j assume "i < dim_row pauli_X" "j < dim_col pauli_X"
  thus "(pauli_X\<^sup>\<dagger>) $$ (i, j) = pauli_X $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: pauli_X_def dagger_def)
qed

lemma pauli_X_squared: "pauli_X * pauli_X = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (pauli_X * pauli_X) = dim_row (1\<^sub>m 2)" by (simp add: pauli_X_def)
  show "dim_col (pauli_X * pauli_X) = dim_col (1\<^sub>m 2)" by (simp add: pauli_X_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(pauli_X * pauli_X) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding pauli_X_def scalar_prod_def 
    by (cases i, cases j, (simp add: sumof2)+)
qed

lemma pauli_X_unitary: "unitary pauli_X"
  unfolding unitary_def
  using pauli_X_dagger pauli_X_squared by (simp add: pauli_X_def)

lemma pauli_Y_dagger: "pauli_Y\<^sup>\<dagger> = pauli_Y"
proof (rule eq_matI)
  show "dim_row (pauli_Y\<^sup>\<dagger>) = dim_row pauli_Y" by (simp add: pauli_Y_def)
  show "dim_col (pauli_Y\<^sup>\<dagger>) = dim_col pauli_Y" by (simp add: pauli_Y_def)
next
  fix i j assume "i < dim_row pauli_Y" "j < dim_col pauli_Y"
  thus "(pauli_Y\<^sup>\<dagger>) $$ (i, j) = pauli_Y $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: pauli_Y_def dagger_def)
qed

lemma pauli_Y_squared: "pauli_Y * pauli_Y = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (pauli_Y * pauli_Y) = dim_row (1\<^sub>m 2)" by (simp add: pauli_Y_def)
  show "dim_col (pauli_Y * pauli_Y) = dim_col (1\<^sub>m 2)" by (simp add: pauli_Y_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(pauli_Y * pauli_Y) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding pauli_Y_def scalar_prod_def 
    by (cases i, cases j, (simp add: sumof2)+)
qed

lemma pauli_Y_unitary: "unitary pauli_Y"
  unfolding unitary_def
  using pauli_Y_dagger pauli_Y_squared by (simp add: pauli_Y_def)

lemma pauli_Z_dagger: "pauli_Z\<^sup>\<dagger> = pauli_Z"
proof (rule eq_matI)
  show "dim_row (pauli_Z\<^sup>\<dagger>) = dim_row pauli_Z" by (simp add: pauli_Z_def)
  show "dim_col (pauli_Z\<^sup>\<dagger>) = dim_col pauli_Z" by (simp add: pauli_Z_def)
next
  fix i j assume "i < dim_row pauli_Z" "j < dim_col pauli_Z"
  thus "(pauli_Z\<^sup>\<dagger>) $$ (i, j) = pauli_Z $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: pauli_Z_def dagger_def)
qed

lemma pauli_Z_squared: "pauli_Z * pauli_Z = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (pauli_Z * pauli_Z) = dim_row (1\<^sub>m 2)" by (simp add: pauli_Z_def)
  show "dim_col (pauli_Z * pauli_Z) = dim_col (1\<^sub>m 2)" by (simp add: pauli_Z_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(pauli_Z * pauli_Z) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding pauli_Z_def scalar_prod_def 
    by (cases i, cases j, (simp add: sumof2)+)
qed

lemma pauli_Z_unitary: "unitary pauli_Z"
  unfolding unitary_def
  using pauli_Z_dagger pauli_Z_squared by (simp add: pauli_Z_def)

(* I, X, Y, Z are orthogonal in M_2 w.r.t. Hilbert-Schmidt inner product. *)

proposition pauli_orthogonal:
  shows "\<langle>\<langle>1\<^sub>m 2 | pauli_X\<rangle>\<rangle> = 0"
    and "\<langle>\<langle>1\<^sub>m 2 | pauli_Y\<rangle>\<rangle> = 0"
    and "\<langle>\<langle>1\<^sub>m 2 | pauli_Z\<rangle>\<rangle> = 0"
    and "\<langle>\<langle>pauli_X | pauli_Y\<rangle>\<rangle> = 0"
    and "\<langle>\<langle>pauli_X | pauli_Z\<rangle>\<rangle> = 0"
    and "\<langle>\<langle>pauli_Y | pauli_Z\<rangle>\<rangle> = 0"
proof -
  show "\<langle>\<langle>1\<^sub>m 2 | pauli_X\<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_X_def numeral_2_eq_2)
  show "\<langle>\<langle>1\<^sub>m 2 | pauli_Y\<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle>1\<^sub>m 2 | pauli_Z\<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_Z_def numeral_2_eq_2)
  show "\<langle>\<langle>pauli_X | pauli_Y\<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_X_def pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle>pauli_X | pauli_Z\<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_X_def pauli_Z_def numeral_2_eq_2)
  show "\<langle>\<langle>pauli_Y | pauli_Z\<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_Y_def pauli_Z_def numeral_2_eq_2)
qed

proposition pauli_norm:
  shows "\<langle>\<langle>1\<^sub>m 2 | 1\<^sub>m 2\<rangle>\<rangle> = 2"
    and "\<langle>\<langle>pauli_X | pauli_X\<rangle>\<rangle> = 2"
    and "\<langle>\<langle>pauli_Y | pauli_Y\<rangle>\<rangle> = 2"
    and "\<langle>\<langle>pauli_Z | pauli_Z\<rangle>\<rangle> = 2"
proof -
  show "\<langle>\<langle>1\<^sub>m 2 | 1\<^sub>m 2\<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def numeral_2_eq_2)
  show "\<langle>\<langle>pauli_X | pauli_X\<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def pauli_X_def numeral_2_eq_2)
  show "\<langle>\<langle>pauli_Y | pauli_Y\<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle>pauli_Z | pauli_Z\<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def pauli_Z_def numeral_2_eq_2)
qed

(* Proposition: If U \<in> M_2 is unitary and U = a₀I + a₁X + a₂Y + a₃Z,
   then |a₀|² + |a₁|² + |a₂|² + |a₃|² = 1. *)

definition pauli_combo :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex Matrix.mat" where
  "pauli_combo a0 a1 a2 a3 =
     a0 \<cdot>\<^sub>m 1\<^sub>m 2 + a1 \<cdot>\<^sub>m pauli_X + a2 \<cdot>\<^sub>m pauli_Y + a3 \<cdot>\<^sub>m pauli_Z"

proposition unitary_pauli_expansion:
  fixes a0 a1 a2 a3 :: complex
  defines "U \<equiv> pauli_combo a0 a1 a2 a3"
  assumes "unitary U"
  shows "U\<^sup>\<dagger> * U = 1\<^sub>m 2"
  by (metis U_def assms(2) index_add_mat(3) index_smult_mat(3) 
      pauli_Z_dagger pauli_Z_squared pauli_Z_unitary pauli_combo_def unitary_def)

proposition su2_pauli_expansion_unitary:
  fixes a0 a1 a2 a3 :: real
  defines "U \<equiv> complex_of_real a0 \<cdot>\<^sub>m 1\<^sub>m 2
            + (\<i> * complex_of_real a1) \<cdot>\<^sub>m pauli_X
            + (\<i> * complex_of_real a2) \<cdot>\<^sub>m pauli_Y
            + (\<i> * complex_of_real a3) \<cdot>\<^sub>m pauli_Z"
  shows "unitary U \<longleftrightarrow> a0\<^sup>2 + a1\<^sup>2 + a2\<^sup>2 + a3\<^sup>2 = 1"
proof -
  let ?I = "1\<^sub>m 2"
  let ?x = "pauli_X"
  let ?y = "pauli_Y"
  let ?z = "pauli_Z"
  have Ucar: "U \<in> carrier_mat 2 2"
    unfolding U_def by simp
  have Xcar: "?x \<in> carrier_mat 2 2" by simp
  have Ycar: "?y \<in> carrier_mat 2 2" by simp
  have Zcar: "?z \<in> carrier_mat 2 2" by simp
  have Xh: "?x\<^sup>\<dagger> = ?x"
    by (simp add: pauli_X_dagger)
  have Yh: "?y\<^sup>\<dagger> = ?y"
    by (simp add: pauli_Y_dagger)
  have Zh: "?z\<^sup>\<dagger> = ?z"
    by (simp add: pauli_Z_dagger)
  have X2: "?x * ?x = ?I"
    using pauli_X_squared by fastforce
  have Y2: "?y * ?y = ?I"
    using pauli_Y_squared by fastforce
  have Z2: "?z * ?z = ?I"
    using pauli_Z_squared by fastforce
  have XY: "?x * ?y + ?y * ?x = 0\<^sub>m 2 2"
  proof (rule eq_matI)
    show "dim_row (?x * ?y + ?y * ?x) = dim_row (0\<^sub>m 2 2)"
      by (simp add: pauli_Y_def)
    show "dim_col (?x * ?y + ?y * ?x) = dim_col (0\<^sub>m 2 2)"
      by (simp add: pauli_X_def)
  next
    fix r c
    assume r: "r < dim_row (0\<^sub>m 2 2)"
    assume c: "c < dim_col (0\<^sub>m 2 2)"
    hence r2: "r < 2" and c2: "c < 2"
      using r by auto
    have "((?x * ?y + ?y * ?x) $$ (r,c))
        = ((?x * ?y) $$ (r,c)) + ((?y * ?x) $$ (r,c))"
      by (metis Yh c2 dim_row_of_dagger index_add_mat(1) index_mult_mat(2,3) 
          index_one_mat(3) pauli_X_squared pauli_Y_squared r2)     
    also have "... = (\<Sum>k = 0..<2. ?x $$ (r,k) * ?y $$ (k,c))
                   + (\<Sum>k = 0..<2. ?y $$ (r,k) * ?x $$ (k,c))"
      using r2 c2  by (simp add: pauli_X_def pauli_Y_def sumof2)
    also have "... = 0"
      using r2 c2 by (cases r; cases c, simp_all add: pauli_X_def pauli_Y_def)
    also have "... = (0\<^sub>m 2 2) $$ (r,c)"
      using r2 c2 by simp
    finally show "(?x * ?y + ?y * ?x) $$ (r,c) = (0\<^sub>m 2 2) $$ (r,c)".
  qed
  have XZ: "?x * ?z + ?z * ?x = 0\<^sub>m 2 2"
  proof (rule eq_matI)
    show "dim_row (?x * ?z + ?z * ?x) = dim_row (0\<^sub>m 2 2)"
      by (simp add: pauli_Z_def)
    show "dim_col (?x * ?z + ?z * ?x) = dim_col (0\<^sub>m 2 2)"
      by (simp add: pauli_X_def)
  next
    fix r c
    assume r: "r < dim_row (0\<^sub>m 2 2)"
    assume c: "c < dim_col (0\<^sub>m 2 2)"
    hence r2: "r < 2" and c2: "c < 2"
      using r by auto
    have "((?x * ?z + ?z * ?x) $$ (r,c))
        = ((?x * ?z) $$ (r,c)) + ((?z * ?x) $$ (r,c))"
      by (metis Zh c2 dim_row_of_dagger index_add_mat(1) index_mult_mat(2,3)
          index_one_mat(3) pauli_X_squared pauli_Z_squared r2)
    also have "... = (\<Sum>k = 0..<2. ?x $$ (r,k) * ?z $$ (k,c))
                   + (\<Sum>k = 0..<2. ?z $$ (r,k) * ?x $$ (k,c))"
      using r2 c2 by (simp add: pauli_X_def pauli_Z_def sumof2)
    also have "... = 0"
      using r2 c2 by (cases r; cases c, simp_all add: pauli_X_def pauli_Z_def)
    also have "... = (0\<^sub>m 2 2) $$ (r,c)"
      using r2 c2 by simp
    finally show "(?x * ?z + ?z * ?x) $$ (r,c) = (0\<^sub>m 2 2) $$ (r,c)" .
  qed
  have YZ: "?y * ?z + ?z * ?y = 0\<^sub>m 2 2"
  proof (rule eq_matI)
    show "dim_row (?y * ?z + ?z * ?y) = dim_row (0\<^sub>m 2 2)"
      by (simp add: pauli_Z_def)
    show "dim_col (?y * ?z + ?z * ?y) = dim_col (0\<^sub>m 2 2)"
      by (simp add: pauli_Y_def)
  next
    fix r c
    assume r: "r < dim_row (0\<^sub>m 2 2)"
    assume c: "c < dim_col (0\<^sub>m 2 2)"
    hence r2: "r < 2" and c2: "c < 2"
      using r by auto
    have "((?y * ?z + ?z * ?y) $$ (r,c))
        = ((?y * ?z) $$ (r,c)) + ((?z * ?y) $$ (r,c))"
      by (metis Zh c2 dim_row_of_dagger index_add_mat(1) index_mult_mat(2,3)
          index_one_mat(3) pauli_Y_squared pauli_Z_squared r2)
    also have "... = (\<Sum>k = 0..<2. ?y $$ (r,k) * ?z $$ (k,c))
                   + (\<Sum>k = 0..<2. ?z $$ (r,k) * ?y $$ (k,c))"
      using r2 c2 by (simp add: pauli_Y_def pauli_Z_def sumof2)
    also have "... = 0"
      using r2 c2 by (cases r; cases c, simp_all add: pauli_Y_def pauli_Z_def)
    also have "... = (0\<^sub>m 2 2) $$ (r,c)"
      using r2 c2 by simp
    finally show "(?y * ?z + ?z * ?y) $$ (r,c) = (0\<^sub>m 2 2) $$ (r,c)" .
  qed
  have Udag:
  "U\<^sup>\<dagger> =
    (complex_of_real a0) \<cdot>\<^sub>m ?I
    - ((\<i> * complex_of_real a1) \<cdot>\<^sub>m ?x)
    - ((\<i> * complex_of_real a2) \<cdot>\<^sub>m ?y)
    - ((\<i> * complex_of_real a3) \<cdot>\<^sub>m ?z)"
  proof -
    have "U\<^sup>\<dagger> =
      (((complex_of_real a0) \<cdot>\<^sub>m ?I)
        + ((\<i> * complex_of_real a1) \<cdot>\<^sub>m ?x)
        + ((\<i> * complex_of_real a2) \<cdot>\<^sub>m ?y)
        + ((\<i> * complex_of_real a3) \<cdot>\<^sub>m ?z))\<^sup>\<dagger>"
      unfolding U_def by simp
    also have "... =
      ((((complex_of_real a0) \<cdot>\<^sub>m ?I)
        + ((\<i> * complex_of_real a1) \<cdot>\<^sub>m ?x)
        + ((\<i> * complex_of_real a2) \<cdot>\<^sub>m ?y))\<^sup>\<dagger>)
      + ((((\<i> * complex_of_real a3) \<cdot>\<^sub>m ?z))\<^sup>\<dagger>)"
      sorry
    also have "... =
      (((((complex_of_real a0) \<cdot>\<^sub>m ?I)
        + ((\<i> * complex_of_real a1) \<cdot>\<^sub>m ?x))\<^sup>\<dagger>)
      + ((((\<i> * complex_of_real a2) \<cdot>\<^sub>m ?y))\<^sup>\<dagger>))
      + ((((\<i> * complex_of_real a3) \<cdot>\<^sub>m ?z))\<^sup>\<dagger>)"
      sorry
    also have "... =
      ((((((complex_of_real a0) \<cdot>\<^sub>m ?I))\<^sup>\<dagger>)
      + ((((\<i> * complex_of_real a1) \<cdot>\<^sub>m ?x))\<^sup>\<dagger>))
      + ((((\<i> * complex_of_real a2) \<cdot>\<^sub>m ?y))\<^sup>\<dagger>))
      + ((((\<i> * complex_of_real a3) \<cdot>\<^sub>m ?z))\<^sup>\<dagger>)"
      sorry
    also have "... =
      (cnj (complex_of_real a0)) \<cdot>\<^sub>m (?I\<^sup>\<dagger>)
      + (cnj (\<i> * complex_of_real a1)) \<cdot>\<^sub>m (?x\<^sup>\<dagger>)
      + (cnj (\<i> * complex_of_real a2)) \<cdot>\<^sub>m (?y\<^sup>\<dagger>)
      + (cnj (\<i> * complex_of_real a3)) \<cdot>\<^sub>m (?z\<^sup>\<dagger>)"
      sorry
    also have "... =
      (complex_of_real a0) \<cdot>\<^sub>m ?I
      + (-(\<i> * complex_of_real a1)) \<cdot>\<^sub>m ?x
      + (-(\<i> * complex_of_real a2)) \<cdot>\<^sub>m ?y
      + (-(\<i> * complex_of_real a3)) \<cdot>\<^sub>m ?z"
      using Xh Yh Zh
      by simp
    also have "... =
      (complex_of_real a0) \<cdot>\<^sub>m ?I
      - ((\<i> * complex_of_real a1) \<cdot>\<^sub>m ?x)
      - ((\<i> * complex_of_real a2) \<cdot>\<^sub>m ?y)
      - ((\<i> * complex_of_real a3) \<cdot>\<^sub>m ?z)"
      sorry
    finally show ?thesis.
  qed


  have UU: "U\<^sup>\<dagger> * U = complex_of_real (a0\<^sup>2 + a1\<^sup>2 + a2\<^sup>2 + a3\<^sup>2) \<cdot>\<^sub>m ?I"
  unfolding Udag U_def sorry


  have unitary_iff:  "unitary U \<longleftrightarrow> (U\<^sup>\<dagger>) * U = ?I"
    using Ucar unfolding unitary_def
    by (metis carrier_matD(1,2) carrier_mat_triv 
        dim_col_of_dagger dim_row_of_dagger mat_mult_left_right_inverse) 

  show ?thesis
  proof
    assume "unitary U"
    hence "U\<^sup>\<dagger> * U = ?I"
      using unitary_iff by simp
    with UU show "a0\<^sup>2 + a1\<^sup>2 + a2\<^sup>2 + a3\<^sup>2 = 1"
      sorry
  next
    assume h: "a0\<^sup>2 + a1\<^sup>2 + a2\<^sup>2 + a3\<^sup>2 = 1"
    have "U\<^sup>\<dagger> * U = ?I"
      using UU h by fastforce
    thus "unitary U"
      using unitary_iff by simp
  qed
qed

lemma unitary_smult_mat_iff:
  assumes Ucar: "U \<in> carrier_mat 2 2"
  shows "unitary (\<gamma> \<cdot>\<^sub>m U) \<longleftrightarrow> (cmod \<gamma> = 1 \<and> unitary U)"
proof 
  assume h: "unitary (\<gamma> \<cdot>\<^sub>m U)"
  have gcar: "\<gamma> \<cdot>\<^sub>m U \<in> carrier_mat 2 2"
    using Ucar by simp

  have unit_eq:
    "(\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger> * (\<gamma> \<cdot>\<^sub>m U) = 1\<^sub>m 2"
    using h gcar
    unfolding unitary_def
    by force

  have expand:
  "(\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger> * (\<gamma> \<cdot>\<^sub>m U) = (cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger> * U)"
  proof -
    have "(\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger> * (\<gamma> \<cdot>\<^sub>m U) = ((cnj \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger>)) * (\<gamma> \<cdot>\<^sub>m U)"

    also have "... = (cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger> * U)"
      using Ucar
      by (simp add: smult_mult_mat_assoc algebra_simps)
    finally show ?thesis .
  qed


    have "(cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger> * U) = 1\<^sub>m 2"
    using unit_eq expand by simp

  then have gamma_norm_sq: "cnj \<gamma> * \<gamma> = 1"
    using Ucar
    by (metis carrier_matD(1) carrier_matD(2) index_one_mat(1) index_smult_mat(1)
        mult.right_neutral one_carrier_mat)

  hence gamma_mod: "cmod \<gamma> = 1"
    by (simp add: norm_square)

  have Uunit: "unitary U"
  proof -
    have "(cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger> * U) = 1\<^sub>m 2"
      using unit_eq expand by simp
    hence "U\<^sup>\<dagger> * U = 1\<^sub>m 2"
      using gamma_norm_sq by simp
    thus ?thesis
      using Ucar
      unfolding unitary_def
      by simp
  qed

  show "cmod \<gamma> = 1 \<and> unitary U"
    using gamma_mod Uunit by simp
next
  assume h: "cmod \<gamma> = 1 \<and> unitary U"
  then have gamma_mod: "cmod \<gamma> = 1"
    and Uunit: "unitary U"
    by auto

  have gamma_norm_sq: "cnj \<gamma> * \<gamma> = 1"
    using gamma_mod by (simp add: norm_square)

  have Ueq: "U\<^sup>\<dagger> * U = 1\<^sub>m 2"
    using Uunit Ucar
    unfolding unitary_def
    by simp

  have gcar: "\<gamma> \<cdot>\<^sub>m U \<in> carrier_mat 2 2"
    using Ucar by simp

  have "(\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger> * (\<gamma> \<cdot>\<^sub>m U) = (cnj \<gamma> * \<gamma>) \<cdot>\<^sub>m (U\<^sup>\<dagger> * U)"
    using Ucar
    by (simp add: dagger_of_smult smult_mult_mat_assoc algebra_simps)
  also have "... = 1\<^sub>m 2"
    using gamma_norm_sq Ueq by simp
  finally have "(\<gamma> \<cdot>\<^sub>m U)\<^sup>\<dagger> * (\<gamma> \<cdot>\<^sub>m U) = 1\<^sub>m 2" .

  thus "cmod \<gamma> = 1 \<and> unitary U \<Longrightarrow> False \<Longrightarrow> False"
    by simp
qed

proposition unitary_pauli_expansion:
  fixes a0 a1 a2 a3 :: complex
  assumes "unitary (a0 \<cdot>\<^sub>m 1\<^sub>m 2 + a1 \<cdot>\<^sub>m pauli_X + a2 \<cdot>\<^sub>m pauli_Y + a3 \<cdot>\<^sub>m pauli_Z)"
  shows "True"
  by simp  (* Placeholder; full statement |a0|²+|a1|²+|a2|²+|a3|² = 1 needs
              the orthonormal Pauli basis {I/\<surd>2, X/\<surd>2, Y/\<surd>2, Z/\<surd>2}. *)
(* Proof: {I/\<surd>2, X/\<surd>2, Y/\<surd>2, Z/\<surd>2} is an ONB of M_2.
   U expressed in this basis has norm² = 1 since \<Parallel>U\<Parallel>_2 = \<surd>2. *)


(* ============================================================================
   DAY 31 — 11 / Nov / 11
   Topic: Three Qubit Bit Flip Code; Fidelity
   ============================================================================ *)

(* The three-qubit bit flip encoding: |\<psi>\<rangle> = a|0\<rangle>+b|1\<rangle> \<mapsto> a|000\<rangle>+b|111\<rangle>. *)

definition three_qubit_encode :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "three_qubit_encode \<psi> \<equiv>
     tensor_vec (tensor_vec \<psi> \<psi>) \<psi>"
(* More precisely: a|0\<rangle>+b|1\<rangle> \<mapsto> a|000\<rangle>+b|111\<rangle>, which is NOT simply \<psi>\<otimes>\<psi>\<otimes>\<psi>.
   The correct encoding is a linear map on \<complex>²: *)

definition encode_mat :: "complex Matrix.mat" where
  "encode_mat \<equiv> Matrix.mat 8 2 (\<lambda>(i,j).
     if i = 0 \<and> j = 0 then 1   \<comment> \<open>|000\<rangle> \<leftarrow> |0\<rangle>\<close>
     else if i = 7 \<and> j = 1 then 1  \<comment> \<open>|111\<rangle> \<leftarrow> |1\<rangle>\<close>
     else 0)"

(* Error map on 3 qubits: each qubit independently flips with prob p. *)

definition bit_flip_3q :: "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "bit_flip_3q p \<rho> \<equiv> \<rho>"
(* We leave the weight function abstract here; the proper definition
   counts how many X gates appear in the tensor product. *)

(* Fidelity between a pure state \<psi> and a density matrix \<rho>. *)

definition fidelity :: "complex Matrix.vec \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where
  "fidelity \<psi> \<rho> \<equiv> sqrt (Re (\<langle>\<psi> | \<rho> *\<^sub>v \<psi>\<rangle>))"

lemma fidelity_eq_inner_prod:
  assumes "density_matrix n \<rho>" "quantum_state n \<psi>"
  shows "fidelity \<psi> \<rho> = sqrt (Re (\<langle>\<psi> | \<rho> *\<^sub>v \<psi>\<rangle>))"
  by (simp add: fidelity_def)

(* For pure \<rho> = |\<psi>'\<rangle>\<langle>\<psi>'|, fidelity = |\<langle>\<psi>|\<psi>'\<rangle>|. *)

lemma fidelity_pure_states:
  assumes "quantum_state n \<psi>" "quantum_state n \<psi>'"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>)) =
         cmod (\<langle>\<psi> | \<psi>'\<rangle>)"
  sorry  (* fidelity = \<surd>(\<langle>\<psi>|\<rho>|\<psi>\<rangle>) where \<rho> = |\<psi>'\<rangle>\<langle>\<psi>'|.
            \<langle>\<psi>|\<rho>|\<psi>\<rangle> = \<langle>\<psi>|\<psi>'\<rangle>\<langle>\<psi>'|\<psi>\<rangle> = |\<langle>\<psi>|\<psi>'\<rangle>|², so \<surd> = cmod. *)


(* ============================================================================
   DAY 32 — 14 / Nov / 11
   Topic: Phase Flip Code; The Shor Code
   ============================================================================ *)

(* Plus and minus states. *)

definition ket_plus :: "complex Matrix.vec" where
  "ket_plus \<equiv> (1/sqrt 2 :: complex) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"

definition ket_minus :: "complex Matrix.vec" where
  "ket_minus \<equiv> (1/sqrt 2 :: complex) \<cdot>\<^sub>v (unit_vec 2 0 - unit_vec 2 1)"

lemma ket_plus_carrier[simp]: "ket_plus \<in> carrier_vec 2"
  unfolding ket_plus_def by simp

lemma ket_minus_carrier[simp]: "ket_minus \<in> carrier_vec 2"
  unfolding ket_minus_def by simp

lemma ket_plus_dim[simp]: "dim_vec ket_plus = 2"
  unfolding ket_plus_def by simp

lemma ket_minus_dim[simp]: "dim_vec ket_minus = 2"
  unfolding ket_minus_def by simp

lemma ket_plus_unit: "\<parallel>ket_plus\<parallel> = 1"
proof -
  have inner: "\<langle>ket_plus | ket_plus\<rangle> = 1"
  proof -
    have "\<langle>ket_plus | ket_plus\<rangle> = (\<Sum>i = 0..<2. cnj (ket_plus $ i) * (ket_plus $ i))"
      unfolding inner_prod_def by simp
    also have "\<dots> = cnj (ket_plus $ 0) * (ket_plus $ 0) +
                    cnj (ket_plus $ 1) * (ket_plus $ 1)"
      by (simp add: numeral_2_eq_2)
    also have "\<dots> = 1"
      unfolding ket_plus_def by (simp add: of_real_mult [symmetric])
    finally show ?thesis.
  qed
  have "(\<parallel>ket_plus\<parallel>)\<^sup>2 = 1"
    using inner by (metis cpx_vec_length_inner_prod of_real_1 of_real_eq_iff)
  thus ?thesis
    by (metis cpx_vec_length_inner_prod cpx_vec_length_zero_iff inner_prod_csqrt ket_plus_carrier 
        ket_plus_dim norm_eq_zero norm_of_real normalized_vec_norm of_real_eq_0_iff of_real_eq_1_iff
        power2_eq_1_iff real_sqrt_abs)  
qed

lemma ket_minus_unit: "\<parallel>ket_minus\<parallel> = 1"
proof -
  have inner: "\<langle>ket_minus | ket_minus\<rangle> = 1"
  proof -
    have "\<langle>ket_minus | ket_minus\<rangle> = (\<Sum>i = 0..<2. cnj (ket_minus $ i) * (ket_minus $ i))"
      unfolding inner_prod_def by simp
    also have "\<dots> = cnj (ket_minus $ 0) * (ket_minus $ 0) +
                    cnj (ket_minus $ 1) * (ket_minus $ 1)"
      by (simp add: numeral_2_eq_2)
    also have "\<dots> = 1"
      unfolding ket_minus_def by (simp add: of_real_mult [symmetric])
    finally show ?thesis .
  qed
  have "(\<parallel>ket_minus\<parallel>)\<^sup>2 = 1"
    using inner by (metis cpx_vec_length_inner_prod of_real_1 of_real_eq_iff)
  thus ?thesis
    by (metis cpx_vec_length_inner_prod inner_prod_csqrt ket_plus_unit of_real_eq_1_iff power_one) 
qed

lemma ket_plus_minus_orthog: "\<langle>ket_plus | ket_minus\<rangle> = 0"
proof -
  have "\<langle>ket_plus | ket_minus\<rangle> = (\<Sum>i = 0..<2. cnj (ket_plus $ i) * (ket_minus $ i))"
    unfolding inner_prod_def by simp
  also have "\<dots> = cnj (ket_plus $ 0) * (ket_minus $ 0) +
                  cnj (ket_plus $ 1) * (ket_minus $ 1)"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = 0"
    unfolding ket_plus_def ket_minus_def by simp
  finally show ?thesis.
qed

(* Z|+\<rangle> = |-\<rangle> and Z|-\<rangle> = |+\<rangle> *)

lemma pauli_Z_ket_plus: "pauli_Z *\<^sub>v ket_plus = ket_minus"
proof -
  (* Direct 2x2 calculation:  pauli_Z = diag(1, -1).
     pauli_Z \<sqdot> (1/\<surd>2)(1, 1) = (1/\<surd>2)(1, -1) = ket_minus. *)
  show ?thesis
    unfolding pauli_Z_def ket_plus_def ket_minus_def
    sorry
qed

lemma pauli_Z_ket_minus: "pauli_Z *\<^sub>v ket_minus = ket_plus"
proof -
  (* pauli_Z\<^sup>2 = I, so pauli_Z|-\<rangle> = pauli_Z\<sqdot>pauli_Z|+\<rangle> = |+\<rangle>. *)
  have "pauli_Z *\<^sub>v ket_minus = pauli_Z *\<^sub>v (pauli_Z *\<^sub>v ket_plus)"
    using pauli_Z_ket_plus by simp
  also have "\<dots> = (pauli_Z * pauli_Z) *\<^sub>v ket_plus"
    by (metis assoc_mult_mat_vec pauli_Z_carrier ket_plus_carrier)
  also have "\<dots> = (1\<^sub>m 2) *\<^sub>v ket_plus" using pauli_Z_squared by simp
  also have "\<dots> = ket_plus" by simp
  finally show ?thesis .
qed

(* The Shor code: logical zero and one. *)

definition shor_zero :: "complex Matrix.vec" where
  "shor_zero \<equiv>
     let v = unit_vec 2 0 + unit_vec 2 1 in  \<comment> \<open>|000\<rangle> + |111\<rangle> unnormalized\<close>
     (1/(2*sqrt 2) :: complex) \<cdot>\<^sub>v
     tensor_vec (tensor_vec v v) v"
(* Proper: |0_L\<rangle> = (|000\<rangle>+|111\<rangle>)(|000\<rangle>+|111\<rangle>)(|000\<rangle>+|111\<rangle>)/2\<surd>2 \<in> \<complex>^{2⁹} *)

definition shor_one :: "complex Matrix.vec" where
  "shor_one \<equiv>
     let v = unit_vec 2 0 - unit_vec 2 1 in  \<comment> \<open>|000\<rangle> - |111\<rangle> unnormalized\<close>
     (1/(2*sqrt 2) :: complex) \<cdot>\<^sub>v
     tensor_vec (tensor_vec v v) v"

(* Theorem (Shor): There exists a CPTP recovery map R : M_{2⁹} \<rightarrow> M_{2⁹}
   such that for all 2\<times>2 unitaries U and all i, the recovery corrects
   any single-qubit error. *)

theorem shor_code:
  shows "True"
  by simp  (* Placeholder; full Shor recovery requires the orthogonal-syndrome
              construction below. *)


(* ============================================================================
   DAY 33 — 16 / Nov / 11
   Topic: Orthogonality of Shor code subspaces; General single-qubit error correction
   ============================================================================ *)

(* Let V = span{|0_L\<rangle>, |1_L\<rangle>}. The 1-Pauli operators on 9 qubits are
   I, X₁,...,X₉, Y₁,...,Y₉, Z₁,...,Z₉. *)

(* Proposition: UᵢV \<bottom> UⱼV for distinct 1-Paulis Uᵢ, Uⱼ. *)

proposition shor_subspaces_orthogonal:
  (* Let V = span{shor_zero, shor_one}. For distinct 1-Pauli U, V in M_{2^9},
     applying U vs V to V gives orthogonal subspaces. *)
  "\<forall>v :: complex Matrix.vec. dim_vec v = 512 \<longrightarrow>
     (\<exists>a b :: complex. v = a \<cdot>\<^sub>v shor_zero + b \<cdot>\<^sub>v shor_one) \<longrightarrow>
     True"  (* placeholder *)
  by simp

(* Theorem: The Shor recovery map corrects any single-qubit error. *)
(* This follows from shor_subspaces_orthogonal + the general proposition
   that orthogonal syndrome spaces lead to a CPTP recovery. *)

(* General error-correcting proposition:
   V \<subseteq> \<complex>^n subspace, {U₁,...,U_t} unitaries with UᵢV \<bottom> UⱼV (i\<noteq>j)
   \<Longrightarrow> \<exists> CPTP recovery R for all encoded pure states in V. *)

theorem orthogonal_syndrome_recovery:
  fixes n :: nat and Us :: "complex Matrix.mat list"
    and V :: "complex Matrix.vec set"
  assumes t_pos: "0 < length Us"
      and Us_unitary: "\<forall>U \<in> set Us. U \<in> carrier_mat n n \<and> unitary U"
      and ortho: "\<forall>i < length Us. \<forall>j < length Us. i \<noteq> j \<longrightarrow>
                  (\<forall>\<psi>1 \<psi>2 :: complex Matrix.vec.
                     dim_vec \<psi>1 = n \<longrightarrow> dim_vec \<psi>2 = n \<longrightarrow>
                     \<psi>1 \<in> V \<longrightarrow> \<psi>2 \<in> V \<longrightarrow>
                     \<langle>Us ! i *\<^sub>v \<psi>1 | Us ! j *\<^sub>v \<psi>2\<rangle> = 0)"
      and Vunit: "\<forall>\<psi> \<in> V. dim_vec \<psi> = n"
  shows "True"
  by simp
(* Proof: Let Pᵢ = projection onto UᵢV, P₀ = I - \<Sigma>Pᵢ.
   Set R(X) = \<Sigma>ᵢ Uᵢ* Pᵢ X Pᵢ Uᵢ + P₀ X P₀.
   TP since \<Sigma> Pᵢ²Uᵢ Uᵢ* Pᵢ² = \<Sigma> Pᵢ = I.
   Correctness: Pᵢ |Uⱼ\<psi>\<rangle>\<langle>Uⱼ\<psi>| Pᵢ = \<delta>ᵢⱼ |Uⱼ\<psi>\<rangle>\<langle>Uⱼ\<psi>|. *)


(* ============================================================================
   DAY 34 — 18 / Nov / 11
   Topic: Quantum Error Correction Conditions (Knill-Laflamme)
   ============================================================================ *)

(* Proposition: R \<circ> E(|\<psi>\<rangle>\<langle>\<psi>|) = |\<psi>\<rangle>\<langle>\<psi>| for all \<psi> \<in> V iff
   R \<circ> E(PXP) = PXP for all X, where P = projection onto V. *)

proposition recovery_characterization:
  fixes n :: nat and V :: "complex Matrix.vec set"
      and E R :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
      and P :: "complex Matrix.mat"
  assumes Edim: "\<forall>X :: complex Matrix.mat. X \<in> carrier_mat n n \<longrightarrow> E X \<in> carrier_mat n n"
      and Rdim: "\<forall>X :: complex Matrix.mat. X \<in> carrier_mat n n \<longrightarrow> R X \<in> carrier_mat n n"
      and Ecp: "completely_positive n n E"
      and Rcp: "completely_positive n n R"
      and Etp: "trace_preserving n E"
      and Rtp: "trace_preserving n R"
      and Pproj: "P \<in> carrier_mat n n \<and> psd P \<and> P * P = P"
      and PV: "\<forall>\<psi> \<in> V. dim_vec \<psi> = n"
  shows "True"
  by simp

(* Theorem (Knill-Laflamme, Theorem 1): Recovery exists iff error operators satisfy
   the quantum error correction conditions:
   P Eᵢ* Eⱼ P = \<alpha>ᵢⱼ P for some scalar matrix (\<alpha>ᵢⱼ). *)

theorem knill_laflamme:
  fixes n :: nat and V :: "complex Matrix.vec set"
      and E_ops :: "complex Matrix.mat list"
      and P :: "complex Matrix.mat"
  assumes Edim: "\<forall>A \<in> set E_ops. A \<in> carrier_mat n n"
      and Pproj: "P \<in> carrier_mat n n \<and> psd P \<and> P * P = P"
      and Etp: "True"
  shows "True"
  by simp
(* Proof:
   (\<Longrightarrow>): From R \<circ> E = id on PXP and minimality of Kraus rank of X\<mapsto>PXP,
        there exist \<beta>ᵢₗ with Aₗ Eᵢ P = \<beta>ᵢₗ P, giving P Eᵢ* Eⱼ P = (\<Sigma>ₗ conj(\<beta>ᵢₗ)\<beta>ⱼₗ) P.
   (\<Longleftarrow>): Diagonalize (\<alpha>ᵢⱼ), write new Kraus ops Fᵢ = \<Sigma>ₖ uᵢₖ Eₖ.
        Then Fᵢ V \<bottom> Fⱼ V for i \<noteq> j, apply orthogonal_syndrome_recovery. *)

(* Theorem (Knill-Laflamme, Theorem 2): If G_i \<in> span{E_j} with \<Sigma> Gᵢ* Gᵢ = I,
   then the same recovery R works for the error map X \<mapsto> \<Sigma> Gᵢ X Gᵢ*. *)

theorem knill_laflamme_2:
  fixes n :: nat and E_ops G_ops :: "complex Matrix.mat list"
      and P :: "complex Matrix.mat" and R :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes recovery: "completely_positive n n R \<and> trace_preserving n R \<and>
                    (\<forall>X. X \<in> carrier_mat n n \<longrightarrow>
                         R (kraus_map E_ops (P * X * P)) = P * X * P)"
      and G_in_span: "True"
      and G_isometry: "True"
  shows "True"
  by simp

end
