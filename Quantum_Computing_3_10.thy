(*  Title:   Quantum_Computing_3_10.thy
    Author:  Dustin Bryant, after Vern Paulsen's lectures of 31 August - 19 September 2011
             (Days 3-10).  Days 1-2 are in Basic_Math.
*)

theory Quantum_Computing_3_10
  imports Basic_Math Jordan_Normal_Form.Schur_Decomposition
begin

section \<open>Day 3 (31 August 2011): unitary matrices, Householder unitaries, Schur's theorem\<close>

subsection \<open>Unitary matrices\<close>

text \<open>\begin{notesdef}
$U\in M_n$ is \emph{unitary} if $U^*U=I$.
\end{notesdef}
\begin{notestheorem}
For $U\in M_n$ the following are equivalent: (a) $U$ is unitary; (b) $U$ is invertible and
$U^{-1}=U^*$; (c) $UU^*=I$; (d) $U^*$ is unitary; (e) the columns of $U$ are orthonormal;
(f) the rows of $U$ are orthonormal; (g) $\norm{Ux}=\norm{x}$ for all $x$ (isometry);
(h) $\braket{Ux}{Uy}=\braket{x}{y}$ for all $x,y$.
\end{notestheorem}
The library predicate \<^term>\<open>unitary U\<close> bundles (a) and (c).  The lemmas below give
(a)$\Rightarrow$(b), (d), (e), (f), (g), (h); (e)$\Rightarrow$(a) is
\<open>orthonormal_mat_unitary\<close>, (g)$\Rightarrow$(a) and (h)$\Rightarrow$(a) are
\<open>unitary_of_isometry\<close> and \<open>unitary_of_inner_prod_preserving\<close> (proved on Day 4, after
the polarisation lemma); (d) is self-dual and (f) follows from (e) for $U^*$.\<close>



lemma unitary_left_right:
  assumes "unitary U"
  shows "U\<^sup>\<dagger> * U = 1\<^sub>m (dim_col U)" and "U * (U\<^sup>\<dagger>) = 1\<^sub>m (dim_row U)"
  using assms by (simp_all add: unitary_def)

text \<open>(b) $U$ is invertible with inverse $U^*$:\<close>

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

text \<open>(d) $U^*$ is unitary:\<close>

lemma unitary_dagger_is_unitary:
  assumes "unitary U"
  shows "unitary (U\<^sup>\<dagger>)"
  using assms by (simp add: unitary_def dagger_of_dagger_is_id mult.commute)

text \<open>(e), (f) the columns and the rows of $U$ are orthonormal:\<close>


lemma unitary_cols_orthonormal:
  assumes U: "unitary U"
      and i: "i < dim_col U"
      and j: "j < dim_col U"
  shows "\<langle>Matrix.col U i | Matrix.col U j\<rangle> = (if i = j then 1 else 0 :: complex)"
  by (cases "i = j",
      metis U cpx_vec_length_inner_prod j of_real_power power_0 power_one unitary_unit_col,
      smt U i j orthogonal_col_of_unitary)


lemma unitary_rows_orthonormal:
  assumes U: "unitary U"
      and i: "i < dim_row U"
      and j: "j < dim_row U"
  shows "\<langle>Matrix.row U i | Matrix.row U j\<rangle> = (if i = j then 1 else 0 :: complex)"
  by (cases "i = j",
      metis U cpx_vec_length_inner_prod j of_real_power power_0 power_one unitary_unit_row,
      smt U i j orthogonal_row_of_unitary)

text \<open>(g), (h) $U$ is an isometry and preserves inner products:\<close>


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


lemma unitary_preserves_inner_prod:
  assumes U: "unitary U"
      and u: "dim_vec u = dim_col U"
      and v: "dim_vec v = dim_col U"
  shows "\<langle>U *\<^sub>v u | U *\<^sub>v v\<rangle> = \<langle>u | v\<rangle>"
  using inner_prod_with_unitary_mat[OF U u v]
  by (metis carrier_mat_triv col_fst_is_col col_mult2 dim_col dim_col_mat(1) 
      ket_vec_col ket_vec_def less_numeral_extra(1) u v) 

subsection \<open>Householder unitaries\<close>

text \<open>\begin{notesdef}
For $w\in\C^n$ with $\norm{w}=1$ let $P_w=\ketbra{w}{w}$, the projection onto
$\operatorname{span}\{w\}$, and $U_w=I-2P_w$.  Then $U_w^*U_w=(I-2P_w)^2=I-4P_w+4P_w^2=I$,
so $U_w$ is unitary: the \emph{Householder unitary} of $w$.
\end{notesdef}
\begin{notesremark}
Geometrically $U_w$ is the reflection through the hyperplane $\{w\}^\perp$.
\end{notesremark}
Formally \<open>householder w\<close> is defined entrywise as $(\delta_{ij}-2w_i\overline{w_j})$ and shown
to equal $I-2\ketbra{w}{w}$.\<close>

abbreviation outer_prod :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat"
    (infixr "\<oslash>" 75)
  where "v \<oslash> w \<equiv> |v\<rangle> * bra_vec w"

lemma bra_vec_index_0:
  assumes j: "j < dim_vec w"
  shows "bra_vec w $$ (0,j) = cnj (w $ j)"
  using j by (simp add: bra_vec_def row_vec_def cpx_mat_cnj_def)

lemma outer_prod_index:
  fixes v w :: "complex Matrix.vec"
  assumes i: "i < dim_vec v"
      and j: "j < dim_vec w"
  shows "(v \<oslash> w) $$ (i,j) = (v $ i) * cnj (w $ j)"
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
  shows "((v \<oslash> w) *\<^sub>v x) $ i = (v $ i) * \<langle>w | x\<rangle>"
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
  shows "(v \<oslash> w) *\<^sub>v x = \<langle>w | x\<rangle> \<cdot>\<^sub>v v"
proof (rule eq_vecI)
  show "dim_vec ((v \<oslash> w) *\<^sub>v x) = dim_vec (\<langle>w | x\<rangle> \<cdot>\<^sub>v v)"
    by (simp add: ket_vec_def)
next
  fix i
  assume i: "i < dim_vec (\<langle>w | x\<rangle> \<cdot>\<^sub>v v)"
  then have iv: "i < dim_vec v"
    by simp
  have "((v \<oslash> w) *\<^sub>v x) $ i = (v $ i) * \<langle>w | x\<rangle>"
    using outer_prod_mult_vec_index[OF xdim iv] .
  also have "\<dots> = (\<langle>w | x\<rangle> \<cdot>\<^sub>v v) $ i"
    using iv by (simp add: algebra_simps)
  finally show "((v \<oslash> w) *\<^sub>v x) $ i = (\<langle>w | x\<rangle> \<cdot>\<^sub>v v) $ i" .
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

text \<open>$\braket vv=0$ iff $v=0$.\<close>

lemma inner_prod_self_eq_zero_iff:
  fixes v :: "complex Matrix.vec"
  shows "\<langle>v | v\<rangle> = 0 \<longleftrightarrow> v = 0\<^sub>v (dim_vec v)"
proof
  assume h: "\<langle>v | v\<rangle> = 0"
  have "complex_of_real (\<parallel>v\<parallel>\<^sup>2) = 0" using h by (simp only: cpx_vec_length_inner_prod)
  hence "\<parallel>v\<parallel>\<^sup>2 = 0" by (simp only: of_real_eq_0_iff)
  hence "\<parallel>v\<parallel> = 0" by simp
  thus "v = 0\<^sub>v (dim_vec v)" using cpx_vec_length_zero_iff by simp
next
  assume "v = 0\<^sub>v (dim_vec v)" thus "\<langle>v | v\<rangle> = 0" by (rule inner_prod_with_itself_eq0)
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

text \<open>The adjoint of an $m\times n$ matrix is $n\times m$.\<close>

lemma dagger_carrier:
  assumes "M \<in> carrier_mat m n"
  shows "(M\<^sup>\<dagger>) \<in> carrier_mat n m"
  using assms
  by (simp add: dagger_def)

definition householder :: "complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "householder w \<equiv>
     Matrix.mat (dim_vec w) (dim_vec w)
       (\<lambda>(i,j). (if i = j then 1 else 0) - 2 * (w $ i) * cnj (w $ j))"

notation householder ("U\<^sub>H")


lemma householder_index:
  assumes "i < dim_vec w" and "j < dim_vec w"
  shows "(householder w) $$ (i,j) =
         (if i = j then 1 else 0) - 2 * (w $ i) * cnj (w $ j)"
  using assms by (simp add: householder_def)

lemma householder_outer_prod:
  "householder w = 1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<oslash> w)"
proof (rule eq_matI)
  show "dim_row (householder w) =
        dim_row (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<oslash> w))"
    by (simp add: householder_def ket_vec_def)
  show "dim_col (householder w) =
        dim_col (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<oslash> w))"
    by (simp add: householder_def bra_vec_def row_vec_def cpx_mat_cnj_def)
next
  fix i j
  assume i: "i < dim_row (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<oslash> w))"
  assume j: "j < dim_col (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<oslash> w))"
  then have ij: "i < dim_vec w" "j < dim_vec w"
    using i by (simp_all add: ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def)

  have "householder w $$ (i,j) =
        (if i = j then (1 :: complex) else 0) - 2 * (w $ i) * cnj (w $ j)"
    using householder_index[OF ij] .
  also have "\<dots> = (if i = j then (1 :: complex) else 0) -
        2 * ((w \<oslash> w) $$ (i,j))"
    using outer_prod_index[OF ij] by simp
  also have "\<dots> = (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<oslash> w)) $$ (i,j)"
    using ij by (simp add: ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def)
  finally show "householder w $$ (i,j) =
        (1\<^sub>m (dim_vec w) - 2 \<cdot>\<^sub>m (w \<oslash> w)) $$ (i,j)" .
qed


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

text \<open>\begin{noteslemma}[Schur]
Given $x,y\in\C^n$ with $\norm{x}=\norm{y}$ there are $w\in\C^n$ with $\norm{w}=1$ and
$\theta$ such that $U_w x=e^{i\theta}y$.
\end{noteslemma}
The formal statement writes $e^{i\theta}$ as \<^term>\<open>Complex (cos \<theta>) (sin \<theta>)\<close>; the case
$x=0$ is treated separately.\<close>

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

text \<open>\begin{notestheorem}[Schur]
For every $A\in M_n$ there is a unitary $U$ such that $U^*AU$ is upper triangular.
\end{notestheorem}
The notes prove this by induction, peeling off one eigenvector with the Householder
unitary of Schur's lemma and recursing on the $(n-1)\times(n-1)$ block.  The formal proof
follows the same route: \<open>schur_triangular_similar\<close> is the similarity version
available from the Jordan-Normal-Form library, and the block-matrix lemmas that follow
assemble the unitary step by step.\<close>

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

text \<open>Any unit vector extends to an orthonormal basis (needed for the induction).\<close>
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

text \<open>\begin{notesremark}
The characteristic polynomial of $A$ is $p_A(t)=\det(tI-A)$, a polynomial of degree $n$.
\end{notesremark}
\begin{notescor}
$\Tr(A)=\lambda_1+\cdots+\lambda_n$, where the $\lambda_j$ are the eigenvalues of $A$.
\end{notescor}
Formally the eigenvalues are listed as the roots of the characteristic polynomial,
$p_A(t)=\prod_j(t-\lambda_j)$, read off the diagonal of the Schur form.\<close>

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



section \<open>Day 4 (2 September 2011): Hermitian matrices; positive semidefinite and positive definite matrices\<close>

subsection \<open>Hermitian matrices\<close>

text \<open>\begin{notesdef}
$H\in M_n$ is \emph{Hermitian} (self-adjoint) if $H=H^*$.
\end{notesdef}
\begin{notestheorem}
The following are equivalent: (a) $H$ is Hermitian; (b) there is a unitary $U$ with
$U^*HU=D$ diagonal with real entries; (c) $\C^n$ has an orthonormal basis of eigenvectors of
$H$ with real eigenvalues; (d) $\braket{x}{Hx}\in\R$ for all $x\in\C^n$.
\end{notestheorem}
Formally \<open>hermitian H\<close> is $H^\dagger=H$; (a)$\Rightarrow$(b) is the spectral theorem
\<open>hermitian_spectral_decomp\<close> below, (a)$\Leftrightarrow$(d) is
\<open>hermitian_iff_real_quad_form\<close>, and (c) is read off from (b): the columns of $U$ are
an orthonormal eigenbasis.  The proof of (d)$\Rightarrow$(a) needs the following lemma,
which the notes note fails over $\R$ (take $T=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$).\<close>

definition hermitian :: "complex Matrix.mat \<Rightarrow> bool" where
  "hermitian A \<equiv> A\<^sup>\<dagger> = A"


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



text \<open>\begin{noteslemma}
For $T\in M_n$, if $\braket{x}{Tx}=0$ for all $x\in\C^n$, then $T=0$.
\end{noteslemma}\<close>

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

text \<open>The adjoint moves across the inner product, $\braket{x}{My}=\braket{M^\dagger x}{y}$:
the defining property of $M^\dagger$.\<close>

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


text \<open>Sums and real multiples of Hermitian matrices are Hermitian; the identity is Hermitian.\<close>

lemma hermitian_plus:
  fixes A B :: "complex Matrix.mat"
  assumes Aherm: "hermitian A" and Bherm: "hermitian B"
      and Ac: "A \<in> carrier_mat k k" and Bc: "B \<in> carrier_mat k k"
  shows "hermitian (A + B)"
  unfolding hermitian_def
proof (rule eq_matI)
  show "dim_row ((A + B)\<^sup>\<dagger>) = dim_row (A + B)" using Ac Bc by simp
  show "dim_col ((A + B)\<^sup>\<dagger>) = dim_col (A + B)" using Ac Bc by simp
  fix i j assume "i < dim_row (A + B)" "j < dim_col (A + B)"
  hence i_lt: "i < k" and j_lt: "j < k" using Ac Bc by auto
  have Ad: "A\<^sup>\<dagger> = A" using Aherm by (simp add: hermitian_def)
  have Bd: "B\<^sup>\<dagger> = B" using Bherm by (simp add: hermitian_def)
  have "((A + B)\<^sup>\<dagger>) $$ (i, j) = cnj ((A + B) $$ (j, i))"
    using i_lt j_lt Ac Bc by (simp add: dagger_def)
  also have "\<dots> = cnj (A $$ (j, i)) + cnj (B $$ (j, i))" using i_lt j_lt Ac Bc by simp
  also have "\<dots> = (A\<^sup>\<dagger>) $$ (i, j) + (B\<^sup>\<dagger>) $$ (i, j)"
    using i_lt j_lt Ac Bc by (simp add: dagger_def)
  also have "\<dots> = A $$ (i, j) + B $$ (i, j)" using Ad Bd by simp
  also have "\<dots> = (A + B) $$ (i, j)" using i_lt j_lt Ac Bc by simp
  finally show "((A + B)\<^sup>\<dagger>) $$ (i, j) = (A + B) $$ (i, j)" .
qed

lemma hermitian_identity:
  "hermitian (1\<^sub>m k :: complex Matrix.mat)"
  unfolding hermitian_def by (rule eq_matI) (auto simp: dagger_def)

lemma hermitian_real_scale:
  fixes A :: "complex Matrix.mat"
  assumes "hermitian A" "A \<in> carrier_mat k k"
  shows "hermitian (complex_of_real d \<cdot>\<^sub>m A)"
  unfolding hermitian_def
proof (rule eq_matI)
  let ?dA = "complex_of_real d \<cdot>\<^sub>m A"
  show "dim_row (?dA\<^sup>\<dagger>) = dim_row ?dA" using assms by simp
  show "dim_col (?dA\<^sup>\<dagger>) = dim_col ?dA" using assms by simp
  fix i j assume "i < dim_row ?dA" "j < dim_col ?dA"
  hence i_lt: "i < k" and j_lt: "j < k" using assms by auto
  have "?dA\<^sup>\<dagger> $$ (i,j) = cnj (?dA $$ (j,i))" using i_lt j_lt assms by (simp add: dagger_def)
  also have "\<dots> = cnj (complex_of_real d * A $$ (j,i))" using i_lt j_lt assms by simp
  also have "\<dots> = complex_of_real d * cnj (A $$ (j,i))" by (simp add: complex_cnj_mult)
  also have "\<dots> = complex_of_real d * (A\<^sup>\<dagger>) $$ (i,j)" using i_lt j_lt assms by (simp add: dagger_def)
  also have "\<dots> = complex_of_real d * A $$ (i,j)" using assms by (simp add: hermitian_def)
  also have "\<dots> = ?dA $$ (i,j)" using i_lt j_lt assms by simp
  finally show "?dA\<^sup>\<dagger> $$ (i,j) = ?dA $$ (i,j)" .
qed

text \<open>The converses (g)$\Rightarrow$(a) and (h)$\Rightarrow$(a) of the Day 3 theorem on unitaries,
postponed until the lemma $\braket{x}{Tx}=0\ \forall x\Rightarrow T=0$ was available: a
square matrix that preserves lengths, or inner products, is unitary (the library proves
the length-preserving case in its own matrix notation as \<open>length_preserving_is_unitary\<close>).\<close>

lemma unitary_of_isometry:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat n n"
      and iso: "\<And>v :: complex Matrix.vec. dim_vec v = n \<Longrightarrow> \<parallel>U *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
  shows "unitary U"
proof -
  let ?T = "U\<^sup>\<dagger> * U - 1\<^sub>m n"
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U by auto
  have UdU: "U\<^sup>\<dagger> * U \<in> carrier_mat n n" using U Ud by auto
  have T_c: "?T \<in> carrier_mat n n" using UdU by auto
  have qf0: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | ?T *\<^sub>v x\<rangle> = 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec" assume xd: "dim_vec x = n"
    have xc: "x \<in> carrier_vec n" using xd by auto
    have Ux: "dim_vec (U *\<^sub>v x) = n" using U xd by auto
    have "\<langle>x | (U\<^sup>\<dagger> * U) *\<^sub>v x\<rangle> = \<langle>x | U\<^sup>\<dagger> *\<^sub>v (U *\<^sub>v x)\<rangle>"
      using U Ud xc by (simp add: assoc_mult_mat_vec)
    also have "\<dots> = \<langle>(U\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | U *\<^sub>v x\<rangle>"
      using inner_prod_adjoint_swap[OF Ud xd Ux] .
    also have "\<dots> = \<langle>U *\<^sub>v x | U *\<^sub>v x\<rangle>"
      by (simp add: dagger_of_dagger_is_id)
    also have "\<dots> = \<langle>x | x\<rangle>"
      by (simp only: cpx_vec_length_inner_prod[symmetric] iso[OF xd])
    finally have A: "\<langle>x | (U\<^sup>\<dagger> * U) *\<^sub>v x\<rangle> = \<langle>x | x\<rangle>" .
    have "?T *\<^sub>v x = (U\<^sup>\<dagger> * U) *\<^sub>v x - 1\<^sub>m n *\<^sub>v x"
      using UdU xc by (simp add: minus_mult_distrib_mat_vec)
    also have "\<dots> = (U\<^sup>\<dagger> * U) *\<^sub>v x - x" using xc by simp
    finally have Tx: "?T *\<^sub>v x = (U\<^sup>\<dagger> * U) *\<^sub>v x - x" .
    have dims: "dim_vec ((U\<^sup>\<dagger> * U) *\<^sub>v x) = dim_vec x" using UdU xd by auto
    have "\<langle>x | ?T *\<^sub>v x\<rangle> = \<langle>x | (U\<^sup>\<dagger> * U) *\<^sub>v x\<rangle> - \<langle>x | x\<rangle>"
      unfolding Tx by (rule inner_prod_right_minus'[OF dims])
    thus "\<langle>x | ?T *\<^sub>v x\<rangle> = 0" using A by simp
  qed
  have T0: "?T = 0\<^sub>m n n" by (rule quadratic_form_zero[OF T_c qf0])
  have UdU1: "U\<^sup>\<dagger> * U = 1\<^sub>m n"
  proof (rule eq_matI)
    show "dim_row (U\<^sup>\<dagger> * U) = dim_row (1\<^sub>m n :: complex Matrix.mat)" using UdU by auto
    show "dim_col (U\<^sup>\<dagger> * U) = dim_col (1\<^sub>m n :: complex Matrix.mat)" using UdU by auto
    fix i j assume "i < dim_row (1\<^sub>m n :: complex Matrix.mat)" "j < dim_col (1\<^sub>m n :: complex Matrix.mat)"
    hence ij: "i < n" "j < n" by auto
    have "?T $$ (i, j) = 0" using T0 ij by simp
    thus "(U\<^sup>\<dagger> * U) $$ (i, j) = (1\<^sub>m n :: complex Matrix.mat) $$ (i, j)"
      using UdU ij by simp
  qed
  have UUd1: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using mat_mult_left_right_inverse[OF Ud U UdU1] .
  show ?thesis unfolding unitary_def using UdU1 UUd1 U by auto
qed

lemma unitary_of_inner_prod_preserving:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat n n"
      and pres: "\<And>u v :: complex Matrix.vec. dim_vec u = n \<Longrightarrow> dim_vec v = n \<Longrightarrow>
                   \<langle>U *\<^sub>v u | U *\<^sub>v v\<rangle> = \<langle>u | v\<rangle>"
  shows "unitary U"
proof (rule unitary_of_isometry[OF U])
  fix v :: "complex Matrix.vec" assume vd: "dim_vec v = n"
  have "complex_of_real (\<parallel>U *\<^sub>v v\<parallel>\<^sup>2) = complex_of_real (\<parallel>v\<parallel>\<^sup>2)"
    using pres[OF vd vd] by (simp only: cpx_vec_length_inner_prod[symmetric])
  hence sq: "\<parallel>U *\<^sub>v v\<parallel>\<^sup>2 = \<parallel>v\<parallel>\<^sup>2" by (simp only: of_real_eq_iff)
  have nn: "0 \<le> \<parallel>U *\<^sub>v v\<parallel>" "0 \<le> \<parallel>v\<parallel>" by (simp_all add: cpx_vec_length_def sum_nonneg)
  show "\<parallel>U *\<^sub>v v\<parallel> = \<parallel>v\<parallel>" using sq nn by (simp add: power2_eq_iff_nonneg)
qed

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

subsection \<open>The spectral theorem for Hermitian matrices\<close>

text \<open>(a)$\Rightarrow$(b) of the theorem above: by Schur, $U^*HU=T$ is upper triangular,
and $T^*=(U^*HU)^*=T$ forces $T$ to be diagonal with real entries.
\<open>diag_mat_of_real D\<close> is the complex diagonal matrix with the real list $D$ on its
diagonal.\<close>
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


subsection \<open>Positive semidefinite and positive definite matrices\<close>

text \<open>\begin{notesdef}
$P\in M_n$ is \emph{positive semidefinite}, $P\ge 0$, if $\braket{x}{Px}\ge 0$ for all
$x\in\C^n$, and \emph{positive definite}, $P>0$, if $\braket{x}{Px}>0$ for all $x\neq 0$.
\end{notesdef}
By part (d) of the previous theorem, $P\ge 0$ implies $P=P^*$.  The formal predicates
\<open>psd\<close> and \<open>pd\<close> carry Hermiticity as an explicit conjunct together with the real-part
inequality; by \<open>hermitian_iff_real_quad_form\<close> this is equivalent to the notes'
definition.
\begin{notestheorem}
$P\ge 0$ if and only if $P=P^*$ and all eigenvalues of $P$ are non-negative.
\end{notestheorem}
\begin{notescor}
$P>0$ if and only if $P=P^*$ and all eigenvalues of $P$ are strictly positive.
\end{notescor}
\begin{notestheorem}
$P\ge 0$ if and only if $P=\sum_{i=1}^m\ketbra{v_i}{v_i}$ for some vectors $v_1,\dots,v_m$.
\end{notestheorem}
Key: if $P=\sum_i\ketbra{v_i}{v_i}$ then $\braket{x}{Px}=\sum_i|\braket{v_i}{x}|^2$.
\begin{notestheorem}
Let $P=\sum_{i=1}^m\ketbra{v_i}{v_i}\in M_n$.  Then $P>0$ if and only if
$\operatorname{span}\{v_1,\dots,v_m\}=\C^n$.
\end{notestheorem}
The notes' form of the definition is \<open>psd_iff_quad_form_nonneg\<close>; the corollary on positive
definite matrices is \<open>pd_iff_pos_eigenvalues\<close> (proved after the square root); the last
theorem is formalised with ``the $v_i$ span $\C^n$'' phrased as ``no nonzero $x$ is
orthogonal to every $v_i$''.\<close>

definition psd :: "complex Matrix.mat \<Rightarrow> bool" where
  "psd P \<equiv> hermitian P \<and>
            (\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
               Re (\<langle>x | P *\<^sub>v x\<rangle>) \<ge> 0)"

definition pd :: "complex Matrix.mat \<Rightarrow> bool" where
  "pd P \<equiv> hermitian P \<and>
           (\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
              x \<noteq> 0\<^sub>v (dim_row P) \<longrightarrow>
              Re (\<langle>x | P *\<^sub>v x\<rangle>) > 0)"

notation psd ("_ \<ge>\<^sub>M 0")
notation pd  ("_ >\<^sub>M 0")


lemma psd_hermitian: "psd P \<Longrightarrow> hermitian P"
  by (simp add: psd_def)

text \<open>The notes' definition, without the explicit Hermiticity conjunct: $P\ge0$ iff every
quadratic form $\braket{x}{Px}$ is a non-negative real number.\<close>

lemma psd_iff_quad_form_nonneg:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
  shows "psd P \<longleftrightarrow>
         (\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow>
            \<langle>x | P *\<^sub>v x\<rangle> \<in> \<real> \<and> 0 \<le> Re (\<langle>x | P *\<^sub>v x\<rangle>))"
proof -
  have dr: "dim_row P = n" using sq by auto
  show ?thesis
    unfolding psd_def dr using hermitian_iff_real_quad_form[OF sq] by blast
qed

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

text \<open>$P\ge 0$ iff $P$ is Hermitian with non-negative eigenvalues:\<close>

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

text \<open>$P\ge 0$ iff $P=\sum_i\ketbra{v_i}{v_i}$.  First the direction $\Leftarrow$:\<close>

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

text \<open>The direction $\Rightarrow$, from the spectral theorem:
$P=\sum_j\lambda_j\ketbra{u_j}{u_j}=\sum_j\ketbra{\lambda_j^{1/2}u_j}{\lambda_j^{1/2}u_j}$.\<close>
text \<open>The spectral theorem for positive matrices: $P=U\,\mathrm{diag}(D)\,U^\dagger$ with $D\ge0$.\<close>

lemma psd_spectral_decomp_nonneg:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>(U :: complex Matrix.mat) (D :: real list).
           U \<in> carrier_mat n n \<and> unitary U \<and> length D = n \<and>
           (\<forall>i < n. 0 \<le> D ! i) \<and>
           P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
proof -
  have herm: "hermitian P" using pos by (rule psd_hermitian)
  obtain U :: "complex Matrix.mat" and D :: "real list" where
      Uc: "U \<in> carrier_mat n n"
    and UU: "unitary U"
    and Dlen: "length D = n"
    and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast
  have P_eq: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using hermitian_spectral_decomp_eq[OF Uc sq UU spec] .
  have PU_eq_UD: "P * U = U * diag_mat_of_real D"
    using hermitian_spectral_decomp_right[OF Uc sq UU spec] .
  have eig_nonneg:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    using psd_iff_nonneg_eigenvalues[OF sq] pos by blast
  have D_nonneg: "\<forall>i < n. D ! i \<ge> 0"
  proof (intro allI impI)
    fix i assume iltn: "i < n"
    let ?ui = "Matrix.col U i"
    have uidim: "dim_vec ?ui = n" using Uc by simp
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
      then have klt: "k < n" using uidim by simp
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
        finally show ?thesis .
      qed
      also have "\<dots> = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k"
        using klt Uc by (simp add: iltn)
      finally show "(P *\<^sub>v ?ui) $ k = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k" .
    qed
    have "0 \<le> Re (complex_of_real (D ! i))"
      using eig eig_nonneg ui_nonzero uidim by blast
    thus "D ! i \<ge> 0" by simp
  qed
  show ?thesis using Uc UU Dlen D_nonneg P_eq by blast
qed

theorem psd_kraus_decomp:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>vs :: complex Matrix.vec list.
         length vs = n \<and>
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
  have vs_len: "length ?vs = n" by simp
  show ?thesis using vs_len vs_dim decomp by blast
qed

text \<open>$P=\sum_i\ketbra{v_i}{v_i}$ is positive definite iff the $v_i$ span $\C^n$:\<close>

text \<open>Entries of $\sum_i\ketbra{v_i}{v_i}$ for an arbitrary list of vectors.\<close>

lemma outer_sum_entry_sum_list:
  assumes vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "outer_sum n vs $$ (i, j) =
         sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) vs)"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  have V_c: "?V \<in> carrier_mat n ?k"
    using vs_dim by (simp add: mat_of_cols_def)
  have Vdag_c: "?V\<^sup>\<dagger> \<in> carrier_mat ?k n"
    using V_c by (rule dagger_carrier)
  have "outer_sum n vs $$ (i, j) = (?V * (?V\<^sup>\<dagger>)) $$ (i, j)"
    by (simp add: outer_sum_def)
  also have "\<dots> = (\<Sum>l<?k. ?V $$ (i, l) * (?V\<^sup>\<dagger>) $$ (l, j))"
    using i_lt j_lt V_c Vdag_c by simp
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j))"
  proof (intro sum.cong refl)
    fix l assume "l \<in> {..<?k}"
    hence l_lt: "l < ?k" by simp
    have vl_dim: "dim_vec (vs ! l) = n" using vs_dim l_lt by auto
    have V_idx: "?V $$ (i, l) = (vs ! l) $ i"
      using i_lt l_lt by (simp add: mat_of_cols_def)
    have Vdag_idx: "(?V\<^sup>\<dagger>) $$ (l, j) = cnj ((vs ! l) $ j)"
      using j_lt l_lt vl_dim by (simp add: dagger_def mat_of_cols_def)
    show "?V $$ (i, l) * (?V\<^sup>\<dagger>) $$ (l, j) = (vs ! l) $ i * cnj ((vs ! l) $ j)"
      using V_idx Vdag_idx by simp
  qed
  also have "\<dots> = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) vs)"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  finally show ?thesis.
qed

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

text \<open>$U\,\mathrm{diag}(D)\,U^\dagger$ is positive whenever the real entries of $D$ are non-negative.\<close>

lemma psd_U_diag_Udag:
  fixes U :: "complex Matrix.mat" and D :: "real list"
  assumes Uc: "U \<in> carrier_mat n n"
      and Dlen: "length D = n"
      and Dnn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  shows "psd (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
proof -
  let ?D = "diag_mat_of_real D"
  let ?P = "U * ?D * (U\<^sup>\<dagger>)"
  have Udag_c: "(U\<^sup>\<dagger>) \<in> carrier_mat n n" using Uc by (rule dagger_carrier)
  have D_c: "?D \<in> carrier_mat n n"
    using Dlen diag_mat_of_real_carrier by metis
  have UD_c: "U * ?D \<in> carrier_mat n n"
    using Uc D_c by simp
  have P_c: "?P \<in> carrier_mat n n"
    using UD_c Udag_c by simp

  have herm: "hermitian ?P"
  proof -
    have UD_dim: "dim_col U = dim_row ?D"
      using Uc D_c by (metis carrier_matD)
    have UDU_dim: "dim_col (U * ?D) = dim_row (U\<^sup>\<dagger>)"
      using UD_c Udag_c by (metis carrier_matD)
    have prep1: "(U * ?D)\<^sup>\<dagger> = ((?D)\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
      using UD_dim by (rule dagger_of_prod)
    have prep2: "((U * ?D) * (U\<^sup>\<dagger>))\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * ?D)\<^sup>\<dagger>)"
      using UDU_dim by (rule dagger_of_prod)
    have prep3: "((U\<^sup>\<dagger>)\<^sup>\<dagger>) = U" using Uc by (subst dagger_of_dagger_is_id, simp)
    have prep4: "(?D)\<^sup>\<dagger> = ?D" using diag_mat_of_real_hermitian[unfolded hermitian_def] .
    have "(?P)\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * ?D)\<^sup>\<dagger>)" using prep2 by simp
    also have "\<dots> = U * ((U * ?D)\<^sup>\<dagger>)" using prep3 by simp
    also have "\<dots> = U * ((?D)\<^sup>\<dagger> * (U\<^sup>\<dagger>))" using prep1 by simp
    also have "\<dots> = U * (?D * (U\<^sup>\<dagger>))" using prep4 by simp
    also have "\<dots> = U * ?D * (U\<^sup>\<dagger>)"
      using Uc D_c Udag_c by (metis assoc_mult_mat)
    finally show ?thesis by (simp add: hermitian_def)
  qed

  have nn: "\<forall>x :: complex Matrix.vec.
              dim_vec x = dim_row ?P \<longrightarrow> 0 \<le> Re \<langle>x | ?P *\<^sub>v x\<rangle>"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume "dim_vec x = dim_row ?P"
    hence xdim: "dim_vec x = n" using P_c by auto
    have xcar: "x \<in> carrier_vec n" using xdim by auto
    let ?y = "(U\<^sup>\<dagger>) *\<^sub>v x"
    have ydim: "dim_vec ?y = n"
      using Udag_c by (metis carrier_matD(1) dim_mult_mat_vec)
    have ycar: "?y \<in> carrier_vec n" using ydim carrier_vec_dim_vec by blast 

    have step1: "?P *\<^sub>v x = U *\<^sub>v (?D *\<^sub>v ?y)"
    proof -
      have "?P *\<^sub>v x = (U * (?D * (U\<^sup>\<dagger>))) *\<^sub>v x"
        using Uc D_c Udag_c by (metis assoc_mult_mat)
      also have "\<dots> = U *\<^sub>v ((?D * (U\<^sup>\<dagger>)) *\<^sub>v x)"
        using Uc D_c Udag_c xcar
        by (intro assoc_mult_mat_vec) auto
      also have "\<dots> = U *\<^sub>v (?D *\<^sub>v ((U\<^sup>\<dagger>) *\<^sub>v x))"
        using D_c Udag_c xcar by (intro arg_cong[where f = "(*\<^sub>v) U"] assoc_mult_mat_vec) auto
      finally show ?thesis .
    qed

    have step2: "\<langle>x | U *\<^sub>v (?D *\<^sub>v ?y)\<rangle> = \<langle>(U\<^sup>\<dagger>) *\<^sub>v x | ?D *\<^sub>v ?y\<rangle>"
      using Uc xdim ydim
      using Dlen inner_prod_adjoint_swap by auto


    have qf_eq: "\<langle>x | ?P *\<^sub>v x\<rangle> = \<langle>?y | ?D *\<^sub>v ?y\<rangle>"
      using step1 step2 by simp

    have D_nn_idx: "\<And>i. i < length D \<Longrightarrow> 0 \<le> D ! i"
      using Dnn Dlen by auto
    have "0 \<le> Re \<langle>?y | ?D *\<^sub>v ?y\<rangle>"
      using diag_mat_of_real_quad_Re_nonneg[OF _ D_nn_idx] ydim Dlen by simp
    thus "0 \<le> Re \<langle>x | ?P *\<^sub>v x\<rangle>" using qf_eq by simp
  qed

  show ?thesis
    unfolding psd_def using herm nn P_c by simp
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

subsection \<open>The positive square root\<close>

text \<open>\begin{notesremark}[Day 8]
Given $P\ge 0$ with $U^*PU=\diag(\lambda_1,\dots,\lambda_n)$, $\lambda_i\ge 0$, put
$P^{1/2}=U\diag(\lambda_1^{1/2},\dots,\lambda_n^{1/2})U^*$.  Then $P^{1/2}\ge 0$ and
$(P^{1/2})^2=P$.
\end{notesremark}
\<open>psd_sqrt P\<close> is defined as a choice of such a square root; \<open>psd_sqrt_exists\<close> is the
existence statement and \<open>psd_sqrt_props\<close> the defining properties.\<close>

definition psd_sqrt :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "psd_sqrt P \<equiv> (SOME Q. Q \<in> carrier_mat (dim_row P) (dim_row P) \<and> psd Q \<and> Q * Q = P)"

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
lemma psd_sqrt_props:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "psd_sqrt P \<in> carrier_mat n n"
    and "psd (psd_sqrt P)"
    and "psd_sqrt P * psd_sqrt P = P"
proof -
  have n: "dim_row P = n" using sq by auto
  have "\<exists>Q :: complex Matrix.mat.
          Q \<in> carrier_mat (dim_row P) (dim_row P) \<and> psd Q \<and> Q * Q = P"
    using psd_sqrt_exists[OF sq pos] n by simp
  from someI_ex[OF this]
  show "psd_sqrt P \<in> carrier_mat n n" and "psd (psd_sqrt P)" and "psd_sqrt P * psd_sqrt P = P"
    unfolding psd_sqrt_def using n by auto
qed


text \<open>The corollary of Day 4: $P>0$ iff $P=P^*$ and all eigenvalues are strictly positive.\<close>

lemma pd_iff_pos_eigenvalues:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
  shows "pd P \<longleftrightarrow>
         (hermitian P \<and>
          (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu))"
proof
  assume pd: "pd P"
  have dr: "dim_row P = n" using sq by auto
  have herm: "hermitian P" using pd by (simp add: pd_def)
  have ev: "\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu"
  proof (intro allI impI, elim conjE)
    fix mu :: complex and v :: "complex Matrix.vec"
    assume vnz: "v \<noteq> 0\<^sub>v n" and vd: "dim_vec v = n" and eig: "P *\<^sub>v v = mu \<cdot>\<^sub>v v"
    have pos: "0 < Re \<langle>v | P *\<^sub>v v\<rangle>" using pd vd vnz dr unfolding pd_def by auto
    have vv_re: "0 < Re \<langle>v | v\<rangle>"
    proof -
      have "\<langle>v | v\<rangle> \<noteq> 0" using vnz vd inner_prod_self_eq_zero_iff[of v] by simp
      moreover have "Im \<langle>v | v\<rangle> = 0" by (rule inner_prod_with_itself_Im)
      moreover have "0 \<le> Re \<langle>v | v\<rangle>" by (rule inner_prod_with_itself_Re)
      ultimately show ?thesis by (metis complex_eq_iff less_eq_real_def zero_complex.simps(1) zero_complex.simps(2))
    qed
    have "\<langle>v | P *\<^sub>v v\<rangle> = mu * \<langle>v | v\<rangle>" using eig by (simp add: inner_prod_right_smult')
    hence "Re \<langle>v | P *\<^sub>v v\<rangle> = Re mu * Re \<langle>v | v\<rangle>"
      using inner_prod_with_itself_Im[of v] by simp
    with pos have "0 < Re mu * Re \<langle>v | v\<rangle>" by simp
    thus "0 < Re mu" using vv_re zero_less_mult_pos2 by blast
  qed
  show "hermitian P \<and> (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu)"
    using herm ev by blast
next
  assume rhs: "hermitian P \<and> (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu)"
  have herm: "hermitian P" using rhs by blast
  have ev: "\<And>mu v. v \<noteq> 0\<^sub>v n \<Longrightarrow> dim_vec v = n \<Longrightarrow> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<Longrightarrow> 0 < Re mu"
    using rhs by blast
  have psd: "psd P"
  proof -
    have "\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
            v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 \<le> Re mu"
    proof (intro allI impI, elim conjE)
      fix mu :: complex and v :: "complex Matrix.vec"
      assume "v \<noteq> 0\<^sub>v n" "dim_vec v = n" "P *\<^sub>v v = mu \<cdot>\<^sub>v v"
      from ev[OF this] show "0 \<le> Re mu" by simp
    qed
    thus ?thesis using psd_iff_nonneg_eigenvalues[OF sq] herm by blast
  qed
  let ?Q = "psd_sqrt P"
  have Qc: "?Q \<in> carrier_mat n n" and Qpsd: "psd ?Q" and QQ: "?Q * ?Q = P"
    using psd_sqrt_props[OF sq psd] by auto
  have Qh: "?Q\<^sup>\<dagger> = ?Q" using psd_hermitian[OF Qpsd] by (simp add: hermitian_def)
  have dr: "dim_row P = n" using sq by auto
  show "pd P"
    unfolding pd_def dr
  proof (intro conjI allI impI)
    show "hermitian P" by (rule herm)
    fix x :: "complex Matrix.vec" assume xd: "dim_vec x = n" and xnz: "x \<noteq> 0\<^sub>v n"
    have xc: "x \<in> carrier_vec n" using xd by auto
    have Qx: "dim_vec (?Q *\<^sub>v x) = n" using Qc xd by auto
    have qf: "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle>"
    proof -
      have "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>x | ?Q *\<^sub>v (?Q *\<^sub>v x)\<rangle>"
        using QQ Qc xc by (metis assoc_mult_mat_vec)
      also have "\<dots> = \<langle>?Q\<^sup>\<dagger> *\<^sub>v x | ?Q *\<^sub>v x\<rangle>"
        using inner_prod_adjoint_swap[OF Qc xd Qx] .
      finally show ?thesis using Qh by simp
    qed
    have "?Q *\<^sub>v x \<noteq> 0\<^sub>v n"
    proof
      assume Qx0: "?Q *\<^sub>v x = 0\<^sub>v n"
      have "P *\<^sub>v x = ?Q *\<^sub>v (?Q *\<^sub>v x)" using QQ Qc xc by (metis assoc_mult_mat_vec)
      also have "\<dots> = 0\<^sub>v n" using Qx0 Qc by auto
      also have "\<dots> = (0 :: complex) \<cdot>\<^sub>v x" using xd by auto
      finally have "P *\<^sub>v x = (0 :: complex) \<cdot>\<^sub>v x" .
      from ev[OF xnz xd this] show False by simp
    qed
    hence "\<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle> \<noteq> 0" using Qx inner_prod_self_eq_zero_iff[of "?Q *\<^sub>v x"] by simp
    moreover have "Im \<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle> = 0" by (rule inner_prod_with_itself_Im)
    moreover have "0 \<le> Re \<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle>" by (rule inner_prod_with_itself_Re)
    ultimately show "0 < Re \<langle>x | P *\<^sub>v x\<rangle>"
      using qf by (metis complex_eq_iff less_eq_real_def zero_complex.simps(1) zero_complex.simps(2))
  qed
qed

section \<open>Day 5 (7 September 2011): tests for positivity; direct sums and partitioned matrices\<close>

subsection \<open>Practical tests for positivity\<close>

text \<open>Given $P=P^*$, how does one decide whether $P\ge 0$ or $P>0$?  The notes give two
tests.  (1) $P>0$ iff every leading principal minor
$\det(p_{ij})_{i,j\le k}$, $k=1,\dots,n$, is positive; the same test with $\ge 0$ does
\emph{not} characterise $P\ge 0$.  This criterion (Sylvester's) is stated without proof
in the notes and is not formalised.  (2) Cholesky's algorithm:
\begin{notestheorem}
If $P=(p_{ij})$ is $n\times n$ with $P=P^*$, then $P\ge 0$ if and only if
$P-\bigl(\tfrac{p_{i1}p_{1j}}{p_{11}}\bigr)_{ij}\ge 0$.
\end{notestheorem}
The subtracted matrix agrees with $P$ in the first row and column, so the difference is
really an $(n-1)\times(n-1)$ matrix and the test can be repeated; when $P\ge 0$ the
algorithm also writes $P$ as a sum of rank-one matrices.  The formal theorem adds the
hypothesis $p_{11}>0$, which the notes leave implicit (for $p_{11}=0$ the quotient is
undefined).\<close>



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

subsection \<open>Direct sums of vector spaces and partitioned matrices\<close>

text \<open>\begin{notesdef}
The \emph{direct sum} of vector spaces $V,W$ is $V\oplus W=\{(v,w): v\in V, w\in W\}$ with
componentwise operations and inner product
$\langle(v_1,w_1)|(v_2,w_2)\rangle=\braket{v_1}{v_2}_V+\braket{w_1}{w_2}_W$.
\end{notesdef}
\begin{notesprop}
If $v_1,\dots,v_n$ is a basis of $V$ and $w_1,\dots,w_k$ a basis of $W$, then
$(v_1,0),\dots,(v_n,0),(0,w_1),\dots,(0,w_k)$ is a basis of $V\oplus W$; hence
$\dim(V\oplus W)=\dim V+\dim W$.
\end{notesprop}
Key examples: $\C^{n+k}=\C^n\oplus\C^k$, and a linear map
$T:\C^{n_1+k_1}\to\C^{n_2+k_2}$ has the block form
$T=\begin{pmatrix}T_{11}&T_{12}\\T_{21}&T_{22}\end{pmatrix}$ with
$T\binom{v}{w}=\binom{T_{11}v+T_{12}w}{T_{21}v+T_{22}w}$.
Formally the direct sum of vectors is the concatenation \<open>v \<oplus>\<^sub>v w\<close>, and block
matrices are the library's \<open>four_block_mat\<close>.\<close>

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


corollary direct_sum_dim:
  "dim_vec (v \<oplus>\<^sub>v w) = dim_vec v + dim_vec w"
  by simp


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


section \<open>Day 6 (9 September 2011): tensor products\<close>

text \<open>\begin{notesdef}
$B:X\times Y\to Z$ is \emph{bilinear} if $B(x_1+x_2,y)=B(x_1,y)+B(x_2,y)$,
$B(x,y_1+y_2)=B(x,y_1)+B(x,y_2)$ and $B(\lambda x,y)=B(x,\lambda y)=\lambda B(x,y)$.
\end{notesdef}
The tensor product $X\otimes Y$ is the span of elementary tensors $x\otimes y$ with the
universal property: every bilinear $B$ factors as $B(x,y)=L_B(x\otimes y)$ for a unique
linear $L_B$.  Key relations: $(x_1+x_2)\otimes y=x_1\otimes y+x_2\otimes y$,
$x\otimes(y_1+y_2)=x\otimes y_1+x\otimes y_2$,
$\lambda(x\otimes y)=(\lambda x)\otimes y=x\otimes(\lambda y)$.
\begin{notestheorem}
If $\{e_1,\dots,e_k\}$ and $\{f_1,\dots,f_m\}$ are bases of $X$ and $Y$, then
$\{e_i\otimes f_j\}$ is a basis of $X\otimes Y$; hence $\dim(X\otimes Y)=\dim X\cdot\dim Y$.
\end{notestheorem}
\begin{notesprop}
With bases as above, every $u\in X\otimes Y$ is uniquely $u=\sum_j x_j\otimes f_j$ with
$x_j\in X$, and uniquely $u=\sum_i e_i\otimes y_i$ with $y_i\in Y$; consequently
$X\otimes Y\cong X\oplus\cdots\oplus X$ ($m$ copies).
\end{notesprop}
\begin{notesdef}
The \emph{Schmidt rank} of $u\in X\otimes Y$ is the least number of elementary tensors in an
expression for $u$.
\end{notesdef}
The formalisation uses the concrete model: $\C^n\otimes\C^m=\C^{nm}$ with
$(v\otimes w)_{im+j}=v_iw_j$ (\<open>tensor_vec v w\<close> from the library).  The three key
relations are the bilinearity lemmas below; the product basis theorem is \<open>tensor_onb\<close>
(Day 7); the unique decomposition along a basis of $Y$ is not stated for vectors (its
operator analogue is in theory Quantum\_Computing11).\<close>


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


text \<open>The Schmidt rank, as the minimum length of a representation by elementary
tensors (no properties of it are needed later):\<close>

definition schmidt_rank :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> nat" where
  "schmidt_rank u m \<equiv>
     Min {k. \<exists>vs :: complex Matrix.vec list. \<exists>ws :: complex Matrix.vec list.
              length vs = k \<and> length ws = k \<and>
              (\<forall>i < k. dim_vec (vs ! i) = dim_vec u div m) \<and>
              (\<forall>i < k. dim_vec (ws ! i) = m) \<and>
              u = foldr (\<lambda>(v,w) acc. tensor_vec v w + acc)
                        (zip vs ws) (0\<^sub>v (dim_vec u))}"


section \<open>Day 7 (12 September 2011): tensor products of Hilbert spaces; the postulates\<close>

text \<open>\begin{notesremark}
For Hilbert spaces $\Hil,\Kil$ set
$\langle h_1\otimes k_1|h_2\otimes k_2\rangle=\braket{h_1}{h_2}_{\Hil}\braket{k_1}{k_2}_{\Kil}$.
\end{notesremark}
\begin{notestheorem}
This extends to a sesquilinear form on $\Hil\otimes\Kil$ with $\langle u|u\rangle=0$ only
for $u=0$, hence to an inner product; in finite dimensions $\Hil\otimes\Kil$ with this inner
product is the Hilbert space tensor product (in infinite dimensions one completes).
\end{notestheorem}
\begin{notesprop}
If $\{h_i\}$ and $\{k_j\}$ are orthonormal bases of $\Hil$ and $\Kil$, then
$\{h_i\otimes k_j\}$ is an orthonormal basis of $\Hil\otimes\Kil$.
\end{notesprop}
In physics notation $e_i\otimes e_j=\ket{ij}$, and for $N$ qubits
$e_{i_1}\otimes\cdots\otimes e_{i_N}=\ket{i_1\cdots i_N}$ with the multi-index
$I=(i_1,\dots,i_N)\in\Z_2^N$.  In the concrete model positivity of the form is automatic;
the multiplicativity of the inner product and the orthonormal product basis are proved
below.\<close>

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

subsection \<open>Postulates of quantum mechanics\<close>

text \<open>\begin{notespost}[1]
To each isolated physical system corresponds a Hilbert space, the \emph{state space}; the
state of the system is completely described by a unit vector in it, the \emph{state vector}.
\end{notespost}
\begin{notespost}[2]
The time evolution of a closed system from $t_1$ to $t_2$ is described by a unitary
$U:\Hil\to\Hil$: a system in state $\psi$ at $t_1$ is in state $U\psi$ at $t_2$.
\end{notespost}
\begin{notespost}[3]
Quantum measurements are described by a collection $\{M_m\}$ of \emph{measurement
operators} on $\Hil$.  If the system is in state $\psi$, the probability of observing $m$ is
$p_m(\psi)=\braket{\psi}{M_m^*M_m\psi}=\norm{M_m\psi}^2$; since the probabilities sum to
one, $\sum_m M_m^*M_m=I$.  After observing $m$ the state is $M_m\psi/p_m(\psi)^{1/2}$.
\end{notespost}
Formally a state is \<open>quantum_state n \<psi>\<close> (a unit vector in $\C^n$), evolution is
\<open>evolve U \<psi>\<close>, a measurement system is a list \<open>Ms\<close> with
\<open>measurement_system n Ms\<close> (all $n\times n$ with $\sum_m M_m^\dagger M_m=I$), and
$p_m(\psi)$ is \<open>meas_prob M \<psi>\<close>.\<close>

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


definition measurement_system :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "measurement_system n Ms \<equiv>
     (\<forall>M \<in> set Ms. M \<in> carrier_mat n n) \<and>
     foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n"

definition meas_prob :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> real" where
  "meas_prob M \<psi> \<equiv> \<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2"


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

text \<open>$p_m(\psi)=\braket{\psi}{M_m^*M_m\psi}$, the form in which the notes state Postulate 3.\<close>

lemma meas_prob_quad_form:
  fixes M :: "complex Matrix.mat" and \<psi> :: "complex Matrix.vec"
  assumes M: "M \<in> carrier_mat n n" and \<psi>: "dim_vec \<psi> = n"
  shows "meas_prob M \<psi> = Re \<langle>\<psi> | (M\<^sup>\<dagger> * M) *\<^sub>v \<psi>\<rangle>"
proof -
  have \<psi>c: "\<psi> \<in> carrier_vec n" using \<psi> by auto
  have Md: "M\<^sup>\<dagger> \<in> carrier_mat n n" using M by auto
  have M\<psi>: "dim_vec (M *\<^sub>v \<psi>) = n" using M \<psi> by auto
  have "\<langle>\<psi> | (M\<^sup>\<dagger> * M) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | M\<^sup>\<dagger> *\<^sub>v (M *\<^sub>v \<psi>)\<rangle>"
    using M Md \<psi>c by (simp add: assoc_mult_mat_vec)
  also have "\<dots> = \<langle>(M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>"
    using inner_prod_adjoint_swap[OF Md \<psi> M\<psi>] .
  also have "\<dots> = \<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>" by (simp add: dagger_of_dagger_is_id)
  finally show ?thesis
    unfolding meas_prob_def by (simp add: cpx_vec_length_inner_prod[symmetric])
qed

text \<open>After outcome $m$ the state becomes $M_m\psi/\norm{M_m\psi}$:\<close>

definition post_meas_state :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "post_meas_state M \<psi> \<equiv> (1 / complex_of_real (\<parallel>M *\<^sub>v \<psi>\<parallel>)) \<cdot>\<^sub>v (M *\<^sub>v \<psi>)"

text \<open>\begin{notespost}[4, Day 9]
The state space of a composite system is the tensor product of the state spaces of its
components; if the $i$-th component is in state $\psi_i$, the system is in state
$\psi_1\otimes\cdots\otimes\psi_n$.
\end{notespost}\<close>

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


section \<open>Day 8 (14 September 2011): the quantum game; projective measurements and expected values\<close>

subsection \<open>Distinguishing states\<close>

text \<open>Alice has two states $\psi_1,\psi_2$ known to Bob; she sends one.  Can Bob build a
measurement system that decides with certainty which one he received?  Formally one wants
$M_1,M_2$ with $\norm{M_1\psi_2}=0$, $\norm{M_1\psi_1}^2=1$, $\norm{M_2\psi_1}=0$,
$\norm{M_2\psi_2}^2=1$.

Case I, $\psi_1\perp\psi_2$: take $M_1=\ketbra{\psi_1}{\psi_1}$, $M_2=\ketbra{\psi_2}{\psi_2}$
and $M_3=I-M_1-M_2$; this distinguishes with certainty (formalised below).

Case II, $\psi_1\not\perp\psi_2$: write $\psi_2=\alpha\psi_1+\beta\gamma$ with
$\gamma\perp\psi_1$ a unit vector, so $\alpha\neq 0$; any measurement system with
$\norm{M_1\psi_1}=1$ satisfies $|\alpha|^2\le\norm{M_1\psi_2}^2$, so outcome $1$ also
occurs with probability at least $|\alpha|^2$ when $\psi_2$ is sent (not formalised).

\begin{notestheorem}
Given linearly independent states $\psi_1,\dots,\psi_n$ there is a measurement system
$M_0,\dots,M_n$ such that if outcome $i\ge 1$ occurs then $\psi_i$ was received.
\end{notestheorem}
The notes' proof takes $E_i$ the projection onto $\operatorname{span}\{\psi_j:j\neq i\}^\perp$,
$M_i=E_i/\sqrt n$, and $M_0=(I-\sum_i M_i^*M_i)^{1/2}$; the remark that follows observes
that the inconclusive outcome $0$ then has probability at least $(n-1)/n$.  Formally this is
\<open>lin_indep_states_unambiguous\<close> below.\<close>

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

text \<open>Case I: orthogonal states can be distinguished perfectly.\<close>

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
          by (metis Qcar add.commute carrier_matD(1,2) 
              diff_add_cancel index_add_mat(1) index_minus_mat(1))
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
text \<open>The theorem on linearly independent states.  Linear independence of a list of vectors is
injectivity of the matrix with those columns; the formal statement produces the measurement
system $M_0,\dots,M_k$ in the order $M_1,\dots,M_k,M_0$ (outcome $i<k$ identifies $\psi_i$,
outcome $k$ is inconclusive).  The proof follows the notes with one change: instead of the
projections $E_i$ onto $\{\psi_j:j\neq i\}^\perp$ it uses the dual vectors
$\phi_i$ with $\braket{\phi_i}{\psi_j}=\delta_{ij}$ (columns of $V(V^*V)^{-1}$) and the
operators $M_i=\sqrt c\,\ketbra{e_0}{\phi_i}$, where $c>0$ makes $I-c\sum_i\ketbra{\phi_i}{\phi_i}$
positive; $M_0$ is its square root.\<close>

definition lin_indep_vecs :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> bool" where
  "lin_indep_vecs n vs \<equiv> (\<forall>v \<in> set vs. dim_vec v = n) \<and>
     (\<forall>x :: complex Matrix.vec. x \<in> carrier_vec (length vs) \<longrightarrow>
         mat_of_cols n vs *\<^sub>v x = 0\<^sub>v n \<longrightarrow> x = 0\<^sub>v (length vs))"

lemma outer_prod_carrier:
  fixes v w :: "complex Matrix.vec"
  assumes "dim_vec v = n" and "dim_vec w = m"
  shows "v \<oslash> w \<in> carrier_mat n m"
  using assms by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def carrier_matI)

lemma outer_prod_dagger:
  fixes v w :: "complex Matrix.vec"
  shows "(v \<oslash> w)\<^sup>\<dagger> = w \<oslash> v"
proof -
  have "(v \<oslash> w)\<^sup>\<dagger> = ((bra_vec w)\<^sup>\<dagger>) * (( |v\<rangle> )\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def)
  also have "(bra_vec w)\<^sup>\<dagger> = |w\<rangle>"
  proof -
    have "bra_vec w = ( |w\<rangle> )\<^sup>\<dagger>" by (simp add: dagger_of_ket_is_bra)
    thus ?thesis by (simp add: dagger_of_dagger_is_id)
  qed
  also have "( |v\<rangle> )\<^sup>\<dagger> = bra_vec v" by (simp add: dagger_of_ket_is_bra)
  finally show ?thesis .
qed

lemma foldr_add_mat_carrier:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat n n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n"
  using assms by (induction xs) auto

lemma foldr_add_mat_index:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat n n" and "i < n" and "j < n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) $$ (i, j) = sum_list (map (\<lambda>x. f x $$ (i, j)) xs)"
  using assms
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat n n" and rest: "\<forall>y \<in> set xs. f y \<in> carrier_mat n n" using Cons.prems by auto
  have rc: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n" by (rule foldr_add_mat_carrier[OF rest])
  show ?case using Cons.IH[OF rest] Cons.prems fx rc by simp
qed

lemma foldr_MdagM_shift:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n" and z: "z \<in> carrier_mat n n"
  shows "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms z
           = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) + z"
  using Ms_c
proof (induction Ms)
  case Nil thus ?case using z by auto
next
  case (Cons M Ms)
  have Mc: "M \<in> carrier_mat n n" and rest: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n" using Cons.prems by auto
  have MM: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n" by (rule mult_carrier_mat[OF dagger_carrier[OF Mc] Mc])
  have carr: "\<forall>M \<in> set Ms. (M\<^sup>\<dagger>) * M \<in> carrier_mat n n"
    using rest by (meson mult_carrier_mat dagger_carrier)
  have rc: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) \<in> carrier_mat n n"
    using foldr_add_mat_carrier[OF carr] .
  show ?case using Cons.IH[OF rest] MM rc z by (simp add: assoc_add_mat)
qed

theorem lin_indep_states_unambiguous:
  fixes \<psi>s :: "complex Matrix.vec list"
  assumes qs: "\<forall>\<psi> \<in> set \<psi>s. quantum_state n \<psi>"
      and li: "lin_indep_vecs n \<psi>s"
      and k: "length \<psi>s = k" and kpos: "0 < k"
  shows "\<exists>Ms :: complex Matrix.mat list.
           measurement_system n Ms \<and> length Ms = k + 1 \<and>
           (\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> meas_prob (Ms ! i) (\<psi>s ! j) = 0) \<and>
           (\<forall>i<k. 0 < meas_prob (Ms ! i) (\<psi>s ! i))"
proof -
  have \<psi>d: "\<forall>\<psi> \<in> set \<psi>s. dim_vec \<psi> = n" using qs by (simp add: quantum_state_def)
  have npos: "0 < n"
  proof -
    have "\<psi>s ! 0 \<in> set \<psi>s" using k kpos by simp
    hence "\<parallel>\<psi>s ! 0\<parallel> = 1" "dim_vec (\<psi>s ! 0) = n" using qs by (auto simp: quantum_state_def)
    thus ?thesis by (cases n) (auto simp: cpx_vec_length_def)
  qed
  \<comment> \<open>The Gram matrix of the states is invertible.\<close>
  let ?V = "mat_of_cols n \<psi>s"
  have Vc: "?V \<in> carrier_mat n k" using mat_of_cols_carrier(1)[of n \<psi>s] k by simp
  let ?G = "?V\<^sup>\<dagger> * ?V"
  have Vd_c: "?V\<^sup>\<dagger> \<in> carrier_mat k n" using dagger_carrier[OF Vc] .
  have Gc: "?G \<in> carrier_mat k k" using Vc Vd_c by auto
  have Gh: "?G\<^sup>\<dagger> = ?G" by (simp add: dagger_of_prod dagger_of_dagger_is_id)
  have inj: "\<And>x :: complex Matrix.vec. x \<in> carrier_vec k \<Longrightarrow> ?V *\<^sub>v x = 0\<^sub>v n \<Longrightarrow> x = 0\<^sub>v k"
    using li k unfolding lin_indep_vecs_def by auto
  have dG: "det ?G \<noteq> 0"
  proof
    assume "det ?G = 0"
    then obtain x :: "complex Matrix.vec"
      where xc: "x \<in> carrier_vec k" and xnz: "x \<noteq> 0\<^sub>v k" and Gx: "?G *\<^sub>v x = 0\<^sub>v k"
      using det_0_iff_vec_prod_zero_field[OF Gc] by auto
    have xd: "dim_vec x = k" using xc by auto
    have Vx: "dim_vec (?V *\<^sub>v x) = n" using Vc xd by auto
    have "\<langle>?V *\<^sub>v x | ?V *\<^sub>v x\<rangle> = \<langle>(?V\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | ?V *\<^sub>v x\<rangle>"
      by (simp add: dagger_of_dagger_is_id)
    also have "\<dots> = \<langle>x | ?V\<^sup>\<dagger> *\<^sub>v (?V *\<^sub>v x)\<rangle>"
      using inner_prod_adjoint_swap[OF Vd_c xd Vx] by simp
    also have "\<dots> = \<langle>x | ?G *\<^sub>v x\<rangle>" using Vc Vd_c xc by (simp add: assoc_mult_mat_vec)
    also have "\<dots> = 0" unfolding inner_prod_def using Gx xd by simp
    finally have "?V *\<^sub>v x = 0\<^sub>v n" using Vx inner_prod_self_eq_zero_iff[of "?V *\<^sub>v x"] by simp
    with inj[OF xc] xnz show False by simp
  qed
  obtain B :: "complex Matrix.mat"
    where Bc: "B \<in> carrier_mat k k" and GB: "?G * B = 1\<^sub>m k" and BG: "B * ?G = 1\<^sub>m k"
    using det_non_zero_imp_unit[OF Gc dG, of "()"] by (auto simp: Units_def ring_mat_def)
  \<comment> \<open>The dual vectors: columns of \<open>V B\<close>.\<close>
  let ?P = "?V * B"
  have Pc: "?P \<in> carrier_mat n k" using Vc Bc by auto
  have Pd_c: "?P\<^sup>\<dagger> \<in> carrier_mat k n" using dagger_carrier[OF Pc] .
  let ?\<phi>s = "cols ?P"
  have \<phi>len: "length ?\<phi>s = k" using Pc Bc by simp
  have \<phi>d: "\<forall>\<phi> \<in> set ?\<phi>s. dim_vec \<phi> = n" using Pc by (auto simp: cols_def)
  have P_eq: "mat_of_cols n ?\<phi>s = ?P" using Pc mat_of_cols_cols[of ?P] by auto
  have Bd_G: "B\<^sup>\<dagger> * ?G = 1\<^sub>m k"
  proof -
    have "B\<^sup>\<dagger> * ?G = (B\<^sup>\<dagger>) * (?G\<^sup>\<dagger>)" using Gh by simp
    also have "\<dots> = (?G * B)\<^sup>\<dagger>" using dagger_of_prod[of ?G B] Gc Bc by auto
    also have "\<dots> = (1\<^sub>m k :: complex Matrix.mat)\<^sup>\<dagger>" using GB by simp
    also have "\<dots> = 1\<^sub>m k" by (rule eq_matI) (auto simp: dagger_def)
    finally show ?thesis .
  qed
  have dual: "\<And>i j. i < k \<Longrightarrow> j < k \<Longrightarrow> \<langle>?\<phi>s ! i | \<psi>s ! j\<rangle> = (if i = j then 1 else 0)"
  proof -
    fix i j assume i: "i < k" and j: "j < k"
    have \<psi>j: "\<psi>s ! j \<in> set \<psi>s" using j k by simp
    have \<psi>jd: "dim_vec (\<psi>s ! j) = n" using \<psi>d \<psi>j by simp
    have "\<langle>?\<phi>s ! i | \<psi>s ! j\<rangle> = (((mat_of_cols n ?\<phi>s)\<^sup>\<dagger>) *\<^sub>v (\<psi>s ! j)) $ i"
      using mat_of_cols_dagger_mult_vec_index[OF \<psi>jd \<phi>d, of i] \<phi>len i by simp
    also have "\<dots> = ((?P\<^sup>\<dagger>) *\<^sub>v Matrix.col ?V j) $ i"
      using P_eq col_mat_of_cols[of j \<psi>s n] j k \<psi>jd by auto
    also have "(?P\<^sup>\<dagger>) *\<^sub>v Matrix.col ?V j = Matrix.col ((?P\<^sup>\<dagger>) * ?V) j"
      using col_mult2[OF Pd_c Vc j] by simp
    also have "Matrix.col ((?P\<^sup>\<dagger>) * ?V) j $ i = ((?P\<^sup>\<dagger>) * ?V) $$ (i, j)"
    proof -
      have PV_c: "(?P\<^sup>\<dagger>) * ?V \<in> carrier_mat k k" using Pd_c Vc by auto
      thus ?thesis using i j carrier_matD[OF PV_c] by (simp add: Matrix.col_def)
    qed
    also have "(?P\<^sup>\<dagger>) * ?V = B\<^sup>\<dagger> * ?G"
    proof -
      have "?P\<^sup>\<dagger> = (B\<^sup>\<dagger>) * (?V\<^sup>\<dagger>)" using dagger_of_prod[of ?V B] Vc Bc by auto
      hence "(?P\<^sup>\<dagger>) * ?V = ((B\<^sup>\<dagger>) * (?V\<^sup>\<dagger>)) * ?V" by simp
      also have "\<dots> = (B\<^sup>\<dagger>) * ((?V\<^sup>\<dagger>) * ?V)"
        using assoc_mult_mat[OF dagger_carrier[OF Bc] Vd_c Vc] .
      finally show ?thesis .
    qed
    also have "\<dots> = 1\<^sub>m k" by (rule Bd_G)
    finally show "\<langle>?\<phi>s ! i | \<psi>s ! j\<rangle> = (if i = j then 1 else 0)" using i j by simp
  qed
  \<comment> \<open>Scale so that \<open>I - c T\<close> is positive, with \<open>T = \<Sum> |\<phi>\<^sub>i\<rangle>\<langle>\<phi>\<^sub>i|\<close>.\<close>
  let ?T = "outer_sum n ?\<phi>s"
  have Tc: "?T \<in> carrier_mat n n" by (intro carrier_matI) auto
  have Tpsd: "psd ?T" using outer_sum_psd[OF \<phi>len \<phi>d] .
  obtain U :: "complex Matrix.mat" and D :: "real list"
    where Uc: "U \<in> carrier_mat n n" and UU: "unitary U" and Dlen: "length D = n"
      and Dnn: "\<forall>i<n. 0 \<le> D ! i" and TUDU: "?T = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF Tc Tpsd] by blast
  define Dmax where "Dmax = sum_list (map abs D)"
  define c where "c = 1 / (1 + Dmax)"
  have Dmax0: "0 \<le> Dmax" unfolding Dmax_def by (rule sum_list_nonneg) auto
  have cpos: "0 < c" unfolding c_def using Dmax0 by simp
  have cD1: "\<And>i. i < n \<Longrightarrow> c * D ! i \<le> 1"
  proof -
    fix i assume i: "i < n"
    have "\<bar>D ! i\<bar> \<in> set (map abs D)" using i Dlen by auto
    hence "\<bar>D ! i\<bar> \<le> Dmax" unfolding Dmax_def by (intro member_le_sum_list) auto
    hence "D ! i \<le> Dmax" by linarith
    hence "c * D ! i \<le> c * Dmax" using cpos by (simp add: mult_left_mono)
    also have "\<dots> = Dmax / (1 + Dmax)" unfolding c_def by simp
    also have "\<dots> \<le> 1" using Dmax0 by (simp add: divide_le_eq)
    finally show "c * D ! i \<le> 1" .
  qed
  define D' where "D' = map (\<lambda>d. 1 - c * d) D"
  have D'len: "length D' = n" using Dlen by (simp add: D'_def)
  have D'nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D' ! i" using cD1 Dlen by (simp add: D'_def)
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] Dlen by metis
  have diagD': "diag_mat_of_real D' = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D"
  proof (rule eq_matI)
    show "dim_row (diag_mat_of_real D') = dim_row (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)"
      using D'len Dlen by simp
    show "dim_col (diag_mat_of_real D') = dim_col (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)"
      using D'len Dlen by simp
    fix i j assume "i < dim_row (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)"
                   "j < dim_col (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)"
    hence ij: "i < n" "j < n" using Dlen by auto
    show "diag_mat_of_real D' $$ (i, j) = (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) $$ (i, j)"
      using ij Dlen D'len by (cases "i = j") (auto simp: D'_def)
  qed
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using unitary_left_right(2)[OF UU] Uc by auto
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by (simp add: dagger_def)
  have ImcT: "1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T = U * diag_mat_of_real D' * (U\<^sup>\<dagger>)"
  proof -
    have one_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
    have cDc: "complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D \<in> carrier_mat n n" using Dc by auto
    have U1c: "U * 1\<^sub>m n \<in> carrier_mat n n" using Uc by auto
    have UcDc: "U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) \<in> carrier_mat n n" using Uc cDc by auto
    have UDc: "U * diag_mat_of_real D \<in> carrier_mat n n" using Uc Dc by auto
    have "U * diag_mat_of_real D' * (U\<^sup>\<dagger>)
            = U * (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>)"
      by (simp only: diagD')
    also have "\<dots> = (U * 1\<^sub>m n - U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)) * (U\<^sup>\<dagger>)"
      by (simp only: mult_minus_distrib_mat[OF Uc one_c cDc])
    also have "\<dots> = U * 1\<^sub>m n * (U\<^sup>\<dagger>) - U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>)"
      by (simp only: minus_mult_distrib_mat[OF U1c UcDc Ud_c])
    also have "U * 1\<^sub>m n * (U\<^sup>\<dagger>) = 1\<^sub>m n" using Uc UUd by simp
    also have "U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>) = complex_of_real c \<cdot>\<^sub>m ?T"
    proof -
      have "U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) = complex_of_real c \<cdot>\<^sub>m (U * diag_mat_of_real D)"
        by (rule mult_smult_distrib[OF Uc Dc])
      hence "U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>)
               = (complex_of_real c \<cdot>\<^sub>m (U * diag_mat_of_real D)) * (U\<^sup>\<dagger>)" by simp
      also have "\<dots> = complex_of_real c \<cdot>\<^sub>m (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
        by (rule mult_smult_assoc_mat[OF UDc Ud_c])
      finally show ?thesis using TUDU by simp
    qed
    finally show ?thesis by simp
  qed

  have ImcT_c: "1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T \<in> carrier_mat n n" using Tc by auto
  have ImcT_psd: "psd (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
    unfolding ImcT using psd_U_diag_Udag[OF Uc D'len] D'nn by blast
  let ?Q = "psd_sqrt (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
  have Qc: "?Q \<in> carrier_mat n n" and Qpsd: "psd ?Q" and QQ: "?Q * ?Q = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T"
    using psd_sqrt_props[OF ImcT_c ImcT_psd] by auto
  have Qh: "?Q\<^sup>\<dagger> = ?Q" using psd_hermitian[OF Qpsd] by (simp add: hermitian_def)
  \<comment> \<open>The measurement operators \<open>M\<^sub>i = \<surd>c |e\<^sub>0\<rangle>\<langle>\<phi>\<^sub>i|\<close> and \<open>M\<^sub>k = Q\<close>.\<close>
  let ?u = "unit_vec n 0"
  have ud: "dim_vec ?u = n" by simp
  have un: "\<parallel>?u\<parallel> = 1" using npos by simp
  have uu: "\<langle>?u | ?u\<rangle> = 1"
  proof -
    have "\<langle>?u | ?u\<rangle> = complex_of_real (\<parallel>?u\<parallel>\<^sup>2)" by (simp only: cpx_vec_length_inner_prod[symmetric])
    thus ?thesis using un by simp
  qed
  define Mi where "Mi = (\<lambda>\<phi> :: complex Matrix.vec. complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>))"
  define Ms where "Ms = map Mi ?\<phi>s @ [?Q]"
  have lenMs: "length Ms = k + 1" by (simp add: Ms_def \<phi>len carrier_matD[OF Bc])
  have Ms_nth: "\<And>i. i < k \<Longrightarrow> Ms ! i = Mi (?\<phi>s ! i)" by (simp add: Ms_def \<phi>len nth_append carrier_matD[OF Bc])
  have Mi_c: "\<And>\<phi>. dim_vec \<phi> = n \<Longrightarrow> Mi \<phi> \<in> carrier_mat n n"
    using outer_prod_carrier[OF ud] by (auto simp: Mi_def)
  have sqc: "sqrt c * sqrt c = c" using cpos by simp
  have MiMi: "\<And>\<phi>. dim_vec \<phi> = n \<Longrightarrow> (Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> = complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)"
  proof -
    fix \<phi> :: "complex Matrix.vec" assume \<phi>: "dim_vec \<phi> = n"
    have c1: "?u \<oslash> \<phi> \<in> carrier_mat n n" using outer_prod_carrier[OF ud \<phi>] .
    have c2: "\<phi> \<oslash> ?u \<in> carrier_mat n n" using outer_prod_carrier[OF \<phi> ud] .
    have dag: "(Mi \<phi>)\<^sup>\<dagger> = complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> ?u)"
      unfolding Mi_def by (simp add: dagger_of_smult outer_prod_dagger)
    have prod: "(\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>) = \<phi> \<oslash> \<phi>"
    proof (rule eq_matI)
      show "dim_row ((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>)) = dim_row (\<phi> \<oslash> \<phi>)"
        using c1 c2 outer_prod_carrier[OF \<phi> \<phi>] by auto
      show "dim_col ((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>)) = dim_col (\<phi> \<oslash> \<phi>)"
        using c1 c2 outer_prod_carrier[OF \<phi> \<phi>] by auto
      fix i j assume "i < dim_row (\<phi> \<oslash> \<phi>)" "j < dim_col (\<phi> \<oslash> \<phi>)"
      hence ij: "i < n" "j < n" using outer_prod_carrier[OF \<phi> \<phi>] by auto
      have dA: "dim_row (\<phi> \<oslash> ?u) = n" "dim_col (\<phi> \<oslash> ?u) = n" using c2 by auto
      have dB: "dim_row (?u \<oslash> \<phi>) = n" "dim_col (?u \<oslash> \<phi>) = n" using c1 by auto
      have "((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>)) $$ (i, j) = Matrix.row (\<phi> \<oslash> ?u) i \<bullet> Matrix.col (?u \<oslash> \<phi>) j"
        using ij by (simp only: index_mult_mat(1) dA dB)
      also have "\<dots> = (\<Sum>l = 0..<n. Matrix.row (\<phi> \<oslash> ?u) i $ l * Matrix.col (?u \<oslash> \<phi>) j $ l)"
        by (simp only: scalar_prod_def dim_col dB)
      also have "\<dots> = (\<Sum>l = 0..<n. (\<phi> $ i * cnj (?u $ l)) * (?u $ l * cnj (\<phi> $ j)))"
      proof (rule sum.cong[OF refl])
        fix l assume "l \<in> {0..<n}"
        hence l: "l < n" by simp
        have r: "Matrix.row (\<phi> \<oslash> ?u) i $ l = (\<phi> \<oslash> ?u) $$ (i, l)"
          using ij l by (simp only: index_row(1) dA)
        have cc: "Matrix.col (?u \<oslash> \<phi>) j $ l = (?u \<oslash> \<phi>) $$ (l, j)"
          using ij l by (simp only: index_col dB)
        have o1: "(\<phi> \<oslash> ?u) $$ (i, l) = \<phi> $ i * cnj (?u $ l)"
          by (rule outer_prod_index) (simp only: \<phi> ij, simp only: ud l)
        have o2: "(?u \<oslash> \<phi>) $$ (l, j) = ?u $ l * cnj (\<phi> $ j)"
          by (rule outer_prod_index) (simp only: ud l, simp only: \<phi> ij)
        show "Matrix.row (\<phi> \<oslash> ?u) i $ l * Matrix.col (?u \<oslash> \<phi>) j $ l
                = (\<phi> $ i * cnj (?u $ l)) * (?u $ l * cnj (\<phi> $ j))"
          by (simp only: r cc o1 o2)
      qed
      also have "\<dots> = \<phi> $ i * cnj (\<phi> $ j) * (\<Sum>l = 0..<n. cnj (?u $ l) * ?u $ l)"
        by (simp add: sum_distrib_left algebra_simps)
      also have "(\<Sum>l = 0..<n. cnj (?u $ l) * ?u $ l) = (\<Sum>l = 0..<n. if l = 0 then 1 else 0)"
        by (rule sum.cong[OF refl]) simp
      also have "\<dots> = 1" using npos by simp
      also have "\<phi> $ i * cnj (\<phi> $ j) * 1 = (\<phi> \<oslash> \<phi>) $$ (i, j)"
        using outer_prod_index[of i \<phi> j \<phi>] ij \<phi> by simp
      finally show "((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>)) $$ (i, j) = (\<phi> \<oslash> \<phi>) $$ (i, j)" .
    qed
    have sc: "complex_of_real (sqrt c) * complex_of_real (sqrt c) = complex_of_real c"
      using sqc cpos by (simp flip: of_real_mult)
    have smm: "\<And>a b (A :: complex Matrix.mat). a \<cdot>\<^sub>m (b \<cdot>\<^sub>m A) = (a * b) \<cdot>\<^sub>m A"
      by (rule eq_matI) (simp_all add: mult.assoc)
    have "(Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> = (complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> ?u)) * Mi \<phi>"
      by (simp only: dag)
    also have "\<dots> = (complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> ?u)) * (complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>))"
      by (simp only: Mi_def)
    also have "\<dots> = complex_of_real (sqrt c) \<cdot>\<^sub>m ((\<phi> \<oslash> ?u) * (complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>)))"
      by (rule mult_smult_assoc_mat[OF c2 smult_carrier_mat[OF c1]])
    also have "(\<phi> \<oslash> ?u) * (complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>))
                 = complex_of_real (sqrt c) \<cdot>\<^sub>m ((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>))"
      by (rule mult_smult_distrib[OF c2 c1])
    also have "\<dots> = complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)" by (simp only: prod)
    also have "complex_of_real (sqrt c) \<cdot>\<^sub>m (complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>))
                 = (complex_of_real (sqrt c) * complex_of_real (sqrt c)) \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)"
      by (rule smm)
    also have "\<dots> = complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)" by (simp only: sc)
    finally show "(Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> = complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)" .
  qed
  have Mi_prob: "\<And>\<phi> \<psi>. dim_vec \<phi> = n \<Longrightarrow> dim_vec \<psi> = n \<Longrightarrow>
                   meas_prob (Mi \<phi>) \<psi> = c * (cmod \<langle>\<phi> | \<psi>\<rangle>)\<^sup>2"
  proof -
    fix \<phi> \<psi> :: "complex Matrix.vec" assume \<phi>: "dim_vec \<phi> = n" and \<psi>: "dim_vec \<psi> = n"
    have c1: "?u \<oslash> \<phi> \<in> carrier_mat n n" using outer_prod_carrier[OF ud \<phi>] .
    have "Mi \<phi> *\<^sub>v \<psi> = complex_of_real (sqrt c) \<cdot>\<^sub>v ((?u \<oslash> \<phi>) *\<^sub>v \<psi>)"
      unfolding Mi_def using smult_mat_mult_vec[OF c1] \<psi> by auto
    also have "(?u \<oslash> \<phi>) *\<^sub>v \<psi> = \<langle>\<phi> | \<psi>\<rangle> \<cdot>\<^sub>v ?u"
      using outer_prod_mult_vec[of \<psi> \<phi> ?u] \<phi> \<psi> by simp
    finally have "\<parallel>Mi \<phi> *\<^sub>v \<psi>\<parallel> = sqrt c * (cmod \<langle>\<phi> | \<psi>\<rangle> * 1)"
      using cpos un by (simp add: cpx_vec_length_smult)
    thus "meas_prob (Mi \<phi>) \<psi> = c * (cmod \<langle>\<phi> | \<psi>\<rangle>)\<^sup>2"
      unfolding meas_prob_def using sqc by (simp add: power_mult_distrib power2_eq_square)
  qed
  \<comment> \<open>The operators form a measurement system.\<close>
  have Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    using Mi_c \<phi>d Qc by (auto simp: Ms_def)
  have fold_map: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) = complex_of_real c \<cdot>\<^sub>m ?T"
  proof (rule eq_matI)
    have carr: "\<forall>\<phi> \<in> set ?\<phi>s. (Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> \<in> carrier_mat n n"
      using Mi_c \<phi>d by (meson mult_carrier_mat dagger_carrier)
    have fold_c: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) \<in> carrier_mat n n"
      using foldr_add_mat_carrier[OF carr] by (simp add: foldr_map o_def)
    show "dim_row (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n)) = dim_row (complex_of_real c \<cdot>\<^sub>m ?T)"
      using fold_c Tc by auto
    show "dim_col (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n)) = dim_col (complex_of_real c \<cdot>\<^sub>m ?T)"
      using fold_c Tc by auto
    fix i j assume "i < dim_row (complex_of_real c \<cdot>\<^sub>m ?T)" "j < dim_col (complex_of_real c \<cdot>\<^sub>m ?T)"
    hence ij: "i < n" "j < n" using Tc by auto
    have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) $$ (i, j)
            = foldr (\<lambda>\<phi> acc. (Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> + acc) ?\<phi>s (0\<^sub>m n n) $$ (i, j)"
      by (simp add: foldr_map o_def)
    also have "\<dots> = sum_list (map (\<lambda>\<phi>. ((Mi \<phi>)\<^sup>\<dagger> * Mi \<phi>) $$ (i, j)) ?\<phi>s)"
      using foldr_add_mat_index[OF carr ij] .
    also have "\<dots> = sum_list (map (\<lambda>\<phi>. complex_of_real c * (\<phi> $ i * cnj (\<phi> $ j))) ?\<phi>s)"
    proof (intro arg_cong[where f = sum_list] map_cong refl)
      fix \<phi> assume "\<phi> \<in> set ?\<phi>s"
      hence d: "dim_vec \<phi> = n" using \<phi>d by blast
      have cc: "\<phi> \<oslash> \<phi> \<in> carrier_mat n n" using outer_prod_carrier[OF d d] .
      have "((Mi \<phi>)\<^sup>\<dagger> * Mi \<phi>) $$ (i, j) = (complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) $$ (i, j)"
        by (simp only: MiMi[OF d])
      also have "\<dots> = complex_of_real c * (\<phi> \<oslash> \<phi>) $$ (i, j)"
        by (rule index_smult_mat(1)) (simp_all only: carrier_matD[OF cc] ij)
      also have "(\<phi> \<oslash> \<phi>) $$ (i, j) = \<phi> $ i * cnj (\<phi> $ j)"
        using outer_prod_index[of i \<phi> j \<phi>] ij d by simp
      finally show "((Mi \<phi>)\<^sup>\<dagger> * Mi \<phi>) $$ (i, j) = complex_of_real c * (\<phi> $ i * cnj (\<phi> $ j))" .
    qed
    also have "\<dots> = complex_of_real c * sum_list (map (\<lambda>\<phi>. \<phi> $ i * cnj (\<phi> $ j)) ?\<phi>s)"
      by (simp add: sum_list_const_mult)
    also have "\<dots> = complex_of_real c * ?T $$ (i, j)"
      using outer_sum_entry_sum_list[OF \<phi>d ij] by simp
    finally show "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) $$ (i, j)
                    = (complex_of_real c \<cdot>\<^sub>m ?T) $$ (i, j)"
      using ij Tc by simp
  qed
  have ms: "measurement_system n Ms"
  proof -
    have QdQ: "(?Q\<^sup>\<dagger>) * ?Q + 0\<^sub>m n n = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T"
      using Qh QQ ImcT_c by simp
    have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)
            = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s)
                (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) [?Q] (0\<^sub>m n n))"
      unfolding Ms_def by (rule foldr_append)
    also have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) [?Q] (0\<^sub>m n n) = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T"
      by (simp only: foldr.simps o_apply id_apply QdQ)
    also have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)
                 = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n)
                     + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
      using Mi_c \<phi>d ImcT_c by (intro foldr_MdagM_shift) auto
    also have "\<dots> = complex_of_real c \<cdot>\<^sub>m ?T + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
      using fold_map by simp
    also have "\<dots> = 1\<^sub>m n"
    proof (rule eq_matI)
      show "dim_row (complex_of_real c \<cdot>\<^sub>m ?T + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)) = dim_row (1\<^sub>m n :: complex Matrix.mat)" using Tc by auto
      show "dim_col (complex_of_real c \<cdot>\<^sub>m ?T + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)) = dim_col (1\<^sub>m n :: complex Matrix.mat)" using Tc by auto
      fix i j assume "i < dim_row (1\<^sub>m n :: complex Matrix.mat)" "j < dim_col (1\<^sub>m n :: complex Matrix.mat)"
      thus "(complex_of_real c \<cdot>\<^sub>m ?T + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)) $$ (i, j) = (1\<^sub>m n :: complex Matrix.mat) $$ (i, j)"
        using Tc by (simp add: algebra_simps)
    qed
    finally show ?thesis unfolding measurement_system_def using Ms_c by blast
  qed
  \<comment> \<open>Outcome \<open>i < k\<close> occurs only for \<open>\<psi>\<^sub>i\<close>, and then with positive probability.\<close>
  have off: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> meas_prob (Ms ! i) (\<psi>s ! j) = 0"
  proof (intro allI impI)
    fix i j assume i: "i < k" and j: "j < k" and ij: "i \<noteq> j"
    have \<phi>i: "dim_vec (?\<phi>s ! i) = n" using \<phi>d \<phi>len i by (simp add: carrier_matD[OF Bc] carrier_matD[OF Pc])
    have \<psi>j: "dim_vec (\<psi>s ! j) = n" using \<psi>d k j by simp
    show "meas_prob (Ms ! i) (\<psi>s ! j) = 0"
      using Ms_nth[OF i] Mi_prob[OF \<phi>i \<psi>j] dual[OF i j] ij by simp
  qed
  have diag: "\<forall>i<k. 0 < meas_prob (Ms ! i) (\<psi>s ! i)"
  proof (intro allI impI)
    fix i assume i: "i < k"
    have \<phi>i: "dim_vec (?\<phi>s ! i) = n" using \<phi>d \<phi>len i by (simp add: carrier_matD[OF Bc] carrier_matD[OF Pc])
    have \<psi>i: "dim_vec (\<psi>s ! i) = n" using \<psi>d k i by simp
    show "0 < meas_prob (Ms ! i) (\<psi>s ! i)"
      using Ms_nth[OF i] Mi_prob[OF \<phi>i \<psi>i] dual[OF i i] cpos by simp
  qed
  show ?thesis using ms lenMs off diag by blast
qed

subsection \<open>Projective measurements, expected values and self-adjoint operators\<close>

text \<open>If a measurement $\{M_m\}$ has real outcomes $\lambda_m$, the expected value of the
outcome in state $\psi$ is
$E=\sum_m p_m(\psi)\lambda_m=\bigl\langle\psi\big|\bigl(\textstyle\sum_m\lambda_mM_m^*M_m\bigr)\psi\bigr\rangle
=\braket{\psi}{H\psi}$ with $H=\sum_m\lambda_mM_m^*M_m$ self-adjoint: expected values of
observables are quadratic forms of Hermitian matrices (\<open>expected_value_eq_quad_form\<close> below).\<close>

text \<open>Formally: a measurement whose operator is the rank-one projection $\ketbra\gamma\gamma$
has $p(\psi)=|\braket\gamma\psi|^2$ (the proposition of Day 12); an \emph{observable} with
outcomes $\lambda_m$ attached to the measurement operators $M_m$ is
$H=\sum_m\lambda_mM_m^*M_m$, which is Hermitian, and the expected outcome
$\sum_m\lambda_mp_m(\psi)$ equals $\braket{\psi}{H\psi}$.\<close>

lemma rank_one_meas_prob:
  fixes \<gamma> \<psi> :: "complex Matrix.vec"
  assumes g: "quantum_state n \<gamma>" and \<psi>: "dim_vec \<psi> = n"
  shows "meas_prob (\<gamma> \<oslash> \<gamma>) \<psi> = (cmod \<langle>\<gamma> | \<psi>\<rangle>)\<^sup>2"
proof -
  have gd: "dim_vec \<gamma> = n" and gn: "\<parallel>\<gamma>\<parallel> = 1" using g by (auto simp: quantum_state_def)
  have "(\<gamma> \<oslash> \<gamma>) *\<^sub>v \<psi> = \<langle>\<gamma> | \<psi>\<rangle> \<cdot>\<^sub>v \<gamma>"
    using outer_prod_mult_vec[of \<psi> \<gamma> \<gamma>] gd \<psi> by simp
  hence "\<parallel>(\<gamma> \<oslash> \<gamma>) *\<^sub>v \<psi>\<parallel> = cmod \<langle>\<gamma> | \<psi>\<rangle> * \<parallel>\<gamma>\<parallel>"
    by (simp add: cpx_vec_length_smult)
  thus ?thesis unfolding meas_prob_def using gn by (simp add: power_mult_distrib)
qed

definition observable :: "nat \<Rightarrow> (real \<times> complex Matrix.mat) list \<Rightarrow> complex Matrix.mat" where
  "observable n lMs \<equiv>
     foldr (\<lambda>(l, M) acc. complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M) + acc) lMs (0\<^sub>m n n)"

definition expected_value :: "(real \<times> complex Matrix.mat) list \<Rightarrow> complex Matrix.vec \<Rightarrow> real" where
  "expected_value lMs \<psi> \<equiv> (\<Sum>(l, M) \<leftarrow> lMs. l * meas_prob M \<psi>)"

lemma observable_Nil [simp]: "observable n [] = 0\<^sub>m n n"
  by (simp add: observable_def)

lemma observable_Cons [simp]:
  "observable n ((l, M) # lMs) = complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M) + observable n lMs"
  by (simp add: observable_def)

lemma observable_carrier:
  assumes "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n"
  shows "observable n lMs \<in> carrier_mat n n"
  using assms by (induction lMs) auto

lemma observable_hermitian:
  assumes "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n"
  shows "hermitian (observable n lMs)"
  using assms
proof (induction lMs)
  case Nil
  show ?case unfolding hermitian_def by (rule eq_matI) (auto simp: dagger_def)
next
  case (Cons lM lMs)
  obtain l M where lM: "lM = (l, M)" by (cases lM)
  have Mc: "M \<in> carrier_mat n n" using Cons.prems lM by auto
  have rest: "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n" using Cons.prems by auto
  have h1: "hermitian (complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M))"
    using psd_hermitian[OF psd_MdagM[OF Mc]] Mc
    by (intro hermitian_real_scale) auto
  have h2: "hermitian (observable n lMs)" using Cons.IH[OF rest] .
  have c1: "complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M) \<in> carrier_mat n n" using Mc by auto
  show ?case unfolding lM observable_Cons
    by (rule hermitian_plus[OF h1 h2 c1 observable_carrier[OF rest]])
qed

lemma expected_value_eq_quad_form:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>: "dim_vec \<psi> = n"
      and lMs: "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n"
  shows "expected_value lMs \<psi> = Re \<langle>\<psi> | observable n lMs *\<^sub>v \<psi>\<rangle>"
  using lMs
proof (induction lMs)
  case Nil
  have "observable n [] *\<^sub>v \<psi> = 0\<^sub>v n" using \<psi> by auto
  moreover have "\<langle>\<psi> | 0\<^sub>v n\<rangle> = 0"
  proof -
    have "(0\<^sub>v n :: complex Matrix.vec) = (0 :: complex) \<cdot>\<^sub>v \<psi>" using \<psi> by auto
    thus ?thesis by (simp only: inner_prod_right_smult') simp
  qed
  ultimately show ?case by (simp add: expected_value_def)
next
  case (Cons lM lMs)
  obtain l M where lM: "lM = (l, M)" by (cases lM)
  have Mc: "M \<in> carrier_mat n n" using Cons.prems lM by auto
  have rest: "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n" using Cons.prems by auto
  have \<psi>c: "\<psi> \<in> carrier_vec n" using \<psi> by auto
  have MM: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n" using Mc by auto
  have obs: "observable n lMs \<in> carrier_mat n n" by (rule observable_carrier[OF rest])
  have c1: "complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M) \<in> carrier_mat n n" using MM by auto
  have "observable n (lM # lMs) *\<^sub>v \<psi>
          = (complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M)) *\<^sub>v \<psi> + observable n lMs *\<^sub>v \<psi>"
    unfolding lM observable_Cons by (rule add_mult_distrib_mat_vec[OF c1 obs \<psi>c])
  also have "(complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M)) *\<^sub>v \<psi>
               = complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>)"
    using smult_mat_mult_vec[OF MM \<psi>c] .
  finally have obs_eq: "observable n (lM # lMs) *\<^sub>v \<psi>
      = complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>) + observable n lMs *\<^sub>v \<psi>" .
  have d1: "dim_vec (complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>)) = dim_vec (observable n lMs *\<^sub>v \<psi>)"
    using Mc MM obs \<psi> by simp
  have "\<langle>\<psi> | observable n (lM # lMs) *\<^sub>v \<psi>\<rangle>
      = \<langle>\<psi> | complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>)\<rangle> + \<langle>\<psi> | observable n lMs *\<^sub>v \<psi>\<rangle>"
    unfolding obs_eq by (rule inner_prod_right_add'[OF d1])
  also have "\<langle>\<psi> | complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>)\<rangle>
      = complex_of_real l * \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>"
    by (rule inner_prod_right_smult')
  finally have split: "\<langle>\<psi> | observable n (lM # lMs) *\<^sub>v \<psi>\<rangle>
      = complex_of_real l * \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle> + \<langle>\<psi> | observable n lMs *\<^sub>v \<psi>\<rangle>" .
  have "expected_value (lM # lMs) \<psi> = l * meas_prob M \<psi> + expected_value lMs \<psi>"
    unfolding lM expected_value_def by simp
  also have "\<dots> = l * Re \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle> + Re \<langle>\<psi> | observable n lMs *\<^sub>v \<psi>\<rangle>"
    using meas_prob_quad_form[OF Mc \<psi>] Cons.IH[OF rest] by simp
  also have "\<dots> = Re \<langle>\<psi> | observable n (lM # lMs) *\<^sub>v \<psi>\<rangle>"
    using split by simp
  finally show ?case .
qed

section \<open>Day 9 (16 September 2011): positive operator-valued measures; composite systems; entanglement\<close>

subsection \<open>Positive operator-valued measures\<close>

text \<open>If two measurement systems satisfy $M_m^*M_m=\tilde M_m^*\tilde M_m$ for all $m$ then
$p_m=\tilde p_m$: only the operators $M_m^*M_m$ matter, and $\sum_mM_m^*M_m=I$.  Conversely
if $P_m\ge 0$ with $\sum_mP_m=I$ then $M_m=P_m^{1/2}$ is a measurement system.
\begin{notesdef}
A \emph{positive operator-valued measure} (POVM) is a set $\{P_m\}$ of positive operators with
$\sum_mP_m=I$.
\end{notesdef}\<close>

definition povm :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "povm n Ps \<equiv>
     (\<forall>P \<in> set Ps. P \<in> carrier_mat n n \<and> psd P) \<and>
     foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n) = 1\<^sub>m n"


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


lemma psd_sqrt_measurement_factor:
  assumes Pcar: "P \<in> carrier_mat n n"
      and Ppsd: "psd P"
  shows "\<exists>M. M \<in> carrier_mat n n \<and> M\<^sup>\<dagger> * M = P"
proof -
  obtain Q where Qcar: "Q \<in> carrier_mat n n"
    and Qpsd: "psd Q"
    and QQ: "Q * Q = P"
    using psd_sqrt_exists[OF Pcar Ppsd] by blast
  have Qdag: "Q\<^sup>\<dagger> = Q"
    using psd_hermitian[OF Qpsd]
    unfolding hermitian_def by simp
  have "Q\<^sup>\<dagger> * Q = P"
    using Qdag QQ by simp
  thus ?thesis
    using Qcar by blast
qed

lemma psd_sqrt_measurement_factors:
  assumes Ps: "\<forall>P \<in> set Ps. P \<in> carrier_mat n n \<and> psd P"
  shows "\<exists>Ms. (\<forall>M \<in> set Ms. M \<in> carrier_mat n n) \<and>
               map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
  using Ps
proof (induction Ps)
  case Nil
  show ?case by simp
next
  case (Cons P Ps)
  have Pcar: "P \<in> carrier_mat n n"
    using Cons.prems by simp
  have Ppsd: "psd P"
    using Cons.prems by simp
  obtain M where Mcar: "M \<in> carrier_mat n n"
    and M_factor: "M\<^sup>\<dagger> * M = P"
    using psd_sqrt_measurement_factor[OF Pcar Ppsd] by blast
  obtain Ms where Mscar: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    and Ms_factor: "map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
    using Cons.IH Cons.prems by simp blast
  have "(\<forall>N \<in> set (M # Ms). N \<in> carrier_mat n n) \<and>
        map (\<lambda>N. N\<^sup>\<dagger> * N) (M # Ms) = P # Ps"
    using Mcar M_factor Mscar Ms_factor by simp
  thus ?case
    by meson
qed

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
  obtain Ms where Mcar: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    and Ms_factor: "map (\<lambda>M. M\<^sup>\<dagger> * M) Ms = Ps"
    using psd_sqrt_measurement_factors[OF psd_each] by blast
  have "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ms (0\<^sub>m n n) =
        foldr (\<lambda>P acc. P + acc) Ps (0\<^sub>m n n)"
    using Ms_factor by (induction Ms arbitrary: Ps) auto
  also have "\<dots> = 1\<^sub>m n"
    using sum_id by simp
  finally have meas_sum:
    "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n" .
  have "measurement_system n Ms"
    unfolding measurement_system_def
    using Mcar meas_sum by simp
  thus ?thesis
    using Ms_factor by blast
qed


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


subsection \<open>Composite systems\<close>

text \<open>Postulate 4 was stated with Day 7.  The notes' example: photons in states
$\tfrac1{\sqrt2}(\ket0+\ket1)$ and $\tfrac1{\sqrt2}(\ket0+i\ket1)$ form the pair
$\tfrac12(\ket{00}+i\ket{01}+\ket{10}+i\ket{11})\in\C^2\otimes\C^2$, a vector of Schmidt
rank $1$.  Two photons described by a unit vector $\psi\in\C^2\otimes\C^2$ can be regarded
as two separate subsystems iff $\psi=\psi_1\otimes\psi_2$ iff the Schmidt rank of $\psi$ is
$1$; otherwise $\psi$ is \emph{entangled}, which does happen in nature.

Tensor products of operators: for $R:\Hil\to\Hil$ and $T:\Kil\to\Kil$ there is a unique
$R\otimes T$ with $(R\otimes T)(\sum_l h_l\otimes k_l)=\sum_l Rh_l\otimes Tk_l$, and
(1) $(R_1\otimes T_1)(R_2\otimes T_2)=R_1R_2\otimes T_1T_2$, (2) $(R\otimes T)^*=R^*\otimes T^*$
(both proved in Basic\_Math for the Kronecker product).
\begin{notesremark}
If lab A has the measurement system $\{M_m\}$ on $\Hil$ and lab B has state space $\Kil$,
the measurement system of the composite is $\{M_m\otimes I_{\Kil}\}$ and
$p_m^{AB}(\psi\otimes\phi)=\norm{(M_m\otimes I)(\psi\otimes\phi)}^2=p_m^A(\psi)$.
\end{notesremark}\<close>

lemma tensor_mat_vec_mult:
  assumes A: "A \<in> carrier_mat nr nc"
      and B: "B \<in> carrier_mat mr mc"
      and v: "dim_vec v = nc"
      and w: "dim_vec w = mc"
  shows "(A \<Otimes> B) *\<^sub>v tensor_vec v w = tensor_vec (A *\<^sub>v v) (B *\<^sub>v w)"
proof (rule eq_vecI)
  have vcar: "v \<in> carrier_vec nc"
    using carrier_vec_dim_vec v by blast

  have wcar: "w \<in> carrier_vec mc"
    using carrier_vec_dim_vec w by blast
  have dim_Av: "dim_vec (A *\<^sub>v v) = nr"
    using A v by simp
  have dim_Bw: "dim_vec (B *\<^sub>v w) = mr"
    using B w by simp
  show "dim_vec ((A \<Otimes> B) *\<^sub>v tensor_vec v w) = dim_vec (tensor_vec (A *\<^sub>v v) (B *\<^sub>v w))"
    using A B v w dim_Av dim_Bw by (simp add: tensor_vec_dim)
next
  fix i
  assume i: "i < dim_vec (tensor_vec (A *\<^sub>v v) (B *\<^sub>v w))"
  have vcar: "v \<in> carrier_vec nc"
    using carrier_vec_dim_vec v by blast
  have wcar: "w \<in> carrier_vec mc"
    using carrier_vec_dim_vec w by blast
  have dim_Av: "dim_vec (A *\<^sub>v v) = nr"
    using A v by simp
  have dim_Bw: "dim_vec (B *\<^sub>v w) = mr"
    using B w by simp
  have i_lt: "i < nr * mr"
    using i dim_Av dim_Bw by (simp add: tensor_vec_dim)
  show "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i"
  proof (cases "nc = 0 \<or> mc = 0")
    case True
    have lhs: "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = 0"
      using A B v w i_lt True
      by (simp add: mult_mat_vec_index tensor_vec_dim,
          smt (verit, ccfv_SIG) carrier_matD(2) conjugate_square_eq_0_vec 
          cscalar_prod_is_inner_prod_swap dim_col_tensor_mat dim_vec
          index_row(2) inner_prod_with_row_bra_vec mult_0_right mult_cancel_left row_bra_vec 
          tensor_vec_dim vcar vec_of_dim_0 wcar)
    have rhs: "tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i = 0"
      using A B v w i_lt True
      by (smt (verit, ccfv_threshold) carrier_matD(1,2) dim_Av dim_Bw dim_col_tensor_mat 
          dim_row_tensor_mat index_mult_mat_vec index_row(2) less_mult_imp_div_less lhs 
          mod_less_divisor mult_eq_0_iff not_gr_zero tensor_vec_dim tensor_vec_index vec_of_dim_0)      
    show ?thesis
      using lhs rhs by simp
  next
    case False
    then have nc_pos: "nc > 0" and mc_pos: "mc > 0"
      by auto
    have mr_pos: "mr > 0"
      using i_lt by (cases mr) auto
    let ?f = "\<lambda>k. (A \<Otimes> B) $$ (i, k) * tensor_vec v w $ k"
    have AB_car: "A \<Otimes> B \<in> carrier_mat (nr * mr) (nc * mc)"
      using A B by auto
    have tvw_car: "tensor_vec v w \<in> carrier_vec (nc * mc)"
      using v w by (metis carrier_vec_dim_vec tensor_vec_dim)
    have lhs_sum: "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = (\<Sum>k = 0..<nc * mc. ?f k)"
      using mult_mat_vec_index[OF AB_car tvw_car i_lt] .
    have group_sum: "(\<Sum>k = 0..<nc * mc. ?f k) = (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc. ?f (a * mc + b))"
    proof -
      have "(\<Sum>k = 0..<nc * mc. ?f k) = (\<Sum>a<nc. sum ?f {a * mc..<a * mc + mc})"
        using sum.nat_group[of ?f mc nc]
        by (simp add: atLeast0LessThan)
      also have "\<dots> = (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc. ?f (a * mc + b))"
      proof (rule sum.cong)
        show "{..<nc} = {0..<nc}"
          by auto
      next
        fix a
        assume a: "a \<in> {0..<nc}"
        show "sum ?f {a * mc..<a * mc + mc} =
              (\<Sum>b = 0..<mc. ?f (a * mc + b))"
        proof (rule sum.reindex_bij_witness[where i = "\<lambda>b. a * mc + b" and j = "\<lambda>x. x - a * mc"])
          show "\<And>b. b \<in> {0..<mc} \<Longrightarrow> a * mc + b \<in> {a * mc..<a * mc + mc}"
            by simp
          show "\<And>x. x \<in> {a * mc..<a * mc + mc} \<Longrightarrow> x - a * mc \<in> {0..<mc}"
            by fastforce
          show "\<And>x. x \<in> {a * mc..<a * mc + mc} \<Longrightarrow> a * mc + (x - a * mc) = x"
            by simp
          show "\<And>b. b \<in> {0..<mc} \<Longrightarrow> a * mc + b - a * mc = b"
            by simp
          show "\<And>x. x \<in> {a * mc..<a * mc + mc} \<Longrightarrow> ?f (a * mc + (x - a * mc)) = ?f x"
            by simp
        qed
      qed
      finally show ?thesis.
    qed
    have expand: "\<And>a b. a < nc \<Longrightarrow> b < mc \<Longrightarrow>
       ?f (a * mc + b) = (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b)"
    proof -
      fix a b
      assume a: "a < nc" and b: "b < mc"
      have k_lt: "a * mc + b < nc * mc"
        by (metis False a b diff_is_0_eq diff_zero div_less_iff_less_mult 
            mult.commute not_less split_div)
      have div_k: "(a * mc + b) div mc = a"
        using b by simp
      have mod_k: "(a * mc + b) mod mc = b"
        using b by simp
      have mat_idx: "(A \<Otimes> B) $$ (i, a * mc + b) = A $$ (i div mr, a) * B $$ (i mod mr, b)"
        using A B i_lt k_lt nc_pos mc_pos div_k mod_k by auto      
      have vec_idx: "tensor_vec v w $ (a * mc + b) = v $ a * w $ b"
        using tensor_vec_index[OF v w k_lt] div_k mod_k by simp
      show "?f (a * mc + b) = (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b)"
        using mat_idx vec_idx by (simp add: algebra_simps)
    qed
    have lhs: "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i =
       (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc. (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b))"
    proof -
      have "((A \<Otimes> B) *\<^sub>v tensor_vec v w) $ i = (\<Sum>k = 0..<nc * mc. ?f k)"
        by (rule lhs_sum)
      also have "\<dots> = (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc. ?f (a * mc + b))"
        by (rule group_sum)
      also have "\<dots> = (\<Sum>a = 0..<nc. \<Sum>b = 0..<mc.
                        (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b))"
      proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
        fix a b
        assume "a \<in> {0..<nc}" and "b \<in> {0..<mc}"
        then have "a < nc" and "b < mc" by auto
        then show "?f (a * mc + b) =
                   (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b)"
          by (rule expand)
      qed
      finally show ?thesis .
    qed


    have div_lt: "i div mr < nr"
      using i_lt mr_pos by (simp add: less_mult_imp_div_less)
    have mod_lt: "i mod mr < mr"
      using mr_pos by simp
    have rhs: "tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i =
       (\<Sum>a = 0..<nc. A $$ (i div mr, a) * v $ a) * (\<Sum>b = 0..<mc. B $$ (i mod mr, b) * w $ b)"
    proof -
      have "tensor_vec (A *\<^sub>v v) (B *\<^sub>v w) $ i = (A *\<^sub>v v) $ (i div mr) * (B *\<^sub>v w) $ (i mod mr)"
        using tensor_vec_index[OF dim_Av dim_Bw i_lt].
      also have "\<dots> = (\<Sum>a = 0..<nc. A $$ (i div mr, a) * v $ a) *
                      (\<Sum>b = 0..<mc. B $$ (i mod mr, b) * w $ b)"
        using mult_mat_vec_index[OF A vcar div_lt]
              mult_mat_vec_index[OF B wcar mod_lt]
        by simp
      finally show ?thesis.
    qed
    have "(\<Sum>a = 0..<nc. \<Sum>b = 0..<mc.
          (A $$ (i div mr, a) * v $ a) * (B $$ (i mod mr, b) * w $ b)) =
          (\<Sum>a = 0..<nc. A $$ (i div mr, a) * v $ a) *
          (\<Sum>b = 0..<mc. B $$ (i mod mr, b) * w $ b)"
      by (simp add: sum_product)
    then show ?thesis
      using lhs rhs by simp
  qed
qed

lemma tensor_mat_vec_mult_right_id:
  assumes A: "A \<in> carrier_mat n n"
      and v: "dim_vec v = n"
      and w: "dim_vec w = m"
  shows "(A \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec v w = tensor_vec (A *\<^sub>v v) w"
proof -
  have "(A \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec v w =
        tensor_vec (A *\<^sub>v v) (1\<^sub>m m *\<^sub>v w)"
    using tensor_mat_vec_mult[OF A one_carrier_mat v w] .
  also have "\<dots> = tensor_vec (A *\<^sub>v v) w"
    using w Matrix.one_mult_mat_vec by force
  finally show ?thesis .
qed


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
    using tensor_mat_vec_mult_right_id[OF M_sq psi_dim phi_dim] .
  (* Step 2: \<parallel>(M\<psi>)\<otimes>\<phi>\<parallel>² = \<parallel>M\<psi>\<parallel>² \<sqdot> \<parallel>\<phi>\<parallel>² = \<parallel>M\<psi>\<parallel>² \<sqdot> 1 *)
  have norm_prod: "\<parallel>tensor_vec (M *\<^sub>v \<psi>) \<phi>\<parallel>^2 = \<parallel>M *\<^sub>v \<psi>\<parallel>^2 * \<parallel>\<phi>\<parallel>^2"
    by (smt (verit) Re_complex_of_real cpx_vec_length_inner_prod of_real_mult tensor_inner_prod)
  have eq: "\<parallel>tensor_vec (M *\<^sub>v \<psi>) \<phi>\<parallel>^2 = \<parallel>M *\<^sub>v \<psi>\<parallel>^2"
    using norm_prod phi_norm by simp
  show ?thesis
    unfolding meas_prob_def using mix eq by simp
qed

subsection \<open>Entanglement\<close>

text \<open>A state $\psi\in\Hil_A\otimes\Hil_B$ is \emph{entangled} if it is not a product
state $u\otimes v$.  The Bell state $\gamma=\tfrac1{\sqrt2}(\ket{00}+\ket{11})$ is
entangled.  The notes' first application of entanglement (A and B share $\gamma$; A measures
$\ketbra00,\ketbra11$ and gets each outcome with probability $\tfrac12$, after which B's
measurement is determined) is not formalised.\<close>

definition entangled :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
  "entangled n m \<psi> \<equiv>
     dim_vec \<psi> = n * m \<and>
     \<not> (\<exists>u v. dim_vec u = n \<and> dim_vec v = m \<and> \<psi> = tensor_vec u v)"

definition bell_state :: "complex Matrix.vec" where
  "bell_state \<equiv> (1 / csqrt 2) \<cdot>\<^sub>v
                 (tensor_vec (unit_vec 2 0) (unit_vec 2 0) +
                  tensor_vec (unit_vec 2 1) (unit_vec 2 1))"

lemma bell_state_norm:
  "\<parallel>bell_state\<parallel> = 1"
proof -
  let ?u = "tensor_vec (unit_vec 2 0) (unit_vec 2 0)"
  let ?v = "tensor_vec (unit_vec 2 1) (unit_vec 2 1)"
  have du: "dim_vec ?u = 4" using tensor_vec_dim by simp
  have dv: "dim_vec ?v = 4" using tensor_vec_dim by simp
  have dsum: "dim_vec (?u + ?v) = 4" using du dv by simp
  have inner_uu: "\<langle>?u | ?u\<rangle> = 1"
    by (smt (verit) cpx_vec_length_inner_prod numeral_2_eq_2 of_real_1 power2_eq_square power_one tensor_inner_prod unit_cpx_vec_length zero_less_Suc)
  have inner_vv: "\<langle>?v | ?v\<rangle> = 1"
    by (smt (verit) Suc_1 cpx_vec_length_inner_prod lessI of_real_1 power2_eq_square power_one tensor_inner_prod unit_cpx_vec_length)
  have inner_uv: "\<langle>?u | ?v\<rangle> = 0"
    by (smt (verit) One_nat_def index_unit_vec(3) lessI mult_zero_right numeral_2_eq_2 one_neq_zero orthogonal_unit_vec tensor_inner_prod zero_less_Suc)
  have inner_vu: "\<langle>?v | ?u\<rangle> = 0"
    using inner_uv inner_prod_cnj[of ?u ?v] du dv by simp
  have inner_sum: "\<langle>?u + ?v | ?u + ?v\<rangle> = 2"
  proof -
    have "\<langle>?u + ?v | ?u + ?v\<rangle>
        = \<langle>?u | ?u + ?v\<rangle> + \<langle>?v | ?u + ?v\<rangle>"
      by (smt (verit, best) complex_cnj_add dsum dv index_unit_vec(3)
          inner_prod_cnj inner_prod_right_add' tensor_vec_dim)
    also have "... = (\<langle>?u | ?u\<rangle> + \<langle>?u | ?v\<rangle>) + (\<langle>?v | ?u\<rangle> + \<langle>?v | ?v\<rangle>)"
      using du dv inner_prod_right_add' by presburger
    also have "... = \<langle>?u | ?u\<rangle> + \<langle>?u | ?v\<rangle> + \<langle>?v | ?u\<rangle> + \<langle>?v | ?v\<rangle>"
      by (simp add: algebra_simps)
    also have "... = 2"
      using inner_uu inner_vv inner_uv inner_vu by simp
    finally show ?thesis.
  qed
  have sq_norm: "(\<parallel>?u + ?v\<parallel>)\<^sup>2 = 2"
  proof -
    have "complex_of_real ((\<parallel>?u + ?v\<parallel>)\<^sup>2) = \<langle>?u + ?v | ?u + ?v\<rangle>"
      using cpx_vec_length_inner_prod[of "?u + ?v"] by simp
    also have "\<dots> = 2" by (rule inner_sum)
    finally have "complex_of_real ((\<parallel>?u + ?v\<parallel>)\<^sup>2) = complex_of_real 2" by simp
    thus ?thesis using of_real_eq_iff by blast
  qed
  then have norm_nonneg: "\<parallel>?u + ?v\<parallel> \<ge> 0"
    by (smt (verit, ccfv_SIG) Re_complex_of_real cpx_vec_length_inner_prod csqrt_of_real_nonneg 
        inner_prod_csqrt inner_prod_with_itself_Im real_sqrt_abs)
  then have norm_sum: "\<parallel>?u + ?v\<parallel> = sqrt 2"
    using sq_norm 
    by (metis real_sqrt_abs2 real_sqrt_power abs_of_nonneg power2_eq_square)
  have smult_form: "bell_state = (1 / csqrt 2) \<cdot>\<^sub>v (?u + ?v)"
    unfolding bell_state_def by simp
  have "\<parallel>bell_state\<parallel> = cmod (1 / csqrt 2) * \<parallel>?u + ?v\<parallel>"
    using smult_form cpx_vec_length_smult[of "1 / csqrt 2" "?u + ?v"] by simp
  also have "cmod (1 / csqrt 2) = 1 / sqrt 2"
    by (simp add: norm_divide)
  also have "\<dots> * \<parallel>?u + ?v\<parallel> = 1 / sqrt 2 * sqrt 2"
    using norm_sum by simp
  also have "\<dots> = 1"
    by (simp add: field_simps)
  finally show ?thesis.
qed

lemma bell_state_is_quantum_state:
  "quantum_state 4 bell_state"
proof -
  let ?u = "tensor_vec (unit_vec 2 0) (unit_vec 2 0)"
  let ?v = "tensor_vec (unit_vec 2 1) (unit_vec 2 1)"
  (* Step 1: each tensor has dim 4. *)
  have du: "dim_vec ?u = 4" using tensor_vec_dim by simp
  have dv: "dim_vec ?v = 4" using tensor_vec_dim by simp
  have dim_sum: "dim_vec (?u + ?v) = 4" using du dv by simp
  then have dim_bell: "dim_vec bell_state = 4"
    unfolding bell_state_def by simp
  (* Step 2: \<parallel>(1/\<surd>2)(?u + ?v)\<parallel>\<^sup>2 = (1/2)(\<langle>?u+?v|?u+?v\<rangle>) = (1/2)(1+0+0+1) = 1 *)
  have norm_bell: "\<parallel>bell_state\<parallel> = 1"
    by (rule bell_state_norm)
  show ?thesis
    unfolding quantum_state_def using dim_bell norm_bell by simp
qed

lemma bell_state_entangled:
  "entangled 2 2 bell_state"
proof -
  have dim_bell: "dim_vec bell_state = 4"
    using bell_state_is_quantum_state unfolding quantum_state_def by simp

  have bell0: "bell_state $ 0 = 1 / csqrt 2"
    unfolding bell_state_def by (simp add: tensor_vec_dim tensor_vec_index)
  have bell2: "bell_state $ 2 = 0"
    unfolding bell_state_def by (simp add: tensor_vec_dim tensor_vec_index)
  have bell3: "bell_state $ 3 = 1 / csqrt 2"
    unfolding bell_state_def by (simp add: tensor_vec_dim tensor_vec_index)

  have not_product:
    "\<not> (\<exists>u v. dim_vec u = 2 \<and> dim_vec v = 2 \<and> bell_state = tensor_vec u v)"
  proof
    assume "\<exists>u v. dim_vec u = 2 \<and> dim_vec v = 2 \<and> bell_state = tensor_vec u v"
    then obtain u v where udim: "dim_vec u = 2" and vdim: "dim_vec v = 2"
      and eq: "bell_state = tensor_vec u v"
      by blast

    have uv0: "u $ 0 * v $ 0 = 1 / csqrt 2"
      using bell0 eq tensor_vec_index[OF udim vdim, of 0] by simp
    then have u0_nonzero: "u $ 0 \<noteq> 0" and v0_nonzero: "v $ 0 \<noteq> 0"
      by auto

    have uv2: "u $ 1 * v $ 0 = 0"
      using bell2 eq tensor_vec_index[OF udim vdim, of 2] by simp
    then have u1_zero: "u $ 1 = 0"
      using v0_nonzero by auto

    have uv3: "u $ 1 * v $ 1 = 1 / csqrt 2"
      using bell3 eq tensor_vec_index[OF udim vdim, of 3] by simp
    then have "1 / csqrt 2 = 0"
      using u1_zero by simp
    then show False
      by simp
  qed

  show ?thesis
    unfolding entangled_def using dim_bell not_product by simp
qed  (* If bell_state = u\<otimes>v then matrix [u₀v₀, u₀v₁; u₁v₀, u₁v₁] has rank 1.
        But the bell_state coefficient matrix [1/\<surd>2, 0; 0, 1/\<surd>2] has rank 2. *)


section \<open>Day 10 (19 September 2011): superdense coding; classical and quantum gates\<close>

subsection \<open>One-qubit gates\<close>

text \<open>The one-qubit gates of the notes:
\[
X=\begin{pmatrix}0&1\\1&0\end{pmatrix}\ (\text{NOT}),\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad
S=\begin{pmatrix}1&0\\0&i\end{pmatrix}.
\]
$H$ is the Hadamard gate; the notes write ``$H^2=X$'' here and correct it to $H^2=I$ on
Day 11, which is what is proved below.  $H$ and $S$ together generate all $2\times2$
unitaries (not formalised).  The library provides \<open>X\<close>, \<open>Y\<close>, \<open>Z\<close>, \<open>H\<close>; the phase gate
is \<open>S_gate\<close> below.\<close>

definition H_gate :: "complex Matrix.mat" where
  "H_gate \<equiv> H"

lemma csqrt_two: "csqrt (2::complex) = (sqrt 2 :: complex)"
  by simp


lemma hadamard_squared:
  "H_gate * H_gate = 1\<^sub>m 2"
  by (simp add: H_gate_def)


lemma hadamard_e0:
  "H_gate *\<^sub>v unit_vec 2 0 =
   (1 / csqrt 2) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"
  by (rule eq_vecI)
     (auto simp add: H_gate_def H_def mult_mat_vec_def scalar_prod_def unit_vec_def csqrt_two
                      less_2_cases)

lemma hadamard_e1:
  "H_gate *\<^sub>v unit_vec 2 1 =
   (1 / csqrt 2) \<cdot>\<^sub>v (unit_vec 2 0 - unit_vec 2 1)"
  by (rule eq_vecI)
     (auto simp add: H_gate_def H_def mult_mat_vec_def scalar_prod_def unit_vec_def csqrt_two
                      less_2_cases)



text \<open>The phase gate $S=\mathrm{diag}(1,i)$ is unitary.\<close>

definition S_gate :: "complex Matrix.mat" where
  "S_gate \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then 1 else if i = 1 \<and> j = 1 then \<i> else 0)"

lemma S_gate_carrier [simp]: "S_gate \<in> carrier_mat 2 2"
  by (simp add: S_gate_def)

lemma S_gate_dagger_S: "S_gate\<^sup>\<dagger> * S_gate = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (S_gate\<^sup>\<dagger> * S_gate) = dim_row (1\<^sub>m 2 :: complex Matrix.mat)" by (simp add: S_gate_def)
  show "dim_col (S_gate\<^sup>\<dagger> * S_gate) = dim_col (1\<^sub>m 2 :: complex Matrix.mat)" by (simp add: S_gate_def)
  fix i j assume "i < dim_row (1\<^sub>m 2 :: complex Matrix.mat)" "j < dim_col (1\<^sub>m 2 :: complex Matrix.mat)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(S_gate\<^sup>\<dagger> * S_gate) $$ (i, j) = (1\<^sub>m 2 :: complex Matrix.mat) $$ (i, j)"
    unfolding S_gate_def dagger_def scalar_prod_def
    by (cases i; cases j) (auto simp: less_2_cases numeral_2_eq_2)
qed

lemma S_gate_S_dagger: "S_gate * (S_gate\<^sup>\<dagger>) = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (S_gate * (S_gate\<^sup>\<dagger>)) = dim_row (1\<^sub>m 2 :: complex Matrix.mat)" by (simp add: S_gate_def)
  show "dim_col (S_gate * (S_gate\<^sup>\<dagger>)) = dim_col (1\<^sub>m 2 :: complex Matrix.mat)" by (simp add: S_gate_def)
  fix i j assume "i < dim_row (1\<^sub>m 2 :: complex Matrix.mat)" "j < dim_col (1\<^sub>m 2 :: complex Matrix.mat)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(S_gate * (S_gate\<^sup>\<dagger>)) $$ (i, j) = (1\<^sub>m 2 :: complex Matrix.mat) $$ (i, j)"
    unfolding S_gate_def dagger_def scalar_prod_def
    by (cases i; cases j) (auto simp: less_2_cases numeral_2_eq_2)
qed

lemma S_gate_unitary: "unitary S_gate"
  unfolding unitary_def using S_gate_dagger_S S_gate_S_dagger by (simp add: S_gate_def)

subsection \<open>Two- and three-qubit gates\<close>

text \<open>The notes tabulate the classical gates AND, OR, XOR, NAND, NOR (Peirce: NAND
generates all Boolean operations; Sheffer: so does NOR).  No two-bit classical gate is a
quantum gate, since it maps two dimensions to one and is not reversible.  The controlled
NOT acts by $\ket{a,b}\mapsto\ket{a,b\oplus a}$:
\[
\mathrm{CNOT}=\begin{pmatrix}1&0&0&0\\0&1&0&0\\0&0&0&1\\0&0&1&0\end{pmatrix},
\]
which is unitary, and Toffoli's CCNOT (identity on the first six basis vectors, swapping
$\ket{110}$ and $\ket{111}$) is a reversible gate generating all Boolean operations; it is
defined in theory Quantum\_Computing11.\<close>

lemma CNOT_unitary: "unitary CNOT"
  using CNOT_is_gate gate.unitary by blast

lemma CNOT_00:
  "CNOT *\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 0)) =
   tensor_vec (unit_vec 2 0) (unit_vec 2 0)"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (tensor_vec (unit_vec 2 0) (unit_vec 2 0))"
  show "(CNOT *\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 0))) $ i =
        tensor_vec (unit_vec 2 0) (unit_vec 2 0) $ i"
    using i
    by (auto simp add: CNOT_def mult_mat_vec_def scalar_prod_def tensor_vec_dim
                        tensor_vec_index unit_vec_def less_2_cases)
next
  show "dim_vec (CNOT *\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 0))) =
        dim_vec (tensor_vec (unit_vec 2 0) (unit_vec 2 0))"
    by (simp add: CNOT_def tensor_vec_dim)
qed

lemma CNOT_10:
  "CNOT *\<^sub>v (tensor_vec (unit_vec 2 1) (unit_vec 2 0)) =
   tensor_vec (unit_vec 2 1) (unit_vec 2 1)"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (tensor_vec (unit_vec 2 1) (unit_vec 2 1))"
  show "(CNOT *\<^sub>v (tensor_vec (unit_vec 2 1) (unit_vec 2 0))) $ i =
        tensor_vec (unit_vec 2 1) (unit_vec 2 1) $ i"
  proof -
    have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
      using i by (auto simp add: tensor_vec_dim)
    then show ?thesis
      using i
      by (auto simp add: CNOT_def mult_mat_vec_def scalar_prod_def tensor_vec_dim
                          tensor_vec_index unit_vec_def less_2_cases)
  qed
next
  show "dim_vec (CNOT *\<^sub>v (tensor_vec (unit_vec 2 1) (unit_vec 2 0))) =
        dim_vec (tensor_vec (unit_vec 2 1) (unit_vec 2 1))"
    by (simp add: CNOT_def tensor_vec_dim)
qed

lemma CNOT_01:
  "CNOT *\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 1)) =
   tensor_vec (unit_vec 2 0) (unit_vec 2 1)"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (tensor_vec (unit_vec 2 0) (unit_vec 2 1))"
  show "(CNOT *\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 1))) $ i =
        tensor_vec (unit_vec 2 0) (unit_vec 2 1) $ i"
    using i
    by (auto simp add: CNOT_def mult_mat_vec_def scalar_prod_def tensor_vec_dim
                        tensor_vec_index unit_vec_def less_2_cases)
next
  show "dim_vec (CNOT *\<^sub>v (tensor_vec (unit_vec 2 0) (unit_vec 2 1))) =
        dim_vec (tensor_vec (unit_vec 2 0) (unit_vec 2 1))"
    by (simp add: CNOT_def tensor_vec_dim)
qed

lemma CNOT_11:
  "CNOT *\<^sub>v (tensor_vec (unit_vec 2 1) (unit_vec 2 1)) =
   tensor_vec (unit_vec 2 1) (unit_vec 2 0)"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (tensor_vec (unit_vec 2 1) (unit_vec 2 0))"
  show "(CNOT *\<^sub>v (tensor_vec (unit_vec 2 1) (unit_vec 2 1))) $ i =
        tensor_vec (unit_vec 2 1) (unit_vec 2 0) $ i"
    using i
    by (auto simp add: CNOT_def mult_mat_vec_def scalar_prod_def tensor_vec_dim
                        tensor_vec_index unit_vec_def less_2_cases)
next
  show "dim_vec (CNOT *\<^sub>v (tensor_vec (unit_vec 2 1) (unit_vec 2 1))) =
        dim_vec (tensor_vec (unit_vec 2 1) (unit_vec 2 0))"
    by (simp add: CNOT_def tensor_vec_dim)
qed

lemma tensor_unit_vec_2_00:
  "tensor_vec (unit_vec 2 0) (unit_vec 2 0) = unit_vec 4 0"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (unit_vec 4 0 :: complex Matrix.vec)"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    by auto
  then show "tensor_vec (unit_vec 2 0) (unit_vec 2 0) $ i =
        (unit_vec 4 0 :: complex Matrix.vec) $ i"
    using i
    by (auto simp add: tensor_vec_dim tensor_vec_index unit_vec_def less_2_cases)
next
  show "dim_vec (tensor_vec (unit_vec 2 0) (unit_vec 2 0)) =
        dim_vec (unit_vec 4 0 :: complex Matrix.vec)"
    by (simp add: tensor_vec_dim)
qed

lemma tensor_unit_vec_2_01:
  "tensor_vec (unit_vec 2 0) (unit_vec 2 1) = unit_vec 4 1"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (unit_vec 4 1 :: complex Matrix.vec)"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    by auto
  then show "tensor_vec (unit_vec 2 0) (unit_vec 2 1) $ i =
        (unit_vec 4 1 :: complex Matrix.vec) $ i"
    using i
    by (auto simp add: tensor_vec_dim tensor_vec_index unit_vec_def less_2_cases)
next
  show "dim_vec (tensor_vec (unit_vec 2 0) (unit_vec 2 1)) =
        dim_vec (unit_vec 4 1 :: complex Matrix.vec)"
    by (simp add: tensor_vec_dim)
qed

lemma tensor_unit_vec_2_10:
  "tensor_vec (unit_vec 2 1) (unit_vec 2 0) = unit_vec 4 2"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (unit_vec 4 2 :: complex Matrix.vec)"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    by auto
  then show "tensor_vec (unit_vec 2 1) (unit_vec 2 0) $ i =
        (unit_vec 4 2 :: complex Matrix.vec) $ i"
    using i
    by (auto simp add: tensor_vec_dim tensor_vec_index unit_vec_def less_2_cases)
next
  show "dim_vec (tensor_vec (unit_vec 2 1) (unit_vec 2 0)) =
        dim_vec (unit_vec 4 2 :: complex Matrix.vec)"
    by (simp add: tensor_vec_dim)
qed

lemma tensor_unit_vec_2_11:
  "tensor_vec (unit_vec 2 1) (unit_vec 2 1) = unit_vec 4 3"
proof (rule eq_vecI)
  fix i
  assume i: "i < dim_vec (unit_vec 4 3 :: complex Matrix.vec)"
  then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    by auto
  then show "tensor_vec (unit_vec 2 1) (unit_vec 2 1) $ i =
        (unit_vec 4 3 :: complex Matrix.vec) $ i"
    using i
    by (auto simp add: tensor_vec_dim tensor_vec_index unit_vec_def less_2_cases)
next
  show "dim_vec (tensor_vec (unit_vec 2 1) (unit_vec 2 1)) =
        dim_vec (unit_vec 4 3 :: complex Matrix.vec)"
    by (simp add: tensor_vec_dim)
qed

subsection \<open>Superdense coding\<close>

text \<open>A and B share $\gamma=\tfrac1{\sqrt2}(\ket{00}+\ket{11})$.  Applying nothing,
$\begin{pmatrix}1&0\\0&-1\end{pmatrix}$, $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ or
$\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ to its qubit, A turns $\gamma$ into one of the four
orthonormal Bell states $\tfrac1{\sqrt2}(\ket{00}\pm\ket{11})$,
$\tfrac1{\sqrt2}(\ket{10}\pm\ket{01})$, so by sending one qubit A communicates two bits; with
$2m$ shared qubits, $4^m$ messages.  Below: the four Bell states and their
orthonormality (the action table itself is not formalised).\<close>

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
proof -
  have dims: "\<forall>v \<in> set bell_basis. dim_vec v = 4"
    unfolding bell_basis_def
    unfolding tensor_unit_vec_2_00 tensor_unit_vec_2_01
              tensor_unit_vec_2_10 tensor_unit_vec_2_11
    by simp
  have sqrt2_mult: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = (2::complex)"
    by (simp add: of_real_def complex_eq_iff)
  have ips: "\<forall>i < length bell_basis. \<forall>j < length bell_basis.
      \<langle>bell_basis ! i | bell_basis ! j\<rangle> = (if i = j then 1 else 0)"
  proof safe
    fix i j
    assume i: "i < length bell_basis" and j: "j < length bell_basis"
    then have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
      unfolding bell_basis_def by auto
    from i j have j_cases: "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3"
      unfolding bell_basis_def by auto
    show "\<langle>bell_basis ! i | bell_basis ! j\<rangle> =
        (if i = j then 1 else 0)"
      using i_cases j_cases
      unfolding bell_basis_def
      unfolding tensor_unit_vec_2_00 tensor_unit_vec_2_01
                tensor_unit_vec_2_10 tensor_unit_vec_2_11
      by (elim disjE; simp add: inner_prod_def unit_vec_def csqrt_two sqrt2_mult field_simps)
  qed
  show ?thesis
    unfolding orthonormal_list_def
    using dims ips by blast
qed

end
