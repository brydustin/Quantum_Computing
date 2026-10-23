(*  Title:   Day03_Unitary_Matrices.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 31 August 2011 (Day 3)
*)

theory Day03_Unitary_Matrices
  imports
    Unitary_Tensor_Algebra
    Jordan_Normal_Form.Schur_Decomposition
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
      using No_Cloning.inner_prod_distrib_left by blast
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
        by (rule No_Cloning.inner_prod_distrib_left) simp
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
        by (rule No_Cloning.inner_prod_distrib_left) (use xdim zdim in simp)
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

end
