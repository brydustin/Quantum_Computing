(*  Title:   Day01_Inner_Product.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 22 August 2011 (Day 1)
*)

theory Day01_Inner_Product
  imports
    Essential_Functional_Analysis.Matrix_Lemmas
    Quantum_Fourier_Transform.QFT
    Isabelle_Marries_Dirac.No_Cloning
begin

(*<*)
text \<open>Isabelle\_Marries\_Dirac names its gates \<open>X\<close>, \<open>Y\<close>, \<open>Z\<close>, \<open>H\<close>, \<open>S\<close>, \<open>T\<close>; hidden here
so that these letters are variables.  The gates remain \<open>Quantum.X\<close> etc.; the project
names are \<open>Pauli_X\<close>, \<open>Pauli_Y\<close>, \<open>Pauli_Z\<close>, \<open>Hadamard\<close>, \<open>Phase_S\<close>.  Theories importing
this one must not import Isabelle\_Marries\_Dirac directly, as that undoes the hiding.\<close>

hide_const (open) Quantum.X Quantum.Y Quantum.Z Quantum.H Quantum.S Quantum.T

(* No_Cloning is imported for cauchy_schwarz_ineq; its simp rules slow down every vector equation. *)

declare cauchy_schwarz_eq [simp del] cauchy_schwarz_col [simp del] eq_from_inner_prod [simp del]
(*>*)

section \<open>Day 1 (22 August 2011): the inner product\<close>

text \<open>Paulsen opens with the dictionary between classical and quantum computing: a bit
is an element of $\Z_2$, a qubit a unit vector in $\C^2$; $N$ bits form $\Z_2^N$, $N$ qubits
a unit vector in $\C^{2^N}\cong\C^2\otimes\cdots\otimes\C^2$; operations are Boolean gates
versus completely positive maps on $M_{2^N}$; information is a probability vector versus a
positive semidefinite matrix of trace one.  He then fixes the physicists' notation.

\begin{notesdef}
$\C^n$ is the space of complex $n$-tuples with the inner product
\[ \braket{y}{x} = \sum_{i=1}^{n} \overline{y_i}\, x_i , \]
which is linear in the right-hand slot, conjugate linear in the left-hand slot
(``sesquilinear''), and positive definite: $\braket{x}{x}\ge 0$ with equality only for
$x=0$.  The Euclidean length is $\norm{x}=\sqrt{\braket{x}{x}}$.  A \emph{Hilbert space} is
a complex vector space with a sesquilinear positive definite form, complete for this norm.
\end{notesdef}

The library's inner product \<^term>\<open>\<langle>y|x\<rangle>\<close> is exactly this form, with indices
running from $0$ to $n-1$.\<close>

lemma inner_prod_sum:
  assumes "dim_vec u = n" and "dim_vec v = n"
  shows "\<langle>u|v\<rangle> = (\<Sum> i \<in> {0..< n}. cnj(u $ i) * (v $ i))"
  using assms by (simp add: inner_prod_def)

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

text \<open>The vector inner product is linear on the right,
$\braket u{av+w}=a\braket uv+\braket uw$, and conjugate-linear on the left; correspondingly
$(\gamma U)^*=\overline\gamma\,U^*$.\<close>

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

subsection \<open>The Hilbert--Schmidt inner product on matrices\<close>

text \<open>\begin{notesdef}[Example]
The space $M_{n,k}$ of complex $n\times k$ matrices is a Hilbert space for
\[ \langle (y_{ij}) \,|\, (x_{ij}) \rangle = \sum_{i}\sum_{j} \overline{y_{ij}}\,x_{ij}, \]
and $M_{n,k}\cong\C^{nk}$.
\end{notesdef}
We write \<open>\<langle>\<langle>y|x\<rangle>\<rangle>\<close> for this Hilbert--Schmidt (Frobenius) inner product; the
double brackets distinguish it from the inner product of vectors.\<close>

definition hs_inner_prod :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex" where
  "hs_inner_prod = (\<lambda> y x. 
     \<Sum> i \<in> {0 ..< dim_row x}. 
       \<Sum> j \<in> {0 ..< dim_col x}. 
         cnj (y $$ (i,j)) * (x $$ (i,j)))"

notation hs_inner_prod ("\<langle>\<langle> _ | _ \<rangle>\<rangle>")



lemma hs_inner_prod_expand:
  assumes "dim_row x = m" and "dim_col x = n"
  shows "\<langle>\<langle> y | x \<rangle>\<rangle> = 
         (\<Sum> i \<in> {0 ..< m}. \<Sum> j \<in> {0 ..< n}. cnj (y $$ (i,j)) * (x $$ (i,j)))"
  using assms by (simp add: hs_inner_prod_def)



lemma hs_inner_prod_square:
  assumes "dim_row x = n" and "dim_col x = n"
  shows "\<langle>\<langle> y | x \<rangle>\<rangle> = 
         (\<Sum> i \<in> {0 ..< n}. \<Sum> j \<in> {0 ..< n}. cnj (y $$ (i,j)) * (x $$ (i,j)))"
  using assms by (simp add: hs_inner_prod_def)


subsection \<open>Properties of the inner product\<close>

text \<open>The properties listed in the notes, verified for the matrix inner product:
conjugate symmetry, linearity in the right-hand slot, conjugate linearity in the left-hand
slot, and positive definiteness.\<close>


lemma hs_inner_prod_cnj:
  assumes "dim_row x = dim_row y" and "dim_col x = dim_col y"
  shows "\<langle>\<langle> x | y \<rangle>\<rangle> = cnj (\<langle>\<langle> y | x \<rangle>\<rangle>)"
proof -
  have "\<langle>\<langle> x | y \<rangle>\<rangle> = 
        (\<Sum> i \<in> {0 ..< dim_row y}. \<Sum> j \<in> {0 ..< dim_col y}. cnj (x $$ (i,j)) * (y $$ (i,j)))"
    using assms by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum> i \<in> {0 ..< dim_row y}. \<Sum> j \<in> {0 ..< dim_col y}. 
                    cnj (cnj (y $$ (i,j)) * (x $$ (i,j))))"
    by (intro sum.cong, auto)
  also have "\<dots> = cnj (\<Sum> i \<in> {0 ..< dim_row y}. \<Sum> j \<in> {0 ..< dim_col y}. 
                    cnj (y $$ (i,j)) * (x $$ (i,j)))"
    by simp
  also have "\<dots> = cnj (\<langle>\<langle> y | x \<rangle>\<rangle>)"
    using assms(1,2) hs_inner_prod_expand by presburger
  finally show ?thesis.
qed



text \<open>Linear in the right slot, conjugate-linear in the left:
\[ \langle Y|X_1+X_2\rangle=\langle Y|X_1\rangle+\langle Y|X_2\rangle,\qquad
   \langle Y|cX\rangle=c\,\langle Y|X\rangle,\qquad \langle cY|X\rangle=\overline c\,\langle Y|X\rangle. \]\<close>

lemma hs_inner_prod_right_add:
  assumes "dim_row X1 = dim_row y" and "dim_col X1 = dim_col y"
      and "dim_row X2 = dim_row y" and "dim_col X2 = dim_col y"
  shows "\<langle>\<langle> y | X1 + X2 \<rangle>\<rangle> = \<langle>\<langle> y | X1 \<rangle>\<rangle> + \<langle>\<langle> y | X2 \<rangle>\<rangle>"
proof -
  have dims: "dim_row (X1 + X2) = dim_row y" "dim_col (X1 + X2) = dim_col y"
    using assms by auto
  show ?thesis
    unfolding hs_inner_prod_def
    using assms by (auto simp: distrib_left sum.distrib intro!: sum.cong)
qed

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

lemma hs_inner_prod_right_smult:
  assumes "dim_row x = dim_row y" and "dim_col x = dim_col y"
  shows "\<langle>\<langle> y | c \<cdot>\<^sub>m x \<rangle>\<rangle> = c * \<langle>\<langle> y | x \<rangle>\<rangle>"
  unfolding hs_inner_prod_def using assms
  by (auto simp: mult.assoc sum_distrib_left intro!: sum.cong)


lemma hs_inner_prod_left_smult:
  assumes "dim_row x = dim_row y" and "dim_col x = dim_col y"
  shows "\<langle>\<langle> c \<cdot>\<^sub>m y | x \<rangle>\<rangle> = cnj c * \<langle>\<langle> y | x \<rangle>\<rangle>"
  unfolding hs_inner_prod_def using assms 
  by (auto simp: mult.assoc sum_distrib_left intro!: sum.cong)



text \<open>Positive definiteness: $\langle X|X\rangle=\sum_{i,j}|x_{ij}|^2$ is real, non-negative,
and $0$ only if every entry is $0$.\<close>

lemma hs_inner_prod_self_real:
  shows "\<langle>\<langle> x | x \<rangle>\<rangle> \<in> \<real>"
proof -
  have "\<langle>\<langle> x | x \<rangle>\<rangle> = (\<Sum> i \<in> {0 ..< dim_row x}. \<Sum> j \<in> {0 ..< dim_col x}. 
                              cnj (x $$ (i,j)) * (x $$ (i,j)))"
    by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum> i \<in> {0 ..< dim_row x}. \<Sum> j \<in> {0 ..< dim_col x}. 
                    (cmod (x $$ (i,j)))^2)"
    by (metis (lifting) ext complex_norm_square mult.commute of_real_hom.hom_sum)
  also have "\<dots> \<in> \<real>"
    by simp
  finally show ?thesis.
qed



lemma hs_inner_prod_self_nonneg:
  shows "Re (\<langle>\<langle> x | x \<rangle>\<rangle>) \<ge> 0"
proof -
  have "Re (\<langle>\<langle> x | x \<rangle>\<rangle>) = (\<Sum> i \<in> {0 ..< dim_row x}. \<Sum> j \<in> {0 ..< dim_col x}. 
                                   (cmod (x $$ (i,j)))^2)"
    unfolding hs_inner_prod_def 
    by(simp, metis (lifting) ext cmod_power2 power2_eq_square)
  also have "\<dots> \<ge> 0"
    by (intro sum_nonneg, simp)
  finally show ?thesis.
qed



lemma hs_inner_prod_eq_zero_imp:
  assumes "\<langle>\<langle> x | x \<rangle>\<rangle> = 0"
      and "i < dim_row x" and "j < dim_col x"
  shows "x $$ (i,j) = 0"
proof -
  define f where "f \<equiv> \<lambda>a b. Re (cnj (x$$(a,b)) * x$$(a,b))"
  (* Each f a b is non-negative *)
  have f_nonneg: "\<And>a b. f a b \<ge> 0"
    by (simp add: f_def)

  (* The double sum of f equals 0.
     We go: sum of f = sum of Re(...) = Re(sum of ...) = Re(0) = 0 *)
  have sum_zero: "(\<Sum>a\<in>{0..<dim_row x}. \<Sum>b\<in>{0..<dim_col x}. f a b) = 0"
  proof -
    have "(\<Sum>a\<in>{0..<dim_row x}. \<Sum>b\<in>{0..<dim_col x}. f a b) =
          Re (\<Sum>a\<in>{0..<dim_row x}. \<Sum>b\<in>{0..<dim_col x}. cnj (x$$(a,b)) * x$$(a,b))"
      unfolding f_def by (simp add: Re_sum[symmetric])
    also have "\<dots> = 0" using assms(1) by (simp add: hs_inner_prod_def)
    finally show ?thesis .
  qed

  (* Each inner sum is non-negative *)
  have inner_nonneg: "\<And>a. 0 \<le> (\<Sum>b\<in>{0..<dim_col x}. f a b)"
    by (intro sum_nonneg) (use f_nonneg in auto)

  (* Peel apart the outer sum — the i-th inner sum must be 0 *)
  have inner_zero: "(\<Sum>b\<in>{0..<dim_col x}. f i b) = 0"
    using sum_nonneg_0[of "{0..<dim_row x}" "\<lambda>a. \<Sum>b\<in>{0..<dim_col x}. f a b" i]
          sum_zero inner_nonneg assms(2) by auto

  (* Peel apart the inner sum — the j-th term must be 0 *)
  have "f i j = 0"
    using sum_nonneg_0[of "{0..<dim_col x}" "\<lambda>b. f i b" j]
          inner_zero f_nonneg assms(3) by auto

  (* f i j = 0 means (cmod(x$$(i,j)))^2 = 0, so x$$(i,j) = 0 *)
  then have "Re (cnj (x$$(i,j)) * x$$(i,j)) = 0" unfolding f_def by simp
  moreover have "cnj (x$$(i,j)) * x$$(i,j) = complex_of_real ((cmod (x$$(i,j)))\<^sup>2)"
    by (simp add: cmod_power2 complex_mult_cnj mult.commute)
  ultimately have "(cmod (x$$(i,j)))\<^sup>2 = 0" 
    by simp
  then have "cmod (x$$(i,j)) = 0" 
    by simp
  then show "x$$(i,j) = 0" 
    by simp
qed

lemma inner_prod_vec_sum_right:
  assumes ud: "dim_vec u = n"
      and wd: "\<And>J. J \<in> Js \<Longrightarrow> dim_vec (w J) = n"
  shows "\<langle>u | vec_sum n Js w\<rangle> = sum (\<lambda>J. \<langle>u | w J\<rangle>) Js"
proof -
  have "\<langle>u | vec_sum n Js w\<rangle> = (\<Sum>i = 0..<n. cnj (u $ i) * vec_sum n Js w $ i)"
    using inner_prod_sum[OF ud, of "vec_sum n Js w"] by simp
  also have "\<dots> = (\<Sum>i = 0..<n. sum (\<lambda>J. cnj (u $ i) * w J $ i) Js)"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = sum (\<lambda>J. \<Sum>i = 0..<n. cnj (u $ i) * w J $ i) Js"
    by (rule sum.swap)
  also have "\<dots> = sum (\<lambda>J. \<langle>u | w J\<rangle>) Js"
  proof (rule sum.cong[OF refl])
    fix J assume J: "J \<in> Js"
    show "(\<Sum>i = 0..<n. cnj (u $ i) * w J $ i) = \<langle>u | w J\<rangle>"
      using inner_prod_sum[OF ud wd[OF J]] by simp
  qed
  finally show ?thesis .
qed

lemma inner_prod_unit_vec_right:
  assumes ud: "dim_vec u = n" and j: "j < n"
  shows "\<langle>u | unit_vec n j\<rangle> = cnj (u $ j)"
proof -
  have "\<langle>u | unit_vec n j\<rangle> = (\<Sum>i = 0..<n. cnj (u $ i) * unit_vec n j $ i)"
    using inner_prod_sum[OF ud, of "unit_vec n j"] by simp
  also have "\<dots> = (\<Sum>i = 0..<n. if i = j then cnj (u $ i) else 0)"
    using j by (intro sum.cong refl) simp
  also have "\<dots> = cnj (u $ j)" using j by simp
  finally show ?thesis .
qed

end
