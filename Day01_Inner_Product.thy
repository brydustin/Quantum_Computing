(*  Title:   Day01_Inner_Product.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 22 August 2011 (Day 1)
*)

theory Day01_Inner_Product
  imports
    Quantum_Fourier_Transform.QFT
    Isabelle_Marries_Dirac.No_Cloning
begin

text \<open>Isabelle\_Marries\_Dirac names its gates \<open>X\<close>, \<open>Y\<close>, \<open>Z\<close>, \<open>H\<close>, \<open>S\<close>, \<open>T\<close>; hidden here
so that these letters are variables.  The gates remain \<open>Quantum.X\<close> etc.; the project
names are \<open>Pauli_X\<close>, \<open>Pauli_Y\<close>, \<open>Pauli_Z\<close>, \<open>Hadamard\<close>, \<open>Phase_S\<close>.  Theories importing
this one must not import Isabelle\_Marries\_Dirac directly, as that undoes the hiding.\<close>

hide_const (open) Quantum.X Quantum.Y Quantum.Z Quantum.H Quantum.S Quantum.T

text \<open>\<open>No_Cloning\<close> is imported for \<open>cauchy_schwarz_ineq\<close>; its simp rules (e.g.\ \<open>v = w\<close> from
inner products) slow simp on every vector equation.\<close>

declare cauchy_schwarz_eq [simp del] cauchy_schwarz_col [simp del] eq_from_inner_prod [simp del]

section \<open>Preliminaries: linear-space isomorphisms\<close>

text \<open>Matrix spaces are represented by carrier predicates on the single type
\<^typ>\<open>complex Matrix.mat\<close>.  The record below packages a carrier with its zero,
addition and scalar multiplication, so that statements such as
$L(\Hil_A)\otimes L(\Hil_B)\cong L(\Hil_A\otimes\Hil_B)$ (Day 15) can be made as explicit
linear isomorphisms with explicit inverses.\<close>

record ('a, 'v) linear_structure =
  ls_carrier :: "'v set"
  ls_zero :: "'v"
  ls_add :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"
  ls_smul :: "'a \<Rightarrow> 'v \<Rightarrow> 'v"

definition linear_structure_map ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "linear_structure_map V W f \<equiv>
     f (ls_zero V) = ls_zero W \<and>
     (\<forall>x \<in> ls_carrier V. f x \<in> ls_carrier W) \<and>
     (\<forall>x \<in> ls_carrier V. \<forall>y \<in> ls_carrier V.
        f (ls_add V x y) = ls_add W (f x) (f y)) \<and>
     (\<forall>c x. x \<in> ls_carrier V \<longrightarrow>
        f (ls_smul V c x) = ls_smul W c (f x))"

definition is_isomorphism_between ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "is_isomorphism_between V W f \<equiv>
     linear_structure_map V W f \<and>
     (\<exists>g. linear_structure_map W V g \<and>
          (\<forall>x \<in> ls_carrier V. g (f x) = x) \<and>
          (\<forall>y \<in> ls_carrier W. f (g y) = y))"

definition is_isomorphic_to ::
  "('a, 'v) linear_structure \<Rightarrow> ('a, 'w) linear_structure \<Rightarrow> bool" where
  "is_isomorphic_to V W \<equiv> \<exists>f. is_isomorphism_between V W f"

lemma is_isomorphism_betweenD_map:
  assumes "is_isomorphism_between V W f"
  shows "linear_structure_map V W f"
  using assms by (simp add: is_isomorphism_between_def)

lemma is_isomorphism_betweenD_inverse:
  assumes "is_isomorphism_between V W f"
  obtains g where "linear_structure_map W V g"
    and "\<And>x. x \<in> ls_carrier V \<Longrightarrow> g (f x) = x"
    and "\<And>y. y \<in> ls_carrier W \<Longrightarrow> f (g y) = y"
  using assms by (auto simp: is_isomorphism_between_def)

definition mat_linear_structure :: "nat \<Rightarrow> nat \<Rightarrow> (complex, complex Matrix.mat) linear_structure" where
  "mat_linear_structure m n \<equiv>
     \<lparr> ls_carrier = carrier_mat m n,
       ls_zero = 0\<^sub>m m n,
       ls_add = (\<lambda>x y. x + y),
       ls_smul = (\<lambda>c x. c \<cdot>\<^sub>m x) \<rparr>"


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

end
