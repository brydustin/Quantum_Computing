(*  Title:   Basic_Math.thy
    Author:  Dustin Bryant, after Vern Paulsen's lectures of 22 and 24 August 2011 (Days 1-2)
*)



theory Basic_Math
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

section \<open>Day 2 (24 August 2011): bases, matrix units, trace, projections\<close>

text \<open>\begin{notesdef}[Examples]
$\C^n$ has the orthonormal basis $e_1,\dots,e_n$ and every $x$ satisfies
$x=\sum_i x_i e_i=\sum_i\braket{e_i}{x}e_i$.  The \emph{matrix units} $E_{ij}$ (entry $1$ in
position $(i,j)$, $0$ elsewhere) form an orthonormal basis of $M_{n,m}$, and
\[ X=\sum_{i,j}X_{ij}E_{ij}=\sum_{i,j}\langle E_{ij}|X\rangle E_{ij}. \]
\end{notesdef}
Formally \<open>E\<lbrakk>i,j ; m,n\<rbrakk>\<close> is the $m\times n$ matrix unit (indices first,
dimensions second).  The notes also recall the conjugate $\overline X$, the transpose
$X^t$, the adjoint $X^*=\overline{X}^{\,t}$ (written $X^\dagger$ by physicists, formally
\<^term>\<open>X\<^sup>\<dagger>\<close>) and the row-times-column rule for matrix products; these are library
notions.\<close>

definition mat_unit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "mat_unit i j m n = Matrix.mat m n (\<lambda>(r,c). if r = i \<and> c = j then 1 else 0)"

notation mat_unit ("E\<lbrakk>_,_ ; _,_\<rbrakk>" [1000, 1000, 1000, 1000] 999)

lemma mat_unit_carrier [simp]: "E\<lbrakk>i,j ; m,n\<rbrakk> \<in> carrier_mat m n"
  by (simp add: mat_unit_def)

lemma mat_unit_dim_row [simp]:
  fixes i j m n :: nat
  shows "dim_row (E\<lbrakk>i,j ; m,n\<rbrakk>) = m"
  by (simp add: mat_unit_def)

lemma mat_unit_dim_col [simp]:
  fixes i j m n :: nat
  shows "dim_col (E\<lbrakk>i,j ; m,n\<rbrakk>) = n"
  by (simp add: mat_unit_def)

lemma mat_unit_index [simp]:
  assumes "r < m" and "c < n"
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,c) = (if r = i \<and> c = j then 1 else 0)"
  using assms by (simp add: mat_unit_def)


text \<open>Pairing with $E_{ij}$ extracts the $(i,j)$ entry: the matrix analogue of
$\braket{e_i}{v}=v_i$.\<close>

lemma hs_inner_prod_mat_unit_left:
  assumes "i < dim_row x" and "j < dim_col x"
  shows "\<langle>\<langle> E\<lbrakk>i,j ; (dim_row x), (dim_col x)\<rbrakk> | x \<rangle>\<rangle> = x $$ (i,j)"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> =
        (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          cnj (E\<lbrakk>i,j ; ?m,?n\<rbrakk> $$ (r,c)) * x $$ (r,c))"
    by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          cnj (if r = i \<and> c = j then 1 else 0) * x $$ (r,c))"
    by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. \<Sum>c \<in> {0..<?n}.
          (if r = i \<and> c = j then x $$ (r,c) else 0))"
    by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>r \<in> {0..<?m}. if r = i then x $$ (i,j) else 0)"
  proof (intro sum.cong refl)
    fix r
    assume hr: "r \<in> {0..<?m}"
    show "(\<Sum>c \<in> {0..<?n}. if r = i \<and> c = j then x $$ (r,c) else 0) =
          (if r = i then x $$ (i,j) else 0)"
    proof (cases "r = i")
      case True
      then have "(\<Sum>c \<in> {0..<?n}. if r = i \<and> c = j then x $$ (r,c) else 0) =
                 (\<Sum>c \<in> {0..<?n}. if c = j then x $$ (i,j) else 0)"
        by (intro sum.cong) auto
      also have "\<dots> = x $$ (i,j)"
      proof -
        have "(\<Sum>c \<in> {0..<?n}. if c = j then x $$ (i,j) else 0) =
              (\<Sum>c \<in> {0..<?n}. (if c = j then 1 else 0) * x $$ (i,j))"
          by (intro sum.cong) auto
        also have "\<dots> = (\<Sum>c \<in> {0..<?n}. if c = j then 1 else 0) * x $$ (i,j)"
          by (metis sum_distrib_right)
        also have "(\<Sum>c \<in> {0..<?n}. if c = j then 1 else (0::complex)) = 1"
          using assms(2) by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  also have "\<dots> = x $$ (i,j)"
  proof -
    have "(\<Sum>r \<in> {0..<?m}. if r = i then x $$ (i,j) else 0) =
          (\<Sum>r \<in> {0..<?m}. (if r = i then 1 else 0) * x $$ (i,j))"
      by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>r \<in> {0..<?m}. if r = i then 1 else 0) * x $$ (i,j)"
      by (metis sum_distrib_right)
    also have "(\<Sum>r \<in> {0..<?m}. if r = i then 1 else (0::complex)) = 1"
      using assms(1) by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis.
qed



lemma mat_unit_orthonormal:
  assumes i_lt: "i < m"
      and j_lt: "j < n"
      and k_lt: "k < m"
      and l_lt: "l < n"
  shows "\<langle>\<langle> E\<lbrakk>i,j ; m,n\<rbrakk> | E\<lbrakk>k,l ; m,n\<rbrakk> \<rangle>\<rangle> =
         (if i = k \<and> j = l then 1 else 0)"
  by (metis hs_inner_prod_mat_unit_left i_lt j_lt mat_unit_dim_col mat_unit_dim_row mat_unit_index)



text \<open>Expansion in the basis $\{E_{ij}\}$, stated entrywise because matrices of
different dimensions cannot be added in the library.\<close>

lemma mat_unit_expansion:
  assumes "r < dim_row x" and "c < dim_col x"
  shows "x $$ (r,c) =
         (\<Sum>i \<in> {0..<dim_row x}. \<Sum>j \<in> {0..<dim_col x}.
            x $$ (i,j) * (mat_unit i j (dim_row x) (dim_col x)) $$ (r,c))"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "(\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)) =
        (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (if i = r \<and> j = c then 1 else 0))"
    using assms by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
                    (if i = r \<and> j = c then x $$ (i,j) else 0))"
    by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>i \<in> {0..<?m}. if i = r then x $$ (r,c) else 0)"
  proof (intro sum.cong refl)
    fix i
    assume hi: "i \<in> {0..<?m}"
    show "(\<Sum>j \<in> {0..<?n}. if i = r \<and> j = c then x $$ (i,j) else 0) =
          (if i = r then x $$ (r,c) else 0)"
    proof (cases "i = r")
      case True
      then have "(\<Sum>j \<in> {0..<?n}. if i = r \<and> j = c then x $$ (i,j) else 0) =
                 (\<Sum>j \<in> {0..<?n}. if j = c then x $$ (r,j) else 0)"
        by (intro sum.cong) auto
      also have "\<dots> = x $$ (r,c)"
      proof -
        have "(\<Sum>j \<in> {0..<?n}. if j = c then x $$ (r,j) else 0) =
              (\<Sum>j \<in> {0..<?n}. (if j = c then 1 else 0) * x $$ (r,c))"
          by (intro sum.cong) auto
        also have "\<dots> = (\<Sum>j \<in> {0..<?n}. if j = c then 1 else 0) * x $$ (r,c)"
          by (metis sum_distrib_right)
        also have "(\<Sum>j \<in> {0..<?n}. if j = c then 1 else (0::complex)) = 1"
          using assms(2) by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  also have "\<dots> = x $$ (r,c)"
  proof -
    have "(\<Sum>i \<in> {0..<?m}. if i = r then x $$ (r,c) else 0) =
          (\<Sum>i \<in> {0..<?m}. (if i = r then 1 else 0) * x $$ (r,c))"
      by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>i \<in> {0..<?m}. if i = r then 1 else 0) * x $$ (r,c)"
      by (metis sum_distrib_right)
    also have "(\<Sum>i \<in> {0..<?m}. if i = r then 1 else (0::complex)) = 1"
      using assms(1) by simp
    finally show ?thesis by simp
  qed
  finally show ?thesis by simp
qed



lemma mat_unit_hs_expansion:
  assumes "r < dim_row x" and "c < dim_col x"
  shows "x $$ (r,c) =
         (\<Sum>i \<in> {0..<dim_row x}. \<Sum>j \<in> {0..<dim_col x}.
            \<langle>\<langle> mat_unit i j (dim_row x) (dim_col x) | x \<rangle>\<rangle> *
            (mat_unit i j (dim_row x) (dim_col x)) $$ (r,c))"
proof -
  let ?m = "dim_row x"
  let ?n = "dim_col x"

  have "(\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          \<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)) =
        (\<Sum>i \<in> {0..<?m}. \<Sum>j \<in> {0..<?n}.
          x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c))"
  proof (intro sum.cong refl)
    fix i
    assume hi: "i \<in> {0..<?m}"
    fix j
    assume hj: "j \<in> {0..<?n}"
    have "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> = x $$ (i,j)"
      using hi hj
      by (simp add: hs_inner_prod_mat_unit_left)
    then show "\<langle>\<langle> E\<lbrakk>i,j ; ?m,?n\<rbrakk> | x \<rangle>\<rangle> * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c) =
               x $$ (i,j) * (E\<lbrakk>i,j ; ?m,?n\<rbrakk>) $$ (r,c)"
      by simp
  qed
  also have "\<dots> = x $$ (r,c)"
    using mat_unit_expansion[OF assms] by simp
  finally show ?thesis by simp
qed

subsection \<open>The trace\<close>

text \<open>\begin{notesdef}
$\Tr:M_{n,n}\to\C$, $\Tr(X)=\sum_{i=1}^n x_{ii}$; we sometimes write $\Tr_n$.
\end{notesdef}
The formal \<open>Tr\<close> sums the diagonal of any matrix.  On matrix units, $\Tr(E_{ii})=1$
and $\Tr(E_{ij})=0$ for $i\neq j$, so the trace is the sum of the diagonal
Hilbert--Schmidt coefficients.\<close>

definition Tr :: "complex Matrix.mat \<Rightarrow> complex" where
  "Tr x = (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0)"

lemma Tr_mat_unit:
  assumes i_lt: "i < m"
      and j_lt: "j < n"
  shows "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) = (if i = j then 1 else 0)"
proof (cases "i = j")
  case True
  have "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) =
        (\<Sum>r<m. if r < n then (E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r<m. if r < n then (if r = i \<and> r = j then 1 else 0) else 0)"
    by (intro sum.cong refl) simp
  also have "... = (\<Sum>r<m. if r = i then 1 else 0)"
    by (metis True j_lt)  
  also have "... = 1"
    using i_lt by simp
  finally show ?thesis
    using True by simp
next
  case False
  have "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) =
        (\<Sum>r<m. if r < n then (E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r<m. if r < n then (if r = i \<and> r = j then 1 else 0) else 0)"
    by (intro sum.cong refl) simp
  also have "... = 0"
    by (simp add: False sum.neutral)
  finally show ?thesis
    using False by simp
qed

corollary Tr_mat_unit_diag:
  assumes "i < n"
  shows "Tr (E\<lbrakk>i,i ; n,n\<rbrakk>) = 1"
  using assms by (simp add: Tr_mat_unit)

corollary Tr_mat_unit_offdiag:
  assumes "i < m" and "j < n" and "i \<noteq> j"
  shows "Tr (E\<lbrakk>i,j ; m,n\<rbrakk>) = 0"
  by (simp add: Tr_mat_unit assms)



lemma Tr_hs_diagonal_sum:
  shows "Tr x =
         (\<Sum>r < dim_row x.
            if r < dim_col x
            then \<langle>\<langle> E\<lbrakk>r,r ; (dim_row x), (dim_col x)\<rbrakk> | x \<rangle>\<rangle>
            else 0)"
  by (smt (verit, ccfv_threshold) Tr_def hs_inner_prod_mat_unit_left lessThan_iff sum.cong)

corollary Tr_hs_diagonal_sum_square:
  assumes rows: "dim_row x = n"
      and cols: "dim_col x = n"
  shows "Tr x = (\<Sum>r<n. \<langle>\<langle> E\<lbrakk>r,r ; n,n\<rbrakk> | x \<rangle>\<rangle>)"
proof -
  have "Tr x = (\<Sum>r<n. x $$ (r,r))"
    using rows cols by (simp add: Tr_def)
  also have "... = (\<Sum>r<n. \<langle>\<langle> E\<lbrakk>r,r ; n,n\<rbrakk> | x \<rangle>\<rangle>)"
    by (intro sum.cong refl, metis cols hs_inner_prod_mat_unit_left lessThan_iff rows)
  finally show ?thesis.
qed


text \<open>The trace is linear.\<close>

lemma Tr_add:
  assumes rows: "dim_row x = dim_row y"
      and cols: "dim_col x = dim_col y"
  shows "Tr (x + y) = Tr x + Tr y"
proof -
  have "Tr (x + y) =
        (\<Sum>r < dim_row x. if r < dim_col x then (x + y) $$ (r,r) else 0)"
    using rows cols by (simp add: Tr_def)
  also have "... =
        (\<Sum>r < dim_row x.
           (if r < dim_col x then x $$ (r,r) else 0) +
           (if r < dim_col x then y $$ (r,r) else 0))"
    by (intro sum.cong refl, simp add: cols rows)
  also have "... =
        (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0) +
        (\<Sum>r < dim_row x. if r < dim_col x then y $$ (r,r) else 0)"
    by (simp add: sum.distrib)
  also have "... = Tr x + Tr y"
    using rows cols by (simp add: Tr_def)
  finally show ?thesis.
qed


lemma Tr_smult: "Tr (a \<cdot>\<^sub>m x) = a * Tr x"
proof -
  have "Tr (a \<cdot>\<^sub>m x) =
        (\<Sum>r < dim_row x. if r < dim_col x then (a \<cdot>\<^sub>m x) $$ (r,r) else 0)"
    by (simp add: Tr_def)
  also have "... =
        (\<Sum>r < dim_row x. a * (if r < dim_col x then x $$ (r,r) else 0))"
    by (intro sum.cong refl) simp
  also have "... =
        a * (\<Sum>r < dim_row x. if r < dim_col x then x $$ (r,r) else 0)"
    by (simp add: sum_distrib_left)
  also have "... = a * Tr x"
    by (simp add: Tr_def)
  finally show ?thesis.
qed

corollary Tr_uminus: "Tr (- x) = - Tr x"
  by (smt (verit, ccfv_threshold) Tr_add add_cancel_right_right add_eq_0_iff carrier_mat_triv 
      index_uminus_mat(2,3) index_zero_mat(2,3)
      right_add_zero_mat uminus_l_inv_mat uminus_uminus_mat)



corollary Tr_diff:
  assumes rows: "dim_row x = dim_row y"
      and cols: "dim_col x = dim_col y"
  shows "Tr (x - y) = Tr x - Tr y"
proof -
  have "Tr (x - y) = Tr (x + (- y))"
    by (metis carrier_mat_triv cols minus_add_uminus_mat rows)
  also have "... = Tr x + Tr (- y)"
    using rows cols by (intro Tr_add) simp_all
  also have "... = Tr x - Tr y"
    by (simp add: Tr_uminus)
  finally show ?thesis.
qed


lemma Tr_zero_mat [simp]:
  shows "Tr (Matrix.mat m n (\<lambda>(r,c). 0)) = 0"
  by (simp add: Tr_def, simp add: sum.neutral)

subsection \<open>Matrix-unit algebra and cyclicity of the trace\<close>

text \<open>$E_{ij}^*=E_{ji}$, $E_{ij}E_{kl}=\delta_{jk}E_{il}$, $\Tr(AB)=\Tr(BA)$,
$\Tr(U^*AU)=\Tr(A)$ for unitary $U$, and $\langle A|B\rangle=\Tr(A^*B)$: the facts about the
trace that the notes use from Day 3 onwards.\<close>

lemma mat_unit_dagger:
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk>)\<^sup>\<dagger> = E\<lbrakk>j,i ; n,m\<rbrakk>"
  by (rule eq_matI, simp_all, simp add: dagger_def)



lemma mat_unit_mult_entry:
  assumes r_lt: "r < m"
      and c_lt: "c < p"
      and j_lt: "j < n"
  shows "(E\<lbrakk>i,j ; m,n\<rbrakk> * E\<lbrakk>k,l ; n,p\<rbrakk>) $$ (r,c) =
         (if j = k \<and> r = i \<and> c = l then 1 else 0)"  
proof -
  have "(E\<lbrakk>i,j ; m,n\<rbrakk> * E\<lbrakk>k,l ; n,p\<rbrakk>) $$ (r,c) =
        (\<Sum>t<n. (E\<lbrakk>i,j ; m,n\<rbrakk>) $$ (r,t) * (E\<lbrakk>k,l ; n,p\<rbrakk>) $$ (t,c))"
    using r_lt c_lt by simp
  also have "... =
        (\<Sum>t<n. (if r = i \<and> t = j then 1 else 0) *
               (if t = k \<and> c = l then 1 else 0))"
    using r_lt c_lt by (intro sum.cong refl) simp
  also have "... =
        (if r = i \<and> c = l
         then (\<Sum>t<n. (if t = j then 1 else 0) * (if t = k then 1 else 0))
         else 0)"
    by fastforce
  also have "... = (if r = i \<and> c = l then (if j = k then 1 else 0) else 0)"
    by (smt (verit) Tr_hs_diagonal_sum Tr_mat_unit_diag j_lt lambda_one lambda_zero mat_unit_dim_col
        mat_unit_dim_row mat_unit_orthonormal sum.cong sum.not_neutral_contains_not_neutral)
  also have "... = (if j = k \<and> r = i \<and> c = l then 1 else 0)"
    by auto
  finally show ?thesis.
qed


lemma Tr_cyclic:
  assumes AB: "dim_col A = dim_row B"
      and BA: "dim_row A = dim_col B"
  shows "Tr (A * B) = Tr (B * A)"
proof -
  let ?m = "dim_row A"
  let ?n = "dim_col A"

  have "Tr (A * B) = (\<Sum>i<?m. (A * B) $$ (i,i))"
    using AB BA by (simp add: Tr_def)
  also have "... = (\<Sum>i<?m. \<Sum>k<?n. A $$ (i,k) * B $$ (k,i))"
    using AB BA by (intro sum.cong refl, simp)
  also have "... = (\<Sum>k<?n. \<Sum>i<?m. A $$ (i,k) * B $$ (k,i))"
    by (rule sum.swap)
  also have "... = (\<Sum>k<?n. \<Sum>i<?m. B $$ (k,i) * A $$ (i,k))"
  proof (rule sum.cong[OF refl])
    fix k
    assume "k \<in> {..<dim_col A}"
    then have k_lt: "k < ?n"
      by (metis lessThan_iff)

    show "(\<Sum>i<?m. A $$ (i,k) * B $$ (k,i)) =
          (\<Sum>i<?m. B $$ (k,i) * A $$ (i,k))"
      by (metis mult.commute)
  qed
  also have "... = (\<Sum>k<?n. (B * A) $$ (k,k))"
    using AB BA by (intro sum.cong refl, simp add:  mult.commute)
  also have "... = Tr (B * A)"
    using AB BA by (simp add: Tr_def)
  finally show ?thesis.
qed

lemma Tr_unitary_conjugation:
  assumes Uu: "unitary U"
      and Arow: "dim_row A = dim_row U"
      and Acol: "dim_col A = dim_row U"
  shows "Tr ((U\<^sup>\<dagger>) * A * U) = Tr(A)"
proof -
  have "Tr ((U\<^sup>\<dagger>) * A * U) = Tr (U * ((U\<^sup>\<dagger>) * A))"
    by (metis Acol Tr_cyclic dim_row_of_dagger index_mult_mat(2,3))
  also have "... = Tr (((1\<^sub>m (dim_row U)) * A))"
    by (smt (verit, ccfv_SIG) Arow Uu assoc_mult_mat carrier_mat_triv dagger_of_dagger_is_id dim_row_of_dagger unitary_def)
  finally show ?thesis
    by (metis Arow left_mult_one_mat')
qed


lemma hs_inner_prod_as_trace:
  assumes rows: "dim_row A = dim_row B"
      and cols: "dim_col A = dim_col B"
  shows "\<langle>\<langle> A | B \<rangle>\<rangle> = Tr ((A\<^sup>\<dagger>) * B)"
proof -
  let ?m = "dim_row A" and ?n = "dim_col A"
  have "\<langle>\<langle> A | B \<rangle>\<rangle> = (\<Sum>i<?m. \<Sum>j<?n. cnj (A $$ (i,j)) * B $$ (i,j))"
    using rows cols by (simp add: hs_inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>j<?n. \<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<?n. (A\<^sup>\<dagger> * B) $$ (j,j))"
  proof (intro sum.cong refl)
    fix j 
    assume "j \<in> {..<?n}"
    then have j_lt: "j < ?n" by simp
    have "(A\<^sup>\<dagger> * B) $$ (j,j) = (\<Sum>i<?m. (A\<^sup>\<dagger>) $$ (j,i) * B $$ (i,j))"
      using j_lt rows cols by simp
    also have "\<dots> = (\<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j))"
      by (intro sum.cong refl, metis dagger_def index_mat(1) j_lt lessThan_iff old.prod.case)
    finally show "(\<Sum>i<?m. cnj (A $$ (i,j)) * B $$ (i,j)) = (A\<^sup>\<dagger> * B) $$ (j,j)"
      by simp
  qed
  also have "\<dots> = Tr (A\<^sup>\<dagger> * B)"
    using rows cols by (simp add: Tr_def)
  finally show ?thesis.
qed

corollary hs_inner_prod_self_as_trace:
  shows "\<langle>\<langle> A | A \<rangle>\<rangle> = Tr ((A\<^sup>\<dagger>) * A)"
  by (rule hs_inner_prod_as_trace) simp_all

subsection \<open>Orthogonal projections and Parseval's identity\<close>

text \<open>\begin{notesdef}[Orthogonal projections]
Let $V\subseteq\C^n$ be a subspace with orthonormal basis $\{v_1,\dots,v_k\}$ and put
$P=\sum_{i=1}^k\ketbra{v_i}{v_i}$.  Then $Px=\sum_i\braket{v_i}{x}v_i\in V$ and
$x-Px\perp V$, so every $x\in\C^n$ is uniquely $x=v+w$ with $v\in V$ and $w\in V^\perp$.
Consequently $P$ does not depend on the orthonormal basis chosen for $V$, $Pv=v$ for
$v\in V$, $P^2=P$ and $P=P^*$: $P$ is \emph{the} orthogonal projection onto $V$.
\end{notesdef}

\begin{notestheorem}[Parseval]
If $\{v_1,\dots,v_k\}$ is an orthonormal basis of $V$ and $v\in V$, then
$\norm{v}^2=\sum_{i=1}^k|\braket{v_i}{v}|^2$.  For $V=\C^n$ this holds for every $v$.
\end{notestheorem}

\begin{notestheorem}
If $P\in M_n$ satisfies $P^2=P$ and $P=P^*$, and $V=\range(P)$, then $P$ is the orthogonal
projection onto $V$.
\end{notestheorem}

Formally, an orthonormal list \<open>vs\<close> of vectors in $\C^n$ is \<^term>\<open>orthonormal_list n vs\<close>,
the matrix with columns $v_1,\dots,v_k$ is \<^term>\<open>mat_of_cols n vs\<close>, and
$P=\sum_i\ketbra{v_i}{v_i}=VV^\dagger$ is \<^term>\<open>outer_sum n vs\<close>.  The results below are the
projection formula, $V^\dagger V=I_k$, the completeness relation $VV^\dagger=I_n$ for a full
basis, $P=P^\dagger$, $P^2=P$, Parseval, the orthogonality of the residual, and the uniqueness
of the decomposition.  Independence of $P$ from the basis is \<open>outer_sum_basis_independent\<close> in
theory Day02\_11\_Supplement; the characterisation of Hermitian idempotents as orthogonal projections is
\<open>projection_annihilates_orthogonal\<close> in theory Quantum\_Computing11.\<close>




definition orthonormal_list :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> bool" where
  "orthonormal_list n vs \<equiv>
     (\<forall>v \<in> set vs. dim_vec v = n) \<and>
     (\<forall>i < length vs. \<forall>j < length vs.
        \<langle>vs ! i | vs ! j\<rangle> = (if i = j then 1 else 0))"

lemma orthonormal_listD_dim:
  assumes "orthonormal_list n vs" and "i < length vs"
  shows "dim_vec (vs ! i) = n"
  using assms by (simp add: orthonormal_list_def)

lemma orthonormal_listD_inner:
  assumes "orthonormal_list n vs" and "i < length vs" and "j < length vs"
  shows "\<langle>vs ! i | vs ! j\<rangle> = (if i = j then 1 else 0)"
  using assms by (simp add: orthonormal_list_def, force)

lemma orthonormal_listD_carrier:
  assumes "orthonormal_list n vs"
  shows "set vs \<subseteq> carrier_vec n"
  using assms orthonormal_list_def by auto



definition outer_sum :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> complex Matrix.mat" where
  "outer_sum n vs = mat_of_cols n vs * ((mat_of_cols n vs)\<^sup>\<dagger>)"

lemma outer_sum_dim_row [simp]: "dim_row (outer_sum n vs) = n"
  by (simp add: outer_sum_def)

lemma outer_sum_dim_col [simp]: "dim_col (outer_sum n vs) = n"
  by (simp add: outer_sum_def)

lemma outer_sum_hermitian:
  shows "(outer_sum n vs)\<^sup>\<dagger> = outer_sum n vs"
  unfolding outer_sum_def
  by (simp add: dagger_of_prod dagger_of_dagger_is_id)



lemma cols_mat_dagger_left:
  assumes orth: "orthonormal_list n vs"
  shows "(mat_of_cols n vs)\<^sup>\<dagger> * (mat_of_cols n vs) = 1\<^sub>m (length vs)"
proof (rule eq_matI)
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  show "dim_row (?V\<^sup>\<dagger> * ?V) = dim_row (1\<^sub>m ?k)" by simp
  show "dim_col (?V\<^sup>\<dagger> * ?V) = dim_col (1\<^sub>m ?k)" by simp
  fix l1 l2
  assume "l1 < dim_row (1\<^sub>m ?k)" and "l2 < dim_col (1\<^sub>m ?k)"
  then have l12: "l1 < ?k" "l2 < ?k" by simp_all

  have dim1: "dim_vec (vs ! l1) = n" using orth l12(1) by (simp add: orthonormal_listD_dim)
  have dim2: "dim_vec (vs ! l2) = n" using orth l12(2) by (simp add: orthonormal_listD_dim)

  have "(?V\<^sup>\<dagger> * ?V) $$ (l1,l2) = (\<Sum>i<n. (?V\<^sup>\<dagger>) $$ (l1,i) * ?V $$ (i,l2))"
    using l12 by simp
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l1) $ i) * (vs ! l2) $ i)"
    using l12 dim1 dim2 by (intro sum.cong refl)
       (simp add: dagger_def mat_of_cols_def)
  also have "\<dots> = \<langle>vs ! l1 | vs ! l2\<rangle>"
    using dim1 dim2 by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (if l1 = l2 then 1 else 0)"
    using orth l12 by (simp add: orthonormal_listD_inner)
  also have "\<dots> = (1\<^sub>m ?k) $$ (l1,l2)"
    using l12 by simp
  finally show "(?V\<^sup>\<dagger> * ?V) $$ (l1,l2) = (1\<^sub>m ?k) $$ (l1,l2)" .
qed



lemma cols_mat_dagger_right:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
  shows "(mat_of_cols n vs) * ((mat_of_cols n vs)\<^sup>\<dagger>) = 1\<^sub>m n"
proof -
  let ?V = "mat_of_cols n vs"
  have left: "?V\<^sup>\<dagger> * ?V = 1\<^sub>m n"
    using cols_mat_dagger_left[OF orth] full by simp
  then have "inverts_mat (?V\<^sup>\<dagger>) ?V"
    by (simp add: full inverts_mat_def)
  then have "inverts_mat ?V (?V\<^sup>\<dagger>)"
    by (metis dim_col_of_dagger full inverts_mat_sym
        mat_of_cols_carrier(2,3) square_mat.elims(3))
  then show ?thesis
    by (simp add: inverts_mat_def full)
qed



lemma completeness_relation:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "(\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)) = (if i = j then 1 else 0)"
proof -
  let ?V = "mat_of_cols n vs"
  have "(?V * (?V\<^sup>\<dagger>)) $$ (i,j) = (\<Sum>l<n. ?V $$ (i,l) * (?V\<^sup>\<dagger>) $$ (l,j))"
    using i_lt j_lt full by simp
  also have "\<dots> = (\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j))"
    using i_lt j_lt full
    by (intro sum.cong refl, simp add: mat_of_cols_def dagger_def orthonormal_listD_dim[OF orth])
  finally have sum_eq: "(\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)) = (?V * (?V\<^sup>\<dagger>)) $$ (i,j)"
    by simp
  also have "(?V * (?V\<^sup>\<dagger>)) $$ (i,j) = (1\<^sub>m n) $$ (i,j)"
    by (simp add: cols_mat_dagger_right full orth)
  also have "\<dots> = (if i = j then 1 else 0)"
    using i_lt j_lt by simp
  finally show ?thesis using sum_eq by simp
qed



lemma outer_sum_index:
  assumes orth: "orthonormal_list n vs"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "(outer_sum n vs) $$ (i,j) = 
         (\<Sum>l < length vs. (vs ! l) $ i * cnj ((vs ! l) $ j))"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  have "(outer_sum n vs) $$ (i,j) = (?V * (?V\<^sup>\<dagger>)) $$ (i,j)"
    by (simp add: outer_sum_def)
  also have "\<dots> = (\<Sum>l<?k. ?V $$ (i,l) * (?V\<^sup>\<dagger>) $$ (l,j))"
    using i_lt j_lt by (simp add: outer_sum_def)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j))"
    using i_lt j_lt
    by (intro sum.cong refl)
       (simp add: mat_of_cols_def dagger_def orthonormal_listD_dim[OF orth])
  finally show ?thesis.
qed



lemma outer_sum_apply:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and i_lt: "i < n"
  shows "(outer_sum n vs *\<^sub>v x) $ i =  (\<Sum>l < length vs. \<langle>vs ! l | x\<rangle> * (vs ! l) $ i)"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  have "(outer_sum n vs *\<^sub>v x) $ i = Matrix.row (outer_sum n vs) i \<bullet> x"
    using i_lt xdim by simp
  also have "\<dots> = (\<Sum>j<n. (outer_sum n vs) $$ (i,j) * x $ j)"
    using i_lt xdim  lessThan_atLeast0 by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>j<n. (\<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j)) * x $ j)"
    by (intro sum.cong refl, simp add: outer_sum_index[OF orth i_lt])
  also have "\<dots> = (\<Sum>j<n. \<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j) * x $ j)"
    by (intro sum.cong refl) (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>l<?k. \<Sum>j<n. (vs ! l) $ i * cnj ((vs ! l) $ j) * x $ j)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * (\<Sum>j<n. cnj ((vs ! l) $ j) * x $ j))"
    by (intro sum.cong refl, 
        metis (mono_tags, lifting) semigroup_mult_class.mult.assoc sum.cong sum_distrib_left)
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * \<langle>vs ! l | x\<rangle>)"
    using atLeast0LessThan inner_prod_def xdim by (intro sum.cong refl, presburger)   
  also have "\<dots> = (\<Sum>l<?k. \<langle>vs ! l | x\<rangle> * (vs ! l) $ i)"
    by (intro sum.cong refl) (simp add: mult.commute)
  finally show ?thesis.
qed



lemma outer_sum_idempotent:
  assumes orth: "orthonormal_list n vs"
  shows "outer_sum n vs * outer_sum n vs = outer_sum n vs"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"

  have "outer_sum n vs * outer_sum n vs = (?V * (?V\<^sup>\<dagger>)) * (?V * (?V\<^sup>\<dagger>))"
    by (simp add: outer_sum_def)
  also have "\<dots> = ?V * ((?V\<^sup>\<dagger>) * ?V) * (?V\<^sup>\<dagger>)"
    by (metis (no_types, lifting) assoc_mult_mat carrier_mat_triv dim_col_of_dagger 
        dim_row_of_dagger mat_of_cols_carrier(2) outer_sum_def outer_sum_dim_col)
  also have "\<dots> = ?V * (1\<^sub>m ?k) * (?V\<^sup>\<dagger>)"
    using cols_mat_dagger_left[OF orth] by simp
  also have "\<dots> = ?V * (?V\<^sup>\<dagger>)"
    by simp
  also have "\<dots> = outer_sum n vs"
    by (simp add: outer_sum_def)
  finally show ?thesis .
qed



lemma parseval:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and vdim: "dim_vec v = n"
      and i_lt: "i < n"
  shows "v $ i = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i)"
proof -
  have "(\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i) =
        (\<Sum>l<n. (\<Sum>j<n. cnj ((vs ! l) $ j) * v $ j) * (vs ! l) $ i)"
    using atLeast0LessThan inner_prod_def vdim by (intro sum.cong refl, simp)   
  also have "\<dots> = (\<Sum>l<n. \<Sum>j<n. cnj ((vs ! l) $ j) * v $ j * (vs ! l) $ i)"
    by (intro sum.cong refl, simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>j<n. \<Sum>l<n. cnj ((vs ! l) $ j) * v $ j * (vs ! l) $ i)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j<n. v $ j * (\<Sum>l<n. (vs ! l) $ i * cnj ((vs ! l) $ j)))"
    by (intro sum.cong refl)
       (simp add: sum_distrib_left mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>j<n. v $ j * (if i = j then 1 else 0))"
    using orth full i_lt by (intro sum.cong refl, simp add: completeness_relation)
  also have "... = (\<Sum>j<n. if j = i then v $ j else 0)"
    by (intro sum.cong refl) auto
  also have "\<dots> = v $ i"
    using i_lt by simp
  finally show ?thesis 
    by simp
qed


corollary parseval_norm:
  assumes orth: "orthonormal_list n vs"
      and full: "length vs = n"
      and vdim: "dim_vec v = n"
  shows "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>l<n. (cmod (\<langle>vs ! l | v\<rangle>))\<^sup>2)"
proof -
  have "\<parallel>v\<parallel>\<^sup>2 = \<langle>v|v\<rangle>"
    using cpx_vec_length_inner_prod by presburger
  also have "\<dots> = (\<Sum>i<n. cnj (v $ i) * v $ i)"
    using vdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj (v $ i) * (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (vs ! l) $ i))"
    using orth full vdim by (intro sum.cong refl arg_cong[where f = "\<lambda>s. cnj (v $ _) * s"], 
        simp add: parseval) 
  also have "\<dots> = (\<Sum>i<n. \<Sum>l<n. cnj (v $ i) * (\<langle>vs ! l | v\<rangle> * (vs ! l) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i<n. \<Sum>l<n. \<langle>vs ! l | v\<rangle> * (cnj (v $ i) * (vs ! l) $ i))"
    by (intro sum.cong refl, simp add: mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>l<n. \<Sum>i<n. \<langle>vs ! l | v\<rangle> * (cnj (v $ i) * (vs ! l) $ i))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * (\<Sum>i<n. cnj (v $ i) * (vs ! l) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * \<langle>v | vs ! l\<rangle>)"
    using atLeast0LessThan full inner_prod_def orth orthonormal_listD_dim by force
  also have "\<dots> = (\<Sum>l<n. \<langle>vs ! l | v\<rangle> * cnj (\<langle>vs ! l | v\<rangle>))"
    by (simp add: full inner_prod_cnj orth orthonormal_listD_dim vdim)    
  also have "\<dots> = (\<Sum>l<n. (cmod (\<langle>vs ! l | v\<rangle>))\<^sup>2)"
    using complex_norm_square by force
  finally show ?thesis
    by (meson of_real_eq_iff) 
qed

text \<open>The residual $x-Px$ is orthogonal to every $v_l$, because
$\braket{v_l}{Px}=\braket{v_l}{x}$; hence the orthogonal decomposition $x=Px+(x-Px)$.\<close>



lemma inner_prod_outer_sum:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and l_lt: "l < length vs"
  shows "\<langle>vs ! l | outer_sum n vs *\<^sub>v x\<rangle> = \<langle>vs ! l | x\<rangle>"
proof -
  let ?k = "length vs"
  have ldim: "dim_vec (vs ! l) = n" 
    using orth l_lt by (simp add: orthonormal_listD_dim)
  have Pdim: "dim_vec (outer_sum n vs *\<^sub>v x) = n" 
    using xdim by simp
  have "\<langle>vs ! l | outer_sum n vs *\<^sub>v x\<rangle> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (outer_sum n vs *\<^sub>v x) $ i)"
    using ldim Pdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (vs ! m) $ i))"
    using orth xdim outer_sum_apply 
    by(intro sum.cong refl arg_cong[where f = "\<lambda>s. cnj _ * s"], auto)
  also have "\<dots> = (\<Sum>i<n. \<Sum>m<?k. cnj ((vs ! l) $ i) * (\<langle>vs ! m | x\<rangle> * (vs ! m) $ i))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i<n. \<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (intro sum.cong refl, simp add: mult.assoc mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>m<?k. \<Sum>i<n. \<langle>vs ! m | x\<rangle> * (cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (\<Sum>i<n. cnj ((vs ! l) $ i) * (vs ! m) $ i))"
    by (intro sum.cong refl, simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * \<langle>vs ! l | vs ! m\<rangle>)"
    using atLeast0LessThan inner_prod_def orth orthonormal_listD_dim by auto    
  also have "\<dots> = (\<Sum>m<?k. \<langle>vs ! m | x\<rangle> * (if l = m then 1 else 0))"
    using orth l_lt by (intro sum.cong refl, simp add: orthonormal_listD_inner)
  also have "\<dots> = (\<Sum>m<?k. if m = l then \<langle>vs ! m | x\<rangle> else 0)"
    by (intro sum.cong refl) auto
  also have "\<dots> = \<langle>vs ! l | x\<rangle>"
    using l_lt by simp
  finally show ?thesis.
qed



lemma residual_orthogonal:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and l_lt: "l < length vs"
  shows "\<langle>vs ! l | x - outer_sum n vs *\<^sub>v x\<rangle> = 0"
proof -
  let ?Px = "outer_sum n vs *\<^sub>v x"
  have ldim: "dim_vec (vs ! l) = n" 
    using orth l_lt by (simp add: orthonormal_listD_dim)
  have Pdim: "dim_vec ?Px = n" 
    using xdim by simp
  have diffdim: "dim_vec (x - ?Px) = n" 
    using xdim Pdim by simp
  have "\<langle>vs ! l | x - ?Px\<rangle> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (x - ?Px) $ i)"
    using ldim diffdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * (x $ i - ?Px $ i))"
    using xdim Pdim by (intro sum.cong refl, simp)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * x $ i - cnj ((vs ! l) $ i) * ?Px $ i)"
    by (intro sum.cong refl, simp add: right_diff_distrib)
  also have "\<dots> = (\<Sum>i<n. cnj ((vs ! l) $ i) * x $ i) -
                  (\<Sum>i<n. cnj ((vs ! l) $ i) * ?Px $ i)"
    by (simp add: sum_subtractf)
  also have "\<dots> = \<langle>vs ! l | x\<rangle> - \<langle>vs ! l | ?Px\<rangle>"
    using ldim xdim Pdim by (simp add: inner_prod_def atLeast0LessThan)
  also have "\<dots> = \<langle>vs ! l | x\<rangle> - \<langle>vs ! l | x\<rangle>"
    using inner_prod_outer_sum[OF orth xdim l_lt] by simp
  also have "\<dots> = 0" 
    by simp
  finally show ?thesis.
qed



corollary orthogonal_decomposition:
  assumes xdim: "dim_vec x = n"
  shows "x = outer_sum n vs *\<^sub>v x + (x - outer_sum n vs *\<^sub>v x)"
proof -
  have "dim_vec (outer_sum n vs *\<^sub>v x) = n" 
    using xdim by simp
  then show ?thesis using xdim
    by (intro eq_vecI, auto)
qed

text \<open>Uniqueness: if $x=v+w$ with $Pv=v$ and $w\perp v_l$ for all $l$, then $v=Px$
and $w=x-Px$.\<close>



lemma outer_sum_orthogonal_zero:
  assumes orth: "orthonormal_list n vs"
      and wdim: "dim_vec w = n"
      and ortho: "\<forall>l < length vs. \<langle>vs ! l | w\<rangle> = 0"
  shows "outer_sum n vs *\<^sub>v w = 0\<^sub>v n"
proof (rule eq_vecI)
  show "dim_vec (outer_sum n vs *\<^sub>v w) = dim_vec (0\<^sub>v n)"
    using wdim by simp
next
  fix i assume "i < dim_vec (0\<^sub>v n)"
  then have i_lt: "i < n" by simp
  have "(outer_sum n vs *\<^sub>v w) $ i =
        (\<Sum>l < length vs. \<langle>vs ! l | w\<rangle> * (vs ! l) $ i)"
    using outer_sum_apply[OF orth wdim i_lt] .
  also have "\<dots> = (\<Sum>l < length vs. 0 * (vs ! l) $ i)"
    using ortho by (intro sum.cong refl) simp
  also have "\<dots> = 0" by simp
  finally show "(outer_sum n vs *\<^sub>v w) $ i = (0\<^sub>v n) $ i"
    using i_lt by simp
qed



lemma outer_sum_add:
  assumes vdim: "dim_vec v = n" and wdim: "dim_vec w = n"
  shows "outer_sum n vs *\<^sub>v (v + w) = 
         outer_sum n vs *\<^sub>v v + outer_sum n vs *\<^sub>v w"
proof -
  have "outer_sum n vs \<in> carrier_mat n n"
    by fastforce

  moreover have "v \<in> carrier_vec n" 
    using vdim carrier_vec_dim_vec by blast
  moreover have "w \<in> carrier_vec n" 
    using wdim carrier_vec_dim_vec by blast
  ultimately show ?thesis
    by (simp add: mult_add_distrib_mat_vec)
qed



lemma orthogonal_decomposition_unique:
  assumes orth: "orthonormal_list n vs"
      and xdim: "dim_vec x = n"
      and vdim: "dim_vec v = n"
      and wdim: "dim_vec w = n"
      and decomp: "x = v + w"
      and v_fixed: "outer_sum n vs *\<^sub>v v = v"
      and w_ortho: "\<forall>l < length vs. \<langle>vs ! l | w\<rangle> = 0"
  shows "v = outer_sum n vs *\<^sub>v x" and "w = x - outer_sum n vs *\<^sub>v x"
proof -
  let ?P = "outer_sum n vs"

  have "v = v + 0\<^sub>v n"
    by (simp add: carrier_vecI vdim)
  also have "\<dots> = ?P *\<^sub>v v + ?P *\<^sub>v w"
    using v_fixed outer_sum_orthogonal_zero[OF orth wdim w_ortho] by simp
  also have "\<dots> = ?P *\<^sub>v (v + w)"
    using outer_sum_add[OF vdim wdim] by simp
  also have "\<dots> = ?P *\<^sub>v x"
    using decomp by simp
  finally show Px_eq: "v = ?P *\<^sub>v x".

  have "w = (v + w) - v"
    using vdim wdim by auto
  also have "\<dots> = x - v"
    using decomp by simp
  also have "\<dots> = x - ?P *\<^sub>v x"
    using Px_eq by simp
  finally show "w = x - ?P *\<^sub>v x".
qed


section \<open>Unitary algebra\<close>

text \<open>Library-level consequences of unitarity ($U^\dagger U=I$ and $UU^\dagger=I$ in the
library's definition) used throughout; Paulsen's Day 3 characterisations of unitaries are
in theory Quantum\_Computing\_3\_10.\<close>

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


section \<open>Tensor product infrastructure\<close>

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
