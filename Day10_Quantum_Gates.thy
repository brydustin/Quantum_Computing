(*  Title:   Day10_Quantum_Gates.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 19 September 2011 (Day 10)
*)

theory Day10_Quantum_Gates
  imports Day09_POVMs_Entanglement
begin

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
unitaries (not formalised).  Formally $H$ is \<open>Hadamard\<close> (the library's \<open>Quantum.H\<close>) and
$S$ is \<open>Phase_S\<close>.\<close>

definition Hadamard :: "complex Matrix.mat" where
  "Hadamard \<equiv> Quantum.H"

lemma csqrt_two: "csqrt (2::complex) = (sqrt 2 :: complex)"
  by simp


lemma hadamard_squared:
  "Hadamard * Hadamard = 1\<^sub>m 2"
  by (simp add: Hadamard_def)


lemma hadamard_e0:
  "Hadamard *\<^sub>v unit_vec 2 0 =
   (1 / csqrt 2) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"
  by (rule eq_vecI)
     (auto simp add: Hadamard_def Quantum.H_def mult_mat_vec_def scalar_prod_def unit_vec_def csqrt_two
                      less_2_cases)

lemma hadamard_e1:
  "Hadamard *\<^sub>v unit_vec 2 1 =
   (1 / csqrt 2) \<cdot>\<^sub>v (unit_vec 2 0 - unit_vec 2 1)"
  by (rule eq_vecI)
     (auto simp add: Hadamard_def Quantum.H_def mult_mat_vec_def scalar_prod_def unit_vec_def csqrt_two
                      less_2_cases)



text \<open>The phase gate $S=\mathrm{diag}(1,i)$ is unitary.\<close>

definition Phase_S :: "complex Matrix.mat" where
  "Phase_S \<equiv> Quantum.S"

lemma Phase_S_carrier [simp]: "Phase_S \<in> carrier_mat 2 2"
  by (simp add: Phase_S_def Quantum.S_def)

lemma Phase_S_dagger_S: "Phase_S\<^sup>\<dagger> * Phase_S = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (Phase_S\<^sup>\<dagger> * Phase_S) = dim_row (1\<^sub>m 2 :: complex Matrix.mat)" by (simp add: Phase_S_def Quantum.S_def)
  show "dim_col (Phase_S\<^sup>\<dagger> * Phase_S) = dim_col (1\<^sub>m 2 :: complex Matrix.mat)" by (simp add: Phase_S_def Quantum.S_def)
  fix i j assume "i < dim_row (1\<^sub>m 2 :: complex Matrix.mat)" "j < dim_col (1\<^sub>m 2 :: complex Matrix.mat)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(Phase_S\<^sup>\<dagger> * Phase_S) $$ (i, j) = (1\<^sub>m 2 :: complex Matrix.mat) $$ (i, j)"
    unfolding Phase_S_def Quantum.S_def dagger_def scalar_prod_def
    by (cases i; cases j) (auto simp: less_2_cases numeral_2_eq_2)
qed

lemma Phase_S_S_dagger: "Phase_S * (Phase_S\<^sup>\<dagger>) = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (Phase_S * (Phase_S\<^sup>\<dagger>)) = dim_row (1\<^sub>m 2 :: complex Matrix.mat)" by (simp add: Phase_S_def Quantum.S_def)
  show "dim_col (Phase_S * (Phase_S\<^sup>\<dagger>)) = dim_col (1\<^sub>m 2 :: complex Matrix.mat)" by (simp add: Phase_S_def Quantum.S_def)
  fix i j assume "i < dim_row (1\<^sub>m 2 :: complex Matrix.mat)" "j < dim_col (1\<^sub>m 2 :: complex Matrix.mat)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(Phase_S * (Phase_S\<^sup>\<dagger>)) $$ (i, j) = (1\<^sub>m 2 :: complex Matrix.mat) $$ (i, j)"
    unfolding Phase_S_def Quantum.S_def dagger_def scalar_prod_def
    by (cases i; cases j) (auto simp: less_2_cases numeral_2_eq_2)
qed

lemma Phase_S_unitary: "unitary Phase_S"
  unfolding unitary_def using Phase_S_dagger_S Phase_S_S_dagger by (simp add: Phase_S_def Quantum.S_def)

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


lemma psd_smult_nonneg:
  assumes c: "0 \<le> c"
      and A: "psd A" and Ac: "A \<in> carrier_mat n n"
  shows "psd (complex_of_real c \<cdot>\<^sub>m A)"
proof -
  have A_dagger: "(A\<^sup>\<dagger>) = A" using A by (simp add: psd_def hermitian_def)
  have A_quad: "\<And>x. dim_vec x = n \<Longrightarrow> Re (\<langle>x | A *\<^sub>v x\<rangle>) \<ge> 0"
    using A Ac by (simp add: psd_def)

  have herm_cA: "((complex_of_real c \<cdot>\<^sub>m A)\<^sup>\<dagger>) = complex_of_real c \<cdot>\<^sub>m A"
  proof -
    have "((complex_of_real c \<cdot>\<^sub>m A)\<^sup>\<dagger>) = (cnj (complex_of_real c)) \<cdot>\<^sub>m (A\<^sup>\<dagger>)"
      by (rule dagger_of_smult)
    also have "\<dots> = complex_of_real c \<cdot>\<^sub>m A"
      using A_dagger by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Action of the scaled matrix on a vector.\<close>
  have smult_mv:
    "\<And>x. x \<in> carrier_vec n \<Longrightarrow>
         (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)"
  proof -
    fix x :: "complex Matrix.vec" assume x_car: "x \<in> carrier_vec n"
    show "(complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)"
    proof (rule eq_vecI)
      show "dim_vec ((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x)
            = dim_vec (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x))"
        using Ac by simp
    next
      fix i assume "i < dim_vec (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x))"
      hence i: "i < n" using Ac by simp
      have r1: "Matrix.row A i \<in> carrier_vec n"
        using Ac i by auto
      have i_dr: "i < dim_row A" using i Ac by simp
      have "((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x) $ i
              = Matrix.row (complex_of_real c \<cdot>\<^sub>m A) i \<bullet> x"
        using i Ac by auto
      also have "\<dots> = (complex_of_real c \<cdot>\<^sub>v Matrix.row A i) \<bullet> x"
        using row_smult[OF i_dr] by simp
      also have "\<dots> = complex_of_real c * (Matrix.row A i \<bullet> x)"
        using r1 x_car by simp
      also have "\<dots> = complex_of_real c * (A *\<^sub>v x) $ i"
        using i Ac by auto
      also have "\<dots> = (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)) $ i"
        using i Ac by auto
      finally show "((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x) $ i
                  = (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)) $ i" .
    qed
  qed

  have quad: "\<And>x. dim_vec x = dim_row (complex_of_real c \<cdot>\<^sub>m A) \<Longrightarrow>
                Re (\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>) \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec"
    assume dx: "dim_vec x = dim_row (complex_of_real c \<cdot>\<^sub>m A)"
    hence dx': "dim_vec x = n" using Ac by simp
    have x_car: "x \<in> carrier_vec n" using dx' by auto

    have "\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>
        = \<langle>x | complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)\<rangle>"
      using smult_mv[OF x_car] by simp
    also have "\<dots> = complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>"
      by (rule inner_prod_right_smult')
    finally have eq: "\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>
                    = complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>" .

    have Re_split: "Re (complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>)
                  = c * Re (\<langle>x | A *\<^sub>v x\<rangle>)"
      by simp
    have "0 \<le> c * Re (\<langle>x | A *\<^sub>v x\<rangle>)"
      using c A_quad[OF dx'] by (rule mult_nonneg_nonneg)
    thus "0 \<le> Re (\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>)"
      using eq Re_split by simp
  qed

  show ?thesis
    unfolding psd_def hermitian_def
    using herm_cA quad by blast
qed


lemma tensor_unit_vec:
  assumes i: "i < n" and j: "j < m"
  shows "tensor_vec (unit_vec n i) (unit_vec m j) = (unit_vec (n * m) (i * m + j) :: complex Matrix.vec)"
proof (rule eq_vecI)
  have d: "dim_vec (tensor_vec (unit_vec n i) (unit_vec m j) :: complex Matrix.vec) = n * m"
    by (rule tensor_vec_dim) simp_all
  fix r assume "r < dim_vec (unit_vec (n * m) (i * m + j) :: complex Matrix.vec)"
  hence r: "r < n * m" by simp
  have m: "0 < m" using j by simp
  have rd: "r div m < n" using r by (simp add: less_mult_imp_div_less)
  have e: "(r div m = i \<and> r mod m = j) \<longleftrightarrow> r = i * m + j"
  proof
    assume "r div m = i \<and> r mod m = j" thus "r = i * m + j" using div_mult_mod_eq[of r m] by simp
  next
    assume "r = i * m + j" thus "r div m = i \<and> r mod m = j" using j m by simp
  qed
  have "tensor_vec (unit_vec n i) (unit_vec m j) $ r = unit_vec n i $ (r div m) * unit_vec m j $ (r mod m)"
    by (rule tensor_vec_index) (use r in simp_all)
  also have "\<dots> = (if r div m = i \<and> r mod m = j then 1 else 0)" using rd m by (simp add: unit_vec_def)
  also have "\<dots> = unit_vec (n * m) (i * m + j) $ r" using e r by (simp add: unit_vec_def)
  finally show "tensor_vec (unit_vec n i) (unit_vec m j) $ r = unit_vec (n * m) (i * m + j) $ r" .
qed (simp add: tensor_vec_dim)


lemma Tr_dagger:
  fixes M :: "complex Matrix.mat"
  assumes M_c: "M \<in> carrier_mat n n"
  shows "Tr (M\<^sup>\<dagger>) = cnj (Tr M)"
proof -
  have dr: "dim_row M = n" and dc: "dim_col M = n" using M_c by auto
  have d_dr: "dim_row (M\<^sup>\<dagger>) = n" using dc by simp
  have d_dc: "dim_col (M\<^sup>\<dagger>) = n" using dr by simp
  have "Tr (M\<^sup>\<dagger>) = (\<Sum>r<n. (M\<^sup>\<dagger>) $$ (r,r))"
    unfolding Tr_def using d_dr d_dc by simp
  also have "\<dots> = (\<Sum>r<n. cnj (M $$ (r,r)))"
    using dr dc unfolding dagger_def by simp
  also have "\<dots> = cnj (\<Sum>r<n. M $$ (r,r))" by simp
  also have "\<dots> = cnj (Tr M)"
    unfolding Tr_def using dr dc by simp
  finally show ?thesis .
qed

end
