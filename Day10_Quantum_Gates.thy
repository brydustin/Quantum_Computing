(*  Title:   Day10_Quantum_Gates.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 19 September 2011 (Day 10)
*)

theory Day10_Quantum_Gates
  imports Day06_Tensor_Products
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
unitaries (not formalised).  Formally $X$, $Y$, $Z$ are \<open>Pauli_X\<close>, \<open>Pauli_Y\<close>,
\<open>Pauli_Z\<close>, $H$ is \<open>Hadamard\<close> (the library's \<open>Quantum.H\<close>) and $S$ is \<open>Phase_S\<close>.\<close>

subsubsection \<open>The Pauli matrices\<close>

text \<open>The notes use two sign conventions for $Y$: $\begin{pmatrix}0&-i\\i&0\end{pmatrix}$ on
Day 10 (the library's \<open>Y\<close>) and $\begin{pmatrix}0&i\\-i&0\end{pmatrix}$ on Day 32.
\<open>Pauli_Y\<close> follows Day 32; both are Hermitian unitary involutions, and the Pauli
identities below carry the corresponding signs.  \<open>Pauli_X\<close> and \<open>Pauli_Z\<close> are the
library's \<open>Quantum.X\<close> and \<open>Quantum.Z\<close>.\<close>

definition Pauli_X :: "complex Matrix.mat" where
  "Pauli_X \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if (i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0) then 1 else 0)"

definition Pauli_Y :: "complex Matrix.mat" where
  "Pauli_Y \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if i = 0 \<and> j = 1 then \<i>
                else if i = 1 \<and> j = 0 then -\<i> else 0)"

definition Pauli_Z :: "complex Matrix.mat" where
  "Pauli_Z \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if i = 0 \<and> j = 0 then 1
                else if i = 1 \<and> j = 1 then -1 else 0)"

text \<open>\[ X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad Y=\begin{pmatrix}0&i\\-i&0\end{pmatrix},\qquad
   Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}. \]
(The notes' $Y$ is the negative of the physicists' $\sigma_y$.)  Each is Hermitian and squares
to $I$, so each is unitary: $U^*U=U^2=I$.\<close>

lemma Pauli_X_carrier [simp]: "Pauli_X \<in> carrier_mat 2 2"
  by (auto simp: Pauli_X_def)

lemma Pauli_Y_carrier [simp]: "Pauli_Y \<in> carrier_mat 2 2"
  by (auto simp: Pauli_Y_def)

lemma Pauli_Z_carrier [simp]: "Pauli_Z \<in> carrier_mat 2 2"
  by (auto simp: Pauli_Z_def)

lemma Pauli_X_dagger: "Pauli_X\<^sup>\<dagger> = Pauli_X"
proof (rule eq_matI)
  show "dim_row (Pauli_X\<^sup>\<dagger>) = dim_row Pauli_X" by (simp add: Pauli_X_def)
  show "dim_col (Pauli_X\<^sup>\<dagger>) = dim_col Pauli_X" by (simp add: Pauli_X_def)
next
  fix i j assume "i < dim_row Pauli_X" "j < dim_col Pauli_X"
  thus "(Pauli_X\<^sup>\<dagger>) $$ (i, j) = Pauli_X $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: Pauli_X_def dagger_def)
qed

lemma Pauli_X_squared: "Pauli_X * Pauli_X = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (Pauli_X * Pauli_X) = dim_row (1\<^sub>m 2)"
    by (simp add: Pauli_X_def)
  show "dim_col (Pauli_X * Pauli_X) = dim_col (1\<^sub>m 2)"
    by (simp add: Pauli_X_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(Pauli_X * Pauli_X) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding Pauli_X_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

lemma Pauli_X_unitary: "unitary Pauli_X"
  unfolding unitary_def
  using Pauli_X_dagger Pauli_X_squared by (simp add: Pauli_X_def)

lemma Pauli_Y_dagger: "Pauli_Y\<^sup>\<dagger> = Pauli_Y"
proof (rule eq_matI)
  show "dim_row (Pauli_Y\<^sup>\<dagger>) = dim_row Pauli_Y" by (simp add: Pauli_Y_def)
  show "dim_col (Pauli_Y\<^sup>\<dagger>) = dim_col Pauli_Y" by (simp add: Pauli_Y_def)
next
  fix i j assume "i < dim_row Pauli_Y" "j < dim_col Pauli_Y"
  thus "(Pauli_Y\<^sup>\<dagger>) $$ (i, j) = Pauli_Y $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: Pauli_Y_def dagger_def)
qed

lemma Pauli_Y_squared: "Pauli_Y * Pauli_Y = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (Pauli_Y * Pauli_Y) = dim_row (1\<^sub>m 2)"
    by (simp add: Pauli_Y_def)
  show "dim_col (Pauli_Y * Pauli_Y) = dim_col (1\<^sub>m 2)"
    by (simp add: Pauli_Y_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(Pauli_Y * Pauli_Y) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding Pauli_Y_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

lemma Pauli_Y_unitary: "unitary Pauli_Y"
  unfolding unitary_def
  using Pauli_Y_dagger Pauli_Y_squared by (simp add: Pauli_Y_def)

lemma Pauli_Z_dagger: "Pauli_Z\<^sup>\<dagger> = Pauli_Z"
proof (rule eq_matI)
  show "dim_row (Pauli_Z\<^sup>\<dagger>) = dim_row Pauli_Z" by (simp add: Pauli_Z_def)
  show "dim_col (Pauli_Z\<^sup>\<dagger>) = dim_col Pauli_Z" by (simp add: Pauli_Z_def)
next
  fix i j assume "i < dim_row Pauli_Z" "j < dim_col Pauli_Z"
  thus "(Pauli_Z\<^sup>\<dagger>) $$ (i, j) = Pauli_Z $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: Pauli_Z_def dagger_def)
qed

lemma Pauli_Z_squared: "Pauli_Z * Pauli_Z = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (Pauli_Z * Pauli_Z) = dim_row (1\<^sub>m 2)"
    by (simp add: Pauli_Z_def)
  show "dim_col (Pauli_Z * Pauli_Z) = dim_col (1\<^sub>m 2)"
    by (simp add: Pauli_Z_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(Pauli_Z * Pauli_Z) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding Pauli_Z_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2 numeral_2_eq_2)+)
qed

lemma Pauli_Z_unitary: "unitary Pauli_Z"
  unfolding unitary_def
  using Pauli_Z_dagger Pauli_Z_squared by (simp add: Pauli_Z_def)

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
defined below.\<close>

lemma CNOT_unitary: "unitary CNOT"
  using CNOT_is_gate gate.unitary by blast

text \<open>CNOT flips the target qubit when the control is $1$, $\ket{ab}\mapsto\ket{a,\,a\oplus b}$:
\[ \ket{00}\mapsto\ket{00},\quad \ket{01}\mapsto\ket{01},\quad \ket{10}\mapsto\ket{11},\quad
   \ket{11}\mapsto\ket{10}. \]\<close>

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

text \<open>In the Kronecker model $\ket{ab}=e_a\otimes e_b=e_{2a+b}\in\C^4$:\<close>

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

definition CCNOT :: "complex Matrix.mat" where
  "CCNOT \<equiv> Matrix.mat 8 8
     (\<lambda>(i,j). if (i = 6 \<and> j = 7) \<or> (i = 7 \<and> j = 6)
               then 1
               else if i = j \<and> i < 6 then 1 else 0)"

lemma CCNOT_dagger [simp]:
  "CCNOT\<^sup>\<dagger> = CCNOT"
  unfolding CCNOT_def dagger_def
  by (simp add: cong_mat)

lemma CCNOT_dim_row [simp]:
  "dim_row CCNOT = 8"
  by (simp add: CCNOT_def)

lemma CCNOT_dim_col [simp]:
  "dim_col CCNOT = 8"
  by (simp add: CCNOT_def)


lemma CCNOT_inv [simp]:
  "CCNOT * CCNOT = 1\<^sub>m 8"
proof (rule eq_matI)
  show "dim_row (CCNOT * CCNOT) = dim_row (1\<^sub>m 8)" by simp
  show "dim_col (CCNOT * CCNOT) = dim_col (1\<^sub>m 8)" by simp
next
  fix i j
  assume "i < dim_row (1\<^sub>m 8)" and "j < dim_col (1\<^sub>m 8)"
  then have i: "i < 8" and j: "j < 8" by simp_all

  define p where "p = (if i < 6 then i else if i = 6 then 7 else 6)"
  define q where "q = (if j < 6 then j else if j = 6 then 7 else 6)"
  have p8: "p < 8" using i by (auto simp: p_def)
  have q8: "q < 8" using j by (auto simp: q_def)

  have row_i: "\<And>k. k < 8 \<Longrightarrow> CCNOT $$ (i, k) = (if k = p then 1 else 0)"
    using i by (auto simp: CCNOT_def p_def)
  have col_j: "\<And>k::nat. k < 8 \<Longrightarrow> CCNOT $$ (k, j) = (if k = q then 1 else 0)"
  proof -
    fix k :: nat assume k: "k < 8"
    from j consider "j < 6" | "j = 6" | "j = 7" by linarith
    then show "CCNOT $$ (k, j) = (if k = q then 1 else 0)"
    proof cases
      case 1
      then have qj: "q = j" by (simp add: q_def)
      show ?thesis using k 1 qj by (auto simp: CCNOT_def)
    next
      case 2
      then have qj: "q = 7" by (simp add: q_def)
      show ?thesis using k 2 qj by (auto simp: CCNOT_def)
    next
      case 3
      then have qj: "q = 6" by (simp add: q_def)
      show ?thesis using k 3 qj by (auto simp: CCNOT_def)
    qed
  qed

  have pq_iff: "(p = q) \<longleftrightarrow> (i = j)"
    using i j by (auto simp: p_def q_def)

  have "(CCNOT * CCNOT) $$ (i, j)
          = (\<Sum>k = 0..<8. CCNOT $$ (i, k) * CCNOT $$ (k, j))"
    using i j by (simp add: times_mat_def scalar_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<8.
        (if k = p then (1::complex) else 0) * (if k = q then 1 else 0))"
    using row_i col_j by auto
  also have "\<dots> = (if p = q then 1 else 0)"
  proof (cases "p = q")
    case True
    have pointwise:
      "(if k = p then (1::complex) else 0) * (if k = q then 1 else 0)
         = (if k = p then 1 else 0)" for k
      using True by simp
    have "(\<Sum>k = 0..<8.
            (if k = p then (1::complex) else 0) * (if k = q then 1 else 0))
        = (\<Sum>k = 0..<8. if k = p then (1::complex) else 0)"
      by (rule sum.cong) (simp_all add: pointwise)
    also have "\<dots> = 1" using p8 by fastforce
    finally show ?thesis using True by simp
  next
    case False
    have "\<And>k. (if k = p then (1::complex) else 0) * (if k = q then 1 else 0) = 0"
      using False by auto
    with False show ?thesis by simp
  qed
  also have "\<dots> = (1\<^sub>m 8) $$ (i, j)"
    using i j pq_iff by simp
  finally show "(CCNOT * CCNOT) $$ (i, j) = (1\<^sub>m 8) $$ (i, j)" .
qed

lemma CCNOT_unitary: "unitary CCNOT"
  by (simp add: unitary_def)

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

text \<open>Lab A and Lab B share $\gamma=\tfrac1{\sqrt2}(|00\rangle+|11\rangle)$, Lab A holding the first
qubit.  Lab A multiplies its qubit by $I$, $\begin{pmatrix}1&0\\0&-1\end{pmatrix}$,
$\begin{pmatrix}0&1\\1&0\end{pmatrix}$ or $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and sends it to
Lab B, which then holds $\tfrac1{\sqrt2}(|00\rangle\pm|11\rangle)$ or
$\tfrac1{\sqrt2}(|01\rangle\pm|10\rangle)$: four orthonormal states, so one qubit carries two bits.
The four matrices are $I$, $Z$, $X$ and $ZX$ (\<open>sd_op_paulis\<close>).\<close>

lemma less4: "i < (4::nat) \<longleftrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by auto

lemma tensor_I2_apply:
  fixes A :: "complex Matrix.mat" and v :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat 2 2" and v: "dim_vec v = 4" and i: "i < 4"
  shows "(Tensor.tensor_mat A (1\<^sub>m 2) *\<^sub>v v) $ i =
         (\<Sum>j<4. A $$ (i div 2, j div 2) * (if i mod 2 = j mod 2 then 1 else 0) * v $ j)"
proof -
  have c: "Tensor.tensor_mat A (1\<^sub>m 2) \<in> carrier_mat 4 4" using A by (intro carrier_matI) auto
  have "(Tensor.tensor_mat A (1\<^sub>m 2) *\<^sub>v v) $ i = (\<Sum>j<4. Tensor.tensor_mat A (1\<^sub>m 2) $$ (i, j) * v $ j)"
    using carrier_matD[OF c] v i by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>j<4. A $$ (i div 2, j div 2) * (if i mod 2 = j mod 2 then 1 else 0) * v $ j)"
  proof (rule sum.cong)
    fix j assume "j \<in> {..<4::nat}"
    hence j: "j < 4" by simp
    have "Tensor.tensor_mat A (1\<^sub>m 2) $$ (i, j) = A $$ (i div 2, j div 2) * 1\<^sub>m 2 $$ (i mod 2, j mod 2)"
      by (rule index_tensor_mat) (use A i j in auto)
    thus "Tensor.tensor_mat A (1\<^sub>m 2) $$ (i, j) * v $ j = A $$ (i div 2, j div 2) * (if i mod 2 = j mod 2 then 1 else 0) * v $ j"
      by simp
  qed simp
  finally show ?thesis .
qed

definition superdense_gamma :: "complex Matrix.vec" where
  "superdense_gamma = bell_basis ! 0"

text \<open>Lab A applies one of the notes' four matrices to its qubit.\<close>

definition sd_op :: "nat \<Rightarrow> complex Matrix.mat" where
  "sd_op k = (if k = 0 then mat_of_rows_list 2 [[1, 0], [0, 1]]
              else if k = 1 then mat_of_rows_list 2 [[1, 0], [0, -1]]
              else if k = 2 then mat_of_rows_list 2 [[0, 1], [1, 0]]
              else mat_of_rows_list 2 [[0, 1], [-1, 0]])"

lemma sd_op_carrier: "sd_op k \<in> carrier_mat 2 2"
  by (simp add: sd_op_def mat_of_rows_list_def eval_nat_numeral)

lemma sd_op_paulis:
  "sd_op 0 = 1\<^sub>m 2" "sd_op 1 = Pauli_Z" "sd_op 2 = Pauli_X" "sd_op 3 = Pauli_Z * Pauli_X"
proof -
  have l2: "\<And>i::nat. i < 2 \<longleftrightarrow> i = 0 \<or> i = 1" by auto
  show "sd_op 0 = 1\<^sub>m 2" by (rule eq_matI) (auto simp: sd_op_def mat_of_rows_list_def l2)
  show "sd_op 1 = Pauli_Z" by (rule eq_matI) (auto simp: sd_op_def mat_of_rows_list_def Pauli_Z_def l2)
  show "sd_op 2 = Pauli_X" by (rule eq_matI) (auto simp: sd_op_def mat_of_rows_list_def Pauli_X_def l2)
  show "sd_op 3 = Pauli_Z * Pauli_X"
    by (rule eq_matI) (auto simp: sd_op_def mat_of_rows_list_def Pauli_Z_def Pauli_X_def l2 scalar_prod_def
        Matrix.row_def Matrix.col_def lessThan_nat_numeral atLeast0LessThan)
qed

text \<open>The notes' table: the four results are the four Bell states.\<close>

lemma superdense_coding_0: "Tensor.tensor_mat (sd_op 0) (1\<^sub>m 2) *\<^sub>v superdense_gamma = bell_basis ! 0"
proof (rule eq_vecI)
  have d: "dim_vec superdense_gamma = 4" by (simp add: superdense_gamma_def bell_basis_def tensor_vec_dim)
  fix i assume "i < dim_vec (bell_basis ! 0)"
  hence i: "i < 4" by (simp add: bell_basis_def tensor_vec_dim)
  show "(Tensor.tensor_mat (sd_op 0) (1\<^sub>m 2) *\<^sub>v superdense_gamma) $ i = bell_basis ! 0 $ i"
    unfolding tensor_I2_apply[OF sd_op_carrier d i]
    using i by (auto simp: less4 superdense_gamma_def bell_basis_def sd_op_def mat_of_rows_list_def
                           tensor_vec_index tensor_vec_dim lessThan_nat_numeral)
qed (use carrier_matD[OF sd_op_carrier] in \<open>simp add: superdense_gamma_def bell_basis_def tensor_vec_dim\<close>)

lemma superdense_coding_1: "Tensor.tensor_mat (sd_op 1) (1\<^sub>m 2) *\<^sub>v superdense_gamma = bell_basis ! 1"
proof (rule eq_vecI)
  have d: "dim_vec superdense_gamma = 4" by (simp add: superdense_gamma_def bell_basis_def tensor_vec_dim)
  fix i assume "i < dim_vec (bell_basis ! 1)"
  hence i: "i < 4" by (simp add: bell_basis_def tensor_vec_dim)
  show "(Tensor.tensor_mat (sd_op 1) (1\<^sub>m 2) *\<^sub>v superdense_gamma) $ i = bell_basis ! 1 $ i"
    unfolding tensor_I2_apply[OF sd_op_carrier d i]
    using i by (auto simp: less4 superdense_gamma_def bell_basis_def sd_op_def mat_of_rows_list_def
                           tensor_vec_index tensor_vec_dim lessThan_nat_numeral)
qed (use carrier_matD[OF sd_op_carrier] in \<open>simp add: superdense_gamma_def bell_basis_def tensor_vec_dim\<close>)

lemma superdense_coding_2: "Tensor.tensor_mat (sd_op 2) (1\<^sub>m 2) *\<^sub>v superdense_gamma = bell_basis ! 2"
proof (rule eq_vecI)
  have d: "dim_vec superdense_gamma = 4" by (simp add: superdense_gamma_def bell_basis_def tensor_vec_dim)
  fix i assume "i < dim_vec (bell_basis ! 2)"
  hence i: "i < 4" by (simp add: bell_basis_def tensor_vec_dim)
  show "(Tensor.tensor_mat (sd_op 2) (1\<^sub>m 2) *\<^sub>v superdense_gamma) $ i = bell_basis ! 2 $ i"
    unfolding tensor_I2_apply[OF sd_op_carrier d i]
    using i by (auto simp: less4 superdense_gamma_def bell_basis_def sd_op_def mat_of_rows_list_def
                           tensor_vec_index tensor_vec_dim lessThan_nat_numeral)
qed (use carrier_matD[OF sd_op_carrier] in \<open>simp add: superdense_gamma_def bell_basis_def tensor_vec_dim\<close>)

lemma superdense_coding_3: "Tensor.tensor_mat (sd_op 3) (1\<^sub>m 2) *\<^sub>v superdense_gamma = bell_basis ! 3"
proof (rule eq_vecI)
  have d: "dim_vec superdense_gamma = 4" by (simp add: superdense_gamma_def bell_basis_def tensor_vec_dim)
  fix i assume "i < dim_vec (bell_basis ! 3)"
  hence i: "i < 4" by (simp add: bell_basis_def tensor_vec_dim)
  show "(Tensor.tensor_mat (sd_op 3) (1\<^sub>m 2) *\<^sub>v superdense_gamma) $ i = bell_basis ! 3 $ i"
    unfolding tensor_I2_apply[OF sd_op_carrier d i]
    using i by (auto simp: less4 superdense_gamma_def bell_basis_def sd_op_def mat_of_rows_list_def
                           tensor_vec_index tensor_vec_dim lessThan_nat_numeral)
qed (use carrier_matD[OF sd_op_carrier] in \<open>simp add: superdense_gamma_def bell_basis_def tensor_vec_dim\<close>)

theorem superdense_coding:
  assumes k: "k < 4"
  shows "Tensor.tensor_mat (sd_op k) (1\<^sub>m 2) *\<^sub>v superdense_gamma = bell_basis ! k"
  using k superdense_coding_0 superdense_coding_1 superdense_coding_2 superdense_coding_3
  unfolding less4 by (elim disjE) simp_all

corollary superdense_coding_orthonormal:
  "orthonormal_list 4 (map (\<lambda>k. Tensor.tensor_mat (sd_op k) (1\<^sub>m 2) *\<^sub>v superdense_gamma) [0..<4])"
proof -
  have "map (\<lambda>k. Tensor.tensor_mat (sd_op k) (1\<^sub>m 2) *\<^sub>v superdense_gamma) [0..<4] = bell_basis"
    by (rule nth_equalityI) (auto simp: superdense_coding bell_basis_def)
  thus ?thesis using bell_basis_orthonormal by simp
qed

end
