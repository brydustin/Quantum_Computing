theory Day10_Superdense_Coding
  imports Day30_Error_Probabilities
begin

section \<open>Day 10: superdense coding (D10-1)\<close>

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
