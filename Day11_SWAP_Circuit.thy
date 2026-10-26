theory Day11_SWAP_Circuit
  imports Quantum_Computing_by_VP.Day06_Tensor_Products
begin

section \<open>Day 11: SWAP from three CNOTs\<close>

lemma less4_cases: "(i::nat) < 4 \<longleftrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
  by auto

text \<open>$\mathrm{CNOT}'$ is CNOT controlled by the second qubit.\<close>

definition CNOT' :: "complex Matrix.mat" where
  "CNOT' = Matrix.mat 4 4 (\<lambda>(i,j). if (i,j) \<in> {(0,0),(1,3),(2,2),(3,1)} then 1 else 0)"

text \<open>D11-3: $\mathrm{SWAP}=\mathrm{CNOT}\cdot\mathrm{CNOT}'\cdot\mathrm{CNOT}$
(\<^const>\<open>SWAP\<close> is the AFP's).\<close>

theorem SWAP_three_CNOTs: "SWAP = CNOT * CNOT' * CNOT"
  by (rule eq_matI)
     (auto simp: SWAP_def CNOT_def CNOT'_def scalar_prod_def sum.atLeast0_lessThan_Suc
        lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq)

lemma SWAP_basis:
  assumes "a < 2" "b < 2"
  shows "SWAP *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 b) (unit_vec 2 a)"
proof -
  have "\<forall>a \<in> {0,1}. \<forall>b \<in> {0,1::nat}.
          SWAP *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 b) (unit_vec 2 a)"
    by (auto intro!: eq_vecI simp: SWAP_def tensor_vec_index tensor_vec_dim scalar_prod_def
        sum.atLeast0_lessThan_Suc lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq less4_cases)
  moreover have "a \<in> {0,1}" "b \<in> {0,1}" using assms by auto
  ultimately show ?thesis by blast
qed

lemma CNOT'_basis:
  assumes "a < 2" "b < 2"
  shows "CNOT' *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 ((a + b) mod 2)) (unit_vec 2 b)"
proof -
  have "\<forall>a \<in> {0,1}. \<forall>b \<in> {0,1::nat}.
          CNOT' *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 ((a + b) mod 2)) (unit_vec 2 b)"
    by (auto intro!: eq_vecI simp: CNOT'_def tensor_vec_index tensor_vec_dim scalar_prod_def
        sum.atLeast0_lessThan_Suc lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq less4_cases)
  moreover have "a \<in> {0,1}" "b \<in> {0,1}" using assms by auto
  ultimately show ?thesis by blast
qed

end
