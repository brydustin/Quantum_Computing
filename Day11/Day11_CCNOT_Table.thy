theory Day11_CCNOT_Table
  imports Day11_Gates_No_Cloning
begin

section \<open>Day 11: the CCNOT truth table (D11-2)\<close>

lemma CCNOT_unit_vec:
  assumes k: "k < 8"
  shows "CCNOT *\<^sub>v unit_vec 8 k = unit_vec 8 (if k = 6 then 7 else if k = 7 then 6 else k)"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (unit_vec 8 (if k = 6 then 7 else if k = 7 then 6 else k) :: complex Matrix.vec)"
  hence r: "r < 8" by simp
  have "(CCNOT *\<^sub>v unit_vec 8 k) $ r = (\<Sum>i<8. CCNOT $$ (r, i) * (if i = k then 1 else 0))"
    using r k by (simp add: scalar_prod_def unit_vec_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<8. if i = k then CCNOT $$ (r, i) else 0)" by (rule sum.cong) simp_all
  also have "\<dots> = CCNOT $$ (r, k)" using k by simp
  also have "\<dots> = (if (r = 6 \<and> k = 7) \<or> (r = 7 \<and> k = 6) then 1 else if r = k \<and> r < 6 then 1 else 0)"
    using r k by (simp add: CCNOT_def)
  also have "\<dots> = unit_vec 8 (if k = 6 then 7 else if k = 7 then 6 else k) $ r"
    using r k by (cases "k = 6"; cases "k = 7"; cases "r = k"; simp add: unit_vec_def)
  finally show "(CCNOT *\<^sub>v unit_vec 8 k) $ r = unit_vec 8 (if k = 6 then 7 else if k = 7 then 6 else k) $ r" .
qed simp

text \<open>On basis states $|a,b,c\rangle=e_a\otimes e_b\otimes e_c$: when $a=0$ nothing happens; when
$a=1$, CNOT acts on $b,c$.\<close>

theorem CCNOT_basis:
  assumes a: "a < 2" and b: "b < 2" and c: "c < 2"
  shows "CCNOT *\<^sub>v tensor_vec (unit_vec 2 a) (tensor_vec (unit_vec 2 b) (unit_vec 2 c)) =
         tensor_vec (unit_vec 2 a) (tensor_vec (unit_vec 2 b) (unit_vec 2 (if a = 1 \<and> b = 1 then 1 - c else c)))"
proof -
  have u: "\<And>c. c < 2 \<Longrightarrow> tensor_vec (unit_vec 2 a) (tensor_vec (unit_vec 2 b) (unit_vec 2 c))
                          = (unit_vec 8 (a * 4 + (b * 2 + c)) :: complex Matrix.vec)"
  proof -
    fix c :: nat assume c: "c < 2"
    have bc: "b * 2 + c < 4" using b c by linarith
    show "tensor_vec (unit_vec 2 a) (tensor_vec (unit_vec 2 b) (unit_vec 2 c)) = (unit_vec 8 (a * 4 + (b * 2 + c)) :: complex Matrix.vec)"
      using tensor_unit_vec[OF b c] tensor_unit_vec[OF a bc] by simp
  qed
  have c': "(if a = 1 \<and> b = 1 then 1 - c else c) < 2" using c by auto
  have k: "a * 4 + (b * 2 + c) < 8" using a b c by linarith
  show ?thesis
    unfolding u[OF c] u[OF c'] CCNOT_unit_vec[OF k]
    using a b c by (auto simp: less_2_cases_iff)
qed

corollary CCNOT_truth_table:
  fixes e :: "nat \<Rightarrow> complex Matrix.vec"
  defines "e \<equiv> \<lambda>a. unit_vec 2 a"
  shows "CCNOT *\<^sub>v tensor_vec (e 0) (tensor_vec (e 0) (e 0)) = tensor_vec (e 0) (tensor_vec (e 0) (e 0))"
    and "CCNOT *\<^sub>v tensor_vec (e 0) (tensor_vec (e 0) (e 1)) = tensor_vec (e 0) (tensor_vec (e 0) (e 1))"
    and "CCNOT *\<^sub>v tensor_vec (e 0) (tensor_vec (e 1) (e 0)) = tensor_vec (e 0) (tensor_vec (e 1) (e 0))"
    and "CCNOT *\<^sub>v tensor_vec (e 0) (tensor_vec (e 1) (e 1)) = tensor_vec (e 0) (tensor_vec (e 1) (e 1))"
    and "CCNOT *\<^sub>v tensor_vec (e 1) (tensor_vec (e 0) (e 0)) = tensor_vec (e 1) (tensor_vec (e 0) (e 0))"
    and "CCNOT *\<^sub>v tensor_vec (e 1) (tensor_vec (e 0) (e 1)) = tensor_vec (e 1) (tensor_vec (e 0) (e 1))"
    and "CCNOT *\<^sub>v tensor_vec (e 1) (tensor_vec (e 1) (e 0)) = tensor_vec (e 1) (tensor_vec (e 1) (e 1))"
    and "CCNOT *\<^sub>v tensor_vec (e 1) (tensor_vec (e 1) (e 1)) = tensor_vec (e 1) (tensor_vec (e 1) (e 0))"
  unfolding e_def by (simp_all add: CCNOT_basis)

end
