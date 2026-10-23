theory HHL_Demo
  imports Vern_Paulsen_QC_Algorithms.HHL_Program Jordan_Normal_Form.Matrix_IArray_Impl Real_Impl.Real_Unique_Impl
begin

section \<open>Running HHL on a $2\times2$ system\<close>

text \<open>The verified circuit, executed.  Numbers in $\mathbb Q(\sqrt2)$ compute exactly with the
AFP entry \<open>Real_Impl\<close>, and matrices run as immutable arrays (\<open>Matrix_IArray_Impl\<close>).  The
example: $A=\begin{pmatrix}2&1\\1&2\end{pmatrix}$ (eigenvalues $3$ and $1$), $b=\ket0$, three
clock qubits, $t_0=\pi/4$, $C=1$.  The theorems show that every computed state is the state of
@{thm [source] hhl_trajectory}.\<close>

subsection \<open>Code equations\<close>

text \<open>The library defines tensor products through lists; these index formulas make them
executable.  \<open>ctrl_blocks\<close> computes each block once.\<close>

lemma tensor_vec_code [code]:
  "tensor_vec v w = Matrix.vec (dim_vec v * dim_vec w) (\<lambda>i. v $ (i div dim_vec w) * w $ (i mod dim_vec w))"
  by (rule eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim)

lemma tensor_mat_code [code]:
  "A \<Otimes> B = Matrix.mat (dim_row A * dim_row B) (dim_col A * dim_col B)
     (\<lambda>(i, j). A $$ (i div dim_row B, j div dim_col B) * B $$ (i mod dim_row B, j mod dim_col B))"
  by (rule eq_matI) (auto intro!: index_tensor_mat gr0I)

definition blocks_of_list :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "blocks_of_list N m Bs = Matrix.mat (N * m) (N * m)
     (\<lambda>(r, c). if r div m = c div m then Bs ! (r div m) $$ (r mod m, c mod m) else 0)"

lemma ctrl_blocks_code [code]: "ctrl_blocks N m B = blocks_of_list N m (map B [0..<N])"
  by (rule eq_matI) (auto simp: ctrl_blocks_def blocks_of_list_def less_mult_imp_div_less)

subsection \<open>The instance\<close>

definition demo_A :: "complex Matrix.mat" where
  "demo_A = Matrix.mat 2 2 (\<lambda>(i, j). if i = j then 2 else 1)"

text \<open>$\omega=e^{i\pi/4}$; then $e^{iA\pi/4}=H\,\mathrm{diag}(\omega^3,\omega)\,H^*$ and the Fourier
matrix has entries $\omega^{jk}/\sqrt8$.\<close>

definition omega8 :: complex where
  "omega8 = Complex (sqrt 2 / 2) (sqrt 2 / 2)"

definition demo_E :: "complex Matrix.mat" where
  "demo_E = Hadamard * diag_cmat [omega8 ^ 3, omega8] * (Hadamard\<^sup>\<dagger>)"

definition demo_F :: "complex Matrix.mat" where
  "demo_F = Matrix.mat 8 8 (\<lambda>(j, k). omega8 ^ (j * k) / complex_of_real (sqrt 8))"

definition demo_gates :: "complex Matrix.mat list" where
  "demo_gates =
     [prep_gate 8 (1\<^sub>m 2), clock_gate (Hadamard \<otimes>\<^bsup>3\<^esup>) 2, ctrl_pow 8 4 (demo_E \<Otimes> 1\<^sub>m 2),
      clock_gate (demo_F\<^sup>\<dagger>) 2, ctrl_blocks 8 4 (\<lambda>j. 1\<^sub>m 2 \<Otimes> rot (1 / (if 2 * j < 8 then real j else real j - 8))),
      clock_gate demo_F 2, ((ctrl_pow 8 4 (demo_E \<Otimes> 1\<^sub>m 2))\<^sup>\<dagger>), clock_gate (Hadamard \<otimes>\<^bsup>3\<^esup>) 2]"

lemma demo_A_carrier [simp]: "demo_A \<in> carrier_mat 2 2"
  by (simp add: demo_A_def)

lemma demo_A_dim [simp]: "dim_row demo_A = 2" "dim_col demo_A = 2"
  by (simp_all add: demo_A_def)

lemma demo_A_index: "i < 2 \<Longrightarrow> j < 2 \<Longrightarrow> demo_A $$ (i, j) = (if i = j then 2 else 1)"
  by (simp add: demo_A_def)

lemma demo_A_hermitian: "hermitian demo_A"
  unfolding hermitian_dagger by (rule eq_matI) (auto simp: dagger_def demo_A_index)

lemma Hadamard_index:
  "i < 2 \<Longrightarrow> j < 2 \<Longrightarrow> Hadamard $$ (i, j) = (if i = 1 \<and> j = 1 then - 1 else 1) / complex_of_real (sqrt 2)"
  by (auto simp: Hadamard_def H_def numeral_2_eq_2 less_Suc_eq)

lemma Hadamard_carrier [simp]: "Hadamard \<in> carrier_mat 2 2"
  by (simp add: Hadamard_def H_def)

lemma Hadamard_dims [simp]: "dim_row Hadamard = 2" "dim_col Hadamard = 2"
  by (simp_all add: Hadamard_def H_def)

lemma Hadamard_dagger: "Hadamard\<^sup>\<dagger> = Hadamard"
  by (rule eq_matI) (auto simp: dagger_def Hadamard_index)

lemma mult2_index:
  assumes "A \<in> carrier_mat 2 2" "B \<in> carrier_mat 2 2" "i < 2" "j < 2"
  shows "(A * B) $$ (i, j) = A $$ (i, 0) * B $$ (0, j) + A $$ (i, 1) * B $$ (1, j)"
proof -
  have "(A * B) $$ (i, j) = (\<Sum>k<2. A $$ (i, k) * B $$ (k, j))"
    using assms by (simp add: scalar_prod_def atLeast0LessThan)
  thus ?thesis by (simp add: numeral_2_eq_2)
qed

lemma sqrt2_sq: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
  by (simp flip: of_real_mult)

lemma demo_decomp: "spectral_decomp demo_A Hadamard [3, 1]"
proof -
  have HA: "Hadamard * demo_A \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF Hadamard_carrier demo_A_carrier])
  have "Hadamard\<^sup>\<dagger> * demo_A * Hadamard = diag_cmat (map complex_of_real [3, 1])"
    unfolding Hadamard_dagger
    by (rule eq_matI) (auto simp: mult2_index[OF HA Hadamard_carrier] mult2_index[OF Hadamard_carrier demo_A_carrier]
        Hadamard_index demo_A_index diag_cmat_def mat_diag_def numeral_2_eq_2 less_Suc_eq field_simps sqrt2_sq)
  moreover have "Quantum.unitary Hadamard" using H_is_gate unfolding Hadamard_def gate_def by simp
  ultimately show ?thesis unfolding spectral_decomp_def by simp
qed

lemma omega8_cis: "omega8 = cis (pi / 4)"
  by (simp add: omega8_def complex_eq_iff cos_45 sin_45)

lemma demo_evolution: "evolution demo_A (pi / 4) = demo_E"
proof -
  have "evolution demo_A (pi / 4) = Hadamard * diag_cmat (map (\<lambda>x. cis (pi / 4 * x)) [3, 1]) * (Hadamard\<^sup>\<dagger>)"
    unfolding evolution_def by (rule mat_fun_decomp[OF demo_A_carrier demo_A_hermitian demo_decomp])
  also have "map (\<lambda>x. cis (pi / 4 * x)) [3, 1] = [omega8 ^ 3, omega8]"
    by (simp add: omega8_cis DeMoivre mult.commute)
  finally show ?thesis unfolding demo_E_def .
qed

lemma demo_fourier: "fourier 8 = demo_F"
  by (rule eq_matI) (simp_all add: fourier_def demo_F_def omega8_cis DeMoivre field_simps)

lemma demo_reg_eig: "reg_eig (pi / 4) 8 j = (if 2 * j < 8 then real j else real j - 8)"
  by (simp add: reg_eig_def)

lemma demo_eigs:
  assumes "l \<in> herm_spectrum demo_A"
  shows "l = 1 \<or> l = 3"
proof -
  obtain v where v: "dim_vec v = 2" "v \<noteq> 0\<^sub>v 2" "demo_A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    using assms unfolding herm_spectrum_iff by auto
  have "(demo_A *\<^sub>v v) $ i = (\<Sum>k<2. demo_A $$ (i, k) * v $ k)" if "i < 2" for i
    using that v(1) by (simp add: scalar_prod_def atLeast0LessThan)
  hence e: "2 * v $ 0 + v $ 1 = l * v $ 0" "v $ 0 + 2 * v $ 1 = l * v $ 1"
    using v(1) v(3)[THEN arg_cong, of "\<lambda>w. w $ 0"] v(3)[THEN arg_cong, of "\<lambda>w. w $ 1"]
    by (simp_all add: numeral_2_eq_2 demo_A_index)
  have nz: "v $ 0 \<noteq> 0 \<or> v $ 1 \<noteq> 0"
    using v(1,2) by (auto simp: vec_eq_iff numeral_2_eq_2 less_Suc_eq)
  have lin: "(1 - c) * (x - y) = 0" "(3 - c) * (x + y) = 0" if "2 * x + y = c * x" "x + 2 * y = c * y" for x y c :: complex
    using that by (simp_all add: algebra_simps flip: that)
  have "(1 - complex_of_real l) * (v $ 0 - v $ 1) = 0" "(3 - complex_of_real l) * (v $ 0 + v $ 1) = 0"
    by (rule lin[OF e])+
  hence "complex_of_real l = 1 \<or> complex_of_real l = 3" using nz by auto
  thus ?thesis using of_real_eq_iff[where 'a = complex, of l 3] by simp
qed

lemma demo_spec:
  assumes "l \<in> herm_spectrum demo_A"
  shows "\<exists>j. 0 < j \<and> j < 2 ^ 3 \<and> l = reg_eig (pi / 4) (2 ^ 3) j"
proof (cases "l = 1")
  case True
  thus ?thesis by (intro exI[of _ 1]) (simp add: demo_reg_eig)
next
  case False
  hence "l = 3" using demo_eigs[OF assms] by simp
  thus ?thesis by (intro exI[of _ 3]) (simp add: demo_reg_eig)
qed

lemma demo_Cb: "j < 2 ^ 3 \<Longrightarrow> \<bar>1 / reg_eig (pi / 4) (2 ^ 3) j\<bar> \<le> 1"
  by (cases "j = 0") (simp_all add: demo_reg_eig)

lemma demo_Ub: "1\<^sub>m 2 \<in> carrier_mat 2 2" "Quantum.unitary (1\<^sub>m 2)" "1\<^sub>m 2 *\<^sub>v unit_vec 2 0 = (unit_vec 2 0 :: complex Matrix.vec)"
  by (simp_all add: Quantum.unitary_def)

subsection \<open>The run is the verified circuit\<close>

theorem demo_gates_eq: "hhl_gates demo_A (1\<^sub>m 2) (pi / 4) 3 1 = demo_gates"
  by (simp add: hhl_gates_def demo_gates_def evo_gate_def rot_gate_def demo_evolution demo_fourier demo_reg_eig)

text \<open>Each prefix of the gate list produces the state of the trajectory theorem.\<close>

theorem demo_trajectory:
  "i \<le> 8 \<Longrightarrow> run_gates (unit_vec 32 0) (take i demo_gates) = hhl_states demo_A (unit_vec 2 0) (pi / 4) 3 1 ! i"
proof (induction i)
  case 0
  have "tensor_vec (unit_vec 8 0) (tensor_vec (unit_vec 2 0) (unit_vec 2 0)) = unit_vec 32 0"
    unfolding unit_vec_tensor by simp
  thus ?case by (simp add: hhl_states_def Let_def)
next
  case (Suc i)
  have i: "i < 8" using Suc.prems by simp
  have "take (Suc i) demo_gates = take i demo_gates @ [demo_gates ! i]"
    by (rule take_Suc_conv_app_nth) (simp add: demo_gates_eq[symmetric] i)
  thus ?case
    using Suc.IH i hhl_steps[OF demo_A_carrier demo_A_hermitian _ _ _ demo_spec demo_Ub i, of 1]
    by (simp add: run_gates_append demo_gates_eq)
qed

theorem demo_run:
  "run_gates (unit_vec 32 0) demo_gates = tensor_vec (unit_vec 8 0) (hhl_out demo_A 1 (unit_vec 2 0))"
proof -
  have u: "tensor_vec (unit_vec (2 ^ 3) 0) (tensor_vec (unit_vec 2 0) (unit_vec 2 0)) = unit_vec 32 0"
    unfolding unit_vec_tensor by simp
  show ?thesis
    using hhl_run[OF demo_A_carrier demo_A_hermitian _ _ _ demo_spec demo_Ub, of 1] unfolding u demo_gates_eq by simp
qed

lemma had_diag_e0:
  "(Hadamard * diag_cmat [a, b] * (Hadamard\<^sup>\<dagger>)) *\<^sub>v unit_vec 2 0 = vec_of_list [(a + b) / 2, (a - b) / 2]"
proof -
  have D: "diag_cmat [a, b] \<in> carrier_mat 2 2" using diag_cmat_carrier[of "[a, b]"] by (simp add: numeral_2_eq_2)
  have HD: "Hadamard * diag_cmat [a, b] \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF Hadamard_carrier D])
  show ?thesis
    unfolding Hadamard_dagger
    by (rule eq_vecI) (auto simp: mult2_index[OF HD Hadamard_carrier] mult2_index[OF Hadamard_carrier D] Hadamard_index
        diag_cmat_def mat_diag_def numeral_2_eq_2 less_Suc_eq field_simps sqrt2_sq)
qed

lemma sqrt_eight_ninths: "sqrt (1 - (1 / 3)\<^sup>2) = 2 * sqrt 2 / 3"
proof -
  have "sqrt (1 - (1 / 3)\<^sup>2) = sqrt (2\<^sup>2 * 2) / sqrt (3\<^sup>2)"
    unfolding real_sqrt_divide[symmetric] by (simp add: power2_eq_square)
  thus ?thesis unfolding real_sqrt_mult real_sqrt_abs by simp
qed

lemma demo_solution: "herm_inv demo_A *\<^sub>v unit_vec 2 0 = vec_of_list [2 / 3, - 1 / 3]"
  unfolding herm_inv_def mat_fun_decomp[OF demo_A_carrier demo_A_hermitian demo_decomp] by (simp add: had_diag_e0)

theorem demo_out:
  "hhl_out demo_A 1 (unit_vec 2 0) = vec_of_list [complex_of_real (sqrt 2) / 3, 2 / 3, complex_of_real (sqrt 2) / 3, - 1 / 3]"
proof -
  have G: "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (1 / x)\<^sup>2))) demo_A *\<^sub>v unit_vec 2 0
             = vec_of_list [complex_of_real (sqrt 2) / 3, complex_of_real (sqrt 2) / 3]"
    unfolding mat_fun_decomp[OF demo_A_carrier demo_A_hermitian demo_decomp] using had_diag_e0
    by (simp add: sqrt_eight_ninths)
  have one: "1 \<cdot>\<^sub>m M = M" for M :: "complex Matrix.mat" by (rule eq_matI) simp_all
  have I: "(complex_of_real 1 \<cdot>\<^sub>m herm_inv demo_A) *\<^sub>v unit_vec 2 0 = vec_of_list [2 / 3, - 1 / 3]"
    unfolding of_real_1 one by (rule demo_solution)
  show ?thesis
    unfolding hhl_out_def G I
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (vec_of_list [complex_of_real (sqrt 2) / 3, 2 / 3, complex_of_real (sqrt 2) / 3, - 1 / 3])"
    hence "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by auto
    thus "(tensor_vec (vec_of_list [complex_of_real (sqrt 2) / 3, complex_of_real (sqrt 2) / 3]) (unit_vec 2 0)
           + tensor_vec (vec_of_list [2 / 3, - 1 / 3]) (unit_vec 2 1)) $ i
          = vec_of_list [complex_of_real (sqrt 2) / 3, 2 / 3, complex_of_real (sqrt 2) / 3, - 1 / 3] $ i"
      by (auto simp: tensor_vec_code vec_index_vCons)
  qed (simp add: tensor_vec_code)
qed

text \<open>The output: $\ket{000}$ goes to $\ket0\otimes\big(\tfrac{\sqrt2}3\ket{00}+\tfrac23\ket{01}
+\tfrac{\sqrt2}3\ket{10}-\tfrac13\ket{11}\big)$; the ancilla-$1$ branch is $A^{-1}b=(\tfrac23,-\tfrac13)$.\<close>

theorem demo_output:
  "run_gates (unit_vec 32 0) demo_gates
   = tensor_vec (unit_vec 8 0) (vec_of_list [complex_of_real (sqrt 2) / 3, 2 / 3, complex_of_real (sqrt 2) / 3, - 1 / 3])"
  unfolding demo_run demo_out ..

lemma demo_solution_norm: "\<parallel>herm_inv demo_A *\<^sub>v unit_vec 2 0\<parallel> = sqrt 5 / 3"
proof -
  have "\<parallel>herm_inv demo_A *\<^sub>v unit_vec 2 0\<parallel> = sqrt (5 / 9)"
    unfolding demo_solution cpx_vec_length_def by (simp add: numeral_2_eq_2 power2_eq_square)
  thus ?thesis by (simp add: real_sqrt_divide)
qed

lemma demo_target:
  "hhl_target demo_A 3 (unit_vec 2 0) = tensor_vec (unit_vec 8 0)
     (tensor_vec (vec_of_list [2 / complex_of_real (sqrt 5), - 1 / complex_of_real (sqrt 5)]) (unit_vec 2 1))"
proof -
  have "complex_of_real (1 / (sqrt 5 / 3)) \<cdot>\<^sub>v vec_of_list [2 / 3, - 1 / 3]
        = vec_of_list [2 / complex_of_real (sqrt 5), - 1 / complex_of_real (sqrt 5)]"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (vec_of_list [2 / complex_of_real (sqrt 5), - 1 / complex_of_real (sqrt 5)])"
    hence "i = 0 \<or> i = 1" by auto
    thus "(complex_of_real (1 / (sqrt 5 / 3)) \<cdot>\<^sub>v vec_of_list [2 / 3, - 1 / 3]) $ i
          = vec_of_list [2 / complex_of_real (sqrt 5), - 1 / complex_of_real (sqrt 5)] $ i"
      by (auto simp: vec_index_vCons field_simps)
  qed simp
  thus ?thesis unfolding hhl_target_def demo_solution_norm unfolding demo_solution by simp
qed

text \<open>The program's Hoare triples: on success the state is $\ket0\otimes\frac{(2,-1)}{\sqrt5}\otimes\ket1$
(@{thm [source] demo_target}), and success has probability at least $\frac59$.\<close>

theorem demo_correct:
  "state_sig.hoare_total_correct [8, 2, 2] (1\<^sub>m 32) (hhl_program demo_A (1\<^sub>m 2) (pi / 4) 3 1)
     (anc_proj 32 0 + outer_prod (hhl_target demo_A 3 (unit_vec 2 0)) (hhl_target demo_A 3 (unit_vec 2 0)))"
  using hhl_correct_total[OF demo_A_carrier demo_A_hermitian _ _ _ demo_spec demo_Ub demo_Cb] by simp

theorem demo_success:
  "state_sig.hoare_total_correct [8, 2, 2] (complex_of_real (5 / 9) \<cdot>\<^sub>m 1\<^sub>m 32)
     (hhl_program demo_A (1\<^sub>m 2) (pi / 4) 3 1) (anc_proj 32 1)"
  using hhl_success_total[OF demo_A_carrier demo_A_hermitian _ _ _ demo_spec demo_Ub demo_Cb]
  by (simp add: demo_solution_norm power_divide)

subsection \<open>Running it\<close>

text \<open>\<open>show_state\<close> lists the nonzero amplitudes with their basis states
$\ket{\text{clock},\text{system},\text{ancilla}}$.  The $i$-th entry of the trace is
\<open>hhl_states \<dots> ! i\<close> by @{thm [source] demo_trajectory}.\<close>

definition show_cpx :: "complex \<Rightarrow> string" where
  "show_cpx z = (if Im z = 0 then show (Re z) else if Re z = 0 then show (Im z) @ ''i''
                 else ''('' @ show (Re z) @ '' + '' @ show (Im z) @ ''i)'')"

definition show_state :: "complex Matrix.vec \<Rightarrow> string list" where
  "show_state v = [show_cpx (v $ r) @ '' |'' @ show (r div 4) @ '','' @ show (r mod 4 div 2) @ '','' @ show (r mod 2) @ ''>''.
                    r \<leftarrow> [0..<dim_vec v], v $ r \<noteq> 0]"

definition demo_trace :: "string list list" where
  "demo_trace = map (\<lambda>i. show_state (run_gates (unit_vec 32 0) (take i demo_gates))) [0..<9]"

value [code] "demo_trace"

text \<open>The success probability, $\norm{A^{-1}b}^2=\frac59$, from the computed final state.\<close>

value [code] "let v = run_gates (unit_vec 32 0) demo_gates in
              show (\<Sum>r\<leftarrow>[0..<32]. if odd r then (Re (v $ r))\<^sup>2 + (Im (v $ r))\<^sup>2 else 0)"

text \<open>The computed output agrees with @{thm [source] demo_output}.\<close>

value [code] "run_gates (unit_vec 32 0) demo_gates
   = tensor_vec (unit_vec 8 0) (vec_of_list [complex_of_real (sqrt 2) / 3, 2 / 3, complex_of_real (sqrt 2) / 3, - 1 / 3])"

end
