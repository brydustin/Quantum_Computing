theory HHL_Gate_Refinements
  imports HHL_Paper_Program
begin

section \<open>Decomposing the remaining large gates\<close>

text \<open>Three refinements of the HHL programs.  The eigenvalue-controlled rotation becomes one
ancilla rotation per clock value $c$, controlled on the whole clock register (\<open>circuit_vctrl\<close>);
with it every gate of the program is elementary, a singly controlled $U^{\pm2^j}$, the preparation
of $\ket b$, or such a value-controlled rotation (\<open>hhl_split_gate_kinds\<close>).  The window state is
prepared by one Householder reflection (\<open>win_reflection\<close>), so the paper-regime programs need no
preparation gate beyond $U_b$ (\<open>hhl_apx_program_prepared\<close>, \<open>hhl_flag_program_prepared\<close>).
Programs with equal circuit matrices have equal denotations (\<open>prog_meas_cong\<close>), so the Fourier
gates inside the paper-regime circuits, including the amplitude-amplified one, can be replaced by
the AFP gate-level circuit (\<open>hhl_apx_fine\<close>).\<close>

subsection \<open>The controlled rotation as one controlled rotation per clock value\<close>

text \<open>\<open>vctrl N m c B\<close> applies $B$ to the second register when the first holds $c$: a single
gate on the ancilla, controlled on all clock qubits (pattern $c$).\<close>

definition vctrl :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "vctrl N m c B = ctrl_blocks N m (\<lambda>c'. if c' = c then B else 1\<^sub>m m)"

lemma vctrl_carrier [simp]: "vctrl N m c B \<in> carrier_mat (N * m) (N * m)"
  by (simp add: vctrl_def)

lemma vctrl_basis:
  assumes c': "c' < N" and w: "dim_vec w = m" and B: "B \<in> carrier_mat m m"
  shows "vctrl N m c B *\<^sub>v tensor_vec (unit_vec N c') w = tensor_vec (unit_vec N c') (if c' = c then B *\<^sub>v w else w)"
  unfolding vctrl_def using ctrl_blocks_basis[OF c' w, of "\<lambda>c'. if c' = c then B else 1\<^sub>m m"] B w
  by (auto simp: one_mult_mat_vec[OF carrier_vecI[OF w]])

lemma vctrl_unitary:
  assumes B: "B \<in> carrier_mat m m" "Quantum.unitary B"
  shows "Quantum.unitary (vctrl N m c B)"
  unfolding vctrl_def by (rule ctrl_blocks_unitary) (use B in \<open>auto simp: id_is_unitary\<close>)

lemma circuit_vctrl_upto:
  assumes B: "\<And>c. c < N \<Longrightarrow> B c \<in> carrier_mat m m"
  shows "j \<le> N \<Longrightarrow> circuit_mat (N * m) (map (\<lambda>c. vctrl N m c (B c)) [0..<j])
                   = ctrl_blocks N m (\<lambda>c'. if c' < j then B c' else 1\<^sub>m m)"
proof (induction j)
  case 0
  show ?case using ctrl_blocks_one[of N m] by simp
next
  case (Suc j)
  have IH: "circuit_mat (N * m) (map (\<lambda>c. vctrl N m c (B c)) [0..<j]) = ctrl_blocks N m (\<lambda>c'. if c' < j then B c' else 1\<^sub>m m)"
    using Suc by simp
  have bj: "B j \<in> carrier_mat m m" using B Suc.prems by simp
  have "circuit_mat (N * m) (map (\<lambda>c. vctrl N m c (B c)) [0..<Suc j])
        = vctrl N m j (B j) * circuit_mat (N * m) (map (\<lambda>c. vctrl N m c (B c)) [0..<j])"
  proof -
    have "map (\<lambda>c. vctrl N m c (B c)) [0..<Suc j] = map (\<lambda>c. vctrl N m c (B c)) [0..<j] @ [vctrl N m j (B j)]" by simp
    moreover have "circuit_mat (N * m) (map (\<lambda>c. vctrl N m c (B c)) [0..<j] @ [vctrl N m j (B j)])
                   = circuit_mat (N * m) [vctrl N m j (B j)] * circuit_mat (N * m) (map (\<lambda>c. vctrl N m c (B c)) [0..<j])"
      by (rule circuit_mat_append) auto
    ultimately show ?thesis using left_mult_one_mat[OF vctrl_carrier] by (simp del: upt_Suc)
  qed
  also have "\<dots> = ctrl_blocks N m (\<lambda>c'. (if c' = j then B j else 1\<^sub>m m) * (if c' < j then B c' else 1\<^sub>m m))"
    unfolding IH by (unfold vctrl_def, rule ctrl_blocks_mult) (use bj B Suc.prems in auto)
  also have "\<dots> = ctrl_blocks N m (\<lambda>c'. if c' < Suc j then B c' else 1\<^sub>m m)"
  proof (rule ctrl_blocks_cong)
    fix c' assume "c' < N"
    hence bc: "B c' \<in> carrier_mat m m" using B by simp
    show "(if c' = j then B j else 1\<^sub>m m) * (if c' < j then B c' else 1\<^sub>m m) = (if c' < Suc j then B c' else 1\<^sub>m m)"
    proof (cases "c' = j")
      case True thus ?thesis using bc by (simp add: right_mult_one_mat)
    qed (use bc in \<open>auto simp: left_mult_one_mat\<close>)
  qed
  finally show ?case .
qed

theorem circuit_vctrl:
  assumes B: "\<And>c. c < N \<Longrightarrow> B c \<in> carrier_mat m m"
  shows "circuit_mat (N * m) (map (\<lambda>c. vctrl N m c (B c)) [0..<N]) = ctrl_blocks N m B"
proof -
  have "circuit_mat (N * m) (map (\<lambda>c. vctrl N m c (B c)) [0..<N]) = ctrl_blocks N m (\<lambda>c'. if c' < N then B c' else 1\<^sub>m m)"
    by (rule circuit_vctrl_upto) (use B in auto)
  also have "\<dots> = ctrl_blocks N m B" by (rule ctrl_blocks_cong) simp
  finally show ?thesis .
qed

definition rot_gates :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "rot_gates A t0 k C = map (\<lambda>c. vctrl (2 ^ k) (dim_row A * 2) c (hhl_rot C t0 (2 ^ k) (dim_row A) c)) [0..<2 ^ k]"

lemma rot_gates_circuit: "circuit_mat (2 ^ k * (dim_row A * 2)) (rot_gates A t0 k C) = rot_gate A t0 (2 ^ k) C"
  unfolding rot_gates_def rot_gate_def by (rule circuit_vctrl) simp

lemma length_rot_gates [simp]: "length (rot_gates A t0 k C) = 2 ^ k" by (simp add: rot_gates_def)


definition hhl_split_blocks :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list list" where
  "hhl_split_blocks A Ub t0 k C = (hhl_blocks A Ub t0 k C)[4 := rot_gates A t0 k C]"

definition hhl_split_gates :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "hhl_split_gates A Ub t0 k C = concat (hhl_split_blocks A Ub t0 k C)"

definition hhl_split_program :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> com" where
  "hhl_split_program A Ub t0 k C = hhl_prog (2 ^ k * (dim_row A * 2)) (hhl_split_gates A Ub t0 k C)"

definition hhl_split_rus :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> com" where
  "hhl_split_rus A Ub t0 k C = hhl_rus_prog (2 ^ k * (dim_row A * 2)) (hhl_split_gates A Ub t0 k C)"

context
  fixes A Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
begin


lemma rot_gates_ok:
  "U \<in> set (rot_gates A t0 k C) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
proof -
  assume "U \<in> set (rot_gates A t0 k C)"
  then obtain c where c: "c < 2 ^ k" and U: "U = vctrl (2 ^ k) (n * 2) c (hhl_rot C t0 (2 ^ k) n c)"
    unfolding rot_gates_def carrier_matD(1)[OF A(1)] by auto
  have r: "Quantum.unitary (rot (C / reg_eig t0 (2 ^ k) c))" by (rule rot_unitary[OF Cb[OF c]])
  have u: "Quantum.unitary (hhl_rot C t0 (2 ^ k) n c)" using r by simp
  have uc: "Quantum.unitary U" unfolding U by (rule vctrl_unitary[OF rot_blk_carrier u])
  have Uc: "U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))" unfolding U by simp
  show ?thesis using unitary_bridge[OF Uc uc] Uc by simp
qed

lemma split_gates_ok:
  "U \<in> set (hhl_split_gates A Ub t0 k C) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
proof -
  assume "U \<in> set (hhl_split_gates A Ub t0 k C)"
  then obtain B where B: "B \<in> set (hhl_split_blocks A Ub t0 k C)" and U: "U \<in> set B" unfolding hhl_split_gates_def by auto
  have "B = rot_gates A t0 k C \<or> B \<in> set (hhl_blocks A Ub t0 k C)"
    using B set_update_subset_insert[of "hhl_blocks A Ub t0 k C" 4 "rot_gates A t0 k C"] unfolding hhl_split_blocks_def by auto
  thus ?thesis
  proof
    assume "B = rot_gates A t0 k C" thus ?thesis using rot_gates_ok U by simp
  next
    assume "B \<in> set (hhl_blocks A Ub t0 k C)"
    hence "U \<in> set (hhl_elem_gates A Ub t0 k C)" using U unfolding hhl_elem_gates_def by auto
    thus ?thesis using elem_gates_ok[OF A n0 k t0 _ Ub Cb] spec by blast
  qed
qed

theorem hhl_split_circuit:
  "circuit_mat (2 ^ k * (n * 2)) (hhl_split_gates A Ub t0 k C) = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
proof -
  let ?D = "2 ^ k * (n * 2)"
  have "map (circuit_mat ?D) (hhl_split_blocks A Ub t0 k C) = (map (circuit_mat ?D) (hhl_blocks A Ub t0 k C))[4 := circuit_mat ?D (rot_gates A t0 k C)]"
    unfolding hhl_split_blocks_def by (simp add: map_update)
  also have "circuit_mat ?D (rot_gates A t0 k C) = rot_gate A t0 (2 ^ k) C" using rot_gates_circuit[of k A t0 C] carrier_matD(1)[OF A(1)] by simp
  also have "map (circuit_mat ?D) (hhl_blocks A Ub t0 k C) = hhl_gates A Ub t0 k C" by (rule hhl_blocks_circuit[OF A(1,2) n0 k Ub(1)])
  also have "(hhl_gates A Ub t0 k C)[4 := rot_gate A t0 (2 ^ k) C] = hhl_gates A Ub t0 k C" by (simp add: hhl_gates_def)
  finally have m: "map (circuit_mat ?D) (hhl_split_blocks A Ub t0 k C) = hhl_gates A Ub t0 k C" .
  show ?thesis unfolding hhl_split_gates_def m[symmetric]
    by (rule circuit_mat_concat) (use split_gates_ok in \<open>auto simp: hhl_split_gates_def\<close>)
qed

theorem hhl_split_success_total:
  "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * (n * 2)))
     (hhl_split_program A Ub t0 k C) (anc_proj (2 ^ k * (n * 2)) 1)"
  unfolding hhl_split_program_def carrier_matD(1)[OF A(1)]
  by (rule hhl_prog_success_total[OF A n0 k t0 spec Ub Cb split_gates_ok hhl_split_circuit])

theorem hhl_split_correct_total:
  "state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_split_program A Ub t0 k C)
     (anc_proj (2 ^ k * (n * 2)) 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_split_program_def carrier_matD(1)[OF A(1)]
  by (rule hhl_prog_correct_total[OF A n0 k t0 spec Ub Cb split_gates_ok hhl_split_circuit])

theorem hhl_split_rus_total:
  "C \<noteq> 0 \<Longrightarrow> state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_split_rus A Ub t0 k C)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_split_rus_def carrier_matD(1)[OF A(1)]
  by (rule hhl_rus_prog_total[OF A n0 k t0 spec Ub Cb split_gates_ok hhl_split_circuit])

text \<open>Every gate is elementary, a singly controlled $U^{\pm2^j}$, the preparation of $\ket b$, or a
rotation of the ancilla controlled on one value $c$ of the clock register.\<close>

theorem hhl_split_gate_kinds:
  assumes U: "U \<in> set (hhl_split_gates A Ub t0 k C)"
  shows "elementary (2 ^ k * (n * 2)) U
         \<or> (\<exists>j<k. U = ctrl_bit (2 ^ k) (n * 2) j ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)
                 \<or> U = ctrl_bit (2 ^ k) (n * 2) j (((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)\<^sup>\<dagger>))
         \<or> U = prep_gate (2 ^ k) Ub
         \<or> (\<exists>c<2 ^ k. U = vctrl (2 ^ k) (n * 2) c (1\<^sub>m n \<Otimes> rot (C / reg_eig t0 (2 ^ k) c)))"
proof -
  let ?E = "evolution A t0 \<Otimes> 1\<^sub>m 2" and ?D = "2 ^ k * (n * 2)"
  have Ec: "?E \<in> carrier_mat (n * 2) (n * 2)" by (rule blocks_E_carrier[OF A(1,2) n0 k Ub(1)])
  have h: "\<forall>U \<in> set (clk_gates n (had_gates k)). elementary ?D U" by (rule clk_gates_elementary[OF had_ok[OF A(1,2) n0 k Ub(1)] n0])
  have fi: "\<forall>U \<in> set (clk_gates n (rev (map dagger (qft_circuit k)))). elementary ?D U"
    by (rule clk_gates_elementary[OF qft_inv_circuit(2) n0])
  have f: "\<forall>U \<in> set (clk_gates n (qft_circuit k)). elementary ?D U"
    by (rule clk_gates_elementary) (use qft_circuit(2) n0 in auto)
  have ei: "U \<in> set (rev (map dagger (evo_gates A t0 k))) \<Longrightarrow> \<exists>j<k. U = ctrl_bit (2 ^ k) (n * 2) j ((?E ^\<^sub>m 2 ^ j)\<^sup>\<dagger>)" for U
    unfolding evo_gates_def carrier_matD(1)[OF A(1)] using ctrl_bit_dagger[OF pow_carrier_mat[OF Ec]] by auto
  have e: "U \<in> set (evo_gates A t0 k) \<Longrightarrow> \<exists>j<k. U = ctrl_bit (2 ^ k) (n * 2) j (?E ^\<^sub>m 2 ^ j)" for U
    unfolding evo_gates_def carrier_matD(1)[OF A(1)] by auto
  have r: "U \<in> set (rot_gates A t0 k C) \<Longrightarrow> \<exists>c<2 ^ k. U = vctrl (2 ^ k) (n * 2) c (1\<^sub>m n \<Otimes> rot (C / reg_eig t0 (2 ^ k) c))" for U
    unfolding rot_gates_def carrier_matD(1)[OF A(1)] by auto
  have "U = prep_gate (2 ^ k) Ub \<or> U \<in> set (clk_gates n (had_gates k)) \<or> U \<in> set (evo_gates A t0 k)
        \<or> U \<in> set (clk_gates n (rev (map dagger (qft_circuit k)))) \<or> U \<in> set (rot_gates A t0 k C)
        \<or> U \<in> set (clk_gates n (qft_circuit k)) \<or> U \<in> set (rev (map dagger (evo_gates A t0 k)))"
    using U unfolding hhl_split_gates_def hhl_split_blocks_def hhl_blocks_def carrier_matD(1)[OF A(1)] by auto
  thus ?thesis using h fi f e ei r by blast
qed

end


subsection \<open>The window-state preparation as one reflection\<close>

lemma win_state_first: "0 < N \<Longrightarrow> win_state N $ 0 = complex_of_real (sqrt (2 / real N) * sin (pi / (2 * real N)))"
  by (simp add: win_state_def win_coef_def)

lemma win_state_first_lt: assumes N: "2 \<le> N" shows "sqrt (2 / real N) * sin (pi / (2 * real N)) < 1"
proof -
  have N0: "0 < real N" using N by simp
  have q: "sqrt (2 / real N) \<le> 1" using N by simp
  have x0: "0 \<le> pi / (2 * real N)" using N0 by simp
  have x1: "pi / (2 * real N) \<le> pi / 4" using N by (intro divide_left_mono) simp_all
  have s: "sin (pi / (2 * real N)) \<le> pi / (2 * real N)" by (rule sin_x_le_x[OF x0])
  show ?thesis
  proof (cases "0 \<le> sin (pi / (2 * real N))")
    case True
    have "sqrt (2 / real N) * sin (pi / (2 * real N)) \<le> 1 * sin (pi / (2 * real N))" by (rule mult_right_mono[OF q True])
    also have "\<dots> \<le> pi / 4" using s x1 by simp
    also have "\<dots> < 1" using pi_less_4 by simp
    finally show ?thesis .
  next
    case False
    hence "sqrt (2 / real N) * sin (pi / (2 * real N)) \<le> 0" by (simp add: mult_nonneg_nonpos)
    thus ?thesis by simp
  qed
qed

lemma win_reflection:
  assumes N: "2 \<le> N"
  shows "householder (Day03_Unitary_Matrices.vec_normalize (unit_vec N 0 - win_state N)) \<in> carrier_mat N N" "Quantum.unitary (householder (Day03_Unitary_Matrices.vec_normalize (unit_vec N 0 - win_state N)))"
    "householder (Day03_Unitary_Matrices.vec_normalize (unit_vec N 0 - win_state N)) *\<^sub>v unit_vec N 0 = win_state N"
  using householder_props[OF dim_win_state win_state_norm[OF N] win_state_first win_state_first_lt[OF N]] N by auto

text \<open>The full preparation: the reflection on the clock register, $U_b$ on the system, nothing on
the ancilla or flag register of $e$ levels.\<close>

definition win_prep :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "win_prep N Ub e = householder (Day03_Unitary_Matrices.vec_normalize (unit_vec N 0 - win_state N)) \<Otimes> (Ub \<Otimes> 1\<^sub>m e)"

lemma win_prep_ok:
  assumes N: "2 \<le> N" and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
    and n0: "0 < n" and e0: "0 < e"
  shows "win_prep N Ub e \<in> carrier_mat (N * (n * e)) (N * (n * e))" "Quantum.unitary (win_prep N Ub e)"
    "win_prep N Ub e *\<^sub>v unit_vec (N * (n * e)) 0 = tensor_vec (win_state N) (tensor_vec b (unit_vec e 0))"
proof -
  note W = win_reflection[OF N]
  have I: "Ub \<Otimes> 1\<^sub>m e \<in> carrier_mat (n * e) (n * e)" by (rule tensor_carrier[OF Ub(1) one_carrier_mat])
  show "win_prep N Ub e \<in> carrier_mat (N * (n * e)) (N * (n * e))" unfolding win_prep_def by (rule tensor_carrier[OF W(1) I])
  show "Quantum.unitary (win_prep N Ub e)" unfolding win_prep_def
    by (rule tensor_mat_unitary[OF W(2) tensor_mat_unitary[OF Ub(2) id_is_unitary]])
  have N0: "0 < N" using N by simp
  have u: "unit_vec (N * (n * e)) 0 = tensor_vec (unit_vec N 0) (tensor_vec (unit_vec n 0) (unit_vec e 0))"
    using unit_vec_tensor[of n e] unit_vec_tensor[of N "n * e"] by simp
  show "win_prep N Ub e *\<^sub>v unit_vec (N * (n * e)) 0 = tensor_vec (win_state N) (tensor_vec b (unit_vec e 0))"
  proof -
    have d1: "dim_vec (tensor_vec (unit_vec n 0) (unit_vec e 0) :: complex Matrix.vec) = n * e" by (simp add: tensor_vec_dim)
    have "(householder (Day03_Unitary_Matrices.vec_normalize (unit_vec N 0 - win_state N)) \<Otimes> (Ub \<Otimes> 1\<^sub>m e)) *\<^sub>v tensor_vec (unit_vec N 0) (tensor_vec (unit_vec n 0) (unit_vec e 0))
          = tensor_vec (householder (Day03_Unitary_Matrices.vec_normalize (unit_vec N 0 - win_state N)) *\<^sub>v unit_vec N 0) ((Ub \<Otimes> 1\<^sub>m e) *\<^sub>v tensor_vec (unit_vec n 0) (unit_vec e 0))"
      by (rule tensor_mat_vec_mult[OF W(1) I]) (simp_all add: d1)
    also have "(Ub \<Otimes> 1\<^sub>m e) *\<^sub>v tensor_vec (unit_vec n 0) (unit_vec e 0) = tensor_vec (Ub *\<^sub>v unit_vec n 0) (1\<^sub>m e *\<^sub>v unit_vec e 0)"
      by (rule tensor_mat_vec_mult[OF Ub(1) one_carrier_mat]) simp_all
    also have "1\<^sub>m e *\<^sub>v unit_vec e 0 = (unit_vec e 0 :: complex Matrix.vec)" by (rule one_mult_mat_vec[OF unit_vec_carrier])
    finally show ?thesis unfolding u win_prep_def W(3) Ub(3) .
  qed
qed


text \<open>The paper-regime programs with this preparation: no assumed preparation gate remains
apart from $U_b$.\<close>

lemma norm1_dim_pos: "dim_vec b = n \<Longrightarrow> \<parallel>b\<parallel> = 1 \<Longrightarrow> 0 < n"
  by (cases n) (auto simp: cpx_vec_length_def)

theorem hhl_apx_program_prepared:
  fixes A V Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n N :: nat and t0 C \<theta> lmin \<epsilon> \<eta> :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real N"
      and V: "V \<in> carrier_mat n n" "Quantum.unitary V" and Vc: "V \<approx>\<^bsub>\<eta>\<^esub> evolution A t0" and eta: "0 \<le> \<eta>"
      and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
      and small: "\<epsilon> + 2 * real (N - 1) * \<eta> \<le> C * t0 / pi"
  shows "state_sig.hoare_total_correct [N, n, 2] (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b N C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m (N * (n * 2)))
     (prog_meas (N * (n * 2)) (anc_proj (N * (n * 2))) (qgates N (n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 N C (win_prep N Ub 2))))
     (outer_prod (apx_t A b N) (apx_t A b N))"
    and "state_sig.hoare_total_correct [N, n, 2] (complex_of_real (1 - (apx_e A b N C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (N * (n * 2)))
     (rus_meas (N * (n * 2)) (anc_proj (N * (n * 2))) (qgates N (n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 N C (win_prep N Ub 2))))
     (outer_prod (apx_t A b N) (apx_t A b N))"
proof -
  have n0: "0 < n" by (rule norm1_dim_pos[OF b])
  have two: "0 < (2::nat)" by simp
  note P = win_prep_ok[OF N Ub n0 two]
  show "state_sig.hoare_total_correct [N, n, 2] (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b N C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m (N * (n * 2)))
     (prog_meas (N * (n * 2)) (anc_proj (N * (n * 2))) (qgates N (n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 N C (win_prep N Ub 2))))
     (outer_prod (apx_t A b N) (apx_t A b N))"
    by (rule hhl_apx_program[OF A t0 N C th lmin spec b e NQ V Vc eta P small])
  show "state_sig.hoare_total_correct [N, n, 2] (complex_of_real (1 - (apx_e A b N C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (N * (n * 2)))
     (rus_meas (N * (n * 2)) (anc_proj (N * (n * 2))) (qgates N (n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 N C (win_prep N Ub 2))))
     (outer_prod (apx_t A b N) (apx_t A b N))"
    by (rule hhl_apx_rus[OF A t0 N C th lmin spec b e NQ V Vc eta P small])
qed

theorem hhl_flag_program_prepared:
  fixes A Ub :: "complex Matrix.mat" and G :: "nat \<Rightarrow> complex Matrix.mat" and b :: "complex Matrix.vec"
    and n N :: nat and \<kappa> t0 \<epsilon> :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and k1: "1 \<le> \<kappa>"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> 1 / \<kappa> \<le> l \<and> l \<le> 1"
      and t0: "0 < t0" "t0 \<le> pi / 2" and N: "2 \<le> N"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3 \<and> Quantum.unitary (G k)"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1"
      and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
      and e: "0 < \<epsilon>" "\<epsilon> * \<kappa> \<le> 1"
      and big: "12 * pi\<^sup>2 * sqrt (4 + 2 * pi\<^sup>2) * \<kappa> / \<epsilon> \<le> real N * t0"
  shows "state_sig.hoare_total_correct [N, n, 3] (complex_of_real ((1 / (4 * \<kappa>))\<^sup>2 * (1 - \<epsilon>\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m (N * (n * 3)))
     (prog_meas (N * (n * 3)) (flag_meas (N * (n * 3)) 3 (\<lambda>c. c = 1))
        (qgates N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (flag_full_prog N n G (win_prep N Ub 3))))
     (outer_prod (flg_t A b N) (flg_t A b N))"
    and "state_sig.hoare_total_correct [N, n, 3] (complex_of_real (1 - \<epsilon>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (N * (n * 3)))
     (rus_meas (N * (n * 3)) (flag_meas (N * (n * 3)) 3 (\<lambda>c. c = 1))
        (qgates N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (flag_full_prog N n G (win_prep N Ub 3))))
     (outer_prod (flg_t A b N) (flg_t A b N))"
proof -
  have three: "0 < (3::nat)" by simp
  note P = win_prep_ok[OF N Ub n0 three]
  show "state_sig.hoare_total_correct [N, n, 3] (complex_of_real ((1 / (4 * \<kappa>))\<^sup>2 * (1 - \<epsilon>\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m (N * (n * 3)))
     (prog_meas (N * (n * 3)) (flag_meas (N * (n * 3)) 3 (\<lambda>c. c = 1))
        (qgates N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (flag_full_prog N n G (win_prep N Ub 3))))
     (outer_prod (flg_t A b N) (flg_t A b N))"
    by (rule hhl_flag_program[OF A n0 k1 spec t0 N G Gh b P e big])
  show "state_sig.hoare_total_correct [N, n, 3] (complex_of_real (1 - \<epsilon>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (N * (n * 3)))
     (rus_meas (N * (n * 3)) (flag_meas (N * (n * 3)) 3 (\<lambda>c. c = 1))
        (qgates N (n * 3) (evolution A t0 \<Otimes> 1\<^sub>m 3) (flag_full_prog N n G (win_prep N Ub 3))))
     (outer_prod (flg_t A b N) (flg_t A b N))"
    by (rule hhl_flag_rus[OF A n0 k1 spec t0 N G Gh b P e big])
qed


subsection \<open>Elementary Fourier gates inside the paper-regime circuits\<close>

text \<open>Programs with the same circuit matrix have the same denotation.\<close>

context state_sig
begin

lemma denote_while_body_cong:
  assumes DS: "\<And>\<sigma>. \<sigma> \<in> carrier_mat d d \<Longrightarrow> DS \<sigma> = DS' \<sigma>" "\<And>\<sigma>. \<sigma> \<in> carrier_mat d d \<Longrightarrow> DS \<sigma> \<in> carrier_mat d d"
    and M1: "M1 \<in> carrier_mat d d"
  shows "\<rho> \<in> carrier_mat d d \<Longrightarrow> denote_while_n_iter M0 M1 DS j \<rho> = denote_while_n_iter M0 M1 DS' j \<rho>"
proof (induction j arbitrary: \<rho>)
  case 0 thus ?case by simp
next
  case (Suc j)
  have c: "M1 * \<rho> * adjoint M1 \<in> carrier_mat d d" using M1 Suc.prems by (auto intro: mult_carrier_mat adjoint_dim)
  show ?case unfolding denote_while_n_iter.simps DS(1)[OF c, symmetric] by (rule Suc.IH[OF DS(2)[OF c]])
qed

lemma prog_meas_cong:
  assumes d0: "0 < d" and Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and Us': "\<And>U. U \<in> set Us' \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and circ: "circuit_mat d Us' = circuit_mat d Us" and r: "\<rho> \<in> carrier_mat d d" and Mc: "M 0 \<in> carrier_mat d d"
  shows "denote (prog_meas d M Us') \<rho> = denote (prog_meas d M Us) \<rho>"
    and "denote (rus_meas d M Us') \<rho> = denote (rus_meas d M Us) \<rho>"
proof -
  have body0: "denote (init_com d ;; utrans_seq Vs) \<sigma> = trace \<sigma> \<cdot>\<^sub>m outer_prod (circuit_mat d Vs *\<^sub>v unit_vec d 0) (circuit_mat d Vs *\<^sub>v unit_vec d 0)"
    if "\<sigma> \<in> carrier_mat d d" "\<And>U. U \<in> set Vs \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" for \<sigma> Vs
    by (rule denote_init_circuit[OF d0]) (use that in auto)
  have body: "denote (init_com d ;; utrans_seq Us') \<sigma> = denote (init_com d ;; utrans_seq Us) \<sigma>" if "\<sigma> \<in> carrier_mat d d" for \<sigma>
  proof -
    have "denote (init_com d ;; utrans_seq Us') \<sigma> = trace \<sigma> \<cdot>\<^sub>m outer_prod (circuit_mat d Us' *\<^sub>v unit_vec d 0) (circuit_mat d Us' *\<^sub>v unit_vec d 0)"
      by (rule body0) (use that Us' in auto)
    also have "\<dots> = trace \<sigma> \<cdot>\<^sub>m outer_prod (circuit_mat d Us *\<^sub>v unit_vec d 0) (circuit_mat d Us *\<^sub>v unit_vec d 0)" unfolding circ ..
    also have "\<dots> = denote (init_com d ;; utrans_seq Us) \<sigma>" by (rule body0[symmetric]) (use that Us in auto)
    finally show ?thesis .
  qed
  have sq: "denote (prog_meas d M Vs) \<rho> = denote (Measure 2 M [SKIP, SKIP]) (denote (init_com d ;; utrans_seq Vs) \<rho>)" for Vs
    unfolding prog_meas_def by (rule denote.simps(3))
  show "denote (prog_meas d M Us') \<rho> = denote (prog_meas d M Us) \<rho>" unfolding sq body[OF r] ..
  have bc: "denote (init_com d ;; utrans_seq Us) \<sigma> \<in> carrier_mat d d" if "\<sigma> \<in> carrier_mat d d" for \<sigma>
  proof -
    have cc: "circuit_mat d Us \<in> carrier_mat d d" by (rule circuit_mat_carrier) (use Us in auto)
    have e: "denote (init_com d ;; utrans_seq Us) \<sigma> = trace \<sigma> \<cdot>\<^sub>m outer_prod (circuit_mat d Us *\<^sub>v unit_vec d 0) (circuit_mat d Us *\<^sub>v unit_vec d 0)"
      by (rule body0) (use that Us in auto)
    show ?thesis unfolding e
      using outer_prod_dim[OF mult_mat_vec_carrier[OF cc unit_vec_carrier] mult_mat_vec_carrier[OF cc unit_vec_carrier]] by simp
  qed
  have "denote (While (\<lambda>j. M (1 - j)) (init_com d ;; utrans_seq Us')) \<sigma> = denote (While (\<lambda>j. M (1 - j)) (init_com d ;; utrans_seq Us)) \<sigma>"
    if s: "\<sigma> \<in> carrier_mat d d" and M1: "M 0 \<in> carrier_mat d d" for \<sigma>
  proof -
    have it: "denote_while_n_iter (M 1) (M 0) (denote (init_com d ;; utrans_seq Us)) j \<sigma>
              = denote_while_n_iter (M 1) (M 0) (denote (init_com d ;; utrans_seq Us')) j \<sigma>" for j
      by (rule denote_while_body_cong[where DS = "denote (init_com d ;; utrans_seq Us)" and DS' = "denote (init_com d ;; utrans_seq Us')"])
         (use body bc M1 s in auto)
    have "denote_while (M 1) (M 0) (denote (init_com d ;; utrans_seq Us')) \<sigma> = denote_while (M 1) (M 0) (denote (init_com d ;; utrans_seq Us)) \<sigma>"
      unfolding denote_while_def denote_while_n.simps it ..
    thus ?thesis by simp
  qed
  note wh = this
  have sr: "denote (rus_meas d M Vs) \<rho> = denote (While (\<lambda>j. M (1 - j)) (init_com d ;; utrans_seq Vs)) (denote (init_com d ;; utrans_seq Vs) \<rho>)" for Vs
    unfolding rus_meas_def by (rule denote.simps(3))
  show "denote (rus_meas d M Us') \<rho> = denote (rus_meas d M Us) \<rho>" unfolding sr body[OF r] wh[OF bc[OF r] Mc] ..
qed

end


context state_sig
begin

theorem meas_transfer:
  assumes d0: "0 < d" and Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and Us': "\<And>U. U \<in> set Us' \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    and circ: "circuit_mat d Us' = circuit_mat d Us" and Mc: "M 0 \<in> carrier_mat d d"
  shows "hoare_total_correct P (prog_meas d M Us) Q \<Longrightarrow> hoare_total_correct P (prog_meas d M Us') Q"
    and "hoare_total_correct P (rus_meas d M Us) Q \<Longrightarrow> hoare_total_correct P (rus_meas d M Us') Q"
  unfolding hoare_total_correct_def density_states_def
  using prog_meas_cong[where Us = Us and Us' = Us' and M = M, OF d0 Us Us' circ _ Mc] by auto

end

text \<open>Replace the Fourier gates $F^\dagger\otimes I$ and $(F^\dagger\otimes I)^\dagger$ of a circuit on
$\C^{2^k}\otimes\C^m$ by the AFP gate-level Fourier circuit.\<close>

definition fref :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "fref k m U = (if U = (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m then map (\<lambda>V. V \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k)))
                 else if U = ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)\<^sup>\<dagger> then map (\<lambda>V. V \<Otimes> 1\<^sub>m m) (qft_circuit k) else [U])"

lemma fref_props:
  assumes U: "U \<in> carrier_mat (2 ^ k * m) (2 ^ k * m)" and m: "0 < m"
  shows "circuit_mat (2 ^ k * m) (fref k m U) = U"
    and "Wg \<in> set (fref k m U) \<Longrightarrow> Wg = U \<or> elementary (2 ^ k * m) Wg"
proof -
  have qc: "\<And>Wg. Wg \<in> set (qft_circuit k) \<Longrightarrow> Wg \<in> carrier_mat (2 ^ k) (2 ^ k)" using qft_circuit(2) elementary_unitary(1) by blast
  have qi: "\<And>Wg. Wg \<in> set (rev (map dagger (qft_circuit k))) \<Longrightarrow> Wg \<in> carrier_mat (2 ^ k) (2 ^ k)"
    using qft_inv_circuit(2) elementary_unitary(1) by blast
  have F: "fourier (2 ^ k) \<in> carrier_mat (2 ^ k) (2 ^ k)" by (rule fourier_carrier)
  have dd: "((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)\<^sup>\<dagger> = fourier (2 ^ k) \<Otimes> 1\<^sub>m m"
    unfolding hermite_cnj_of_tensor dagger_of_dagger_is_id by simp
  show "circuit_mat (2 ^ k * m) (fref k m U) = U"
  proof (cases "U = (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m")
    case True
    have "circuit_mat (2 ^ k * m) (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k))))
          = circuit_mat (2 ^ k) (rev (map dagger (qft_circuit k))) \<Otimes> 1\<^sub>m m"
      by (rule circuit_mat_tensor_right) (use qi m in auto)
    thus ?thesis unfolding fref_def using True qft_inv_circuit(1) by simp
  next
    case False
    show ?thesis
    proof (cases "U = ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)\<^sup>\<dagger>")
      case True
      have "circuit_mat (2 ^ k * m) (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (qft_circuit k)) = circuit_mat (2 ^ k) (qft_circuit k) \<Otimes> 1\<^sub>m m"
        by (rule circuit_mat_tensor_right) (use qc m in auto)
      thus ?thesis unfolding fref_def using False True qft_circuit(1) dd by simp
    next
      case False2: False
      thus ?thesis unfolding fref_def using False U by (simp add: left_mult_one_mat)
    qed
  qed
  show "Wg \<in> set (fref k m U) \<Longrightarrow> Wg = U \<or> elementary (2 ^ k * m) Wg"
  proof -
    assume w: "Wg \<in> set (fref k m U)"
    have e1: "\<forall>G \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k)))). elementary (2 ^ k * m) G"
      by (rule elementary_map_right[OF qft_inv_circuit(2) m])
    have q2: "\<forall>G \<in> set (qft_circuit k). elementary (2 ^ k) G" using qft_circuit(2) by blast
    have e2: "\<forall>G \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (qft_circuit k)). elementary (2 ^ k * m) G"
      by (rule elementary_map_right[OF q2 m])
    show ?thesis
    proof (cases "U = (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m")
      case True
      hence fr: "fref k m U = map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k)))" unfolding fref_def by simp
      have "Wg \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k))))" using w unfolding fr .
      thus ?thesis using e1 by blast
    next
      case False
      show ?thesis
      proof (cases "U = ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)\<^sup>\<dagger>")
        case True
        hence fr: "fref k m U = map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (qft_circuit k)" using False unfolding fref_def by simp
        have "Wg \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (qft_circuit k))" using w unfolding fr .
        thus ?thesis using e2 by blast
      next
        case False2: False thus ?thesis using w False unfolding fref_def by simp
      qed
    qed
  qed
qed

definition fine_gates :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "fine_gates k m Us = concat (map (fref k m) Us)"

lemma fine_gates_props:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * m) (2 ^ k * m) \<and> Complex_Matrix.unitary U" and m: "0 < m"
  shows "circuit_mat (2 ^ k * m) (fine_gates k m Us) = circuit_mat (2 ^ k * m) Us"
    and "\<And>Wg. Wg \<in> set (fine_gates k m Us) \<Longrightarrow> Wg \<in> carrier_mat (2 ^ k * m) (2 ^ k * m) \<and> Complex_Matrix.unitary Wg"
    and "\<And>Wg. Wg \<in> set (fine_gates k m Us) \<Longrightarrow> Wg \<in> set Us \<or> elementary (2 ^ k * m) Wg"
proof -
  show kind: "\<And>Wg. Wg \<in> set (fine_gates k m Us) \<Longrightarrow> Wg \<in> set Us \<or> elementary (2 ^ k * m) Wg"
  proof -
    fix Wg assume "Wg \<in> set (fine_gates k m Us)"
    then obtain U where U: "U \<in> set Us" and w: "Wg \<in> set (fref k m U)" unfolding fine_gates_def by auto
    have "Wg = U \<or> elementary (2 ^ k * m) Wg" by (rule fref_props(2)[OF conjunct1[OF Us[OF U]] m w])
    thus "Wg \<in> set Us \<or> elementary (2 ^ k * m) Wg" using U by blast
  qed
  show ok: "\<And>Wg. Wg \<in> set (fine_gates k m Us) \<Longrightarrow> Wg \<in> carrier_mat (2 ^ k * m) (2 ^ k * m) \<and> Complex_Matrix.unitary Wg"
  proof -
    fix Wg assume "Wg \<in> set (fine_gates k m Us)"
    hence "Wg \<in> set Us \<or> elementary (2 ^ k * m) Wg" by (rule kind)
    thus "Wg \<in> carrier_mat (2 ^ k * m) (2 ^ k * m) \<and> Complex_Matrix.unitary Wg"
      using Us elementary_unitary unitary_bridge by blast
  qed
  have "circuit_mat (2 ^ k * m) (fine_gates k m Us) = circuit_mat (2 ^ k * m) (map (circuit_mat (2 ^ k * m)) (map (fref k m) Us))"
    unfolding fine_gates_def by (rule circuit_mat_concat) (use ok in \<open>auto simp: fine_gates_def\<close>)
  also have "map (circuit_mat (2 ^ k * m)) (map (fref k m) Us) = Us"
    unfolding map_map comp_def by (rule map_idI) (rule fref_props(1)[OF conjunct1[OF Us] m])
  finally show "circuit_mat (2 ^ k * m) (fine_gates k m Us) = circuit_mat (2 ^ k * m) Us" .
qed


text \<open>For a clock register of $k$ qubits ($N=2^k$), the single run and the amplitude-amplified
program of the paper's regime, with every Fourier transform in elementary gates.\<close>

theorem hhl_apx_fine:
  fixes A V Prep :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C \<theta> lmin \<epsilon> \<eta> :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and k: "1 \<le> k"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real (2 ^ k)"
      and V: "V \<in> carrier_mat n n" "Quantum.unitary V" and Vc: "V \<approx>\<^bsub>\<eta>\<^esub> evolution A t0" and eta: "0 \<le> \<eta>"
      and Prep: "Prep \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))" "Quantum.unitary Prep"
        "Prep *\<^sub>v unit_vec (2 ^ k * (n * 2)) 0 = tensor_vec (win_state (2 ^ k)) (tensor_vec b (unit_vec 2 0))"
      and small: "\<epsilon> + 2 * real (2 ^ k - 1) * \<eta> \<le> C * t0 / pi"
  defines "c \<equiv> hhl_full_prog A t0 (2 ^ k) C Prep" and "K \<equiv> 2 ^ k * (n * 2)"
  shows "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
     (prog_meas K (anc_proj K) (fine_gates k (n * 2) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c)))
     (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    and "\<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel> < 1 \<Longrightarrow> \<exists>j. calls (aa_prog K 2 (\<lambda>c. c = 1) c j) = (2 * j + 1) * (2 * (2 ^ k - 1))
           \<and> real j \<le> pi\<^sup>2 / (4 * C * t0)
           \<and> state_sig.hoare_total_correct [2 ^ k, n, 2]
               (complex_of_real ((1 - \<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel>\<^sup>2) * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
               (prog_meas K (anc_proj K) (fine_gates k (n * 2) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j))))
               (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    and "\<And>j U. U \<in> set (fine_gates k (n * 2) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)))
           \<Longrightarrow> U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<or> elementary K U"
proof -
  have N: "2 \<le> (2::nat) ^ k" using power_increasing[of 1 k "2::nat"] k by simp
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = K" by (simp add: d_def K_def)
  note ab = apx_basics[OF A t0 N C th lmin spec b e NQ V Vc eta Prep small]
  have m0: "0 < n * 2" using ab(1) by simp
  have Mc: "anc_proj d 0 \<in> carrier_mat d d" by simp
  have ok: "\<And>U. U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c') \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    if g: "gates_ok K c'" for c'
    using qgates_ok[OF ab(2,3) g[unfolded K_def]] dd K_def by simp
  have tr: "hoare_total_correct P (prog_meas d (anc_proj d) (fine_gates k (n * 2) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c'))) Q"
    if g: "gates_ok K c'" and h: "hoare_total_correct P (prog_meas d (anc_proj d) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c')) Q" for c' P Q
  proof -
    note f = fine_gates_props[where k = k and m = "n * 2" and Us = "qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c'", OF ok[OF g, unfolded dd K_def] m0]
    show ?thesis
      by (rule meas_transfer(1)[OF _ ok[OF g] _ _ Mc h]) (use ab(1) f(1,2) dd K_def in auto)
  qed
  show "hoare_total_correct (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
     (prog_meas K (anc_proj K) (fine_gates k (n * 2) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c)))
     (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
  proof -
    have g0: "gates_ok K c" unfolding K_def c_def by (rule ab(4))
    have h0: "hoare_total_correct (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m d)
       (prog_meas d (anc_proj d) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c)) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
      unfolding dd K_def c_def by (rule hhl_apx_program[OF A t0 N C th lmin spec b e NQ V Vc eta Prep small])
    show ?thesis using tr[OF g0 h0] unfolding dd .
  qed
  show "\<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel> < 1 \<Longrightarrow> \<exists>j. calls (aa_prog K 2 (\<lambda>c. c = 1) c j) = (2 * j + 1) * (2 * (2 ^ k - 1))
           \<and> real j \<le> pi\<^sup>2 / (4 * C * t0)
           \<and> hoare_total_correct
               (complex_of_real ((1 - \<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel>\<^sup>2) * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
               (prog_meas K (anc_proj K) (fine_gates k (n * 2) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j))))
               (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
  proof -
    assume y1: "\<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel> < 1"
    obtain j where j1: "calls (aa_prog K 2 (\<lambda>c. c = 1) c j) = (2 * j + 1) * (2 * (2 ^ k - 1))" and j2: "real j \<le> pi\<^sup>2 / (4 * C * t0)"
      and j3: "hoare_total_correct
           (complex_of_real ((1 - \<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel>\<^sup>2) * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas K (anc_proj K) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j))) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
      unfolding c_def K_def by (rule hhl_apx_amplified[OF A t0 N C th lmin spec b e NQ V Vc eta Prep small y1[unfolded c_def]])
    have g: "gates_ok K (aa_prog K 2 (\<lambda>c. c = 1) c j)" unfolding K_def c_def by (rule gates_ok_aa_prog[OF ab(4)])
    have j3': "hoare_total_correct
           (complex_of_real ((1 - \<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel>\<^sup>2) * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas d (anc_proj d) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j))) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
      using j3 unfolding dd .
    show ?thesis using j1 j2 tr[OF g j3'] unfolding dd by blast
  qed
  show "\<And>j U. U \<in> set (fine_gates k (n * 2) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)))
           \<Longrightarrow> U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<or> elementary K U"
  proof -
    fix j U assume U: "U \<in> set (fine_gates k (n * 2) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)))"
    have g: "gates_ok K (aa_prog K 2 (\<lambda>c. c = 1) c j)" unfolding K_def c_def by (rule gates_ok_aa_prog[OF ab(4)])
    have okU: "\<And>W. W \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<Longrightarrow>
               W \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary W"
      using qgates_ok[OF ab(2,3), where c = "aa_prog K 2 (\<lambda>c. c = 1) c j"] g by (simp add: K_def)
    have "U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<or> elementary (2 ^ k * (n * 2)) U"
      by (rule fine_gates_props(3)[OF okU m0 U])
    thus "U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<or> elementary K U" by (simp add: K_def)
  qed
qed

end
