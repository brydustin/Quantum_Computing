theory Toffoli_Gates
  imports HHL_Algorithm.HHL_All_Elementary
begin

section \<open>The Toffoli gate from two-qubit gates\<close>

text \<open>Barenco et al.: with $V^2 = X$, the Toffoli gate is
$C_bV \cdot \mathrm{CNOT}_{ab} \cdot C_bV^\dagger \cdot \mathrm{CNOT}_{ab} \cdot C_aV$.
On three wires write $c = 2a + b$ for the two controls and keep the target as the low qubit.
Every factor is block diagonal over $c$, up to a permutation of $c$, so the identity reduces
to products of $2 \times 2$ blocks.\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{quantikz}[row sep=0.35cm, column sep=0.4cm]
\lstick{$a$} & \ctrl{2} & \qw \\
\lstick{$b$} & \ctrl{1} & \qw \\
\lstick{$t$} & \targ{} & \qw
\end{quantikz}
\;=\;
\begin{quantikz}[row sep=0.35cm, column sep=0.4cm]
\lstick{$a$} & \ctrl{2} & \ctrl{1} & \qw & \ctrl{1} & \qw & \qw \\
\lstick{$b$} & \qw & \targ{} & \ctrl{1} & \targ{} & \ctrl{1} & \qw \\
\lstick{$t$} & \gate{V} & \qw & \gate{V^\dagger} & \qw & \gate{V} & \qw
\end{quantikz}
\qquad $V^2 = X$ \\[0.3em]
{\small Time runs left to right: the product above, read from the right.}
\end{center}
\<close>

definition sqx :: "complex Matrix.mat" where
  "sqx = Matrix.mat 2 2 (\<lambda>(r, c). if r = c then (1 + \<i>) / 2 else (1 - \<i>) / 2)"

definition notm :: "complex Matrix.mat" where "notm = pmat 2 (\<lambda>t. 1 - t)"

lemma sqx_carrier [simp]: "sqx \<in> carrier_mat 2 2" by (simp add: sqx_def)

lemma sqx_sq: "sqx * sqx = notm"
  by (rule eq_matI) (auto simp: sqx_def notm_def pmat_def scalar_prod_def numeral_2_eq_2 atLeast0LessThan
      lessThan_Suc less_Suc_eq complex_eq_iff)

lemma sqx_dagger: "sqx\<^sup>\<dagger> = Matrix.mat 2 2 (\<lambda>(r, c). if r = c then (1 - \<i>) / 2 else (1 + \<i>) / 2)"
  by (rule eq_matI) (auto simp: sqx_def dagger_def numeral_2_eq_2 less_Suc_eq complex_cnj_divide)

lemma sqx_unitary: "(sqx\<^sup>\<dagger>) * sqx = 1\<^sub>m 2" "sqx * (sqx\<^sup>\<dagger>) = 1\<^sub>m 2"
  unfolding sqx_dagger by (rule eq_matI; auto simp: sqx_def scalar_prod_def numeral_2_eq_2 atLeast0LessThan
      lessThan_Suc less_Suc_eq complex_eq_iff)+

definition cblk :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "cblk Q b = (if b = 1 then Q else 1\<^sub>m 2)"

lemma cblk_carrier: "Q \<in> carrier_mat 2 2 \<Longrightarrow> cblk Q b \<in> carrier_mat 2 2" by (simp add: cblk_def)

text \<open>Controlled-$Q$ on two wires (control high), and the three-wire gates.\<close>

definition cv :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where "cv Q = ctrl_blocks 2 2 (cblk Q)"

abbreviation sw8 :: "complex Matrix.mat" where "sw8 \<equiv> pmat 4 gs \<Otimes> 1\<^sub>m 2"
abbreviation cn8 :: "complex Matrix.mat" where "cn8 \<equiv> pmat 4 gc \<Otimes> 1\<^sub>m 2"

definition tof8 :: "complex Matrix.mat" where
  "tof8 = ctrl_blocks 4 2 (\<lambda>c. if c = 3 then notm else 1\<^sub>m 2)"

definition tof_gates :: "complex Matrix.mat list" where
  "tof_gates = [sw8, 1\<^sub>m 2 \<Otimes> cv sqx, sw8, cn8, 1\<^sub>m 2 \<Otimes> cv (sqx\<^sup>\<dagger>), cn8, 1\<^sub>m 2 \<Otimes> cv sqx]"

lemma length_tof_gates: "length tof_gates = 7" by (simp add: tof_gates_def)

lemma low_cv:
  assumes "Q \<in> carrier_mat 2 2"
  shows "1\<^sub>m 2 \<Otimes> cv Q = ctrl_blocks 4 2 (\<lambda>c. cblk Q (c mod 2))"
  using ctrl_blocks_mod2[of "cblk Q" 2 2] cblk_carrier[OF assms] by (simp add: cv_def)

lemma conj4:
  assumes f: "\<And>t. t < 4 \<Longrightarrow> f t < 4" "\<And>t. t < 4 \<Longrightarrow> f (f t) = t" and B: "\<And>c. c < 4 \<Longrightarrow> B c \<in> carrier_mat 2 2"
  shows "circuit_mat 8 [pmat 4 f \<Otimes> 1\<^sub>m 2, ctrl_blocks 4 2 B, pmat 4 f \<Otimes> 1\<^sub>m 2] = ctrl_blocks 4 2 (\<lambda>c. B (f c))"
proof -
  have P: "pmat 4 f \<Otimes> 1\<^sub>m 2 \<in> carrier_mat 8 8" using tensor_carrier[OF pmat_carrier one_carrier_mat, of 4 f 2] by simp
  have "circuit_mat 8 [pmat 4 f \<Otimes> 1\<^sub>m 2, ctrl_blocks 4 2 B, pmat 4 f \<Otimes> 1\<^sub>m 2]
      = (pmat 4 f \<Otimes> 1\<^sub>m 2) * ctrl_blocks 4 2 B * (pmat 4 f \<Otimes> 1\<^sub>m 2)"
    using left_mult_one_mat[OF P] by simp
  also have "\<dots> = ctrl_blocks 4 2 (\<lambda>c. B (f c))" by (rule ctrl_conj) (use f B in auto)
  finally show ?thesis .
qed

lemma gs_gc_lt: "t < 4 \<Longrightarrow> gs t < 4" "t < 4 \<Longrightarrow> gs (gs t) = t" "t < 4 \<Longrightarrow> gc t < 4" "t < 4 \<Longrightarrow> gc (gc t) = t"
  by (auto simp: Transposition.transpose_def)

lemma gates8_carrier: "U \<in> set tof_gates \<Longrightarrow> U \<in> carrier_mat 8 8"
proof -
  have "1\<^sub>m 2 \<Otimes> cv Q \<in> carrier_mat 8 8" if "Q \<in> carrier_mat 2 2" for Q
    unfolding low_cv[OF that] using ctrl_blocks_carrier[of 4 2] by simp
  moreover have "pmat 4 f \<Otimes> 1\<^sub>m 2 \<in> carrier_mat 8 8" for f
    using tensor_carrier[OF pmat_carrier one_carrier_mat, of 4 f 2] by simp
  ultimately show "U \<in> set tof_gates \<Longrightarrow> U \<in> carrier_mat 8 8"
    unfolding tof_gates_def using dagger_carrier[OF sqx_carrier] by auto
qed

theorem tof_circuit: "circuit_mat 8 tof_gates = tof8"
proof -
  have sd: "sqx\<^sup>\<dagger> \<in> carrier_mat 2 2" by (rule dagger_carrier[OF sqx_carrier])
  have cb: "\<And>Q c. Q \<in> carrier_mat 2 2 \<Longrightarrow> cblk Q (c mod 2) \<in> carrier_mat 2 2" by (rule cblk_carrier)
  let ?A = "\<lambda>c. cblk sqx (gs c mod 2)" and ?B = "\<lambda>c. cblk (sqx\<^sup>\<dagger>) (gc c mod 2)" and ?C = "\<lambda>c. cblk sqx (c mod 2)"
  have c1: "circuit_mat 8 [sw8, 1\<^sub>m 2 \<Otimes> cv sqx, sw8] = ctrl_blocks 4 2 ?A"
    unfolding low_cv[OF sqx_carrier] by (rule conj4) (simp_all add: Transposition.transpose_def cb)
  have c2: "circuit_mat 8 [cn8, 1\<^sub>m 2 \<Otimes> cv (sqx\<^sup>\<dagger>), cn8] = ctrl_blocks 4 2 ?B"
    unfolding low_cv[OF sd] by (rule conj4) (simp_all add: Transposition.transpose_def cb sd)
  have c3: "circuit_mat 8 [1\<^sub>m 2 \<Otimes> cv sqx] = ctrl_blocks 4 2 ?C"
    unfolding low_cv[OF sqx_carrier] by (rule circuit_mat_single) (use ctrl_blocks_carrier[of 4 2 ?C] in simp)
  have split: "tof_gates = [sw8, 1\<^sub>m 2 \<Otimes> cv sqx, sw8] @ [cn8, 1\<^sub>m 2 \<Otimes> cv (sqx\<^sup>\<dagger>), cn8] @ [1\<^sub>m 2 \<Otimes> cv sqx]"
    by (simp add: tof_gates_def)
  have car: "\<And>U. U \<in> set [sw8, 1\<^sub>m 2 \<Otimes> cv sqx, sw8] \<Longrightarrow> U \<in> carrier_mat 8 8"
    "\<And>U. U \<in> set [cn8, 1\<^sub>m 2 \<Otimes> cv (sqx\<^sup>\<dagger>), cn8] \<Longrightarrow> U \<in> carrier_mat 8 8"
    "\<And>U. U \<in> set [1\<^sub>m 2 \<Otimes> cv sqx] \<Longrightarrow> U \<in> carrier_mat 8 8"
    using gates8_carrier unfolding tof_gates_def by auto
  have a1: "circuit_mat 8 ([cn8, 1\<^sub>m 2 \<Otimes> cv (sqx\<^sup>\<dagger>), cn8] @ [1\<^sub>m 2 \<Otimes> cv sqx])
      = circuit_mat 8 [1\<^sub>m 2 \<Otimes> cv sqx] * circuit_mat 8 [cn8, 1\<^sub>m 2 \<Otimes> cv (sqx\<^sup>\<dagger>), cn8]"
    by (rule circuit_mat_append[OF car(2) car(3)])
  have a0: "circuit_mat 8 tof_gates = circuit_mat 8 ([cn8, 1\<^sub>m 2 \<Otimes> cv (sqx\<^sup>\<dagger>), cn8] @ [1\<^sub>m 2 \<Otimes> cv sqx])
      * circuit_mat 8 [sw8, 1\<^sub>m 2 \<Otimes> cv sqx, sw8]"
    unfolding split by (rule circuit_mat_append) (use car in auto)
  have "circuit_mat 8 tof_gates = ctrl_blocks 4 2 ?C * ctrl_blocks 4 2 ?B * ctrl_blocks 4 2 ?A"
    unfolding a0 a1 c1 c2 c3 ..
  also have "\<dots> = ctrl_blocks 4 2 ?C * (ctrl_blocks 4 2 ?B * ctrl_blocks 4 2 ?A)"
    by (rule assoc_mult_mat) auto
  also have "\<dots> = ctrl_blocks 4 2 ?C * ctrl_blocks 4 2 (\<lambda>c. ?B c * ?A c)"
    by (rule arg_cong[where f = "\<lambda>M. ctrl_blocks 4 2 ?C * M"], rule ctrl_blocks_mult) (simp_all add: cb sd)
  also have "\<dots> = ctrl_blocks 4 2 (\<lambda>c. ?C c * (?B c * ?A c))"
    by (rule ctrl_blocks_mult) (auto intro!: mult_carrier_mat cb sd)
  also have "\<dots> = tof8" unfolding tof8_def
  proof (rule ctrl_blocks_cong)
    fix c :: nat assume "c < 4"
    hence "c = 0 \<or> c = 1 \<or> c = 2 \<or> c = 3" by auto
    thus "?C c * (?B c * ?A c) = (if c = 3 then notm else 1\<^sub>m 2)"
      by (elim disjE) (simp_all add: cblk_def Transposition.transpose_def sqx_unitary sqx_sq sd
          right_mult_one_mat[OF sd] left_mult_one_mat[OF sqx_carrier])
  qed
  finally show ?thesis .
qed

lemma elementary4:
  assumes "G \<in> carrier_mat 4 4" "Quantum.unitary G"
  shows "elementary 4 G"
proof -
  have "gate 2 G" using assms by (simp add: gate_def square_mat.simps)
  thus ?thesis using elementary_gate[of 2 G] by simp
qed

lemma elementary8_low: "G \<in> carrier_mat 4 4 \<Longrightarrow> Quantum.unitary G \<Longrightarrow> elementary 8 (1\<^sub>m 2 \<Otimes> G)"
  using elementary_left[OF elementary4, of G 2] by simp

lemma elementary8_high: "G \<in> carrier_mat 4 4 \<Longrightarrow> Quantum.unitary G \<Longrightarrow> elementary 8 (G \<Otimes> 1\<^sub>m 2)"
  using elementary_right[OF elementary4, of G 2] by simp

lemma cv_unitary:
  assumes "Q \<in> carrier_mat 2 2" "(Q\<^sup>\<dagger>) * Q = 1\<^sub>m 2" "Q * (Q\<^sup>\<dagger>) = 1\<^sub>m 2"
  shows "cv Q \<in> carrier_mat 4 4" "Quantum.unitary (cv Q)"
proof -
  show "cv Q \<in> carrier_mat 4 4" unfolding cv_def using ctrl_blocks_carrier[of 2 2] by simp
  have "Quantum.unitary (cblk Q k)" for k
    using assms id_is_unitary[of 2] by (cases "k = 1") (auto simp: cblk_def Quantum.unitary_def)
  thus "Quantum.unitary (cv Q)" unfolding cv_def by (intro ctrl_blocks_unitary) (simp_all add: cblk_carrier assms(1))
qed

theorem tof_gates_elementary: "U \<in> set tof_gates \<Longrightarrow> elementary 8 U"
proof -
  have sd: "sqx\<^sup>\<dagger> \<in> carrier_mat 2 2" by (rule dagger_carrier[OF sqx_carrier])
  have dd: "(sqx\<^sup>\<dagger>)\<^sup>\<dagger> = sqx" by (rule dagger_of_dagger_is_id)
  have p: "pmat 4 f \<in> carrier_mat 4 4 \<and> Quantum.unitary (pmat 4 f)" if "\<And>t. t < 4 \<Longrightarrow> f t < 4" "\<And>t. t < 4 \<Longrightarrow> f (f t) = t" for f
    using pmat_unitary_invol[OF that] by simp
  note v = cv_unitary[OF sqx_carrier sqx_unitary] and v' = cv_unitary[OF sd, unfolded dd, OF sqx_unitary(2,1)]
  show "U \<in> set tof_gates \<Longrightarrow> elementary 8 U"
    unfolding tof_gates_def using p[of gs] p[of gc] gs_gc_lt
    by (auto intro: elementary8_low elementary8_high v v')
qed

end
