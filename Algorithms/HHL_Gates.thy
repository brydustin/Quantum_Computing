theory HHL_Gates
  imports HHL_Program QFT_Fourier
begin

text \<open>The program of \<open>HHL_Program\<close> with every stage written as a list of gates: the Hadamard
layer as $k$ single-qubit Hadamards, the controlled evolution as one controlled $U^{2^j}$ per
clock qubit, and $F$ as the gate-level circuit of the AFP entry \<open>Quantum_Fourier_Transform\<close>
(Hadamards, controlled phase rotations, swaps; \<open>ordered_QFT_fourier\<close>).  The gate list has the
same circuit matrix as \<open>hhl_gates\<close>, so the theorems of \<open>HHL_Program\<close> hold for it.\<close>

section \<open>The HHL program in elementary gates\<close>

subsection \<open>Circuits of gate lists\<close>

lemma circuit_mat_append:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K" and "\<And>U. U \<in> set Vs \<Longrightarrow> U \<in> carrier_mat K K"
  shows "circuit_mat K (Us @ Vs) = circuit_mat K Vs * circuit_mat K Us"
proof -
  have Vc: "circuit_mat K Vs \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use assms(2) in auto)
  show ?thesis using assms(1)
  proof (induction Us)
    case Nil
    show ?case using Vc by simp
  next
    case (Cons U Us)
    have U: "U \<in> carrier_mat K K" and IH: "circuit_mat K (Us @ Vs) = circuit_mat K Vs * circuit_mat K Us" using Cons by auto
    have Uc: "circuit_mat K Us \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use Cons.prems in auto)
    have "circuit_mat K ((U # Us) @ Vs) = circuit_mat K Vs * circuit_mat K Us * U" using IH by simp
    also have "\<dots> = circuit_mat K Vs * (circuit_mat K Us * U)" by (rule assoc_mult_mat[OF Vc Uc U])
    finally show ?case by simp
  qed
qed

lemma circuit_mat_single: "U \<in> carrier_mat K K \<Longrightarrow> circuit_mat K [U] = U"
  by simp

lemma circuit_mat_concat:
  assumes "\<And>Us U. Us \<in> set Bs \<Longrightarrow> U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K"
  shows "circuit_mat K (concat Bs) = circuit_mat K (map (circuit_mat K) Bs)"
  using assms
proof (induction Bs)
  case (Cons Us Bs)
  have "circuit_mat K (concat (Us # Bs)) = circuit_mat K (concat Bs) * circuit_mat K Us"
    unfolding concat.simps by (rule circuit_mat_append) (use Cons.prems in auto)
  moreover have "circuit_mat K (concat Bs) = circuit_mat K (map (circuit_mat K) Bs)"
    by (rule Cons.IH) (use Cons.prems in auto)
  ultimately show ?case by simp
qed simp

lemma circuit_mat_tensor_right:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K" and K: "0 < K" and m: "0 < m"
  shows "circuit_mat (K * m) (map (\<lambda>U. U \<Otimes> 1\<^sub>m m) Us) = circuit_mat K Us \<Otimes> 1\<^sub>m m"
  using assms(1)
proof (induction Us)
  case Nil
  show ?case by (simp add: tensor_mat_id)
next
  case (Cons U Us)
  have U: "U \<in> carrier_mat K K" and IH: "circuit_mat (K * m) (map (\<lambda>U. U \<Otimes> 1\<^sub>m m) Us) = circuit_mat K Us \<Otimes> 1\<^sub>m m"
    using Cons by auto
  have Cc: "circuit_mat K Us \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use Cons.prems in auto)
  have "circuit_mat (K * m) (map (\<lambda>U. U \<Otimes> 1\<^sub>m m) (U # Us)) = (circuit_mat K Us \<Otimes> 1\<^sub>m m) * (U \<Otimes> 1\<^sub>m m)" using IH by simp
  also have "\<dots> = (circuit_mat K Us * U) \<Otimes> (1\<^sub>m m * 1\<^sub>m m)"
    by (rule mult_distr_tensor[symmetric]) (use Cc U K m in auto)
  finally show ?case by simp
qed

lemma circuit_mat_tensor_left:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K" and K: "0 < K" and m: "0 < m"
  shows "circuit_mat (m * K) (map (\<lambda>U. 1\<^sub>m m \<Otimes> U) Us) = 1\<^sub>m m \<Otimes> circuit_mat K Us"
  using assms(1)
proof (induction Us)
  case Nil
  show ?case by (simp add: tensor_mat_id)
next
  case (Cons U Us)
  have U: "U \<in> carrier_mat K K" and IH: "circuit_mat (m * K) (map (\<lambda>U. 1\<^sub>m m \<Otimes> U) Us) = 1\<^sub>m m \<Otimes> circuit_mat K Us"
    using Cons by auto
  have Cc: "circuit_mat K Us \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use Cons.prems in auto)
  have "circuit_mat (m * K) (map (\<lambda>U. 1\<^sub>m m \<Otimes> U) (U # Us)) = (1\<^sub>m m \<Otimes> circuit_mat K Us) * (1\<^sub>m m \<Otimes> U)" using IH by simp
  also have "\<dots> = (1\<^sub>m m * 1\<^sub>m m) \<Otimes> (circuit_mat K Us * U)"
    by (rule mult_distr_tensor[symmetric]) (use Cc U K m in auto)
  finally show ?case by simp
qed

lemma circuit_mat_dagger:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K"
  shows "circuit_mat K (rev (map dagger Us)) = (circuit_mat K Us)\<^sup>\<dagger>"
  using assms
proof (induction Us)
  case Nil
  show ?case by simp
next
  case (Cons U Us)
  have U: "U \<in> carrier_mat K K" and IH: "circuit_mat K (rev (map dagger Us)) = (circuit_mat K Us)\<^sup>\<dagger>" using Cons by auto
  have Cc: "circuit_mat K Us \<in> carrier_mat K K" by (rule circuit_mat_carrier) (use Cons.prems in auto)
  have "circuit_mat K (rev (map dagger (U # Us))) = circuit_mat K [U\<^sup>\<dagger>] * circuit_mat K (rev (map dagger Us))"
    by (simp only: list.map rev.simps, rule circuit_mat_append) (use Cons.prems dagger_carrier in auto)
  also have "\<dots> = (U\<^sup>\<dagger>) * ((circuit_mat K Us)\<^sup>\<dagger>)" unfolding IH by (simp add: left_mult_one_mat[OF dagger_carrier[OF U]])
  also have "\<dots> = (circuit_mat K Us * U)\<^sup>\<dagger>" by (rule dagger_of_prod[symmetric]) (use Cc U in simp)
  finally show ?case by simp
qed

lemma pow_mat_add: "G \<in> carrier_mat m m \<Longrightarrow> G ^\<^sub>m (i + j) = G ^\<^sub>m i * G ^\<^sub>m j"
proof (induction j)
  case 0
  show ?case using 0 by simp
next
  case (Suc j)
  have "G ^\<^sub>m (i + Suc j) = G ^\<^sub>m i * G ^\<^sub>m j * G" using Suc by simp
  also have "\<dots> = G ^\<^sub>m i * (G ^\<^sub>m j * G)" by (rule assoc_mult_mat) (use Suc.prems in auto)
  finally show ?case by simp
qed

subsection \<open>Elementary gates\<close>

text \<open>A one- or two-qubit unitary on adjacent wires, the identity elsewhere.\<close>

definition elementary :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "elementary K U \<longleftrightarrow> (\<exists>a b q G. q \<in> {1, 2} \<and> G \<in> carrier_mat (2 ^ q) (2 ^ q) \<and> Quantum.unitary G \<and> 0 < a \<and> 0 < b \<and>
     K = a * (2 ^ q * b) \<and> U = 1\<^sub>m a \<Otimes> (G \<Otimes> 1\<^sub>m b))"

lemma elementary_gate:
  assumes G: "gate q G" and q: "q \<in> {1, 2}"
  shows "elementary (2 ^ q) G"
proof -
  have Gc: "G \<in> carrier_mat (2 ^ q) (2 ^ q)" using G by (auto simp: gate_def square_mat.simps)
  have "G = 1\<^sub>m 1 \<Otimes> (G \<Otimes> 1\<^sub>m 1)" by (simp only: right_tensor_id[OF Gc] left_tensor_id[OF Gc])
  thus ?thesis unfolding elementary_def using Gc G q by (intro exI[of _ 1] exI[of _ 1] exI[of _ q] exI[of _ G]) (auto simp: gate_def)
qed

lemma elementary_right:
  assumes E: "elementary K U" and m: "0 < m"
  shows "elementary (K * m) (U \<Otimes> 1\<^sub>m m)"
proof -
  obtain a b q G where G: "q \<in> {1, 2}" "G \<in> carrier_mat (2 ^ q) (2 ^ q)" "Quantum.unitary G" "0 < a" "0 < b"
      and K: "K = a * (2 ^ q * b)" and U: "U = 1\<^sub>m a \<Otimes> (G \<Otimes> 1\<^sub>m b)"
    using E unfolding elementary_def by blast
  have "U \<Otimes> 1\<^sub>m m = 1\<^sub>m a \<Otimes> (G \<Otimes> 1\<^sub>m (b * m))"
    unfolding U tensor_mat_id[symmetric] by (simp only: tensor_mat_is_assoc)
  moreover have "K * m = a * (2 ^ q * (b * m))" unfolding K by simp
  ultimately show ?thesis unfolding elementary_def using G m by (intro exI[of _ a] exI[of _ "b * m"] exI[of _ q] exI[of _ G]) simp
qed

lemma elementary_left:
  assumes E: "elementary K U" and m: "0 < m"
  shows "elementary (m * K) (1\<^sub>m m \<Otimes> U)"
proof -
  obtain a b q G where G: "q \<in> {1, 2}" "G \<in> carrier_mat (2 ^ q) (2 ^ q)" "Quantum.unitary G" "0 < a" "0 < b"
      and K: "K = a * (2 ^ q * b)" and U: "U = 1\<^sub>m a \<Otimes> (G \<Otimes> 1\<^sub>m b)"
    using E unfolding elementary_def by blast
  have "1\<^sub>m m \<Otimes> U = 1\<^sub>m (m * a) \<Otimes> (G \<Otimes> 1\<^sub>m b)"
    unfolding U tensor_mat_id[symmetric] by (simp only: tensor_mat_is_assoc)
  moreover have "m * K = (m * a) * (2 ^ q * b)" unfolding K by simp
  ultimately show ?thesis unfolding elementary_def using G m by (intro exI[of _ "m * a"] exI[of _ b] exI[of _ q] exI[of _ G]) simp
qed

lemma elementary_dagger:
  assumes E: "elementary K U"
  shows "elementary K (U\<^sup>\<dagger>)"
proof -
  obtain a b q G where G: "q \<in> {1, 2}" "G \<in> carrier_mat (2 ^ q) (2 ^ q)" "Quantum.unitary G" "0 < a" "0 < b"
      and K: "K = a * (2 ^ q * b)" and U: "U = 1\<^sub>m a \<Otimes> (G \<Otimes> 1\<^sub>m b)"
    using E unfolding elementary_def by blast
  have "U\<^sup>\<dagger> = 1\<^sub>m a \<Otimes> ((G\<^sup>\<dagger>) \<Otimes> 1\<^sub>m b)" unfolding U by (simp add: tensor_mat_adjoint)
  thus ?thesis unfolding elementary_def using G K dagger_carrier[OF G(2)] unitary_dagger[OF G(3)]
    by (intro exI[of _ a] exI[of _ b] exI[of _ q] exI[of _ "G\<^sup>\<dagger>"]) simp
qed

lemma elementary_unitary:
  assumes E: "elementary K U"
  shows "U \<in> carrier_mat K K" "Quantum.unitary U"
proof -
  obtain a b q G where G: "q \<in> {1, 2}" "G \<in> carrier_mat (2 ^ q) (2 ^ q)" "Quantum.unitary G" "0 < a" "0 < b"
      and K: "K = a * (2 ^ q * b)" and U: "U = 1\<^sub>m a \<Otimes> (G \<Otimes> 1\<^sub>m b)"
    using E unfolding elementary_def by blast
  show "U \<in> carrier_mat K K" unfolding U K using G(2) by (intro carrier_matI) auto
  show "Quantum.unitary U" unfolding U by (intro tensor_mat_unitary id_is_unitary G(3))
qed

subsection \<open>The AFP circuits as gate lists\<close>

text \<open>The circuits of the AFP entry \<open>Quantum_Fourier_Transform\<close> are matrix products of
one- and two-qubit gates tensored with identities; the gate lists below list those factors in
the order applied.\<close>

fun swap_down_gates :: "nat \<Rightarrow> complex Matrix.mat list" where
  "swap_down_gates 0 = []"
| "swap_down_gates (Suc 0) = []"
| "swap_down_gates (Suc (Suc 0)) = [SWAP]"
| "swap_down_gates (Suc (Suc (Suc n))) = map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) (swap_down_gates (Suc (Suc n))) @ [1\<^sub>m (2 ^ Suc n) \<Otimes> SWAP]"

fun swap_up_gates :: "nat \<Rightarrow> complex Matrix.mat list" where
  "swap_up_gates 0 = []"
| "swap_up_gates (Suc 0) = []"
| "swap_up_gates (Suc (Suc 0)) = [SWAP]"
| "swap_up_gates (Suc (Suc (Suc n))) = map (\<lambda>U. 1\<^sub>m 2 \<Otimes> U) (swap_up_gates (Suc (Suc n))) @ [SWAP \<Otimes> 1\<^sub>m (2 ^ Suc n)]"

lemma elementary_SWAP: "elementary 4 SWAP"
  using elementary_gate[OF SWAP_is_gate] by simp

lemma elementary_ok: "elementary K U \<Longrightarrow> U \<in> carrier_mat K K"
  by (rule elementary_unitary(1))

lemma elementary_map_right:
  "\<forall>U \<in> set Us. elementary K U \<Longrightarrow> 0 < m \<Longrightarrow> \<forall>U \<in> set (map (\<lambda>U. U \<Otimes> 1\<^sub>m m) Us). elementary (K * m) U"
  using elementary_right by auto

lemma elementary_map_left:
  "\<forall>U \<in> set Us. elementary K U \<Longrightarrow> 0 < m \<Longrightarrow> \<forall>U \<in> set (map (\<lambda>U. 1\<^sub>m m \<Otimes> U) Us). elementary (m * K) U"
  using elementary_left by auto

lemma elementary_carriers: "\<forall>U \<in> set Us. elementary K U \<Longrightarrow> U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K"
  using elementary_ok by blast

lemma pow_Suc3: "(2::nat) ^ Suc (Suc (Suc n)) = 2 ^ Suc (Suc n) * 2" "(2::nat) ^ Suc (Suc (Suc n)) = 2 * 2 ^ Suc (Suc n)"
    "(2::nat) ^ Suc (Suc (Suc n)) = 2 ^ Suc n * 4" "(2::nat) ^ Suc (Suc (Suc n)) = 4 * 2 ^ Suc n"
  by simp_all

lemma swap_down_gates:
  "circuit_mat (2 ^ n) (swap_down_gates n) = SWAP_down n \<and> (\<forall>U \<in> set (swap_down_gates n). elementary (2 ^ n) U)"
proof (induction n rule: swap_down_gates.induct)
  case 3
  have "circuit_mat 4 [SWAP] = SWAP" by (rule circuit_mat_single[OF SWAP_carrier_mat])
  thus ?case using elementary_SWAP by (simp add: numeral_Bit0 del: circuit_mat.simps)
next
  case (4 n)
  let ?g = "swap_down_gates (Suc (Suc n))" and ?K = "2 ^ Suc (Suc (Suc n)) :: nat"
  have IH: "circuit_mat (2 ^ Suc (Suc n)) ?g = SWAP_down (Suc (Suc n))" "\<forall>U \<in> set ?g. elementary (2 ^ Suc (Suc n)) U"
    using 4 by blast+
  have e1: "\<forall>U \<in> set (map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) ?g). elementary ?K U"
    unfolding pow_Suc3(1) by (rule elementary_map_right[OF IH(2)]) simp
  have e2: "elementary ?K (1\<^sub>m (2 ^ Suc n) \<Otimes> SWAP)"
    unfolding pow_Suc3(3) by (rule elementary_left[OF elementary_SWAP]) simp
  have "circuit_mat ?K (swap_down_gates (Suc (Suc (Suc n))))
        = circuit_mat ?K [1\<^sub>m (2 ^ Suc n) \<Otimes> SWAP] * circuit_mat ?K (map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) ?g)"
    unfolding swap_down_gates.simps by (rule circuit_mat_append) (use elementary_carriers[OF e1] elementary_ok[OF e2] in auto)
  also have "circuit_mat ?K (map (\<lambda>U. U \<Otimes> 1\<^sub>m 2) ?g) = SWAP_down (Suc (Suc n)) \<Otimes> 1\<^sub>m 2"
    unfolding pow_Suc3(1) IH(1)[symmetric] by (rule circuit_mat_tensor_right) (use elementary_carriers[OF IH(2)] in auto)
  also have "circuit_mat ?K [1\<^sub>m (2 ^ Suc n) \<Otimes> SWAP] = 1\<^sub>m (2 ^ Suc n) \<Otimes> SWAP"
    by (rule circuit_mat_single[OF elementary_ok[OF e2]])
  finally have c: "circuit_mat ?K (swap_down_gates (Suc (Suc (Suc n)))) = SWAP_down (Suc (Suc (Suc n)))" by simp
  have "\<forall>U \<in> set (swap_down_gates (Suc (Suc (Suc n)))). elementary ?K U"
    unfolding swap_down_gates.simps set_append using e1 e2 by auto
  thus ?case using c by blast
qed simp_all

lemma pow_Suc2': "(2::nat) ^ Suc (Suc n) = 2 ^ Suc n * 2" "(2::nat) ^ Suc (Suc n) = 2 * 2 ^ Suc n"
  by simp_all

lemma elementary_two: "gate 1 G \<Longrightarrow> elementary 2 G"
  using elementary_gate[of 1 G] by simp

lemma elementary_four: "gate 2 G \<Longrightarrow> elementary 4 G"
  using elementary_gate[of 2 G] by simp

lemma swap_up_gates:
  "circuit_mat (2 ^ n) (swap_up_gates n) = SWAP_up n \<and> (\<forall>U \<in> set (swap_up_gates n). elementary (2 ^ n) U)"
proof (induction n rule: swap_up_gates.induct)
  case 3
  have "circuit_mat 4 [SWAP] = SWAP" by (rule circuit_mat_single[OF SWAP_carrier_mat])
  thus ?case using elementary_SWAP by (simp add: numeral_Bit0 del: circuit_mat.simps)
next
  case (4 n)
  let ?g = "swap_up_gates (Suc (Suc n))" and ?K = "2 ^ Suc (Suc (Suc n)) :: nat"
  have IH: "circuit_mat (2 ^ Suc (Suc n)) ?g = SWAP_up (Suc (Suc n))" "\<forall>U \<in> set ?g. elementary (2 ^ Suc (Suc n)) U"
    using 4 by blast+
  have e1: "\<forall>U \<in> set (map (\<lambda>U. 1\<^sub>m 2 \<Otimes> U) ?g). elementary ?K U"
    unfolding pow_Suc3(2) by (rule elementary_map_left[OF IH(2)]) simp
  have e2: "elementary ?K (SWAP \<Otimes> 1\<^sub>m (2 ^ Suc n))"
    unfolding pow_Suc3(4) by (rule elementary_right[OF elementary_SWAP]) simp
  have "circuit_mat ?K (swap_up_gates (Suc (Suc (Suc n))))
        = circuit_mat ?K [SWAP \<Otimes> 1\<^sub>m (2 ^ Suc n)] * circuit_mat ?K (map (\<lambda>U. 1\<^sub>m 2 \<Otimes> U) ?g)"
    unfolding swap_up_gates.simps by (rule circuit_mat_append) (use elementary_carriers[OF e1] elementary_ok[OF e2] in auto)
  also have "circuit_mat ?K (map (\<lambda>U. 1\<^sub>m 2 \<Otimes> U) ?g) = 1\<^sub>m 2 \<Otimes> SWAP_up (Suc (Suc n))"
    unfolding pow_Suc3(2) IH(1)[symmetric] by (rule circuit_mat_tensor_left) (use elementary_carriers[OF IH(2)] in auto)
  also have "circuit_mat ?K [SWAP \<Otimes> 1\<^sub>m (2 ^ Suc n)] = SWAP \<Otimes> 1\<^sub>m (2 ^ Suc n)"
    by (rule circuit_mat_single[OF elementary_ok[OF e2]])
  finally have c: "circuit_mat ?K (swap_up_gates (Suc (Suc (Suc n)))) = SWAP_up (Suc (Suc (Suc n)))" by simp
  have "\<forall>U \<in> set (swap_up_gates (Suc (Suc (Suc n)))). elementary ?K U"
    unfolding swap_up_gates.simps set_append using e1 e2 by auto
  thus ?case using c by blast
qed simp_all

fun control_gates :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "control_gates 0 U = []"
| "control_gates (Suc 0) U = []"
| "control_gates (Suc (Suc 0)) U = [control2 U]"
| "control_gates (Suc (Suc (Suc n))) U = map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) (swap_up_gates (Suc (Suc n))) @
     [control2 U \<Otimes> 1\<^sub>m (2 ^ Suc n)] @ map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) (swap_down_gates (Suc (Suc n)))"

lemma control_gates:
  assumes U: "gate 1 U"
  shows "circuit_mat (2 ^ n) (control_gates n U) = control n U \<and> (\<forall>G \<in> set (control_gates n U). elementary (2 ^ n) G)"
proof (induction n rule: swap_up_gates.induct)
  case 3
  have c: "control2 U \<in> carrier_mat 4 4" by simp
  have "circuit_mat 4 [control2 U] = control2 U" by (rule circuit_mat_single[OF c])
  thus ?case using elementary_four[OF control2_is_gate[OF U]] by (simp add: numeral_Bit0 del: circuit_mat.simps)
next
  case (4 n)
  let ?u = "swap_up_gates (Suc (Suc n))" and ?d = "swap_down_gates (Suc (Suc n))" and ?K = "2 ^ Suc (Suc (Suc n)) :: nat"
  let ?c = "control2 U \<Otimes> 1\<^sub>m (2 ^ Suc n)"
  have u: "circuit_mat (2 ^ Suc (Suc n)) ?u = SWAP_up (Suc (Suc n))" "\<forall>V \<in> set ?u. elementary (2 ^ Suc (Suc n)) V"
    using swap_up_gates by blast+
  have d: "circuit_mat (2 ^ Suc (Suc n)) ?d = SWAP_down (Suc (Suc n))" "\<forall>V \<in> set ?d. elementary (2 ^ Suc (Suc n)) V"
    using swap_down_gates by blast+
  have eu: "\<forall>V \<in> set (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?u). elementary ?K V"
    unfolding pow_Suc3(2) by (rule elementary_map_left[OF u(2)]) simp
  have ed: "\<forall>V \<in> set (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?d). elementary ?K V"
    unfolding pow_Suc3(2) by (rule elementary_map_left[OF d(2)]) simp
  have ec: "elementary ?K ?c"
    unfolding pow_Suc3(4) by (rule elementary_right[OF elementary_four[OF control2_is_gate[OF U]]]) simp
  have "circuit_mat ?K (control_gates (Suc (Suc (Suc n))) U)
        = circuit_mat ?K ([?c] @ map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?d) * circuit_mat ?K (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?u)"
    unfolding control_gates.simps by (rule circuit_mat_append) (use elementary_carriers[OF eu] elementary_carriers[OF ed] elementary_ok[OF ec] in auto)
  also have "circuit_mat ?K ([?c] @ map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?d) = circuit_mat ?K (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?d) * circuit_mat ?K [?c]"
    by (rule circuit_mat_append) (use elementary_carriers[OF ed] elementary_ok[OF ec] in auto)
  also have "circuit_mat ?K (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?d) = 1\<^sub>m 2 \<Otimes> SWAP_down (Suc (Suc n))"
    unfolding pow_Suc3(2) d(1)[symmetric] by (rule circuit_mat_tensor_left) (use elementary_carriers[OF d(2)] in auto)
  also have "circuit_mat ?K (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?u) = 1\<^sub>m 2 \<Otimes> SWAP_up (Suc (Suc n))"
    unfolding pow_Suc3(2) u(1)[symmetric] by (rule circuit_mat_tensor_left) (use elementary_carriers[OF u(2)] in auto)
  also have "circuit_mat ?K [?c] = ?c" by (rule circuit_mat_single[OF elementary_ok[OF ec]])
  finally have c: "circuit_mat ?K (control_gates (Suc (Suc (Suc n))) U) = control (Suc (Suc (Suc n))) U" by simp
  have "\<forall>V \<in> set (control_gates (Suc (Suc (Suc n))) U). elementary ?K V"
    unfolding control_gates.simps set_append using eu ed ec by auto
  thus ?case using c by blast
qed simp_all

fun crot_gates :: "nat \<Rightarrow> complex Matrix.mat list" where
  "crot_gates 0 = []"
| "crot_gates (Suc 0) = []"
| "crot_gates (Suc (Suc n)) = map (\<lambda>V. V \<Otimes> 1\<^sub>m 2) (crot_gates (Suc n)) @ control_gates (Suc (Suc n)) (R (Suc (Suc n)))"

lemma crot_gates:
  "circuit_mat (2 ^ n) (crot_gates n) = controlled_rotations n \<and> (\<forall>U \<in> set (crot_gates n). elementary (2 ^ n) U)"
proof (induction n rule: crot_gates.induct)
  case (3 n)
  let ?g = "crot_gates (Suc n)" and ?c = "control_gates (Suc (Suc n)) (R (Suc (Suc n)))" and ?K = "2 ^ Suc (Suc n) :: nat"
  have IH: "circuit_mat (2 ^ Suc n) ?g = controlled_rotations (Suc n)" "\<forall>U \<in> set ?g. elementary (2 ^ Suc n) U"
    using 3 by blast+
  have c: "circuit_mat ?K ?c = control (Suc (Suc n)) (R (Suc (Suc n)))" "\<forall>U \<in> set ?c. elementary ?K U"
    using control_gates[OF R_is_gate] by blast+
  have e1: "\<forall>U \<in> set (map (\<lambda>V. V \<Otimes> 1\<^sub>m 2) ?g). elementary ?K U"
    unfolding pow_Suc2'(1) by (rule elementary_map_right[OF IH(2)]) simp
  have "circuit_mat ?K (crot_gates (Suc (Suc n))) = circuit_mat ?K ?c * circuit_mat ?K (map (\<lambda>V. V \<Otimes> 1\<^sub>m 2) ?g)"
    unfolding crot_gates.simps by (rule circuit_mat_append) (use elementary_carriers[OF e1] elementary_carriers[OF c(2)] in auto)
  also have "circuit_mat ?K (map (\<lambda>V. V \<Otimes> 1\<^sub>m 2) ?g) = controlled_rotations (Suc n) \<Otimes> 1\<^sub>m 2"
    unfolding pow_Suc2'(1) IH(1)[symmetric] by (rule circuit_mat_tensor_right) (use elementary_carriers[OF IH(2)] in auto)
  finally have cc: "circuit_mat ?K (crot_gates (Suc (Suc n))) = controlled_rotations (Suc (Suc n))" unfolding c(1) by simp
  have "\<forall>U \<in> set (crot_gates (Suc (Suc n))). elementary ?K U"
    unfolding crot_gates.simps set_append using e1 c(2) by auto
  thus ?case using cc by blast
qed simp_all

fun qft_gates :: "nat \<Rightarrow> complex Matrix.mat list" where
  "qft_gates 0 = []"
| "qft_gates (Suc 0) = [Quantum.H]"
| "qft_gates (Suc (Suc n)) = (Quantum.H \<Otimes> 1\<^sub>m (2 ^ Suc n)) # crot_gates (Suc (Suc n)) @ map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) (qft_gates (Suc n))"

lemma qft_gates:
  "circuit_mat (2 ^ n) (qft_gates n) = QFT n \<and> (\<forall>U \<in> set (qft_gates n). elementary (2 ^ n) U)"
proof (induction n rule: qft_gates.induct)
  case 2
  have "circuit_mat 2 [Quantum.H] = Quantum.H" by (rule circuit_mat_single) (simp add: H_def)
  thus ?case using elementary_two[OF H_is_gate] by (simp del: circuit_mat.simps)
next
  case (3 n)
  let ?g = "qft_gates (Suc n)" and ?c = "crot_gates (Suc (Suc n))" and ?K = "2 ^ Suc (Suc n) :: nat"
  let ?h = "Quantum.H \<Otimes> 1\<^sub>m (2 ^ Suc n)"
  have IH: "circuit_mat (2 ^ Suc n) ?g = QFT (Suc n)" "\<forall>U \<in> set ?g. elementary (2 ^ Suc n) U"
    using 3 by blast+
  have c: "circuit_mat ?K ?c = controlled_rotations (Suc (Suc n))" "\<forall>U \<in> set ?c. elementary ?K U"
    using crot_gates by blast+
  have e1: "\<forall>U \<in> set (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?g). elementary ?K U"
    unfolding pow_Suc2'(2) by (rule elementary_map_left[OF IH(2)]) simp
  have eh: "elementary ?K ?h" unfolding pow_Suc2'(2) by (rule elementary_right[OF elementary_two[OF H_is_gate]]) simp
  have "circuit_mat ?K (qft_gates (Suc (Suc n))) = circuit_mat ?K (?c @ map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?g) * ?h"
    by simp
  also have "circuit_mat ?K (?c @ map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?g) = circuit_mat ?K (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?g) * circuit_mat ?K ?c"
    by (rule circuit_mat_append) (use elementary_carriers[OF e1] elementary_carriers[OF c(2)] in auto)
  also have "circuit_mat ?K (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?g) = 1\<^sub>m 2 \<Otimes> QFT (Suc n)"
    unfolding pow_Suc2'(2) IH(1)[symmetric] by (rule circuit_mat_tensor_left) (use elementary_carriers[OF IH(2)] in auto)
  finally have cc: "circuit_mat ?K (qft_gates (Suc (Suc n))) = QFT (Suc (Suc n))" unfolding c(1) by simp
  have "\<forall>U \<in> set (qft_gates (Suc (Suc n))). elementary ?K U"
    unfolding qft_gates.simps set_append using e1 c(2) eh by auto
  thus ?case using cc by blast
qed simp

fun rev_gates :: "nat \<Rightarrow> complex Matrix.mat list" where
  "rev_gates 0 = []"
| "rev_gates (Suc 0) = []"
| "rev_gates (Suc (Suc 0)) = [SWAP]"
| "rev_gates (Suc (Suc (Suc n))) = swap_down_gates (Suc (Suc (Suc n))) @ map (\<lambda>V. V \<Otimes> 1\<^sub>m 2) (rev_gates (Suc (Suc n)))"

lemma rev_gates:
  "circuit_mat (2 ^ n) (rev_gates n) = reverse_qubits n \<and> (\<forall>U \<in> set (rev_gates n). elementary (2 ^ n) U)"
proof (induction n rule: rev_gates.induct)
  case 3
  have "circuit_mat 4 [SWAP] = SWAP" by (rule circuit_mat_single[OF SWAP_carrier_mat])
  thus ?case using elementary_SWAP by (simp add: numeral_Bit0 del: circuit_mat.simps)
next
  case (4 n)
  let ?g = "rev_gates (Suc (Suc n))" and ?s = "swap_down_gates (Suc (Suc (Suc n)))" and ?K = "2 ^ Suc (Suc (Suc n)) :: nat"
  have IH: "circuit_mat (2 ^ Suc (Suc n)) ?g = reverse_qubits (Suc (Suc n))" "\<forall>U \<in> set ?g. elementary (2 ^ Suc (Suc n)) U"
    using 4 by blast+
  have s: "circuit_mat ?K ?s = SWAP_down (Suc (Suc (Suc n)))" "\<forall>U \<in> set ?s. elementary ?K U"
    using swap_down_gates by blast+
  have e1: "\<forall>U \<in> set (map (\<lambda>V. V \<Otimes> 1\<^sub>m 2) ?g). elementary ?K U"
    unfolding pow_Suc3(1) by (rule elementary_map_right[OF IH(2)]) simp
  have "circuit_mat ?K (rev_gates (Suc (Suc (Suc n)))) = circuit_mat ?K (map (\<lambda>V. V \<Otimes> 1\<^sub>m 2) ?g) * circuit_mat ?K ?s"
    unfolding rev_gates.simps by (rule circuit_mat_append) (use elementary_carriers[OF e1] elementary_carriers[OF s(2)] in auto)
  also have "circuit_mat ?K (map (\<lambda>V. V \<Otimes> 1\<^sub>m 2) ?g) = reverse_qubits (Suc (Suc n)) \<Otimes> 1\<^sub>m 2"
    unfolding pow_Suc3(1) IH(1)[symmetric] by (rule circuit_mat_tensor_right) (use elementary_carriers[OF IH(2)] in auto)
  finally have cc: "circuit_mat ?K (rev_gates (Suc (Suc (Suc n)))) = reverse_qubits (Suc (Suc (Suc n)))" unfolding s(1) by simp
  have "\<forall>U \<in> set (rev_gates (Suc (Suc (Suc n)))). elementary ?K U"
    unfolding rev_gates.simps set_append using e1 s(2) by auto
  thus ?case using cc by blast
qed simp_all

text \<open>The Fourier transform $F_{2^n}$ as a list of elementary gates: Hadamards, controlled
phase rotations and swaps.\<close>

definition qft_circuit :: "nat \<Rightarrow> complex Matrix.mat list" where
  "qft_circuit n = qft_gates n @ rev_gates n"

theorem qft_circuit:
  shows "circuit_mat (2 ^ n) (qft_circuit n) = fourier (2 ^ n)"
    and "U \<in> set (qft_circuit n) \<Longrightarrow> elementary (2 ^ n) U"
proof -
  have q: "circuit_mat (2 ^ n) (qft_gates n) = QFT n" "\<forall>U \<in> set (qft_gates n). elementary (2 ^ n) U" using qft_gates by blast+
  have r: "circuit_mat (2 ^ n) (rev_gates n) = reverse_qubits n" "\<forall>U \<in> set (rev_gates n). elementary (2 ^ n) U" using rev_gates by blast+
  have "circuit_mat (2 ^ n) (qft_circuit n) = reverse_qubits n * QFT n"
    unfolding qft_circuit_def q(1)[symmetric] r(1)[symmetric]
    by (rule circuit_mat_append) (use elementary_carriers[OF q(2)] elementary_carriers[OF r(2)] in auto)
  thus "circuit_mat (2 ^ n) (qft_circuit n) = fourier (2 ^ n)" unfolding ordered_QFT_def[symmetric] ordered_QFT_fourier .
  show "U \<in> set (qft_circuit n) \<Longrightarrow> elementary (2 ^ n) U" unfolding qft_circuit_def using q(2) r(2) by auto
qed

text \<open>The Hadamard layer $H^{\otimes n}$ as $n$ single-qubit Hadamards.\<close>

fun had_gates :: "nat \<Rightarrow> complex Matrix.mat list" where
  "had_gates 0 = []"
| "had_gates (Suc 0) = [Hadamard]"
| "had_gates (Suc (Suc n)) = (Hadamard \<Otimes> 1\<^sub>m (2 ^ Suc n)) # map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) (had_gates (Suc n))"

lemma had_gates:
  "1 \<le> n \<Longrightarrow> circuit_mat (2 ^ n) (had_gates n) = Hadamard \<otimes>\<^bsup>n\<^esup> \<and> (\<forall>U \<in> set (had_gates n). elementary (2 ^ n) U)"
proof (induction n rule: had_gates.induct)
  case 2
  have "circuit_mat 2 [Hadamard] = Hadamard" by (rule circuit_mat_single) (simp add: Hadamard_def H_def)
  thus ?case using elementary_two[OF H_is_gate] by (simp add: Hadamard_def del: circuit_mat.simps)
next
  case (3 n)
  let ?g = "had_gates (Suc n)" and ?K = "2 ^ Suc (Suc n) :: nat" and ?h = "Hadamard \<Otimes> 1\<^sub>m (2 ^ Suc n)"
  have IH: "circuit_mat (2 ^ Suc n) ?g = Hadamard \<otimes>\<^bsup>Suc n\<^esup>" "\<forall>U \<in> set ?g. elementary (2 ^ Suc n) U"
    using 3 by auto
  have Hc: "Hadamard \<in> carrier_mat 2 2" by (simp add: Hadamard_def H_def)
  have Lc: "Hadamard \<otimes>\<^bsup>Suc n\<^esup> \<in> carrier_mat (2 ^ Suc n) (2 ^ Suc n)" by (rule hadamard_layer_carrier) simp
  have e1: "\<forall>U \<in> set (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?g). elementary ?K U"
    unfolding pow_Suc2'(2) by (rule elementary_map_left[OF IH(2)]) simp
  have eh: "elementary ?K ?h" unfolding pow_Suc2'(2) Hadamard_def by (rule elementary_right[OF elementary_two[OF H_is_gate]]) simp
  have "circuit_mat ?K (had_gates (Suc (Suc n))) = circuit_mat ?K (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?g) * ?h" by simp
  also have "circuit_mat ?K (map (\<lambda>V. 1\<^sub>m 2 \<Otimes> V) ?g) = 1\<^sub>m 2 \<Otimes> (Hadamard \<otimes>\<^bsup>Suc n\<^esup>)"
    unfolding pow_Suc2'(2) IH(1)[symmetric] by (rule circuit_mat_tensor_left) (use elementary_carriers[OF IH(2)] in auto)
  also have "(1\<^sub>m 2 \<Otimes> (Hadamard \<otimes>\<^bsup>Suc n\<^esup>)) * ?h = (1\<^sub>m 2 * Hadamard) \<Otimes> ((Hadamard \<otimes>\<^bsup>Suc n\<^esup>) * 1\<^sub>m (2 ^ Suc n))"
    by (rule mult_distr_tensor[symmetric]) (use Hc Lc in auto)
  also have "\<dots> = Hadamard \<otimes>\<^bsup>Suc (Suc n)\<^esup>" using Hc Lc by simp
  finally have cc: "circuit_mat ?K (had_gates (Suc (Suc n))) = Hadamard \<otimes>\<^bsup>Suc (Suc n)\<^esup>" .
  have "\<forall>U \<in> set (had_gates (Suc (Suc n))). elementary ?K U"
    unfolding had_gates.simps set_simps using e1 eh by auto
  thus ?case using cc by blast
qed simp

subsection \<open>Controlled powers, one clock qubit at a time\<close>

text \<open>$\mathrm{C}_jG$: apply $G$ to the system when bit $j$ of the clock value is $1$.  The
controlled power $\sum_c\ket c\bra c\otimes U^c$ of phase estimation is the product of
$\mathrm{C}_jU^{2^j}$ over the $k$ clock qubits, since $c=\sum_j c_j2^j$.\<close>

definition ctrl_bit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "ctrl_bit N m j G = ctrl_blocks N m (\<lambda>c. if odd (c div 2 ^ j) then G else 1\<^sub>m m)"

lemma ctrl_bit_carrier [simp]: "ctrl_bit N m j G \<in> carrier_mat (N * m) (N * m)"
  by (simp add: ctrl_bit_def)

lemma dim_ctrl_bit [simp]: "dim_row (ctrl_bit N m j G) = N * m" "dim_col (ctrl_bit N m j G) = N * m"
  by (simp_all add: ctrl_bit_def)

lemma ctrl_bit_basis:
  assumes c: "c < N" and w: "dim_vec w = m" and G: "G \<in> carrier_mat m m"
  shows "ctrl_bit N m j G *\<^sub>v tensor_vec (unit_vec N c) w = tensor_vec (unit_vec N c) (if odd (c div 2 ^ j) then G *\<^sub>v w else w)"
proof -
  have "ctrl_bit N m j G *\<^sub>v tensor_vec (unit_vec N c) w = tensor_vec (unit_vec N c) ((if odd (c div 2 ^ j) then G else 1\<^sub>m m) *\<^sub>v w)"
    unfolding ctrl_bit_def by (rule ctrl_blocks_basis[OF c w]) (use G in simp)
  thus ?thesis using one_mult_mat_vec[OF carrier_vecI[OF w]] by (cases "odd (c div 2 ^ j)") simp_all
qed

lemma ctrl_bit_unitary: "G \<in> carrier_mat m m \<Longrightarrow> Quantum.unitary G \<Longrightarrow> Quantum.unitary (ctrl_bit N m j G)"
  unfolding ctrl_bit_def by (rule ctrl_blocks_unitary) auto

lemma ctrl_bit_dagger:
  assumes G: "G \<in> carrier_mat m m"
  shows "(ctrl_bit N m j G)\<^sup>\<dagger> = ctrl_bit N m j (G\<^sup>\<dagger>)"
proof -
  have "(ctrl_bit N m j G)\<^sup>\<dagger> = ctrl_blocks N m (\<lambda>c. (if odd (c div 2 ^ j) then G else 1\<^sub>m m)\<^sup>\<dagger>)"
    unfolding ctrl_bit_def by (rule ctrl_blocks_dagger) (use G in simp)
  also have "\<dots> = ctrl_bit N m j (G\<^sup>\<dagger>)" unfolding ctrl_bit_def by (rule ctrl_blocks_cong) simp
  finally show ?thesis .
qed

lemma ctrl_bit_mult:
  assumes "G \<in> carrier_mat m m" "G' \<in> carrier_mat m m"
  shows "ctrl_bit N m j G * ctrl_bit N m j G' = ctrl_bit N m j (G * G')"
proof -
  have "ctrl_bit N m j G * ctrl_bit N m j G' = ctrl_blocks N m (\<lambda>c. (if odd (c div 2 ^ j) then G else 1\<^sub>m m) * (if odd (c div 2 ^ j) then G' else 1\<^sub>m m))"
    unfolding ctrl_bit_def by (rule ctrl_blocks_mult) (use assms in auto)
  also have "\<dots> = ctrl_bit N m j (G * G')" unfolding ctrl_bit_def by (rule ctrl_blocks_cong) simp
  finally show ?thesis .
qed

text \<open>$\mathrm{C}_jU^{e}$ is $e$ applications of $\mathrm{C}_jU$.\<close>

lemma ctrl_bit_pow:
  assumes G: "G \<in> carrier_mat m m"
  shows "ctrl_bit N m j (G ^\<^sub>m e) = ctrl_bit N m j G ^\<^sub>m e"
proof (induction e)
  case 0
  have "ctrl_bit N m j (1\<^sub>m m) = 1\<^sub>m (N * m)" unfolding ctrl_bit_def if_cancel by (rule ctrl_blocks_one)
  thus ?case using G by simp
next
  case (Suc e)
  have "ctrl_bit N m j (G ^\<^sub>m Suc e) = ctrl_bit N m j (G ^\<^sub>m e) * ctrl_bit N m j G"
    using ctrl_bit_mult[OF pow_carrier_mat[OF G] G] by simp
  thus ?case unfolding Suc by simp
qed

lemma circuit_mat_replicate: "G \<in> carrier_mat K K \<Longrightarrow> circuit_mat K (replicate e G) = G ^\<^sub>m e"
  by (induction e) simp_all

lemma ctrl_pow_bits:
  assumes G: "G \<in> carrier_mat m m"
  shows "circuit_mat (N * m) (map (\<lambda>j. ctrl_bit N m j (G ^\<^sub>m 2 ^ j)) [0..<k]) = ctrl_blocks N m (\<lambda>c. G ^\<^sub>m (c mod 2 ^ k))"
proof (induction k)
  case 0
  have "ctrl_blocks N m (\<lambda>c. G ^\<^sub>m (c mod 2 ^ 0)) = ctrl_blocks N m (\<lambda>_. 1\<^sub>m m)" using G by simp
  thus ?case using ctrl_blocks_one by simp
next
  case (Suc k)
  let ?f = "\<lambda>j. ctrl_bit N m j (G ^\<^sub>m 2 ^ j)"
  have "circuit_mat (N * m) (map ?f [0..<Suc k]) = circuit_mat (N * m) [?f k] * circuit_mat (N * m) (map ?f [0..<k])"
    unfolding upt_Suc_append[OF le0] map_append list.map by (rule circuit_mat_append) auto
  also have "\<dots> = ?f k * ctrl_blocks N m (\<lambda>c. G ^\<^sub>m (c mod 2 ^ k))" unfolding Suc by simp
  also have "\<dots> = ctrl_blocks N m (\<lambda>c. (if odd (c div 2 ^ k) then G ^\<^sub>m 2 ^ k else 1\<^sub>m m) * G ^\<^sub>m (c mod 2 ^ k))"
    unfolding ctrl_bit_def by (rule ctrl_blocks_mult) (use G in auto)
  also have "\<dots> = ctrl_blocks N m (\<lambda>c. G ^\<^sub>m (c mod 2 ^ Suc k))"
  proof (rule ctrl_blocks_cong)
    fix c :: nat
    have cm: "c mod 2 ^ Suc k = 2 ^ k * (c div 2 ^ k mod 2) + c mod 2 ^ k"
      unfolding power_Suc2 by (rule mod_mult2_eq)
    show "(if odd (c div 2 ^ k) then G ^\<^sub>m 2 ^ k else 1\<^sub>m m) * G ^\<^sub>m (c mod 2 ^ k) = G ^\<^sub>m (c mod 2 ^ Suc k)"
    proof (cases "odd (c div 2 ^ k)")
      case True
      hence "c mod 2 ^ Suc k = 2 ^ k + c mod 2 ^ k" unfolding cm by (simp add: odd_iff_mod_2_eq_one)
      thus ?thesis using True pow_mat_add[OF G] by simp
    next
      case False
      hence "c mod 2 ^ Suc k = c mod 2 ^ k" unfolding cm by (simp add: even_iff_mod_2_eq_zero)
      thus ?thesis using False G by simp
    qed
  qed
  finally show ?case .
qed

theorem ctrl_pow_qubits:
  assumes G: "G \<in> carrier_mat m m"
  shows "circuit_mat (2 ^ k * m) (map (\<lambda>j. ctrl_bit (2 ^ k) m j (G ^\<^sub>m 2 ^ j)) [0..<k]) = ctrl_pow (2 ^ k) m G"
  unfolding ctrl_pow_bits[OF G] ctrl_pow_blocks by (rule ctrl_blocks_cong) simp

text \<open>Counting oracle calls: the controlled power is $2^k-1$ applications of the singly
controlled gates $\mathrm{C}_jU$.\<close>

lemma sum_list_pow2: "sum_list (map (\<lambda>j. 2 ^ j) [0..<k]) = (2::nat) ^ k - 1"
  by (induction k) simp_all

theorem ctrl_pow_queries:
  assumes G: "G \<in> carrier_mat m m"
  shows "circuit_mat (2 ^ k * m) (concat (map (\<lambda>j. replicate (2 ^ j) (ctrl_bit (2 ^ k) m j G)) [0..<k])) = ctrl_pow (2 ^ k) m G"
    and "length (concat (map (\<lambda>j. replicate (2 ^ j) (ctrl_bit (2 ^ k) m j G)) [0..<k])) = 2 ^ k - 1"
proof -
  have "circuit_mat (2 ^ k * m) (concat (map (\<lambda>j. replicate (2 ^ j) (ctrl_bit (2 ^ k) m j G)) [0..<k]))
        = circuit_mat (2 ^ k * m) (map (circuit_mat (2 ^ k * m)) (map (\<lambda>j. replicate (2 ^ j) (ctrl_bit (2 ^ k) m j G)) [0..<k]))"
    by (rule circuit_mat_concat) auto
  also have "map (circuit_mat (2 ^ k * m)) (map (\<lambda>j. replicate (2 ^ j) (ctrl_bit (2 ^ k) m j G)) [0..<k])
             = map (\<lambda>j. ctrl_bit (2 ^ k) m j (G ^\<^sub>m 2 ^ j)) [0..<k]"
    by (simp add: circuit_mat_replicate[OF ctrl_bit_carrier] ctrl_bit_pow[OF G])
  finally show "circuit_mat (2 ^ k * m) (concat (map (\<lambda>j. replicate (2 ^ j) (ctrl_bit (2 ^ k) m j G)) [0..<k])) = ctrl_pow (2 ^ k) m G"
    unfolding ctrl_pow_qubits[OF G] .
  show "length (concat (map (\<lambda>j. replicate (2 ^ j) (ctrl_bit (2 ^ k) m j G)) [0..<k])) = 2 ^ k - 1"
    by (simp add: length_concat comp_def sum_list_pow2)
qed

subsection \<open>The HHL circuit in elementary gates\<close>

definition clk_gates :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "clk_gates n Us = map (\<lambda>U. clock_gate U n) Us"

definition evo_gates :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "evo_gates A t0 k = map (\<lambda>j. ctrl_bit (2 ^ k) (dim_row A * 2) j ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)) [0..<k]"

text \<open>The eight stages of \<open>hhl_gates\<close>, each as a gate list: prepare $\ket b$; $k$ Hadamards;
$\mathrm{C}_jU^{2^j}$ for each clock qubit $j$; the inverse Fourier circuit; the controlled
rotation; the Fourier circuit; the inverse controlled powers; $k$ Hadamards.\<close>

definition hhl_blocks :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list list" where
  "hhl_blocks A Ub t0 k C =
     [[prep_gate (2 ^ k) Ub], clk_gates (dim_row A) (had_gates k), evo_gates A t0 k,
      clk_gates (dim_row A) (rev (map dagger (qft_circuit k))), [rot_gate A t0 (2 ^ k) C],
      clk_gates (dim_row A) (qft_circuit k), rev (map dagger (evo_gates A t0 k)), clk_gates (dim_row A) (had_gates k)]"

definition hhl_elem_gates :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "hhl_elem_gates A Ub t0 k C = concat (hhl_blocks A Ub t0 k C)"

definition hhl_elem_program :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> com" where
  "hhl_elem_program A Ub t0 k C = hhl_prog (2 ^ k * (dim_row A * 2)) (hhl_elem_gates A Ub t0 k C)"

definition hhl_elem_rus :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> com" where
  "hhl_elem_rus A Ub t0 k C = hhl_rus_prog (2 ^ k * (dim_row A * 2)) (hhl_elem_gates A Ub t0 k C)"

lemma length_hhl_blocks [simp]: "length (hhl_blocks A Ub t0 k C) = 8" by (simp add: hhl_blocks_def)

lemma length_evo_gates [simp]: "length (evo_gates A t0 k) = k" by (simp add: evo_gates_def)

text \<open>Gate counts.\<close>

lemma length_swap_down_gates [simp]: "length (swap_down_gates n) = n - 1"
  by (induction n rule: swap_down_gates.induct) simp_all

lemma length_swap_up_gates [simp]: "length (swap_up_gates n) = n - 1"
  by (induction n rule: swap_up_gates.induct) simp_all

lemma length_control_gates [simp]: "length (control_gates n U) = 2 * n - 3"
  by (induction n U rule: control_gates.induct) simp_all

lemma length_crot_gates [simp]: "length (crot_gates n) = (n - 1)\<^sup>2"
  by (induction n rule: crot_gates.induct) (simp_all add: power2_eq_square)

lemma length_had_gates [simp]: "length (had_gates n) = n"
  by (induction n rule: had_gates.induct) simp_all

lemma length_rev_gates: "2 * length (rev_gates n) = n * (n - 1)"
  by (induction n rule: rev_gates.induct) (simp_all add: algebra_simps)

lemma length_qft_gates: "6 * length (qft_gates n) = 6 * n + (n - 1) * n * (2 * n - 1)"
  by (induction n rule: qft_gates.induct) (simp_all add: power2_eq_square algebra_simps)

text \<open>The AFP Fourier circuit on $n$ qubits has $(n^3+2n)/3$ gates: the controlled rotations
are routed through nearest-neighbour swaps.\<close>

theorem length_qft_circuit: "3 * length (qft_circuit n) = n ^ 3 + 2 * n"
proof -
  have "6 * length (qft_circuit n) = 2 * n ^ 3 + 4 * n"
    unfolding qft_circuit_def length_append using length_qft_gates[of n] length_rev_gates[of n]
    by (cases n) (simp_all add: algebra_simps power2_eq_square power3_eq_cube)
  thus ?thesis by simp
qed

lemma length_clk_gates [simp]: "length (clk_gates n Us) = length Us" by (simp add: clk_gates_def)

theorem length_hhl_elem_gates: "3 * length (hhl_elem_gates A Ub t0 k C) = 2 * k ^ 3 + 16 * k + 6"
  unfolding hhl_elem_gates_def hhl_blocks_def using length_qft_circuit[of k] by simp


lemma clk_gates_circuit:
  assumes "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k) (2 ^ k)" and n: "0 < n"
  shows "circuit_mat (2 ^ k * (n * 2)) (clk_gates n Us) = clock_gate (circuit_mat (2 ^ k) Us) n"
  unfolding clk_gates_def clock_gate_def by (rule circuit_mat_tensor_right) (use assms in auto)

lemma clk_gates_elementary:
  "\<forall>U \<in> set Us. elementary (2 ^ k) U \<Longrightarrow> 0 < n \<Longrightarrow> \<forall>U \<in> set (clk_gates n Us). elementary (2 ^ k * (n * 2)) U"
  unfolding clk_gates_def clock_gate_def by (rule elementary_map_right) auto

lemma qft_inv_circuit:
  shows "circuit_mat (2 ^ k) (rev (map dagger (qft_circuit k))) = (fourier (2 ^ k))\<^sup>\<dagger>"
    and "\<forall>U \<in> set (rev (map dagger (qft_circuit k))). elementary (2 ^ k) U"
proof -
  show "circuit_mat (2 ^ k) (rev (map dagger (qft_circuit k))) = (fourier (2 ^ k))\<^sup>\<dagger>"
    unfolding qft_circuit(1)[symmetric] by (rule circuit_mat_dagger) (use qft_circuit(2) elementary_ok in blast)
  show "\<forall>U \<in> set (rev (map dagger (qft_circuit k))). elementary (2 ^ k) U"
    using qft_circuit(2) elementary_dagger by auto
qed

context
  fixes A Ub :: "complex Matrix.mat" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "Quantum_Computing_3_10.hermitian A" and n0: "0 < n" and k: "1 \<le> k"
    and Ub: "Ub \<in> carrier_mat n n"
begin

lemma blocks_nA: "dim_row A = n" using A(1) by simp

lemma blocks_E_carrier: "evolution A t0 \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)"
  by (rule tensor_carrier[OF evolution_carrier[OF A] one_carrier_mat])

lemma evo_gates_carrier: "U \<in> set (evo_gates A t0 k) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
  unfolding evo_gates_def blocks_nA by auto

lemma evo_gates_circuit: "circuit_mat (2 ^ k * (n * 2)) (evo_gates A t0 k) = evo_gate A t0 (2 ^ k)"
  unfolding evo_gates_def evo_gate_def blocks_nA by (rule ctrl_pow_qubits[OF blocks_E_carrier])

lemma evo_inv_circuit: "circuit_mat (2 ^ k * (n * 2)) (rev (map dagger (evo_gates A t0 k))) = (evo_gate A t0 (2 ^ k))\<^sup>\<dagger>"
  unfolding evo_gates_circuit[symmetric] by (rule circuit_mat_dagger[OF evo_gates_carrier])

lemma had_ok: "\<forall>U \<in> set (had_gates k). elementary (2 ^ k) U" and had_circuit: "circuit_mat (2 ^ k) (had_gates k) = Hadamard \<otimes>\<^bsup>k\<^esup>"
  using had_gates[OF k] by blast+

theorem hhl_blocks_circuit: "map (circuit_mat (2 ^ k * (n * 2))) (hhl_blocks A Ub t0 k C) = hhl_gates A Ub t0 k C"
proof -
  have pc: "prep_gate (2 ^ k) Ub \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
    unfolding prep_gate_def by (rule tensor_carrier[OF one_carrier_mat tensor_carrier[OF Ub one_carrier_mat]])
  have rc: "rot_gate A t0 (2 ^ k) C \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
    unfolding rot_gate_def blocks_nA by simp
  have h: "circuit_mat (2 ^ k * (n * 2)) (clk_gates n (had_gates k)) = clock_gate (Hadamard \<otimes>\<^bsup>k\<^esup>) n"
    unfolding had_circuit[symmetric] by (rule clk_gates_circuit[OF _ n0]) (use had_ok elementary_ok in blast)
  have fi: "circuit_mat (2 ^ k * (n * 2)) (clk_gates n (rev (map dagger (qft_circuit k)))) = clock_gate ((fourier (2 ^ k))\<^sup>\<dagger>) n"
    unfolding qft_inv_circuit(1)[symmetric] by (rule clk_gates_circuit[OF _ n0]) (use qft_inv_circuit(2) elementary_ok in blast)
  have f: "circuit_mat (2 ^ k * (n * 2)) (clk_gates n (qft_circuit k)) = clock_gate (fourier (2 ^ k)) n"
    unfolding qft_circuit(1)[symmetric] by (rule clk_gates_circuit[OF _ n0]) (use qft_circuit(2) elementary_ok in blast)
  show ?thesis unfolding hhl_blocks_def hhl_gates_def blocks_nA
    using circuit_mat_single[OF pc] circuit_mat_single[OF rc] h fi f evo_gates_circuit evo_inv_circuit by simp
qed

text \<open>Every gate is a one- or two-qubit gate, a singly controlled $U^{\pm2^j}$ ($U=e^{iAt_0}$,
$j<k$), the preparation of $\ket b$, or the eigenvalue-controlled rotation.  The $2k$ controlled
powers are $2(2^k-1)$ singly controlled $U^{\pm1}$ (\<open>ctrl_pow_queries\<close>).\<close>

theorem hhl_elem_gate_kinds:
  assumes U: "U \<in> set (hhl_elem_gates A Ub t0 k C)"
  shows "elementary (2 ^ k * (n * 2)) U
         \<or> (\<exists>j<k. U = ctrl_bit (2 ^ k) (n * 2) j ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)
                 \<or> U = ctrl_bit (2 ^ k) (n * 2) j (((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)\<^sup>\<dagger>))
         \<or> U = prep_gate (2 ^ k) Ub \<or> U = rot_gate A t0 (2 ^ k) C"
proof -
  let ?E = "evolution A t0 \<Otimes> 1\<^sub>m 2" and ?D = "2 ^ k * (n * 2)"
  have h: "\<forall>U \<in> set (clk_gates n (had_gates k)). elementary ?D U" by (rule clk_gates_elementary[OF had_ok n0])
  have fi: "\<forall>U \<in> set (clk_gates n (rev (map dagger (qft_circuit k)))). elementary ?D U"
    by (rule clk_gates_elementary[OF qft_inv_circuit(2) n0])
  have f: "\<forall>U \<in> set (clk_gates n (qft_circuit k)). elementary ?D U"
    by (rule clk_gates_elementary) (use qft_circuit(2) n0 in auto)
  have ei: "U \<in> set (rev (map dagger (evo_gates A t0 k))) \<Longrightarrow> \<exists>j<k. U = ctrl_bit (2 ^ k) (n * 2) j ((?E ^\<^sub>m 2 ^ j)\<^sup>\<dagger>)" for U
    unfolding evo_gates_def blocks_nA using ctrl_bit_dagger[OF pow_carrier_mat[OF blocks_E_carrier]] by auto
  have e: "U \<in> set (evo_gates A t0 k) \<Longrightarrow> \<exists>j<k. U = ctrl_bit (2 ^ k) (n * 2) j (?E ^\<^sub>m 2 ^ j)" for U
    unfolding evo_gates_def blocks_nA by auto
  have "U = prep_gate (2 ^ k) Ub \<or> U \<in> set (clk_gates n (had_gates k)) \<or> U \<in> set (evo_gates A t0 k)
        \<or> U \<in> set (clk_gates n (rev (map dagger (qft_circuit k)))) \<or> U = rot_gate A t0 (2 ^ k) C
        \<or> U \<in> set (clk_gates n (qft_circuit k)) \<or> U \<in> set (rev (map dagger (evo_gates A t0 k)))"
    using U unfolding hhl_elem_gates_def hhl_blocks_def blocks_nA by auto
  thus ?thesis using h fi f e ei by blast
qed

end

subsection \<open>The program in elementary gates\<close>

context
  fixes A Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "Quantum_Computing_3_10.hermitian A" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
begin

lemma elem_gates_ok:
  assumes U: "U \<in> set (hhl_elem_gates A Ub t0 k C)"
  shows "U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
proof -
  let ?E = "evolution A t0 \<Otimes> 1\<^sub>m 2" and ?D = "2 ^ k * (n * 2)"
  have Ec: "?E \<in> carrier_mat (n * 2) (n * 2)" by (rule blocks_E_carrier[OF A(1,2) n0 k Ub(1)])
  have Eu: "Quantum.unitary ?E" by (rule tensor_mat_unitary_one_right[OF evolution_unitary[OF A]])
  have Pc: "?E ^\<^sub>m 2 ^ j \<in> carrier_mat (n * 2) (n * 2)" "Quantum.unitary (?E ^\<^sub>m 2 ^ j)" for j
    using pow_carrier_mat[OF Ec] unitary_pow[OF Ec Eu] by auto
  have q: "U \<in> carrier_mat ?D ?D \<and> Quantum.unitary U"
    using hhl_elem_gate_kinds[OF A(1,2) n0 k Ub(1) U]
  proof (elim disjE exE conjE)
    assume "elementary ?D U" thus ?thesis using elementary_unitary by blast
  next
    fix j assume "j < k" "U = ctrl_bit (2 ^ k) (n * 2) j (?E ^\<^sub>m 2 ^ j)"
    thus ?thesis using ctrl_bit_unitary[OF Pc] by simp
  next
    fix j assume "j < k" "U = ctrl_bit (2 ^ k) (n * 2) j ((?E ^\<^sub>m 2 ^ j)\<^sup>\<dagger>)"
    thus ?thesis using ctrl_bit_unitary[OF dagger_carrier[OF Pc(1)] unitary_dagger[OF Pc(2)]] by simp
  next
    assume "U = prep_gate (2 ^ k) Ub"
    thus ?thesis using hhl_gates_unitary[OF A n0 k t0 spec Ub Cb] by (simp add: hhl_gates_def)
  next
    assume "U = rot_gate A t0 (2 ^ k) C"
    thus ?thesis using hhl_gates_unitary[OF A n0 k t0 spec Ub Cb] by (simp add: hhl_gates_def)
  qed
  thus ?thesis using unitary_bridge by blast
qed

lemma block_gates_ok:
  "i < 8 \<Longrightarrow> U \<in> set (hhl_blocks A Ub t0 k C ! i) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
  by (rule elem_gates_ok) (auto simp: hhl_elem_gates_def)

theorem hhl_elem_circuit:
  "circuit_mat (2 ^ k * (n * 2)) (hhl_elem_gates A Ub t0 k C) = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
  unfolding hhl_elem_gates_def hhl_blocks_circuit[OF A(1,2) n0 k Ub(1), symmetric]
  by (rule circuit_mat_concat) (use elem_gates_ok in \<open>auto simp: hhl_elem_gates_def\<close>)

text \<open>The theorems of \<open>HHL_Program\<close> for the program in elementary gates.\<close>

theorem hhl_elem_success:
  "state_sig.hoare_partial [2 ^ k, n, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * (n * 2)))
     (hhl_elem_program A Ub t0 k C) (anc_proj (2 ^ k * (n * 2)) 1)"
  unfolding hhl_elem_program_def blocks_nA[OF A(1,2) n0 k Ub(1)]
  by (rule hhl_prog_success[OF A n0 k t0 spec Ub Cb elem_gates_ok hhl_elem_circuit])

theorem hhl_elem_correct:
  "state_sig.hoare_partial [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_elem_program A Ub t0 k C)
     (anc_proj (2 ^ k * (n * 2)) 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_elem_program_def blocks_nA[OF A(1,2) n0 k Ub(1)]
  by (rule hhl_prog_correct[OF A n0 k t0 spec Ub Cb elem_gates_ok hhl_elem_circuit])

theorem hhl_elem_rus_correct:
  "state_sig.hoare_partial [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_elem_rus A Ub t0 k C)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_elem_rus_def blocks_nA[OF A(1,2) n0 k Ub(1)]
  by (rule hhl_rus_prog_correct[OF A n0 k t0 spec Ub Cb elem_gates_ok hhl_elem_circuit])

theorem hhl_elem_success_total:
  "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * (n * 2)))
     (hhl_elem_program A Ub t0 k C) (anc_proj (2 ^ k * (n * 2)) 1)"
  unfolding hhl_elem_program_def blocks_nA[OF A(1,2) n0 k Ub(1)]
  by (rule hhl_prog_success_total[OF A n0 k t0 spec Ub Cb elem_gates_ok hhl_elem_circuit])

theorem hhl_elem_correct_total:
  "state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_elem_program A Ub t0 k C)
     (anc_proj (2 ^ k * (n * 2)) 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_elem_program_def blocks_nA[OF A(1,2) n0 k Ub(1)]
  by (rule hhl_prog_correct_total[OF A n0 k t0 spec Ub Cb elem_gates_ok hhl_elem_circuit])

theorem hhl_elem_rus_partial:
  "state_sig.hoare_partial_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_elem_rus A Ub t0 k C)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_elem_rus_def blocks_nA[OF A(1,2) n0 k Ub(1)]
  by (rule hhl_rus_prog_partial[OF A n0 k t0 spec Ub Cb elem_gates_ok hhl_elem_circuit])

text \<open>The trajectory stage by stage: block $i$ takes $\ket{\psi_i}$ to $\ket{\psi_{i+1}}$
(\<open>hhl_states\<close>), and the whole gate list takes $\ket{000}$ to $\ket0\otimes\mathrm{out}$.\<close>

theorem hhl_elem_stage_triples:
  assumes i: "i < 8"
  shows "state_sig.hoare_partial [2 ^ k, n, 2]
           (outer_prod (hhl_states A b t0 k C ! i) (hhl_states A b t0 k C ! i))
           (utrans_seq (hhl_blocks A Ub t0 k C ! i))
           (outer_prod (hhl_states A b t0 k C ! Suc i) (hhl_states A b t0 k C ! Suc i))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  let ?B = "hhl_blocks A Ub t0 k C ! i" and ?\<psi> = "hhl_states A b t0 k C ! i"
  have dd: "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  have g: "\<And>U. U \<in> set ?B \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" using block_gates_ok[OF i] dd by auto
  have S: "dim_vec ?\<psi> = d" "inner_prod ?\<psi> ?\<psi> = 1" using states_ok[OF A n0 k t0 spec Ub Cb, of i] i dd by auto
  have "run_gates ?\<psi> ?B = circuit_mat d ?B *\<^sub>v ?\<psi>" by (rule circuit_mat_run[symmetric]) (use g S in auto)
  also have "circuit_mat d ?B = hhl_gates A Ub t0 k C ! i"
    using arg_cong[OF hhl_blocks_circuit[OF A(1,2) n0 k Ub(1)], of "\<lambda>l. l ! i"] i dd by simp
  also have "hhl_gates A Ub t0 k C ! i *\<^sub>v ?\<psi> = hhl_states A b t0 k C ! Suc i" by (rule hhl_steps[OF A n0 k t0 spec Ub i])
  finally show ?thesis using hoare_run[where Us = ?B, OF g S] by simp
qed

theorem hhl_elem_trajectory:
  "state_sig.hoare_partial [2 ^ k, n, 2]
     (outer_prod (hhl_states A b t0 k C ! 0) (hhl_states A b t0 k C ! 0))
     (utrans_seq (hhl_elem_gates A Ub t0 k C))
     (outer_prod (hhl_states A b t0 k C ! 8) (hhl_states A b t0 k C ! 8))"
proof -
  interpret state_sig "[2 ^ k, n, 2]" .
  let ?\<psi> = "hhl_states A b t0 k C ! 0"
  have dd: "d = 2 ^ k * (n * 2)" by (simp add: d_def)
  have nA': "dim_row A = n" using A(1) by simp
  have g: "\<And>U. U \<in> set (hhl_elem_gates A Ub t0 k C) \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" using elem_gates_ok dd by auto
  have g0: "\<And>U. U \<in> set (hhl_gates A Ub t0 k C) \<Longrightarrow> U \<in> carrier_mat d d" using gates_ok[OF A n0 k t0 spec Ub Cb] dd by auto
  have S: "dim_vec ?\<psi> = d" "inner_prod ?\<psi> ?\<psi> = 1" using states_ok[OF A n0 k t0 spec Ub Cb, of 0] dd by auto
  have "run_gates ?\<psi> (hhl_elem_gates A Ub t0 k C) = circuit_mat d (hhl_elem_gates A Ub t0 k C) *\<^sub>v ?\<psi>"
    by (rule circuit_mat_run[symmetric]) (use g S in auto)
  also have "\<dots> = circuit_mat d (hhl_gates A Ub t0 k C) *\<^sub>v ?\<psi>" unfolding dd hhl_elem_circuit ..
  also have "\<dots> = run_gates ?\<psi> (hhl_gates A Ub t0 k C)" by (rule circuit_mat_run) (use g0 S in auto)
  also have "\<dots> = hhl_states A b t0 k C ! 8"
    using hhl_run[OF A n0 k t0 spec Ub] by (simp add: hhl_states_def Let_def nA')
  finally show ?thesis using hoare_run[where Us = "hhl_elem_gates A Ub t0 k C", OF g S] by simp
qed

end

end
