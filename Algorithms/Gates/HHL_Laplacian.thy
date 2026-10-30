theory HHL_Laplacian
  imports HHL_Stage_Counts
begin

section \<open>HHL for the shifted cycle Laplacian in elementary gates\<close>

subsection \<open>The simulation and the register product\<close>

lemma lap_V:
  fixes t :: real and r :: nat
  assumes m: "2 \<le> m" and mu: "0 \<le> \<mu>" and r: "0 < r"
  defines "E \<equiv> evolution_product (2 ^ m) (t / real r) (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m)))"
  shows "E ^\<^sub>m r \<in> carrier_mat (2 ^ m) (2 ^ m)" "Quantum.unitary (E ^\<^sub>m r)"
    "E ^\<^sub>m r \<approx>\<^bsub>18 * (2 + \<mu>)\<^sup>2 * t\<^sup>2 / real r\<^esub> evolution (slap (2 ^ m) \<mu>) t"
proof -
  note n = pow_facts[OF m]
  have pinv: "\<And>c. c < 2 \<Longrightarrow> invol (2 ^ m) (lp (2 ^ m) c)" using lp_invol[OF n(1)] by blast
  have L: "0 \<le> 2 + \<mu>" using mu by simp
  have hb: "\<And>H. H \<in> set (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m))) \<Longrightarrow> herm_bounded (2 ^ m) (2 + \<mu>) H"
    by (rule sparse_parts_bounded[OF slap_carrier slap_hermitian pinv L slap_bound[OF mu]])
  have Ec: "E \<in> carrier_mat (2 ^ m) (2 ^ m)" unfolding E_def
    by (rule evolution_product_carrier) (use hb in \<open>auto simp: herm_bounded_def\<close>)
  show "E ^\<^sub>m r \<in> carrier_mat (2 ^ m) (2 ^ m)" using Ec by simp
  show "Quantum.unitary (E ^\<^sub>m r)" by (rule unitary_pow[OF Ec]) (unfold E_def, rule evolution_product_unitary[OF hb])
  show "E ^\<^sub>m r \<approx>\<^bsub>18 * (2 + \<mu>)\<^sup>2 * t\<^sup>2 / real r\<^esub> evolution (slap (2 ^ m) \<mu>) t"
    unfolding E_def by (rule slap_trotter[OF mu n(1,2) r])
qed

lemma hhl_reg:
  assumes Vm: "Vm \<in> carrier_mat n n" "Quantum.unitary Vm" and N: "0 < N" and A: "dim_row A = n"
    and P: "Prep \<in> carrier_mat (N * (n * 2)) (N * (n * 2))"
  shows "circuit_mat (N * (n * 2)) [Prep, ctrl_pow N (n * 2) (Vm \<Otimes> 1\<^sub>m 2), (fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2),
      hhl_rot_stage A t0 N C, ((fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2))\<^sup>\<dagger>, (ctrl_pow N (n * 2) (Vm \<Otimes> 1\<^sub>m 2))\<^sup>\<dagger>]
    = sem N (n * 2) (Vm \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 N C Prep)"
proof -
  let ?D = "N * (n * 2)" and ?O = "Vm \<Otimes> 1\<^sub>m 2"
  let ?Cp = "ctrl_pow N (n * 2) ?O" and ?Fd = "(fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2)" and ?Rg = "hhl_rot_stage A t0 N C"
  have O: "?O \<in> carrier_mat (n * 2) (n * 2)" "Quantum.unitary ?O" using Vm by (auto intro!: carrier_matI tensor_mat_unitary_one_right)
  have Cc: "?Cp \<in> carrier_mat ?D ?D" by simp
  have Fc: "?Fd \<in> carrier_mat ?D ?D" using dagger_carrier[OF fourier_carrier[of N]] by (intro carrier_matI) simp_all
  have Rc: "?Rg \<in> carrier_mat ?D ?D" using hhl_rot_stage_ok[of A t0 N C] A by simp
  have Cd: "?Cp\<^sup>\<dagger> \<in> carrier_mat ?D ?D" and Fd: "?Fd\<^sup>\<dagger> \<in> carrier_mat ?D ?D" using Cc Fc by (simp_all add: dagger_carrier)
  have pe: "pe_unitary N (n * 2) ?O = ?Fd * ?Cp" by (simp add: pe_unitary_def)
  have pd: "(?Fd * ?Cp)\<^sup>\<dagger> = (?Cp\<^sup>\<dagger>) * (?Fd\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Fc Cc in simp)
  have "sem N (n * 2) ?O (hhl_full_prog A t0 N C Prep) = sem N (n * 2) ?O (HHL_Simulation.hhl_prog N (n * 2) ?Rg) * Prep"
    by (simp add: hhl_full_prog_def A)
  also have "sem N (n * 2) ?O (HHL_Simulation.hhl_prog N (n * 2) ?Rg) = ((?Cp\<^sup>\<dagger>) * (?Fd\<^sup>\<dagger>)) * (?Rg * (?Fd * ?Cp))"
    using sem_hhl_prog[OF O N Rc] unfolding pe pd .
  finally have s: "sem N (n * 2) ?O (hhl_full_prog A t0 N C Prep) = ((?Cp\<^sup>\<dagger>) * (?Fd\<^sup>\<dagger>)) * (?Rg * (?Fd * ?Cp)) * Prep" .
  show ?thesis unfolding s using P Cc Fc Rc Cd Fd by (simp add: assoc_mult_mat[of _ ?D ?D _ ?D _ ?D])
qed

subsection \<open>The whole circuit\<close>

definition lift_a :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "lift_a a Us = map (\<lambda>U. 1\<^sub>m (2 ^ a) \<Otimes> U) Us"

lemma lift_a_props:
  assumes E: "\<forall>U \<in> set Us. elementary (2 ^ Kr) U"
  shows "stands_for (2 ^ a) (2 ^ Kr) (circuit_mat (2 ^ (Kr + a)) (lift_a a Us)) (circuit_mat (2 ^ Kr) Us)"
    "\<forall>U \<in> set (lift_a a Us). elementary (2 ^ (Kr + a)) U" "length (lift_a a Us) = length Us"
proof -
  have KK: "(2::nat) ^ (Kr + a) = 2 ^ a * 2 ^ Kr" by (simp add: power_add)
  have c: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ Kr) (2 ^ Kr)" using E elementary_unitary(1) by blast
  have "circuit_mat (2 ^ (Kr + a)) (lift_a a Us) = 1\<^sub>m (2 ^ a) \<Otimes> circuit_mat (2 ^ Kr) Us"
    unfolding lift_a_def KK by (rule circuit_mat_tensor_left[OF c]) simp_all
  thus "stands_for (2 ^ a) (2 ^ Kr) (circuit_mat (2 ^ (Kr + a)) (lift_a a Us)) (circuit_mat (2 ^ Kr) Us)"
    using stands_for_lift[OF circuit_mat_carrier[OF c], where A = "2 ^ a"] by simp
  show "\<forall>U \<in> set (lift_a a Us). elementary (2 ^ (Kr + a)) U"
    unfolding lift_a_def KK using E elementary_left by auto
  show "length (lift_a a Us) = length Us" by (simp add: lift_a_def)
qed

text_raw \<open>
\begin{center}\normalfont
\begin{quantikz}[row sep=0.35cm, column sep=0.3cm]
\lstick{clock $\ket{0}^k$} & \gate{W}\qwbundle{} & \ctrl{1} & \gate{F^\dagger} & \ctrl{2} & \gate{F} & \ctrl{1} & \qw \\
\lstick{system $\ket{0}^m$} & \gate{U_b}\qwbundle{} & \gate{V^{c}} & \qw & \qw & \qw & \gate{V^{-c}} & \qw \\
\lstick{flag $\ket{0}$} & \qw & \qw & \qw & \gate{R_c} & \qw & \qw & \meter{}
\end{quantikz} \\[0.3em]
{\small The seven blocks of \texttt{hhl\_lap\_gates}: window $W$, preparation $U_b$, phase estimation
(each $V^{2^j}$ controlled by clock bit $j$), inverse Fourier transform, rotation of the flag by the
clock value $c$, and the inverses.  Ancillas are not drawn.}
\end{center}
\<close>

definition hhl_angles :: "real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "hhl_angles t0 k C c = arcsin (clamp (C / reg_eig t0 (2 ^ k) c))"

definition hhl_lap_gates :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "hhl_lap_gates m k a p \<mu> t0 r C Bs = concat
     [lift_a a (map (\<lambda>G. G \<Otimes> 1\<^sub>m (2 ^ m * 2)) (prep_gates k (win_coef (2 ^ k)))),
      relab (m + p) (Suc (m + k) + a) ([1..<Suc m] @ [Suc (m + k)..<Suc (m + k) + p]) Bs,
      lap_pe m k a \<mu> t0 r,
      lift_a a (map (\<lambda>G. G \<Otimes> 1\<^sub>m (2 ^ m * 2)) (rev (map dagger (qft_circuit k)))),
      lift_a a (rs_gates k m (hhl_angles t0 k C)),
      rev (map dagger (lift_a a (map (\<lambda>G. G \<Otimes> 1\<^sub>m (2 ^ m * 2)) (rev (map dagger (qft_circuit k)))))),
      rev (map dagger (lap_pe m k a \<mu> t0 r))]"

subsection \<open>Small bridges\<close>

lemma anc_unit:
  assumes N: "0 < N"
  shows "anc A N *\<^sub>v unit_vec N 0 = unit_vec (A * N) 0"
proof -
  have "anc A N *\<^sub>v unit_vec N 0 = Matrix.col (anc A N) 0" by (rule mult_mat_vec_unit_vec[OF anc_carrier N])
  also have "\<dots> = unit_vec (A * N) 0" by (rule eq_vecI) (use N in \<open>auto simp: anc_def unit_vec_def\<close>)
  finally show ?thesis .
qed

lemma circuit_two:
  assumes "G1 \<in> carrier_mat K K" "G2 \<in> carrier_mat K K" "\<And>U. U \<in> set Gs \<Longrightarrow> U \<in> carrier_mat K K"
  shows "circuit_mat K (G1 # G2 # Gs) = circuit_mat K ((G2 * G1) # Gs)"
  using assms circuit_mat_carrier[of Gs K] by (simp add: assoc_mult_mat[of _ K K _ K _ K])

lemma win_prep_split:
  assumes k: "1 \<le> k" and n0: "0 < n" and Ub: "Ub \<in> carrier_mat n n"
  shows "win_prep_mat k n Ub = prep_gate (2 ^ k) Ub * (circuit_mat (2 ^ k) (prep_gates k (win_coef (2 ^ k))) \<Otimes> 1\<^sub>m (n * 2))"
proof -
  let ?K = "2 ^ k * (n * 2)" and ?L = "map (\<lambda>G. G \<Otimes> 1\<^sub>m (n * 2)) (prep_gates k (win_coef (2 ^ k)))"
  have wc: "\<And>G. G \<in> set (prep_gates k (win_coef (2 ^ k))) \<Longrightarrow> G \<in> carrier_mat (2 ^ k) (2 ^ k)"
    using window_prep(2)[OF k] elementary_unitary(1) by blast
  have Lc: "\<And>U. U \<in> set ?L \<Longrightarrow> U \<in> carrier_mat ?K ?K" using wc by auto
  have Pc: "prep_gate (2 ^ k) Ub \<in> carrier_mat ?K ?K" using Ub by (simp add: prep_gate_def)
  have "win_prep_mat k n Ub = circuit_mat ?K [prep_gate (2 ^ k) Ub] * circuit_mat ?K ?L"
    unfolding win_prep_mat_def win_prep_gates_def by (rule circuit_mat_append) (use Lc Pc in auto)
  also have "circuit_mat ?K ?L = circuit_mat (2 ^ k) (prep_gates k (win_coef (2 ^ k))) \<Otimes> 1\<^sub>m (n * 2)"
    by (rule circuit_mat_tensor_right[OF wc]) (use n0 in simp_all)
  finally show ?thesis using Pc by simp
qed

lemma rot_stage_slap:
  "hhl_rot_stage (slap (2 ^ m) \<mu>) t0 (2 ^ k) C = ctrl_blocks (2 ^ k) (2 ^ m * 2) (\<lambda>c. 1\<^sub>m (2 ^ m) \<Otimes> Rot (hhl_angles t0 k C c))"
  unfolding hhl_rot_stage_def hhl_angles_def dim_slap by (rule ctrl_blocks_cong) (simp add: rot_Rot[OF clamp_abs])

lemma prep_gate_wg:
  assumes Ub: "Ub \<in> carrier_mat (2 ^ m) (2 ^ m)"
  shows "wg (Suc (m + k)) [1..<Suc m] Ub = prep_gate (2 ^ k) Ub"
proof -
  have e: "(2::nat) ^ 1 = 2" "k + m + 1 = Suc (m + k)" "1 + m = Suc m" by simp_all
  have "1\<^sub>m (2 ^ k) \<Otimes> (Ub \<Otimes> 1\<^sub>m (2 ^ 1)) = wg (k + m + 1) [1..<1 + m] Ub" by (rule tensor_wg[OF Ub])
  hence "1\<^sub>m (2 ^ k) \<Otimes> (Ub \<Otimes> 1\<^sub>m 2) = wg (Suc (m + k)) [1..<Suc m] Ub" unfolding e .
  thus ?thesis unfolding prep_gate_def by (rule sym)
qed

subsection \<open>The headline\<close>

text \<open>HHL for $A = L + \mu I$, $L$ the cycle Laplacian on $2^m$ points, with every gate
elementary on $a$ clean ancillas: the clock window, the given preparation \<open>Bs\<close> of $\ket b$ on
$p \le a$ ancillas, phase estimation by $2(2^k-1)$ controlled $r$-step Trotter products, the
Fourier circuit and the rotation stage.  The output is the HHL output for the Trotter product $V$,
so the guarantees of \<open>hhl_complete\<close> hold with $\eta = 18(2+\mu)^2 t_0^2/r$.\<close>

theorem hhl_lap_gates_correct:
  fixes Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and Bs :: "complex Matrix.mat list"
    and m k a p r :: nat and \<mu> t0 C \<theta> lmin \<epsilon> :: real
  assumes m: "2 \<le> m" and k: "1 \<le> k" and am: "m \<le> a" and ap: "p \<le> a" and r: "0 < r" and mu: "0 \<le> \<mu>"
    and Bs: "\<forall>U \<in> set Bs. elementary (2 ^ (m + p)) U" and SB: "stands_for (2 ^ p) (2 ^ m) (circuit_mat (2 ^ (m + p)) Bs) Ub"
    and Ub: "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec (2 ^ m) 0 = b" and b: "dim_vec b = 2 ^ m" "\<parallel>b\<parallel> = 1"
    and t0: "0 < t0" and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin" "lmin \<le> \<mu>"
    and tb: "t0 * (4 + \<mu>) \<le> pi / 2" and e: "0 < \<epsilon>"
    and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real (2 ^ k)"
    and small: "\<epsilon> + 2 * real (2 ^ k - 1) * (18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r) \<le> C * t0 / pi"
  defines "K \<equiv> Suc (m + k) + a"
    and "out \<equiv> sem (2 ^ k) (2 ^ m * 2) (evolution_product (2 ^ m) (t0 / real r) (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m))) ^\<^sub>m r \<Otimes> 1\<^sub>m 2)
                (hhl_full_prog (slap (2 ^ m) \<mu>) t0 (2 ^ k) C (win_prep_mat k (2 ^ m) Ub)) *\<^sub>v unit_vec (2 ^ k * (2 ^ m * 2)) 0"
    and "x \<equiv> herm_inv (slap (2 ^ m) \<mu>) *\<^sub>v b"
  shows "\<forall>U \<in> set (hhl_lap_gates m k a p \<mu> t0 r C Bs). elementary (2 ^ K) U"
    "circuit_mat (2 ^ K) (hhl_lap_gates m k a p \<mu> t0 r C Bs) *\<^sub>v unit_vec (2 ^ K) 0 = anc (2 ^ a) (2 ^ Suc (m + k)) *\<^sub>v out"
    "C * t0 / pi \<le> \<parallel>post1 out\<parallel>"
    "\<parallel>complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out
       - tensor_vec (win_state (2 ^ k)) (tensor_vec (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x) (unit_vec 2 1))\<parallel>
      \<le> 2 * (\<epsilon> + 2 * real (2 ^ k - 1) * (18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r)) / (C * \<parallel>x\<parallel>)"
    "length (hhl_lap_gates m k a p \<mu> t0 r C Bs) \<le> k * (1 + 2 ^ k * (2 * k + 1)) + length Bs * (4 * K + 1)
      + 2 * ((2 ^ k - 1) * (r * (2 * (m * (m + 2) * (6 * K + 7)) + 3 * (4 * K + 1))))
      + 2 * (k ^ 3 + 2 * k) + (2 * m + 1) * (1 + 2 ^ k * (2 * k + 1))"
proof -
  let ?n = "2 ^ m :: nat" and ?N = "2 ^ k :: nat" and ?R = "Suc (m + k)"
  let ?D = "2 ^ k * (2 ^ m * 2) :: nat"
  let ?Lw0 = "map (\<lambda>G. G \<Otimes> 1\<^sub>m (2 ^ m * 2)) (prep_gates k (win_coef (2 ^ k)))"
  let ?Lf0 = "map (\<lambda>G. G \<Otimes> 1\<^sub>m (2 ^ m * 2)) (rev (map dagger (qft_circuit k)))"
  let ?Lr0 = "rs_gates k m (hhl_angles t0 k C)"
  let ?vs = "[1..<Suc m] @ [?R..<?R + p]"
  let ?Lb = "relab (m + p) K ?vs Bs" and ?Lp = "lap_pe m k a \<mu> t0 r"
  let ?W = "circuit_mat (2 ^ k) (prep_gates k (win_coef (2 ^ k)))"
  define A where "A = slap (2 ^ m) \<mu>"
  define Vr where "Vr = evolution_product (2 ^ m) (t0 / real r) (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m))) ^\<^sub>m r"
  let ?Rg = "hhl_rot_stage A t0 ?N C"
  let ?Cp = "ctrl_pow ?N (?n * 2) (Vr \<Otimes> 1\<^sub>m 2)" and ?Fd = "(fourier ?N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (?n * 2)"
  have DR: "?D = 2 ^ ?R" by (simp add: power_add ac_simps)
  have KK: "(2::nat) ^ K = 2 ^ a * 2 ^ ?R" by (simp add: K_def power_add)
  have KR: "K = ?R + a" by (simp add: K_def)
  have n0: "0 < ?n" by simp
  have N2: "2 \<le> ?N" using power_increasing[OF k, of "2::nat"] by simp
  \<comment> \<open>the simulation and the matrix\<close>
  note LV = lap_V[OF m mu r, where t = t0, folded Vr_def]
  have Ac: "A \<in> carrier_mat ?n ?n" "hermitian A" unfolding A_def by (simp_all add: slap_hermitian)
  have dA: "dim_row A = ?n" unfolding A_def by simp
  have spec: "lmin \<le> l \<and> t0 * l \<le> pi / 2" if "l \<in> herm_spectrum A" for l
  proof -
    have "\<mu> \<le> l \<and> l \<le> 4 + \<mu>" using slap_spectrum that unfolding A_def by blast
    moreover have "t0 * l \<le> t0 * (4 + \<mu>)" using calculation t0 by (simp add: mult_left_mono)
    ultimately show ?thesis using lmin(2) tb by linarith
  qed
  have Ubc: "Ub \<in> carrier_mat ?n ?n" using SB by (simp add: stands_for_def)
  note WP = win_prep_gates_props[OF k n0 Ubc Ub]
  have eta: "0 \<le> 18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r" by simp
  have Vc: "Vr \<approx>\<^bsub>18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r\<^esub> evolution A t0" using LV(3) unfolding A_def .
  have small': "\<epsilon> + 2 * real (?N - 1) * (18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r) \<le> C * t0 / pi" using small by simp
  note HC = hhl_complete[OF Ac t0 N2 C th lmin(1) spec b e NQ LV(1,2) Vc eta WP(3,4,5) small']
  show "C * t0 / pi \<le> \<parallel>post1 out\<parallel>" using HC(1) unfolding out_def A_def Vr_def by (simp add: ac_simps)
  show "\<parallel>complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out
       - tensor_vec (win_state (2 ^ k)) (tensor_vec (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x) (unit_vec 2 1))\<parallel>
      \<le> 2 * (\<epsilon> + 2 * real (2 ^ k - 1) * (18 * (2 + \<mu>)\<^sup>2 * t0\<^sup>2 / real r)) / (C * \<parallel>x\<parallel>)"
    using HC(2) unfolding out_def x_def A_def Vr_def by (simp add: ac_simps)
  \<comment> \<open>the seven blocks on the register\<close>
  have N0: "0 < ?N" by simp
  have Ew0: "\<forall>U \<in> set ?Lw0. elementary (2 ^ ?R) U"
    using window_prep(2)[OF k] elementary_right[of "2 ^ k" _ "2 ^ m * 2"] unfolding DR[symmetric] by auto
  have Ef0: "\<forall>U \<in> set ?Lf0. elementary (2 ^ ?R) U"
    using qft_inv_circuit(2)[of k] elementary_right[of "2 ^ k" _ "2 ^ m * 2"] unfolding DR[symmetric] by auto
  have Er0: "\<forall>U \<in> set ?Lr0. elementary (2 ^ ?R) U" using rs_gates_props(2)[OF k] unfolding DR[symmetric] .
  have wc: "\<And>G. G \<in> set (prep_gates k (win_coef (2 ^ k))) \<Longrightarrow> G \<in> carrier_mat (2 ^ k) (2 ^ k)"
    using window_prep(2)[OF k] elementary_unitary(1) by blast
  have fc: "\<And>G. G \<in> set (rev (map dagger (qft_circuit k))) \<Longrightarrow> G \<in> carrier_mat (2 ^ k) (2 ^ k)"
    using qft_inv_circuit(2)[of k] elementary_unitary(1) by blast
  have cw0: "circuit_mat (2 ^ ?R) ?Lw0 = ?W \<Otimes> 1\<^sub>m (?n * 2)"
    unfolding DR[symmetric] by (rule circuit_mat_tensor_right[OF wc]) simp_all
  have cf0: "circuit_mat (2 ^ ?R) ?Lf0 = ?Fd"
    unfolding DR[symmetric] qft_inv_circuit(1)[symmetric] by (rule circuit_mat_tensor_right[OF fc]) simp_all
  have cr0: "circuit_mat (2 ^ ?R) ?Lr0 = ?Rg"
    using rs_gates_props(1)[OF k, of m "hhl_angles t0 k C"] unfolding DR A_def rot_stage_slap .
  note S1 = lift_a_props[OF Ew0, where a = a, folded KR] and S4 = lift_a_props[OF Ef0, where a = a, folded KR]
    and S5 = lift_a_props[OF Er0, where a = a, folded KR]
  \<comment> \<open>the preparation of b\<close>
  have vd: "distinct ?vs" and vK: "\<And>v. v \<in> set ?vs \<Longrightarrow> v < K" and vl: "length ?vs = m + p"
    using ap by (auto simp: K_def)
  have vlo: "\<And>l. l < m \<Longrightarrow> ?vs ! l < ?R" and vhi: "\<And>l. l < p \<Longrightarrow> ?R \<le> ?vs ! (m + l) \<and> ?vs ! (m + l) < ?R + a"
    using ap by (auto simp: nth_append simp del: upt_Suc)
  note RB = relab_props[OF Bs vd vK vl]
  have tk: "take m ?vs = [1..<Suc m]" by simp
  have S2: "stands_for (2 ^ a) (2 ^ ?R) (circuit_mat (2 ^ K) ?Lb) (prep_gate ?N Ub)"
  proof -
    have SW: "stands_for (2 ^ a) (2 ^ ?R) (wg (?R + a) ?vs (circuit_mat (2 ^ (m + p)) Bs)) (wg ?R (take m ?vs) Ub)"
      by (rule stands_for_wg[OF SB vd vl]) (use vlo vhi in simp_all)
    have c: "circuit_mat (2 ^ K) ?Lb = wg (?R + a) ?vs (circuit_mat (2 ^ (m + p)) Bs)" using RB(1) unfolding KR .
    show ?thesis unfolding c using SW unfolding tk prep_gate_wg[OF Ubc] .
  qed
  \<comment> \<open>phase estimation and its inverse\<close>
  note PE = lap_pe_props[OF m am mu, where t = t0 and r = r and k = k]
  have S3: "stands_for (2 ^ a) (2 ^ ?R) (circuit_mat (2 ^ K) ?Lp) ?Cp" using PE(1) unfolding Vr_def KR .
  have Vu: "Quantum.unitary (Vr \<Otimes> 1\<^sub>m 2)" and Vt: "Vr \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (?n * 2) (?n * 2)"
    using LV(1,2) unfolding Vr_def by (auto intro!: carrier_matI tensor_mat_unitary_one_right)
  have Cu: "Quantum.unitary ?Cp" by (rule ctrl_blocks_unitary) (auto intro: pow_carrier_mat[OF Vt] unitary_pow[OF Vt Vu])
  have Cc: "?Cp \<in> carrier_mat (2 ^ ?R) (2 ^ ?R)" unfolding DR[symmetric] by simp
  have Fu: "Quantum.unitary ?Fd" using circuit_elementary_unitary(2)[where Us = ?Lf0 and K = "2 ^ ?R"] Ef0 cf0 by auto
  have Fc: "?Fd \<in> carrier_mat (2 ^ ?R) (2 ^ ?R)" using circuit_elementary_unitary(1)[where Us = ?Lf0 and K = "2 ^ ?R"] Ef0 cf0 by auto
  have Elp: "\<forall>U \<in> set ?Lp. elementary (2 ^ K) U" using PE(2) unfolding KR .
  have Elf: "\<forall>U \<in> set (lift_a a ?Lf0). elementary (2 ^ K) U" by (rule S4(2))
  have uni: "(U\<^sup>\<dagger>) * U = 1\<^sub>m (2 ^ a * 2 ^ ?R)" if "Quantum.unitary U" "U \<in> carrier_mat (2 ^ K) (2 ^ K)" for U
    using that unfolding Quantum.unitary_def KK by simp
  have unr: "G * (G\<^sup>\<dagger>) = 1\<^sub>m (2 ^ ?R)" if "Quantum.unitary G" "G \<in> carrier_mat (2 ^ ?R) (2 ^ ?R)" for G
    using that unfolding Quantum.unitary_def by simp
  have cud: "\<And>Us. \<forall>U \<in> set Us. elementary (2 ^ K) U \<Longrightarrow> circuit_mat (2 ^ K) (rev (map dagger Us)) = (circuit_mat (2 ^ K) Us)\<^sup>\<dagger>"
    by (rule circuit_mat_dagger) (use elementary_unitary(1) in blast)
  have S6: "stands_for (2 ^ a) (2 ^ ?R) (circuit_mat (2 ^ K) (rev (map dagger (lift_a a ?Lf0)))) (?Fd\<^sup>\<dagger>)"
    unfolding cud[OF Elf] using stands_for_dagger[OF S4(1)[unfolded cf0] uni unr[OF Fu Fc]]
      circuit_elementary_unitary[of "lift_a a ?Lf0" "2 ^ K"] Elf by auto
  have S7: "stands_for (2 ^ a) (2 ^ ?R) (circuit_mat (2 ^ K) (rev (map dagger ?Lp))) (?Cp\<^sup>\<dagger>)"
    unfolding cud[OF Elp] using stands_for_dagger[OF S3 uni unr[OF Cu Cc]]
      circuit_elementary_unitary[of ?Lp "2 ^ K"] Elp by auto
  \<comment> \<open>the whole list\<close>
  let ?Ls = "[lift_a a ?Lw0, ?Lb, ?Lp, lift_a a ?Lf0, lift_a a ?Lr0, rev (map dagger (lift_a a ?Lf0)), rev (map dagger ?Lp)]"
  have G: "hhl_lap_gates m k a p \<mu> t0 r C Bs = concat ?Ls" by (simp add: hhl_lap_gates_def K_def)
  have Edag: "\<And>Us. \<forall>U \<in> set Us. elementary (2 ^ K) U \<Longrightarrow> \<forall>U \<in> set (rev (map dagger Us)). elementary (2 ^ K) U"
    using elementary_dagger by auto
  have El: "\<forall>U \<in> set (concat ?Ls). elementary (2 ^ K) U"
    using S1(2) RB(2) Elp Elf S5(2) Edag[OF Elf] Edag[OF Elp] by auto
  show "\<forall>U \<in> set (hhl_lap_gates m k a p \<mu> t0 r C Bs). elementary (2 ^ K) U" unfolding G by (rule El)
  have "circuit_mat (2 ^ K) (concat ?Ls) = circuit_mat (2 ^ K) (map (circuit_mat (2 ^ K)) ?Ls)"
    by (rule circuit_mat_concat) (use El elementary_unitary(1) in fastforce)
  hence circ: "circuit_mat (2 ^ K) (hhl_lap_gates m k a p \<mu> t0 r C Bs) = circuit_mat (2 ^ a * 2 ^ ?R) (map (circuit_mat (2 ^ K)) ?Ls)"
    unfolding G KK[symmetric] .
  have ST: "stands_for (2 ^ a) (2 ^ ?R) (circuit_mat (2 ^ a * 2 ^ ?R) (map (circuit_mat (2 ^ K)) ?Ls))
      (circuit_mat (2 ^ ?R) [?W \<Otimes> 1\<^sub>m (?n * 2), prep_gate ?N Ub, ?Cp, ?Fd, ?Rg, ?Fd\<^sup>\<dagger>, ?Cp\<^sup>\<dagger>])"
    by (rule stands_for_circuit) (simp only: list.map list_all2_Cons list_all2_Nil, intro conjI refl S2 S3 S6 S7
        S1(1)[unfolded cw0] S4(1)[unfolded cf0] S5(1)[unfolded cr0])
  have Wc: "?W \<Otimes> 1\<^sub>m (?n * 2) \<in> carrier_mat (2 ^ ?R) (2 ^ ?R)" using cw0 circuit_elementary_unitary(1)[where Us = ?Lw0 and K = "2 ^ ?R"] Ew0 by auto
  have Pc: "prep_gate ?N Ub \<in> carrier_mat (2 ^ ?R) (2 ^ ?R)" unfolding DR[symmetric] prep_gate_def by (rule carrier_matI) (use Ubc in simp_all)
  have Rc: "?Rg \<in> carrier_mat (2 ^ ?R) (2 ^ ?R)" using cr0 circuit_elementary_unitary(1)[where Us = ?Lr0 and K = "2 ^ ?R"] Er0 by auto
  have reg: "circuit_mat (2 ^ ?R) [?W \<Otimes> 1\<^sub>m (?n * 2), prep_gate ?N Ub, ?Cp, ?Fd, ?Rg, ?Fd\<^sup>\<dagger>, ?Cp\<^sup>\<dagger>]
      = sem ?N (?n * 2) (Vr \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 ?N C (win_prep_mat k ?n Ub))"
  proof -
    have "circuit_mat (2 ^ ?R) [?W \<Otimes> 1\<^sub>m (?n * 2), prep_gate ?N Ub, ?Cp, ?Fd, ?Rg, ?Fd\<^sup>\<dagger>, ?Cp\<^sup>\<dagger>]
        = circuit_mat (2 ^ ?R) [prep_gate ?N Ub * (?W \<Otimes> 1\<^sub>m (?n * 2)), ?Cp, ?Fd, ?Rg, ?Fd\<^sup>\<dagger>, ?Cp\<^sup>\<dagger>]"
      by (rule circuit_two[OF Wc Pc]) (use Cc Fc Rc in \<open>auto simp: dagger_carrier\<close>)
    also have "prep_gate ?N Ub * (?W \<Otimes> 1\<^sub>m (?n * 2)) = win_prep_mat k ?n Ub" by (rule win_prep_split[OF k n0 Ubc, symmetric])
    also have "circuit_mat (2 ^ ?R) [win_prep_mat k ?n Ub, ?Cp, ?Fd, ?Rg, ?Fd\<^sup>\<dagger>, ?Cp\<^sup>\<dagger>]
        = sem ?N (?n * 2) (Vr \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 ?N C (win_prep_mat k ?n Ub))"
      unfolding DR[symmetric] by (rule hhl_reg[OF LV(1,2)[folded Vr_def] N0 dA WP(3)])
    finally show ?thesis .
  qed
  have e0: "unit_vec (2 ^ K) 0 = anc (2 ^ a) (2 ^ ?R) *\<^sub>v unit_vec (2 ^ ?R) 0" unfolding KK by (rule anc_unit[symmetric]) simp
  show "circuit_mat (2 ^ K) (hhl_lap_gates m k a p \<mu> t0 r C Bs) *\<^sub>v unit_vec (2 ^ K) 0 = anc (2 ^ a) (2 ^ Suc (m + k)) *\<^sub>v out"
    unfolding circ e0 stands_for_apply[OF ST unit_vec_carrier] reg unfolding out_def A_def Vr_def DR ..
  \<comment> \<open>the count\<close>
  have l1: "length (lift_a a ?Lw0) \<le> k * (1 + 2 ^ k * (2 * k + 1))" using S1(3) length_prep_gates[of k] by simp
  have l2: "length ?Lb \<le> length Bs * (4 * K + 1)" by (rule RB(3))
  have l3: "length ?Lp \<le> (2 ^ k - 1) * (r * (2 * (m * (m + 2) * (6 * K + 7)) + 3 * (4 * K + 1)))" using PE(3) unfolding KR .
  have l4: "length (lift_a a ?Lf0) \<le> k ^ 3 + 2 * k" using S4(3) length_qft[of k] by simp
  have l5: "length (lift_a a ?Lr0) \<le> (2 * m + 1) * (1 + 2 ^ k * (2 * k + 1))" using S5(3) rs_gates_props(3)[OF k] by simp
  show "length (hhl_lap_gates m k a p \<mu> t0 r C Bs) \<le> k * (1 + 2 ^ k * (2 * k + 1)) + length Bs * (4 * K + 1)
      + 2 * ((2 ^ k - 1) * (r * (2 * (m * (m + 2) * (6 * K + 7)) + 3 * (4 * K + 1))))
      + 2 * (k ^ 3 + 2 * k) + (2 * m + 1) * (1 + 2 ^ k * (2 * k + 1))"
    unfolding G using l1 l2 l3 l4 l5 by simp
qed

end
