theory Simulation_Rounded
  imports Diagonal_Oracle
begin

section \<open>The simulation with rounded entries\<close>

text \<open>Replacing the entry and diagonal gates by their $b$-bit roundings moves each by at most
$6\pi/2^b$ and $2\pi/2^b$; the errors of a product of unitaries add up.\<close>

definition sgate_rnd :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> sgate \<Rightarrow> complex Matrix.mat" where
  "sgate_rnd b n d A Os g = (if g = Ent then ent_rounded b (n * n) (ent_code b n d A)
     else if g = DiagQ then dia_rounded b (n * n) (dia_code b n d A) else sgate_mat n d A Os g)"

definition gate_err :: "nat \<Rightarrow> sgate \<Rightarrow> real" where
  "gate_err b g = (if g = Ent then 6 * pi / 2 ^ b else if g = DiagQ then 2 * pi / 2 ^ b else 0)"

lemma rblock_unitary: "Quantum.unitary (rblock \<theta> \<phi>)"
proof -
  note H = hadamard_facts
  have p: "pp s \<in> carrier_mat 2 2" "Quantum.unitary (pp s)" for s by (simp_all add: pp_def dmat_unitary)
  have z: "zp s \<in> carrier_mat 2 2" "Quantum.unitary (zp s)" for s by (simp_all add: zp_def dmat_unitary)
  have c1: "pp \<phi> * Hadamard \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF p(1) H(1)])
  have c2: "pp \<phi> * Hadamard * zp \<theta> \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF c1 z(1)])
  have c3: "pp \<phi> * Hadamard * zp \<theta> * Hadamard \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF c2 H(1)])
  have u1: "Quantum.unitary (pp \<phi> * Hadamard)" by (rule unitary_mult[OF p(2) H(2) p(1) H(1)])
  have u2: "Quantum.unitary (pp \<phi> * Hadamard * zp \<theta>)" by (rule unitary_mult[OF u1 z(2) c1 z(1)])
  have u3: "Quantum.unitary (pp \<phi> * Hadamard * zp \<theta> * Hadamard)" by (rule unitary_mult[OF u2 H(2) c2 H(1)])
  show ?thesis unfolding rblock_left by (rule unitary_mult[OF u3 p(2) c3 p(1)])
qed

lemma sgate_rnd_facts:
  assumes g: "gate_ok K g" and Os: "\<And>c. c < K \<Longrightarrow> colour_oracle n (q c) (Os c)"
  shows "sgate_rnd b n d A Os g \<in> carrier_mat (n * n * 2) (n * n * 2)" "Quantum.unitary (sgate_rnd b n d A Os g)"
    "sgate_mat n d A Os g \<in> carrier_mat (n * n * 2) (n * n * 2)" "Quantum.unitary (sgate_mat n d A Os g)"
    "sgate_mat n d A Os g \<approx>\<^bsub>gate_err b g\<^esub> sgate_rnd b n d A Os g"
proof -
  have Oc: "\<And>c. c < K \<Longrightarrow> Os c \<in> carrier_mat (n * n * 2) (n * n * 2)" using Os unfolding colour_oracle_def by blast
  show sc: "sgate_mat n d A Os g \<in> carrier_mat (n * n * 2) (n * n * 2)" by (rule sgate_carrier[where K = K]) (use Oc g in auto)
  show "Quantum.unitary (sgate_mat n d A Os g)"
    using g Os by (cases g) (auto simp: colour_oracle_def unitary_dagger cmp_gate_def invol_pmat_unitary
        cmp_perm_invol ent_gate_unitary dia_gate_unitary)
  show "sgate_rnd b n d A Os g \<in> carrier_mat (n * n * 2) (n * n * 2)"
    using sc by (simp add: sgate_rnd_def ent_rounded_def dia_rounded_def)
  show "Quantum.unitary (sgate_rnd b n d A Os g)"
    using g Os by (cases g) (auto simp: sgate_rnd_def colour_oracle_def unitary_dagger cmp_gate_def invol_pmat_unitary
        cmp_perm_invol ent_rounded_def dia_rounded_def intro!: ctrl_blocks_unitary rblock_unitary dmat_unitary)
  show "sgate_mat n d A Os g \<approx>\<^bsub>gate_err b g\<^esub> sgate_rnd b n d A Os g"
  proof (cases "g = Ent \<or> g = DiagQ")
    case True
    thus ?thesis using ent_gate_rounded[of n d A b] dia_gate_rounded[of n d A b]
      by (auto simp: sgate_rnd_def gate_err_def)
  next
    case False
    hence "sgate_rnd b n d A Os g = sgate_mat n d A Os g" "gate_err b g = 0" by (auto simp: sgate_rnd_def gate_err_def)
    thus ?thesis using op_close_refl[OF order_refl sc] by simp
  qed
qed

theorem sim_rounded_close:
  assumes Os: "\<And>c. c < K \<Longrightarrow> colour_oracle n (q c) (Os c)" and sl: "\<And>g. g \<in> set sl \<Longrightarrow> gate_ok K g"
  shows "sg_run n d A Os sl \<approx>\<^bsub>sum_list (map (gate_err b) sl)\<^esub> circuit_mat (n * n * 2) (map (sgate_rnd b n d A Os) sl)"
proof -
  let ?N = "n * n * 2"
  have "sg_run n d A Os sl \<approx>\<^bsub>sum_list (map (gate_err b) sl)\<^esub> circuit_mat ?N (map (sgate_rnd b n d A Os) sl)
      \<and> circuit_mat ?N (map (sgate_rnd b n d A Os) sl) \<in> carrier_mat ?N ?N \<and> Quantum.unitary (circuit_mat ?N (map (sgate_rnd b n d A Os) sl))
      \<and> sg_run n d A Os sl \<in> carrier_mat ?N ?N \<and> Quantum.unitary (sg_run n d A Os sl)"
    using sl
  proof (induction sl)
    case Nil
    have "(1\<^sub>m ?N :: complex Matrix.mat) \<approx>\<^bsub>0\<^esub> 1\<^sub>m ?N" by (rule op_close_refl[where n = ?N]) simp_all
    thus ?case by (simp add: id_is_unitary)
  next
    case (Cons g sl)
    have g: "gate_ok K g" using Cons.prems by simp
    have sl': "\<And>h. h \<in> set sl \<Longrightarrow> gate_ok K h" using Cons.prems by simp
    note IH = Cons.IH[OF sl']
    note F = sgate_rnd_facts[where K = K and q = q and Os = Os, OF g Os]
    let ?R = "sg_run n d A Os sl" and ?Q = "circuit_mat ?N (map (sgate_rnd b n d A Os) sl)"
    let ?G = "sgate_mat n d A Os g" and ?H = "sgate_rnd b n d A Os g"
    have Rc: "?R \<in> carrier_mat ?N ?N" and Ru: "Quantum.unitary ?R" and Qc: "?Q \<in> carrier_mat ?N ?N"
      and Qu: "Quantum.unitary ?Q" and cl: "?R \<approx>\<^bsub>sum_list (map (gate_err b) sl)\<^esub> ?Q" using IH by blast+
    have c1: "?R * ?G \<approx>\<^bsub>sum_list (map (gate_err b) sl)\<^esub> ?Q * ?G"
      by (rule op_close_mult_right[OF F(3,4) Rc Qc cl])
    have c2: "?Q * ?G \<approx>\<^bsub>gate_err b g\<^esub> ?Q * ?H"
      by (rule op_close_mult_left[OF Qc Qu F(3) F(1) F(5)])
    have "?R * ?G \<approx>\<^bsub>sum_list (map (gate_err b) sl) + gate_err b g\<^esub> ?Q * ?H"
      by (rule op_close_trans[OF c1 c2 mult_carrier_mat[OF Rc F(3)] mult_carrier_mat[OF Qc F(3)] mult_carrier_mat[OF Qc F(1)]])
    moreover have "?Q * ?H \<in> carrier_mat ?N ?N" "Quantum.unitary (?Q * ?H)"
      using mult_carrier_mat[OF Qc F(1)] unitary_mult[OF Qu F(2) Qc F(1)] by simp_all
    moreover have "?R * ?G \<in> carrier_mat ?N ?N" "Quantum.unitary (?R * ?G)"
      using mult_carrier_mat[OF Rc F(3)] unitary_mult[OF Ru F(4) Rc F(3)] by simp_all
    ultimately show ?case by (simp add: add.commute)
  qed
  thus ?thesis by blast
qed

lemma sum_list_concat: "sum_list (concat xss) = sum_list (map sum_list xss)"
  by (induction xss) simp_all

lemma sim_gates_err: "sum_list (map (gate_err b) (sim_gates K r)) = r * (K * (6 * pi / 2 ^ b) + 2 * pi / 2 ^ b)"
proof -
  have c: "sum_list (map (gate_err b) (colour_gates c)) = 6 * pi / 2 ^ b" for c
    by (simp add: colour_gates_def gate_err_def)
  have s: "sum_list (map (gate_err b) (step_gates K)) = K * (6 * pi / 2 ^ b) + 2 * pi / 2 ^ b"
    by (simp add: step_gates_def map_concat sum_list_concat comp_def c sum_list_triv gate_err_def)
  show ?thesis by (simp add: sim_gates_def map_concat sum_list_concat s map_replicate sum_list_replicate)
qed

end
