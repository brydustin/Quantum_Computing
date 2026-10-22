theory HHL_Trajectory
  imports HHL_Discussion QPE_Register
begin

section \<open>The HHL circuit gate by gate\<close>

text \<open>Registers: clock $\C^N$ ($N=2^k$), system $\C^n$, ancilla $\C^2$, in this order.\<close>

definition prep_gate :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "prep_gate N Ub = 1\<^sub>m N \<Otimes> (Ub \<Otimes> 1\<^sub>m 2)"

definition clock_gate :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "clock_gate G n = G \<Otimes> 1\<^sub>m (n * 2)"

definition evo_gate :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "evo_gate A t0 N = ctrl_pow N (dim_row A * 2) (evolution A t0 \<Otimes> 1\<^sub>m 2)"

definition rot_gate :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "rot_gate A t0 N C = ctrl_blocks N (dim_row A * 2) (hhl_rot C t0 N (dim_row A))"

definition spec_proj :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "spec_proj A t0 N j = mat_fun (\<lambda>x. if x = reg_eig t0 N j then 1 else 0) A"

definition hhl_out :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "hhl_out A C b = tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0)
                 + tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1)"

text \<open>The matrix of $b\mapsto\sum_j\ket j\otimes(F_jb\otimes\ket0+G_jb\otimes\ket1)$.\<close>

definition blk_lift :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "blk_lift N n F G = Matrix.mat (N * (n * 2)) n
     (\<lambda>(r, s). if r mod 2 = 0 then F (r div (n * 2)) $$ (r mod (n * 2) div 2, s) else G (r div (n * 2)) $$ (r mod (n * 2) div 2, s))"

lemma blk_lift_carrier [simp]: "blk_lift N n F G \<in> carrier_mat (N * (n * 2)) n"
  by (simp add: blk_lift_def)

lemma blk_lift_mult_vec:
  assumes F: "\<And>j. j < N \<Longrightarrow> F j \<in> carrier_mat n n" and G: "\<And>j. j < N \<Longrightarrow> G j \<in> carrier_mat n n" and b: "dim_vec b = n"
  shows "blk_lift N n F G *\<^sub>v b = reg_sum N (n * 2) (\<lambda>j. tensor_vec (F j *\<^sub>v b) (unit_vec 2 0) + tensor_vec (G j *\<^sub>v b) (unit_vec 2 1))"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (reg_sum N (n * 2) (\<lambda>j. tensor_vec (F j *\<^sub>v b) (unit_vec 2 0) + tensor_vec (G j *\<^sub>v b) (unit_vec 2 1)))"
  hence r: "r < N * (n * 2)" by simp
  hence n: "0 < n" by (cases n) auto
  define j where "j = r div (n * 2)"
  define q where "q = r mod (n * 2)"
  have j: "j < N" unfolding j_def using r by (simp add: less_mult_imp_div_less)
  have q: "q < n * 2" unfolding q_def using n by simp
  have s0: "q div 2 < n" using q by linarith
  have t: "q mod 2 = r mod 2" unfolding q_def by (simp add: mod_mod_cancel)
  have rr: "r = j * (n * 2) + q" unfolding j_def q_def by (rule div_mult_mod_eq[symmetric])
  have Fd: "dim_row (F j) = n" "dim_col (F j) = n" and Gd: "dim_row (G j) = n" "dim_col (G j) = n" using F[OF j] G[OF j] by auto
  have d0: "dim_vec (tensor_vec (F j *\<^sub>v b) (unit_vec 2 0)) = n * 2" by (rule tensor_vec_dim) (simp_all add: Fd)
  have d1: "dim_vec (tensor_vec (G j *\<^sub>v b) (unit_vec 2 1)) = n * 2" by (rule tensor_vec_dim) (simp_all add: Gd)
  have "(blk_lift N n F G *\<^sub>v b) $ r =
        (\<Sum>s<n. (if r mod 2 = 0 then F j $$ (q div 2, s) else G j $$ (q div 2, s)) * b $ s)"
    unfolding j_def q_def using r b by (simp add: blk_lift_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (if r mod 2 = 0 then (F j *\<^sub>v b) $ (q div 2) else (G j *\<^sub>v b) $ (q div 2))"
    using s0 Fd Gd b by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (tensor_vec (F j *\<^sub>v b) (unit_vec 2 0) + tensor_vec (G j *\<^sub>v b) (unit_vec 2 1)) $ q"
  proof -
    have "(tensor_vec (F j *\<^sub>v b) (unit_vec 2 0) + tensor_vec (G j *\<^sub>v b) (unit_vec 2 1)) $ q =
          (F j *\<^sub>v b) $ (q div 2) * unit_vec 2 0 $ (q mod 2) + (G j *\<^sub>v b) $ (q div 2) * unit_vec 2 1 $ (q mod 2)"
      using q d1 Fd Gd tensor_vec_index[of "F j *\<^sub>v b" n "unit_vec 2 0" 2 q] tensor_vec_index[of "G j *\<^sub>v b" n "unit_vec 2 1" 2 q]
      by simp
    also have "\<dots> = (if r mod 2 = 0 then (F j *\<^sub>v b) $ (q div 2) else (G j *\<^sub>v b) $ (q div 2))"
      using t by (auto simp: unit_vec_def)
    finally show ?thesis by simp
  qed
  also have "\<dots> = reg_sum N (n * 2) (\<lambda>j. tensor_vec (F j *\<^sub>v b) (unit_vec 2 0) + tensor_vec (G j *\<^sub>v b) (unit_vec 2 1)) $ r"
    unfolding rr by (rule reg_sum_index[OF j q, symmetric])
  finally show "(blk_lift N n F G *\<^sub>v b) $ r = reg_sum N (n * 2) (\<lambda>j. tensor_vec (F j *\<^sub>v b) (unit_vec 2 0) + tensor_vec (G j *\<^sub>v b) (unit_vec 2 1)) $ r" .
qed (simp add: blk_lift_def)

lemma reg_eig_inj:
  assumes t0: "0 < t0" and j: "j < N" and i: "i < N" and e: "reg_eig t0 N j = reg_eig t0 N i"
  shows "j = i"
proof -
  have N: "0 < real N" using j by simp
  have e': "(if 2 * j < N then real j else real j - real N) = (if 2 * i < N then real i else real i - real N)"
    using e t0 N by (simp add: reg_eig_def field_simps)
  show ?thesis using e' j i by (auto split: if_splits)
qed

text \<open>The gates in order: prepare $\ket b$, Hadamard layer, controlled evolution, inverse Fourier
transform, controlled rotation, Fourier transform, inverse controlled evolution, Hadamard layer.\<close>

definition hhl_gates :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "hhl_gates A Ub t0 k C =
     [prep_gate (2 ^ k) Ub, clock_gate (Hadamard \<otimes>\<^bsup>k\<^esup>) (dim_row A), evo_gate A t0 (2 ^ k),
      clock_gate ((fourier (2 ^ k))\<^sup>\<dagger>) (dim_row A), rot_gate A t0 (2 ^ k) C, clock_gate (fourier (2 ^ k)) (dim_row A),
      (evo_gate A t0 (2 ^ k))\<^sup>\<dagger>, clock_gate (Hadamard \<otimes>\<^bsup>k\<^esup>) (dim_row A)]"

text \<open>The state after each gate, for $b=U_b\ket0$ and $\mathrm{out}=G_0b\otimes\ket0+G_1b\otimes\ket1$.\<close>

definition hhl_states :: "complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.vec list" where
  "hhl_states A b t0 k C = (let N = 2 ^ k; n = dim_row A; r = 1 / complex_of_real (sqrt (real N)); E = evolution A t0 in
     [tensor_vec (unit_vec N 0) (tensor_vec (unit_vec n 0) (unit_vec 2 0)),
      tensor_vec (unit_vec N 0) (tensor_vec b (unit_vec 2 0)),
      tensor_vec (uniform_state N) (tensor_vec b (unit_vec 2 0)),
      reg_sum N (n * 2) (\<lambda>j. r \<cdot>\<^sub>v tensor_vec (E ^\<^sub>m j *\<^sub>v b) (unit_vec 2 0)),
      reg_sum N (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 N j *\<^sub>v b) (unit_vec 2 0)),
      reg_sum N (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 N j *\<^sub>v b) (rot (C / reg_eig t0 N j) *\<^sub>v unit_vec 2 0)),
      reg_sum N (n * 2) (\<lambda>j. r \<cdot>\<^sub>v ((E ^\<^sub>m j \<Otimes> 1\<^sub>m 2) *\<^sub>v hhl_out A C b)),
      tensor_vec (uniform_state N) (hhl_out A C b),
      tensor_vec (unit_vec N 0) (hhl_out A C b)])"

lemma length_hhl_gates [simp]: "length (hhl_gates A Ub t0 k C) = 8" by (simp add: hhl_gates_def)
lemma length_hhl_states [simp]: "length (hhl_states A b t0 k C) = 9" by (simp add: hhl_states_def Let_def)

primrec run_gates :: "complex Matrix.vec \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.vec" where
  "run_gates v [] = v"
| "run_gates v (U # Us) = run_gates (U *\<^sub>v v) Us"

lemma run_gates_norm:
  "(\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat K K \<and> unitary U) \<Longrightarrow> dim_vec v = K \<Longrightarrow> \<parallel>run_gates v Us\<parallel> = \<parallel>v\<parallel>"
proof (induction Us arbitrary: v)
  case (Cons U Us)
  have U: "U \<in> carrier_mat K K" "unitary U" using Cons.prems by auto
  have "\<parallel>run_gates (U *\<^sub>v v) Us\<parallel> = \<parallel>U *\<^sub>v v\<parallel>" by (rule Cons.IH) (use Cons.prems U in auto)
  also have "\<dots> = \<parallel>v\<parallel>" by (rule unitary_vnorm[OF U Cons.prems(2)])
  finally show ?case by simp
qed simp

lemma tensor_carrier: "A \<in> carrier_mat a a \<Longrightarrow> B \<in> carrier_mat c c \<Longrightarrow> A \<Otimes> B \<in> carrier_mat (a * c) (a * c)"
  by (rule carrier_matI) auto

lemma ctrl_pow_tensor:
  assumes Vm: "Vm \<in> carrier_mat m m" and a: "dim_vec a = N" and w: "dim_vec w = m"
  shows "ctrl_pow N m Vm *\<^sub>v tensor_vec a w = reg_sum N m (\<lambda>j. a $ j \<cdot>\<^sub>v (Vm ^\<^sub>m j *\<^sub>v w))"
proof -
  have Vj: "Vm ^\<^sub>m j \<in> carrier_mat m m" for j using Vm by simp
  have "ctrl_pow N m Vm *\<^sub>v tensor_vec a w = ctrl_blocks N m (\<lambda>j. Vm ^\<^sub>m j) *\<^sub>v reg_sum N m (\<lambda>j. a $ j \<cdot>\<^sub>v w)"
    unfolding tensor_reg_sum[OF a w] ..
  also have "\<dots> = reg_sum N m (\<lambda>j. Vm ^\<^sub>m j *\<^sub>v (a $ j \<cdot>\<^sub>v w))" by (rule ctrl_blocks_reg_sum) (simp_all add: Vj w)
  also have "\<dots> = reg_sum N m (\<lambda>j. a $ j \<cdot>\<^sub>v (Vm ^\<^sub>m j *\<^sub>v w))"
    by (rule reg_sum_cong) (simp add: mult_mat_vec[OF Vj carrier_vecI[OF w]])
  finally show ?thesis .
qed

lemma pow_tensor_one:
  assumes E: "E \<in> carrier_mat n n" and n: "0 < n"
  shows "(E \<Otimes> 1\<^sub>m 2) ^\<^sub>m j = (E ^\<^sub>m j) \<Otimes> 1\<^sub>m 2"
proof (induction j)
  case 0
  show ?case using tensor_mat_id[of n 2] E by simp
next
  case (Suc j)
  have "(E \<Otimes> 1\<^sub>m 2) ^\<^sub>m Suc j = ((E ^\<^sub>m j) \<Otimes> 1\<^sub>m 2) * (E \<Otimes> 1\<^sub>m 2)" using Suc by simp
  also have "\<dots> = (E ^\<^sub>m j * E) \<Otimes> (1\<^sub>m 2 * 1\<^sub>m 2)"
    by (rule mult_distr_tensor[symmetric]) (use E n in simp_all)
  finally show ?case by simp
qed

context
  fixes A Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat n n" "unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
begin

lemma b_dim: "dim_vec b = n" using Ub by auto

lemma hhl_out_dim: "dim_vec (hhl_out A C b) = n * 2"
proof -
  have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
  have Gc: "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A \<in> carrier_mat n n" by (rule mat_fun_carrier[OF A])
  show ?thesis using Hc Gc unfolding hhl_out_def by (simp add: tensor_vec_dim)
qed

lemma traj_prep:
  "prep_gate (2 ^ k) Ub *\<^sub>v tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (unit_vec n 0) (unit_vec 2 0))
   = tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec b (unit_vec 2 0))"
proof -
  have UI: "Ub \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)" by (rule tensor_carrier[OF Ub(1) one_carrier_mat])
  have "prep_gate (2 ^ k) Ub *\<^sub>v tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (unit_vec n 0) (unit_vec 2 0))
        = tensor_vec (1\<^sub>m (2 ^ k) *\<^sub>v unit_vec (2 ^ k) 0) ((Ub \<Otimes> 1\<^sub>m 2) *\<^sub>v tensor_vec (unit_vec n 0) (unit_vec 2 0))"
    unfolding prep_gate_def by (rule tensor_mat_vec_mult[OF one_carrier_mat UI]) (simp_all add: tensor_vec_dim)
  also have "(Ub \<Otimes> 1\<^sub>m 2) *\<^sub>v tensor_vec (unit_vec n 0) (unit_vec 2 0) = tensor_vec (Ub *\<^sub>v unit_vec n 0) (1\<^sub>m 2 *\<^sub>v unit_vec 2 0)"
    by (rule tensor_mat_vec_mult[OF Ub(1) one_carrier_mat]) simp_all
  finally show ?thesis using Ub(3) by simp
qed

lemma traj_hadamard:
  assumes w: "dim_vec w = n * 2"
  shows "clock_gate (Hadamard \<otimes>\<^bsup>k\<^esup>) n *\<^sub>v tensor_vec (unit_vec (2 ^ k) 0) w = tensor_vec (uniform_state (2 ^ k)) w"
proof -
  have "clock_gate (Hadamard \<otimes>\<^bsup>k\<^esup>) n *\<^sub>v tensor_vec (unit_vec (2 ^ k) 0) w
        = tensor_vec ((Hadamard \<otimes>\<^bsup>k\<^esup>) *\<^sub>v unit_vec (2 ^ k) 0) (1\<^sub>m (n * 2) *\<^sub>v w)"
    unfolding clock_gate_def by (rule tensor_mat_vec_mult[OF hadamard_layer_carrier[OF k] one_carrier_mat]) (simp_all add: w)
  thus ?thesis using hadamard_layer_zero[OF k] carrier_vecI[OF w] by simp
qed

lemma traj_evolve:
  "evo_gate A t0 (2 ^ k) *\<^sub>v tensor_vec (uniform_state (2 ^ k)) (tensor_vec b (unit_vec 2 0))
   = reg_sum (2 ^ k) (n * 2) (\<lambda>j. (1 / complex_of_real (sqrt (real (2 ^ k)))) \<cdot>\<^sub>v tensor_vec (evolution A t0 ^\<^sub>m j *\<^sub>v b) (unit_vec 2 0))"
proof -
  have E: "evolution A t0 \<in> carrier_mat n n" using A by simp
  have V: "evolution A t0 \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)" by (rule tensor_carrier[OF E one_carrier_mat])
  have nA: "dim_row A = n" using A(1) by simp
  have "evo_gate A t0 (2 ^ k) *\<^sub>v tensor_vec (uniform_state (2 ^ k)) (tensor_vec b (unit_vec 2 0))
        = reg_sum (2 ^ k) (n * 2) (\<lambda>j. uniform_state (2 ^ k) $ j \<cdot>\<^sub>v ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m j *\<^sub>v tensor_vec b (unit_vec 2 0)))"
    unfolding evo_gate_def nA by (rule ctrl_pow_tensor[OF V]) (simp_all add: uniform_state_def tensor_vec_dim b_dim)
  also have "\<dots> = reg_sum (2 ^ k) (n * 2) (\<lambda>j. (1 / complex_of_real (sqrt (real (2 ^ k)))) \<cdot>\<^sub>v tensor_vec (evolution A t0 ^\<^sub>m j *\<^sub>v b) (unit_vec 2 0))"
  proof (rule reg_sum_cong)
    fix j :: nat assume j: "j < 2 ^ k"
    have "(evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m j *\<^sub>v tensor_vec b (unit_vec 2 0) = tensor_vec (evolution A t0 ^\<^sub>m j *\<^sub>v b) (1\<^sub>m 2 *\<^sub>v unit_vec 2 0)"
      unfolding pow_tensor_one[OF E n0] by (rule tensor_mat_vec_mult[OF pow_carrier_mat[OF E] one_carrier_mat]) (simp_all add: b_dim)
    thus "uniform_state (2 ^ k) $ j \<cdot>\<^sub>v ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m j *\<^sub>v tensor_vec b (unit_vec 2 0))
          = (1 / complex_of_real (sqrt (real (2 ^ k)))) \<cdot>\<^sub>v tensor_vec (evolution A t0 ^\<^sub>m j *\<^sub>v b) (unit_vec 2 0)"
      using j by (simp add: uniform_state_def)
  qed
  finally show ?thesis .
qed

lemma spec_proj_carrier: "spec_proj A t0 (2 ^ k) j \<in> carrier_mat n n"
  unfolding spec_proj_def using A by simp

lemma spec_proj_dim [simp]: "dim_row (spec_proj A t0 (2 ^ k) j) = n" "dim_col (spec_proj A t0 (2 ^ k) j) = n"
  using spec_proj_carrier[of j] by auto

text \<open>Phase estimation: the clock ends in $\sum_j\ket j\otimes\Pi_jb$, with $\Pi_j$ the spectral
projector of $A$ at the grid eigenvalue $\lambda_j$.\<close>

lemma traj_qpe:
  "clock_gate ((fourier (2 ^ k))\<^sup>\<dagger>) n *\<^sub>v (evo_gate A t0 (2 ^ k) *\<^sub>v tensor_vec (uniform_state (2 ^ k)) (tensor_vec b (unit_vec 2 0)))
   = reg_sum (2 ^ k) (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (unit_vec 2 0))"
proof -
  let ?N = "2 ^ k :: nat" and ?u = "uniform_state (2 ^ k)" and ?E = "evolution A t0"
  let ?V = "?E \<Otimes> 1\<^sub>m 2" and ?W = "pe_unitary (2 ^ k) (n * 2) (evolution A t0 \<Otimes> 1\<^sub>m 2)"
  let ?Emb = "lift_mat n ?u (1\<^sub>m n) (0\<^sub>m n n)" and ?L = "blk_lift ?N n (spec_proj A t0 ?N) (\<lambda>_. 0\<^sub>m n n)"
  have N: "0 < ?N" by simp
  have nA: "dim_row A = n" using A(1) by simp
  have du: "dim_vec ?u = ?N" by (simp add: uniform_state_def)
  have Ec: "?E \<in> carrier_mat n n" using A by simp
  have Vc: "?V \<in> carrier_mat (n * 2) (n * 2)" by (rule tensor_carrier[OF Ec one_carrier_mat])
  have Wc: "?W \<in> carrier_mat (?N * (n * 2)) (?N * (n * 2))" by simp
  have Ec': "?Emb \<in> carrier_mat (?N * (n * 2)) n" using lift_mat_carrier[of n ?u] du by simp
  have emb: "?Emb *\<^sub>v v = tensor_vec ?u (tensor_vec v (unit_vec 2 0))" if v: "dim_vec v = n" for v
  proof -
    have vc: "v \<in> carrier_vec n" using v by (rule carrier_vecI)
    have z: "tensor_vec (0\<^sub>m n n *\<^sub>v v) (unit_vec 2 1) = 0\<^sub>v (n * 2)"
      using vc by (intro eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim scalar_prod_left_zero)
    have "?Emb *\<^sub>v v = tensor_vec ?u (tensor_vec (1\<^sub>m n *\<^sub>v v) (unit_vec 2 0) + tensor_vec (0\<^sub>m n n *\<^sub>v v) (unit_vec 2 1))"
      by (rule lift_mat_mult_vec[OF one_carrier_mat zero_carrier_mat v])
    also have "1\<^sub>m n *\<^sub>v v = v" using vc by simp
    also note z
    also have "tensor_vec v (unit_vec 2 0) + 0\<^sub>v (n * 2) = tensor_vec v (unit_vec 2 0)"
      by (rule right_zero_vec[OF carrier_vecI[OF tensor_vec_dim[OF v]]]) simp
    finally show ?thesis .
  qed
  have Lv: "?L *\<^sub>v v = reg_sum ?N (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 ?N j *\<^sub>v v) (unit_vec 2 0))" if v: "dim_vec v = n" for v
  proof -
    have "?L *\<^sub>v v = reg_sum ?N (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 ?N j *\<^sub>v v) (unit_vec 2 0) + tensor_vec (0\<^sub>m n n *\<^sub>v v) (unit_vec 2 1))"
      by (rule blk_lift_mult_vec[OF spec_proj_carrier zero_carrier_mat v])
    also have "\<dots> = reg_sum ?N (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 ?N j *\<^sub>v v) (unit_vec 2 0))"
    proof (rule reg_sum_cong)
      fix j assume "j < ?N"
      have d0: "dim_vec (tensor_vec (spec_proj A t0 ?N j *\<^sub>v v) (unit_vec 2 0)) = n * 2"
        by (rule tensor_vec_dim) (simp_all add: spec_proj_carrier[of j, THEN carrier_matD(1)])
      have z: "tensor_vec (0\<^sub>m n n *\<^sub>v v) (unit_vec 2 1) = 0\<^sub>v (n * 2)"
        using carrier_vecI[OF v] by (intro eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim scalar_prod_left_zero)
      show "tensor_vec (spec_proj A t0 ?N j *\<^sub>v v) (unit_vec 2 0) + tensor_vec (0\<^sub>m n n *\<^sub>v v) (unit_vec 2 1)
            = tensor_vec (spec_proj A t0 ?N j *\<^sub>v v) (unit_vec 2 0)"
        unfolding z by (rule right_zero_vec[OF carrier_vecI[OF d0]])
    qed
    finally show ?thesis .
  qed
  have WE: "?W * ?Emb = ?L"
  proof (rule eigvec_mat_eqI[OF A mult_carrier_mat[OF Wc Ec'] blk_lift_carrier])
    fix v l assume v: "dim_vec v = n" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vc: "v \<in> carrier_vec n" using v by (rule carrier_vecI)
    show "(?W * ?Emb) *\<^sub>v v = ?L *\<^sub>v v"
    proof (cases "v = 0\<^sub>v n")
      case True
      thus ?thesis using mult_zero_vec_right[OF mult_carrier_mat[OF Wc Ec']] mult_zero_vec_right[OF blk_lift_carrier] by simp
    next
      case False
      hence "l \<in> herm_spectrum A" unfolding herm_spectrum_iff nA using v ev by (intro exI[of _ v]) simp
      then obtain j0 where j0: "0 < j0" "j0 < ?N" and l: "l = reg_eig t0 ?N j0" using spec by blast
      have phase: "cis (t0 * reg_eig t0 ?N j0) = cis (2 * pi * (real j0 / real ?N))" by (rule reg_eig_phase[OF t0 N])
      have Vev: "?V *\<^sub>v tensor_vec v (unit_vec 2 0) = cis (2 * pi * (real j0 / real ?N)) \<cdot>\<^sub>v tensor_vec v (unit_vec 2 0)"
      proof -
        have "?V *\<^sub>v tensor_vec v (unit_vec 2 0) = tensor_vec (?E *\<^sub>v v) (1\<^sub>m 2 *\<^sub>v unit_vec 2 0)"
          by (rule tensor_mat_vec_mult[OF Ec one_carrier_mat v]) simp
        also have "?E *\<^sub>v v = cis (t0 * reg_eig t0 ?N j0) \<cdot>\<^sub>v v" using evolution_eigen[OF A v ev] l by simp
        finally show ?thesis unfolding phase using tensor_vec_smult_left[OF v, of "unit_vec 2 0" 2] by simp
      qed
      have "(?W * ?Emb) *\<^sub>v v = ?W *\<^sub>v (?Emb *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF Wc Ec' vc])
      also have "\<dots> = tensor_vec (unit_vec ?N j0) (tensor_vec v (unit_vec 2 0))"
        unfolding emb[OF v] by (rule pe_unitary_exact[OF N j0(2) Vc _ Vev]) (simp add: tensor_vec_dim v)
      also have "\<dots> = ?L *\<^sub>v v"
      proof -
        have P: "spec_proj A t0 ?N j *\<^sub>v v = (if j = j0 then v else 0\<^sub>v n)" if j: "j < ?N" for j
        proof -
          have "spec_proj A t0 ?N j *\<^sub>v v = (if l = reg_eig t0 ?N j then 1 else 0) \<cdot>\<^sub>v v"
            unfolding spec_proj_def by (rule mat_fun_eigen[OF A v ev])
          moreover have e: "l = reg_eig t0 ?N j \<longleftrightarrow> j = j0"
          proof
            assume a: "l = reg_eig t0 ?N j"
            have "reg_eig t0 ?N j = reg_eig t0 ?N j0" using a l by linarith
            thus "j = j0" by (rule reg_eig_inj[OF t0 j j0(2)])
          next
            assume "j = j0"
            thus "l = reg_eig t0 ?N j" using l by simp
          qed
          ultimately show ?thesis
          proof (cases "j = j0")
            case True
            thus ?thesis using \<open>spec_proj A t0 ?N j *\<^sub>v v = (if l = reg_eig t0 ?N j then 1 else 0) \<cdot>\<^sub>v v\<close> e vc by simp
          next
            case False
            hence "spec_proj A t0 ?N j *\<^sub>v v = 0 \<cdot>\<^sub>v v" using \<open>spec_proj A t0 ?N j *\<^sub>v v = (if l = reg_eig t0 ?N j then 1 else 0) \<cdot>\<^sub>v v\<close> e by simp
            also have "0 \<cdot>\<^sub>v v = 0\<^sub>v n" using v by (intro eq_vecI) simp_all
            finally show ?thesis using False by simp
          qed
        qed
        have "tensor_vec (unit_vec ?N j0) (tensor_vec v (unit_vec 2 0))
              = reg_sum ?N (n * 2) (\<lambda>j. unit_vec ?N j0 $ j \<cdot>\<^sub>v tensor_vec v (unit_vec 2 0))"
          by (rule tensor_reg_sum) (simp_all add: tensor_vec_dim v)
        also have "\<dots> = reg_sum ?N (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 ?N j *\<^sub>v v) (unit_vec 2 0))"
        proof (rule reg_sum_cong)
          fix j assume j: "j < ?N"
          show "unit_vec ?N j0 $ j \<cdot>\<^sub>v tensor_vec v (unit_vec 2 0) = tensor_vec (spec_proj A t0 ?N j *\<^sub>v v) (unit_vec 2 0)"
          proof (cases "j = j0")
            case True
            thus ?thesis unfolding P[OF j] using j carrier_vecI[OF tensor_vec_dim[OF v refl]] by simp
          next
            case False
            have "unit_vec ?N j0 $ j \<cdot>\<^sub>v tensor_vec v (unit_vec 2 0) = 0\<^sub>v (n * 2)"
              using False j v by (intro eq_vecI) (simp_all add: tensor_vec_dim unit_vec_def)
            moreover have "tensor_vec (0\<^sub>v n) (unit_vec 2 0) = 0\<^sub>v (n * 2)"
              by (intro eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim)
            ultimately show ?thesis unfolding P[OF j] using False by simp
          qed
        qed
        finally show ?thesis using Lv[OF v] by simp
      qed
      finally show ?thesis .
    qed
  qed
  have bc: "b \<in> carrier_vec n" using b_dim by (rule carrier_vecI)
  have W: "clock_gate ((fourier ?N)\<^sup>\<dagger>) n * evo_gate A t0 ?N = ?W"
    unfolding clock_gate_def evo_gate_def pe_unitary_def nA ..
  have "clock_gate ((fourier ?N)\<^sup>\<dagger>) n *\<^sub>v (evo_gate A t0 ?N *\<^sub>v tensor_vec ?u (tensor_vec b (unit_vec 2 0)))
        = ?W *\<^sub>v tensor_vec ?u (tensor_vec b (unit_vec 2 0))"
    unfolding W[symmetric] by (rule assoc_mult_mat_vec[symmetric]) (auto simp: clock_gate_def evo_gate_def nA tensor_vec_dim b_dim uniform_state_def intro!: carrier_vecI)
  also have "\<dots> = ?W *\<^sub>v (?Emb *\<^sub>v b)" unfolding emb[OF b_dim] ..
  also have "\<dots> = (?W * ?Emb) *\<^sub>v b" by (rule assoc_mult_mat_vec[OF Wc Ec' bc, symmetric])
  also have "\<dots> = reg_sum ?N (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 ?N j *\<^sub>v b) (unit_vec 2 0))" unfolding WE by (rule Lv[OF b_dim])
  finally show ?thesis .
qed

text \<open>The controlled rotation writes $C/\lambda_j$ into the ancilla of branch $j$.\<close>

lemma traj_rotate:
  "rot_gate A t0 (2 ^ k) C *\<^sub>v reg_sum (2 ^ k) (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (unit_vec 2 0))
   = reg_sum (2 ^ k) (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (rot (C / reg_eig t0 (2 ^ k) j) *\<^sub>v unit_vec 2 0))"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have dP: "dim_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) = n" for j using spec_proj_carrier[of j] by simp
  have "rot_gate A t0 (2 ^ k) C *\<^sub>v reg_sum (2 ^ k) (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (unit_vec 2 0))
        = reg_sum (2 ^ k) (n * 2) (\<lambda>j. hhl_rot C t0 (2 ^ k) n j *\<^sub>v tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (unit_vec 2 0))"
    unfolding rot_gate_def nA by (rule ctrl_blocks_reg_sum) (simp_all add: tensor_vec_dim dP)
  also have "\<dots> = reg_sum (2 ^ k) (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (rot (C / reg_eig t0 (2 ^ k) j) *\<^sub>v unit_vec 2 0))"
  proof (rule reg_sum_cong)
    fix j assume "j < (2::nat) ^ k"
    have "hhl_rot C t0 (2 ^ k) n j *\<^sub>v tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (unit_vec 2 0)
          = tensor_vec (1\<^sub>m n *\<^sub>v (spec_proj A t0 (2 ^ k) j *\<^sub>v b)) (rot (C / reg_eig t0 (2 ^ k) j) *\<^sub>v unit_vec 2 0)"
      by (rule tensor_mat_vec_mult[OF one_carrier_mat rot_carrier]) (simp_all add: dP)
    thus "hhl_rot C t0 (2 ^ k) n j *\<^sub>v tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (unit_vec 2 0)
          = tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (rot (C / reg_eig t0 (2 ^ k) j) *\<^sub>v unit_vec 2 0)"
      using carrier_vecI[OF dP[of j]] by simp
  qed
  finally show ?thesis .
qed

lemma evo_gate_carrier: "evo_gate A t0 (2 ^ k) \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
  using A(1) by (simp add: evo_gate_def)

lemma evo_gate_unitary: "unitary (evo_gate A t0 (2 ^ k))"
proof -
  have Ec: "evolution A t0 \<in> carrier_mat n n" using A by simp
  have V: "evolution A t0 \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)" by (rule tensor_carrier[OF Ec one_carrier_mat])
  have Vu: "unitary (evolution A t0 \<Otimes> 1\<^sub>m 2)" by (rule tensor_mat_unitary_one_right) (rule evolution_unitary[OF A])
  show ?thesis unfolding evo_gate_def using A(1)
    by simp (rule ctrl_blocks_unitary, simp_all add: V unitary_pow[OF V Vu])
qed

lemma clock_gate_dagger: "(clock_gate G n)\<^sup>\<dagger> = clock_gate (G\<^sup>\<dagger>) n"
  unfolding clock_gate_def tensor_mat_adjoint by simp

text \<open>Uncomputation.  With $\mathrm{out}=G_0b\otimes\ket0+G_1b\otimes\ket1$ the HHL output
(\<open>hhl\<close>), the Fourier transform leaves $\sum_j\frac1{\sqrt N}\ket j\otimes(e^{iAt_0j}\otimes I)\,\mathrm{out}$,
and the inverse controlled evolution then gives $\frac1{\sqrt N}\sum_j\ket j\otimes\mathrm{out}$.\<close>

lemma traj_uncompute:
  defines "\<psi>5 \<equiv> reg_sum (2 ^ k) (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (rot (C / reg_eig t0 (2 ^ k) j) *\<^sub>v unit_vec 2 0))"
  shows "clock_gate (fourier (2 ^ k)) n *\<^sub>v \<psi>5
         = reg_sum (2 ^ k) (n * 2) (\<lambda>j. (1 / complex_of_real (sqrt (real (2 ^ k)))) \<cdot>\<^sub>v ((evolution A t0 ^\<^sub>m j \<Otimes> 1\<^sub>m 2) *\<^sub>v hhl_out A C b))"
    and "((evo_gate A t0 (2 ^ k))\<^sup>\<dagger>) *\<^sub>v (clock_gate (fourier (2 ^ k)) n *\<^sub>v \<psi>5) = tensor_vec (uniform_state (2 ^ k)) (hhl_out A C b)"
proof -
  let ?N = "2 ^ k :: nat" and ?u = "uniform_state (2 ^ k)"
  let ?F = "clock_gate (fourier ?N) n" and ?Fd = "clock_gate ((fourier ?N)\<^sup>\<dagger>) n" and ?C = "evo_gate A t0 ?N"
  let ?R = "rot_gate A t0 ?N C" and ?x2 = "tensor_vec ?u (tensor_vec b (unit_vec 2 0))"
  have N: "0 < ?N" by simp
  have nA: "dim_row A = n" using A(1) by simp
  have Fc: "?F \<in> carrier_mat (?N * (n * 2)) (?N * (n * 2))" and Fdc: "?Fd \<in> carrier_mat (?N * (n * 2)) (?N * (n * 2))"
    unfolding clock_gate_def by (rule tensor_carrier[OF fourier_carrier one_carrier_mat],
      rule tensor_carrier[OF dagger_carrier[OF fourier_carrier] one_carrier_mat])
  have Cc: "?C \<in> carrier_mat (?N * (n * 2)) (?N * (n * 2))" by (rule evo_gate_carrier)
  have Rc: "?R \<in> carrier_mat (?N * (n * 2)) (?N * (n * 2))" using A(1) by (simp add: rot_gate_def)
  have x2: "?x2 \<in> carrier_vec (?N * (n * 2))" by (rule carrier_vecI) (simp add: tensor_vec_dim uniform_state_def b_dim)
  have W: "hhl_W A t0 ?N = ?Fd * ?C" unfolding hhl_Wd_def pe_unitary_def clock_gate_def evo_gate_def nA ..
  have Wd: "(hhl_W A t0 ?N)\<^sup>\<dagger> = (?C\<^sup>\<dagger>) * ?F"
  proof -
    have "(?Fd * ?C)\<^sup>\<dagger> = (?C\<^sup>\<dagger>) * (?Fd\<^sup>\<dagger>)" by (rule dagger_of_prod) (use Fdc Cc in simp)
    also have "(?Fd\<^sup>\<dagger>) = ?F" unfolding clock_gate_dagger by (simp add: dagger_of_dagger_is_id)
    finally show ?thesis unfolding W .
  qed
  have x4: "?Fd *\<^sub>v (?C *\<^sub>v ?x2) = reg_sum ?N (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 ?N j *\<^sub>v b) (unit_vec 2 0))"
    by (rule traj_qpe)
  have x5: "?R *\<^sub>v (?Fd *\<^sub>v (?C *\<^sub>v ?x2)) = \<psi>5" unfolding x4 \<psi>5_def by (rule traj_rotate)
  have H: "hhl_circuit A t0 ?N C *\<^sub>v ?x2 = tensor_vec ?u (hhl_out A C b)"
    unfolding hhl_out_def by (rule hhl[OF A t0 N spec b_dim])
  have Cu: "unitary ?C" by (rule evo_gate_unitary)
  show b7: "(?C\<^sup>\<dagger>) *\<^sub>v (?F *\<^sub>v \<psi>5) = tensor_vec ?u (hhl_out A C b)"
  proof -
    have p5: "\<psi>5 \<in> carrier_vec (?N * (n * 2))" unfolding \<psi>5_def by (rule carrier_vecI) simp
    have "(?C\<^sup>\<dagger>) *\<^sub>v (?F *\<^sub>v \<psi>5) = ((?C\<^sup>\<dagger>) * ?F) *\<^sub>v \<psi>5" by (rule assoc_mult_mat_vec[symmetric, OF dagger_carrier[OF Cc] Fc p5])
    also have "\<dots> = ((hhl_W A t0 ?N)\<^sup>\<dagger>) *\<^sub>v (?R *\<^sub>v ((?Fd * ?C) *\<^sub>v ?x2))"
      unfolding Wd[symmetric] x5[symmetric] using assoc_mult_mat_vec[OF Fdc Cc x2] by simp
    also have "\<dots> = hhl_circuit A t0 ?N C *\<^sub>v ?x2"
    proof -
      have Wc: "hhl_W A t0 ?N \<in> carrier_mat (?N * (n * 2)) (?N * (n * 2))" unfolding W using Fdc Cc by simp
      have "hhl_circuit A t0 ?N C *\<^sub>v ?x2 = ((hhl_W A t0 ?N)\<^sup>\<dagger>) *\<^sub>v ((?R * hhl_W A t0 ?N) *\<^sub>v ?x2)"
        unfolding flag_circuit_def rot_gate_def[symmetric] nA[symmetric]
        by (rule assoc_mult_mat_vec[OF dagger_carrier[OF Wc]]) (use Rc Wc x2 nA in auto)
      also have "(?R * hhl_W A t0 ?N) *\<^sub>v ?x2 = ?R *\<^sub>v (hhl_W A t0 ?N *\<^sub>v ?x2)" by (rule assoc_mult_mat_vec[OF Rc Wc x2])
      finally show ?thesis unfolding W by simp
    qed
    finally show ?thesis using H by simp
  qed
  show "?F *\<^sub>v \<psi>5 = reg_sum ?N (n * 2) (\<lambda>j. (1 / complex_of_real (sqrt (real ?N))) \<cdot>\<^sub>v ((evolution A t0 ^\<^sub>m j \<Otimes> 1\<^sub>m 2) *\<^sub>v hhl_out A C b))"
  proof -
    have p6: "?F *\<^sub>v \<psi>5 \<in> carrier_vec (?N * (n * 2))" unfolding \<psi>5_def using Fc by (intro carrier_vecI) simp
    have CCd: "?C * (?C\<^sup>\<dagger>) = 1\<^sub>m (?N * (n * 2))" using Cu Cc unfolding unitary_def by simp
    have "?F *\<^sub>v \<psi>5 = (?C * (?C\<^sup>\<dagger>)) *\<^sub>v (?F *\<^sub>v \<psi>5)" unfolding CCd using p6 by simp
    also have "\<dots> = ?C *\<^sub>v ((?C\<^sup>\<dagger>) *\<^sub>v (?F *\<^sub>v \<psi>5))" by (rule assoc_mult_mat_vec[OF Cc dagger_carrier[OF Cc] p6])
    also have "\<dots> = ?C *\<^sub>v tensor_vec ?u (hhl_out A C b)" unfolding b7 ..
    also have "\<dots> = reg_sum ?N (n * 2) (\<lambda>j. ?u $ j \<cdot>\<^sub>v ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m j *\<^sub>v hhl_out A C b))"
    proof -
      have Ec: "evolution A t0 \<in> carrier_mat n n" using A by simp
      have dO: "dim_vec (hhl_out A C b) = n * 2" by (rule hhl_out_dim)
      show ?thesis unfolding evo_gate_def nA
        by (rule ctrl_pow_tensor[OF tensor_carrier[OF Ec one_carrier_mat]]) (simp_all add: uniform_state_def dO)
    qed
    also have "\<dots> = reg_sum ?N (n * 2) (\<lambda>j. (1 / complex_of_real (sqrt (real ?N))) \<cdot>\<^sub>v ((evolution A t0 ^\<^sub>m j \<Otimes> 1\<^sub>m 2) *\<^sub>v hhl_out A C b))"
    proof -
      have Ec2: "evolution A t0 \<in> carrier_mat n n" using A by simp
      show ?thesis by (rule reg_sum_cong) (simp add: uniform_state_def pow_tensor_one[OF Ec2 n0])
    qed
    finally show ?thesis .
  qed
qed

text \<open>The Hadamard layer resets the clock.\<close>

lemma traj_reset:
  assumes w: "dim_vec w = n * 2"
  shows "clock_gate (Hadamard \<otimes>\<^bsup>k\<^esup>) n *\<^sub>v tensor_vec (uniform_state (2 ^ k)) w = tensor_vec (unit_vec (2 ^ k) 0) w"
proof -
  have "clock_gate (Hadamard \<otimes>\<^bsup>k\<^esup>) n *\<^sub>v tensor_vec (uniform_state (2 ^ k)) w
        = tensor_vec ((Hadamard \<otimes>\<^bsup>k\<^esup>) *\<^sub>v uniform_state (2 ^ k)) (1\<^sub>m (n * 2) *\<^sub>v w)"
    unfolding clock_gate_def by (rule tensor_mat_vec_mult[OF hadamard_layer_carrier[OF k] one_carrier_mat]) (simp_all add: w uniform_state_def)
  thus ?thesis using hadamard_layer_uniform[OF k] carrier_vecI[OF w] by simp
qed

text \<open>The whole circuit takes $\ket0\ket0\ket0$ to $\ket0\otimes\mathrm{out}$.\<close>

theorem hhl_run:
  "run_gates (tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (unit_vec n 0) (unit_vec 2 0))) (hhl_gates A Ub t0 k C)
   = tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have w: "dim_vec (tensor_vec b (unit_vec 2 0)) = n * 2" by (simp add: tensor_vec_dim b_dim)
  show ?thesis
    unfolding hhl_gates_def nA run_gates.simps traj_prep traj_hadamard[OF w] traj_qpe[unfolded nA] traj_rotate
              traj_uncompute(2) traj_reset[OF hhl_out_dim] ..
qed

lemma hhl_gates_unitary:
  assumes Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
  shows "U \<in> set (hhl_gates A Ub t0 k C) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> unitary U"
proof -
  assume U: "U \<in> set (hhl_gates A Ub t0 k C)"
  have nA: "dim_row A = n" using A(1) by simp
  have N: "0 < (2::nat) ^ k" by simp
  have H: "Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m (n * 2) \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
    by (rule tensor_carrier[OF hadamard_layer_carrier[OF k] one_carrier_mat])
  have Hu: "unitary (Hadamard \<otimes>\<^bsup>k\<^esup> \<Otimes> 1\<^sub>m (n * 2))" by (rule tensor_mat_unitary_one_right[OF hadamard_layer_unitary[OF k]])
  have P: "prep_gate (2 ^ k) Ub \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
    unfolding prep_gate_def by (rule tensor_carrier[OF one_carrier_mat tensor_carrier[OF Ub(1) one_carrier_mat]])
  have Pu: "unitary (prep_gate (2 ^ k) Ub)"
    unfolding prep_gate_def by (rule tensor_mat_unitary[OF id_is_unitary tensor_mat_unitary_one_right[OF Ub(2)]])
  have F: "fourier (2 ^ k) \<Otimes> 1\<^sub>m (n * 2) \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
    by (rule tensor_carrier[OF fourier_carrier one_carrier_mat])
  have Fu: "unitary (fourier (2 ^ k) \<Otimes> 1\<^sub>m (n * 2))" by (rule tensor_mat_unitary_one_right[OF fourier_unitary[OF N]])
  have Fd: "(fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2) \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
    by (rule tensor_carrier[OF dagger_carrier[OF fourier_carrier] one_carrier_mat])
  have Fdu: "unitary ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2))"
    by (rule tensor_mat_unitary_one_right[OF unitary_dagger[OF fourier_unitary[OF N]]])
  have R: "rot_gate A t0 (2 ^ k) C \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))" using A(1) by (simp add: rot_gate_def)
  have Ru: "unitary (rot_gate A t0 (2 ^ k) C)"
    unfolding rot_gate_def nA
    by (rule ctrl_blocks_unitary) (auto intro: tensor_carrier tensor_mat_unitary id_is_unitary rot_unitary Cb)
  have E: "evo_gate A t0 (2 ^ k) \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))" by (rule evo_gate_carrier)
  show ?thesis using U H Hu P Pu F Fu Fd Fdu R Ru E evo_gate_unitary dagger_carrier[OF E] unitary_dagger[OF evo_gate_unitary]
    unfolding hhl_gates_def nA clock_gate_def by auto
qed

lemma hhl_out_norm:
  assumes Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
  shows "\<parallel>hhl_out A C b\<parallel> = 1"
proof -
  have e: "\<parallel>unit_vec m 0\<parallel> = 1" if "0 < m" for m :: nat
    using that by (simp add: cpx_vec_length_def lessThan_atLeast0 sum.atLeast_Suc_lessThan unit_vec_def)
  let ?\<psi>0 = "tensor_vec (unit_vec (2 ^ k) 0) (tensor_vec (unit_vec n 0) (unit_vec 2 0))"
  have d0: "dim_vec ?\<psi>0 = 2 ^ k * (n * 2)" by (simp add: tensor_vec_dim)
  have "\<parallel>?\<psi>0\<parallel> = 1" using e[of "2 ^ k"] e[OF n0] e[of 2]
    by (simp add: vnorm_tensor tensor_vec_dim)
  moreover have "\<parallel>run_gates ?\<psi>0 (hhl_gates A Ub t0 k C)\<parallel> = \<parallel>?\<psi>0\<parallel>"
    by (rule run_gates_norm[OF hhl_gates_unitary[OF Cb] d0])
  moreover have "\<parallel>tensor_vec (unit_vec (2 ^ k) 0) (hhl_out A C b)\<parallel> = \<parallel>hhl_out A C b\<parallel>"
    using e[of "2 ^ k"] by (simp add: vnorm_tensor hhl_out_dim)
  ultimately show ?thesis unfolding hhl_run by simp
qed

text \<open>The two ancilla branches: $\norm{G_0b}^2+C^2\norm{A^{-1}b}^2=1$; the second term is the
success probability.\<close>

lemma hhl_out_branches:
  assumes Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
  shows "\<parallel>mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b\<parallel>\<^sup>2 + C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2 = 1"
proof -
  let ?g0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b" and ?x = "herm_inv A *\<^sub>v b"
  have Hc: "herm_inv A \<in> carrier_mat n n" unfolding herm_inv_def by (rule mat_fun_carrier[OF A])
  have Gc: "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A \<in> carrier_mat n n" by (rule mat_fun_carrier[OF A])
  have dg: "dim_vec ?g0 = n" and dx: "dim_vec ?x = n" using Hc Gc b_dim by simp_all
  have g1: "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b = complex_of_real C \<cdot>\<^sub>v ?x"
    by (rule smult_mat_mult_vec[OF Hc carrier_vecI[OF b_dim]])
  have o: "\<langle>tensor_vec ?g0 (unit_vec 2 0)|tensor_vec (complex_of_real C \<cdot>\<^sub>v ?x) (unit_vec 2 1)\<rangle> = 0"
  proof -
    have z: "\<langle>unit_vec 2 0|unit_vec 2 1\<rangle> = 0" by (simp add: Quantum.inner_prod_def unit_vec_def numeral_2_eq_2 atLeast0LessThan lessThan_Suc)
    show ?thesis using tensor_inner_prod[of ?g0 n "complex_of_real C \<cdot>\<^sub>v ?x" "unit_vec 2 0" 2 "unit_vec 2 1"] dg dx z by simp
  qed
  have "1 = \<parallel>hhl_out A C b\<parallel>\<^sup>2" using hhl_out_norm[OF Cb] by simp
  also have "\<dots> = \<parallel>tensor_vec ?g0 (unit_vec 2 0)\<parallel>\<^sup>2 + \<parallel>tensor_vec (complex_of_real C \<cdot>\<^sub>v ?x) (unit_vec 2 1)\<parallel>\<^sup>2"
    unfolding hhl_out_def g1 by (rule vnorm_pythagoras[OF _ _ o]) (use Hc Gc b_dim in \<open>simp_all add: tensor_vec_dim\<close>)
  also have "\<dots> = \<parallel>?g0\<parallel>\<^sup>2 + C\<^sup>2 * \<parallel>?x\<parallel>\<^sup>2"
  proof -
    have e: "\<parallel>unit_vec 2 i\<parallel> = 1" if "i < 2" for i
      using that by (auto simp: cpx_vec_length_def numeral_2_eq_2 lessThan_Suc unit_vec_def)
    show ?thesis using e[of 0] e[of 1] dg dx by (simp add: vnorm_tensor cpx_vec_length_smult power_mult_distrib)
  qed
  finally show ?thesis by simp
qed

text \<open>Gate $i$ maps state $i$ to state $i+1$.\<close>

theorem hhl_steps:
  assumes i: "i < 8"
  shows "hhl_gates A Ub t0 k C ! i *\<^sub>v hhl_states A b t0 k C ! i = hhl_states A b t0 k C ! Suc i"
proof -
  have nA: "dim_row A = n" using A(1) by simp
  have w: "dim_vec (tensor_vec b (unit_vec 2 0)) = n * 2" by (simp add: tensor_vec_dim b_dim)
  have s3: "clock_gate ((fourier (2 ^ k))\<^sup>\<dagger>) n *\<^sub>v reg_sum (2 ^ k) (n * 2) (\<lambda>j. (1 / complex_of_real (sqrt (real (2 ^ k)))) \<cdot>\<^sub>v tensor_vec (evolution A t0 ^\<^sub>m j *\<^sub>v b) (unit_vec 2 0))
            = reg_sum (2 ^ k) (n * 2) (\<lambda>j. tensor_vec (spec_proj A t0 (2 ^ k) j *\<^sub>v b) (unit_vec 2 0))"
    using traj_qpe unfolding traj_evolve .
  have s6: "(evo_gate A t0 (2 ^ k))\<^sup>\<dagger> *\<^sub>v reg_sum (2 ^ k) (n * 2) (\<lambda>j. (1 / complex_of_real (sqrt (real (2 ^ k)))) \<cdot>\<^sub>v ((evolution A t0 ^\<^sub>m j \<Otimes> 1\<^sub>m 2) *\<^sub>v hhl_out A C b))
            = tensor_vec (uniform_state (2 ^ k)) (hhl_out A C b)"
    using traj_uncompute(2) unfolding traj_uncompute(1) .
  have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i = 6 \<or> i = 7" using i by linarith
  thus ?thesis
    by (elim disjE) (simp_all add: hhl_gates_def hhl_states_def Let_def nA traj_prep traj_hadamard[OF w]
        traj_evolve s3[simplified] traj_rotate traj_uncompute(1) s6[simplified] traj_reset[OF hhl_out_dim])
qed

end

end
