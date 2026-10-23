theory Day09_Bell_Measurement
  imports Quantum_Computing_by_VP_3_10.Day09_POVMs_Entanglement
begin

section \<open>Day 9: measuring one half of a Bell pair\<close>

definition e0 :: "complex Matrix.vec" where "e0 = unit_vec 2 0"
definition e1 :: "complex Matrix.vec" where "e1 = unit_vec 2 1"
definition proj0 :: "complex Matrix.mat" where "proj0 = e0 \<oslash> e0"
definition proj1 :: "complex Matrix.mat" where "proj1 = e1 \<oslash> e1"

lemma e_dims [simp]: "dim_vec e0 = 2" "dim_vec e1 = 2"
  by (simp_all add: e0_def e1_def)

lemma e_inner [simp]: "\<langle>e0|e0\<rangle> = 1" "\<langle>e0|e1\<rangle> = 0" "\<langle>e1|e0\<rangle> = 0" "\<langle>e1|e1\<rangle> = 1"
  by (simp_all add: e0_def e1_def inner_prod_def unit_vec_def)

lemma proj_carrier [simp]: "proj0 \<in> carrier_mat 2 2" "proj1 \<in> carrier_mat 2 2"
  by (simp_all add: proj0_def proj1_def ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def carrier_matI)

lemma proj_apply [simp]:
  "proj0 *\<^sub>v e0 = e0" "proj0 *\<^sub>v e1 = 0\<^sub>v 2" "proj1 *\<^sub>v e0 = 0\<^sub>v 2" "proj1 *\<^sub>v e1 = e1"
proof -
  have z: "(0::complex) \<cdot>\<^sub>v e0 = 0\<^sub>v 2" "(0::complex) \<cdot>\<^sub>v e1 = 0\<^sub>v 2" by (auto intro!: eq_vecI)
  show "proj0 *\<^sub>v e0 = e0" "proj0 *\<^sub>v e1 = 0\<^sub>v 2" "proj1 *\<^sub>v e0 = 0\<^sub>v 2" "proj1 *\<^sub>v e1 = e1"
    by (simp_all add: proj0_def proj1_def outer_prod_mult_vec z)
qed

lemma bell_state_e: "bell_state = (1 / csqrt 2) \<cdot>\<^sub>v (tensor_vec e0 e0 + tensor_vec e1 e1)"
  unfolding bell_state_def e0_def e1_def ..

lemma tensor_zero_left: "dim_vec w = 2 \<Longrightarrow> tensor_vec (0\<^sub>v 2) w = 0\<^sub>v 4"
  by (rule eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim)

lemma tensor_zero_right: "dim_vec v = 2 \<Longrightarrow> tensor_vec v (0\<^sub>v 2) = 0\<^sub>v 4"
  by (rule eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim)

text \<open>Measuring the first qubit of $\beta=\tfrac1{\sqrt2}(\ket{00}+\ket{11})$ with
$P_0=\ketbra00$, $P_1=\ketbra11$:
\[ (P_0\otimes I)\beta=\tfrac1{\sqrt2}\ket{00},\qquad (P_1\otimes I)\beta=\tfrac1{\sqrt2}\ket{11}, \]
so each outcome has probability $\tfrac12$ and leaves the second qubit in the same basis
state as the first.\<close>

lemma A_meas_bell:
  "(proj0 \<Otimes> 1\<^sub>m 2) *\<^sub>v bell_state = (1 / csqrt 2) \<cdot>\<^sub>v tensor_vec e0 e0"
  "(proj1 \<Otimes> 1\<^sub>m 2) *\<^sub>v bell_state = (1 / csqrt 2) \<cdot>\<^sub>v tensor_vec e1 e1"
proof -
  have c: "\<And>P. P \<in> carrier_mat 2 2 \<Longrightarrow> P \<Otimes> 1\<^sub>m 2 \<in> carrier_mat 4 4" by auto
  have t: "\<And>a b. dim_vec a = 2 \<Longrightarrow> dim_vec b = 2 \<Longrightarrow> tensor_vec a b \<in> carrier_vec 4"
    by (auto intro: carrier_vecI simp: tensor_vec_dim)
  have m: "\<And>P a b. P \<in> carrier_mat 2 2 \<Longrightarrow> dim_vec a = 2 \<Longrightarrow> dim_vec b = 2 \<Longrightarrow>
              (P \<Otimes> 1\<^sub>m 2) *\<^sub>v tensor_vec a b = tensor_vec (P *\<^sub>v a) b"
    by (rule tensor_mat_vec_mult_right_id) auto
  have one: "\<And>v :: complex Matrix.vec. v \<in> carrier_vec 4 \<Longrightarrow> 0\<^sub>v 4 + v = v" "\<And>v :: complex Matrix.vec. v \<in> carrier_vec 4 \<Longrightarrow> v + 0\<^sub>v 4 = v"
    by auto
  show "(proj0 \<Otimes> 1\<^sub>m 2) *\<^sub>v bell_state = (1 / csqrt 2) \<cdot>\<^sub>v tensor_vec e0 e0"
    unfolding bell_state_e
    using mult_mat_vec[OF c[OF proj_carrier(1)] add_carrier_vec[OF t t]]
      mult_add_distrib_mat_vec[OF c[OF proj_carrier(1)] t t]
    by (simp add: m tensor_zero_left one t)
  show "(proj1 \<Otimes> 1\<^sub>m 2) *\<^sub>v bell_state = (1 / csqrt 2) \<cdot>\<^sub>v tensor_vec e1 e1"
    unfolding bell_state_e
    using mult_mat_vec[OF c[OF proj_carrier(2)] add_carrier_vec[OF t t]]
      mult_add_distrib_mat_vec[OF c[OF proj_carrier(2)] t t]
    by (simp add: m tensor_zero_left one t)
qed

lemma tensor_e_norm: "\<parallel>tensor_vec e0 e0\<parallel> = 1" "\<parallel>tensor_vec e1 e1\<parallel> = 1"
proof -
  have n1: "\<And>v. \<langle>v|v\<rangle> = 1 \<Longrightarrow> \<parallel>v\<parallel> = 1"
  proof -
    fix v assume "\<langle>v|v\<rangle> = 1"
    hence "complex_of_real (\<parallel>v\<parallel>\<^sup>2) = 1" using cpx_vec_length_inner_prod[of v] by simp
    hence "\<parallel>v\<parallel>\<^sup>2 = 1" by (metis of_real_eq_1_iff)
    moreover have "\<parallel>v\<parallel> \<ge> 0" unfolding cpx_vec_length_def by (simp add: sum_nonneg)
    ultimately show "\<parallel>v\<parallel> = 1" by (smt (verit) power2_eq_1_iff)
  qed
  have t: "\<And>a. dim_vec a = 2 \<Longrightarrow> \<langle>a|a\<rangle> = 1 \<Longrightarrow> \<langle>tensor_vec a a|tensor_vec a a\<rangle> = 1"
  proof -
    fix a :: "complex Matrix.vec" assume d: "dim_vec a = 2" and a: "\<langle>a|a\<rangle> = 1"
    have "\<langle>tensor_vec a a|tensor_vec a a\<rangle> = \<langle>a|a\<rangle> * \<langle>a|a\<rangle>" by (rule tensor_inner_prod[OF d d d d])
    thus "\<langle>tensor_vec a a|tensor_vec a a\<rangle> = 1" unfolding a by simp
  qed
  show "\<parallel>tensor_vec e0 e0\<parallel> = 1" "\<parallel>tensor_vec e1 e1\<parallel> = 1"
    by (rule n1, rule t, simp_all)+
qed

text \<open>D9-6: A measures $\ketbra00,\ketbra11$ on the shared state $\gamma$: each outcome has
probability $\tfrac12$, and $\gamma$ collapses to $e_0\otimes e_0$ resp.\ $e_1\otimes e_1$, after
which B's measurement $I\otimes M_m$ gives A's outcome with probability $1$.\<close>

theorem bell_measurement:
  "meas_prob (proj0 \<Otimes> 1\<^sub>m 2) bell_state = 1/2"
  "meas_prob (proj1 \<Otimes> 1\<^sub>m 2) bell_state = 1/2"
  "post_meas_state (proj0 \<Otimes> 1\<^sub>m 2) bell_state = tensor_vec e0 e0"
  "post_meas_state (proj1 \<Otimes> 1\<^sub>m 2) bell_state = tensor_vec e1 e1"
  "meas_prob (1\<^sub>m 2 \<Otimes> proj0) (tensor_vec e0 e0) = 1"
  "meas_prob (1\<^sub>m 2 \<Otimes> proj1) (tensor_vec e1 e1) = 1"
proof -
  have s: "cmod (1 / csqrt 2) = 1 / sqrt 2" "cmod (1 / complex_of_real (sqrt 2)) = 1 / sqrt 2"
    by (simp_all add: norm_divide)
  show "meas_prob (proj0 \<Otimes> 1\<^sub>m 2) bell_state = 1/2" "meas_prob (proj1 \<Otimes> 1\<^sub>m 2) bell_state = 1/2"
    unfolding meas_prob_def A_meas_bell by (simp_all add: cpx_vec_length_smult tensor_e_norm s power_divide)
  have r: "1 / complex_of_real (1 / sqrt 2) * (1 / csqrt 2) = 1"
          "1 / complex_of_real (1 / sqrt 2) * (1 / complex_of_real (sqrt 2)) = 1"
    by (simp_all add: field_simps)
  show "post_meas_state (proj0 \<Otimes> 1\<^sub>m 2) bell_state = tensor_vec e0 e0"
       "post_meas_state (proj1 \<Otimes> 1\<^sub>m 2) bell_state = tensor_vec e1 e1"
    unfolding post_meas_state_def A_meas_bell by (simp_all add: cpx_vec_length_smult tensor_e_norm s r smult_smult_assoc)
  have m: "\<And>P a b. P \<in> carrier_mat 2 2 \<Longrightarrow> dim_vec a = 2 \<Longrightarrow> dim_vec b = 2 \<Longrightarrow>
              (1\<^sub>m 2 \<Otimes> P) *\<^sub>v tensor_vec a b = tensor_vec a (P *\<^sub>v b)"
  proof -
    fix P :: "complex Matrix.mat" and a b :: "complex Matrix.vec" assume P: "P \<in> carrier_mat 2 2" and a: "dim_vec a = 2" and b: "dim_vec b = 2"
    have ac: "a \<in> carrier_vec 2" by (rule carrier_vecI[OF a])
    show "(1\<^sub>m 2 \<Otimes> P) *\<^sub>v tensor_vec a b = tensor_vec a (P *\<^sub>v b)"
      using tensor_mat_vec_mult[OF one_carrier_mat P a b] ac by simp
  qed
  show "meas_prob (1\<^sub>m 2 \<Otimes> proj0) (tensor_vec e0 e0) = 1" "meas_prob (1\<^sub>m 2 \<Otimes> proj1) (tensor_vec e1 e1) = 1"
    unfolding meas_prob_def by (simp_all add: m tensor_e_norm)
qed

lemma proj_explicit:
  "proj0 = Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then 1 else 0)"
  "proj1 = Matrix.mat 2 2 (\<lambda>(i,j). if i = 1 \<and> j = 1 then 1 else 0)"
  by (auto intro!: eq_matI simp: proj0_def proj1_def outer_prod_index e0_def e1_def
      ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def)

lemma proj_measurement_system: "measurement_system 2 [proj0, proj1]"
  unfolding measurement_system_def proj_explicit
  by (auto intro!: eq_matI simp: dagger_def scalar_prod_def less_2_cases_iff numeral_2_eq_2 lessThan_Suc)

end
