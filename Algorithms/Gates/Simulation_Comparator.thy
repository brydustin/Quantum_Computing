theory Simulation_Comparator
  imports Clean_Ancillas
begin

section \<open>The sparse simulation with a compiled comparator\<close>

text \<open>Registers of $m$ qubits ($n = 2^m$) on $4m+6$ wires: the comparator becomes its elementary
gates, every other gate is a query acting on the data wires only.\<close>

definition sgate_gates :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> sgate \<Rightarrow> complex Matrix.mat list" where
  "sgate_gates m d A Os g = (if g = Cmp then compile (4 * m + 6) (sort_flag m)
     else [1\<^sub>m (2 ^ (2 * m + 5)) \<Otimes> sgate_mat (2 ^ m) d A Os g])"

definition sim_compiled :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> sgate list \<Rightarrow> complex Matrix.mat list" where
  "sim_compiled m d A Os sl = concat (map (sgate_gates m d A Os) sl)"

lemma sgate_gates_stands_for:
  assumes g: "gate_ok K g" and Os: "\<And>c. c < K \<Longrightarrow> Os c \<in> carrier_mat (2 ^ m * 2 ^ m * 2) (2 ^ m * 2 ^ m * 2)"
  shows "stands_for (2 ^ (2 * m + 5)) (2 ^ m * 2 ^ m * 2) (circuit_mat (2 ^ (4 * m + 6)) (sgate_gates m d A Os g))
     (sgate_mat (2 ^ m) d A Os g)"
proof (cases "g = Cmp")
  case True
  thus ?thesis using cmp_compiled_stands_for by (simp add: sgate_gates_def)
next
  case False
  have G: "sgate_mat (2 ^ m) d A Os g \<in> carrier_mat (2 ^ m * 2 ^ m * 2) (2 ^ m * 2 ^ m * 2)"
    by (rule sgate_carrier[where K = K]) (use Os g in auto)
  have c: "1\<^sub>m (2 ^ (2 * m + 5)) \<Otimes> sgate_mat (2 ^ m) d A Os g \<in> carrier_mat (2 ^ (4 * m + 6)) (2 ^ (4 * m + 6))"
    unfolding anc_size using G by simp
  have "circuit_mat (2 ^ (4 * m + 6)) (sgate_gates m d A Os g) = 1\<^sub>m (2 ^ (2 * m + 5)) \<Otimes> sgate_mat (2 ^ m) d A Os g"
    using False left_mult_one_mat[OF c] by (simp add: sgate_gates_def)
  thus ?thesis using stands_for_lift[OF G] by simp
qed

theorem sim_compiled_stands_for:
  assumes sl: "\<And>g. g \<in> set sl \<Longrightarrow> gate_ok K g"
    and Os: "\<And>c. c < K \<Longrightarrow> Os c \<in> carrier_mat (2 ^ m * 2 ^ m * 2) (2 ^ m * 2 ^ m * 2)"
  shows "stands_for (2 ^ (2 * m + 5)) (2 ^ m * 2 ^ m * 2) (circuit_mat (2 ^ (4 * m + 6)) (sim_compiled m d A Os sl))
     (sg_run (2 ^ m) d A Os sl)"
proof -
  let ?B = "map (sgate_gates m d A Os) sl"
  have car: "U \<in> carrier_mat (2 ^ (4 * m + 6)) (2 ^ (4 * m + 6))" if us: "Us \<in> set ?B" and u: "U \<in> set Us" for Us U
  proof -
    obtain g where g: "g \<in> set sl" and Us: "Us = sgate_gates m d A Os g" using us unfolding set_map by blast
    show ?thesis
    proof (cases "g = Cmp")
      case True
      hence "elementary (2 ^ (4 * m + 6)) U"
        using u Us sort_flag_gates(1)[of m] by (simp add: sgate_gates_def)
      thus ?thesis by (rule elementary_carrier)
    next
      case False
      have "sgate_mat (2 ^ m) d A Os g \<in> carrier_mat (2 ^ m * 2 ^ m * 2) (2 ^ m * 2 ^ m * 2)"
        by (rule sgate_carrier[where K = K]) (use Os sl g in auto)
      thus ?thesis using u Us False unfolding anc_size by (simp add: sgate_gates_def)
    qed
  qed
  have "circuit_mat (2 ^ (4 * m + 6)) (sim_compiled m d A Os sl) = circuit_mat (2 ^ (4 * m + 6)) (map (circuit_mat (2 ^ (4 * m + 6))) ?B)"
    unfolding sim_compiled_def by (rule circuit_mat_concat) (use car in blast)
  moreover have "list_all2 (stands_for (2 ^ (2 * m + 5)) (2 ^ m * 2 ^ m * 2)) (map (circuit_mat (2 ^ (4 * m + 6))) ?B)
      (map (sgate_mat (2 ^ m) d A Os) sl)"
    using sl by (auto simp: list_all2_map1 list_all2_map2 list_all2_same intro!: sgate_gates_stands_for[OF _ Os])
  ultimately show ?thesis using stands_for_circuit[where A = "2 ^ (2 * m + 5)" and N = "2 ^ m * 2 ^ m * 2"]
    unfolding anc_size by simp
qed


subsection \<open>Counting the gates\<close>

lemma length_sim_compiled:
  "length (sim_compiled m d A Os sl) = length (filter is_query sl)
     + length (filter (\<lambda>g. \<not> is_query g) sl) * length (compile (4 * m + 6) (sort_flag m))"
proof (induction sl)
  case (Cons g sl)
  thus ?case by (cases g) (simp_all add: sim_compiled_def sgate_gates_def)
qed (simp add: sim_compiled_def)

lemma sim_gates_cmps: "length (filter (\<lambda>g. \<not> is_query g) (sim_gates K r)) = r * (2 * K)"
  using sum_length_filter_compl[of is_query "sim_gates K r"] sim_gates_length[of K r] sim_gates_queries[of K r]
  by (simp add: algebra_simps)

lemma sim_compiled_kinds:
  "U \<in> set (sim_compiled m d A Os sl) \<Longrightarrow>
     elementary (2 ^ (4 * m + 6)) U \<or> (\<exists>g \<in> set sl. is_query g \<and> U = 1\<^sub>m (2 ^ (2 * m + 5)) \<Otimes> sgate_mat (2 ^ m) d A Os g)"
proof -
  assume "U \<in> set (sim_compiled m d A Os sl)"
  then obtain g where g: "g \<in> set sl" and u: "U \<in> set (sgate_gates m d A Os g)" by (auto simp: sim_compiled_def)
  show ?thesis
  proof (cases "g = Cmp")
    case True
    thus ?thesis using u sort_flag_gates(1)[of m] by (simp add: sgate_gates_def)
  next
    case False
    hence "is_query g" by (cases g) simp_all
    thus ?thesis using u g False by (auto simp: sgate_gates_def)
  qed
qed

subsection \<open>The simulation in elementary gates and queries\<close>

text \<open>For an $s$-sparse Hermitian $A$ on $m$ qubits: started with the $2m+5$ workspace wires clear
and in $\ket x\ket0\ket0$, the compiled circuit acts as the simulated evolution $V$, which is
$8(sLt)^2/r$-close to $e^{itA}$.  It makes $r(6s-2)$ queries; every other gate is elementary,
at most $2r(2s-1)(107m+33)(24m+43)$ of them.\<close>

theorem sparse_simulation_compiled:
  fixes m s r :: nat and t :: real and A :: "complex Matrix.mat" and Os :: "nat \<Rightarrow> complex Matrix.mat"
  defines "n \<equiv> 2 ^ m" and "In0 \<equiv> anc (2 ^ (2 * m + 5)) (2 ^ m * 2 ^ m * 2) * emb (2 ^ m)"
    and "C \<equiv> sim_compiled m (t / real r) A Os (sim_gates (2 * s - 1) r)"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and s: "1 \<le> s"
      and L: "0 \<le> L" and Lb: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (A $$ (i, j)) \<le> L"
      and cov: "edge_cover n (2 * s - 1) p (edges n A)"
      and Os: "\<And>c. c < 2 * s - 1 \<Longrightarrow> colour_oracle n (p c) (Os c)" and r: "0 < r"
  shows "circuit_mat (2 ^ (4 * m + 6)) C * In0 = In0 * sim_mat n (t / real r) A (2 * s - 1) p r"
    and "sim_mat n (t / real r) A (2 * s - 1) p r \<approx>\<^bsub>8 * (real s * L * t)\<^sup>2 / real r\<^esub> evolution A t"
    and "U \<in> set C \<Longrightarrow> elementary (2 ^ (4 * m + 6)) U \<or>
           (\<exists>g \<in> set (sim_gates (2 * s - 1) r). is_query g \<and> U = 1\<^sub>m (2 ^ (2 * m + 5)) \<Otimes> sgate_mat n (t / real r) A Os g)"
    and "length (filter is_query (sim_gates (2 * s - 1) r)) = r * (6 * s - 2)"
    and "length C \<le> r * (6 * s - 2) + r * (2 * (2 * s - 1)) * ((107 * m + 33) * (24 * m + 43))"
proof -
  note S = sparse_simulation_circuit[OF A[unfolded n_def] s L Lb[unfolded n_def] cov[unfolded n_def] Os[unfolded n_def] r]
  have Oc: "\<And>c. c < 2 * s - 1 \<Longrightarrow> Os c \<in> carrier_mat (2 ^ m * 2 ^ m * 2) (2 ^ m * 2 ^ m * 2)"
    using Os unfolding colour_oracle_def n_def by blast
  have sf: "stands_for (2 ^ (2 * m + 5)) (2 ^ m * 2 ^ m * 2) (circuit_mat (2 ^ (4 * m + 6)) C)
      (sg_run (2 ^ m) (t / real r) A Os (sim_gates (2 * s - 1) r))"
    unfolding C_def by (rule sim_compiled_stands_for[OF sim_gates_ok Oc])
  let ?P = "circuit_mat (2 ^ (4 * m + 6)) C" and ?R = "sg_run (2 ^ m) (t / real r) A Os (sim_gates (2 * s - 1) r)"
    and ?a = "anc (2 ^ (2 * m + 5)) (2 ^ m * 2 ^ m * 2)" and ?V = "sim_mat (2 ^ m) (t / real r) A (2 * s - 1) p r"
  have P: "?P \<in> carrier_mat (2 ^ (2 * m + 5) * (2 ^ m * 2 ^ m * 2)) (2 ^ (2 * m + 5) * (2 ^ m * 2 ^ m * 2))"
    and R: "?R \<in> carrier_mat (2 ^ m * 2 ^ m * 2) (2 ^ m * 2 ^ m * 2)" and Pa: "?P * ?a = ?a * ?R"
    using sf by (simp_all add: stands_for_def)
  have V: "?V \<in> carrier_mat (2 ^ m) (2 ^ m)" using S(2) by (simp add: n_def)
  have "?P * (?a * emb (2 ^ m)) = (?P * ?a) * emb (2 ^ m)" by (rule assoc_mult_mat[OF P anc_carrier emb_carrier, symmetric])
  also have "\<dots> = ?a * (?R * emb (2 ^ m))" unfolding Pa by (rule assoc_mult_mat[OF anc_carrier R emb_carrier])
  also have "?R * emb (2 ^ m) = emb (2 ^ m) * ?V" using S(1) by (simp add: n_def)
  also have "?a * (emb (2 ^ m) * ?V) = (?a * emb (2 ^ m)) * ?V" by (rule assoc_mult_mat[OF anc_carrier emb_carrier V, symmetric])
  finally show "circuit_mat (2 ^ (4 * m + 6)) C * In0 = In0 * sim_mat n (t / real r) A (2 * s - 1) p r"
    by (simp add: In0_def n_def)
  show "sim_mat n (t / real r) A (2 * s - 1) p r \<approx>\<^bsub>8 * (real s * L * t)\<^sup>2 / real r\<^esub> evolution A t" using S(4) by (simp add: n_def)
  show "U \<in> set C \<Longrightarrow> elementary (2 ^ (4 * m + 6)) U \<or>
      (\<exists>g \<in> set (sim_gates (2 * s - 1) r). is_query g \<and> U = 1\<^sub>m (2 ^ (2 * m + 5)) \<Otimes> sgate_mat n (t / real r) A Os g)"
    unfolding C_def n_def by (rule sim_compiled_kinds)
  show q: "length (filter is_query (sim_gates (2 * s - 1) r)) = r * (6 * s - 2)" by (rule S(5))
  show "length C \<le> r * (6 * s - 2) + r * (2 * (2 * s - 1)) * ((107 * m + 33) * (24 * m + 43))"
    unfolding C_def length_sim_compiled q sim_gates_cmps using sort_flag_gates(2)[of m] by simp
qed

end
