theory Distant_Diagonals
  imports Entry_Oracle
begin

section \<open>Two-qubit diagonal gates on distant wires\<close>

text \<open>\<open>dgate K c \<psi>\<close> multiplies $\ket z$ by $e^{i\psi(z_c, z_0)}$.  Swapping wire $c$ down to wire 1 turns
it into a diagonal gate on the two lowest wires; swapping back undoes the move.\<close>

definition dgate :: "nat \<Rightarrow> nat \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> real) \<Rightarrow> complex Matrix.mat" where
  "dgate K c \<psi> = dmat (2 ^ K) (\<lambda>z. \<psi> (bit z c) (bit z 0))"

definition dgate_gates :: "nat \<Rightarrow> nat \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list" where
  "dgate_gates K c \<psi> = map (cgate K 1) (swops (dn c 1)) @ [1\<^sub>m (2 ^ (K - 2)) \<Otimes> dmat 4 (\<lambda>d. \<psi> (bit d 1) (bit d 0))]
     @ map (cgate K 1) (swops (rev (dn c 1)))"

lemma dmat_unit: "t < N \<Longrightarrow> dmat N \<psi> *\<^sub>v unit_vec N t = cis (\<psi> t) \<cdot>\<^sub>v unit_vec N t"
  by (rule eq_vecI) (auto simp: dmat_mult_vec unit_vec_def)

lemma pmat_dmat_conj:
  assumes f: "\<And>t. t < N \<Longrightarrow> f t < N" and h: "\<And>t. t < N \<Longrightarrow> h t < N" and hf: "\<And>t. t < N \<Longrightarrow> h (f t) = t"
  shows "pmat N h * dmat N \<psi> * pmat N f = dmat N (\<lambda>t. \<psi> (f t))"
proof (rule mat_eq_unit)
  show "pmat N h * dmat N \<psi> * pmat N f \<in> carrier_mat N N"
    by (rule mult_carrier_mat[OF mult_carrier_mat[OF pmat_carrier dmat_carrier] pmat_carrier])
  show "dmat N (\<lambda>t. \<psi> (f t)) \<in> carrier_mat N N" by (rule dmat_carrier)
  fix t assume t: "t < N"
  have u: "unit_vec N t \<in> carrier_vec N" "unit_vec N (f t) \<in> carrier_vec N" by simp_all
  have "pmat N h * dmat N \<psi> * pmat N f *\<^sub>v unit_vec N t = pmat N h * dmat N \<psi> *\<^sub>v (pmat N f *\<^sub>v unit_vec N t)"
    by (rule assoc_mult_mat_vec[OF mult_carrier_mat[OF pmat_carrier dmat_carrier] pmat_carrier u(1)])
  also have "pmat N f *\<^sub>v unit_vec N t = unit_vec N (f t)" by (rule pmat_unit[where f = f, OF t f[OF t]])
  also have "pmat N h * dmat N \<psi> *\<^sub>v unit_vec N (f t) = pmat N h *\<^sub>v (dmat N \<psi> *\<^sub>v unit_vec N (f t))"
    by (rule assoc_mult_mat_vec[OF pmat_carrier dmat_carrier u(2)])
  also have "dmat N \<psi> *\<^sub>v unit_vec N (f t) = cis (\<psi> (f t)) \<cdot>\<^sub>v unit_vec N (f t)" by (rule dmat_unit[OF f[OF t]])
  also have "pmat N h *\<^sub>v (cis (\<psi> (f t)) \<cdot>\<^sub>v unit_vec N (f t)) = cis (\<psi> (f t)) \<cdot>\<^sub>v (pmat N h *\<^sub>v unit_vec N (f t))"
    by (rule mult_mat_vec[OF pmat_carrier u(2)])
  also have "pmat N h *\<^sub>v unit_vec N (f t) = unit_vec N t"
    using pmat_unit[where f = h, OF f[OF t] h[OF f[OF t]]] hf[OF t] by simp
  also have "cis (\<psi> (f t)) \<cdot>\<^sub>v unit_vec N t = dmat N (\<lambda>t. \<psi> (f t)) *\<^sub>v unit_vec N t" by (rule dmat_unit[OF t, symmetric])
  finally show "pmat N h * dmat N \<psi> * pmat N f *\<^sub>v unit_vec N t = dmat N (\<lambda>t. \<psi> (f t)) *\<^sub>v unit_vec N t" .
qed

lemma one_tensor_dmat:
  assumes a: "0 < a" and q: "0 < q"
  shows "1\<^sub>m a \<Otimes> dmat q \<psi> = dmat (a * q) (\<lambda>z. \<psi> (z mod q))"
proof (rule eq_matI)
  fix r t assume "r < dim_row (dmat (a * q) (\<lambda>z. \<psi> (z mod q)))" "t < dim_col (dmat (a * q) (\<lambda>z. \<psi> (z mod q)))"
  hence rt: "r < a * q" "t < a * q" by (simp_all add: dmat_def mat_diag_def)
  have e: "r = t \<longleftrightarrow> r div q = t div q \<and> r mod q = t mod q"
  proof
    assume h: "r div q = t div q \<and> r mod q = t mod q"
    have "r = r div q * q + r mod q" by simp
    also have "\<dots> = t div q * q + t mod q" using h by simp
    also have "\<dots> = t" by simp
    finally show "r = t" .
  qed simp
  have "(1\<^sub>m a \<Otimes> dmat q \<psi>) $$ (r, t) = 1\<^sub>m a $$ (r div q, t div q) * dmat q \<psi> $$ (r mod q, t mod q)"
    using index_tensor_mat[of "1\<^sub>m a" a a "dmat q \<psi>" q q r t] rt a q by (simp add: dmat_def mat_diag_def)
  also have "\<dots> = dmat (a * q) (\<lambda>z. \<psi> (z mod q)) $$ (r, t)"
    using rt e q by (auto simp: dmat_def mat_diag_def div_less_iff_less_mult)
  finally show "(1\<^sub>m a \<Otimes> dmat q \<psi>) $$ (r, t) = dmat (a * q) (\<lambda>z. \<psi> (z mod q)) $$ (r, t)" .
qed (simp_all add: dmat_def mat_diag_def)

lemma bit_mod4: "k < 2 \<Longrightarrow> bit (z mod 4) k \<longleftrightarrow> bit (z :: nat) k"
proof -
  assume k: "k < 2"
  have "z mod 4 = take_bit 2 z" by (simp add: take_bit_eq_mod)
  thus ?thesis using k by (simp add: bit_take_bit_iff)
qed

theorem dgate_gates_props:
  assumes c: "1 \<le> c" "c < K"
  shows "circuit_mat (2 ^ K) (dgate_gates K c \<psi>) = dgate K c \<psi>"
    "\<forall>U \<in> set (dgate_gates K c \<psi>). elementary (2 ^ K) U" "length (dgate_gates K c \<psi>) \<le> 2 * K + 1"
proof -
  let ?js = "dn c 1" and ?\<psi>' = "\<lambda>d :: nat. \<psi> (bit d 1) (bit d 0)"
  have rj: "\<And>j. j \<in> set ?js \<Longrightarrow> j + 2 \<le> K" using c by (auto simp: dn_def)
  have rj': "\<And>j. j \<in> set (rev ?js) \<Longrightarrow> j + 2 \<le> K" using rj by simp
  note A = swops_circuit[OF rj] and C = swops_circuit[OF rj']
  have K4: "(2::nat) ^ K = 2 ^ (K - 2) * 4"
  proof -
    have k2: "K = (K - 2) + 2" using c by simp
    have "(2::nat) ^ K = 2 ^ (K - 2) * 2 ^ 2" by (subst (1) k2) (rule power_add)
    thus ?thesis by simp
  qed
  let ?D = "1\<^sub>m (2 ^ (K - 2)) \<Otimes> dmat 4 ?\<psi>'"
  have D: "?D = dmat (2 ^ K) (\<lambda>z. ?\<psi>' (z mod 4))" unfolding K4 by (rule one_tensor_dmat) simp_all
  have Dc: "?D \<in> carrier_mat (2 ^ K) (2 ^ K)" unfolding D by (rule dmat_carrier)
  have eD: "elementary (2 ^ K) ?D"
  proof -
    have "elementary 4 (dmat 4 ?\<psi>')" by (rule elementary4) (simp_all add: dmat_unitary)
    from elementary_left[OF this, of "2 ^ (K - 2)"] show ?thesis unfolding K4 by simp
  qed
  let ?f = "apply_ops (swops ?js)" and ?h = "apply_ops (swops (rev ?js))"
  have f: "\<And>t. t < 2 ^ K \<Longrightarrow> ?f t < 2 ^ K" by (rule apply_ops_lt) (use rj in auto)
  have h: "\<And>t. t < 2 ^ K \<Longrightarrow> ?h t < 2 ^ K" by (rule apply_ops_lt) (use rj' in auto)
  have hf: "\<And>t. ?h (?f t) = t" using apply_ops_rev[of "swops ?js"] by (simp add: rev_map)
  have bits: "?\<psi>' (?f z mod 4) = \<psi> (bit z c) (bit z 0)" for z
  proof -
    have "pm ?js 1 = c" "pm ?js 0 = 0" using c by (simp_all add: pm_dn)
    thus ?thesis by (simp add: bit_mod4 bit_swops)
  qed
  have e1: "circuit_mat (2 ^ K) (dgate_gates K c \<psi>)
      = circuit_mat (2 ^ K) (map (cgate K 1) (swops (rev ?js))) * ?D * circuit_mat (2 ^ K) (map (cgate K 1) (swops ?js))"
  proof -
    have a1: "circuit_mat (2 ^ K) (map (cgate K 1) (swops ?js) @ [?D] @ map (cgate K 1) (swops (rev ?js)))
        = circuit_mat (2 ^ K) ([?D] @ map (cgate K 1) (swops (rev ?js))) * circuit_mat (2 ^ K) (map (cgate K 1) (swops ?js))"
      by (rule circuit_mat_append) (use A(2) C(2) Dc elementary_unitary(1) in auto)
    have a2: "circuit_mat (2 ^ K) ([?D] @ map (cgate K 1) (swops (rev ?js)))
        = circuit_mat (2 ^ K) (map (cgate K 1) (swops (rev ?js))) * circuit_mat (2 ^ K) [?D]"
      by (rule circuit_mat_append) (use C(2) Dc elementary_unitary(1) in auto)
    show ?thesis unfolding dgate_gates_def a1 a2 circuit_mat_single[OF Dc] ..
  qed
  have e2: "circuit_mat (2 ^ K) (dgate_gates K c \<psi>) = pmat (2 ^ K) ?h * ?D * pmat (2 ^ K) ?f"
    unfolding e1 by (simp only: A(1) C(1))
  have "pmat (2 ^ K) ?h * dmat (2 ^ K) (\<lambda>z. ?\<psi>' (z mod 4)) * pmat (2 ^ K) ?f = dmat (2 ^ K) (\<lambda>t. ?\<psi>' (?f t mod 4))"
    by (rule pmat_dmat_conj[OF f h hf])
  also have "\<dots> = dmat (2 ^ K) (\<lambda>z. \<psi> (bit z c) (bit z 0))" by (simp only: bits)
  finally show "circuit_mat (2 ^ K) (dgate_gates K c \<psi>) = dgate K c \<psi>" unfolding e2 D dgate_def .
  show "\<forall>U \<in> set (dgate_gates K c \<psi>). elementary (2 ^ K) U"
    using A(2) C(2) eD by (auto simp: dgate_gates_def)
  show "length (dgate_gates K c \<psi>) \<le> 2 * K + 1" using c by (simp add: dgate_gates_def)
qed

end
