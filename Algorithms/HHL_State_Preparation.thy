theory HHL_State_Preparation
  imports HHL_Uniform_Rotation
begin

section \<open>State preparation by uniformly controlled rotations\<close>

text \<open>A state with amplitudes $a_x\ge0$ on $k$ qubits is prepared from $\ket{0\cdots0}$ by $k$
levels; level $j$ rotates qubit $j$ by an angle depending on the first $j$ qubits, so that afterwards
the first $j+1$ qubits carry the norms of the amplitude blocks (\<open>lev_step\<close>, \<open>cascade_prepares\<close>).
Each level is a uniformly controlled rotation; with no register between controls and target all its
gates are elementary (\<open>state_prep\<close>).  For the sine window this replaces the $k$-qubit reflection
(\<open>window_prep\<close>), and the paper-regime programs then have only elementary gates, ancilla rotations
controlled by the last clock qubit, the preparation of $\ket b$ and oracle calls
(\<open>hhl_apx_fine3\<close>).\<close>

text \<open>Amplitudes $a_x\ge0$ on $k$ qubits.  \<open>pnorm k a j c\<close> is the norm of the amplitudes whose
first $j$ qubits read $c$.\<close>

definition pnorm :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "pnorm k a j c = sqrt (\<Sum>x<2 ^ (k - j). (a (c * 2 ^ (k - j) + x))\<^sup>2)"

definition pangle :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "pangle k a j c = (if pnorm k a j c = 0 then 0 else arcsin (pnorm k a (Suc j) (2 * c + 1) / pnorm k a j c))"


lemma pnorm_split:
  assumes j: "j < k"
  shows "(pnorm k a j c)\<^sup>2 = (pnorm k a (Suc j) (2 * c))\<^sup>2 + (pnorm k a (Suc j) (2 * c + 1))\<^sup>2"
proof -
  let ?h = "2 ^ (k - Suc j) :: nat"
  have e: "(2::nat) ^ (k - j) = 2 * ?h" using j by (simp add: power_Suc[symmetric] Suc_diff_Suc)
  have "(\<Sum>x<2 ^ (k - j). (a (c * 2 ^ (k - j) + x))\<^sup>2) = (\<Sum>x<?h + ?h. (a (c * (2 * ?h) + x))\<^sup>2)"
    unfolding e by (simp add: mult_2)
  also have "\<dots> = (\<Sum>x<?h. (a (c * (2 * ?h) + x))\<^sup>2) + (\<Sum>x<?h. (a (c * (2 * ?h) + (?h + x)))\<^sup>2)"
    by (rule sum_split_add)
  also have "\<dots> = (\<Sum>x<?h. (a (2 * c * ?h + x))\<^sup>2) + (\<Sum>x<?h. (a ((2 * c + 1) * ?h + x))\<^sup>2)"
    by (simp add: algebra_simps)
  finally show ?thesis unfolding pnorm_def by (simp add: sum_nonneg)
qed

lemma pnorm_ge0: "0 \<le> pnorm k a j c" by (simp add: pnorm_def sum_nonneg)

lemma pangle_cos_sin:
  assumes j: "j < k"
  shows "cos (pangle k a j c) * pnorm k a j c = pnorm k a (Suc j) (2 * c) \<and>
         sin (pangle k a j c) * pnorm k a j c = pnorm k a (Suc j) (2 * c + 1)"
proof -
  note sp = pnorm_split[OF j, of a c]
  let ?P = "pnorm k a j c" and ?L = "pnorm k a (Suc j) (2 * c)" and ?R = "pnorm k a (Suc j) (2 * c + 1)"
  have g: "0 \<le> ?P" "0 \<le> ?L" "0 \<le> ?R" by (simp_all add: pnorm_ge0)
  show ?thesis
  proof (cases "?P = 0")
    case True
    have "?L\<^sup>2 + ?R\<^sup>2 = 0" using sp True by simp
    hence "?L = 0" "?R = 0" using g by (simp_all add: sum_power2_eq_zero_iff)
    thus ?thesis using True by simp
  next
    case nz: False
    hence P0: "0 < ?P" using g by simp
    have sq: "?R\<^sup>2 \<le> ?P\<^sup>2" using sp by simp
    have r: "?R \<le> ?P" by (rule power2_le_imp_le[OF sq g(1)])
    have q: "?R / ?P \<le> 1" "- 1 \<le> ?R / ?P" using r P0 g by (simp_all add: field_simps)
    have s: "sin (pangle k a j c) = ?R / ?P" using nz q by (simp add: pangle_def sin_arcsin)
    have c: "cos (pangle k a j c) = sqrt (1 - (?R / ?P)\<^sup>2)" using nz q by (simp add: pangle_def cos_arcsin)
    have P2: "?P\<^sup>2 \<noteq> 0" using P0 by simp
    have "1 - (?R / ?P)\<^sup>2 = (?P\<^sup>2 - ?R\<^sup>2) / ?P\<^sup>2" using P2 by (simp add: power_divide field_simps)
    also have "\<dots> = (?L / ?P)\<^sup>2" using sp by (simp add: power_divide)
    finally have "1 - (?R / ?P)\<^sup>2 = (?L / ?P)\<^sup>2" .
    hence "cos (pangle k a j c) = ?L / ?P" unfolding c using g P0 by simp
    thus ?thesis unfolding s using P0 by simp
  qed
qed


definition pvec :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "pvec k a j = Matrix.vec (2 ^ k) (\<lambda>x. if x mod 2 ^ (k - j) = 0 then complex_of_real (pnorm k a j (x div 2 ^ (k - j))) else 0)"

definition lev :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "lev k a j = ctrl_blocks (2 ^ j) (2 * 2 ^ (k - Suc j)) (\<lambda>c. Rot (pangle k a j c) \<Otimes> 1\<^sub>m (2 ^ (k - Suc j)))"

lemma lev_dim: "j < k \<Longrightarrow> 2 ^ j * (2 * 2 ^ (k - Suc j)) = (2::nat) ^ k"
proof -
  assume j: "j < k"
  have "2 ^ j * (2 * 2 ^ (k - Suc j)) = (2::nat) ^ (j + Suc (k - Suc j))" by (simp add: power_add)
  also have "j + Suc (k - Suc j) = k" using j by simp
  finally show ?thesis .
qed

lemma div_split2: "r div h = 2 * (r div (2 * h)) + r mod (2 * h) div h" for r h :: nat
proof -
  have a: "r div (2 * h) = r div h div 2" by (simp add: div_mult2_eq Groups.mult.commute[of 2 h])
  have b: "r mod (2 * h) div h = r div h mod 2"
  proof (cases "h = 0")
    case False
    have "r mod (h * 2) = h * (r div h mod 2) + r mod h" by (rule mod_mult2_eq)
    hence "r mod (2 * h) div h = (h * (r div h mod 2) + r mod h) div h" by (simp add: Groups.mult.commute[of 2 h])
    also have "\<dots> = r div h mod 2" using False by simp
    finally show ?thesis .
  qed simp
  show ?thesis unfolding a b by simp
qed

lemma lev_step:
  assumes j: "j < k"
  shows "lev k a j *\<^sub>v pvec k a j = pvec k a (Suc j)"
proof (rule eq_vecI)
  let ?h = "2 ^ (k - Suc j) :: nat" and ?m = "2 * 2 ^ (k - Suc j) :: nat"
  have mk: "(2::nat) ^ (k - j) = ?m" using j by (simp add: power_Suc[symmetric] Suc_diff_Suc)
  have K: "2 ^ j * ?m = (2::nat) ^ k" by (rule lev_dim[OF j])
  have h0: "0 < ?h" by simp
  show "dim_vec (lev k a j *\<^sub>v pvec k a j) = dim_vec (pvec k a (Suc j))" using K by (simp add: lev_def pvec_def)
  fix r assume "r < dim_vec (pvec k a (Suc j))"
  hence r: "r < 2 ^ j * ?m" using K by (simp add: pvec_def)
  let ?c = "r div ?m" and ?s0 = "r div ?m * ?m" and ?th = "pangle k a j (r div ?m)"
  have c: "?c < 2 ^ j" using r by (simp add: less_mult_imp_div_less)
  have s0: "?s0 < 2 ^ j * ?m" using c by (intro mult_less_mono1) simp_all
  let ?t = "\<lambda>s. lev k a j $$ (r, s) * pvec k a j $ s"
  have z: "?t s = (if s = ?s0 then ?t ?s0 else 0)" if s: "s < 2 ^ j * ?m" for s
  proof (cases "s = ?s0")
    case False
    show ?thesis
    proof (cases "s mod ?m = 0")
      case True
      have "s div ?m \<noteq> ?c"
      proof
        assume "s div ?m = ?c"
        hence "s = ?s0" using True div_mult_mod_eq[of s ?m] by simp
        thus False using False by simp
      qed
      hence "lev k a j $$ (r, s) = 0" unfolding lev_def using r s by (simp add: ctrl_blocks_index)
      thus ?thesis using False by simp
    next
      case nz: False
      have "pvec k a j $ s = 0" using nz s K by (simp add: pvec_def mk)
      thus ?thesis using False by simp
    qed
  qed simp
  have "(lev k a j *\<^sub>v pvec k a j) $ r = (\<Sum>s<2 ^ j * ?m. ?t s)"
    using r K by (simp add: lev_def pvec_def scalar_prod_def atLeast0LessThan Groups.mult_ac)
  also have "\<dots> = (\<Sum>s<2 ^ j * ?m. if s = ?s0 then ?t ?s0 else 0)" by (rule sum.cong[OF refl]) (simp add: z)
  also have "\<dots> = ?t ?s0" using s0 by simp
  also have "lev k a j $$ (r, ?s0) = (Rot ?th \<Otimes> 1\<^sub>m ?h) $$ (r mod ?m, 0)"
    unfolding lev_def using r s0 by (simp add: ctrl_blocks_index)
  also have "\<dots> = Rot ?th $$ (r mod ?m div ?h, 0) * 1\<^sub>m ?h $$ (r mod ?m mod ?h, 0)"
    using index_tensor_mat[of "Rot ?th" 2 2 "1\<^sub>m ?h" ?h ?h "r mod ?m" 0] h0 by simp
  also have "pvec k a j $ ?s0 = complex_of_real (pnorm k a j ?c)" using s0 K by (simp add: pvec_def mk)
  finally have e: "(lev k a j *\<^sub>v pvec k a j) $ r
                 = Rot ?th $$ (r mod ?m div ?h, 0) * 1\<^sub>m ?h $$ (r mod ?m mod ?h, 0) * complex_of_real (pnorm k a j ?c)" .
  have mm: "r mod ?m mod ?h = r mod ?h" by (simp add: mod_mod_cancel)
  have bit: "r mod ?m div ?h < 2" using h0 by (simp add: less_mult_imp_div_less)
  have dv: "r div ?h = 2 * ?c + r mod ?m div ?h" by (rule div_split2)
  note cs = pangle_cos_sin[OF j, of a ?c]
  show "(lev k a j *\<^sub>v pvec k a j) $ r = pvec k a (Suc j) $ r"
  proof (cases "r mod ?h = 0")
    case False
    thus ?thesis unfolding e mm using r K h0 by (simp add: pvec_def)
  next
    case True
    have "r mod ?m div ?h = 0 \<or> r mod ?m div ?h = 1" using bit by auto
    thus ?thesis
    proof
      assume b0: "r mod ?m div ?h = 0"
      have "Rot ?th $$ (0, 0) * complex_of_real (pnorm k a j ?c) = complex_of_real (pnorm k a (Suc j) (2 * ?c))"
        using cs by (simp add: Rot_def of_real_mult[symmetric] Groups.mult.commute)
      thus ?thesis unfolding e mm b0 using r K True dv b0 by (simp add: pvec_def)
    next
      assume b1: "r mod ?m div ?h = 1"
      have "Rot ?th $$ (1, 0) * complex_of_real (pnorm k a j ?c) = complex_of_real (pnorm k a (Suc j) (2 * ?c + 1))"
        using cs by (simp add: Rot_def of_real_mult[symmetric] Groups.mult.commute)
      thus ?thesis unfolding e mm b1 using r K True dv b1 by (simp add: pvec_def)
    qed
  qed
qed


lemma pvec_zero:
  assumes n: "(\<Sum>x<2 ^ k. (a x)\<^sup>2) = 1"
  shows "pvec k a 0 = unit_vec (2 ^ k) 0"
proof (rule eq_vecI)
  fix x assume "x < dim_vec (unit_vec (2 ^ k) 0 :: complex Matrix.vec)"
  hence x: "x < 2 ^ k" by simp
  have p0: "pnorm k a 0 0 = 1" unfolding pnorm_def using n by simp
  show "pvec k a 0 $ x = unit_vec (2 ^ k) 0 $ x" using x p0 by (simp add: pvec_def unit_vec_def)
qed (simp add: pvec_def)

lemma pvec_full:
  assumes a: "\<And>x. x < 2 ^ k \<Longrightarrow> 0 \<le> a x"
  shows "pvec k a k = Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))"
  by (rule eq_vecI) (simp_all add: pvec_def pnorm_def a)

lemma lev_carrier: "j < k \<Longrightarrow> lev k a j \<in> carrier_mat (2 ^ k) (2 ^ k)"
proof -
  assume j: "j < k"
  have "lev k a j \<in> carrier_mat (2 ^ j * (2 * 2 ^ (k - Suc j))) (2 ^ j * (2 * 2 ^ (k - Suc j)))" by (simp add: lev_def)
  thus ?thesis unfolding lev_dim[OF j] .
qed

lemma cascade: "j \<le> k \<Longrightarrow> run_gates (pvec k a 0) (map (lev k a) [0..<j]) = pvec k a j"
proof (induction j)
  case 0 thus ?case by simp
next
  case (Suc j)
  have "run_gates (pvec k a 0) (map (lev k a) [0..<Suc j]) = lev k a j *\<^sub>v run_gates (pvec k a 0) (map (lev k a) [0..<j])"
    by (simp add: run_gates_append)
  also have "\<dots> = lev k a j *\<^sub>v pvec k a j" using Suc by simp
  also have "\<dots> = pvec k a (Suc j)" by (rule lev_step) (use Suc.prems in simp)
  finally show ?case .
qed

theorem cascade_prepares:
  assumes n: "(\<Sum>x<2 ^ k. (a x)\<^sup>2) = 1" and a: "\<And>x. x < 2 ^ k \<Longrightarrow> 0 \<le> a x"
  shows "circuit_mat (2 ^ k) (map (lev k a) [0..<k]) *\<^sub>v unit_vec (2 ^ k) 0 = Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))"
proof -
  have "circuit_mat (2 ^ k) (map (lev k a) [0..<k]) *\<^sub>v unit_vec (2 ^ k) 0 = run_gates (unit_vec (2 ^ k) 0) (map (lev k a) [0..<k])"
    by (rule circuit_mat_run) (auto simp: lev_carrier)
  also have "\<dots> = pvec k a k" using cascade[of k k a] pvec_zero[OF n] by simp
  finally show ?thesis using pvec_full[OF a] by simp
qed

subsection \<open>Each level in elementary gates\<close>

lemma ctrl_blocks_tensor_right:
  assumes B: "\<And>c. c < N \<Longrightarrow> B c \<in> carrier_mat m m" and m: "0 < m" and r: "0 < r"
  shows "ctrl_blocks N m B \<Otimes> 1\<^sub>m r = ctrl_blocks N (m * r) (\<lambda>c. B c \<Otimes> 1\<^sub>m r)"
proof (rule eq_matI)
  fix x y assume "x < dim_row (ctrl_blocks N (m * r) (\<lambda>c. B c \<Otimes> 1\<^sub>m r))" "y < dim_col (ctrl_blocks N (m * r) (\<lambda>c. B c \<Otimes> 1\<^sub>m r))"
  hence xy: "x < N * (m * r)" "y < N * (m * r)" by simp_all
  have xy': "x div r < N * m" "y div r < N * m" using xy by (simp_all add: less_mult_imp_div_less Groups.mult_ac)
  have N0: "0 < N" using xy by (cases N) auto
  have d: "z div (m * r) = z div r div m" for z by (simp add: div_mult2_eq Groups.mult.commute[of m r])
  have md: "z mod (m * r) div r = z div r mod m" "z mod (m * r) mod r = z mod r" for z
    using r by (simp_all add: mod_mult2_eq Groups.mult.commute[of m r] div_mult2_eq mod_mod_cancel)
  have mr: "z mod (m * r) < m * r" for z using m r by simp
  have "(ctrl_blocks N m B \<Otimes> 1\<^sub>m r) $$ (x, y) = ctrl_blocks N m B $$ (x div r, y div r) * 1\<^sub>m r $$ (x mod r, y mod r)"
    using index_tensor_mat[of "ctrl_blocks N m B" "N * m" "N * m" "1\<^sub>m r" r r x y] xy m r N0 by (simp add: Groups.mult_ac)
  also have "\<dots> = (if x div r div m = y div r div m then B (x div r div m) $$ (x div r mod m, y div r mod m) else 0) * (if x mod r = y mod r then 1 else 0)"
    using xy' r by (simp add: ctrl_blocks_index)
  also have "\<dots> = ctrl_blocks N (m * r) (\<lambda>c. B c \<Otimes> 1\<^sub>m r) $$ (x, y)"
  proof -
    have Bc: "B (x div r div m) \<in> carrier_mat m m" using B xy' by (simp add: less_mult_imp_div_less)
    have "(B (x div r div m) \<Otimes> 1\<^sub>m r) $$ (x mod (m * r), y mod (m * r))
          = B (x div r div m) $$ (x div r mod m, y div r mod m) * (if x mod r = y mod r then 1 else 0)"
      using index_tensor_mat[of "B (x div r div m)" m m "1\<^sub>m r" r r "x mod (m * r)" "y mod (m * r)"] Bc mr m r
      by (simp add: md)
    note f = this
    show ?thesis
    proof (cases "x div r div m = y div r div m")
      case True
      have "ctrl_blocks N (m * r) (\<lambda>c. B c \<Otimes> 1\<^sub>m r) $$ (x, y) = (B (x div r div m) \<Otimes> 1\<^sub>m r) $$ (x mod (m * r), y mod (m * r))"
        using xy True by (simp add: ctrl_blocks_index d)
      thus ?thesis unfolding f using True by simp
    next
      case False
      have "ctrl_blocks N (m * r) (\<lambda>c. B c \<Otimes> 1\<^sub>m r) $$ (x, y) = 0" using xy False by (simp add: ctrl_blocks_index d)
      thus ?thesis using False by simp
    qed
  qed
  finally show "(ctrl_blocks N m B \<Otimes> 1\<^sub>m r) $$ (x, y) = ctrl_blocks N (m * r) (\<lambda>c. B c \<Otimes> 1\<^sub>m r) $$ (x, y)" .
qed (simp_all add: Groups.mult_ac)


lemma ctrl_blocks_mod2:
  assumes B: "\<And>b. b < 2 \<Longrightarrow> B b \<in> carrier_mat m m" and m: "0 < m" and a0: "0 < a"
  shows "ctrl_blocks (a * 2) m (\<lambda>c. B (c mod 2)) = 1\<^sub>m a \<Otimes> ctrl_blocks 2 m B"
proof (rule eq_matI)
  fix x y assume "x < dim_row (1\<^sub>m a \<Otimes> ctrl_blocks 2 m B)" "y < dim_col (1\<^sub>m a \<Otimes> ctrl_blocks 2 m B)"
  hence xy: "x < a * 2 * m" "y < a * 2 * m" by (simp_all add: Groups.mult_ac)
  have m2: "z mod (2 * m) < 2 * m" for z using m by simp
  have d: "z div (2 * m) = z div m div 2" "z mod (2 * m) div m = z div m mod 2" "z mod (2 * m) mod m = z mod m" for z
    using m by (simp_all add: div_mult2_eq mod_mult2_eq Groups.mult.commute[of 2 m] mod_mod_cancel)
  have q: "x div m = y div m \<longleftrightarrow> x div m div 2 = y div m div 2 \<and> x div m mod 2 = y div m mod 2"
  proof
    assume h: "x div m div 2 = y div m div 2 \<and> x div m mod 2 = y div m mod 2"
    have "x div m = x div m div 2 * 2 + x div m mod 2" by simp
    also have "\<dots> = y div m div 2 * 2 + y div m mod 2" using h by simp
    also have "\<dots> = y div m" by simp
    finally show "x div m = y div m" .
  qed simp
  have "(1\<^sub>m a \<Otimes> ctrl_blocks 2 m B) $$ (x, y) = 1\<^sub>m a $$ (x div (2 * m), y div (2 * m)) * ctrl_blocks 2 m B $$ (x mod (2 * m), y mod (2 * m))"
    using index_tensor_mat[of "1\<^sub>m a" a a "ctrl_blocks 2 m B" "2 * m" "2 * m" x y] xy a0 m by (simp add: Groups.mult_ac)
  also have "\<dots> = (if x div m = y div m then B (x div m mod 2) $$ (x mod m, y mod m) else 0)"
  proof -
    have xy2: "x < a * (2 * m)" "y < a * (2 * m)" using xy by (simp_all add: Groups.mult.assoc)
    have dv: "x div (2 * m) < a" "y div (2 * m) < a" using xy2 by (simp_all add: less_mult_imp_div_less)
    have i1: "1\<^sub>m a $$ (x div (2 * m), y div (2 * m)) = (if x div (2 * m) = y div (2 * m) then 1 else (0::complex))"
      using dv by simp
    have i2: "ctrl_blocks 2 m B $$ (x mod (2 * m), y mod (2 * m))
              = (if x mod (2 * m) div m = y mod (2 * m) div m then B (x mod (2 * m) div m) $$ (x mod (2 * m) mod m, y mod (2 * m) mod m) else 0)"
      by (rule ctrl_blocks_index) (use m2 in simp_all)
    show ?thesis unfolding i1 i2 unfolding d q by simp
  qed
  also have "\<dots> = ctrl_blocks (a * 2) m (\<lambda>c. B (c mod 2)) $$ (x, y)" using xy by (simp add: ctrl_blocks_index)
  finally show "ctrl_blocks (a * 2) m (\<lambda>c. B (c mod 2)) $$ (x, y) = (1\<^sub>m a \<Otimes> ctrl_blocks 2 m B) $$ (x, y)" by simp
qed (simp_all add: Groups.mult_ac)

lemma cv0_one_elementary:
  assumes j: "1 \<le> j" and W: "Wr \<in> carrier_mat 2 2" "Quantum.unitary Wr"
  shows "elementary (2 ^ j * (1 * 2)) (cv0 j 1 Wr)"
proof -
  let ?B = "\<lambda>b. if b = 1 then Wr else 1\<^sub>m 2" and ?a = "2 ^ (j - 1) :: nat"
  have Bc: "\<And>b. b < 2 \<Longrightarrow> ?B b \<in> carrier_mat 2 2" using W by simp
  have aj: "?a * 2 = 2 ^ j"
  proof -
    obtain j' where "j = Suc j'" using j by (cases j) auto
    thus ?thesis by simp
  qed
  have "cv0 j 1 Wr = ctrl_blocks (2 ^ j) 2 (\<lambda>c. if odd c then Wr else 1\<^sub>m 2)"
    unfolding cv0_def left_tensor_id[OF W(1)] Groups.monoid_mult_class.mult_1_left ..
  also have "\<dots> = ctrl_blocks (?a * 2) 2 (\<lambda>c. ?B (c mod 2))"
    unfolding aj by (rule ctrl_blocks_cong) (auto simp: odd_iff_mod_2_eq_one)
  also have "\<dots> = 1\<^sub>m ?a \<Otimes> ctrl_blocks 2 2 ?B" by (rule ctrl_blocks_mod2[OF Bc]) simp_all
  finally have e0: "cv0 j 1 Wr = 1\<^sub>m ?a \<Otimes> ctrl_blocks 2 2 ?B" .
  have r1: "ctrl_blocks 2 2 ?B \<Otimes> 1\<^sub>m 1 = ctrl_blocks 2 2 ?B" by (rule right_tensor_id[of _ "2 * 2" "2 * 2"]) (rule ctrl_blocks_carrier)
  have e: "cv0 j 1 Wr = 1\<^sub>m ?a \<Otimes> (ctrl_blocks 2 2 ?B \<Otimes> 1\<^sub>m 1)" unfolding r1 by (rule e0)
  have u: "Quantum.unitary (ctrl_blocks 2 2 ?B)" by (rule ctrl_blocks_unitary) (use W in \<open>auto simp: id_is_unitary\<close>)
  have K: "2 ^ j * (1 * 2) = ?a * (2 ^ 2 * 1)" using aj by simp
  show ?thesis unfolding elementary_def
  proof (rule exI[of _ ?a], rule exI[of _ 1], rule exI[of _ 2], rule exI[of _ "ctrl_blocks 2 2 ?B"], intro conjI)
    show "cv0 j 1 Wr = 1\<^sub>m ?a \<Otimes> (ctrl_blocks 2 2 ?B \<Otimes> 1\<^sub>m 1)" by (rule e)
    show "2 ^ j * (1 * 2) = ?a * (2 ^ 2 * 1)" by (rule K)
    show "Quantum.unitary (ctrl_blocks 2 2 ?B)" by (rule u)
    show "ctrl_blocks 2 2 ?B \<in> carrier_mat (2 ^ 2) (2 ^ 2)" using ctrl_blocks_carrier[of 2 2 ?B] by (simp add: numeral_eq_Suc)
  qed simp_all
qed

lemma ucr_one_elementary:
  assumes U: "U \<in> set (ucr_gates j 1 \<theta>)"
  shows "elementary (2 ^ j * (1 * 2)) U"
proof -
  have "elementary (2 ^ j * (1 * 2)) U \<or> (\<exists>a. U = cv0 j 1 (Rot a))" by (rule ucr_gate_kinds[OF U]) simp
  thus ?thesis
  proof
    assume "\<exists>a. U = cv0 j 1 (Rot a)"
    then obtain a where Ua: "U = cv0 j 1 (Rot a)" by blast
    show ?thesis
    proof (cases "j = 0")
      case True
      have "nzmasks 0 = []" by (simp add: nzmasks_def masks_def)
      hence "U = anc_rot 0 1 (sum_list (map (walsh 0 \<theta>) (masks 0)))" using U True by (simp add: ucr_gates_def)
      thus ?thesis using anc_rot_elementary[of 1 0] True by simp
    next
      case False
      thus ?thesis unfolding Ua by (intro cv0_one_elementary) (simp_all add: Rot_unitary)
    qed
  qed
qed

definition lev_gates :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "lev_gates k a j = map (\<lambda>G. G \<Otimes> 1\<^sub>m (2 ^ (k - Suc j))) (ucr_gates j 1 (pangle k a j))"

lemma lev_gates_props:
  assumes j: "j < k"
  shows "circuit_mat (2 ^ k) (lev_gates k a j) = lev k a j" and "\<And>U. U \<in> set (lev_gates k a j) \<Longrightarrow> elementary (2 ^ k) U"
proof -
  let ?h = "2 ^ (k - Suc j) :: nat" and ?Kj = "2 ^ j * (1 * 2) :: nat"
  have Kh: "?Kj * ?h = 2 ^ k" using lev_dim[OF j] by (simp add: Groups.mult_ac)
  have gc: "\<And>U. U \<in> set (ucr_gates j 1 (pangle k a j)) \<Longrightarrow> U \<in> carrier_mat ?Kj ?Kj"
    using ucr_gates_ok[of _ j 1] by simp
  have "circuit_mat (?Kj * ?h) (lev_gates k a j) = circuit_mat ?Kj (ucr_gates j 1 (pangle k a j)) \<Otimes> 1\<^sub>m ?h"
    unfolding lev_gates_def by (rule circuit_mat_tensor_right) (use gc in simp_all)
  also have "circuit_mat ?Kj (ucr_gates j 1 (pangle k a j)) = ctrl_blocks (2 ^ j) (1 * 2) (\<lambda>c. 1\<^sub>m 1 \<Otimes> Rot (pangle k a j c))"
    by (rule ucr_circuit) simp
  also have "\<dots> \<Otimes> 1\<^sub>m ?h = ctrl_blocks (2 ^ j) (1 * 2 * ?h) (\<lambda>c. (1\<^sub>m 1 \<Otimes> Rot (pangle k a j c)) \<Otimes> 1\<^sub>m ?h)"
    by (rule ctrl_blocks_tensor_right) (use tensor_one_Rot_carrier[of 1] in simp_all)
  also have "\<dots> = lev k a j"
  proof -
    have l1: "\<And>x. 1\<^sub>m 1 \<Otimes> Rot x = Rot x" by (rule left_tensor_id[OF Rot_carrier])
    show ?thesis unfolding lev_def l1 by simp
  qed
  finally show "circuit_mat (2 ^ k) (lev_gates k a j) = lev k a j" unfolding Kh .
  show "\<And>U. U \<in> set (lev_gates k a j) \<Longrightarrow> elementary (2 ^ k) U"
  proof -
    fix U assume "U \<in> set (lev_gates k a j)"
    then obtain G where G: "G \<in> set (ucr_gates j 1 (pangle k a j))" and U: "U = G \<Otimes> 1\<^sub>m ?h" unfolding lev_gates_def by auto
    have "elementary (?Kj * ?h) (G \<Otimes> 1\<^sub>m ?h)" by (rule elementary_right[OF ucr_one_elementary[OF G]]) simp
    thus "elementary (2 ^ k) U" unfolding U Kh .
  qed
qed

definition prep_gates :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list" where
  "prep_gates k a = concat (map (lev_gates k a) [0..<k])"

theorem state_prep:
  assumes n: "(\<Sum>x<2 ^ k. (a x)\<^sup>2) = 1" and a: "\<And>x. x < 2 ^ k \<Longrightarrow> 0 \<le> a x"
  shows "circuit_mat (2 ^ k) (prep_gates k a) *\<^sub>v unit_vec (2 ^ k) 0 = Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))"
    and "\<And>U. U \<in> set (prep_gates k a) \<Longrightarrow> elementary (2 ^ k) U"
proof -
  show el: "\<And>U. U \<in> set (prep_gates k a) \<Longrightarrow> elementary (2 ^ k) U"
    unfolding prep_gates_def using lev_gates_props(2) by fastforce
  have "circuit_mat (2 ^ k) (prep_gates k a) = circuit_mat (2 ^ k) (map (circuit_mat (2 ^ k)) (map (lev_gates k a) [0..<k]))"
    unfolding prep_gates_def by (rule circuit_mat_concat) (use el elementary_unitary in \<open>auto simp: prep_gates_def\<close>)
  also have "map (circuit_mat (2 ^ k)) (map (lev_gates k a) [0..<k]) = map (lev k a) [0..<k]"
    by (simp add: lev_gates_props(1))
  finally show "circuit_mat (2 ^ k) (prep_gates k a) *\<^sub>v unit_vec (2 ^ k) 0 = Matrix.vec (2 ^ k) (\<lambda>x. complex_of_real (a x))"
    using cascade_prepares[OF n a] by simp
qed

subsection \<open>The sine window\<close>

lemma win_coef_nonneg: "\<tau> < N \<Longrightarrow> 0 \<le> win_coef N \<tau>"
proof -
  assume t: "\<tau> < N"
  have "0 \<le> pi * (real \<tau> + 1 / 2) / real N" by simp
  moreover have "pi * (real \<tau> + 1 / 2) / real N \<le> pi"
  proof -
    have "\<tau> + 1 \<le> N" using t by simp
    hence "real (\<tau> + 1) \<le> real N" by (simp only: of_nat_le_iff)
    hence "real \<tau> + 1 / 2 \<le> real N" by simp
    thus ?thesis by (simp add: divide_le_eq mult_left_le)
  qed
  ultimately have "0 \<le> sin (pi * (real \<tau> + 1 / 2) / real N)" by (rule sin_ge_zero)
  thus ?thesis unfolding win_coef_def by simp
qed

lemma win_coef_norm: "2 \<le> N \<Longrightarrow> (\<Sum>x<N. (win_coef N x)\<^sup>2) = 1"
proof -
  assume N: "2 \<le> N"
  have "1 = \<parallel>win_state N\<parallel>\<^sup>2" using win_state_norm[OF N] by simp
  also have "\<dots> = (\<Sum>x<N. (win_coef N x)\<^sup>2)" unfolding vnorm_sq by (simp add: win_state_def)
  finally show ?thesis by simp
qed

theorem window_prep:
  assumes k: "1 \<le> k"
  shows "circuit_mat (2 ^ k) (prep_gates k (win_coef (2 ^ k))) *\<^sub>v unit_vec (2 ^ k) 0 = win_state (2 ^ k)"
    and "\<And>U. U \<in> set (prep_gates k (win_coef (2 ^ k))) \<Longrightarrow> elementary (2 ^ k) U"
proof -
  have N: "2 \<le> (2::nat) ^ k" using power_increasing[of 1 k "2::nat"] k by simp
  show "circuit_mat (2 ^ k) (prep_gates k (win_coef (2 ^ k))) *\<^sub>v unit_vec (2 ^ k) 0 = win_state (2 ^ k)"
    "\<And>U. U \<in> set (prep_gates k (win_coef (2 ^ k))) \<Longrightarrow> elementary (2 ^ k) U"
    using state_prep[OF win_coef_norm[OF N] win_coef_nonneg] unfolding win_state_def by simp_all
qed


subsection \<open>The full preparation in gates\<close>

definition win_prep_gates :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "win_prep_gates k n Ub = map (\<lambda>G. G \<Otimes> 1\<^sub>m (n * 2)) (prep_gates k (win_coef (2 ^ k))) @ [prep_gate (2 ^ k) Ub]"

definition win_prep_mat :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "win_prep_mat k n Ub = circuit_mat (2 ^ k * (n * 2)) (win_prep_gates k n Ub)"

lemma win_prep_gates_props:
  assumes k: "1 \<le> k" and n0: "0 < n" and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
  shows "\<And>U. U \<in> set (win_prep_gates k n Ub) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
    and "\<And>U. U \<in> set (win_prep_gates k n Ub) \<Longrightarrow> elementary (2 ^ k * (n * 2)) U \<or> U = prep_gate (2 ^ k) Ub"
    and "win_prep_mat k n Ub \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))" "Quantum.unitary (win_prep_mat k n Ub)"
    and "win_prep_mat k n Ub *\<^sub>v unit_vec (2 ^ k * (n * 2)) 0 = tensor_vec (win_state (2 ^ k)) (tensor_vec b (unit_vec 2 0))"
proof -
  let ?K = "2 ^ k * (n * 2)" and ?W = "circuit_mat (2 ^ k) (prep_gates k (win_coef (2 ^ k)))"
  note wp = window_prep[OF k]
  have m0: "0 < n * 2" using n0 by simp
  have pc: "prep_gate (2 ^ k) Ub \<in> carrier_mat ?K ?K"
    unfolding prep_gate_def by (rule tensor_carrier[OF one_carrier_mat tensor_carrier[OF Ub(1) one_carrier_mat]])
  have pu: "Quantum.unitary (prep_gate (2 ^ k) Ub)"
    unfolding prep_gate_def by (rule tensor_mat_unitary[OF id_is_unitary tensor_mat_unitary[OF Ub(2) id_is_unitary]])
  show kind: "\<And>U. U \<in> set (win_prep_gates k n Ub) \<Longrightarrow> elementary ?K U \<or> U = prep_gate (2 ^ k) Ub"
  proof -
    fix U assume "U \<in> set (win_prep_gates k n Ub)"
    hence "(\<exists>G \<in> set (prep_gates k (win_coef (2 ^ k))). U = G \<Otimes> 1\<^sub>m (n * 2)) \<or> U = prep_gate (2 ^ k) Ub"
      unfolding win_prep_gates_def by auto
    thus "elementary ?K U \<or> U = prep_gate (2 ^ k) Ub" using elementary_right[OF wp(2) m0] by blast
  qed
  show ok: "\<And>U. U \<in> set (win_prep_gates k n Ub) \<Longrightarrow> U \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary U"
  proof -
    fix U assume "U \<in> set (win_prep_gates k n Ub)"
    hence "elementary ?K U \<or> U = prep_gate (2 ^ k) Ub" by (rule kind)
    thus "U \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary U"
      using elementary_unitary unitary_bridge pc pu by blast
  qed
  show "win_prep_mat k n Ub \<in> carrier_mat ?K ?K" unfolding win_prep_mat_def by (rule circuit_mat_carrier) (use ok in blast)
  show "Quantum.unitary (win_prep_mat k n Ub)"
  proof -
    have c: "win_prep_mat k n Ub \<in> carrier_mat ?K ?K" unfolding win_prep_mat_def by (rule circuit_mat_carrier) (use ok in blast)
    interpret state_sig "[2 ^ k, n, 2]" .
    have dd: "d = ?K" by (simp add: d_def)
    have "Complex_Matrix.unitary (circuit_mat d (win_prep_gates k n Ub))" by (rule circuit_mat_unitary) (use ok dd in auto)
    hence "Complex_Matrix.unitary (win_prep_mat k n Ub)" unfolding win_prep_mat_def dd .
    hence r: "win_prep_mat k n Ub * Complex_Matrix.adjoint (win_prep_mat k n Ub) = 1\<^sub>m ?K"
      using c unfolding Complex_Matrix.unitary_def inverts_mat_def by simp
    have l: "Complex_Matrix.adjoint (win_prep_mat k n Ub) * win_prep_mat k n Ub = 1\<^sub>m ?K"
      by (rule mat_mult_left_right_inverse[OF c adjoint_dim[OF c] r])
    show ?thesis using c r l unfolding Quantum.unitary_def dagger_adjoint by simp
  qed
  have wc: "\<And>G. G \<in> set (prep_gates k (win_coef (2 ^ k))) \<Longrightarrow> G \<in> carrier_mat (2 ^ k) (2 ^ k)"
    using wp(2) elementary_unitary(1) by blast
  have Wc: "?W \<in> carrier_mat (2 ^ k) (2 ^ k)" by (rule circuit_mat_carrier) (rule wc)
  have c1: "circuit_mat ?K (map (\<lambda>G. G \<Otimes> 1\<^sub>m (n * 2)) (prep_gates k (win_coef (2 ^ k)))) = ?W \<Otimes> 1\<^sub>m (n * 2)"
    by (rule circuit_mat_tensor_right) (use wc m0 in simp_all)
  have "win_prep_mat k n Ub = circuit_mat ?K [prep_gate (2 ^ k) Ub] * circuit_mat ?K (map (\<lambda>G. G \<Otimes> 1\<^sub>m (n * 2)) (prep_gates k (win_coef (2 ^ k))))"
    unfolding win_prep_mat_def win_prep_gates_def by (rule circuit_mat_append) (use wc pc in auto)
  also have "circuit_mat ?K [prep_gate (2 ^ k) Ub] = prep_gate (2 ^ k) Ub" using pc by (simp add: left_mult_one_mat)
  finally have e: "win_prep_mat k n Ub = prep_gate (2 ^ k) Ub * (?W \<Otimes> 1\<^sub>m (n * 2))" unfolding c1 .
  have u0: "unit_vec ?K 0 = tensor_vec (unit_vec (2 ^ k) 0) (unit_vec (n * 2) 0)" using unit_vec_kron[of 0 "2 ^ k" "n * 2"] n0 by simp
  have u1: "unit_vec (n * 2) 0 = tensor_vec (unit_vec n 0) (unit_vec 2 0 :: complex Matrix.vec)" using unit_vec_kron[of 0 n 2] n0 by simp
  have s1: "(?W \<Otimes> 1\<^sub>m (n * 2)) *\<^sub>v unit_vec ?K 0 = tensor_vec (win_state (2 ^ k)) (unit_vec (n * 2) 0)"
  proof -
    have "(?W \<Otimes> 1\<^sub>m (n * 2)) *\<^sub>v tensor_vec (unit_vec (2 ^ k) 0) (unit_vec (n * 2) 0) = tensor_vec (?W *\<^sub>v unit_vec (2 ^ k) 0) (1\<^sub>m (n * 2) *\<^sub>v unit_vec (n * 2) 0)"
      by (rule tensor_mat_vec_mult[OF Wc one_carrier_mat]) simp_all
    thus ?thesis unfolding u0 wp(1) one_mult_mat_vec[OF unit_vec_carrier] .
  qed
  have s2: "prep_gate (2 ^ k) Ub *\<^sub>v tensor_vec (win_state (2 ^ k)) (unit_vec (n * 2) 0) = tensor_vec (win_state (2 ^ k)) (tensor_vec b (unit_vec 2 0))"
  proof -
    have I: "Ub \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (n * 2) (n * 2)" by (rule tensor_carrier[OF Ub(1) one_carrier_mat])
    have "prep_gate (2 ^ k) Ub *\<^sub>v tensor_vec (win_state (2 ^ k)) (unit_vec (n * 2) 0)
          = tensor_vec (1\<^sub>m (2 ^ k) *\<^sub>v win_state (2 ^ k)) ((Ub \<Otimes> 1\<^sub>m 2) *\<^sub>v unit_vec (n * 2) 0)"
      unfolding prep_gate_def by (rule tensor_mat_vec_mult[OF one_carrier_mat I]) simp_all
    also have "(Ub \<Otimes> 1\<^sub>m 2) *\<^sub>v unit_vec (n * 2) 0 = tensor_vec (Ub *\<^sub>v unit_vec n 0) (1\<^sub>m 2 *\<^sub>v unit_vec 2 0)"
      unfolding u1 by (rule tensor_mat_vec_mult[OF Ub(1) one_carrier_mat]) simp_all
    also have "1\<^sub>m (2 ^ k) *\<^sub>v win_state (2 ^ k) = win_state (2 ^ k)" by (rule one_mult_mat_vec) (simp add: carrier_vecI)
    finally show ?thesis using Ub(3) by (simp add: one_mult_mat_vec[OF unit_vec_carrier])
  qed
  show "win_prep_mat k n Ub *\<^sub>v unit_vec ?K 0 = tensor_vec (win_state (2 ^ k)) (tensor_vec b (unit_vec 2 0))"
    unfolding e using assoc_mult_mat_vec[OF pc tensor_carrier[OF Wc one_carrier_mat], of "unit_vec ?K 0"] s1 s2 by simp
qed


subsection \<open>The paper-regime program with all large gates refined\<close>

lemma fref_fourier:
  assumes U: "U = (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m \<or> U = ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)\<^sup>\<dagger>" and m: "0 < m"
    and Wg: "Wg \<in> set (fref k m U)"
  shows "elementary (2 ^ k * m) Wg"
proof -
  have e1: "\<forall>G \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k)))). elementary (2 ^ k * m) G"
    by (rule elementary_map_right[OF qft_inv_circuit(2) m])
  have q2: "\<forall>G \<in> set (qft_circuit k). elementary (2 ^ k) G" using qft_circuit(2) by blast
  have e2: "\<forall>G \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (qft_circuit k)). elementary (2 ^ k * m) G" by (rule elementary_map_right[OF q2 m])
  show ?thesis
  proof (cases "U = (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m")
    case True
    hence fr: "fref k m U = map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k)))" unfolding fref_def by simp
    have "Wg \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (rev (map dagger (qft_circuit k))))" using Wg unfolding fr .
    thus ?thesis using e1 by blast
  next
    case False
    hence "U = ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)\<^sup>\<dagger>" using U by simp
    hence fr: "fref k m U = map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (qft_circuit k)" using False unfolding fref_def by simp
    have "Wg \<in> set (map (\<lambda>G. G \<Otimes> 1\<^sub>m m) (qft_circuit k))" using Wg unfolding fr .
    thus ?thesis using e2 by blast
  qed
qed

lemma fref_other: "U \<noteq> (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m \<Longrightarrow> U \<noteq> ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m m)\<^sup>\<dagger> \<Longrightarrow> fref k m U = [U]"
  by (simp add: fref_def)

lemma pchain_gates: "U \<in> set (qgates N m Oc (pchain K j)) \<Longrightarrow> U = 1\<^sub>m K \<or> (\<exists>P d. U = call_mat N m Oc P d)"
  by (induction j) auto

lemma pchain_adj_gates: "U \<in> set (qgates N m Oc (adj (pchain K j))) \<Longrightarrow> U = 1\<^sub>m K \<or> (\<exists>P d. U = call_mat N m Oc P d)"
  by (induction j) auto

lemma full_prog_gates:
  assumes U: "U \<in> set (qgates N m' Oc (hhl_full_prog A t0 N C Prep))"
  shows "U = Prep \<or> U = 1\<^sub>m (N * (dim_row A * 2)) \<or> U = (fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (dim_row A * 2)
         \<or> U = ((fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (dim_row A * 2))\<^sup>\<dagger>
         \<or> U = hhl_rot_stage A t0 N C \<or> (\<exists>P d. U = call_mat N m' Oc P d)"
proof -
  have "U = Prep \<or> U \<in> set (qgates N m' Oc (pchain (N * (dim_row A * 2)) (N - 1))) \<or> U = (fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (dim_row A * 2)
        \<or> U = hhl_rot_stage A t0 N C \<or> U = ((fourier N)\<^sup>\<dagger> \<Otimes> 1\<^sub>m (dim_row A * 2))\<^sup>\<dagger>
        \<or> U \<in> set (qgates N m' Oc (adj (pchain (N * (dim_row A * 2)) (N - 1))))"
    using U unfolding hhl_full_prog_def HHL_Simulation.hhl_prog_def pe_prog_def by auto
  thus ?thesis using pchain_gates[of U N m' Oc] pchain_adj_gates[of U N m' Oc] by blast
qed


lemma one_elementary:
  assumes K: "0 < K"
  shows "elementary (K * 2) (1\<^sub>m (K * 2))"
  unfolding elementary_def
proof (rule exI[of _ K], rule exI[of _ 1], rule exI[of _ 1], rule exI[of _ "1\<^sub>m 2"], intro conjI)
  have r: "1\<^sub>m 2 \<Otimes> 1\<^sub>m 1 = (1\<^sub>m 2 :: complex Matrix.mat)" by (rule right_tensor_id) (rule one_carrier_mat)
  have t: "1\<^sub>m K \<Otimes> 1\<^sub>m 2 = (1\<^sub>m (K * 2) :: complex Matrix.mat)" by (rule tensor_mat_id)
  show "1\<^sub>m (K * 2) = 1\<^sub>m K \<Otimes> (1\<^sub>m 2 \<Otimes> 1\<^sub>m 1)" unfolding r t ..
  show "K * 2 = K * (2 ^ 1 * 1)" by simp
  show "Quantum.unitary (1\<^sub>m 2 :: complex Matrix.mat)" by (rule id_is_unitary)
qed (use K in simp_all)

definition fine3_gates :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "fine3_gates k n Ub \<theta> Us = concat (map (\<lambda>U. if U = win_prep_mat k n Ub then win_prep_gates k n Ub
        else if U = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta> c)) then ucr_gates k n \<theta> else fref k (n * 2) U) Us)"

lemma fine3_gates_props:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
    and k: "1 \<le> k" and n0: "0 < n" and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
  shows "circuit_mat (2 ^ k * (n * 2)) (fine3_gates k n Ub \<theta> Us) = circuit_mat (2 ^ k * (n * 2)) Us"
    and "\<And>W. W \<in> set (fine3_gates k n Ub \<theta> Us) \<Longrightarrow> W \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary W"
    and "\<And>W. W \<in> set (fine3_gates k n Ub \<theta> Us) \<Longrightarrow>
           elementary (2 ^ k * (n * 2)) W \<or> (\<exists>a. W = cv0 k n (Rot a)) \<or> W = prep_gate (2 ^ k) Ub
           \<or> (W \<in> set Us \<and> W \<noteq> win_prep_mat k n Ub \<and> W \<noteq> ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta> c))
              \<and> W \<noteq> (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2) \<and> W \<noteq> ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2))\<^sup>\<dagger>)"
proof -
  let ?K = "2 ^ k * (n * 2)" and ?RS = "ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta> c))" and ?P = "win_prep_mat k n Ub"
  let ?F = "(fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2)" and ?F' = "((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2))\<^sup>\<dagger>"
  let ?R = "\<lambda>U. if U = ?P then win_prep_gates k n Ub else if U = ?RS then ucr_gates k n \<theta> else fref k (n * 2) U"
  have m0: "0 < n * 2" using n0 by simp
  note wp = win_prep_gates_props[OF k n0 Ub]
  show kind: "\<And>W. W \<in> set (fine3_gates k n Ub \<theta> Us) \<Longrightarrow> elementary ?K W \<or> (\<exists>a. W = cv0 k n (Rot a)) \<or> W = prep_gate (2 ^ k) Ub
                 \<or> (W \<in> set Us \<and> W \<noteq> ?P \<and> W \<noteq> ?RS \<and> W \<noteq> ?F \<and> W \<noteq> ?F')"
  proof -
    fix W assume "W \<in> set (fine3_gates k n Ub \<theta> Us)"
    then obtain U where U: "U \<in> set Us" and w: "W \<in> set (?R U)" unfolding fine3_gates_def set_concat set_map by blast
    show "elementary ?K W \<or> (\<exists>a. W = cv0 k n (Rot a)) \<or> W = prep_gate (2 ^ k) Ub \<or> (W \<in> set Us \<and> W \<noteq> ?P \<and> W \<noteq> ?RS \<and> W \<noteq> ?F \<and> W \<noteq> ?F')"
    proof (cases "U = ?P")
      case True
      hence "W \<in> set (win_prep_gates k n Ub)" using w by simp
      thus ?thesis using wp(2) by blast
    next
      case nP: False
      show ?thesis
      proof (cases "U = ?RS")
        case True
        hence "W \<in> set (ucr_gates k n \<theta>)" using w nP by simp
        thus ?thesis using ucr_gate_kinds[OF _ n0] by blast
      next
        case nR: False
        hence wf: "W \<in> set (fref k (n * 2) U)" using w nP by simp
        show ?thesis
        proof (cases "U = ?F \<or> U = ?F'")
          case True thus ?thesis using fref_fourier[OF True m0 wf] by blast
        next
          case False
          hence "fref k (n * 2) U = [U]" by (intro fref_other) simp_all
          hence "W = U" using wf by simp
          thus ?thesis using U nP nR False by blast
        qed
      qed
    qed
  qed
  have cv: "Quantum.unitary (cv0 k n (Rot a)) \<and> cv0 k n (Rot a) \<in> carrier_mat ?K ?K" for a
    using cv0_unitary[OF Rot_unitary Rot_carrier] by (simp add: cv0_def)
  have pg: "prep_gate (2 ^ k) Ub \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary (prep_gate (2 ^ k) Ub)"
    using wp(1)[of "prep_gate (2 ^ k) Ub"] by (simp add: win_prep_gates_def)
  show ok: "\<And>W. W \<in> set (fine3_gates k n Ub \<theta> Us) \<Longrightarrow> W \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary W"
  proof -
    fix W assume w: "W \<in> set (fine3_gates k n Ub \<theta> Us)"
    note kd = kind[OF w]
    show "W \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary W"
    proof (rule disjE[OF kd])
      assume "elementary ?K W" thus ?thesis using elementary_unitary unitary_bridge by blast
    next
      assume r: "(\<exists>a. W = cv0 k n (Rot a)) \<or> W = prep_gate (2 ^ k) Ub \<or> (W \<in> set Us \<and> W \<noteq> ?P \<and> W \<noteq> ?RS \<and> W \<noteq> ?F \<and> W \<noteq> ?F')"
      show ?thesis
      proof (rule disjE[OF r])
        assume "\<exists>a. W = cv0 k n (Rot a)"
        then obtain a where Wa: "W = cv0 k n (Rot a)" by blast
        thus ?thesis using cv[of a] unitary_bridge by blast
      next
        assume "W = prep_gate (2 ^ k) Ub \<or> (W \<in> set Us \<and> W \<noteq> ?P \<and> W \<noteq> ?RS \<and> W \<noteq> ?F \<and> W \<noteq> ?F')"
        thus ?thesis using pg Us by blast
      qed
    qed
  qed
  have "circuit_mat ?K (fine3_gates k n Ub \<theta> Us) = circuit_mat ?K (map (circuit_mat ?K) (map ?R Us))"
    unfolding fine3_gates_def by (rule circuit_mat_concat) (use ok in \<open>auto simp: fine3_gates_def\<close>)
  also have "map (circuit_mat ?K) (map ?R Us) = Us"
    unfolding map_map comp_def
  proof (rule map_idI)
    fix U assume U: "U \<in> set Us"
    show "circuit_mat ?K (?R U) = U"
    proof (cases "U = ?P")
      case True thus ?thesis by (simp add: win_prep_mat_def)
    next
      case nP: False
      show ?thesis
      proof (cases "U = ?RS")
        case True thus ?thesis using nP ucr_circuit[OF n0] by simp
      next
        case False thus ?thesis using nP fref_props(1)[OF conjunct1[OF Us[OF U]] m0] by simp
      qed
    qed
  qed
  finally show "circuit_mat ?K (fine3_gates k n Ub \<theta> Us) = circuit_mat ?K Us" .
qed


text \<open>The paper's regime as programs in which every gate is elementary, a rotation of the ancilla
controlled by the last clock qubit, the preparation of $\ket b$, or an oracle call.\<close>

theorem hhl_apx_fine3:
  fixes A V Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C \<theta> lmin \<epsilon> \<eta> :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and k: "1 \<le> k"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real (2 ^ k)"
      and V: "V \<in> carrier_mat n n" "Quantum.unitary V" and Vc: "op_close n \<eta> V (evolution A t0)" and eta: "0 \<le> \<eta>"
      and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
      and small: "\<epsilon> + 2 * real (2 ^ k - 1) * \<eta> \<le> C * t0 / pi"
  defines "K \<equiv> 2 ^ k * (n * 2)" and "\<theta>s \<equiv> \<lambda>c. arcsin (clamp (C / reg_eig t0 (2 ^ k) c))"
    and "Gs \<equiv> fine3_gates k n Ub (\<lambda>c. arcsin (clamp (C / reg_eig t0 (2 ^ k) c))) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k n Ub)))"
  shows "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    and "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (rus_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    and "\<And>U. U \<in> set Gs \<Longrightarrow> elementary K U \<or> (\<exists>a. U = cv0 k n (Rot a)) \<or> U = prep_gate (2 ^ k) Ub
           \<or> (\<exists>P d. U = call_mat (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) P d)"
proof -
  have N: "2 \<le> (2::nat) ^ k" using power_increasing[of 1 k "2::nat"] k by simp
  have n0: "0 < n" by (rule norm1_dim_pos[OF b])
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = K" by (simp add: d_def K_def)
  note wp = win_prep_gates_props[OF k n0 Ub]
  note P = wp(3,4,5)
  note ab = apx_basics[OF A t0 N C th lmin spec b e NQ V Vc eta P small]
  let ?Us = "qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k n Ub))"
  have g: "gates_ok K (hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k n Ub))" unfolding K_def by (rule ab(4))
  have ok: "\<And>U. U \<in> set ?Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
    using qgates_ok[OF ab(2,3), where c = "hhl_full_prog A t0 (2 ^ k) C (win_prep_mat k n Ub)"] g by (simp add: K_def)
  note f = fine3_gates_props[where \<theta> = \<theta>s and Us = ?Us, OF ok k n0 Ub, unfolded \<theta>s_def]
  have okd: "\<And>U. U \<in> set ?Us \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" using ok dd K_def by simp
  have okG: "\<And>U. U \<in> set Gs \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U" using f(2) dd K_def Gs_def by simp
  have circ: "circuit_mat d Gs = circuit_mat d ?Us" unfolding Gs_def dd K_def by (rule f(1))
  have d0: "0 < d" using ab(1) dd K_def by simp
  have Mc: "anc_proj d 0 \<in> carrier_mat d d" by simp
  show "hoare_total_correct (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
  proof -
    have h: "hoare_total_correct (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
           (prog_meas d (anc_proj d) ?Us) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
      unfolding dd K_def by (rule hhl_apx_program[OF A t0 N C th lmin spec b e NQ V Vc eta P small])
    show ?thesis using meas_transfer(1)[OF d0 okd okG circ Mc h] unfolding dd .
  qed
  show "hoare_total_correct (complex_of_real (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (rus_meas K (anc_proj K) Gs) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
  proof -
    have h: "hoare_total_correct (complex_of_real (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m K)
           (rus_meas d (anc_proj d) ?Us) (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
      unfolding dd K_def by (rule hhl_apx_rus[OF A t0 N C th lmin spec b e NQ V Vc eta P small])
    show ?thesis using meas_transfer(2)[OF d0 okd okG circ Mc h] unfolding dd .
  qed
  show "\<And>U. U \<in> set Gs \<Longrightarrow> elementary K U \<or> (\<exists>a. U = cv0 k n (Rot a)) \<or> U = prep_gate (2 ^ k) Ub
           \<or> (\<exists>P d. U = call_mat (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) P d)"
  proof -
    fix U assume U: "U \<in> set Gs"
    have rs: "hhl_rot_stage A t0 (2 ^ k) C = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (arcsin (clamp (C / reg_eig t0 (2 ^ k) c))))"
      by (rule rot_stage_ucr) (use A(1) in simp)
    have nA: "dim_row A = n" using A(1) by simp
    have kd: "elementary K U \<or> (\<exists>a. U = cv0 k n (Rot a)) \<or> U = prep_gate (2 ^ k) Ub
           \<or> (U \<in> set ?Us \<and> U \<noteq> win_prep_mat k n Ub \<and> U \<noteq> ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (arcsin (clamp (C / reg_eig t0 (2 ^ k) c))))
              \<and> U \<noteq> (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2) \<and> U \<noteq> ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2))\<^sup>\<dagger>)"
      using f(3)[OF _ U[unfolded Gs_def]] unfolding K_def by blast
    have one: "elementary K (1\<^sub>m (2 ^ k * (n * 2)))"
      unfolding K_def using one_elementary[of "2 ^ k * n"] n0 by (simp add: Groups.mult_ac)
    show "elementary K U \<or> (\<exists>a. U = cv0 k n (Rot a)) \<or> U = prep_gate (2 ^ k) Ub
           \<or> (\<exists>P d. U = call_mat (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) P d)"
    proof (rule disjE[OF kd])
      assume "elementary K U" thus ?thesis by blast
    next
      assume r: "(\<exists>a. U = cv0 k n (Rot a)) \<or> U = prep_gate (2 ^ k) Ub
           \<or> (U \<in> set ?Us \<and> U \<noteq> win_prep_mat k n Ub \<and> U \<noteq> ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (arcsin (clamp (C / reg_eig t0 (2 ^ k) c))))
              \<and> U \<noteq> (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2) \<and> U \<noteq> ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2))\<^sup>\<dagger>)"
      show ?thesis
      proof (rule disjE[OF r])
        assume "\<exists>a. U = cv0 k n (Rot a)" thus ?thesis by blast
      next
        assume r2: "U = prep_gate (2 ^ k) Ub
           \<or> (U \<in> set ?Us \<and> U \<noteq> win_prep_mat k n Ub \<and> U \<noteq> ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (arcsin (clamp (C / reg_eig t0 (2 ^ k) c))))
              \<and> U \<noteq> (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2) \<and> U \<noteq> ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2))\<^sup>\<dagger>)"
        show ?thesis
        proof (rule disjE[OF r2])
          assume "U = prep_gate (2 ^ k) Ub" thus ?thesis by blast
        next
          assume h: "U \<in> set ?Us \<and> U \<noteq> win_prep_mat k n Ub \<and> U \<noteq> ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (arcsin (clamp (C / reg_eig t0 (2 ^ k) c))))
              \<and> U \<noteq> (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2) \<and> U \<noteq> ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (n * 2))\<^sup>\<dagger>"
          have "U = win_prep_mat k n Ub \<or> U = 1\<^sub>m (2 ^ k * (dim_row A * 2)) \<or> U = (fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (dim_row A * 2)
                \<or> U = ((fourier (2 ^ k))\<^sup>\<dagger> \<Otimes> 1\<^sub>m (dim_row A * 2))\<^sup>\<dagger> \<or> U = hhl_rot_stage A t0 (2 ^ k) C
                \<or> (\<exists>P d. U = call_mat (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) P d)"
            by (rule full_prog_gates) (use h in blast)
          thus ?thesis using h one unfolding nA rs by blast
        qed
      qed
    qed
  qed
qed

end
