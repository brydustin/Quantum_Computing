theory HHL_Uniform_Rotation
  imports HHL_Gate_Refinements
begin

section \<open>The eigenvalue-controlled rotation in elementary gates\<close>

text \<open>The rotation stage $\sum_c\ket c\bra c\otimes I\otimes R(\theta_c)$ is a uniformly controlled
rotation.  With the Walsh--Hadamard coefficients $\psi_S=2^{-k}\sum_c\theta_c(-1)^{S\cdot c}$ one has
$\theta_c=\sum_S\psi_S-2\sum_{S\ne\emptyset}\psi_S[S\cdot c\text{ odd}]$ (\<open>walsh_inversion\<close>,
\<open>ucr_angle\<close>), so the stage is one rotation of the ancilla followed by $2^k-1$ parity-controlled
rotations (\<open>ucr_circuit\<close>).  Each parity is computed into the last clock qubit by a chain of
nearest-neighbour CNOT and SWAP gates (\<open>parity_chain_correct\<close>), which are elementary gates
(\<open>cgate_elementary\<close>); the rotation is then controlled by that qubit, and the chain is undone
(\<open>pblock_circuit\<close>).  The HHL program with this stage (\<open>hhl_fine_correct_total\<close>) has only
elementary gates, oracle calls, the preparation of $\ket b$ and rotations of the ancilla controlled
by the last clock qubit (\<open>hhl_fine_gate_kinds\<close>); the same holds for the paper-regime and
amplified circuits (\<open>hhl_apx_fine2\<close>).\<close>


subsection \<open>Lifting a permutation of two adjacent bits\<close>

definition lift2 :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lift2 g j c = c div (4 * 2 ^ j) * (4 * 2 ^ j) + g (c div 2 ^ j mod 4) * 2 ^ j + c mod 2 ^ j"

lemma lift2_Suc: "lift2 g (Suc j) c = 2 * lift2 g j (c div 2) + c mod 2"
proof -
  have a: "c div (4 * 2 ^ Suc j) = c div 2 div (4 * 2 ^ j)"
  proof -
    have "(4::nat) * 2 ^ Suc j = 2 * (4 * 2 ^ j)" by simp
    thus ?thesis by (simp only: div_mult2_eq)
  qed
  have b: "c div 2 ^ Suc j = c div 2 div 2 ^ j" by (simp add: div_mult2_eq)
  have m: "c mod 2 ^ Suc j = 2 * (c div 2 mod 2 ^ j) + c mod 2" by (simp add: mod_mult2_eq Groups.mult_ac)
  show ?thesis unfolding lift2_def a b m by (simp add: algebra_simps)
qed

lemma lift2_0: "lift2 g 0 c = c div 4 * 4 + g (c mod 4)" by (simp add: lift2_def)

lemma lift2_lt:
  assumes g: "\<And>x. x < 4 \<Longrightarrow> g x < 4" and j: "j + 2 \<le> k" and c: "c < 2 ^ k"
  shows "lift2 g j c < 2 ^ k"
proof -
  let ?b = "2 ^ j :: nat"
  have b0: "0 < ?b" by simp
  have k: "2 ^ k = 2 ^ (k - (j + 2)) * (4 * ?b)"
  proof -
    have e: "k = (k - (j + 2)) + (j + 2)" using j by simp
    have "(2::nat) ^ k = 2 ^ ((k - (j + 2)) + (j + 2))" by (subst e[symmetric]) (rule refl)
    also have "\<dots> = 2 ^ (k - (j + 2)) * 2 ^ (j + 2)" by (rule power_add)
    finally show ?thesis by (simp add: Groups.mult_ac)
  qed
  have q: "c div (4 * ?b) < 2 ^ (k - (j + 2))" using c by (simp add: k less_mult_imp_div_less)
  have "g (c div ?b mod 4) * ?b + c mod ?b < 4 * ?b"
  proof -
    have "g (c div ?b mod 4) \<le> 3" using g[of "c div ?b mod 4"] by simp
    hence a: "g (c div ?b mod 4) * ?b \<le> 3 * ?b" by (rule mult_le_mono1)
    have m: "c mod ?b < ?b" by simp
    show ?thesis using a m by linarith
  qed
  hence "lift2 g j c < c div (4 * ?b) * (4 * ?b) + 4 * ?b" unfolding lift2_def by simp
  also have "\<dots> = Suc (c div (4 * ?b)) * (4 * ?b)" by simp
  also have "\<dots> \<le> 2 ^ (k - (j + 2)) * (4 * ?b)" using q by (intro mult_le_mono1) simp
  finally show ?thesis using k by simp
qed


lemma digits3:
  fixes r X Y Z b :: nat
  assumes b: "0 < b" and Y: "Y < 4" and Z: "Z < b"
  shows "r = X * (4 * b) + Y * b + Z \<longleftrightarrow> r div (4 * b) = X \<and> r div b mod 4 = Y \<and> r mod b = Z"
proof
  assume r: "r = X * (4 * b) + Y * b + Z"
  have e: "r = (X * 4 + Y) * b + Z" unfolding r by (simp add: algebra_simps)
  have d: "r div b = X * 4 + Y" unfolding e using Z b by simp
  show "r div (4 * b) = X \<and> r div b mod 4 = Y \<and> r mod b = Z"
  proof (intro conjI)
    show "r div (4 * b) = X" using d Y by (simp add: div_mult2_eq Groups.mult.commute[of 4 b])
    show "r div b mod 4 = Y" using d Y by simp
    show "r mod b = Z" unfolding e using Z by simp
  qed
next
  assume h: "r div (4 * b) = X \<and> r div b mod 4 = Y \<and> r mod b = Z"
  have "r = r div (4 * b) * (4 * b) + r mod (4 * b)" by (rule div_mult_mod_eq[symmetric])
  also have "r mod (4 * b) = b * (r div b mod 4) + r mod b" by (simp add: mod_mult2_eq Groups.mult.commute[of 4 b])
  finally show "r = X * (4 * b) + Y * b + Z" using h by (simp add: Groups.mult_ac)
qed

lemma pmat_lift2:
  assumes g: "\<And>x. x < 4 \<Longrightarrow> g x < 4" and j: "j + 2 \<le> k"
  shows "pmat (2 ^ k) (lift2 g j) = 1\<^sub>m (2 ^ (k - (j + 2))) \<Otimes> (pmat 4 g \<Otimes> 1\<^sub>m (2 ^ j))"
proof -
  let ?a = "2 ^ (k - (j + 2)) :: nat" and ?b = "2 ^ j :: nat"
  have k: "(2::nat) ^ k = ?a * (4 * ?b)"
  proof -
    have e: "k = (k - (j + 2)) + (j + 2)" using j by simp
    have "(2::nat) ^ k = 2 ^ ((k - (j + 2)) + (j + 2))" by (subst e[symmetric]) (rule refl)
    also have "\<dots> = 2 ^ (k - (j + 2)) * 2 ^ (j + 2)" by (rule power_add)
    finally show ?thesis by (simp add: Groups.mult_ac)
  qed
  have b0: "0 < ?b" by simp
  show ?thesis
  proof (rule eq_matI)
    fix r t assume "r < dim_row (1\<^sub>m ?a \<Otimes> (pmat 4 g \<Otimes> 1\<^sub>m ?b))" "t < dim_col (1\<^sub>m ?a \<Otimes> (pmat 4 g \<Otimes> 1\<^sub>m ?b))"
    hence rt: "r < ?a * (4 * ?b)" "t < ?a * (4 * ?b)" by simp_all
    have m4: "r mod (4 * ?b) < 4 * ?b" "t mod (4 * ?b) < 4 * ?b" using b0 by simp_all
    have e1: "(pmat 4 g \<Otimes> 1\<^sub>m ?b) $$ (r mod (4 * ?b), t mod (4 * ?b))
              = pmat 4 g $$ (r mod (4 * ?b) div ?b, t mod (4 * ?b) div ?b) * 1\<^sub>m ?b $$ (r mod (4 * ?b) mod ?b, t mod (4 * ?b) mod ?b)"
      using index_tensor_mat[of "pmat 4 g" 4 4 "1\<^sub>m ?b" ?b ?b "r mod (4 * ?b)" "t mod (4 * ?b)"] m4 b0 by simp
    have md: "x mod (4 * ?b) div ?b = x div ?b mod 4" "x mod (4 * ?b) mod ?b = x mod ?b" for x
      by (simp_all add: mod_mult2_eq Groups.mult.commute[of 4 "?b"] div_mult2_eq)
    have q: "r div ?b mod 4 < 4" "t div ?b mod 4 < 4" by simp_all
    have "(1\<^sub>m ?a \<Otimes> (pmat 4 g \<Otimes> 1\<^sub>m ?b)) $$ (r, t)
          = 1\<^sub>m ?a $$ (r div (4 * ?b), t div (4 * ?b)) * (pmat 4 g \<Otimes> 1\<^sub>m ?b) $$ (r mod (4 * ?b), t mod (4 * ?b))"
      using index_tensor_mat[of "1\<^sub>m ?a" ?a ?a "pmat 4 g \<Otimes> 1\<^sub>m ?b" "4 * ?b" "4 * ?b" r t] rt b0 by simp
    also have "\<dots> = (if r div (4 * ?b) = t div (4 * ?b) \<and> r div ?b mod 4 = g (t div ?b mod 4) \<and> r mod ?b = t mod ?b then 1 else 0)"
    proof -
      have da: "r div (4 * ?b) < ?a" "t div (4 * ?b) < ?a" using rt by (simp_all add: less_mult_imp_div_less)
      have i1: "1\<^sub>m ?a $$ (r div (4 * ?b), t div (4 * ?b)) = (if r div (4 * ?b) = t div (4 * ?b) then 1 else (0::complex))"
        using da by simp
      have i2: "pmat 4 g $$ (r div ?b mod 4, t div ?b mod 4) = (if r div ?b mod 4 = g (t div ?b mod 4) then 1 else 0)"
        using q by (simp add: pmat_def)
      have i3: "1\<^sub>m ?b $$ (r mod ?b, t mod ?b) = (if r mod ?b = t mod ?b then 1 else (0::complex))" using b0 by simp
      show ?thesis unfolding e1 md i1 i2 i3 by simp
    qed
    also have "\<dots> = (if r = lift2 g j t then 1 else 0)"
      using digits3[where r = r and X = "t div (4 * ?b)" and Y = "g (t div ?b mod 4)" and Z = "t mod ?b", OF b0 g[OF q(2)]] b0
      by (simp add: lift2_def)
    also have "\<dots> = pmat (2 ^ k) (lift2 g j) $$ (r, t)" using rt k by (simp add: pmat_def)
    finally show "pmat (2 ^ k) (lift2 g j) $$ (r, t) = (1\<^sub>m ?a \<Otimes> (pmat 4 g \<Otimes> 1\<^sub>m ?b)) $$ (r, t)" by simp
  qed (simp_all add: k)
qed


lemma lift2_digits:
  assumes g: "\<And>x. x < 4 \<Longrightarrow> g x < 4"
  shows "lift2 g j c div (4 * 2 ^ j) = c div (4 * 2 ^ j)" "lift2 g j c div 2 ^ j mod 4 = g (c div 2 ^ j mod 4)"
    "lift2 g j c mod 2 ^ j = c mod 2 ^ j"
proof -
  have b0: "0 < (2::nat) ^ j" by simp
  have e: "lift2 g j c = c div (4 * 2 ^ j) * (4 * 2 ^ j) + g (c div 2 ^ j mod 4) * 2 ^ j + c mod 2 ^ j"
    by (simp only: lift2_def)
  have "lift2 g j c div (4 * 2 ^ j) = c div (4 * 2 ^ j) \<and> lift2 g j c div 2 ^ j mod 4 = g (c div 2 ^ j mod 4) \<and> lift2 g j c mod 2 ^ j = c mod 2 ^ j"
    by (rule digits3[where r = "lift2 g j c" and X = "c div (4 * 2 ^ j)" and Y = "g (c div 2 ^ j mod 4)" and Z = "c mod 2 ^ j", OF b0 g, THEN iffD1, OF _ _ e]) simp_all
  thus "lift2 g j c div (4 * 2 ^ j) = c div (4 * 2 ^ j)" "lift2 g j c div 2 ^ j mod 4 = g (c div 2 ^ j mod 4)"
    "lift2 g j c mod 2 ^ j = c mod 2 ^ j" by simp_all
qed

lemma lift2_invol:
  assumes g: "\<And>x. x < 4 \<Longrightarrow> g x < 4" "\<And>x. x < 4 \<Longrightarrow> g (g x) = x"
  shows "lift2 g j (lift2 g j c) = c"
proof -
  have d1: "lift2 g j c div (4 * 2 ^ j) = c div (4 * 2 ^ j)" by (rule lift2_digits(1)) (use g(1) in blast)
  have d2: "lift2 g j c div 2 ^ j mod 4 = g (c div 2 ^ j mod 4)" by (rule lift2_digits(2)) (use g(1) in blast)
  have d3: "lift2 g j c mod 2 ^ j = c mod 2 ^ j" by (rule lift2_digits(3)) (use g(1) in blast)
  have gg: "g (g (c div 2 ^ j mod 4)) = c div 2 ^ j mod 4" by (rule g(2)) simp
  have "lift2 g j (lift2 g j c) = c div (4 * 2 ^ j) * (4 * 2 ^ j) + c div 2 ^ j mod 4 * 2 ^ j + c mod 2 ^ j"
    by (simp only: lift2_def[of g j "lift2 g j c"] d1 d2 d3 gg)
  also have "\<dots> = c"
    by (rule digits3[where r = c and X = "c div (4 * 2 ^ j)" and Y = "c div 2 ^ j mod 4" and Z = "c mod 2 ^ j" and b = "2 ^ j", THEN iffD2, symmetric]) simp_all
  finally show ?thesis .
qed

subsection \<open>Rotations\<close>

definition Rot :: "real \<Rightarrow> complex Matrix.mat" where
  "Rot a = Matrix.mat 2 2 (\<lambda>(i, j). if i = j then complex_of_real (cos a)
                                   else if i = 1 then complex_of_real (sin a) else - complex_of_real (sin a))"

lemma Rot_carrier [simp]: "Rot a \<in> carrier_mat 2 2" by (simp add: Rot_def)

lemma dim_Rot [simp]: "dim_row (Rot a) = 2" "dim_col (Rot a) = 2" by (simp_all add: Rot_def)

lemma Rot_add: "Rot a * Rot b = Rot (a + b)"
  by (rule eq_matI) (auto simp: Rot_def scalar_prod_def numeral_2_eq_2 atLeast0LessThan lessThan_Suc cos_add sin_add algebra_simps less_Suc_eq)

lemma Rot_zero: "Rot 0 = 1\<^sub>m 2" by (rule eq_matI) (auto simp: Rot_def less_Suc_eq numeral_2_eq_2)

lemma Rot_unitary: "Quantum.unitary (Rot a)"
proof -
  have d: "(Rot a)\<^sup>\<dagger> = Rot (- a)" by (rule eq_matI) (auto simp: Rot_def dagger_def less_Suc_eq numeral_2_eq_2)
  show ?thesis unfolding Quantum.unitary_def d using Rot_add[of a "- a"] Rot_add[of "- a" a] by (simp add: Rot_zero)
qed

lemma rot_Rot: "\<bar>c\<bar> \<le> 1 \<Longrightarrow> rot c = Rot (arcsin c)"
  by (rule eq_matI) (auto simp: rot_def Rot_def cos_arcsin sin_arcsin less_Suc_eq numeral_2_eq_2)

subsection \<open>Parity of a set of clock bits, accumulated in the last clock qubit\<close>

abbreviation gc :: "nat \<Rightarrow> nat" where "gc \<equiv> Transposition.transpose 2 3"
abbreviation gs :: "nat \<Rightarrow> nat" where "gs \<equiv> Transposition.transpose 1 2"

lemma gc_props: "x < 4 \<Longrightarrow> gc x < 4" "x < 4 \<Longrightarrow> gc (gc x) = x" by (auto simp: Transposition.transpose_def)
lemma gs_props: "x < 4 \<Longrightarrow> gs x < 4" "x < 4 \<Longrightarrow> gs (gs x) = x" by (auto simp: Transposition.transpose_def)

definition opg :: "bool \<Rightarrow> nat \<Rightarrow> nat" where "opg b = (if b then gc else gs)"

lemma opg_props: "x < 4 \<Longrightarrow> opg b x < 4" "x < 4 \<Longrightarrow> opg b (opg b x) = x"
  by (auto simp: opg_def Transposition.transpose_def)

definition opf :: "bool \<times> nat \<Rightarrow> nat \<Rightarrow> nat" where "opf op = lift2 (opg (fst op)) (snd op)"

fun apply_ops :: "(bool \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat" where
  "apply_ops [] c = c"
| "apply_ops (op # os) c = apply_ops os (opf op c)"

fun par :: "bool list \<Rightarrow> nat \<Rightarrow> bool" where
  "par [] c = False"
| "par (m # ms) c = ((m \<and> odd c) \<noteq> par ms (c div 2))"

fun parity_chain :: "bool list \<Rightarrow> (bool \<times> nat) list" where
  "parity_chain [] = []"
| "parity_chain (m # ms) = (if True \<in> set ms then map (\<lambda>(b, j). (b, Suc j)) (parity_chain ms) @ [(m, 0)] else [])"

lemma par_false: "True \<notin> set ms \<Longrightarrow> par ms c = False"
  by (induction ms arbitrary: c) auto

lemma apply_ops_shift: "apply_ops (map (\<lambda>(b, j). (b, Suc j)) os) c = 2 * apply_ops os (c div 2) + c mod 2"
proof (induction os arbitrary: c)
  case Nil show ?case by simp
next
  case (Cons op os)
  obtain b j where op: "op = (b, j)" by (cases op)
  have "opf (b, Suc j) c = 2 * opf (b, j) (c div 2) + c mod 2" unfolding opf_def by (simp add: lift2_Suc)
  thus ?case using Cons.IH[of "opf (b, Suc j) c"] op by simp
qed

lemma apply_ops_snoc: "apply_ops (os @ [op]) c = opf op (apply_ops os c)"
  by (induction os arbitrary: c) auto

lemma opg_low:
  assumes a: "a < 2" and b: "b < 2"
  shows "odd (opg True (2 * a + b)) = (odd b \<noteq> odd a)" "odd (opg False (2 * a + b)) = odd a"
proof -
  have "a = 0 \<or> a = 1" "b = 0 \<or> b = 1" using a b by auto
  thus "odd (opg True (2 * a + b)) = (odd b \<noteq> odd a)" "odd (opg False (2 * a + b)) = odd a"
    by (auto simp: opg_def Transposition.transpose_def)
qed

lemma mod4_split: "(2 * x + y) mod 4 = 2 * (x mod 2) + y" if "y < 2" for x y :: nat
proof -
  have x: "x = 2 * (x div 2) + x mod 2" by simp
  have e: "2 * x + y = (2 * (x mod 2) + y) + 4 * (x div 2)" using x by linarith
  have l: "2 * (x mod 2) + y < 4" using that by simp
  show ?thesis unfolding e mod_mult_self2 using l by (rule mod_less)
qed

lemma parity_chain_correct: "True \<in> set ms \<Longrightarrow> odd (apply_ops (parity_chain ms) c) = par ms c"
proof (induction ms arbitrary: c)
  case Nil thus ?case by simp
next
  case (Cons m ms)
  show ?case
  proof (cases "True \<in> set ms")
    case True
    let ?y = "2 * apply_ops (parity_chain ms) (c div 2) + c mod 2"
    have IH: "odd (apply_ops (parity_chain ms) (c div 2)) = par ms (c div 2)" by (rule Cons.IH[OF True])
    have e: "apply_ops (parity_chain (m # ms)) c = opf (m, 0) ?y" using True by (simp add: apply_ops_snoc apply_ops_shift)
    have y4: "?y mod 4 = 2 * (apply_ops (parity_chain ms) (c div 2) mod 2) + c mod 2" by (rule mod4_split) simp
    have "odd (opf (m, 0) ?y) = odd (opg m (?y mod 4))" by (simp add: opf_def lift2_0)
    also have "\<dots> = par (m # ms) c"
    proof (cases m)
      case True thus ?thesis unfolding y4 using opg_low(1)[of "apply_ops (parity_chain ms) (c div 2) mod 2" "c mod 2"] IH by simp
    next
      case False thus ?thesis unfolding y4 using opg_low(2)[of "apply_ops (parity_chain ms) (c div 2) mod 2" "c mod 2"] IH by simp
    qed
    finally show ?thesis using e by simp
  next
    case False
    hence m: "m = True" using Cons.prems by auto
    thus ?thesis using False par_false[OF False] by simp
  qed
qed

lemma parity_chain_pos: "(b, j) \<in> set (parity_chain ms) \<Longrightarrow> j + 2 \<le> length ms"
proof (induction ms arbitrary: b j)
  case Nil thus ?case by simp
next
  case (Cons m ms)
  show ?case
  proof (cases "True \<in> set ms")
    case True
    hence "(b, j) \<in> set (map (\<lambda>(b, j). (b, Suc j)) (parity_chain ms)) \<or> (b, j) = (m, 0)" using Cons.prems by auto
    thus ?thesis
    proof
      assume "(b, j) \<in> set (map (\<lambda>(b, j). (b, Suc j)) (parity_chain ms))"
      then obtain j' where "(b, j') \<in> set (parity_chain ms)" "j = Suc j'" by auto
      thus ?thesis using Cons.IH by fastforce
    next
      assume "(b, j) = (m, 0)"
      moreover have "ms \<noteq> []" using True by auto
      ultimately show ?thesis by (cases ms) auto
    qed
  next
    case False thus ?thesis using Cons.prems by simp
  qed
qed


subsection \<open>Clock gates\<close>

lemma opf_lt: "j + 2 \<le> k \<Longrightarrow> c < 2 ^ k \<Longrightarrow> opf (b, j) c < 2 ^ k"
  unfolding opf_def by (simp add: lift2_lt opg_props)

lemma opf_invol: "opf op (opf op c) = c"
  unfolding opf_def by (rule lift2_invol) (simp_all add: opg_props)

lemma apply_ops_lt: "(\<And>b j. (b, j) \<in> set os \<Longrightarrow> j + 2 \<le> k) \<Longrightarrow> c < 2 ^ k \<Longrightarrow> apply_ops os c < 2 ^ k"
proof (induction os arbitrary: c)
  case Nil thus ?case by simp
next
  case (Cons op os)
  obtain b j where op: "op = (b, j)" by (cases op)
  have "opf op c < 2 ^ k" unfolding op by (rule opf_lt) (use Cons.prems op in auto)
  moreover have "\<And>b j. (b, j) \<in> set os \<Longrightarrow> j + 2 \<le> k" using Cons.prems(1) by (metis list.set_intros(2))
  ultimately show ?case using Cons.IH[of "opf op c"] by simp
qed

lemma apply_ops_rev: "apply_ops (rev os) (apply_ops os c) = c"
proof (induction os arbitrary: c)
  case Nil thus ?case by simp
next
  case (Cons op os)
  have "apply_ops (rev (op # os)) (apply_ops (op # os) c) = opf op (apply_ops (rev os) (apply_ops os (opf op c)))"
    by (simp add: apply_ops_snoc)
  also have "\<dots> = c" using Cons.IH opf_invol by simp
  finally show ?case .
qed

definition cgate :: "nat \<Rightarrow> nat \<Rightarrow> bool \<times> nat \<Rightarrow> complex Matrix.mat" where
  "cgate k m op = pmat (2 ^ k) (opf op) \<Otimes> 1\<^sub>m m"

lemma circuit_cgates:
  assumes os: "\<And>b j. (b, j) \<in> set os \<Longrightarrow> j + 2 \<le> k" and m: "0 < m"
  shows "circuit_mat (2 ^ k * m) (map (cgate k m) os) = pmat (2 ^ k) (apply_ops os) \<Otimes> 1\<^sub>m m"
  using os
proof (induction os)
  case Nil
  show ?case using tensor_mat_id[of "2 ^ k" m] by (simp add: pmat_id[unfolded id_def, symmetric])
next
  case (Cons op os)
  obtain b j where op: "op = (b, j)" by (cases op)
  have tl: "\<And>b j. (b, j) \<in> set os \<Longrightarrow> j + 2 \<le> k" using Cons.prems by (metis list.set_intros(2))
  have IH: "circuit_mat (2 ^ k * m) (map (cgate k m) os) = pmat (2 ^ k) (apply_ops os) \<Otimes> 1\<^sub>m m"
    by (rule Cons.IH) (rule tl)
  have r: "\<And>t. t < 2 ^ k \<Longrightarrow> opf op t < 2 ^ k" unfolding op by (rule opf_lt) (use Cons.prems op in auto)
  have "circuit_mat (2 ^ k * m) (map (cgate k m) (op # os)) = (pmat (2 ^ k) (apply_ops os) \<Otimes> 1\<^sub>m m) * (pmat (2 ^ k) (opf op) \<Otimes> 1\<^sub>m m)"
    by (simp add: IH cgate_def)
  also have "\<dots> = (pmat (2 ^ k) (apply_ops os) * pmat (2 ^ k) (opf op)) \<Otimes> (1\<^sub>m m * 1\<^sub>m m)"
    by (rule mult_distr_tensor[symmetric]) (use m in simp_all)
  also have "\<dots> = pmat (2 ^ k) (apply_ops (op # os)) \<Otimes> 1\<^sub>m m"
  proof -
    have "pmat (2 ^ k) (apply_ops os) * pmat (2 ^ k) (opf op) = pmat (2 ^ k) (apply_ops os \<circ> opf op)" by (rule pmat_mult) (rule r)
    moreover have "apply_ops os \<circ> opf op = apply_ops (op # os)" by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  finally show ?case .
qed


lemma cgate_elementary:
  assumes j: "j + 2 \<le> k" and m: "0 < m"
  shows "elementary (2 ^ k * m) (cgate k m (b, j))"
proof -
  let ?a = "2 ^ (k - (j + 2)) :: nat" and ?G = "pmat 4 (opg b)"
  have k2: "(2::nat) ^ k = ?a * (4 * 2 ^ j)"
  proof -
    have e: "k = (k - (j + 2)) + (j + 2)" using j by simp
    have "(2::nat) ^ k = 2 ^ ((k - (j + 2)) + (j + 2))" by (subst e[symmetric]) (rule refl)
    also have "\<dots> = 2 ^ (k - (j + 2)) * 2 ^ (j + 2)" by (rule power_add)
    finally show ?thesis by (simp add: Groups.mult_ac)
  qed
  have "cgate k m (b, j) = (1\<^sub>m ?a \<Otimes> (?G \<Otimes> 1\<^sub>m (2 ^ j))) \<Otimes> 1\<^sub>m m"
    unfolding cgate_def opf_def using pmat_lift2[of "opg b" j k] j by (simp add: opg_props)
  also have "\<dots> = 1\<^sub>m ?a \<Otimes> ((?G \<Otimes> 1\<^sub>m (2 ^ j)) \<Otimes> 1\<^sub>m m)" by (rule tensor_mat_is_assoc[symmetric])
  also have "(?G \<Otimes> 1\<^sub>m (2 ^ j)) \<Otimes> 1\<^sub>m m = ?G \<Otimes> 1\<^sub>m (2 ^ j * m)"
    using tensor_mat_is_assoc[of ?G "1\<^sub>m (2 ^ j)" "1\<^sub>m m"] tensor_mat_id[of "2 ^ j" m] by simp
  finally have e: "cgate k m (b, j) = 1\<^sub>m ?a \<Otimes> (?G \<Otimes> 1\<^sub>m (2 ^ j * m))" .
  have u: "Quantum.unitary ?G" by (rule pmat_unitary_invol) (simp_all add: opg_props)
  show ?thesis unfolding elementary_def
    by (rule exI[of _ ?a], rule exI[of _ "2 ^ j * m"], rule exI[of _ 2], rule exI[of _ ?G])
       (use e u m k2 in \<open>simp add: Groups.mult_ac\<close>)
qed

lemma unit_vec_kron:
  assumes i: "i < N * m"
  shows "unit_vec (N * m) i = tensor_vec (unit_vec N (i div m)) (unit_vec m (i mod m) :: complex Matrix.vec)"
proof (rule eq_vecI)
  have m0: "0 < m" using i by (cases m) auto
  show "dim_vec (unit_vec (N * m) i) = dim_vec (tensor_vec (unit_vec N (i div m)) (unit_vec m (i mod m) :: complex Matrix.vec))"
    by (simp add: tensor_vec_dim)
  fix r assume "r < dim_vec (tensor_vec (unit_vec N (i div m)) (unit_vec m (i mod m) :: complex Matrix.vec))"
  hence r: "r < N * m" by (simp add: tensor_vec_dim)
  have "(r = i) \<longleftrightarrow> (r div m = i div m \<and> r mod m = i mod m)"
  proof
    assume h: "r div m = i div m \<and> r mod m = i mod m"
    have "r = r div m * m + r mod m" by simp
    also have "\<dots> = i div m * m + i mod m" using h by simp
    also have "\<dots> = i" by simp
    finally show "r = i" .
  qed simp
  thus "unit_vec (N * m) i $ r = tensor_vec (unit_vec N (i div m)) (unit_vec m (i mod m)) $ r"
    using tensor_vec_index[of "unit_vec N (i div m)" N "unit_vec m (i mod m)" m r] r i m0
    by (auto simp: unit_vec_def less_mult_imp_div_less)
qed

lemma ctrl_conj:
  assumes f: "\<And>t. t < N \<Longrightarrow> f t < N" and h: "\<And>t. t < N \<Longrightarrow> h (f t) = t"
    and B: "\<And>c. c < N \<Longrightarrow> B c \<in> carrier_mat m m"
  shows "(pmat N h \<Otimes> 1\<^sub>m m) * ctrl_blocks N m B * (pmat N f \<Otimes> 1\<^sub>m m) = ctrl_blocks N m (\<lambda>c. B (f c))"
proof (rule mat_eq_unit)
  show "(pmat N h \<Otimes> 1\<^sub>m m) * ctrl_blocks N m B * (pmat N f \<Otimes> 1\<^sub>m m) \<in> carrier_mat (N * m) (N * m)"
    by (rule mult_carrier_mat[OF mult_carrier_mat[OF tensor_carrier[OF pmat_carrier one_carrier_mat] ctrl_blocks_carrier]
          tensor_carrier[OF pmat_carrier one_carrier_mat]])
  show "ctrl_blocks N m (\<lambda>c. B (f c)) \<in> carrier_mat (N * m) (N * m)" by simp
  fix i assume i: "i < N * m"
  let ?c = "i div m" and ?y = "i mod m"
  have m0: "0 < m" using i by (cases m) auto
  have c: "?c < N" using i by (simp add: less_mult_imp_div_less)
  have y: "?y < m" using m0 by simp
  have ey: "dim_vec (unit_vec m ?y :: complex Matrix.vec) = m" by simp
  have Bfc: "B (f ?c) \<in> carrier_mat m m" by (rule B[OF f[OF c]])
  have w: "dim_vec (B (f ?c) *\<^sub>v unit_vec m ?y) = m" using Bfc by simp
  have s1: "(pmat N f \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec (unit_vec N ?c) (unit_vec m ?y) = tensor_vec (unit_vec N (f ?c)) (unit_vec m ?y)"
  proof -
    have "(pmat N f \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec (unit_vec N ?c) (unit_vec m ?y) = tensor_vec (pmat N f *\<^sub>v unit_vec N ?c) (1\<^sub>m m *\<^sub>v unit_vec m ?y)"
      by (rule tensor_mat_vec_mult[OF pmat_carrier one_carrier_mat]) simp_all
    thus ?thesis unfolding pmat_unit[where f = f, OF c f[OF c]] one_mult_mat_vec[OF unit_vec_carrier] .
  qed
  have s2: "ctrl_blocks N m B *\<^sub>v tensor_vec (unit_vec N (f ?c)) (unit_vec m ?y) = tensor_vec (unit_vec N (f ?c)) (B (f ?c) *\<^sub>v unit_vec m ?y)"
    by (rule ctrl_blocks_basis[where B = B, OF f[OF c] ey Bfc])
  have s3: "(pmat N h \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec (unit_vec N (f ?c)) (B (f ?c) *\<^sub>v unit_vec m ?y) = tensor_vec (unit_vec N ?c) (B (f ?c) *\<^sub>v unit_vec m ?y)"
  proof -
    have "(pmat N h \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec (unit_vec N (f ?c)) (B (f ?c) *\<^sub>v unit_vec m ?y)
          = tensor_vec (pmat N h *\<^sub>v unit_vec N (f ?c)) (1\<^sub>m m *\<^sub>v (B (f ?c) *\<^sub>v unit_vec m ?y))"
      by (rule tensor_mat_vec_mult[OF pmat_carrier one_carrier_mat]) (use w Bfc in simp_all)
    moreover have "pmat N h *\<^sub>v unit_vec N (f ?c) = unit_vec N ?c" using pmat_unit[where f = h and t = "f ?c", OF f[OF c]] h[OF c] c by simp
    ultimately show ?thesis unfolding one_mult_mat_vec[OF carrier_vecI[OF w]] by simp
  qed
  have r: "ctrl_blocks N m (\<lambda>c. B (f c)) *\<^sub>v tensor_vec (unit_vec N ?c) (unit_vec m ?y) = tensor_vec (unit_vec N ?c) (B (f ?c) *\<^sub>v unit_vec m ?y)"
    by (rule ctrl_blocks_basis[where B = "\<lambda>c. B (f c)", OF c ey Bfc])
  have "((pmat N h \<Otimes> 1\<^sub>m m) * ctrl_blocks N m B * (pmat N f \<Otimes> 1\<^sub>m m)) *\<^sub>v tensor_vec (unit_vec N ?c) (unit_vec m ?y)
        = (pmat N h \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_blocks N m B *\<^sub>v ((pmat N f \<Otimes> 1\<^sub>m m) *\<^sub>v tensor_vec (unit_vec N ?c) (unit_vec m ?y)))"
    by (rule assoc3_mult_vec[OF tensor_carrier[OF pmat_carrier one_carrier_mat] ctrl_blocks_carrier tensor_carrier[OF pmat_carrier one_carrier_mat]])
       (simp add: carrier_vecI tensor_vec_dim)
  also have "\<dots> = tensor_vec (unit_vec N ?c) (B (f ?c) *\<^sub>v unit_vec m ?y)" unfolding s1 s2 s3 ..
  finally show "((pmat N h \<Otimes> 1\<^sub>m m) * ctrl_blocks N m B * (pmat N f \<Otimes> 1\<^sub>m m)) *\<^sub>v unit_vec (N * m) i = ctrl_blocks N m (\<lambda>c. B (f c)) *\<^sub>v unit_vec (N * m) i"
    unfolding unit_vec_kron[OF i] r .
qed


subsection \<open>Parity-controlled rotations of the ancilla\<close>

text \<open>\<open>cv0 k n W\<close>: $W$ on the ancilla, controlled by the last clock qubit (the identity on the
system register between them).\<close>

definition cv0 :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "cv0 k n Wr = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. if odd c then 1\<^sub>m n \<Otimes> Wr else 1\<^sub>m (n * 2))"

definition pblock :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "pblock k n ms a = map (cgate k (n * 2)) (parity_chain ms) @ [cv0 k n (Rot a)] @ map (cgate k (n * 2)) (rev (parity_chain ms))"

lemma tensor_one_Rot_carrier: "1\<^sub>m n \<Otimes> Rot a \<in> carrier_mat (n * 2) (n * 2)"
  by (rule tensor_carrier[OF one_carrier_mat Rot_carrier])

lemma pblock_circuit:
  assumes ms: "True \<in> set ms" "length ms = k" and n0: "0 < n"
  shows "circuit_mat (2 ^ k * (n * 2)) (pblock k n ms a)
         = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. if par ms c then 1\<^sub>m n \<Otimes> Rot a else 1\<^sub>m (n * 2))"
proof -
  let ?K = "2 ^ k * (n * 2)" and ?ch = "parity_chain ms"
  have pos: "\<And>b j. (b, j) \<in> set ?ch \<Longrightarrow> j + 2 \<le> k" using parity_chain_pos ms(2) by fastforce
  have posr: "\<And>b j. (b, j) \<in> set (rev ?ch) \<Longrightarrow> j + 2 \<le> k" using pos by simp
  have m0: "0 < n * 2" using n0 by simp
  have c1: "circuit_mat ?K (map (cgate k (n * 2)) ?ch) = pmat (2 ^ k) (apply_ops ?ch) \<Otimes> 1\<^sub>m (n * 2)"
    by (rule circuit_cgates[OF pos m0])
  have c2: "circuit_mat ?K (map (cgate k (n * 2)) (rev ?ch)) = pmat (2 ^ k) (apply_ops (rev ?ch)) \<Otimes> 1\<^sub>m (n * 2)"
    by (rule circuit_cgates[OF posr m0])
  have cg: "\<And>U. U \<in> set (map (cgate k (n * 2)) os) \<Longrightarrow> U \<in> carrier_mat ?K ?K" for os
    by (auto simp: cgate_def intro!: tensor_carrier[OF pmat_carrier one_carrier_mat, simplified])
  have cvc: "cv0 k n (Rot a) \<in> carrier_mat ?K ?K" by (simp add: cv0_def)
  have p0: "circuit_mat ?K (pblock k n ms a)
        = circuit_mat ?K (map (cgate k (n * 2)) (rev ?ch)) * circuit_mat ?K [cv0 k n (Rot a)] * circuit_mat ?K (map (cgate k (n * 2)) ?ch)"
  proof -
    have "circuit_mat ?K (pblock k n ms a) = circuit_mat ?K ([cv0 k n (Rot a)] @ map (cgate k (n * 2)) (rev ?ch)) * circuit_mat ?K (map (cgate k (n * 2)) ?ch)"
      unfolding pblock_def by (rule circuit_mat_append) (use cg cvc in auto)
    also have "circuit_mat ?K ([cv0 k n (Rot a)] @ map (cgate k (n * 2)) (rev ?ch))
               = circuit_mat ?K (map (cgate k (n * 2)) (rev ?ch)) * circuit_mat ?K [cv0 k n (Rot a)]"
      by (rule circuit_mat_append) (use cg cvc in auto)
    finally show ?thesis .
  qed
  have cs: "circuit_mat ?K [cv0 k n (Rot a)] = cv0 k n (Rot a)" using cvc by (simp add: left_mult_one_mat)
  have p1: "circuit_mat ?K (map (cgate k (n * 2)) (rev ?ch)) * circuit_mat ?K [cv0 k n (Rot a)] * circuit_mat ?K (map (cgate k (n * 2)) ?ch)
        = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. if odd (apply_ops ?ch c) then 1\<^sub>m n \<Otimes> Rot a else 1\<^sub>m (n * 2))"
    unfolding c1 c2 cs unfolding cv0_def
    by (rule ctrl_conj[where B = "\<lambda>c. if odd c then 1\<^sub>m n \<Otimes> Rot a else 1\<^sub>m (n * 2)"])
       (use apply_ops_lt[OF pos] apply_ops_rev tensor_one_Rot_carrier in auto)
  have p2: "ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. if odd (apply_ops ?ch c) then 1\<^sub>m n \<Otimes> Rot a else 1\<^sub>m (n * 2))
             = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. if par ms c then 1\<^sub>m n \<Otimes> Rot a else 1\<^sub>m (n * 2))"
    using parity_chain_correct[OF ms(1)] by simp
  show ?thesis unfolding p0 p1 p2 ..
qed


subsection \<open>Walsh--Hadamard angles\<close>

definition sg :: "bool \<Rightarrow> real" where "sg b = (if b then - 1 else 1)"

definition masks :: "nat \<Rightarrow> bool list list" where "masks k = List.n_lists k [False, True]"

lemma sum_list_masks_Suc: "sum_list (map f (masks (Suc k))) = sum_list (map (\<lambda>ys. f (False # ys) + f (True # ys)) (masks k))"
proof -
  have "sum_list (map f (concat (map (\<lambda>ys. map (\<lambda>y. y # ys) [False, True]) L)))
             = sum_list (map (\<lambda>ys. f (False # ys) + f (True # ys)) L)" for L
    by (induction L) (simp_all add: Groups.add.assoc)
  thus ?thesis unfolding masks_def by simp
qed

lemma length_masks: "ms \<in> set (masks k) \<Longrightarrow> length ms = k"
  unfolding masks_def by (simp add: length_n_lists_elem)

lemma sg_neq: "sg (a \<noteq> b) = sg a * sg b" by (simp add: sg_def)

lemma walsh_orth:
  "c < 2 ^ k \<Longrightarrow> c' < 2 ^ k \<Longrightarrow> sum_list (map (\<lambda>ms. sg (par ms c) * sg (par ms c')) (masks k)) = (if c = c' then 2 ^ k else 0)"
proof (induction k arbitrary: c c')
  case 0 thus ?case by (simp add: masks_def sg_def)
next
  case (Suc k)
  have h: "c div 2 < 2 ^ k" "c' div 2 < 2 ^ k" using Suc.prems by (simp_all add: less_mult_imp_div_less Groups.mult.commute)
  have "sum_list (map (\<lambda>ms. sg (par ms c) * sg (par ms c')) (masks (Suc k)))
        = sum_list (map (\<lambda>ys. (1 + sg (odd c) * sg (odd c')) * (sg (par ys (c div 2)) * sg (par ys (c' div 2)))) (masks k))"
    unfolding sum_list_masks_Suc
  proof (rule arg_cong[where f = sum_list], rule map_cong[OF refl])
    fix ys
    have p: "par (False # ys) x = par ys (x div 2)" "par (True # ys) x = (odd x \<noteq> par ys (x div 2))" for x by simp_all
    show "sg (par (False # ys) c) * sg (par (False # ys) c') + sg (par (True # ys) c) * sg (par (True # ys) c')
          = (1 + sg (odd c) * sg (odd c')) * (sg (par ys (c div 2)) * sg (par ys (c' div 2)))"
      unfolding p sg_neq by (simp add: algebra_simps)
  qed
  also have "\<dots> = (1 + sg (odd c) * sg (odd c')) * sum_list (map (\<lambda>ys. sg (par ys (c div 2)) * sg (par ys (c' div 2))) (masks k))"
    by (simp add: sum_list_const_mult)
  also have "\<dots> = (1 + sg (odd c) * sg (odd c')) * (if c div 2 = c' div 2 then 2 ^ k else 0)" by (simp add: Suc.IH[OF h])
  also have "\<dots> = (if c = c' then 2 ^ Suc k else 0)"
  proof -
    have "c = c' \<longleftrightarrow> (odd c \<longleftrightarrow> odd c') \<and> c div 2 = c' div 2"
    proof
      assume h: "(odd c \<longleftrightarrow> odd c') \<and> c div 2 = c' div 2"
      have m: "c mod 2 = c' mod 2" unfolding mod2_eq_if using h by simp
      have d: "c div 2 = c' div 2" using h by simp
      have "c = c div 2 * 2 + c mod 2" by simp
      also have "\<dots> = c' div 2 * 2 + c' mod 2" unfolding m d ..
      also have "\<dots> = c'" by simp
      finally show "c = c'" .
    qed simp
    thus ?thesis by (auto simp: sg_def)
  qed
  finally show ?case .
qed

lemma sum_list_sum_swap: "sum_list (map (\<lambda>x. \<Sum>c\<in>A. g x c) L) = (\<Sum>c\<in>A. sum_list (map (\<lambda>x. g x c) L))"
  by (induction L) (simp_all add: sum.distrib)

definition walsh :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool list \<Rightarrow> real" where
  "walsh k \<theta> ms = (\<Sum>c'<2 ^ k. \<theta> c' * sg (par ms c')) / 2 ^ k"

lemma walsh_inversion:
  assumes c: "c < 2 ^ k"
  shows "sum_list (map (\<lambda>ms. walsh k \<theta> ms * sg (par ms c)) (masks k)) = \<theta> c"
proof -
  have "sum_list (map (\<lambda>ms. walsh k \<theta> ms * sg (par ms c)) (masks k))
        = sum_list (map (\<lambda>ms. \<Sum>c'<2 ^ k. \<theta> c' * (sg (par ms c') * sg (par ms c)) / 2 ^ k) (masks k))"
  proof (rule arg_cong[where f = sum_list], rule map_cong[OF refl])
    fix ms
    show "walsh k \<theta> ms * sg (par ms c) = (\<Sum>c'<2 ^ k. \<theta> c' * (sg (par ms c') * sg (par ms c)) / 2 ^ k)"
      unfolding walsh_def sum_divide_distrib[symmetric] sum_distrib_right by (simp add: sum_distrib_left Groups.mult_ac)
  qed
  also have "\<dots> = (\<Sum>c'<2 ^ k. sum_list (map (\<lambda>ms. \<theta> c' * (sg (par ms c') * sg (par ms c)) / 2 ^ k) (masks k)))"
    by (rule sum_list_sum_swap)
  also have "\<dots> = (\<Sum>c'<2 ^ k. \<theta> c' * (if c' = c then 2 ^ k else 0) / 2 ^ k)"
  proof (rule sum.cong[OF refl])
    fix c' :: nat assume "c' \<in> {..<2 ^ k}"
    hence c': "c' < 2 ^ k" by simp
    have "sum_list (map (\<lambda>ms. \<theta> c' * (sg (par ms c') * sg (par ms c)) / 2 ^ k) (masks k))
          = \<theta> c' * sum_list (map (\<lambda>ms. sg (par ms c') * sg (par ms c)) (masks k)) / 2 ^ k"
    proof -
      have "(\<lambda>ms. \<theta> c' * (sg (par ms c') * sg (par ms c)) / 2 ^ k) = (\<lambda>ms. (\<theta> c' / 2 ^ k) * (sg (par ms c') * sg (par ms c)))"
        by (rule ext) simp
      thus ?thesis by (simp only: sum_list_const_mult) simp
    qed
    thus "sum_list (map (\<lambda>ms. \<theta> c' * (sg (par ms c') * sg (par ms c)) / 2 ^ k) (masks k)) = \<theta> c' * (if c' = c then 2 ^ k else 0) / 2 ^ k"
      by (simp only: walsh_orth[OF c' c])
  qed
  also have "\<dots> = (\<Sum>c'<2 ^ k. if c' = c then \<theta> c else 0)" by (rule sum.cong) auto
  also have "\<dots> = \<theta> c" using c by simp
  finally show ?thesis .
qed


subsection \<open>The uniformly controlled rotation\<close>

definition anc_rot :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "anc_rot k n a = 1\<^sub>m (2 ^ k * n) \<Otimes> Rot a"

definition nzmasks :: "nat \<Rightarrow> bool list list" where "nzmasks k = filter (\<lambda>ms. True \<in> set ms) (masks k)"

definition ucr_gates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list" where
  "ucr_gates k n \<theta> = anc_rot k n (sum_list (map (walsh k \<theta>) (masks k)))
     # concat (map (\<lambda>ms. pblock k n ms (- 2 * walsh k \<theta> ms)) (nzmasks k))"

lemma ctrl_const:
  assumes B: "B \<in> carrier_mat m m" and m: "0 < m"
  shows "1\<^sub>m N \<Otimes> B = ctrl_blocks N m (\<lambda>_. B)"
proof (rule eq_matI)
  fix r s assume "r < dim_row (ctrl_blocks N m (\<lambda>_. B))" "s < dim_col (ctrl_blocks N m (\<lambda>_. B))"
  hence rs: "r < N * m" "s < N * m" by simp_all
  have "(1\<^sub>m N \<Otimes> B) $$ (r, s) = 1\<^sub>m N $$ (r div m, s div m) * B $$ (r mod m, s mod m)"
  proof -
    have N0: "0 < N" using rs by (cases N) auto
    show ?thesis using index_tensor_mat[of "1\<^sub>m N" N N B m m r s] rs B m N0 by simp
  qed
  also have "\<dots> = ctrl_blocks N m (\<lambda>_. B) $$ (r, s)"
    using rs m by (simp add: ctrl_blocks_index less_mult_imp_div_less)
  finally show "(1\<^sub>m N \<Otimes> B) $$ (r, s) = ctrl_blocks N m (\<lambda>_. B) $$ (r, s)" .
qed (use B in auto)

lemma anc_rot_ctrl: "0 < n \<Longrightarrow> anc_rot k n a = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot a)"
proof -
  assume n0: "0 < n"
  have "anc_rot k n a = (1\<^sub>m (2 ^ k) \<Otimes> 1\<^sub>m n) \<Otimes> Rot a" unfolding anc_rot_def tensor_mat_id ..
  also have "\<dots> = 1\<^sub>m (2 ^ k) \<Otimes> (1\<^sub>m n \<Otimes> Rot a)" by (rule tensor_mat_is_assoc[symmetric])
  also have "\<dots> = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot a)"
    by (rule ctrl_const[OF tensor_one_Rot_carrier]) (use n0 in simp)
  finally show ?thesis .
qed

lemma one_Rot_zero: "1\<^sub>m n \<Otimes> Rot 0 = 1\<^sub>m (n * 2)" by (simp add: Rot_zero tensor_mat_id)

lemma one_Rot_mult: "0 < n \<Longrightarrow> (1\<^sub>m n \<Otimes> Rot x) * (1\<^sub>m n \<Otimes> Rot y) = 1\<^sub>m n \<Otimes> Rot (x + y)"
  using mult_distr_tensor[of "1\<^sub>m n" "1\<^sub>m n" "Rot x" "Rot y"] by (simp add: Rot_add)

lemma pblock_circuit':
  assumes "True \<in> set ms" "length ms = k" and n0: "0 < n"
  shows "circuit_mat (2 ^ k * (n * 2)) (pblock k n ms a) = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (if par ms c then a else 0))"
  unfolding pblock_circuit[OF assms] by (rule ctrl_blocks_cong) (simp add: one_Rot_zero)

lemma pblock_carrier: "U \<in> set (pblock k n ms a) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))"
  by (auto simp: pblock_def cgate_def cv0_def intro!: tensor_carrier[OF pmat_carrier one_carrier_mat, simplified])

lemma concat_pblock_circuit:
  assumes L: "\<And>ms. ms \<in> set L \<Longrightarrow> True \<in> set ms \<and> length ms = k" and n0: "0 < n"
  shows "circuit_mat (2 ^ k * (n * 2)) (concat (map (\<lambda>ms. pblock k n ms (f ms)) L))
         = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (sum_list (map (\<lambda>ms. if par ms c then f ms else 0) L)))"
  using L
proof (induction L)
  case Nil
  show ?case using ctrl_blocks_one[of "2 ^ k" "n * 2"] by (simp add: one_Rot_zero)
next
  case (Cons ms L)
  let ?K = "2 ^ k * (n * 2)"
  have IH: "circuit_mat ?K (concat (map (\<lambda>ms. pblock k n ms (f ms)) L))
            = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (sum_list (map (\<lambda>ms. if par ms c then f ms else 0) L)))"
    by (rule Cons.IH) (use Cons.prems in auto)
  have hd: "True \<in> set ms" "length ms = k" using Cons.prems by auto
  have "circuit_mat ?K (concat (map (\<lambda>ms. pblock k n ms (f ms)) (ms # L)))
        = circuit_mat ?K (concat (map (\<lambda>ms. pblock k n ms (f ms)) L)) * circuit_mat ?K (pblock k n ms (f ms))"
    by (simp only: list.map concat.simps, rule circuit_mat_append) (use pblock_carrier in auto)
  also have "\<dots> = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. (1\<^sub>m n \<Otimes> Rot (sum_list (map (\<lambda>ms. if par ms c then f ms else 0) L)))
                                                  * (1\<^sub>m n \<Otimes> Rot (if par ms c then f ms else 0)))"
    unfolding IH pblock_circuit'[OF hd n0] by (rule ctrl_blocks_mult) (simp_all add: tensor_one_Rot_carrier)
  also have "\<dots> = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (sum_list (map (\<lambda>ms. if par ms c then f ms else 0) (ms # L))))"
    by (rule ctrl_blocks_cong) (simp add: one_Rot_mult[OF n0] Groups.add.commute)
  finally show ?case .
qed

lemma ucr_angle:
  assumes c: "c < 2 ^ k"
  shows "sum_list (map (\<lambda>ms. if par ms c then - 2 * walsh k \<theta> ms else 0) (nzmasks k)) + sum_list (map (walsh k \<theta>) (masks k)) = \<theta> c"
proof -
  have e: "sum_list (map (\<lambda>ms. if par ms c then - 2 * walsh k \<theta> ms else 0) (nzmasks k))
           = sum_list (map (\<lambda>ms. if par ms c then - 2 * walsh k \<theta> ms else 0) (masks k))"
    unfolding nzmasks_def sum_list_map_filter'
    by (rule arg_cong[where f = sum_list], rule map_cong[OF refl]) (auto dest: par_false)
  have "\<theta> c = sum_list (map (\<lambda>ms. walsh k \<theta> ms * sg (par ms c)) (masks k))" by (rule walsh_inversion[OF c, symmetric])
  also have "\<dots> = sum_list (map (\<lambda>ms. (if par ms c then - 2 * walsh k \<theta> ms else 0) + walsh k \<theta> ms) (masks k))"
    by (rule arg_cong[where f = sum_list], rule map_cong[OF refl]) (simp add: sg_def)
  also have "\<dots> = sum_list (map (\<lambda>ms. if par ms c then - 2 * walsh k \<theta> ms else 0) (masks k)) + sum_list (map (walsh k \<theta>) (masks k))"
    by (simp add: sum_list_addf)
  finally show ?thesis unfolding e by simp
qed

theorem ucr_circuit:
  assumes n0: "0 < n"
  shows "circuit_mat (2 ^ k * (n * 2)) (ucr_gates k n \<theta>) = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta> c))"
proof -
  let ?K = "2 ^ k * (n * 2)" and ?a0 = "sum_list (map (walsh k \<theta>) (masks k))"
  let ?L = "concat (map (\<lambda>ms. pblock k n ms (- 2 * walsh k \<theta> ms)) (nzmasks k))"
  have L: "\<And>ms. ms \<in> set (nzmasks k) \<Longrightarrow> True \<in> set ms \<and> length ms = k"
    by (auto simp: nzmasks_def length_masks)
  have ac: "anc_rot k n ?a0 \<in> carrier_mat ?K ?K" unfolding anc_rot_ctrl[OF n0] by simp
  have cc: "circuit_mat ?K ?L = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (sum_list (map (\<lambda>ms. if par ms c then - 2 * walsh k \<theta> ms else 0) (nzmasks k))))"
    by (rule concat_pblock_circuit) (use L n0 in auto)
  have "circuit_mat ?K (ucr_gates k n \<theta>) = circuit_mat ?K ?L * anc_rot k n ?a0"
    unfolding ucr_gates_def by simp
  also have "\<dots> = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. (1\<^sub>m n \<Otimes> Rot (sum_list (map (\<lambda>ms. if par ms c then - 2 * walsh k \<theta> ms else 0) (nzmasks k))))
                                               * (1\<^sub>m n \<Otimes> Rot ?a0))"
    unfolding cc anc_rot_ctrl[OF n0] by (rule ctrl_blocks_mult) (simp_all add: tensor_one_Rot_carrier)
  also have "\<dots> = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta> c))"
    by (rule ctrl_blocks_cong) (simp add: one_Rot_mult[OF n0] ucr_angle)
  finally show ?thesis .
qed

lemma anc_rot_elementary:
  assumes n0: "0 < n"
  shows "elementary (2 ^ k * (n * 2)) (anc_rot k n a)"
proof -
  have r1: "Rot a \<Otimes> 1\<^sub>m 1 = Rot a" by (rule right_tensor_id[OF Rot_carrier])
  have "2 ^ k * (n * 2) = (2 ^ k * n) * (2 ^ 1 * 1)" by simp
  thus ?thesis unfolding elementary_def anc_rot_def
    by (intro exI[of _ "2 ^ k * n"] exI[of _ 1] exI[of _ 1] exI[of _ "Rot a"]) (use n0 r1 Rot_unitary in simp)
qed

theorem ucr_gate_kinds:
  assumes U: "U \<in> set (ucr_gates k n \<theta>)" and n0: "0 < n"
  shows "elementary (2 ^ k * (n * 2)) U \<or> (\<exists>a. U = cv0 k n (Rot a))"
proof -
  have "U = anc_rot k n (sum_list (map (walsh k \<theta>) (masks k))) \<or> (\<exists>ms \<in> set (nzmasks k). \<exists>a. U \<in> set (pblock k n ms a))"
    using U unfolding ucr_gates_def by auto
  thus ?thesis
  proof
    assume "U = anc_rot k n (sum_list (map (walsh k \<theta>) (masks k)))" thus ?thesis using anc_rot_elementary[OF n0] by simp
  next
    assume "\<exists>ms \<in> set (nzmasks k). \<exists>a. U \<in> set (pblock k n ms a)"
    then obtain ms a where ms: "ms \<in> set (nzmasks k)" and Ua: "U \<in> set (pblock k n ms a)" by blast
    have len: "length ms = k" using ms by (auto simp: nzmasks_def length_masks)
    have pos: "\<And>b j. (b, j) \<in> set (parity_chain ms) \<Longrightarrow> j + 2 \<le> k" using parity_chain_pos len by fastforce
    have m0: "0 < n * 2" using n0 by simp
    have "U = cv0 k n (Rot a) \<or> (\<exists>b j. (b, j) \<in> set (parity_chain ms) \<and> U = cgate k (n * 2) (b, j))"
      using Ua unfolding pblock_def by auto
    thus ?thesis using cgate_elementary[OF pos m0] by blast
  qed
qed

lemma cv0_unitary: "Quantum.unitary Wr \<Longrightarrow> Wr \<in> carrier_mat 2 2 \<Longrightarrow> Quantum.unitary (cv0 k n Wr)"
  unfolding cv0_def by (rule ctrl_blocks_unitary) (auto intro: tensor_carrier[OF one_carrier_mat] simp: id_is_unitary)


lemma ucr_gates_ok:
  assumes U: "U \<in> set (ucr_gates k n \<theta>)" and n0: "0 < n"
  shows "U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
proof -
  have "elementary (2 ^ k * (n * 2)) U \<or> (\<exists>a. U = cv0 k n (Rot a))" by (rule ucr_gate_kinds[OF U n0])
  thus ?thesis
  proof
    assume "elementary (2 ^ k * (n * 2)) U"
    thus ?thesis using elementary_unitary unitary_bridge by blast
  next
    assume "\<exists>a. U = cv0 k n (Rot a)"
    then obtain a where Ua: "U = cv0 k n (Rot a)" by blast
    have c: "U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))" unfolding Ua by (simp add: cv0_def)
    have "Quantum.unitary U" unfolding Ua by (rule cv0_unitary[OF Rot_unitary Rot_carrier])
    thus ?thesis using c unitary_bridge[OF c] by blast
  qed
qed

subsection \<open>The HHL program with the rotation in elementary gates\<close>

definition hhl_theta :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "hhl_theta A t0 k C c = arcsin (C / reg_eig t0 (2 ^ k) c)"

definition hhl_fine_blocks :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list list" where
  "hhl_fine_blocks A Ub t0 k C = (hhl_blocks A Ub t0 k C)[4 := ucr_gates k (dim_row A) (hhl_theta A t0 k C)]"

definition hhl_fine_gates :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat list" where
  "hhl_fine_gates A Ub t0 k C = concat (hhl_fine_blocks A Ub t0 k C)"

definition hhl_fine_program :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> com" where
  "hhl_fine_program A Ub t0 k C = hhl_prog (2 ^ k * (dim_row A * 2)) (hhl_fine_gates A Ub t0 k C)"

definition hhl_fine_rus :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> com" where
  "hhl_fine_rus A Ub t0 k C = hhl_rus_prog (2 ^ k * (dim_row A * 2)) (hhl_fine_gates A Ub t0 k C)"

context
  fixes A Ub :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and k: "1 \<le> k" and t0: "0 < t0"
    and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>j. 0 < j \<and> j < 2 ^ k \<and> l = reg_eig t0 (2 ^ k) j"
    and Ub: "Ub \<in> carrier_mat n n" "Quantum.unitary Ub" "Ub *\<^sub>v unit_vec n 0 = b"
    and Cb: "\<And>j. j < 2 ^ k \<Longrightarrow> \<bar>C / reg_eig t0 (2 ^ k) j\<bar> \<le> 1"
begin


lemma rot_gate_ucr: "rot_gate A t0 (2 ^ k) C = circuit_mat (2 ^ k * (n * 2)) (ucr_gates k n (hhl_theta A t0 k C))"
proof -
  have "rot_gate A t0 (2 ^ k) C = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (hhl_theta A t0 k C c))"
    unfolding rot_gate_def carrier_matD(1)[OF A(1)] hhl_theta_def by (rule ctrl_blocks_cong) (simp add: rot_Rot[OF Cb])
  thus ?thesis unfolding ucr_circuit[OF n0] .
qed

lemma ucr_ok:
  "U \<in> set (ucr_gates k n \<theta>) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
proof -
  assume U: "U \<in> set (ucr_gates k n \<theta>)"
  have "elementary (2 ^ k * (n * 2)) U \<or> (\<exists>a. U = cv0 k n (Rot a))" by (rule ucr_gate_kinds[OF U n0])
  thus ?thesis
  proof
    assume "elementary (2 ^ k * (n * 2)) U"
    thus ?thesis using elementary_unitary unitary_bridge by blast
  next
    assume "\<exists>a. U = cv0 k n (Rot a)"
    then obtain a where Ua: "U = cv0 k n (Rot a)" by blast
    have c: "U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))" unfolding Ua by (simp add: cv0_def)
    have "Quantum.unitary U" unfolding Ua by (rule cv0_unitary[OF Rot_unitary Rot_carrier])
    thus ?thesis using c unitary_bridge[OF c] by blast
  qed
qed

lemma fine_gates_ok:
  "U \<in> set (hhl_fine_gates A Ub t0 k C) \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U"
proof -
  assume "U \<in> set (hhl_fine_gates A Ub t0 k C)"
  then obtain B where B: "B \<in> set (hhl_fine_blocks A Ub t0 k C)" and U: "U \<in> set B" unfolding hhl_fine_gates_def by auto
  have "B = ucr_gates k n (hhl_theta A t0 k C) \<or> B \<in> set (hhl_blocks A Ub t0 k C)"
    using B set_update_subset_insert[of "hhl_blocks A Ub t0 k C" 4 "ucr_gates k n (hhl_theta A t0 k C)"]
    unfolding hhl_fine_blocks_def carrier_matD(1)[OF A(1)] by auto
  thus ?thesis
  proof
    assume "B = ucr_gates k n (hhl_theta A t0 k C)" thus ?thesis using ucr_ok U by simp
  next
    assume "B \<in> set (hhl_blocks A Ub t0 k C)"
    hence "U \<in> set (hhl_elem_gates A Ub t0 k C)" using U unfolding hhl_elem_gates_def by auto
    thus ?thesis using elem_gates_ok[OF A n0 k t0 _ Ub Cb] spec by blast
  qed
qed

theorem hhl_fine_circuit:
  "circuit_mat (2 ^ k * (n * 2)) (hhl_fine_gates A Ub t0 k C) = circuit_mat (2 ^ k * (n * 2)) (hhl_gates A Ub t0 k C)"
proof -
  let ?D = "2 ^ k * (n * 2)"
  have "map (circuit_mat ?D) (hhl_fine_blocks A Ub t0 k C)
        = (map (circuit_mat ?D) (hhl_blocks A Ub t0 k C))[4 := circuit_mat ?D (ucr_gates k n (hhl_theta A t0 k C))]"
    unfolding hhl_fine_blocks_def carrier_matD(1)[OF A(1)] by (simp add: map_update)
  also have "circuit_mat ?D (ucr_gates k n (hhl_theta A t0 k C)) = rot_gate A t0 (2 ^ k) C" by (rule rot_gate_ucr[symmetric])
  also have "map (circuit_mat ?D) (hhl_blocks A Ub t0 k C) = hhl_gates A Ub t0 k C" by (rule hhl_blocks_circuit[OF A(1,2) n0 k Ub(1)])
  also have "(hhl_gates A Ub t0 k C)[4 := rot_gate A t0 (2 ^ k) C] = hhl_gates A Ub t0 k C" by (simp add: hhl_gates_def)
  finally have m: "map (circuit_mat ?D) (hhl_fine_blocks A Ub t0 k C) = hhl_gates A Ub t0 k C" .
  show ?thesis unfolding hhl_fine_gates_def m[symmetric]
    by (rule circuit_mat_concat) (use fine_gates_ok in \<open>auto simp: hhl_fine_gates_def\<close>)
qed

theorem hhl_fine_success_total:
  "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real (C\<^sup>2 * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m (2 ^ k * (n * 2)))
     (hhl_fine_program A Ub t0 k C) (anc_proj (2 ^ k * (n * 2)) 1)"
  unfolding hhl_fine_program_def carrier_matD(1)[OF A(1)]
  by (rule hhl_prog_success_total[OF A n0 k t0 spec Ub Cb fine_gates_ok hhl_fine_circuit])

theorem hhl_fine_correct_total:
  "state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_fine_program A Ub t0 k C)
     (anc_proj (2 ^ k * (n * 2)) 0 + outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_fine_program_def carrier_matD(1)[OF A(1)]
  by (rule hhl_prog_correct_total[OF A n0 k t0 spec Ub Cb fine_gates_ok hhl_fine_circuit])

theorem hhl_fine_rus_total:
  "C \<noteq> 0 \<Longrightarrow> state_sig.hoare_total_correct [2 ^ k, n, 2] (1\<^sub>m (2 ^ k * (n * 2))) (hhl_fine_rus A Ub t0 k C)
     (outer_prod (hhl_target A k b) (hhl_target A k b))"
  unfolding hhl_fine_rus_def carrier_matD(1)[OF A(1)]
  by (rule hhl_rus_prog_total[OF A n0 k t0 spec Ub Cb fine_gates_ok hhl_fine_circuit])

text \<open>Every gate is elementary (one or two neighbouring qubits), a singly controlled $U^{\pm2^j}$
(an oracle call), the preparation of $\ket b$, or a rotation of the ancilla controlled by the last
clock qubit.\<close>

theorem hhl_fine_gate_kinds:
  assumes U: "U \<in> set (hhl_fine_gates A Ub t0 k C)"
  shows "elementary (2 ^ k * (n * 2)) U
         \<or> (\<exists>j<k. U = ctrl_bit (2 ^ k) (n * 2) j ((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)
                 \<or> U = ctrl_bit (2 ^ k) (n * 2) j (((evolution A t0 \<Otimes> 1\<^sub>m 2) ^\<^sub>m 2 ^ j)\<^sup>\<dagger>))
         \<or> U = prep_gate (2 ^ k) Ub
         \<or> (\<exists>a. U = cv0 k n (Rot a))"
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
  have r: "U \<in> set (ucr_gates k n (hhl_theta A t0 k C)) \<Longrightarrow> elementary ?D U \<or> (\<exists>a. U = cv0 k n (Rot a))" for U
    by (rule ucr_gate_kinds[OF _ n0])
  have "U = prep_gate (2 ^ k) Ub \<or> U \<in> set (clk_gates n (had_gates k)) \<or> U \<in> set (evo_gates A t0 k)
        \<or> U \<in> set (clk_gates n (rev (map dagger (qft_circuit k)))) \<or> U \<in> set (ucr_gates k n (hhl_theta A t0 k C))
        \<or> U \<in> set (clk_gates n (qft_circuit k)) \<or> U \<in> set (rev (map dagger (evo_gates A t0 k)))"
    using U unfolding hhl_fine_gates_def hhl_fine_blocks_def hhl_blocks_def carrier_matD(1)[OF A(1)] by auto
  thus ?thesis using h fi f e ei r by blast
qed

end


subsection \<open>The paper-regime circuits with Fourier transforms and rotation in elementary gates\<close>

definition fine2_gates :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat list" where
  "fine2_gates k n \<theta> Us = concat (map (\<lambda>U. if U = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta> c)) then ucr_gates k n \<theta>
                                            else fref k (n * 2) U) Us)"

lemma fine2_gates_props:
  assumes Us: "\<And>U. U \<in> set Us \<Longrightarrow> U \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary U" and n0: "0 < n"
  shows "circuit_mat (2 ^ k * (n * 2)) (fine2_gates k n \<theta> Us) = circuit_mat (2 ^ k * (n * 2)) Us"
    and "\<And>W. W \<in> set (fine2_gates k n \<theta> Us) \<Longrightarrow> W \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary W"
    and "\<And>W. W \<in> set (fine2_gates k n \<theta> Us) \<Longrightarrow>
           (W \<in> set Us \<and> W \<noteq> ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta> c))) \<or> elementary (2 ^ k * (n * 2)) W \<or> (\<exists>a. W = cv0 k n (Rot a))"
proof -
  let ?K = "2 ^ k * (n * 2)" and ?RS = "ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta> c))"
  let ?R = "\<lambda>U. if U = ?RS then ucr_gates k n \<theta> else fref k (n * 2) U"
  have m0: "0 < n * 2" using n0 by simp
  show kind: "\<And>W. W \<in> set (fine2_gates k n \<theta> Us) \<Longrightarrow> (W \<in> set Us \<and> W \<noteq> ?RS) \<or> elementary ?K W \<or> (\<exists>a. W = cv0 k n (Rot a))"
  proof -
    fix W assume "W \<in> set (fine2_gates k n \<theta> Us)"
    then obtain U where U: "U \<in> set Us" and w: "W \<in> set (?R U)" unfolding fine2_gates_def set_concat set_map by blast
    show "(W \<in> set Us \<and> W \<noteq> ?RS) \<or> elementary ?K W \<or> (\<exists>a. W = cv0 k n (Rot a))"
    proof (cases "U = ?RS")
      case True
      hence "W \<in> set (ucr_gates k n \<theta>)" using w by simp
      thus ?thesis using ucr_gate_kinds[OF _ n0] by blast
    next
      case False
      hence "W \<in> set (fref k (n * 2) U)" using w by simp
      hence "W = U \<or> elementary ?K W" by (rule fref_props(2)[OF conjunct1[OF Us[OF U]] m0])
      thus ?thesis using U False by blast
    qed
  qed
  show ok: "\<And>W. W \<in> set (fine2_gates k n \<theta> Us) \<Longrightarrow> W \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary W"
  proof -
    fix W assume w: "W \<in> set (fine2_gates k n \<theta> Us)"
    have "(W \<in> set Us \<and> W \<noteq> ?RS) \<or> elementary ?K W \<or> (\<exists>a. W = cv0 k n (Rot a))" by (rule kind[OF w])
    thus "W \<in> carrier_mat ?K ?K \<and> Complex_Matrix.unitary W"
    proof (elim disjE)
      assume "W \<in> set Us \<and> W \<noteq> ?RS" thus ?thesis using Us by blast
    next
      assume "elementary ?K W" thus ?thesis using elementary_unitary unitary_bridge by blast
    next
      assume "\<exists>a. W = cv0 k n (Rot a)"
      then obtain a where Wa: "W = cv0 k n (Rot a)" by blast
      have "W \<in> set (ucr_gates k n \<theta>) \<or> True" by simp
      have c: "W \<in> carrier_mat ?K ?K" unfolding Wa by (simp add: cv0_def)
      have "Quantum.unitary W" unfolding Wa by (rule cv0_unitary[OF Rot_unitary Rot_carrier])
      thus ?thesis using c unitary_bridge[OF c] by blast
    qed
  qed
  have "circuit_mat ?K (fine2_gates k n \<theta> Us) = circuit_mat ?K (map (circuit_mat ?K) (map ?R Us))"
    unfolding fine2_gates_def by (rule circuit_mat_concat) (use ok in \<open>auto simp: fine2_gates_def\<close>)
  also have "map (circuit_mat ?K) (map ?R Us) = Us"
    unfolding map_map comp_def
  proof (rule map_idI)
    fix U assume U: "U \<in> set Us"
    show "circuit_mat ?K (?R U) = U"
    proof (cases "U = ?RS")
      case True thus ?thesis using ucr_circuit[OF n0] by simp
    next
      case False thus ?thesis using fref_props(1)[OF conjunct1[OF Us[OF U]] m0] by simp
    qed
  qed
  finally show "circuit_mat ?K (fine2_gates k n \<theta> Us) = circuit_mat ?K Us" .
qed

lemma rot_stage_ucr:
  assumes "dim_row A = n"
  shows "hhl_rot_stage A t0 (2 ^ k) C = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (arcsin (clamp (C / reg_eig t0 (2 ^ k) c))))"
  unfolding hhl_rot_stage_def assms by (rule ctrl_blocks_cong) (simp add: rot_Rot[OF clamp_abs])


theorem hhl_apx_fine2:
  fixes A V Prep :: "complex Matrix.mat" and b :: "complex Matrix.vec" and n k :: nat and t0 C \<theta> lmin \<epsilon> \<eta> :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and k: "1 \<le> k"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real (2 ^ k)"
      and V: "V \<in> carrier_mat n n" "Quantum.unitary V" and Vc: "op_close n \<eta> V (evolution A t0)" and eta: "0 \<le> \<eta>"
      and Prep: "Prep \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2))" "Quantum.unitary Prep"
        "Prep *\<^sub>v unit_vec (2 ^ k * (n * 2)) 0 = tensor_vec (win_state (2 ^ k)) (tensor_vec b (unit_vec 2 0))"
      and small: "\<epsilon> + 2 * real (2 ^ k - 1) * \<eta> \<le> C * t0 / pi"
  defines "c \<equiv> hhl_full_prog A t0 (2 ^ k) C Prep" and "K \<equiv> 2 ^ k * (n * 2)"
    and "\<theta>s \<equiv> \<lambda>c. arcsin (clamp (C / reg_eig t0 (2 ^ k) c))"
  shows "state_sig.hoare_total_correct [2 ^ k, n, 2] (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
     (prog_meas K (anc_proj K) (fine2_gates k n \<theta>s (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c)))
     (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    and "\<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel> < 1 \<Longrightarrow> \<exists>j. calls (aa_prog K 2 (\<lambda>c. c = 1) c j) = (2 * j + 1) * (2 * (2 ^ k - 1))
           \<and> real j \<le> pi\<^sup>2 / (4 * C * t0)
           \<and> state_sig.hoare_total_correct [2 ^ k, n, 2]
               (complex_of_real ((1 - \<parallel>post1 (apx_out V n (2 ^ k) c)\<parallel>\<^sup>2) * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
               (prog_meas K (anc_proj K) (fine2_gates k n \<theta>s (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j))))
               (outer_prod (apx_t A b (2 ^ k)) (apx_t A b (2 ^ k)))"
    and "\<And>j U. U \<in> set (fine2_gates k n \<theta>s (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)))
           \<Longrightarrow> (U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<and> U \<noteq> hhl_rot_stage A t0 (2 ^ k) C)
               \<or> elementary K U \<or> (\<exists>a. U = cv0 k n (Rot a))"
proof -
  have N: "2 \<le> (2::nat) ^ k" using power_increasing[of 1 k "2::nat"] k by simp
  interpret state_sig "[2 ^ k, n, 2]" .
  have dd: "d = K" by (simp add: d_def K_def)
  note ab = apx_basics[OF A t0 N C th lmin spec b e NQ V Vc eta Prep small]
  have m0: "0 < n * 2" using ab(1) by simp
  have n0: "0 < n" using ab(1) by simp
  have rs: "hhl_rot_stage A t0 (2 ^ k) C = ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta>s c))"
    unfolding \<theta>s_def by (rule rot_stage_ucr) (use A(1) in simp)
  have Mc: "anc_proj d 0 \<in> carrier_mat d d" by simp
  have ok: "\<And>U. U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c') \<Longrightarrow> U \<in> carrier_mat d d \<and> Complex_Matrix.unitary U"
    if g: "gates_ok K c'" for c'
    using qgates_ok[OF ab(2,3) g[unfolded K_def]] dd K_def by simp
  have tr: "hoare_total_correct P (prog_meas d (anc_proj d) (fine2_gates k n \<theta>s (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c'))) Q"
    if g: "gates_ok K c'" and h: "hoare_total_correct P (prog_meas d (anc_proj d) (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c')) Q" for c' P Q
  proof -
    note f = fine2_gates_props[where k = k and n = n and \<theta> = \<theta>s and Us = "qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c'", OF ok[OF g, unfolded dd K_def] n0]
    show ?thesis
      by (rule meas_transfer(1)[OF _ ok[OF g] _ _ Mc h]) (use ab(1) f(1,2) dd K_def in auto)
  qed
  show "hoare_total_correct (complex_of_real ((C * t0 / pi)\<^sup>2 * (1 - (apx_e A b (2 ^ k) C \<epsilon> \<eta>)\<^sup>2)) \<cdot>\<^sub>m 1\<^sub>m K)
     (prog_meas K (anc_proj K) (fine2_gates k n \<theta>s (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) c)))
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
               (prog_meas K (anc_proj K) (fine2_gates k n \<theta>s (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j))))
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
  show "\<And>j U. U \<in> set (fine2_gates k n \<theta>s (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)))
           \<Longrightarrow> (U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<and> U \<noteq> hhl_rot_stage A t0 (2 ^ k) C)
               \<or> elementary K U \<or> (\<exists>a. U = cv0 k n (Rot a))"
  proof -
    fix j U assume U: "U \<in> set (fine2_gates k n \<theta>s (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)))"
    have g: "gates_ok K (aa_prog K 2 (\<lambda>c. c = 1) c j)" unfolding K_def c_def by (rule gates_ok_aa_prog[OF ab(4)])
    have okU: "\<And>W. W \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<Longrightarrow>
               W \<in> carrier_mat (2 ^ k * (n * 2)) (2 ^ k * (n * 2)) \<and> Complex_Matrix.unitary W"
      using qgates_ok[OF ab(2,3), where c = "aa_prog K 2 (\<lambda>c. c = 1) c j"] g by (simp add: K_def)
    have "(U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<and> U \<noteq> ctrl_blocks (2 ^ k) (n * 2) (\<lambda>c. 1\<^sub>m n \<Otimes> Rot (\<theta>s c)))
          \<or> elementary (2 ^ k * (n * 2)) U \<or> (\<exists>a. U = cv0 k n (Rot a))"
      by (rule fine2_gates_props(3)[OF okU n0 U])
    thus "(U \<in> set (qgates (2 ^ k) (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog K 2 (\<lambda>c. c = 1) c j)) \<and> U \<noteq> hhl_rot_stage A t0 (2 ^ k) C)
          \<or> elementary K U \<or> (\<exists>a. U = cv0 k n (Rot a))" unfolding rs by (simp add: K_def)
  qed
qed

end
