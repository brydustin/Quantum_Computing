theory HHL_Reduction
  imports HHL_Runtime
begin

section \<open>The reduction from circuits to matrix inversion\<close>

text \<open>The construction behind the optimality results of the HHL paper (Section III, App.~A5).
A circuit $U_1,\dots,U_T$ becomes the unitary $\mathcal U$ on a clock register of size $3T$, and
$A=I-e^{-1/T}\mathcal U$.  We prove that $A^{-1}(\ket0\otimes\psi)$ is the finite sum
$\sum_{c<3T}e^{-c/T}\ket c\otimes W_c\psi/(1-e^{-3})$, that $(1-e^{-1/T})\norm v\le\norm{Av}\le(1+e^{-1/T})\norm v$
(so $\kappa\le2T+1$), that the clock lies in $[T,2T)$ with probability
$e^{-2}/(1+e^{-2}+e^{-4})\ge1/10$, and that then the system register holds $U_T\cdots U_1\psi$.
The complexity-theoretic consequences (Theorems 4--6) are outside the library.\<close>


text \<open>Section III and App.~A5 of the paper: a circuit $U_1,\dots,U_T$ on $\C^m$ is turned into a
unitary $\mathcal U$ on $\C^{3T}\otimes\C^m$ that applies $U_1,\dots,U_T$, then $T$ identities, then
$U_T^*,\dots,U_1^*$ while advancing a clock modulo $3T$.  (The paper writes $U^*_{3T+1-t}$ for the
third block; with $t=1,\dots,T$ this must be $U^*_{T+1-t}$.)  Clock value $c$ is $0$-indexed.\<close>

definition red_gate :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "red_gate T m Ug c = (if c < T then Ug (c + 1) else if c < 2 * T then 1\<^sub>m m else ((Ug (3 * T - c))\<^sup>\<dagger>))"

definition red_U :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "red_U T m Ug = Matrix.mat (3 * T * m) (3 * T * m)
     (\<lambda>(r, s). if r div m = Suc (s div m) mod (3 * T) then red_gate T m Ug (s div m) $$ (r mod m, s mod m) else 0)"

lemma red_U_carrier [simp]: "red_U T m Ug \<in> carrier_mat (3 * T * m) (3 * T * m)"
  by (simp add: red_U_def)

lemma sum_split_add:
  fixes a b :: nat and g :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>s<a + b. g s) = (\<Sum>s<a. g s) + (\<Sum>j<b. g (a + j))"
  by (induction b) (simp_all add: add_ac)

lemma block_div_mod:
  fixes b j m :: nat
  shows "j < m \<Longrightarrow> (b * m + j) div m = b \<and> (b * m + j) mod m = j"
  by simp

definition red_A :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "red_A T m Ug = 1\<^sub>m (3 * T * m) - complex_of_real (exp (- 1 / real T)) \<cdot>\<^sub>m red_U T m Ug"

definition red_coeff :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "red_coeff T c = exp (- real c / real T) / (1 - exp (- 3))"

lemma blk_reg_sum: "c < K \<Longrightarrow> dim_vec (f c) = m \<Longrightarrow> blk m (reg_sum K m f) c = f c"
  by (intro eq_vecI) (simp_all add: blk_def reg_sum_index)

text \<open>The clock distribution: $\Pr(T\le c<2T)=e^{-2}/(1+e^{-2}+e^{-4})\ge1/10$.\<close>

lemma geometric_thirds:
  fixes q :: real and T :: nat
  shows "(\<Sum>c<3 * T. q ^ c) = (1 + q ^ T + q ^ (2 * T)) * (\<Sum>c<T. q ^ c)"
    and "(\<Sum>c\<in>{T..<2 * T}. q ^ c) = q ^ T * (\<Sum>c<T. q ^ c)"
proof -
  have e: "3 * T = T + T + T" "2 * T = T + T" by simp_all
  have a: "(\<Sum>j<T. q ^ (T + j)) = q ^ T * (\<Sum>c<T. q ^ c)" by (simp add: power_add sum_distrib_left)
  have b: "(\<Sum>j<T. q ^ (T + T + j)) = q ^ (2 * T) * (\<Sum>c<T. q ^ c)"
    by (simp add: power_add sum_distrib_left mult_2)
  show "(\<Sum>c<3 * T. q ^ c) = (1 + q ^ T + q ^ (2 * T)) * (\<Sum>c<T. q ^ c)"
    unfolding e(1) sum_split_add[of _ "T + T" T] sum_split_add[of _ T T] a b by (simp only: distrib_right mult_1)
  have "(\<Sum>c\<in>{T..<2 * T}. q ^ c) = (\<Sum>j<T. q ^ (T + j))"
  proof -
    have iv: "{T..<2 * T} = {0 + T..<T + T}" by (simp add: mult_2)
    have "(\<Sum>c\<in>{0 + T..<T + T}. q ^ c) = (\<Sum>j\<in>{0..<T}. q ^ (j + T))" by (rule sum.shift_bounds_nat_ivl)
    thus ?thesis unfolding iv by (simp add: atLeast0LessThan add.commute)
  qed
  thus "(\<Sum>c\<in>{T..<2 * T}. q ^ c) = q ^ T * (\<Sum>c<T. q ^ c)" by (simp add: power_add sum_distrib_left)
qed

lemma tenth_bound: "1 / 10 \<le> exp (- 2) / (1 + exp (- 2) + exp (- 4) :: real)"
proof -
  let ?y = "exp (- 2) :: real"
  have y4: "exp (- 4) = ?y\<^sup>2" by (simp add: power2_eq_square exp_add[symmetric])
  have "(15 / 16 :: real) ^ 32 \<le> exp (- 1 / 16) ^ 32"
    using exp_ge_add_one_self[of "- 1 / 16"] by (intro power_mono) simp_all
  also have "exp (- 1 / 16) ^ 32 = ?y" by (simp add: exp_of_nat_mult[symmetric])
  finally have y1: "(15 / 16 :: real) ^ 32 \<le> ?y" .
  have n: "1 / 8 \<le> (15 / 16 :: real) ^ 32" by (simp add: power_divide)
  have ylo: "1 / 8 \<le> ?y" using n y1 by linarith
  have yhi: "?y \<le> 1" by simp
  have "1 \<le> ?y * (9 - ?y)"
  proof -
    have "8 * ?y \<le> ?y * (9 - ?y)" using yhi by (simp add: algebra_simps)
    thus ?thesis using ylo by linarith
  qed
  hence "1 + ?y + ?y\<^sup>2 \<le> 10 * ?y" by (simp add: algebra_simps power2_eq_square)
  moreover have dpos: "0 < 1 + ?y + ?y\<^sup>2" by (simp add: add_pos_nonneg)
  ultimately show ?thesis unfolding y4 by (simp add: le_divide_eq)
qed

context
  fixes T m :: nat and Ug :: "nat \<Rightarrow> complex Matrix.mat"
  assumes T0: "0 < T" and Ug: "\<forall>j. 1 \<le> j \<longrightarrow> j \<le> T \<longrightarrow> Ug j \<in> carrier_mat m m \<and> unitary (Ug j)"
begin

abbreviation "D \<equiv> 3 * T"
abbreviation "V \<equiv> red_gate T m Ug"

lemma V_ok: "c < D \<Longrightarrow> V c \<in> carrier_mat m m \<and> unitary (V c)"
proof -
  assume c: "c < D"
  consider "c < T" | "T \<le> c" "c < 2 * T" | "2 * T \<le> c" by linarith
  thus ?thesis
  proof cases
    case 1 thus ?thesis using Ug[rule_format, of "c + 1"] by (simp add: red_gate_def)
  next
    case 2 thus ?thesis by (simp add: red_gate_def id_is_unitary)
  next
    case 3
    have "1 \<le> 3 * T - c" "3 * T - c \<le> T" using 3 c by simp_all
    thus ?thesis using 3 Ug[rule_format, of "3 * T - c"] by (simp add: red_gate_def dagger_carrier unitary_dagger)
  qed
qed

text \<open>The action on block vectors: block $c'$ of $\mathcal Ux$ is $V_{c'-1}x_{c'-1}$ (indices mod $3T$).\<close>

definition prev :: "nat \<Rightarrow> nat" where "prev c = (c + D - 1) mod D"

lemma prev_lt: "prev c < D" using T0 by (simp add: prev_def)

lemma prev_zero: "prev 0 = D - 1" using T0 by (simp add: prev_def)

lemma suc_prev: "c < D \<Longrightarrow> Suc (prev c) mod D = c"
proof -
  assume c: "c < D"
  show ?thesis
  proof (cases "c = 0")
    case True thus ?thesis using T0 by (simp add: prev_def mod_Suc)
  next
    case False
    hence e: "c + D - 1 = (c - 1) + D" by simp
    have "prev c = c - 1" unfolding prev_def e using c by simp
    thus ?thesis using False c by simp
  qed
qed

lemma prev_suc: "s < D \<Longrightarrow> prev (Suc s mod D) = s"
proof -
  assume s: "s < D"
  show ?thesis
  proof (cases "Suc s = D")
    case True thus ?thesis using T0 by (simp add: prev_def)
  next
    case False
    hence "Suc s mod D = Suc s" using s by simp
    thus ?thesis using T0 s by (simp add: prev_def)
  qed
qed

lemma prev_bij: "bij_betw prev {..<D} {..<D}"
proof (rule bij_betw_imageI)
  show "inj_on prev {..<D}"
  proof (rule inj_onI)
    fix a b assume a: "a \<in> {..<D}" and b: "b \<in> {..<D}" and e: "prev a = prev b"
    have "Suc (prev a) mod D = Suc (prev b) mod D" using e by simp
    thus "a = b" using suc_prev[of a] suc_prev[of b] a b by simp
  qed
  show "prev ` {..<D} = {..<D}"
  proof
    show "prev ` {..<D} \<subseteq> {..<D}" using prev_lt by auto
    show "{..<D} \<subseteq> prev ` {..<D}"
    proof
      fix b assume b: "b \<in> {..<D}"
      have "prev (Suc b mod D) = b" using prev_suc b by simp
      moreover have "Suc b mod D \<in> {..<D}" using T0 by simp
      ultimately show "b \<in> prev ` {..<D}" by (metis image_eqI)
    qed
  qed
qed

lemma cond_prev: "b < D \<Longrightarrow> c < D \<Longrightarrow> (c = Suc b mod D) = (b = prev c)"
  using suc_prev prev_suc by metis

lemma red_U_reg_sum:
  assumes f: "\<And>c. c < D \<Longrightarrow> dim_vec (f c) = m"
  shows "red_U T m Ug *\<^sub>v reg_sum D m f = reg_sum D m (\<lambda>c. V (prev c) *\<^sub>v f (prev c))"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (reg_sum D m (\<lambda>c. V (prev c) *\<^sub>v f (prev c)))"
  hence r: "r < D * m" by simp
  note ri = less_mult_imp_div_less[OF r] reg_sum_index_mod[OF r]
  let ?c = "r div m" and ?i = "r mod m"
  have Vp: "V (prev ?c) \<in> carrier_mat m m" using V_ok[OF prev_lt] by simp
  have "(red_U T m Ug *\<^sub>v reg_sum D m f) $ r
        = (\<Sum>s<D * m. (if ?c = Suc (s div m) mod D then V (s div m) $$ (?i, s mod m) else 0) * f (s div m) $ (s mod m))"
    using r by (simp add: red_U_def scalar_prod_def atLeast0LessThan reg_sum_def)
  also have "\<dots> = (\<Sum>b<D. \<Sum>j<m. (if ?c = Suc b mod D then V b $$ (?i, j) else 0) * f b $ j)"
    unfolding sum_blocks by (intro sum.cong refl) (simp add: block_div_mod)
  also have "\<dots> = (\<Sum>b<D. if b = prev ?c then (\<Sum>j<m. V b $$ (?i, j) * f b $ j) else 0)"
    by (intro sum.cong refl) (simp add: cond_prev ri(1))
  also have "\<dots> = (\<Sum>j<m. V (prev ?c) $$ (?i, j) * f (prev ?c) $ j)" using prev_lt by simp
  also have "\<dots> = reg_sum D m (\<lambda>c. V (prev c) *\<^sub>v f (prev c)) $ r"
    using r ri Vp f[OF prev_lt] by (simp add: reg_sum_def scalar_prod_def atLeast0LessThan)
  finally show "(red_U T m Ug *\<^sub>v reg_sum D m f) $ r = reg_sum D m (\<lambda>c. V (prev c) *\<^sub>v f (prev c)) $ r" .
qed (simp add: red_U_def)

text \<open>The gates applied in the first $k$ clock steps.\<close>

primrec W :: "nat \<Rightarrow> complex Matrix.mat" where
  "W 0 = 1\<^sub>m m"
| "W (Suc k) = V (k mod D) * W k"

primrec circ :: "nat \<Rightarrow> complex Matrix.mat" where
  "circ 0 = 1\<^sub>m m"
| "circ (Suc t) = Ug (Suc t) * circ t"

lemma W_carrier: "W k \<in> carrier_mat m m"
proof (induction k)
  case (Suc k)
  have "k mod D < D" using T0 by simp
  thus ?case using mult_carrier_mat[OF conjunct1[OF V_ok] Suc.IH] by simp
qed simp

lemma W_unitary: "unitary (W k)"
proof (induction k)
  case 0 show ?case by (simp add: id_is_unitary)
next
  case (Suc k)
  have kD: "k mod D < D" using T0 by simp
  show ?case unfolding W.simps
    by (rule unitary_mult[OF conjunct2[OF V_ok[OF kD]] Suc conjunct1[OF V_ok[OF kD]] W_carrier])
qed

lemma circ_carrier: "t \<le> T \<Longrightarrow> circ t \<in> carrier_mat m m"
proof (induction t)
  case (Suc t)
  have "Ug (Suc t) \<in> carrier_mat m m" using Ug[rule_format, of "Suc t"] Suc.prems by simp
  thus ?case using mult_carrier_mat[OF _ Suc.IH] Suc.prems by simp
qed simp

lemma W_circ: "k \<le> T \<Longrightarrow> W k = circ k"
proof (induction k)
  case (Suc k)
  have "k mod D = k" using Suc.prems by simp
  moreover have "V k = Ug (Suc k)" using Suc.prems by (simp add: red_gate_def)
  ultimately show ?case using Suc by simp
qed simp

lemma W_middle: "T \<le> k \<Longrightarrow> k \<le> 2 * T \<Longrightarrow> W k = circ T"
proof (induction k)
  case 0 thus ?case using T0 by simp
next
  case (Suc k)
  show ?case
  proof (cases "Suc k = T")
    case True thus ?thesis using W_circ[of "Suc k"] by simp
  next
    case False
    hence k: "T \<le> k" "k < 2 * T" using Suc.prems by simp_all
    have "k mod D = k" using k by simp
    moreover have "V k = 1\<^sub>m m" using k by (simp add: red_gate_def)
    ultimately show ?thesis using Suc.IH[OF k(1)] k circ_carrier[of T] by simp
  qed
qed

lemma W_undo: "j \<le> T \<Longrightarrow> W (2 * T + j) = circ (T - j)"
proof (induction j)
  case 0 thus ?case using W_middle[of "2 * T"] by simp
next
  case (Suc j)
  have j: "j < T" using Suc.prems by simp
  have km: "(2 * T + j) mod D = 2 * T + j" using j by simp
  have Vk: "V (2 * T + j) = ((Ug (T - j))\<^sup>\<dagger>)" using j by (simp add: red_gate_def)
  have Tj: "T - j = Suc (T - Suc j)" using j by simp
  have U: "Ug (T - j) \<in> carrier_mat m m" "unitary (Ug (T - j))" using Ug[rule_format, of "T - j"] j by simp_all
  have C: "circ (T - Suc j) \<in> carrier_mat m m" by (rule circ_carrier) simp
  have "W (2 * T + Suc j) = (Ug (T - j))\<^sup>\<dagger> * circ (T - j)" using Suc.IH j km Vk by simp
  also have "circ (T - j) = Ug (T - j) * circ (T - Suc j)" unfolding Tj by simp
  also have "(Ug (T - j))\<^sup>\<dagger> * (Ug (T - j) * circ (T - Suc j)) = ((Ug (T - j))\<^sup>\<dagger> * Ug (T - j)) * circ (T - Suc j)"
    by (rule assoc_mult_mat[OF dagger_carrier[OF U(1)] U(1) C, symmetric])
  also have "(Ug (T - j))\<^sup>\<dagger> * Ug (T - j) = 1\<^sub>m m" using U unfolding unitary_def by auto
  finally show ?case using C by simp
qed

lemma W_cycle: "W D = 1\<^sub>m m"
  using W_undo[of T] by (simp add: numeral_3_eq_3 algebra_simps)

lemma W_suc: "c < D \<Longrightarrow> W (Suc c) = V c * W c"
  by simp

lemma W_zero: "W 0 = 1\<^sub>m m"
  by simp


abbreviation "UU \<equiv> red_U T m Ug"
lemma Wdim [simp]: "dim_row (W k) = m" "dim_col (W k) = m" using carrier_matD[OF W_carrier] by simp_all
lemma Vpdim [simp]: "dim_row (V (prev c)) = m" "dim_col (V (prev c)) = m" using carrier_matD[OF conjunct1[OF V_ok[OF prev_lt]]] by simp_all

definition ket0 :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "ket0 \<psi> = reg_sum D m (\<lambda>c. if c = 0 then \<psi> else 0\<^sub>v m)"

definition red_x :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "red_x \<psi> = reg_sum D m (\<lambda>c. complex_of_real (red_coeff T c) \<cdot>\<^sub>v (W c *\<^sub>v \<psi>))"

lemma dim_ket0: "dim_vec (ket0 \<psi>) = D * m" by (simp add: ket0_def)
lemma dim_red_x: "dim_vec (red_x \<psi>) = D * m" by (simp add: red_x_def)

lemma coeff_step: "exp (- 1 / real T) * red_coeff T c = red_coeff T (Suc c)"
proof -
  have "exp (- 1 / real T) * exp (- real c / real T) = exp (- real (Suc c) / real T)"
    unfolding exp_add[symmetric] by (rule arg_cong[where f = exp]) (use T0 in \<open>simp add: field_simps\<close>)
  thus ?thesis unfolding red_coeff_def by (simp add: mult.assoc[symmetric] times_divide_eq_right[symmetric])
qed

lemma coeff_last: "exp (- 1 / real T) * red_coeff T (D - 1) = exp (- 3) / (1 - exp (- 3))"
proof -
  have "Suc (D - 1) = D" using T0 by simp
  hence "exp (- 1 / real T) * red_coeff T (D - 1) = red_coeff T D" using coeff_step[of "D - 1"] by simp
  also have "red_coeff T D = exp (- 3) / (1 - exp (- 3))" unfolding red_coeff_def using T0 by simp
  finally show ?thesis .
qed

theorem red_inverse:
  assumes \<psi>: "dim_vec \<psi> = m"
  shows "red_A T m Ug *\<^sub>v red_x \<psi> = ket0 \<psi>"
proof -
  let ?e = "complex_of_real (exp (- 1 / real T))"
  let ?f = "\<lambda>c. complex_of_real (red_coeff T c) \<cdot>\<^sub>v (W c *\<^sub>v \<psi>)"
  have df: "dim_vec (?f c) = m" for c using W_carrier[where k = c] by simp
  have xc: "red_x \<psi> \<in> carrier_vec (D * m)" unfolding red_x_def by (rule carrier_vecI) simp
  have Ux: "UU *\<^sub>v red_x \<psi> = reg_sum D m (\<lambda>c. V (prev c) *\<^sub>v ?f (prev c))"
    unfolding red_x_def by (rule red_U_reg_sum) simp
  have "red_A T m Ug *\<^sub>v red_x \<psi> = red_x \<psi> - ?e \<cdot>\<^sub>v (UU *\<^sub>v red_x \<psi>)"
  proof -
    have "red_A T m Ug *\<^sub>v red_x \<psi> = 1\<^sub>m (D * m) *\<^sub>v red_x \<psi> - (?e \<cdot>\<^sub>m UU) *\<^sub>v red_x \<psi>"
      unfolding red_A_def by (rule minus_mult_distrib_mat_vec[OF one_carrier_mat smult_carrier_mat[OF red_U_carrier] xc])
    thus ?thesis using xc smult_mat_mult_vec[of UU "D * m" "D * m" "red_x \<psi>" ?e] by simp
  qed
  also have "?e \<cdot>\<^sub>v (UU *\<^sub>v red_x \<psi>) = reg_sum D m (\<lambda>c. ?e \<cdot>\<^sub>v (V (prev c) *\<^sub>v ?f (prev c)))"
    unfolding Ux by (rule reg_sum_smult) simp
  also have "red_x \<psi> - \<dots> = reg_sum D m (\<lambda>c. ?f c - ?e \<cdot>\<^sub>v (V (prev c) *\<^sub>v ?f (prev c)))"
    unfolding red_x_def by (rule reg_sum_diff) simp
  also have "\<dots> = ket0 \<psi>" unfolding ket0_def
  proof (rule reg_sum_cong)
    fix c assume c: "c < D"
    have Vp: "V (prev c) \<in> carrier_mat m m" using V_ok[OF prev_lt] by simp
    have Wpc: "W (prev c) \<in> carrier_mat m m" by (rule W_carrier)
    have step: "V (prev c) *\<^sub>v ?f (prev c) = complex_of_real (red_coeff T (prev c)) \<cdot>\<^sub>v (W (Suc (prev c)) *\<^sub>v \<psi>)"
    proof -
      have "V (prev c) *\<^sub>v ?f (prev c) = complex_of_real (red_coeff T (prev c)) \<cdot>\<^sub>v (V (prev c) *\<^sub>v (W (prev c) *\<^sub>v \<psi>))"
        by (rule mult_mat_vec[OF Vp], rule carrier_vecI) (use Wpc \<psi> in simp)
      also have "V (prev c) *\<^sub>v (W (prev c) *\<^sub>v \<psi>) = W (Suc (prev c)) *\<^sub>v \<psi>"
        using assoc_mult_mat_vec[OF Vp Wpc carrier_vecI[OF \<psi>]] W_suc[OF prev_lt] by simp
      finally show ?thesis .
    qed
    show "?f c - ?e \<cdot>\<^sub>v (V (prev c) *\<^sub>v ?f (prev c)) = (if c = 0 then \<psi> else 0\<^sub>v m)"
    proof (cases "c = 0")
      case True
      have pc: "prev c = D - 1" unfolding True by (rule prev_zero)
      have W0: "W (Suc (prev c)) = 1\<^sub>m m" unfolding pc using W_cycle T0 by simp
      have W00: "W 0 = 1\<^sub>m m" by (rule W_zero)
      have Wz: "W 0 *\<^sub>v \<psi> = \<psi>" unfolding W00 using one_mult_mat_vec[OF carrier_vecI[OF \<psi>]] .
      have c0: "red_coeff T 0 = 1 / (1 - exp (- 3))" by (simp add: red_coeff_def)
      have f0: "?f c = complex_of_real (1 / (1 - exp (- 3))) \<cdot>\<^sub>v \<psi>" unfolding True Wz c0 ..
      have s0: "?e \<cdot>\<^sub>v (V (prev c) *\<^sub>v ?f (prev c)) = complex_of_real (exp (- 3) / (1 - exp (- 3))) \<cdot>\<^sub>v \<psi>"
      proof -
        have "?e \<cdot>\<^sub>v (V (prev c) *\<^sub>v ?f (prev c)) = (?e * complex_of_real (red_coeff T (prev c))) \<cdot>\<^sub>v \<psi>"
          unfolding step W0 using \<psi> by (simp add: smult_smult_assoc carrier_vecI[OF \<psi>])
        also have "?e * complex_of_real (red_coeff T (prev c)) = complex_of_real (exp (- 3) / (1 - exp (- 3)))"
          unfolding pc coeff_last[symmetric] by simp
        finally show ?thesis .
      qed
      have "?f c - ?e \<cdot>\<^sub>v (V (prev c) *\<^sub>v ?f (prev c))
            = complex_of_real (1 / (1 - exp (- 3))) \<cdot>\<^sub>v \<psi> - complex_of_real (exp (- 3) / (1 - exp (- 3))) \<cdot>\<^sub>v \<psi>"
        unfolding f0 s0 ..
      also have "\<dots> = \<psi>"
      proof -
        have "1 / (1 - exp (- 3)) - exp (- 3) / (1 - exp (- 3)) = (1::real)"
        proof -
          have "exp (- 3) < (1::real)" by simp
          thus ?thesis by (simp add: field_simps)
        qed
        hence "complex_of_real (1 / (1 - exp (- 3))) - complex_of_real (exp (- 3) / (1 - exp (- 3))) = 1"
          by (metis of_real_1 of_real_diff)
        hence h: "z / (1 - complex_of_real (exp (- 3))) - complex_of_real (exp (- 3)) * z / (1 - complex_of_real (exp (- 3))) = z" for z
        proof -
          assume one: "complex_of_real (1 / (1 - exp (- 3))) - complex_of_real (exp (- 3) / (1 - exp (- 3))) = 1"
          have "z / (1 - complex_of_real (exp (- 3))) - complex_of_real (exp (- 3)) * z / (1 - complex_of_real (exp (- 3)))
                = (complex_of_real (1 / (1 - exp (- 3))) - complex_of_real (exp (- 3) / (1 - exp (- 3)))) * z"
            by (simp add: algebra_simps diff_divide_distrib)
          thus ?thesis unfolding one by simp
        qed
        show ?thesis using \<psi> h by (intro eq_vecI) simp_all
      qed
      finally show ?thesis using True by simp
    next
      case False
      have pc: "Suc (prev c) = c"
      proof (cases "Suc (prev c) = D")
        case True thus ?thesis using suc_prev[OF c] False by simp
      next
        case nd: False
        hence "Suc (prev c) < D" using prev_lt[where c = c] by simp
        thus ?thesis using suc_prev[OF c] by simp
      qed
      have "?f c - ?e \<cdot>\<^sub>v (V (prev c) *\<^sub>v ?f (prev c)) = 0\<^sub>v m"
        unfolding step pc using \<psi> W_carrier[where k = c] coeff_step[of "prev c", unfolded pc]
        by (intro eq_vecI) (simp_all flip: of_real_mult)
      thus ?thesis using False by simp
    qed
  qed
  finally show ?thesis .
qed



lemma Udim [simp]: "dim_row UU = D * m" "dim_col UU = D * m" by (simp_all add: red_U_def)

text \<open>$\mathcal U$ preserves norms, so $(1-e^{-1/T})\norm v\le\norm{Av}\le(1+e^{-1/T})\norm v$.\<close>

lemma red_U_norm:
  assumes v: "dim_vec v = D * m"
  shows "\<parallel>UU *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
proof -
  let ?f = "blk m v"
  have vv: "reg_sum D m ?f = v" by (rule reg_sum_blk[OF v])
  have "UU *\<^sub>v reg_sum D m ?f = reg_sum D m (\<lambda>c. V (prev c) *\<^sub>v ?f (prev c))" by (rule red_U_reg_sum) simp
  hence Uv: "UU *\<^sub>v v = reg_sum D m (\<lambda>c. V (prev c) *\<^sub>v ?f (prev c))" by (simp only: vv)
  have dV: "dim_vec (V (prev c) *\<^sub>v ?f (prev c)) = m" for c using carrier_matD(1)[OF conjunct1[OF V_ok[OF prev_lt[where c = c]]]] by simp
  have "\<parallel>UU *\<^sub>v v\<parallel>\<^sup>2 = (\<Sum>c<D. \<parallel>V (prev c) *\<^sub>v ?f (prev c)\<parallel>\<^sup>2)" unfolding Uv by (rule vnorm_reg_sum_sq) (rule dV)
  also have "\<dots> = (\<Sum>c<D. \<parallel>?f (prev c)\<parallel>\<^sup>2)"
    by (rule sum.cong[OF refl]) (simp add: unitary_vnorm[OF conjunct1[OF V_ok[OF prev_lt]] conjunct2[OF V_ok[OF prev_lt]]])
  also have "\<dots> = (\<Sum>c<D. \<parallel>?f c\<parallel>\<^sup>2)" by (rule sum.reindex_bij_betw[OF prev_bij])
  also have "\<dots> = \<parallel>v\<parallel>\<^sup>2" using vnorm_reg_sum_sq[of D ?f m] vv by simp
  finally show ?thesis using vnorm_ge0 by (metis power2_eq_iff_nonneg)
qed

lemma red_A_mult:
  assumes v: "dim_vec v = D * m"
  shows "red_A T m Ug *\<^sub>v v = v - complex_of_real (exp (- 1 / real T)) \<cdot>\<^sub>v (UU *\<^sub>v v)"
proof -
  have vc: "v \<in> carrier_vec (D * m)" by (rule carrier_vecI[OF v])
  have "red_A T m Ug *\<^sub>v v = 1\<^sub>m (D * m) *\<^sub>v v - (complex_of_real (exp (- 1 / real T)) \<cdot>\<^sub>m UU) *\<^sub>v v"
    unfolding red_A_def by (rule minus_mult_distrib_mat_vec[OF one_carrier_mat smult_carrier_mat[OF red_U_carrier] vc])
  thus ?thesis using vc smult_mat_mult_vec[OF red_U_carrier carrier_vecI[OF v]] by simp
qed

theorem red_A_bounds:
  assumes v: "dim_vec v = D * m"
  shows "(1 - exp (- 1 / real T)) * \<parallel>v\<parallel> \<le> \<parallel>red_A T m Ug *\<^sub>v v\<parallel>"
    and "\<parallel>red_A T m Ug *\<^sub>v v\<parallel> \<le> (1 + exp (- 1 / real T)) * \<parallel>v\<parallel>"
proof -
  let ?e = "exp (- 1 / real T)" and ?u = "UU *\<^sub>v v"
  have du: "dim_vec ?u = D * m" by simp
  have nu: "\<parallel>complex_of_real ?e \<cdot>\<^sub>v ?u\<parallel> = ?e * \<parallel>v\<parallel>" unfolding cpx_vec_length_smult red_U_norm[OF v] by simp
  have A: "red_A T m Ug *\<^sub>v v = v - complex_of_real ?e \<cdot>\<^sub>v ?u" by (rule red_A_mult[OF v])
  show "\<parallel>red_A T m Ug *\<^sub>v v\<parallel> \<le> (1 + ?e) * \<parallel>v\<parallel>"
  proof -
    have "\<parallel>v - complex_of_real ?e \<cdot>\<^sub>v ?u\<parallel> \<le> \<parallel>v - 0\<^sub>v (D * m)\<parallel> + \<parallel>0\<^sub>v (D * m) - complex_of_real ?e \<cdot>\<^sub>v ?u\<parallel>"
      by (rule vnorm_diff_le[where n = "D * m"]) (simp_all add: v)
    also have "\<parallel>v - 0\<^sub>v (D * m)\<parallel> = \<parallel>v\<parallel>" using v by (simp add: cpx_vec_length_def)
    also have "\<parallel>0\<^sub>v (D * m) - complex_of_real ?e \<cdot>\<^sub>v ?u\<parallel> = \<parallel>complex_of_real ?e \<cdot>\<^sub>v ?u\<parallel>" by (simp add: cpx_vec_length_def)
    finally show ?thesis unfolding A nu by (simp add: algebra_simps)
  qed
  show "(1 - ?e) * \<parallel>v\<parallel> \<le> \<parallel>red_A T m Ug *\<^sub>v v\<parallel>"
  proof -
    have "\<bar>\<parallel>v\<parallel> - \<parallel>complex_of_real ?e \<cdot>\<^sub>v ?u\<parallel>\<bar> \<le> \<parallel>v - complex_of_real ?e \<cdot>\<^sub>v ?u\<parallel>" by (rule vnorm_reverse) (simp add: v)
    thus ?thesis unfolding A nu by (simp add: algebra_simps abs_le_iff)
  qed
qed

text \<open>Hence $\kappa(A)\le(1+e^{-1/T})/(1-e^{-1/T})\le2T+1$, i.e.\ $O(T)$.  (The paper's App.~A5 states
$\kappa\le2T$; the exact value $(1+e^{-1/T})/(1-e^{-1/T})=\coth\frac1{2T}$ is slightly larger.)\<close>

lemma red_kappa: "(1 + exp (- 1 / real T)) / (1 - exp (- 1 / real T)) \<le> 2 * real T + 1"
proof -
  let ?e = "exp (- 1 / real T)"
  have TR: "0 < real T" using T0 by simp
  have e1: "?e < 1" using TR by simp
  have "1 + 1 / real T \<le> exp (1 / real T)" using exp_ge_add_one_self[of "1 / real T"] by simp
  hence "?e * (1 + 1 / real T) \<le> ?e * exp (1 / real T)" by (intro mult_left_mono) simp_all
  also have "?e * exp (1 / real T) = 1" by (simp add: exp_minus[symmetric] exp_add[symmetric])
  finally have "?e * (real T + 1) \<le> real T" using TR by (simp add: field_simps)
  hence "1 + ?e \<le> (2 * real T + 1) * (1 - ?e)" by (simp add: algebra_simps)
  thus ?thesis using e1 by (simp add: divide_le_eq)
qed

corollary red_solution_unique:
  assumes \<psi>: "dim_vec \<psi> = m" and y: "dim_vec y = D * m" and Ay: "red_A T m Ug *\<^sub>v y = ket0 \<psi>"
  shows "y = red_x \<psi>"
proof -
  let ?x = "red_x \<psi>"
  have dx: "dim_vec ?x = D * m" by (rule dim_red_x)
  have Ac: "red_A T m Ug \<in> carrier_mat (D * m) (D * m)" unfolding red_A_def by (rule minus_carrier_mat[OF smult_carrier_mat[OF red_U_carrier]])
  have "red_A T m Ug *\<^sub>v (y - ?x) = red_A T m Ug *\<^sub>v y - red_A T m Ug *\<^sub>v ?x"
    by (rule mult_minus_distrib_mat_vec[OF Ac]) (simp_all add: carrier_vecI y dx)
  also have "\<dots> = 0\<^sub>v (D * m)"
  proof -
    have ri: "red_A T m Ug *\<^sub>v ?x = ket0 \<psi>" by (rule red_inverse[OF \<psi>])
    have dk: "dim_vec (ket0 \<psi>) = D * m" by (rule dim_ket0)
    show ?thesis unfolding Ay ri using dk by (intro eq_vecI) simp_all
  qed
  finally have "\<parallel>red_A T m Ug *\<^sub>v (y - ?x)\<parallel> = 0" by (simp add: cpx_vec_length_def)
  hence "(1 - exp (- 1 / real T)) * \<parallel>y - ?x\<parallel> \<le> 0" using red_A_bounds(1)[of "y - ?x"] y dx by simp
  moreover have "0 < 1 - exp (- 1 / real T)" using T0 by simp
  ultimately have "\<parallel>y - ?x\<parallel> = 0" using vnorm_ge0[of "y - ?x"] by (simp add: mult_le_0_iff)
  hence z: "y - ?x = 0\<^sub>v (D * m)" using cpx_vec_length_zero_iff[of "y - ?x"] y dx by simp
  show ?thesis
  proof (rule eq_vecI)
    fix i assume "i < dim_vec ?x"
    hence i: "i < D * m" using dx by simp
    have "(y - ?x) $ i = 0" using z i by simp
    thus "y $ i = ?x $ i" using i y dx by simp
  qed (simp add: y dx)
qed



lemma red_x_blocks:
  assumes \<psi>: "dim_vec \<psi> = m" and c: "c < 3 * T"
  shows "blk m (red_x \<psi>) c = complex_of_real (red_coeff T c) \<cdot>\<^sub>v (W c *\<^sub>v \<psi>)"
proof -
  have rx: "red_x \<psi> = reg_sum (3 * T) m (\<lambda>c. complex_of_real (red_coeff T c) \<cdot>\<^sub>v (W c *\<^sub>v \<psi>))"
    by (rule red_x_def)
  show ?thesis unfolding rx by (rule blk_reg_sum[OF c]) (use carrier_matD(1)[OF W_carrier[where k = c]] in simp)
qed

lemma red_x_block_norm:
  assumes \<psi>: "dim_vec \<psi> = m" "\<parallel>\<psi>\<parallel> = 1" and c: "c < 3 * T"
  shows "\<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2 = exp (- 2 / real T) ^ c / (1 - exp (- 3))\<^sup>2"
proof -
  have "\<parallel>blk m (red_x \<psi>) c\<parallel> = red_coeff T c"
    unfolding red_x_blocks[OF \<psi>(1) c] cpx_vec_length_smult norm_of_real unitary_vnorm[OF W_carrier W_unitary \<psi>(1)] \<psi>(2)
    by (simp add: red_coeff_def)
  hence "\<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2 = (red_coeff T c)\<^sup>2" by simp
  also have "\<dots> = exp (- 2 / real T) ^ c / (1 - exp (- 3))\<^sup>2"
  proof -
    have "(exp (- real c / real T))\<^sup>2 = exp (- 2 / real T) ^ c"
      by (simp add: power2_eq_square exp_add[symmetric] exp_of_nat_mult[symmetric] field_simps)
    thus ?thesis unfolding red_coeff_def by (simp add: power_divide)
  qed
  finally show ?thesis .
qed

theorem red_clock_prob:
  assumes \<psi>: "dim_vec \<psi> = m" "\<parallel>\<psi>\<parallel> = 1"
  shows "(\<Sum>c\<in>{T..<2 * T}. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2) / (\<Sum>c<3 * T. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2)
         = exp (- 2) / (1 + exp (- 2) + exp (- 4))"
    and "1 / 10 \<le> (\<Sum>c\<in>{T..<2 * T}. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2) / (\<Sum>c<3 * T. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2)"
proof -
  let ?q = "exp (- 2 / real T)" and ?d = "(1 - exp (- 3 :: real))\<^sup>2"
  have TR: "0 < real T" using T0 by simp
  have qT: "?q ^ T = exp (- 2)" using TR by (simp add: exp_of_nat_mult[symmetric])
  have q2T: "?q ^ (2 * T) = exp (- 4)" using TR by (simp add: exp_of_nat_mult[symmetric])
  have S0: "0 < (\<Sum>c<T. ?q ^ c)" using T0 by (intro sum_pos) auto
  have num: "(\<Sum>c\<in>{T..<2 * T}. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2) = exp (- 2) * (\<Sum>c<T. ?q ^ c) / ?d"
  proof -
    have "(\<Sum>c\<in>{T..<2 * T}. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2) = (\<Sum>c\<in>{T..<2 * T}. ?q ^ c / ?d)"
      by (rule sum.cong[OF refl]) (simp add: red_x_block_norm[OF \<psi>])
    also have "\<dots> = (\<Sum>c\<in>{T..<2 * T}. ?q ^ c) / ?d" by (simp add: sum_divide_distrib)
    finally show ?thesis unfolding geometric_thirds(2) qT .
  qed
  have den: "(\<Sum>c<3 * T. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2) = (1 + exp (- 2) + exp (- 4)) * (\<Sum>c<T. ?q ^ c) / ?d"
  proof -
    have "(\<Sum>c<3 * T. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2) = (\<Sum>c<3 * T. ?q ^ c / ?d)"
      by (rule sum.cong[OF refl]) (simp add: red_x_block_norm[OF \<psi>])
    also have "\<dots> = (\<Sum>c<3 * T. ?q ^ c) / ?d" by (simp add: sum_divide_distrib)
    finally show ?thesis unfolding geometric_thirds(1) qT q2T .
  qed
  have d0: "0 < ?d" by simp
  show eq: "(\<Sum>c\<in>{T..<2 * T}. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2) / (\<Sum>c<3 * T. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2)
         = exp (- 2) / (1 + exp (- 2) + exp (- 4))"
  proof -
    have cancel: "Sv \<noteq> 0 \<Longrightarrow> dv \<noteq> 0 \<Longrightarrow> (a * Sv / dv) / (b * Sv / dv) = a / (b::real)" for a b Sv dv
      by (simp add: field_simps)
    show ?thesis unfolding num den by (rule cancel) (use S0 d0 in simp_all)
  qed
  show "1 / 10 \<le> (\<Sum>c\<in>{T..<2 * T}. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2) / (\<Sum>c<3 * T. \<parallel>blk m (red_x \<psi>) c\<parallel>\<^sup>2)"
    unfolding eq by (rule tenth_bound)
qed

text \<open>The part of the solution with clock in $[T,2T)$ is a product state whose system part is the
circuit output $U_T\cdots U_1\psi$.\<close>

theorem red_post_state:
  assumes \<psi>: "dim_vec \<psi> = m"
  shows "reg_sum (3 * T) m (\<lambda>c. if T \<le> c \<and> c < 2 * T then blk m (red_x \<psi>) c else 0\<^sub>v m)
         = tensor_vec (Matrix.vec (3 * T) (\<lambda>c. if T \<le> c \<and> c < 2 * T then complex_of_real (red_coeff T c) else 0)) (circ T *\<^sub>v \<psi>)"
proof -
  have Cc: "circ T \<in> carrier_mat m m" using W_middle[where k = T] W_carrier[where k = T] by simp
  have dc: "dim_vec (circ T *\<^sub>v \<psi>) = m" using Cc by simp
  show ?thesis
    unfolding tensor_reg_sum[OF _ dc, of "Matrix.vec (3 * T) (\<lambda>c. if T \<le> c \<and> c < 2 * T then complex_of_real (red_coeff T c) else 0)" "3 * T", simplified]
  proof (rule reg_sum_cong)
    fix c assume c: "c < 3 * T"
    show "(if T \<le> c \<and> c < 2 * T then blk m (red_x \<psi>) c else 0\<^sub>v m)
          = Matrix.vec (3 * T) (\<lambda>c. if T \<le> c \<and> c < 2 * T then complex_of_real (red_coeff T c) else 0) $ c \<cdot>\<^sub>v (circ T *\<^sub>v \<psi>)"
      using c red_x_blocks[OF \<psi> c] W_middle[where k = c] dc by (auto intro: eq_vecI)
  qed
qed

end

end
