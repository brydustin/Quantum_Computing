theory HHL
  imports Phase_Estimation
begin

section \<open>The HHL algorithm\<close>

text \<open>Harrow, Hassidim and Lloyd's algorithm for $Ax=b$, $A$ Hermitian: phase estimation of
$e^{it_0A}$ writes the eigenvalue $\lambda$ of each eigencomponent into a register, a rotation
controlled by the register puts $C/\lambda$ into the amplitude of an ancilla $\ket1$, and phase
estimation is undone.  Measuring the ancilla in $\ket1$ leaves the system in
$A^{-1}b/\norm{A^{-1}b}$.  The space is register $\otimes$ (system $\otimes$ ancilla).\<close>

subsection \<open>Block-diagonal controlled operations\<close>

lemma div_mod_eq_iff:
  fixes r c m :: nat
  shows "r = c \<longleftrightarrow> r div m = c div m \<and> r mod m = c mod m"
  by (metis div_mult_mod_eq)

lemma ctrl_blocks_cong:
  assumes "\<And>k. k < N \<Longrightarrow> B k = B' k"
  shows "ctrl_blocks N m B = ctrl_blocks N m B'"
proof (rule eq_matI)
  fix r c assume "r < dim_row (ctrl_blocks N m B')" "c < dim_col (ctrl_blocks N m B')"
  hence r: "r < N * m" and c: "c < N * m" by simp_all
  have "r div m < N" using r by (simp add: less_mult_imp_div_less)
  thus "ctrl_blocks N m B $$ (r, c) = ctrl_blocks N m B' $$ (r, c)"
    using r c assms by (simp add: ctrl_blocks_index)
qed simp_all

lemma ctrl_blocks_one: "ctrl_blocks N m (\<lambda>_. 1\<^sub>m m) = 1\<^sub>m (N * m)"
proof (rule eq_matI)
  fix r c assume "r < dim_row (1\<^sub>m (N * m) :: complex Matrix.mat)" "c < dim_col (1\<^sub>m (N * m) :: complex Matrix.mat)"
  hence r: "r < N * m" and c: "c < N * m" by simp_all
  hence m: "0 < m" by (cases m) auto
  show "ctrl_blocks N m (\<lambda>_. 1\<^sub>m m) $$ (r, c) = 1\<^sub>m (N * m) $$ (r, c)"
    using r c m div_mod_eq_iff[of r c m] by (auto simp: ctrl_blocks_index)
qed simp_all

lemma sum_if_const: "(\<Sum>i\<in>A. if P then f i else 0) = (if P then (\<Sum>i\<in>A. f i) else 0)"
  by (cases P) simp_all

lemma tensor_unit_index:
  assumes "k' < N" "i' < m" "dim_vec w = m"
  shows "tensor_vec (unit_vec N k) w $ (k' * m + i') = (if k' = k then w $ i' else 0)"
  using tensor_vec_index[of "unit_vec N k" N w m "k' * m + i'"] block_index[OF assms(1,2)] assms
  by (simp add: unit_vec_def)

lemma ctrl_blocks_col_index:
  assumes "r < N * m" "k' < N" "i' < m"
  shows "ctrl_blocks N m B $$ (r, k' * m + i') = (if r div m = k' then B k' $$ (r mod m, i') else 0)"
  using block_index[OF assms(2,3)] assms(1) by (auto simp: ctrl_blocks_index)

lemma ctrl_blocks_row_index:
  assumes "c < N * m" "k' < N" "i' < m"
  shows "ctrl_blocks N m B $$ (k' * m + i', c) = (if k' = c div m then B k' $$ (i', c mod m) else 0)"
  using block_index[OF assms(2,3)] assms(1) by (auto simp: ctrl_blocks_index)

text \<open>On a basis state of the register, $\sum_k\ket k\bra k\otimes B_k$ applies $B_k$.\<close>

lemma ctrl_blocks_basis:
  assumes k: "k < N" and w: "dim_vec w = m" and B: "B k \<in> carrier_mat m m"
  shows "ctrl_blocks N m B *\<^sub>v tensor_vec (unit_vec N k) w = tensor_vec (unit_vec N k) (B k *\<^sub>v w)"
proof -
  have dt: "dim_vec (tensor_vec (unit_vec N k) w) = N * m" by (rule tensor_vec_dim) (simp_all add: w)
  have dt2: "dim_vec (tensor_vec (unit_vec N k) (B k *\<^sub>v w)) = N * m"
    by (rule tensor_vec_dim) (use B in simp_all)
  show ?thesis
  proof (rule eq_vecI)
    fix r assume "r < dim_vec (tensor_vec (unit_vec N k) (B k *\<^sub>v w))"
    hence r: "r < N * m" using dt2 by simp
    hence m: "0 < m" by (cases m) auto
    define k1 i where "k1 = r div m" and "i = r mod m"
    have k1: "k1 < N" unfolding k1_def using r by (simp add: less_mult_imp_div_less)
    have i: "i < m" unfolding i_def using m by simp
    have Bd: "dim_row (B k) = m" "dim_col (B k) = m" using B by auto
    have "(ctrl_blocks N m B *\<^sub>v tensor_vec (unit_vec N k) w) $ r =
          (\<Sum>c<N * m. ctrl_blocks N m B $$ (r, c) * tensor_vec (unit_vec N k) w $ c)"
      using r dt by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>k'<N. \<Sum>i'<m. ctrl_blocks N m B $$ (r, k' * m + i') *
                                       tensor_vec (unit_vec N k) w $ (k' * m + i'))"
      by (rule sum_blocks)
    also have "\<dots> = (\<Sum>k'<N. if k' = k \<and> k1 = k then (\<Sum>i'<m. B k $$ (i, i') * w $ i') else 0)"
    proof (rule sum.cong[OF refl])
      fix k' assume "k' \<in> {..<N}"
      hence k': "k' < N" by simp
      have "(\<Sum>i'<m. ctrl_blocks N m B $$ (r, k' * m + i') * tensor_vec (unit_vec N k) w $ (k' * m + i')) =
            (\<Sum>i'<m. if k' = k \<and> k1 = k then B k $$ (i, i') * w $ i' else 0)"
        by (rule sum.cong[OF refl])
           (auto simp: ctrl_blocks_col_index[OF r k'] tensor_unit_index[OF k' _ w] k1_def i_def)
      also have "\<dots> = (if k' = k \<and> k1 = k then (\<Sum>i'<m. B k $$ (i, i') * w $ i') else 0)"
        by (rule sum_if_const)
      finally show "(\<Sum>i'<m. ctrl_blocks N m B $$ (r, k' * m + i') * tensor_vec (unit_vec N k) w $ (k' * m + i')) =
            (if k' = k \<and> k1 = k then (\<Sum>i'<m. B k $$ (i, i') * w $ i') else 0)" .
    qed
    also have "\<dots> = (if k1 = k then (\<Sum>i'<m. B k $$ (i, i') * w $ i') else 0)" using k by auto
    also have "\<dots> = (if k1 = k then (B k *\<^sub>v w) $ i else 0)"
      using k i Bd w by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = tensor_vec (unit_vec N k) (B k *\<^sub>v w) $ r"
      using tensor_vec_index[of "unit_vec N k" N "B k *\<^sub>v w" m r] r Bd k1
      by (simp add: k1_def i_def unit_vec_def)
    finally show "(ctrl_blocks N m B *\<^sub>v tensor_vec (unit_vec N k) w) $ r =
                  tensor_vec (unit_vec N k) (B k *\<^sub>v w) $ r" .
  qed (use dt2 in simp)
qed

lemma ctrl_blocks_dagger:
  assumes B: "\<And>k. k < N \<Longrightarrow> B k \<in> carrier_mat m m"
  shows "(ctrl_blocks N m B)\<^sup>\<dagger> = ctrl_blocks N m (\<lambda>k. (B k)\<^sup>\<dagger>)"
proof (rule eq_matI)
  fix r c assume "r < dim_row (ctrl_blocks N m (\<lambda>k. (B k)\<^sup>\<dagger>))" "c < dim_col (ctrl_blocks N m (\<lambda>k. (B k)\<^sup>\<dagger>))"
  hence r: "r < N * m" and c: "c < N * m" by simp_all
  hence m: "0 < m" by (cases m) auto
  have rN: "r div m < N" using r by (simp add: less_mult_imp_div_less)
  have Bd: "dim_row (B (r div m)) = m" "dim_col (B (r div m)) = m" using B[OF rN] by auto
  show "(ctrl_blocks N m B)\<^sup>\<dagger> $$ (r, c) = ctrl_blocks N m (\<lambda>k. (B k)\<^sup>\<dagger>) $$ (r, c)"
    using r c m Bd by (auto simp: dagger_def ctrl_blocks_index)
qed (simp_all add: dagger_def)

lemma ctrl_blocks_mult:
  assumes B1: "\<And>k. k < N \<Longrightarrow> B1 k \<in> carrier_mat m m" and B2: "\<And>k. k < N \<Longrightarrow> B2 k \<in> carrier_mat m m"
  shows "ctrl_blocks N m B1 * ctrl_blocks N m B2 = ctrl_blocks N m (\<lambda>k. B1 k * B2 k)"
proof (rule eq_matI)
  fix r c assume "r < dim_row (ctrl_blocks N m (\<lambda>k. B1 k * B2 k))" "c < dim_col (ctrl_blocks N m (\<lambda>k. B1 k * B2 k))"
  hence r: "r < N * m" and c: "c < N * m" by simp_all
  hence m: "0 < m" by (cases m) auto
  define k i j where "k = r div m" and "i = r mod m" and "j = c mod m"
  have k: "k < N" unfolding k_def using r by (simp add: less_mult_imp_div_less)
  have i: "i < m" and j: "j < m" unfolding i_def j_def using m by simp_all
  have Bd: "dim_row (B1 k) = m" "dim_col (B1 k) = m" "dim_row (B2 k) = m" "dim_col (B2 k) = m"
    using B1[OF k] B2[OF k] by auto
  have "(ctrl_blocks N m B1 * ctrl_blocks N m B2) $$ (r, c) =
        (\<Sum>x<N * m. ctrl_blocks N m B1 $$ (r, x) * ctrl_blocks N m B2 $$ (x, c))"
    using r c by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k'<N. \<Sum>i'<m. ctrl_blocks N m B1 $$ (r, k' * m + i') * ctrl_blocks N m B2 $$ (k' * m + i', c))"
    by (rule sum_blocks)
  also have "\<dots> = (\<Sum>k'<N. if k' = k \<and> c div m = k then (\<Sum>i'<m. B1 k $$ (i, i') * B2 k $$ (i', j)) else 0)"
  proof (rule sum.cong[OF refl])
    fix k' assume "k' \<in> {..<N}"
    hence k': "k' < N" by simp
    have "(\<Sum>i'<m. ctrl_blocks N m B1 $$ (r, k' * m + i') * ctrl_blocks N m B2 $$ (k' * m + i', c)) =
          (\<Sum>i'<m. if k' = k \<and> c div m = k then B1 k $$ (i, i') * B2 k $$ (i', j) else 0)"
      by (rule sum.cong[OF refl])
         (auto simp: ctrl_blocks_col_index[OF r k'] ctrl_blocks_row_index[OF c k'] k_def i_def j_def)
    also have "\<dots> = (if k' = k \<and> c div m = k then (\<Sum>i'<m. B1 k $$ (i, i') * B2 k $$ (i', j)) else 0)"
      by (rule sum_if_const)
    finally show "(\<Sum>i'<m. ctrl_blocks N m B1 $$ (r, k' * m + i') * ctrl_blocks N m B2 $$ (k' * m + i', c)) =
          (if k' = k \<and> c div m = k then (\<Sum>i'<m. B1 k $$ (i, i') * B2 k $$ (i', j)) else 0)" .
  qed
  also have "\<dots> = (if c div m = k then (\<Sum>i'<m. B1 k $$ (i, i') * B2 k $$ (i', j)) else 0)" using k by auto
  also have "\<dots> = (if r div m = c div m then (B1 k * B2 k) $$ (i, j) else 0)"
    using k i j Bd by (auto simp: scalar_prod_def atLeast0LessThan k_def)
  also have "\<dots> = ctrl_blocks N m (\<lambda>k. B1 k * B2 k) $$ (r, c)"
    using r c by (simp add: ctrl_blocks_index k_def i_def j_def)
  finally show "(ctrl_blocks N m B1 * ctrl_blocks N m B2) $$ (r, c) = ctrl_blocks N m (\<lambda>k. B1 k * B2 k) $$ (r, c)" .
qed simp_all

lemma ctrl_blocks_unitary:
  assumes B: "\<And>k. k < N \<Longrightarrow> B k \<in> carrier_mat m m" and u: "\<And>k. k < N \<Longrightarrow> unitary (B k)"
  shows "unitary (ctrl_blocks N m B)"
proof -
  have Bd: "\<And>k. k < N \<Longrightarrow> (B k)\<^sup>\<dagger> \<in> carrier_mat m m" using B dagger_carrier by blast
  have D: "(ctrl_blocks N m B)\<^sup>\<dagger> = ctrl_blocks N m (\<lambda>k. (B k)\<^sup>\<dagger>)"
    by (rule ctrl_blocks_dagger) (simp add: B)
  have "(ctrl_blocks N m B)\<^sup>\<dagger> * ctrl_blocks N m B = ctrl_blocks N m (\<lambda>k. (B k)\<^sup>\<dagger> * B k)"
    unfolding D by (rule ctrl_blocks_mult) (simp_all add: B Bd)
  also have "\<dots> = ctrl_blocks N m (\<lambda>_. 1\<^sub>m m)"
    by (rule ctrl_blocks_cong) (use B u in \<open>auto simp: unitary_def\<close>)
  finally have l: "(ctrl_blocks N m B)\<^sup>\<dagger> * ctrl_blocks N m B = 1\<^sub>m (N * m)" by (simp add: ctrl_blocks_one)
  have "ctrl_blocks N m B * ((ctrl_blocks N m B)\<^sup>\<dagger>) = ctrl_blocks N m (\<lambda>k. B k * ((B k)\<^sup>\<dagger>))"
    unfolding D by (rule ctrl_blocks_mult) (simp_all add: B Bd)
  also have "\<dots> = ctrl_blocks N m (\<lambda>_. 1\<^sub>m m)"
    by (rule ctrl_blocks_cong) (use B u in \<open>auto simp: unitary_def\<close>)
  finally have r: "ctrl_blocks N m B * ((ctrl_blocks N m B)\<^sup>\<dagger>) = 1\<^sub>m (N * m)" by (simp add: ctrl_blocks_one)
  show ?thesis unfolding unitary_def using l r by simp
qed

lemma unitary_pow:
  assumes U: "U \<in> carrier_mat m m" and u: "unitary U"
  shows "unitary (U ^\<^sub>m k)"
proof (induction k)
  case 0
  show ?case by (simp add: id_is_unitary)
next
  case (Suc k)
  have "unitary (U ^\<^sub>m k * U)" by (rule unitary_mult[OF Suc u pow_carrier_mat[OF U] U])
  thus ?case by simp
qed

subsection \<open>The circuit\<close>

text \<open>The ancilla rotation $R(c)\ket0=\sqrt{1-c^2}\ket0+c\ket1$.\<close>

definition rot :: "real \<Rightarrow> complex Matrix.mat" where
  "rot c = Matrix.mat 2 2 (\<lambda>(i, j). if i = j then complex_of_real (sqrt (1 - c\<^sup>2))
                                     else if i = 1 then complex_of_real c else - complex_of_real c)"

lemma rot_carrier [simp]: "rot c \<in> carrier_mat 2 2"
  by (simp add: rot_def)

lemma dim_rot [simp]: "dim_row (rot c) = 2" "dim_col (rot c) = 2"
  by (simp_all add: rot_def)

lemma rot_e0: "rot c *\<^sub>v unit_vec 2 0 =
  complex_of_real (sqrt (1 - c\<^sup>2)) \<cdot>\<^sub>v unit_vec 2 0 + complex_of_real c \<cdot>\<^sub>v unit_vec 2 1"
  by (rule eq_vecI) (auto simp: rot_def scalar_prod_def unit_vec_def less_2_cases numeral_2_eq_2)

lemma rot_unitary:
  assumes c: "\<bar>c\<bar> \<le> 1"
  shows "unitary (rot c)"
proof -
  have c2: "0 \<le> 1 - c\<^sup>2" using c by (simp add: abs_square_le_1)
  have ab: "\<bar>1 - c * c\<bar> = 1 - c * c" using c2 by (simp add: power2_eq_square)
  have s: "complex_of_real (sqrt (1 - c\<^sup>2)) * complex_of_real (sqrt (1 - c\<^sup>2)) = complex_of_real (1 - c\<^sup>2)"
    using c2 by (simp flip: of_real_mult)
  have l: "(rot c)\<^sup>\<dagger> * rot c = 1\<^sub>m 2"
    by (rule eq_matI)
       (auto simp: rot_def dagger_def scalar_prod_def less_2_cases numeral_2_eq_2 s ab algebra_simps
             simp flip: of_real_mult of_real_add)
  have r: "rot c * ((rot c)\<^sup>\<dagger>) = 1\<^sub>m 2"
    by (rule eq_matI)
       (auto simp: rot_def dagger_def scalar_prod_def less_2_cases numeral_2_eq_2 s ab algebra_simps
             simp flip: of_real_mult of_real_add)
  show ?thesis unfolding unitary_def using l r by simp
qed

text \<open>Register value $k$ encodes the eigenvalue $\lambda_k=2\pi k/(t_0N)$ for $k<N/2$ and
$2\pi(k-N)/(t_0N)$ otherwise (negative eigenvalues), since $e^{it_0\lambda_k}=e^{2\pi ik/N}$.\<close>

definition reg_eig :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "reg_eig t0 N k = 2 * pi * (if 2 * k < N then real k else real k - real N) / (t0 * real N)"

lemma reg_eig_phase:
  assumes t0: "0 < t0" and N: "0 < N"
  shows "cis (t0 * reg_eig t0 N k) = cis (2 * pi * (real k / real N))"
proof (cases "2 * k < N")
  case True
  thus ?thesis using t0 N by (simp add: reg_eig_def)
next
  case False
  have "t0 * reg_eig t0 N k = 2 * pi * (real k / real N) - 2 * pi"
    using False t0 N by (simp add: reg_eig_def field_simps)
  hence "cis (t0 * reg_eig t0 N k) = cis (2 * pi * (real k / real N)) / cis (2 * pi)"
    by (simp only: cis_divide)
  thus ?thesis by simp
qed

lemma reg_eig_nonzero: "0 < t0 \<Longrightarrow> 0 < k \<Longrightarrow> k < N \<Longrightarrow> reg_eig t0 N k \<noteq> 0"
  by (auto simp: reg_eig_def)

text \<open>Phase estimation $W$ of $e^{it_0A}$ with a $d$-level flag register, the flag gates $G_k$
controlled by the register value $k$, and $W^*$.  HHL rotates a qubit flag by $R(f(k))$; exact HHL
takes $f(k)=C/\lambda_k$.\<close>

definition pe_unitary :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "pe_unitary N m V = (((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) * ctrl_pow N m V"

definition hhl_Wd :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "hhl_Wd A t0 N d = pe_unitary N (dim_row A * d) (evolution A t0 \<Otimes> 1\<^sub>m d)"

abbreviation hhl_W :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "hhl_W A t0 N \<equiv> hhl_Wd A t0 N 2"

definition flag_circuit :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "flag_circuit A t0 N d G = (hhl_Wd A t0 N d)\<^sup>\<dagger> * (ctrl_blocks N (dim_row A * d) (\<lambda>k. 1\<^sub>m (dim_row A) \<Otimes> G k) * hhl_Wd A t0 N d)"

abbreviation hhl_gen :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> complex Matrix.mat" where
  "hhl_gen A t0 N f \<equiv> flag_circuit A t0 N 2 (\<lambda>k. rot (f k))"

abbreviation fun_circuit :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> complex Matrix.mat" where
  "fun_circuit A t0 N h \<equiv> hhl_gen A t0 N (\<lambda>k. h (reg_eig t0 N k))"

abbreviation hhl_circuit :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "hhl_circuit A t0 N C \<equiv> hhl_gen A t0 N (\<lambda>k. C / reg_eig t0 N k)"

abbreviation hhl_rot :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "hhl_rot C t0 N n k \<equiv> 1\<^sub>m n \<Otimes> rot (C / reg_eig t0 N k)"

lemma rot_blk_carrier [simp]: "1\<^sub>m n \<Otimes> rot x \<in> carrier_mat (n * 2) (n * 2)"
  by (rule carrier_matI) simp_all

lemma pe_unitary_carrier [simp]: "pe_unitary N m V \<in> carrier_mat (N * m) (N * m)"
  by (rule carrier_matI) (simp_all add: pe_unitary_def)

lemma pe_unitary_unitary:
  assumes N: "0 < N" and V: "V \<in> carrier_mat m m" "unitary V"
  shows "unitary (pe_unitary N m V)"
proof -
  have F: "unitary (((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m)"
    by (rule tensor_mat_unitary_one_right) (rule unitary_dagger[OF fourier_unitary[OF N]])
  have Fc: "((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m \<in> carrier_mat (N * m) (N * m)" by (rule carrier_matI) simp_all
  have C: "unitary (ctrl_pow N m V)"
    by (rule ctrl_blocks_unitary) (simp_all add: V unitary_pow[OF V])
  show ?thesis unfolding pe_unitary_def by (rule unitary_mult[OF F C Fc ctrl_blocks_carrier])
qed

text \<open>On $\frac1{\sqrt N}\sum_k\ket k\otimes w$ with $Vw=e^{2\pi ik/N}w$, phase estimation gives $\ket k\otimes w$.\<close>

lemma pe_unitary_exact:
  assumes N: "0 < N" and k: "k < N" and V: "V \<in> carrier_mat m m" and w: "dim_vec w = m"
      and ev: "V *\<^sub>v w = cis (2 * pi * (real k / real N)) \<cdot>\<^sub>v w"
  shows "pe_unitary N m V *\<^sub>v tensor_vec (uniform_state N) w = tensor_vec (unit_vec N k) w"
proof -
  have Fc: "((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m \<in> carrier_mat (N * m) (N * m)" by (rule carrier_matI) simp_all
  have xc: "tensor_vec (uniform_state N) w \<in> carrier_vec (N * m)"
    by (rule carrier_vecI, rule tensor_vec_dim) (simp_all add: uniform_state_def w)
  have "pe_unitary N m V *\<^sub>v tensor_vec (uniform_state N) w =
        (((fourier N)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow N m V *\<^sub>v tensor_vec (uniform_state N) w)"
    unfolding pe_unitary_def by (rule assoc_mult_mat_vec[OF Fc ctrl_blocks_carrier xc])
  also have "\<dots> = tensor_vec (Matrix.vec N (pe_amp N (real k / real N))) w"
    by (rule phase_estimation[OF V w ev])
  also have "Matrix.vec N (pe_amp N (real k / real N)) = unit_vec N k"
    by (rule phase_estimation_exact[OF N k])
  finally show ?thesis .
qed

lemma unitary_undo:
  assumes W: "W \<in> carrier_mat K K" "unitary W" and x: "dim_vec x = K" and y: "W *\<^sub>v x = y"
  shows "W\<^sup>\<dagger> *\<^sub>v y = x"
proof -
  have xc: "x \<in> carrier_vec K" using x by (rule carrier_vecI)
  have "W\<^sup>\<dagger> *\<^sub>v y = (W\<^sup>\<dagger> * W) *\<^sub>v x"
    unfolding y[symmetric] by (rule assoc_mult_mat_vec[OF dagger_carrier[OF W(1)] W(1) xc, symmetric])
  also have "W\<^sup>\<dagger> * W = 1\<^sub>m K" using W unfolding unitary_def by auto
  finally show ?thesis using xc by simp
qed

subsection \<open>The circuit on an eigenvector\<close>

theorem fun_circuit_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and k: "k < N" and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real (reg_eig t0 N k) \<cdot>\<^sub>v u"
  shows "fun_circuit A t0 N h *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
         tensor_vec (uniform_state N) (tensor_vec u (rot (h (reg_eig t0 N k)) *\<^sub>v unit_vec 2 0))"
proof -
  let ?E = "evolution A t0" and ?V = "evolution A t0 \<Otimes> 1\<^sub>m 2" and ?W = "hhl_W A t0 N"
  let ?CR = "ctrl_blocks N (n * 2) (\<lambda>k. 1\<^sub>m n \<Otimes> rot (h (reg_eig t0 N k)))" and ?r = "rot (h (reg_eig t0 N k)) *\<^sub>v unit_vec 2 0"
  have nA: "dim_row A = n" using A(1) by simp
  have Ec: "?E \<in> carrier_mat n n" using A by (rule evolution_carrier)
  have Vc: "?V \<in> carrier_mat (n * 2) (n * 2)" using Ec by (intro carrier_matI) auto
  have Vu: "unitary ?V" by (rule tensor_mat_unitary_one_right) (rule evolution_unitary[OF A])
  have W: "?W = pe_unitary N (n * 2) ?V" unfolding hhl_Wd_def nA ..
  have Wc: "?W \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" unfolding W by simp
  have Wu: "unitary ?W" unfolding W by (rule pe_unitary_unitary[OF N Vc Vu])
  have phase: "cis (t0 * reg_eig t0 N k) = cis (2 * pi * (real k / real N))"
    by (rule reg_eig_phase[OF t0 N])
  have Vev: "?V *\<^sub>v tensor_vec u v = cis (2 * pi * (real k / real N)) \<cdot>\<^sub>v tensor_vec u v"
    if v: "dim_vec v = 2" for v
  proof -
    have "?V *\<^sub>v tensor_vec u v = tensor_vec (?E *\<^sub>v u) (1\<^sub>m 2 *\<^sub>v v)"
      by (rule tensor_mat_vec_mult[OF Ec one_carrier_mat u v])
    also have "?E *\<^sub>v u = cis (t0 * reg_eig t0 N k) \<cdot>\<^sub>v u" by (rule evolution_eigen[OF A u ev])
    also have "1\<^sub>m 2 *\<^sub>v v = v" using carrier_vecI[OF v] by simp
    finally show ?thesis unfolding phase using tensor_vec_smult_left[OF _ v, of u n] u by simp
  qed
  have uv: "dim_vec (tensor_vec u v) = n * 2" if "dim_vec v = 2" for v by (rule tensor_vec_dim[OF u that])
  have dr: "dim_vec ?r = 2" by simp
  have s1: "?W *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
        tensor_vec (unit_vec N k) (tensor_vec u (unit_vec 2 0))"
    unfolding W by (rule pe_unitary_exact[OF N k Vc uv Vev]) simp_all
  have s2: "?CR *\<^sub>v tensor_vec (unit_vec N k) (tensor_vec u (unit_vec 2 0)) =
                 tensor_vec (unit_vec N k) (tensor_vec u ?r)"
  proof -
    have "?CR *\<^sub>v tensor_vec (unit_vec N k) (tensor_vec u (unit_vec 2 0)) =
          tensor_vec (unit_vec N k) ((1\<^sub>m n \<Otimes> rot (h (reg_eig t0 N k))) *\<^sub>v tensor_vec u (unit_vec 2 0))"
      by (rule ctrl_blocks_basis[OF k uv]) simp_all
    also have "(1\<^sub>m n \<Otimes> rot (h (reg_eig t0 N k))) *\<^sub>v tensor_vec u (unit_vec 2 0) = tensor_vec (1\<^sub>m n *\<^sub>v u) ?r"
      by (rule tensor_mat_vec_mult[OF one_carrier_mat rot_carrier u]) simp
    also have "1\<^sub>m n *\<^sub>v u = u" using carrier_vecI[OF u] by simp
    finally show ?thesis .
  qed
  have s3: "?W\<^sup>\<dagger> *\<^sub>v tensor_vec (unit_vec N k) (tensor_vec u ?r) = tensor_vec (uniform_state N) (tensor_vec u ?r)"
  proof (rule unitary_undo[OF Wc Wu])
    show "dim_vec (tensor_vec (uniform_state N) (tensor_vec u ?r)) = N * (n * 2)"
      by (rule tensor_vec_dim) (simp_all add: uniform_state_def uv[OF dr])
    show "?W *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u ?r) = tensor_vec (unit_vec N k) (tensor_vec u ?r)"
      unfolding W by (rule pe_unitary_exact[OF N k Vc uv[OF dr] Vev[OF dr]])
  qed
  have x0: "tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) \<in> carrier_vec (N * (n * 2))"
    by (rule carrier_vecI, rule tensor_vec_dim) (simp_all add: uniform_state_def uv)
  have CRc: "?CR \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" by simp
  have "fun_circuit A t0 N h *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
        ?W\<^sup>\<dagger> *\<^sub>v ((?CR * ?W) *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)))"
    unfolding flag_circuit_def nA by (rule assoc_mult_mat_vec[OF dagger_carrier[OF Wc] mult_carrier_mat[OF CRc Wc] x0])
  also have "(?CR * ?W) *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
             ?CR *\<^sub>v (?W *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)))"
    by (rule assoc_mult_mat_vec[OF CRc Wc x0])
  finally show ?thesis unfolding s1 s2 s3 .
qed

corollary hhl_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and k: "k < N" and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real (reg_eig t0 N k) \<cdot>\<^sub>v u"
  shows "hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec u (unit_vec 2 0)) =
         tensor_vec (uniform_state N) (tensor_vec u (rot (C / reg_eig t0 N k) *\<^sub>v unit_vec 2 0))"
  by (rule fun_circuit_eigen[OF A t0 N k u ev, where h = "\<lambda>x. C / x"])

subsection \<open>All right-hand sides\<close>

lemma mult_zero_vec_right: "B \<in> carrier_mat K n \<Longrightarrow> B *\<^sub>v 0\<^sub>v n = 0\<^sub>v K"
  by (rule eq_vecI) (auto simp: scalar_prod_def)

text \<open>The matrix of $b\mapsto a\otimes(M_0b\otimes\ket0+M_1b\otimes\ket1)$.\<close>

definition lift_mat :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "lift_mat n a M0 M1 = Matrix.mat (dim_vec a * (n * 2)) n
     (\<lambda>(r, s). a $ (r div (n * 2)) *
        (if r mod 2 = 0 then M0 $$ (r mod (n * 2) div 2, s) else M1 $$ (r mod (n * 2) div 2, s)))"

lemma lift_mat_carrier [simp]: "lift_mat n a M0 M1 \<in> carrier_mat (dim_vec a * (n * 2)) n"
  by (simp add: lift_mat_def)

lemma lift_mat_mult_vec:
  assumes M0: "M0 \<in> carrier_mat n n" and M1: "M1 \<in> carrier_mat n n" and b: "dim_vec b = n"
  shows "lift_mat n a M0 M1 *\<^sub>v b =
         tensor_vec a (tensor_vec (M0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec (M1 *\<^sub>v b) (unit_vec 2 1))"
proof -
  let ?N = "dim_vec a"
  have d0: "dim_vec (tensor_vec (M0 *\<^sub>v b) (unit_vec 2 0)) = n * 2" by (rule tensor_vec_dim) (use M0 in simp_all)
  have d1: "dim_vec (tensor_vec (M1 *\<^sub>v b) (unit_vec 2 1)) = n * 2" by (rule tensor_vec_dim) (use M1 in simp_all)
  have dX: "dim_vec (tensor_vec (M0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec (M1 *\<^sub>v b) (unit_vec 2 1)) = n * 2"
    using d1 by simp
  have dt: "dim_vec (tensor_vec a (tensor_vec (M0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec (M1 *\<^sub>v b) (unit_vec 2 1))) = ?N * (n * 2)"
    by (rule tensor_vec_dim[OF refl dX])
  show ?thesis
  proof (rule eq_vecI)
    fix r assume "r < dim_vec (tensor_vec a (tensor_vec (M0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec (M1 *\<^sub>v b) (unit_vec 2 1)))"
    hence r: "r < ?N * (n * 2)" using dt by simp
    hence n: "0 < n" by (cases n) auto
    define q where "q = r mod (n * 2)"
    have q: "q < n * 2" unfolding q_def using n by simp
    have s0: "q div 2 < n" using q by linarith
    have t: "q mod 2 = r mod 2" unfolding q_def by (simp add: mod_mod_cancel)
    have Md: "dim_row M0 = n" "dim_col M0 = n" "dim_row M1 = n" "dim_col M1 = n" using M0 M1 by auto
    have "(lift_mat n a M0 M1 *\<^sub>v b) $ r =
          (\<Sum>s<n. a $ (r div (n * 2)) * (if r mod 2 = 0 then M0 $$ (q div 2, s) else M1 $$ (q div 2, s)) * b $ s)"
      unfolding q_def using r b by (simp add: lift_mat_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = a $ (r div (n * 2)) * (if r mod 2 = 0 then (M0 *\<^sub>v b) $ (q div 2) else (M1 *\<^sub>v b) $ (q div 2))"
      using s0 Md b by (simp add: scalar_prod_def atLeast0LessThan sum_distrib_left mult_ac)
    also have "\<dots> = tensor_vec a (tensor_vec (M0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec (M1 *\<^sub>v b) (unit_vec 2 1)) $ r"
    proof -
      have "(tensor_vec (M0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec (M1 *\<^sub>v b) (unit_vec 2 1)) $ q =
            (M0 *\<^sub>v b) $ (q div 2) * unit_vec 2 0 $ (q mod 2) + (M1 *\<^sub>v b) $ (q div 2) * unit_vec 2 1 $ (q mod 2)"
        using q d1 Md tensor_vec_index[of "M0 *\<^sub>v b" n "unit_vec 2 0" 2 q] tensor_vec_index[of "M1 *\<^sub>v b" n "unit_vec 2 1" 2 q]
        by simp
      also have "\<dots> = (if r mod 2 = 0 then (M0 *\<^sub>v b) $ (q div 2) else (M1 *\<^sub>v b) $ (q div 2))"
        using t by (auto simp: unit_vec_def)
      finally show ?thesis
        using tensor_vec_index[OF refl dX r] by (simp add: q_def)
    qed
    finally show "(lift_mat n a M0 M1 *\<^sub>v b) $ r =
      tensor_vec a (tensor_vec (M0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec (M1 *\<^sub>v b) (unit_vec 2 1)) $ r" .
  qed (use dt in \<open>simp add: lift_mat_def\<close>)
qed

text \<open>The embedding $b\mapsto a\otimes b\otimes\ket0$, and on an eigenvector the ideal output
$a\otimes u\otimes R(h(\lambda))\ket0$.\<close>

lemma lift_mat_emb:
  assumes v: "dim_vec v = n"
  shows "lift_mat n a (1\<^sub>m n) (0\<^sub>m n n) *\<^sub>v v = tensor_vec a (tensor_vec v (unit_vec 2 0))"
proof -
  have vc: "v \<in> carrier_vec n" using v by (rule carrier_vecI)
  have z: "tensor_vec (0\<^sub>m n n *\<^sub>v v) (unit_vec 2 1) = 0\<^sub>v (n * 2)"
    using vc by (intro eq_vecI) (simp_all add: tensor_vec_index tensor_vec_dim scalar_prod_left_zero)
  have "lift_mat n a (1\<^sub>m n) (0\<^sub>m n n) *\<^sub>v v =
        tensor_vec a (tensor_vec (1\<^sub>m n *\<^sub>v v) (unit_vec 2 0) + tensor_vec (0\<^sub>m n n *\<^sub>v v) (unit_vec 2 1))"
    by (rule lift_mat_mult_vec[OF one_carrier_mat zero_carrier_mat v])
  also have "1\<^sub>m n *\<^sub>v v = v" using vc by simp
  also note z
  also have "tensor_vec v (unit_vec 2 0) + 0\<^sub>v (n * 2) = tensor_vec v (unit_vec 2 0)"
    by (rule right_zero_vec[OF carrier_vecI[OF tensor_vec_dim[OF v]]]) simp
  finally show ?thesis .
qed

lemma lift_mat_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
  shows "lift_mat n a (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (h x)\<^sup>2))) A) (mat_fun (\<lambda>x. complex_of_real (h x)) A) *\<^sub>v u =
         tensor_vec a (tensor_vec u (rot (h l) *\<^sub>v unit_vec 2 0))"
proof -
  let ?G0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (h x)\<^sup>2))) A" and ?G1 = "mat_fun (\<lambda>x. complex_of_real (h x)) A"
  let ?c = "h l" and ?s = "sqrt (1 - (h l)\<^sup>2)"
  have g0: "?G0 *\<^sub>v u = complex_of_real ?s \<cdot>\<^sub>v u" by (rule mat_fun_eigen[OF A u ev])
  have g1: "?G1 *\<^sub>v u = complex_of_real ?c \<cdot>\<^sub>v u" by (rule mat_fun_eigen[OF A u ev])
  have "lift_mat n a ?G0 ?G1 *\<^sub>v u = tensor_vec a (tensor_vec (?G0 *\<^sub>v u) (unit_vec 2 0) + tensor_vec (?G1 *\<^sub>v u) (unit_vec 2 1))"
    by (rule lift_mat_mult_vec[OF mat_fun_carrier[OF A] mat_fun_carrier[OF A] u])
  also have "tensor_vec (?G0 *\<^sub>v u) (unit_vec 2 0) + tensor_vec (?G1 *\<^sub>v u) (unit_vec 2 1) = tensor_vec u (rot ?c *\<^sub>v unit_vec 2 0)"
    unfolding g0 g1 rot_e0
    using tensor_vec_bilinear_right[OF u, of "complex_of_real ?s \<cdot>\<^sub>v unit_vec 2 0" 2 "complex_of_real ?c \<cdot>\<^sub>v unit_vec 2 1"]
          tensor_vec_smult_right[OF u, of "unit_vec 2 0" 2] tensor_vec_smult_right[OF u, of "unit_vec 2 1" 2]
          tensor_vec_smult_left[OF u, of "unit_vec 2 0" 2] tensor_vec_smult_left[OF u, of "unit_vec 2 1" 2]
    by simp
  finally show ?thesis .
qed

text \<open>$C/x$ as a matrix function is $C\,A^{-1}$.\<close>

lemma herm_inv_scale:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "mat_fun (\<lambda>x. complex_of_real (C / x)) A = complex_of_real C \<cdot>\<^sub>m herm_inv A"
proof (rule mat_fun_eqI[OF A])
  have Hi: "herm_inv A \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
  show "complex_of_real C \<cdot>\<^sub>m herm_inv A \<in> carrier_mat n n" using Hi by simp
  show "fun_on_eigen A (\<lambda>x. complex_of_real (C / x)) (complex_of_real C \<cdot>\<^sub>m herm_inv A)"
    unfolding fun_on_eigen_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vn: "dim_vec v = n" using v A(1) by simp
    show "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v v = complex_of_real (C / l) \<cdot>\<^sub>v v"
      using smult_mat_mult_vec[OF Hi carrier_vecI[OF vn], of "complex_of_real C"] herm_inv_eigen[OF A vn ev]
      by (simp add: smult_smult_assoc divide_inverse)
  qed
qed

corollary ideal_mat_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
  shows "lift_mat n a (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A) (complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v u =
         tensor_vec a (tensor_vec u (rot (C / l) *\<^sub>v unit_vec 2 0))"
  using lift_mat_eigen[OF A u ev, where h = "\<lambda>x. C / x" and a = a] unfolding herm_inv_scale[OF A] .

text \<open>Replacing the rotation angle $C/\lambda$ by $h(\lambda)$ gives $h(A)\ket b$ on the ancilla $\ket1$.\<close>

theorem fun_circuit_output:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>k. k < N \<and> l = reg_eig t0 N k"
      and b: "dim_vec b = n"
  shows "fun_circuit A t0 N h *\<^sub>v tensor_vec (uniform_state N) (tensor_vec b (unit_vec 2 0)) =
         tensor_vec (uniform_state N)
           (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (h x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
            tensor_vec (mat_fun (\<lambda>x. complex_of_real (h x)) A *\<^sub>v b) (unit_vec 2 1))"
proof -
  let ?G0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (h x)\<^sup>2))) A"
  let ?G1 = "mat_fun (\<lambda>x. complex_of_real (h x)) A"
  let ?H = "fun_circuit A t0 N h" and ?u = "uniform_state N"
  let ?Emb = "lift_mat n ?u (1\<^sub>m n) (0\<^sub>m n n)" and ?Out = "lift_mat n ?u ?G0 ?G1"
  have du: "dim_vec ?u = N" by (simp add: uniform_state_def)
  have nA: "dim_row A = n" using A(1) by simp
  have G0: "?G0 \<in> carrier_mat n n" using A by simp
  have G1: "?G1 \<in> carrier_mat n n" using A by simp
  have Hc: "?H \<in> carrier_mat (N * (n * 2)) (N * (n * 2))"
    unfolding flag_circuit_def hhl_Wd_def nA
    by (rule mult_carrier_mat[OF dagger_carrier[OF pe_unitary_carrier] mult_carrier_mat[OF ctrl_blocks_carrier pe_unitary_carrier]])
  have Ec: "?Emb \<in> carrier_mat (N * (n * 2)) n" using lift_mat_carrier[of n ?u] du by simp
  have Oc: "?Out \<in> carrier_mat (N * (n * 2)) n" using lift_mat_carrier[of n ?u] du by simp
  note emb = lift_mat_emb[where a = ?u]
  have HE: "?H * ?Emb = ?Out"
  proof (rule eigvec_mat_eqI[OF A mult_carrier_mat[OF Hc Ec] Oc])
    fix v l assume v: "dim_vec v = n" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vc: "v \<in> carrier_vec n" using v by (rule carrier_vecI)
    show "(?H * ?Emb) *\<^sub>v v = ?Out *\<^sub>v v"
    proof (cases "v = 0\<^sub>v n")
      case True
      thus ?thesis using mult_zero_vec_right[OF mult_carrier_mat[OF Hc Ec]] mult_zero_vec_right[OF Oc] by simp
    next
      case False
      hence "l \<in> herm_spectrum A" unfolding herm_spectrum_iff nA using v ev by (intro exI[of _ v]) simp
      then obtain k where k: "k < N" and l: "l = reg_eig t0 N k" using spec by blast
      have "(?H * ?Emb) *\<^sub>v v = ?H *\<^sub>v (?Emb *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF Hc Ec vc])
      also have "\<dots> = tensor_vec ?u (tensor_vec v (rot (h l) *\<^sub>v unit_vec 2 0))"
        unfolding emb[OF v] l by (rule fun_circuit_eigen[OF A t0 N k v ev[unfolded l]])
      also have "\<dots> = ?Out *\<^sub>v v" by (rule lift_mat_eigen[OF A v ev, symmetric])
      finally show ?thesis .
    qed
  qed
  have bc: "b \<in> carrier_vec n" using b by (rule carrier_vecI)
  have "?H *\<^sub>v tensor_vec ?u (tensor_vec b (unit_vec 2 0)) = ?H *\<^sub>v (?Emb *\<^sub>v b)" unfolding emb[OF b] ..
  also have "\<dots> = (?H * ?Emb) *\<^sub>v b" by (rule assoc_mult_mat_vec[OF Hc Ec bc, symmetric])
  also have "\<dots> = ?Out *\<^sub>v b" unfolding HE ..
  also have "\<dots> = tensor_vec ?u (tensor_vec (?G0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec (?G1 *\<^sub>v b) (unit_vec 2 1))"
    by (rule lift_mat_mult_vec[OF G0 G1 b])
  finally show ?thesis .
qed


theorem hhl:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>k. 0 < k \<and> k < N \<and> l = reg_eig t0 N k"
      and b: "dim_vec b = n"
  shows "hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec b (unit_vec 2 0)) =
         tensor_vec (uniform_state N)
           (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
            tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))"
proof -
  have "mat_fun (\<lambda>x. complex_of_real (C / x)) A = complex_of_real C \<cdot>\<^sub>m herm_inv A" by (rule herm_inv_scale[OF A])
  moreover have "hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec b (unit_vec 2 0)) =
         tensor_vec (uniform_state N)
           (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
            tensor_vec (mat_fun (\<lambda>x. complex_of_real (C / x)) A *\<^sub>v b) (unit_vec 2 1))"
    by (rule fun_circuit_output[OF A t0 N _ b, where h = "\<lambda>x. C / x"]) (use spec in blast)
  ultimately show ?thesis by simp
qed

text \<open>Reading off the solution: $x=A^{-1}b$ solves $Ax=b$, the ancilla-$\ket1$ part of the output is
$C\,(u\otimes x\otimes\ket1)$, and its squared norm (the probability of measuring the ancilla in
$\ket1$) is $C^2\norm x^2$.\<close>

lemma uniform_state_norm: "0 < N \<Longrightarrow> \<langle>uniform_state N|uniform_state N\<rangle> = 1"
proof -
  assume N: "0 < N"
  have "\<langle>uniform_state N|uniform_state N\<rangle> = (\<Sum>i<N. cnj (1 / complex_of_real (sqrt (real N))) * (1 / complex_of_real (sqrt (real N))))"
    by (simp add: uniform_state_def inner_prod_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = of_nat N * (1 / (complex_of_real (sqrt (real N)) * complex_of_real (sqrt (real N))))" by simp
  also have "\<dots> = 1" using N by (simp add: sqrt_N_sq)
  finally show ?thesis .
qed

corollary hhl_solution:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "0 < N"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<exists>k. 0 < k \<and> k < N \<and> l = reg_eig t0 N k"
      and b: "dim_vec b = n"
  defines "x \<equiv> herm_inv A *\<^sub>v b"
  shows "A *\<^sub>v x = b"
    and "hhl_circuit A t0 N C *\<^sub>v tensor_vec (uniform_state N) (tensor_vec b (unit_vec 2 0)) =
         tensor_vec (uniform_state N) (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0)) +
         complex_of_real C \<cdot>\<^sub>v tensor_vec (uniform_state N) (tensor_vec x (unit_vec 2 1))"
    and "\<langle>tensor_vec (uniform_state N) (tensor_vec (complex_of_real C \<cdot>\<^sub>v x) (unit_vec 2 1)) |
          tensor_vec (uniform_state N) (tensor_vec (complex_of_real C \<cdot>\<^sub>v x) (unit_vec 2 1))\<rangle> =
         complex_of_real (C\<^sup>2) * \<langle>x|x\<rangle>"
proof -
  let ?G0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A" and ?u = "uniform_state N"
  have Hi: "herm_inv A \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
  have bc: "b \<in> carrier_vec n" using b by (rule carrier_vecI)
  have xd: "dim_vec x = n" unfolding x_def using Hi by simp
  have du: "dim_vec ?u = N" by (simp add: uniform_state_def)
  have z: "0 \<notin> herm_spectrum A"
  proof
    assume "0 \<in> herm_spectrum A"
    then obtain k where "0 < k" "k < N" "0 = reg_eig t0 N k" using spec by blast
    thus False using reg_eig_nonzero[OF t0] by metis
  qed
  have "A *\<^sub>v x = (A * herm_inv A) *\<^sub>v b" unfolding x_def by (rule assoc_mult_mat_vec[OF A(1) Hi bc, symmetric])
  also have "A * herm_inv A = 1\<^sub>m n" by (rule herm_inv(2)[OF A z])
  finally show "A *\<^sub>v x = b" using bc by simp
  have g1: "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b = complex_of_real C \<cdot>\<^sub>v x"
    unfolding x_def by (rule smult_mat_mult_vec[OF Hi carrier_vecI[OF b]])
  have G0d: "dim_vec (?G0 *\<^sub>v b) = n" using carrier_matD(1)[OF mat_fun_carrier[OF A]] by simp
  have d0: "dim_vec (tensor_vec (?G0 *\<^sub>v b) (unit_vec 2 0)) = n * 2" by (rule tensor_vec_dim[OF G0d]) simp
  have d1: "dim_vec (tensor_vec x (unit_vec 2 1)) = n * 2" by (rule tensor_vec_dim[OF xd]) simp
  have d1': "dim_vec (tensor_vec (complex_of_real C \<cdot>\<^sub>v x) (unit_vec 2 1)) = n * 2" by (rule tensor_vec_dim) (simp_all add: xd)
  show "hhl_circuit A t0 N C *\<^sub>v tensor_vec ?u (tensor_vec b (unit_vec 2 0)) =
        tensor_vec ?u (tensor_vec (?G0 *\<^sub>v b) (unit_vec 2 0)) + complex_of_real C \<cdot>\<^sub>v tensor_vec ?u (tensor_vec x (unit_vec 2 1))"
  proof -
    have e1: "tensor_vec (complex_of_real C \<cdot>\<^sub>v x) (unit_vec 2 1) = complex_of_real C \<cdot>\<^sub>v tensor_vec x (unit_vec 2 1)"
      by (rule tensor_vec_smult_left[OF xd]) simp
    have d2: "dim_vec (complex_of_real C \<cdot>\<^sub>v tensor_vec x (unit_vec 2 1)) = n * 2" using d1 by simp
    have "hhl_circuit A t0 N C *\<^sub>v tensor_vec ?u (tensor_vec b (unit_vec 2 0)) =
          tensor_vec ?u (tensor_vec (?G0 *\<^sub>v b) (unit_vec 2 0) + complex_of_real C \<cdot>\<^sub>v tensor_vec x (unit_vec 2 1))"
      unfolding g1[symmetric] e1[symmetric] by (rule hhl[OF A t0 N _ b]) (rule spec)
    also have "\<dots> = tensor_vec ?u (tensor_vec (?G0 *\<^sub>v b) (unit_vec 2 0)) +
                     tensor_vec ?u (complex_of_real C \<cdot>\<^sub>v tensor_vec x (unit_vec 2 1))"
      by (rule tensor_vec_bilinear_right[OF du d0 d2])
    also have "tensor_vec ?u (complex_of_real C \<cdot>\<^sub>v tensor_vec x (unit_vec 2 1)) =
               complex_of_real C \<cdot>\<^sub>v tensor_vec ?u (tensor_vec x (unit_vec 2 1))"
      by (rule tensor_vec_smult_right[OF du d1])
    finally show ?thesis .
  qed
  have "\<langle>tensor_vec ?u (tensor_vec (complex_of_real C \<cdot>\<^sub>v x) (unit_vec 2 1)) |
         tensor_vec ?u (tensor_vec (complex_of_real C \<cdot>\<^sub>v x) (unit_vec 2 1))\<rangle> =
        \<langle>?u|?u\<rangle> * (\<langle>complex_of_real C \<cdot>\<^sub>v x|complex_of_real C \<cdot>\<^sub>v x\<rangle> * \<langle>unit_vec 2 1|unit_vec 2 1\<rangle>)"
  proof -
    have cx: "dim_vec (complex_of_real C \<cdot>\<^sub>v x) = n" using xd by simp
    have e: "dim_vec (unit_vec 2 1) = 2" by simp
    show ?thesis unfolding tensor_inner_prod[OF du du d1' d1'] tensor_inner_prod[OF cx cx e e] ..
  qed
  also have "\<dots> = complex_of_real (C\<^sup>2) * \<langle>x|x\<rangle>"
    using uniform_state_norm[OF N] xd
    by (simp add: inner_prod_def scalar_prod_def unit_vec_def sum_distrib_left power2_eq_square
                  atLeast0LessThan less_2_cases numeral_2_eq_2 mult_ac)
  finally show "\<langle>tensor_vec ?u (tensor_vec (complex_of_real C \<cdot>\<^sub>v x) (unit_vec 2 1)) |
         tensor_vec ?u (tensor_vec (complex_of_real C \<cdot>\<^sub>v x) (unit_vec 2 1))\<rangle> = complex_of_real (C\<^sup>2) * \<langle>x|x\<rangle>" .
qed

subsection \<open>The success probability\<close>

text \<open>The diagonal of a spectral decomposition consists of eigenvalues.\<close>

lemma spectral_decomp_eig_in_spectrum:
  assumes A: "A \<in> carrier_mat n n" and sd: "spectral_decomp A U D" and j: "j < n"
  shows "D ! j \<in> herm_spectrum A"
proof -
  note d = spectral_decompD[OF A sd]
  have cd: "dim_vec (Matrix.col U j) = n" using d(1) by simp
  have nz: "Matrix.col U j \<noteq> 0\<^sub>v n"
  proof
    assume z: "Matrix.col U j = 0\<^sub>v n"
    have "(U\<^sup>\<dagger> * U) $$ (j, j) = Matrix.row (U\<^sup>\<dagger>) j \<bullet> Matrix.col U j"
      by (rule index_mult_mat(1)) (use d(1) j in simp_all)
    also have "\<dots> = 0" unfolding z by (rule scalar_prod_right_zero) (use d(1) j in \<open>simp add: dagger_def\<close>)
    finally show False using d(4) j by simp
  qed
  show ?thesis unfolding herm_spectrum_iff
    using spectral_decomp_col[OF A sd j] cd nz A by (intro exI[of _ "Matrix.col U j"]) simp
qed

text \<open>A real function non-negative on the spectrum gives a positive matrix.\<close>

lemma mat_fun_psd:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and f: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> 0 \<le> f l"
  shows "psd (mat_fun (\<lambda>x. complex_of_real (f x)) A)"
proof -
  obtain U D where sd: "spectral_decomp A U D" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have "mat_fun (\<lambda>x. complex_of_real (f x)) A = U * diag_cmat (map (\<lambda>x. complex_of_real (f x)) D) * (U\<^sup>\<dagger>)"
    by (rule mat_fun_decomp[OF A sd])
  also have "diag_cmat (map (\<lambda>x. complex_of_real (f x)) D) = diag_mat_of_real (map f D)"
    by (simp add: diag_mat_of_real_cmat o_def)
  finally have e: "mat_fun (\<lambda>x. complex_of_real (f x)) A = U * diag_mat_of_real (map f D) * (U\<^sup>\<dagger>)" .
  show ?thesis unfolding e
    by (rule psd_U_diag_Udag[OF d(1)]) (use d(3) f spectral_decomp_eig_in_spectrum[OF A(1) sd] in simp_all)
qed

lemma mat_fun_add:
  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  shows "mat_fun (\<lambda>x. g x + h x) A = mat_fun g A + mat_fun h A"
proof (rule mat_fun_eqI[OF A])
  show "mat_fun g A + mat_fun h A \<in> carrier_mat n n" using A by simp
  show "fun_on_eigen A (\<lambda>x. g x + h x) (mat_fun g A + mat_fun h A)" unfolding fun_on_eigen_def
  proof (intro allI impI)
    fix v l assume v: "dim_vec v = dim_row A" and ev: "A *\<^sub>v v = complex_of_real l \<cdot>\<^sub>v v"
    have vn: "dim_vec v = n" using v A(1) by simp
    have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF vn])
    have "(mat_fun g A + mat_fun h A) *\<^sub>v v = mat_fun g A *\<^sub>v v + mat_fun h A *\<^sub>v v"
      by (rule add_mult_distrib_mat_vec[OF mat_fun_carrier[OF A] mat_fun_carrier[OF A] vc])
    also have "\<dots> = g l \<cdot>\<^sub>v v + h l \<cdot>\<^sub>v v" by (simp add: mat_fun_eigen[OF A vn ev])
    also have "\<dots> = (g l + h l) \<cdot>\<^sub>v v" by (simp add: add_smult_distrib_vec)
    finally show "(mat_fun g A + mat_fun h A) *\<^sub>v v = (g l + h l) \<cdot>\<^sub>v v" .
  qed
qed

lemma inner_prod_add_right:
  assumes "dim_vec a = n" "dim_vec b = n" "dim_vec c = n"
  shows "\<langle>a|b + c\<rangle> = \<langle>a|b\<rangle> + \<langle>a|c\<rangle>"
  using assms by (simp add: inner_prod_def scalar_prod_def sum.distrib algebra_simps)

text \<open>If $C\le|\lambda|\le\Lambda$ on the spectrum, $C>0$, the probability $C^2\norm{A^{-1}b}^2$ of the
ancilla outcome $\ket1$ is at least $(C/\Lambda)^2\norm b^2$: for unit $b$ and $C=\lambda_{\min}$ this
is $1/\kappa^2$.\<close>

theorem hhl_success_bound:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and C: "0 < C"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> C \<le> \<bar>l\<bar> \<and> \<bar>l\<bar> \<le> \<Lambda>"
      and b: "dim_vec b = n"
  shows "(C / \<Lambda>)\<^sup>2 * Re \<langle>b|b\<rangle> \<le> C\<^sup>2 * Re \<langle>herm_inv A *\<^sub>v b|herm_inv A *\<^sub>v b\<rangle>"
proof -
  let ?Ai = "herm_inv A" and ?P = "mat_fun (\<lambda>x. complex_of_real (1 / x\<^sup>2 - 1 / \<Lambda>\<^sup>2)) A"
  have Ai: "?Ai \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
  have bc: "b \<in> carrier_vec n" by (rule carrier_vecI[OF b])
  have Pc: "?P \<in> carrier_mat n n" using A by simp
  have Ad: "dim_vec (?Ai *\<^sub>v b) = n" using Ai by simp
  have L: "C \<le> \<Lambda>" if "l \<in> herm_spectrum A" for l using spec[OF that] by linarith
  have psd: "psd ?P"
  proof (rule mat_fun_psd[OF A])
    fix l assume l: "l \<in> herm_spectrum A"
    have "0 < \<bar>l\<bar>" "\<bar>l\<bar> \<le> \<Lambda>" using spec[OF l] C by linarith+
    hence "\<bar>l\<bar>\<^sup>2 \<le> \<Lambda>\<^sup>2" by (intro power_mono) simp_all
    hence "l\<^sup>2 \<le> \<Lambda>\<^sup>2" by simp
    moreover have "0 < l\<^sup>2" using \<open>0 < \<bar>l\<bar>\<close> by simp
    ultimately show "0 \<le> 1 / l\<^sup>2 - 1 / \<Lambda>\<^sup>2" by (simp add: frac_le)
  qed
  have "\<langle>?Ai *\<^sub>v b|?Ai *\<^sub>v b\<rangle> = \<langle>b|?Ai *\<^sub>v (?Ai *\<^sub>v b)\<rangle>"
    using inner_prod_adjoint_swap[OF Ai b Ad] herm_inv_hermitian[OF A] unfolding hermitian_def by simp
  also have "?Ai *\<^sub>v (?Ai *\<^sub>v b) = (?Ai * ?Ai) *\<^sub>v b" by (rule assoc_mult_mat_vec[OF Ai Ai bc, symmetric])
  also have "?Ai * ?Ai = mat_fun (\<lambda>x. complex_of_real (inverse x) * complex_of_real (inverse x)) A"
    unfolding herm_inv_def by (rule mat_fun_mult[OF A])
  also have "\<dots> = mat_fun (\<lambda>x. complex_of_real (1 / x\<^sup>2 - 1 / \<Lambda>\<^sup>2) + complex_of_real (1 / \<Lambda>\<^sup>2)) A"
    by (rule mat_fun_cong[OF A]) (simp add: power2_eq_square field_simps flip: of_real_mult of_real_add)
  also have "\<dots> = ?P + complex_of_real (1 / \<Lambda>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m n"
    unfolding mat_fun_add[OF A] mat_fun_const[OF A] ..
  also have "(?P + complex_of_real (1 / \<Lambda>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m n) *\<^sub>v b = ?P *\<^sub>v b + complex_of_real (1 / \<Lambda>\<^sup>2) \<cdot>\<^sub>v b"
    using add_mult_distrib_mat_vec[OF Pc _ bc, of "complex_of_real (1 / \<Lambda>\<^sup>2) \<cdot>\<^sub>m 1\<^sub>m n"]
          smult_mat_mult_vec[of "1\<^sub>m n" n n b] b bc by simp
  also have "\<langle>b|?P *\<^sub>v b + complex_of_real (1 / \<Lambda>\<^sup>2) \<cdot>\<^sub>v b\<rangle> = \<langle>b|?P *\<^sub>v b\<rangle> + complex_of_real (1 / \<Lambda>\<^sup>2) * \<langle>b|b\<rangle>"
    using inner_prod_add_right[of b n "?P *\<^sub>v b" "complex_of_real (1 / \<Lambda>\<^sup>2) \<cdot>\<^sub>v b"] inner_prod_distrib_right[of b b]
          b Pc by simp
  finally have e: "Re \<langle>?Ai *\<^sub>v b|?Ai *\<^sub>v b\<rangle> = Re \<langle>b|?P *\<^sub>v b\<rangle> + 1 / \<Lambda>\<^sup>2 * Re \<langle>b|b\<rangle>" by simp
  have "0 \<le> Re \<langle>b|?P *\<^sub>v b\<rangle>" using psd Pc b unfolding psd_def by auto
  hence "1 / \<Lambda>\<^sup>2 * Re \<langle>b|b\<rangle> \<le> Re \<langle>?Ai *\<^sub>v b|?Ai *\<^sub>v b\<rangle>" using e by linarith
  hence "C\<^sup>2 * (1 / \<Lambda>\<^sup>2 * Re \<langle>b|b\<rangle>) \<le> C\<^sup>2 * Re \<langle>?Ai *\<^sub>v b|?Ai *\<^sub>v b\<rangle>" by (rule mult_left_mono) simp
  thus ?thesis by (simp add: power_divide)
qed

subsection \<open>Non-Hermitian systems\<close>

text \<open>For square $A$, the Hermitian $\tilde A=\begin{pmatrix}0&A\\A^*&0\end{pmatrix}$ has
$\tilde A(0\oplus x)=b\oplus0$ when $Ax=b$, so HHL applied to $\tilde A$ and $b\oplus0$ returns
$0\oplus x$.\<close>

definition herm_embed :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "herm_embed A = four_block_mat (0\<^sub>m (dim_row A) (dim_row A)) A (A\<^sup>\<dagger>) (0\<^sub>m (dim_col A) (dim_col A))"

lemma herm_embed_carrier: "A \<in> carrier_mat m n \<Longrightarrow> herm_embed A \<in> carrier_mat (m + n) (m + n)"
  by (auto simp: herm_embed_def)

lemma herm_embed_hermitian:
  assumes A: "A \<in> carrier_mat m n"
  shows "hermitian (herm_embed A)"
proof -
  have "(herm_embed A)\<^sup>\<dagger> = four_block_mat ((0\<^sub>m m m)\<^sup>\<dagger>) ((A\<^sup>\<dagger>)\<^sup>\<dagger>) (A\<^sup>\<dagger>) ((0\<^sub>m n n)\<^sup>\<dagger>)"
    unfolding herm_embed_def using A
    by (simp add: dagger_four_block_mat_complex[OF zero_carrier_mat A dagger_carrier[OF A] zero_carrier_mat])
  also have "\<dots> = herm_embed A" using A by (simp add: herm_embed_def dagger_zero_mat dagger_of_dagger_is_id)
  finally show ?thesis unfolding hermitian_def .
qed

lemma zero_mat_mult_vec: "dim_vec v = n \<Longrightarrow> 0\<^sub>m K n *\<^sub>v v = 0\<^sub>v K"
  by (rule eq_vecI) (auto simp: scalar_prod_def)

lemma herm_embed_mult:
  assumes A: "A \<in> carrier_mat m n" and a: "dim_vec a = m" and c: "dim_vec c = n"
  shows "herm_embed A *\<^sub>v (a @\<^sub>v c) = (A *\<^sub>v c) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v a)"
proof -
  have ac: "a \<in> carrier_vec m" "c \<in> carrier_vec n" by (rule carrier_vecI[OF a], rule carrier_vecI[OF c])
  have "herm_embed A *\<^sub>v (a @\<^sub>v c) = (0\<^sub>m m m *\<^sub>v a + A *\<^sub>v c) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v a + 0\<^sub>m n n *\<^sub>v c)"
    unfolding herm_embed_def using A
    by (simp add: four_block_mat_mult_vec[OF zero_carrier_mat A dagger_carrier[OF A] zero_carrier_mat ac])
  also have "0\<^sub>m m m *\<^sub>v a = 0\<^sub>v m" by (rule zero_mat_mult_vec[OF a])
  also have "0\<^sub>m n n *\<^sub>v c = 0\<^sub>v n" by (rule zero_mat_mult_vec[OF c])
  also have "A\<^sup>\<dagger> *\<^sub>v a + 0\<^sub>v n = A\<^sup>\<dagger> *\<^sub>v a"
    by (rule right_zero_vec, rule carrier_vecI) (use A a in simp)
  also have "0\<^sub>v m + A *\<^sub>v c = A *\<^sub>v c"
    by (rule left_zero_vec, rule carrier_vecI) (use A c in simp)
  finally show ?thesis .
qed

lemma herm_embed_solve:
  assumes A: "A \<in> carrier_mat n n" and x: "dim_vec x = n" and ax: "A *\<^sub>v x = b"
  shows "herm_embed A *\<^sub>v (0\<^sub>v n @\<^sub>v x) = b @\<^sub>v 0\<^sub>v n"
  unfolding herm_embed_mult[OF A _ x, of "0\<^sub>v n", simplified] ax
  using mult_zero_vec_right[OF dagger_carrier[OF A]] by simp

lemma herm_embed_inverse:
  assumes A: "A \<in> carrier_mat n n" and x: "dim_vec x = n" and ax: "A *\<^sub>v x = b"
      and z: "0 \<notin> herm_spectrum (herm_embed A)"
  shows "herm_inv (herm_embed A) *\<^sub>v (b @\<^sub>v 0\<^sub>v n) = 0\<^sub>v n @\<^sub>v x"
proof -
  let ?T = "herm_embed A"
  have T: "?T \<in> carrier_mat (n + n) (n + n)" "hermitian ?T"
    using herm_embed_carrier[OF A] herm_embed_hermitian[OF A] by auto
  have Ti: "herm_inv ?T \<in> carrier_mat (n + n) (n + n)" using T unfolding herm_inv_def by simp
  have yc: "0\<^sub>v n @\<^sub>v x \<in> carrier_vec (n + n)" using x by (intro carrier_vecI) simp
  have "herm_inv ?T *\<^sub>v (b @\<^sub>v 0\<^sub>v n) = herm_inv ?T *\<^sub>v (?T *\<^sub>v (0\<^sub>v n @\<^sub>v x))"
    unfolding herm_embed_solve[OF A x ax] ..
  also have "\<dots> = (herm_inv ?T * ?T) *\<^sub>v (0\<^sub>v n @\<^sub>v x)" by (rule assoc_mult_mat_vec[OF Ti T(1) yc, symmetric])
  also have "herm_inv ?T * ?T = 1\<^sub>m (n + n)" by (rule herm_inv(1)[OF T z])
  finally show ?thesis using yc by simp
qed

end
