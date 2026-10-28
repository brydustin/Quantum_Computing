(*  Title:   Day12_Quantum_Parallelism.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 23 September 2011 (Day 12)
*)

theory Day12_Quantum_Parallelism
  imports
    Day08_Measurements
    Day09_POVMs_Entanglement
    Day10_Quantum_Gates
begin

section \<open>Day 12 (23 September 2011): quantum parallelism\<close>

text \<open>Since $He_0=(e_0+e_1)/\sqrt2$,
\[ H^{\otimes N}(e_0\otimes\cdots\otimes e_0)=\Bigl(\tfrac1{\sqrt2}\Bigr)^N\sum_{J\in\Z_2^N}e_J
   =\Bigl(\tfrac1{\sqrt2}\Bigr)^N\sum_J\ket J . \]
Only the case $N=1$ is stated here; the general identity is \<open>hadamard_uniform_N\<close> below (with \<open>tensor_pow_mat\<close> for $H^{\otimes N}$).

\begin{notesdef}[Oracle]
For $f:\Z_2^N\to\Z_2$, the vectors $e_J\otimes e_{i+f(J)}$ form an orthonormal basis of
$(\C^2)^{\otimes N}\otimes\C^2$, so there is a unitary $U_f$ with
$U_f(e_J\otimes e_i)=e_J\otimes e_{i+f(J)}$, the \emph{oracle} for $f$.
\end{notesdef}
\begin{notesprop}
For a unit vector $\gamma$, the measurement $P_0=\ketbra\gamma\gamma$, $P_1=I-P_0$ has
$p_0(\psi)=|\braket\gamma\psi|^2$ and $p_1(\psi)=1-|\braket\gamma\psi|^2$.
\end{notesprop}
Application: with $x=(He_0)^{\otimes N}$, $U_f(x\otimes e_0)=2^{-N/2}\sum_J e_J\otimes e_{f(J)}$,
and measuring against $\gamma=x\otimes e_0$ gives $\braket\gamma{U_f(x\otimes e_0)}=M/2^N$ with
$M=\#\{J:f(J)=0\}$, hence $p_0=(M/2^N)^2$: repeating the experiment estimates $M$ (a
Bernoulli trial).  The existence of the oracle is formalised below; the proposition is
\<open>rank_one_meas_prob\<close> (Day 8); the counting identity is \<open>counting_probability\<close>
below.\<close>

definition oracle_unitary :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "oracle_unitary f N \<equiv>
     \<exists>U :: complex Matrix.mat.
       U \<in> carrier_mat (2^(N+1)) (2^(N+1)) \<and>
       unitary U \<and>
       (\<forall>J < 2^N. \<forall>i < 2.
          U *\<^sub>v (tensor_vec (unit_vec (2^N) J) (unit_vec 2 i)) =
          tensor_vec (unit_vec (2^N) J) (unit_vec 2 ((i + f J) mod 2)))"

text \<open>The oracle is the permutation matrix of the involution $\sigma(2J+i)=2J+(i\oplus f(J))$ of the
computational basis of $\C^{2^N}\otimes\C^2$ (the basis vector $e_J\otimes e_i$ is $e_{2J+i}$):
$Ue_l=e_{\sigma(l)}$, so $U^2=I$ and $U=U^*$.\<close>

theorem oracle_exists:
  fixes f :: "nat \<Rightarrow> nat"
  assumes f_range: "\<forall>J < 2^(N :: nat). f J < 2"
  shows "oracle_unitary f N"
proof -
  let ?d = "(2::nat) ^ N * 2"
  define \<sigma> where "\<sigma> l = (l div 2) * 2 + (l mod 2 + f (l div 2)) mod 2" for l
  have \<sigma>_lt: "\<sigma> l < ?d" if "l < ?d" for l
    unfolding \<sigma>_def using less_mult_imp_div_less[OF that] mod_less_divisor[of 2 "l mod 2 + f (l div 2)"] by linarith
  have \<sigma>\<sigma>: "\<sigma> (\<sigma> l) = l" if "l < ?d" for l
  proof -
    have "\<sigma> l div 2 = l div 2" "\<sigma> l mod 2 = (l mod 2 + f (l div 2)) mod 2" unfolding \<sigma>_def by simp_all
    thus ?thesis unfolding \<sigma>_def[of "\<sigma> l"] by (simp add: mod_add_left_eq add.assoc div_mult_mod_eq flip: mult_2)
  qed
  define U :: "complex Matrix.mat" where "U = Matrix.mat ?d ?d (\<lambda>(k, l). if k = \<sigma> l then 1 else 0)"
  have Uc: "U \<in> carrier_mat ?d ?d" unfolding U_def by simp
  have Ucol: "U *\<^sub>v unit_vec ?d l = unit_vec ?d (\<sigma> l)" if "l < ?d" for l
    using that \<sigma>_lt[OF that] by (intro eq_vecI) (auto simp: U_def)
  have UU: "U * U = 1\<^sub>m ?d"
  proof (rule eq_matI)
    fix k l assume "k < dim_row (1\<^sub>m ?d)" "l < dim_col (1\<^sub>m ?d)"
    hence kl: "k < ?d" "l < ?d" by simp_all
    have "(U * U) $$ (k, l) = (\<Sum>m = 0..<?d. (if k = \<sigma> m then 1 else 0) * (if m = \<sigma> l then 1 else 0))"
      using kl by (simp add: U_def scalar_prod_def lessThan_atLeast0)
    also have "\<dots> = (\<Sum>m = 0..<?d. if m = \<sigma> l then (if k = \<sigma> m then 1 else 0) else 0)"
      by (intro sum.cong refl) simp
    also have "\<dots> = (if k = l then 1 else 0)" using \<sigma>_lt[OF kl(2)] \<sigma>\<sigma>[OF kl(2)] by (simp add: sum.delta)
    finally show "(U * U) $$ (k, l) = 1\<^sub>m ?d $$ (k, l)" using kl by simp
  qed (simp_all add: U_def)
  have Ud: "U\<^sup>\<dagger> = U"
  proof (rule eq_matI)
    fix k l assume "k < dim_row U" "l < dim_col U"
    hence kl: "k < ?d" "l < ?d" unfolding U_def by simp_all
    have "(l = \<sigma> k) = (k = \<sigma> l)" using \<sigma>\<sigma>[OF kl(1)] \<sigma>\<sigma>[OF kl(2)] by auto
    thus "U\<^sup>\<dagger> $$ (k, l) = U $$ (k, l)" using kl unfolding U_def dagger_def by simp
  qed (simp_all add: U_def dagger_def)
  have uU: "unitary U" unfolding unitary_def Ud using UU Uc by simp
  have act: "U *\<^sub>v tensor_vec (unit_vec (2^N) J) (unit_vec 2 i) =
             tensor_vec (unit_vec (2^N) J) (unit_vec 2 ((i + f J) mod 2))" if J: "J < 2^N" and i: "i < 2" for J i
  proof -
    have l: "J * 2 + i < ?d" using J i by linarith
    have s: "\<sigma> (J * 2 + i) = J * 2 + (i + f J) mod 2" unfolding \<sigma>_def using i by simp
    have r: "(i + f J) mod 2 < 2" by simp
    show ?thesis unfolding tensor_unit_vec[OF J i] tensor_unit_vec[OF J r] Ucol[OF l] s ..
  qed
  show ?thesis unfolding oracle_unitary_def using Uc
    by (intro exI[of _ U] conjI allI impI) (simp_all add: uU act mult.commute)
qed

text \<open>$M=\#\{J<2^N : f(J)=0\}$, the quantity estimated by the counting experiment.\<close>

definition count_zeros :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "count_zeros f N \<equiv> card {J. J < 2^N \<and> f J = 0}"

subsection \<open>$H^{\otimes N}$ on $|0\cdots0\rangle$ and the counting probability (D12-1, D12-4)\<close>

text \<open>$N$-fold tensor powers (last factor least significant, matching @{const tensor_vec}).\<close>

primrec tensor_pow_mat :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "tensor_pow_mat A 0 = 1\<^sub>m 1"
| "tensor_pow_mat A (Suc k) = Tensor.tensor_mat (tensor_pow_mat A k) A"

primrec tensor_pow_vec :: "complex Matrix.vec \<Rightarrow> nat \<Rightarrow> complex Matrix.vec" where
  "tensor_pow_vec v 0 = Matrix.vec 1 (\<lambda>_. 1)"
| "tensor_pow_vec v (Suc k) = tensor_vec (tensor_pow_vec v k) v"

lemma tensor_pow_mat_carrier:
  assumes "A \<in> carrier_mat 2 2"
  shows "tensor_pow_mat A k \<in> carrier_mat (2^k) (2^k)"
  using assms by (induction k) auto

lemma tensor_pow_vec_dim:
  assumes "dim_vec v = 2"
  shows "dim_vec (tensor_pow_vec v k) = 2^k"
  using assms by (induction k) (auto simp: tensor_vec_dim)

text \<open>By the mixed-product rule $(A\otimes B)(v\otimes w)=Av\otimes Bw$, applied $k$ times,
$A^{\otimes k}v^{\otimes k}=(Av)^{\otimes k}$.  With $H\ket0=\tfrac1{\sqrt2}(1,1)$, and since
$(c,c)^{\otimes N}$ is the constant vector with entries $c^N$,
\[ H^{\otimes N}\ket{0\cdots0}=\frac1{\sqrt{2^N}}\sum_{J<2^N}\ket J. \]\<close>

lemma tensor_pow_mat_vec:
  assumes Ac: "A \<in> carrier_mat 2 2" and vd: "dim_vec v = 2"
  shows "tensor_pow_mat A k *\<^sub>v tensor_pow_vec v k = tensor_pow_vec (A *\<^sub>v v) k"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have Pc: "tensor_pow_mat A k \<in> carrier_mat (2^k) (2^k)" by (rule tensor_pow_mat_carrier[OF Ac])
  have pd: "dim_vec (tensor_pow_vec v k) = 2^k" by (rule tensor_pow_vec_dim[OF vd])
  show ?case
    using tensor_mat_vec_mult[OF Pc Ac pd vd] Suc.IH by simp
qed

lemma tensor_pow_vec_const:
  "tensor_pow_vec (Matrix.vec 2 (\<lambda>_. c)) k = Matrix.vec (2^k) (\<lambda>_. c^k)"
proof (induction k)
  case 0 show ?case by simp
next
  case (Suc k)
  show ?case
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (Matrix.vec (2 ^ Suc k) (\<lambda>_. c ^ Suc k))"
    hence i: "i < 2^k * 2" by simp
    have idiv: "i div 2 < 2^k" using i by (simp add: div_less_iff_less_mult)
    show "tensor_pow_vec (Matrix.vec 2 (\<lambda>_. c)) (Suc k) $ i =
          Matrix.vec (2 ^ Suc k) (\<lambda>_. c ^ Suc k) $ i"
      using tensor_vec_index[of "Matrix.vec (2^k) (\<lambda>_. c^k)" "2^k" "Matrix.vec 2 (\<lambda>_. c)" 2 i] i idiv
      by (simp add: Suc.IH)
  qed (simp add: tensor_vec_dim Suc.IH)
qed

definition uniform_vec :: "nat \<Rightarrow> complex Matrix.vec" where
  "uniform_vec N = Matrix.vec (2^N) (\<lambda>_. complex_of_real (1 / sqrt 2) ^ N)"

lemma uniform_vec_dim [simp]: "dim_vec (uniform_vec N) = 2^N"
  by (simp add: uniform_vec_def)

lemma hadamard_e0_const: "Hadamard *\<^sub>v unit_vec 2 0 = Matrix.vec 2 (\<lambda>_. complex_of_real (1 / sqrt 2))"
proof -
  have c: "1 / csqrt 2 = complex_of_real (1 / sqrt 2)" by (simp add: csqrt_two)
  show ?thesis unfolding hadamard_e0 c
    by (rule eq_vecI) (auto simp: less_2_cases_iff)
qed

theorem hadamard_uniform_N:
  "tensor_pow_mat Hadamard N *\<^sub>v tensor_pow_vec (unit_vec 2 0) N = uniform_vec N"
proof -
  have Hc: "Hadamard \<in> carrier_mat 2 2" by (simp add: Hadamard_def Quantum.H_def)
  have "tensor_pow_mat Hadamard N *\<^sub>v tensor_pow_vec (unit_vec 2 0) N = tensor_pow_vec (Hadamard *\<^sub>v unit_vec 2 0) N"
    by (rule tensor_pow_mat_vec[OF Hc]) simp
  also have "\<dots> = tensor_pow_vec (Matrix.vec 2 (\<lambda>_. complex_of_real (1 / sqrt 2))) N"
    unfolding hadamard_e0_const ..
  also have "\<dots> = uniform_vec N" unfolding tensor_pow_vec_const uniform_vec_def ..
  finally show ?thesis .
qed

lemma inner_prod_unit_vec_2:
  assumes "k < 2"
  shows "\<langle>unit_vec 2 0 | unit_vec 2 k\<rangle> = (if k = 0 then 1 else 0)"
proof -
  have "\<langle>unit_vec 2 0 | unit_vec 2 k\<rangle> = cnj (unit_vec 2 0 $ k)"
    using inner_prod_unit_vec_right[of "unit_vec 2 0" 2 k] assms by simp
  thus ?thesis using assms by simp
qed

text \<open>Every basis state has amplitude $2^{-N/2}$ in the uniform state, which therefore has norm
$\sqrt{2^N\cdot2^{-N}}=1$.\<close>

lemma inner_prod_uniform_unit:
  assumes "J < 2^N"
  shows "\<langle>uniform_vec N | unit_vec (2^N) J\<rangle> = complex_of_real (1 / sqrt 2) ^ N"
  using inner_prod_unit_vec_right[of "uniform_vec N" "2^N" J] assms by (simp add: uniform_vec_def)

lemma uniform_coeff_sq:
  "complex_of_real (1 / sqrt 2) ^ N * complex_of_real (1 / sqrt 2) ^ N = complex_of_real ((1/2) ^ N)"
proof -
  \<comment> \<open>Coercion inference parses \<open>complex_of_real (1 / sqrt 2)\<close> as \<open>1 / complex_of_real (sqrt 2)\<close>.\<close>
  have s2: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
    using real_sqrt_pow2[of 2] by (simp add: power2_eq_square flip: of_real_mult)
  have "complex_of_real (1 / sqrt 2) * complex_of_real (1 / sqrt 2) = complex_of_real (1/2)"
    by (simp add: times_divide_times_eq s2)
  thus ?thesis unfolding power_mult_distrib[symmetric] of_real_power
    by (rule arg_cong[where f = "\<lambda>z. z ^ N"])
qed

lemma uniform_vec_self: "\<langle>uniform_vec N | uniform_vec N\<rangle> = 1"
proof -
  let ?c = "complex_of_real (1 / sqrt 2) ^ N"
  have "\<langle>uniform_vec N | uniform_vec N\<rangle> = (\<Sum>i = 0..<2^N. cnj (uniform_vec N $ i) * uniform_vec N $ i)"
    using inner_prod_sum[of "uniform_vec N" "2^N" "uniform_vec N"] by simp
  also have "\<dots> = (\<Sum>i = 0..<(2::nat)^N. ?c * ?c)"
    by (intro sum.cong refl) (simp add: uniform_vec_def)
  also have "\<dots> = (\<Sum>i = 0..<(2::nat)^N. complex_of_real ((1/2) ^ N))" unfolding uniform_coeff_sq ..
  also have "\<dots> = of_nat (2^N) * complex_of_real ((1/2) ^ N)" by simp
  also have "\<dots> = ((2::complex) * (1/2)) ^ N" by (simp only: power_mult_distrib) simp
  also have "\<dots> = 1" by simp
  finally show ?thesis .
qed

lemma uniform_tensor_e0_as_sum:
  "tensor_vec (uniform_vec N) (unit_vec 2 0) =
   vec_sum (2^(N+1)) {J. J < 2^N}
     (\<lambda>J. complex_of_real (1 / sqrt 2) ^ N \<cdot>\<^sub>v tensor_vec (unit_vec (2^N) J) (unit_vec 2 0))"
proof (rule eq_vecI)
  let ?c = "complex_of_real (1 / sqrt 2) ^ N"
  let ?t = "\<lambda>J. tensor_vec (unit_vec (2^N) J) (unit_vec 2 0)"
  fix i assume "i < dim_vec (vec_sum (2^(N+1)) {J. J < 2^N} (\<lambda>J. ?c \<cdot>\<^sub>v ?t J))"
  hence i': "i < 2^(N+1)" by simp
  hence i: "i < 2^N * 2" by (simp add: power_add)
  have idiv: "i div 2 < 2^N" using i by (simp add: div_less_iff_less_mult)
  have lhs: "tensor_vec (uniform_vec N) (unit_vec 2 0) $ i = ?c * (if i mod 2 = 0 then 1 else 0)"
    using tensor_vec_index[of "uniform_vec N" "2^N" "unit_vec 2 0" 2 i] i idiv
    by (simp add: uniform_vec_def)
  have trm: "\<And>J :: nat. J < 2^N \<Longrightarrow>
      (?c \<cdot>\<^sub>v ?t J) $ i = (if i div 2 = J then ?c * (if i mod 2 = 0 then 1 else 0) else 0)"
  proof -
    fix J :: nat assume J: "J < 2^N"
    have "(?c \<cdot>\<^sub>v ?t J) $ i = ?c * ?t J $ i"
      using i by (simp add: tensor_vec_dim)
    also have "?t J $ i = unit_vec (2^N) J $ (i div 2) * unit_vec 2 0 $ (i mod 2)"
      using tensor_vec_index[of "unit_vec (2^N) J" "2^N" "unit_vec 2 0" 2 i] i by simp
    also have "\<dots> = (if i div 2 = J then 1 else 0) * (if i mod 2 = 0 then 1 else 0)"
      using idiv J by simp
    finally have e: "(?c \<cdot>\<^sub>v ?t J) $ i = ?c * ((if i div 2 = J then 1 else 0) * (if i mod 2 = 0 then 1 else 0))" .
    show "(?c \<cdot>\<^sub>v ?t J) $ i = (if i div 2 = J then ?c * (if i mod 2 = 0 then 1 else 0) else 0)"
      unfolding e by simp
  qed
  have "vec_sum (2^(N+1)) {J. J < 2^N} (\<lambda>J. ?c \<cdot>\<^sub>v ?t J) $ i = sum (\<lambda>J. (?c \<cdot>\<^sub>v ?t J) $ i) {J. J < 2^N}"
    by (rule vec_sum_index[OF i'])
  also have "\<dots> = sum (\<lambda>J. if i div 2 = J then ?c * (if i mod 2 = 0 then 1 else 0) else 0) {J. J < 2^N}"
  proof (rule sum.cong[OF refl])
    fix J :: nat assume "J \<in> {J. J < 2^N}"
    hence "J < 2^N" by simp
    thus "(?c \<cdot>\<^sub>v ?t J) $ i = (if i div 2 = J then ?c * (if i mod 2 = 0 then 1 else 0) else 0)"
      by (rule trm)
  qed
  also have "\<dots> = ?c * (if i mod 2 = 0 then 1 else 0)"
    using idiv by (simp add: sum.delta')
  finally show "tensor_vec (uniform_vec N) (unit_vec 2 0) $ i =
        vec_sum (2^(N+1)) {J. J < 2^N} (\<lambda>J. ?c \<cdot>\<^sub>v ?t J) $ i"
    using lhs by simp
qed (simp add: tensor_vec_dim power_add)

lemma uniform_e0_state: "quantum_state (2^(N+1)) (tensor_vec (uniform_vec N) (unit_vec 2 0))"
proof -
  let ?\<gamma> = "tensor_vec (uniform_vec N) (unit_vec 2 0)"
  have gd: "dim_vec ?\<gamma> = 2^(N+1)" by (simp add: tensor_vec_dim power_add)
  have "\<langle>?\<gamma> | ?\<gamma>\<rangle> = \<langle>uniform_vec N | uniform_vec N\<rangle> * \<langle>unit_vec 2 0 | unit_vec 2 0\<rangle>"
    by (rule tensor_inner_prod) simp_all
  also have "\<dots> = 1" using uniform_vec_self inner_prod_unit_vec_2[of 0] by simp
  finally have "complex_of_real (\<parallel>?\<gamma>\<parallel>\<^sup>2) = 1" by (simp only: cpx_vec_length_inner_prod)
  hence sq: "\<parallel>?\<gamma>\<parallel>\<^sup>2 = 1" using of_real_eq_1_iff by fastforce
  have nn: "0 \<le> \<parallel>?\<gamma>\<parallel>" by (simp add: cpx_vec_length_def sum_nonneg)
  have "\<parallel>?\<gamma>\<parallel> = 1" using sq nn by (auto simp: power2_eq_1_iff)
  thus ?thesis using gd by (simp add: quantum_state_def)
qed

text \<open>The notes' computation: with $x=H^{\otimes N}|0\cdots0\rangle$ and $\gamma=x\otimes e_0$,
$p_0(U_f(x\otimes e_0))=(M/2^N)^2$ where $M=\#\{J: f(J)=0\}$.\<close>

theorem counting_probability:
  fixes f :: "nat \<Rightarrow> nat" and U :: "complex Matrix.mat"
  assumes f_range: "\<forall>J < 2^N. f J < 2"
      and Uc: "U \<in> carrier_mat (2^(N+1)) (2^(N+1))"
      and orac: "\<forall>J < 2^N. \<forall>i < 2.
          U *\<^sub>v (tensor_vec (unit_vec (2^N) J) (unit_vec 2 i)) =
          tensor_vec (unit_vec (2^N) J) (unit_vec 2 ((i + f J) mod 2))"
  shows "meas_prob (tensor_vec (uniform_vec N) (unit_vec 2 0) \<oslash> tensor_vec (uniform_vec N) (unit_vec 2 0))
           (U *\<^sub>v tensor_vec (uniform_vec N) (unit_vec 2 0))
         = (real (count_zeros f N) / 2^N)\<^sup>2"
proof -
  define \<gamma> where "\<gamma> = tensor_vec (uniform_vec N) (unit_vec 2 0)"
  let ?c = "complex_of_real (1 / sqrt 2) ^ N"
  let ?S = "{J. J < (2::nat)^N}"
  let ?t = "\<lambda>J. tensor_vec (unit_vec (2^N) J) (unit_vec 2 0)"
  let ?t' = "\<lambda>J. tensor_vec (unit_vec (2^N) J) (unit_vec 2 (f J))"
  have finS: "finite ?S" by simp
  have td: "\<And>J :: nat. dim_vec (?t J) = 2^(N+1)" by (simp add: tensor_vec_dim power_add)
  have t'd: "\<And>J :: nat. dim_vec (?t' J) = 2^(N+1)" by (simp add: tensor_vec_dim power_add)
  have gd: "dim_vec \<gamma> = 2^(N+1)" unfolding \<gamma>_def by (simp add: tensor_vec_dim power_add)
  have Ut: "\<And>J :: nat. J < 2^N \<Longrightarrow> U *\<^sub>v ?t J = ?t' J"
  proof -
    fix J :: nat assume J: "J < 2^N"
    have fJ: "(0 + f J) mod 2 = f J" using f_range J by simp
    show "U *\<^sub>v ?t J = ?t' J"
      using orac[rule_format, OF J, of 0] unfolding fJ by simp
  qed
  have Ug: "U *\<^sub>v \<gamma> = vec_sum (2^(N+1)) ?S (\<lambda>J. ?c \<cdot>\<^sub>v ?t' J)"
  proof -
    have "U *\<^sub>v \<gamma> = U *\<^sub>v vec_sum (2^(N+1)) ?S (\<lambda>J. ?c \<cdot>\<^sub>v ?t J)"
      unfolding \<gamma>_def uniform_tensor_e0_as_sum ..
    also have "\<dots> = vec_sum (2^(N+1)) ?S (\<lambda>J. U *\<^sub>v (?c \<cdot>\<^sub>v ?t J))"
      by (rule mult_mat_vec_vec_sum[OF Uc finS]) (simp add: td)
    also have "\<dots> = vec_sum (2^(N+1)) ?S (\<lambda>J. ?c \<cdot>\<^sub>v ?t' J)"
      by (rule vec_sum_cong) (simp add: mult_mat_vec_smult_vec[OF Uc td] Ut)
    finally show ?thesis .
  qed
  have ip: "\<langle>\<gamma> | U *\<^sub>v \<gamma>\<rangle> = complex_of_real (real (count_zeros f N) * (1/2)^N)"
  proof -
    have "\<langle>\<gamma> | U *\<^sub>v \<gamma>\<rangle> = sum (\<lambda>J. \<langle>\<gamma> | ?c \<cdot>\<^sub>v ?t' J\<rangle>) ?S"
      unfolding Ug by (rule inner_prod_vec_sum_right[OF gd]) (simp add: t'd)
    also have "\<dots> = sum (\<lambda>J. ?c * (?c * (if f J = 0 then 1 else 0))) ?S"
    proof (rule sum.cong[OF refl])
      fix J assume "J \<in> ?S"
      hence J: "J < 2^N" by simp
      have "\<langle>\<gamma> | ?c \<cdot>\<^sub>v ?t' J\<rangle> = ?c * \<langle>\<gamma> | ?t' J\<rangle>"
        by (rule inner_prod_right_smult')
      also have "\<langle>\<gamma> | ?t' J\<rangle> = \<langle>uniform_vec N | unit_vec (2^N) J\<rangle> * \<langle>unit_vec 2 0 | unit_vec 2 (f J)\<rangle>"
        unfolding \<gamma>_def by (rule tensor_inner_prod) simp_all
      also have "\<dots> = ?c * (if f J = 0 then 1 else 0)"
        using inner_prod_uniform_unit[OF J] inner_prod_unit_vec_2 f_range J by simp
      finally show "\<langle>\<gamma> | ?c \<cdot>\<^sub>v ?t' J\<rangle> = ?c * (?c * (if f J = 0 then 1 else 0))" .
    qed
    also have "\<dots> = sum (\<lambda>J. if f J = 0 then ?c * ?c else 0) ?S"
      by (intro sum.cong refl) simp
    also have "\<dots> = of_nat (count_zeros f N) * (?c * ?c)"
    proof -
      have "?S \<inter> {J. f J = 0} = {J. J < 2^N \<and> f J = 0}" by auto
      thus ?thesis by (simp add: sum.If_cases[OF finS] count_zeros_def)
    qed
    also have "\<dots> = complex_of_real (real (count_zeros f N) * (1/2)^N)"
      unfolding uniform_coeff_sq by simp
    finally show ?thesis .
  qed
  have p: "meas_prob (\<gamma> \<oslash> \<gamma>) (U *\<^sub>v \<gamma>) = (cmod \<langle>\<gamma> | U *\<^sub>v \<gamma>\<rangle>)\<^sup>2"
    using rank_one_meas_prob[OF uniform_e0_state[of N, folded \<gamma>_def], of "U *\<^sub>v \<gamma>"] Uc by simp
  have nn: "0 \<le> real (count_zeros f N) * (1/2)^N" by simp
  have "cmod \<langle>\<gamma> | U *\<^sub>v \<gamma>\<rangle> = \<bar>real (count_zeros f N) * (1/2)^N\<bar>"
    unfolding ip by (rule norm_of_real)
  also have "\<dots> = real (count_zeros f N) * (1/2)^N" using nn by simp
  also have "\<dots> = real (count_zeros f N) / 2^N" by (simp add: power_one_over)
  finally have "meas_prob (\<gamma> \<oslash> \<gamma>) (U *\<^sub>v \<gamma>) = (real (count_zeros f N) / 2^N)\<^sup>2"
    unfolding p by simp
  thus ?thesis unfolding \<gamma>_def .
qed

end
