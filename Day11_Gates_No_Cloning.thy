(*  Title:   Day11_Gates_No_Cloning.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 21 September 2011 (Day 11)
*)

theory Day11_Gates_No_Cloning
  imports Day09_POVMs_Entanglement Day10_Quantum_Gates
begin

section \<open>Day 11 (21 September 2011): gates revisited, circuit diagrams, no-cloning\<close>

text \<open>The lecture opens with two corrections: $H^2=I$ (not $X$), with $He_0=(e_0+e_1)/\sqrt2$,
$Xe_0=e_1$, $Xe_1=e_0$, $He_1=(e_0-e_1)/\sqrt2$, so that $X$ and $H$ are reflections; and the
truth tables of CNOT ($\ket{a,b}\mapsto\ket{a,b+a}$, arithmetic in $\Z_2$) and of CCNOT
($\ket{a,b,c}\mapsto\ket{a,b,c+ab}$).  Circuit diagrams are introduced; the CNOT with
control on the second wire has matrix $\begin{pmatrix}1&0&0&0\\0&0&0&1\\0&0&1&0\\0&1&0&0\end{pmatrix}$,
and three alternating CNOTs compose to the swap of the two wires (\<open>SWAP_three_CNOTs\<close>
below).\<close>

subsection \<open>Cloning and no-cloning\<close>

text \<open>CNOT clones the computational basis: $U(e_a\otimes e_0)=e_a\otimes e_a$, and
more generally $\ket{i_1\cdots i_n}\otimes\ket{0\cdots0}\mapsto\ket{i_1\cdots i_n}\otimes
\ket{i_1\cdots i_n}$ for some unitary.  But for $\psi=\alpha e_0+\beta e_1$ with
$\alpha\beta\neq0$, $U(\psi\otimes e_0)\neq\psi\otimes\psi$.
\begin{notestheorem}[No-cloning]
There is no state $\phi$ and unitary $U$ on $\Hil\otimes\Hil$ with $U(\psi\otimes\phi)=\psi\otimes\psi$
for all $\psi\in\Hil$.
\end{notestheorem}
The notes argue with $-\psi$; the formal proof (for $\dim\Hil=n\ge2$ and unit vectors $\psi$)
uses two states with inner product neither $0$ nor $1$.\<close>

definition is_cloner :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
  "is_cloner n U \<phi> \<equiv>
     U \<in> carrier_mat (n^2) (n^2) \<and> unitary U \<and> dim_vec \<phi> = n \<and>
     (\<forall>\<psi>. quantum_state n \<psi> \<longrightarrow>
        U *\<^sub>v tensor_vec \<psi> \<phi> = tensor_vec \<psi> \<psi>)"

text \<open>Two states whose inner product is neither $0$ nor $1$ exist once $n\ge2$.\<close>

lemma two_states_nontrivial_inner_prod:
  assumes n: "2 \<le> n"
  obtains \<psi>\<^sub>1 \<psi>\<^sub>2 :: "complex Matrix.vec"
    where "quantum_state n \<psi>\<^sub>1" and "quantum_state n \<psi>\<^sub>2"
      and "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> \<noteq> (0 :: real)" and "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> \<noteq> (1 :: real)"
proof -
  define r :: complex where "r = complex_of_real (1 / sqrt 2)"
  define \<psi>\<^sub>1 :: "complex Matrix.vec" where "\<psi>\<^sub>1 = unit_vec n 0"
  define \<psi>\<^sub>2 :: "complex Matrix.vec" where
    "\<psi>\<^sub>2 = Matrix.vec n (\<lambda>i. if i = 0 \<or> i = 1 then r else 0)"

  from n have n0: "0 < n" and n1: "1 < n" by auto

  \<comment> \<open>Arithmetic facts about \<open>r\<close>.\<close>
  have sqrt2_pos: "(0::real) < sqrt 2" by simp
  have sqrt2_sq: "sqrt 2 * sqrt 2 = 2"
    using sqrt2_pos
    by auto 
  have r_sq_real: "(1 / sqrt 2) * (1 / sqrt 2) = (1::real) / 2"
    using sqrt2_sq by simp
  have r_sq: "r * r = 1 / 2"
    unfolding r_def
    by (metis numeral_One of_real_divide of_real_mult of_real_numeral r_sq_real)   
  have cnj_r: "cnj r = r"
    unfolding r_def by simp
  have r_ne_0: "r \<noteq> 0"
    unfolding r_def using sqrt2_pos by simp
  have r_ne_1: "r \<noteq> 1"
    using r_sq by fastforce
 
  \<comment> \<open>\<open>\<psi>\<^sub>1\<close> is a quantum state.\<close>
  have \<psi>\<^sub>1_dim: "dim_vec \<psi>\<^sub>1 = n" by (simp add: \<psi>\<^sub>1_def)
  have \<psi>\<^sub>1_qs: "quantum_state n \<psi>\<^sub>1"
    unfolding quantum_state_def using n0 by (simp add: \<psi>\<^sub>1_def)

  have \<psi>\<^sub>2_dim: "dim_vec \<psi>\<^sub>2 = n" by (simp add: \<psi>\<^sub>2_def)
  have \<psi>\<^sub>2_entry: "\<And>i. i < n \<Longrightarrow> \<psi>\<^sub>2 $ i = (if i = 0 \<or> i = 1 then r else 0)"
    by (simp add: \<psi>\<^sub>2_def)

  have set_split: "{0..<n} = {0, 1} \<union> {2..<n}" using n by auto
  have set_disj:  "{0::nat, 1} \<inter> {2..<n} = {}" by auto

  have inner_\<psi>\<^sub>2_self: "\<langle>\<psi>\<^sub>2 | \<psi>\<^sub>2\<rangle> = (1 :: real)"
  proof -
    let ?t = "\<lambda>i::nat. if i = 0 \<or> i = 1 then cnj r * r else (0::complex)"

    have sum_01: "(\<Sum>i \<in> {0::nat, 1}. ?t i) = 2 * (cnj r * r)" by simp
    have sum_2n: "(\<Sum>i \<in> {2::nat..<n}. ?t i) = 0"
      by (rule sum.neutral, auto)

    have "\<langle>\<psi>\<^sub>2 | \<psi>\<^sub>2\<rangle> = (\<Sum>i = 0..<n. cnj (\<psi>\<^sub>2 $ i) * \<psi>\<^sub>2 $ i)"
      unfolding inner_prod_def using \<psi>\<^sub>2_dim by simp
    also have "\<dots> = (\<Sum>i = 0..<n. ?t i)"
      by (rule sum.cong, auto simp: \<psi>\<^sub>2_entry)
    also have "\<dots> = (\<Sum>i \<in> {0, 1} \<union> {2..<n}. ?t i)"
      by (subst set_split, simp)
    also have "\<dots> = (\<Sum>i \<in> {0::nat, 1}. ?t i) + (\<Sum>i \<in> {2::nat..<n}. ?t i)"
      by (rule sum.union_disjoint) (auto simp: set_disj)
    also have "\<dots> = 2 * (cnj r * r) + 0"
      using sum_01 sum_2n by simp
    also have "\<dots> = 2 * (r * r)" using cnj_r by simp
    also have "\<dots> = 1" using r_sq
      by (simp add: mult.commute) 
    finally show ?thesis by simp
  qed

  \<comment> \<open>\<open>\<parallel>\<psi>\<^sub>2\<parallel> = 1\<close> follows from \<open>\<langle>\<psi>\<^sub>2|\<psi>\<^sub>2\<rangle> = 1\<close> via
      \<open>cpx_vec_length_inner_prod\<close> and non-negativity of the norm.\<close>
  have \<psi>\<^sub>2_norm_sq: "\<parallel>\<psi>\<^sub>2\<parallel>\<^sup>2 = 1"
    using inner_\<psi>\<^sub>2_self
    by (metis cpx_vec_length_inner_prod of_real_1 of_real_eq_iff)
  have \<psi>\<^sub>2_norm: "\<parallel>\<psi>\<^sub>2\<parallel> = 1"
    by (metis Re_complex_of_real \<psi>\<^sub>2_norm_sq bell_state_norm 
        cpx_vec_length_inner_prod inner_prod_csqrt power_one)   
  have \<psi>\<^sub>2_qs: "quantum_state n \<psi>\<^sub>2"
    unfolding quantum_state_def using \<psi>\<^sub>2_dim \<psi>\<^sub>2_norm by simp

  have inner_\<psi>\<^sub>1_\<psi>\<^sub>2: "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> = r"
  proof -
    have "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> = (\<Sum>i = 0..<n. cnj (\<psi>\<^sub>1 $ i) * \<psi>\<^sub>2 $ i)"
      unfolding inner_prod_def using \<psi>\<^sub>2_dim by simp
    also have "\<dots> = (\<Sum>i = 0..<n. if i = 0 then r else 0)"
    proof (rule sum.cong, simp)
      fix i assume "i \<in> {0..<n}"
      then have "i < n" by simp
      thus "cnj (\<psi>\<^sub>1 $ i) * \<psi>\<^sub>2 $ i = (if i = 0 then r else 0)"
        by (auto simp: \<psi>\<^sub>1_def \<psi>\<^sub>2_entry)
    qed
    also have "\<dots> = r"
      using n0 by simp
    finally show ?thesis.
  qed

  from \<psi>\<^sub>1_qs \<psi>\<^sub>2_qs inner_\<psi>\<^sub>1_\<psi>\<^sub>2 r_ne_0 r_ne_1 that
  show thesis by simp
qed

text \<open>The notes' argument: a cloner $U$ with ancilla $\varphi$ makes $\varphi$ a unit vector, and
$\braket{\psi_1}{\psi_2}=\braket{U(\psi_1\otimes\varphi)}{U(\psi_2\otimes\varphi)}=\braket{\psi_1}{\psi_2}^2$ for
unit $\psi_1,\psi_2$, so $\braket{\psi_1}{\psi_2}\in\{0,1\}$; two states with inner product strictly between
exist once $n\ge2$.\<close>

theorem no_cloning:
  assumes n2: "2 \<le> n"
  shows "\<not> (\<exists>U \<phi>. is_cloner n U \<phi>)"
proof
  assume "\<exists>U \<phi>. is_cloner n U \<phi>"
  then obtain U \<phi> where cloner: "is_cloner n U \<phi>" by blast
  from cloner have U_carr: "U \<in> carrier_mat (n^2) (n^2)"
               and U_un:   "unitary U"
               and \<phi>_dim:  "dim_vec \<phi> = n"
               and clone:  "\<forall>\<psi>. quantum_state n \<psi> \<longrightarrow>
                              U *\<^sub>v tensor_vec \<psi> \<phi> = tensor_vec \<psi> \<psi>"
    unfolding is_cloner_def by auto
  from U_carr have U_dc: "dim_col U = n^2" by simp

  obtain \<psi>\<^sub>1 \<psi>\<^sub>2 :: "complex Matrix.vec"
    where \<psi>\<^sub>1_qs: "quantum_state n \<psi>\<^sub>1"
      and \<psi>\<^sub>2_qs: "quantum_state n \<psi>\<^sub>2"
      and c_ne0: "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> \<noteq> 0"
      and c_ne1: "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> \<noteq> 1"
    using two_states_nontrivial_inner_prod[OF n2]
    by auto

  define c :: complex where "c = \<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle>"

  from \<psi>\<^sub>1_qs have \<psi>\<^sub>1_dim: "dim_vec \<psi>\<^sub>1 = n" by (simp add: quantum_state_def)
  from \<psi>\<^sub>2_qs have \<psi>\<^sub>2_dim: "dim_vec \<psi>\<^sub>2 = n" by (simp add: quantum_state_def)

  have inner_self_\<psi>\<^sub>1: "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>1\<rangle> = 1"
    using \<psi>\<^sub>1_qs
    by (metis cpx_vec_length_inner_prod of_real_1 one_power2 quantum_state_norm1)

  have \<phi>_unit: "\<langle>\<phi> | \<phi>\<rangle> = 1"
  proof -
    have tv1_dim: "dim_vec (tensor_vec \<psi>\<^sub>1 \<phi>) = n^2"
      using \<psi>\<^sub>1_dim \<phi>_dim by (simp add: tensor_vec_dim power2_eq_square)
    have clone_\<psi>\<^sub>1: "U *\<^sub>v tensor_vec \<psi>\<^sub>1 \<phi> = tensor_vec \<psi>\<^sub>1 \<psi>\<^sub>1"
      using clone \<psi>\<^sub>1_qs by blast

    have "\<langle>tensor_vec \<psi>\<^sub>1 \<phi> | tensor_vec \<psi>\<^sub>1 \<phi>\<rangle>
            = \<langle>U *\<^sub>v tensor_vec \<psi>\<^sub>1 \<phi> | U *\<^sub>v tensor_vec \<psi>\<^sub>1 \<phi>\<rangle>"
      using unitary_preserves_inner_prod[OF U_un] tv1_dim U_dc by simp
    also have "\<dots> = \<langle>tensor_vec \<psi>\<^sub>1 \<psi>\<^sub>1 | tensor_vec \<psi>\<^sub>1 \<psi>\<^sub>1\<rangle>"
      using clone_\<psi>\<^sub>1 by simp
    also have "\<dots> = \<langle>\<psi>\<^sub>1 | \<psi>\<^sub>1\<rangle> * \<langle>\<psi>\<^sub>1 | \<psi>\<^sub>1\<rangle>"
      using tensor_inner_prod[OF \<psi>\<^sub>1_dim \<psi>\<^sub>1_dim \<psi>\<^sub>1_dim \<psi>\<^sub>1_dim].
    finally have lhs:
      "\<langle>tensor_vec \<psi>\<^sub>1 \<phi> | tensor_vec \<psi>\<^sub>1 \<phi>\<rangle> = \<langle>\<psi>\<^sub>1|\<psi>\<^sub>1\<rangle> * \<langle>\<psi>\<^sub>1|\<psi>\<^sub>1\<rangle>".

    have "\<langle>tensor_vec \<psi>\<^sub>1 \<phi> | tensor_vec \<psi>\<^sub>1 \<phi>\<rangle> = \<langle>\<psi>\<^sub>1|\<psi>\<^sub>1\<rangle> * \<langle>\<phi>|\<phi>\<rangle>"
      using tensor_inner_prod[OF \<psi>\<^sub>1_dim \<psi>\<^sub>1_dim \<phi>_dim \<phi>_dim].
    with lhs have "\<langle>\<psi>\<^sub>1|\<psi>\<^sub>1\<rangle> * \<langle>\<phi>|\<phi>\<rangle> = \<langle>\<psi>\<^sub>1|\<psi>\<^sub>1\<rangle> * \<langle>\<psi>\<^sub>1|\<psi>\<^sub>1\<rangle>" by simp
    thus "\<langle>\<phi>|\<phi>\<rangle> = 1"
      using inner_self_\<psi>\<^sub>1 by simp
  qed

  have tv1_dim: "dim_vec (tensor_vec \<psi>\<^sub>1 \<phi>) = n^2"
    using \<psi>\<^sub>1_dim \<phi>_dim by (simp add: tensor_vec_dim power2_eq_square)
  have tv2_dim: "dim_vec (tensor_vec \<psi>\<^sub>2 \<phi>) = n^2"
    using \<psi>\<^sub>2_dim \<phi>_dim by (simp add: tensor_vec_dim power2_eq_square)
  have clone_\<psi>\<^sub>1: "U *\<^sub>v tensor_vec \<psi>\<^sub>1 \<phi> = tensor_vec \<psi>\<^sub>1 \<psi>\<^sub>1"
    using clone \<psi>\<^sub>1_qs by blast
  have clone_\<psi>\<^sub>2: "U *\<^sub>v tensor_vec \<psi>\<^sub>2 \<phi> = tensor_vec \<psi>\<^sub>2 \<psi>\<^sub>2"
    using clone \<psi>\<^sub>2_qs by blast

  have "c = \<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle>" by (simp add: c_def)
  also have "\<dots> = \<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> * \<langle>\<phi> | \<phi>\<rangle>"
    using \<phi>_unit by simp
  also have "\<dots> = \<langle>tensor_vec \<psi>\<^sub>1 \<phi> | tensor_vec \<psi>\<^sub>2 \<phi>\<rangle>"
    using tensor_inner_prod[OF \<psi>\<^sub>1_dim \<psi>\<^sub>2_dim \<phi>_dim \<phi>_dim] by simp
  also have "\<dots> = \<langle>U *\<^sub>v tensor_vec \<psi>\<^sub>1 \<phi> | U *\<^sub>v tensor_vec \<psi>\<^sub>2 \<phi>\<rangle>"
    using unitary_preserves_inner_prod[OF U_un] tv1_dim tv2_dim U_dc by simp
  also have "\<dots> = \<langle>tensor_vec \<psi>\<^sub>1 \<psi>\<^sub>1 | tensor_vec \<psi>\<^sub>2 \<psi>\<^sub>2\<rangle>"
    using clone_\<psi>\<^sub>1 clone_\<psi>\<^sub>2 by simp
  also have "\<dots> = \<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> * \<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle>"
    using tensor_inner_prod[OF \<psi>\<^sub>1_dim \<psi>\<^sub>2_dim \<psi>\<^sub>1_dim \<psi>\<^sub>2_dim].
  also have "\<dots> = c * c" by (simp add: c_def)
  finally have c_eq_sq: "c = c * c".

  have "c * (c - 1) = 0"
    using c_eq_sq by (simp add: algebra_simps)
  hence "c = 0 \<or> c = 1" by auto
  with c_ne0 c_ne1 show False by (simp add: c_def)
qed

subsection \<open>SWAP from three CNOTs\<close>

lemma less4_cases: "(i::nat) < 4 \<longleftrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
  by auto

text \<open>$\mathrm{CNOT}'$ is CNOT controlled by the second qubit.\<close>

definition CNOT' :: "complex Matrix.mat" where
  "CNOT' = Matrix.mat 4 4 (\<lambda>(i,j). if (i,j) \<in> {(0,0),(1,3),(2,2),(3,1)} then 1 else 0)"

text \<open>D11-3: $\mathrm{SWAP}=\mathrm{CNOT}\cdot\mathrm{CNOT}'\cdot\mathrm{CNOT}$
(\<^const>\<open>SWAP\<close> is the AFP's).\<close>

theorem SWAP_three_CNOTs: "SWAP = CNOT * CNOT' * CNOT"
  by (rule eq_matI)
     (auto simp: SWAP_def CNOT_def CNOT'_def scalar_prod_def sum.atLeast0_lessThan_Suc
        lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq)

lemma SWAP_basis:
  assumes "a < 2" "b < 2"
  shows "SWAP *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 b) (unit_vec 2 a)"
proof -
  have "\<forall>a \<in> {0,1}. \<forall>b \<in> {0,1::nat}.
          SWAP *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 b) (unit_vec 2 a)"
    by (auto intro!: eq_vecI simp: SWAP_def tensor_vec_index tensor_vec_dim scalar_prod_def
        sum.atLeast0_lessThan_Suc lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq less4_cases)
  moreover have "a \<in> {0,1}" "b \<in> {0,1}" using assms by auto
  ultimately show ?thesis by blast
qed

lemma CNOT'_basis:
  assumes "a < 2" "b < 2"
  shows "CNOT' *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 ((a + b) mod 2)) (unit_vec 2 b)"
proof -
  have "\<forall>a \<in> {0,1}. \<forall>b \<in> {0,1::nat}.
          CNOT' *\<^sub>v tensor_vec (unit_vec 2 a) (unit_vec 2 b) = tensor_vec (unit_vec 2 ((a + b) mod 2)) (unit_vec 2 b)"
    by (auto intro!: eq_vecI simp: CNOT'_def tensor_vec_index tensor_vec_dim scalar_prod_def
        sum.atLeast0_lessThan_Suc lessThan_Suc atLeast0LessThan[symmetric] less_Suc_eq less4_cases)
  moreover have "a \<in> {0,1}" "b \<in> {0,1}" using assms by auto
  ultimately show ?thesis by blast
qed

subsection \<open>The CCNOT truth table (D11-2)\<close>

lemma CCNOT_unit_vec:
  assumes k: "k < 8"
  shows "CCNOT *\<^sub>v unit_vec 8 k = unit_vec 8 (if k = 6 then 7 else if k = 7 then 6 else k)"
proof (rule eq_vecI)
  fix r assume "r < dim_vec (unit_vec 8 (if k = 6 then 7 else if k = 7 then 6 else k) :: complex Matrix.vec)"
  hence r: "r < 8" by simp
  have "(CCNOT *\<^sub>v unit_vec 8 k) $ r = (\<Sum>i<8. CCNOT $$ (r, i) * (if i = k then 1 else 0))"
    using r k by (simp add: scalar_prod_def unit_vec_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<8. if i = k then CCNOT $$ (r, i) else 0)" by (rule sum.cong) simp_all
  also have "\<dots> = CCNOT $$ (r, k)" using k by simp
  also have "\<dots> = (if (r = 6 \<and> k = 7) \<or> (r = 7 \<and> k = 6) then 1 else if r = k \<and> r < 6 then 1 else 0)"
    using r k by (simp add: CCNOT_def)
  also have "\<dots> = unit_vec 8 (if k = 6 then 7 else if k = 7 then 6 else k) $ r"
    using r k by (cases "k = 6"; cases "k = 7"; cases "r = k"; simp add: unit_vec_def)
  finally show "(CCNOT *\<^sub>v unit_vec 8 k) $ r = unit_vec 8 (if k = 6 then 7 else if k = 7 then 6 else k) $ r" .
qed simp

text \<open>On basis states $|a,b,c\rangle=e_a\otimes e_b\otimes e_c$: when $a=0$ nothing happens; when
$a=1$, CNOT acts on $b,c$.\<close>

theorem CCNOT_basis:
  assumes a: "a < 2" and b: "b < 2" and c: "c < 2"
  shows "CCNOT *\<^sub>v tensor_vec (unit_vec 2 a) (tensor_vec (unit_vec 2 b) (unit_vec 2 c)) =
         tensor_vec (unit_vec 2 a) (tensor_vec (unit_vec 2 b) (unit_vec 2 (if a = 1 \<and> b = 1 then 1 - c else c)))"
proof -
  have u: "\<And>c. c < 2 \<Longrightarrow> tensor_vec (unit_vec 2 a) (tensor_vec (unit_vec 2 b) (unit_vec 2 c))
                          = (unit_vec 8 (a * 4 + (b * 2 + c)) :: complex Matrix.vec)"
  proof -
    fix c :: nat assume c: "c < 2"
    have bc: "b * 2 + c < 4" using b c by linarith
    show "tensor_vec (unit_vec 2 a) (tensor_vec (unit_vec 2 b) (unit_vec 2 c)) = (unit_vec 8 (a * 4 + (b * 2 + c)) :: complex Matrix.vec)"
      using tensor_unit_vec[OF b c] tensor_unit_vec[OF a bc] by simp
  qed
  have c': "(if a = 1 \<and> b = 1 then 1 - c else c) < 2" using c by auto
  have k: "a * 4 + (b * 2 + c) < 8" using a b c by linarith
  show ?thesis
    unfolding u[OF c] u[OF c'] CCNOT_unit_vec[OF k]
    using a b c by (auto simp: less_2_cases_iff)
qed

corollary CCNOT_truth_table:
  fixes e :: "nat \<Rightarrow> complex Matrix.vec"
  defines "e \<equiv> \<lambda>a. unit_vec 2 a"
  shows "CCNOT *\<^sub>v tensor_vec (e 0) (tensor_vec (e 0) (e 0)) = tensor_vec (e 0) (tensor_vec (e 0) (e 0))"
    and "CCNOT *\<^sub>v tensor_vec (e 0) (tensor_vec (e 0) (e 1)) = tensor_vec (e 0) (tensor_vec (e 0) (e 1))"
    and "CCNOT *\<^sub>v tensor_vec (e 0) (tensor_vec (e 1) (e 0)) = tensor_vec (e 0) (tensor_vec (e 1) (e 0))"
    and "CCNOT *\<^sub>v tensor_vec (e 0) (tensor_vec (e 1) (e 1)) = tensor_vec (e 0) (tensor_vec (e 1) (e 1))"
    and "CCNOT *\<^sub>v tensor_vec (e 1) (tensor_vec (e 0) (e 0)) = tensor_vec (e 1) (tensor_vec (e 0) (e 0))"
    and "CCNOT *\<^sub>v tensor_vec (e 1) (tensor_vec (e 0) (e 1)) = tensor_vec (e 1) (tensor_vec (e 0) (e 1))"
    and "CCNOT *\<^sub>v tensor_vec (e 1) (tensor_vec (e 1) (e 0)) = tensor_vec (e 1) (tensor_vec (e 1) (e 1))"
    and "CCNOT *\<^sub>v tensor_vec (e 1) (tensor_vec (e 1) (e 1)) = tensor_vec (e 1) (tensor_vec (e 1) (e 0))"
  unfolding e_def by (simp_all add: CCNOT_basis)

end
