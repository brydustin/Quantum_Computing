(*
  Title:      Quantum_Computing11.thy
  Author:     Dustin Bryant (based on lectures of Vern Paulsen)

  Day 11 split from Quantum_Computing.thy.  Days 3 through 10 are
  imported from Quantum_Computing_3_10 so they can live in the heap image.
*)

theory Quantum_Computing11
  imports Vern_Paulsen_QC_3_10.Quantum_Computing_3_10
begin

(* ============================================================================
   DAY 11 — 21 / Sep / 11
   Topic: CNOT, CCNOT, Circuit Diagrams; No-Cloning Theorem
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Toffoli (CCNOT) gate: |a,b,c\<rangle> \<mapsto> |a, b, c\<oplus>(a\<and>b)\<rangle>
   -------------------------------------------------------------------------- *)

(* CCNOT is the 8\<times>8 matrix that is the identity on the first 6 basis vectors
   and swaps |110\<rangle> and |111\<rangle>. *)

definition CCNOT :: "complex Matrix.mat" where
  "CCNOT \<equiv> Matrix.mat 8 8
     (\<lambda>(i,j). if (i = 6 \<and> j = 7) \<or> (i = 7 \<and> j = 6)
               then 1
               else if i = j \<and> i < 6 then 1 else 0)"

lemma CCNOT_dagger [simp]:
  "CCNOT\<^sup>\<dagger> = CCNOT"
  unfolding CCNOT_def dagger_def
  by (simp add: cong_mat)

lemma CCNOT_dim_row [simp]:
  "dim_row CCNOT = 8"
  by (simp add: CCNOT_def)

lemma CCNOT_dim_col [simp]:
  "dim_col CCNOT = 8"
  by (simp add: CCNOT_def)

(* CCNOT is the permutation matrix of the transposition 6 \<leftrightarrow> 7, so each row /
   column has exactly one nonzero entry.  Encode that explicitly so we never
   have to enumerate all 64 entries of the product. *)

lemma CCNOT_inv [simp]:
  "CCNOT * CCNOT = 1\<^sub>m 8"
proof (rule eq_matI)
  show "dim_row (CCNOT * CCNOT) = dim_row (1\<^sub>m 8)" by simp
  show "dim_col (CCNOT * CCNOT) = dim_col (1\<^sub>m 8)" by simp
next
  fix i j
  assume "i < dim_row (1\<^sub>m 8)" and "j < dim_col (1\<^sub>m 8)"
  then have i: "i < 8" and j: "j < 8" by simp_all

  define p where "p = (if i < 6 then i else if i = 6 then 7 else 6)"
  define q where "q = (if j < 6 then j else if j = 6 then 7 else 6)"
  have p8: "p < 8" using i by (auto simp: p_def)
  have q8: "q < 8" using j by (auto simp: q_def)

  have row_i: "\<And>k. k < 8 \<Longrightarrow> CCNOT $$ (i, k) = (if k = p then 1 else 0)"
    using i by (auto simp: CCNOT_def p_def)
  have col_j: "\<And>k::nat. k < 8 \<Longrightarrow> CCNOT $$ (k, j) = (if k = q then 1 else 0)"
  proof -
    fix k :: nat assume k: "k < 8"
    from j consider "j < 6" | "j = 6" | "j = 7" by linarith
    then show "CCNOT $$ (k, j) = (if k = q then 1 else 0)"
    proof cases
      case 1
      then have qj: "q = j" by (simp add: q_def)
      show ?thesis using k 1 qj by (auto simp: CCNOT_def)
    next
      case 2
      then have qj: "q = 7" by (simp add: q_def)
      show ?thesis using k 2 qj by (auto simp: CCNOT_def)
    next
      case 3
      then have qj: "q = 6" by (simp add: q_def)
      show ?thesis using k 3 qj by (auto simp: CCNOT_def)
    qed
  qed

  have pq_iff: "(p = q) \<longleftrightarrow> (i = j)"
    using i j by (auto simp: p_def q_def)

  have "(CCNOT * CCNOT) $$ (i, j)
          = (\<Sum>k = 0..<8. CCNOT $$ (i, k) * CCNOT $$ (k, j))"
    using i j by (simp add: times_mat_def scalar_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<8.
        (if k = p then (1::complex) else 0) * (if k = q then 1 else 0))"
    using row_i col_j by auto
  also have "\<dots> = (if p = q then 1 else 0)"
  proof (cases "p = q")
    case True
    have pointwise:
      "(if k = p then (1::complex) else 0) * (if k = q then 1 else 0)
         = (if k = p then 1 else 0)" for k
      using True by simp
    have "(\<Sum>k = 0..<8.
            (if k = p then (1::complex) else 0) * (if k = q then 1 else 0))
        = (\<Sum>k = 0..<8. if k = p then (1::complex) else 0)"
      by (rule sum.cong) (simp_all add: pointwise)
    also have "\<dots> = 1" using p8 by fastforce
    finally show ?thesis using True by simp
  next
    case False
    have "\<And>k. (if k = p then (1::complex) else 0) * (if k = q then 1 else 0) = 0"
      using False by auto
    with False show ?thesis by simp
  qed
  also have "\<dots> = (1\<^sub>m 8) $$ (i, j)"
    using i j pq_iff by simp
  finally show "(CCNOT * CCNOT) $$ (i, j) = (1\<^sub>m 8) $$ (i, j)" .
qed

lemma CCNOT_unitary: "unitary CCNOT"
  by (simp add: unitary_def)

(* --------------------------------------------------------------------------
   No-Cloning Theorem
   -------------------------------------------------------------------------- *)

(* A cloner for state space H would be a fixed state \<phi> and a unitary U on H\<otimes>H
   such that U(\<psi>\<otimes>\<phi>) = \<psi>\<otimes>\<psi> for ALL unit vectors \<psi>. *)

definition is_cloner :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
  "is_cloner n U \<phi> \<equiv>
     U \<in> carrier_mat (n^2) (n^2) \<and> unitary U \<and> dim_vec \<phi> = n \<and>
     (\<forall>\<psi>. quantum_state n \<psi> \<longrightarrow>
        U *\<^sub>v tensor_vec \<psi> \<phi> = tensor_vec \<psi> \<psi>)"

(* Helper: when n \<ge> 2, there exist two quantum states whose inner product
   is neither 0 nor 1.  Explicit witness: \<psi>\<^sub>1 = |0\<rangle>, \<psi>\<^sub>2 = (|0\<rangle> + |1\<rangle>)/\<surd>2,
   giving \<langle>\<psi>\<^sub>1|\<psi>\<^sub>2\<rangle> = 1/\<surd>2.  The construction is standard but bureaucratic; we
   leave the concrete computation for later. *)

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

  \<comment> \<open>Arithmetic facts about @{term r}.\<close>
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
 
  \<comment> \<open>@{term \<psi>\<^sub>1} is a quantum state.\<close>
  have \<psi>\<^sub>1_dim: "dim_vec \<psi>\<^sub>1 = n" by (simp add: \<psi>\<^sub>1_def)
  have \<psi>\<^sub>1_qs: "quantum_state n \<psi>\<^sub>1"
    unfolding quantum_state_def using n0 by (simp add: \<psi>\<^sub>1_def)

  \<comment> \<open>Compute @{term "\<langle>\<psi>\<^sub>2 | \<psi>\<^sub>2\<rangle> = 1"} by splitting the sum at indices 0 and 1.\<close>
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

  \<comment> \<open>@{term "\<parallel>\<psi>\<^sub>2\<parallel> = 1"} follows from @{term "\<langle>\<psi>\<^sub>2|\<psi>\<^sub>2\<rangle> = 1"} via
      @{thm cpx_vec_length_inner_prod} and non-negativity of the norm.\<close>
  have \<psi>\<^sub>2_norm_sq: "\<parallel>\<psi>\<^sub>2\<parallel>\<^sup>2 = 1"
    using inner_\<psi>\<^sub>2_self
    by (metis cpx_vec_length_inner_prod of_real_1 of_real_eq_iff)
  have \<psi>\<^sub>2_norm: "\<parallel>\<psi>\<^sub>2\<parallel> = 1"
    by (metis Re_complex_of_real \<psi>\<^sub>2_norm_sq bell_state_norm 
        cpx_vec_length_inner_prod inner_prod_csqrt power_one)   
  have \<psi>\<^sub>2_qs: "quantum_state n \<psi>\<^sub>2"
    unfolding quantum_state_def using \<psi>\<^sub>2_dim \<psi>\<^sub>2_norm by simp

  \<comment> \<open>Compute @{term "\<langle>\<psi>\<^sub>1 | \<psi>\<^sub>2\<rangle> = r"}.\<close>
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

(* No-Cloning Theorem: no cloner exists (for n \<ge> 2). *)

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

  \<comment> \<open>Pick two unit vectors @{term \<psi>\<^sub>1}, @{term \<psi>\<^sub>2} whose inner product
      @{term c} is neither 0 nor 1.\<close>
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

  \<comment> \<open>Step 1: derive that @{term \<phi>} is itself a unit vector.  Apply the
      cloner identity to @{term \<psi>\<^sub>1}, take the inner product with itself,
      and use unitarity plus @{thm tensor_inner_prod}.\<close>
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

  \<comment> \<open>Step 2: apply the cloner identity to @{term \<psi>\<^sub>1} and @{term \<psi>\<^sub>2}, chain
      inner-product equalities via unitarity and @{thm tensor_inner_prod},
      obtaining @{term "c = c*c"}.\<close>
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

  \<comment> \<open>Step 3: @{term "c = c * c"} forces @{term "c \<in> {0, 1}"}, contradicting
      the choice of @{term \<psi>\<^sub>1}, @{term \<psi>\<^sub>2}.\<close>
  have "c * (c - 1) = 0"
    using c_eq_sq by (simp add: algebra_simps)
  hence "c = 0 \<or> c = 1" by auto
  with c_ne0 c_ne1 show False by (simp add: c_def)
qed


(* ============================================================================
   DAY 12 — 23 / Sep / 11
   Topic: Quantum Parallelism; Oracles
   ============================================================================ *)

(* --------------------------------------------------------------------------
   N-fold tensor product of Hadamard
   -------------------------------------------------------------------------- *)

(* H\<otimes>N applied to |00\<dots>0\<rangle> gives a uniform superposition:
   H^\<otimes>N (e\<^sub>0 \<otimes> \<cdots> \<otimes> e\<^sub>0) = (1/\<surd>2)^N \<Sigma>_{J \<in> Z\<^sub>2^N} e_J  *)

(* We state this for the case N=1 and build inductively. *)

lemma hadamard_uniform_1:
  "H_gate *\<^sub>v unit_vec 2 0 =
   (1/csqrt 2) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"
  using hadamard_e0.

(* --------------------------------------------------------------------------
   Oracle for a function f : Z\<^sub>2^N \<rightarrow> Z\<^sub>2
   -------------------------------------------------------------------------- *)

(* The oracle U_f acts on (\<complex>\<^sup>2)^\<otimes>(N+1) by U_f(e_J \<otimes> e_i) = e_J \<otimes> e_{i\<oplus>f(J)}.
   It is unitary because {e_J \<otimes> e_{i\<oplus>f(J)} : J, i} is an orthonormal basis. *)

definition oracle_unitary :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "oracle_unitary f N \<equiv>
     \<exists>U :: complex Matrix.mat.
       U \<in> carrier_mat (2^(N+1)) (2^(N+1)) \<and>
       unitary U \<and>
       (\<forall>J < 2^N. \<forall>i < 2.
          U *\<^sub>v (tensor_vec (unit_vec (2^N) J) (unit_vec 2 i)) =
          tensor_vec (unit_vec (2^N) J) (unit_vec 2 ((i + f J) mod 2)))"

(* The oracle exists for any f: Z\<^sub>2^N \<rightarrow> Z\<^sub>2. *)

theorem oracle_exists:
  fixes f :: "nat \<Rightarrow> nat"
  assumes f_range: "\<forall>J < 2^(N :: nat). f J < 2"
  shows "oracle_unitary f N"
proof -
  define d :: nat where "d = (2::nat)^(N+1)"
  define d0 :: nat where "d0 = (2::nat)^N"
  have d_eq: "d = d0 * 2"
    unfolding d_def d0_def
  proof -
    have "(2::nat)^(N+1) = (2::nat)^N * (2::nat)^1"
      by (rule power_add)
    also have "(2::nat)^N * (2::nat)^1 = (2::nat)^N * 2"
      by simp
    finally show "(2::nat)^(N+1) = (2::nat)^N * 2" .
  qed
  have d0_pos: "0 < d0" by (simp add: d0_def)
  have d_pos: "0 < d" by (simp add: d_def)

  \<comment> \<open>The oracle permutes basis indices by flipping bit 0 (target qubit) when
      {term "f (l div 2) = 1"}.  We express it as a function @{term \<sigma>}.\<close>
  define \<sigma> :: "nat \<Rightarrow> nat" where
    "\<sigma> l = (l div 2) * 2 + ((l mod 2) + f (l div 2)) mod 2" for l

  \<comment> \<open>The function @{term \<sigma>} stays inside the index range.\<close>
  have \<sigma>_bound: "\<And>l. l < d \<Longrightarrow> \<sigma> l < d"
  proof -
    fix l :: nat assume l: "l < d"
    have div_lt: "l div 2 < d0"
      using l d_eq by (simp add: less_mult_imp_div_less)
    hence "(l div 2) * 2 \<le> (d0 - 1) * 2"
      by (simp add: mult_le_mono1)
    also have "\<dots> = d - 2" using d_eq d0_pos by (simp add: mult.commute)
    finally have bound1: "(l div 2) * 2 \<le> d - 2" .
    have bound2: "((l mod 2) + f (l div 2)) mod 2 < 2" by simp
    have "\<sigma> l < (l div 2) * 2 + 2"
      unfolding \<sigma>_def using bound2 by linarith
    also have "\<dots> \<le> d" using bound1 d_eq d0_pos by linarith
    finally show "\<sigma> l < d" .
  qed

  \<comment> \<open>The function @{term \<sigma>} is an involution: @{term "\<sigma> \<circ> \<sigma> = id"}.\<close>
  have \<sigma>_invol: "\<And>l. l < d \<Longrightarrow> \<sigma> (\<sigma> l) = l"
  proof -
    fix l :: nat assume l: "l < d"
    define J where "J = l div 2"
    define i where "i = l mod 2"
    have J_lt: "J < d0" using l d_eq J_def by (simp add: less_mult_imp_div_less)
    have i_lt: "i < 2" using i_def by simp
    have l_eq: "l = J * 2 + i"
      using J_def i_def by (metis mult_div_mod_eq mult.commute)
    have fJ_lt: "f J < 2" using f_range J_lt d0_def by blast

    \<comment> \<open>Compute @{term "\<sigma> l"}.\<close>      
    have s1: "\<sigma> l = J * 2 + (i + f J) mod 2"
      unfolding \<sigma>_def J_def[symmetric] i_def[symmetric] by simp
    let ?i1 = "(i + f J) mod 2"
    have i1_lt: "?i1 < 2" by simp

    \<comment> \<open>Decompose @{term "\<sigma> l"} in the same div/mod form.\<close>
    have div_sub: "(J * 2 + ?i1) div 2 = J"
      using i1_lt by simp
    have mod_sub: "(J * 2 + ?i1) mod 2 = ?i1"
      using i1_lt by simp

    have "\<sigma> (\<sigma> l) = J * 2 + (?i1 + f J) mod 2"
      using s1 unfolding \<sigma>_def
      using div_sub mod_sub by presburger
    also have "(?i1 + f J) mod 2 = (i + 2 * f J) mod 2"
      by (simp add: mod_add_left_eq mult_2, presburger)
    also have "\<dots> = i mod 2" by simp
    also have "i mod 2 = i" using i_lt by simp
    finally show "\<sigma> (\<sigma> l) = l" using l_eq by simp
  qed

  \<comment> \<open>Define the oracle matrix as the permutation matrix for @{term \<sigma>}.\<close>
  define U :: "complex Matrix.mat" where
    "U = Matrix.mat d d (\<lambda>(k, l). if k = \<sigma> l then 1 else 0)"
  have U_dr: "dim_row U = d" by (simp add: U_def)
  have U_dc: "dim_col U = d" by (simp add: U_def)
  have U_carr: "U \<in> carrier_mat d d"
    using U_dr U_dc by auto

  have U_entry: "\<And>k l. k < d \<Longrightarrow> l < d \<Longrightarrow>
      U $$ (k, l) = (if k = \<sigma> l then 1 else 0)"
    by (simp add: U_def)

  \<comment> \<open>Column \<open>l\<close> of \<open>U\<close> has a unique 1 at row \<open>\<sigma> l\<close>; row \<open>k\<close> has a unique 1
      at column \<open>\<sigma> k\<close> (by involution).\<close>
  have U_row: "\<And>k m. k < d \<Longrightarrow> m < d \<Longrightarrow>
      U $$ (k, m) = (if m = \<sigma> k then 1 else 0)"
  proof -
    fix k m :: nat 
    assume k: "k < d" and m: "m < d"
    show "U $$ (k, m) = (if m = \<sigma> k then 1 else 0)"
    proof (cases "k = \<sigma> m")
      assume k_eqs: "k = \<sigma> m"
      then have "\<sigma> k = m" using \<sigma>_invol[OF m] by auto
      with k_eqs U_entry[OF k m] 
      show ?thesis 
        by simp
    next
      assume kne: "k \<noteq> \<sigma> m"
      \<comment> \<open>We also cannot have @{term "m = \<sigma> k"}, since otherwise
          @{term "\<sigma> m"} would equal @{term "\<sigma> (\<sigma> k)"}, which by
          involution equals @{term k}, contradicting @{term kne}.\<close>
      have "m \<noteq> \<sigma> k"
      proof
        assume "m = \<sigma> k"
        hence "\<sigma> m = \<sigma> (\<sigma> k)" by simp
        also have "\<dots> = k" using \<sigma>_invol[OF k].
        finally have "\<sigma> m = k".
        thus False using kne by simp
      qed
      with kne U_entry[OF k m] show ?thesis by simp
    qed
  qed

  \<comment> \<open>Unitarity of \<open>U\<close>: @{term "U\<^sup>\<dagger> = U"} and @{term "U * U = 1\<^sub>m d"}.\<close>
  have U_dagger: "U\<^sup>\<dagger> = U"
  proof (rule eq_matI)
    show "dim_row (U\<^sup>\<dagger>) = dim_row U" by (simp add: U_def dagger_def)
    show "dim_col (U\<^sup>\<dagger>) = dim_col U" by (simp add: U_def dagger_def)
  next
    fix k l
    assume "k < dim_row U" and "l < dim_col U"
    then have k: "k < d" and l: "l < d" by (simp_all add: U_dr U_dc)
    have "U\<^sup>\<dagger> $$ (k, l) = cnj (U $$ (l, k))"
      using k l by (simp add: dagger_def U_def)
    also have "\<dots> = cnj (if l = \<sigma> k then 1 else 0)"
      using d_eq U_row \<sigma>_invol k l by force  
    also have "\<dots> = (if l = \<sigma> k then 1 else 0)"
      by (simp add: if_distrib [where f = cnj] cong: if_cong)
    also have "\<dots> = U $$ (k, l)"
      using U_row[OF k l] by simp
    finally show "U\<^sup>\<dagger> $$ (k, l) = U $$ (k, l)".
  qed

  have U_sq: "U * U = 1\<^sub>m d"
  proof (rule eq_matI)
    show "dim_row (U * U) = dim_row (1\<^sub>m d)" by (simp add: U_dr)
    show "dim_col (U * U) = dim_col (1\<^sub>m d)" by (simp add: U_dc)
  next
    fix k l
    assume "k < dim_row (1\<^sub>m d)" and "l < dim_col (1\<^sub>m d)"
    then have k: "k < d" and l: "l < d" by simp_all
    have \<sigma>l_lt: "\<sigma> l < d" using \<sigma>_bound l by blast

    have "(U * U) $$ (k, l) = (\<Sum>m = 0..<d. U $$ (k, m) * U $$ (m, l))"
      using k l U_dr U_dc by (simp add: times_mat_def scalar_prod_def)
    also have "\<dots> = (\<Sum>m = 0..<d.
          (if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0))"
    proof (rule sum.cong, simp)
      fix m assume "m \<in> {0..<d}"
      hence m: "m < d" by simp
      have hk: "U $$ (k, m) = (if m = \<sigma> k then 1 else 0)"
        using U_row[OF k m] .
      have hl: "U $$ (m, l) = (if m = \<sigma> l then 1 else 0)"
        using U_entry[OF m l] .
      show "U $$ (k, m) * U $$ (m, l)
              = (if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0)"
        by (simp add: hk hl)
    qed
    also have "\<dots> = (if \<sigma> k = \<sigma> l then 1 else 0)"
    proof (cases "\<sigma> k = \<sigma> l")
      case True
      have pw: "(if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0)
              = (if m = \<sigma> k then 1 else 0)" for m
        using True by simp
      have "(\<Sum>m = 0..<d.
             (if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0))
          = (\<Sum>m = 0..<d. if m = \<sigma> k then (1::complex) else 0)"
        by (rule sum.cong, simp_all add: pw)
      also have "\<dots> = 1"
        using \<sigma>_bound[OF k] by simp
      finally show ?thesis using True by simp
    next
      case False
      have pw: "(if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0) = 0" for m
        using False by auto
      with False show ?thesis by simp
    qed
    also have "\<dots> = (1\<^sub>m d) $$ (k, l)"
    proof (cases "k = l")
      case True
      then show ?thesis using k l by simp
    next
      case False
      have "\<sigma> k \<noteq> \<sigma> l"
      proof
        assume "\<sigma> k = \<sigma> l"
        then have "\<sigma> (\<sigma> k) = \<sigma> (\<sigma> l)" by simp
        with \<sigma>_invol[OF k] \<sigma>_invol[OF l] have "k = l"
          by argo 
        with False show False by simp
      qed
      with False show ?thesis using k l by simp
    qed
    finally show "(U * U) $$ (k, l) = (1\<^sub>m d) $$ (k, l)".
  qed

  have U_unitary: "unitary U"
    unfolding unitary_def
    using U_dagger U_sq U_dr U_dc by simp

  \<comment> \<open>Action on tensor-product basis vectors.\<close>
  have U_acts: "\<And>J i. J < d0 \<Longrightarrow> i < 2 \<Longrightarrow>
     U *\<^sub>v tensor_vec (unit_vec d0 J) (unit_vec 2 i) =
     tensor_vec (unit_vec d0 J) (unit_vec 2 ((i + f J) mod 2))"
  proof -
    fix J i :: nat
    assume J: "J < d0" and i: "i < 2"

    let ?v = "tensor_vec (unit_vec d0 J) (unit_vec 2 i)"
    let ?i1 = "(i + f J) mod 2"
    let ?w = "tensor_vec (unit_vec d0 J) (unit_vec 2 ?i1)"

    have i1_lt: "?i1 < 2" by simp
    have idx_lt: "J * 2 + i < d" 
      using J i d_eq by simp

    have idx1_lt: "J * 2 + ?i1 < d" 
      using J i1_lt d_eq by simp


    have v_dim: "dim_vec ?v = d"
      using tensor_vec_dim d_eq by simp
    have w_dim: "dim_vec ?w = d"
      using tensor_vec_dim d_eq by simp

    \<comment> \<open>Entries of @{term ?v}: 1 at index @{term "J * 2 + i"}, 0 elsewhere.\<close>
    have v_entry: "\<And>k. k < d \<Longrightarrow> ?v $ k = (if k = J * 2 + i then 1 else 0)"
    proof -
      fix k assume k: "k < d"
      have "?v $ k = unit_vec d0 J $ (k div 2) * unit_vec 2 i $ (k mod 2)"
        using tensor_vec_index[of "unit_vec d0 J" d0 "unit_vec 2 i" 2 k] k d_eq
        by simp
      also have "\<dots> = (if k div 2 = J then 1 else 0) * (if k mod 2 = i then 1 else 0)"
        using J i d_eq k by auto 
      also have "\<dots> = (if k div 2 = J \<and> k mod 2 = i then 1 else 0)" by auto
      also have "\<dots> = (if k = J * 2 + i then 1 else 0)"
        using i by (auto simp: mult.commute)
      finally show "?v $ k = (if k = J * 2 + i then 1 else 0)".
    qed

    have w_entry: "\<And>k. k < d \<Longrightarrow> ?w $ k = (if k = J * 2 + ?i1 then 1 else 0)"
    proof -
      fix k assume k: "k < d"
      have "?w $ k = unit_vec d0 J $ (k div 2) * unit_vec 2 ?i1 $ (k mod 2)"
        using tensor_vec_index[of "unit_vec d0 J" d0 "unit_vec 2 ?i1" 2 k] k d_eq by simp
      also have "\<dots> = (if k div 2 = J then 1 else 0) * (if k mod 2 = ?i1 then 1 else 0)"
        using J i1_lt d_eq k by auto
      also have "\<dots> = (if k div 2 = J \<and> k mod 2 = ?i1 then 1 else 0)" 
        by auto
      also have "\<dots> = (if k = J * 2 + ?i1 then 1 else 0)"
        using i1_lt by (auto simp: mult.commute, metis mult_div_mod_eq)
      finally show "?w $ k = (if k = J * 2 + ?i1 then 1 else 0)".
    qed

    \<comment> \<open>@{term "\<sigma> (J * 2 + i) = J * 2 + ?i1"}.\<close>
    have \<sigma>_at: "\<sigma> (J * 2 + i) = J * 2 + ?i1"
      unfolding \<sigma>_def using i by simp

    \<comment> \<open>Show equality entry-by-entry.\<close>
    show "U *\<^sub>v ?v = ?w"
    proof (rule eq_vecI)
      show "dim_vec (U *\<^sub>v ?v) = dim_vec ?w"
        using U_dr U_dc v_dim w_dim by simp
    next
      fix k assume "k < dim_vec ?w"
      then have k: "k < d" using w_dim by simp
      have "(U *\<^sub>v ?v) $ k = (\<Sum>m = 0..<d. U $$ (k, m) * ?v $ m)"
        using k U_dr U_dc v_dim
        by (simp add: mult_mat_vec_def scalar_prod_def)
      also have "\<dots> = (\<Sum>m = 0..<d.
            (if m = \<sigma> k then (1::complex) else 0) *
            (if m = J * 2 + i then 1 else 0))"
        using U_row[OF k] v_entry
        by (intro sum.cong refl, simp)
      also have "\<dots> = (if \<sigma> k = J * 2 + i then 1 else 0)"
      proof (cases "\<sigma> k = J * 2 + i")
        case True
        hence pw: "(if m = \<sigma> k then (1::complex) else 0) *
                    (if m = J * 2 + i then 1 else 0)
                  = (if m = \<sigma> k then 1 else 0)" for m
          by simp
        have "(\<Sum>m = 0..<d.
               (if m = \<sigma> k then (1::complex) else 0) *
               (if m = J * 2 + i then 1 else 0))
            = (\<Sum>m = 0..<d. if m = \<sigma> k then (1::complex) else 0)"
          by (rule sum.cong) (simp_all add: pw)
        also have "\<dots> = 1"
          using \<sigma>_bound[OF k] by simp
        finally show ?thesis using True by simp
      next
        case False
        hence "(if m = \<sigma> k then (1::complex) else 0) * (if m = J * 2 + i then 1 else 0) = 0" for m
          by auto
        thus ?thesis 
          using False by simp
      qed
      also have "\<dots> = (if k = J * 2 + ?i1 then 1 else 0)"
      proof (cases "\<sigma> k = J * 2 + i")
        case True
        hence "k = \<sigma> (J * 2 + i)" using \<sigma>_invol[OF k] by (metis)
        also have "\<dots> = J * 2 + ?i1" using \<sigma>_at.
        finally have "k = J * 2 + ?i1".
        with True show ?thesis by simp
      next
        case False
        moreover have "k \<noteq> J * 2 + ?i1"
        proof
          assume kk: "k = J * 2 + ?i1"
          have "\<sigma> k = \<sigma> (J * 2 + ?i1)" using kk by simp
          also have "\<dots> = J * 2 + i"
          proof -
            have "\<sigma> (J * 2 + ?i1) = \<sigma> (\<sigma> (J * 2 + i))"
              using \<sigma>_at by simp
            also have "\<dots> = J * 2 + i"
              using \<sigma>_invol[OF idx_lt].
            finally show ?thesis.
          qed
          finally have "\<sigma> k = J * 2 + i".
          thus False using False by simp
        qed
        ultimately show ?thesis by simp
      qed
      also have "\<dots> = ?w $ k"
        using w_entry[OF k] by simp
      finally show "(U *\<^sub>v ?v) $ k = ?w $ k".
    qed
  qed

  show "oracle_unitary f N"
    unfolding oracle_unitary_def
    using U_carr U_unitary U_acts d_eq d_pos
    by (metis d0_def d_def) 
qed

(* Probability of outcome 0 when measuring U_f(x \<otimes> e\<^sub>0) with respect to |x \<otimes> e\<^sub>0\<rangle>:
   p\<^sub>0 = (#{J : f(J)=0} / 2^N)\<^sup>2 = (M/2^N)\<^sup>2 *)

definition count_zeros :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "count_zeros f N \<equiv> card {J. J < 2^N \<and> f J = 0}"


(* ============================================================================
   DAY 13 — 26 / Sep / 11
   Topic: Ensembles and Mixed States; Density Matrices
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Ensembles
   -------------------------------------------------------------------------- *)

definition ensemble :: "nat \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> bool" where
  "ensemble n E \<equiv>
     (\<forall>(p, \<psi>) \<in> set E. p \<ge> 0 \<and> quantum_state n \<psi>) \<and>
     (\<Sum>(p, _) \<leftarrow> E. p) = 1"

(* --------------------------------------------------------------------------
   Density Matrix
   -------------------------------------------------------------------------- *)

definition density_matrix :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "density_matrix n \<rho> \<equiv> \<rho> \<in> carrier_mat n n \<and> psd \<rho> \<and> Tr \<rho> = 1"

(* Density matrix associated to a pure state *)

definition pure_density :: "complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "pure_density \<psi> \<equiv>
     let n = dim_vec \<psi> in
     outer_sum n [\<psi>]"

lemma Tr_outer_sum_single:
  assumes dim: "dim_vec \<psi> = n"
  shows "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
proof -
  have "Tr (outer_sum n [\<psi>]) = (\<Sum>r<n. \<psi> $ r * cnj (\<psi> $ r))"
    using dim
    by (simp add: Tr_def outer_sum_def mat_of_cols_def dagger_def scalar_prod_def)
  also have "\<dots> = (\<Sum>r<n. cnj (\<psi> $ r) * \<psi> $ r)"
    by (simp add: mult.commute)
  also have "\<dots> = \<langle>\<psi> | \<psi>\<rangle>"
    using dim by (simp add: inner_prod_def lessThan_atLeast0)
  finally show ?thesis .
qed

lemma pure_density_is_density_matrix:
  assumes "quantum_state n \<psi>"
  shows "density_matrix n (pure_density \<psi>)"
proof -
  (* pure_density \<psi> = |\<psi>\<rangle>\<langle>\<psi>|.  Hermitian: outer_sum_hermitian.
     PSD: outer_sum_psd.  Tr = \<langle>\<psi>|\<psi>\<rangle> = \<parallel>\<psi>\<parallel>\<^sup>2 = 1. *)
  have dim: "dim_vec \<psi> = n" using assms by (auto simp: quantum_state_def)
  have norm: "\<parallel>\<psi>\<parallel> = 1" using assms by (auto simp: quantum_state_def)
  have psd: "psd (outer_sum n [\<psi>])"
    using dim by (intro outer_sum_psd) auto
  have tr: "Tr (outer_sum n [\<psi>]) = 1"
  proof -
    have "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
      by (rule Tr_outer_sum_single[OF dim])
    also have "\<dots> = 1"
      using norm cpx_vec_length_inner_prod[of \<psi>] by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding density_matrix_def pure_density_def Let_def
    using dim psd tr by fastforce
qed

(* Density matrix of an ensemble *)

definition ensemble_density :: "nat \<Rightarrow> (real \<times> complex Matrix.vec) list \<Rightarrow> complex Matrix.mat" where
  "ensemble_density n E \<equiv>
     foldr (\<lambda>(p,\<psi>) acc. complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + acc)
           E (0\<^sub>m n n)"

(* -- Auxiliary: PSD preservation helpers (not in the imported library) -- *)

lemma psd_zero_mat [simp]:
  "psd (0\<^sub>m n n)"
proof -
  have herm: "((0\<^sub>m n n)\<^sup>\<dagger>) = 0\<^sub>m n n"
    unfolding dagger_def by (rule eq_matI) simp_all
  have quad: "\<And>x::complex Matrix.vec.
        dim_vec x = n \<Longrightarrow> Re (\<langle>x | (0\<^sub>m n n) *\<^sub>v x\<rangle>) \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec" assume dx: "dim_vec x = n"
    have "(0\<^sub>m n n) *\<^sub>v x = 0\<^sub>v n"
      using dx by (intro eq_vecI) (simp_all add: scalar_prod_def)
    hence "\<langle>x | (0\<^sub>m n n) *\<^sub>v x\<rangle> = 0"
      using dx by (simp add: inner_prod_def)
    thus "Re (\<langle>x | (0\<^sub>m n n) *\<^sub>v x\<rangle>) \<ge> 0" by simp
  qed
  show ?thesis
    unfolding psd_def hermitian_def
    using herm quad by simp
qed

lemma psd_smult_nonneg:
  assumes c: "0 \<le> c"
      and A: "psd A" and Ac: "A \<in> carrier_mat n n"
  shows "psd (complex_of_real c \<cdot>\<^sub>m A)"
proof -
  have A_dagger: "(A\<^sup>\<dagger>) = A" using A by (simp add: psd_def hermitian_def)
  have A_quad: "\<And>x. dim_vec x = n \<Longrightarrow> Re (\<langle>x | A *\<^sub>v x\<rangle>) \<ge> 0"
    using A Ac by (simp add: psd_def)

  have herm_cA: "((complex_of_real c \<cdot>\<^sub>m A)\<^sup>\<dagger>) = complex_of_real c \<cdot>\<^sub>m A"
  proof -
    have "((complex_of_real c \<cdot>\<^sub>m A)\<^sup>\<dagger>) = (cnj (complex_of_real c)) \<cdot>\<^sub>m (A\<^sup>\<dagger>)"
      by (rule dagger_of_smult)
    also have "\<dots> = complex_of_real c \<cdot>\<^sub>m A"
      using A_dagger by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Action of the scaled matrix on a vector.\<close>
  have smult_mv:
    "\<And>x. x \<in> carrier_vec n \<Longrightarrow>
         (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)"
  proof -
    fix x :: "complex Matrix.vec" assume x_car: "x \<in> carrier_vec n"
    show "(complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)"
    proof (rule eq_vecI)
      show "dim_vec ((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x)
            = dim_vec (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x))"
        using Ac by simp
    next
      fix i assume "i < dim_vec (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x))"
      hence i: "i < n" using Ac by simp
      have r1: "Matrix.row A i \<in> carrier_vec n"
        using Ac i by auto
      have i_dr: "i < dim_row A" using i Ac by simp
      have "((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x) $ i
              = Matrix.row (complex_of_real c \<cdot>\<^sub>m A) i \<bullet> x"
        using i Ac by auto
      also have "\<dots> = (complex_of_real c \<cdot>\<^sub>v Matrix.row A i) \<bullet> x"
        using row_smult[OF i_dr] by simp
      also have "\<dots> = complex_of_real c * (Matrix.row A i \<bullet> x)"
        using r1 x_car by simp
      also have "\<dots> = complex_of_real c * (A *\<^sub>v x) $ i"
        using i Ac by auto
      also have "\<dots> = (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)) $ i"
        using i Ac by auto
      finally show "((complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x) $ i
                  = (complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)) $ i" .
    qed
  qed

  have quad: "\<And>x. dim_vec x = dim_row (complex_of_real c \<cdot>\<^sub>m A) \<Longrightarrow>
                Re (\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>) \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec"
    assume dx: "dim_vec x = dim_row (complex_of_real c \<cdot>\<^sub>m A)"
    hence dx': "dim_vec x = n" using Ac by simp
    have x_car: "x \<in> carrier_vec n" using dx' by auto

    have "\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>
        = \<langle>x | complex_of_real c \<cdot>\<^sub>v (A *\<^sub>v x)\<rangle>"
      using smult_mv[OF x_car] by simp
    also have "\<dots> = complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>"
      by (rule inner_prod_right_smult')
    finally have eq: "\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>
                    = complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>" .

    have Re_split: "Re (complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>)
                  = c * Re (\<langle>x | A *\<^sub>v x\<rangle>)"
      by simp
    have "0 \<le> c * Re (\<langle>x | A *\<^sub>v x\<rangle>)"
      using c A_quad[OF dx'] by (rule mult_nonneg_nonneg)
    thus "0 \<le> Re (\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>)"
      using eq Re_split by simp
  qed

  show ?thesis
    unfolding psd_def hermitian_def
    using herm_cA quad by blast
qed

lemma psd_add_psd:
  assumes A: "psd A" and B: "psd B"
      and Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n"
  shows "psd (A + B)"
proof -
  have A_dagger: "(A\<^sup>\<dagger>) = A" using A by (simp add: psd_def hermitian_def)
  have B_dagger: "(B\<^sup>\<dagger>) = B" using B by (simp add: psd_def hermitian_def)
  have A_quad: "\<And>x. dim_vec x = n \<Longrightarrow> Re (\<langle>x | A *\<^sub>v x\<rangle>) \<ge> 0"
    using A Ac by (simp add: psd_def)
  have B_quad: "\<And>x. dim_vec x = n \<Longrightarrow> Re (\<langle>x | B *\<^sub>v x\<rangle>) \<ge> 0"
    using B Bc by (simp add: psd_def)

  have herm_AB: "((A + B)\<^sup>\<dagger>) = A + B"
  proof (rule eq_matI)
    show "dim_row ((A + B)\<^sup>\<dagger>) = dim_row (A + B)"
      using Ac Bc by simp
    show "dim_col ((A + B)\<^sup>\<dagger>) = dim_col (A + B)"
      using Ac Bc by simp
  next
    fix i j
    assume "i < dim_row (A + B)" and "j < dim_col (A + B)"
    then have i: "i < n" and j: "j < n" using Ac Bc by auto
    have "((A + B)\<^sup>\<dagger>) $$ (i, j) = cnj ((A + B) $$ (j, i))"
      using i j Ac Bc by (simp add: dagger_def)
    also have "\<dots> = cnj (A $$ (j, i)) + cnj (B $$ (j, i))"
      using i j Ac Bc by simp
    also have "\<dots> = (A\<^sup>\<dagger>) $$ (i, j) + (B\<^sup>\<dagger>) $$ (i, j)"
      using i j Ac Bc by (simp add: dagger_def)
    also have "\<dots> = A $$ (i, j) + B $$ (i, j)"
      using A_dagger B_dagger by simp
    also have "\<dots> = (A + B) $$ (i, j)"
      using i j Ac Bc by simp
    finally show "((A + B)\<^sup>\<dagger>) $$ (i, j) = (A + B) $$ (i, j)" .
  qed

  have quad: "\<And>x. dim_vec x = dim_row (A + B) \<Longrightarrow>
                Re (\<langle>x | (A + B) *\<^sub>v x\<rangle>) \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec"
    assume dx: "dim_vec x = dim_row (A + B)"
    hence dx': "dim_vec x = n" using Ac Bc by simp
    have x_car: "x \<in> carrier_vec n" using dx' by auto
    have Ax_car: "A *\<^sub>v x \<in> carrier_vec n" using Ac x_car by auto
    have Bx_car: "B *\<^sub>v x \<in> carrier_vec n" using Bc x_car by auto
    have dim_eq: "dim_vec (A *\<^sub>v x) = dim_vec (B *\<^sub>v x)"
      using Ac Bc by simp

    have "\<langle>x | (A + B) *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x + B *\<^sub>v x\<rangle>"
      using add_mult_distrib_mat_vec[OF Ac Bc x_car] by simp
    also have "\<dots> = \<langle>x | A *\<^sub>v x\<rangle> + \<langle>x | B *\<^sub>v x\<rangle>"
      by (rule inner_prod_right_add'[OF dim_eq])
    finally have eq: "\<langle>x | (A + B) *\<^sub>v x\<rangle>
                    = \<langle>x | A *\<^sub>v x\<rangle> + \<langle>x | B *\<^sub>v x\<rangle>" .

    have "0 \<le> Re (\<langle>x | A *\<^sub>v x\<rangle>) + Re (\<langle>x | B *\<^sub>v x\<rangle>)"
      using A_quad[OF dx'] B_quad[OF dx'] by simp
    thus "0 \<le> Re (\<langle>x | (A + B) *\<^sub>v x\<rangle>)"
      using eq by simp
  qed

  show ?thesis
    unfolding psd_def hermitian_def
    using herm_AB quad by blast
qed

(* -- Auxiliary: structural lemmas about ensemble_density on a list -- *)

lemma ensemble_density_Nil [simp]:
  "ensemble_density n [] = 0\<^sub>m n n"
  by (simp add: ensemble_density_def)

lemma ensemble_density_Cons:
  "ensemble_density n ((p, \<psi>) # E) =
     complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + ensemble_density n E"
  by (simp add: ensemble_density_def)

lemma ensemble_density_carrier:
  assumes "\<forall>(p, \<psi>) \<in> set E. quantum_state n \<psi>"
  shows "ensemble_density n E \<in> carrier_mat n n"
  using assms
proof (induct E)
  case Nil
  show ?case by simp
next
  case (Cons a E)
  obtain p \<psi> where a_eq: "a = (p, \<psi>)" by (cases a) auto
  have q: "quantum_state n \<psi>" using Cons.prems a_eq by auto
  have os_car: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have sm_car: "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n"
    using os_car by auto
  have IH: "ensemble_density n E \<in> carrier_mat n n"
    using Cons.hyps Cons.prems by auto
  show ?case
    unfolding a_eq ensemble_density_Cons
    using IH by (rule add_carrier_mat)
qed

lemma ensemble_density_psd_aux:
  assumes "\<forall>(p, \<psi>) \<in> set E. p \<ge> 0 \<and> quantum_state n \<psi>"
  shows "psd (ensemble_density n E)"
  using assms
proof (induct E)
  case Nil
  show ?case by simp
next
  case (Cons a E)
  obtain p \<psi> where a_eq: "a = (p, \<psi>)" by (cases a) auto
  have p_nn: "0 \<le> p" using Cons.prems a_eq by auto
  have q: "quantum_state n \<psi>" using Cons.prems a_eq by auto
  have d\<psi>: "dim_vec \<psi> = n" using q by (simp add: quantum_state_def)

  have os_car: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have os_psd: "psd (outer_sum n [\<psi>])"
    using d\<psi> by (intro outer_sum_psd) auto
  have sm_psd: "psd (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>])"
    using p_nn os_psd os_car by (rule psd_smult_nonneg)
  have sm_car: "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n"
    using os_car by auto

  have IH_psd: "psd (ensemble_density n E)"
    using Cons.hyps Cons.prems by auto
  have IH_car: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier) (use Cons.prems in auto)

  show ?case
    unfolding a_eq ensemble_density_Cons
    using sm_psd IH_psd sm_car IH_car by (rule psd_add_psd)
qed

lemma Tr_zero_mat' [simp]:
  "Tr (0\<^sub>m n n) = 0"
  by (simp add: Tr_def zero_mat_def)

lemma ensemble_density_Tr:
  assumes "\<forall>(p, \<psi>) \<in> set E. quantum_state n \<psi>"
  shows "Tr (ensemble_density n E) = complex_of_real (\<Sum>(p, _) \<leftarrow> E. p)"
  using assms
proof (induct E)
  case Nil
  show ?case by simp
next
  case (Cons a E)
  obtain p \<psi> where a_eq: "a = (p, \<psi>)" by (cases a) auto
  have q: "quantum_state n \<psi>" using Cons.prems a_eq by auto
  have d\<psi>: "dim_vec \<psi> = n" using q by (simp add: quantum_state_def)

  have os_car: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have sm_car: "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n"
    using os_car by auto
  have IH_car: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier) (use Cons.prems in auto)

  have Tr_os: "Tr (outer_sum n [\<psi>]) = 1"
  proof -
    have "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
      by (rule Tr_outer_sum_single[OF d\<psi>])
    also have "\<dots> = 1"
      using q by (metis cpx_vec_length_inner_prod of_real_1 one_power2 quantum_state_norm1)
    finally show ?thesis .
  qed

  have "Tr (ensemble_density n ((p, \<psi>) # E))
        = Tr (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + ensemble_density n E)"
    by (simp add: ensemble_density_Cons)
  also have "\<dots> = Tr (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>]) + Tr (ensemble_density n E)"
  proof (rule Tr_add)
    show "dim_row (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>]) = dim_row (ensemble_density n E)"
      using sm_car IH_car by auto
    show "dim_col (complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>]) = dim_col (ensemble_density n E)"
      using sm_car IH_car by auto
  qed
  also have "\<dots> = complex_of_real p * Tr (outer_sum n [\<psi>]) + Tr (ensemble_density n E)"
    by (simp add: Tr_smult)
  also have "\<dots> = complex_of_real p + Tr (ensemble_density n E)"
    using Tr_os by simp
  also have "\<dots> = complex_of_real p + complex_of_real (\<Sum>(p, _) \<leftarrow> E. p)"
    using Cons.hyps Cons.prems by auto
  also have "\<dots> = complex_of_real (p + (\<Sum>(p, _) \<leftarrow> E. p))"
    by simp
  also have "\<dots> = complex_of_real (\<Sum>(p, _) \<leftarrow> ((p, \<psi>) # E). p)"
    by simp
  finally show ?case unfolding a_eq .
qed

(* The ensemble density is a density matrix *)

theorem ensemble_density_is_dm:
  assumes E: "ensemble n E"
  shows "density_matrix n (ensemble_density n E)"
proof -
  from E have states_q: "\<forall>(p, \<psi>) \<in> set E. quantum_state n \<psi>"
    and states_pq: "\<forall>(p, \<psi>) \<in> set E. p \<ge> 0 \<and> quantum_state n \<psi>"
    and probs: "(\<Sum>(p, _) \<leftarrow> E. p) = 1"
    unfolding ensemble_def by auto

  have carr: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier[OF states_q])
  have psd_ed: "psd (ensemble_density n E)"
    by (rule ensemble_density_psd_aux[OF states_pq])
  have tr_ed: "Tr (ensemble_density n E) = 1"
    using ensemble_density_Tr[OF states_q] probs by simp

  show ?thesis
    unfolding density_matrix_def
    using carr psd_ed tr_ed by blast
qed

(* --------------------------------------------------------------------------
   Von Neumann's approach: probabilities via Tr(M\<dagger>M \<rho>)
   -------------------------------------------------------------------------- *)

(* For a pure state \<psi>: \<Parallel>M\<psi>\<Parallel>\<^sup>2 = Tr(M\<dagger>M |\<psi>\<rangle>\<langle>\<psi>|) *)

lemma pure_state_prob_trace:
  fixes M :: "complex Matrix.mat" and \<psi> :: "complex Matrix.vec"
  assumes st: "quantum_state n \<psi>"
      and Msq: "M \<in> carrier_mat n n"
  shows "meas_prob M \<psi> = Re (Tr ((M\<^sup>\<dagger>) * M * outer_sum n [\<psi>]))"
proof -
  let ?A = "(M\<^sup>\<dagger>) * M"
  have Ac: "?A \<in> carrier_mat n n" using Msq by auto
  have dpsi: "dim_vec \<psi> = n" using st by (simp add: quantum_state_def)
  have psi_car: "\<psi> \<in> carrier_vec n" using dpsi by auto
  have Mpsi_car: "M *\<^sub>v \<psi> \<in> carrier_vec n" using Msq psi_car by auto

  \<comment> \<open>Entry formula for \<open>outer_sum n [\<psi>]\<close>.\<close>
  have OS_entry: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
                 outer_sum n [\<psi>] $$ (i, j) = \<psi> $ i * cnj (\<psi> $ j)"
  proof -
    fix i j :: nat assume i: "i < n" and j: "j < n"
    let ?V = "mat_of_cols n [\<psi>]"
    have dVr: "dim_row ?V = n" by simp
    have dVc: "dim_col ?V = 1" by simp
    have Vc: "?V \<in> carrier_mat n 1" by auto
    have dVdr: "dim_row (?V\<^sup>\<dagger>) = 1" by simp
    have dVdc: "dim_col (?V\<^sup>\<dagger>) = n" by simp
    have Vdc: "(?V\<^sup>\<dagger>) \<in> carrier_mat 1 n"
      using dVdr dVdc by auto

    have Vi0: "?V $$ (i, 0) = \<psi> $ i"
      using i by (simp add: mat_of_cols_index)
    have Vj0: "?V $$ (j, 0) = \<psi> $ j"
      using j by (simp add: mat_of_cols_index)
    have Vd_0j: "(?V\<^sup>\<dagger>) $$ (0, j) = cnj (\<psi> $ j)"
    proof -
      have "(?V\<^sup>\<dagger>) $$ (0, j) = cnj (?V $$ (j, 0))"
        using j dVr dVc by (simp add: dagger_def)
      with Vj0 show ?thesis by simp
    qed

    have "outer_sum n [\<psi>] $$ (i, j) = (?V * (?V\<^sup>\<dagger>)) $$ (i, j)"
      by (simp add: outer_sum_def)
    also have "\<dots> = Matrix.row ?V i \<bullet> Matrix.col (?V\<^sup>\<dagger>) j"
    proof -
      have "i < dim_row ?V" using i dVr by simp
      moreover have "j < dim_col (?V\<^sup>\<dagger>)" using j dVdc by simp
      ultimately show ?thesis by (simp add: times_mat_def)
    qed
    also have "\<dots> = (\<Sum>k = 0..<1. Matrix.row ?V i $ k * Matrix.col (?V\<^sup>\<dagger>) j $ k)"
      using dVdr by (simp add: scalar_prod_def)
    also have "\<dots> = Matrix.row ?V i $ 0 * Matrix.col (?V\<^sup>\<dagger>) j $ 0" by simp
    also have "Matrix.row ?V i $ 0 = ?V $$ (i, 0)"
      using i dVc by auto
    also have "Matrix.col (?V\<^sup>\<dagger>) j $ 0 = (?V\<^sup>\<dagger>) $$ (0, j)"
    proof -
      have h1: "0 < dim_row (?V\<^sup>\<dagger>)" using dVdr by simp
      have h2: "j < dim_col (?V\<^sup>\<dagger>)" using j dVdc by simp
      show ?thesis by (rule index_col[OF h1 h2])
    qed
    finally show "outer_sum n [\<psi>] $$ (i, j) = \<psi> $ i * cnj (\<psi> $ j)"
      using Vi0 Vd_0j by simp
  qed

  \<comment> \<open>Cyclic identity: \<open>Tr (A \<cdot> |\<psi>\<rangle>\<langle>\<psi>|) = \<langle>\<psi> | A \<psi>\<rangle>\<close>.\<close>
  have Tr_id: "Tr (?A * outer_sum n [\<psi>]) = \<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>"
  proof -
    have OSc: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
    have prodc: "?A * outer_sum n [\<psi>] \<in> carrier_mat n n" using Ac OSc by auto
    have "Tr (?A * outer_sum n [\<psi>])
           = (\<Sum>i<n. (?A * outer_sum n [\<psi>]) $$ (i, i))"
    proof -
      have dr: "dim_row (?A * outer_sum n [\<psi>]) = n" using prodc by auto
      have dc: "dim_col (?A * outer_sum n [\<psi>]) = n" using prodc by auto
      show ?thesis using dr dc by (simp add: Tr_def)
    qed
    also have "\<dots> = (\<Sum>i<n. \<Sum>k = 0..<n. ?A $$ (i, k) * outer_sum n [\<psi>] $$ (k, i))"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {..<n}"
      hence i: "i < n" by simp
      have iA: "i < dim_row ?A" using i Ac by auto
      have iOS: "i < dim_col (outer_sum n [\<psi>])" using i OSc by auto
      have dOS: "dim_row (outer_sum n [\<psi>]) = n" using OSc by auto
      have "(?A * outer_sum n [\<psi>]) $$ (i, i)
            = Matrix.row ?A i \<bullet> Matrix.col (outer_sum n [\<psi>]) i"
        using iA iOS by (simp add: times_mat_def)
      also have "\<dots> = (\<Sum>k = 0..<n.
           Matrix.row ?A i $ k * Matrix.col (outer_sum n [\<psi>]) i $ k)"
        using dOS by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>k = 0..<n. ?A $$ (i, k) * outer_sum n [\<psi>] $$ (k, i))"
      proof (intro sum.cong refl)
        fix k assume "k \<in> {0..<n}"
        hence k: "k < n" by simp
        have "Matrix.row ?A i $ k = ?A $$ (i, k)"
          using i k Ac by auto
        moreover have "Matrix.col (outer_sum n [\<psi>]) i $ k
                     = outer_sum n [\<psi>] $$ (k, i)"
          using k i OSc by auto
        ultimately show
          "Matrix.row ?A i $ k * Matrix.col (outer_sum n [\<psi>]) i $ k
             = ?A $$ (i, k) * outer_sum n [\<psi>] $$ (k, i)"
          by simp
      qed
      finally show "(?A * outer_sum n [\<psi>]) $$ (i, i)
                  = (\<Sum>k = 0..<n. ?A $$ (i, k) * outer_sum n [\<psi>] $$ (k, i))" .
    qed
    also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i)))"
    proof -
      have entry:
        "\<And>i j. i \<in> {..<n} \<Longrightarrow> j \<in> {..<n} \<Longrightarrow>
            ?A $$ (i, j) * outer_sum n [\<psi>] $$ (j, i)
             = ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i))"
      proof -
        fix i j
        assume "i \<in> {..<n}"
        assume "j \<in> {..<n}"
        hence i: "i < n" and j: "j < n"
          using \<open>i \<in> {..<n}\<close> by auto 
        from OS_entry[OF j i]
        show "?A $$ (i, j) * outer_sum n [\<psi>] $$ (j, i)
             = ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i))"
          by simp
      qed
      have "(\<Sum>i<n. \<Sum>j = 0..<n. ?A $$ (i, j) * outer_sum n [\<psi>] $$ (j, i))
           = (\<Sum>i<n. \<Sum>j<n. ?A $$ (i, j) * outer_sum n [\<psi>] $$ (j, i))"
        by (simp add: lessThan_atLeast0)
      also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i)))"
        using entry by (intro sum.cong refl) simp
      finally show ?thesis.
    qed
    also have "\<dots> = (\<Sum>i<n. cnj (\<psi> $ i) * (\<Sum>k = 0..<n. ?A $$ (i, k) * \<psi> $ k))"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {..<n}"
      have "(\<Sum>j<n. ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i)))
           = (\<Sum>j<n. cnj (\<psi> $ i) * (?A $$ (i, j) * \<psi> $ j))"
        by (intro sum.cong refl) (simp add: ac_simps)
      also have "\<dots> = cnj (\<psi> $ i) * (\<Sum>j<n. ?A $$ (i, j) * \<psi> $ j)"
        by (simp add: sum_distrib_left)
      also have "\<dots> = cnj (\<psi> $ i) * (\<Sum>k = 0..<n. ?A $$ (i, k) * \<psi> $ k)"
        by (simp add: lessThan_atLeast0)
      finally show "(\<Sum>j<n. ?A $$ (i, j) * (\<psi> $ j * cnj (\<psi> $ i)))
                  = cnj (\<psi> $ i) * (\<Sum>k = 0..<n. ?A $$ (i, k) * \<psi> $ k)" .
    qed
    also have "\<dots> = (\<Sum>i<n. cnj (\<psi> $ i) * (?A *\<^sub>v \<psi>) $ i)"
      using Ac dpsi
      by (intro sum.cong refl, simp add: mult_mat_vec_index psi_car)
    also have "\<dots> = \<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>"
      using Msq atLeast0LessThan inner_prod_def by auto 
    finally show ?thesis.
  qed

  \<comment> \<open>Bridge \<open>\<parallel>M\<psi>\<parallel>\<^sup>2 = Re \<langle>\<psi> | M\<^sup>\<dagger> M \<psi>\<rangle>\<close> via adjoint swap.\<close>
  have inner_eq: "\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle> = cnj (\<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>)"
  proof -
    have "\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle> = \<langle>(M\<^sup>\<dagger>) *\<^sub>v (M *\<^sub>v \<psi>) | \<psi>\<rangle>"
    proof -
      have dim_Mpsi: "dim_vec (M *\<^sub>v \<psi>) = n" using Mpsi_car carrier_vecD by blast 
      show ?thesis by (rule inner_prod_adjoint_swap[OF Msq dim_Mpsi dpsi])
    qed
    also have "(M\<^sup>\<dagger>) *\<^sub>v (M *\<^sub>v \<psi>) = ?A *\<^sub>v \<psi>"
      using Msq psi_car
      by (metis assoc_mult_mat_vec carrier_matD(1) carrier_matI dim_col_of_dagger)
    finally have "\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle> = \<langle>?A *\<^sub>v \<psi> | \<psi>\<rangle>".
    also have "\<dots> = cnj (\<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>)"
      using Msq dpsi inner_prod_cnj by force          
    finally show ?thesis.
  qed

  have norm_sq: "\<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2 = Re (\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>)"
    by (metis Re_complex_of_real cpx_vec_length_inner_prod)
  have "meas_prob M \<psi> = \<parallel>M *\<^sub>v \<psi>\<parallel>\<^sup>2" by (simp add: meas_prob_def)
  also have "\<dots> = Re (\<langle>M *\<^sub>v \<psi> | M *\<^sub>v \<psi>\<rangle>)" by (rule norm_sq)
  also have "\<dots> = Re (cnj (\<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>))" using inner_eq by simp
  also have "\<dots> = Re (\<langle>\<psi> | ?A *\<^sub>v \<psi>\<rangle>)" by simp
  also have "\<dots> = Re (Tr (?A * outer_sum n [\<psi>]))" using Tr_id by simp
  finally show ?thesis.
qed

(* For an ensemble with density \<rho>: p_\<alpha>(\<rho>) = Tr(M_\<alpha>\<dagger> M_\<alpha> \<rho>) *)

(* Helper: the trace of a PSD matrix has non-negative real part (in fact
   it is a non-negative real number). *)

lemma Tr_psd_Re_nonneg:
  assumes P: "psd P" and Pc: "P \<in> carrier_mat n n"
  shows "0 \<le> Re (Tr P)"
proof -
  have dr: "dim_row P = n" and dc: "dim_col P = n" using Pc by auto

  \<comment> \<open>Diagonal entries are inner products with unit vectors.\<close>
  have diag_entry:
    "\<And>i. i < n \<Longrightarrow> P $$ (i, i) = \<langle>unit_vec n i | P *\<^sub>v unit_vec n i\<rangle>"
  proof -
    fix i assume i: "i < n"
    let ?e = "unit_vec n i"
    have de: "dim_vec ?e = n" by simp
    have Pe_idx: "\<And>k. k < n \<Longrightarrow> (P *\<^sub>v ?e) $ k = P $$ (k, i)"
    proof -
      fix k assume k: "k < n"
      have "(P *\<^sub>v ?e) $ k = Matrix.row P k \<bullet> ?e"
        using k Pc by auto
      also have "\<dots> = (\<Sum>m = 0..<n. Matrix.row P k $ m * ?e $ m)"
        using k Pc by (simp add: scalar_prod_def)
      also have "\<dots> = (\<Sum>m = 0..<n. if m = i then Matrix.row P k $ m else 0)"
        using i by (intro sum.cong refl) simp
      also have "\<dots> = Matrix.row P k $ i"
        using i by simp
      also have "\<dots> = P $$ (k, i)"
        using k i Pc by auto
      finally show "(P *\<^sub>v ?e) $ k = P $$ (k, i)".
    qed
    have "\<langle>?e | P *\<^sub>v ?e\<rangle> = (\<Sum>k = 0..<n. cnj (?e $ k) * (P *\<^sub>v ?e) $ k)"
      using Pc by (simp add: inner_prod_def)
    also have "\<dots> = (\<Sum>k = 0..<n. if k = i then (P *\<^sub>v ?e) $ k else 0)"
      using i by (intro sum.cong refl) simp
    also have "\<dots> = (P *\<^sub>v ?e) $ i"
      using i by simp
    also have "\<dots> = P $$ (i, i)"
      using Pe_idx[OF i] by simp
    finally show "P $$ (i, i) = \<langle>?e | P *\<^sub>v ?e\<rangle>" by simp
  qed

  \<comment> \<open>Each diagonal entry has non-negative real part, so the trace does.\<close>
  have Re_diag_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> Re (P $$ (i, i))"
  proof -
    fix i assume i: "i < n"
    have "Re (P $$ (i, i)) = Re (\<langle>unit_vec n i | P *\<^sub>v unit_vec n i\<rangle>)"
      using diag_entry[OF i] by simp
    moreover have "0 \<le> Re (\<langle>unit_vec n i | P *\<^sub>v unit_vec n i\<rangle>)"
      using P Pc by (simp add: psd_def)
    ultimately show "0 \<le> Re (P $$ (i, i))" by simp
  qed

  have "Re (Tr P) = Re (\<Sum>r<n. if r < n then P $$ (r, r) else 0)"
    using dr dc by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>r<n. Re (P $$ (r, r)))" by simp
  finally have "Re (Tr P) = (\<Sum>r<n. Re (P $$ (r, r)))".
  moreover have "0 \<le> (\<Sum>r<n. Re (P $$ (r, r)))"
    using Re_diag_nn by (intro sum_nonneg) auto
  ultimately show ?thesis by simp
qed

lemma ensemble_prob_trace:
  fixes Ms :: "complex Matrix.mat list"
  assumes ms: "measurement_system n Ms"
      and dm: "density_matrix n \<rho>"
      and Min: "M \<in> set Ms"
  shows "Re (Tr ((M\<^sup>\<dagger>) * M * \<rho>)) \<ge> 0"
proof -
  have M_carr: "M \<in> carrier_mat n n"
    using ms Min by (auto simp: measurement_system_def)
  have rho_carr: "\<rho> \<in> carrier_mat n n" using dm by (auto simp: density_matrix_def)
  have rho_psd: "psd \<rho>" using dm by (auto simp: density_matrix_def)

  \<comment> \<open>Take a PSD square root of @{term \<rho>}.\<close>
  obtain Q where Qc: "Q \<in> carrier_mat n n" and Qpsd: "psd Q" and QQ: "Q * Q = \<rho>"
    using psd_sqrt_exists[OF rho_carr rho_psd] by blast
  have Qdag: "(Q\<^sup>\<dagger>) = Q" using Qpsd by (simp add: psd_def hermitian_def)
  have Md_c: "(M\<^sup>\<dagger>) \<in> carrier_mat n n" using M_carr by auto
  have MdM_c: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n" using Md_c M_carr by auto
  have MQ_c: "M * Q \<in> carrier_mat n n" using M_carr Qc by auto
  have MQd_c: "((M * Q)\<^sup>\<dagger>) \<in> carrier_mat n n"
  proof -
    have dr: "dim_row ((M * Q)\<^sup>\<dagger>) = dim_col (M * Q)" by simp
    have dc: "dim_col ((M * Q)\<^sup>\<dagger>) = dim_row (M * Q)" by simp
    have "dim_col (M * Q) = n" using MQ_c by auto
    moreover have "dim_row (M * Q) = n" using MQ_c by auto
    ultimately show ?thesis using dr dc by auto
  qed

  \<comment> \<open>Key identity: @{term "(M*Q)\<^sup>\<dagger> * (M*Q) = Q * (M\<^sup>\<dagger>) * M * Q"}.\<close>
  have expand: "((M * Q)\<^sup>\<dagger>) * (M * Q) = Q * ((M\<^sup>\<dagger>) * M) * Q"
  proof -
    have "((M * Q)\<^sup>\<dagger>) * (M * Q) = ((Q\<^sup>\<dagger>) * (M\<^sup>\<dagger>)) * (M * Q)"
      using M_carr Qc by (simp add: dagger_of_prod)
    also have "\<dots> = (Q * (M\<^sup>\<dagger>)) * (M * Q)" using Qdag by simp
    also have "\<dots> = Q * ((M\<^sup>\<dagger>) * (M * Q))"
      using assoc_mult_mat[OF Qc Md_c MQ_c] by simp
    also have "\<dots> = Q * (((M\<^sup>\<dagger>) * M) * Q)"
      using assoc_mult_mat[OF Md_c M_carr Qc, symmetric] by simp
    also have "\<dots> = (Q * ((M\<^sup>\<dagger>) * M)) * Q"
      using assoc_mult_mat[OF Qc MdM_c Qc, symmetric] by simp
    finally show ?thesis by simp
  qed

  \<comment> \<open>Key identity 2: @{term "Tr (A*Q*Q) = Tr (Q * A * Q)"} for \<open>A = M\<^sup>\<dagger>*M\<close>.\<close>
  have Tr_eq: "Tr ((M\<^sup>\<dagger>) * M * \<rho>) = Tr (((M * Q)\<^sup>\<dagger>) * (M * Q))"
  proof -
    have "Tr ((M\<^sup>\<dagger>) * M * \<rho>) = Tr ((M\<^sup>\<dagger>) * M * (Q * Q))"
      using QQ by simp
    also have "\<dots> = Tr (((M\<^sup>\<dagger>) * M * Q) * Q)"
      using MdM_c Qc by simp
    also have "\<dots> = Tr (Q * ((M\<^sup>\<dagger>) * M * Q))"
    proof (rule Tr_cyclic)
      show "dim_col ((M\<^sup>\<dagger>) * M * Q) = dim_row Q" using MdM_c Qc by auto
      show "dim_row ((M\<^sup>\<dagger>) * M * Q) = dim_col Q" using MdM_c Qc by auto
    qed
    also have "\<dots> = Tr (Q * ((M\<^sup>\<dagger>) * M) * Q)"
      using Qc MdM_c by simp
    also have "\<dots> = Tr (((M * Q)\<^sup>\<dagger>) * (M * Q))"
      using expand by simp
    finally show ?thesis.
  qed

  \<comment> \<open>\<open>(MQ)\<^sup>\<dagger>(MQ)\<close> is PSD, so its trace has non-negative real part.\<close>
  have MQd_MQ_psd: "psd (((M * Q)\<^sup>\<dagger>) * (M * Q))"
    using psd_MdagM[OF MQ_c] by simp
  have MQd_MQ_c: "((M * Q)\<^sup>\<dagger>) * (M * Q) \<in> carrier_mat n n"
    using MQ_c MQd_c by auto

  have "0 \<le> Re (Tr (((M * Q)\<^sup>\<dagger>) * (M * Q)))"
    using Tr_psd_Re_nonneg[OF MQd_MQ_psd MQd_MQ_c].
  thus ?thesis using Tr_eq by simp
qed


(* ============================================================================
   DAY 14 — 28 / Sep / 11
   Topic: Characterisation of Density Matrices; Pure States;
          Composite Ensembles; Partial Trace (motivation)
   ============================================================================ *)

(* --------------------------------------------------------------------------
   \<section>15.1 (Continuation).  Every density matrix is the density of some
   ensemble (the spectral ensemble).  Combined with the Day-13 theorem
   \<open>ensemble_density_is_dm\<close>, this characterises density matrices as exactly
   those \<rho> with \<rho> \<ge> 0 and \<open>Tr \<rho> = 1\<close>.
   -------------------------------------------------------------------------- *)

(* Unfolding the definition: for square \<rho>, being a density matrix is just
   \<open>\<rho> \<ge> 0 \<and> Tr \<rho> = 1\<close>.  This matches Paulsen's Definition on p.\ 43. *)

theorem density_matrix_characterisation:
  fixes \<rho> :: "complex Matrix.mat"
  assumes sq: "\<rho> \<in> carrier_mat n n"
  shows "density_matrix n \<rho> \<longleftrightarrow> psd \<rho> \<and> Tr \<rho> = 1"
  using sq by (simp add: density_matrix_def)

(* --- Helpers for the spectral-ensemble construction -------------------- *)

lemma ensemble_density_carrier_dim:
  shows "ensemble_density n E \<in> carrier_mat n n"
proof (induct E)
  case Nil show ?case by (simp add: ensemble_density_def)
next
  case (Cons a E)
  obtain p \<psi> where a: "a = (p, \<psi>)" by (cases a) auto
  have "ensemble_density n (a # E)
          = complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] + ensemble_density n E"
    by (simp add: a ensemble_density_Cons)
  moreover have "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>] \<in> carrier_mat n n"
    by auto
  ultimately show ?case using Cons.hyps by auto
qed

lemma outer_sum_singleton_index:
  assumes r: "r < n" and c: "c < n"
  shows "outer_sum n [\<psi>] $$ (r, c) = \<psi> $ r * cnj (\<psi> $ c)"
proof -
  let ?M = "mat_of_cols n [\<psi>]"
  let ?Md = "(?M)\<^sup>\<dagger>"
  have M_car: "?M \<in> carrier_mat n 1"
    by (simp add: mat_of_cols_def)
  have Md_car: "?Md \<in> carrier_mat 1 n"
    using M_car by auto
  have dr: "r < dim_row ?M" using M_car r by auto
  have dc: "c < dim_col ?Md" using Md_car c by auto
  have "outer_sum n [\<psi>] $$ (r, c) = (?M * ?Md) $$ (r, c)"
    by (simp add: outer_sum_def)
  also have "\<dots> = Matrix.row ?M r \<bullet> Matrix.col ?Md c"
    using dc dr index_mult_mat(1) by blast
  also have "\<dots> = (\<Sum>j = 0..<1. ?M $$ (r, j) * ?Md $$ (j, c))"
    using M_car Md_car r c
    by (simp add: scalar_prod_def Matrix.row_def Matrix.col_def)
  also have "\<dots> = ?M $$ (r, 0) * ?Md $$ (0, c)"
    by simp
  also have "\<dots> = \<psi> $ r * cnj (\<psi> $ c)"
    using r c by (simp add: mat_of_cols_def dagger_def)
  finally show ?thesis.
qed

lemma ensemble_density_index:
  assumes r: "r < n" and c: "c < n"
  shows "ensemble_density n E $$ (r, c) =
         (\<Sum>(p, \<psi>) \<leftarrow> E. complex_of_real p * \<psi> $ r * cnj (\<psi> $ c))"
proof (induct E)
  case Nil
  have "ensemble_density n [] $$ (r, c) = (0\<^sub>m n n) $$ (r, c)"
    by (simp add: ensemble_density_def)
  also have "\<dots> = 0" using r c by simp
  finally show ?case by simp
next
  case (Cons a E)
  obtain p \<psi> where a: "a = (p, \<psi>)" by (cases a) auto
  let ?S = "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>]"
  have S_car: "?S \<in> carrier_mat n n" by auto
  have ED_car: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier_dim)
  have sum_car: "?S + ensemble_density n E \<in> carrier_mat n n"
    using S_car ED_car by auto
  have "ensemble_density n (a # E) $$ (r, c)
          = (?S + ensemble_density n E) $$ (r, c)"
    by (simp add: a ensemble_density_Cons)
  also have "\<dots> = ?S $$ (r, c) + ensemble_density n E $$ (r, c)"
    using S_car ED_car r c by simp
  also have "?S $$ (r, c) = complex_of_real p * outer_sum n [\<psi>] $$ (r, c)"
    using r c by simp
  also have "outer_sum n [\<psi>] $$ (r, c) = \<psi> $ r * cnj (\<psi> $ c)"
    using r c by (rule outer_sum_singleton_index)
  also have "ensemble_density n E $$ (r, c) =
               (\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<phi> $ r * cnj (\<phi> $ c))"
    by (rule Cons.hyps)
  finally show ?case
    by (simp add: a mult.assoc)
qed

(* --- Spectral ensemble: main theorem ----------------------------------- *)

theorem spectral_ensemble_exists:
  fixes \<rho> :: "complex Matrix.mat"
  assumes dm: "density_matrix n \<rho>"
  shows "\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>"
proof -
  have rho_car: "\<rho> \<in> carrier_mat n n"
   and rho_psd: "psd \<rho>"
   and rho_Tr: "Tr \<rho> = 1"
    using dm unfolding density_matrix_def by auto
  have rho_herm: "hermitian \<rho>" using rho_psd by (rule psd_hermitian)

  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
       and Dlen: "length D = n"
       and spec: "U\<^sup>\<dagger> * \<rho> * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF rho_car rho_herm] by blast
  have Udag_car: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have rho_times_U: "\<rho> * U = U * diag_mat_of_real D"
    using hermitian_spectral_decomp_right[OF Uc rho_car UU spec].

  \<comment> \<open>Columns of U are unit vectors of length n.\<close>
  have col_dim: "\<And>i. i < n \<Longrightarrow> dim_vec (Matrix.col U i) = n" using Uc by simp
  have col_norm: "\<And>i. i < n \<Longrightarrow> \<parallel>Matrix.col U i\<parallel> = 1"
    using UU Uc unitary_unit_col by (metis carrier_matD(2))
  have col_qs: "\<And>i. i < n \<Longrightarrow> quantum_state n (Matrix.col U i)"
    using col_dim col_norm by (auto simp: quantum_state_def)
  have col_ne: "\<And>i. i < n \<Longrightarrow> Matrix.col U i \<noteq> 0\<^sub>v n"
  proof -
    fix i assume i: "i < n"
    show "Matrix.col U i \<noteq> 0\<^sub>v n"
    proof
      assume z: "Matrix.col U i = 0\<^sub>v n"
      hence "\<parallel>Matrix.col U i\<parallel> = 0"
        using col_dim[OF i] cpx_vec_length_zero_iff by metis
      with col_norm[OF i] show False by simp
    qed
  qed

  \<comment> \<open>Each column of U is an eigenvector of \<rho> with eigenvalue \<open>D ! i\<close>.\<close>
  have eig: "\<And>i. i < n \<Longrightarrow>
               \<rho> *\<^sub>v Matrix.col U i = complex_of_real (D!i) \<cdot>\<^sub>v Matrix.col U i"
  proof -
    fix i assume i: "i < n"
    let ?u = "Matrix.col U i"
    show "\<rho> *\<^sub>v ?u = complex_of_real (D!i) \<cdot>\<^sub>v ?u"
    proof (rule eq_vecI)
      show "dim_vec (\<rho> *\<^sub>v ?u) = dim_vec (complex_of_real (D!i) \<cdot>\<^sub>v ?u)"
        using rho_car col_dim[OF i] by simp
    next
      fix k assume k: "k < dim_vec (complex_of_real (D!i) \<cdot>\<^sub>v ?u)"
      hence klt: "k < n" using col_dim[OF i] by simp
      have "(\<rho> *\<^sub>v ?u) $ k = (\<rho> * U) $$ (k, i)"
        using rho_car Uc i klt
        by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using rho_times_U by simp
      also have "\<dots> = (\<Sum>j = 0..<n.
                          U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
        using Uc Dlen klt i by (simp add: scalar_prod_def lessThan_atLeast0)
      also have "\<dots> = (\<Sum>j = 0..<n.
                          if j = i then U $$ (k, j) * complex_of_real (D!i) else 0)"
        using Dlen i by (intro sum.cong refl) auto
      also have "\<dots> = U $$ (k, i) * complex_of_real (D!i)"
        using i by simp
      also have "\<dots> = complex_of_real (D!i) * U $$ (k, i)"
        by (simp add: mult.commute)
      also have "\<dots> = (complex_of_real (D!i) \<cdot>\<^sub>v ?u) $ k"
        using klt Uc i by simp
      finally show "(\<rho> *\<^sub>v ?u) $ k = (complex_of_real (D!i) \<cdot>\<^sub>v ?u) $ k".
    qed
  qed

  \<comment> \<open>Eigenvalues are non-negative (\<rho> is PSD).\<close>
  have eig_nn:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> \<rho> *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    using psd_iff_nonneg_eigenvalues[OF rho_car] rho_psd by blast
  have D_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  proof -
    fix i assume i: "i < n"
    have "0 \<le> Re (complex_of_real (D ! i))"
      using eig_nn eig[OF i] col_ne[OF i] col_dim[OF i] by blast
    thus "0 \<le> D ! i" by simp
  qed

  \<comment> \<open>Eigenvalues sum to \<open>Tr \<rho> = 1\<close>.\<close>
  have Tr_diag: "Tr (diag_mat_of_real D) = (\<Sum>i<n. complex_of_real (D!i))"
    using Dlen by (simp add: Tr_def)
  have D_sum_complex: "(\<Sum>i<n. complex_of_real (D!i)) = 1"
  proof -
    have "(\<Sum>i<n. complex_of_real (D!i)) = Tr (diag_mat_of_real D)"
      using Tr_diag by simp
    also have "\<dots> = Tr (U\<^sup>\<dagger> * \<rho> * U)" using spec by simp
    also have "\<dots> = Tr \<rho>"
      using Tr_unitary_conjugation[OF UU] rho_car Uc by simp
    also have "\<dots> = 1" using rho_Tr by simp
    finally show ?thesis.
  qed
  have D_sum: "(\<Sum>i<n. D!i) = 1"
  proof -
    have "complex_of_real (\<Sum>i<n. D!i) = (\<Sum>i<n. complex_of_real (D!i))"
      by simp
    also have "\<dots> = 1" by (rule D_sum_complex)
    finally show ?thesis
      using of_real_eq_1_iff by blast
  qed

  \<comment> \<open>Build the ensemble \<open>E = map (\<lambda>i. (D!i, col U i)) [0..<n]\<close>.\<close>
  define E where "E = map (\<lambda>i. (D!i, Matrix.col U i)) [0..<n]"
  have E_set: "set E = (\<lambda>i. (D!i, Matrix.col U i)) ` {..<n}"
    by (simp add: E_def atLeast0LessThan)
  have ens_ok: "\<forall>(p, \<psi>) \<in> set E. 0 \<le> p \<and> quantum_state n \<psi>"
    using E_set D_nn col_qs by auto
  have probs: "(\<Sum>(p, _) \<leftarrow> E. p) = 1"
  proof -
    have "(\<Sum>(p, _) \<leftarrow> E. p) = sum_list (map (\<lambda>i. D!i) [0..<n])"
      unfolding E_def by (simp add: o_def case_prod_beta)
    also have "\<dots> = (\<Sum>i = 0..<n. D!i)"
      by (simp add: interv_sum_list_conv_sum_set_nat)
    also have "\<dots> = (\<Sum>i<n. D!i)"
      by (simp add: atLeast0LessThan)
    also have "\<dots> = 1" by (rule D_sum)
    finally show ?thesis.
  qed
  have ens: "ensemble n E"
    unfolding ensemble_def using ens_ok probs by blast

  \<comment> \<open>Entry-wise: \<open>ensemble_density n E = U * diag_mat_of_real D * U\<^sup>\<dagger> = \<rho>\<close>.\<close>
  have ED_car: "ensemble_density n E \<in> carrier_mat n n"
    by (rule ensemble_density_carrier_dim)
  have ED_eq: "ensemble_density n E = \<rho>"
  proof (rule eq_matI)
    show "dim_row (ensemble_density n E) = dim_row \<rho>"
      using ED_car rho_car by simp
    show "dim_col (ensemble_density n E) = dim_col \<rho>"
      using ED_car rho_car by simp
  next
    fix r c assume rc: "r < dim_row \<rho>" "c < dim_col \<rho>"
    then have r: "r < n" and c: "c < n" using rho_car by auto

    \<comment> \<open>LHS via entry formula.\<close>
    have LHS: "ensemble_density n E $$ (r, c) =
               (\<Sum>i<n. complex_of_real (D!i) * U $$ (r, i) * cnj (U $$ (c, i)))"
    proof -
      have "ensemble_density n E $$ (r, c) =
              (\<Sum>(p, \<psi>) \<leftarrow> E. complex_of_real p * \<psi> $ r * cnj (\<psi> $ c))"
        by (rule ensemble_density_index[OF r c])
      also have "\<dots> = sum_list (map (\<lambda>i. complex_of_real (D!i)
                                          * Matrix.col U i $ r
                                          * cnj (Matrix.col U i $ c)) [0..<n])"
        unfolding E_def by (simp add: o_def case_prod_beta)
      also have "\<dots> = (\<Sum>i = 0..<n.
                          complex_of_real (D!i)
                            * Matrix.col U i $ r
                            * cnj (Matrix.col U i $ c))"
        by (simp add: interv_sum_list_conv_sum_set_nat)
      also have "\<dots> = (\<Sum>i<n. complex_of_real (D!i)
                                * Matrix.col U i $ r
                                * cnj (Matrix.col U i $ c))"
        by (simp add: atLeast0LessThan)
      also have "\<dots> = (\<Sum>i<n. complex_of_real (D!i) * U $$ (r, i) * cnj (U $$ (c, i)))"
        using Uc r c by (intro sum.cong refl) simp
      finally show ?thesis.
    qed

    \<comment> \<open>RHS: expand \<rho> = U * diag_mat_of_real D * U-dagger entry-wise.\<close>
    let ?UD = "U * diag_mat_of_real D"
    have diag_car: "diag_mat_of_real D \<in> carrier_mat n n"
      using Dlen by force
    have UD_car: "?UD \<in> carrier_mat n n"
      using Uc diag_car by auto

    have UD_index: "\<And>k. k < n \<Longrightarrow>
         ?UD $$ (r, k) = complex_of_real (D!k) * U $$ (r, k)"
    proof -
      fix k assume k: "k < n"
      have "?UD $$ (r, k) = (\<Sum>j = 0..<n. U $$ (r, j) * diag_mat_of_real D $$ (j, k))"
        using Uc Dlen r k by (simp add: scalar_prod_def lessThan_atLeast0)
      also have "\<dots> = (\<Sum>j = 0..<n.
                          if j = k then U $$ (r, j) * complex_of_real (D!k) else 0)"
        using Dlen k by (intro sum.cong refl) auto
      also have "\<dots> = U $$ (r, k) * complex_of_real (D!k)"
        using k by simp
      also have "\<dots> = complex_of_real (D!k) * U $$ (r, k)"
        by (simp add: mult.commute)
      finally show "?UD $$ (r, k) = complex_of_real (D!k) * U $$ (r, k)".
    qed

    have RHS: "\<rho> $$ (r, c) =
               (\<Sum>i<n. complex_of_real (D!i) * U $$ (r, i) * cnj (U $$ (c, i)))"
    proof -
      have r_UD: "r < dim_row ?UD" using UD_car r by auto
      have c_Ud: "c < dim_col (U\<^sup>\<dagger>)" using Udag_car c by auto
      have rho_expand: "\<rho> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
        by (rule hermitian_spectral_decomp_eq[OF Uc rho_car UU spec])
      have dim_col_Ud: "dim_vec (Matrix.col (U\<^sup>\<dagger>) c) = n"
        using Uc by simp
      have "\<rho> $$ (r, c) = (?UD * (U\<^sup>\<dagger>)) $$ (r, c)"
        using rho_expand by simp
      also have "\<dots> = Matrix.row ?UD r \<bullet> Matrix.col (U\<^sup>\<dagger>) c"
        using index_mult_mat(1)[OF r_UD c_Ud] .
      also have "\<dots> = (\<Sum>k = 0..<n. Matrix.row ?UD r $ k * Matrix.col (U\<^sup>\<dagger>) c $ k)"
        unfolding scalar_prod_def using dim_col_Ud by simp
      also have "\<dots> = (\<Sum>k = 0..<n. ?UD $$ (r, k) * (U\<^sup>\<dagger>) $$ (k, c))"
      proof (intro sum.cong refl)
        fix k assume k: "k \<in> {0..<n}"
        hence klt: "k < n" by simp
        have kr: "r < dim_row ?UD" using UD_car r by auto
        have kc_UD: "k < dim_col ?UD" using UD_car klt by auto
        have rowk: "Matrix.row ?UD r $ k = ?UD $$ (r, k)"
          using kr kc_UD by simp
        have kr_Ud: "k < dim_row (U\<^sup>\<dagger>)" using Udag_car klt by auto
        have kc_Ud: "c < dim_col (U\<^sup>\<dagger>)" using Udag_car c by auto
        have colk: "Matrix.col (U\<^sup>\<dagger>) c $ k = (U\<^sup>\<dagger>) $$ (k, c)"
          using kr_Ud kc_Ud by (simp add: dagger_def)
        show "Matrix.row ?UD r $ k * Matrix.col (U\<^sup>\<dagger>) c $ k
                = ?UD $$ (r, k) * (U\<^sup>\<dagger>) $$ (k, c)"
          by (simp add: rowk colk)
      qed
      also have "\<dots> = (\<Sum>k = 0..<n. complex_of_real (D!k) * U $$ (r, k)
                                      * cnj (U $$ (c, k)))"
        using UD_index Uc c by (intro sum.cong refl, simp add: dagger_def)
      also have "\<dots> = (\<Sum>i<n. complex_of_real (D!i) * U $$ (r, i)
                                * cnj (U $$ (c, i)))"
        by (simp add: atLeast0LessThan)
      finally show ?thesis.
    qed
    from LHS RHS show "ensemble_density n E $$ (r, c) = \<rho> $$ (r, c)" 
      by simp
  qed

  from ens ED_eq show ?thesis by blast
qed

corollary density_matrix_iff_ensemble:
  fixes \<rho> :: "complex Matrix.mat"
  shows "density_matrix n \<rho> \<longleftrightarrow>
           (\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>)"
proof
  assume "density_matrix n \<rho>"
  thus "\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>"
    by (rule spectral_ensemble_exists)
next
  assume "\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>"
  then obtain E where ens: "ensemble n E"
                 and eq: "ensemble_density n E = \<rho>" by blast
  have "density_matrix n (ensemble_density n E)"
    by (rule ensemble_density_is_dm[OF ens])
  with eq show "density_matrix n \<rho>" by simp
qed

(* --------------------------------------------------------------------------
   \<section>15.1 (Pure states).  A density matrix of the form \<open>|\<psi>\<rangle>\<langle>\<psi>|\<close> is called
   a \<^emph>\<open>pure state\<close>.  Any ensemble representing such a \<rho> uses only vectors
   parallel to \<psi>.
   -------------------------------------------------------------------------- *)

definition pure_state_density :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "pure_state_density n \<rho> \<equiv>
     density_matrix n \<rho> \<and>
     (\<exists>\<psi>. quantum_state n \<psi> \<and> \<rho> = pure_density \<psi>)"

lemma pure_state_density_is_density:
  assumes "pure_state_density n \<rho>"
  shows "density_matrix n \<rho>"
  using assms by (simp add: pure_state_density_def)

lemma pure_density_is_pure_state_density:
  assumes "quantum_state n \<psi>"
  shows "pure_state_density n (pure_density \<psi>)"
  unfolding pure_state_density_def
  using assms pure_density_is_density_matrix by blast

(* Rank-1 characterisation: a density matrix \<rho> is pure iff it is idempotent
   (equivalently, iff it is a rank-one projection).  Not explicit in
   Paulsen p.\ 44 but a standard companion fact whose proof uses the spectral
   decomposition from Days 3\<endash>10. *)

theorem pure_density_iff_idempotent:
  fixes \<rho> :: "complex Matrix.mat"
  assumes dm: "density_matrix n \<rho>"
  shows "pure_state_density n \<rho> \<longleftrightarrow> \<rho> * \<rho> = \<rho>"
proof
  assume pure: "pure_state_density n \<rho>"
  then obtain \<psi> where st: "quantum_state n \<psi>" and rho_eq: "\<rho> = pure_density \<psi>"
    unfolding pure_state_density_def by blast
  have \<psi>_dim: "dim_vec \<psi> = n" using st by (simp add: quantum_state_def)
  have \<psi>_norm: "\<parallel>\<psi>\<parallel> = 1" using st by (simp add: quantum_state_def)
  have \<psi>_inner: "\<langle>\<psi> | \<psi>\<rangle> = 1"
    using \<psi>_norm cpx_vec_length_inner_prod[of \<psi>]
    by (metis of_real_1 one_power2)

  let ?M = "mat_of_cols n [\<psi>]"
  let ?Md = "(?M)\<^sup>\<dagger>"
  have M_car: "?M \<in> carrier_mat n 1"
    by (simp add: mat_of_cols_def)
  have Md_car: "?Md \<in> carrier_mat 1 n"
    using M_car by auto
  have MMd_car: "?M * ?Md \<in> carrier_mat n n"
    using M_car Md_car by auto

  have rho_MMd: "\<rho> = ?M * ?Md"
  proof -
    have "pure_density \<psi> = outer_sum n [\<psi>]"
      using \<psi>_dim by (simp add: pure_density_def)
    also have "\<dots> = ?M * ?Md"
      by (simp add: outer_sum_def)
    finally show ?thesis using rho_eq by simp
  qed

  have MdM: "?Md * ?M = 1\<^sub>m 1"
  proof (rule eq_matI)
    show "dim_row (?Md * ?M) = dim_row (1\<^sub>m 1)" using Md_car M_car by auto
    show "dim_col (?Md * ?M) = dim_col (1\<^sub>m 1)" using Md_car M_car by auto
  next
    fix i j assume ij: "i < dim_row (1\<^sub>m 1)" "j < dim_col (1\<^sub>m 1)"
    then have i0: "i = 0" and j0: "j = 0" by simp_all
    have r_Md: "0 < dim_row ?Md" using Md_car by simp
    have c_M: "0 < dim_col ?M" using M_car by simp
    have dvc: "dim_vec (Matrix.col ?M 0) = n" using M_car by simp
    have "(?Md * ?M) $$ (0, 0) = Matrix.row ?Md 0 \<bullet> Matrix.col ?M 0"
      using index_mult_mat(1)[OF r_Md c_M] .
    also have "\<dots> = (\<Sum>k = 0..<n. Matrix.row ?Md 0 $ k * Matrix.col ?M 0 $ k)"
      unfolding scalar_prod_def using dvc by simp
    also have "\<dots> = (\<Sum>k = 0..<n. ?Md $$ (0, k) * ?M $$ (k, 0))"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {0..<n}"
      hence klt: "k < n" by simp
      have kr_Md: "0 < dim_row ?Md" using Md_car by simp
      have kc_Md: "k < dim_col ?Md" using Md_car klt by simp
      have kr_M: "k < dim_row ?M" using M_car klt by simp
      have kc_M: "0 < dim_col ?M" using M_car by simp
      have rowk: "Matrix.row ?Md 0 $ k = ?Md $$ (0, k)"
        using kr_Md kc_Md by (simp add: dagger_def)
      have colk: "Matrix.col ?M 0 $ k = ?M $$ (k, 0)"
        using kr_M kc_M by simp
      show "Matrix.row ?Md 0 $ k * Matrix.col ?M 0 $ k = ?Md $$ (0, k) * ?M $$ (k, 0)"
        using rowk by (simp add: rowk colk)
    qed
    also have "\<dots> = (\<Sum>k = 0..<n. cnj (\<psi> $ k) * \<psi> $ k)"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {0..<n}"
      hence klt: "k < n" by simp
      have md_eq: "?Md $$ (0, k) = cnj (\<psi> $ k)"
        using klt \<psi>_dim by (simp add: mat_of_cols_def dagger_def)
      have m_eq: "?M $$ (k, 0) = \<psi> $ k"
        using klt \<psi>_dim by (simp add: mat_of_cols_def)
      show "?Md $$ (0, k) * ?M $$ (k, 0) = cnj (\<psi> $ k) * \<psi> $ k"
        by (simp add: md_eq m_eq)
    qed
    also have "\<dots> = \<langle>\<psi> | \<psi>\<rangle>"
      using \<psi>_dim by (simp add: inner_prod_def lessThan_atLeast0)
    also have "\<dots> = 1" using \<psi>_inner .
    finally have e00: "(?Md * ?M) $$ (0, 0) = 1" .
    show "(?Md * ?M) $$ (i, j) = (1\<^sub>m 1) $$ (i, j)"
      using i0 j0 e00 by simp
  qed

  have "\<rho> * \<rho> = (?M * ?Md) * (?M * ?Md)"
    using rho_MMd by simp
  also have "\<dots> = ?M * (?Md * (?M * ?Md))"
    using assoc_mult_mat[OF M_car Md_car MMd_car] .
  also have "\<dots> = ?M * ((?Md * ?M) * ?Md)"
    using assoc_mult_mat[OF Md_car M_car Md_car] by simp
  also have "\<dots> = ?M * ((1\<^sub>m 1) * ?Md)"
    using MdM by simp
  also have "\<dots> = ?M * ?Md"
    using Md_car by simp
  also have "\<dots> = \<rho>" using rho_MMd by simp
  finally show "\<rho> * \<rho> = \<rho>" .
next
  assume idem: "\<rho> * \<rho> = \<rho>"

  have rho_car: "\<rho> \<in> carrier_mat n n"
   and rho_psd: "psd \<rho>"
   and rho_Tr: "Tr \<rho> = 1"
    using dm unfolding density_matrix_def by auto
  have rho_herm: "hermitian \<rho>" using rho_psd by (rule psd_hermitian)

  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
       and Dlen: "length D = n"
       and spec: "U\<^sup>\<dagger> * \<rho> * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF rho_car rho_herm] by blast
  have Udag_car: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have UdU: "U\<^sup>\<dagger> * U = 1\<^sub>m n"
    using Uc UU unfolding unitary_def by auto
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using Uc UU unfolding unitary_def by auto
  have rho_eq: "\<rho> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    by (rule hermitian_spectral_decomp_eq[OF Uc rho_car UU spec])
  have rho_times_U: "\<rho> * U = U * diag_mat_of_real D"
    by (rule hermitian_spectral_decomp_right[OF Uc rho_car UU spec])
  have diag_car: "diag_mat_of_real D \<in> carrier_mat n n"
    using Dlen by force

  \<comment> \<open>Columns of U are unit vectors; eigenvectors with eigenvalues D!i.\<close>
  have col_dim: "\<And>i. i < n \<Longrightarrow> dim_vec (Matrix.col U i) = n" using Uc by simp
  have col_norm: "\<And>i. i < n \<Longrightarrow> \<parallel>Matrix.col U i\<parallel> = 1"
    using UU Uc unitary_unit_col by (metis carrier_matD(2))
  have col_qs: "\<And>i. i < n \<Longrightarrow> quantum_state n (Matrix.col U i)"
    using col_dim col_norm by (auto simp: quantum_state_def)
  have col_ne: "\<And>i. i < n \<Longrightarrow> Matrix.col U i \<noteq> 0\<^sub>v n"
  proof -
    fix i assume i: "i < n"
    show "Matrix.col U i \<noteq> 0\<^sub>v n"
    proof
      assume z: "Matrix.col U i = 0\<^sub>v n"
      hence "\<parallel>Matrix.col U i\<parallel> = 0"
        using col_dim[OF i] cpx_vec_length_zero_iff by metis
      with col_norm[OF i] show False by simp
    qed
  qed
  have eig: "\<And>i. i < n \<Longrightarrow>
               \<rho> *\<^sub>v Matrix.col U i = complex_of_real (D!i) \<cdot>\<^sub>v Matrix.col U i"
  proof -
    fix i assume i: "i < n"
    let ?u = "Matrix.col U i"
    show "\<rho> *\<^sub>v ?u = complex_of_real (D!i) \<cdot>\<^sub>v ?u"
    proof (rule eq_vecI)
      show "dim_vec (\<rho> *\<^sub>v ?u) = dim_vec (complex_of_real (D!i) \<cdot>\<^sub>v ?u)"
        using rho_car col_dim[OF i] by simp
    next
      fix k assume k: "k < dim_vec (complex_of_real (D!i) \<cdot>\<^sub>v ?u)"
      hence klt: "k < n" using col_dim[OF i] by simp
      have "(\<rho> *\<^sub>v ?u) $ k = (\<rho> * U) $$ (k, i)"
        using rho_car Uc i klt
        by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using rho_times_U by simp
      also have "\<dots> = (\<Sum>j = 0..<n.
                          U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
        using Uc Dlen klt i by (simp add: scalar_prod_def lessThan_atLeast0)
      also have "\<dots> = (\<Sum>j = 0..<n.
                          if j = i then U $$ (k, j) * complex_of_real (D!i) else 0)"
        using Dlen i by (intro sum.cong refl) auto
      also have "\<dots> = U $$ (k, i) * complex_of_real (D!i)"
        using i by simp
      also have "\<dots> = complex_of_real (D!i) * U $$ (k, i)"
        by (simp add: mult.commute)
      also have "\<dots> = (complex_of_real (D!i) \<cdot>\<^sub>v ?u) $ k"
        using klt Uc i by simp
      finally show "(\<rho> *\<^sub>v ?u) $ k = (complex_of_real (D!i) \<cdot>\<^sub>v ?u) $ k" .
    qed
  qed

  \<comment> \<open>Eigenvalues are non-negative and sum to 1.\<close>
  have D_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  proof -
    fix i assume i: "i < n"
    have "0 \<le> Re (complex_of_real (D ! i))"
      using psd_iff_nonneg_eigenvalues[OF rho_car] rho_psd eig[OF i]
            col_ne[OF i] col_dim[OF i] by blast
    thus "0 \<le> D ! i" by simp
  qed
  have D_sum: "(\<Sum>i<n. D!i) = 1"
  proof -
    have "complex_of_real (\<Sum>i<n. D!i) = (\<Sum>i<n. complex_of_real (D!i))"
      by simp
    also have "\<dots> = Tr (diag_mat_of_real D)"
      using Dlen by (simp add: Tr_def)
    also have "\<dots> = Tr (U\<^sup>\<dagger> * \<rho> * U)" using spec by simp
    also have "\<dots> = Tr \<rho>"
      using Tr_unitary_conjugation[OF UU] rho_car Uc by simp
    also have "\<dots> = 1" using rho_Tr .
    finally show ?thesis using of_real_eq_1_iff by blast
  qed

  \<comment> \<open>Idempotence of \<rho> forces (D!i) squared = D!i for each i, so D!i in {0,1}.\<close>
  have DD_eq_D: "diag_mat_of_real D * diag_mat_of_real D = diag_mat_of_real D"
  proof -
    have "diag_mat_of_real D * diag_mat_of_real D
            = ((U\<^sup>\<dagger>) * \<rho> * U) * ((U\<^sup>\<dagger>) * \<rho> * U)"
      using spec by simp
    also have "\<dots> = (U\<^sup>\<dagger>) * \<rho> * (U * (U\<^sup>\<dagger>)) * \<rho> * U"
      using Uc Udag_car rho_car by (simp, smt (verit, best) assoc_mult_mat mult_carrier_mat)
    also have "\<dots> = (U\<^sup>\<dagger>) * \<rho> * (1\<^sub>m n) * \<rho> * U"
      using UUd by simp
    also have "\<dots> = (U\<^sup>\<dagger>) * \<rho> * \<rho> * U"
      using rho_car Uc Udag_car by simp
    also have "\<dots> = (U\<^sup>\<dagger>) * \<rho> * U"
      using idem rho_car Uc Udag_car by simp
    also have "\<dots> = diag_mat_of_real D" using spec.
    finally show ?thesis.
  qed
  have D_sq: "\<And>i. i < n \<Longrightarrow> (D!i) * (D!i) = D!i"
  proof -
    fix i assume i: "i < n"
    have "complex_of_real (D!i) * complex_of_real (D!i) =
          (\<Sum>j = 0..<n. diag_mat_of_real D $$ (i, j) * diag_mat_of_real D $$ (j, i))"
    proof -
      have "(\<Sum>j = 0..<n. diag_mat_of_real D $$ (i, j) * diag_mat_of_real D $$ (j, i))
            = (\<Sum>j = 0..<n. if j = i then complex_of_real (D!i) * complex_of_real (D!i) else 0)"
        using Dlen i by (intro sum.cong refl) auto
      also have "\<dots> = complex_of_real (D!i) * complex_of_real (D!i)"
        using i by simp
      finally show ?thesis by simp
    qed
    also have "\<dots> = (diag_mat_of_real D * diag_mat_of_real D) $$ (i, i)"
      using diag_car Dlen i by (simp add: scalar_prod_def lessThan_atLeast0)
    also have "\<dots> = diag_mat_of_real D $$ (i, i)"
      using DD_eq_D by simp
    also have "\<dots> = complex_of_real (D!i)"
      using Dlen i by simp
    finally have "complex_of_real (D!i) * complex_of_real (D!i) = complex_of_real (D!i)" .
    hence "complex_of_real ((D!i) * (D!i)) = complex_of_real (D!i)" by simp
    thus "(D!i) * (D!i) = D!i" using of_real_eq_iff by blast
  qed
  have D_binary: "\<And>i. i < n \<Longrightarrow> D!i = 0 \<or> D!i = 1"
  proof -
    fix i assume i: "i < n"
    have "(D!i) * (D!i - 1) = 0" using D_sq[OF i] by simp
    thus "D!i = 0 \<or> D!i = 1" by auto
  qed

  \<comment> \<open>Exactly one index has eigenvalue 1; the rest are 0.\<close>
  have card_ones: "card {i. i < n \<and> D!i = 1} = 1"
  proof -
    let ?S = "{i. i < n \<and> D!i = 1}"
    have fin: "finite ?S" by auto
    have intEq: "{..<n} \<inter> {i. D!i = 1} = ?S" by auto
    have "(1::real) = (\<Sum>i<n. D ! i)" using D_sum by simp
    also have "\<dots> = (\<Sum>i<n. if D!i = 1 then (1::real) else 0)"
      using D_binary by (intro sum.cong refl) auto
    also have "\<dots> = (\<Sum>i \<in> {..<n} \<inter> {i. D!i = 1}. (1::real))
                  + (\<Sum>i \<in> {..<n} \<inter> -{i. D!i = 1}. (0::real))"
      by (rule sum.If_cases[OF finite_lessThan])
    also have "\<dots> = (\<Sum>i \<in> ?S. (1::real))"
      using intEq by simp
    also have "\<dots> = real (card ?S)" by simp
    finally have "real (card ?S) = 1" by simp
    thus ?thesis by (metis of_nat_1_eq_iff)
  qed
  obtain j where Sj: "{i. i < n \<and> D!i = 1} = {j}"
    using card_1_singletonE[OF card_ones] by blast
  have ex_one: "\<exists>!j. j < n \<and> D!j = 1"
  proof
    show "j < n \<and> D!j = 1" using Sj by auto
  next
    fix k assume "k < n \<and> D!k = 1"
    thus "k = j" using Sj by auto
  qed
  then obtain j where j_lt: "j < n" and D_j: "D!j = 1"
    and D_unique: "\<And>i. i < n \<Longrightarrow> D!i = 1 \<Longrightarrow> i = j"
    by blast
  have D_others: "\<And>i. i < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> D!i = 0"
    using D_binary D_unique by blast

  \<comment> \<open>Then \<rho> = pure_density (col U j).\<close>
  let ?\<psi> = "Matrix.col U j"
  have psi_qs: "quantum_state n ?\<psi>" using col_qs[OF j_lt] .

  have rho_pure: "\<rho> = pure_density ?\<psi>"
  proof (rule eq_matI)
    have rho_pdim: "pure_density ?\<psi> = outer_sum n [?\<psi>]"
      using col_dim[OF j_lt] by (simp add: pure_density_def)
    have pd_car: "outer_sum n [?\<psi>] \<in> carrier_mat n n" by auto
    show "dim_row \<rho> = dim_row (pure_density ?\<psi>)"
      using rho_car pd_car rho_pdim by simp
    show "dim_col \<rho> = dim_col (pure_density ?\<psi>)"
      using rho_car pd_car rho_pdim by simp
  next
    fix r c assume rc: "r < dim_row (pure_density ?\<psi>)" "c < dim_col (pure_density ?\<psi>)"
    have rho_pdim: "pure_density ?\<psi> = outer_sum n [?\<psi>]"
      using col_dim[OF j_lt] by (simp add: pure_density_def)
    have pd_car: "outer_sum n [?\<psi>] \<in> carrier_mat n n" by auto
    from rc rho_pdim pd_car have r: "r < n" and c: "c < n" by auto

    have pd_index: "pure_density ?\<psi> $$ (r, c) = ?\<psi> $ r * cnj (?\<psi> $ c)"
      using rho_pdim outer_sum_singleton_index[OF r c] by simp

    let ?UD = "U * diag_mat_of_real D"
    have UD_car: "?UD \<in> carrier_mat n n" using Uc diag_car by auto

    have UD_index: "\<And>k. k < n \<Longrightarrow>
         ?UD $$ (r, k) = complex_of_real (D!k) * U $$ (r, k)"
    proof -
      fix k assume k: "k < n"
      have "?UD $$ (r, k) = (\<Sum>j = 0..<n. U $$ (r, j) * diag_mat_of_real D $$ (j, k))"
        using Uc Dlen r k by (simp add: scalar_prod_def lessThan_atLeast0)
      also have "\<dots> = (\<Sum>j = 0..<n.
                          if j = k then U $$ (r, j) * complex_of_real (D!k) else 0)"
        using Dlen k by (intro sum.cong refl) auto
      also have "\<dots> = U $$ (r, k) * complex_of_real (D!k)"
        using k by simp
      also have "\<dots> = complex_of_real (D!k) * U $$ (r, k)"
        by (simp add: mult.commute)
      finally show "?UD $$ (r, k) = complex_of_real (D!k) * U $$ (r, k)" .
    qed

    have r_UD: "r < dim_row ?UD" using UD_car r by auto
    have c_Ud: "c < dim_col (U\<^sup>\<dagger>)" using Udag_car c by auto
    have dim_col_Ud: "dim_vec (Matrix.col (U\<^sup>\<dagger>) c) = n" using Uc by simp

    have "\<rho> $$ (r, c) = (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) $$ (r, c)"
      by (simp only: rho_eq)
    also have "\<dots> = Matrix.row ?UD r \<bullet> Matrix.col (U\<^sup>\<dagger>) c"
      using index_mult_mat(1)[OF r_UD c_Ud] .
    also have "\<dots> = (\<Sum>k = 0..<n. Matrix.row ?UD r $ k * Matrix.col (U\<^sup>\<dagger>) c $ k)"
      unfolding scalar_prod_def using dim_col_Ud by simp
    also have "\<dots> = (\<Sum>k = 0..<n. ?UD $$ (r, k) * (U\<^sup>\<dagger>) $$ (k, c))"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {0..<n}"
      hence klt: "k < n" by simp
      have kr: "r < dim_row ?UD" using UD_car r by auto
      have kc_UD: "k < dim_col ?UD" using UD_car klt by auto
      have rowk: "Matrix.row ?UD r $ k = ?UD $$ (r, k)"
        using kr kc_UD by simp
      have kr_Ud: "k < dim_row (U\<^sup>\<dagger>)" using Udag_car klt by auto
      have kc_Ud': "c < dim_col (U\<^sup>\<dagger>)" using Udag_car c by auto
      have colk: "Matrix.col (U\<^sup>\<dagger>) c $ k = (U\<^sup>\<dagger>) $$ (k, c)"
        using kr_Ud kc_Ud' by (simp add: dagger_def)
      show "Matrix.row ?UD r $ k * Matrix.col (U\<^sup>\<dagger>) c $ k
              = ?UD $$ (r, k) * (U\<^sup>\<dagger>) $$ (k, c)"
        by (simp add: rowk colk)
    qed
    also have "\<dots> = (\<Sum>k = 0..<n. complex_of_real (D!k) * U $$ (r, k)
                                    * cnj (U $$ (c, k)))"
      using UD_index Uc c by (intro sum.cong refl, simp add: dagger_def)
    also have "\<dots> = (\<Sum>k = 0..<n. if k = j
                                  then U $$ (r, j) * cnj (U $$ (c, j)) else 0)"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {0..<n}"
      hence klt: "k < n" by simp
      show "complex_of_real (D!k) * U $$ (r, k) * cnj (U $$ (c, k))
            = (if k = j then U $$ (r, j) * cnj (U $$ (c, j)) else 0)"
      proof (cases "k = j")
        case True
        thus ?thesis using D_j by simp
      next
        case False
        hence "D!k = 0" using D_others klt by simp
        thus ?thesis using False by simp
      qed
    qed
    also have "\<dots> = U $$ (r, j) * cnj (U $$ (c, j))"
      using j_lt by simp
    also have "\<dots> = ?\<psi> $ r * cnj (?\<psi> $ c)"
      using Uc r c j_lt by simp
    also have "\<dots> = pure_density ?\<psi> $$ (r, c)"
      using pd_index by simp
    finally show "\<rho> $$ (r, c) = pure_density ?\<psi> $$ (r, c)".
  qed

  show "pure_state_density n \<rho>"
    unfolding pure_state_density_def using dm rho_pure psi_qs by blast
qed

(* Helper: outer_sum n [\<psi>] acts on \<gamma> as multiplication by \<langle>\<psi>|\<gamma>\<rangle>. *)

lemma outer_sum_singleton_mult_vec:
  assumes \<psi>_dim: "dim_vec \<psi> = n" and \<gamma>_dim: "dim_vec \<gamma> = n"
  shows "outer_sum n [\<psi>] *\<^sub>v \<gamma> = \<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>"
proof (rule eq_vecI)
  show "dim_vec (outer_sum n [\<psi>] *\<^sub>v \<gamma>) = dim_vec (\<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>)"
    using \<psi>_dim by simp
next
  fix i assume i: "i < dim_vec (\<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>)"
  hence ilt: "i < n" using \<psi>_dim by simp
  have os_car: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have dcg: "dim_vec \<gamma> = n" using \<gamma>_dim .
  have "(outer_sum n [\<psi>] *\<^sub>v \<gamma>) $ i
        = (\<Sum>k = 0..<n. outer_sum n [\<psi>] $$ (i, k) * \<gamma> $ k)"
    using ilt \<gamma>_dim os_car by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<n. \<psi> $ i * cnj (\<psi> $ k) * \<gamma> $ k)"
    by (intro sum.cong refl) (simp add: outer_sum_singleton_index[OF ilt])
  also have "\<dots> = (\<Sum>k = 0..<n. \<psi> $ i * (cnj (\<psi> $ k) * \<gamma> $ k))"
    by (intro sum.cong refl) (simp add: mult.assoc)
  also have "\<dots> = \<psi> $ i * (\<Sum>k = 0..<n. cnj (\<psi> $ k) * \<gamma> $ k)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = \<psi> $ i * \<langle>\<psi>|\<gamma>\<rangle>"
    using \<gamma>_dim by (simp add: inner_prod_def lessThan_atLeast0)
  also have "\<dots> = \<langle>\<psi>|\<gamma>\<rangle> * \<psi> $ i" by (simp add: mult.commute)
  also have "\<dots> = (\<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>) $ i" using ilt \<psi>_dim by simp
  finally show "(outer_sum n [\<psi>] *\<^sub>v \<gamma>) $ i = (\<langle>\<psi>|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>) $ i" .
qed

(* Helper: quadratic form of ensemble_density E at \<gamma>
   is \<Sum>_E p \<cdot> |\<langle>\<psi>|\<gamma>\<rangle>|\<^sup>2 (complex form). *)

lemma ensemble_density_quad_form:
  assumes E_dim: "\<forall>(p, \<psi>) \<in> set E. dim_vec \<psi> = n"
      and \<gamma>_dim: "dim_vec \<gamma> = n"
  shows "\<langle>\<gamma> | ensemble_density n E *\<^sub>v \<gamma>\<rangle> =
         (\<Sum>(p, \<psi>) \<leftarrow> E. complex_of_real p * \<langle>\<psi>|\<gamma>\<rangle> * cnj \<langle>\<psi>|\<gamma>\<rangle>)"
  using E_dim
proof (induction E)
  case Nil
  have ed_nil: "ensemble_density n [] = 0\<^sub>m n n"
    by (simp add: ensemble_density_def)
  have "ensemble_density n [] *\<^sub>v \<gamma> = 0\<^sub>v n"
  proof (rule eq_vecI)
    show "dim_vec (ensemble_density n [] *\<^sub>v \<gamma>) = dim_vec (0\<^sub>v n)"
      using ed_nil by simp
  next
    fix i assume i: "i < dim_vec (0\<^sub>v n)"
    hence ilt: "i < n" by simp
    have "(ensemble_density n [] *\<^sub>v \<gamma>) $ i
          = (\<Sum>k = 0..<n. (0\<^sub>m n n) $$ (i, k) * \<gamma> $ k)"
      using ed_nil ilt \<gamma>_dim by (simp add: scalar_prod_def)
    also have "\<dots> = 0" using ilt by simp
    also have "\<dots> = (0\<^sub>v n) $ i" using ilt by simp
    finally show "(ensemble_density n [] *\<^sub>v \<gamma>) $ i = (0\<^sub>v n) $ i" .
  qed
  hence "\<langle>\<gamma> | ensemble_density n [] *\<^sub>v \<gamma>\<rangle> = \<langle>\<gamma> | 0\<^sub>v n\<rangle>" by simp
  also have "\<dots> = 0" using \<gamma>_dim by (simp add: inner_prod_def)
  finally show ?case by simp
next
  case (Cons a E')
  obtain p \<psi>\<^sub>0 where a: "a = (p, \<psi>\<^sub>0)" by (cases a) auto
  have \<psi>\<^sub>0_dim: "dim_vec \<psi>\<^sub>0 = n" using Cons.prems a by auto
  have rest_dim: "\<forall>(p, \<psi>) \<in> set E'. dim_vec \<psi> = n"
    using Cons.prems by auto
  have IH: "\<langle>\<gamma> | ensemble_density n E' *\<^sub>v \<gamma>\<rangle> =
            (\<Sum>(q, \<phi>) \<leftarrow> E'. complex_of_real q * \<langle>\<phi>|\<gamma>\<rangle> * cnj \<langle>\<phi>|\<gamma>\<rangle>)"
    by (rule Cons.IH[OF rest_dim])

  let ?pM = "complex_of_real p \<cdot>\<^sub>m outer_sum n [\<psi>\<^sub>0]"
  let ?ED = "ensemble_density n E'"
  have pM_car: "?pM \<in> carrier_mat n n" by auto
  have ED_car: "?ED \<in> carrier_mat n n"
    by (rule ensemble_density_carrier_dim)
  have \<gamma>_car: "\<gamma> \<in> carrier_vec n" using \<gamma>_dim by auto

  have split: "ensemble_density n ((p, \<psi>\<^sub>0) # E') *\<^sub>v \<gamma>
               = ?pM *\<^sub>v \<gamma> + ?ED *\<^sub>v \<gamma>"
  proof -
    have "ensemble_density n ((p, \<psi>\<^sub>0) # E') *\<^sub>v \<gamma>
          = (?pM + ?ED) *\<^sub>v \<gamma>"
      by (simp add: ensemble_density_Cons)
    also have "\<dots> = ?pM *\<^sub>v \<gamma> + ?ED *\<^sub>v \<gamma>"
      by (rule add_mult_distrib_mat_vec[OF pM_car ED_car \<gamma>_car])
    finally show ?thesis .
  qed

  have pM_mv: "?pM *\<^sub>v \<gamma> = complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>)"
  proof (rule eq_vecI)
    show "dim_vec (?pM *\<^sub>v \<gamma>) = dim_vec (complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>))"
      by simp
  next
    fix i assume i: "i < dim_vec (complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>))"
    hence ilt: "i < n" by simp
    have os_car: "outer_sum n [\<psi>\<^sub>0] \<in> carrier_mat n n" by auto
    have "(?pM *\<^sub>v \<gamma>) $ i
          = (\<Sum>k = 0..<n. ?pM $$ (i, k) * \<gamma> $ k)"
      using ilt \<gamma>_dim pM_car by (simp add: scalar_prod_def)
    also have "\<dots> = (\<Sum>k = 0..<n.
                      complex_of_real p * (outer_sum n [\<psi>\<^sub>0] $$ (i, k)) * \<gamma> $ k)"
      using ilt os_car by (intro sum.cong refl) simp
    also have "\<dots> = (\<Sum>k = 0..<n.
                      complex_of_real p * (outer_sum n [\<psi>\<^sub>0] $$ (i, k) * \<gamma> $ k))"
      by (intro sum.cong refl) (simp add: mult.assoc)
    also have "\<dots> = complex_of_real p
                      * (\<Sum>k = 0..<n. outer_sum n [\<psi>\<^sub>0] $$ (i, k) * \<gamma> $ k)"
      by (simp add: sum_distrib_left)
    also have "\<dots> = complex_of_real p * ((outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>) $ i)"
      using ilt \<gamma>_dim os_car by (simp add: scalar_prod_def)
    also have "\<dots> = (complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>)) $ i"
      using ilt os_car by simp
    finally show "(?pM *\<^sub>v \<gamma>) $ i = (complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>)) $ i" .
  qed

  have pM_inner: "\<langle>\<gamma> | ?pM *\<^sub>v \<gamma>\<rangle>
                 = complex_of_real p * \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * cnj \<langle>\<psi>\<^sub>0|\<gamma>\<rangle>"
  proof -
    have "\<langle>\<gamma> | ?pM *\<^sub>v \<gamma>\<rangle>
          = \<langle>\<gamma> | complex_of_real p \<cdot>\<^sub>v (outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>)\<rangle>"
      using pM_mv by simp
    also have "\<dots> = complex_of_real p * \<langle>\<gamma> | outer_sum n [\<psi>\<^sub>0] *\<^sub>v \<gamma>\<rangle>"
      by (rule inner_prod_right_smult')
    also have "\<dots> = complex_of_real p * \<langle>\<gamma> | \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> \<cdot>\<^sub>v \<psi>\<^sub>0\<rangle>"
      using outer_sum_singleton_mult_vec[OF \<psi>\<^sub>0_dim \<gamma>_dim] by simp
    also have "\<dots> = complex_of_real p * (\<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * \<langle>\<gamma>|\<psi>\<^sub>0\<rangle>)"
      by (simp add: inner_prod_right_smult')
    also have "\<dots> = complex_of_real p * \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * \<langle>\<gamma>|\<psi>\<^sub>0\<rangle>"
      by (simp add: mult.assoc)
    also have "\<dots> = complex_of_real p * \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * cnj \<langle>\<psi>\<^sub>0|\<gamma>\<rangle>"
      using inner_prod_cnj[of \<psi>\<^sub>0 \<gamma>] \<psi>\<^sub>0_dim \<gamma>_dim by simp
    finally show ?thesis .
  qed

  have dim_eq: "dim_vec (?pM *\<^sub>v \<gamma>) = dim_vec (?ED *\<^sub>v \<gamma>)"
    using pM_car ED_car by auto

  have "\<langle>\<gamma> | ensemble_density n ((p, \<psi>\<^sub>0) # E') *\<^sub>v \<gamma>\<rangle>
        = \<langle>\<gamma> | ?pM *\<^sub>v \<gamma> + ?ED *\<^sub>v \<gamma>\<rangle>"
    using split by simp
  also have "\<dots> = \<langle>\<gamma> | ?pM *\<^sub>v \<gamma>\<rangle> + \<langle>\<gamma> | ?ED *\<^sub>v \<gamma>\<rangle>"
    by (rule inner_prod_right_add'[OF dim_eq])
  also have "\<dots> = complex_of_real p * \<langle>\<psi>\<^sub>0|\<gamma>\<rangle> * cnj \<langle>\<psi>\<^sub>0|\<gamma>\<rangle>
                 + (\<Sum>(q, \<phi>) \<leftarrow> E'. complex_of_real q * \<langle>\<phi>|\<gamma>\<rangle> * cnj \<langle>\<phi>|\<gamma>\<rangle>)"
    using pM_inner IH by simp
  also have "\<dots> = (\<Sum>(q, \<phi>) \<leftarrow> (p, \<psi>\<^sub>0) # E'. complex_of_real q * \<langle>\<phi>|\<gamma>\<rangle> * cnj \<langle>\<phi>|\<gamma>\<rangle>)"
    by simp
  finally show ?case using a by simp
qed

(* The main theorem. *)

theorem pure_ensemble_parallel:
  fixes \<psi> :: "complex Matrix.vec"
  assumes st: "quantum_state n \<psi>"
      and ens: "ensemble n E"
      and dens: "ensemble_density n E = pure_density \<psi>"
      and mem: "(p, \<psi>\<^sub>i) \<in> set E"
      and ppos: "0 < p"
  shows "\<exists>\<beta>. \<psi>\<^sub>i = \<beta> \<cdot>\<^sub>v \<psi>"
proof -
  \<comment> \<open>Basic facts about psi, psi_i, and E.\<close>
  have \<psi>_dim: "dim_vec \<psi> = n" using st by (simp add: quantum_state_def)
  have \<psi>_norm: "\<parallel>\<psi>\<parallel> = 1" using st by (simp add: quantum_state_def)
  have \<psi>_inner: "\<langle>\<psi>|\<psi>\<rangle> = 1"
    using \<psi>_norm cpx_vec_length_inner_prod[of \<psi>]
    by (metis of_real_1 one_power2)

  have E_qs: "\<forall>(p, \<phi>) \<in> set E. quantum_state n \<phi>"
    using ens by (auto simp: ensemble_def)
  have E_p_nn: "\<forall>(p, \<phi>) \<in> set E. 0 \<le> p"
    using ens by (auto simp: ensemble_def)
  have E_dim: "\<forall>(q, \<phi>) \<in> set E. dim_vec \<phi> = n"
    using E_qs by (auto simp: quantum_state_def)

  have \<psi>\<^sub>i_qs: "quantum_state n \<psi>\<^sub>i" using E_qs mem by fastforce
  have \<psi>\<^sub>i_dim: "dim_vec \<psi>\<^sub>i = n"
    using \<psi>\<^sub>i_qs by (simp add: quantum_state_def)

  \<comment> \<open>Define beta = inner psi psi_i and w = psi_i - beta * psi.\<close>
  define \<beta> where "\<beta> = \<langle>\<psi>|\<psi>\<^sub>i\<rangle>"
  define w where "w = \<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>"
  have w_dim: "dim_vec w = n"
    unfolding w_def using \<psi>_dim \<psi>\<^sub>i_dim by simp
  have \<psi>_\<beta>\<psi>_dim: "dim_vec (\<beta> \<cdot>\<^sub>v \<psi>) = dim_vec \<psi>\<^sub>i"
    using \<psi>_dim \<psi>\<^sub>i_dim by simp

  \<comment> \<open>Step 1: w \<perp> \<psi>, i.e. \<langle>\<psi>|w\<rangle> = 0.\<close>
  have \<psi>_perp_w: "\<langle>\<psi>|w\<rangle> = 0"
  proof -
    have "\<langle>\<psi>|w\<rangle> = \<langle>\<psi>|\<psi>\<^sub>i\<rangle> - \<langle>\<psi>|\<beta> \<cdot>\<^sub>v \<psi>\<rangle>"
      unfolding w_def
      by (rule inner_prod_right_minus'[OF \<psi>_\<beta>\<psi>_dim[symmetric]])
    also have "\<dots> = \<langle>\<psi>|\<psi>\<^sub>i\<rangle> - \<beta> * \<langle>\<psi>|\<psi>\<rangle>"
      by (simp add: inner_prod_right_smult')
    also have "\<dots> = \<beta> - \<beta>" using \<psi>_inner by (simp add: \<beta>_def)
    also have "\<dots> = 0" by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Step 2: pure-density psi acting on w is zero.\<close>
  have pd_w_zero: "pure_density \<psi> *\<^sub>v w = 0\<^sub>v n"
  proof -
    have "pure_density \<psi> *\<^sub>v w = outer_sum n [\<psi>] *\<^sub>v w"
      by (simp add: pure_density_def \<psi>_dim)
    also have "\<dots> = \<langle>\<psi>|w\<rangle> \<cdot>\<^sub>v \<psi>"
      by (rule outer_sum_singleton_mult_vec[OF \<psi>_dim w_dim])
    also have "\<dots> = 0 \<cdot>\<^sub>v \<psi>" using \<psi>_perp_w by simp
    also have "\<dots> = 0\<^sub>v n"
      using \<psi>_dim by (intro eq_vecI) simp_all
    finally show ?thesis .
  qed

  \<comment> \<open>Step 3: quadratic form at w is zero via dens.\<close>
  have quad_zero: "\<langle>w | ensemble_density n E *\<^sub>v w\<rangle> = 0"
  proof -
    have "\<langle>w | ensemble_density n E *\<^sub>v w\<rangle> = \<langle>w | pure_density \<psi> *\<^sub>v w\<rangle>"
      using dens by simp
    also have "\<dots> = \<langle>w | 0\<^sub>v n\<rangle>" using pd_w_zero by simp
    also have "\<dots> = 0" using w_dim by (simp add: inner_prod_def)
    finally show ?thesis .
  qed

  \<comment> \<open>Step 4: expand via quad_form, extract real sum, show each term is 0.\<close>
  have sum_cplx_zero:
    "(\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>) = 0"
    using ensemble_density_quad_form[OF E_dim w_dim] quad_zero by simp

  have termwise: "\<And>q \<phi>. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>
                        = complex_of_real (q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
  proof -
    fix q :: real and \<phi> :: "complex Matrix.vec"
    have "\<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle> = complex_of_real ((cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
      using complex_norm_square[of "\<langle>\<phi>|w\<rangle>"] by simp
    hence "complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>
           = complex_of_real q * complex_of_real ((cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
      by (simp add: mult.assoc)
    also have "\<dots> = complex_of_real (q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
      by simp
    finally show "complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>
                 = complex_of_real (q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)" .
  qed

  have cplx_eq_real:
    "(\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>)
      = complex_of_real (\<Sum>(q, \<phi>) \<leftarrow> E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
  proof -
    have "(\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real q * \<langle>\<phi>|w\<rangle> * cnj \<langle>\<phi>|w\<rangle>)
          = (\<Sum>(q, \<phi>) \<leftarrow> E. complex_of_real (q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2))"
      by (intro arg_cong[where f=sum_list] map_cong refl)
         (simp add: termwise case_prod_beta)
    also have "\<dots> = complex_of_real (\<Sum>(q, \<phi>) \<leftarrow> E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2)"
    proof (induct E)
      case Nil show ?case by simp
    next
      case (Cons a E'') thus ?case by (cases a) simp
    qed
    finally show ?thesis .
  qed

  have sum_real_zero: "(\<Sum>(q, \<phi>) \<leftarrow> E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2) = 0"
    using sum_cplx_zero cplx_eq_real
    by auto

  have terms_nn: "\<forall>(q, \<phi>) \<in> set E. 0 \<le> q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2"
    using E_p_nn by (auto simp: mult_nonneg_nonneg)

  have each_zero: "\<forall>(q, \<phi>) \<in> set E. q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2 = 0"
  proof -
    let ?xs = "map (\<lambda>(q, \<phi>). q * (cmod \<langle>\<phi>|w\<rangle>)\<^sup>2) E"
    have nn: "\<And>x. x \<in> set ?xs \<Longrightarrow> 0 \<le> x"
      using terms_nn by (auto simp: case_prod_beta)
    have sum0: "sum_list ?xs = 0"
      using sum_real_zero by (simp add: o_def case_prod_beta)
    have "\<forall>x \<in> set ?xs. x = 0"
      using sum_list_nonneg_eq_0_iff[OF nn] sum0 by blast
    thus ?thesis by (auto simp: case_prod_beta)
  qed

  \<comment> \<open>Step 5: for our (p, psi_i), p > 0 and the term is 0, so inner psi_i w = 0.\<close>
  have \<psi>\<^sub>i_perp_w: "\<langle>\<psi>\<^sub>i|w\<rangle> = 0"
  proof -
    have "p * (cmod \<langle>\<psi>\<^sub>i|w\<rangle>)\<^sup>2 = 0"
      using each_zero mem by auto
    hence "(cmod \<langle>\<psi>\<^sub>i|w\<rangle>)\<^sup>2 = 0" using ppos by simp
    hence "cmod \<langle>\<psi>\<^sub>i|w\<rangle> = 0" by simp
    thus ?thesis by simp
  qed

  \<comment> \<open>Step 6: compute inner psi_i w = inner psi_i psi_i minus beta cnj beta.\<close>
  have \<psi>\<^sub>i\<psi>_cnj: "\<langle>\<psi>\<^sub>i|\<psi>\<rangle> = cnj \<beta>"
    unfolding \<beta>_def using inner_prod_cnj[of \<psi> \<psi>\<^sub>i] \<psi>_dim \<psi>\<^sub>i_dim by simp

  have \<psi>\<^sub>i_inner_sq: "\<langle>\<psi>\<^sub>i|\<psi>\<^sub>i\<rangle> = \<beta> * cnj \<beta>"
  proof -
    have dim_eq: "dim_vec \<psi>\<^sub>i = dim_vec (\<beta> \<cdot>\<^sub>v \<psi>)" using \<psi>_dim \<psi>\<^sub>i_dim by simp
    have "0 = \<langle>\<psi>\<^sub>i|w\<rangle>" using \<psi>\<^sub>i_perp_w by simp
    also have "\<dots> = \<langle>\<psi>\<^sub>i|\<psi>\<^sub>i\<rangle> - \<langle>\<psi>\<^sub>i|\<beta> \<cdot>\<^sub>v \<psi>\<rangle>"
      unfolding w_def
      by (rule inner_prod_right_minus'[OF dim_eq])
    also have "\<dots> = \<langle>\<psi>\<^sub>i|\<psi>\<^sub>i\<rangle> - \<beta> * \<langle>\<psi>\<^sub>i|\<psi>\<rangle>"
      by (simp add: inner_prod_right_smult')
    also have "\<dots> = \<langle>\<psi>\<^sub>i|\<psi>\<^sub>i\<rangle> - \<beta> * cnj \<beta>"
      using \<psi>\<^sub>i\<psi>_cnj by simp
    finally show ?thesis by simp
  qed

  \<comment> \<open>Step 7: \<langle>w|w\<rangle> = 0.\<close>
  have w_inner_zero: "\<langle>w|w\<rangle> = 0"
  proof -
    have dim_eq: "dim_vec (\<beta> \<cdot>\<^sub>v \<psi>) = dim_vec \<psi>\<^sub>i" using \<psi>_dim \<psi>\<^sub>i_dim by simp
    have w_equiv: "w = \<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>" by (simp add: w_def)
    have "\<langle>w|w\<rangle> = \<langle>\<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>| w\<rangle>" using w_equiv by simp
    also have "\<dots> = \<langle>\<psi>\<^sub>i|w\<rangle> - \<langle>\<beta> \<cdot>\<^sub>v \<psi>|w\<rangle>"
      by (rule inner_prod_left_minus'[OF dim_eq[symmetric]])
         (simp add: w_dim \<psi>\<^sub>i_dim)
    also have "\<langle>\<beta> \<cdot>\<^sub>v \<psi>|w\<rangle> = cnj \<beta> * \<langle>\<psi>|w\<rangle>"
    proof -
      have "dim_vec \<psi> = dim_vec w" using \<psi>_dim w_dim by simp
      thus ?thesis by (rule inner_prod_left_smult')
    qed
    also have "cnj \<beta> * \<langle>\<psi>|w\<rangle> = 0" using \<psi>_perp_w by simp
    finally show ?thesis using \<psi>\<^sub>i_perp_w by simp
  qed

  \<comment> \<open>Step 8: inner w w = 0 so w = 0.\<close>
  have w_zero: "w = 0\<^sub>v n"
  proof -
    have "(complex_of_real (\<parallel>w\<parallel>))\<^sup>2 = \<langle>w|w\<rangle>"
      using cpx_vec_length_inner_prod[of w] by simp
    hence "(complex_of_real (\<parallel>w\<parallel>))\<^sup>2 = 0" using w_inner_zero by simp
    hence "(\<parallel>w\<parallel>)\<^sup>2 = 0"
      by (metis of_real_0 of_real_eq_iff of_real_power)
    hence "\<parallel>w\<parallel> = 0" by simp
    thus "w = 0\<^sub>v n"
      using w_dim cpx_vec_length_zero_iff by metis
  qed

  \<comment> \<open>Conclusion: psi_i = beta * psi.\<close>
  have "\<psi>\<^sub>i = \<beta> \<cdot>\<^sub>v \<psi>"
  proof (rule eq_vecI)
    show "dim_vec \<psi>\<^sub>i = dim_vec (\<beta> \<cdot>\<^sub>v \<psi>)" using \<psi>_dim \<psi>\<^sub>i_dim by simp
  next
    fix i assume i: "i < dim_vec (\<beta> \<cdot>\<^sub>v \<psi>)"
    hence ilt: "i < n" using \<psi>_dim by simp
    have "(\<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>) $ i = 0" using w_zero ilt by (simp add: w_def)
    moreover have "(\<psi>\<^sub>i - \<beta> \<cdot>\<^sub>v \<psi>) $ i = \<psi>\<^sub>i $ i - \<beta> * \<psi> $ i"
      using ilt \<psi>_dim \<psi>\<^sub>i_dim by (simp add: minus_vec_def)
    ultimately have "\<psi>\<^sub>i $ i = \<beta> * \<psi> $ i" by simp
    thus "\<psi>\<^sub>i $ i = (\<beta> \<cdot>\<^sub>v \<psi>) $ i"
      using ilt \<psi>_dim by simp
  qed
  thus ?thesis by blast
qed

(* --------------------------------------------------------------------------
   \<section>15.2 Composite Ensembles.  The pure density of a tensor is the tensor
   of pure densities: \<open>|\<psi> \<otimes> \<phi>\<rangle>\<langle>\<psi> \<otimes> \<phi>| = |\<psi>\<rangle>\<langle>\<psi>| \<otimes> |\<phi>\<rangle>\<langle>\<phi>|\<close>.
   -------------------------------------------------------------------------- *)

lemma tensor_pure_density:
  fixes \<psi> \<phi> :: "complex Matrix.vec"
  assumes \<psi>_dim: "dim_vec \<psi> = m"
      and \<phi>_dim: "dim_vec \<phi> = p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "pure_density (tensor_vec \<psi> \<phi>) =
         (pure_density \<psi>) \<Otimes> (pure_density \<phi>)"
  sorry
  (* Proof sketch (PDF p.\ 45, verification of \<open>|\<psi>\<otimes>\<phi>\<rangle>\<langle>\<psi>\<otimes>\<phi>| = |\<psi>\<rangle>\<langle>\<psi>| \<otimes> |\<phi>\<rangle>\<langle>\<phi>|\<close>):
     both sides live in \<open>carrier_mat (m*p) (m*p)\<close>.  For indices
       \<open>i = i\<^sub>1*p + i\<^sub>2\<close>, \<open>j = j\<^sub>1*p + j\<^sub>2\<close> with \<open>i\<^sub>1,j\<^sub>1<m\<close>, \<open>i\<^sub>2,j\<^sub>2<p\<close>,
     LHS $$ (i,j) = \<open>(tensor_vec \<psi> \<phi>) $ i * cnj ((tensor_vec \<psi> \<phi>) $ j)
                  = (\<psi>$i\<^sub>1 \<cdot> \<phi>$i\<^sub>2) * cnj (\<psi>$j\<^sub>1 \<cdot> \<phi>$j\<^sub>2)
                  = (\<psi>$i\<^sub>1 * cnj (\<psi>$j\<^sub>1)) * (\<phi>$i\<^sub>2 * cnj (\<phi>$j\<^sub>2))
                  = pure_density \<psi> $$ (i\<^sub>1,j\<^sub>1) * pure_density \<phi> $$ (i\<^sub>2,j\<^sub>2)\<close>,
     which is exactly \<open>index_tensor_mat\<close> applied to RHS.  Conclude by
     \<open>eq_matI\<close>. *)

(* --------------------------------------------------------------------------
   \<section>15.3 Partial Traces (motivation).
   For a bipartite density matrix \<rho> \<in> L(H\<^sub>A \<otimes> H\<^sub>B), measurements acting only
   on the A-side correspond to operators of the form \<open>M \<Otimes> 1\<^sub>m p\<close>.  One seeks
   a linear "partial trace" map \<open>tr\<^sub>B : L(H\<^sub>A \<otimes> H\<^sub>B) \<rightarrow> L(H\<^sub>A)\<close> satisfying
       \<open>Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>) = Tr (M * tr\<^sub>B \<rho>)    \<forall>M\<close>.
   Existence, uniqueness, and the construction of \<open>tr\<^sub>B\<close> are taken up in Day 15.
   -------------------------------------------------------------------------- *)


end