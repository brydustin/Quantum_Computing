(*
  Title:      Quantum_Computing11.thy
  Author:     Dustin Bryant (based on lectures of Vern Paulsen)

  Day 11 split from Quantum_Computing.thy.  Days 3 through 10 are
  imported from Quantum_Computing_3_10 so they can live in the heap image.
*)

theory Quantum_Computing11
  imports
    Vern_Paulsen_QC_3_10.Basic_Math
    Vern_Paulsen_QC_3_10.Quantum_Computing_3_10
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
proof -
  let ?T = "tensor_vec \<psi> \<phi>"
  let ?A = "pure_density \<psi>"
  let ?B = "pure_density \<phi>"
  have T_dim: "dim_vec ?T = m * p"
    using tensor_vec_dim \<psi>_dim \<phi>_dim by simp
  have lhs_eq: "pure_density ?T = outer_sum (m * p) [?T]"
    using T_dim by (simp add: pure_density_def)
  have lhs_car: "pure_density ?T \<in> carrier_mat (m*p) (m*p)"
    using lhs_eq by force
  have A_car: "?A \<in> carrier_mat m m"
    using \<psi>_dim by (simp add: pure_density_def, simp add: carrier_matI)
  have B_car: "?B \<in> carrier_mat p p"
    using \<phi>_dim by (simp add: pure_density_def, simp add: carrier_matI)
  have rhs_dim_row: "dim_row (?A \<Otimes> ?B) = m * p" using A_car B_car by auto
  have rhs_dim_col: "dim_col (?A \<Otimes> ?B) = m * p" using A_car B_car by auto

  show ?thesis
  proof (rule eq_matI)
    show "dim_row (pure_density ?T) = dim_row (?A \<Otimes> ?B)"
      using lhs_car rhs_dim_row by auto
    show "dim_col (pure_density ?T) = dim_col (?A \<Otimes> ?B)"
      using lhs_car rhs_dim_col by auto
  next
    fix r c
    assume rc: "r < dim_row (?A \<Otimes> ?B)" "c < dim_col (?A \<Otimes> ?B)"
    from rc rhs_dim_row rhs_dim_col have r_lt: "r < m * p" and c_lt: "c < m * p"
      by auto

    let ?r1 = "r div p"  let ?r2 = "r mod p"
    let ?c1 = "c div p"  let ?c2 = "c mod p"
    have r1_lt: "?r1 < m" using r_lt less_mult_imp_div_less by blast
    have r2_lt: "?r2 < p" using p_pos by simp
    have c1_lt: "?c1 < m" using c_lt less_mult_imp_div_less by blast
    have c2_lt: "?c2 < p" using p_pos by simp

    \<comment> \<open>LHS entry.\<close>
    have lhs_ent: "pure_density ?T $$ (r, c) = ?T $ r * cnj (?T $ c)"
      using lhs_eq outer_sum_singleton_index[OF r_lt c_lt] by simp
    have T_r: "?T $ r = \<psi> $ ?r1 * \<phi> $ ?r2"
      using tensor_vec_index[OF \<psi>_dim \<phi>_dim r_lt] .
    have T_c: "?T $ c = \<psi> $ ?c1 * \<phi> $ ?c2"
      using tensor_vec_index[OF \<psi>_dim \<phi>_dim c_lt] .
    have lhs_ent': "pure_density ?T $$ (r, c)
                    = \<psi> $ ?r1 * \<phi> $ ?r2 * (cnj (\<psi> $ ?c1) * cnj (\<phi> $ ?c2))"
      using lhs_ent T_r T_c by simp

    \<comment> \<open>RHS entry via index_tensor_mat.\<close>
    have AB_ent: "(?A \<Otimes> ?B) $$ (r, c) = ?A $$ (?r1, ?c1) * ?B $$ (?r2, ?c2)"
    proof -
      have drA: "dim_row ?A = m" using A_car by auto
      have dcA: "dim_col ?A = m" using A_car by auto
      have drB: "dim_row ?B = p" using B_car by auto
      have dcB: "dim_col ?B = p" using B_car by auto
      show ?thesis
        using index_tensor_mat[OF drA dcA drB dcB] r_lt c_lt m_pos p_pos
        by simp
    qed
    have A_ent: "?A $$ (?r1, ?c1) = \<psi> $ ?r1 * cnj (\<psi> $ ?c1)"
    proof -
      have "?A = outer_sum m [\<psi>]"
        using \<psi>_dim by (simp add: pure_density_def)
      thus ?thesis
        using outer_sum_singleton_index[OF r1_lt c1_lt] by simp
    qed
    have B_ent: "?B $$ (?r2, ?c2) = \<phi> $ ?r2 * cnj (\<phi> $ ?c2)"
    proof -
      have "?B = outer_sum p [\<phi>]"
        using \<phi>_dim by (simp add: pure_density_def)
      thus ?thesis
        using outer_sum_singleton_index[OF r2_lt c2_lt] by simp
    qed
    have rhs_ent: "(?A \<Otimes> ?B) $$ (r, c)
                   = (\<psi> $ ?r1 * cnj (\<psi> $ ?c1)) * (\<phi> $ ?r2 * cnj (\<phi> $ ?c2))"
      using AB_ent A_ent B_ent by simp

    show "pure_density ?T $$ (r, c) = (?A \<Otimes> ?B) $$ (r, c)"
      using lhs_ent' rhs_ent by (simp add: mult.commute mult.left_commute)
  qed
qed

(* --------------------------------------------------------------------------
   \<section>15.3 Partial Traces (motivation).
   For a bipartite density matrix \<rho> \<in> L(H\<^sub>A \<otimes> H\<^sub>B), measurements acting only
   on the A-side correspond to operators of the form \<open>M \<Otimes> 1\<^sub>m p\<close>.  One seeks
   a linear "partial trace" map \<open>tr\<^sub>B : L(H\<^sub>A \<otimes> H\<^sub>B) \<rightarrow> L(H\<^sub>A)\<close> satisfying
       \<open>Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>) = Tr (M * tr\<^sub>B \<rho>)    \<forall>M\<close>.
   Existence, uniqueness, and the construction of \<open>tr\<^sub>B\<close> are taken up in Day 15.
   -------------------------------------------------------------------------- *)


(* ============================================================================
   DAY 15 — 30 / Sep / 11
   Topic: Trace Formulas; Tensor Products of Operators; Partial Traces
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Section 16.1.  Tr(A) equals the sum of quadratic forms in any orthonormal
   basis.  (PDF p.46.)
   -------------------------------------------------------------------------- *)

theorem trace_via_onb:
  fixes A :: "complex Matrix.mat"
  assumes sq: "A \<in> carrier_mat n n"
      and orth: "orthonormal_list n vs"
      and full: "length vs = n"
  shows "Tr A = (\<Sum>i<n. \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>)"
proof -
  let ?V = "mat_of_cols n vs"
  have U: "unitary ?V"
    using orth full by (rule orthonormal_mat_unitary)
  have Vrow: "dim_row ?V = n"
    by (simp add: mat_of_cols_def)
  have Vcol: "dim_col ?V = n"
    using full by (simp add: mat_of_cols_def)
  have Arow: "dim_row A = n" and Acol: "dim_col A = n"
    using sq by auto

  have diag:
    "\<And>i. i < n \<Longrightarrow>
      ((?V\<^sup>\<dagger> * A * ?V) $$ (i, i)) = \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>"
  proof -
    fix i assume i_lt: "i < n"
    have vi_dim: "dim_vec (vs ! i) = n"
      using orth full i_lt by (simp add: orthonormal_listD_dim)
    have AV_entry:
      "\<And>k. k < n \<Longrightarrow> (A * ?V) $$ (k, i) = (A *\<^sub>v vs ! i) $ k"
    proof -
      fix k assume k_lt: "k < n"
      have "(A * ?V) $$ (k, i) = (\<Sum>j<n. A $$ (k, j) * ?V $$ (j, i))"
        using Arow Acol Vrow Vcol k_lt i_lt by simp
      also have "\<dots> = (\<Sum>j<n. A $$ (k, j) * (vs ! i) $ j)"
        using full i_lt by (intro sum.cong refl) (simp add: mat_of_cols_def)
      also have "\<dots> = (A *\<^sub>v vs ! i) $ k"
        using Arow Acol vi_dim k_lt
        by (simp add: scalar_prod_def lessThan_atLeast0)
      finally show "(A * ?V) $$ (k, i) = (A *\<^sub>v vs ! i) $ k" .
    qed

    have "((?V\<^sup>\<dagger> * A * ?V) $$ (i, i)) =
          ((?V\<^sup>\<dagger> * (A * ?V)) $$ (i, i))"
      using sq Vrow Vcol by (metis Vrow assoc_mult_mat carrier_mat_triv dim_col_of_dagger)
    also have "\<dots> = (\<Sum>k<n. (?V\<^sup>\<dagger>) $$ (i, k) * (A * ?V) $$ (k, i))"
      using Arow Acol Vrow Vcol i_lt by simp
    also have "\<dots> = (\<Sum>k<n. cnj ((vs ! i) $ k) * (A *\<^sub>v vs ! i) $ k)"
      using full i_lt by (intro sum.cong refl, metis AV_entry Vcol case_prod_conv dagger_def 
                          index_mat(1) lessThan_iff mat_of_cols_carrier(2) mat_of_cols_def) 
    also have "\<dots> = \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>"
      using Arow vi_dim by (simp add: inner_prod_def lessThan_atLeast0)
    finally show "((?V\<^sup>\<dagger> * A * ?V) $$ (i, i)) =  \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>".
  qed

  have "Tr (?V\<^sup>\<dagger> * A * ?V) =
        (\<Sum>i<n. ((?V\<^sup>\<dagger> * A * ?V) $$ (i, i)))"
    using Vrow Vcol Arow Acol by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>i<n. \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>)"
    by (intro sum.cong refl) (simp add: diag)
  finally have "Tr (?V\<^sup>\<dagger> * A * ?V) =
                (\<Sum>i<n. \<langle>vs ! i | A *\<^sub>v vs ! i\<rangle>)" .
  moreover have "Tr (?V\<^sup>\<dagger> * A * ?V) = Tr A"
    using U Arow Acol Vrow by (subst Tr_unitary_conjugation, simp_all)
  ultimately show ?thesis
    by simp
qed

(* --------------------------------------------------------------------------
   Tr(R tensor T) = Tr R times Tr T.  (PDF pp.46-47.)
   -------------------------------------------------------------------------- *)

theorem trace_tensor:
  fixes R T :: "complex Matrix.mat"
  assumes Rsq: "R \<in> carrier_mat m m"
      and Tsq: "T \<in> carrier_mat p p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "Tr (R \<Otimes> T) = Tr R * Tr T"
proof -
  have drR: "dim_row R = m" using Rsq by auto
  have dcR: "dim_col R = m" using Rsq by auto
  have drT: "dim_row T = p" using Tsq by auto
  have dcT: "dim_col T = p" using Tsq by auto
  have RT_car: "R \<Otimes> T \<in> carrier_mat (m*p) (m*p)"
    using Rsq Tsq by auto

  \<comment> \<open>Diagonal entries factor via index_tensor_mat.\<close>
  have ent: "\<And>i k. i < m \<Longrightarrow> k < p \<Longrightarrow>
             (R \<Otimes> T) $$ (i * p + k, i * p + k) = R $$ (i, i) * T $$ (k, k)"
  proof -
    fix i k assume i_lt: "i < m" and k_lt: "k < p"
    have rb: "i * p + k < m * p"
    proof -
      have "i * p + k < (i + 1) * p" using k_lt by simp
      moreover have "(i + 1) * p \<le> m * p"
      proof -
        have "i + 1 \<le> m" using i_lt by simp
        thus "(i + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have dv: "(i * p + k) div p = i" using k_lt by simp
    have md: "(i * p + k) mod p = k" using k_lt by simp
    have "(R \<Otimes> T) $$ (i * p + k, i * p + k)
          = R $$ ((i*p+k) div p, (i*p+k) div p)
            * T $$ ((i*p+k) mod p, (i*p+k) mod p)"
      using index_tensor_mat[OF drR dcR drT dcT rb rb m_pos p_pos] .
    also have "\<dots> = R $$ (i, i) * T $$ (k, k)"
      using dv md by simp
    finally show "(R \<Otimes> T) $$ (i * p + k, i * p + k) = R $$ (i, i) * T $$ (k, k)" .
  qed

  \<comment> \<open>Bijection {..<m} x {..<p} -> {..<m*p} via (i, k) |-> i*p + k.\<close>
  have bij: "bij_betw (\<lambda>(i, k). i * p + k) ({..<m} \<times> {..<p}) {..<m*p}"
  proof (rule bij_betwI[where g = "\<lambda>r. (r div p, r mod p)"])
    show "(\<lambda>(i, k). i * p + k) \<in> {..<m} \<times> {..<p} \<rightarrow> {..<m*p}"
    proof
      fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
      then obtain i k where z: "z = (i, k)" and i_lt: "i < m" and k_lt: "k < p"
        by blast
      have "i * p + k < (i + 1) * p" using k_lt by simp
      moreover have "(i + 1) * p \<le> m * p"
      proof -
        have "i + 1 \<le> m" using i_lt by simp
        thus "(i + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately have "i * p + k < m * p" by linarith
      thus "(case z of (i, k) \<Rightarrow> i * p + k) \<in> {..<m*p}"
        using z by simp
    qed
  next
    show "(\<lambda>r. (r div p, r mod p)) \<in> {..<m*p} \<rightarrow> {..<m} \<times> {..<p}"
      using p_pos by (auto simp: less_mult_imp_div_less)
  next
    fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
    then obtain i k where z: "z = (i, k)" and i_lt: "i < m" and k_lt: "k < p"
      by blast
    show "(\<lambda>r. (r div p, r mod p)) ((\<lambda>(i, k). i * p + k) z) = z"
      using z k_lt by simp
  next
    fix r assume r_in: "r \<in> {..<m*p}"
    show "(\<lambda>(i, k). i * p + k) ((\<lambda>r. (r div p, r mod p)) r) = r"
      by simp
  qed

  have "Tr (R \<Otimes> T) = (\<Sum>r<m*p. (R \<Otimes> T) $$ (r, r))"
    using RT_car by (simp add: Tr_def, 
        smt (verit, del_insts) carrier_matD(1,2) 
             dim_col_tensor_mat dim_row_tensor_mat lessThan_iff sum.cong)
  also have "\<dots> = (\<Sum>(i, k) \<in> {..<m} \<times> {..<p}.
                    (R \<Otimes> T) $$ (i * p + k, i * p + k))"
    using sum.reindex_bij_betw[OF bij, symmetric, of "\<lambda>r. (R \<Otimes> T) $$ (r, r)"]
    by (simp add: case_prod_beta)
  also have "\<dots> = (\<Sum>(i, k) \<in> {..<m} \<times> {..<p}. R $$ (i, i) * T $$ (k, k))"
    by (intro sum.cong refl) (auto simp: ent)
  also have "\<dots> = (\<Sum>i<m. \<Sum>k<p. R $$ (i, i) * T $$ (k, k))"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>i<m. R $$ (i, i)) * (\<Sum>k<p. T $$ (k, k))"
    by (simp add: sum_product)
  also have "\<dots> = Tr R * Tr T"
    using Rsq Tsq by (simp add: Tr_def)
  finally show ?thesis.
qed

(* --------------------------------------------------------------------------
   Section 16.1 (cont'd).  The canonical map
       Gamma : L(H_A) tensor L(H_B) -> L(H_A tensor H_B),  R tensor T |-> R tensor T
   is a vector-space isomorphism in finite dimensions.  We record only the
   dimension-counting half: both sides have dimension (m*p)^2.
   -------------------------------------------------------------------------- *)

proposition L_tensor_dim:
  fixes m p :: nat
  shows "m^2 * p^2 = (m * p)^2"
  by (simp add: power2_eq_square mult.assoc mult.left_commute)

definition operator_tensor_iso_map :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "operator_tensor_iso_map m p c \<equiv>
     Matrix.mat (m*p) (m*p)
       (\<lambda>(r,s). c $$ ((r div p) * m + (s div p), (r mod p) * p + (s mod p)))"

lemma operator_tensor_iso_map_carrier [simp]:
  "operator_tensor_iso_map m p c \<in> carrier_mat (m*p) (m*p)"
  by (simp add: operator_tensor_iso_map_def)

lemma operator_tensor_iso_map_entry:
  assumes "r < m*p" and "s < m*p"
  shows "operator_tensor_iso_map m p c $$ (r,s) =
         c $$ ((r div p) * m + (s div p), (r mod p) * p + (s mod p))"
  using assms by (simp add: operator_tensor_iso_map_def)

lemma operator_tensor_iso_map_row_bound:
  fixes m p r s :: nat
  assumes p_pos: "0 < p" and "r < m*p" and "s < m*p"
  shows "(r div p) * m + (s div p) < m*m"
proof -
  have rdiv: "r div p < m"
    using div_less_iff_less_mult[OF p_pos, of r m] assms(2) by simp
  have sdiv: "s div p < m"
    using div_less_iff_less_mult[OF p_pos, of s m] assms(3) by simp
  have "(r div p) * m + (s div p) < (r div p) * m + m"
    using sdiv by simp
  also have "\<dots> = Suc (r div p) * m"
    by simp
  also have "\<dots> \<le> m * m"
    using rdiv by (metis Suc_leI mult.commute mult_le_mono2)
  finally show ?thesis .
qed

lemma operator_tensor_iso_map_col_bound:
  fixes p r s :: nat
  assumes p_pos: "0 < p"
  shows "(r mod p) * p + (s mod p) < p*p"
proof -
  have rmod: "r mod p < p"
    using mod_less_divisor[of p r] p_pos by simp
  have smod: "s mod p < p"
    using mod_less_divisor[of p s] p_pos by simp
  have "(r mod p) * p + (s mod p) < (r mod p) * p + p"
    using smod by simp
  also have "\<dots> = Suc (r mod p) * p"
    by simp
  also have "\<dots> \<le> p * p"
    using rmod by (metis Suc_leI mult.commute mult_le_mono2)
  finally show ?thesis .
qed

definition operator_tensor_iso_inv :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "operator_tensor_iso_inv m p x \<equiv>
     Matrix.mat (m*m) (p*p)
       (\<lambda>(a,b). x $$ ((a div m) * p + (b div p), (a mod m) * p + (b mod p)))"

definition operator_tensor_coordinate_space ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex, complex Matrix.mat) linear_structure" where
  "operator_tensor_coordinate_space m p \<equiv> mat_linear_structure (m*m) (p*p)"

definition bipartite_operator_space ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex, complex Matrix.mat) linear_structure" where
  "bipartite_operator_space m p \<equiv> mat_linear_structure (m*p) (m*p)"

lemma operator_tensor_iso_inv_carrier [simp]:
  "operator_tensor_iso_inv m p x \<in> carrier_mat (m*m) (p*p)"
  by (simp add: operator_tensor_iso_inv_def)

lemma operator_tensor_iso_inv_entry:
  assumes "a < m*m" and "b < p*p"
  shows "operator_tensor_iso_inv m p x $$ (a,b) =
         x $$ ((a div m) * p + (b div p), (a mod m) * p + (b mod p))"
  using assms by (simp add: operator_tensor_iso_inv_def)

lemma operator_tensor_iso_inv_row_bound:
  fixes m p a b :: nat
  assumes m_pos: "0 < m" and p_pos: "0 < p" and "a < m*m" and "b < p*p"
  shows "(a div m) * p + (b div p) < m*p"
proof -
  have adiv: "a div m < m"
    using div_less_iff_less_mult[OF m_pos, of a m] assms(3) by simp
  have bdiv: "b div p < p"
    using div_less_iff_less_mult[OF p_pos, of b p] assms(4) by simp
  have "(a div m) * p + (b div p) < (a div m) * p + p"
    using bdiv by simp
  also have "\<dots> = Suc (a div m) * p"
    by simp
  also have "\<dots> \<le> m * p"
    using adiv by (metis Suc_leI mult_le_mono1)
  finally show ?thesis .
qed

lemma operator_tensor_iso_inv_col_bound:
  fixes m p a b :: nat
  assumes m_pos: "0 < m" and p_pos: "0 < p"
  shows "(a mod m) * p + (b mod p) < m*p"
proof -
  have amod: "a mod m < m"
    using mod_less_divisor[of m a] m_pos by simp
  have bmod: "b mod p < p"
    using mod_less_divisor[of p b] p_pos by simp
  have "(a mod m) * p + (b mod p) < (a mod m) * p + p"
    using bmod by simp
  also have "\<dots> = Suc (a mod m) * p"
    by simp
  also have "\<dots> \<le> m * p"
    using amod by (metis Suc_leI mult_le_mono1)
  finally show ?thesis .
qed

lemma operator_tensor_iso_map_add:
  assumes p_pos: "0 < p"
      and x: "x \<in> carrier_mat (m*m) (p*p)"
      and y: "y \<in> carrier_mat (m*m) (p*p)"
  shows "operator_tensor_iso_map m p (x + y) =
         operator_tensor_iso_map m p x + operator_tensor_iso_map m p y"
proof (rule eq_matI, goal_cases)
  case (1 i j)
  then have i: "i < m*p" and j: "j < m*p"
    by (simp_all add: operator_tensor_iso_map_def)
  have row: "(i div p) * m + (j div p) < m*m"
    using operator_tensor_iso_map_row_bound[OF p_pos i j] .
  have col: "(i mod p) * p + (j mod p) < p*p"
    using operator_tensor_iso_map_col_bound[OF p_pos, of i j] .
  show ?case
    using i j row col x y by (simp add: operator_tensor_iso_map_def)
next
  case 2
  show ?case by (simp add: operator_tensor_iso_map_def)
next
  case 3
  show ?case by (simp add: operator_tensor_iso_map_def)
qed

lemma operator_tensor_iso_map_zero:
  assumes p_pos: "0 < p"
  shows "operator_tensor_iso_map m p (0\<^sub>m (m*m) (p*p)) = 0\<^sub>m (m*p) (m*p)"
  by (auto simp: operator_tensor_iso_map_def intro!: eq_matI index_zero_mat(1)
      intro: operator_tensor_iso_map_row_bound[OF p_pos]
             operator_tensor_iso_map_col_bound[OF p_pos])

lemma operator_tensor_iso_map_smult:
  assumes p_pos: "0 < p"
      and x: "x \<in> carrier_mat (m*m) (p*p)"
  shows "operator_tensor_iso_map m p (c \<cdot>\<^sub>m x) =
         c \<cdot>\<^sub>m operator_tensor_iso_map m p x"
proof (rule eq_matI, goal_cases)
  case (1 i j)
  then have i: "i < m*p" and j: "j < m*p"
    by (simp_all add: operator_tensor_iso_map_def)
  have row: "(i div p) * m + (j div p) < m*m"
    using operator_tensor_iso_map_row_bound[OF p_pos i j] .
  have col: "(i mod p) * p + (j mod p) < p*p"
    using operator_tensor_iso_map_col_bound[OF p_pos, of i j] .
  show ?case
    using i j row col x by (simp add: operator_tensor_iso_map_def)
next
  case 2
  show ?case by (simp add: operator_tensor_iso_map_def)
next
  case 3
  show ?case by (simp add: operator_tensor_iso_map_def)
qed

lemma operator_tensor_iso_inv_add:
  assumes m_pos: "0 < m"
      and p_pos: "0 < p"
      and x: "x \<in> carrier_mat (m*p) (m*p)"
      and y: "y \<in> carrier_mat (m*p) (m*p)"
  shows "operator_tensor_iso_inv m p (x + y) =
         operator_tensor_iso_inv m p x + operator_tensor_iso_inv m p y"
proof (rule eq_matI, goal_cases)
  case (1 a b)
  then have a: "a < m*m" and b: "b < p*p"
    by (simp_all add: operator_tensor_iso_inv_def)
  have row: "(a div m) * p + (b div p) < m*p"
    using operator_tensor_iso_inv_row_bound[OF m_pos p_pos a b] .
  have col: "(a mod m) * p + (b mod p) < m*p"
    using operator_tensor_iso_inv_col_bound[OF m_pos p_pos, of a b] .
  show ?case
    using a b row col x y by (simp add: operator_tensor_iso_inv_def)
next
  case 2
  show ?case by (simp add: operator_tensor_iso_inv_def)
next
  case 3
  show ?case by (simp add: operator_tensor_iso_inv_def)
qed

lemma operator_tensor_iso_inv_zero:
  assumes m_pos: "0 < m" and p_pos: "0 < p"
  shows "operator_tensor_iso_inv m p (0\<^sub>m (m*p) (m*p)) = 0\<^sub>m (m*m) (p*p)"
  by (auto simp: operator_tensor_iso_inv_def intro!: eq_matI index_zero_mat(1)
      intro: operator_tensor_iso_inv_row_bound[OF m_pos p_pos]
             operator_tensor_iso_inv_col_bound[OF m_pos p_pos])

lemma operator_tensor_iso_inv_smult:
  assumes m_pos: "0 < m"
      and p_pos: "0 < p"
      and x: "x \<in> carrier_mat (m*p) (m*p)"
  shows "operator_tensor_iso_inv m p (c \<cdot>\<^sub>m x) =
         c \<cdot>\<^sub>m operator_tensor_iso_inv m p x"
proof (rule eq_matI, goal_cases)
  case (1 a b)
  then have a: "a < m*m" and b: "b < p*p"
    by (simp_all add: operator_tensor_iso_inv_def)
  have row: "(a div m) * p + (b div p) < m*p"
    using operator_tensor_iso_inv_row_bound[OF m_pos p_pos a b] .
  have col: "(a mod m) * p + (b mod p) < m*p"
    using operator_tensor_iso_inv_col_bound[OF m_pos p_pos, of a b] .
  show ?case
    using a b row col x by (simp add: operator_tensor_iso_inv_def)
next
  case 2
  show ?case by (simp add: operator_tensor_iso_inv_def)
next
  case 3
  show ?case by (simp add: operator_tensor_iso_inv_def)
qed

proposition operator_tensor_space_isomorphism:
  assumes m_pos: "0 < m"
      and p_pos: "0 < p"
  shows "is_isomorphism_between
           (operator_tensor_coordinate_space m p)
           (bipartite_operator_space m p)
           (operator_tensor_iso_map m p)"
proof -
  let ?V = "operator_tensor_coordinate_space m p"
  let ?W = "bipartite_operator_space m p"
  let ?F = "operator_tensor_iso_map m p"
  let ?G = "operator_tensor_iso_inv m p"

  have F_linear: "linear_structure_map ?V ?W ?F"
    unfolding linear_structure_map_def operator_tensor_coordinate_space_def
      bipartite_operator_space_def mat_linear_structure_def
    by (auto intro: operator_tensor_iso_map_zero[OF p_pos]
               operator_tensor_iso_map_add[OF p_pos]
               operator_tensor_iso_map_smult[OF p_pos])

  have G_linear: "linear_structure_map ?W ?V ?G"
    unfolding linear_structure_map_def operator_tensor_coordinate_space_def
      bipartite_operator_space_def mat_linear_structure_def
    by (auto intro: operator_tensor_iso_inv_zero[OF m_pos p_pos]
               operator_tensor_iso_inv_add[OF m_pos p_pos]
               operator_tensor_iso_inv_smult[OF m_pos p_pos])

  have GF: "\<And>x. x \<in> ls_carrier ?V \<Longrightarrow> ?G (?F x) = x"
  proof -
    fix x
    assume x: "x \<in> ls_carrier ?V"
    then have xc: "x \<in> carrier_mat (m*m) (p*p)"
      by (simp add: operator_tensor_coordinate_space_def mat_linear_structure_def)
    show "?G (?F x) = x"
    proof (rule eq_matI)
      show "dim_row (?G (?F x)) = dim_row x"
        using xc by (simp add: operator_tensor_iso_inv_def)
      show "dim_col (?G (?F x)) = dim_col x"
        using xc by (simp add: operator_tensor_iso_inv_def)
    next
      fix a b
      assume ab: "a < dim_row x" "b < dim_col x"
      then have a: "a < m*m" and b: "b < p*p"
        using xc by auto
      have adiv: "a div m < m"
        using a m_pos by (simp add: div_less_iff_less_mult)
      have amod: "a mod m < m"
        using m_pos by simp
      have bdiv: "b div p < p"
        using b p_pos by (simp add: div_less_iff_less_mult)
      have bmod: "b mod p < p"
        using p_pos by simp
      have row: "(a div m) * p + (b div p) < m * p"
        using operator_tensor_iso_inv_row_bound[OF m_pos p_pos a b] .
      have col: "(a mod m) * p + (b mod p) < m * p"
        using operator_tensor_iso_inv_col_bound[OF m_pos p_pos, of a b] .
      have div_row: "((a div m) * p + (b div p)) div p = a div m"
        using bdiv by simp
      have div_col: "((a mod m) * p + (b mod p)) div p = a mod m"
        using bmod by simp
      have mod_row: "((a div m) * p + (b div p)) mod p = b div p"
        using bdiv by simp
      have mod_col: "((a mod m) * p + (b mod p)) mod p = b mod p"
        using bmod by simp
      have recomb_a: "(a div m) * m + (a mod m) = a"
        by simp
      have recomb_b: "(b div p) * p + (b mod p) = b"
        by simp
      show "?G (?F x) $$ (a,b) = x $$ (a,b)"
        using a b row col div_row div_col mod_row mod_col recomb_a recomb_b
        by (simp add: operator_tensor_iso_inv_def operator_tensor_iso_map_def)
    qed
  qed

  have FG: "\<And>y. y \<in> ls_carrier ?W \<Longrightarrow> ?F (?G y) = y"
  proof -
    fix y
    assume y: "y \<in> ls_carrier ?W"
    then have yc: "y \<in> carrier_mat (m*p) (m*p)"
      by (simp add: bipartite_operator_space_def mat_linear_structure_def)
    show "?F (?G y) = y"
    proof (rule eq_matI)
      show "dim_row (?F (?G y)) = dim_row y"
        using yc by (simp add: operator_tensor_iso_map_def)
      show "dim_col (?F (?G y)) = dim_col y"
        using yc by (simp add: operator_tensor_iso_map_def)
    next
      fix r s
      assume rs: "r < dim_row y" "s < dim_col y"
      then have r: "r < m*p" and s: "s < m*p"
        using yc by auto
      have rdiv: "r div p < m"
        using r p_pos by (simp add: div_less_iff_less_mult)
      have sdiv: "s div p < m"
        using s p_pos by (simp add: div_less_iff_less_mult)
      have rmod: "r mod p < p"
        using p_pos by simp
      have smod: "s mod p < p"
        using p_pos by simp
      have row: "(r div p) * m + (s div p) < m * m"
        using operator_tensor_iso_map_row_bound[OF p_pos r s] .
      have col: "(r mod p) * p + (s mod p) < p * p"
        using operator_tensor_iso_map_col_bound[OF p_pos, of r s] .
      have div_row: "((r div p) * m + (s div p)) div m = r div p"
        using sdiv by simp
      have mod_row: "((r div p) * m + (s div p)) mod m = s div p"
        using sdiv by simp
      have div_col: "((r mod p) * p + (s mod p)) div p = r mod p"
        using smod by simp
      have mod_col: "((r mod p) * p + (s mod p)) mod p = s mod p"
        using smod by simp
      have recomb_r: "(r div p) * p + (r mod p) = r"
        by simp
      have recomb_s: "(s div p) * p + (s mod p) = s"
        by simp
      show "?F (?G y) $$ (r,s) = y $$ (r,s)"
        using r s row col div_row mod_row div_col mod_col recomb_r recomb_s
        by (simp add: operator_tensor_iso_inv_def operator_tensor_iso_map_def)
    qed
  qed

  show ?thesis
    unfolding is_isomorphism_between_def
    using F_linear G_linear GF FG by blast
qed

corollary operator_tensor_space_isomorphic:
  assumes "0 < m" and "0 < p"
  shows "is_isomorphic_to
           (operator_tensor_coordinate_space m p)
           (bipartite_operator_space m p)"
  using operator_tensor_space_isomorphism[OF assms]
  by (auto simp: is_isomorphic_to_def)

(* --------------------------------------------------------------------------
   Section 16.2.  Partial traces.  For X in L(H_A tensor H_B) we define
       tr_B : L(H_A tensor H_B) -> L(H_A),     tr_B(R tensor T) = (Tr T) * R,
       tr_A : L(H_A tensor H_B) -> L(H_B),     tr_A(R tensor T) = (Tr R) * T.
   Concrete implementation: view X as an m*p by m*p matrix indexed by
   pairs (i, k) with i < m, k < p and flat index i*p + k (so H_A is the
   "block" factor and H_B is the "within-block" factor, matching Isabelle's
   tensor convention (A tensor B)$$(r, c) = A$$(r div rB, c div cB) *
   B$$(r mod rB, c mod cB)).  Then
       (tr_B X)$$(i, j) = sum_k < p. X $$ (i*p + k, j*p + k),
       (tr_A X)$$(i, j) = sum_k < m. X $$ (k*p + i, k*p + j).
   -------------------------------------------------------------------------- *)

record 'lab qspace =
  qdim :: nat
  qlabel :: 'lab

record 'lab bipartite_space =
  left_space :: "'lab qspace"
  right_space :: "'lab qspace"

definition partial_trace_B :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "partial_trace_B m p x \<equiv>
     Matrix.mat m m (\<lambda>(i, j). \<Sum>k<p. x $$ (i * p + k, j * p + k))"

definition partial_trace_A :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "partial_trace_A m p x \<equiv>
     Matrix.mat p p (\<lambda>(i, j). \<Sum>k<m. x $$ (k * p + i, k * p + j))"

definition partial_trace_on ::
  "'lab qspace \<Rightarrow> 'lab bipartite_space \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "partial_trace_on s ab x \<equiv>
     (if s = right_space ab then
        partial_trace_B (qdim (left_space ab)) (qdim (right_space ab)) x
      else if s = left_space ab then
        partial_trace_A (qdim (left_space ab)) (qdim (right_space ab)) x
      else 0\<^sub>m 0 0)"

notation partial_trace_on ("tr\<^bsub>_\<^esub>\<^bsup>_\<^esup> _" [1000, 1000, 1000] 1000)

lemma partial_trace_on_right:
  fixes S :: "'lab qspace" and AB :: "'lab bipartite_space"
  assumes "S = right_space AB"
  shows "tr\<^bsub>S\<^esub>\<^bsup>AB\<^esup> x =
         partial_trace_B (qdim (left_space AB)) (qdim (right_space AB)) x"
  using assms by (simp add: partial_trace_on_def)

lemma partial_trace_on_left:
  fixes S :: "'lab qspace" and AB :: "'lab bipartite_space"
  assumes "S = left_space AB"
      and "left_space AB \<noteq> right_space AB"
  shows "tr\<^bsub>S\<^esub>\<^bsup>AB\<^esup> x =
         partial_trace_A (qdim (left_space AB)) (qdim (right_space AB)) x"
  using assms by (simp add: partial_trace_on_def)

lemma dim_row_partial_trace_B [simp]: "dim_row (partial_trace_B m p x) = m"
  by (simp add: partial_trace_B_def)

lemma dim_col_partial_trace_B [simp]: "dim_col (partial_trace_B m p x) = m"
  by (simp add: partial_trace_B_def)

lemma partial_trace_B_carrier [simp]:
  "partial_trace_B m p x \<in> carrier_mat m m"
  by auto

lemma dim_row_partial_trace_A [simp]: "dim_row (partial_trace_A m p x) = p"
  by (simp add: partial_trace_A_def)

lemma dim_col_partial_trace_A [simp]: "dim_col (partial_trace_A m p x) = p"
  by (simp add: partial_trace_A_def)

lemma partial_trace_A_carrier [simp]:
  "partial_trace_A m p x \<in> carrier_mat p p"
  by auto

(* Defining property on elementary tensors. *)

lemma partial_trace_B_tensor:
  fixes R T :: "complex Matrix.mat"
  assumes Rsq: "R \<in> carrier_mat m m"
      and Tsq: "T \<in> carrier_mat p p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "partial_trace_B m p (R \<Otimes> T) = Tr T \<cdot>\<^sub>m R"
proof (rule eq_matI)
  show "dim_row (partial_trace_B m p (R \<Otimes> T)) = dim_row (Tr T \<cdot>\<^sub>m R)"
    using Rsq by simp
  show "dim_col (partial_trace_B m p (R \<Otimes> T)) = dim_col (Tr T \<cdot>\<^sub>m R)"
    using Rsq by simp
next
  fix i j
  assume ij: "i < dim_row (Tr T \<cdot>\<^sub>m R)" "j < dim_col (Tr T \<cdot>\<^sub>m R)"
  from ij Rsq have i_lt: "i < m" and j_lt: "j < m" by auto

  have drR: "dim_row R = m" using Rsq by auto
  have dcR: "dim_col R = m" using Rsq by auto
  have drT: "dim_row T = p" using Tsq by auto
  have dcT: "dim_col T = p" using Tsq by auto

  have ent_eq: "\<And>k. k < p \<Longrightarrow>
                (R \<Otimes> T) $$ (i * p + k, j * p + k) = R $$ (i, j) * T $$ (k, k)"
  proof -
    fix k assume k_lt: "k < p"
    have rb: "i * p + k < m * p"
    proof -
      have "i * p + k < (i + 1) * p" using k_lt by simp
      moreover have "(i + 1) * p \<le> m * p"
      proof -
        have "i + 1 \<le> m" using i_lt by simp
        thus "(i + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have cb: "j * p + k < m * p"
    proof -
      have "j * p + k < (j + 1) * p" using k_lt by simp
      moreover have "(j + 1) * p \<le> m * p"
      proof -
        have "j + 1 \<le> m" using j_lt by simp
        thus "(j + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have dv1: "(i * p + k) div p = i" using k_lt by simp
    have dv2: "(j * p + k) div p = j" using k_lt by simp
    have md1: "(i * p + k) mod p = k" using k_lt by simp
    have md2: "(j * p + k) mod p = k" using k_lt by simp
    have "(R \<Otimes> T) $$ (i * p + k, j * p + k)
          = R $$ ((i*p+k) div p, (j*p+k) div p) * T $$ ((i*p+k) mod p, (j*p+k) mod p)"
      using index_tensor_mat[OF drR dcR drT dcT rb cb m_pos p_pos] .
    also have "\<dots> = R $$ (i, j) * T $$ (k, k)"
      using dv1 dv2 md1 md2 by simp
    finally show "(R \<Otimes> T) $$ (i * p + k, j * p + k) = R $$ (i, j) * T $$ (k, k)" .
  qed

  have "partial_trace_B m p (R \<Otimes> T) $$ (i, j)
        = (\<Sum>k<p. (R \<Otimes> T) $$ (i * p + k, j * p + k))"
    using i_lt j_lt by (simp add: partial_trace_B_def)
  also have "\<dots> = (\<Sum>k<p. R $$ (i, j) * T $$ (k, k))"
    using ent_eq by (intro sum.cong refl) simp
  also have "\<dots> = R $$ (i, j) * (\<Sum>k<p. T $$ (k, k))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = R $$ (i, j) * Tr T"
    using Tsq by (simp add: Tr_def)
  also have "\<dots> = Tr T * R $$ (i, j)"
    by (simp add: mult.commute)
  also have "\<dots> = (Tr T \<cdot>\<^sub>m R) $$ (i, j)"
    using i_lt j_lt Rsq by simp
  finally show "partial_trace_B m p (R \<Otimes> T) $$ (i, j) = (Tr T \<cdot>\<^sub>m R) $$ (i, j)" .
qed

lemma partial_trace_A_tensor:
  fixes R T :: "complex Matrix.mat"
  assumes Rsq: "R \<in> carrier_mat m m"
      and Tsq: "T \<in> carrier_mat p p"
      and m_pos: "0 < m" and p_pos: "0 < p"
  shows "partial_trace_A m p (R \<Otimes> T) = Tr R \<cdot>\<^sub>m T"
proof (rule eq_matI)
  show "dim_row (partial_trace_A m p (R \<Otimes> T)) = dim_row (Tr R \<cdot>\<^sub>m T)"
    using Tsq by simp
  show "dim_col (partial_trace_A m p (R \<Otimes> T)) = dim_col (Tr R \<cdot>\<^sub>m T)"
    using Tsq by simp
next
  fix i j
  assume ij: "i < dim_row (Tr R \<cdot>\<^sub>m T)" "j < dim_col (Tr R \<cdot>\<^sub>m T)"
  from ij Tsq have i_lt: "i < p" and j_lt: "j < p" by auto

  have drR: "dim_row R = m" using Rsq by auto
  have dcR: "dim_col R = m" using Rsq by auto
  have drT: "dim_row T = p" using Tsq by auto
  have dcT: "dim_col T = p" using Tsq by auto

  have ent_eq: "\<And>k. k < m \<Longrightarrow>
                (R \<Otimes> T) $$ (k * p + i, k * p + j) = R $$ (k, k) * T $$ (i, j)"
  proof -
    fix k assume k_lt: "k < m"
    have rb: "k * p + i < m * p"
    proof -
      have "k * p + i < (k + 1) * p" using i_lt by simp
      moreover have "(k + 1) * p \<le> m * p"
      proof -
        have "k + 1 \<le> m" using k_lt by simp
        thus "(k + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have cb: "k * p + j < m * p"
    proof -
      have "k * p + j < (k + 1) * p" using j_lt by simp
      moreover have "(k + 1) * p \<le> m * p"
      proof -
        have "k + 1 \<le> m" using k_lt by simp
        thus "(k + 1) * p \<le> m * p" by (rule mult_le_mono1)
      qed
      ultimately show ?thesis by linarith
    qed
    have dv1: "(k * p + i) div p = k" using i_lt by simp
    have dv2: "(k * p + j) div p = k" using j_lt by simp
    have md1: "(k * p + i) mod p = i" using i_lt by simp
    have md2: "(k * p + j) mod p = j" using j_lt by simp
    have "(R \<Otimes> T) $$ (k * p + i, k * p + j)
          = R $$ ((k*p+i) div p, (k*p+j) div p) * T $$ ((k*p+i) mod p, (k*p+j) mod p)"
      using index_tensor_mat[OF drR dcR drT dcT rb cb m_pos p_pos] .
    also have "\<dots> = R $$ (k, k) * T $$ (i, j)"
      using dv1 dv2 md1 md2 by simp
    finally show "(R \<Otimes> T) $$ (k * p + i, k * p + j) = R $$ (k, k) * T $$ (i, j)" .
  qed

  have "partial_trace_A m p (R \<Otimes> T) $$ (i, j)
        = (\<Sum>k<m. (R \<Otimes> T) $$ (k * p + i, k * p + j))"
    using i_lt j_lt by (simp add: partial_trace_A_def)
  also have "\<dots> = (\<Sum>k<m. R $$ (k, k) * T $$ (i, j))"
    using ent_eq by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>k<m. R $$ (k, k)) * T $$ (i, j)"
    by (simp add: sum_distrib_right)
  also have "\<dots> = Tr R * T $$ (i, j)"
    using Rsq by (simp add: Tr_def)
  also have "\<dots> = (Tr R \<cdot>\<^sub>m T) $$ (i, j)"
    using i_lt j_lt Tsq by simp
  finally show "partial_trace_A m p (R \<Otimes> T) $$ (i, j) = (Tr R \<cdot>\<^sub>m T) $$ (i, j)" .
qed

(* --------------------------------------------------------------------------
   Section 16.3.  Partial traces and measurements (motivation).
   For a bipartite density matrix rho on H_A tensor H_B, an A-side
   measurement system {M_alpha} acts as {M_alpha tensor I_{H_B}}, and
       Tr ((M_alpha-dagger M_alpha) tensor I_{H_B} . rho)
         = Tr ((M_alpha-dagger M_alpha) . tr_B(rho)).
   Thus Lab A only sees rho^A = tr_B(rho).  Existence, uniqueness, and
   density-matrix preservation of the partial trace, together with the
   compatibility theorem above, are taken up in Day 16.
   -------------------------------------------------------------------------- *)


(* ============================================================================
   DAY 16 — 3 / Oct / 11
   Topic: Partial Traces
   ============================================================================ *)

(* The legacy file begins Day 16 by defining partial traces.  In this split
   theory those definitions are already in Section 16.2 above, using the
   flattened index i*p + k for H_A \<otimes> H_B.  We continue with the next
   properties of that construction. *)

lemma partial_trace_B_trace:
  fixes X :: "complex Matrix.mat"
  assumes Xsq: "X \<in> carrier_mat (m * p) (m * p)"
      and p_pos: "0 < p"
  shows "Tr (partial_trace_B m p X) = Tr X"
proof -
  have Xrow: "dim_row X = m * p" and Xcol: "dim_col X = m * p"
    using Xsq by auto

  have bij: "bij_betw (\<lambda>(i, k). i * p + k) ({..<m} \<times> {..<p}) {..<m*p}"
  proof (rule bij_betwI[where g = "\<lambda>r. (r div p, r mod p)"])
    show "(\<lambda>(i, k). i * p + k) \<in> {..<m} \<times> {..<p} \<rightarrow> {..<m*p}"
    proof
      fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
      then obtain i k where z: "z = (i, k)" and i_lt: "i < m" and k_lt: "k < p"
        by blast
      have "i * p + k < (i + 1) * p"
        using k_lt by simp
      moreover have "(i + 1) * p \<le> m * p"
      proof -
        have "i + 1 \<le> m"
          using i_lt by simp
        thus "(i + 1) * p \<le> m * p"
          by (rule mult_le_mono1)
      qed
      ultimately have "i * p + k < m * p"
        by linarith
      thus "(case z of (i, k) \<Rightarrow> i * p + k) \<in> {..<m*p}"
        using z by simp
    qed
  next
    show "(\<lambda>r. (r div p, r mod p)) \<in> {..<m*p} \<rightarrow> {..<m} \<times> {..<p}"
      using p_pos by (auto simp: less_mult_imp_div_less)
  next
    fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
    then obtain i k where z: "z = (i, k)" and k_lt: "k < p"
      by blast
    show "(\<lambda>r. (r div p, r mod p)) ((\<lambda>(i, k). i * p + k) z) = z"
      using z k_lt by simp
  next
    fix r assume r_in: "r \<in> {..<m*p}"
    show "(\<lambda>(i, k). i * p + k) ((\<lambda>r. (r div p, r mod p)) r) = r"
      by simp
  qed

  have "Tr (partial_trace_B m p X) =
        (\<Sum>i<m. partial_trace_B m p X $$ (i, i))"
    by (simp add: Tr_def)
  also have "\<dots> = (\<Sum>i<m. \<Sum>k<p. X $$ (i * p + k, i * p + k))"
    by (intro sum.cong refl) (simp add: partial_trace_B_def)
  also have "\<dots> = (\<Sum>(i, k) \<in> {..<m} \<times> {..<p}. X $$ (i * p + k, i * p + k))"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>r<m*p. X $$ (r, r))"
    using sum.reindex_bij_betw[OF bij, symmetric, of "\<lambda>r. X $$ (r, r)"]
    by (simp add: case_prod_beta)
  also have "\<dots> = Tr X"
    using Xrow Xcol by (simp add: Tr_def)
  finally show ?thesis .
qed

lemma partial_trace_B_hermitian:
  fixes X :: "complex Matrix.mat"
  assumes Xsq: "X \<in> carrier_mat (m * p) (m * p)"
      and herm: "hermitian X"
  shows "hermitian (partial_trace_B m p X)"
proof -
  have Xrow: "dim_row X = m * p" and Xcol: "dim_col X = m * p"
    using Xsq by auto
  have entry:
    "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow>
      partial_trace_B m p X $$ (i, j) =
      cnj (partial_trace_B m p X $$ (j, i))"
  proof -
    fix i j assume i_lt: "i < m" and j_lt: "j < m"
    have "partial_trace_B m p X $$ (i, j) =
          (\<Sum>k<p. X $$ (i * p + k, j * p + k))"
      using i_lt j_lt by (simp add: partial_trace_B_def)
    also have "\<dots> = (\<Sum>k<p. cnj (X $$ (j * p + k, i * p + k)))"
    proof (intro sum.cong refl)
      fix k assume k_mem: "k \<in> {..<p}"
      then have k_lt: "k < p" by simp
      have row_lt: "i * p + k < m * p"
      proof -
        have "i * p + k < (i + 1) * p" using k_lt by simp
        moreover have "(i + 1) * p \<le> m * p"
        proof -
          have "i + 1 \<le> m" using i_lt by simp
          thus "(i + 1) * p \<le> m * p" by (rule mult_le_mono1)
        qed
        ultimately show ?thesis by linarith
      qed
      have col_lt: "j * p + k < m * p"
      proof -
        have "j * p + k < (j + 1) * p" using k_lt by simp
        moreover have "(j + 1) * p \<le> m * p"
        proof -
          have "j + 1 \<le> m" using j_lt by simp
          thus "(j + 1) * p \<le> m * p" by (rule mult_le_mono1)
        qed
        ultimately show ?thesis by linarith
      qed
      show "X $$ (i * p + k, j * p + k) =
            cnj (X $$ (j * p + k, i * p + k))"
      proof -
        have Xdag: "X\<^sup>\<dagger> = X"
          using herm by (simp add: hermitian_def)
        have "X $$ (i * p + k, j * p + k) =
              X\<^sup>\<dagger> $$ (i * p + k, j * p + k)"
          using Xdag by simp
        also have "\<dots> = cnj (X $$ (j * p + k, i * p + k))"
          using Xrow Xcol row_lt col_lt by (simp add: dagger_def)
        finally show ?thesis .
      qed
    qed
    also have "\<dots> = cnj (\<Sum>k<p. X $$ (j * p + k, i * p + k))"
      by simp
    also have "\<dots> = cnj (partial_trace_B m p X $$ (j, i))"
      using i_lt j_lt by (simp add: partial_trace_B_def)
    finally show "partial_trace_B m p X $$ (i, j) =
                  cnj (partial_trace_B m p X $$ (j, i))" .
  qed
  show ?thesis
    unfolding hermitian_def
  proof (rule eq_matI)
    show "dim_row ((partial_trace_B m p X)\<^sup>\<dagger>) = dim_row (partial_trace_B m p X)"
      by simp
    show "dim_col ((partial_trace_B m p X)\<^sup>\<dagger>) = dim_col (partial_trace_B m p X)"
      by simp
  next
    fix i j
    assume ij: "i < dim_row (partial_trace_B m p X)" "j < dim_col (partial_trace_B m p X)"
    then have i_lt: "i < m" and j_lt: "j < m"
      by simp_all
    show "(partial_trace_B m p X)\<^sup>\<dagger> $$ (i, j) =
          partial_trace_B m p X $$ (i, j)"
      using i_lt j_lt entry[OF i_lt j_lt] entry[OF j_lt i_lt]
      by (simp add: dagger_def)
  qed
qed

(* Partial trace of a density matrix is a density matrix.  The carrier, trace,
   and Hermitian parts are now explicit; the remaining mathematical content is
   positivity of the block trace. *)

lemma partial_trace_B_is_density:
  fixes X :: "complex Matrix.mat"
  assumes dm: "density_matrix (m * p) X"
      and p_pos: "0 < p"
  shows "density_matrix m (partial_trace_B m p X)"
proof -
  have Xsq: "X \<in> carrier_mat (m * p) (m * p)"
    using dm by (auto simp: density_matrix_def)
  have Xpsd: "psd X"
    using dm by (auto simp: density_matrix_def)
  have Xherm: "hermitian X"
    using Xpsd by (rule psd_hermitian)
  have carr: "partial_trace_B m p X \<in> carrier_mat m m"
    by simp
  have herm: "hermitian (partial_trace_B m p X)"
    using partial_trace_B_hermitian[OF Xsq Xherm] .
  have nonneg:
    "\<And>v. dim_vec v = m \<Longrightarrow> Re \<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle> \<ge> 0"
  proof -
    fix v :: "complex Matrix.vec"
    assume vdim: "dim_vec v = m"

    define wk where wk_def:
      "wk k = Matrix.vec (m * p) (\<lambda>t. if t mod p = k then v $ (t div p) else 0)"

    have wk_dim: "\<And>k. dim_vec (wk k) = m * p"
      using \<open>wk \<equiv> \<lambda>k. Matrix.vec (m * p) (\<lambda>t. if t mod p = k then v $ (t div p) else 0)\<close> 
        dim_vec by blast

    have wk_nonneg:
      "\<And>k. k < p \<Longrightarrow> Re \<langle>wk k | X *\<^sub>v wk k\<rangle> \<ge> 0"
      using Xpsd
      unfolding psd_def
      using Xsq wk_dim by fastforce

    have pt_expand:
      "\<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle>
       = (\<Sum>k<p. \<langle>wk k | X *\<^sub>v wk k\<rangle>)"
    proof -
      have lhs_entry:
        "\<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle>
         = (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) *
              (partial_trace_B m p X $$ (i,j)) * (v $ j))"
        using vdim
        unfolding inner_prod_def scalar_prod_def
        using atLeast0LessThan inner_T_double_sum inner_prod_def by auto

      also have "... =
         (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) *
            (\<Sum>k<p. X $$ (i * p + k, j * p + k)) * (v $ j))"
        using Xsq
        unfolding partial_trace_B_def
        by simp

      also have "... =
         (\<Sum>i<m. \<Sum>j<m. \<Sum>k<p.
             cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))"
        by (simp add: sum_distrib_left sum_distrib_right mult.assoc)

      also have "... =
         (\<Sum>i<m. \<Sum>k<p. \<Sum>j<m.
             cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))"
        by (intro sum.cong[OF refl] sum.swap)

      also have "... =
         (\<Sum>k<p. \<Sum>i<m. \<Sum>j<m.
             cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))"
        by (rule sum.swap)

      also have "... = (\<Sum>k<p. \<langle>wk k | X *\<^sub>v wk k\<rangle>)"
      proof (rule sum.cong[OF refl])
        fix k
        assume "k \<in> {..<p}"
        then have k_lt: "k < p"
          by simp

        have ipk_lt: "\<And>i. i < m \<Longrightarrow> i * p + k < m * p"
        proof -
          fix i :: nat
          assume i_lt: "i < m"
          have "i * p + k < i * p + p" using k_lt by simp
          also have "\<dots> = (i + 1) * p" by simp
          also have "\<dots> \<le> m * p"
            using i_lt by (intro mult_le_mono1) simp
          finally show "i * p + k < m * p" .
        qed

        have wk_eval:
          "\<And>a. a < m * p \<Longrightarrow>
                 (wk k) $ a = (if a mod p = k then v $ (a div p) else 0)"
          using \<open>wk \<equiv> \<lambda>k. Matrix.vec (m * p) (\<lambda>t. if t mod p = k then v $ (t div p) else 0)\<close>
          by simp

        have wk_at: "\<And>i. i < m \<Longrightarrow> (wk k) $ (i * p + k) = v $ i"
        proof -
          fix i :: nat assume i_lt: "i < m"
          have bnd: "i * p + k < m * p" using ipk_lt[OF i_lt] .
          have md: "(i * p + k) mod p = k" using k_lt by simp
          have dv: "(i * p + k) div p = i" using k_lt by simp
          show "(wk k) $ (i * p + k) = v $ i"
            using wk_eval[OF bnd] md dv by simp
        qed

        have wk_zero:
          "\<And>a. a < m * p \<Longrightarrow> a mod p \<noteq> k \<Longrightarrow> (wk k) $ a = 0"
          using wk_eval by simp

        have inj_ipk: "inj_on (\<lambda>i. i * p + k) {..<m}"
          using p_pos by (auto simp: inj_on_def)

        have B_eq:
          "(\<lambda>i. i * p + k) ` {..<m} = {a. a < m * p \<and> a mod p = k}"
        proof (intro equalityI subsetI)
          fix x assume "x \<in> (\<lambda>i. i * p + k) ` {..<m}"
          then obtain i where x_eq: "x = i * p + k" and i_lt: "i < m"
            by auto
          have "x < m * p" using ipk_lt[OF i_lt] x_eq by simp
          moreover have "x mod p = k" using x_eq k_lt by simp
          ultimately show "x \<in> {a. a < m * p \<and> a mod p = k}" by simp
        next
          fix x assume "x \<in> {a. a < m * p \<and> a mod p = k}"
          then have x_lt: "x < m * p" and x_mod: "x mod p = k" by auto
          have div_lt: "x div p < m"
            using x_lt p_pos less_mult_imp_div_less by blast
          have x_eq: "x = (x div p) * p + k"
            using x_mod by (metis div_mult_mod_eq)
          from div_lt x_eq show "x \<in> (\<lambda>i. i * p + k) ` {..<m}"
            by (auto intro!: image_eqI)
        qed

        let ?B = "{a. a < m * p \<and> a mod p = k}"

        have B_subset: "?B \<subseteq> {..<m * p}" by auto

        have idx:
          "\<langle>wk k | X *\<^sub>v wk k\<rangle>
           = (\<Sum>a<m*p. \<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))"
          unfolding inner_prod_def scalar_prod_def
          using wk_dim[of k] Xsq inner_T_double_sum inner_prod_def lessThan_atLeast0
          by auto

        also have "\<dots> =
           (\<Sum>a \<in> ?B. \<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))"
        proof (rule sum.mono_neutral_right)
          show "finite {..<m * p}" by simp
          show "?B \<subseteq> {..<m * p}" by auto
          show "\<forall>a \<in> {..<m * p} - ?B.
                  (\<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b)) = 0"
          proof
            fix a assume "a \<in> {..<m * p} - ?B"
            then have a_lt: "a < m * p" and a_md: "a mod p \<noteq> k" by auto
            hence "(wk k) $ a = 0" using wk_zero by simp
            thus "(\<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b)) = 0"
              by simp
          qed
        qed

        also have "\<dots> =
           (\<Sum>a \<in> ?B. \<Sum>b \<in> ?B. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))"
        proof (rule sum.cong[OF refl])
          fix a assume "a \<in> ?B"
          show "(\<Sum>b<m*p. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))
               = (\<Sum>b \<in> ?B. cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b))"
          proof (rule sum.mono_neutral_right)
            show "finite {..<m * p}" by simp
            show "?B \<subseteq> {..<m * p}" by auto
            show "\<forall>b \<in> {..<m * p} - ?B.
                    cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b) = 0"
            proof
              fix b assume "b \<in> {..<m * p} - ?B"
              then have b_lt: "b < m * p" and b_md: "b mod p \<noteq> k" by auto
              hence "(wk k) $ b = 0" using wk_zero by simp
              thus "cnj ((wk k) $ a) * X $$ (a,b) * ((wk k) $ b) = 0"
                by simp
            qed
          qed
        qed

        also have "\<dots> =
           (\<Sum>i<m. \<Sum>j<m.
              cnj ((wk k) $ (i * p + k)) * X $$ (i * p + k, j * p + k)
              * ((wk k) $ (j * p + k)))"
          using B_eq[symmetric] inj_ipk
          by (simp add: sum.reindex)

        also have "\<dots> =
           (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))"
          using wk_at by (intro sum.cong refl) simp

        finally have wk_eq:
          "\<langle>wk k | X *\<^sub>v wk k\<rangle>
           = (\<Sum>i<m. \<Sum>j<m. cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))" .

        show
          "(\<Sum>i<m. \<Sum>j<m. cnj (v $ i) * X $$ (i * p + k, j * p + k) * (v $ j))
           = \<langle>wk k | X *\<^sub>v wk k\<rangle>"
          using wk_eq by simp
      qed

      finally show ?thesis .
    qed

    have "Re \<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle>
          = Re (\<Sum>k<p. \<langle>wk k | X *\<^sub>v wk k\<rangle>)"
      using pt_expand by simp
    also have "... = (\<Sum>k<p. Re \<langle>wk k | X *\<^sub>v wk k\<rangle>)"
      by simp
    also have "... \<ge> 0"
      using wk_nonneg
      by (meson lessThan_iff sum_nonneg) 
    finally show "Re \<langle>v | partial_trace_B m p X *\<^sub>v v\<rangle> \<ge> 0".
  qed

  have psd: "psd (partial_trace_B m p X)"
    unfolding psd_def using herm nonneg by simp
  have tr: "Tr (partial_trace_B m p X) = 1"
    using partial_trace_B_trace[OF Xsq p_pos] dm
    by (simp add: density_matrix_def)
  show ?thesis
    unfolding density_matrix_def using carr psd tr by simp
qed

(* Key identity: measurements in Lab A only see rho_A = tr_B(rho). *)

theorem partial_trace_measurement:
  fixes meas :: "complex Matrix.mat" and \<rho> :: "complex Matrix.mat"
  assumes M_sq: "meas \<in> carrier_mat m m"
      and dm: "density_matrix (m * p) \<rho>"
      and p_pos: "0 < p"
  shows "Tr (((meas\<^sup>\<dagger> * meas) \<Otimes> 1\<^sub>m p) * \<rho>) =
         Tr (meas\<^sup>\<dagger> * meas * partial_trace_B m p \<rho>)"
proof -
  define M where M_def: "M = meas\<^sup>\<dagger> * meas"

  have rho_carr: "\<rho> \<in> carrier_mat (m * p) (m * p)"
    using dm by (auto simp: density_matrix_def)
  have rho_row: "dim_row \<rho> = m * p" and rho_col: "dim_col \<rho> = m * p"
    using rho_carr by auto

  have Mdag_carr: "meas\<^sup>\<dagger> \<in> carrier_mat m m"
    using M_sq by auto
  have M_carr: "M \<in> carrier_mat m m"
    unfolding M_def using Mdag_carr M_sq by simp
  have M_row: "dim_row M = m" and M_col: "dim_col M = m"
    using M_carr by auto

  have I_row: "dim_row (1\<^sub>m p :: complex Matrix.mat) = p"
   and I_col: "dim_col (1\<^sub>m p :: complex Matrix.mat) = p"
    by simp_all

  have MI_carr: "(M \<Otimes> 1\<^sub>m p) \<in> carrier_mat (m * p) (m * p)"
    using M_carr by simp
  have MI_row: "dim_row (M \<Otimes> 1\<^sub>m p) = m * p"
   and MI_col: "dim_col (M \<Otimes> 1\<^sub>m p) = m * p"
    using MI_carr by auto

  have ptB_carr: "partial_trace_B m p \<rho> \<in> carrier_mat m m"
    by simp

  have main_eq:
    "Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>) = Tr (M * partial_trace_B m p \<rho>)"
  proof (cases "m = 0")
    case True
    have lhs0: "Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>) = 0"
      using True MI_carr rho_carr by (simp add: Tr_def)
    have rhs0: "Tr (M * partial_trace_B m p \<rho>) = 0"
      using True M_carr ptB_carr by (simp add: Tr_def)
    show ?thesis using lhs0 rhs0 by simp
  next
    case False
    then have m_pos: "0 < m" by simp

    have bij: "bij_betw (\<lambda>(i, a). i * p + a) ({..<m} \<times> {..<p}) {..<m * p}"
    proof (rule bij_betwI[where g = "\<lambda>r. (r div p, r mod p)"])
      show "(\<lambda>(i, a). i * p + a) \<in> {..<m} \<times> {..<p} \<rightarrow> {..<m * p}"
      proof
        fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
        then obtain i a where z: "z = (i, a)" and i_lt: "i < m" and a_lt: "a < p"
          by blast
        have "i * p + a < (i + 1) * p" using a_lt by simp
        moreover have "(i + 1) * p \<le> m * p"
          using i_lt by (intro mult_le_mono1) simp
        ultimately have "i * p + a < m * p" by linarith
        thus "(case z of (i, a) \<Rightarrow> i * p + a) \<in> {..<m * p}"
          using z by simp
      qed
    next
      show "(\<lambda>r. (r div p, r mod p)) \<in> {..<m * p} \<rightarrow> {..<m} \<times> {..<p}"
        using p_pos by (auto simp: less_mult_imp_div_less)
    next
      fix z assume z_in: "z \<in> {..<m} \<times> {..<p}"
      then obtain i a where z: "z = (i, a)" and a_lt: "a < p" by blast
      show "(\<lambda>r. (r div p, r mod p)) ((\<lambda>(i, a). i * p + a) z) = z"
        using z a_lt by simp
    next
      fix r assume "r \<in> {..<m * p}"
      show "(\<lambda>(i, a). i * p + a) ((\<lambda>r. (r div p, r mod p)) r) = r"
        by simp
    qed

    have ipa_lt: "\<And>i a. i < m \<Longrightarrow> a < p \<Longrightarrow> i * p + a < m * p"
    proof -
      fix i a :: nat assume i_lt: "i < m" and a_lt: "a < p"
      have "i * p + a < (i + 1) * p" using a_lt by simp
      also have "\<dots> \<le> m * p" using i_lt by (intro mult_le_mono1) simp
      finally show "i * p + a < m * p" .
    qed

    have tens_entry:
      "\<And>i a j b. i < m \<Longrightarrow> a < p \<Longrightarrow> j < m \<Longrightarrow> b < p \<Longrightarrow>
         (M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
         = M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)"
    proof -
      fix i a j b :: nat
      assume i_lt: "i < m" and a_lt: "a < p"
         and j_lt: "j < m" and b_lt: "b < p"
      have rb: "i * p + a < m * p" using ipa_lt[OF i_lt a_lt] .
      have cb: "j * p + b < m * p" using ipa_lt[OF j_lt b_lt] .
      have dv1: "(i * p + a) div p = i" using a_lt by simp
      have dv2: "(j * p + b) div p = j" using b_lt by simp
      have md1: "(i * p + a) mod p = a" using a_lt by simp
      have md2: "(j * p + b) mod p = b" using b_lt by simp
      have "(M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
            = M $$ ((i*p+a) div p, (j*p+b) div p)
              * (1\<^sub>m p :: complex Matrix.mat) $$ ((i*p+a) mod p, (j*p+b) mod p)"
        using index_tensor_mat[OF M_row M_col I_row I_col rb cb m_pos p_pos] .
      also have "\<dots> = M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)"
        using dv1 dv2 md1 md2 by simp
      finally show "(M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
                    = M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)" .
    qed

    have prod_carr: "(M \<Otimes> 1\<^sub>m p) * \<rho> \<in> carrier_mat (m * p) (m * p)"
      using MI_carr rho_carr by simp

    have "Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>)
          = (\<Sum>r < m * p. ((M \<Otimes> 1\<^sub>m p) * \<rho>) $$ (r, r))"
      using prod_carr M_row rho_col by (simp add: Tr_def)

    also have "\<dots> = (\<Sum>r < m * p. \<Sum>s < m * p.
                       (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))"
    proof (intro sum.cong refl)
      fix r assume "r \<in> {..<m * p}"
      then have r_lt: "r < m * p" by simp
      have "((M \<Otimes> 1\<^sub>m p) * \<rho>) $$ (r, r) = Matrix.row (M \<Otimes> 1\<^sub>m p) r \<bullet> Matrix.col \<rho> r"
        using r_lt MI_carr rho_carr by force
      also have "\<dots> = (\<Sum>s < m * p. (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))"
        using r_lt MI_carr rho_carr MI_col MI_row
        by (simp add: scalar_prod_def lessThan_atLeast0, force)
      finally show "((M \<Otimes> 1\<^sub>m p) * \<rho>) $$ (r, r)
                    = (\<Sum>s < m * p. (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))".
    qed
    also have "\<dots> = (\<Sum>r < m * p. \<Sum>(j, b) \<in> {..<m} \<times> {..<p}.
                       (M \<Otimes> 1\<^sub>m p) $$ (r, j * p + b) * \<rho> $$ (j * p + b, r))"
    proof (intro sum.cong refl)
      fix r assume "r \<in> {..<m * p}"
      show "(\<Sum>s < m * p. (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r))
            = (\<Sum>(j, b) \<in> {..<m} \<times> {..<p}.
                 (M \<Otimes> 1\<^sub>m p) $$ (r, j * p + b) * \<rho> $$ (j * p + b, r))"
        using sum.reindex_bij_betw[OF bij, symmetric,
                of "\<lambda>s. (M \<Otimes> 1\<^sub>m p) $$ (r, s) * \<rho> $$ (s, r)"]
        by (simp add: case_prod_beta)
    qed

    also have "\<dots> = (\<Sum>(i, a) \<in> {..<m} \<times> {..<p}. \<Sum>(j, b) \<in> {..<m} \<times> {..<p}.
                       (M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
                       * \<rho> $$ (j * p + b, i * p + a))"
      using sum.reindex_bij_betw[OF bij, symmetric,
              of "\<lambda>r. \<Sum>(j, b) \<in> {..<m} \<times> {..<p}.
                        (M \<Otimes> 1\<^sub>m p) $$ (r, j * p + b) * \<rho> $$ (j * p + b, r)"]
      by (simp add: case_prod_beta)

    also have "\<dots> = (\<Sum>i < m. \<Sum>a < p. \<Sum>j < m. \<Sum>b < p.
                       (M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
                       * \<rho> $$ (j * p + b, i * p + a))"
      by (simp add: sum.cartesian_product[symmetric])

    also have "\<dots> = (\<Sum>i < m. \<Sum>a < p. \<Sum>j < m. \<Sum>b < p.
                       M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)
                       * \<rho> $$ (j * p + b, i * p + a))"
    proof (intro sum.cong refl)
      fix i a j b
      assume "i \<in> {..<m}" "a \<in> {..<p}" "j \<in> {..<m}" "b \<in> {..<p}"
      then have "i < m" "a < p" "j < m" "b < p" by simp_all
      thus "(M \<Otimes> 1\<^sub>m p) $$ (i * p + a, j * p + b)
            * \<rho> $$ (j * p + b, i * p + a)
            = M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)
              * \<rho> $$ (j * p + b, i * p + a)"
        using tens_entry by simp
    qed

    also have "\<dots> = (\<Sum>i < m. \<Sum>a < p. \<Sum>j < m.
                       M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))"
    proof (intro sum.cong refl)
      fix i a j
      assume "i \<in> {..<m}" "a \<in> {..<p}" "j \<in> {..<m}"
      then have i_lt: "i < m" and a_lt: "a < p" and j_lt: "j < m"
        by simp_all
      have "(\<Sum>b < p. M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)
                       * \<rho> $$ (j * p + b, i * p + a))
            = (\<Sum>b < p. (if a = b
                          then M $$ (i, j) * \<rho> $$ (j * p + b, i * p + a)
                          else 0))"
        using a_lt by (intro sum.cong refl) auto
      also have "\<dots> = (\<Sum>b < p. (if a = b
                                  then M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a)
                                  else 0))"
        by (intro sum.cong refl) auto
      also have "\<dots> = M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a)"
        using a_lt by (simp add: sum.delta)
      finally show "(\<Sum>b < p. M $$ (i, j) * (1\<^sub>m p :: complex Matrix.mat) $$ (a, b)
                       * \<rho> $$ (j * p + b, i * p + a))
                    = M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a)".
    qed

    also have "\<dots> = (\<Sum>i < m. \<Sum>j < m. \<Sum>a < p.
                       M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..<m}"
      show "(\<Sum>a < p. \<Sum>j < m. M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))
            = (\<Sum>j < m. \<Sum>a < p. M $$ (i, j) * \<rho> $$ (j * p + a, i * p + a))"
        by (rule sum.swap)
    qed
    also have "\<dots> = (\<Sum>i < m. \<Sum>j < m.
                       M $$ (i, j) * (\<Sum>a < p. \<rho> $$ (j * p + a, i * p + a)))"
      by (simp add: sum_distrib_left)

    also have "\<dots> = (\<Sum>i < m. \<Sum>j < m.
                       M $$ (i, j) * partial_trace_B m p \<rho> $$ (j, i))"
      by (intro sum.cong refl) (simp add: partial_trace_B_def)

    also have "\<dots> = (\<Sum>i < m. (M * partial_trace_B m p \<rho>) $$ (i, i))"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {..<m}"
      then have i_lt: "i < m" by simp
      have "(M * partial_trace_B m p \<rho>) $$ (i, i)
            = (\<Sum>j < m. M $$ (i, j) * partial_trace_B m p \<rho> $$ (j, i))"
        using i_lt M_carr ptB_carr
        by (simp add: scalar_prod_def lessThan_atLeast0)
      thus "(\<Sum>j < m. M $$ (i, j) * partial_trace_B m p \<rho> $$ (j, i))
            = (M * partial_trace_B m p \<rho>) $$ (i, i)"
        by simp
    qed

    also have "\<dots> = Tr (M * partial_trace_B m p \<rho>)"
      using M_carr ptB_carr by (simp add: Tr_def)

    finally show "Tr ((M \<Otimes> 1\<^sub>m p) * \<rho>) = Tr (M * partial_trace_B m p \<rho>)".
  qed

  show ?thesis
    using main_eq by (simp add: M_def)
qed

(* ============================================================================
   DAY 17 — Measurement Maps
   Topic: M(\<rho>) = \<Sum>_\<alpha> M_\<alpha> \<rho> M_\<alpha>\<^sup>\<dagger> sends density matrices to density matrices.
   ============================================================================ *)

definition meas_map :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "meas_map Ms \<rho> \<equiv>
     foldr (\<lambda>M acc. M * \<rho> * (M\<^sup>\<dagger>) + acc) Ms (0\<^sub>m (dim_row \<rho>) (dim_col \<rho>))"

lemma meas_map_Nil [simp]:
  "meas_map [] \<rho> = 0\<^sub>m (dim_row \<rho>) (dim_col \<rho>)"
  by (simp add: meas_map_def)

lemma meas_map_Cons [simp]:
  "meas_map (M # Ms) \<rho> = M * \<rho> * (M\<^sup>\<dagger>) + meas_map Ms \<rho>"
  by (simp add: meas_map_def)

lemma meas_map_carrier:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "meas_map Ms \<rho> \<in> carrier_mat n n"
  using Ms_c
proof (induction Ms)
  case Nil
  show ?case using \<rho>_c by simp
next
  case (Cons M Ms)
  hence M_c: "M \<in> carrier_mat n n" and Ms_c': "\<forall>X \<in> set Ms. X \<in> carrier_mat n n"
    by auto
  have Mdag_c: "M\<^sup>\<dagger> \<in> carrier_mat n n"
    using M_c
    by (simp add: dagger_def) 
  have term_c: "M * \<rho> * (M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c \<rho>_c Mdag_c by simp
  have rec_c: "meas_map Ms \<rho> \<in> carrier_mat n n"
    using Cons.IH Ms_c' by blast
  show ?case
    using term_c rec_c by simp
qed

lemma dagger_carrier:
  assumes "M \<in> carrier_mat m n"
  shows "(M\<^sup>\<dagger>) \<in> carrier_mat n m"
  using assms
  by (simp add: dagger_def) 

lemma meas_map_psd:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
      and \<rho>_psd: "psd \<rho>"
  shows "psd (meas_map Ms \<rho>)"
  using Ms_c
proof (induction Ms)
  case Nil
  have "meas_map [] \<rho> = 0\<^sub>m n n" using \<rho>_c by simp
  thus ?case using psd_zero_mat by simp
next
  case (Cons M Ms)
  hence M_c: "M \<in> carrier_mat n n" and Ms_c': "\<forall>X \<in> set Ms. X \<in> carrier_mat n n"
    by auto
  have Mdag_c: "(M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c by (rule dagger_carrier)
  obtain Q where Qc: "Q \<in> carrier_mat n n" and Qpsd: "psd Q" and QQ: "Q * Q = \<rho>"
    using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
  have Qdag: "(Q\<^sup>\<dagger>) = Q" using Qpsd by (simp add: psd_def hermitian_def)
  have MQ_c: "M * Q \<in> carrier_mat n n"
    using M_c Qc by (intro mult_carrier_mat) auto
  have MQdag_c: "((M * Q)\<^sup>\<dagger>) \<in> carrier_mat n n"
    using MQ_c by (rule dagger_carrier)

  have term_eq: "M * \<rho> * (M\<^sup>\<dagger>) = (M * Q) * ((M * Q)\<^sup>\<dagger>)"
  proof -
    have dagprod: "((M * Q)\<^sup>\<dagger>) = (Q\<^sup>\<dagger>) * (M\<^sup>\<dagger>)"
      using M_c Qc by (simp add: dagger_of_prod)
    have dagprod': "((M * Q)\<^sup>\<dagger>) = Q * (M\<^sup>\<dagger>)"
      using dagprod Qdag by simp
    have a1: "(M * Q) * ((M * Q)\<^sup>\<dagger>) = (M * Q) * (Q * (M\<^sup>\<dagger>))"
      using dagprod' by simp
    have a2: "(M * Q) * (Q * (M\<^sup>\<dagger>)) = M * Q * Q * (M\<^sup>\<dagger>)"
      using M_c Qc Mdag_c
      by (metis assoc_mult_mat mult_carrier_mat)
    have a3: "M * Q * Q * (M\<^sup>\<dagger>) = M * (Q * Q) * (M\<^sup>\<dagger>)"
      using M_c Qc by (metis assoc_mult_mat)
    have a4: "M * (Q * Q) * (M\<^sup>\<dagger>) = M * \<rho> * (M\<^sup>\<dagger>)" using QQ by simp
    show ?thesis using a1 a2 a3 a4 by simp
  qed

  have term_psd: "psd (M * \<rho> * (M\<^sup>\<dagger>))"
  proof -
    have psd_dd: "psd (((M * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((M * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF MQdag_c] .
    have dd_eq: "((M * Q)\<^sup>\<dagger>\<^sup>\<dagger>) = M * Q"
      using MQ_c by (simp add: dagger_of_dagger_is_id)
    from psd_dd dd_eq have "psd ((M * Q) * ((M * Q)\<^sup>\<dagger>))" by simp
    thus ?thesis using term_eq by simp
  qed
  have term_c: "M * \<rho> * (M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c \<rho>_c Mdag_c by (intro mult_carrier_mat) auto
  have IH_c: "meas_map Ms \<rho> \<in> carrier_mat n n"
    using meas_map_carrier[OF Ms_c' \<rho>_c] .
  have IH_psd: "psd (meas_map Ms \<rho>)"
    using Cons.IH Ms_c' by blast
  have "psd (M * \<rho> * (M\<^sup>\<dagger>) + meas_map Ms \<rho>)"
    using term_psd IH_psd term_c IH_c by (rule psd_add_psd)
  thus ?case by simp
qed

lemma foldr_MdagM_carrier:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
  shows "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) \<in> carrier_mat n n"
  using Ms_c
proof (induction Ms)
  case Nil
  show ?case by simp
next
  case (Cons K Ks)
  hence K_c: "K \<in> carrier_mat n n" and Ks_c: "\<forall>X \<in> set Ks. X \<in> carrier_mat n n"
    by auto
  have Kdag_c: "(K\<^sup>\<dagger>) \<in> carrier_mat n n" using K_c by (rule dagger_carrier)
  have KdK_c: "(K\<^sup>\<dagger>) * K \<in> carrier_mat n n"
    using Kdag_c K_c by (intro mult_carrier_mat) auto
  have rec_c: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ks (0\<^sub>m n n) \<in> carrier_mat n n"
    using Cons.IH Ks_c by blast
  show ?case using KdK_c rec_c by simp
qed

lemma meas_map_trace_aux:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "Tr (meas_map Ms \<rho>) =
         Tr (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) * \<rho>)"
  using Ms_c
proof (induction Ms)
  case Nil
  have lhs: "Tr (meas_map [] \<rho>) = 0"
    using \<rho>_c by (simp add: Tr_def)
  have "(0\<^sub>m n n :: complex Matrix.mat) * \<rho> = 0\<^sub>m n n"
    using \<rho>_c by simp
  hence rhs: "Tr ((0\<^sub>m n n :: complex Matrix.mat) * \<rho>) = 0"
    by (simp add: Tr_def)
  show ?case using lhs rhs by simp
next
  case (Cons M Ms)
  hence M_c: "M \<in> carrier_mat n n" and Ms_c': "\<forall>X \<in> set Ms. X \<in> carrier_mat n n"
    by auto
  have Mdag_c: "(M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c by (rule dagger_carrier)
  have MdM_c: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n"
    using Mdag_c M_c by (intro mult_carrier_mat) auto
  have MrM_c: "M * \<rho> * (M\<^sup>\<dagger>) \<in> carrier_mat n n"
    using M_c \<rho>_c Mdag_c by (intro mult_carrier_mat) auto
  have IH_carr: "meas_map Ms \<rho> \<in> carrier_mat n n"
    using meas_map_carrier[OF Ms_c' \<rho>_c] .
  define S where S_def:
    "S = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)"
  have S_carr: "S \<in> carrier_mat n n"
    unfolding S_def using foldr_MdagM_carrier[OF Ms_c'].

  have IH: "Tr (meas_map Ms \<rho>) = Tr (S * \<rho>)"
    using Cons.IH[OF Ms_c'] by (simp add: S_def)

  have step_a: "Tr (M * \<rho> * (M\<^sup>\<dagger>)) = Tr ((M\<^sup>\<dagger>) * M * \<rho>)"
  proof -
    have "Tr (M * \<rho> * (M\<^sup>\<dagger>)) = Tr ((M\<^sup>\<dagger>) * (M * \<rho>))"
      using M_c \<rho>_c Mdag_c by (intro Tr_cyclic) auto
    also have "\<dots> = Tr ((M\<^sup>\<dagger>) * M * \<rho>)"
      using Mdag_c M_c \<rho>_c by (metis assoc_mult_mat)
    finally show ?thesis .
  qed

  have "Tr (meas_map (M # Ms) \<rho>) = Tr (M * \<rho> * (M\<^sup>\<dagger>) + meas_map Ms \<rho>)"
    by simp
  also have "\<dots> = Tr (M * \<rho> * (M\<^sup>\<dagger>)) + Tr (meas_map Ms \<rho>)"
    using MrM_c IH_carr by (intro Tr_add) auto
  also have "\<dots> = Tr ((M\<^sup>\<dagger>) * M * \<rho>) + Tr (S * \<rho>)"
    using step_a IH by simp
  also have "\<dots> = Tr (((M\<^sup>\<dagger>) * M) * \<rho> + S * \<rho>)"
    using MdM_c S_carr \<rho>_c by (intro Tr_add[symmetric]) auto
  also have "\<dots> = Tr (((M\<^sup>\<dagger>) * M + S) * \<rho>)"
    using MdM_c S_carr \<rho>_c by (simp add: add_mult_distrib_mat)
  also have "\<dots> = Tr (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (M # Ms) (0\<^sub>m n n) * \<rho>)"
    by (simp add: S_def)
  finally show ?case.
qed

lemma meas_map_density:
  assumes ms: "measurement_system n Ms"
      and dm: "density_matrix n \<rho>"
  shows "density_matrix n (meas_map Ms \<rho>)"
proof -
  have rho_carr: "\<rho> \<in> carrier_mat n n"
    using dm by (auto simp: density_matrix_def)
  have rho_psd: "psd \<rho>"
    using dm by (auto simp: density_matrix_def)
  have rho_tr: "Tr \<rho> = 1"
    using dm by (auto simp: density_matrix_def)
  have Ms_carr: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    using ms by (simp add: measurement_system_def)
  have id_eq: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) = 1\<^sub>m n"
    using ms by (simp add: measurement_system_def)

  have map_carr: "meas_map Ms \<rho> \<in> carrier_mat n n"
    using meas_map_carrier[OF Ms_carr rho_carr] .

  have map_psd: "psd (meas_map Ms \<rho>)"
    using meas_map_psd[OF Ms_carr rho_carr rho_psd] .

  have "Tr (meas_map Ms \<rho>) = Tr (1\<^sub>m n * \<rho>)"
    using meas_map_trace_aux[OF Ms_carr rho_carr] id_eq by simp
  also have "\<dots> = Tr \<rho>"
    using rho_carr by simp
  finally have map_tr: "Tr (meas_map Ms \<rho>) = 1"
    using rho_tr by simp

  show ?thesis
    unfolding density_matrix_def using map_carr map_psd map_tr by simp
qed

(* --------------------------------------------------------------------------
   Quantum noise and completely positive maps
   -------------------------------------------------------------------------- *)

definition kraus_map_dim :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "kraus_map_dim d Ws \<rho> \<equiv>
     foldr (\<lambda>W acc. W * \<rho> * (W\<^sup>\<dagger>) + acc) Ws (0\<^sub>m d d)"

definition kraus_map :: "complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "kraus_map Ws \<rho> \<equiv> kraus_map_dim (dim_row \<rho>) Ws \<rho>"

definition kraus_operators :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> bool" where
  "kraus_operators n d Ws \<equiv>
     (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and>
     foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Ws (0\<^sub>m n n) = 1\<^sub>m n"

lemma kraus_map_dim_Nil [simp]:
  "kraus_map_dim d [] \<rho> = 0\<^sub>m d d"
  by (simp add: kraus_map_dim_def)

lemma kraus_map_dim_Cons [simp]:
  "kraus_map_dim d (W # Ws) \<rho> =
     W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>"
  by (simp add: kraus_map_dim_def)

lemma kraus_map_dim_carrier:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
  using Ws_c
proof (induction Ws)
  case Nil
  show ?case by simp
next
  case (Cons W Ws)
  hence W_c: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  have term_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
    using W_c \<rho>_c Wdag_c by (intro mult_carrier_mat) auto
  have rec_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using Cons.IH Ws_c' by blast
  show ?case
    using term_c rec_c by simp
qed

lemma kraus_map_dim_psd:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
      and \<rho>_psd: "psd \<rho>"
  shows "psd (kraus_map_dim d Ws \<rho>)"
  using Ws_c
proof (induction Ws)
  case Nil
  show ?case by simp
next
  case (Cons W Ws)
  hence W_c: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W_c by (rule dagger_carrier)
  obtain Q where Qc: "Q \<in> carrier_mat n n" and Qpsd: "psd Q" and QQ: "Q * Q = \<rho>"
    using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
  have Qdag: "Q\<^sup>\<dagger> = Q"
    using Qpsd by (simp add: psd_def hermitian_def)
  have WQ_c: "W * Q \<in> carrier_mat d n"
    using W_c Qc by (intro mult_carrier_mat) auto
  have WQdag_c: "(W * Q)\<^sup>\<dagger> \<in> carrier_mat n d"
    using WQ_c by (rule dagger_carrier)

  have term_eq: "W * \<rho> * (W\<^sup>\<dagger>) = (W * Q) * ((W * Q)\<^sup>\<dagger>)"
  proof -
    have dagprod: "(W * Q)\<^sup>\<dagger> = (Q\<^sup>\<dagger>) * (W\<^sup>\<dagger>)"
      using W_c Qc by (simp add: dagger_of_prod)
    have dagprod': "(W * Q)\<^sup>\<dagger> = Q * (W\<^sup>\<dagger>)"
      using dagprod Qdag by simp
    have "(W * Q) * ((W * Q)\<^sup>\<dagger>) = (W * Q) * (Q * (W\<^sup>\<dagger>))"
      using dagprod' by simp
    also have "\<dots> = W * Q * Q * (W\<^sup>\<dagger>)"
      using W_c Qc Wdag_c by (metis assoc_mult_mat mult_carrier_mat)
    also have "\<dots> = W * (Q * Q) * (W\<^sup>\<dagger>)"
      using W_c Qc by (metis assoc_mult_mat)
    also have "\<dots> = W * \<rho> * (W\<^sup>\<dagger>)"
      using QQ by simp
    finally show ?thesis by simp
  qed

  have term_psd: "psd (W * \<rho> * (W\<^sup>\<dagger>))"
  proof -
    have psd_dd: "psd (((W * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((W * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF WQdag_c] .
    have dd_eq: "((W * Q)\<^sup>\<dagger>\<^sup>\<dagger>) = W * Q"
      using WQ_c by (simp add: dagger_of_dagger_is_id)
    from psd_dd dd_eq have "psd ((W * Q) * ((W * Q)\<^sup>\<dagger>))"
      by simp
    thus ?thesis
      using term_eq by simp
  qed
  have term_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
    using W_c \<rho>_c Wdag_c by (intro mult_carrier_mat) auto
  have IH_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' \<rho>_c] .
  have IH_psd: "psd (kraus_map_dim d Ws \<rho>)"
    using Cons.IH Ws_c' by blast
  have "psd (W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>)"
    using term_psd IH_psd term_c IH_c by (rule psd_add_psd)
  thus ?case by simp
qed

definition positive_map :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "positive_map n d \<Phi> \<equiv>
     (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d) \<and>
     (\<forall>P. P \<in> carrier_mat n n \<longrightarrow> psd P \<longrightarrow> psd (\<Phi> P))"

lemma kraus_map_dim_positive_map:
  assumes Ws: "kraus_operators n d Ws"
  shows "positive_map n d (kraus_map_dim d Ws)"
proof -
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    using Ws by (simp add: kraus_operators_def)
  show ?thesis
    unfolding positive_map_def
    using kraus_map_dim_carrier[OF Ws_c]
          kraus_map_dim_psd[OF Ws_c]
    by blast
qed

definition trace_preserving :: "nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "trace_preserving n \<Phi> \<equiv>
     \<forall>X. X \<in> carrier_mat n n \<longrightarrow> Tr (\<Phi> X) = Tr X"

definition unital_map :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "unital_map n d \<Phi> \<equiv> \<Phi> (1\<^sub>m n) = 1\<^sub>m d"

definition block_of_mat :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "block_of_mat n x a b \<equiv>
     Matrix.mat n n (\<lambda>(r,c). x $$ (a*n + r, b*n + c))"

lemma block_of_mat_carrier [simp]:
  "block_of_mat n X a b \<in> carrier_mat n n"
  by (simp add: block_of_mat_def)

lemma block_of_mat_index:
  assumes "r < n" and "c < n"
  shows "block_of_mat n X a b $$ (r,c) = X $$ (a*n + r, b*n + c)"
  using assms by (simp add: block_of_mat_def)

lemma block_of_mat_single:
  assumes X: "X \<in> carrier_mat n n"
  shows "block_of_mat n X 0 0 = X"
proof (rule eq_matI)
  show "dim_row (block_of_mat n X 0 0) = dim_row X"
    using X by (simp add: block_of_mat_def)
  show "dim_col (block_of_mat n X 0 0) = dim_col X"
    using X by (simp add: block_of_mat_def)
next
  fix i j
  assume "i < dim_row X" and "j < dim_col X"
  then have "i < n" and "j < n"
    using X by auto
  thus "block_of_mat n X 0 0 $$ (i,j) = X $$ (i,j)"
    by (simp add: block_of_mat_index)
qed

definition amplification :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "amplification n d p \<Phi> x \<equiv>
     Matrix.mat (p*d) (p*d)
       (\<lambda>(i,j). \<Phi> (block_of_mat n x (i div d) (j div d)) $$
             (i mod d, j mod d))"

lemma amplification_carrier [simp]:
  "amplification n d p \<Phi> X \<in> carrier_mat (p*d) (p*d)"
  by (simp add: amplification_def)

lemma amplification_index:
  assumes "i < p*d" and "j < p*d"
  shows "amplification n d p \<Phi> X $$ (i,j) =
         \<Phi> (block_of_mat n X (i div d) (j div d)) $$
             (i mod d, j mod d)"
  using assms by (simp add: amplification_def)

lemma amplification_one:
  assumes X: "X \<in> carrier_mat n n"
      and range: "\<Phi> X \<in> carrier_mat d d"
  shows "amplification n d 1 \<Phi> X = \<Phi> X"
proof (rule eq_matI)
  show "dim_row (amplification n d 1 \<Phi> X) = dim_row (\<Phi> X)"
    using range by (simp add: amplification_def)
  show "dim_col (amplification n d 1 \<Phi> X) = dim_col (\<Phi> X)"
    using range by (simp add: amplification_def)
next
  fix i j
  assume i: "i < dim_row (\<Phi> X)" and j: "j < dim_col (\<Phi> X)"
  then have id: "i < d" and jd: "j < d"
    using range by auto
  have div_i: "i div d = 0"
    using id by simp
  have div_j: "j div d = 0"
    using jd by simp
  have mod_i: "i mod d = i"
    using id by simp
  have mod_j: "j mod d = j"
    using jd by simp
  have "amplification n d 1 \<Phi> X $$ (i,j)
      = \<Phi> (block_of_mat n X (i div d) (j div d)) $$ (i mod d, j mod d)"
    using id jd by (simp add: amplification_index)
  also have "\<dots> = \<Phi> (block_of_mat n X 0 0) $$ (i,j)"
    using div_i div_j mod_i mod_j by simp
  also have "\<dots> = \<Phi> X $$ (i,j)"
    using block_of_mat_single[OF X] by simp
  finally show "amplification n d 1 \<Phi> X $$ (i,j) = \<Phi> X $$ (i,j)".
qed

lemma tensor_id_kraus_carrier:
  assumes W: "W \<in> carrier_mat d n"
  shows "(1\<^sub>m p \<Otimes> W) \<in> carrier_mat (p*d) (p*n)"
  using W by simp

lemma tensor_id_kraus_list_carrier:
  assumes Ws: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "\<forall>L \<in> set (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws).
           L \<in> carrier_mat (p*d) (p*n)"
  using Ws tensor_id_kraus_carrier by auto

lemma tensor_id_kraus_index:
  assumes W: "W \<in> carrier_mat d n"
      and r: "r < p*d"
      and c: "c < p*n"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "(1\<^sub>m p \<Otimes> W) $$ (r,c) =
         (if r div d = c div n then W $$ (r mod d, c mod n) else 0)"
proof -
  have rowW: "dim_row W = d" and colW: "dim_col W = n"
    using W by auto
  have rd: "r div d < p"
    using r dpos by (simp add: less_mult_imp_div_less)
  have cn: "c div n < p"
    using c npos by (simp add: less_mult_imp_div_less)
  have ppos: "0 < p"
    using r dpos by (cases p) auto
  have "(1\<^sub>m p \<Otimes> W) $$ (r,c) =
        (1\<^sub>m p :: complex Matrix.mat) $$ (r div d, c div n) *
        W $$ (r mod d, c mod n)"
    using index_tensor_mat[OF _ _ rowW colW r c _ npos, of "1\<^sub>m p"]
    using ppos by simp
  also have "\<dots> =
        (if r div d = c div n then W $$ (r mod d, c mod n) else 0)"
    using rd cn by simp
  finally show ?thesis .
qed

lemma sum_block_delta:
  fixes f :: "nat \<Rightarrow> complex"
  assumes a: "a < p"
      and npos: "0 < n"
  shows "(\<Sum>t < p*n. if a = t div n then f (t mod n) else 0) =
         (\<Sum>r < n. f r)"
proof -
  have bij: "bij_betw (\<lambda>(q, r). q * n + r) ({..<p} \<times> {..<n}) {..<p*n}"
  proof (rule bij_betwI[where g = "\<lambda>t. (t div n, t mod n)"])
    show "(\<lambda>(q, r). q * n + r) \<in> {..<p} \<times> {..<n} \<rightarrow> {..<p*n}"
    proof
      fix z assume "z \<in> {..<p} \<times> {..<n}"
      then obtain q r where z: "z = (q, r)" and q: "q < p" and r: "r < n"
        by blast
      have "q * n + r < (q + 1) * n"
        using r by simp
      also have "\<dots> \<le> p * n"
      proof -
        have "q + 1 \<le> p"
          using q by simp
        thus "(q + 1) * n \<le> p * n"
          by (rule mult_le_mono1)
      qed
      finally show "(case z of (q, r) \<Rightarrow> q * n + r) \<in> {..<p*n}"
        using z by simp
    qed
  next
    show "(\<lambda>t. (t div n, t mod n)) \<in> {..<p*n} \<rightarrow> {..<p} \<times> {..<n}"
      using npos by (auto simp: less_mult_imp_div_less)
  next
    fix z assume "z \<in> {..<p} \<times> {..<n}"
    then obtain q r where z: "z = (q, r)" and r: "r < n"
      by blast
    show "(\<lambda>t. (t div n, t mod n)) ((\<lambda>(q, r). q * n + r) z) = z"
      using z r by simp
  next
    fix t assume "t \<in> {..<p*n}"
    show "(\<lambda>(q, r). q * n + r) ((\<lambda>t. (t div n, t mod n)) t) = t"
      by simp
  qed

  have "(\<Sum>t < p*n. if a = t div n then f (t mod n) else 0) =
        (\<Sum>(q, r) \<in> {..<p} \<times> {..<n}. if a = q then f r else 0)"
    using sum.reindex_bij_betw[OF bij, symmetric,
        of "\<lambda>t. if a = t div n then f (t mod n) else 0"]
  proof -
    have "(\<Sum>t < p*n. if a = t div n then f (t mod n) else 0) =
          (\<Sum>x \<in> {..<p} \<times> {..<n}.
             if a = ((case x of (q, r) \<Rightarrow> q * n + r) div n)
             then f (((case x of (q, r) \<Rightarrow> q * n + r) mod n)) else 0)"
      using sum.reindex_bij_betw[OF bij, symmetric,
          of "\<lambda>t. if a = t div n then f (t mod n) else 0"]
      by (simp add: case_prod_beta)
    also have "\<dots> = (\<Sum>(q, r) \<in> {..<p} \<times> {..<n}. if a = q then f r else 0)"
    proof (intro sum.cong refl)
      fix x assume x: "x \<in> {..<p} \<times> {..<n}"
      then obtain q r where xr: "x = (q, r)" and r: "r < n"
        by blast
      show "(if a = ((case x of (q, r) \<Rightarrow> q * n + r) div n)
             then f (((case x of (q, r) \<Rightarrow> q * n + r) mod n)) else 0) =
            (case x of (q, r) \<Rightarrow> if a = q then f r else 0)"
        using xr r npos by simp
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = (\<Sum>q < p. \<Sum>r < n. if a = q then f r else 0)"
    by (simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>q < p. if a = q then (\<Sum>r < n. f r) else 0)"
    by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>r < n. f r)"
    using a by (simp add: sum.delta)
  finally show ?thesis .
qed

lemma sum_block_delta_index:
  fixes h :: "nat \<Rightarrow> complex"
  assumes a: "a < p"
      and npos: "0 < n"
  shows "(\<Sum>t < p*n. if a = t div n then h t else 0) =
         (\<Sum>r < n. h (a*n + r))"
proof -
  have eq: "\<And>t. t < p*n \<Longrightarrow>
      (if a = t div n then h t else 0) =
      (if a = t div n then h (a*n + t mod n) else 0)"
  proof -
    fix t assume t: "t < p*n"
    show "(if a = t div n then h t else 0) =
          (if a = t div n then h (a*n + t mod n) else 0)"
    proof (cases "a = t div n")
      case True
      have "t = (t div n) * n + t mod n"
        by simp
      also have "\<dots> = a * n + t mod n"
        using True by simp
      finally show ?thesis
        using True by simp
    next
      case False
      thus ?thesis by simp
    qed
  qed
  have "(\<Sum>t < p*n. if a = t div n then h t else 0) =
        (\<Sum>t < p*n. if a = t div n then h (a*n + t mod n) else 0)"
    by (intro sum.cong refl eq) simp
  also have "\<dots> = (\<Sum>r < n. h (a*n + r))"
    using sum_block_delta[OF a npos, of "\<lambda>r. h (a*n + r)"] .
  finally show ?thesis .
qed

lemma tensor_id_kraus_left_mult_index:
  assumes W: "W \<in> carrier_mat d n"
      and x: "x \<in> carrier_mat (p*n) q"
      and i: "i < p*d"
      and s: "s < q"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "((1\<^sub>m p \<Otimes> W) * x) $$ (i,s) =
         (\<Sum>t < n. W $$ (i mod d, t) * x $$ ((i div d) * n + t, s))"
proof -
  have a: "i div d < p"
    using i dpos by (simp add: less_mult_imp_div_less)
  have L: "(1\<^sub>m p \<Otimes> W) \<in> carrier_mat (p*d) (p*n)"
    using W by (rule tensor_id_kraus_carrier)
  have iL: "i < dim_row (1\<^sub>m p \<Otimes> W)"
    using W i by auto
  have sx: "s < dim_col x"
    using x s by auto
  have "((1\<^sub>m p \<Otimes> W) * x) $$ (i,s) =
        Matrix.row (1\<^sub>m p \<Otimes> W) i \<bullet> Matrix.col x s"
    using index_mult_mat(1)[OF iL sx] .
  also have "\<dots> =
        (\<Sum>r = 0..<p*n. (1\<^sub>m p \<Otimes> W) $$ (i,r) * x $$ (r,s))"
  proof -
    have "Matrix.row (1\<^sub>m p \<Otimes> W) i \<bullet> Matrix.col x s =
          (\<Sum>r = 0..<p*n.
             Matrix.row (1\<^sub>m p \<Otimes> W) i $ r * Matrix.col x s $ r)"
      unfolding scalar_prod_def using x by simp
    also have "\<dots> =
          (\<Sum>r = 0..<p*n. (1\<^sub>m p \<Otimes> W) $$ (i,r) * x $$ (r,s))"
      using W x i s by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  also have "\<dots> =
        (\<Sum>r < p*n. (1\<^sub>m p \<Otimes> W) $$ (i,r) * x $$ (r,s))"
    by (simp add: lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>r < p*n. if i div d = r div n
             then W $$ (i mod d, r mod n) * x $$ (r,s) else 0)"
    using W i dpos npos
    by (intro sum.cong refl) (simp add: tensor_id_kraus_index)
  also have "\<dots> =
        (\<Sum>t < n. W $$ (i mod d, t) * x $$ ((i div d) * n + t, s))"
    using sum_block_delta_index[OF a npos,
        of "\<lambda>r. W $$ (i mod d, r mod n) * x $$ (r,s)"]
    by simp
  finally show ?thesis .
qed

lemma tensor_id_kraus_right_mult_index:
  assumes W: "W \<in> carrier_mat d n"
      and y: "y \<in> carrier_mat q (p*n)"
      and i: "i < q"
      and j: "j < p*d"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "(y * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j) =
         (\<Sum>s < n. y $$ (i, (j div d) * n + s) * (W\<^sup>\<dagger>) $$ (s, j mod d))"
proof -
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W by (rule dagger_carrier)
  have b: "j div d < p"
    using j dpos by (simp add: less_mult_imp_div_less)
  have R: "(1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*n) (p*d)"
    using Wdag by (rule tensor_id_kraus_carrier)
  have iy: "i < dim_row y"
    using y i by auto
  have jR: "j < dim_col (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))"
    using W j by auto
  have "(y * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j) =
        Matrix.row y i \<bullet> Matrix.col (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) j"
    using index_mult_mat(1)[OF iy jR] .
  also have "\<dots> =
        (\<Sum>r = 0..<p*n. y $$ (i,r) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) $$ (r,j))"
  proof -
    have "Matrix.row y i \<bullet> Matrix.col (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) j =
          (\<Sum>r = 0..<p*n.
             Matrix.row y i $ r * Matrix.col (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) j $ r)"
      unfolding scalar_prod_def using W y by simp
    also have "\<dots> =
          (\<Sum>r = 0..<p*n. y $$ (i,r) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) $$ (r,j))"
      using W y i j by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  also have "\<dots> =
        (\<Sum>r < p*n. y $$ (i,r) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) $$ (r,j))"
    by (simp add: lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>r < p*n. if j div d = r div n
             then y $$ (i,r) * (W\<^sup>\<dagger>) $$ (r mod n, j mod d) else 0)"
    using Wdag j dpos npos
    by (intro sum.cong refl) (simp add: tensor_id_kraus_index mult.commute)
  also have "\<dots> =
        (\<Sum>s < n. y $$ (i, (j div d) * n + s) * (W\<^sup>\<dagger>) $$ (s, j mod d))"
    using sum_block_delta_index[OF b npos,
        of "\<lambda>r. y $$ (i,r) * (W\<^sup>\<dagger>) $$ (r mod n, j mod d)"]
    by simp
  finally show ?thesis .
qed

lemma kraus_term_index:
  assumes W: "W \<in> carrier_mat d n"
      and B: "B \<in> carrier_mat n n"
      and i: "i < d"
      and j: "j < d"
  shows "(W * B * (W\<^sup>\<dagger>)) $$ (i,j) =
         (\<Sum>s < n. (\<Sum>t < n. W $$ (i,t) * B $$ (t,s)) * (W\<^sup>\<dagger>) $$ (s,j))"
proof -
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W by (rule dagger_carrier)
  have WB: "W * B \<in> carrier_mat d n"
    using W B by (intro mult_carrier_mat) auto
  have iWB: "i < dim_row (W * B)"
    using WB i by auto
  have jWdag: "j < dim_col (W\<^sup>\<dagger>)"
    using Wdag j by auto
  have "(W * B * (W\<^sup>\<dagger>)) $$ (i,j) =
        Matrix.row (W * B) i \<bullet> Matrix.col (W\<^sup>\<dagger>) j"
    using index_mult_mat(1)[OF iWB jWdag] .
  also have "\<dots> = (\<Sum>s = 0..<n. (W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j))"
  proof -
    have "Matrix.row (W * B) i \<bullet> Matrix.col (W\<^sup>\<dagger>) j =
          (\<Sum>s = 0..<n. Matrix.row (W * B) i $ s * Matrix.col (W\<^sup>\<dagger>) j $ s)"
      unfolding scalar_prod_def using W WB by simp
    also have "\<dots> = (\<Sum>s = 0..<n. (W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j))"
    proof (intro sum.cong refl)
      fix s assume s: "s \<in> {0..<n}"
      hence sn: "s < n" by simp
      have "Matrix.row (W * B) i $ s = (W * B) $$ (i,s)"
        using B WB i sn by (simp add: Matrix.row_def)
      moreover have "Matrix.col (W\<^sup>\<dagger>) j $ s = (W\<^sup>\<dagger>) $$ (s,j)"
        using W Wdag j sn by (simp add: Matrix.col_def)
      ultimately show "Matrix.row (W * B) i $ s * Matrix.col (W\<^sup>\<dagger>) j $ s =
        (W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j)"
        by simp
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = (\<Sum>s < n. (W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j))"
    by (simp add: lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>s < n. (\<Sum>t < n. W $$ (i,t) * B $$ (t,s)) * (W\<^sup>\<dagger>) $$ (s,j))"
  proof (intro sum.cong refl)
    fix s assume s: "s \<in> {..<n}"
    hence sn: "s < n" by simp
    have iW: "i < dim_row W"
      using W i by auto
    have sB: "s < dim_col B"
      using B sn by auto
    have "(W * B) $$ (i,s) = Matrix.row W i \<bullet> Matrix.col B s"
      using index_mult_mat(1)[OF iW sB] .
    also have "\<dots> = (\<Sum>t = 0..<n. W $$ (i,t) * B $$ (t,s))"
    proof -
      have "Matrix.row W i \<bullet> Matrix.col B s =
            (\<Sum>t = 0..<n. Matrix.row W i $ t * Matrix.col B s $ t)"
        unfolding scalar_prod_def using W B by simp
      also have "\<dots> = (\<Sum>t = 0..<n. W $$ (i,t) * B $$ (t,s))"
        using W B i sn by (intro sum.cong refl) simp
      finally show ?thesis .
    qed
    also have "\<dots> = (\<Sum>t < n. W $$ (i,t) * B $$ (t,s))"
      by (simp add: lessThan_atLeast0)
    finally show "(W * B) $$ (i,s) * (W\<^sup>\<dagger>) $$ (s,j) =
        (\<Sum>t<n. W $$ (i,t) * B $$ (t,s)) * (W\<^sup>\<dagger>) $$ (s,j)"
      by simp
  qed
  finally show ?thesis .
qed

lemma kraus_amplification_single:
  assumes W: "W \<in> carrier_mat d n"
      and x: "x \<in> carrier_mat (p*n) (p*n)"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x =
         ((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))"
proof (rule eq_matI)
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W by (rule dagger_carrier)
  have L: "(1\<^sub>m p \<Otimes> W) \<in> carrier_mat (p*d) (p*n)"
    using W by (rule tensor_id_kraus_carrier)
  have R: "(1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*n) (p*d)"
    using Wdag by (rule tensor_id_kraus_carrier)
  have LX: "(1\<^sub>m p \<Otimes> W) * x \<in> carrier_mat (p*d) (p*n)"
    using L x by (intro mult_carrier_mat) auto
  have RHS_c: "((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*d) (p*d)"
    using mult_carrier_mat[OF LX R] by simp
  show "dim_row (amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x) =
        dim_row (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)))"
    using W RHS_c by (simp add: amplification_def)
  show "dim_col (amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x) =
        dim_col (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)))"
    using W RHS_c by (simp add: amplification_def)
next
  fix i j
  assume ij: "i < dim_row (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)))"
             "j < dim_col (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)))"
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using W by (rule dagger_carrier)
  have L: "(1\<^sub>m p \<Otimes> W) \<in> carrier_mat (p*d) (p*n)"
    using W by (rule tensor_id_kraus_carrier)
  have R: "(1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*n) (p*d)"
    using Wdag by (rule tensor_id_kraus_carrier)
  have LX: "(1\<^sub>m p \<Otimes> W) * x \<in> carrier_mat (p*d) (p*n)"
    using L x by (intro mult_carrier_mat) auto
  have RHS_c: "((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) \<in> carrier_mat (p*d) (p*d)"
    using mult_carrier_mat[OF LX R] by simp
  have i_pd: "i < p*d" and j_pd: "j < p*d"
    using W ij RHS_c by auto
  have imodd: "i mod d < d" and jmodd: "j mod d < d"
    using dpos by simp_all
  have idiv: "i div d < p" and jdiv: "j div d < p"
    using i_pd j_pd dpos by (simp_all add: less_mult_imp_div_less)
  have lhs:
    "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x $$ (i,j) =
     (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
        x $$ ((i div d) * n + t, (j div d) * n + s)) *
        (W\<^sup>\<dagger>) $$ (s, j mod d))"
  proof -
    have "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x $$ (i,j) =
          (W * block_of_mat n x (i div d) (j div d) * (W\<^sup>\<dagger>)) $$ (i mod d, j mod d)"
      using i_pd j_pd by (simp add: amplification_def)
    also have "\<dots> =
       (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
          block_of_mat n x (i div d) (j div d) $$ (t,s)) *
          (W\<^sup>\<dagger>) $$ (s, j mod d))"
    proof -
      have Bc: "block_of_mat n x (i div d) (j div d) \<in> carrier_mat n n"
        by (simp add: block_of_mat_def)
      show ?thesis
        using kraus_term_index[OF W Bc imodd jmodd] .
    qed
    also have "\<dots> =
       (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
          x $$ ((i div d) * n + t, (j div d) * n + s)) *
          (W\<^sup>\<dagger>) $$ (s, j mod d))"
      by (intro sum.cong refl arg_cong2[where f="(*)"] sum.cong) (simp_all add: block_of_mat_def)
    finally show ?thesis .
  qed
  have rhs:
    "(((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j) =
     (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
        x $$ ((i div d) * n + t, (j div d) * n + s)) *
        (W\<^sup>\<dagger>) $$ (s, j mod d))"
  proof -
    have "(((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j) =
          (\<Sum>s < n. ((1\<^sub>m p \<Otimes> W) * x) $$ (i, (j div d) * n + s) *
             (W\<^sup>\<dagger>) $$ (s, j mod d))"
      by (rule tensor_id_kraus_right_mult_index[where W=W and d=d and n=n and p=p and q="p*d"])
         (use W LX i_pd j_pd dpos npos in auto)
    also have "\<dots> =
       (\<Sum>s < n. (\<Sum>t < n. W $$ (i mod d,t) *
          x $$ ((i div d) * n + t, (j div d) * n + s)) *
          (W\<^sup>\<dagger>) $$ (s, j mod d))"
    proof (intro sum.cong refl)
      fix s assume s: "s \<in> {..<n}"
      hence sn: "s < n" by simp
      have col: "(j div d) * n + s < p*n"
      proof -
        have "(j div d) * n + s < (j div d + 1) * n"
          using sn by simp
        also have "\<dots> \<le> p * n"
        proof -
          have "j div d + 1 \<le> p"
            using jdiv by simp
          thus "(j div d + 1) * n \<le> p * n"
            by (rule mult_le_mono1)
        qed
        finally show ?thesis .
      qed
      show "((1\<^sub>m p \<Otimes> W) * x) $$ (i, (j div d) * n + s) *
             (W\<^sup>\<dagger>) $$ (s, j mod d) =
            (\<Sum>t<n. W $$ (i mod d, t) *
                x $$ (i div d * n + t, j div d * n + s)) *
             (W\<^sup>\<dagger>) $$ (s, j mod d)"
        using tensor_id_kraus_left_mult_index[OF W x i_pd col dpos npos]
        by simp
    qed
    finally show ?thesis .
  qed
  show "amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x $$ (i,j) =
        (((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>))) $$ (i,j)"
    using lhs rhs by simp
qed

lemma amplification_zero_map:
  assumes dpos: "0 < d"
  shows "amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x = 0\<^sub>m (p*d) (p*d)"
proof (rule eq_matI)
  show "dim_row (amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x) = dim_row (0\<^sub>m (p*d) (p*d))"
    by (simp add: amplification_def)
  show "dim_col (amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x) = dim_col (0\<^sub>m (p*d) (p*d))"
    by (simp add: amplification_def)
next
  fix i j
  assume i: "i < dim_row (0\<^sub>m (p*d) (p*d))"
     and j: "j < dim_col (0\<^sub>m (p*d) (p*d))"
  show "amplification n d p (\<lambda>\<rho>. 0\<^sub>m d d) x $$ (i,j) =
        (0\<^sub>m (p*d) (p*d)) $$ (i,j)"
    using i j dpos by (simp add: amplification_def)
qed

lemma amplification_add:
  assumes dpos: "0 < d"
      and F: "\<And>a b. F (block_of_mat n x a b) \<in> carrier_mat d d"
      and G: "\<And>a b. G (block_of_mat n x a b) \<in> carrier_mat d d"
  shows "amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x =
         amplification n d p F x + amplification n d p G x"
proof (rule eq_matI)
  show "dim_row (amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x) =
        dim_row (amplification n d p F x + amplification n d p G x)"
    by (simp add: amplification_def)
  show "dim_col (amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x) =
        dim_col (amplification n d p F x + amplification n d p G x)"
    by (simp add: amplification_def)
next
  fix i j
  assume i: "i < dim_row (amplification n d p F x + amplification n d p G x)"
     and j: "j < dim_col (amplification n d p F x + amplification n d p G x)"
  have ipd: "i < p*d" and jpd: "j < p*d"
    using i j by (simp_all add: amplification_def)
  have imodd: "i mod d < d" and jmodd: "j mod d < d"
    using dpos by simp_all
  let ?B = "block_of_mat n x (i div d) (j div d)"
  have FB: "F ?B \<in> carrier_mat d d"
    by (rule F)
  have GB: "G ?B \<in> carrier_mat d d"
    by (rule G)
  show "amplification n d p (\<lambda>\<rho>. F \<rho> + G \<rho>) x $$ (i,j) =
        (amplification n d p F x + amplification n d p G x) $$ (i,j)"
    using ipd jpd imodd jmodd FB GB
    by (simp add: amplification_def)
qed

lemma amplification_kraus_map_dim:
  assumes Ws: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and x: "x \<in> carrier_mat (p*n) (p*n)"
      and dpos: "0 < d"
      and npos: "0 < n"
  shows "amplification n d p (kraus_map_dim d Ws) x =
         kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) x"
  using Ws
proof (induction Ws)
  case Nil
  show ?case
    by (simp add: amplification_zero_map[OF dpos])
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Wsc: "\<forall>W\<in>set Ws. W \<in> carrier_mat d n"
    by auto
  have term_c: "\<And>a b. W * block_of_mat n x a b * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
  proof -
    fix a b
    have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
      using Wc by (rule dagger_carrier)
    have Bc: "block_of_mat n x a b \<in> carrier_mat n n"
      by (simp add: block_of_mat_def)
    have WB: "W * block_of_mat n x a b \<in> carrier_mat d n"
      using mult_carrier_mat[OF Wc Bc] by simp
    show "W * block_of_mat n x a b * (W\<^sup>\<dagger>) \<in> carrier_mat d d"
      using mult_carrier_mat[OF WB Wdag] by simp
  qed
  have rest_c: "\<And>a b. kraus_map_dim d Ws (block_of_mat n x a b) \<in> carrier_mat d d"
  proof -
    fix a b
    have Bc: "block_of_mat n x a b \<in> carrier_mat n n"
      by (simp add: block_of_mat_def)
    show "kraus_map_dim d Ws (block_of_mat n x a b) \<in> carrier_mat d d"
      using kraus_map_dim_carrier[OF Wsc Bc] .
  qed
  have cons_fun:
    "kraus_map_dim d (W # Ws) = (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>)"
    by (rule ext) simp
  have "amplification n d p (kraus_map_dim d (W # Ws)) x =
        amplification n d p (\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)) x +
        amplification n d p (kraus_map_dim d Ws) x"
    using amplification_add[
        where F="\<lambda>\<rho>. W * \<rho> * (W\<^sup>\<dagger>)" and G="kraus_map_dim d Ws"
          and n=n and d=d and p=p and x=x,
        OF dpos term_c rest_c]
    by (simp add: cons_fun)
  also have "\<dots> =
        ((1\<^sub>m p \<Otimes> W) * x) * (1\<^sub>m p \<Otimes> (W\<^sup>\<dagger>)) +
        kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) x"
    using kraus_amplification_single[OF Wc x dpos npos] Cons.IH[OF Wsc] by simp
  also have "\<dots> = kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) (W # Ws)) x"
    using Wc by (simp add: tensor_mat_adjoint)
  finally show ?case .
qed

definition p_positive :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "p_positive n d p \<Phi> \<equiv>
     \<forall>X :: complex Matrix.mat. X \<in> carrier_mat (p*n) (p*n) \<longrightarrow> psd X \<longrightarrow>
       psd (amplification n d p \<Phi> X)"

definition completely_positive :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "completely_positive n d \<Phi> \<equiv> \<forall>p > 0. p_positive n d p \<Phi>"

theorem kraus_is_cp:
  assumes Ws: "kraus_operators n d Ws"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (kraus_map_dim d Ws)"
proof -
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    using Ws by (simp add: kraus_operators_def)
  show ?thesis
  proof (unfold completely_positive_def p_positive_def, intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p"
       and X_c: "X \<in> carrier_mat (p*n) (p*n)"
       and X_psd: "psd X"
    have lifted_c: "\<forall>L \<in> set (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws).
        L \<in> carrier_mat (p*d) (p*n)"
      using tensor_id_kraus_list_carrier[OF Ws_c] .
    have amp_eq: "amplification n d p (kraus_map_dim d Ws) X =
        kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) X"
      using amplification_kraus_map_dim[OF Ws_c X_c dpos npos] .
    show "psd (amplification n d p (kraus_map_dim d Ws) X)"
      using kraus_map_dim_psd[OF lifted_c X_c X_psd] amp_eq by simp
  qed
qed

(* ============================================================================
   DAY 18 — Theory of CP Maps; Span of M_n^+
   ============================================================================ *)

(* Any X \<in> M_n can be written as X = (P1 - P2) + i(P3 - P4) with each Pi \<ge> 0.
   Hence span(M_n^+) = M_n. *)

lemma diag_mat_of_real_hermitian:
  "((diag_mat_of_real D)\<^sup>\<dagger>) = diag_mat_of_real D"
proof (rule eq_matI)
  show "dim_row ((diag_mat_of_real D)\<^sup>\<dagger>) = dim_row (diag_mat_of_real D)"
    by simp
  show "dim_col ((diag_mat_of_real D)\<^sup>\<dagger>) = dim_col (diag_mat_of_real D)"
    by simp
next
  fix i j
  assume ij: "i < dim_row (diag_mat_of_real D)"
             "j < dim_col (diag_mat_of_real D)"
  hence iln: "i < length D" and jln: "j < length D" by simp_all
  have "(diag_mat_of_real D)\<^sup>\<dagger> $$ (i,j) = cnj (diag_mat_of_real D $$ (j,i))"
    using iln jln by (simp add: dagger_def)
  also have "\<dots> = (if i = j then cnj (of_real (D ! i)) else 0)"
    using iln jln by auto
  also have "\<dots> = (if i = j then of_real (D ! i) else 0)"
    by simp
  also have "\<dots> = diag_mat_of_real D $$ (i,j)"
    using iln jln by auto
  finally show "(diag_mat_of_real D)\<^sup>\<dagger> $$ (i,j) = diag_mat_of_real D $$ (i,j)".
qed

lemma psd_U_diag_Udag:
  fixes U :: "complex Matrix.mat" and D :: "real list"
  assumes Uc: "U \<in> carrier_mat n n"
      and Dlen: "length D = n"
      and Dnn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  shows "psd (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
proof -
  let ?D = "diag_mat_of_real D"
  let ?P = "U * ?D * (U\<^sup>\<dagger>)"
  have Udag_c: "(U\<^sup>\<dagger>) \<in> carrier_mat n n" using Uc by (rule dagger_carrier)
  have D_c: "?D \<in> carrier_mat n n"
    using Dlen diag_mat_of_real_carrier by metis
  have UD_c: "U * ?D \<in> carrier_mat n n"
    using Uc D_c by simp
  have P_c: "?P \<in> carrier_mat n n"
    using UD_c Udag_c by simp

  have herm: "hermitian ?P"
  proof -
    have UD_dim: "dim_col U = dim_row ?D"
      using Uc D_c by (metis carrier_matD)
    have UDU_dim: "dim_col (U * ?D) = dim_row (U\<^sup>\<dagger>)"
      using UD_c Udag_c by (metis carrier_matD)
    have prep1: "(U * ?D)\<^sup>\<dagger> = ((?D)\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
      using UD_dim by (rule dagger_of_prod)
    have prep2: "((U * ?D) * (U\<^sup>\<dagger>))\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * ?D)\<^sup>\<dagger>)"
      using UDU_dim by (rule dagger_of_prod)
    have prep3: "((U\<^sup>\<dagger>)\<^sup>\<dagger>) = U" using Uc by (subst dagger_of_dagger_is_id, simp)
    have prep4: "(?D)\<^sup>\<dagger> = ?D" using diag_mat_of_real_hermitian.
    have "(?P)\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * ?D)\<^sup>\<dagger>)" using prep2 by simp
    also have "\<dots> = U * ((U * ?D)\<^sup>\<dagger>)" using prep3 by simp
    also have "\<dots> = U * ((?D)\<^sup>\<dagger> * (U\<^sup>\<dagger>))" using prep1 by simp
    also have "\<dots> = U * (?D * (U\<^sup>\<dagger>))" using prep4 by simp
    also have "\<dots> = U * ?D * (U\<^sup>\<dagger>)"
      using Uc D_c Udag_c by (metis assoc_mult_mat)
    finally show ?thesis by (simp add: hermitian_def)
  qed

  have nn: "\<forall>x :: complex Matrix.vec.
              dim_vec x = dim_row ?P \<longrightarrow> 0 \<le> Re \<langle>x | ?P *\<^sub>v x\<rangle>"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume "dim_vec x = dim_row ?P"
    hence xdim: "dim_vec x = n" using P_c by auto
    have xcar: "x \<in> carrier_vec n" using xdim by auto
    let ?y = "(U\<^sup>\<dagger>) *\<^sub>v x"
    have ydim: "dim_vec ?y = n"
      using Udag_c by (metis carrier_matD(1) dim_mult_mat_vec)
    have ycar: "?y \<in> carrier_vec n" using ydim carrier_vec_dim_vec by blast 

    have step1: "?P *\<^sub>v x = U *\<^sub>v (?D *\<^sub>v ?y)"
    proof -
      have "?P *\<^sub>v x = (U * (?D * (U\<^sup>\<dagger>))) *\<^sub>v x"
        using Uc D_c Udag_c by (metis assoc_mult_mat)
      also have "\<dots> = U *\<^sub>v ((?D * (U\<^sup>\<dagger>)) *\<^sub>v x)"
        using Uc D_c Udag_c xcar
        by (intro assoc_mult_mat_vec) auto
      also have "\<dots> = U *\<^sub>v (?D *\<^sub>v ((U\<^sup>\<dagger>) *\<^sub>v x))"
        using D_c Udag_c xcar by (intro arg_cong[where f = "(*\<^sub>v) U"] assoc_mult_mat_vec) auto
      finally show ?thesis .
    qed

    have step2: "\<langle>x | U *\<^sub>v (?D *\<^sub>v ?y)\<rangle> = \<langle>(U\<^sup>\<dagger>) *\<^sub>v x | ?D *\<^sub>v ?y\<rangle>"
      using Uc xdim ydim
      using Dlen inner_prod_adjoint_swap by auto


    have qf_eq: "\<langle>x | ?P *\<^sub>v x\<rangle> = \<langle>?y | ?D *\<^sub>v ?y\<rangle>"
      using step1 step2 by simp

    have D_nn_idx: "\<And>i. i < length D \<Longrightarrow> 0 \<le> D ! i"
      using Dnn Dlen by auto
    have "0 \<le> Re \<langle>?y | ?D *\<^sub>v ?y\<rangle>"
      using diag_mat_of_real_quad_Re_nonneg[OF _ D_nn_idx] ydim Dlen by simp
    thus "0 \<le> Re \<langle>x | ?P *\<^sub>v x\<rangle>" using qf_eq by simp
  qed

  show ?thesis
    unfolding psd_def using herm nn P_c by simp
qed

lemma hermitian_decomp_psd:
  fixes H :: "complex Matrix.mat"
  assumes sq: "H \<in> carrier_mat n n"
      and herm: "hermitian H"
  shows "\<exists>P1 P2 :: complex Matrix.mat.
         P1 \<in> carrier_mat n n \<and> P2 \<in> carrier_mat n n \<and>
         psd P1 \<and> psd P2 \<and>
         H = P1 - P2"
proof -
  (* Spectral decomp: H = U D (U\<^sup>\<dagger>), D real diagonal.  Split D into D+ (\<lambda>i \<ge> 0)
     and D- (-\<lambda>i for \<lambda>i < 0).  Then P1 = U D+ (U\<^sup>\<dagger>), P2 = U D- (U\<^sup>\<dagger>). *)
  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
    and Dlen: "length D = n"
    and spec: "(U\<^sup>\<dagger>) * H * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast
  let ?Dpos = "map (\<lambda>x. max x 0) D"
  let ?Dneg = "map (\<lambda>x. max (- x) 0) D"
  let ?P1 = "U * diag_mat_of_real ?Dpos * (U\<^sup>\<dagger>)"
  let ?P2 = "U * diag_mat_of_real ?Dneg * (U\<^sup>\<dagger>)"
  have Udag: "(U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using Uc by (rule dagger_carrier)
  have Dpos_len: "length ?Dpos = n" using Dlen by simp
  have Dneg_len: "length ?Dneg = n" using Dlen by simp
  have c1: "?P1 \<in> carrier_mat n n"
    using Uc Udag Dpos_len by auto
  have c2: "?P2 \<in> carrier_mat n n"
    using Uc Udag Dneg_len by auto

  have Dpos_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> ?Dpos ! i"
    using Dlen by simp
  have Dneg_nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> ?Dneg ! i"
    using Dlen by simp
  have p1: "psd ?P1"
    using psd_U_diag_Udag[OF Uc Dpos_len Dpos_nn].
  have p2: "psd ?P2"
    using psd_U_diag_Udag[OF Uc Dneg_len Dneg_nn].

  (* H = U * diag D * U\<^sup>\<dagger> *)
  have UdagU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n" using Uc UU unfolding unitary_def by auto
  have UUdag: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using Uc UU unfolding unitary_def by auto
  have D_c: "diag_mat_of_real D \<in> carrier_mat n n"
    using Dlen diag_mat_of_real_carrier by metis
  have H_eq: "H = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
  proof -
    have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = U * ((U\<^sup>\<dagger>) * H * U) * (U\<^sup>\<dagger>)"
      using spec by simp
    also have "\<dots> = (U * (U\<^sup>\<dagger>)) * H * (U * (U\<^sup>\<dagger>))"
      using Uc Udag sq
      by (smt (verit, ccfv_SIG) assoc_mult_mat carrier_mat_triv mult_carrier_mat)
    also have "\<dots> = 1\<^sub>m n * H * 1\<^sub>m n" using UUdag by simp
    also have "\<dots> = H" using sq by simp
    finally show ?thesis by simp
  qed

  (* diag_mat_of_real D = diag ?Dpos - diag ?Dneg *)
  have diag_split: "diag_mat_of_real D
                  = diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg"
  proof (rule eq_matI)
    show "dim_row (diag_mat_of_real D)
        = dim_row (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg)"
      using Dpos_len Dneg_len Dlen by simp
    show "dim_col (diag_mat_of_real D)
        = dim_col (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg)"
      using Dpos_len Dneg_len Dlen by simp
  next
    fix i j
    assume "i < dim_row (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg)"
           "j < dim_col (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg)"
    hence iln: "i < n" and jln: "j < n"
      using Dpos_len Dneg_len by auto
    have iD: "i < length D" and jD: "j < length D"
      using iln jln Dlen by auto
    have iDp: "i < length ?Dpos" and jDp: "j < length ?Dpos"
      using iln jln Dpos_len by auto
    have iDn: "i < length ?Dneg" and jDn: "j < length ?Dneg"
      using iln jln Dneg_len by auto
    have rhs_entry:
      "(diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg) $$ (i,j)
       = diag_mat_of_real ?Dpos $$ (i,j) - diag_mat_of_real ?Dneg $$ (i,j)"
      using iDp jDp by simp
    show "diag_mat_of_real D $$ (i,j)
        = (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg) $$ (i,j)"
    proof (cases "i = j")
      case True
      have lhs_val: "diag_mat_of_real D $$ (i,j) = of_real (D ! i)"
        using True iD by simp
      have p_val: "diag_mat_of_real ?Dpos $$ (i,j) = of_real (max (D ! i) 0)"
        using True iDp Dlen by simp
      have n_val: "diag_mat_of_real ?Dneg $$ (i,j) = of_real (max (- (D ! i)) 0)"
        using True iDn Dlen by simp
      have real_split: "(D ! i) = max (D ! i) 0 - max (- (D ! i)) 0"
        by linarith
      have of_real_split:
        "(of_real (D ! i) :: complex)
         = of_real (max (D ! i) 0) - of_real (max (- (D ! i)) 0)"
        using real_split by (metis of_real_diff)
      show ?thesis
        using lhs_val p_val n_val rhs_entry of_real_split by simp
    next
      case False
      have lhs0: "diag_mat_of_real D $$ (i,j) = 0" using iD jD False by simp
      have p0: "diag_mat_of_real ?Dpos $$ (i,j) = 0"
        using iDp jDp False by simp
      have n0: "diag_mat_of_real ?Dneg $$ (i,j) = 0"
        using iDn jDn False by simp
      show ?thesis using lhs0 p0 n0 rhs_entry by simp
    qed
  qed

  have Dp_c: "diag_mat_of_real ?Dpos \<in> carrier_mat n n"
    using Dpos_len diag_mat_of_real_carrier by metis
  have Dn_c: "diag_mat_of_real ?Dneg \<in> carrier_mat n n"
    using Dneg_len diag_mat_of_real_carrier by metis
  have UDp_c: "U * diag_mat_of_real ?Dpos \<in> carrier_mat n n"
    using Uc Dp_c by (intro mult_carrier_mat) auto
  have UDn_c: "U * diag_mat_of_real ?Dneg \<in> carrier_mat n n"
    using Uc Dn_c by (intro mult_carrier_mat) auto

  have eq: "H = ?P1 - ?P2"
  proof -
    have "H = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" using H_eq .
    also have "\<dots> = U * (diag_mat_of_real ?Dpos - diag_mat_of_real ?Dneg) * (U\<^sup>\<dagger>)"
      using diag_split by simp
    also have "\<dots> = (U * diag_mat_of_real ?Dpos - U * diag_mat_of_real ?Dneg) * (U\<^sup>\<dagger>)"
      using Uc Dp_c Dn_c by (simp add: mult_minus_distrib_mat)
    also have "\<dots> = U * diag_mat_of_real ?Dpos * (U\<^sup>\<dagger>)
                  - U * diag_mat_of_real ?Dneg * (U\<^sup>\<dagger>)"
      using UDp_c UDn_c Udag by (simp add: minus_mult_distrib_mat)
    finally show ?thesis .
  qed

  show ?thesis using c1 c2 p1 p2 eq by blast
qed

(* Proof: Let \<lambda>1,...,\<lambda>n be eigenvalues with ONB u1,...,un.
   P1 = \<Sum>_{\<lambda>i\<ge>0} \<lambda>i |ui\<rangle>\<langle>ui|, P2 = \<Sum>_{\<lambda>i<0} (-\<lambda>i) |ui\<rangle>\<langle>ui|.
   Both \<ge> 0 and H = P1 - P2. *)

lemma matrix_decomp_psd:
  fixes X :: "complex Matrix.mat"
  assumes sq: "X \<in> carrier_mat n n"
  shows "\<exists>P1 P2 P3 P4 :: complex Matrix.mat.
         (\<forall>i \<in> {0..3}. [P1,P2,P3,P4] ! i \<in> carrier_mat n n \<and> psd ([P1,P2,P3,P4] ! i)) \<and>
         X = (P1 - P2) + \<i> \<cdot>\<^sub>m (P3 - P4)"
proof -
  let ?Hr = "(((1/2) :: complex) \<cdot>\<^sub>m (X + (X\<^sup>\<dagger>)))"
  let ?Hi = "(((1 / (2 * \<i>)) :: complex) \<cdot>\<^sub>m (X - (X\<^sup>\<dagger>)))"

  have Hr_carrier: "?Hr \<in> carrier_mat n n"
    using sq by auto
  have Hi_carrier: "?Hi \<in> carrier_mat n n"
    using sq by auto

  have Hr_herm: "hermitian ?Hr"
  proof -
    have "((?Hr)\<^sup>\<dagger>) = ?Hr"
    proof (rule eq_matI)
      show "dim_row ((?Hr)\<^sup>\<dagger>) = dim_row ?Hr"
        using Hr_carrier sq by (simp add: dagger_def)
      show "dim_col ((?Hr)\<^sup>\<dagger>) = dim_col ?Hr"
        using Hr_carrier sq by (simp add: dagger_def)
    next
      fix i j
      assume "i < dim_row ?Hr" "j < dim_col ?Hr"
      hence iln: "i < n" and jln: "j < n" using Hr_carrier by auto
      have hr_ji: "?Hr $$ (j,i) = (1/2) * (X $$ (j,i) + cnj (X $$ (i,j)))"
        using iln jln sq by (simp add: dagger_def)
      have hr_ij: "?Hr $$ (i,j) = (1/2) * (X $$ (i,j) + cnj (X $$ (j,i)))"
        using iln jln sq by (simp add: dagger_def)
      have d_eval: "(?Hr)\<^sup>\<dagger> $$ (i,j) = cnj (?Hr $$ (j,i))"
        using iln jln Hr_carrier sq by (simp add: dagger_def)
      have d_val: "(?Hr)\<^sup>\<dagger> $$ (i,j)
                 = (1/2) * (cnj (X $$ (j,i)) + X $$ (i,j))"
        using d_eval hr_ji by simp
      have "(?Hr)\<^sup>\<dagger> $$ (i,j)
            = (1/2) * (cnj (X $$ (j,i)) + X $$ (i,j))" using d_val.
      also have "\<dots> = (1/2) * (X $$ (i,j) + cnj (X $$ (j,i)))"
        by (simp add: add.commute)
      also have "\<dots> = ?Hr $$ (i,j)" using hr_ij[symmetric].
      finally show "(?Hr)\<^sup>\<dagger> $$ (i,j) = ?Hr $$ (i,j)".
    qed
    thus ?thesis by (simp add: hermitian_def)
  qed

  have Hi_herm: "hermitian ?Hi"
  proof -
    have "((?Hi)\<^sup>\<dagger>) = ?Hi"
    proof (rule eq_matI)
      show "dim_row ((?Hi)\<^sup>\<dagger>) = dim_row ?Hi"
        using Hi_carrier sq by (simp add: dagger_def)
      show "dim_col ((?Hi)\<^sup>\<dagger>) = dim_col ?Hi"
        using Hi_carrier sq by (simp add: dagger_def)
    next
      fix i j
      assume "i < dim_row ?Hi" "j < dim_col ?Hi"
      hence iln: "i < n" and jln: "j < n" using Hi_carrier by auto
      have hi_ji: "?Hi $$ (j,i) = (1 / (2 * \<i>)) * (X $$ (j,i) - cnj (X $$ (i,j)))"
        using iln jln sq by (simp add: dagger_def)
      have hi_ij: "?Hi $$ (i,j) = (1 / (2 * \<i>)) * (X $$ (i,j) - cnj (X $$ (j,i)))"
        using iln jln sq by (simp add: dagger_def)
      have d_eval: "(?Hi)\<^sup>\<dagger> $$ (i,j) = cnj (?Hi $$ (j,i))"
        using iln jln Hi_carrier sq by (simp add: dagger_def)
      have cnj_coef: "cnj (1 / (2 * \<i>) :: complex) = - (1 / (2 * \<i>))"
        by (simp add: complex_eq_iff)
      have "(?Hi)\<^sup>\<dagger> $$ (i,j) = cnj (?Hi $$ (j,i))" using d_eval .
      also have "\<dots> = cnj ((1 / (2 * \<i>)) * (X $$ (j,i) - cnj (X $$ (i,j))))"
        using hi_ji by simp
      also have "\<dots> = cnj (1 / (2 * \<i>)) * cnj (X $$ (j,i) - cnj (X $$ (i,j)))"
        by simp
      also have "\<dots> = (- (1 / (2 * \<i>))) * (cnj (X $$ (j,i)) - X $$ (i,j))"
        using cnj_coef by simp
      also have "\<dots> = (1 / (2 * \<i>)) * (X $$ (i,j) - cnj (X $$ (j,i)))"
        by (simp add: field_simps)
      also have "\<dots> = ?Hi $$ (i,j)" using hi_ij[symmetric].
      finally show "(?Hi)\<^sup>\<dagger> $$ (i,j) = ?Hi $$ (i,j)".
    qed
    thus ?thesis by (simp add: hermitian_def)
  qed

  obtain A B :: "complex Matrix.mat"
    where A_car: "A \<in> carrier_mat n n"
      and B_car: "B \<in> carrier_mat n n"
      and A_psd: "psd A"
      and B_psd: "psd B"
      and Hr_decomp: "?Hr = A - B"
    using hermitian_decomp_psd[OF Hr_carrier Hr_herm] by blast

  obtain C D :: "complex Matrix.mat"
    where C_car: "C \<in> carrier_mat n n"
      and D_car: "D \<in> carrier_mat n n"
      and C_psd: "psd C"
      and D_psd: "psd D"
      and Hi_decomp: "?Hi = C - D"
    using hermitian_decomp_psd[OF Hi_carrier Hi_herm] by blast

  have X_split: "X = ?Hr + (\<i> \<cdot>\<^sub>m ?Hi)"
  proof (rule eq_matI)
    show "dim_row X = dim_row (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
      using sq Hr_carrier Hi_carrier by simp
    show "dim_col X = dim_col (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
      using sq Hr_carrier Hi_carrier by simp
  next
    fix i j
    assume "i < dim_row (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
           "j < dim_col (?Hr + (\<i> \<cdot>\<^sub>m ?Hi))"
    hence iln: "i < n" and jln: "j < n" using Hr_carrier Hi_carrier by auto
    have hr_at: "?Hr $$ (i,j) = (1/2) * (X $$ (i,j) + cnj (X $$ (j,i)))"
      using iln jln sq by (simp add: dagger_def)
    have hi_at: "?Hi $$ (i,j)
                 = (1 / (2 * \<i>)) * (X $$ (i,j) - cnj (X $$ (j,i)))"
      using iln jln sq by (simp add: dagger_def)
    have iHi_c: "\<i> \<cdot>\<^sub>m ?Hi \<in> carrier_mat n n"
      using Hi_carrier by simp
    have Hi_dim_row: "dim_row ?Hi = n" using Hi_carrier by auto
    have Hi_dim_col: "dim_col ?Hi = n" using Hi_carrier by auto
    have iHi_at: "(\<i> \<cdot>\<^sub>m ?Hi) $$ (i,j) = \<i> * ?Hi $$ (i,j)"
      using iln jln Hi_dim_row Hi_dim_col index_smult_mat(1) by metis
    have Hr_dim_row: "dim_row ?Hr = n" using Hr_carrier by auto
    have Hr_dim_col: "dim_col ?Hr = n" using Hr_carrier by auto
    have iHi_dim_row: "dim_row (\<i> \<cdot>\<^sub>m ?Hi) = n" using iHi_c by auto
    have iHi_dim_col: "dim_col (\<i> \<cdot>\<^sub>m ?Hi) = n" using iHi_c by auto
    have add_at: "(?Hr + (\<i> \<cdot>\<^sub>m ?Hi)) $$ (i,j)
                = ?Hr $$ (i,j) + (\<i> \<cdot>\<^sub>m ?Hi) $$ (i,j)"
      using iln jln Hr_dim_row Hr_dim_col iHi_dim_row iHi_dim_col index_add_mat(1)
      by metis
    have sum_at: "(?Hr + (\<i> \<cdot>\<^sub>m ?Hi)) $$ (i,j)
                = ?Hr $$ (i,j) + \<i> * ?Hi $$ (i,j)"
      using add_at iHi_at by simp
    have arith:
      "(1/2 :: complex) * (X $$ (i,j) + cnj (X $$ (j,i)))
       + \<i> * ((1 / (2 * \<i>)) * (X $$ (i,j) - cnj (X $$ (j,i))))
       = X $$ (i,j)"
      by (simp add: field_simps)
    show "X $$ (i,j) = (?Hr + (\<i> \<cdot>\<^sub>m ?Hi)) $$ (i,j)"
      using sum_at hr_at hi_at arith by simp
  qed

  have X_decomp: "X = (A - B) + \<i> \<cdot>\<^sub>m (C - D)"
    using X_split Hr_decomp Hi_decomp by simp

  have list_cond:
    "\<forall>i \<in> {0..3}. [A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
  proof clarify
    fix i :: nat
    assume i: "i \<in> {0..3}"
    then have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
      by auto
    then show "[A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
    proof
      assume "i = 0"
      then show ?thesis using A_car A_psd by simp
    next
      assume "i = 1 \<or> i = 2 \<or> i = 3"
      then show "[A,B,C,D] ! i \<in> carrier_mat n n \<and> psd ([A,B,C,D] ! i)"
      proof -
        assume "i = 1 \<or> i = 2 \<or> i = 3"
        then show ?thesis
        proof
          assume "i = 1"
          then show ?thesis using B_car B_psd by simp
        next
          assume "i = 2 \<or> i = 3"
          then show ?thesis
          proof -
            assume "i = 2 \<or> i = 3"
            then show ?thesis
            proof
              assume "i = 2"
              then show ?thesis using C_car C_psd by simp
            next
              assume "i = 3"
              then show ?thesis using D_car D_psd by auto
            qed
          qed
        qed
      qed
    qed
  qed
  show ?thesis
    using list_cond X_decomp by blast
qed

(* ============================================================================
   DAY 19 — 10 / Oct / 11
   Topic: Choi's Theorem
   ============================================================================ *)

definition choi_matrix :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "choi_matrix n d \<Phi> \<equiv>
     Matrix.mat (n*d) (n*d)
       (\<lambda>(r,c). \<Phi> (mat_unit (r div d) (c div d) n n) $$ (r mod d, c mod d))"

notation choi_matrix ("P\<^sub>\<Phi>")

definition choi_seed :: "nat \<Rightarrow> complex Matrix.mat" where
  "choi_seed n \<equiv>
     Matrix.mat (n*n) (n*n)
       (\<lambda>(r,c). mat_unit (r div n) (c div n) n n $$ (r mod n, c mod n))"

lemma choi_seed_carrier [simp]:
  "choi_seed n \<in> carrier_mat (n*n) (n*n)"
  by (simp add: choi_seed_def)

lemma choi_seed_block:
  assumes npos: "n > 0"
      and a: "a < n"
      and b: "b < n"
  shows "block_of_mat n (choi_seed n) a b = mat_unit a b n n"
proof (rule eq_matI)
  show "dim_row (block_of_mat n (choi_seed n) a b) = dim_row (mat_unit a b n n)"
    by (simp add: block_of_mat_def)
  show "dim_col (block_of_mat n (choi_seed n) a b) = dim_col (mat_unit a b n n)"
    by (simp add: block_of_mat_def)
next
  fix r c
  assume r: "r < dim_row (mat_unit a b n n)"
     and c: "c < dim_col (mat_unit a b n n)"
  then have rn: "r < n" and cn: "c < n" by simp_all
  have row_lt: "a * n + r < n * n"
  proof -
    have "a * n + r < a * n + n"
      using rn by simp
    also have "\<dots> = Suc a * n"
      by simp
    also have "\<dots> \<le> n * n"
    proof -
      have "Suc a \<le> n"
        using a by simp
      thus "Suc a * n \<le> n * n"
        by (metis mult.commute mult_le_mono2)
    qed
    finally show ?thesis .
  qed
  have col_lt: "b * n + c < n * n"
  proof -
    have "b * n + c < b * n + n"
      using cn by simp
    also have "\<dots> = Suc b * n"
      by simp
    also have "\<dots> \<le> n * n"
    proof -
      have "Suc b \<le> n"
        using b by simp
      thus "Suc b * n \<le> n * n"
        by (metis mult.commute mult_le_mono2)
    qed
    finally show ?thesis .
  qed
  have div_row: "(a*n + r) div n = a"
    using npos rn by simp
  have div_col: "(b*n + c) div n = b"
    using npos cn by simp
  have mod_row: "(a*n + r) mod n = r"
    using npos rn by simp
  have mod_col: "(b*n + c) mod n = c"
    using npos cn by simp
  have "block_of_mat n (choi_seed n) a b $$ (r,c)
      = choi_seed n $$ (a*n + r, b*n + c)"
    using rn cn by (simp add: block_of_mat_def)
  also have "\<dots> =
      mat_unit ((a*n + r) div n) ((b*n + c) div n) n n $$
        ((a*n + r) mod n, (b*n + c) mod n)"
    using row_lt col_lt by (simp add: choi_seed_def)
  also have "\<dots> = mat_unit a b n n $$ (r,c)"
    using div_row div_col mod_row mod_col by simp
  finally show "block_of_mat n (choi_seed n) a b $$ (r,c) = mat_unit a b n n $$ (r,c)".
qed

lemma choi_matrix_as_amplification:
  assumes npos: "n > 0"
      and dpos: "d > 0"
  shows "choi_matrix n d \<Phi> = amplification n d n \<Phi> (choi_seed n)"
proof (rule eq_matI)
  show "dim_row (choi_matrix n d \<Phi>) = dim_row (amplification n d n \<Phi> (choi_seed n))"
    by (simp add: choi_matrix_def amplification_def)
  show "dim_col (choi_matrix n d \<Phi>) = dim_col (amplification n d n \<Phi> (choi_seed n))"
    by (simp add: choi_matrix_def amplification_def)
next
  fix i j
  assume i: "i < dim_row (amplification n d n \<Phi> (choi_seed n))"
     and j: "j < dim_col (amplification n d n \<Phi> (choi_seed n))"
  then have id: "i < n*d" and jd: "j < n*d"
    by (simp_all add: amplification_def)
  have a_lt: "i div d < n"
    using id dpos by (simp add: div_less_iff_less_mult)
  have b_lt: "j div d < n"
    using jd dpos by (simp add: div_less_iff_less_mult)
  have "choi_matrix n d \<Phi> $$ (i,j)
      = \<Phi> (mat_unit (i div d) (j div d) n n) $$ (i mod d, j mod d)"
    using id jd by (simp add: choi_matrix_def)
  also have "\<dots> =
      \<Phi> (block_of_mat n (choi_seed n) (i div d) (j div d)) $$ (i mod d, j mod d)"
    using choi_seed_block[OF npos a_lt b_lt] by simp
  also have "\<dots> = amplification n d n \<Phi> (choi_seed n) $$ (i,j)"
    using id jd by (simp add: amplification_def)
  finally show "choi_matrix n d \<Phi> $$ (i,j) =
      amplification n d n \<Phi> (choi_seed n) $$ (i,j)".
qed

lemma choi_psd_if_cp:
  assumes npos: "n > 0"
      and dpos: "d > 0"
      and cp: "completely_positive n d \<Phi>"
  shows "psd (choi_matrix n d \<Phi>)"
proof -
  have pp: "p_positive n d n \<Phi>"
    using cp npos by (simp add: completely_positive_def)
  \<comment> \<open>The seed is the rank-one matrix \<open>v v\<^sup>\<dagger>\<close> for the (unnormalized) maximally
     entangled vector \<open>v = \<Sum>\<^sub>i e\<^sub>i \<otimes> e\<^sub>i\<close>, i.e. the \<open>n*n\<close>-vector that is 1 at
     position \<open>i*(n+1)\<close> for \<open>i < n\<close> and 0 elsewhere.\<close>
  define v :: "complex Matrix.vec" where
    "v = Matrix.vec (n*n) (\<lambda>r. if r div n = r mod n then 1 else 0)"
  have v_dim: "dim_vec v = n*n" by (simp add: v_def)
  let ?V = "mat_of_cols (n*n) [v]"
  have V_car: "?V \<in> carrier_mat (n*n) 1"
    by (simp add: mat_of_cols_def)
  have Vdag_car: "?V\<^sup>\<dagger> \<in> carrier_mat 1 (n*n)"
    using V_car by (simp add: dagger_def)
  have V_idx: "\<And>i. i < n*n \<Longrightarrow> ?V $$ (i,0) = v $ i"
    by (simp add: mat_of_cols_def)
  have Vdag_idx: "\<And>j. j < n*n \<Longrightarrow> (?V\<^sup>\<dagger>) $$ (0,j) = cnj (v $ j)"
    by (simp add: dagger_def mat_of_cols_def)
  have os_psd: "psd (outer_sum (n*n) [v])"
    using v_dim by (intro outer_sum_psd) auto
  have seed_eq: "choi_seed n = outer_sum (n*n) [v]"
  proof (rule eq_matI)
    show "dim_row (choi_seed n) = dim_row (outer_sum (n*n) [v])"
      by (simp add: choi_seed_def)
    show "dim_col (choi_seed n) = dim_col (outer_sum (n*n) [v])"
      by (simp add: choi_seed_def)
  next
    fix r c
    assume r_lt: "r < dim_row (outer_sum (n*n) [v])"
       and c_lt: "c < dim_col (outer_sum (n*n) [v])"
    hence rnn: "r < n*n" and cnn: "c < n*n" by simp_all
    have rdn: "r div n < n"
      using rnn npos by (simp add: div_less_iff_less_mult)
    have cdn: "c div n < n"
      using cnn npos by (simp add: div_less_iff_less_mult)
    have rmn: "r mod n < n" using npos by simp
    have cmn: "c mod n < n" using npos by simp
    have "choi_seed n $$ (r,c) =
          mat_unit (r div n) (c div n) n n $$ (r mod n, c mod n)"
      using rnn cnn by (simp add: choi_seed_def)
    also have "\<dots> = (if r mod n = r div n \<and> c mod n = c div n then 1 else 0)"
      using rmn cmn by simp
    also have "\<dots> = v $ r * cnj (v $ c)"
      using rnn cnn by (auto simp: v_def)
    also have "\<dots> = ?V $$ (r,0) * (?V\<^sup>\<dagger>) $$ (0,c)"
      using V_idx[OF rnn] Vdag_idx[OF cnn] by simp
    also have "\<dots> = (\<Sum>l<1. ?V $$ (r,l) * (?V\<^sup>\<dagger>) $$ (l,c))"
      by simp
    also have "\<dots> = (?V * (?V\<^sup>\<dagger>)) $$ (r,c)"
      using rnn cnn V_car Vdag_car
      by (simp add: index_mult_mat(1))
    also have "\<dots> = outer_sum (n*n) [v] $$ (r,c)"
      by (simp add: outer_sum_def)
    finally show "choi_seed n $$ (r,c) = outer_sum (n*n) [v] $$ (r,c)" .
  qed
  have seed_psd: "psd (choi_seed n)"
    using os_psd seed_eq by simp
  have "psd (amplification n d n \<Phi> (choi_seed n))"
    using pp seed_psd by (simp add: p_positive_def)
  thus ?thesis
    using choi_matrix_as_amplification[OF npos dpos, of \<Phi>] by simp
qed

(* ============================================================================
   Helpers for the reverse direction of Choi's theorem.
   ============================================================================ *)

text \<open>
  Complete positivity from a Kraus list without the trace-preservation
  constraint: the argument is the same as @{thm kraus_is_cp}, which only uses
  the carrier hypothesis.
\<close>
lemma kraus_cp_no_tp:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (kraus_map_dim d Ws)"
proof (unfold completely_positive_def p_positive_def, intro allI impI)
  fix p :: nat and X :: "complex Matrix.mat"
  assume ppos: "0 < p"
     and X_c: "X \<in> carrier_mat (p*n) (p*n)"
     and X_psd: "psd X"
  have lifted_c: "\<forall>L \<in> set (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws).
      L \<in> carrier_mat (p*d) (p*n)"
    using tensor_id_kraus_list_carrier[OF Ws_c] .
  have amp_eq: "amplification n d p (kraus_map_dim d Ws) X =
      kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) X"
    using amplification_kraus_map_dim[OF Ws_c X_c dpos npos] .
  show "psd (amplification n d p (kraus_map_dim d Ws) X)"
    using kraus_map_dim_psd[OF lifted_c X_c X_psd] amp_eq by simp
qed

text \<open>Linearity of the Kraus-sum map in its matrix argument.\<close>

lemma kraus_map_dim_add:
  assumes A_c: "A \<in> carrier_mat n n" and B_c: "B \<in> carrier_mat n n"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (A + B) =
         kraus_map_dim d Ws A + kraus_map_dim d Ws B"
  using Ws_c
proof (induction Ws)
  case Nil
  have "kraus_map_dim d [] (A + B) = 0\<^sub>m d d" by simp
  also have "\<dots> = (0\<^sub>m d d :: complex Matrix.mat) + 0\<^sub>m d d"
    by (intro eq_matI) auto
  also have "\<dots> = kraus_map_dim d [] A + kraus_map_dim d [] B"
    by simp
  finally show ?case .
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have WA_c: "W * A \<in> carrier_mat d n" using Wc A_c by auto
  have WB_c: "W * B \<in> carrier_mat d n" using Wc B_c by auto
  have WAD_c: "W * A * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using WA_c Wdag by auto
  have WBD_c: "W * B * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using WB_c Wdag by auto
  have rec_cA: "kraus_map_dim d Ws A \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' A_c] .
  have rec_cB: "kraus_map_dim d Ws B \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' B_c] .

  have sum_c: "A + B \<in> carrier_mat n n" using A_c B_c by auto
  have W_sum: "W * (A + B) = W * A + W * B"
    using Wc A_c B_c by (simp add: mult_add_distrib_mat)
  have "W * (A + B) * (W\<^sup>\<dagger>) = (W * A + W * B) * (W\<^sup>\<dagger>)"
    using W_sum by simp
  also have "\<dots> = W * A * (W\<^sup>\<dagger>) + W * B * (W\<^sup>\<dagger>)"
    using WA_c WB_c Wdag by (simp add: add_mult_distrib_mat)
  finally have term_split:
    "W * (A + B) * (W\<^sup>\<dagger>) = W * A * (W\<^sup>\<dagger>) + W * B * (W\<^sup>\<dagger>)" .

  have IH: "kraus_map_dim d Ws (A + B) =
            kraus_map_dim d Ws A + kraus_map_dim d Ws B"
    using Cons.IH[OF Ws_c'] .

  have "kraus_map_dim d (W # Ws) (A + B) =
        W * (A + B) * (W\<^sup>\<dagger>) + kraus_map_dim d Ws (A + B)"
    by simp
  also have "\<dots> = (W * A * (W\<^sup>\<dagger>) + W * B * (W\<^sup>\<dagger>))
                + (kraus_map_dim d Ws A + kraus_map_dim d Ws B)"
    using term_split IH by simp
  also have "\<dots> = (W * A * (W\<^sup>\<dagger>) + kraus_map_dim d Ws A)
                + (W * B * (W\<^sup>\<dagger>) + kraus_map_dim d Ws B)"
    using WAD_c WBD_c rec_cA rec_cB
    by (intro eq_matI) (auto simp: add.commute add.assoc)
  also have "\<dots> = kraus_map_dim d (W # Ws) A + kraus_map_dim d (W # Ws) B"
    by simp
  finally show ?case .
qed

lemma kraus_map_dim_smult:
  assumes A_c: "A \<in> carrier_mat n n"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m kraus_map_dim d Ws A"
  using Ws_c
proof (induction Ws)
  case Nil
  have "(c \<cdot>\<^sub>m 0\<^sub>m d d :: complex Matrix.mat) = 0\<^sub>m d d"
    by (intro eq_matI) auto
  thus ?case by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have WA_c: "W * A \<in> carrier_mat d n" using Wc A_c by auto
  have WAD_c: "W * A * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using WA_c Wdag by auto
  have rec_c: "kraus_map_dim d Ws A \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' A_c] .

  have W_scale: "W * (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m (W * A)"
    using Wc A_c by (simp add: mult_smult_distrib)
  have "W * (c \<cdot>\<^sub>m A) * (W\<^sup>\<dagger>) = (c \<cdot>\<^sub>m (W * A)) * (W\<^sup>\<dagger>)"
    using W_scale by simp
  also have "\<dots> = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>))"
    using WA_c Wdag by (simp add: mult_smult_assoc_mat)
  finally have term_eq:
    "W * (c \<cdot>\<^sub>m A) * (W\<^sup>\<dagger>) = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>))" .

  have IH: "kraus_map_dim d Ws (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m kraus_map_dim d Ws A"
    using Cons.IH[OF Ws_c'] .

  have "kraus_map_dim d (W # Ws) (c \<cdot>\<^sub>m A) =
        W * (c \<cdot>\<^sub>m A) * (W\<^sup>\<dagger>) + kraus_map_dim d Ws (c \<cdot>\<^sub>m A)"
    by simp
  also have "\<dots> = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>)) + c \<cdot>\<^sub>m kraus_map_dim d Ws A"
    using term_eq IH by simp
  also have "\<dots> = c \<cdot>\<^sub>m (W * A * (W\<^sup>\<dagger>) + kraus_map_dim d Ws A)"
    using WAD_c rec_c by (simp add: add_smult_distrib_left_mat)
  also have "\<dots> = c \<cdot>\<^sub>m kraus_map_dim d (W # Ws) A"
    by simp
  finally show ?case .
qed

lemma kraus_map_dim_zero [simp]:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "kraus_map_dim d Ws (0\<^sub>m n n) = 0\<^sub>m d d"
  using Ws_c
proof (induction Ws)
  case Nil show ?case by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have W0: "W * (0\<^sub>m n n) = 0\<^sub>m d n"
    using Wc by (metis right_mult_zero_mat carrier_matD(2))
  have term_zero: "W * (0\<^sub>m n n) * (W\<^sup>\<dagger>) = 0\<^sub>m d d"
    using W0 Wdag by (metis left_mult_zero_mat carrier_matD)
  have IH: "kraus_map_dim d Ws (0\<^sub>m n n) = 0\<^sub>m d d" using Cons.IH[OF Ws_c'] .
  have "kraus_map_dim d (W # Ws) (0\<^sub>m n n) =
        W * (0\<^sub>m n n) * (W\<^sup>\<dagger>) + kraus_map_dim d Ws (0\<^sub>m n n)"
    by simp
  also have "\<dots> = 0\<^sub>m d d + 0\<^sub>m d d"
    using term_zero IH by simp
  also have "\<dots> = 0\<^sub>m d d"
    by (intro eq_matI) auto
  finally show ?case .
qed

text \<open>Enumeration of \<open>[0..<n] \<times> [0..<n]\<close> as a list of pairs.\<close>

definition mat_unit_pairs :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "mat_unit_pairs n \<equiv>
     concat (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"

lemma mat_unit_pairs_set:
  "set (mat_unit_pairs n) = {p. fst p < n \<and> snd p < n}"
  unfolding mat_unit_pairs_def by auto

lemma mat_unit_pairs_distinct: "distinct (mat_unit_pairs n)"
  unfolding mat_unit_pairs_def
proof (intro distinct_concat)
  have inj: "inj_on (\<lambda>a. map (Pair a) [0..<n]) (set [0..<n])"
  proof (rule inj_onI)
    fix a1 a2
    assume a1_in: "a1 \<in> set [0..<n]" and a2_in: "a2 \<in> set [0..<n]"
       and eq: "map (Pair a1) [0..<n] = map (Pair a2) [0..<n]"
    have npos: "0 < n" using a1_in by simp
    from eq show "a1 = a2" using npos by auto
  qed
  show "distinct (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"
    using inj by (simp add: distinct_map)
next
  fix ys
  assume "ys \<in> set (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"
  thus "distinct ys"
    by (auto simp: distinct_map inj_on_def)
next
  fix ys zs
  assume "ys \<in> set (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"
     and "zs \<in> set (map (\<lambda>a. map (Pair a) [0..<n]) [0..<n])"
     and "ys \<noteq> zs"
  thus "set ys \<inter> set zs = {}"
    by auto
qed

text \<open>Generic pair-indexed linear combination of \<open>f (E\<^sub>a\<^sub>b)\<close> contributions,
  weighted by the entries of \<open>A\<close>.\<close>

primrec pair_comb ::
  "(complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> complex Matrix.mat" where
  "pair_comb f A n d [] = 0\<^sub>m d d" |
  "pair_comb f A n d (p # ps) =
     A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n) + pair_comb f A n d ps"

lemma pair_comb_carrier:
  assumes f_car: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> f (mat_unit a b n n) \<in> carrier_mat d d"
      and ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
  shows "pair_comb f A n d ps \<in> carrier_mat d d"
  using ps_valid
proof (induction ps)
  case Nil show ?case by simp
next
  case (Cons p ps)
  obtain a b where p_eq: "p = (a,b)" by (cases p)
  hence a_lt: "a < n" and b_lt: "b < n"
    using Cons.prems by auto
  have fE_car: "f (mat_unit a b n n) \<in> carrier_mat d d"
    using f_car[OF a_lt b_lt] .
  have smult_c: "A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n) \<in> carrier_mat d d"
    using fE_car p_eq by simp
  have rec_c: "pair_comb f A n d ps \<in> carrier_mat d d"
    using Cons by auto
  show ?case using smult_c rec_c by simp
qed

lemma pair_comb_entry:
  assumes f_car: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> f (mat_unit a b n n) \<in> carrier_mat d d"
      and ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
      and r_lt: "r < d" and c_lt: "c < d"
  shows "pair_comb f A n d ps $$ (r,c) =
         (\<Sum>p \<leftarrow> ps. A $$ p * f (mat_unit (fst p) (snd p) n n) $$ (r,c))"
  using ps_valid
proof (induction ps)
  case Nil
  show ?case using r_lt c_lt by simp
next
  case (Cons p ps)
  obtain a b where p_eq: "p = (a,b)" by (cases p)
  hence a_lt: "a < n" and b_lt: "b < n"
    using Cons.prems by auto
  have fE_car: "f (mat_unit a b n n) \<in> carrier_mat d d"
    using f_car[OF a_lt b_lt] .
  have smult_c: "A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n) \<in> carrier_mat d d"
    using fE_car p_eq by simp
  have rec_c: "pair_comb f A n d ps \<in> carrier_mat d d"
    using Cons.prems f_car pair_comb_carrier[where f=f] by auto
  have IH: "pair_comb f A n d ps $$ (r,c) =
            (\<Sum>q \<leftarrow> ps. A $$ q * f (mat_unit (fst q) (snd q) n n) $$ (r,c))"
    using Cons by auto
  have "pair_comb f A n d (p # ps) $$ (r,c) =
        (A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n) + pair_comb f A n d ps) $$ (r,c)"
    by simp
  also have "\<dots> = (A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)) $$ (r,c)
                + pair_comb f A n d ps $$ (r,c)"
    using smult_c rec_c r_lt c_lt by simp
  also have "(A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)) $$ (r,c)
           = A $$ p * f (mat_unit (fst p) (snd p) n n) $$ (r,c)"
    using fE_car r_lt c_lt p_eq by simp
  finally show ?case using IH by simp
qed

text \<open>For the identity-like choice \<open>f = id\<close>, the pair combination reconstructs
  \<open>A\<close> when \<open>ps\<close> enumerates all basis positions.\<close>

lemma pair_comb_id_reconstructs:
  assumes A_car: "A \<in> carrier_mat n n"
  shows "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) = A"
proof (rule eq_matI)
  have ps_valid: "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
    using mat_unit_pairs_set by auto
  have comb_car: "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) \<in> carrier_mat n n"
  proof (rule pair_comb_carrier)
    fix a b :: nat
    assume "a < n" "b < n"
    show "(\<lambda>X. X) (mat_unit a b n n) \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
  qed (use ps_valid in auto)
  show "dim_row (pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n)) = dim_row A"
    using comb_car A_car by auto
  show "dim_col (pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n)) = dim_col A"
    using comb_car A_car by auto
next
  fix r c
  assume "r < dim_row A" "c < dim_col A"
  hence r_lt: "r < n" and c_lt: "c < n"
    using A_car by auto
  have ps_valid: "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
    using mat_unit_pairs_set by auto
  have pc_entry:
    "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) $$ (r,c) =
     (\<Sum>p \<leftarrow> mat_unit_pairs n. A $$ p * (\<lambda>X. X) (mat_unit (fst p) (snd p) n n) $$ (r,c))"
  proof (rule pair_comb_entry)
    fix a b :: nat
    assume "a < n" "b < n"
    show "(\<lambda>X. X) (mat_unit a b n n) \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
  qed (use ps_valid r_lt c_lt in auto)
  have "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) $$ (r,c) =
        (\<Sum>p \<leftarrow> mat_unit_pairs n. A $$ p * mat_unit (fst p) (snd p) n n $$ (r,c))"
    using pc_entry by simp
  also have "\<dots> = (\<Sum>p \<leftarrow> mat_unit_pairs n.
                    A $$ p * (if fst p = r \<and> snd p = c then 1 else 0))"
    using r_lt c_lt
    by (intro arg_cong[where f=sum_list] list.map_cong refl)
       (auto simp: case_prod_beta)
  also have "\<dots> = (\<Sum>p \<leftarrow> mat_unit_pairs n.
                    (if p = (r,c) then A $$ (r,c) else 0))"
    by (intro arg_cong[where f=sum_list] list.map_cong refl)
       (auto simp: prod_eq_iff)
  also have "\<dots> = A $$ (r,c)"
  proof -
    have rc_in: "(r,c) \<in> set (mat_unit_pairs n)"
      using r_lt c_lt by (simp add: mat_unit_pairs_set)
    have dist: "distinct (mat_unit_pairs n)"
      by (rule mat_unit_pairs_distinct)
    have "(\<Sum>p \<leftarrow> mat_unit_pairs n.
             (if p = (r,c) then A $$ (r,c) else 0))
          = (\<Sum>p \<in> set (mat_unit_pairs n).
               (if p = (r,c) then A $$ (r,c) else 0))"
      using dist by (rule sum_list_distinct_conv_sum_set)
    also have "\<dots> = A $$ (r,c)"
      using rc_in by (subst sum.delta_remove) auto
    finally show ?thesis .
  qed
  finally show "pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n) $$ (r,c) = A $$ (r,c)"
    by simp
qed

text \<open>For a linear map \<open>f : M\<^sub>n \<rightarrow> M\<^sub>d\<close>, applying \<open>f\<close> to \<open>A\<close> equals the
  pair combination of \<open>f\<close> evaluated on the basis.\<close>

lemma linear_eq_pair_comb:
  fixes f :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes f_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n \<Longrightarrow>
                   f (X + Y) = f X + f Y"
      and f_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow> f (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m f X"
      and f_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> f X \<in> carrier_mat d d"
      and A_car: "A \<in> carrier_mat n n"
      and npos: "n > 0" and dpos: "d > 0"
  shows "f A = pair_comb f A n d (mat_unit_pairs n)"
proof -
  have Eab_car: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> mat_unit a b n n \<in> carrier_mat n n"
    by (simp add: mat_unit_def)
  have fEab_car: "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow> f (mat_unit a b n n) \<in> carrier_mat d d"
    using f_car Eab_car by blast
  have f_zero: "f (0\<^sub>m n n) = 0\<^sub>m d d"
  proof -
    have zc: "0\<^sub>m n n \<in> carrier_mat n n" by auto
    have "f (0\<^sub>m n n) = f (0 \<cdot>\<^sub>m 0\<^sub>m n n)"
      by (intro arg_cong[where f=f]) (rule eq_matI, auto)
    also have "\<dots> = 0 \<cdot>\<^sub>m f (0\<^sub>m n n)"
      using f_smult[OF zc] by simp
    also have "\<dots> = 0\<^sub>m d d"
      using f_car[OF zc] by (intro eq_matI) auto
    finally show ?thesis.
  qed
  \<comment> \<open>Key induction: for any list \<open>ps\<close> of valid pairs, \<open>f\<close> applied to the
     \<open>\<lambda>X. X\<close> pair-combination equals the \<open>f\<close> pair-combination.\<close>
  have gen: "\<And>ps. (\<forall>p \<in> set ps. fst p < n \<and> snd p < n) \<Longrightarrow>
              f (pair_comb (\<lambda>X. X) A n n ps) = pair_comb f A n d ps"
  proof -
    fix ps :: "(nat \<times> nat) list"
    assume ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
    show "f (pair_comb (\<lambda>X. X) A n n ps) = pair_comb f A n d ps"
      using ps_valid
    proof (induction ps)
      case Nil
      show ?case using f_zero by simp
    next
      case (Cons p ps)
      obtain a b where p_eq: "p = (a,b)" by (cases p)
      hence a_lt: "a < n" and b_lt: "b < n"
        using Cons.prems by auto
      have Eab_c: "mat_unit a b n n \<in> carrier_mat n n"
        using a_lt b_lt Eab_car by simp
      have smult_Eab_c: "A $$ p \<cdot>\<^sub>m mat_unit (fst p) (snd p) n n \<in> carrier_mat n n"
        using Eab_c p_eq by simp
      have ps_valid': "\<forall>q \<in> set ps. fst q < n \<and> snd q < n"
        using Cons.prems by simp
      have rec_c: "pair_comb (\<lambda>X. X) A n n ps \<in> carrier_mat n n"
      proof (rule pair_comb_carrier)
        fix a b :: nat
        assume "a < n" "b < n"
        show "(\<lambda>X. X) (mat_unit a b n n) \<in> carrier_mat n n"
          by (simp add: mat_unit_def)
      qed (use ps_valid' in auto)
      have "f (pair_comb (\<lambda>X. X) A n n (p # ps)) =
            f (A $$ p \<cdot>\<^sub>m mat_unit (fst p) (snd p) n n + pair_comb (\<lambda>X. X) A n n ps)"
        by simp
      also have "\<dots> = f (A $$ p \<cdot>\<^sub>m mat_unit (fst p) (snd p) n n)
                    + f (pair_comb (\<lambda>X. X) A n n ps)"
        using f_add[OF smult_Eab_c rec_c] by simp
      also have "\<dots> = A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)
                    + f (pair_comb (\<lambda>X. X) A n n ps)"
      proof -
        have "f (A $$ p \<cdot>\<^sub>m mat_unit (fst p) (snd p) n n)
              = A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)"
          using f_smult[OF Eab_c] p_eq by simp
        thus ?thesis by simp
      qed
      also have "\<dots> = A $$ p \<cdot>\<^sub>m f (mat_unit (fst p) (snd p) n n)
                    + pair_comb f A n d ps"
        using Cons.IH[OF ps_valid'] by simp
      also have "\<dots> = pair_comb f A n d (p # ps)"
        by simp
      finally show ?case.
    qed
  qed
  have ps_valid_full: "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
    using mat_unit_pairs_set by auto
  have "f A = f (pair_comb (\<lambda>X. X) A n n (mat_unit_pairs n))"
    using pair_comb_id_reconstructs[OF A_car] by simp
  also have "\<dots> = pair_comb f A n d (mat_unit_pairs n)"
    using gen[OF ps_valid_full].
  finally show ?thesis.
qed

text \<open>Conjugation \<open>W E\<^sub>a\<^sub>b W\<^sup>\<dagger>\<close> has entry \<open>W\<^sub>i\<^sub>a\<cdot>\<^sup>\<dagger>W\<^sub>j\<^sub>b\<close>.\<close>

lemma conjugation_mat_unit_entry:
  assumes Wc: "W \<in> carrier_mat d n"
      and a_lt: "a < n" and b_lt: "b < n"
      and i_lt: "i < d" and j_lt: "j < d"
  shows "(W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
         W $$ (i, a) * cnj (W $$ (j, b))"
proof -
  have Eab_c: "mat_unit a b n n \<in> carrier_mat n n"
    by (simp add: mat_unit_def)
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have WE_c: "W * mat_unit a b n n \<in> carrier_mat d n"
    using Wc Eab_c by auto
  have dim_WE: "dim_col (W * mat_unit a b n n) = n"
    using WE_c by auto
  have dim_W: "dim_col W = n" using Wc by auto
  have i_WE: "i < dim_row (W * mat_unit a b n n)"
    using WE_c i_lt by auto
  have j_Wdag: "j < dim_col (W\<^sup>\<dagger>)"
    using Wdag_c j_lt by auto
  have "(W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)
      = Matrix.row (W * mat_unit a b n n) i \<bullet> Matrix.col (W\<^sup>\<dagger>) j"
    using index_mult_mat(1)[OF i_WE j_Wdag].
  also have "\<dots> = (\<Sum>p<n.
        Matrix.row (W * mat_unit a b n n) i $ p * Matrix.col (W\<^sup>\<dagger>) j $ p)"
    unfolding scalar_prod_def using dim_WE dim_W Wdag_c
    by (simp add: atLeast0LessThan)
  also have "\<dots> = (\<Sum>p<n.
        (W * mat_unit a b n n) $$ (i, p) * (W\<^sup>\<dagger>) $$ (p, j))"
  proof (intro sum.cong refl)
    fix p assume "p \<in> {..<n}"
    hence p_lt: "p < n" by simp
    have "Matrix.row (W * mat_unit a b n n) i $ p = (W * mat_unit a b n n) $$ (i, p)"
      using i_WE p_lt dim_WE by simp
    moreover have "Matrix.col (W\<^sup>\<dagger>) j $ p = (W\<^sup>\<dagger>) $$ (p, j)"
      using Wdag_c j_lt p_lt
      by (metis carrier_matD(1) carrier_matD(2) index_col)
    ultimately show "Matrix.row (W * mat_unit a b n n) i $ p *
                     Matrix.col (W\<^sup>\<dagger>) j $ p
                   = (W * mat_unit a b n n) $$ (i, p) * (W\<^sup>\<dagger>) $$ (p, j)"
      by simp
  qed
  also have "\<dots> = (\<Sum>p<n.
        (\<Sum>q<n. W $$ (i, q) * mat_unit a b n n $$ (q, p)) * (W\<^sup>\<dagger>) $$ (p, j))"
  proof (intro sum.cong refl)
    fix p assume "p \<in> {..<n}"
    hence p_lt: "p < n" by simp
    have i_W: "i < dim_row W" using Wc i_lt by auto
    have p_E: "p < dim_col (mat_unit a b n n)" using Eab_c p_lt by simp
    have "(W * mat_unit a b n n) $$ (i, p) =
          Matrix.row W i \<bullet> Matrix.col (mat_unit a b n n) p"
      using index_mult_mat(1)[OF i_W p_E] .
    also have "\<dots> = (\<Sum>q<n. Matrix.row W i $ q *
                           Matrix.col (mat_unit a b n n) p $ q)"
      unfolding scalar_prod_def using dim_W
      by (simp add: atLeast0LessThan)
    also have "\<dots> = (\<Sum>q<n. W $$ (i, q) * mat_unit a b n n $$ (q, p))"
    proof (intro sum.cong refl)
      fix q assume "q \<in> {..<n}"
      hence q_lt: "q < n" by simp
      have "Matrix.row W i $ q = W $$ (i, q)"
        using i_W q_lt dim_W by simp
      moreover have
        "Matrix.col (mat_unit a b n n) p $ q = mat_unit a b n n $$ (q, p)"
        using Eab_c p_lt q_lt by simp
      ultimately show "Matrix.row W i $ q * Matrix.col (mat_unit a b n n) p $ q
                     = W $$ (i, q) * mat_unit a b n n $$ (q, p)"
        by simp
    qed
    finally show
      "(W * mat_unit a b n n) $$ (i, p) * (W\<^sup>\<dagger>) $$ (p, j) =
       (\<Sum>q<n. W $$ (i, q) * mat_unit a b n n $$ (q, p)) * (W\<^sup>\<dagger>) $$ (p, j)"
      by simp
  qed
  also have "\<dots> = (\<Sum>p<n.
        (\<Sum>q<n. W $$ (i, q) * (if q = a \<and> p = b then 1 else 0))
           * (W\<^sup>\<dagger>) $$ (p, j))"
    by (intro sum.cong refl) (simp)
  also have "\<dots> = (\<Sum>p<n.
        (if p = b then W $$ (i, a) else 0) * (W\<^sup>\<dagger>) $$ (p, j))"
  proof (intro sum.cong refl)
    fix p assume "p \<in> {..<n}"
    hence p_lt: "p < n" by simp
    have "(\<Sum>q<n. W $$ (i, q) * (if q = a \<and> p = b then 1 else 0))
        = (\<Sum>q<n. if q = a \<and> p = b then W $$ (i, q) else 0)"
      by (intro sum.cong refl) simp
    also have "\<dots> = (if p = b then W $$ (i, a) else 0)"
      using a_lt by simp
    finally show "(\<Sum>q<n. W $$ (i, q) * (if q = a \<and> p = b then 1 else 0))
               * (W\<^sup>\<dagger>) $$ (p, j)
               = (if p = b then W $$ (i, a) else 0) * (W\<^sup>\<dagger>) $$ (p, j)"
      by simp
  qed
  also have "\<dots> = (\<Sum>p<n. if p = b then W $$ (i, a) * (W\<^sup>\<dagger>) $$ (p, j) else 0)"
    by (intro sum.cong refl) simp
  also have "\<dots> = W $$ (i, a) * (W\<^sup>\<dagger>) $$ (b, j)"
    using b_lt by simp
  also have "(W\<^sup>\<dagger>) $$ (b, j) = cnj (W $$ (j, b))"
    using Wc b_lt j_lt by (simp add: dagger_def)
  finally show ?thesis.
qed

text \<open>Entry-wise formula for @{const kraus_map_dim} as a sum over the list.\<close>

lemma kraus_map_dim_entry_sum_list:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and rho_c: "\<rho> \<in> carrier_mat n n"
      and i_lt: "i < d" and j_lt: "j < d"
  shows "kraus_map_dim d Ws \<rho> $$ (i, j) =
         sum_list (map (\<lambda>W. (W * \<rho> * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
  using Ws_c
proof (induction Ws)
  case Nil
  show ?case using i_lt j_lt by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n" and Ws_c': "\<forall>X \<in> set Ws. X \<in> carrier_mat d n"
    by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have Wr_c: "W * \<rho> \<in> carrier_mat d n" using Wc rho_c by auto
  have WrW_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using Wr_c Wdag_c by auto
  have rec_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' rho_c] .
  have IH: "kraus_map_dim d Ws \<rho> $$ (i, j) =
            sum_list (map (\<lambda>W. (W * \<rho> * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
    using Cons.IH[OF Ws_c'] .
  show "kraus_map_dim d (W # Ws) \<rho> $$ (i, j)
      = sum_list (map (\<lambda>W. (W * \<rho> * (W\<^sup>\<dagger>)) $$ (i, j)) (W # Ws))"
    using IH WrW_c rec_c i_lt j_lt by simp
qed

text \<open>Entry-wise formula for @{const outer_sum} without orthonormality.\<close>

lemma outer_sum_entry_sum_list:
  assumes vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
      and i_lt: "i < n" and j_lt: "j < n"
  shows "outer_sum n vs $$ (i, j) =
         sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) vs)"
proof -
  let ?V = "mat_of_cols n vs"
  let ?k = "length vs"
  have V_c: "?V \<in> carrier_mat n ?k"
    using vs_dim by (simp add: mat_of_cols_def)
  have Vdag_c: "?V\<^sup>\<dagger> \<in> carrier_mat ?k n"
    using V_c by (rule dagger_carrier)
  have "outer_sum n vs $$ (i, j) = (?V * (?V\<^sup>\<dagger>)) $$ (i, j)"
    by (simp add: outer_sum_def)
  also have "\<dots> = (\<Sum>l<?k. ?V $$ (i, l) * (?V\<^sup>\<dagger>) $$ (l, j))"
    using i_lt j_lt V_c Vdag_c by simp
  also have "\<dots> = (\<Sum>l<?k. (vs ! l) $ i * cnj ((vs ! l) $ j))"
  proof (intro sum.cong refl)
    fix l assume "l \<in> {..<?k}"
    hence l_lt: "l < ?k" by simp
    have vl_dim: "dim_vec (vs ! l) = n" using vs_dim l_lt by auto
    have V_idx: "?V $$ (i, l) = (vs ! l) $ i"
      using i_lt l_lt by (simp add: mat_of_cols_def)
    have Vdag_idx: "(?V\<^sup>\<dagger>) $$ (l, j) = cnj ((vs ! l) $ j)"
      using j_lt l_lt vl_dim by (simp add: dagger_def mat_of_cols_def)
    show "?V $$ (i, l) * (?V\<^sup>\<dagger>) $$ (l, j) = (vs ! l) $ i * cnj ((vs ! l) $ j)"
      using V_idx Vdag_idx by simp
  qed
  also have "\<dots> = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) vs)"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  finally show ?thesis.
qed

text \<open>Kraus representation extracted from a psd Choi matrix: reshape each
  column of a psd factorization of \<open>P\<^sub>\<Phi>\<close> into a Kraus operator, and the
  resulting list agrees with \<open>\<Phi>\<close> on all of \<open>M\<^sub>n\<close>.\<close>

lemma kraus_rep_of_psd_choi:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
      and psdP: "psd (choi_matrix n d \<Phi>)"
  shows "\<exists>Ws :: complex Matrix.mat list.
           length Ws = n * d \<and>
           (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and>
           (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
proof -
  have P_car: "choi_matrix n d \<Phi> \<in> carrier_mat (n*d) (n*d)"
    by (simp add: choi_matrix_def)
  (* Extract a length-aware psd factorisation of the Choi matrix.  We
     spell out the existential elimination explicitly: obtain a
     witness \<open>vs\<^sub>0\<close> from \<open>psd_kraus_decomp\<close>, decompose its
     conjunctive predicate, and re-introduce \<open>vs\<close> with the three
     named facts. *)
  obtain vs :: "complex Matrix.vec list"
    where vs_len: "length vs = n*d"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n*d"
      and vs_sum: "outer_sum (n*d) vs = choi_matrix n d \<Phi>"
  proof -
    have ex_decomp:
      "\<exists>vs :: complex Matrix.vec list.
          length vs = n*d
          \<and> (\<forall>v \<in> set vs. dim_vec v = n*d)
          \<and> outer_sum (n*d) vs = choi_matrix n d \<Phi>"
      using psd_kraus_decomp[OF P_car psdP] .
    obtain vs\<^sub>0 :: "complex Matrix.vec list"
      where vs\<^sub>0_props:
        "length vs\<^sub>0 = n*d
         \<and> (\<forall>v \<in> set vs\<^sub>0. dim_vec v = n*d)
         \<and> outer_sum (n*d) vs\<^sub>0 = choi_matrix n d \<Phi>"
      using ex_decomp by (elim exE)
    from vs\<^sub>0_props
    have len: "length vs\<^sub>0 = n*d"
      and dim: "\<forall>v \<in> set vs\<^sub>0. dim_vec v = n*d"
      and sum: "outer_sum (n*d) vs\<^sub>0 = choi_matrix n d \<Phi>"
      by (rule conjunct1, rule conjunct1[OF conjunct2],
          rule conjunct2[OF conjunct2])
    show thesis using that[OF len dim sum] .
  qed
  define Ws :: "complex Matrix.mat list" where
    "Ws = map (\<lambda>v. Matrix.mat d n (\<lambda>(i, a). v $ (a*d + i))) vs"
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    by (auto simp: Ws_def)
  have len_Ws: "length Ws = length vs"
    by (simp add: Ws_def)

  have match_unit:
    "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow>
       \<Phi> (mat_unit a b n n) = kraus_map_dim d Ws (mat_unit a b n n)"
  proof -
    fix a b assume a_lt: "a < n" and b_lt: "b < n"
    have Eab_c: "mat_unit a b n n \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
    have \<Phi>Eab_c: "\<Phi> (mat_unit a b n n) \<in> carrier_mat d d"
      using range Eab_c by blast
    have kmd_c: "kraus_map_dim d Ws (mat_unit a b n n) \<in> carrier_mat d d"
      using kraus_map_dim_carrier[OF Ws_c Eab_c] .
    show "\<Phi> (mat_unit a b n n) = kraus_map_dim d Ws (mat_unit a b n n)"
    proof (rule eq_matI)
      show "dim_row (\<Phi> (mat_unit a b n n)) =
            dim_row (kraus_map_dim d Ws (mat_unit a b n n))"
        using \<Phi>Eab_c kmd_c by auto
      show "dim_col (\<Phi> (mat_unit a b n n)) =
            dim_col (kraus_map_dim d Ws (mat_unit a b n n))"
        using \<Phi>Eab_c kmd_c by auto
    next
      fix i j
      assume "i < dim_row (kraus_map_dim d Ws (mat_unit a b n n))"
             "j < dim_col (kraus_map_dim d Ws (mat_unit a b n n))"
      hence i_lt: "i < d" and j_lt: "j < d"
        using kmd_c by auto
      have adi_lt: "a*d + i < n*d"
        using a_lt i_lt
        by (metis Nat.add_0_right div_less div_less_iff_less_mult div_mult_self3 dpos not_less0)
      have bdj_lt: "b*d + j < n*d"
        using b_lt j_lt
        by (metis Nat.add_0_right div_less div_less_iff_less_mult div_mult_self3 dpos not_less0)
      have adi_div: "(a*d + i) div d = a" using i_lt dpos by simp
      have bdj_div: "(b*d + j) div d = b" using j_lt dpos by simp
      have adi_mod: "(a*d + i) mod d = i" using i_lt dpos by simp
      have bdj_mod: "(b*d + j) mod d = j" using j_lt dpos by simp
      have "\<Phi> (mat_unit a b n n) $$ (i, j)
          = choi_matrix n d \<Phi> $$ (a*d + i, b*d + j)"
        using adi_lt bdj_lt adi_div bdj_div adi_mod bdj_mod
        by (simp add: choi_matrix_def)
      also have "\<dots> = outer_sum (n*d) vs $$ (a*d + i, b*d + j)"
        using vs_sum by simp
      also have "\<dots> = sum_list (map (\<lambda>v. v $ (a*d + i) * cnj (v $ (b*d + j))) vs)"
        using outer_sum_entry_sum_list[OF vs_dim adi_lt bdj_lt] .
      also have "\<dots> = sum_list (map (\<lambda>W. (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
      proof -
        have point_eq:
          "\<And>W. W \<in> set Ws \<Longrightarrow>
              (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
              W $$ (i, a) * cnj (W $$ (j, b))"
        proof -
          fix W assume W_in: "W \<in> set Ws"
          have Wc_k: "W \<in> carrier_mat d n" using Ws_c W_in by simp
          show "(W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
                W $$ (i, a) * cnj (W $$ (j, b))"
            using conjugation_mat_unit_entry[OF Wc_k a_lt b_lt i_lt j_lt] .
        qed
        have "sum_list (map (\<lambda>v. v $ (a*d + i) * cnj (v $ (b*d + j))) vs) =
              sum_list (map (\<lambda>W. W $$ (i, a) * cnj (W $$ (j, b))) Ws)"
          unfolding Ws_def
          using i_lt a_lt j_lt b_lt
          by (induction vs) simp_all
        also have "\<dots> = sum_list (map (\<lambda>W. (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
          using point_eq
          by (intro arg_cong[where f=sum_list] map_cong refl) (metis)
        finally show ?thesis.
      qed
      also have "\<dots> = kraus_map_dim d Ws (mat_unit a b n n) $$ (i, j)"
        using kraus_map_dim_entry_sum_list[OF Ws_c Eab_c i_lt j_lt] by simp
      finally show "\<Phi> (mat_unit a b n n) $$ (i, j) =
                    kraus_map_dim d Ws (mat_unit a b n n) $$ (i, j)".
    qed
  qed

  have kmd_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws (X + Y) = kraus_map_dim d Ws X + kraus_map_dim d Ws Y"
    using kraus_map_dim_add Ws_c by blast
  have kmd_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m kraus_map_dim d Ws X"
    using kraus_map_dim_smult Ws_c by blast
  have kmd_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws X \<in> carrier_mat d d"
    using kraus_map_dim_carrier Ws_c by blast
  have \<Phi>_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X \<in> carrier_mat d d"
    using range by blast

  have phi_eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
  proof (intro allI impI)
    fix A :: "complex Matrix.mat" assume Ac: "A \<in> carrier_mat n n"
    have lhs: "\<Phi> A = pair_comb \<Phi> A n d (mat_unit_pairs n)"
      using linear_eq_pair_comb[OF linear smult \<Phi>_car Ac npos dpos] .
    have rhs: "kraus_map_dim d Ws A =
               pair_comb (kraus_map_dim d Ws) A n d (mat_unit_pairs n)"
      using linear_eq_pair_comb[OF kmd_add kmd_smult kmd_car Ac npos dpos] .
    have comb_eq:
      "pair_comb \<Phi> A n d (mat_unit_pairs n) =
       pair_comb (kraus_map_dim d Ws) A n d (mat_unit_pairs n)"
    proof -
      have "\<And>ps. (\<forall>p \<in> set ps. fst p < n \<and> snd p < n) \<Longrightarrow>
          pair_comb \<Phi> A n d ps = pair_comb (kraus_map_dim d Ws) A n d ps"
      proof -
        fix ps :: "(nat \<times> nat) list"
        assume ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
        show "pair_comb \<Phi> A n d ps =
              pair_comb (kraus_map_dim d Ws) A n d ps"
          using ps_valid
        proof (induction ps)
          case Nil show ?case by simp
        next
          case (Cons p ps)
          obtain a b where p_eq: "p = (a, b)" by (cases p)
          hence a_lt: "a < n" and b_lt: "b < n"
            using Cons.prems by auto
          have basis_eq: "\<Phi> (mat_unit (fst p) (snd p) n n) =
                          kraus_map_dim d Ws (mat_unit (fst p) (snd p) n n)"
            using match_unit[OF a_lt b_lt] p_eq by simp
          have IH: "pair_comb \<Phi> A n d ps =
                    pair_comb (kraus_map_dim d Ws) A n d ps"
            using Cons by auto
          show ?case using basis_eq IH by simp
        qed
      qed
      moreover have "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
        using mat_unit_pairs_set by auto
      ultimately show ?thesis by blast
    qed
    show "\<Phi> A = kraus_map_dim d Ws A"
      using lhs rhs comb_eq by simp
  qed

  have Ws_len: "length Ws = n * d"
    using vs_len len_Ws by simp
  show ?thesis using Ws_len Ws_c phi_eq by blast
qed

theorem choi_theorem:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
  shows "completely_positive n d \<Phi> \<longleftrightarrow>
         psd (choi_matrix n d \<Phi>)"
proof
  assume "completely_positive n d \<Phi>"
  thus "psd (choi_matrix n d \<Phi>)"
    using choi_psd_if_cp[OF npos dpos] by simp
next
  assume psdP: "psd (choi_matrix n d \<Phi>)"
  \<comment> \<open>Factor \<open>P\<^sub>\<Phi> = \<Sum>\<^sub>k v\<^sub>k v\<^sub>k\<^sup>\<dagger>\<close> and reshape each \<open>v\<^sub>k \<in> \<complex>\<^bsup>nd\<^esup>\<close> into a
     \<open>d \<times> n\<close> Kraus operator \<open>W\<^sub>k\<close>.  Each \<open>W\<^sub>k\<close> is given by
     \<open>(W\<^sub>k)\<^sub>i\<^sub>a = v\<^sub>k $ (a*d + i)\<close>, matching the Choi-index convention.\<close>
  have P_car: "choi_matrix n d \<Phi> \<in> carrier_mat (n*d) (n*d)"
    by (simp add: choi_matrix_def)
  obtain vs :: "complex Matrix.vec list"
    where vs_len: "length vs = n*d"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n*d"
      and vs_sum: "outer_sum (n*d) vs = choi_matrix n d \<Phi>"
    using psd_kraus_decomp[OF P_car psdP] by blast
  define Ws :: "complex Matrix.mat list" where
    "Ws = map (\<lambda>v. Matrix.mat d n (\<lambda>(i, a). v $ (a*d + i))) vs"
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    by (auto simp: Ws_def)
  have len_Ws: "length Ws = length vs"
    by (simp add: Ws_def)

  \<comment> \<open>Step 1: \<open>\<Phi>(E\<^sub>a\<^sub>b) = kraus_map_dim d Ws E\<^sub>a\<^sub>b\<close> for \<open>a, b < n\<close>.\<close>
  have match_unit:
    "\<And>a b. a < n \<Longrightarrow> b < n \<Longrightarrow>
       \<Phi> (mat_unit a b n n) = kraus_map_dim d Ws (mat_unit a b n n)"
  proof -
    fix a b assume a_lt: "a < n" and b_lt: "b < n"
    have Eab_c: "mat_unit a b n n \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
    have \<Phi>Eab_c: "\<Phi> (mat_unit a b n n) \<in> carrier_mat d d"
      using range Eab_c by blast
    have kmd_c: "kraus_map_dim d Ws (mat_unit a b n n) \<in> carrier_mat d d"
      using kraus_map_dim_carrier[OF Ws_c Eab_c] .
    show "\<Phi> (mat_unit a b n n) = kraus_map_dim d Ws (mat_unit a b n n)"
    proof (rule eq_matI)
      show "dim_row (\<Phi> (mat_unit a b n n)) =
            dim_row (kraus_map_dim d Ws (mat_unit a b n n))"
        using \<Phi>Eab_c kmd_c by auto
      show "dim_col (\<Phi> (mat_unit a b n n)) =
            dim_col (kraus_map_dim d Ws (mat_unit a b n n))"
        using \<Phi>Eab_c kmd_c by auto
    next
      fix i j
      assume "i < dim_row (kraus_map_dim d Ws (mat_unit a b n n))"
             "j < dim_col (kraus_map_dim d Ws (mat_unit a b n n))"
      hence i_lt: "i < d" and j_lt: "j < d"
        using kmd_c by auto
      have adi_lt: "a*d + i < n*d"
        using a_lt i_lt
        by (metis Nat.add_0_right div_less div_less_iff_less_mult div_mult_self3 dpos not_less0)
      
      have bdj_lt: "b*d + j < n*d"
        using b_lt j_lt
        by (metis Nat.add_0_right div_less div_less_iff_less_mult div_mult_self3 dpos not_less0)

      have adi_div: "(a*d + i) div d = a" using i_lt dpos by simp
      have bdj_div: "(b*d + j) div d = b" using j_lt dpos by simp
      have adi_mod: "(a*d + i) mod d = i" using i_lt dpos by simp
      have bdj_mod: "(b*d + j) mod d = j" using j_lt dpos by simp
      \<comment> \<open>LHS via the Choi matrix.\<close>
      have "\<Phi> (mat_unit a b n n) $$ (i, j)
          = choi_matrix n d \<Phi> $$ (a*d + i, b*d + j)"
        using adi_lt bdj_lt adi_div bdj_div adi_mod bdj_mod
        by (simp add: choi_matrix_def)
      also have "\<dots> = outer_sum (n*d) vs $$ (a*d + i, b*d + j)"
        using vs_sum by simp
      also have "\<dots> = sum_list (map (\<lambda>v. v $ (a*d + i) * cnj (v $ (b*d + j))) vs)"
        using outer_sum_entry_sum_list[OF vs_dim adi_lt bdj_lt] .
      \<comment> \<open>RHS via the reshape identity.\<close>
      also have "\<dots> = sum_list (map (\<lambda>W. (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
      proof -
        have "\<And>v. v \<in> set vs \<Longrightarrow>
              (Matrix.mat d n (\<lambda>(i, a). v $ (a*d + i))) $$ (i, a)
              = v $ (a*d + i)"
          using i_lt a_lt by simp
        have Ws_nth: "\<And>k. k < length vs \<Longrightarrow>
              Ws ! k = Matrix.mat d n (\<lambda>(i, a). (vs ! k) $ (a*d + i))"
          by (simp add: Ws_def)
        have Ws_c_idx: "\<And>k. k < length vs \<Longrightarrow> Ws ! k \<in> carrier_mat d n"
          using Ws_c len_Ws by (auto simp: set_conv_nth)
        have point_eq:
          "\<And>W. W \<in> set Ws \<Longrightarrow>
              (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
              W $$ (i, a) * cnj (W $$ (j, b))"
        proof -
          fix W assume "W \<in> set Ws"
          then obtain k where k_lt: "k < length Ws" and W_eq: "W = Ws ! k"
            by (metis in_set_conv_nth)
          have Wc_k: "W \<in> carrier_mat d n"
            using W_eq Ws_c \<open>W \<in> set Ws\<close> by simp
          show "(W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j) =
                W $$ (i, a) * cnj (W $$ (j, b))"
            using conjugation_mat_unit_entry[OF Wc_k a_lt b_lt i_lt j_lt].
        qed
        have "sum_list (map (\<lambda>v. v $ (a*d + i) * cnj (v $ (b*d + j))) vs) =
              sum_list (map (\<lambda>W. W $$ (i, a) * cnj (W $$ (j, b))) Ws)"
          unfolding Ws_def
          using i_lt a_lt j_lt b_lt
          by (induction vs) simp_all
        also have "\<dots> = sum_list (map (\<lambda>W. (W * mat_unit a b n n * (W\<^sup>\<dagger>)) $$ (i, j)) Ws)"
          using point_eq
          by (intro arg_cong[where f=sum_list] map_cong refl) (metis)
        finally show ?thesis.
      qed
      also have "\<dots> = kraus_map_dim d Ws (mat_unit a b n n) $$ (i, j)"
        using kraus_map_dim_entry_sum_list[OF Ws_c Eab_c i_lt j_lt] by simp
      finally show "\<Phi> (mat_unit a b n n) $$ (i, j) =
                    kraus_map_dim d Ws (mat_unit a b n n) $$ (i, j)" .
    qed
  qed

  \<comment> \<open>Step 2: Extend to all \<open>A \<in> M\<^sub>n\<close> by linearity.\<close>
  have kmd_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws (X + Y) = kraus_map_dim d Ws X + kraus_map_dim d Ws Y"
    using kraus_map_dim_add Ws_c by blast
  have kmd_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m kraus_map_dim d Ws X"
    using kraus_map_dim_smult Ws_c by blast
  have kmd_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow>
      kraus_map_dim d Ws X \<in> carrier_mat d d"
    using kraus_map_dim_carrier Ws_c by blast
  have \<Phi>_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X \<in> carrier_mat d d"
    using range by blast

  have phi_eq: "\<And>A. A \<in> carrier_mat n n \<Longrightarrow>
                \<Phi> A = kraus_map_dim d Ws A"
  proof -
    fix A :: "complex Matrix.mat" assume Ac: "A \<in> carrier_mat n n"
    have lhs: "\<Phi> A = pair_comb \<Phi> A n d (mat_unit_pairs n)"
      using linear_eq_pair_comb[OF linear smult \<Phi>_car Ac npos dpos] .
    have rhs: "kraus_map_dim d Ws A =
               pair_comb (kraus_map_dim d Ws) A n d (mat_unit_pairs n)"
      using linear_eq_pair_comb[OF kmd_add kmd_smult kmd_car Ac npos dpos] .
    \<comment> \<open>Both pair combinations are equal because the basis values agree.\<close>
    have comb_eq:
      "pair_comb \<Phi> A n d (mat_unit_pairs n) =
       pair_comb (kraus_map_dim d Ws) A n d (mat_unit_pairs n)"
    proof -
      have "\<And>ps. (\<forall>p \<in> set ps. fst p < n \<and> snd p < n) \<Longrightarrow>
          pair_comb \<Phi> A n d ps = pair_comb (kraus_map_dim d Ws) A n d ps"
      proof -
        fix ps :: "(nat \<times> nat) list"
        assume ps_valid: "\<forall>p \<in> set ps. fst p < n \<and> snd p < n"
        show "pair_comb \<Phi> A n d ps =
              pair_comb (kraus_map_dim d Ws) A n d ps"
          using ps_valid
        proof (induction ps)
          case Nil show ?case by simp
        next
          case (Cons p ps)
          obtain a b where p_eq: "p = (a, b)" by (cases p)
          hence a_lt: "a < n" and b_lt: "b < n"
            using Cons.prems by auto
          have basis_eq: "\<Phi> (mat_unit (fst p) (snd p) n n) =
                          kraus_map_dim d Ws (mat_unit (fst p) (snd p) n n)"
            using match_unit[OF a_lt b_lt] p_eq by simp
          have IH: "pair_comb \<Phi> A n d ps =
                    pair_comb (kraus_map_dim d Ws) A n d ps"
            using Cons by auto
          show ?case using basis_eq IH by simp
        qed
      qed
      moreover have "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
        using mat_unit_pairs_set by auto
      ultimately show ?thesis by blast
    qed
    show "\<Phi> A = kraus_map_dim d Ws A"
      using lhs rhs comb_eq by simp
  qed

  \<comment> \<open>Step 3: Transport CP from the Kraus representation back to \<open>\<Phi>\<close>.\<close>
  have kmd_cp: "completely_positive n d (kraus_map_dim d Ws)"
    using kraus_cp_no_tp[OF Ws_c npos dpos].
  show "completely_positive n d \<Phi>"
    unfolding completely_positive_def p_positive_def
  proof (intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and Xc: "X \<in> carrier_mat (p*n) (p*n)"
       and Xpsd: "psd X"
    have psd_kmd: "psd (amplification n d p (kraus_map_dim d Ws) X)"
      using kmd_cp ppos Xc Xpsd
      by (auto simp: completely_positive_def p_positive_def)
    have amp_eq:
      "amplification n d p \<Phi> X = amplification n d p (kraus_map_dim d Ws) X"
    proof (rule eq_matI)
      show "dim_row (amplification n d p \<Phi> X) =
            dim_row (amplification n d p (kraus_map_dim d Ws) X)"
        by (simp add: amplification_def)
      show "dim_col (amplification n d p \<Phi> X) =
            dim_col (amplification n d p (kraus_map_dim d Ws) X)"
        by (simp add: amplification_def)
    next
      fix i j
      assume "i < dim_row (amplification n d p (kraus_map_dim d Ws) X)"
             "j < dim_col (amplification n d p (kraus_map_dim d Ws) X)"
      hence i_lt: "i < p*d" and j_lt: "j < p*d"
        by (simp_all add: amplification_def)
      have block_c: "block_of_mat n X (i div d) (j div d) \<in> carrier_mat n n"
        by (simp add: block_of_mat_def)
      have phi_kmd:
        "\<Phi> (block_of_mat n X (i div d) (j div d))
         = kraus_map_dim d Ws (block_of_mat n X (i div d) (j div d))"
        using phi_eq[OF block_c].
      show "amplification n d p \<Phi> X $$ (i, j) =
            amplification n d p (kraus_map_dim d Ws) X $$ (i, j)"
        using i_lt j_lt phi_kmd
        by (simp add: amplification_def)
    qed
    show "psd (amplification n d p \<Phi> X)"
      using psd_kmd amp_eq by simp
  qed
qed

text \<open>Accumulated \<open>\<Sum>\<^sub>i W\<^sub>i\<^sup>\<dagger> W\<^sub>i\<close> over a Kraus list.\<close>

definition sum_wdag_w :: "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "sum_wdag_w n Ws \<equiv>
     foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Ws (0\<^sub>m n n)"

lemma sum_wdag_w_Nil [simp]: "sum_wdag_w n [] = 0\<^sub>m n n"
  by (simp add: sum_wdag_w_def)

lemma sum_wdag_w_Cons:
  "sum_wdag_w n (W # Ws) = (W\<^sup>\<dagger>) * W + sum_wdag_w n Ws"
  by (simp add: sum_wdag_w_def)

lemma sum_wdag_w_carrier:
  assumes "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "sum_wdag_w n Ws \<in> carrier_mat n n"
  using assms
proof (induction Ws)
  case Nil show ?case by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n" by simp
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d"
    using Wc by (rule dagger_carrier)
  have WdW_c: "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n" using Wdag_c Wc by auto
  show ?case
    using WdW_c Cons by (simp add: sum_wdag_w_Cons)
qed

lemma kraus_operators_altdef:
  "kraus_operators n d Ws \<longleftrightarrow>
     (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> sum_wdag_w n Ws = 1\<^sub>m n"
  by (simp add: kraus_operators_def sum_wdag_w_def)

lemma Tr_kraus_map_dim_as_wdagw:
  fixes \<rho> :: "complex Matrix.mat"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and X_c: "\<rho> \<in> carrier_mat n n"
  shows "Tr (kraus_map_dim d Ws \<rho>) = Tr (sum_wdag_w n Ws * \<rho>)"
  using Ws_c
proof (induction Ws)
  case Nil
  have "kraus_map_dim d [] \<rho> = 0\<^sub>m d d" by simp
  hence lhs: "Tr (kraus_map_dim d [] \<rho>) = 0" by simp
  have "sum_wdag_w n [] * \<rho> = 0\<^sub>m n n * \<rho>" by simp
  also have "\<dots> = 0\<^sub>m n n"
    using X_c by (metis carrier_matD(1) left_mult_zero_mat)
  finally have "Tr (sum_wdag_w n [] * \<rho>) = 0" by simp
  thus ?case using lhs by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>Y \<in> set Ws. Y \<in> carrier_mat d n" by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d" using Wc by (rule dagger_carrier)
  have WX_c: "W * \<rho> \<in> carrier_mat d n" using Wc X_c by auto
  have WXWd_c: "W * \<rho> * (W\<^sup>\<dagger>) \<in> carrier_mat d d" using WX_c Wdag_c by auto
  have km_c: "kraus_map_dim d Ws \<rho> \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF Ws_c' X_c].
  have WdW_c: "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n" using Wdag_c Wc by auto
  have sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Ws_c'].
  have sum_X_c: "sum_wdag_w n Ws * \<rho> \<in> carrier_mat n n"
    using sum_c X_c by auto
  have WdWX_c: "(W\<^sup>\<dagger>) * W * \<rho> \<in> carrier_mat n n"
    using WdW_c X_c by auto

  have tr_cyc:
    "Tr (W * \<rho> * (W\<^sup>\<dagger>)) = Tr ((W\<^sup>\<dagger>) * W * \<rho>)"
  proof -
    have "Tr (W * \<rho> * (W\<^sup>\<dagger>)) = Tr ((W\<^sup>\<dagger>) * (W * \<rho>))"
      using WX_c Wdag_c Wc X_c by (intro Tr_cyclic) auto
    also have "\<dots> = Tr ((W\<^sup>\<dagger>) * W * \<rho>)"
      using Wdag_c Wc X_c by simp
    finally show ?thesis.
  qed

  have IH: "Tr (kraus_map_dim d Ws \<rho>) = Tr (sum_wdag_w n Ws * \<rho>)"
    using Cons.IH[OF Ws_c'].

  have "Tr (kraus_map_dim d (W # Ws) \<rho>)
      = Tr (W * \<rho> * (W\<^sup>\<dagger>) + kraus_map_dim d Ws \<rho>)"
    by simp
  also have "\<dots> = Tr (W * \<rho> * (W\<^sup>\<dagger>)) + Tr (kraus_map_dim d Ws \<rho>)"
    using WXWd_c km_c by (intro Tr_add) auto
  also have "\<dots> = Tr ((W\<^sup>\<dagger>) * W * \<rho>) + Tr (sum_wdag_w n Ws * \<rho>)"
    using tr_cyc IH by simp
  also have "\<dots> = Tr ((W\<^sup>\<dagger>) * W * \<rho> + sum_wdag_w n Ws * \<rho>)"
    using WdWX_c sum_X_c
    by (metis Tr_add carrier_matD(1) carrier_matD(2))
  also have "(W\<^sup>\<dagger>) * W * \<rho> + sum_wdag_w n Ws * \<rho>
           = ((W\<^sup>\<dagger>) * W + sum_wdag_w n Ws) * \<rho>"
    using WdW_c sum_c X_c by (simp add: add_mult_distrib_mat)
  also have "(W\<^sup>\<dagger>) * W + sum_wdag_w n Ws = sum_wdag_w n (W # Ws)"
    by (simp add: sum_wdag_w_Cons)
  finally show ?case .
qed

text \<open>The \<open>\<Sum>\<^sub>i W\<^sub>i\<^sup>\<dagger> W\<^sub>i\<close> matrix entry equals a sum-list of
  \<open>cnj(W\<^sub>i\<^sub>k\<^sub>a)\<cdot>W\<^sub>i\<^sub>k\<^sub>b\<close> contributions (needed to recover \<open>1\<^sub>n\<close> from trace preservation).\<close>

lemma sum_wdag_w_entry:
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and a_lt: "a < n" and b_lt: "b < n"
  shows "sum_wdag_w n Ws $$ (a, b) =
         sum_list (map (\<lambda>W. ((W\<^sup>\<dagger>) * W) $$ (a, b)) Ws)"
  using Ws_c
proof (induction Ws)
  case Nil show ?case using a_lt b_lt by simp
next
  case (Cons W Ws)
  hence Wc: "W \<in> carrier_mat d n"
    and Ws_c': "\<forall>Y \<in> set Ws. Y \<in> carrier_mat d n" by auto
  have Wdag_c: "W\<^sup>\<dagger> \<in> carrier_mat n d" using Wc by (rule dagger_carrier)
  have WdW_c: "(W\<^sup>\<dagger>) * W \<in> carrier_mat n n" using Wdag_c Wc by auto
  have sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
    using sum_wdag_w_carrier[OF Ws_c'].
  have IH: "sum_wdag_w n Ws $$ (a, b) =
            sum_list (map (\<lambda>W. ((W\<^sup>\<dagger>) * W) $$ (a, b)) Ws)"
    using Cons.IH[OF Ws_c'].
  have "sum_wdag_w n (W # Ws) $$ (a, b)
      = ((W\<^sup>\<dagger>) * W + sum_wdag_w n Ws) $$ (a, b)"
    by (simp add: sum_wdag_w_Cons)
  also have "\<dots> = ((W\<^sup>\<dagger>) * W) $$ (a, b) + sum_wdag_w n Ws $$ (a, b)"
    using WdW_c sum_c a_lt b_lt by simp
  also have "\<dots> = ((W\<^sup>\<dagger>) * W) $$ (a, b)
               + sum_list (map (\<lambda>W. ((W\<^sup>\<dagger>) * W) $$ (a, b)) Ws)"
    using IH by simp
  finally show ?case by simp
qed

text \<open>Pairing with \<open>E\<^sub>a\<^sub>b\<close> extracts the \<open>(b,a)\<close> entry under the trace.\<close>

lemma Tr_mult_mat_unit:
  assumes M_c: "M \<in> carrier_mat n n"
      and a_lt: "a < n" and b_lt: "b < n"
  shows "Tr (M * mat_unit a b n n) = M $$ (b, a)"
proof -
  let ?E = "mat_unit a b n n"
  have E_c: "?E \<in> carrier_mat n n" by (simp add: mat_unit_def)
  have ME_c: "M * ?E \<in> carrier_mat n n" using M_c E_c by auto
  have "Tr (M * ?E) = (\<Sum>i<n. (M * ?E) $$ (i, i))"
    using ME_c by (auto simp: Tr_def)
  also have "\<dots> = (\<Sum>i<n.
        (\<Sum>k<n. M $$ (i, k) * ?E $$ (k, i)))"
  proof (intro sum.cong refl)
    fix i assume "i \<in> {..<n}"
    hence i_lt: "i < n" by simp
    have i_M: "i < dim_row M" using M_c i_lt by auto
    have i_E: "i < dim_col ?E" using E_c i_lt by auto
    have "(M * ?E) $$ (i, i) = Matrix.row M i \<bullet> Matrix.col ?E i"
      using index_mult_mat(1)[OF i_M i_E] .
    also have "\<dots> = (\<Sum>k<n. Matrix.row M i $ k * Matrix.col ?E i $ k)"
      unfolding scalar_prod_def using M_c
      by (simp add: atLeast0LessThan)
    also have "\<dots> = (\<Sum>k<n. M $$ (i, k) * ?E $$ (k, i))"
    proof (intro sum.cong refl)
      fix k assume "k \<in> {..<n}"
      hence k_lt: "k < n" by simp
      have row: "Matrix.row M i $ k = M $$ (i, k)"
        using i_M k_lt M_c by simp
      have col: "Matrix.col ?E i $ k = ?E $$ (k, i)"
        using E_c k_lt i_lt by simp
      show "Matrix.row M i $ k * Matrix.col ?E i $ k = M $$ (i, k) * ?E $$ (k, i)"
        using row col by simp
    qed
    finally show "(M * ?E) $$ (i, i) = (\<Sum>k<n. M $$ (i, k) * ?E $$ (k, i))".
  qed
  also have "\<dots> = (\<Sum>i<n.
        (\<Sum>k<n. M $$ (i, k) * (if k = a \<and> i = b then 1 else 0)))"
    by (intro sum.cong refl) simp
  also have "\<dots> = (\<Sum>i<n.
        (if i = b then M $$ (i, a) else 0))"
  proof (intro sum.cong refl)
    fix i assume "i \<in> {..<n}"
    hence i_lt: "i < n" by simp
    show "(\<Sum>k<n. M $$ (i, k) * (if k = a \<and> i = b then 1 else 0))
        = (if i = b then M $$ (i, a) else 0)"
    proof (cases "i = b")
      case True
      have "(\<Sum>k<n. M $$ (i, k) * (if k = a \<and> i = b then 1 else 0))
          = (\<Sum>k<n. if k = a then M $$ (i, k) else 0)"
        using True by (intro sum.cong refl, simp)
      also have "\<dots> = M $$ (i, a)"
        using a_lt by simp
      finally show ?thesis using True by simp
    next
      case False
      thus ?thesis by (simp cong: sum.cong)
    qed
  qed
  also have "\<dots> = M $$ (b, a)"
    using b_lt by simp
  finally show ?thesis.
qed

theorem choi_kraus_cptp:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and npos: "n > 0"
      and dpos: "d > 0"
  shows "(completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>) \<longleftrightarrow>
         (\<exists>Ws :: complex Matrix.mat list.
            kraus_operators n d Ws \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X))"
proof
  \<comment> \<open>Direction \<open>\<Longleftarrow>\<close>: a Kraus representation yields a CP trace-preserving map.\<close>
  assume "\<exists>Ws :: complex Matrix.mat list.
            kraus_operators n d Ws \<and>
            (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
  then obtain Ws where
        Ws_kraus: "kraus_operators n d Ws"
    and phi_eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X"
    by blast
  have Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
    using Ws_kraus by (simp add: kraus_operators_def)
  have Ws_sum: "sum_wdag_w n Ws = 1\<^sub>m n"
    using Ws_kraus by (simp add: kraus_operators_altdef)

  \<comment> \<open>CP: transport from @{thm kraus_is_cp} through the agreement on \<open>M\<^sub>n\<close>.\<close>
  have kmd_cp: "completely_positive n d (kraus_map_dim d Ws)"
    using kraus_is_cp[OF Ws_kraus npos dpos] .
  have cp_\<Phi>: "completely_positive n d \<Phi>"
    unfolding completely_positive_def p_positive_def
  proof (intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and Xc: "X \<in> carrier_mat (p*n) (p*n)"
       and Xpsd: "psd X"
    have psd_kmd: "psd (amplification n d p (kraus_map_dim d Ws) X)"
      using kmd_cp ppos Xc Xpsd
      by (auto simp: completely_positive_def p_positive_def)
    have amp_eq:
      "amplification n d p \<Phi> X = amplification n d p (kraus_map_dim d Ws) X"
    proof (rule eq_matI)
      show "dim_row (amplification n d p \<Phi> X) =
            dim_row (amplification n d p (kraus_map_dim d Ws) X)"
        by (simp add: amplification_def)
      show "dim_col (amplification n d p \<Phi> X) =
            dim_col (amplification n d p (kraus_map_dim d Ws) X)"
        by (simp add: amplification_def)
    next
      fix i j
      assume "i < dim_row (amplification n d p (kraus_map_dim d Ws) X)"
             "j < dim_col (amplification n d p (kraus_map_dim d Ws) X)"
      hence i_lt: "i < p*d" and j_lt: "j < p*d"
        by (simp_all add: amplification_def)
      have block_c: "block_of_mat n X (i div d) (j div d) \<in> carrier_mat n n"
        by (simp add: block_of_mat_def)
      have "\<Phi> (block_of_mat n X (i div d) (j div d))
          = kraus_map_dim d Ws (block_of_mat n X (i div d) (j div d))"
        using phi_eq block_c by simp
      thus "amplification n d p \<Phi> X $$ (i, j) =
            amplification n d p (kraus_map_dim d Ws) X $$ (i, j)"
        using i_lt j_lt by (simp add: amplification_def)
    qed
    show "psd (amplification n d p \<Phi> X)"
      using psd_kmd amp_eq by simp
  qed

  \<comment> \<open>TP: use \<open>Tr (\<Phi> X) = Tr(\<Sum>W\<^sup>\<dagger>W \<cdot> X) = Tr (1\<^sub>n \<cdot> X) = Tr X\<close>.\<close>
  have tp_\<Phi>: "trace_preserving n \<Phi>"
    unfolding trace_preserving_def
  proof (intro allI impI)
    fix A :: "complex Matrix.mat" assume Ac: "A \<in> carrier_mat n n"
    have "Tr (\<Phi> A) = Tr (kraus_map_dim d Ws A)"
      using phi_eq Ac by simp
    also have "\<dots> = Tr (sum_wdag_w n Ws * A)"
      using Tr_kraus_map_dim_as_wdagw[OF Ws_c Ac].
    also have "\<dots> = Tr (1\<^sub>m n * A)"
      using Ws_sum by simp
    also have "\<dots> = Tr A"
      using Ac by simp
    finally show "Tr (\<Phi> A) = Tr A".
  qed

  show "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>"
    using cp_\<Phi> tp_\<Phi> by simp
next
  \<comment> \<open>Direction \<open>\<Longrightarrow>\<close>: a CP trace-preserving map admits a Kraus form.\<close>
  assume "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>"
  hence cp: "completely_positive n d \<Phi>"
    and tp: "trace_preserving n \<Phi>" by auto
  \<comment> \<open>Step 1: CP implies the Choi matrix is psd.\<close>
  have psdP: "psd (choi_matrix n d \<Phi>)"
    using choi_theorem[OF linear smult range npos dpos] cp by blast
  \<comment> \<open>Step 2: reshape a decomposition of the Choi matrix into a Kraus list.\<close>
  obtain Ws :: "complex Matrix.mat list"
    where Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and phi_eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos psdP]
    by blast
  \<comment> \<open>Step 3: trace preservation forces sum_wdag_w n Ws = 1_n.\<close>
  have sum_is_one: "sum_wdag_w n Ws = 1\<^sub>m n"
  proof (rule eq_matI)
    have sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
      using sum_wdag_w_carrier[OF Ws_c].
    show "dim_row (sum_wdag_w n Ws) = dim_row (1\<^sub>m n)"
      using sum_c by auto
    show "dim_col (sum_wdag_w n Ws) = dim_col (1\<^sub>m n)"
      using sum_c by auto
  next
    fix a b
    assume a_in: "a < dim_row (1\<^sub>m n)"
       and b_in: "b < dim_col (1\<^sub>m n)"
    hence a_lt: "a < n" and b_lt: "b < n" by auto
    let ?E = "mat_unit b a n n"
    have E_c: "?E \<in> carrier_mat n n" by (simp add: mat_unit_def)
    have sum_c: "sum_wdag_w n Ws \<in> carrier_mat n n"
      using sum_wdag_w_carrier[OF Ws_c].
    have one_c: "1\<^sub>m n \<in> carrier_mat n n" by simp
    \<comment> \<open>Pair both sides with the mat_unit (b,a) and compare through Tr.\<close>
    have lhs: "sum_wdag_w n Ws $$ (a, b) = Tr (sum_wdag_w n Ws * ?E)"
      using Tr_mult_mat_unit[OF sum_c b_lt a_lt] by simp
    have rhs: "1\<^sub>m n $$ (a, b) = Tr (1\<^sub>m n * ?E)"
      using Tr_mult_mat_unit[OF one_c b_lt a_lt] by simp
    have "Tr (sum_wdag_w n Ws * ?E) = Tr (kraus_map_dim d Ws ?E)"
      using Tr_kraus_map_dim_as_wdagw[OF Ws_c E_c] by simp
    also have "\<dots> = Tr (\<Phi> ?E)"
      using phi_eq E_c by simp
    also have "\<dots> = Tr ?E"
      using tp E_c by (simp add: trace_preserving_def)
    also have "\<dots> = Tr (1\<^sub>m n * ?E)"
      using E_c by simp
    finally have "Tr (sum_wdag_w n Ws * ?E) = Tr (1\<^sub>m n * ?E)" .
    thus "sum_wdag_w n Ws $$ (a, b) = 1\<^sub>m n $$ (a, b)"
      using lhs rhs by simp
  qed
  \<comment> \<open>Step 4: package the Kraus list.\<close>
  have kraus: "kraus_operators n d Ws"
    unfolding kraus_operators_altdef using Ws_c sum_is_one by simp
  show "\<exists>Ws :: complex Matrix.mat list.
          kraus_operators n d Ws \<and>
          (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
    using kraus phi_eq by blast
qed


(* ============================================================================
   DAY 20 \<mdash> 12 / Oct / 11
   Topic: d = 1 case of Choi; adjoint of a CP map;
          UCP / CPTP duality; Choi rank.
   ============================================================================ *)

(* --------------------------------------------------------------------------
   1. Adjoint of a Kraus-represented map.

   If \<Phi>(X) = \<Sum>\<^sub>i A\<^sub>i X A\<^sub>i\<^sup>\<dagger> with A\<^sub>i \<in> M\<^sub>d\<^sub>,\<^sub>n, the Hilbert-Schmidt
   adjoint \<Phi>\<^sup>* : M\<^sub>d \<rightarrow> M\<^sub>n is \<Phi>\<^sup>*(Y) = \<Sum>\<^sub>i A\<^sub>i\<^sup>\<dagger> Y A\<^sub>i.
   The output dimension \<open>n\<close> is kept explicit (needed when \<open>As\<close> is empty).
   -------------------------------------------------------------------------- *)

definition kraus_adjoint_dim ::
  "nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "kraus_adjoint_dim n As y \<equiv>
     foldr (\<lambda>A acc. (A\<^sup>\<dagger>) * y * A + acc) As (0\<^sub>m n n)"

lemma kraus_adjoint_dim_Nil [simp]:
  fixes Y :: "complex Matrix.mat"
  shows "kraus_adjoint_dim n [] Y = 0\<^sub>m n n"
  by (simp add: kraus_adjoint_dim_def)

lemma kraus_adjoint_dim_Cons [simp]:
  fixes Y :: "complex Matrix.mat"
  shows "kraus_adjoint_dim n (A # As) Y =
           (A\<^sup>\<dagger>) * Y * A + kraus_adjoint_dim n As Y"
  by (simp add: kraus_adjoint_dim_def)

lemma kraus_adjoint_dim_carrier:
  fixes Y :: "complex Matrix.mat"
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and Y_c: "Y \<in> carrier_mat d d"
  shows "kraus_adjoint_dim n As Y \<in> carrier_mat n n"
  using As_c
proof (induction As)
  case Nil
  show ?case by simp
next
  case (Cons A As)
  hence A_c: "A \<in> carrier_mat d n"
    and As_c': "\<forall>X \<in> set As. X \<in> carrier_mat d n"
    by auto
  have Adag_c: "A\<^sup>\<dagger> \<in> carrier_mat n d"
    using A_c by (rule dagger_carrier)
  have term_c: "(A\<^sup>\<dagger>) * Y * A \<in> carrier_mat n n"
    using Adag_c Y_c A_c by (intro mult_carrier_mat) auto
  have rec_c: "kraus_adjoint_dim n As Y \<in> carrier_mat n n"
    using Cons.IH As_c' by blast
  show ?case
    using term_c rec_c by simp
qed

(* Adjoint is itself a Kraus map whose operators are the daggers. *)

lemma kraus_adjoint_dim_as_kraus_map_dim:
  fixes Y :: "complex Matrix.mat"
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and Y_c: "Y \<in> carrier_mat d d"
  shows "kraus_adjoint_dim n As Y =
           kraus_map_dim n (map (\<lambda>A. A\<^sup>\<dagger>) As) Y"
  using As_c
proof (induction As)
  case Nil
  show ?case by simp
next
  case (Cons A As)
  hence A_c: "A \<in> carrier_mat d n"
    and As_c': "\<forall>X \<in> set As. X \<in> carrier_mat d n"
    by auto
  have dd_eq: "(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
    using A_c by (simp add: dagger_of_dagger_is_id)
  have IH: "kraus_adjoint_dim n As Y
              = kraus_map_dim n (map (\<lambda>A. A\<^sup>\<dagger>) As) Y"
    using Cons.IH As_c' by blast
  show "kraus_adjoint_dim n (A # As) Y  
      = kraus_map_dim n (map (\<lambda>A. A\<^sup>\<dagger>) (A # As)) Y"
    using dd_eq IH by simp
qed

(* --------------------------------------------------------------------------
   2. Hilbert-Schmidt adjoint identity.

      \<langle>\<langle> Y | kraus_map_dim d As X \<rangle>\<rangle>
        = \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>.

   Induction on \<open>As\<close>; each summand reduces via trace cyclicity and
   \<open>((A\<^sup>\<dagger>) Y A)\<^sup>\<dagger> = (A\<^sup>\<dagger>) Y\<^sup>\<dagger> A\<close> (applied in the Tr-form of \<langle>\<langle>\<cdot>|\<cdot>\<rangle>\<rangle>).
   -------------------------------------------------------------------------- *)

lemma hs_inner_prod_left_add:
  assumes d1r: "dim_row Y1 = dim_row X" and d1c: "dim_col Y1 = dim_col X"
      and d2r: "dim_row Y2 = dim_row X" and d2c: "dim_col Y2 = dim_col X"
  shows "\<langle>\<langle> Y1 + Y2 | X \<rangle>\<rangle> = \<langle>\<langle> Y1 | X \<rangle>\<rangle> + \<langle>\<langle> Y2 | X \<rangle>\<rangle>"
proof -
  have sum_eq: "(Y1 + Y2) $$ (i, j) = Y1 $$ (i, j) + Y2 $$ (i, j)"
    if ij: "i < dim_row X" "j < dim_col X" for i j
    using that d1r d1c d2r d2c by simp
  have "\<langle>\<langle> Y1 + Y2 | X \<rangle>\<rangle>
          = (\<Sum>i\<in>{0..<dim_row X}. \<Sum>j\<in>{0..<dim_col X}.
               cnj ((Y1 + Y2) $$ (i, j)) * X $$ (i, j))"
    by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum>i\<in>{0..<dim_row X}. \<Sum>j\<in>{0..<dim_col X}.
               (cnj (Y1 $$ (i, j)) + cnj (Y2 $$ (i, j))) * X $$ (i, j))"
    by (intro sum.cong refl) (simp add: sum_eq)
  also have "\<dots> = (\<Sum>i\<in>{0..<dim_row X}. \<Sum>j\<in>{0..<dim_col X}.
                       cnj (Y1 $$ (i, j)) * X $$ (i, j))
                + (\<Sum>i\<in>{0..<dim_row X}. \<Sum>j\<in>{0..<dim_col X}.
                       cnj (Y2 $$ (i, j)) * X $$ (i, j))"
    by (simp add: distrib_right sum.distrib)
  also have "\<dots> = \<langle>\<langle> Y1 | X \<rangle>\<rangle> + \<langle>\<langle> Y2 | X \<rangle>\<rangle>"
    by (simp add: hs_inner_prod_def)
  finally show ?thesis .
qed

lemma hs_inner_prod_right_zero:
  "\<langle>\<langle> y | 0\<^sub>m m n \<rangle>\<rangle> = 0"
proof -
  have "\<langle>\<langle> y | 0\<^sub>m m n \<rangle>\<rangle>
          = (\<Sum>i\<in>{0..<m}. \<Sum>j\<in>{0..<n}.
                cnj (y $$ (i, j)) * (0\<^sub>m m n) $$ (i, j))"
    by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum>i\<in>{0..<m}. \<Sum>j\<in>{0..<n}. (0 :: complex))"
    by (intro sum.cong refl) simp
  also have "\<dots> = 0" by simp
  finally show ?thesis.
qed

lemma hs_inner_prod_left_zero:
  fixes X :: "complex Matrix.mat"
  assumes X_c: "X \<in> carrier_mat m n"
  shows "\<langle>\<langle> 0\<^sub>m m n | X \<rangle>\<rangle> = 0"
proof -
  from X_c have dr: "dim_row X = m" and dc: "dim_col X = n" by auto
  have "\<langle>\<langle> 0\<^sub>m m n | X \<rangle>\<rangle>
          = (\<Sum>i\<in>{0..<m}. \<Sum>j\<in>{0..<n}.
                cnj ((0\<^sub>m m n) $$ (i, j)) * X $$ (i, j))"
    using dr dc by (simp add: hs_inner_prod_def)
  also have "\<dots> = (\<Sum>i\<in>{0..<m}. \<Sum>j\<in>{0..<n}. (0 :: complex))"
    by (intro sum.cong refl) simp
  also have "\<dots> = 0" by simp
  finally show ?thesis.
qed

(* Single-Kraus-term identity:
     \<langle>\<langle> Y | A X A\<^sup>\<dagger> \<rangle>\<rangle> = \<langle>\<langle> A\<^sup>\<dagger> Y A | X \<rangle>\<rangle>
   for A \<in> M_{d,n}, X \<in> M_n, Y \<in> M_d.  Proved via
   hs_inner_prod_as_trace + Tr_cyclic + (A\<^sup>\<dagger> Y A)\<^sup>\<dagger> = A\<^sup>\<dagger> Y\<^sup>\<dagger> A. *)

lemma hs_inner_prod_kraus_term:
  fixes A X Y :: "complex Matrix.mat"
  assumes A_c: "A \<in> carrier_mat d n"
      and X_c: "X \<in> carrier_mat n n"
      and Y_c: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) \<rangle>\<rangle> = \<langle>\<langle> (A\<^sup>\<dagger>) * Y * A | X \<rangle>\<rangle>"
proof -
  have Adag_c: "A\<^sup>\<dagger> \<in> carrier_mat n d" using A_c by (rule dagger_carrier)
  have Ydag_c: "Y\<^sup>\<dagger> \<in> carrier_mat d d" using Y_c by (rule dagger_carrier)
  have AX_c: "A * X \<in> carrier_mat d n"
    using A_c X_c by (rule mult_carrier_mat)
  have AXAd_c: "A * X * (A\<^sup>\<dagger>) \<in> carrier_mat d d"
    using AX_c Adag_c by (rule mult_carrier_mat)
  have YdA_c: "Y\<^sup>\<dagger> * A \<in> carrier_mat d n"
    using Ydag_c A_c by (rule mult_carrier_mat)
  have YdAX_c: "Y\<^sup>\<dagger> * A * X \<in> carrier_mat d n"
    using YdA_c X_c by (rule mult_carrier_mat)
  have AdY_c: "A\<^sup>\<dagger> * Y \<in> carrier_mat n d"
    using Adag_c Y_c by (rule mult_carrier_mat)
  have AdYA_c: "A\<^sup>\<dagger> * Y * A \<in> carrier_mat n n"
    using AdY_c A_c by (rule mult_carrier_mat)
  have AdYd_c: "(A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) \<in> carrier_mat n d"
    using Adag_c Ydag_c by (rule mult_carrier_mat)
  have AdYdA_c: "(A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A \<in> carrier_mat n n"
    using AdYd_c A_c by (rule mult_carrier_mat)

  (* LHS as trace *)
  have lhs: "\<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) \<rangle>\<rangle> = Tr (Y\<^sup>\<dagger> * (A * X * (A\<^sup>\<dagger>)))"
    using Y_c AXAd_c by (intro hs_inner_prod_as_trace) auto

  (* Re-bracket: Y\<^sup>\<dagger> * (A X * A\<^sup>\<dagger>) = (Y\<^sup>\<dagger> * A * X) * A\<^sup>\<dagger> *)
  have assoc1: "Y\<^sup>\<dagger> * (A * X * (A\<^sup>\<dagger>)) = (Y\<^sup>\<dagger> * A * X) * (A\<^sup>\<dagger>)"
    using Ydag_c A_c X_c Adag_c
    by (smt (verit) AX_c assoc_mult_mat mult_carrier_mat)

  (* Trace cyclicity: Tr ((Y\<^sup>\<dagger> A X) A\<^sup>\<dagger>) = Tr (A\<^sup>\<dagger> (Y\<^sup>\<dagger> A X)) *)
  have cyc: "Tr ((Y\<^sup>\<dagger> * A * X) * (A\<^sup>\<dagger>)) = Tr ((A\<^sup>\<dagger>) * (Y\<^sup>\<dagger> * A * X))"
    using YdAX_c Adag_c by (intro Tr_cyclic, blast+)
    

  (* Re-bracket: A\<^sup>\<dagger> * (Y\<^sup>\<dagger> * A * X) = (A\<^sup>\<dagger> * Y\<^sup>\<dagger> * A) * X *)
  have assoc2: "(A\<^sup>\<dagger>) * ((Y\<^sup>\<dagger>) * A * X) = ((A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A) * X"
    using Adag_c Ydag_c A_c X_c
    by (smt (verit) YdA_c assoc_mult_mat mult_carrier_mat)

  (* Dagger identity: (A\<^sup>\<dagger> * Y * A)\<^sup>\<dagger> = A\<^sup>\<dagger> * Y\<^sup>\<dagger> * A *)
  have dim1: "dim_col ((A\<^sup>\<dagger>) * Y) = dim_row A"
    using AdY_c A_c by (metis carrier_matD)
  have dim2: "dim_col (A\<^sup>\<dagger>) = dim_row Y"
    using Adag_c Y_c by (metis carrier_matD)
  have dag_eq: "((A\<^sup>\<dagger>) * Y * A)\<^sup>\<dagger> = (A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A"
  proof -
    have step1: "((A\<^sup>\<dagger>) * Y * A)\<^sup>\<dagger> = (A\<^sup>\<dagger>) * (((A\<^sup>\<dagger>) * Y)\<^sup>\<dagger>)"
      using dim1 by (rule dagger_of_prod)
    have step2: "((A\<^sup>\<dagger>) * Y)\<^sup>\<dagger> = (Y\<^sup>\<dagger>) * ((A\<^sup>\<dagger>)\<^sup>\<dagger>)"
      using dim2 by (rule dagger_of_prod)
    have step3: "(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
      using A_c by (simp add: dagger_of_dagger_is_id)
    have step4: "(A\<^sup>\<dagger>) * ((Y\<^sup>\<dagger>) * A) = (A\<^sup>\<dagger>) * (Y\<^sup>\<dagger>) * A"
      using Adag_c Ydag_c A_c by simp
    show ?thesis
      using step1 step2 step3 step4 by simp
  qed

  (* RHS as trace *)
  have rhs: "\<langle>\<langle> (A\<^sup>\<dagger>) * Y * A | X \<rangle>\<rangle> = Tr (((A\<^sup>\<dagger>) * Y * A)\<^sup>\<dagger> * X)"
    using AdYA_c X_c by (intro hs_inner_prod_as_trace) auto

  show ?thesis
    using lhs assoc1 cyc assoc2 dag_eq rhs by simp
qed

theorem kraus_adjoint_correct:
  fixes As :: "complex Matrix.mat list"
    and X :: "complex Matrix.mat"
    and Y :: "complex Matrix.mat"
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and X_c: "X \<in> carrier_mat n n"
      and Y_c: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> Y | kraus_map_dim d As X \<rangle>\<rangle>
         = \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
  using As_c
proof (induction As)
  case Nil
  have lhs0: "\<langle>\<langle> Y | kraus_map_dim d [] X \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_right_zero)
  have rhs0: "\<langle>\<langle> kraus_adjoint_dim n [] Y | X \<rangle>\<rangle> = 0"
    using X_c hs_inner_prod_as_trace kraus_adjoint_dim_def by force
  show "\<langle>\<langle> Y | kraus_map_dim d [] X \<rangle>\<rangle> = \<langle>\<langle> kraus_adjoint_dim n [] Y | X \<rangle>\<rangle>" using lhs0 rhs0 by simp
next
  case (Cons A As)
  hence A_c: "A \<in> carrier_mat d n"
    and As_c': "\<forall>B \<in> set As. B \<in> carrier_mat d n"
    by auto
  have Adag_c: "A\<^sup>\<dagger> \<in> carrier_mat n d" using A_c by (rule dagger_carrier)
  have AX_c: "A * X \<in> carrier_mat d n" using A_c X_c by (rule mult_carrier_mat)
  have AXAd_c: "A * X * (A\<^sup>\<dagger>) \<in> carrier_mat d d"
    using AX_c Adag_c by (rule mult_carrier_mat)
  have AdY_c: "A\<^sup>\<dagger> * Y \<in> carrier_mat n d"
    using Adag_c Y_c by (rule mult_carrier_mat)
  have AdYA_c: "A\<^sup>\<dagger> * Y * A \<in> carrier_mat n n"
    using AdY_c A_c by (rule mult_carrier_mat)
  have km_c: "kraus_map_dim d As X \<in> carrier_mat d d"
    using kraus_map_dim_carrier[OF As_c' X_c] .
  have ka_c: "kraus_adjoint_dim n As Y \<in> carrier_mat n n"
    using kraus_adjoint_dim_carrier[OF As_c' Y_c] .

  have IH: "\<langle>\<langle> Y | kraus_map_dim d As X \<rangle>\<rangle>
         = \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using Cons.IH As_c' by blast

  have left_add: "\<langle>\<langle> A\<^sup>\<dagger> * Y * A + kraus_adjoint_dim n As Y | X \<rangle>\<rangle>
                  = \<langle>\<langle> A\<^sup>\<dagger> * Y * A | X \<rangle>\<rangle>
                    + \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using AdYA_c ka_c X_c
    by (metis carrier_matD(1,2) complex_cnj_add hs_inner_prod_cnj hs_inner_prod_right_add index_add_mat(2,3))

  have "\<langle>\<langle> Y | kraus_map_dim d (A # As) X \<rangle>\<rangle>
        = \<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) + kraus_map_dim d As X \<rangle>\<rangle>"
    by simp
  also have "\<dots> = \<langle>\<langle> Y | A * X * (A\<^sup>\<dagger>) \<rangle>\<rangle>
                  + \<langle>\<langle> Y | kraus_map_dim d As X \<rangle>\<rangle>"
    using Y_c AXAd_c km_c by (intro hs_inner_prod_right_add) auto
  also have "\<dots> = \<langle>\<langle> A\<^sup>\<dagger> * Y * A | X \<rangle>\<rangle>
                  + \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using hs_inner_prod_kraus_term[OF A_c X_c Y_c] IH by simp
  also have "\<dots> = \<langle>\<langle> A\<^sup>\<dagger> * Y * A + kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using left_add by simp
  also have "\<dots> = \<langle>\<langle> kraus_adjoint_dim n (A # As) Y | X \<rangle>\<rangle>"
    by simp
  finally show ?case.
qed

(* --------------------------------------------------------------------------
   3. CP \<leftrightarrow> CP of the adjoint; UCP \<leftrightarrow> CPTP of the adjoint.

   When \<Phi> has a Kraus representation (A\<^sub>i), \<Phi>\<^sup>* is the Kraus map with
   operators (A\<^sub>i\<^sup>\<dagger>) \<mdash> cf. \<open>kraus_adjoint_dim_as_kraus_map_dim\<close>.
   Hence \<open>kraus_is_cp\<close> applies in both directions.
   -------------------------------------------------------------------------- *)

theorem adjoint_cp_from_kraus:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive d n (kraus_adjoint_dim n As)"
proof -
  define Bs where "Bs = map (\<lambda>A. A\<^sup>\<dagger>) As"
  have Bs_c: "\<forall>B \<in> set Bs. B \<in> carrier_mat n d"
    using As_c by (auto simp: Bs_def dagger_carrier)

  show ?thesis
  proof (unfold completely_positive_def p_positive_def, intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p"
       and X_c: "X \<in> carrier_mat (p*d) (p*d)"
       and X_psd: "psd X"

    (* Amplification of kraus_adjoint_dim n As agrees with that of
       kraus_map_dim n Bs because the two functions agree on M_{d,d}
       (kraus_adjoint_dim_as_kraus_map_dim). *)
    have amp_eq:
      "amplification d n p (kraus_adjoint_dim n As) X =
       amplification d n p (kraus_map_dim n Bs) X"
    proof (rule eq_matI)
      show "dim_row (amplification d n p (kraus_adjoint_dim n As) X) =
            dim_row (amplification d n p (kraus_map_dim n Bs) X)"
        by (simp add: amplification_def)
      show "dim_col (amplification d n p (kraus_adjoint_dim n As) X) =
            dim_col (amplification d n p (kraus_map_dim n Bs) X)"
        by (simp add: amplification_def)
    next
      fix i j
      assume i: "i < dim_row (amplification d n p (kraus_map_dim n Bs) X)"
         and j: "j < dim_col (amplification d n p (kraus_map_dim n Bs) X)"
      hence ipn: "i < p*n" and jpn: "j < p*n"
        by (auto simp: amplification_def)
      have B_c: "block_of_mat d X (i div n) (j div n) \<in> carrier_mat d d"
        by (simp add: block_of_mat_def)
      have eq:
        "kraus_adjoint_dim n As (block_of_mat d X (i div n) (j div n)) =
         kraus_map_dim n Bs (block_of_mat d X (i div n) (j div n))"
        unfolding Bs_def
        using kraus_adjoint_dim_as_kraus_map_dim[OF As_c B_c].
      have lhs_index:
        "amplification d n p (kraus_adjoint_dim n As) X $$ (i,j)
           = (kraus_adjoint_dim n As)
                (block_of_mat d X (i div n) (j div n)) $$
             (i mod n, j mod n)"
        using ipn jpn by (simp add: amplification_def)
      have rhs_index:
        "amplification d n p (kraus_map_dim n Bs) X $$ (i,j)
           = (kraus_map_dim n Bs)
                (block_of_mat d X (i div n) (j div n)) $$
             (i mod n, j mod n)"
        using ipn jpn by (simp add: amplification_def)
      show "amplification d n p (kraus_adjoint_dim n As) X $$ (i,j) =
            amplification d n p (kraus_map_dim n Bs) X $$ (i,j)"
        using lhs_index rhs_index eq by simp
    qed

    (* Reduce to PSD-ness of an amplified Kraus map (no TP needed). *)
    have lifted_c:
      "\<forall>L \<in> set (map (\<lambda>B. 1\<^sub>m p \<Otimes> B) Bs). L \<in> carrier_mat (p*n) (p*d)"
      using tensor_id_kraus_list_carrier[OF Bs_c] .
    have amp_kr:
      "amplification d n p (kraus_map_dim n Bs) X =
         kraus_map_dim (p*n) (map (\<lambda>B. 1\<^sub>m p \<Otimes> B) Bs) X"
      using amplification_kraus_map_dim[OF Bs_c X_c npos dpos] .
    have psd_kr:
      "psd (kraus_map_dim (p*n) (map (\<lambda>B. 1\<^sub>m p \<Otimes> B) Bs) X)"
      using kraus_map_dim_psd[OF lifted_c X_c X_psd] .
    show "psd (amplification d n p (kraus_adjoint_dim n As) X)"
      using amp_eq amp_kr psd_kr by simp
  qed
qed

(* Helper: kraus_map_dim d As (1\<^sub>m n) = \<Sum> A A\<^sup>\<dagger>, which is
   sum_wdag_w d (map dagger As) since (A\<^sup>\<dagger>)\<^sup>\<dagger> A\<^sup>\<dagger> = A A\<^sup>\<dagger>. *)

lemma kraus_map_dim_one_eq_sum_wdag_w_dagger:
  fixes As :: "complex Matrix.mat list"
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
  shows "kraus_map_dim d As (1\<^sub>m n)
         = sum_wdag_w d (map (\<lambda>A. A\<^sup>\<dagger>) As)"
  using As_c
proof (induction As)
  case Nil
  show ?case by (simp add: sum_wdag_w_def)
next
  case (Cons A As)
  hence A_c: "A \<in> carrier_mat d n"
    and As_c': "\<forall>B \<in> set As. B \<in> carrier_mat d n" by auto
  have Adag_c: "A\<^sup>\<dagger> \<in> carrier_mat n d" using A_c by (rule dagger_carrier)
  have A_one: "A * 1\<^sub>m n = A" using A_c by simp
  have ddag: "(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
    using A_c by (simp add: dagger_of_dagger_is_id)
  have IH: "kraus_map_dim d As (1\<^sub>m n)
              = sum_wdag_w d (map (\<lambda>A. A\<^sup>\<dagger>) As)"
    using Cons.IH As_c' .
  have "kraus_map_dim d (A # As) (1\<^sub>m n)
          = A * 1\<^sub>m n * (A\<^sup>\<dagger>) + kraus_map_dim d As (1\<^sub>m n)"
    by simp
  also have "\<dots> = A * (A\<^sup>\<dagger>) + sum_wdag_w d (map (\<lambda>A. A\<^sup>\<dagger>) As)"
    using A_one IH by simp
  also have "\<dots> = ((A\<^sup>\<dagger>)\<^sup>\<dagger>) * (A\<^sup>\<dagger>)
                  + sum_wdag_w d (map (\<lambda>A. A\<^sup>\<dagger>) As)"
    using ddag by simp
  also have "\<dots> = sum_wdag_w d (A\<^sup>\<dagger> # map (\<lambda>A. A\<^sup>\<dagger>) As)"
    by (simp add: sum_wdag_w_Cons)
  also have "\<dots> = sum_wdag_w d (map (\<lambda>A. A\<^sup>\<dagger>) (A # As))"
    by simp
  finally show ?case .
qed

theorem cp_unital_iff_adjoint_tp:
  assumes As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "unital_map n d (kraus_map_dim d As)
         \<longleftrightarrow> trace_preserving d (kraus_adjoint_dim n As)"
proof -
  define Bs where "Bs = map (\<lambda>A. A\<^sup>\<dagger>) As"
  have Bs_c: "\<forall>B \<in> set Bs. B \<in> carrier_mat n d"
    using As_c by (auto simp: Bs_def dagger_carrier)
  let ?M = "sum_wdag_w d Bs"
  have M_c: "?M \<in> carrier_mat d d"
    using sum_wdag_w_carrier[OF Bs_c] .

  (* Unital: \<Phi>(I_n) = \<Sum> A A\<^sup>\<dagger> = ?M, so unital iff ?M = I_d *)
  have unital_iff:
    "unital_map n d (kraus_map_dim d As) \<longleftrightarrow> ?M = 1\<^sub>m d"
  proof -
    have eq: "kraus_map_dim d As (1\<^sub>m n) = ?M"
      unfolding Bs_def
      using kraus_map_dim_one_eq_sum_wdag_w_dagger[OF As_c] .
    show ?thesis unfolding unital_map_def using eq by simp
  qed

  (* TP: Tr(\<Phi>\<^sup>*(Y)) = Tr(?M * Y), so TP iff \<forall>Y. Tr(?M * Y) = Tr Y *)
  have Tr_adj:
    "\<And>Y. Y \<in> carrier_mat d d
       \<Longrightarrow> Tr (kraus_adjoint_dim n As Y) = Tr (?M * Y)"
  proof -
    fix Y :: "complex Matrix.mat"
    assume Y_c: "Y \<in> carrier_mat d d"
    have step1: "kraus_adjoint_dim n As Y = kraus_map_dim n Bs Y"
      unfolding Bs_def
      using kraus_adjoint_dim_as_kraus_map_dim[OF As_c Y_c] .
    have step2: "Tr (kraus_map_dim n Bs Y) = Tr (?M * Y)"
      using Tr_kraus_map_dim_as_wdagw[OF Bs_c Y_c] .
    show "Tr (kraus_adjoint_dim n As Y) = Tr (?M * Y)"
      using step1 step2 by simp
  qed

  have tp_iff:
    "trace_preserving d (kraus_adjoint_dim n As) \<longleftrightarrow> ?M = 1\<^sub>m d"
  proof
    assume tp: "trace_preserving d (kraus_adjoint_dim n As)"
    have Tr_eq: "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> Tr (?M * Y) = Tr Y"
    proof -
      fix Y :: "complex Matrix.mat"
      assume Y_c: "Y \<in> carrier_mat d d"
      have "Tr (kraus_adjoint_dim n As Y) = Tr Y"
        using tp Y_c by (simp add: trace_preserving_def)
      thus "Tr (?M * Y) = Tr Y" using Tr_adj[OF Y_c] by simp
    qed
    show "?M = 1\<^sub>m d"
    proof (rule eq_matI)
      show "dim_row ?M = dim_row (1\<^sub>m d)" using M_c by simp
      show "dim_col ?M = dim_col (1\<^sub>m d)" using M_c by simp
    next
      fix i j
      assume i: "i < dim_row (1\<^sub>m d)" and j: "j < dim_col (1\<^sub>m d)"
      hence id: "i < d" and jd: "j < d" by simp_all
      let ?E = "mat_unit j i d d"
      have E_c: "?E \<in> carrier_mat d d"
        by (simp add: mat_unit_def)
      have Tr_ME: "Tr (?M * ?E) = ?M $$ (i, j)"
        using Tr_mult_mat_unit[OF M_c jd id] .
      have Tr_E: "Tr ?E = (if j = i then 1 else 0)"
        using Tr_mat_unit[OF jd id] .
      have eq: "Tr (?M * ?E) = Tr ?E"
        using Tr_eq[OF E_c] .
      have M_ij: "?M $$ (i, j) = (if j = i then 1 else 0)"
        using Tr_ME Tr_E eq by simp
      have one_ij: "(1\<^sub>m d) $$ (i, j) = (if i = j then 1 else 0)"
        using id jd by simp
      show "?M $$ (i, j) = (1\<^sub>m d) $$ (i, j)"
        using M_ij one_ij by (cases "i = j") auto
    qed
  next
    assume M_id: "?M = 1\<^sub>m d"
    show "trace_preserving d (kraus_adjoint_dim n As)"
    proof (unfold trace_preserving_def, intro allI impI)
      fix Y :: "complex Matrix.mat"
      assume Y_c: "Y \<in> carrier_mat d d"
      have "Tr (kraus_adjoint_dim n As Y) = Tr (?M * Y)"
        using Tr_adj[OF Y_c] .
      also have "\<dots> = Tr ((1\<^sub>m d) * Y)" using M_id by simp
      also have "\<dots> = Tr Y" using Y_c by simp
      finally show "Tr (kraus_adjoint_dim n As Y) = Tr Y" .
    qed
  qed

  show ?thesis using unital_iff tp_iff by simp
qed

(* --------------------------------------------------------------------------
   4. d = 1 case of Choi's theorem: positive \<Leftrightarrow> CP for \<phi> : M\<^sub>n \<rightarrow> \<complex>.

   The direction CP \<Leftrightarrow> P\<^sub>\<phi> \<ge> 0 is already Choi's theorem with d = 1.
   Only "positive \<Rightarrow> CP" is new content.  Given P = (P\<^sub>i\<^sub>j) \<in> M\<^sub>r(M\<^sub>n)\<^sup>+
   and v = (\<alpha>\<^sub>i), form Y with \<alpha>\<^sub>i\<cdot>I as the i-th block row.  Then
   Y\<^sup>* P Y = \<Sum> cnj(\<alpha>\<^sub>i)\<alpha>\<^sub>j P\<^sub>i\<^sub>j \<ge> 0, so \<phi> positive gives
   \<langle>v | \<phi>\<^sup>(\<^sup>r\<^sup>)(P) v\<rangle> = \<phi>(Y\<^sup>* P Y) \<ge> 0.
   -------------------------------------------------------------------------- *)

(* Linearity-over-double-sum: a linear map evaluated at a matrix M
   produces an entry-wise double sum over the matrix-unit basis. *)

lemma phi_entry_double_sum:
  fixes \<phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes f_add: "\<And>X Y. X \<in> carrier_mat n n \<Longrightarrow> Y \<in> carrier_mat n n
                    \<Longrightarrow> \<phi> (X + Y) = \<phi> X + \<phi> Y"
      and f_smult: "\<And>c X. X \<in> carrier_mat n n \<Longrightarrow> \<phi> (c \<cdot>\<^sub>m X) = c \<cdot>\<^sub>m \<phi> X"
      and f_car: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<phi> X \<in> carrier_mat d d"
      and M_c: "M \<in> carrier_mat n n"
      and r_lt: "r < d" and c_lt: "c < d"
      and npos: "0 < n" and dpos: "0 < d"
  shows "\<phi> M $$ (r, c) =
         (\<Sum>i<n. \<Sum>j<n. M $$ (i, j) * \<phi> (mat_unit i j n n) $$ (r, c))"
proof -
  have ps_valid: "\<forall>p \<in> set (mat_unit_pairs n). fst p < n \<and> snd p < n"
    using mat_unit_pairs_set by auto
  have phi_pc: "\<phi> M = pair_comb \<phi> M n d (mat_unit_pairs n)"
    using linear_eq_pair_comb[OF f_add f_smult f_car M_c npos dpos] .
  have fE_car: "\<And>a b. a < n \<Longrightarrow> b < n
                  \<Longrightarrow> \<phi> (mat_unit a b n n) \<in> carrier_mat d d"
  proof -
    fix a b :: nat
    assume "a < n" "b < n"
    have "mat_unit a b n n \<in> carrier_mat n n"
      by (simp add: mat_unit_def)
    thus "\<phi> (mat_unit a b n n) \<in> carrier_mat d d"
      using f_car by blast
  qed

  let ?term = "\<lambda>p. M $$ p * \<phi> (mat_unit (fst p) (snd p) n n) $$ (r, c)"
  have entry_eq:
    "\<phi> M $$ (r, c) = (\<Sum>p \<leftarrow> mat_unit_pairs n. ?term p)"
  proof -
    have pc_entry:
      "pair_comb \<phi> M n d (mat_unit_pairs n) $$ (r, c)
         = (\<Sum>p \<leftarrow> mat_unit_pairs n. ?term p)"
    proof (rule pair_comb_entry)
      fix a b :: nat
      assume "a < n" "b < n"
      thus "\<phi> (mat_unit a b n n) \<in> carrier_mat d d"
        using fE_car by blast
    qed (use ps_valid r_lt c_lt in auto)
    show ?thesis using pc_entry phi_pc by simp
  qed
  also have "\<dots> = (\<Sum>p \<in> set (mat_unit_pairs n). ?term p)"
    using mat_unit_pairs_distinct
    by (rule sum_list_distinct_conv_sum_set)
  also have "\<dots> = (\<Sum>p \<in> {0..<n} \<times> {0..<n}. ?term p)"
    using mat_unit_pairs_set
    by (intro sum.cong) (auto)
  also have "\<dots> = (\<Sum>i \<in> {0..<n}. \<Sum>j \<in> {0..<n}. ?term (i, j))"
    by (simp add: sum.cartesian_product')
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n.
                    M $$ (i, j) * \<phi> (mat_unit i j n n) $$ (r, c))"
    by (simp add: atLeast0LessThan)
  finally show ?thesis.
qed

theorem positive_scalar_is_cp:
  fixes \<phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n
                      \<Longrightarrow> \<phi> (A + B) = \<phi> A + \<phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<phi> A \<in> carrier_mat 1 1"
      and pos:    "positive_map n 1 \<phi>"
      and npos:   "0 < n"
  shows "completely_positive n 1 \<phi>"
proof -
  let ?P = "choi_matrix n 1 \<phi>"
  have one_pos: "(0 :: nat) < 1" by simp
  have P_n: "?P \<in> carrier_mat n n"
    by (simp add: choi_matrix_def)
  have P_entry: "\<And>a b. a < n \<Longrightarrow> b < n
                    \<Longrightarrow> ?P $$ (a, b) = \<phi> (mat_unit a b n n) $$ (0, 0)"
    by (simp add: choi_matrix_def)
  have range': "\<And>A. A \<in> carrier_mat n n \<Longrightarrow> \<phi> A \<in> carrier_mat 1 1"
    using range by blast

  (* For arbitrary x \<in> \<complex>\<^sup>n, express \<langle>x | P x\<rangle> as \<phi>(\<rho>\<^sub>x) $$ (0,0)
     where \<rho>\<^sub>x is rank-one psd. *)
  have quad_real_nonneg:
    "\<And>x :: complex Matrix.vec. dim_vec x = n \<Longrightarrow>
       \<langle>x | ?P *\<^sub>v x\<rangle> \<in> \<real> \<and> Re (\<langle>x | ?P *\<^sub>v x\<rangle>) \<ge> 0"
  proof -
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    let ?cx = "Matrix.vec n (\<lambda>i. cnj (x $ i))"
    let ?Xx = "outer_sum n [?cx]"
    have cx_dim: "dim_vec ?cx = n" by simp
    have cx_set: "\<forall>v \<in> set [?cx]. dim_vec v = n" by simp
    have Xx_c: "?Xx \<in> carrier_mat n n" by auto
    have Xx_psd: "psd ?Xx"
      using outer_sum_psd[where vs="[?cx]" and k=1 and n=n] cx_set by simp
    have Xx_entry: "\<And>a b. a < n \<Longrightarrow> b < n
                       \<Longrightarrow> ?Xx $$ (a, b) = cnj (x $ a) * x $ b"
    proof -
      fix a b assume a: "a < n" and b: "b < n"
      have "?Xx $$ (a, b)
              = sum_list (map (\<lambda>v. v $ a * cnj (v $ b)) [?cx])"
        using outer_sum_entry_sum_list[OF cx_set a b] .
      also have "\<dots> = ?cx $ a * cnj (?cx $ b)" by simp
      also have "\<dots> = cnj (x $ a) * cnj (cnj (x $ b))"
        using a b by simp
      also have "\<dots> = cnj (x $ a) * x $ b" by simp
      finally show "?Xx $$ (a, b) = cnj (x $ a) * x $ b" .
    qed

    have phiXx_c: "\<phi> ?Xx \<in> carrier_mat 1 1" using range' Xx_c by blast
    have phiXx_psd: "psd (\<phi> ?Xx)"
      using pos Xx_psd Xx_c by (auto simp: positive_map_def)

    (* psd in M\<^sub>1: hermitian gives realness of (0,0) entry *)
    have phiXx_real: "\<phi> ?Xx $$ (0, 0) \<in> \<real>"
    proof -
      have herm: "(\<phi> ?Xx)\<^sup>\<dagger> = \<phi> ?Xx"
        using phiXx_psd by (simp add: psd_def hermitian_def)
      have "(\<phi> ?Xx)\<^sup>\<dagger> $$ (0, 0) = cnj (\<phi> ?Xx $$ (0, 0))"
        using phiXx_c by (simp add: dagger_def)
      hence "cnj (\<phi> ?Xx $$ (0, 0)) = \<phi> ?Xx $$ (0, 0)" using herm by simp
      thus ?thesis using Reals_cnj_iff by metis
    qed

    (* psd: \<langle>(1) | (\<phi> X\<^sub>x) (1)\<rangle> \<ge> 0 gives Re of (0,0) entry \<ge> 0 *)
    have phiXx_nonneg: "Re (\<phi> ?Xx $$ (0, 0)) \<ge> 0"
    proof -
      let ?one = "Matrix.vec 1 (\<lambda>i. (1 :: complex))"
      have one_dim: "dim_vec ?one = 1" by simp
      have one_eq_dr: "dim_vec ?one = dim_row (\<phi> ?Xx)"
        using phiXx_c by simp
      have nn_quad: "Re (\<langle>?one | (\<phi> ?Xx) *\<^sub>v ?one\<rangle>) \<ge> 0"
        using phiXx_psd one_eq_dr by (auto simp: psd_def)

      (* \<langle>?one | M *_v ?one\<rangle> = M $$ (0,0) for M \<in> M\<^sub>1 *)
      have prod_dim: "dim_vec ((\<phi> ?Xx) *\<^sub>v ?one) = 1"
        using phiXx_c by simp
      have prod_entry: "((\<phi> ?Xx) *\<^sub>v ?one) $ 0 = \<phi> ?Xx $$ (0, 0)"
      proof -
        have "((\<phi> ?Xx) *\<^sub>v ?one) $ 0
                = (\<Sum>k<dim_col (\<phi> ?Xx). \<phi> ?Xx $$ (0, k) * ?one $ k)"
          using phiXx_c
          by (simp add: scalar_prod_def atLeast0LessThan)
        also have "\<dots> = (\<Sum>k<1. \<phi> ?Xx $$ (0, k) * ?one $ k)"
          using phiXx_c by simp
        also have "\<dots> = \<phi> ?Xx $$ (0, 0) * ?one $ 0"
          by simp
        also have "\<dots> = \<phi> ?Xx $$ (0, 0)" by simp
        finally show ?thesis .
      qed
      have inner_eq: "\<langle>?one | (\<phi> ?Xx) *\<^sub>v ?one\<rangle> = \<phi> ?Xx $$ (0, 0)"
      proof -
        have "\<langle>?one | (\<phi> ?Xx) *\<^sub>v ?one\<rangle>
                = (\<Sum>i<dim_vec ((\<phi> ?Xx) *\<^sub>v ?one).
                    cnj (?one $ i) * ((\<phi> ?Xx) *\<^sub>v ?one) $ i)"
          by (simp add: inner_prod_def atLeast0LessThan)
        also have "\<dots> = (\<Sum>i<1. cnj (?one $ i) * ((\<phi> ?Xx) *\<^sub>v ?one) $ i)"
          using prod_dim by simp
        also have "\<dots> = cnj (?one $ 0) * ((\<phi> ?Xx) *\<^sub>v ?one) $ 0" by simp
        also have "\<dots> = \<phi> ?Xx $$ (0, 0)" using prod_entry by simp
        finally show ?thesis .
      qed
      show ?thesis using nn_quad inner_eq by simp
    qed

    (* \<langle>x | P *\<^sub>v x\<rangle> equals \<phi>(\<rho>\<^sub>x) $$ (0,0) by linearity over the
       matrix-unit basis. *)
    have inner_lhs:
      "\<langle>x | ?P *\<^sub>v x\<rangle>
         = (\<Sum>i<n. \<Sum>j<n. cnj (x $ i) * x $ j * ?P $$ (i, j))"
    proof -
      have prod_dim: "dim_vec (?P *\<^sub>v x) = n" using P_n by simp
      have "\<langle>x | ?P *\<^sub>v x\<rangle>
              = (\<Sum>i<dim_vec (?P *\<^sub>v x).
                   cnj (x $ i) * (?P *\<^sub>v x) $ i)"
        by (simp add: inner_prod_def atLeast0LessThan)
      also have "\<dots> = (\<Sum>i<n. cnj (x $ i) * (?P *\<^sub>v x) $ i)"
        using prod_dim by simp
      also have "\<dots> = (\<Sum>i<n. cnj (x $ i) *
                          (\<Sum>j<n. ?P $$ (i, j) * x $ j))"
      proof (intro sum.cong refl)
        fix i assume i_in: "i \<in> {..<n}"
        hence i_lt: "i < n" by simp
        have "(?P *\<^sub>v x) $ i
                = (\<Sum>j<dim_col ?P. ?P $$ (i, j) * x $ j)"
          using i_lt P_n xdim
          by (simp add: scalar_prod_def atLeast0LessThan)
        also have "\<dots> = (\<Sum>j<n. ?P $$ (i, j) * x $ j)"
          using P_n by simp
        finally show "cnj (x $ i) * (?P *\<^sub>v x) $ i =
                      cnj (x $ i) * (\<Sum>j<n. ?P $$ (i, j) * x $ j)" by simp
      qed
      also have "\<dots> = (\<Sum>i<n. \<Sum>j<n.
                        cnj (x $ i) * x $ j * ?P $$ (i, j))"
      proof (intro sum.cong refl)
        fix i assume "i \<in> {..<n}"
        have "cnj (x $ i) * (\<Sum>j<n. ?P $$ (i, j) * x $ j)
                = (\<Sum>j<n. cnj (x $ i) * (?P $$ (i, j) * x $ j))"
          by (simp add: sum_distrib_left)
        also have "\<dots> = (\<Sum>j<n. cnj (x $ i) * x $ j * ?P $$ (i, j))"
          by (metis (mono_tags, opaque_lifting) mult.commute mult.left_commute)
        finally show "cnj (x $ i) * (\<Sum>j<n. ?P $$ (i, j) * x $ j)
                       = (\<Sum>j<n. cnj (x $ i) * x $ j * ?P $$ (i, j))" .
      qed
      finally show ?thesis.
    qed

    have quad_eq: "\<langle>x | ?P *\<^sub>v x\<rangle> = \<phi> ?Xx $$ (0, 0)"
    proof -
      have phi_Xx_eq:
        "\<phi> ?Xx $$ (0, 0) =
           (\<Sum>i<n. \<Sum>j<n. ?Xx $$ (i, j) * \<phi> (mat_unit i j n n) $$ (0, 0))"
        using phi_entry_double_sum[OF linear smult range' Xx_c
                                       _ _ npos one_pos] by simp
      have step:
        "(\<Sum>i<n. \<Sum>j<n. cnj (x $ i) * x $ j * ?P $$ (i, j))
         = (\<Sum>i<n. \<Sum>j<n. ?Xx $$ (i, j) * \<phi> (mat_unit i j n n) $$ (0, 0))"
        using P_entry Xx_entry by (intro sum.cong refl, auto)        
      show ?thesis using inner_lhs phi_Xx_eq step by simp
    qed

    show "\<langle>x | ?P *\<^sub>v x\<rangle> \<in> \<real> \<and> Re (\<langle>x | ?P *\<^sub>v x\<rangle>) \<ge> 0"
      using quad_eq phiXx_real phiXx_nonneg by simp
  qed

  have psd_choi: "psd ?P"
  proof -
    have herm: "hermitian ?P"
    proof -
      have "\<forall>x :: complex Matrix.vec. dim_vec x = n
              \<longrightarrow> \<langle>x | ?P *\<^sub>v x\<rangle> \<in> \<real>"
        using quad_real_nonneg by blast
      thus ?thesis
        using P_n hermitian_iff_real_quad_form by metis
    qed
    have nonneg:
      "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row ?P
         \<longrightarrow> Re (\<langle>x | ?P *\<^sub>v x\<rangle>) \<ge> 0"
    proof (intro allI impI)
      fix x :: "complex Matrix.vec"
      assume "dim_vec x = dim_row ?P"
      hence "dim_vec x = n" using P_n by simp
      thus "Re (\<langle>x | ?P *\<^sub>v x\<rangle>) \<ge> 0"
        using quad_real_nonneg by blast
    qed
    show ?thesis unfolding psd_def using herm nonneg P_n by simp
  qed

  show "completely_positive n 1 \<phi>"
    using choi_theorem[OF linear smult range npos one_pos] psd_choi by simp
qed

(* --------------------------------------------------------------------------
   5. Choi rank.

   \<open>choi_rank n d \<Phi>\<close> := the smallest \<open>length As\<close> over all Kraus
   representations of \<Phi>.  Choi's theorem gives
   \<open>choi_rank n d \<Phi> = rank (P\<^sub>\<Phi>)\<close>, which we state but defer.
   -------------------------------------------------------------------------- *)

definition choi_rank ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> nat" where
  "choi_rank n d \<Phi> \<equiv>
     Inf { length As | As :: complex Matrix.mat list.
             (\<forall>A \<in> set As. A \<in> carrier_mat d n)
             \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X) }"

(* Choi-rank = rank(P_\<Phi>) is deferred; it relies on a matrix-rank predicate
   for complex matrices that has not been set up in this development. *)


(* ============================================================================
   DAY 21 \<mdash> 14 / Oct / 11
   Topic: Kraus Rank Bound; Uniqueness of Minimal Kraus Representation
   ============================================================================ *)

(* --------------------------------------------------------------------------
   1. Kraus rank bound.

   For any CP map \<Phi>: M\<^sub>n \<rightarrow> M\<^sub>d, there is a Kraus representation with at
   most \<open>n*d\<close> operators.  Indeed, \<open>P\<^sub>\<Phi> \<in> M\<^sub>n\<^sub>d\<close> is psd by
   \<open>choi_theorem\<close>, hence factors as \<open>\<Sum>\<^sub>k v\<^sub>k v\<^sub>k\<^sup>\<dagger>\<close> with at most \<open>n*d\<close>
   vectors (one per coordinate of an eigenbasis of P\<^sub>\<Phi>).  The
   length-aware variants of \<open>psd_kraus_decomp\<close> and
   \<open>kraus_rep_of_psd_choi\<close> directly give the bound.
   -------------------------------------------------------------------------- *)

corollary kraus_rank_bound:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n
                      \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp:     "completely_positive n d \<Phi>"
      and npos:   "0 < n"
      and dpos:   "0 < d"
  shows "\<exists>As :: complex Matrix.mat list.
           length As \<le> n * d \<and>
           (\<forall>A \<in> set As. A \<in> carrier_mat d n) \<and>
           (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X)"
proof -
  have psd_choi: "psd (choi_matrix n d \<Phi>)"
    using choi_theorem[OF linear smult range npos dpos] cp by simp
  obtain Ws :: "complex Matrix.mat list"
    where Ws_len: "length Ws = n * d"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Ws_eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos psd_choi]
    by blast
  have Ws_len_le: "length Ws \<le> n * d" using Ws_len by simp
  show ?thesis using Ws_len_le Ws_c Ws_eq by blast
qed


(* --------------------------------------------------------------------------
   2. Trivial preservation: an injective linear map T : \<complex>\<^sup>r \<rightarrow> \<complex>\<^sup>m
      gives an onto adjoint T\<^sup>\<dagger> : \<complex>\<^sup>m \<rightarrow> \<complex>\<^sup>r.

   The Isabelle formalisation here is a thin wrapper: for any vector \<open>w\<close>
   of dimension \<open>m\<close>, the value \<open>T\<^sup>\<dagger> w\<close> exists and lies in \<complex>\<^sup>r.
   The deeper "onto" property (every \<open>h \<in> \<complex>\<^sup>r\<close> is hit) requires a
   rank-nullity argument and is deferred.
   -------------------------------------------------------------------------- *)

lemma adjoint_image_in_dom:
  fixes T :: "complex Matrix.mat"
  assumes sq: "T \<in> carrier_mat m r"
  shows "\<forall>w :: complex Matrix.vec. dim_vec w = m
           \<longrightarrow> dim_vec (T\<^sup>\<dagger> *\<^sub>v w) = r"
  using sq by auto


(* --------------------------------------------------------------------------
   3. Choi rank: bounded by \<open>n*d\<close>.

   The set whose infimum defines \<open>choi_rank\<close> is non-empty (Day 21 above)
   and consists of natural numbers, so the Inf is realised and bounded by
   \<open>n*d\<close>.  This is the abstract content of the rank inequality
   cr(\<Phi>) \<le> n d.
   -------------------------------------------------------------------------- *)

corollary choi_rank_le:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n
                      \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp:     "completely_positive n d \<Phi>"
      and npos:   "0 < n"
      and dpos:   "0 < d"
  shows "choi_rank n d \<Phi> \<le> n * d"
proof -
  obtain As where As_len: "length As \<le> n * d"
              and As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
              and As_eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X"
    using kraus_rank_bound[OF linear smult range cp npos dpos] by blast
  have len_in:
    "length As
       \<in> { length Bs | Bs :: complex Matrix.mat list.
              (\<forall>B \<in> set Bs. B \<in> carrier_mat d n)
              \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Bs X) }"
    using As_c As_eq by blast
  have "Inf { length Bs | Bs :: complex Matrix.mat list.
                 (\<forall>B \<in> set Bs. B \<in> carrier_mat d n)
                 \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Bs X) }
        \<le> length As"
    using len_in by (intro cInf_lower) auto
  also have "\<dots> \<le> n * d" using As_len .
  finally show ?thesis unfolding choi_rank_def .
qed


(* ============================================================================
   DAY 22 \<mdash> 17 / Oct / 11
   Topic: Linear Independence of Kraus Operators; Convex Sets; Krein-Milman
   ============================================================================ *)

(* --------------------------------------------------------------------------
   1. Convex sets and extreme points (abstract).

   Used as scaffolding for the next few days.  The definitions are
   parametric in subsets of \<open>complex Matrix.mat\<close>, viewing them as
   subsets of a real vector space via complex matrix arithmetic.
   -------------------------------------------------------------------------- *)

definition convex_set_mat :: "complex Matrix.mat set \<Rightarrow> bool" where
  "convex_set_mat C \<equiv>
     \<forall>A \<in> C. \<forall>B \<in> C. \<forall>t :: real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
       complex_of_real t \<cdot>\<^sub>m A
       + (1 - complex_of_real t) \<cdot>\<^sub>m B \<in> C"

definition extreme_point_mat ::
  "complex Matrix.mat set \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "extreme_point_mat C v \<equiv>
     v \<in> C \<and>
     \<not> (\<exists>v1 \<in> C. \<exists>v2 \<in> C. v1 \<noteq> v \<and> v \<noteq> v2 \<and>
           v = (1/2 :: complex) \<cdot>\<^sub>m v1 + (1/2 :: complex) \<cdot>\<^sub>m v2)"

definition affine_map_mat ::
  "(complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "affine_map_mat tmap \<equiv>
     \<forall>A B. \<forall>t :: real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
       tmap (complex_of_real t \<cdot>\<^sub>m A
             + (1 - complex_of_real t) \<cdot>\<^sub>m B) =
       complex_of_real t \<cdot>\<^sub>m tmap A
       + (1 - complex_of_real t) \<cdot>\<^sub>m tmap B"


(* --------------------------------------------------------------------------
   2. UCP and CPTP function-spaces.
   -------------------------------------------------------------------------- *)

definition UCP ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) set" where
  "UCP n d \<equiv> {\<Phi>. completely_positive n d \<Phi> \<and> unital_map n d \<Phi>}"

definition CPTP ::
  "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) set" where
  "CPTP n d \<equiv> {\<Phi>. completely_positive n d \<Phi> \<and> trace_preserving n \<Phi>}"


(* --------------------------------------------------------------------------
   3. Amplification commutes with scalar multiplication
   (companion to \<open>amplification_add\<close>).
   -------------------------------------------------------------------------- *)

lemma amplification_smult:
  assumes dpos: "0 < d"
      and F_block: "\<And>a b. F (block_of_mat n x a b) \<in> carrier_mat d d"
  shows "amplification n d p (\<lambda>\<rho>. c \<cdot>\<^sub>m F \<rho>) x
         = c \<cdot>\<^sub>m amplification n d p F x"
proof (rule eq_matI)
  show "dim_row (amplification n d p (\<lambda>\<rho>. c \<cdot>\<^sub>m F \<rho>) x) =
        dim_row (c \<cdot>\<^sub>m amplification n d p F x)"
    by (simp add: amplification_def)
  show "dim_col (amplification n d p (\<lambda>\<rho>. c \<cdot>\<^sub>m F \<rho>) x) =
        dim_col (c \<cdot>\<^sub>m amplification n d p F x)"
    by (simp add: amplification_def)
next
  fix i j
  assume i: "i < dim_row (c \<cdot>\<^sub>m amplification n d p F x)"
     and j: "j < dim_col (c \<cdot>\<^sub>m amplification n d p F x)"
  have ipd: "i < p*d" and jpd: "j < p*d"
    using i j by (simp_all add: amplification_def)
  have imodd: "i mod d < d" and jmodd: "j mod d < d"
    using dpos by simp_all
  let ?B = "block_of_mat n x (i div d) (j div d)"
  have FB: "F ?B \<in> carrier_mat d d"
    by (rule F_block)
  show "amplification n d p (\<lambda>\<rho>. c \<cdot>\<^sub>m F \<rho>) x $$ (i,j) =
        (c \<cdot>\<^sub>m amplification n d p F x) $$ (i,j)"
    using ipd jpd imodd jmodd FB
    by (simp add: amplification_def)
qed


(* --------------------------------------------------------------------------
   4. UCP is convex: \<open>t \<Phi>\<^sub>1 + (1-t) \<Phi>\<^sub>2 \<in> UCP\<close> for \<open>t \<in> [0,1]\<close>.

   The proof has two halves: CP closed under non-negative linear
   combinations (via \<open>amplification_add\<close>, \<open>amplification_smult\<close>,
   \<open>psd_smult_nonneg\<close>, \<open>psd_add_psd\<close>) and unitality preserved
   (since \<open>t \<sqdot> I + (1-t) \<sqdot> I = I\<close>).

   We strengthen the hypotheses slightly with explicit range conditions
   on each \<open>\<Phi>\<^sub>i\<close>; these are implicit in the standard reading of
   \<open>completely_positive n d\<close> (output in M_d), but \<open>completely_positive\<close>
   itself does not constrain the output type, so we make the range a
   formal assumption.
   -------------------------------------------------------------------------- *)

lemma UCP_convex:
  fixes t :: real
  assumes t_nn:   "0 \<le> t"
      and t_le:   "t \<le> 1"
      and \<Phi>1_in:  "\<Phi>1 \<in> UCP n d"
      and \<Phi>2_in:  "\<Phi>2 \<in> UCP n d"
      and r1: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>1 X \<in> carrier_mat d d"
      and r2: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>2 X \<in> carrier_mat d d"
      and dpos: "0 < d"
  shows "(\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X
              + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X) \<in> UCP n d"
proof -
  let ?\<Psi> = "\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X
                + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X"
  have cp1: "completely_positive n d \<Phi>1"
    using \<Phi>1_in by (simp add: UCP_def)
  have cp2: "completely_positive n d \<Phi>2"
    using \<Phi>2_in by (simp add: UCP_def)
  have un1: "unital_map n d \<Phi>1"
    using \<Phi>1_in by (simp add: UCP_def)
  have un2: "unital_map n d \<Phi>2"
    using \<Phi>2_in by (simp add: UCP_def)
  have one_minus_nn: "0 \<le> 1 - t" using t_le by simp
  have one_minus_eq: "(1 - complex_of_real t) = complex_of_real (1 - t)"
    by simp

  (* Unitality. *)
  have \<Psi>_unital: "unital_map n d ?\<Psi>"
  proof -
    have \<Phi>1_one: "\<Phi>1 (1\<^sub>m n) = 1\<^sub>m d" using un1 by (simp add: unital_map_def)
    have \<Phi>2_one: "\<Phi>2 (1\<^sub>m n) = 1\<^sub>m d" using un2 by (simp add: unital_map_def)
    have "?\<Psi> (1\<^sub>m n) = complex_of_real t \<cdot>\<^sub>m (1\<^sub>m d :: complex Matrix.mat)
                       + (1 - complex_of_real t) \<cdot>\<^sub>m (1\<^sub>m d)"
      using \<Phi>1_one \<Phi>2_one by simp
    also have "\<dots> = (complex_of_real t + (1 - complex_of_real t))
                     \<cdot>\<^sub>m (1\<^sub>m d :: complex Matrix.mat)"
      by (rule add_smult_distrib_right_mat[symmetric]) auto
    also have "\<dots> = (1 :: complex) \<cdot>\<^sub>m (1\<^sub>m d :: complex Matrix.mat)"
      by simp
    also have "\<dots> = 1\<^sub>m d"
      by (intro eq_matI) auto
    finally show ?thesis unfolding unital_map_def .
  qed

  (* Complete positivity. *)
  have \<Psi>_cp: "completely_positive n d ?\<Psi>"
    unfolding completely_positive_def p_positive_def
  proof (intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and X_c: "X \<in> carrier_mat (p*n) (p*n)"
       and X_psd: "psd X"
    have block_c: "\<And>a b. block_of_mat n X a b \<in> carrier_mat n n"
      by (simp add: block_of_mat_def)
    have F1_block: "\<And>a b. \<Phi>1 (block_of_mat n X a b) \<in> carrier_mat d d"
      using r1 block_c by blast
    have F2_block: "\<And>a b. \<Phi>2 (block_of_mat n X a b) \<in> carrier_mat d d"
      using r2 block_c by blast
    let ?F1 = "\<lambda>\<rho>. complex_of_real t \<cdot>\<^sub>m \<Phi>1 \<rho>"
    let ?F2 = "\<lambda>\<rho>. (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 \<rho>"
    have F1'_block: "\<And>a b. ?F1 (block_of_mat n X a b) \<in> carrier_mat d d"
      using F1_block by simp
    have F2'_block: "\<And>a b. ?F2 (block_of_mat n X a b) \<in> carrier_mat d d"
      using F2_block by simp

    (* amplification distributes over the convex combination *)
    have amp_eq:
      "amplification n d p ?\<Psi> X
         = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
           + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
    proof -
      have step_add:
        "amplification n d p (\<lambda>\<rho>. ?F1 \<rho> + ?F2 \<rho>) X
           = amplification n d p ?F1 X + amplification n d p ?F2 X"
        using amplification_add[where F = ?F1 and G = ?F2
                                 and n = n and d = d and p = p and x = X,
                                OF dpos F1'_block F2'_block] .
      have step_s1:
        "amplification n d p ?F1 X
           = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X"
        using amplification_smult[where F = \<Phi>1 and c = "complex_of_real t"
                                   and n = n and d = d and p = p and x = X,
                                  OF dpos F1_block] .
      have step_s2:
        "amplification n d p ?F2 X
           = (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
        using amplification_smult[where F = \<Phi>2 and c = "1 - complex_of_real t"
                                   and n = n and d = d and p = p and x = X,
                                  OF dpos F2_block] .
      show ?thesis using step_add step_s1 step_s2 by simp
    qed

    have amp1_psd: "psd (amplification n d p \<Phi>1 X)"
      using cp1 ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    have amp2_psd: "psd (amplification n d p \<Phi>2 X)"
      using cp2 ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    have amp1_c: "amplification n d p \<Phi>1 X \<in> carrier_mat (p*d) (p*d)"
      by (simp add: amplification_def)
    have amp2_c: "amplification n d p \<Phi>2 X \<in> carrier_mat (p*d) (p*d)"
      by (simp add: amplification_def)

    have term1_psd:
      "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X)"
      using t_nn amp1_psd amp1_c by (rule psd_smult_nonneg)
    have term2_psd:
      "psd ((1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
    proof -
      have prev: "psd (complex_of_real (1 - t)
                          \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
        using one_minus_nn amp2_psd amp2_c by (rule psd_smult_nonneg)
      have rew: "complex_of_real (1 - t) = 1 - complex_of_real t"
        by simp
      show ?thesis using prev rew by metis
    qed
    have term1_c:
      "complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
        \<in> carrier_mat (p*d) (p*d)"
      using amp1_c by simp
    have term2_c:
      "(1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X
        \<in> carrier_mat (p*d) (p*d)"
      using amp2_c by simp

    have psum_psd:
      "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
            + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
      using term1_psd term2_psd term1_c term2_c
      by (rule psd_add_psd)

    show "psd (amplification n d p ?\<Psi> X)"
      using amp_eq psum_psd by simp
  qed

  show ?thesis using \<Psi>_cp \<Psi>_unital by (simp add: UCP_def)
qed


(* --------------------------------------------------------------------------
   5. CPTP is convex.

   The CP half re-uses the argument from \<open>UCP_convex\<close>; trace-preservation
   reduces to \<open>Tr (\<Psi> X) = t \<sqdot> Tr X + (1-t) \<sqdot> Tr X = Tr X\<close> via
   \<open>Tr_add\<close> and \<open>Tr_smult\<close>.
   -------------------------------------------------------------------------- *)

lemma CPTP_convex:
  fixes t :: real
  assumes t_nn:   "0 \<le> t"
      and t_le:   "t \<le> 1"
      and \<Phi>1_in:  "\<Phi>1 \<in> CPTP n d"
      and \<Phi>2_in:  "\<Phi>2 \<in> CPTP n d"
      and r1: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>1 X \<in> carrier_mat d d"
      and r2: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi>2 X \<in> carrier_mat d d"
      and dpos: "0 < d"
  shows "(\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X
              + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X) \<in> CPTP n d"
proof -
  let ?\<Psi> = "\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X
                + (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X"
  have cp1: "completely_positive n d \<Phi>1"
    using \<Phi>1_in by (simp add: CPTP_def)
  have cp2: "completely_positive n d \<Phi>2"
    using \<Phi>2_in by (simp add: CPTP_def)
  have tp1: "trace_preserving n \<Phi>1"
    using \<Phi>1_in by (simp add: CPTP_def)
  have tp2: "trace_preserving n \<Phi>2"
    using \<Phi>2_in by (simp add: CPTP_def)

  have one_minus_nn: "0 \<le> 1 - t" using t_le by simp

  (* CP: copy of UCP_convex's CP half. *)
  have \<Psi>_cp: "completely_positive n d ?\<Psi>"
    unfolding completely_positive_def p_positive_def
  proof (intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and X_c: "X \<in> carrier_mat (p*n) (p*n)"
       and X_psd: "psd X"
    have block_c: "\<And>a b. block_of_mat n X a b \<in> carrier_mat n n"
      by (simp add: block_of_mat_def)
    have F1_block: "\<And>a b. \<Phi>1 (block_of_mat n X a b) \<in> carrier_mat d d"
      using r1 block_c by blast
    have F2_block: "\<And>a b. \<Phi>2 (block_of_mat n X a b) \<in> carrier_mat d d"
      using r2 block_c by blast
    let ?F1 = "\<lambda>\<rho>. complex_of_real t \<cdot>\<^sub>m \<Phi>1 \<rho>"
    let ?F2 = "\<lambda>\<rho>. (1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 \<rho>"
    have F1'_block: "\<And>a b. ?F1 (block_of_mat n X a b) \<in> carrier_mat d d"
      using F1_block by simp
    have F2'_block: "\<And>a b. ?F2 (block_of_mat n X a b) \<in> carrier_mat d d"
      using F2_block by simp
    have amp_eq:
      "amplification n d p ?\<Psi> X
         = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
           + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
    proof -
      have step_add:
        "amplification n d p (\<lambda>\<rho>. ?F1 \<rho> + ?F2 \<rho>) X
           = amplification n d p ?F1 X + amplification n d p ?F2 X"
        using amplification_add[where F = ?F1 and G = ?F2
                                 and n = n and d = d and p = p and x = X,
                                OF dpos F1'_block F2'_block] .
      have step_s1:
        "amplification n d p ?F1 X
           = complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X"
        using amplification_smult[where F = \<Phi>1 and c = "complex_of_real t"
                                   and n = n and d = d and p = p and x = X,
                                  OF dpos F1_block] .
      have step_s2:
        "amplification n d p ?F2 X
           = (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X"
        using amplification_smult[where F = \<Phi>2 and c = "1 - complex_of_real t"
                                   and n = n and d = d and p = p and x = X,
                                  OF dpos F2_block] .
      show ?thesis using step_add step_s1 step_s2 by simp
    qed
    have amp1_psd: "psd (amplification n d p \<Phi>1 X)"
      using cp1 ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    have amp2_psd: "psd (amplification n d p \<Phi>2 X)"
      using cp2 ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    have amp1_c: "amplification n d p \<Phi>1 X \<in> carrier_mat (p*d) (p*d)"
      by (simp add: amplification_def)
    have amp2_c: "amplification n d p \<Phi>2 X \<in> carrier_mat (p*d) (p*d)"
      by (simp add: amplification_def)
    have term1_psd:
      "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X)"
      using t_nn amp1_psd amp1_c by (rule psd_smult_nonneg)
    have term2_psd:
      "psd ((1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
    proof -
      have prev: "psd (complex_of_real (1 - t)
                          \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
        using one_minus_nn amp2_psd amp2_c by (rule psd_smult_nonneg)
      have rew: "complex_of_real (1 - t) = 1 - complex_of_real t" by simp
      show ?thesis using prev rew by metis
    qed
    have term1_c:
      "complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
        \<in> carrier_mat (p*d) (p*d)"
      using amp1_c by simp
    have term2_c:
      "(1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X
        \<in> carrier_mat (p*d) (p*d)"
      using amp2_c by simp
    have psum_psd:
      "psd (complex_of_real t \<cdot>\<^sub>m amplification n d p \<Phi>1 X
            + (1 - complex_of_real t) \<cdot>\<^sub>m amplification n d p \<Phi>2 X)"
      using term1_psd term2_psd term1_c term2_c by (rule psd_add_psd)
    show "psd (amplification n d p ?\<Psi> X)"
      using amp_eq psum_psd by simp
  qed

  (* Trace preservation: Tr(t Phi1 X + (1-t) Phi2 X) = Tr X. *)
  have \<Psi>_tp: "trace_preserving n ?\<Psi>"
  proof (unfold trace_preserving_def, intro allI impI)
    fix X :: "complex Matrix.mat"
    assume X_c: "X \<in> carrier_mat n n"
    have \<Phi>1X_c: "\<Phi>1 X \<in> carrier_mat d d" using r1 X_c by blast
    have \<Phi>2X_c: "\<Phi>2 X \<in> carrier_mat d d" using r2 X_c by blast
    have Tr1: "Tr (\<Phi>1 X) = Tr X"
      using tp1 X_c by (simp add: trace_preserving_def)
    have Tr2: "Tr (\<Phi>2 X) = Tr X"
      using tp2 X_c by (simp add: trace_preserving_def)
    have row_eq:
      "dim_row (complex_of_real t \<cdot>\<^sub>m \<Phi>1 X)
       = dim_row ((1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
      using \<Phi>1X_c \<Phi>2X_c by simp
    have col_eq:
      "dim_col (complex_of_real t \<cdot>\<^sub>m \<Phi>1 X)
       = dim_col ((1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
      using \<Phi>1X_c \<Phi>2X_c by simp
    have "Tr (?\<Psi> X) = Tr (complex_of_real t \<cdot>\<^sub>m \<Phi>1 X)
                       + Tr ((1 - complex_of_real t) \<cdot>\<^sub>m \<Phi>2 X)"
      using row_eq col_eq by (rule Tr_add)
    also have "\<dots> = complex_of_real t * Tr (\<Phi>1 X)
                    + (1 - complex_of_real t) * Tr (\<Phi>2 X)"
      by (simp add: Tr_smult)
    also have "\<dots> = complex_of_real t * Tr X
                    + (1 - complex_of_real t) * Tr X"
      using Tr1 Tr2 by simp
    also have "\<dots> = (complex_of_real t + (1 - complex_of_real t)) * Tr X"
      by (simp add: ring_distribs)
    also have "\<dots> = 1 * Tr X" by simp
    also have "\<dots> = Tr X" by simp
    finally show "Tr (?\<Psi> X) = Tr X" .
  qed

  show ?thesis using \<Psi>_cp \<Psi>_tp by (simp add: CPTP_def)
qed


(* ============================================================================
   DAY 29 \<mdash> 7 / Nov / 11
   Topic: Classical Error Correction; Hamming Weight and Distance

   Days 23-28 are skipped here:
     - Day 23 (Choi Theorem 3 / extreme-point classification of UCP)
       and Day 24-28 (Arveson Extension, separability, entanglement
       witnesses) require partial-isometry / Hahn-Banach machinery
       that lies beyond the matrix infrastructure currently set up.
   We resume at Day 29, which is purely classical and stands alone.
   ============================================================================ *)

(* --------------------------------------------------------------------------
   Classical binary strings as \<open>nat list\<close>s with entries in \<open>{0,1}\<close>.
   -------------------------------------------------------------------------- *)

definition hamming_weight :: "nat list \<Rightarrow> nat" where
  "hamming_weight v \<equiv> length (filter (\<lambda>b. b \<noteq> 0) v)"

definition hamming_dist :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "hamming_dist v w \<equiv> hamming_weight (map2 (\<lambda>a b. (a + b) mod 2) v w)"

lemma hamming_weight_Nil [simp]: "hamming_weight [] = 0"
  by (simp add: hamming_weight_def)

lemma hamming_weight_Cons:
  "hamming_weight (a # v)
     = (if a \<noteq> 0 then Suc (hamming_weight v) else hamming_weight v)"
  by (simp add: hamming_weight_def)

lemma hamming_dist_Nil [simp]:
  "hamming_dist [] [] = 0"
  by (simp add: hamming_dist_def)

lemma hamming_dist_Cons:
  "hamming_dist (a # v) (b # w)
     = (if (a + b) mod 2 \<noteq> 0
        then Suc (hamming_dist v w)
        else hamming_dist v w)"
  by (simp add: hamming_dist_def hamming_weight_Cons)

lemma hamming_dist_symm:
  assumes "length v = length w"
  shows "hamming_dist v w = hamming_dist w v"
  using assms
proof (induction v arbitrary: w)
  case Nil thus ?case by (cases w) simp_all
next
  case (Cons a v)
  then obtain b ws where w_eq: "w = b # ws"
    by (cases w) auto
  with Cons.prems have len_eq: "length v = length ws" by simp
  show ?case
    using Cons.IH[OF len_eq] w_eq
    by (simp add: hamming_dist_Cons add.commute)
qed

lemma hamming_dist_zero:
  assumes lenw:   "length v = length w"
      and bits_v: "\<forall>x \<in> set v. x < 2"
      and bits_w: "\<forall>x \<in> set w. x < 2"
  shows "hamming_dist v w = 0 \<longleftrightarrow> v = w"
  using lenw bits_v bits_w
proof (induction v arbitrary: w)
  case Nil
  hence "w = []" by (cases w) auto
  thus ?case by simp
next
  case (Cons a v)
  obtain b ws where w_eq: "w = b # ws"
    using Cons.prems(1) by (cases w) auto
  have len_eq: "length v = length ws"
    using Cons.prems(1) w_eq by simp
  have a_lt: "a < 2" using Cons.prems(2) by simp
  have b_lt: "b < 2" using Cons.prems(3) w_eq by simp
  have bits_v': "\<forall>x \<in> set v. x < 2" using Cons.prems(2) by simp
  have bits_ws: "\<forall>x \<in> set ws. x < 2" using Cons.prems(3) w_eq by simp
  have bit_eq_iff_mod: "((a + b) mod 2 = 0) \<longleftrightarrow> a = b"
    using a_lt b_lt by arith
  have IH: "hamming_dist v ws = 0 \<longleftrightarrow> v = ws"
    using Cons.IH[OF len_eq bits_v' bits_ws] .
  show ?case
    using w_eq bit_eq_iff_mod IH
    by (auto simp: hamming_dist_Cons)
qed

lemma hamming_dist_self [simp]:
  "hamming_dist v v = 0"
  by (induction v, auto simp: hamming_dist_Cons)


(* --------------------------------------------------------------------------
   Code distance and error-correction capacity.
   -------------------------------------------------------------------------- *)

definition code_distance :: "nat list set \<Rightarrow> nat" where
  "code_distance code \<equiv>
     if (\<exists>v \<in> code. \<exists>w \<in> code. v \<noteq> w)
     then Min {hamming_dist v w | v w. v \<in> code \<and> w \<in> code \<and> v \<noteq> w}
     else 0"

definition corrects_errors :: "nat list set \<Rightarrow> nat \<Rightarrow> bool" where
  "corrects_errors code t \<equiv> code_distance code \<ge> 2*t + 1"


(* --------------------------------------------------------------------------
   Parity-check encoding: append the XOR of all bits.

   Adding any single-bit error changes one bit of the codeword, so the
   corrupted word differs from the original.
   -------------------------------------------------------------------------- *)

definition parity_bit :: "nat list \<Rightarrow> nat" where
  "parity_bit v \<equiv> foldr (\<lambda>a b. (a + b) mod 2) v 0"

definition parity_check_encode :: "nat list \<Rightarrow> nat list" where
  "parity_check_encode v \<equiv> v @ [parity_bit v]"

lemma length_parity_check_encode [simp]:
  "length (parity_check_encode v) = length v + 1"
  by (simp add: parity_check_encode_def)

lemma hamming_weight_pos_iff:
  "0 < hamming_weight v \<longleftrightarrow> (\<exists>x \<in> set v. x \<noteq> 0)"
  by (induction v, auto simp: hamming_weight_Cons)

lemma hamming_dist_pos_iff:
  assumes lenw:   "length v = length w"
      and bits_v: "\<forall>x \<in> set v. x < 2"
      and bits_w: "\<forall>x \<in> set w. x < 2"
  shows "0 < hamming_dist v w \<longleftrightarrow> v \<noteq> w"
  using hamming_dist_zero[OF lenw bits_v bits_w] by linarith

lemma parity_bit_lt_2: "parity_bit v < 2"
  by (induction v, auto simp: parity_bit_def)

lemma parity_check_encode_binary:
  assumes "\<forall>x \<in> set v. x < 2"
  shows "\<forall>x \<in> set (parity_check_encode v). x < 2"
  using assms parity_bit_lt_2
  by (auto simp: parity_check_encode_def)

(* Adding any single-bit error to a parity-check codeword changes that bit:
   the corrupted word differs from the original.  Both \<open>v\<close> and \<open>e\<close>
   are required to be binary; without that, a non-binary error of even
   value could leave the codeword unchanged modulo 2. *)

lemma parity_check_detects_one_error:
  assumes lenE:   "length e = length v + 1"
      and bits_v: "\<forall>x \<in> set v. x < 2"
      and bits_e: "\<forall>x \<in> set e. x < 2"
      and weight: "hamming_weight e = 1"
  shows "parity_check_encode v
           \<noteq> map2 (\<lambda>a b. (a + b) mod 2) (parity_check_encode v) e"
proof
  let ?c = "parity_check_encode v"
  let ?d = "map2 (\<lambda>a b. (a + b) mod 2) ?c e"
  assume eq: "?c = ?d"

  have len_c: "length ?c = length v + 1" by simp

  (* The error is binary with exactly one nonzero entry, hence e ! i = 1 there. *)
  have "0 < hamming_weight e" using weight by simp
  hence "\<exists>x \<in> set e. x \<noteq> 0" by (simp add: hamming_weight_pos_iff)
  then obtain x where x_in: "x \<in> set e" and x_nz: "x \<noteq> 0" by blast
  from x_in obtain i where i_lt: "i < length e" and x_eq: "e ! i = x"
    by (metis in_set_conv_nth)
  from x_in bits_e have x_lt: "x < 2" by simp
  from x_nz x_lt x_eq have ei_one: "e ! i = 1" by linarith

  have i_lt_c: "i < length ?c" using i_lt lenE by simp

  (* The codeword is binary, so its i-th entry is in {0,1}. *)
  have ci_bin: "?c ! i < 2"
  proof -
    have "?c ! i \<in> set ?c"
      using i_lt_c by (rule nth_mem)
    thus ?thesis
      using parity_check_encode_binary[OF bits_v] by blast
  qed

  (* The XOR'ed word at index i is (?c ! i + e ! i) mod 2. *)
  have d_at_i: "?d ! i = (?c ! i + e ! i) mod 2"
    using i_lt i_lt_c lenE by simp

  have eq_i: "?c ! i = (?c ! i + 1) mod 2"
    using eq d_at_i ei_one by simp
  thus False using ci_bin by presburger
qed


definition repetition_encode :: "nat list \<Rightarrow> nat list" where
  "repetition_encode v \<equiv> v @ v"

lemma length_repetition_encode [simp]:
  "length (repetition_encode v) = 2 * length v"
  by (simp add: repetition_encode_def)

lemma hamming_dist_repetition_doubles:
  assumes "length v = length w"
  shows "hamming_dist (repetition_encode v) (repetition_encode w)
           = 2 * hamming_dist v w"
  using assms
  unfolding repetition_encode_def hamming_dist_def hamming_weight_def
  by (simp add: zip_append1 zip_append2 mult_2)


(* ============================================================================
   DAY 30 \<mdash> 9 / Nov / 11
   Topic: Quantum Error Correction; Bit Flip and Phase Flip Codes
   ============================================================================ *)

(* --------------------------------------------------------------------------
   The Pauli matrices.  We use the names \<open>pauli_X / Y / Z\<close> rather than
   the imported \<open>X / Y / Z\<close> from Quantum.thy so they can serve as locally
   stable, fixed-name constants in the rest of this development.  (The
   imported \<open>X / Y / Z\<close> are the same matrices.)
   -------------------------------------------------------------------------- *)

definition pauli_X :: "complex Matrix.mat" where
  "pauli_X \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if (i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0) then 1 else 0)"

definition pauli_Y :: "complex Matrix.mat" where
  "pauli_Y \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if i = 0 \<and> j = 1 then \<i>
                else if i = 1 \<and> j = 0 then -\<i> else 0)"

definition pauli_Z :: "complex Matrix.mat" where
  "pauli_Z \<equiv> Matrix.mat 2 2
       (\<lambda>(i,j). if i = 0 \<and> j = 0 then 1
                else if i = 1 \<and> j = 1 then -1 else 0)"

lemma pauli_X_carrier [simp]: "pauli_X \<in> carrier_mat 2 2"
  by (auto simp: pauli_X_def)

lemma pauli_Y_carrier [simp]: "pauli_Y \<in> carrier_mat 2 2"
  by (auto simp: pauli_Y_def)

lemma pauli_Z_carrier [simp]: "pauli_Z \<in> carrier_mat 2 2"
  by (auto simp: pauli_Z_def)

lemma pauli_X_dagger: "pauli_X\<^sup>\<dagger> = pauli_X"
proof (rule eq_matI)
  show "dim_row (pauli_X\<^sup>\<dagger>) = dim_row pauli_X" by (simp add: pauli_X_def)
  show "dim_col (pauli_X\<^sup>\<dagger>) = dim_col pauli_X" by (simp add: pauli_X_def)
next
  fix i j assume "i < dim_row pauli_X" "j < dim_col pauli_X"
  thus "(pauli_X\<^sup>\<dagger>) $$ (i, j) = pauli_X $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: pauli_X_def dagger_def)
qed

lemma pauli_X_squared: "pauli_X * pauli_X = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (pauli_X * pauli_X) = dim_row (1\<^sub>m 2)"
    by (simp add: pauli_X_def)
  show "dim_col (pauli_X * pauli_X) = dim_col (1\<^sub>m 2)"
    by (simp add: pauli_X_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(pauli_X * pauli_X) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding pauli_X_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2)+)
qed

lemma pauli_X_unitary: "unitary pauli_X"
  unfolding unitary_def
  using pauli_X_dagger pauli_X_squared by (simp add: pauli_X_def)

lemma pauli_Y_dagger: "pauli_Y\<^sup>\<dagger> = pauli_Y"
proof (rule eq_matI)
  show "dim_row (pauli_Y\<^sup>\<dagger>) = dim_row pauli_Y" by (simp add: pauli_Y_def)
  show "dim_col (pauli_Y\<^sup>\<dagger>) = dim_col pauli_Y" by (simp add: pauli_Y_def)
next
  fix i j assume "i < dim_row pauli_Y" "j < dim_col pauli_Y"
  thus "(pauli_Y\<^sup>\<dagger>) $$ (i, j) = pauli_Y $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: pauli_Y_def dagger_def)
qed

lemma pauli_Y_squared: "pauli_Y * pauli_Y = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (pauli_Y * pauli_Y) = dim_row (1\<^sub>m 2)"
    by (simp add: pauli_Y_def)
  show "dim_col (pauli_Y * pauli_Y) = dim_col (1\<^sub>m 2)"
    by (simp add: pauli_Y_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(pauli_Y * pauli_Y) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding pauli_Y_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2)+)
qed

lemma pauli_Y_unitary: "unitary pauli_Y"
  unfolding unitary_def
  using pauli_Y_dagger pauli_Y_squared by (simp add: pauli_Y_def)

lemma pauli_Z_dagger: "pauli_Z\<^sup>\<dagger> = pauli_Z"
proof (rule eq_matI)
  show "dim_row (pauli_Z\<^sup>\<dagger>) = dim_row pauli_Z" by (simp add: pauli_Z_def)
  show "dim_col (pauli_Z\<^sup>\<dagger>) = dim_col pauli_Z" by (simp add: pauli_Z_def)
next
  fix i j assume "i < dim_row pauli_Z" "j < dim_col pauli_Z"
  thus "(pauli_Z\<^sup>\<dagger>) $$ (i, j) = pauli_Z $$ (i, j)"
    by (cases "i = 0"; cases "j = 0"; simp add: pauli_Z_def dagger_def)
qed

lemma pauli_Z_squared: "pauli_Z * pauli_Z = 1\<^sub>m 2"
proof (rule eq_matI)
  show "dim_row (pauli_Z * pauli_Z) = dim_row (1\<^sub>m 2)"
    by (simp add: pauli_Z_def)
  show "dim_col (pauli_Z * pauli_Z) = dim_col (1\<^sub>m 2)"
    by (simp add: pauli_Z_def)
next
  fix i j assume "i < dim_row (1\<^sub>m 2)" "j < dim_col (1\<^sub>m 2)"
  hence ij: "i < 2" "j < 2" by auto
  thus "(pauli_Z * pauli_Z) $$ (i, j) = (1\<^sub>m 2) $$ (i, j)"
    unfolding pauli_Z_def scalar_prod_def
    by (cases i, cases j, (simp add: sumof2)+)
qed

lemma pauli_Z_unitary: "unitary pauli_Z"
  unfolding unitary_def
  using pauli_Z_dagger pauli_Z_squared by (simp add: pauli_Z_def)


(* --------------------------------------------------------------------------
   I, X, Y, Z form an orthogonal basis of M\<^sub>2 with respect to the
   Hilbert-Schmidt inner product, each having squared norm 2.
   -------------------------------------------------------------------------- *)

proposition pauli_orthogonal:
  shows "\<langle>\<langle> 1\<^sub>m 2 | pauli_X \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> 1\<^sub>m 2 | pauli_Y \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> 1\<^sub>m 2 | pauli_Z \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> pauli_X | pauli_Y \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> pauli_X | pauli_Z \<rangle>\<rangle> = 0"
    and "\<langle>\<langle> pauli_Y | pauli_Z \<rangle>\<rangle> = 0"
proof -
  show "\<langle>\<langle> 1\<^sub>m 2 | pauli_X \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_X_def numeral_2_eq_2)
  show "\<langle>\<langle> 1\<^sub>m 2 | pauli_Y \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle> 1\<^sub>m 2 | pauli_Z \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_Z_def numeral_2_eq_2)
  show "\<langle>\<langle> pauli_X | pauli_Y \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_X_def pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle> pauli_X | pauli_Z \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_X_def pauli_Z_def numeral_2_eq_2)
  show "\<langle>\<langle> pauli_Y | pauli_Z \<rangle>\<rangle> = 0"
    by (simp add: hs_inner_prod_def pauli_Y_def pauli_Z_def numeral_2_eq_2)
qed

proposition pauli_norm:
  shows "\<langle>\<langle> 1\<^sub>m 2 | (1\<^sub>m 2 :: complex Matrix.mat) \<rangle>\<rangle> = 2"
    and "\<langle>\<langle> pauli_X | pauli_X \<rangle>\<rangle> = 2"
    and "\<langle>\<langle> pauli_Y | pauli_Y \<rangle>\<rangle> = 2"
    and "\<langle>\<langle> pauli_Z | pauli_Z \<rangle>\<rangle> = 2"
proof -
  show "\<langle>\<langle> 1\<^sub>m 2 | (1\<^sub>m 2 :: complex Matrix.mat) \<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def numeral_2_eq_2)
  show "\<langle>\<langle> pauli_X | pauli_X \<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def pauli_X_def numeral_2_eq_2)
  show "\<langle>\<langle> pauli_Y | pauli_Y \<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def pauli_Y_def numeral_2_eq_2)
  show "\<langle>\<langle> pauli_Z | pauli_Z \<rangle>\<rangle> = 2"
    by (simp add: hs_inner_prod_def pauli_Z_def numeral_2_eq_2)
qed


(* --------------------------------------------------------------------------
   The bit-flip channel: with probability \<open>p\<close>, apply Pauli X.
   -------------------------------------------------------------------------- *)

definition bit_flip_channel ::
  "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "bit_flip_channel p \<rho> \<equiv>
     complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
     + complex_of_real p \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>))"

lemma bit_flip_channel_carrier:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "bit_flip_channel p \<rho> \<in> carrier_mat 2 2"
proof -
  have x_c: "pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c assms by (rule mult_carrier_mat)
  have x\<rho>xd_c: "pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)
  show ?thesis
    using assms x\<rho>xd_c by (auto simp: bit_flip_channel_def)
qed

(* The bit-flip channel preserves trace: Tr(X rho X^dagger) = Tr rho
   since X^dagger X = I, then add the (1-p) and p contributions. *)

lemma bit_flip_channel_trace_preserving:
  fixes p :: real
  assumes \<rho>_c: "\<rho> \<in> carrier_mat 2 2"
  shows "Tr (bit_flip_channel p \<rho>) = Tr \<rho>"
proof -
  have x_c: "pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c \<rho>_c by (rule mult_carrier_mat)
  have x\<rho>xd_c: "pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)
  have xdx_eq: "(pauli_X\<^sup>\<dagger>) * pauli_X = 1\<^sub>m 2"
    using pauli_X_dagger pauli_X_squared by simp

  (* Tr(X \<rho> X^dagger) = Tr(X^dagger X \<rho>) = Tr(I \<rho>) = Tr \<rho>, by cyclicity. *)
  have tr_conj: "Tr (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)) = Tr \<rho>"
  proof -
    have "Tr (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)) = Tr (pauli_X\<^sup>\<dagger> * (pauli_X * \<rho>))"
    proof (rule Tr_cyclic)
      show "dim_col (pauli_X * \<rho>) = dim_row (pauli_X\<^sup>\<dagger>)"
        using x\<rho>_c xd_c by (metis carrier_matD)
      show "dim_row (pauli_X * \<rho>) = dim_col (pauli_X\<^sup>\<dagger>)"
        using x\<rho>_c xd_c by (metis carrier_matD)
    qed
    also have "\<dots> = Tr ((pauli_X\<^sup>\<dagger> * pauli_X) * \<rho>)"
      by (metis xd_c x_c \<rho>_c assoc_mult_mat)
    also have "\<dots> = Tr ((1\<^sub>m 2) * \<rho>)" using xdx_eq by simp
    also have "\<dots> = Tr \<rho>" using \<rho>_c by simp
    finally show ?thesis .
  qed

  have row_eq: "dim_row (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_row (complex_of_real p \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)))"
    using \<rho>_c x\<rho>xd_c by (metis carrier_matD index_smult_mat)
  have col_eq: "dim_col (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_col (complex_of_real p \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)))"
    using \<rho>_c x\<rho>xd_c by (metis carrier_matD index_smult_mat)
  have "Tr (bit_flip_channel p \<rho>)
          = Tr (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
            + Tr (complex_of_real p \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)))"
    unfolding bit_flip_channel_def
    using row_eq col_eq by (rule Tr_add)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>))"
    by (simp add: Tr_smult)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr \<rho>"
    using tr_conj by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) * Tr \<rho>"
    by (simp add: ring_distribs)
  also have "\<dots> = 1 * Tr \<rho>"
    by simp
  also have "\<dots> = Tr \<rho>" by simp
  finally show ?thesis .
qed

(* The bit-flip channel preserves PSD: convex combination of two PSD
   matrices, where X . rho . X^dagger is PSD via X^2 = I. *)

lemma bit_flip_channel_psd:
  fixes p :: real
  assumes p_nn:    "0 \<le> p"
      and p_le_1:  "p \<le> 1"
      and \<rho>_c:    "\<rho> \<in> carrier_mat 2 2"
      and \<rho>_psd:  "psd \<rho>"
  shows "psd (bit_flip_channel p \<rho>)"
proof -
  have x_c: "pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c \<rho>_c by (rule mult_carrier_mat)
  have x\<rho>xd_c: "pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)

  have one_minus_nn: "0 \<le> 1 - p" using p_le_1 by simp

  (* X . \<rho> . X^dagger is PSD: factor \<rho> = Q*Q via the psd-sqrt, then
     X . Q*Q . X^dagger = (X Q) (X Q)^dagger which is psd by psd_MdagM. *)
  have conj_psd: "psd (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>))"
  proof -
    obtain Q where Q_c:    "Q \<in> carrier_mat 2 2"
               and Q_psd:  "psd Q"
               and Q_sq:   "Q * Q = \<rho>"
      using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
    have Q_dagger: "Q\<^sup>\<dagger> = Q"
      using Q_psd by (simp add: psd_def hermitian_def)
    have XQ_c: "pauli_X * Q \<in> carrier_mat 2 2"
      using x_c Q_c by (rule mult_carrier_mat)
    have XQd_c: "(pauli_X * Q)\<^sup>\<dagger> \<in> carrier_mat 2 2"
      using XQ_c by (rule dagger_carrier)
    have eq: "pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>) = (pauli_X * Q) * ((pauli_X * Q)\<^sup>\<dagger>)"
    proof -
      have dim_eq: "dim_col pauli_X = dim_row Q"
        using x_c Q_c by (metis carrier_matD)
      have dagprod: "(pauli_X * Q)\<^sup>\<dagger> = (Q\<^sup>\<dagger>) * (pauli_X\<^sup>\<dagger>)"
        using dim_eq by (rule dagger_of_prod)
      hence dagprod': "(pauli_X * Q)\<^sup>\<dagger> = Q * (pauli_X\<^sup>\<dagger>)"
        using Q_dagger by simp
      have "(pauli_X * Q) * ((pauli_X * Q)\<^sup>\<dagger>)
              = (pauli_X * Q) * (Q * (pauli_X\<^sup>\<dagger>))"
        using dagprod' by simp
      also have "\<dots> = pauli_X * Q * Q * (pauli_X\<^sup>\<dagger>)"
        using x_c Q_c xd_c by (metis assoc_mult_mat mult_carrier_mat)
      also have "\<dots> = pauli_X * (Q * Q) * (pauli_X\<^sup>\<dagger>)"
        using x_c Q_c by (metis assoc_mult_mat)
      also have "\<dots> = pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)"
        using Q_sq by simp
      finally show ?thesis by simp
    qed
    have psd_dd: "psd (((pauli_X * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((pauli_X * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF XQd_c] .
    have dd_eq: "(pauli_X * Q)\<^sup>\<dagger>\<^sup>\<dagger> = pauli_X * Q"
      using XQ_c by (simp add: dagger_of_dagger_is_id)
    have "psd ((pauli_X * Q) * ((pauli_X * Q)\<^sup>\<dagger>))"
      using psd_dd dd_eq by simp
    thus ?thesis using eq by simp
  qed

  have term1_psd: "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)"
    using one_minus_nn \<rho>_psd \<rho>_c by (rule psd_smult_nonneg)
  have term2_psd: "psd (complex_of_real p \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)))"
    using p_nn conj_psd x\<rho>xd_c by (rule psd_smult_nonneg)

  have term1_c: "complex_of_real (1 - p) \<cdot>\<^sub>m \<rho> \<in> carrier_mat 2 2"
    using \<rho>_c by simp
  have term2_c: "complex_of_real p \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>))
                   \<in> carrier_mat 2 2"
    using x\<rho>xd_c by simp

  have "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
              + complex_of_real p \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)))"
    using term1_psd term2_psd term1_c term2_c by (rule psd_add_psd)
  thus ?thesis by (simp add: bit_flip_channel_def)
qed


(* ============================================================================
   DAY 31 \<mdash> 11 / Nov / 11
   Topic: Three Qubit Bit Flip Code; Fidelity
   ============================================================================ *)

(* Logical encoding |\<psi>\<rangle> = a|0\<rangle> + b|1\<rangle> \<mapsto> a|000\<rangle> + b|111\<rangle>, expressed as
   a 8\<times>2 isometry sending the i-th computational basis vector of \<complex>\<^sup>2 to
   the i-th computational basis vector of \<complex>\<^sup>8 (with i \<in> {0, 7}). *)

definition encode_mat :: "complex Matrix.mat" where
  "encode_mat \<equiv> Matrix.mat 8 2 (\<lambda>(i,j).
     if i = 0 \<and> j = 0 then 1
     else if i = 7 \<and> j = 1 then 1
     else 0)"

lemma encode_mat_carrier [simp]: "encode_mat \<in> carrier_mat 8 2"
  by (auto simp: encode_mat_def)

(* Fidelity between a pure state \<psi> and a density matrix \<rho>. *)

definition fidelity ::
  "complex Matrix.vec \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where
  "fidelity \<psi> \<rho> \<equiv> sqrt (Re (\<langle>\<psi> | \<rho> *\<^sub>v \<psi>\<rangle>))"

lemma fidelity_def_eq:
  "fidelity \<psi> \<rho> = sqrt (Re (\<langle>\<psi> | \<rho> *\<^sub>v \<psi>\<rangle>))"
  by (simp add: fidelity_def)

(* For a pure state \<rho> = |\<psi>'\<rangle>\<langle>\<psi>'|, fidelity = |\<langle>\<psi> | \<psi>'\<rangle>|. *)

lemma fidelity_pure_states:
  fixes \<psi> \<psi>' :: "complex Matrix.vec"
  assumes \<psi>_qs:  "quantum_state n \<psi>"
      and \<psi>'_qs: "quantum_state n \<psi>'"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>))
           = cmod (\<langle>\<psi> | \<psi>'\<rangle>)"
proof -
  let ?\<rho> = "(mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>)"
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have \<psi>'_dim: "dim_vec \<psi>' = n" using \<psi>'_qs by (simp add: quantum_state_def)

  have rho_eq: "?\<rho> = outer_sum n [\<psi>']"
    by (simp add: outer_sum_def)

  (* ?\<rho> *_v \<psi> = \<langle>\<psi>'|\<psi>\<rangle> \<cdot>\<^sub>v \<psi>' *)
  have \<rho>\<psi>: "?\<rho> *\<^sub>v \<psi> = \<langle>\<psi>' | \<psi>\<rangle> \<cdot>\<^sub>v \<psi>'"
    using outer_sum_singleton_mult_vec[OF \<psi>'_dim \<psi>_dim] rho_eq by simp

  (* \<langle>\<psi> | ?\<rho> *_v \<psi>\<rangle> = \<langle>\<psi>|\<psi>'\<rangle> * \<langle>\<psi>'|\<psi>\<rangle> = (cmod \<langle>\<psi>|\<psi>'\<rangle>)^2 *)
  have inner_eq: "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<psi>'\<rangle> * \<langle>\<psi>' | \<psi>\<rangle>"
  proof -
    have "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<langle>\<psi>'|\<psi>\<rangle> \<cdot>\<^sub>v \<psi>'\<rangle>"
      using \<rho>\<psi> by simp
    also have "\<dots> = \<langle>\<psi>'|\<psi>\<rangle> * \<langle>\<psi> | \<psi>'\<rangle>"
      by (rule inner_prod_right_smult')
    finally show ?thesis by (simp add: mult.commute)
  qed

  have conj_swap: "\<langle>\<psi>' | \<psi>\<rangle> = cnj (\<langle>\<psi> | \<psi>'\<rangle>)"
    by (metis \<psi>_dim \<psi>'_dim inner_prod_cnj)

  have sq_real:
    "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = complex_of_real ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
  proof -
    have "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<psi>'\<rangle> * cnj (\<langle>\<psi> | \<psi>'\<rangle>)"
      using inner_eq conj_swap by simp
    also have "\<dots> = complex_of_real ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
      by (simp add: complex_norm_square mult.commute, metis complex_norm_square of_real_power)
    finally show ?thesis.
  qed

  have re_eq: "Re (\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle>) = (cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2"
    using sq_real by simp

  have nn: "0 \<le> cmod (\<langle>\<psi> | \<psi>'\<rangle>)" by simp

  have "fidelity \<psi> ?\<rho> = sqrt (Re (\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle>))"
    by (simp add: fidelity_def)
  also have "\<dots> = sqrt ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
    using re_eq by simp
  also have "\<dots> = cmod (\<langle>\<psi> | \<psi>'\<rangle>)"
    using nn by simp
  finally show ?thesis.
qed

(* Pure-state fidelity to itself: a unit vector has fidelity 1 with its own
   density matrix. *)

lemma fidelity_self:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>]) * ((mat_of_cols n [\<psi>])\<^sup>\<dagger>)) = 1"
proof -
  have norm1: "\<parallel>\<psi>\<parallel> = 1"
    using \<psi>_qs by (simp add: quantum_state_def)
  have "fidelity \<psi> ((mat_of_cols n [\<psi>]) * ((mat_of_cols n [\<psi>])\<^sup>\<dagger>))
          = cmod (\<langle>\<psi> | \<psi>\<rangle>)"
    using fidelity_pure_states[OF \<psi>_qs \<psi>_qs] .
  also have "\<dots> = cmod (complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2))"
    by (metis cpx_vec_length_inner_prod)
  also have "\<dots> = cmod (complex_of_real (1\<^sup>2))"
    using norm1 by simp
  also have "\<dots> = 1"
    by simp
  finally show ?thesis .
qed

(* Pure-state fidelity is zero on orthogonal states. *)

lemma fidelity_orthogonal:
  fixes \<psi> \<psi>' :: "complex Matrix.vec"
  assumes \<psi>_qs:  "quantum_state n \<psi>"
      and \<psi>'_qs: "quantum_state n \<psi>'"
      and ortho: "\<langle>\<psi> | \<psi>'\<rangle> = 0"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>)) = 0"
  using fidelity_pure_states[OF \<psi>_qs \<psi>'_qs] ortho by simp


(* ============================================================================
   DAY 32 \<mdash> 14 / Nov / 11
   Topic: Phase Flip Code; Plus and Minus States
   ============================================================================ *)

(* The X-eigenbasis of \<complex>\<^sup>2: |+\<rangle> = (|0\<rangle> + |1\<rangle>)/\<surd>2, |-\<rangle> = (|0\<rangle> - |1\<rangle>)/\<surd>2. *)

definition ket_plus :: "complex Matrix.vec" where
  "ket_plus \<equiv> (1 / sqrt 2 :: complex) \<cdot>\<^sub>v (unit_vec 2 0 + unit_vec 2 1)"

definition ket_minus :: "complex Matrix.vec" where
  "ket_minus \<equiv> (1 / sqrt 2 :: complex) \<cdot>\<^sub>v (unit_vec 2 0 - unit_vec 2 1)"

lemma ket_plus_carrier [simp]: "ket_plus \<in> carrier_vec 2"
  by (simp add: ket_plus_def)

lemma ket_minus_carrier [simp]: "ket_minus \<in> carrier_vec 2"
  by (simp add: ket_minus_def)

lemma ket_plus_dim [simp]: "dim_vec ket_plus = 2"
  by (simp add: ket_plus_def)

lemma ket_minus_dim [simp]: "dim_vec ket_minus = 2"
  by (simp add: ket_minus_def)

lemma ket_plus_index_0: "ket_plus $ 0 = 1 / sqrt 2"
  by (simp add: ket_plus_def)

lemma ket_plus_index_1: "ket_plus $ 1 = 1 / sqrt 2"
  by (simp add: ket_plus_def)

lemma ket_minus_index_0: "ket_minus $ 0 = 1 / sqrt 2"
  by (simp add: ket_minus_def)

lemma ket_minus_index_1: "ket_minus $ 1 = - 1 / sqrt 2"
  by (simp add: ket_minus_def)

lemma ket_plus_unit: "\<parallel>ket_plus\<parallel> = 1"
proof -
  have inner: "\<langle>ket_plus | ket_plus\<rangle> = 1"
  proof -
    have "\<langle>ket_plus | ket_plus\<rangle>
            = (\<Sum>i = 0..<2. cnj (ket_plus $ i) * (ket_plus $ i))"
      unfolding inner_prod_def by simp
    also have "\<dots> = cnj (ket_plus $ 0) * (ket_plus $ 0)
                    + cnj (ket_plus $ 1) * (ket_plus $ 1)"
      by (simp add: numeral_2_eq_2)
    also have "\<dots> = 1"
      unfolding ket_plus_def by (simp add: of_real_mult [symmetric])
    finally show ?thesis .
  qed
  have "(\<parallel>ket_plus\<parallel>)\<^sup>2 = 1"
    using inner by (metis cpx_vec_length_inner_prod of_real_1 of_real_eq_iff)
  thus ?thesis
    by (metis cpx_vec_length_inner_prod cpx_vec_length_zero_iff
        inner_prod_csqrt ket_plus_carrier ket_plus_dim norm_eq_zero
        norm_of_real normalized_vec_norm of_real_eq_0_iff of_real_eq_1_iff
        power2_eq_1_iff real_sqrt_abs)
qed

lemma ket_minus_unit: "\<parallel>ket_minus\<parallel> = 1"
proof -
  have inner: "\<langle>ket_minus | ket_minus\<rangle> = 1"
  proof -
    have "\<langle>ket_minus | ket_minus\<rangle>
            = (\<Sum>i = 0..<2. cnj (ket_minus $ i) * (ket_minus $ i))"
      unfolding inner_prod_def by simp
    also have "\<dots> = cnj (ket_minus $ 0) * (ket_minus $ 0)
                    + cnj (ket_minus $ 1) * (ket_minus $ 1)"
      by (simp add: numeral_2_eq_2)
    also have "\<dots> = 1"
      unfolding ket_minus_def by (simp add: of_real_mult [symmetric])
    finally show ?thesis .
  qed
  have "(\<parallel>ket_minus\<parallel>)\<^sup>2 = 1"
    using inner by (metis cpx_vec_length_inner_prod of_real_1 of_real_eq_iff)
  thus ?thesis
    by (metis cpx_vec_length_inner_prod inner_prod_csqrt ket_plus_unit
        of_real_eq_1_iff power_one)
qed

lemma ket_plus_minus_orthog: "\<langle>ket_plus | ket_minus\<rangle> = 0"
proof -
  have "\<langle>ket_plus | ket_minus\<rangle>
          = (\<Sum>i = 0..<2. cnj (ket_plus $ i) * (ket_minus $ i))"
    unfolding inner_prod_def by simp
  also have "\<dots> = cnj (ket_plus $ 0) * (ket_minus $ 0)
                  + cnj (ket_plus $ 1) * (ket_minus $ 1)"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = 0"
    unfolding ket_plus_def ket_minus_def by simp
  finally show ?thesis .
qed

(* Pauli Z swaps |+\<rangle> and |-\<rangle>:  Z|+\<rangle> = |-\<rangle>, Z|-\<rangle> = |+\<rangle>. *)

lemma pauli_Z_ket_plus: "pauli_Z *\<^sub>v ket_plus = ket_minus"
proof (rule eq_vecI)
  show "dim_vec (pauli_Z *\<^sub>v ket_plus) = dim_vec ket_minus"
    by (simp add: pauli_Z_def)
next
  fix i assume "i < dim_vec ket_minus"
  hence i_lt: "i < 2" by simp
  have "(pauli_Z *\<^sub>v ket_plus) $ i =
        (\<Sum>k = 0..<2. pauli_Z $$ (i, k) * ket_plus $ k)"
    using i_lt by (simp add: scalar_prod_def pauli_Z_def)
  also have "\<dots> = pauli_Z $$ (i, 0) * ket_plus $ 0
                  + pauli_Z $$ (i, 1) * ket_plus $ 1"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = ket_minus $ i"
    using i_lt
    by (cases "i = 0";
        simp add: pauli_Z_def ket_plus_def ket_minus_def)
  finally show "(pauli_Z *\<^sub>v ket_plus) $ i = ket_minus $ i" .
qed

lemma pauli_Z_ket_minus: "pauli_Z *\<^sub>v ket_minus = ket_plus"
proof -
  have "pauli_Z *\<^sub>v ket_minus = pauli_Z *\<^sub>v (pauli_Z *\<^sub>v ket_plus)"
    using pauli_Z_ket_plus by simp
  also have "\<dots> = (pauli_Z * pauli_Z) *\<^sub>v ket_plus"
    by (metis assoc_mult_mat_vec pauli_Z_carrier ket_plus_carrier)
  also have "\<dots> = (1\<^sub>m 2) *\<^sub>v ket_plus"
    using pauli_Z_squared by simp
  also have "\<dots> = ket_plus" by simp
  finally show ?thesis .
qed

(* |+\<rangle> and |-\<rangle> are eigenvectors of X with eigenvalues +1 and -1. *)

lemma pauli_X_ket_plus: "pauli_X *\<^sub>v ket_plus = ket_plus"
proof (rule eq_vecI)
  show "dim_vec (pauli_X *\<^sub>v ket_plus) = dim_vec ket_plus"
    by (simp add: pauli_X_def)
next
  fix i assume "i < dim_vec ket_plus"
  hence i_lt: "i < 2" by simp
  have "(pauli_X *\<^sub>v ket_plus) $ i =
        (\<Sum>k = 0..<2. pauli_X $$ (i, k) * ket_plus $ k)"
    using i_lt by (simp add: scalar_prod_def pauli_X_def)
  also have "\<dots> = pauli_X $$ (i, 0) * ket_plus $ 0
                  + pauli_X $$ (i, 1) * ket_plus $ 1"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = ket_plus $ i"
    using i_lt
    by (cases "i = 0";
        simp add: pauli_X_def ket_plus_def)
  finally show "(pauli_X *\<^sub>v ket_plus) $ i = ket_plus $ i" .
qed

lemma pauli_X_ket_minus: "pauli_X *\<^sub>v ket_minus = - ket_minus"
proof (rule eq_vecI)
  show "dim_vec (pauli_X *\<^sub>v ket_minus) = dim_vec (- ket_minus)"
    by (simp add: pauli_X_def)
next
  fix i assume "i < dim_vec (- ket_minus)"
  hence i_lt: "i < 2" by simp
  have "(pauli_X *\<^sub>v ket_minus) $ i =
        (\<Sum>k = 0..<2. pauli_X $$ (i, k) * ket_minus $ k)"
    using i_lt by (simp add: scalar_prod_def pauli_X_def)
  also have "\<dots> = pauli_X $$ (i, 0) * ket_minus $ 0
                  + pauli_X $$ (i, 1) * ket_minus $ 1"
    by (simp add: numeral_2_eq_2)
  also have "\<dots> = (- ket_minus) $ i"
    using i_lt
    by (cases "i = 0";
        simp add: pauli_X_def ket_minus_def)
  finally show "(pauli_X *\<^sub>v ket_minus) $ i = (- ket_minus) $ i" .
qed


(* --------------------------------------------------------------------------
   Shor 9-qubit logical states.

   We package only the explicit vector-valued definitions; the recovery
   theorem (Day 33) and Knill-Laflamme conditions (Day 34) are deep
   results that lie beyond the current development.
   -------------------------------------------------------------------------- *)

definition shor_zero :: "complex Matrix.vec" where
  "shor_zero \<equiv>
     let v = unit_vec 2 0 + unit_vec 2 1 in
     (1 / (2 * sqrt 2) :: complex)
       \<cdot>\<^sub>v tensor_vec (tensor_vec v v) v"

definition shor_one :: "complex Matrix.vec" where
  "shor_one \<equiv>
     let v = unit_vec 2 0 - unit_vec 2 1 in
     (1 / (2 * sqrt 2) :: complex)
       \<cdot>\<^sub>v tensor_vec (tensor_vec v v) v"

lemma shor_zero_dim [simp]: "dim_vec shor_zero = 8"
  by (simp add: shor_zero_def Let_def, simp add: tensor_vec_dim)

lemma shor_one_dim [simp]: "dim_vec shor_one = 8"
  by (smt (verit, best) index_minus_vec(2) index_smult_vec(2) index_unit_vec(3) 
      mult_2 mult_commute_abs numeral_Bit0 shor_one_def tensor_vec_dim)

lemma shor_zero_carrier [simp]: "shor_zero \<in> carrier_vec 8"
  by (simp add: carrier_dim_vec)

lemma shor_one_carrier [simp]: "shor_one \<in> carrier_vec 8"
  by (simp add: carrier_dim_vec)


(* --------------------------------------------------------------------------
   Projection operators.

   A projection P on \<complex>\<^sup>n is a hermitian idempotent: P\<^sup>\<dagger> = P
   and P * P = P.  These are the building blocks of the syndrome-recovery
   construction (Days 33-34).
   -------------------------------------------------------------------------- *)

definition projection :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "projection n P \<equiv>
     P \<in> carrier_mat n n \<and> hermitian P \<and> P * P = P"

lemma projection_carrier:
  "projection n P \<Longrightarrow> P \<in> carrier_mat n n"
  by (simp add: projection_def)

lemma projection_hermitian:
  "projection n P \<Longrightarrow> hermitian P"
  by (simp add: projection_def)

lemma projection_idempotent:
  "projection n P \<Longrightarrow> P * P = P"
  by (simp add: projection_def)

lemma projection_zero: "projection n (0\<^sub>m n n)"
  by (auto simp: projection_def hermitian_def dagger_def)

lemma projection_one: "projection n (1\<^sub>m n)"
  by (auto simp: projection_def hermitian_def dagger_def)

(* A projection is psd: it equals P\<^sup>\<dagger> P, which is psd by psd_MdagM. *)

lemma projection_psd:
  assumes "projection n P"
  shows "psd P"
proof -
  have P_c: "P \<in> carrier_mat n n" using assms by (rule projection_carrier)
  have P_h: "hermitian P" using assms by (rule projection_hermitian)
  have P_idem: "P * P = P" using assms by (rule projection_idempotent)
  have P_dag: "P\<^sup>\<dagger> = P" using P_h by (simp add: hermitian_def)
  have eq: "P = (P\<^sup>\<dagger>) * P" using P_dag P_idem by simp
  have psd_PdP: "psd (P\<^sup>\<dagger> * P)"
    using P_c by (rule psd_MdagM)
  show ?thesis using eq psd_PdP by simp
qed

(* Complementary projection P0 = I - P, when P is a projection. *)

lemma projection_complement_idempotent:
  assumes "projection n P"
  shows "(1\<^sub>m n - P) * (1\<^sub>m n - P) = 1\<^sub>m n - P"
proof -
  have P_c: "P \<in> carrier_mat n n"
    using assms by (rule projection_carrier)

  have P_idem: "P * P = P"
    using assms by (rule projection_idempotent)

  have P_one_l: "1\<^sub>m n * P = P"
    using P_c by simp

  have P_one_r: "P * 1\<^sub>m n = P"
    using P_c by simp

  have I_one: "(1\<^sub>m n :: complex Matrix.mat) * 1\<^sub>m n = 1\<^sub>m n"
    by simp

  have "(1\<^sub>m n - P) * (1\<^sub>m n - P) = (1\<^sub>m n) * (1\<^sub>m n - P) - P * (1\<^sub>m n - P)"
    by (meson P_c minus_carrier_mat minus_mult_distrib_mat one_carrier_mat)
  also have "... = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * P) - (P * (1\<^sub>m n) - P * P)"
    by (metis P_c mult_minus_distrib_mat one_carrier_mat)
  also have "... = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * P) - (P * (1\<^sub>m n)) + P * P"
    using P_c by (simp add: algebra_simps, auto)
  also have "... = (1\<^sub>m n - P) - P + P * P"
    by (simp add: P_one_l P_one_r)
  also have "... = (1\<^sub>m n - P) - P + P"
    using P_idem by simp
  also have "... = 1\<^sub>m n - P"
    by auto
  finally show ?thesis.
qed


(* --------------------------------------------------------------------------
   Bonus: classical-code helpers extending Day 29.
   -------------------------------------------------------------------------- *)

lemma hamming_weight_append:
  "hamming_weight (xs @ ys) = hamming_weight xs + hamming_weight ys"
  by (simp add: hamming_weight_def)

lemma hamming_weight_repetition_encode:
  "hamming_weight (repetition_encode v) = 2 * hamming_weight v"
  by (simp add: repetition_encode_def hamming_weight_append)

lemma repetition_encode_binary:
  assumes "\<forall>x \<in> set v. x < 2"
  shows "\<forall>x \<in> set (repetition_encode v). x < 2"
  using assms by (auto simp: repetition_encode_def)


(* ============================================================================
   DAY 34 \<mdash> 18 / Nov / 11
   Topic: Algebra of Projections (Building Blocks for Knill-Laflamme)

   The standard algebraic facts about projections that underlie the
   orthogonal-syndrome / Knill-Laflamme construction.  The full
   Knill-Laflamme theorems remain deferred; they need eigenbasis
   decomposition machinery beyond the current scope.
   ============================================================================ *)

(* The complementary projection \<open>1 - P\<close> is itself a projection. *)

lemma projection_complement:
  assumes "projection n P"
  shows "projection n (1\<^sub>m n - P)"
proof -
  have P_c: "P \<in> carrier_mat n n" using assms by (rule projection_carrier)
  have P_h: "hermitian P" using assms by (rule projection_hermitian)
  have P_dag: "P\<^sup>\<dagger> = P" using P_h by (simp add: hermitian_def)
  have I_dag: "(1\<^sub>m n :: complex Matrix.mat)\<^sup>\<dagger> = 1\<^sub>m n"
    by (intro eq_matI) (auto simp: dagger_def)
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have IP_c: "(1\<^sub>m n - P) \<in> carrier_mat n n"
    using P_c by (rule minus_carrier_mat)
  have IP_dag: "(1\<^sub>m n - P)\<^sup>\<dagger> = 1\<^sub>m n - P"
  proof (rule eq_matI)
    show "dim_row ((1\<^sub>m n - P)\<^sup>\<dagger>) = dim_row (1\<^sub>m n - P)"
      using P_c by simp
    show "dim_col ((1\<^sub>m n - P)\<^sup>\<dagger>) = dim_col (1\<^sub>m n - P)"
      using P_c by simp
  next
    fix i j
    assume i: "i < dim_row (1\<^sub>m n - P)"
       and j: "j < dim_col (1\<^sub>m n - P)"
    hence ij: "i < n" "j < n" using P_c by simp_all
    have P_swap: "P $$ (j, i) = cnj (P $$ (i, j))"
    proof -
      have "(P\<^sup>\<dagger>) $$ (i, j) = cnj (P $$ (j, i))"
        using ij P_c by (simp add: dagger_def)
      hence "P $$ (i, j) = cnj (P $$ (j, i))"
        using P_dag by simp
      thus ?thesis by (simp add: complex_cnj_cnj)
    qed
    have one_entry_self_cnj:
      "(1\<^sub>m n :: complex Matrix.mat) $$ (j, i)
        = cnj ((1\<^sub>m n :: complex Matrix.mat) $$ (i, j))"
      using ij by auto
    show "((1\<^sub>m n - P)\<^sup>\<dagger>) $$ (i, j) = (1\<^sub>m n - P) $$ (i, j)"
      using ij P_c P_swap one_entry_self_cnj
      by (simp add: dagger_def index_minus_mat)
  qed
  have IP_h: "hermitian (1\<^sub>m n - P)" using IP_dag by (simp add: hermitian_def)
  have IP_idem: "(1\<^sub>m n - P) * (1\<^sub>m n - P) = 1\<^sub>m n - P"
    using assms by (rule projection_complement_idempotent)
  show ?thesis
    unfolding projection_def using IP_c IP_h IP_idem by blast
qed

(* Two projections are *orthogonal* if their product (in either order) is zero. *)

definition orthogonal_projections ::
  "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
  "orthogonal_projections n P Q \<equiv>
     projection n P \<and> projection n Q \<and>
     P * Q = 0\<^sub>m n n \<and> Q * P = 0\<^sub>m n n"

lemma orthogonal_projections_carrier_left:
  "orthogonal_projections n P Q \<Longrightarrow> P \<in> carrier_mat n n"
  by (simp add: orthogonal_projections_def projection_def)

lemma orthogonal_projections_carrier_right:
  "orthogonal_projections n P Q \<Longrightarrow> Q \<in> carrier_mat n n"
  by (simp add: orthogonal_projections_def projection_def)

lemma orthogonal_projections_symm:
  "orthogonal_projections n P Q \<longleftrightarrow> orthogonal_projections n Q P"
  by (auto simp: orthogonal_projections_def)

(* The sum of orthogonal projections is a projection. *)

lemma orthogonal_projections_sum:
  assumes opq: "orthogonal_projections n P Q"
  shows "projection n (P + Q)"
proof -
  have P_proj: "projection n P"
    using opq by (simp add: orthogonal_projections_def)
  have Q_proj: "projection n Q"
    using opq by (simp add: orthogonal_projections_def)
  have PQ_zero: "P * Q = 0\<^sub>m n n"
    using opq by (simp add: orthogonal_projections_def)
  have QP_zero: "Q * P = 0\<^sub>m n n"
    using opq by (simp add: orthogonal_projections_def)
  have P_c: "P \<in> carrier_mat n n" using P_proj by (rule projection_carrier)
  have Q_c: "Q \<in> carrier_mat n n" using Q_proj by (rule projection_carrier)
  have P_idem: "P * P = P" using P_proj by (rule projection_idempotent)
  have Q_idem: "Q * Q = Q" using Q_proj by (rule projection_idempotent)
  have P_h: "hermitian P" using P_proj by (rule projection_hermitian)
  have Q_h: "hermitian Q" using Q_proj by (rule projection_hermitian)
  have P_dag: "P\<^sup>\<dagger> = P" using P_h by (simp add: hermitian_def)
  have Q_dag: "Q\<^sup>\<dagger> = Q" using Q_h by (simp add: hermitian_def)

  have PQ_c: "P + Q \<in> carrier_mat n n" using P_c Q_c by simp

  have PQ_dag: "(P + Q)\<^sup>\<dagger> = P + Q"
  proof -
    have "(P + Q)\<^sup>\<dagger> = (P\<^sup>\<dagger>) + (Q\<^sup>\<dagger>)"
      using P_c Q_c
      by (intro eq_matI) (auto simp: dagger_def index_add_mat)
    also have "\<dots> = P + Q" using P_dag Q_dag by simp
    finally show ?thesis .
  qed
  have PQ_h: "hermitian (P + Q)" using PQ_dag by (simp add: hermitian_def)

  have PQ_idem: "(P + Q) * (P + Q) = P + Q"
  proof -
    have expand:
      "(P + Q) * (P + Q) = P * P + P * Q + (Q * P + Q * Q)"
      using P_c Q_c
      by (smt (verit) add_carrier_mat add_mult_distrib_mat
          mult_add_distrib_mat assoc_add_mat)
    have "P * P + P * Q + (Q * P + Q * Q)
            = P + 0\<^sub>m n n + (0\<^sub>m n n + Q)"
      using P_idem Q_idem PQ_zero QP_zero by simp
    also have "\<dots> = P + Q"
      using P_c Q_c by (intro eq_matI) auto
    finally show ?thesis using expand by simp
  qed
  show ?thesis unfolding projection_def using PQ_c PQ_h PQ_idem by blast
qed

(* Pythagorean decomposition: P + Q + (I - P - Q) = I when P, Q are
   orthogonal projections.  Building block for the Day-33 syndrome
   decomposition I = (sum P_i) + (I - sum P_i). *)

lemma orthogonal_projections_decomp_id:
  assumes "orthogonal_projections n P Q"
  shows "P + Q + (1\<^sub>m n - P - Q) = 1\<^sub>m n"
proof -
  have P_c: "P \<in> carrier_mat n n"
    using assms by (rule orthogonal_projections_carrier_left)
  have Q_c: "Q \<in> carrier_mat n n"
    using assms by (rule orthogonal_projections_carrier_right)
  show ?thesis using P_c Q_c by (intro eq_matI) auto
qed


(* ============================================================================
   DAY 35
   Topic: Rank-One Projections from Unit Vectors

   For a unit vector \<psi> \<in> \<complex>\<^sup>n, the operator |\<psi>\<rangle>\<langle>\<psi>| =
   outer_sum n [\<psi>] is a rank-one orthogonal projection: hermitian and
   idempotent (using \<langle>\<psi>|\<psi>\<rangle> = 1).
   ============================================================================ *)

lemma outer_sum_singleton_hermitian:
  fixes \<psi> :: "complex Matrix.vec"
  shows "(outer_sum n [\<psi>])\<^sup>\<dagger> = outer_sum n [\<psi>]"
proof (rule eq_matI)
  show "dim_row ((outer_sum n [\<psi>])\<^sup>\<dagger>) = dim_row (outer_sum n [\<psi>])"
    by simp
  show "dim_col ((outer_sum n [\<psi>])\<^sup>\<dagger>) = dim_col (outer_sum n [\<psi>])"
    by simp
next
  fix i j
  assume i: "i < dim_row (outer_sum n [\<psi>])"
     and j: "j < dim_col (outer_sum n [\<psi>])"
  hence ij: "i < n" "j < n" by simp_all
  have e1: "(outer_sum n [\<psi>])\<^sup>\<dagger> $$ (i, j)
              = cnj ((outer_sum n [\<psi>]) $$ (j, i))"
    using ij by (simp add: dagger_def)
  also have "\<dots> = cnj (\<psi> $ j * cnj (\<psi> $ i))"
    using outer_sum_singleton_index[OF ij(2) ij(1)] by simp
  also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j)"
    by (simp add: complex_cnj_cnj complex_cnj_mult mult.commute)
  also have "\<dots> = (outer_sum n [\<psi>]) $$ (i, j)"
    using outer_sum_singleton_index[OF ij(1) ij(2)] by simp
  finally show "(outer_sum n [\<psi>])\<^sup>\<dagger> $$ (i, j)
                  = (outer_sum n [\<psi>]) $$ (i, j)" .
qed

lemma outer_sum_singleton_idempotent:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "outer_sum n [\<psi>] * outer_sum n [\<psi>] = outer_sum n [\<psi>]"
proof -
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have norm1: "\<parallel>\<psi>\<parallel> = 1" using \<psi>_qs by (simp add: quantum_state_def)
  have inner_self: "\<langle>\<psi> | \<psi>\<rangle> = 1"
  proof -
    have "\<langle>\<psi> | \<psi>\<rangle> = complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2)"
      by (metis cpx_vec_length_inner_prod)
    also have "\<dots> = complex_of_real (1\<^sup>2)" using norm1 by simp
    also have "\<dots> = 1" by simp
    finally show ?thesis .
  qed
  let ?M = "outer_sum n [\<psi>]"
  have M_c: "?M \<in> carrier_mat n n" by auto
  show "?M * ?M = ?M"
  proof (rule eq_matI)
    show "dim_row (?M * ?M) = dim_row ?M" using M_c by simp
    show "dim_col (?M * ?M) = dim_col ?M" using M_c by simp
  next
    fix i j
    assume i: "i < dim_row ?M" and j: "j < dim_col ?M"
    hence ij: "i < n" "j < n" by simp_all
    have step1: "(?M * ?M) $$ (i, j)
                   = (\<Sum>k = 0..<n. ?M $$ (i, k) * ?M $$ (k, j))"
      using ij M_c
      by (simp add: scalar_prod_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>k = 0..<n.
                       \<psi> $ i * cnj (\<psi> $ k) * (\<psi> $ k * cnj (\<psi> $ j)))"
      using ij
      by (intro sum.cong refl)
         (simp add: outer_sum_singleton_index)
    also have "\<dots> = (\<Sum>k = 0..<n.
                      \<psi> $ i * cnj (\<psi> $ j) * (cnj (\<psi> $ k) * \<psi> $ k))"
      by (intro sum.cong refl) (simp add: ac_simps)
    also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j)
                    * (\<Sum>k = 0..<n. cnj (\<psi> $ k) * \<psi> $ k)"
      by (simp add: sum_distrib_left)
    also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j) * \<langle>\<psi> | \<psi>\<rangle>"
      using \<psi>_dim
      by (simp add: inner_prod_def lessThan_atLeast0)
    also have "\<dots> = \<psi> $ i * cnj (\<psi> $ j)"
      using inner_self by simp
    also have "\<dots> = ?M $$ (i, j)"
      using outer_sum_singleton_index[OF ij(1) ij(2)] by simp
    finally show "(?M * ?M) $$ (i, j) = ?M $$ (i, j)" .
  qed
qed

lemma rank1_projection:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "projection n (outer_sum n [\<psi>])"
proof -
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have c: "outer_sum n [\<psi>] \<in> carrier_mat n n" by auto
  have h: "hermitian (outer_sum n [\<psi>])"
    using outer_sum_singleton_hermitian
    by (simp add: hermitian_def)
  have idem: "outer_sum n [\<psi>] * outer_sum n [\<psi>] = outer_sum n [\<psi>]"
    using outer_sum_singleton_idempotent[OF \<psi>_qs] .
  show ?thesis unfolding projection_def using c h idem by blast
qed


(* ============================================================================
   DAY 36
   Topic: Trace of a Rank-One Projection; Projection Action on its Image

   Two concrete corollaries of the rank-one projection machinery:
     - The rank-1 projection |\<psi>\<rangle>\<langle>\<psi>| acts as the identity on \<psi>
       itself (the defining eigenvector property).
     - The trace of |\<psi>\<rangle>\<langle>\<psi>| equals \<langle>\<psi>|\<psi>\<rangle>, hence 1
       for a normalised state.
   ============================================================================ *)

lemma rank1_projection_acts_identity:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "outer_sum n [\<psi>] *\<^sub>v \<psi> = \<psi>"
proof -
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have norm1: "\<parallel>\<psi>\<parallel> = 1" using \<psi>_qs by (simp add: quantum_state_def)
  have inner_self: "\<langle>\<psi> | \<psi>\<rangle> = 1"
  proof -
    have "\<langle>\<psi> | \<psi>\<rangle> = complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2)"
      by (metis cpx_vec_length_inner_prod)
    also have "\<dots> = complex_of_real (1\<^sup>2)" using norm1 by simp
    also have "\<dots> = 1" by simp
    finally show ?thesis .
  qed
  have act: "outer_sum n [\<psi>] *\<^sub>v \<psi> = \<langle>\<psi> | \<psi>\<rangle> \<cdot>\<^sub>v \<psi>"
    using outer_sum_singleton_mult_vec[OF \<psi>_dim \<psi>_dim] .
  also have "\<dots> = (1 :: complex) \<cdot>\<^sub>v \<psi>" using inner_self by simp
  also have "\<dots> = \<psi>" by (intro eq_vecI) auto
  finally show ?thesis .
qed

lemma rank1_projection_trace_inner:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_dim: "dim_vec \<psi> = n"
  shows "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
proof -
  let ?M = "outer_sum n [\<psi>]"
  have M_c: "?M \<in> carrier_mat n n" by auto
  have "Tr ?M = (\<Sum>r < n. ?M $$ (r, r))"
    using M_c by (auto simp: Tr_def)
  also have "\<dots> = (\<Sum>r < n. \<psi> $ r * cnj (\<psi> $ r))"
    by (intro sum.cong refl) (simp add: outer_sum_singleton_index)
  also have "\<dots> = (\<Sum>r = 0..<n. cnj (\<psi> $ r) * \<psi> $ r)"
    by (intro sum.cong refl)
       (auto simp: atLeast0LessThan mult.commute)
  also have "\<dots> = \<langle>\<psi> | \<psi>\<rangle>"
    using \<psi>_dim by (simp add: inner_prod_def)
  finally show ?thesis .
qed

lemma rank1_projection_trace_one:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "Tr (outer_sum n [\<psi>]) = 1"
proof -
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have norm1: "\<parallel>\<psi>\<parallel> = 1" using \<psi>_qs by (simp add: quantum_state_def)
  have "Tr (outer_sum n [\<psi>]) = \<langle>\<psi> | \<psi>\<rangle>"
    using rank1_projection_trace_inner[OF \<psi>_dim] .
  also have "\<dots> = complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2)"
    by (metis cpx_vec_length_inner_prod)
  also have "\<dots> = complex_of_real (1\<^sup>2)" using norm1 by simp
  also have "\<dots> = 1" by simp
  finally show ?thesis .
qed


(* ============================================================================
   DAY 37
   Topic: Bit-Flip Channel Boundary Cases

   The bit-flip channel \<open>bit_flip_channel p\<close> at \<open>p = 0\<close> is the
   identity (no errors), and at \<open>p = 1\<close> is the X-conjugation channel
   (every qubit flipped).  Useful sanity checks and corner-case tools.
   ============================================================================ *)

lemma bit_flip_channel_zero:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "bit_flip_channel 0 \<rho> = \<rho>"
proof -
  have x_c: "pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c assms by (rule mult_carrier_mat)
  have x\<rho>xd_c: "pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)
  have one_smul: "(1 :: complex) \<cdot>\<^sub>m \<rho> = \<rho>"
    by (intro eq_matI) auto
  have zero_smul: "(0 :: complex) \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>))
                    = 0\<^sub>m 2 2"
    using x\<rho>xd_c by (intro eq_matI) auto
  have rho_zero: "\<rho> + 0\<^sub>m 2 2 = \<rho>"
    using assms by (intro eq_matI) auto
  have "bit_flip_channel 0 \<rho>
          = (1 :: complex) \<cdot>\<^sub>m \<rho>
            + (0 :: complex) \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>))"
    by (simp add: bit_flip_channel_def)
  also have "\<dots> = \<rho> + 0\<^sub>m 2 2"
    using one_smul zero_smul by simp
  also have "\<dots> = \<rho>" using rho_zero .
  finally show ?thesis .
qed

lemma bit_flip_channel_one:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "bit_flip_channel 1 \<rho> = pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)"
proof -
  have x_c: "pauli_X \<in> carrier_mat 2 2" by simp
  have xd_c: "pauli_X\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using x_c by (rule dagger_carrier)
  have x\<rho>_c: "pauli_X * \<rho> \<in> carrier_mat 2 2"
    using x_c assms by (rule mult_carrier_mat)
  have x\<rho>xd_c: "pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using x\<rho>_c xd_c by (rule mult_carrier_mat)
  have one_smul: "(1 :: complex) \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>))
                    = pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)"
    by (intro eq_matI) auto
  have zero_smul: "(0 :: complex) \<cdot>\<^sub>m \<rho> = 0\<^sub>m 2 2"
    using assms by (intro eq_matI) auto
  have zero_plus: "0\<^sub>m 2 2 + pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)
                    = pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)"
    using x\<rho>xd_c by (intro eq_matI) auto
  have "bit_flip_channel 1 \<rho>
          = (0 :: complex) \<cdot>\<^sub>m \<rho>
            + (1 :: complex) \<cdot>\<^sub>m (pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>))"
    by (simp add: bit_flip_channel_def)
  also have "\<dots> = 0\<^sub>m 2 2 + pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)"
    using zero_smul one_smul by simp
  also have "\<dots> = pauli_X * \<rho> * (pauli_X\<^sup>\<dagger>)"
    using zero_plus .
  finally show ?thesis .
qed


(* ============================================================================
   DAY 38
   Topic: Phase-Flip Channel

   The phase-flip channel applies Pauli-Z with probability \<open>p\<close>:
   \<open>phase_flip_channel p \<rho> = (1-p) \<sqdot> \<rho> + p \<sqdot> Z \<rho> Z\<^sup>\<dagger>\<close>.
   It is the Z-analogue of \<open>bit_flip_channel\<close>; the same proof skeleton
   gives carrier preservation, trace preservation and PSD preservation.
   ============================================================================ *)

definition phase_flip_channel ::
  "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "phase_flip_channel p \<rho> \<equiv>
     complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
     + complex_of_real p \<cdot>\<^sub>m (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>))"

lemma phase_flip_channel_carrier:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "phase_flip_channel p \<rho> \<in> carrier_mat 2 2"
proof -
  have z_c: "pauli_Z \<in> carrier_mat 2 2" by simp
  have zd_c: "pauli_Z\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using z_c by (rule dagger_carrier)
  have z\<rho>_c: "pauli_Z * \<rho> \<in> carrier_mat 2 2"
    using z_c assms by (rule mult_carrier_mat)
  have z\<rho>zd_c: "pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using z\<rho>_c zd_c by (rule mult_carrier_mat)
  show ?thesis
    using assms z\<rho>zd_c by (auto simp: phase_flip_channel_def)
qed

lemma phase_flip_channel_trace_preserving:
  fixes p :: real
  assumes \<rho>_c: "\<rho> \<in> carrier_mat 2 2"
  shows "Tr (phase_flip_channel p \<rho>) = Tr \<rho>"
proof -
  have z_c: "pauli_Z \<in> carrier_mat 2 2" by simp
  have zd_c: "pauli_Z\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using z_c by (rule dagger_carrier)
  have z\<rho>_c: "pauli_Z * \<rho> \<in> carrier_mat 2 2"
    using z_c \<rho>_c by (rule mult_carrier_mat)
  have z\<rho>zd_c: "pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using z\<rho>_c zd_c by (rule mult_carrier_mat)
  have zdz_eq: "(pauli_Z\<^sup>\<dagger>) * pauli_Z = 1\<^sub>m 2"
    using pauli_Z_dagger pauli_Z_squared by simp

  have tr_conj: "Tr (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>)) = Tr \<rho>"
  proof -
    have "Tr (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>)) = Tr (pauli_Z\<^sup>\<dagger> * (pauli_Z * \<rho>))"
    proof (rule Tr_cyclic)
      show "dim_col (pauli_Z * \<rho>) = dim_row (pauli_Z\<^sup>\<dagger>)"
        using z\<rho>_c zd_c by (metis carrier_matD)
      show "dim_row (pauli_Z * \<rho>) = dim_col (pauli_Z\<^sup>\<dagger>)"
        using z\<rho>_c zd_c by (metis carrier_matD)
    qed
    also have "\<dots> = Tr ((pauli_Z\<^sup>\<dagger> * pauli_Z) * \<rho>)"
      by (metis zd_c z_c \<rho>_c assoc_mult_mat)
    also have "\<dots> = Tr ((1\<^sub>m 2) * \<rho>)" using zdz_eq by simp
    also have "\<dots> = Tr \<rho>" using \<rho>_c by simp
    finally show ?thesis .
  qed

  have row_eq: "dim_row (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_row (complex_of_real p
                              \<cdot>\<^sub>m (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>)))"
    using \<rho>_c z\<rho>zd_c by (metis carrier_matD index_smult_mat)
  have col_eq: "dim_col (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_col (complex_of_real p
                              \<cdot>\<^sub>m (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>)))"
    using \<rho>_c z\<rho>zd_c by (metis carrier_matD index_smult_mat)
  have "Tr (phase_flip_channel p \<rho>)
          = Tr (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
            + Tr (complex_of_real p \<cdot>\<^sub>m (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>)))"
    unfolding phase_flip_channel_def
    using row_eq col_eq by (rule Tr_add)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>))"
    by (simp add: Tr_smult)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr \<rho>"
    using tr_conj by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) * Tr \<rho>"
    by (simp add: ring_distribs)
  also have "\<dots> = 1 * Tr \<rho>" by simp
  also have "\<dots> = Tr \<rho>" by simp
  finally show ?thesis .
qed

lemma phase_flip_channel_psd:
  fixes p :: real
  assumes p_nn:    "0 \<le> p"
      and p_le_1:  "p \<le> 1"
      and \<rho>_c:    "\<rho> \<in> carrier_mat 2 2"
      and \<rho>_psd:  "psd \<rho>"
  shows "psd (phase_flip_channel p \<rho>)"
proof -
  have z_c: "pauli_Z \<in> carrier_mat 2 2" by simp
  have zd_c: "pauli_Z\<^sup>\<dagger> \<in> carrier_mat 2 2"
    using z_c by (rule dagger_carrier)
  have z\<rho>_c: "pauli_Z * \<rho> \<in> carrier_mat 2 2"
    using z_c \<rho>_c by (rule mult_carrier_mat)
  have z\<rho>zd_c: "pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>) \<in> carrier_mat 2 2"
    using z\<rho>_c zd_c by (rule mult_carrier_mat)
  have one_minus_nn: "0 \<le> 1 - p" using p_le_1 by simp

  have conj_psd: "psd (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>))"
  proof -
    obtain Q where Q_c:    "Q \<in> carrier_mat 2 2"
               and Q_psd:  "psd Q"
               and Q_sq:   "Q * Q = \<rho>"
      using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
    have Q_dagger: "Q\<^sup>\<dagger> = Q"
      using Q_psd by (simp add: psd_def hermitian_def)
    have ZQ_c: "pauli_Z * Q \<in> carrier_mat 2 2"
      using z_c Q_c by (rule mult_carrier_mat)
    have ZQd_c: "(pauli_Z * Q)\<^sup>\<dagger> \<in> carrier_mat 2 2"
      using ZQ_c by (rule dagger_carrier)
    have eq: "pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>) = (pauli_Z * Q) * ((pauli_Z * Q)\<^sup>\<dagger>)"
    proof -
      have dim_eq: "dim_col pauli_Z = dim_row Q"
        using z_c Q_c by (metis carrier_matD)
      have dagprod: "(pauli_Z * Q)\<^sup>\<dagger> = (Q\<^sup>\<dagger>) * (pauli_Z\<^sup>\<dagger>)"
        using dim_eq by (rule dagger_of_prod)
      hence dagprod': "(pauli_Z * Q)\<^sup>\<dagger> = Q * (pauli_Z\<^sup>\<dagger>)"
        using Q_dagger by simp
      have "(pauli_Z * Q) * ((pauli_Z * Q)\<^sup>\<dagger>)
              = (pauli_Z * Q) * (Q * (pauli_Z\<^sup>\<dagger>))"
        using dagprod' by simp
      also have "\<dots> = pauli_Z * Q * Q * (pauli_Z\<^sup>\<dagger>)"
        using z_c Q_c zd_c by (metis assoc_mult_mat mult_carrier_mat)
      also have "\<dots> = pauli_Z * (Q * Q) * (pauli_Z\<^sup>\<dagger>)"
        using z_c Q_c by (metis assoc_mult_mat)
      also have "\<dots> = pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>)"
        using Q_sq by simp
      finally show ?thesis by simp
    qed
    have psd_dd: "psd (((pauli_Z * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((pauli_Z * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF ZQd_c] .
    have dd_eq: "(pauli_Z * Q)\<^sup>\<dagger>\<^sup>\<dagger> = pauli_Z * Q"
      using ZQ_c by (simp add: dagger_of_dagger_is_id)
    have "psd ((pauli_Z * Q) * ((pauli_Z * Q)\<^sup>\<dagger>))"
      using psd_dd dd_eq by simp
    thus ?thesis using eq by simp
  qed

  have term1_psd: "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)"
    using one_minus_nn \<rho>_psd \<rho>_c by (rule psd_smult_nonneg)
  have term2_psd: "psd (complex_of_real p \<cdot>\<^sub>m (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>)))"
    using p_nn conj_psd z\<rho>zd_c by (rule psd_smult_nonneg)

  have term1_c: "complex_of_real (1 - p) \<cdot>\<^sub>m \<rho> \<in> carrier_mat 2 2"
    using \<rho>_c by simp
  have term2_c: "complex_of_real p \<cdot>\<^sub>m (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>))
                   \<in> carrier_mat 2 2"
    using z\<rho>zd_c by simp

  have "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
              + complex_of_real p \<cdot>\<^sub>m (pauli_Z * \<rho> * (pauli_Z\<^sup>\<dagger>)))"
    using term1_psd term2_psd term1_c term2_c by (rule psd_add_psd)
  thus ?thesis by (simp add: phase_flip_channel_def)
qed


(* ============================================================================
   DAY 39
   Topic: General Unitary-Conjugation Channel

   Abstract the bit-flip / phase-flip pattern: for a unitary \<open>U \<in> M\<^sub>n\<close>,
   the channel \<open>\<rho> \<mapsto> (1-p) \<sqdot> \<rho> + p \<sqdot> U \<rho> U\<^sup>\<dagger>\<close> is
   trace-preserving and PSD-preserving for \<open>0 \<le> p \<le> 1\<close>.
   The bit-flip and phase-flip channels are immediate instances.
   ============================================================================ *)

definition unitary_conj_channel ::
  "complex Matrix.mat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "unitary_conj_channel U p \<rho> \<equiv>
     complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
     + complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>))"

lemma unitary_conj_channel_carrier:
  assumes U_c: "U \<in> carrier_mat n n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "unitary_conj_channel U p \<rho> \<in> carrier_mat n n"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have U\<rho>_c: "U * \<rho> \<in> carrier_mat n n"
    using U_c \<rho>_c by (rule mult_carrier_mat)
  have U\<rho>Ud_c: "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  show ?thesis
    using \<rho>_c U\<rho>Ud_c by (auto simp: unitary_conj_channel_def)
qed

lemma unitary_conj_channel_trace_preserving:
  fixes p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "Tr (unitary_conj_channel U p \<rho>) = Tr \<rho>"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have U\<rho>_c: "U * \<rho> \<in> carrier_mat n n"
    using U_c \<rho>_c by (rule mult_carrier_mat)
  have U\<rho>Ud_c: "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  have UdU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n"
    using U_unit U_c by (auto simp: unitary_def)

  have tr_conj: "Tr (U * \<rho> * (U\<^sup>\<dagger>)) = Tr \<rho>"
  proof -
    have "Tr (U * \<rho> * (U\<^sup>\<dagger>)) = Tr (U\<^sup>\<dagger> * (U * \<rho>))"
    proof (rule Tr_cyclic)
      show "dim_col (U * \<rho>) = dim_row (U\<^sup>\<dagger>)"
        using U\<rho>_c Ud_c by (metis carrier_matD)
      show "dim_row (U * \<rho>) = dim_col (U\<^sup>\<dagger>)"
        using U\<rho>_c Ud_c by (metis carrier_matD)
    qed
    also have "\<dots> = Tr ((U\<^sup>\<dagger> * U) * \<rho>)"
      by (metis Ud_c U_c \<rho>_c assoc_mult_mat)
    also have "\<dots> = Tr ((1\<^sub>m n) * \<rho>)" using UdU by simp
    also have "\<dots> = Tr \<rho>" using \<rho>_c by simp
    finally show ?thesis .
  qed

  have row_eq: "dim_row (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_row (complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    using \<rho>_c U\<rho>Ud_c by (metis carrier_matD index_smult_mat)
  have col_eq: "dim_col (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
                  = dim_col (complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    using \<rho>_c U\<rho>Ud_c by (metis carrier_matD index_smult_mat)
  have "Tr (unitary_conj_channel U p \<rho>)
          = Tr (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)
            + Tr (complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    unfolding unitary_conj_channel_def
    using row_eq col_eq by (rule Tr_add)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr (U * \<rho> * (U\<^sup>\<dagger>))"
    by (simp add: Tr_smult)
  also have "\<dots> = complex_of_real (1 - p) * Tr \<rho>
                  + complex_of_real p * Tr \<rho>"
    using tr_conj by simp
  also have "\<dots> = (complex_of_real (1 - p) + complex_of_real p) * Tr \<rho>"
    by (simp add: ring_distribs)
  also have "\<dots> = 1 * Tr \<rho>" by simp
  also have "\<dots> = Tr \<rho>" by simp
  finally show ?thesis .
qed

lemma unitary_conj_channel_psd:
  fixes p :: real
  assumes p_nn:    "0 \<le> p"
      and p_le_1:  "p \<le> 1"
      and U_c:    "U \<in> carrier_mat n n"
      and \<rho>_c:    "\<rho> \<in> carrier_mat n n"
      and \<rho>_psd:  "psd \<rho>"
  shows "psd (unitary_conj_channel U p \<rho>)"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have U\<rho>_c: "U * \<rho> \<in> carrier_mat n n"
    using U_c \<rho>_c by (rule mult_carrier_mat)
  have U\<rho>Ud_c: "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
    using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  have one_minus_nn: "0 \<le> 1 - p" using p_le_1 by simp

  have conj_psd: "psd (U * \<rho> * (U\<^sup>\<dagger>))"
  proof -
    obtain Q where Q_c:    "Q \<in> carrier_mat n n"
               and Q_psd:  "psd Q"
               and Q_sq:   "Q * Q = \<rho>"
      using psd_sqrt_exists[OF \<rho>_c \<rho>_psd] by blast
    have Q_dagger: "Q\<^sup>\<dagger> = Q"
      using Q_psd by (simp add: psd_def hermitian_def)
    have UQ_c: "U * Q \<in> carrier_mat n n"
      using U_c Q_c by (rule mult_carrier_mat)
    have UQd_c: "(U * Q)\<^sup>\<dagger> \<in> carrier_mat n n"
      using UQ_c by (rule dagger_carrier)
    have eq: "U * \<rho> * (U\<^sup>\<dagger>) = (U * Q) * ((U * Q)\<^sup>\<dagger>)"
    proof -
      have dim_eq: "dim_col U = dim_row Q"
        using U_c Q_c by (metis carrier_matD)
      have dagprod: "(U * Q)\<^sup>\<dagger> = (Q\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
        using dim_eq by (rule dagger_of_prod)
      hence dagprod': "(U * Q)\<^sup>\<dagger> = Q * (U\<^sup>\<dagger>)"
        using Q_dagger by simp
      have "(U * Q) * ((U * Q)\<^sup>\<dagger>) = (U * Q) * (Q * (U\<^sup>\<dagger>))"
        using dagprod' by simp
      also have "\<dots> = U * Q * Q * (U\<^sup>\<dagger>)"
        using U_c Q_c Ud_c by (metis assoc_mult_mat mult_carrier_mat)
      also have "\<dots> = U * (Q * Q) * (U\<^sup>\<dagger>)"
        using U_c Q_c by (metis assoc_mult_mat)
      also have "\<dots> = U * \<rho> * (U\<^sup>\<dagger>)" using Q_sq by simp
      finally show ?thesis by simp
    qed
    have psd_dd: "psd (((U * Q)\<^sup>\<dagger>\<^sup>\<dagger>) * ((U * Q)\<^sup>\<dagger>))"
      using psd_MdagM[OF UQd_c] .
    have dd_eq: "(U * Q)\<^sup>\<dagger>\<^sup>\<dagger> = U * Q"
      using UQ_c by (simp add: dagger_of_dagger_is_id)
    have "psd ((U * Q) * ((U * Q)\<^sup>\<dagger>))"
      using psd_dd dd_eq by simp
    thus ?thesis using eq by simp
  qed

  have term1_psd: "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>)"
    using one_minus_nn \<rho>_psd \<rho>_c by (rule psd_smult_nonneg)
  have term2_psd: "psd (complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    using p_nn conj_psd U\<rho>Ud_c by (rule psd_smult_nonneg)
  have term1_c: "complex_of_real (1 - p) \<cdot>\<^sub>m \<rho> \<in> carrier_mat n n"
    using \<rho>_c by simp
  have term2_c: "complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)) \<in> carrier_mat n n"
    using U\<rho>Ud_c by simp
  have "psd (complex_of_real (1 - p) \<cdot>\<^sub>m \<rho>
              + complex_of_real p \<cdot>\<^sub>m (U * \<rho> * (U\<^sup>\<dagger>)))"
    using term1_psd term2_psd term1_c term2_c by (rule psd_add_psd)
  thus ?thesis by (simp add: unitary_conj_channel_def)
qed

(* The bit-flip and phase-flip channels are instances of the unitary-
   conjugation channel for the Pauli matrices X and Z. *)

lemma bit_flip_eq_unitary_conj:
  "bit_flip_channel p \<rho> = unitary_conj_channel pauli_X p \<rho>"
  by (simp add: bit_flip_channel_def unitary_conj_channel_def)

lemma phase_flip_eq_unitary_conj:
  "phase_flip_channel p \<rho> = unitary_conj_channel pauli_Z p \<rho>"
  by (simp add: phase_flip_channel_def unitary_conj_channel_def)


(* ============================================================================
   DAY 40
   Topic: Bit-Phase-Flip (Y) Channel; Identity Channel

   Two further channels assembled from the unitary-conjugation
   framework of Day 39:
     - The bit-phase-flip channel applies Pauli-Y with probability p.
     - The identity channel is the unitary-conjugation channel with
       p = 0 (or with U = I), trivially CPTP.
   ============================================================================ *)

definition bit_phase_flip_channel ::
  "real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "bit_phase_flip_channel p \<rho> \<equiv> unitary_conj_channel pauli_Y p \<rho>"

lemma bit_phase_flip_channel_carrier:
  assumes "\<rho> \<in> carrier_mat 2 2"
  shows "bit_phase_flip_channel p \<rho> \<in> carrier_mat 2 2"
  unfolding bit_phase_flip_channel_def
  using pauli_Y_carrier assms
  by (rule unitary_conj_channel_carrier)

lemma bit_phase_flip_channel_trace_preserving:
  fixes p :: real
  assumes \<rho>_c: "\<rho> \<in> carrier_mat 2 2"
  shows "Tr (bit_phase_flip_channel p \<rho>) = Tr \<rho>"
  unfolding bit_phase_flip_channel_def
  using pauli_Y_carrier pauli_Y_unitary \<rho>_c
  by (rule unitary_conj_channel_trace_preserving)

lemma bit_phase_flip_channel_psd:
  fixes p :: real
  assumes p_nn:    "0 \<le> p"
      and p_le_1:  "p \<le> 1"
      and \<rho>_c:    "\<rho> \<in> carrier_mat 2 2"
      and \<rho>_psd:  "psd \<rho>"
  shows "psd (bit_phase_flip_channel p \<rho>)"
  unfolding bit_phase_flip_channel_def
  using p_nn p_le_1 pauli_Y_carrier \<rho>_c \<rho>_psd
  by (rule unitary_conj_channel_psd)


(* The identity channel is CPTP: trace and PSD preserved trivially. *)

definition identity_channel ::
  "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "identity_channel \<rho> \<equiv> \<rho>"

lemma identity_channel_carrier:
  "\<rho> \<in> carrier_mat n n \<Longrightarrow> identity_channel \<rho> \<in> carrier_mat n n"
  by (simp add: identity_channel_def)

lemma identity_channel_trace_preserving:
  "\<rho> \<in> carrier_mat n n \<Longrightarrow> Tr (identity_channel \<rho>) = Tr \<rho>"
  by (simp add: identity_channel_def)

lemma identity_channel_psd:
  "\<rho> \<in> carrier_mat n n \<Longrightarrow> psd \<rho> \<Longrightarrow> psd (identity_channel \<rho>)"
  by (simp add: identity_channel_def)

(* The identity channel is the unitary-conjugation channel with p = 0
   (any U works, but the natural choice is U = 1\<^sub>m n). *)

lemma identity_channel_eq_unitary_conj_zero:
  assumes \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "identity_channel \<rho> = unitary_conj_channel (1\<^sub>m n) 0 \<rho>"
proof -
  have I_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
  have Id_c: "(1\<^sub>m n :: complex Matrix.mat)\<^sup>\<dagger> \<in> carrier_mat n n"
    using I_c by (rule dagger_carrier)
  have I\<rho>_c: "(1\<^sub>m n :: complex Matrix.mat) * \<rho> \<in> carrier_mat n n"
    using I_c \<rho>_c by (rule mult_carrier_mat)
  have I\<rho>Id_c: "(1\<^sub>m n :: complex Matrix.mat) * \<rho> * ((1\<^sub>m n)\<^sup>\<dagger>)
                  \<in> carrier_mat n n"
    using I\<rho>_c Id_c by (rule mult_carrier_mat)
  have one_smul: "(1 :: complex) \<cdot>\<^sub>m \<rho> = \<rho>"
    using \<rho>_c by (intro eq_matI) auto
  have zero_smul: "(0 :: complex) \<cdot>\<^sub>m
                     ((1\<^sub>m n :: complex Matrix.mat) * \<rho>
                      * ((1\<^sub>m n)\<^sup>\<dagger>))
                    = 0\<^sub>m n n"
    using I\<rho>Id_c by (intro eq_matI) auto
  have rho_zero: "\<rho> + 0\<^sub>m n n = \<rho>"
    using \<rho>_c by (intro eq_matI) auto
  have "unitary_conj_channel (1\<^sub>m n) 0 \<rho>
          = (1 :: complex) \<cdot>\<^sub>m \<rho>
            + (0 :: complex) \<cdot>\<^sub>m
                ((1\<^sub>m n :: complex Matrix.mat) * \<rho> * ((1\<^sub>m n)\<^sup>\<dagger>))"
    by (simp add: unitary_conj_channel_def)
  also have "\<dots> = \<rho> + 0\<^sub>m n n" using one_smul zero_smul by simp
  also have "\<dots> = \<rho>" using rho_zero .
  finally show ?thesis by (simp add: identity_channel_def)
qed


(* ============================================================================
   DAY 41
   Topic: Channel Composition

   The composition \<open>G \<circ> F\<close> of two trace-preserving maps is again
   trace-preserving (subject to carrier-preservation of \<open>F\<close>).  The
   identity channel is a left and right unit for composition.
   ============================================================================ *)

lemma compose_trace_preserving:
  assumes F_tp:    "trace_preserving n F"
      and G_tp:    "trace_preserving n G"
      and F_range: "\<forall>\<rho>. \<rho> \<in> carrier_mat n n \<longrightarrow> F \<rho> \<in> carrier_mat n n"
  shows "trace_preserving n (\<lambda>\<rho>. G (F \<rho>))"
proof (unfold trace_preserving_def, intro allI impI)
  fix \<rho> :: "complex Matrix.mat"
  assume \<rho>_c: "\<rho> \<in> carrier_mat n n"
  have F\<rho>_c: "F \<rho> \<in> carrier_mat n n" using F_range \<rho>_c by blast
  have "Tr (G (F \<rho>)) = Tr (F \<rho>)"
    using G_tp F\<rho>_c by (simp add: trace_preserving_def)
  also have "\<dots> = Tr \<rho>"
    using F_tp \<rho>_c by (simp add: trace_preserving_def)
  finally show "Tr (G (F \<rho>)) = Tr \<rho>" .
qed

(* The identity channel is a unit for composition. *)

lemma identity_channel_compose_left:
  "(\<lambda>\<rho>. identity_channel (F \<rho>)) = F"
  by (simp add: identity_channel_def)

lemma identity_channel_compose_right:
  "(\<lambda>\<rho>. F (identity_channel \<rho>)) = F"
  by (simp add: identity_channel_def)


(* ============================================================================
   DAY 42
   Topic: More composition properties; unital composition

   Building further on Day 41: unital channel composition, and the
   identity-channel preservation properties.
   ============================================================================ *)

lemma compose_unital_map:
  assumes F_un: "unital_map n n F"
      and G_un: "unital_map n n G"
  shows "unital_map n n (\<lambda>\<rho>. F (G \<rho>))"
proof -
  have G_one: "G (1\<^sub>m n) = 1\<^sub>m n"
    using G_un by (simp add: unital_map_def)
  have F_one: "F (1\<^sub>m n) = 1\<^sub>m n"
    using F_un by (simp add: unital_map_def)
  have "F (G (1\<^sub>m n)) = F (1\<^sub>m n)" using G_one by simp
  also have "\<dots> = 1\<^sub>m n" using F_one by simp
  finally show ?thesis by (simp add: unital_map_def)
qed

(* identity_channel is unital and trace-preserving. *)

lemma identity_channel_unital: "unital_map n n identity_channel"
  by (simp add: unital_map_def identity_channel_def)

lemma identity_channel_trace_preserving_full:
  "trace_preserving n identity_channel"
  by (simp add: trace_preserving_def identity_channel_def)

(* identity_channel is a UCP / CPTP map (taking its CP property as
   self-evident from \<rho> \<mapsto> \<rho> being completely positive). *)

lemma identity_channel_completely_positive:
  assumes "0 < n"
  shows "completely_positive n n identity_channel"
proof -
  have amp_eq:
    "\<And>p X. 0 < p \<Longrightarrow> X \<in> carrier_mat (p*n) (p*n)
      \<Longrightarrow> amplification n n p identity_channel X = X"
  proof -
    fix p :: nat and X :: "complex Matrix.mat"
    assume p_pos: "0 < p" and X_c: "X \<in> carrier_mat (p*n) (p*n)"
    show "amplification n n p identity_channel X = X"
    proof (rule eq_matI)
      show "dim_row (amplification n n p identity_channel X) = dim_row X"
        using X_c by (simp add: amplification_def)
      show "dim_col (amplification n n p identity_channel X) = dim_col X"
        using X_c by (simp add: amplification_def)
    next
      fix i j
      assume i: "i < dim_row X" and j: "j < dim_col X"
      hence ij: "i < p*n" "j < p*n" using X_c by simp_all
      have imodn: "i mod n < n" and jmodn: "j mod n < n"
        using assms by simp_all
      have iqn: "i div n < p" using ij(1) assms
        by (simp add: less_mult_imp_div_less)
      have jqn: "j div n < p" using ij(2) assms
        by (simp add: less_mult_imp_div_less)
      have idn: "i div n * n + i mod n = i" by simp
      have jdn: "j div n * n + j mod n = j" by simp
      have block_idx:
        "block_of_mat n X (i div n) (j div n) $$ (i mod n, j mod n)
         = X $$ (i, j)"
        using imodn jmodn iqn jqn ij X_c
        by (simp add: block_of_mat_def idn jdn)
      show "amplification n n p identity_channel X $$ (i, j)
              = X $$ (i, j)"
        using ij block_idx
        by (simp add: amplification_def identity_channel_def)
    qed
  qed
  show ?thesis
    unfolding completely_positive_def p_positive_def
    using amp_eq by auto
qed


(* ============================================================================
   DAY 43
   Topic: Kraus-map CP (without TP); unitary conjugation is CP

   Extract a Kraus-map CP lemma without the trace-preserving condition
   that \<open>kraus_is_cp\<close> imposes via \<open>kraus_operators\<close>.  Use it to give
   single-Kraus-operator (\<rho> \<mapsto> U \<rho> U^dagger) CP, and assemble
   identity_channel CPTP / UCP membership.
   ============================================================================ *)

lemma kraus_map_dim_is_cp:
  fixes Ws :: "complex Matrix.mat list"
  assumes Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (kraus_map_dim d Ws)"
proof (unfold completely_positive_def p_positive_def, intro allI impI)
  fix p :: nat and X :: "complex Matrix.mat"
  assume ppos: "0 < p"
     and X_c: "X \<in> carrier_mat (p*n) (p*n)"
     and X_psd: "psd X"
  have lifted_c:
    "\<forall>L \<in> set (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws). L \<in> carrier_mat (p*d) (p*n)"
    using tensor_id_kraus_list_carrier[OF Ws_c] .
  have amp_eq:
    "amplification n d p (kraus_map_dim d Ws) X
       = kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) X"
    using amplification_kraus_map_dim[OF Ws_c X_c dpos npos] .
  have psd_kr:
    "psd (kraus_map_dim (p*d) (map (\<lambda>W. 1\<^sub>m p \<Otimes> W) Ws) X)"
    using kraus_map_dim_psd[OF lifted_c X_c X_psd] .
  show "psd (amplification n d p (kraus_map_dim d Ws) X)"
    using amp_eq psd_kr by simp
qed


(* Single-operator conjugation \<rho> \<mapsto> U \<rho> U^dagger is CP. *)

definition conjugation_channel ::
  "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "conjugation_channel U \<rho> \<equiv> U * \<rho> * (U\<^sup>\<dagger>)"

lemma conjugation_channel_eq_kraus:
  assumes U_c: "U \<in> carrier_mat d n"
      and \<rho>_c: "\<rho> \<in> carrier_mat n n"
  shows "conjugation_channel U \<rho> = kraus_map_dim d [U] \<rho>"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n d"
    using U_c by (rule dagger_carrier)
  have U\<rho>_c: "U * \<rho> \<in> carrier_mat d n"
    using U_c \<rho>_c by (rule mult_carrier_mat)
  have U\<rho>Ud_c: "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat d d"
    using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  have add_zero: "U * \<rho> * (U\<^sup>\<dagger>) + 0\<^sub>m d d = U * \<rho> * (U\<^sup>\<dagger>)"
    using U\<rho>Ud_c by (intro eq_matI) auto
  show ?thesis
    unfolding conjugation_channel_def
    by (simp add: add_zero)
qed

lemma conjugation_channel_cp:
  assumes U_c: "U \<in> carrier_mat d n"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (kraus_map_dim d [U])"
proof -
  have Ws_c: "\<forall>W \<in> set [U]. W \<in> carrier_mat d n" using U_c by simp
  show ?thesis using kraus_map_dim_is_cp[OF Ws_c npos dpos] .
qed


(* identity_channel is CPTP / UCP. *)

lemma identity_channel_UCP:
  assumes "0 < n"
  shows "identity_channel \<in> UCP n n"
  unfolding UCP_def
  using identity_channel_completely_positive[OF assms]
        identity_channel_unital
  by simp

lemma identity_channel_CPTP:
  assumes "0 < n"
  shows "identity_channel \<in> CPTP n n"
  unfolding CPTP_def
  using identity_channel_completely_positive[OF assms]
        identity_channel_trace_preserving_full
  by simp


(* ============================================================================
   DAY 44
   Topic: Pure conjugation \<rho> \<mapsto> U \<rho> U^dagger is a CPTP map

   We package the single-Kraus-operator conjugation channel as an
   actual function and show it is CP and (for unitary U) trace-
   preserving and unital.  This gives us a clean witness that the
   building blocks of \<open>unitary_conj_channel\<close> are CPTP.
   ============================================================================ *)

(* The conjugation channel \<rho> \<mapsto> U \<rho> U^dagger is CP. *)

lemma map_conj_cp:
  assumes U_c: "U \<in> carrier_mat d n"
      and U_range: "\<forall>\<rho>. \<rho> \<in> carrier_mat n n
                       \<longrightarrow> U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat d d"
      and npos: "0 < n"
      and dpos: "0 < d"
  shows "completely_positive n d (\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>))"
proof -
  have Ws_c: "\<forall>W \<in> set [U]. W \<in> carrier_mat d n" using U_c by simp
  let ?F = "\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)"
  let ?G = "kraus_map_dim d [U]"
  have agree:
    "\<And>\<rho>. \<rho> \<in> carrier_mat n n \<Longrightarrow> ?F \<rho> = ?G \<rho>"
    using conjugation_channel_eq_kraus[OF U_c]
    by (simp add: conjugation_channel_def)
  have G_cp: "completely_positive n d ?G"
    using kraus_map_dim_is_cp[OF Ws_c npos dpos] .
  show ?thesis
  proof (unfold completely_positive_def p_positive_def, intro allI impI)
    fix p :: nat and X :: "complex Matrix.mat"
    assume ppos: "0 < p" and X_c: "X \<in> carrier_mat (p*n) (p*n)"
       and X_psd: "psd X"
    have amp_eq:
      "amplification n d p ?F X = amplification n d p ?G X"
    proof (rule eq_matI)
      show "dim_row (amplification n d p ?F X)
              = dim_row (amplification n d p ?G X)"
        by (simp add: amplification_def)
      show "dim_col (amplification n d p ?F X)
              = dim_col (amplification n d p ?G X)"
        by (simp add: amplification_def)
    next
      fix i j
      assume "i < dim_row (amplification n d p ?G X)"
             "j < dim_col (amplification n d p ?G X)"
      hence ij: "i < p*d" "j < p*d"
        by (simp_all add: amplification_def)
      have B_c: "block_of_mat n X (i div d) (j div d) \<in> carrier_mat n n"
        by (simp add: block_of_mat_def)
      have eq: "?F (block_of_mat n X (i div d) (j div d))
                = ?G (block_of_mat n X (i div d) (j div d))"
        using agree[OF B_c] .
      show "amplification n d p ?F X $$ (i, j)
              = amplification n d p ?G X $$ (i, j)"
        using ij eq by (simp add: amplification_def)
    qed
    have psd_G: "psd (amplification n d p ?G X)"
      using G_cp ppos X_c X_psd
      by (auto simp: completely_positive_def p_positive_def)
    show "psd (amplification n d p ?F X)"
      using amp_eq psd_G by simp
  qed
qed

(* For unitary U, conjugation is unital and trace-preserving. *)

lemma map_conj_unital:
  fixes U :: "complex Matrix.mat"
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
  shows "U * (1\<^sub>m n) * (U\<^sup>\<dagger>) = 1\<^sub>m n"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have UI: "U * (1\<^sub>m n) = U" using U_c by simp
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using U_unit U_c by (auto simp: unitary_def)
  have "U * (1\<^sub>m n) * (U\<^sup>\<dagger>) = U * (U\<^sup>\<dagger>)" using UI by simp
  also have "\<dots> = 1\<^sub>m n" using UUd .
  finally show ?thesis .
qed


(* ============================================================================
   DAY 45
   Topic: Unitary conjugation belongs to UCP; unitary_conj_channel in UCP

   Combine \<open>map_conj_cp\<close> (CP) and \<open>map_conj_unital\<close>
   (unitality) to put unitary conjugation in UCP n n, then apply
   UCP_convex to put \<open>unitary_conj_channel U p\<close> in UCP for any
   p \<in> [0,1] and unitary U.
   ============================================================================ *)

lemma map_conj_in_UCP:
  fixes U :: "complex Matrix.mat"
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and npos: "0 < n"
  shows "(\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)) \<in> UCP n n"
proof -
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have range_full:
    "\<forall>\<rho>. \<rho> \<in> carrier_mat n n \<longrightarrow> U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
  proof (intro allI impI)
    fix \<rho> :: "complex Matrix.mat" assume \<rho>_c: "\<rho> \<in> carrier_mat n n"
    have U\<rho>_c: "U * \<rho> \<in> carrier_mat n n"
      using U_c \<rho>_c by (rule mult_carrier_mat)
    show "U * \<rho> * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
      using U\<rho>_c Ud_c by (rule mult_carrier_mat)
  qed
  have cp: "completely_positive n n (\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>))"
    using map_conj_cp[OF U_c range_full npos npos] .
  have un: "unital_map n n (\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>))"
    using map_conj_unital[OF U_c U_unit]
    by (simp add: unital_map_def)
  show ?thesis using cp un by (simp add: UCP_def)
qed

lemma unitary_conj_channel_in_UCP:
  fixes U :: "complex Matrix.mat" and p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and p_nn: "0 \<le> p"
      and p_le: "p \<le> 1"
      and npos: "0 < n"
  shows "unitary_conj_channel U p \<in> UCP n n"
proof -
  let ?Phi1 = "identity_channel :: complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  let ?Phi2 = "\<lambda>\<rho>. U * \<rho> * (U\<^sup>\<dagger>)"
  let ?t = "1 - p"
  have t_nn: "0 \<le> ?t" using p_le by simp
  have t_le: "?t \<le> 1" using p_nn by simp
  have Phi1_in: "?Phi1 \<in> UCP n n" using identity_channel_UCP[OF npos] .
  have Phi2_in: "?Phi2 \<in> UCP n n"
    using map_conj_in_UCP[OF U_c U_unit npos] .
  have r1: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> ?Phi1 X \<in> carrier_mat n n"
    by (simp add: identity_channel_def)
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U_c by (rule dagger_carrier)
  have r2: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> ?Phi2 X \<in> carrier_mat n n"
  proof (intro allI impI)
    fix X :: "complex Matrix.mat" assume X_c: "X \<in> carrier_mat n n"
    have UX_c: "U * X \<in> carrier_mat n n"
      using U_c X_c by (rule mult_carrier_mat)
    show "U * X * (U\<^sup>\<dagger>) \<in> carrier_mat n n"
      using UX_c Ud_c by (rule mult_carrier_mat)
  qed
  have convex_ucp:
    "(\<lambda>X. complex_of_real ?t \<cdot>\<^sub>m ?Phi1 X
          + (1 - complex_of_real ?t) \<cdot>\<^sub>m ?Phi2 X) \<in> UCP n n"
    using UCP_convex[OF t_nn t_le Phi1_in Phi2_in r1 r2 npos] .
  (* Match the convex form to unitary_conj_channel. *)
  have shift: "(1 :: complex) - complex_of_real (1 - p) = complex_of_real p"
    by simp
  have id_eq: "\<And>X. ?Phi1 X = X" by (simp add: identity_channel_def)
  have func_eq:
    "(\<lambda>X. complex_of_real ?t \<cdot>\<^sub>m ?Phi1 X
          + (1 - complex_of_real ?t) \<cdot>\<^sub>m ?Phi2 X)
       = unitary_conj_channel U p"
  proof (rule ext)
    fix X :: "complex Matrix.mat"
    have "complex_of_real ?t \<cdot>\<^sub>m ?Phi1 X
            + (1 - complex_of_real ?t) \<cdot>\<^sub>m ?Phi2 X
          = complex_of_real (1 - p) \<cdot>\<^sub>m X
            + complex_of_real p \<cdot>\<^sub>m (U * X * (U\<^sup>\<dagger>))"
      using shift id_eq by simp
    also have "\<dots> = unitary_conj_channel U p X"
      by (simp add: unitary_conj_channel_def)
    finally show "complex_of_real ?t \<cdot>\<^sub>m ?Phi1 X
                    + (1 - complex_of_real ?t) \<cdot>\<^sub>m ?Phi2 X
                  = unitary_conj_channel U p X" .
  qed
  show ?thesis using convex_ucp func_eq by simp
qed

(* unitary_conj_channel is therefore CPTP: CP from UCP, plus the
   already-proved trace preservation. *)

lemma unitary_conj_channel_in_CPTP:
  fixes U :: "complex Matrix.mat" and p :: real
  assumes U_c: "U \<in> carrier_mat n n"
      and U_unit: "unitary U"
      and p_nn: "0 \<le> p"
      and p_le: "p \<le> 1"
      and npos: "0 < n"
  shows "unitary_conj_channel U p \<in> CPTP n n"
proof -
  have ucp: "unitary_conj_channel U p \<in> UCP n n"
    using unitary_conj_channel_in_UCP[OF U_c U_unit p_nn p_le npos] .
  have cp: "completely_positive n n (unitary_conj_channel U p)"
    using ucp by (simp add: UCP_def)
  have tp: "trace_preserving n (unitary_conj_channel U p)"
    unfolding trace_preserving_def
    by (intro allI impI;
        rule unitary_conj_channel_trace_preserving[OF U_c U_unit])
  show ?thesis using cp tp by (simp add: CPTP_def)
qed


(* ============================================================================
   DAY 46
   Topic: bit-flip, phase-flip, bit-phase-flip channels are CPTP / UCP

   Each Pauli channel is a unitary_conj_channel applied to the
   corresponding Pauli matrix.  Since X, Y, Z are all unitary in M_2,
   the Day-45 result puts each in UCP 2 2 and CPTP 2 2 for p \<in> [0,1].
   ============================================================================ *)

lemma bit_flip_channel_eq:
  "bit_flip_channel p = unitary_conj_channel pauli_X p"
  by (rule ext) (simp add: bit_flip_eq_unitary_conj)

lemma phase_flip_channel_eq:
  "phase_flip_channel p = unitary_conj_channel pauli_Z p"
  by (rule ext) (simp add: phase_flip_eq_unitary_conj)

lemma bit_phase_flip_channel_eq:
  "bit_phase_flip_channel p = unitary_conj_channel pauli_Y p"
  by (rule ext) (simp add: bit_phase_flip_channel_def)

lemma bit_flip_channel_UCP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "bit_flip_channel p \<in> UCP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_UCP[OF pauli_X_carrier pauli_X_unitary
                                         p_nn p_le npos]
    by (simp add: bit_flip_channel_eq)
qed

lemma bit_flip_channel_CPTP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "bit_flip_channel p \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_CPTP[OF pauli_X_carrier pauli_X_unitary
                                          p_nn p_le npos]
    by (simp add: bit_flip_channel_eq)
qed

lemma phase_flip_channel_UCP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "phase_flip_channel p \<in> UCP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_UCP[OF pauli_Z_carrier pauli_Z_unitary
                                         p_nn p_le npos]
    by (simp add: phase_flip_channel_eq)
qed

lemma phase_flip_channel_CPTP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "phase_flip_channel p \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_CPTP[OF pauli_Z_carrier pauli_Z_unitary
                                          p_nn p_le npos]
    by (simp add: phase_flip_channel_eq)
qed

lemma bit_phase_flip_channel_UCP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "bit_phase_flip_channel p \<in> UCP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_UCP[OF pauli_Y_carrier pauli_Y_unitary
                                         p_nn p_le npos]
    by (simp add: bit_phase_flip_channel_eq)
qed

lemma bit_phase_flip_channel_CPTP:
  fixes p :: real
  assumes p_nn: "0 \<le> p" and p_le: "p \<le> 1"
  shows "bit_phase_flip_channel p \<in> CPTP 2 2"
proof -
  have npos: "(0 :: nat) < 2" by simp
  show ?thesis
    using unitary_conj_channel_in_CPTP[OF pauli_Y_carrier pauli_Y_unitary
                                          p_nn p_le npos]
    by (simp add: bit_phase_flip_channel_eq)
qed


(* ============================================================================
   DAY 47
   Topic: Singleton Pauli lists are valid Kraus-operator lists

   The singleton list [P], where P is a self-adjoint involution
   (P^dagger = P, P^2 = I), satisfies the kraus_operators predicate
   on M_2.  This recovers the Pauli channels' \<open>p = 1\<close> case as a
   genuine Kraus map.
   ============================================================================ *)

lemma pauli_X_kraus_operators:
  "kraus_operators 2 2 [pauli_X]"
proof -
  have X_c: "pauli_X \<in> carrier_mat 2 2" by simp
  have X_dag: "pauli_X\<^sup>\<dagger> = pauli_X" by (rule pauli_X_dagger)
  have X_sq: "pauli_X * pauli_X = 1\<^sub>m 2" by (rule pauli_X_squared)
  have I_c: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp
  have all_in: "\<forall>W \<in> set [pauli_X]. W \<in> carrier_mat 2 2"
    using X_c by simp
  have step:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [pauli_X] (0\<^sub>m 2 2)
       = pauli_X * pauli_X + 0\<^sub>m 2 2"
    using X_dag by simp
  also have "\<dots> = 1\<^sub>m 2 + 0\<^sub>m 2 2" using X_sq by simp
  also have "\<dots> = 1\<^sub>m 2"
    using I_c by (intro eq_matI) auto
  finally have sum_eq:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [pauli_X] (0\<^sub>m 2 2) = 1\<^sub>m 2" .
  show ?thesis
    unfolding kraus_operators_def
    using all_in sum_eq by blast
qed

lemma pauli_Y_kraus_operators:
  "kraus_operators 2 2 [pauli_Y]"
proof -
  have Y_c: "pauli_Y \<in> carrier_mat 2 2" by simp
  have Y_dag: "pauli_Y\<^sup>\<dagger> = pauli_Y" by (rule pauli_Y_dagger)
  have Y_sq: "pauli_Y * pauli_Y = 1\<^sub>m 2" by (rule pauli_Y_squared)
  have I_c: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp
  have all_in: "\<forall>W \<in> set [pauli_Y]. W \<in> carrier_mat 2 2"
    using Y_c by simp
  have step:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [pauli_Y] (0\<^sub>m 2 2)
       = pauli_Y * pauli_Y + 0\<^sub>m 2 2"
    using Y_dag by simp
  also have "\<dots> = 1\<^sub>m 2 + 0\<^sub>m 2 2" using Y_sq by simp
  also have "\<dots> = 1\<^sub>m 2"
    using I_c by (intro eq_matI) auto
  finally have sum_eq:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [pauli_Y] (0\<^sub>m 2 2) = 1\<^sub>m 2" .
  show ?thesis
    unfolding kraus_operators_def
    using all_in sum_eq by blast
qed

lemma pauli_Z_kraus_operators:
  "kraus_operators 2 2 [pauli_Z]"
proof -
  have Z_c: "pauli_Z \<in> carrier_mat 2 2" by simp
  have Z_dag: "pauli_Z\<^sup>\<dagger> = pauli_Z" by (rule pauli_Z_dagger)
  have Z_sq: "pauli_Z * pauli_Z = 1\<^sub>m 2" by (rule pauli_Z_squared)
  have I_c: "(1\<^sub>m 2 :: complex Matrix.mat) \<in> carrier_mat 2 2" by simp
  have all_in: "\<forall>W \<in> set [pauli_Z]. W \<in> carrier_mat 2 2"
    using Z_c by simp
  have step:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [pauli_Z] (0\<^sub>m 2 2)
       = pauli_Z * pauli_Z + 0\<^sub>m 2 2"
    using Z_dag by simp
  also have "\<dots> = 1\<^sub>m 2 + 0\<^sub>m 2 2" using Z_sq by simp
  also have "\<dots> = 1\<^sub>m 2"
    using I_c by (intro eq_matI) auto
  finally have sum_eq:
    "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) [pauli_Z] (0\<^sub>m 2 2) = 1\<^sub>m 2" .
  show ?thesis
    unfolding kraus_operators_def
    using all_in sum_eq by blast
qed


end