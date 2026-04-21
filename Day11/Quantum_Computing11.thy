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

theorem spectral_ensemble_exists:
  fixes \<rho> :: "complex Matrix.mat"
  assumes dm: "density_matrix n \<rho>"
  shows "\<exists>E. ensemble n E \<and> ensemble_density n E = \<rho>"
  sorry
  (* Proof sketch (PDF p.\ 43, proof of the Proposition, direction \<Leftarrow>):
     From \<open>density_matrix n \<rho>\<close> we have \<rho> hermitian, \<rho> PSD, and \<open>Tr \<rho> = 1\<close>.
     By \<open>hermitian_spectral_decomp\<close> (Days 3\<endash>10) there exist a unitary U and a
     real list D of length n with \<open>U\<^sup>\<dagger> * \<rho> * U = diag_mat_of_real D\<close>, hence
       \<open>\<rho> = U * diag_mat_of_real D * U\<^sup>\<dagger> = \<Sum>i<n. (D!i) \<cdot> |col U i\<rangle>\<langle>col U i|\<close>.
     Each \<open>D!i\<close> is \<ge>0 (\<rho> PSD) and \<open>\<Sum>i<n. D!i = Tr \<rho> = 1\<close>.  Thus
       \<open>E = zip D (map (\<lambda>i. col U i) [0..<n])\<close>
     is an ensemble with \<open>ensemble_density n E = \<rho>\<close>. *)

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
  show "\<rho> * \<rho> = \<rho>" sorry
  (* Proof sketch: with \<rho> = mat_of_cols n [\<psi>] * (mat_of_cols n [\<psi>])\<^sup>\<dagger>
     = M * M\<^sup>\<dagger>, one has M\<^sup>\<dagger> * M = (1\<^sub>m 1) since \<open>\<langle>\<psi>|\<psi>\<rangle> = \<parallel>\<psi>\<parallel>\<^sup>2 = 1\<close>.
     Then \<rho>\<^sup>2 = M * (M\<^sup>\<dagger> * M) * M\<^sup>\<dagger> = M * M\<^sup>\<dagger> = \<rho>. *)
next
  assume idem: "\<rho> * \<rho> = \<rho>"
  show "pure_state_density n \<rho>" sorry
  (* Proof sketch: spectral decomposition gives \<rho> = U * diag_mat_of_real D * U\<^sup>\<dagger>
     with D!i \<ge> 0 (PSD) and \<open>\<Sum>i<n. D!i = Tr \<rho> = 1\<close>.  Idempotence forces
     (D!i)\<^sup>2 = D!i, i.e. D!i \<in> {0,1}; combined with \<open>\<Sum>i<n. D!i = 1\<close>, exactly
     one diagonal entry equals 1.  Let \<psi> = col U i for that i; then
     \<open>\<rho> = pure_density \<psi>\<close> and \<psi> is a unit vector, so \<open>quantum_state n \<psi>\<close>. *)
qed

theorem pure_ensemble_parallel:
  fixes \<psi> :: "complex Matrix.vec"
  assumes st: "quantum_state n \<psi>"
      and ens: "ensemble n E"
      and dens: "ensemble_density n E = pure_density \<psi>"
      and mem: "(p, \<psi>\<^sub>i) \<in> set E"
      and ppos: "0 < p"
  shows "\<exists>\<beta>. \<psi>\<^sub>i = \<beta> \<cdot>\<^sub>v \<psi>"
  sorry
  (* Proof sketch (PDF p.\ 44): fix any \<gamma> with \<open>dim_vec \<gamma> = n\<close> and \<open>\<langle>\<psi>|\<gamma>\<rangle> = 0\<close>.
     Compute \<open>\<langle>\<gamma> | pure_density \<psi> *\<^sub>v \<gamma>\<rangle> = |\<langle>\<psi>|\<gamma>\<rangle>|\<^sup>2 = 0\<close>.  By \<open>dens\<close> the same
     quantity equals \<open>\<Sum>_{(p,\<psi>\<^sub>j) \<in> E} p \<cdot> |\<langle>\<psi>\<^sub>j|\<gamma>\<rangle>|\<^sup>2\<close> \<ge> 0, so every term
     vanishes; in particular \<open>\<langle>\<psi>\<^sub>i|\<gamma>\<rangle> = 0\<close> using \<open>ppos\<close>.  Thus \<psi>\<^sub>i is orthogonal
     to every \<gamma> orthogonal to \<psi>, so \<psi>\<^sub>i lies in \<open>span {\<psi>}\<close>, and we can write
     \<open>\<psi>\<^sub>i = \<beta> \<cdot>\<^sub>v \<psi>\<close> with \<open>\<beta> = \<langle>\<psi>|\<psi>\<^sub>i\<rangle>\<close>. *)

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