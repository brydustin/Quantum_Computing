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

lemma CCNOT_inv [simp]:
  "CCNOT * CCNOT = 1\<^sub>m 8"
  apply (simp add: CCNOT_def times_mat_def one_mat_def)
  apply (rule cong_mat)
  by (auto simp: scalar_prod_def)

lemma CCNOT_dim_row [simp]:
  "dim_row CCNOT = 8"
  by (simp add: CCNOT_def)

lemma CCNOT_dim_col [simp]:
  "dim_col CCNOT = 8"
  by (simp add: CCNOT_def)

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

(* No-Cloning Theorem: no cloner exists (for n \<ge> 2). *)

theorem no_cloning:
  assumes n2: "2 \<le> n"
  shows "\<not> (\<exists>U \<phi>. is_cloner n U \<phi>)"
proof
  assume "\<exists>U \<phi>. is_cloner n U \<phi>"
  then obtain U \<phi> where cloner: "is_cloner n U \<phi>" by blast
  (* Take two distinct unit vectors \<psi>1, \<psi>2 with \<langle>\<psi>1|\<psi>2\<rangle> \<noteq> 0 and \<noteq> 1
     (possible since n \<ge> 2).  Use unitarity of U to get
       \<langle>\<psi>1\<otimes>\<phi> | \<psi>2\<otimes>\<phi>\<rangle> = \<langle>U(\<psi>1\<otimes>\<phi>) | U(\<psi>2\<otimes>\<phi>)\<rangle> = \<langle>\<psi>1\<otimes>\<psi>1 | \<psi>2\<otimes>\<psi>2\<rangle>.
     LHS = \<langle>\<psi>1|\<psi>2\<rangle>\<sqdot>\<langle>\<phi>|\<phi>\<rangle> = \<langle>\<psi>1|\<psi>2\<rangle>.
     RHS = \<langle>\<psi>1|\<psi>2\<rangle>\<sqdot>\<langle>\<psi>1|\<psi>2\<rangle> = \<langle>\<psi>1|\<psi>2\<rangle>².
     So \<langle>\<psi>1|\<psi>2\<rangle> = \<langle>\<psi>1|\<psi>2\<rangle>², which forces \<langle>\<psi>1|\<psi>2\<rangle> \<in> {0, 1}. *)
  show False sorry
qed

end
