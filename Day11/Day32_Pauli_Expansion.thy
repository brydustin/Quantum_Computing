theory Day32_Pauli_Expansion
  imports QC_Prelims
begin

section \<open>Day 32: the Pauli expansion identity for unitaries (D32-7)\<close>

lemma cmod_parallelogram:
  fixes a b :: complex
  shows "(cmod (a + b))\<^sup>2 + (cmod (a - b))\<^sup>2 = 2 * (cmod a)\<^sup>2 + 2 * (cmod b)\<^sup>2"
  unfolding cmod_power2 by (simp add: power2_eq_square algebra_simps)

proposition pauli_expansion_unitary:
  fixes U :: "complex Matrix.mat" and a0 a1 a2 a3 :: complex
  assumes Uu: "unitary U"
      and U_eq: "U = a0 \<cdot>\<^sub>m 1\<^sub>m 2 + a1 \<cdot>\<^sub>m pauli_X + a2 \<cdot>\<^sub>m pauli_Y + a3 \<cdot>\<^sub>m pauli_Z"
  shows "(cmod a0)\<^sup>2 + (cmod a1)\<^sup>2 + (cmod a2)\<^sup>2 + (cmod a3)\<^sup>2 = 1"
proof -
  have Uc: "U \<in> carrier_mat 2 2"
    unfolding U_eq by (simp add: pauli_X_def pauli_Y_def pauli_Z_def)
  have dr: "dim_row U = 2" and dc: "dim_col U = 2" using Uc by auto
  have e00: "U $$ (0,0) = a0 + a3"
    by (simp add: U_eq pauli_X_def pauli_Y_def pauli_Z_def)
  have e01: "U $$ (0,1) = a1 + \<i> * a2"
    by (simp add: U_eq pauli_X_def pauli_Y_def pauli_Z_def)
  have e10: "U $$ (1,0) = a1 - \<i> * a2"
    by (simp add: U_eq pauli_X_def pauli_Y_def pauli_Z_def)
  have e11: "U $$ (1,1) = a0 - a3"
    by (simp add: U_eq pauli_X_def pauli_Y_def pauli_Z_def)
  have UdU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m 2" using Uu dc by (simp add: unitary_def)
  have tr2: "Tr ((U\<^sup>\<dagger>) * U) = 2" unfolding UdU by (simp add: Tr_one_mat)
  have hs: "\<langle>\<langle> U | U \<rangle>\<rangle> = Tr ((U\<^sup>\<dagger>) * U)"
    by (rule hs_inner_prod_as_trace) simp_all
  have expand: "\<langle>\<langle> U | U \<rangle>\<rangle> =
      cnj (U $$ (0,0)) * U $$ (0,0) + cnj (U $$ (0,1)) * U $$ (0,1)
    + cnj (U $$ (1,0)) * U $$ (1,0) + cnj (U $$ (1,1)) * U $$ (1,1)"
    unfolding hs_inner_prod_def dr dc by (simp add: numeral_2_eq_2)
  have "2 = Re (\<langle>\<langle> U | U \<rangle>\<rangle>)" using hs tr2 by simp
  also have "\<dots> = (cmod (a0 + a3))\<^sup>2 + (cmod (a1 + \<i> * a2))\<^sup>2
                 + (cmod (a1 - \<i> * a2))\<^sup>2 + (cmod (a0 - a3))\<^sup>2"
    unfolding expand e00 e01 e10 e11 cnj_mult_self_cmod by simp
  also have "\<dots> = 2 * ((cmod a0)\<^sup>2 + (cmod a1)\<^sup>2 + (cmod a2)\<^sup>2 + (cmod a3)\<^sup>2)"
  proof -
    have p1: "(cmod (a0 + a3))\<^sup>2 + (cmod (a0 - a3))\<^sup>2 = 2 * (cmod a0)\<^sup>2 + 2 * (cmod a3)\<^sup>2"
      by (rule cmod_parallelogram)
    have p2: "(cmod (a1 + \<i> * a2))\<^sup>2 + (cmod (a1 - \<i> * a2))\<^sup>2 = 2 * (cmod a1)\<^sup>2 + 2 * (cmod a2)\<^sup>2"
      using cmod_parallelogram[of a1 "\<i> * a2"] by (simp add: norm_mult)
    have "(cmod (a0 + a3))\<^sup>2 + (cmod (a1 + \<i> * a2))\<^sup>2 + (cmod (a1 - \<i> * a2))\<^sup>2 + (cmod (a0 - a3))\<^sup>2
          = ((cmod (a0 + a3))\<^sup>2 + (cmod (a0 - a3))\<^sup>2) + ((cmod (a1 + \<i> * a2))\<^sup>2 + (cmod (a1 - \<i> * a2))\<^sup>2)"
      by (simp add: algebra_simps)
    also have "\<dots> = (2 * (cmod a0)\<^sup>2 + 2 * (cmod a3)\<^sup>2) + (2 * (cmod a1)\<^sup>2 + 2 * (cmod a2)\<^sup>2)"
      unfolding p1 p2 ..
    also have "\<dots> = 2 * ((cmod a0)\<^sup>2 + (cmod a1)\<^sup>2 + (cmod a2)\<^sup>2 + (cmod a3)\<^sup>2)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  finally show ?thesis by simp
qed

end
