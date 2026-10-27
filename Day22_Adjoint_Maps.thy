theory Day22_Adjoint_Maps
  imports Day19_Choi_Positivity
begin

section \<open>Day 22: the adjoint map, an affine bijection from UCP onto CPTP (D22-5)\<close>

text \<open>The notes: $\mathrm{UCP}(M_n,M_d)$ and $\mathrm{CPTP}(M_d,M_n)$ are convex, and
$\Gamma(\Phi)=\Phi^*$ is an affine bijection between them with affine inverse, so the two
convex sets are affinely isomorphic.  The adjoint was available only for Kraus maps
(\<^const>\<open>kraus_adjoint_dim\<close>); here it is defined for every linear $\Phi$.  Maps are total
functions on matrices, so $\Gamma$ is a bijection up to agreement on $M_n$, resp.\ $M_d$:
$\Gamma$ sends linear UCP maps to linear CPTP maps and back, and $\Gamma(\Gamma(\Phi))=\Phi$ on
$M_n$.  The set \<^const>\<open>UCP\<close> does not record linearity, which the notes' maps have, so it is
assumed.\<close>

text \<open>For linear $\Phi:M_n\to M_d$, $\Phi^*:M_d\to M_n$ is determined by
$\langle Y|\Phi(X)\rangle=\langle\Phi^*(Y)|X\rangle$; taking $X=E_{ij}$ gives
$\Phi^*(Y)_{ij}=\langle\Phi(E_{ij})|Y\rangle$.\<close>

definition map_adjoint :: "nat \<Rightarrow> nat \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "map_adjoint n d \<Phi> Y = Matrix.mat n n (\<lambda>(i, j). \<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>)"

text \<open>$\Phi^*:M_d\to M_n$ is determined by $\langle\Phi^*(Y)|X\rangle=\langle Y|\Phi(X)\rangle$.  Since
$\Phi(X)=\sum_{i,j}x_{ij}\Phi(E_{ij})$ for linear $\Phi$, it suffices that
\[ \Phi^*(Y)_{ij}=\langle\Phi(E_{ij})|Y\rangle, \]
which is the definition.\<close>

lemma map_adjoint_carrier [simp]: "map_adjoint n d \<Phi> Y \<in> carrier_mat n n"
  by (simp add: map_adjoint_def)

lemma map_adjoint_dims [simp]: "dim_row (map_adjoint n d \<Phi> Y) = n" "dim_col (map_adjoint n d \<Phi> Y) = n"
  by (simp_all add: map_adjoint_def)

lemma lin_entry:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and X: "X \<in> carrier_mat n n" and a: "a < d" and b: "b < d"
  shows "\<Phi> X $$ (a, b) = (\<Sum>i<n. \<Sum>j<n. X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b))"
proof -
  have Ec: "\<And>i j. \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d" using L unfolding lin_on_def by simp
  have "\<Phi> X $$ (a, b) = msum d d (\<lambda>(i,j). X $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) (List.product [0..<n] [0..<n]) $$ (a, b)"
    by (simp add: lin_expansion[OF L X])
  also have "\<dots> = (\<Sum>x\<leftarrow>List.product [0..<n] [0..<n]. ((\<lambda>(i,j). X $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) x) $$ (a, b))"
    by (rule msum_index) (use Ec a b in auto)
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b))"
    unfolding sum_list_product_upt using Ec a b carrier_matD[OF Ec] by simp
  finally show ?thesis .
qed

theorem map_adjoint_correct:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and X: "X \<in> carrier_mat n n" and Y: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> Y | \<Phi> X \<rangle>\<rangle> = \<langle>\<langle> map_adjoint n d \<Phi> Y | X \<rangle>\<rangle>"
proof -
  have Ec: "\<And>i j. \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d" using L unfolding lin_on_def by simp
  have PX: "\<Phi> X \<in> carrier_mat d d" using L X unfolding lin_on_def by simp
  have "\<langle>\<langle> Y | \<Phi> X \<rangle>\<rangle> = (\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * \<Phi> X $$ (a, b))"
    using PX by (simp add: hs_inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>a<d. \<Sum>b<d. \<Sum>i<n. \<Sum>j<n. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (simp add: lin_entry[OF L X] sum_distrib_left)
  also have "\<dots> = (\<Sum>a<d. \<Sum>i<n. \<Sum>b<d. \<Sum>j<n. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. \<Sum>a<d. \<Sum>b<d. \<Sum>j<n. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. \<Sum>a<d. \<Sum>j<n. \<Sum>b<d. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (rule sum.cong[OF refl], rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. \<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))"
    by (rule sum.cong[OF refl], rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. cnj (\<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>) * X $$ (i, j))"
  proof (intro sum.cong refl)
    fix i j
    have "cnj (\<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>) = \<langle>\<langle> Y | \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<rangle>\<rangle>"
      using hs_inner_prod_cnj[of Y "\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)"] carrier_matD[OF Y] carrier_matD[OF Ec[of i j]] by simp
    also have "\<dots> = (\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b))"
      using carrier_matD[OF Ec[of i j]] by (simp add: hs_inner_prod_def atLeast0LessThan)
    finally have c: "cnj (\<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>) = (\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b))" .
    have "(\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))
          = (\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)) * X $$ (i, j)"
      by (simp add: sum_distrib_left sum_distrib_right mult_ac)
    thus "(\<Sum>a<d. \<Sum>b<d. cnj (Y $$ (a, b)) * (X $$ (i, j) * \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (a, b)))
                  = cnj (\<langle>\<langle> \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) | Y \<rangle>\<rangle>) * X $$ (i, j)" unfolding c .
  qed
  also have "\<dots> = \<langle>\<langle> map_adjoint n d \<Phi> Y | X \<rangle>\<rangle>"
    using X by (simp add: hs_inner_prod_def map_adjoint_def atLeast0LessThan)
  finally show ?thesis .
qed

lemma hs_inner_prod_mat_unit:
  assumes A: "A \<in> carrier_mat n n" and i: "i < n" and j: "j < n"
  shows "\<langle>\<langle> A | E\<lbrakk>i,j ; n,n\<rbrakk> \<rangle>\<rangle> = cnj (A $$ (i, j))"
proof -
  have "\<langle>\<langle> A | E\<lbrakk>i,j ; n,n\<rbrakk> \<rangle>\<rangle> = (\<Sum>a<n. \<Sum>b<n. cnj (A $$ (a, b)) * (if a = i \<and> b = j then 1 else 0))"
    by (simp add: hs_inner_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>a<n. if a = i then cnj (A $$ (a, j)) else 0)"
    by (rule sum.cong[OF refl]) (use j in \<open>auto simp: if_distrib cong: if_cong\<close>)
  also have "\<dots> = cnj (A $$ (i, j))" using i by simp
  finally show ?thesis .
qed

lemma hs_inner_prod_ext:
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
      and eq: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<langle>\<langle> A | X \<rangle>\<rangle> = \<langle>\<langle> B | X \<rangle>\<rangle>"
  shows "A = B"
proof (rule eq_matI)
  fix i j assume "i < dim_row B" "j < dim_col B"
  hence i: "i < n" and j: "j < n" using B by auto
  have "cnj (A $$ (i, j)) = cnj (B $$ (i, j))"
    using eq[of "E\<lbrakk>i,j ; n,n\<rbrakk>"] hs_inner_prod_mat_unit[OF A i j] hs_inner_prod_mat_unit[OF B i j] by simp
  thus "A $$ (i, j) = B $$ (i, j)" by simp
qed (use A B in auto)

lemma map_adjoint_lin: "lin_on d n (carrier_mat d d) (map_adjoint n d \<Phi>)"
  unfolding lin_on_def
proof (intro conjI ballI allI)
  fix A B :: "complex Matrix.mat" assume A: "A \<in> carrier_mat d d" and B: "B \<in> carrier_mat d d"
  show "map_adjoint n d \<Phi> (A + B) = map_adjoint n d \<Phi> A + map_adjoint n d \<Phi> B"
    by (rule eq_matI) (use A B in \<open>auto simp: map_adjoint_def hs_inner_prod_def sum.distrib distrib_left\<close>)
next
  fix A :: "complex Matrix.mat" and c :: complex assume A: "A \<in> carrier_mat d d"
  show "map_adjoint n d \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m map_adjoint n d \<Phi> A"
    by (rule eq_matI) (use A in \<open>auto simp: map_adjoint_def hs_inner_prod_def sum_distrib_left mult_ac\<close>)
qed simp

lemma map_adjoint_cong:
  assumes "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = \<Psi> X"
  shows "map_adjoint n d \<Phi> = map_adjoint n d \<Psi>"
  unfolding map_adjoint_def using assms by (intro ext) (simp add: mat_unit_def)

text \<open>For a Kraus map the adjoint is \<^const>\<open>kraus_adjoint_dim\<close>.\<close>

lemma map_adjoint_kraus:
  assumes As: "\<forall>A \<in> set As. A \<in> carrier_mat d n" and Y: "Y \<in> carrier_mat d d"
  shows "map_adjoint n d (kraus_map_dim d As) Y = kraus_adjoint_dim n As Y"
proof (rule hs_inner_prod_ext[OF map_adjoint_carrier kraus_adjoint_dim_carrier[OF As Y]])
  fix X :: "complex Matrix.mat" assume X: "X \<in> carrier_mat n n"
  have L: "lin_on n d (carrier_mat n n) (kraus_map_dim d As)" by (rule kraus_lin_on[OF As])
  show "\<langle>\<langle> map_adjoint n d (kraus_map_dim d As) Y | X \<rangle>\<rangle> = \<langle>\<langle> kraus_adjoint_dim n As Y | X \<rangle>\<rangle>"
    using map_adjoint_correct[OF L X Y] kraus_adjoint_correct[OF As X Y] by simp
qed

text \<open>$\Phi^{**}=\Phi$.\<close>

theorem map_adjoint_adjoint:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and X: "X \<in> carrier_mat n n"
  shows "map_adjoint d n (map_adjoint n d \<Phi>) X = \<Phi> X"
proof -
  have PX: "\<Phi> X \<in> carrier_mat d d" using L X unfolding lin_on_def by simp
  have "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> \<langle>\<langle> map_adjoint d n (map_adjoint n d \<Phi>) X | Y \<rangle>\<rangle> = \<langle>\<langle> \<Phi> X | Y \<rangle>\<rangle>"
  proof -
    fix Y :: "complex Matrix.mat" assume Y: "Y \<in> carrier_mat d d"
    have Ac: "map_adjoint d n (map_adjoint n d \<Phi>) X \<in> carrier_mat d d" by simp
    have "\<langle>\<langle> map_adjoint d n (map_adjoint n d \<Phi>) X | Y \<rangle>\<rangle> = \<langle>\<langle> X | map_adjoint n d \<Phi> Y \<rangle>\<rangle>"
      using map_adjoint_correct[OF map_adjoint_lin Y X] by simp
    also have "\<dots> = cnj \<langle>\<langle> map_adjoint n d \<Phi> Y | X \<rangle>\<rangle>"
      using hs_inner_prod_cnj[of X "map_adjoint n d \<Phi> Y"] carrier_matD[OF X] by simp
    also have "\<dots> = cnj \<langle>\<langle> Y | \<Phi> X \<rangle>\<rangle>" using map_adjoint_correct[OF L X Y] by simp
    also have "\<dots> = \<langle>\<langle> \<Phi> X | Y \<rangle>\<rangle>"
      using hs_inner_prod_cnj[of "\<Phi> X" Y] carrier_matD[OF PX] carrier_matD[OF Y] by simp
    finally show "\<langle>\<langle> map_adjoint d n (map_adjoint n d \<Phi>) X | Y \<rangle>\<rangle> = \<langle>\<langle> \<Phi> X | Y \<rangle>\<rangle>" .
  qed
  moreover have "\<And>A B. A \<in> carrier_mat d d \<Longrightarrow> B \<in> carrier_mat d d \<Longrightarrow> (\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> \<langle>\<langle> A | Y \<rangle>\<rangle> = \<langle>\<langle> B | Y \<rangle>\<rangle>) \<Longrightarrow> A = B"
    by (rule hs_inner_prod_ext)
  ultimately show ?thesis using PX by force
qed

lemma cp_kraus_form:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and cp: "completely_positive n d \<Phi>" and n: "0 < n" and d: "0 < d"
  shows "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Ws X)"
  using choi_four_conditions[OF lin_on_choi_hyps[OF L] n d] cp by blast

lemma trace_preserving_cong:
  assumes "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = \<Psi> X"
  shows "trace_preserving n \<Phi> \<longleftrightarrow> trace_preserving n \<Psi>"
  using assms unfolding trace_preserving_def by auto

text \<open>$\Gamma(\Phi)=\Phi^*$ maps the unital CP maps $M_n\to M_d$ to the CPTP maps $M_d\to M_n$ and
back.\<close>

theorem adjoint_ucp_imp_cptp:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and U: "\<Phi> \<in> UCP n d" and n: "0 < n" and d: "0 < d"
  shows "map_adjoint n d \<Phi> \<in> CPTP d n"
proof -
  have cp: "completely_positive n d \<Phi>" and un: "\<Phi> (1\<^sub>m n) = 1\<^sub>m d" using U by (auto simp: UCP_def unital_map_def)
  obtain Ws where Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and W: "\<And>X. X \<in> carrier_mat n n \<Longrightarrow> \<Phi> X = kraus_map_dim d Ws X"
    using cp_kraus_form[OF L cp n d] by blast
  have eq: "\<And>Y. Y \<in> carrier_mat d d \<Longrightarrow> map_adjoint n d \<Phi> Y = kraus_adjoint_dim n Ws Y"
    using map_adjoint_cong[of n \<Phi> "kraus_map_dim d Ws" d] W map_adjoint_kraus[OF Wc] by simp
  have "completely_positive d n (kraus_adjoint_dim n Ws)" by (rule adjoint_cp_from_kraus[OF Wc n d])
  hence "completely_positive d n (map_adjoint n d \<Phi>)" using completely_positive_cong[of d "map_adjoint n d \<Phi>" "kraus_adjoint_dim n Ws" n] eq by blast
  moreover have "unital_map n d (kraus_map_dim d Ws)" using un W[of "1\<^sub>m n"] by (simp add: unital_map_def)
  hence "trace_preserving d (kraus_adjoint_dim n Ws)" using cp_unital_iff_adjoint_tp[OF Wc n d] by simp
  hence "trace_preserving d (map_adjoint n d \<Phi>)" using trace_preserving_cong[of d "map_adjoint n d \<Phi>" "kraus_adjoint_dim n Ws"] eq by blast
  ultimately show ?thesis by (simp add: CPTP_def)
qed

theorem adjoint_cptp_imp_ucp:
  assumes L: "lin_on d n (carrier_mat d d) \<Psi>" and C: "\<Psi> \<in> CPTP d n" and n: "0 < n" and d: "0 < d"
  shows "map_adjoint d n \<Psi> \<in> UCP n d"
proof -
  have cp: "completely_positive d n \<Psi>" and tp: "trace_preserving d \<Psi>" using C by (auto simp: CPTP_def)
  obtain Bs where Bc: "\<forall>B \<in> set Bs. B \<in> carrier_mat n d" and B: "\<And>X. X \<in> carrier_mat d d \<Longrightarrow> \<Psi> X = kraus_map_dim n Bs X"
    using cp_kraus_form[OF L cp d n] by blast
  define As where "As = map (\<lambda>B. B\<^sup>\<dagger>) Bs"
  have Ac: "\<forall>A \<in> set As. A \<in> carrier_mat d n" using Bc by (auto simp: As_def intro: dagger_carrier)
  have BsAs: "map (\<lambda>A. A\<^sup>\<dagger>) As = Bs" by (simp add: As_def comp_def dagger_of_dagger_is_id)
  have eq: "\<And>Y. Y \<in> carrier_mat n n \<Longrightarrow> map_adjoint d n \<Psi> Y = kraus_map_dim d As Y"
  proof -
    fix Y :: "complex Matrix.mat" assume Y: "Y \<in> carrier_mat n n"
    have "map_adjoint d n \<Psi> Y = kraus_adjoint_dim d Bs Y"
      using map_adjoint_cong[of d \<Psi> "kraus_map_dim n Bs" n] B map_adjoint_kraus[OF Bc Y] by simp
    also have "\<dots> = kraus_map_dim d As Y" unfolding As_def by (rule kraus_adjoint_dim_as_kraus_map_dim[OF Bc Y])
    finally show "map_adjoint d n \<Psi> Y = kraus_map_dim d As Y" .
  qed
  have "completely_positive n d (kraus_map_dim d As)" by (rule kraus_cp_no_tp[OF Ac n d])
  hence "completely_positive n d (map_adjoint d n \<Psi>)" using completely_positive_cong[of n "map_adjoint d n \<Psi>" "kraus_map_dim d As" d] eq by blast
  moreover have "\<And>X. X \<in> carrier_mat d d \<Longrightarrow> kraus_adjoint_dim n As X = \<Psi> X"
    using kraus_adjoint_dim_as_kraus_map_dim[OF Ac] B unfolding BsAs by simp
  hence "trace_preserving d (kraus_adjoint_dim n As)" using tp trace_preserving_cong[of d "kraus_adjoint_dim n As" \<Psi>] by blast
  hence "unital_map n d (kraus_map_dim d As)" using cp_unital_iff_adjoint_tp[OF Ac n d] by simp
  hence "unital_map n d (map_adjoint d n \<Psi>)" using eq[of "1\<^sub>m n"] by (simp add: unital_map_def)
  ultimately show ?thesis by (simp add: UCP_def)
qed

text \<open>$\Gamma$ is affine (for real weights), and $\Gamma^{-1}=\Gamma$ by
@{thm [source] map_adjoint_adjoint}.\<close>

lemma hs_inner_prod_left_real_comb:
  fixes t s :: real
  assumes A: "A \<in> carrier_mat d d" and B: "B \<in> carrier_mat d d" and Y: "Y \<in> carrier_mat d d"
  shows "\<langle>\<langle> complex_of_real t \<cdot>\<^sub>m A + complex_of_real s \<cdot>\<^sub>m B | Y \<rangle>\<rangle>
         = complex_of_real t * \<langle>\<langle> A | Y \<rangle>\<rangle> + complex_of_real s * \<langle>\<langle> B | Y \<rangle>\<rangle>"
proof -
  have "\<langle>\<langle> complex_of_real t \<cdot>\<^sub>m A + complex_of_real s \<cdot>\<^sub>m B | Y \<rangle>\<rangle>
        = (\<Sum>i<d. \<Sum>j<d. complex_of_real t * (cnj (A $$ (i, j)) * Y $$ (i, j)) + complex_of_real s * (cnj (B $$ (i, j)) * Y $$ (i, j)))"
  proof -
    have e: "\<And>i j. i < d \<Longrightarrow> j < d \<Longrightarrow> cnj ((complex_of_real t \<cdot>\<^sub>m A + complex_of_real s \<cdot>\<^sub>m B) $$ (i, j)) * Y $$ (i, j)
        = complex_of_real t * (cnj (A $$ (i, j)) * Y $$ (i, j)) + complex_of_real s * (cnj (B $$ (i, j)) * Y $$ (i, j))"
      using A B by (simp add: algebra_simps)
    show ?thesis unfolding hs_inner_prod_def carrier_matD(1,2)[OF Y] atLeast0LessThan
      by (intro sum.cong refl) (simp add: e)
  qed
  also have "\<dots> = complex_of_real t * \<langle>\<langle> A | Y \<rangle>\<rangle> + complex_of_real s * \<langle>\<langle> B | Y \<rangle>\<rangle>"
    using carrier_matD[OF Y] by (simp add: hs_inner_prod_def atLeast0LessThan sum.distrib sum_distrib_left)
  finally show ?thesis .
qed

theorem map_adjoint_affine:
  fixes t :: real
  assumes L1: "lin_on n d (carrier_mat n n) \<Phi>1" and L2: "lin_on n d (carrier_mat n n) \<Phi>2" and Y: "Y \<in> carrier_mat d d"
  shows "map_adjoint n d (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + complex_of_real (1 - t) \<cdot>\<^sub>m \<Phi>2 X) Y
         = complex_of_real t \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + complex_of_real (1 - t) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y"
proof (rule eq_matI)
  fix i j assume "i < dim_row (complex_of_real t \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + complex_of_real (1 - t) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y)"
    "j < dim_col (complex_of_real t \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + complex_of_real (1 - t) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y)"
  hence i: "i < n" and j: "j < n" by simp_all
  have c1: "\<Phi>1 (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d" and c2: "\<Phi>2 (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d"
    using L1 L2 unfolding lin_on_def by simp_all
  show "map_adjoint n d (\<lambda>X. complex_of_real t \<cdot>\<^sub>m \<Phi>1 X + complex_of_real (1 - t) \<cdot>\<^sub>m \<Phi>2 X) Y $$ (i, j)
        = (complex_of_real t \<cdot>\<^sub>m map_adjoint n d \<Phi>1 Y + complex_of_real (1 - t) \<cdot>\<^sub>m map_adjoint n d \<Phi>2 Y) $$ (i, j)"
    using i j hs_inner_prod_left_real_comb[OF c1 c2 Y, of t "1 - t"] by (simp add: map_adjoint_def)
qed simp_all

end
