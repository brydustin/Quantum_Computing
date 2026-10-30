theory Kraus_Maps_Bridge
  imports Kraus_Maps.Kraus_Maps Complex_Bounded_Operators.Cblinfun_Matrix
    Quantum_Computing_CP_Maps.Day19_Choi_Theorem
begin

section \<open>The lectures' Kraus maps as Kraus maps of the AFP\<close>

text \<open>The AFP entry \emph{Kraus Maps} (Unruh) defines Kraus families and Kraus maps on trace-class
operators of arbitrary Hilbert spaces, \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> of \emph{Complex Bounded Operators}.  The
lectures work with matrices.  For finite types the two meet: \<^const>\<open>cblinfun_of_mat\<close> and
\<^const>\<open>mat_of_cblinfun\<close> translate between $n\times n$ matrices and operators on \<open>'n ell2\<close>, $n$
the cardinality of \<open>'n\<close>, and every operator there is trace class.  A list of Kraus matrices
$W_0,\dots,W_{k-1}$ gives the Kraus family $\{(W_i,i)\}$ (zero operators removed, indices keeping
repeated matrices apart).  Its Kraus map is the lectures' $\rho\mapsto\sum_iW_i\rho W_i^*$, it is
trace preserving exactly when $\sum_iW_i^*W_i=I$, and by Choi's theorem (Lecture 19) every
completely positive map of the lectures is a Kraus map of the AFP.\<close>

unbundle cblinfun_syntax

subsection \<open>Matrices and trace-class operators\<close>

definition tc_of_mat :: "complex Matrix.mat \<Rightarrow> ('a::enum ell2, 'a ell2) trace_class" where
  "tc_of_mat M = Abs_trace_class (cblinfun_of_mat M)"

definition mat_of_tc :: "('a::enum ell2, 'a ell2) trace_class \<Rightarrow> complex Matrix.mat" where
  "mat_of_tc T = mat_of_cblinfun (from_trace_class T)"

lemma from_tc_of_mat: "from_trace_class (tc_of_mat M :: ('a::enum ell2, 'a ell2) trace_class) = cblinfun_of_mat M"
  unfolding tc_of_mat_def by (rule Abs_trace_class_inverse) simp

lemma tc_of_mat_of_tc: "tc_of_mat (mat_of_tc T) = T"
  unfolding tc_of_mat_def mat_of_tc_def mat_of_cblinfun_inverse by (rule from_trace_class_inverse)

lemma mat_of_tc_carrier: "mat_of_tc (T :: ('a::enum ell2, 'a ell2) trace_class) \<in> carrier_mat CARD('a) CARD('a)"
  using mat_of_cblinfun_ell2_carrier[of "from_trace_class T"]
  by (simp add: mat_of_tc_def canonical_basis_length)

lemma mat_of_cblinfun_of_mat:
  assumes "M \<in> carrier_mat CARD('b) CARD('a)"
  shows "mat_of_cblinfun (cblinfun_of_mat M :: 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2) = M"
  using assms by (intro cblinfun_of_mat_inverse) simp

lemma dagger_mat_adjoint: "M\<^sup>\<dagger> = mat_adjoint M"
  by (rule eq_matI) (simp_all add: dagger_def mat_adjoint_def mat_of_rows_def)

lemma mat_of_cblinfun_sum_list:
  fixes f :: "'c \<Rightarrow> 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2"
  shows "mat_of_cblinfun (\<Sum>W\<leftarrow>Ws. f W) = foldr (\<lambda>W acc. mat_of_cblinfun (f W) + acc) Ws (0\<^sub>m CARD('b) CARD('a))"
  by (induction Ws) (simp_all add: mat_of_cblinfun_zero mat_of_cblinfun_plus)

lemma mat_of_cblinfun_sandwich_of_mat:
  assumes W: "W \<in> carrier_mat CARD('b) CARD('a)" and A: "A \<in> carrier_mat CARD('a) CARD('a)"
  shows "mat_of_cblinfun (sandwich (cblinfun_of_mat W :: 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2) (cblinfun_of_mat A))
    = W * A * (W\<^sup>\<dagger>)"
  by (simp add: sandwich_apply mat_of_cblinfun_compose mat_of_cblinfun_adj mat_of_cblinfun_of_mat[OF W]
      mat_of_cblinfun_of_mat[OF A] dagger_mat_adjoint)

lemma mat_of_cblinfun_gram:
  assumes W: "W \<in> carrier_mat CARD('b) CARD('a)"
  shows "mat_of_cblinfun ((cblinfun_of_mat W :: 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2)* o\<^sub>C\<^sub>L
      (cblinfun_of_mat W :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2))
    = (W\<^sup>\<dagger>) * W"
  by (simp add: mat_of_cblinfun_compose mat_of_cblinfun_adj mat_of_cblinfun_of_mat[OF W] dagger_mat_adjoint)

subsection \<open>The Kraus family of a list of matrices\<close>

definition kf_of_mats :: "complex Matrix.mat list \<Rightarrow> ('a::enum ell2, 'b::enum ell2, nat) kraus_family" where
  "kf_of_mats Ws = Abs_kraus_family ((\<lambda>i. (cblinfun_of_mat (Ws ! i), i)) `
     {i. i < length Ws \<and> cblinfun_of_mat (Ws ! i) \<noteq> (0 :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)})"

lemma Rep_kf_of_mats:
  "Rep_kraus_family (kf_of_mats Ws :: ('a::enum ell2, 'b::enum ell2, nat) kraus_family) =
     (\<lambda>i. (cblinfun_of_mat (Ws ! i), i)) ` {i. i < length Ws \<and> cblinfun_of_mat (Ws ! i) \<noteq> (0 :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)}"
  unfolding kf_of_mats_def by (rule Abs_kraus_family_inverse, rule CollectI, rule kraus_family_if_finite) auto

lemma finite_kf_of_mats: "finite (Rep_kraus_family (kf_of_mats Ws :: ('a::enum ell2, 'b::enum ell2, nat) kraus_family))"
  unfolding Rep_kf_of_mats by simp

lemma sum_kf_of_mats:
  fixes g :: "('a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2) \<Rightarrow> 'c::comm_monoid_add"
  assumes g0: "g 0 = 0"
  shows "(\<Sum>E\<in>Rep_kraus_family (kf_of_mats Ws :: ('a ell2, 'b ell2, nat) kraus_family). g (fst E))
    = (\<Sum>W\<leftarrow>Ws. g (cblinfun_of_mat W))"
proof -
  let ?op = "\<lambda>i. cblinfun_of_mat (Ws ! i) :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2"
  let ?I = "{i. i < length Ws \<and> ?op i \<noteq> 0}"
  have inj: "inj_on (\<lambda>i. (?op i, i)) ?I" by (rule inj_onI) simp
  have "(\<Sum>E\<in>Rep_kraus_family (kf_of_mats Ws :: ('a ell2, 'b ell2, nat) kraus_family). g (fst E))
      = (\<Sum>i\<in>?I. g (?op i))"
    unfolding Rep_kf_of_mats sum.reindex[OF inj] by (simp add: comp_def)
  also have "\<dots> = (\<Sum>i<length Ws. g (?op i))"
    by (rule sum.mono_neutral_left) (use g0 in auto)
  also have "\<dots> = (\<Sum>W\<leftarrow>Ws. g (cblinfun_of_mat W))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  finally show ?thesis .
qed

subsection \<open>The three theorems\<close>

text \<open>The Kraus map of the family is the lectures' Kraus map \<^const>\<open>kraus_map_dim\<close>.\<close>

theorem kf_of_mats_apply:
  assumes \<rho>: "\<rho> \<in> carrier_mat CARD('a) CARD('a)" and Ws: "\<forall>W\<in>set Ws. W \<in> carrier_mat CARD('b) CARD('a)"
  shows "mat_of_tc (kf_apply (kf_of_mats Ws :: ('a::enum ell2, 'b::enum ell2, nat) kraus_family) (tc_of_mat \<rho>))
    = kraus_map_dim CARD('b) Ws \<rho>"
proof -
  let ?K = "kf_of_mats Ws :: ('a ell2, 'b ell2, nat) kraus_family"
  have fin: "finite (Rep_kraus_family ?K)" by (rule finite_kf_of_mats)
  have "kf_apply ?K (tc_of_mat \<rho>) = (\<Sum>E\<in>Rep_kraus_family ?K. sandwich_tc (fst E) (tc_of_mat \<rho>))"
    by (simp add: kf_apply_def fin)
  hence "from_trace_class (kf_apply ?K (tc_of_mat \<rho>))
      = (\<Sum>E\<in>Rep_kraus_family ?K. sandwich (fst E) (cblinfun_of_mat \<rho> :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2))"
    by (simp add: from_trace_class_sum from_trace_class_sandwich_tc from_tc_of_mat)
  also have "\<dots> = (\<Sum>W\<leftarrow>Ws. sandwich (cblinfun_of_mat W) (cblinfun_of_mat \<rho> :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2))"
    by (rule sum_kf_of_mats) simp
  finally have s: "from_trace_class (kf_apply ?K (tc_of_mat \<rho>))
      = (\<Sum>W\<leftarrow>Ws. sandwich (cblinfun_of_mat W) (cblinfun_of_mat \<rho> :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2))" .
  have e: "mat_of_tc (kf_apply ?K (tc_of_mat \<rho>))
      = foldr (\<lambda>W acc. mat_of_cblinfun (sandwich (cblinfun_of_mat W :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) (cblinfun_of_mat \<rho>)) + acc)
          Ws (0\<^sub>m CARD('b) CARD('b))"
    unfolding mat_of_tc_def s mat_of_cblinfun_sum_list ..
  show ?thesis
    unfolding e kraus_map_dim_def
  proof (rule foldr_cong[OF refl refl])
    fix x :: "complex Matrix.mat" and acc :: "complex Matrix.mat" assume "x \<in> set Ws"
    hence x: "x \<in> carrier_mat CARD('b) CARD('a)" using Ws by blast
    show "mat_of_cblinfun (sandwich (cblinfun_of_mat x :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) (cblinfun_of_mat \<rho>)) + acc
        = x * \<rho> * (x\<^sup>\<dagger>) + acc"
      by (simp only: mat_of_cblinfun_sandwich_of_mat[OF x \<rho>])
  qed
qed

text \<open>It is trace preserving exactly when the matrices are Kraus operators, $\sum_iW_i^*W_i=I$.\<close>

theorem kf_of_mats_trace_preserving:
  assumes Ws: "\<forall>W\<in>set Ws. W \<in> carrier_mat CARD('b) CARD('a)"
  shows "kf_trace_preserving (kf_of_mats Ws :: ('a::enum ell2, 'b::enum ell2, nat) kraus_family)
    \<longleftrightarrow> kraus_operators CARD('a) CARD('b) Ws"
proof -
  let ?K = "kf_of_mats Ws :: ('a ell2, 'b ell2, nat) kraus_family"
  have "kf_bound ?K = (\<Sum>E\<in>Rep_kraus_family ?K. (fst E)* o\<^sub>C\<^sub>L fst E)"
    unfolding kf_bound_finite[OF finite_kf_of_mats] by (simp add: case_prod_unfold)
  also have "\<dots> = (\<Sum>W\<leftarrow>Ws. (cblinfun_of_mat W :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)* o\<^sub>C\<^sub>L cblinfun_of_mat W)"
    by (rule sum_kf_of_mats) simp
  finally have kb: "kf_bound ?K = (\<Sum>W\<leftarrow>Ws. (cblinfun_of_mat W :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)* o\<^sub>C\<^sub>L cblinfun_of_mat W)" .
  have m: "mat_of_cblinfun (kf_bound ?K) = foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Ws (0\<^sub>m CARD('a) CARD('a))"
    unfolding kb mat_of_cblinfun_sum_list
  proof (rule foldr_cong[OF refl refl])
    fix x :: "complex Matrix.mat" and acc :: "complex Matrix.mat" assume "x \<in> set Ws"
    hence x: "x \<in> carrier_mat CARD('b) CARD('a)" using Ws by blast
    show "mat_of_cblinfun ((cblinfun_of_mat x :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)* o\<^sub>C\<^sub>L
        (cblinfun_of_mat x :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)) + acc = (x\<^sup>\<dagger>) * x + acc"
      by (simp only: mat_of_cblinfun_gram[OF x])
  qed
  have "kf_trace_preserving ?K \<longleftrightarrow> mat_of_cblinfun (kf_bound ?K) = mat_of_cblinfun (id_cblinfun :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2)"
    unfolding kf_trace_preserving_iff_bound_id using mat_of_cblinfun_inj by (auto dest: injD)
  also have "\<dots> \<longleftrightarrow> kraus_operators CARD('a) CARD('b) Ws"
    unfolding m mat_of_cblinfun_id kraus_operators_def using Ws by simp
  finally show ?thesis .
qed

text \<open>A map of matrices read as a map of trace-class operators.\<close>

definition tc_map :: "(complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> ('a::enum ell2, 'a ell2) trace_class \<Rightarrow> ('b::enum ell2, 'b ell2) trace_class" where
  "tc_map \<Phi> T = tc_of_mat (\<Phi> (mat_of_tc T))"

lemma tc_map_kraus:
  assumes Ws: "\<forall>W\<in>set Ws. W \<in> carrier_mat CARD('b) CARD('a)"
    and eq: "\<forall>A. A \<in> carrier_mat CARD('a) CARD('a) \<longrightarrow> \<Phi> A = kraus_map_dim CARD('b) Ws A"
  shows "(tc_map \<Phi> :: ('a::enum ell2, 'a ell2) trace_class \<Rightarrow> ('b::enum ell2, 'b ell2) trace_class)
    = kf_apply (kf_of_mats Ws)"
proof
  fix T :: "('a ell2, 'a ell2) trace_class"
  have c: "mat_of_tc T \<in> carrier_mat CARD('a) CARD('a)" by (rule mat_of_tc_carrier)
  have "tc_map \<Phi> T = tc_of_mat (kraus_map_dim CARD('b) Ws (mat_of_tc T))" using eq c by (simp add: tc_map_def)
  also have "\<dots> = tc_of_mat (mat_of_tc (kf_apply (kf_of_mats Ws :: ('a ell2, 'b ell2, nat) kraus_family) (tc_of_mat (mat_of_tc T))))"
    by (simp only: kf_of_mats_apply[OF c Ws])
  also have "\<dots> = kf_apply (kf_of_mats Ws :: ('a ell2, 'b ell2, nat) kraus_family) T" by (simp only: tc_of_mat_of_tc)
  finally show "tc_map \<Phi> T = kf_apply (kf_of_mats Ws :: ('a ell2, 'b ell2, nat) kraus_family) T" .
qed

text \<open>Every completely positive map of the lectures (Paulsen's definition, Lecture 17) is a Kraus
map of the AFP, and every completely positive trace-preserving one a trace-preserving Kraus map.\<close>

theorem cp_kraus_map:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat CARD('a) CARD('a) \<Longrightarrow> B \<in> carrier_mat CARD('a) CARD('a) \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult: "\<And>c A. A \<in> carrier_mat CARD('a) CARD('a) \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range: "\<forall>A. A \<in> carrier_mat CARD('a) CARD('a) \<longrightarrow> \<Phi> A \<in> carrier_mat CARD('b) CARD('b)"
      and cp: "completely_positive CARD('a) CARD('b) \<Phi>"
  shows "Kraus_Maps.kraus_map (tc_map \<Phi> :: ('a::enum ell2, 'a ell2) trace_class \<Rightarrow> ('b::enum ell2, 'b ell2) trace_class)"
proof -
  have n: "CARD('a) > 0" and d: "CARD('b) > 0" by simp_all
  obtain Ws where Ws: "\<forall>W\<in>set Ws. W \<in> carrier_mat CARD('b) CARD('a)"
    and eq: "\<forall>A. A \<in> carrier_mat CARD('a) CARD('a) \<longrightarrow> \<Phi> A = kraus_map_dim CARD('b) Ws A"
    using kraus_rep_of_psd_choi[OF linear smult range n d choi_psd_if_cp[OF n d cp]] by blast
  show ?thesis
    unfolding Kraus_Maps.kraus_map_def tc_map_kraus[OF Ws eq] by blast
qed

theorem cptp_trace_preserving_kraus_map:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat CARD('a) CARD('a) \<Longrightarrow> B \<in> carrier_mat CARD('a) CARD('a) \<Longrightarrow>
                   \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult: "\<And>c A. A \<in> carrier_mat CARD('a) CARD('a) \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range: "\<forall>A. A \<in> carrier_mat CARD('a) CARD('a) \<longrightarrow> \<Phi> A \<in> carrier_mat CARD('b) CARD('b)"
      and cp: "completely_positive CARD('a) CARD('b) \<Phi>" and tp: "trace_preserving CARD('a) \<Phi>"
  shows "km_trace_preserving (tc_map \<Phi> :: ('a::enum ell2, 'a ell2) trace_class \<Rightarrow> ('b::enum ell2, 'b ell2) trace_class)"
proof -
  have n: "CARD('a) > 0" and d: "CARD('b) > 0" by simp_all
  obtain Ws where K: "kraus_operators CARD('a) CARD('b) Ws"
    and eq: "\<forall>A. A \<in> carrier_mat CARD('a) CARD('a) \<longrightarrow> \<Phi> A = kraus_map_dim CARD('b) Ws A"
    using choi_kraus_cptp[OF linear smult range n d] cp tp by blast
  have Ws: "\<forall>W\<in>set Ws. W \<in> carrier_mat CARD('b) CARD('a)" using K by (simp add: kraus_operators_def)
  have "kf_trace_preserving (kf_of_mats Ws :: ('a ell2, 'b ell2, nat) kraus_family)"
    using kf_of_mats_trace_preserving[OF Ws] K by simp
  thus ?thesis unfolding tc_map_kraus[OF Ws eq] by (intro km_trace_preserving_def'[THEN iffD2]) blast
qed

end
