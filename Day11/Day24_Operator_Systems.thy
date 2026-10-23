theory Day24_Operator_Systems
  imports Day17_Environment_Model
begin

section \<open>Day 24 (24 October 2011): operator systems\<close>

text \<open>Day 24: operator systems $S\subseteq M_n$ (subspaces containing $I$ and closed under
adjoints), the matrices $M_p(S)$ over them, and completely positive maps on $S$.  An element of
$M_p(M_n)$ is a $pn\times pn$ matrix whose $(a,b)$ block is \<open>block_of_mat n X a b\<close>; the
ampliation $\Phi^{(p)}$ is \<open>amplification n d p \<Phi>\<close> (Day 19).\<close>

definition operator_system :: "nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> bool" where
  "operator_system n OS \<longleftrightarrow> OS \<subseteq> carrier_mat n n \<and> 1\<^sub>m n \<in> OS \<and> (\<forall>A \<in> OS. A\<^sup>\<dagger> \<in> OS)
     \<and> (\<forall>A \<in> OS. \<forall>B \<in> OS. A + B \<in> OS) \<and> (\<forall>A \<in> OS. \<forall>c. c \<cdot>\<^sub>m A \<in> OS)"

definition Mp :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> complex Matrix.mat set" where
  "Mp p n OS = {A \<in> carrier_mat (p * n) (p * n). \<forall>a < p. \<forall>b < p. block_of_mat n A a b \<in> OS}"

definition lin_on :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "lin_on n d OS \<Phi> \<longleftrightarrow> (\<forall>A \<in> OS. \<Phi> A \<in> carrier_mat d d) \<and> (\<forall>A \<in> OS. \<forall>B \<in> OS. \<Phi> (A + B) = \<Phi> A + \<Phi> B)
     \<and> (\<forall>A \<in> OS. \<forall>c. \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A)"

definition p_positive_on :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "p_positive_on n d p OS \<Phi> \<longleftrightarrow> (\<forall>A \<in> Mp p n OS. psd A \<longrightarrow> psd (amplification n d p \<Phi> A))"

definition cp_on :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex Matrix.mat) \<Rightarrow> bool" where
  "cp_on n d OS \<Phi> \<longleftrightarrow> (\<forall>p > 0. p_positive_on n d p OS \<Phi>)"

lemma block_of_mat_dims [simp]: "dim_row (block_of_mat n A a b) = n" "dim_col (block_of_mat n A a b) = n"
  by (simp_all add: block_of_mat_def)

text \<open>An operator system is a subspace $S\subseteq M_n$ with $I\in S$ and $S^*=S$.  $M_p(S)$ consists of
the $p\times p$ block matrices with every block in $S$, and $\Phi$ is $p$-positive on $S$ if
$\Phi^{(p)}$ sends the positive elements of $M_p(S)$ to positive matrices.\<close>

lemma operator_systemD:
  assumes "operator_system n OS"
  shows "OS \<subseteq> carrier_mat n n" "1\<^sub>m n \<in> OS" "\<And>A. A \<in> OS \<Longrightarrow> A\<^sup>\<dagger> \<in> OS"
    "\<And>A B. A \<in> OS \<Longrightarrow> B \<in> OS \<Longrightarrow> A + B \<in> OS" "\<And>A c. A \<in> OS \<Longrightarrow> c \<cdot>\<^sub>m A \<in> OS"
  using assms unfolding operator_system_def by blast+

lemma operator_system_zero:
  assumes OS: "operator_system n OS"
  shows "0\<^sub>m n n \<in> OS"
proof -
  have "0 \<cdot>\<^sub>m 1\<^sub>m n \<in> OS" by (rule operator_systemD(5)[OF OS operator_systemD(2)[OF OS]])
  moreover have "0 \<cdot>\<^sub>m 1\<^sub>m n = (0\<^sub>m n n :: complex Matrix.mat)" by (rule eq_matI) simp_all
  ultimately show ?thesis by simp
qed

lemma operator_system_diff:
  assumes OS: "operator_system n OS" and A: "A \<in> OS" and B: "B \<in> OS"
  shows "A - B \<in> OS"
proof -
  have Ac: "A \<in> carrier_mat n n" and Bc: "B \<in> carrier_mat n n" using operator_systemD(1)[OF OS] A B by auto
  have "A + (-1) \<cdot>\<^sub>m B \<in> OS" by (rule operator_systemD(4)[OF OS A operator_systemD(5)[OF OS B]])
  moreover have "A + (-1) \<cdot>\<^sub>m B = A - B" using Ac Bc by (intro eq_matI) auto
  ultimately show ?thesis by simp
qed

text \<open>For $S=M_n$ these are the notions of Days 17--18:\<close>

lemma operator_system_full: "operator_system n (carrier_mat n n)"
  unfolding operator_system_def by auto

lemma Mp_full: "Mp p n (carrier_mat n n) = carrier_mat (p * n) (p * n)"
  unfolding Mp_def by auto

lemma cp_on_full: "cp_on n d (carrier_mat n n) \<Phi> \<longleftrightarrow> completely_positive n d \<Phi>"
  unfolding cp_on_def p_positive_on_def completely_positive_def p_positive_def Mp_full by blast

lemma cp_on_mono:
  assumes "cp_on n d OS \<Phi>" and "OS' \<subseteq> OS"
  shows "cp_on n d OS' \<Phi>"
  using assms unfolding cp_on_def p_positive_on_def Mp_def by blast

subsection \<open>$M_p(OS)$ is an operator system\<close>

lemma block_of_mat_add:
  assumes "A \<in> carrier_mat (p * n) (p * n)" "B \<in> carrier_mat (p * n) (p * n)" "a < p" "b < p"
  shows "block_of_mat n (A + B) a b = block_of_mat n A a b + block_of_mat n B a b"
proof (rule eq_matI)
  fix r c assume "r < dim_row (block_of_mat n A a b + block_of_mat n B a b)"
    "c < dim_col (block_of_mat n A a b + block_of_mat n B a b)"
  hence r: "r < n" and c: "c < n" by simp_all
  have "a * n + r < p * n" "b * n + c < p * n" using mult_index_lt[OF assms(3) r] mult_index_lt[OF assms(4) c] by simp_all
  thus "block_of_mat n (A + B) a b $$ (r,c) = (block_of_mat n A a b + block_of_mat n B a b) $$ (r,c)"
    using assms r c by (simp add: block_of_mat_index)
qed simp_all

lemma block_of_mat_smult:
  assumes "A \<in> carrier_mat (p * n) (p * n)" "a < p" "b < p"
  shows "block_of_mat n (k \<cdot>\<^sub>m A) a b = k \<cdot>\<^sub>m block_of_mat n A a b"
proof (rule eq_matI)
  fix r c assume "r < dim_row (k \<cdot>\<^sub>m block_of_mat n A a b)" "c < dim_col (k \<cdot>\<^sub>m block_of_mat n A a b)"
  hence r: "r < n" and c: "c < n" by simp_all
  have "a * n + r < p * n" "b * n + c < p * n" using mult_index_lt[OF assms(2) r] mult_index_lt[OF assms(3) c] by simp_all
  thus "block_of_mat n (k \<cdot>\<^sub>m A) a b $$ (r,c) = (k \<cdot>\<^sub>m block_of_mat n A a b) $$ (r,c)"
    using assms r c by (simp add: block_of_mat_index)
qed simp_all

lemma block_of_mat_dagger:
  assumes "A \<in> carrier_mat (p * n) (p * n)" "a < p" "b < p"
  shows "block_of_mat n (A\<^sup>\<dagger>) a b = (block_of_mat n A b a)\<^sup>\<dagger>"
proof (rule eq_matI)
  fix r c assume "r < dim_row ((block_of_mat n A b a)\<^sup>\<dagger>)" "c < dim_col ((block_of_mat n A b a)\<^sup>\<dagger>)"
  hence r: "r < n" and c: "c < n" by simp_all
  have "a * n + r < p * n" "b * n + c < p * n" using mult_index_lt[OF assms(2) r] mult_index_lt[OF assms(3) c] by simp_all
  thus "block_of_mat n (A\<^sup>\<dagger>) a b $$ (r,c) = ((block_of_mat n A b a)\<^sup>\<dagger>) $$ (r,c)"
    using assms r c by (simp add: block_of_mat_index dagger_def)
qed simp_all

lemma block_of_mat_one:
  assumes "a < p" "b < p"
  shows "block_of_mat n (1\<^sub>m (p * n)) a b = (if a = b then 1\<^sub>m n else 0\<^sub>m n n)"
proof (rule eq_matI)
  fix r c assume "r < dim_row (if a = b then 1\<^sub>m n else 0\<^sub>m n n :: complex Matrix.mat)"
    "c < dim_col (if a = b then 1\<^sub>m n else 0\<^sub>m n n :: complex Matrix.mat)"
  hence r: "r < n" and c: "c < n" by (simp_all split: if_splits)
  have i: "a * n + r < p * n" "b * n + c < p * n" using mult_index_lt[OF assms(1) r] mult_index_lt[OF assms(2) c] by simp_all
  have "a * n + r = b * n + c \<longleftrightarrow> a = b \<and> r = c"
    using mult_index_div_mod[OF r] mult_index_div_mod[OF c] by metis
  thus "block_of_mat n (1\<^sub>m (p * n)) a b $$ (r,c) = (if a = b then 1\<^sub>m n else 0\<^sub>m n n :: complex Matrix.mat) $$ (r,c)"
    using i r c by (simp add: block_of_mat_index)
qed (simp_all split: if_splits)

text \<open>The note of Day 24: $M_p(S)$ is again an operator system.\<close>

lemma Mp_operator_system:
  assumes OS: "operator_system n OS"
  shows "operator_system (p * n) (Mp p n OS)"
  unfolding operator_system_def
proof (intro conjI ballI allI)
  show "Mp p n OS \<subseteq> carrier_mat (p * n) (p * n)" unfolding Mp_def by blast
  show "1\<^sub>m (p * n) \<in> Mp p n OS" unfolding Mp_def
    using block_of_mat_one operator_systemD(2)[OF OS] operator_system_zero[OF OS] by simp
next
  fix A assume "A \<in> Mp p n OS"
  hence Ac: "A \<in> carrier_mat (p * n) (p * n)" and Ab: "\<And>a b. a < p \<Longrightarrow> b < p \<Longrightarrow> block_of_mat n A a b \<in> OS"
    unfolding Mp_def by blast+
  show "A\<^sup>\<dagger> \<in> Mp p n OS" unfolding Mp_def
    using Ac Ab block_of_mat_dagger[OF Ac] operator_systemD(3)[OF OS] by auto
  fix c :: complex
  show "c \<cdot>\<^sub>m A \<in> Mp p n OS" unfolding Mp_def
    using Ac Ab block_of_mat_smult[OF Ac] operator_systemD(5)[OF OS] by auto
next
  fix A B assume "A \<in> Mp p n OS" "B \<in> Mp p n OS"
  hence Ac: "A \<in> carrier_mat (p * n) (p * n)" and Ab: "\<And>a b. a < p \<Longrightarrow> b < p \<Longrightarrow> block_of_mat n A a b \<in> OS"
    and Bc: "B \<in> carrier_mat (p * n) (p * n)" and Bb: "\<And>a b. a < p \<Longrightarrow> b < p \<Longrightarrow> block_of_mat n B a b \<in> OS"
    unfolding Mp_def by blast+
  show "A + B \<in> Mp p n OS" unfolding Mp_def
    using Ac Bc Ab Bb block_of_mat_add[OF Ac Bc] operator_systemD(4)[OF OS] by auto
qed

subsection \<open>Every element is a combination of four positives\<close>

lemma herm_bound:
  assumes Hmc: "Hm \<in> carrier_mat n n" and Hmh: "hermitian Hm"
  shows "\<exists>c::real. 0 \<le> c \<and> psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n - Hm) \<and> psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + Hm)"
proof -
  obtain U :: "complex Matrix.mat" and D :: "real list"
    where Uc: "U \<in> carrier_mat n n" and Uu: "unitary U" and Dl: "length D = n"
      and spec: "(U\<^sup>\<dagger>) * Hm * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF Hmc Hmh] by blast
  define c where "c = (\<Sum>i<n. \<bar>D ! i\<bar>)"
  have c0: "0 \<le> c" unfolding c_def by (rule sum_nonneg) simp
  have cD: "\<And>i. i < n \<Longrightarrow> \<bar>D ! i\<bar> \<le> c"
    unfolding c_def by (rule member_le_sum) simp_all
  have Hme: "Hm = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF Uc Hmc Uu spec])
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using Uu Uc unfolding unitary_def by simp
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Uc])
  have dc: "diag_mat_of_real D \<in> carrier_mat n n" using Dl by (simp add: diag_mat_of_real_def mat_diag_def)
  have shift: "\<And>s::real. U * diag_mat_of_real (map (\<lambda>x. c + s * x) D) * (U\<^sup>\<dagger>)
                = complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real s \<cdot>\<^sub>m Hm"
  proof -
    fix s :: real
    have "diag_mat_of_real (map (\<lambda>x. c + s * x) D) = complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real s \<cdot>\<^sub>m diag_mat_of_real D"
      using Dl by (intro eq_matI) (auto simp: diag_mat_of_real_def mat_diag_def)
    hence "U * diag_mat_of_real (map (\<lambda>x. c + s * x) D) * (U\<^sup>\<dagger>)
           = U * (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real s \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>)" by simp
    also have "\<dots> = complex_of_real c \<cdot>\<^sub>m (U * (U\<^sup>\<dagger>)) + complex_of_real s \<cdot>\<^sub>m (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
    proof -
      have I: "complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" and sD: "complex_of_real s \<cdot>\<^sub>m diag_mat_of_real D \<in> carrier_mat n n"
        using dc by simp_all
      have "U * (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real s \<cdot>\<^sub>m diag_mat_of_real D)
            = complex_of_real c \<cdot>\<^sub>m U + complex_of_real s \<cdot>\<^sub>m (U * diag_mat_of_real D)"
        by (simp only: mult_add_distrib_mat[OF Uc I sD] mult_smult_distrib[OF Uc one_carrier_mat]
            mult_smult_distrib[OF Uc dc] right_mult_one_mat[OF Uc])
      moreover have "(complex_of_real c \<cdot>\<^sub>m U + complex_of_real s \<cdot>\<^sub>m (U * diag_mat_of_real D)) * (U\<^sup>\<dagger>)
            = complex_of_real c \<cdot>\<^sub>m (U * (U\<^sup>\<dagger>)) + complex_of_real s \<cdot>\<^sub>m (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
        by (simp only: add_mult_distrib_mat[OF smult_carrier_mat[OF Uc] smult_carrier_mat[OF mult_carrier_mat[OF Uc dc]] Ud]
            mult_smult_assoc_mat[OF Uc Ud] mult_smult_assoc_mat[OF mult_carrier_mat[OF Uc dc] Ud])
      ultimately show ?thesis by simp
    qed
    finally show "U * diag_mat_of_real (map (\<lambda>x. c + s * x) D) * (U\<^sup>\<dagger>)
                = complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real s \<cdot>\<^sub>m Hm" unfolding UUd Hme[symmetric] .
  qed
  have p: "\<And>s::real. \<bar>s\<bar> \<le> 1 \<Longrightarrow> psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real s \<cdot>\<^sub>m Hm)"
  proof -
    fix s :: real assume s: "\<bar>s\<bar> \<le> 1"
    have "\<And>i. i < n \<Longrightarrow> 0 \<le> map (\<lambda>x. c + s * x) D ! i"
    proof -
      fix i assume i: "i < n"
      have "\<bar>s\<bar> * \<bar>D ! i\<bar> \<le> \<bar>D ! i\<bar>" by (rule mult_left_le_one_le) (use s in auto)
      hence "\<bar>s * D ! i\<bar> \<le> c" using cD[OF i] by (simp add: abs_mult)
      thus "0 \<le> map (\<lambda>x. c + s * x) D ! i" using abs_le_D2[of "s * D ! i" c] i Dl by simp
    qed
    hence "psd (U * diag_mat_of_real (map (\<lambda>x. c + s * x) D) * (U\<^sup>\<dagger>))"
      by (intro psd_U_diag_Udag[OF Uc]) (simp_all add: Dl)
    thus "psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real s \<cdot>\<^sub>m Hm)" unfolding shift .
  qed
  have m: "complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real (-1) \<cdot>\<^sub>m Hm = complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n - Hm"
    using Hmc by (intro eq_matI) auto
  have pl: "complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + complex_of_real 1 \<cdot>\<^sub>m Hm = complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + Hm"
    using Hmc by (intro eq_matI) auto
  show ?thesis using c0 p[of "-1"] p[of 1] unfolding m pl by auto
qed

text \<open>Proposition (Day 24): $X=(P_1-P_2)+i(P_3-P_4)$ with $P_k\in S^+$.\<close>

proposition operator_system_four_positives:
  assumes OS: "operator_system n OS" and A: "A \<in> OS"
  shows "\<exists>P1 P2 P3 P4. P1 \<in> OS \<and> P2 \<in> OS \<and> P3 \<in> OS \<and> P4 \<in> OS \<and> psd P1 \<and> psd P2 \<and> psd P3 \<and> psd P4
           \<and> A = (P1 - P2) + \<i> \<cdot>\<^sub>m (P3 - P4)"
proof -
  have Ac: "A \<in> carrier_mat n n" using operator_systemD(1)[OF OS] A by auto
  define Hm where "Hm = (1/2) \<cdot>\<^sub>m (A + (A\<^sup>\<dagger>))"
  define Km where "Km = (-\<i>/2) \<cdot>\<^sub>m (A - (A\<^sup>\<dagger>))"
  have Ad: "A\<^sup>\<dagger> \<in> OS" by (rule operator_systemD(3)[OF OS A])
  have HmS: "Hm \<in> OS" unfolding Hm_def by (intro operator_systemD(5)[OF OS] operator_systemD(4)[OF OS A Ad])
  have KmS: "Km \<in> OS" unfolding Km_def by (intro operator_systemD(5)[OF OS] operator_system_diff[OF OS A Ad])
  have Hmc: "Hm \<in> carrier_mat n n" and Kmc: "Km \<in> carrier_mat n n" unfolding Hm_def Km_def using Ac by auto
  have Hmh: "hermitian Hm" unfolding hermitian_def Hm_def using Ac by (intro eq_matI) (auto simp: dagger_def)
  have Kmh: "hermitian Km" unfolding hermitian_def Km_def using Ac by (intro eq_matI) (auto simp: dagger_def algebra_simps)
  have AHmKm: "A = Hm + \<i> \<cdot>\<^sub>m Km" unfolding Hm_def Km_def using Ac by (intro eq_matI) (auto simp: dagger_def algebra_simps)
  have split: "\<And>M. M \<in> OS \<Longrightarrow> M \<in> carrier_mat n n \<Longrightarrow> hermitian M \<Longrightarrow>
      \<exists>Q1 Q2. Q1 \<in> OS \<and> Q2 \<in> OS \<and> psd Q1 \<and> psd Q2 \<and> M = Q1 - Q2"
  proof -
    fix M assume MS: "M \<in> OS" and Mc: "M \<in> carrier_mat n n" and Mh: "hermitian M"
    obtain c :: real where c0: "0 \<le> c" and p1: "psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n - M)"
      and p2: "psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + M)" using herm_bound[OF Mc Mh] by blast
    define Q1 where "Q1 = complex_of_real (1/2) \<cdot>\<^sub>m (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + M)"
    define Q2 where "Q2 = complex_of_real (1/2) \<cdot>\<^sub>m (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n - M)"
    have I: "complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n \<in> OS" by (rule operator_systemD(5)[OF OS operator_systemD(2)[OF OS]])
    have "Q1 \<in> OS" unfolding Q1_def by (intro operator_systemD(5)[OF OS] operator_systemD(4)[OF OS I MS])
    moreover have "Q2 \<in> OS" unfolding Q2_def by (intro operator_systemD(5)[OF OS] operator_system_diff[OF OS I MS])
    moreover have "psd Q1" unfolding Q1_def by (rule psd_smult_nonneg[OF _ p2]) (use Mc in auto)
    moreover have "psd Q2" unfolding Q2_def by (rule psd_smult_nonneg[OF _ p1]) (use Mc in auto)
    moreover have "M = Q1 - Q2" unfolding Q1_def Q2_def using Mc by (intro eq_matI) (auto simp: algebra_simps)
    ultimately show "\<exists>Q1 Q2. Q1 \<in> OS \<and> Q2 \<in> OS \<and> psd Q1 \<and> psd Q2 \<and> M = Q1 - Q2" by blast
  qed
  obtain P1 P2 where "P1 \<in> OS" "P2 \<in> OS" "psd P1" "psd P2" "Hm = P1 - P2" using split[OF HmS Hmc Hmh] by blast
  moreover obtain P3 P4 where "P3 \<in> OS" "P4 \<in> OS" "psd P3" "psd P4" "Km = P3 - P4" using split[OF KmS Kmc Kmh] by blast
  ultimately show ?thesis using AHmKm by blast
qed

end
