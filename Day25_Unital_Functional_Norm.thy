(*  Title:   Day25_Unital_Functional_Norm.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 26 October 2011 (Day 25)
*)

theory Day25_Unital_Functional_Norm
  imports Day25_Arveson_Correspondence "HOL-Analysis.L2_Norm"
begin

subsection \<open>A unital functional is positive iff it has norm one (D25-4)\<close>

text \<open>Day 25 proposition (D25-4): for an operator system $S\subseteq M_n$ and a linear
$f:S\to\C$ with $f(I)=1$, $f$ is positive iff $\norm f=1$.  The operator norm is
$\norm A=\sup\{\norm{Av}:\norm v\le1\}$ and, as in the notes, $\norm f$ is defined for bounded $f$.
The proof differs from the notes in one step: for $P\ge0$ the bound
$\norm{P-sI+itI}^2\le s^2+t^2$ ($s=\norm P/2$) comes from $P^2\le\norm P\,P$, which uses the
square root of $P$, instead of from the spectrum of $P$.  Cauchy--Schwarz is
\<open>cauchy_schwarz_ineq\<close> of Isabelle\_Marries\_Dirac.\<close>

definition op_norm :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where
  "op_norm n A = Sup {\<parallel>A *\<^sub>v v\<parallel> | v. dim_vec v = n \<and> \<parallel>v\<parallel> \<le> 1}"

definition fun_norm :: "nat \<Rightarrow> complex Matrix.mat set \<Rightarrow> (complex Matrix.mat \<Rightarrow> complex) \<Rightarrow> real" where
  "fun_norm n TS f = Sup {cmod (f A) | A. A \<in> TS \<and> op_norm n A \<le> 1}"

subsubsection \<open>Vectors\<close>

lemma cauchy_schwarz_norm:
  assumes "dim_vec v = dim_vec w"
  shows "cmod \<langle>v|w\<rangle> \<le> \<parallel>v\<parallel> * \<parallel>w\<parallel>"
proof -
  have "(cmod \<langle>v|w\<rangle>)\<^sup>2 \<le> Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)" by (rule cauchy_schwarz_ineq[OF assms])
  also have "Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>) = (\<parallel>v\<parallel> * \<parallel>w\<parallel>)\<^sup>2"
  proof -
    have "\<langle>v|v\<rangle> * \<langle>w|w\<rangle> = complex_of_real (\<parallel>v\<parallel>\<^sup>2 * \<parallel>w\<parallel>\<^sup>2)"
      unfolding cpx_vec_length_inner_prod[symmetric] by (simp del: cpx_vec_length_inner_prod)
    thus ?thesis by (simp del: cpx_vec_length_inner_prod add: power_mult_distrib)
  qed
  finally show ?thesis using cpx_vec_length_nonneg[of v] cpx_vec_length_nonneg[of w]
    by (meson power2_le_imp_le zero_le_mult_iff)
qed

lemma inner_add_smult_expand:
  assumes "dim_vec u = dim_vec x"
  shows "\<langle>u + z \<cdot>\<^sub>v x | u + z \<cdot>\<^sub>v x\<rangle> = \<langle>u|u\<rangle> + z * \<langle>u|x\<rangle> + cnj z * \<langle>x|u\<rangle> + cnj z * z * \<langle>x|x\<rangle>"
  unfolding inner_prod_def using assms
  by (simp add: sum.distrib sum_distrib_left algebra_simps)

lemma entry_le_vnorm: "i < dim_vec v \<Longrightarrow> cmod (v $ i) \<le> \<parallel>v\<parallel>"
proof -
  assume i: "i < dim_vec v"
  have "(cmod (v $ i))\<^sup>2 \<le> (\<Sum>j<dim_vec v. (cmod (v $ j))\<^sup>2)" by (rule member_le_sum) (use i in auto)
  thus ?thesis unfolding cpx_vec_length_def by (rule real_le_rsqrt)
qed

lemma vnorm_le_sum: "\<parallel>w\<parallel> \<le> (\<Sum>i<dim_vec w. cmod (w $ i))"
  using L2_set_le_sum[of "{..<dim_vec w}" "\<lambda>i. cmod (w $ i)"]
  unfolding cpx_vec_length_def L2_set_def by simp

lemma vnorm_zero_iff: "dim_vec v = n \<Longrightarrow> \<parallel>v\<parallel> = 0 \<longleftrightarrow> v = 0\<^sub>v n"
  using cpx_vec_length_zero_iff[of v] by auto

subsubsection \<open>The operator norm\<close>

text \<open>The operator norm $\norm A=\sup\{\norm{Av}:\norm v\le1\}$ is finite because
$\norm{Av}\le\bigl(\sum_{i,k}|a_{ik}|\bigr)\norm v$.  It satisfies $\norm{Av}\le\norm A\,\norm v$,
$\norm I=1$ and $\norm{cA}\le|c|\,\norm A$, and vanishes only at $A=0$.\<close>

lemma mult_vec_norm_bound:
  assumes A: "A \<in> carrier_mat n n" and v: "dim_vec v = n"
  shows "\<parallel>A *\<^sub>v v\<parallel> \<le> (\<Sum>i<n. \<Sum>k<n. cmod (A $$ (i,k))) * \<parallel>v\<parallel>"
proof -
  have e: "cmod ((A *\<^sub>v v) $ i) \<le> (\<Sum>k<n. cmod (A $$ (i,k))) * \<parallel>v\<parallel>" if i: "i < n" for i
  proof -
    have "(A *\<^sub>v v) $ i = (\<Sum>k<n. A $$ (i,k) * v $ k)"
      using A v i by (simp add: scalar_prod_def atLeast0LessThan)
    hence "cmod ((A *\<^sub>v v) $ i) \<le> (\<Sum>k<n. cmod (A $$ (i,k) * v $ k))" by (simp add: sum_norm_le)
    also have "\<dots> \<le> (\<Sum>k<n. cmod (A $$ (i,k)) * \<parallel>v\<parallel>)"
      by (intro sum_mono) (use v entry_le_vnorm in \<open>auto simp: norm_mult intro: mult_left_mono\<close>)
    finally show ?thesis by (simp add: sum_distrib_right)
  qed
  have "\<parallel>A *\<^sub>v v\<parallel> \<le> (\<Sum>i<n. cmod ((A *\<^sub>v v) $ i))" using vnorm_le_sum[of "A *\<^sub>v v"] A by simp
  also have "\<dots> \<le> (\<Sum>i<n. (\<Sum>k<n. cmod (A $$ (i,k))) * \<parallel>v\<parallel>)" by (intro sum_mono e) simp
  finally show ?thesis by (simp add: sum_distrib_right)
qed

lemma op_norm_bdd:
  assumes A: "A \<in> carrier_mat n n"
  shows "bdd_above {\<parallel>A *\<^sub>v v\<parallel> | v. dim_vec v = n \<and> \<parallel>v\<parallel> \<le> 1}"
proof (rule bdd_aboveI)
  let ?C = "\<Sum>i<n. \<Sum>k<n. cmod (A $$ (i,k))"
  fix x assume "x \<in> {\<parallel>A *\<^sub>v v\<parallel> | v. dim_vec v = n \<and> \<parallel>v\<parallel> \<le> 1}"
  then obtain v where v: "dim_vec v = n" "\<parallel>v\<parallel> \<le> 1" and x: "x = \<parallel>A *\<^sub>v v\<parallel>" by blast
  have "?C \<ge> 0" by (simp add: sum_nonneg)
  hence "?C * \<parallel>v\<parallel> \<le> ?C" using v(2) by (simp add: mult_left_le)
  thus "x \<le> ?C" using mult_vec_norm_bound[OF A v(1)] x by simp
qed

lemma mult_zero_vec': "A \<in> carrier_mat n n \<Longrightarrow> A *\<^sub>v 0\<^sub>v n = 0\<^sub>v n"
  by (rule eq_vecI) (auto simp: scalar_prod_def)

lemma op_norm_ge:
  assumes A: "A \<in> carrier_mat n n" and v: "dim_vec v = n" "\<parallel>v\<parallel> \<le> 1"
  shows "\<parallel>A *\<^sub>v v\<parallel> \<le> op_norm n A"
  unfolding op_norm_def by (rule cSup_upper[OF _ op_norm_bdd[OF A]]) (use v in blast)

lemma op_norm_nonneg:
  assumes A: "A \<in> carrier_mat n n"
  shows "0 \<le> op_norm n A"
proof -
  have "\<parallel>A *\<^sub>v 0\<^sub>v n\<parallel> \<le> op_norm n A" by (rule op_norm_ge[OF A]) (simp_all add: cpx_vec_length_def)
  thus ?thesis using mult_zero_vec'[OF A] by (simp add: cpx_vec_length_def)
qed

lemma op_norm_mult:
  assumes A: "A \<in> carrier_mat n n" and v: "dim_vec v = n"
  shows "\<parallel>A *\<^sub>v v\<parallel> \<le> op_norm n A * \<parallel>v\<parallel>"
proof (cases "\<parallel>v\<parallel> = 0")
  case True
  hence "v = 0\<^sub>v n" using vnorm_zero_iff[OF v] by simp
  thus ?thesis using mult_zero_vec'[OF A] True by (simp add: cpx_vec_length_def)
next
  case False
  hence pos: "\<parallel>v\<parallel> > 0" using cpx_vec_length_nonneg[of v] by simp
  let ?u = "complex_of_real (1 / \<parallel>v\<parallel>) \<cdot>\<^sub>v v"
  have u: "dim_vec ?u = n" "\<parallel>?u\<parallel> \<le> 1" using v pos by (simp_all add: cpx_vec_length_smult norm_divide)
  have "A *\<^sub>v ?u = complex_of_real (1 / \<parallel>v\<parallel>) \<cdot>\<^sub>v (A *\<^sub>v v)"
    using mult_mat_vec[OF A carrier_vecI[OF v]] by simp
  hence "\<parallel>A *\<^sub>v ?u\<parallel> = \<parallel>A *\<^sub>v v\<parallel> / \<parallel>v\<parallel>" using pos by (simp add: cpx_vec_length_smult norm_divide)
  hence "\<parallel>A *\<^sub>v v\<parallel> / \<parallel>v\<parallel> \<le> op_norm n A" using op_norm_ge[OF A u] by simp
  thus ?thesis using pos by (simp add: divide_le_eq)
qed

lemma op_norm_le:
  assumes A: "A \<in> carrier_mat n n" and c: "0 \<le> c" and b: "\<And>v. dim_vec v = n \<Longrightarrow> \<parallel>A *\<^sub>v v\<parallel> \<le> c * \<parallel>v\<parallel>"
  shows "op_norm n A \<le> c"
  unfolding op_norm_def
proof (rule cSup_least)
  show "{\<parallel>A *\<^sub>v v\<parallel> | v. dim_vec v = n \<and> \<parallel>v\<parallel> \<le> 1} \<noteq> {}"
    by (rule ccontr) (auto simp: cpx_vec_length_def dest: spec[of _ "0\<^sub>v n"])
  fix x assume "x \<in> {\<parallel>A *\<^sub>v v\<parallel> | v. dim_vec v = n \<and> \<parallel>v\<parallel> \<le> 1}"
  then obtain v where v: "dim_vec v = n" "\<parallel>v\<parallel> \<le> 1" and x: "x = \<parallel>A *\<^sub>v v\<parallel>" by blast
  have "c * \<parallel>v\<parallel> \<le> c" using c v(2) by (simp add: mult_left_le)
  thus "x \<le> c" using b[OF v(1)] x by simp
qed

lemma op_norm_one:
  assumes n: "0 < n"
  shows "op_norm n (1\<^sub>m n) = 1"
proof (rule antisym)
  show "op_norm n (1\<^sub>m n) \<le> 1" by (rule op_norm_le) (auto intro: carrier_vecI)
  have u: "dim_vec (unit_vec n 0) = n" "\<parallel>unit_vec n 0\<parallel> = 1"
    by (simp, simp add: n)
  have "\<parallel>1\<^sub>m n *\<^sub>v unit_vec n 0\<parallel> \<le> op_norm n (1\<^sub>m n)" by (rule op_norm_ge) (use u in simp_all)
  thus "1 \<le> op_norm n (1\<^sub>m n)" using u by simp
qed

lemma op_norm_smult_le:
  assumes A: "A \<in> carrier_mat n n"
  shows "op_norm n (c \<cdot>\<^sub>m A) \<le> cmod c * op_norm n A"
proof (rule op_norm_le)
  show "c \<cdot>\<^sub>m A \<in> carrier_mat n n" using A by simp
  show "0 \<le> cmod c * op_norm n A" using op_norm_nonneg[OF A] by simp
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = n"
  have "\<parallel>(c \<cdot>\<^sub>m A) *\<^sub>v v\<parallel> = cmod c * \<parallel>A *\<^sub>v v\<parallel>" by (simp add: smult_mat_mult_vec[OF A carrier_vecI[OF v]] cpx_vec_length_smult)
  also have "\<dots> \<le> cmod c * (op_norm n A * \<parallel>v\<parallel>)" by (intro mult_left_mono op_norm_mult[OF A v]) simp
  finally show "\<parallel>(c \<cdot>\<^sub>m A) *\<^sub>v v\<parallel> \<le> cmod c * op_norm n A * \<parallel>v\<parallel>" by (simp add: mult.assoc)
qed

lemma op_norm_zero_imp:
  assumes A: "A \<in> carrier_mat n n" and z: "op_norm n A = 0"
  shows "A = 0\<^sub>m n n"
proof (rule eq_matI)
  fix i j assume "i < dim_row (0\<^sub>m n n :: complex Matrix.mat)" "j < dim_col (0\<^sub>m n n :: complex Matrix.mat)"
  hence i: "i < n" and j: "j < n" by simp_all
  have "\<parallel>A *\<^sub>v unit_vec n j\<parallel> \<le> 0" using op_norm_mult[OF A, of "unit_vec n j"] z by simp
  hence "A *\<^sub>v unit_vec n j = 0\<^sub>v n" using vnorm_zero_iff[of "A *\<^sub>v unit_vec n j" n] cpx_vec_length_nonneg A
    by (simp add: dual_order.antisym)
  hence "(A *\<^sub>v unit_vec n j) $ i = 0" using i by simp
  thus "A $$ (i,j) = 0\<^sub>m n n $$ (i,j)" using A i j by simp
qed (use A in auto)

subsubsection \<open>Unital functionals\<close>

context
  fixes n :: nat and TS :: "complex Matrix.mat set" and f :: "complex Matrix.mat \<Rightarrow> complex"
  assumes OS: "operator_system n TS" and L: "lin_fun_on TS f" and f1: "f (1\<^sub>m n) = 1"
begin

lemma TSc: "A \<in> TS \<Longrightarrow> A \<in> carrier_mat n n" using operator_systemD(1)[OF OS] by blast

lemma lin2: "A \<in> TS \<Longrightarrow> B \<in> TS \<Longrightarrow> f (a \<cdot>\<^sub>m A + b \<cdot>\<^sub>m B) = a * f A + b * f B"
  using L operator_systemD(5)[OF OS] unfolding lin_fun_on_def by simp

lemma comb_in: "A \<in> TS \<Longrightarrow> B \<in> TS \<Longrightarrow> a \<cdot>\<^sub>m A + b \<cdot>\<^sub>m B \<in> TS"
  using operator_systemD(4,5)[OF OS] by blast

lemma f_zero: "f (0\<^sub>m n n) = 0"
proof -
  have "f (0 \<cdot>\<^sub>m 1\<^sub>m n) = 0 * f (1\<^sub>m n)" using L operator_systemD(2)[OF OS] unfolding lin_fun_on_def by blast
  moreover have "(0::complex) \<cdot>\<^sub>m 1\<^sub>m n = 0\<^sub>m n n" by (rule eq_matI) simp_all
  ultimately show ?thesis by simp
qed

text \<open>A Hermitian $A\in S$ with $|\Re\langle x|Ax\rangle|\le c\norm x^2$ satisfies
$cI\pm A\ge0$, so a positive $f$ has $f(A)$ real with $|f(A)|\le c$.\<close>

lemma herm_bound:
  assumes pos: "positive_fun_on TS f" and A: "A \<in> TS" "hermitian A" and c: "0 \<le> c"
      and b: "\<And>x. dim_vec x = n \<Longrightarrow> \<bar>Re \<langle>x|A *\<^sub>v x\<rangle>\<bar> \<le> c * \<parallel>x\<parallel>\<^sup>2"
  shows "Im (f A) = 0" and "\<bar>Re (f A)\<bar> \<le> c"
proof -
  have Ac: "A \<in> carrier_mat n n" by (rule TSc[OF A(1)])
  have I: "1\<^sub>m n \<in> TS" by (rule operator_systemD(2)[OF OS])
  have ps: "psd (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A)" if e: "e = 1 \<or> e = -1" for e :: complex
    unfolding psd_def
  proof (intro conjI allI impI)
    have eA: "hermitian (e \<cdot>\<^sub>m A)"
      using e hermitian_real_scale[OF A(2) Ac, of 1] hermitian_real_scale[OF A(2) Ac, of "-1"] by auto
    show "hermitian (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A)"
      by (rule hermitian_plus[OF hermitian_real_scale[OF hermitian_identity one_carrier_mat] eA])
         (rule smult_carrier_mat one_carrier_mat Ac)+
    fix x :: "complex Matrix.vec" assume "dim_vec x = dim_row (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A)"
    hence x: "dim_vec x = n"
      using Ac by auto 
    have xc: "x \<in> carrier_vec n" by (rule carrier_vecI[OF x])
    have Mx: "(complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A) *\<^sub>v x = complex_of_real c \<cdot>\<^sub>v x + e \<cdot>\<^sub>v (A *\<^sub>v x)"
      unfolding add_mult_distrib_mat_vec[OF smult_carrier_mat[OF one_carrier_mat] smult_carrier_mat[OF Ac] xc]
                smult_mat_mult_vec[OF one_carrier_mat xc] smult_mat_mult_vec[OF Ac xc] one_mult_mat_vec[OF xc] ..
    have dd: "dim_vec (complex_of_real c \<cdot>\<^sub>v x) = dim_vec (e \<cdot>\<^sub>v (A *\<^sub>v x))" using Ac x by simp
    have "\<langle>x|(complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A) *\<^sub>v x\<rangle> = complex_of_real c * \<langle>x|x\<rangle> + e * \<langle>x|A *\<^sub>v x\<rangle>"
      unfolding Mx inner_prod_right_add'[OF dd] inner_prod_right_smult' ..
    hence "Re \<langle>x|(complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A) *\<^sub>v x\<rangle> = c * \<parallel>x\<parallel>\<^sup>2 + Re e * Re \<langle>x|A *\<^sub>v x\<rangle> - Im e * Im \<langle>x|A *\<^sub>v x\<rangle>"
      unfolding cpx_vec_length_inner_prod[symmetric] by (simp del: cpx_vec_length_inner_prod)
    also have "\<dots> = c * \<parallel>x\<parallel>\<^sup>2 + Re e * Re \<langle>x|A *\<^sub>v x\<rangle>" using e by auto
    finally show "0 \<le> Re \<langle>x|(complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + e \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>" using b[OF x] e by auto
  qed
  have p1: "0 \<le> f (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + 1 \<cdot>\<^sub>m A)" and p2: "0 \<le> f (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + (-1) \<cdot>\<^sub>m A)"
    using pos ps comb_in[OF I A(1)] unfolding positive_fun_on_def by blast+
  have "f (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + 1 \<cdot>\<^sub>m A) = complex_of_real c + f A"
       "f (complex_of_real c \<cdot>\<^sub>m 1\<^sub>m n + (-1) \<cdot>\<^sub>m A) = complex_of_real c - f A"
    using lin2[OF I A(1)] f1 by simp_all
  hence "0 \<le> complex_of_real c + f A" "0 \<le> complex_of_real c - f A" using p1 p2 by simp_all
  thus "Im (f A) = 0" "\<bar>Re (f A)\<bar> \<le> c" by (auto simp: less_eq_complex_def)
qed

lemma adjoint_inner:
  assumes A: "A \<in> carrier_mat n n" and x: "dim_vec x = n"
  shows "\<langle>x|A\<^sup>\<dagger> *\<^sub>v x\<rangle> = cnj \<langle>x|A *\<^sub>v x\<rangle>"
proof -
  have "\<langle>x|A\<^sup>\<dagger> *\<^sub>v x\<rangle> = \<langle>(A\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x|x\<rangle>"
    by (rule inner_prod_adjoint_swap[OF dagger_carrier[OF A] x x])
  also have "\<dots> = \<langle>A *\<^sub>v x|x\<rangle>" by (simp add: dagger_of_dagger_is_id)
  also have "\<dots> = cnj \<langle>x|A *\<^sub>v x\<rangle>" by (rule inner_prod_cnj) (use A x in simp)
  finally show ?thesis .
qed

text \<open>$(\Rightarrow)$: a positive unital $f$ has $|f(A)|\le\norm A$.\<close>

lemma positive_imp_bound:
  assumes pos: "positive_fun_on TS f" and A: "A \<in> TS"
  shows "cmod (f A) \<le> op_norm n A"
proof (cases "f A = 0")
  case True thus ?thesis using op_norm_nonneg[OF TSc[OF A]] by simp
next
  case False
  let ?r = "op_norm n A" and ?w = "cnj (f A) / complex_of_real (cmod (f A))"
  have Ac: "A \<in> carrier_mat n n" by (rule TSc[OF A])
  have w1: "cmod ?w = 1" using False by (simp add: norm_divide)
  have wf: "?w * f A = complex_of_real (cmod (f A))"
    using False by (simp add: complex_norm_square[symmetric] power2_eq_square field_simps mult.commute)
  define Y where "Y = ?w \<cdot>\<^sub>m A"
  have Y: "Y \<in> TS" unfolding Y_def by (rule operator_systemD(5)[OF OS A])
  have Yc: "Y \<in> carrier_mat n n" by (rule TSc[OF Y])
  have Yd: "Y\<^sup>\<dagger> \<in> TS" by (rule operator_systemD(3)[OF OS Y])
  have fY: "f Y = complex_of_real (cmod (f A))"
    using L A operator_systemD(5)[OF OS] wf unfolding Y_def lin_fun_on_def by simp
  have Ynorm: "\<parallel>Y *\<^sub>v x\<parallel> \<le> ?r * \<parallel>x\<parallel>" if x: "dim_vec x = n" for x
  proof -
    have "\<parallel>Y *\<^sub>v x\<parallel> = cmod ?w * \<parallel>A *\<^sub>v x\<parallel>" unfolding Y_def by (simp add: smult_mat_mult_vec[OF Ac carrier_vecI[OF x]] cpx_vec_length_smult)
    thus ?thesis using op_norm_mult[OF Ac x] w1 by simp
  qed
  have zb: "cmod \<langle>x|Y *\<^sub>v x\<rangle> \<le> ?r * \<parallel>x\<parallel>\<^sup>2" if x: "dim_vec x = n" for x
  proof -
    have "cmod \<langle>x|Y *\<^sub>v x\<rangle> \<le> \<parallel>x\<parallel> * \<parallel>Y *\<^sub>v x\<parallel>" by (rule cauchy_schwarz_norm) (use Yc x in simp)
    also have "\<dots> \<le> \<parallel>x\<parallel> * (?r * \<parallel>x\<parallel>)" by (intro mult_left_mono Ynorm[OF x] cpx_vec_length_nonneg)
    finally show ?thesis by (simp add: power2_eq_square mult_ac)
  qed
  define Hm where "Hm = (1/2) \<cdot>\<^sub>m Y + (1/2) \<cdot>\<^sub>m (Y\<^sup>\<dagger>)"
  define Km where "Km = (-\<i>/2) \<cdot>\<^sub>m Y + (\<i>/2) \<cdot>\<^sub>m (Y\<^sup>\<dagger>)"
  have HK: "Hm \<in> TS" "Km \<in> TS" unfolding Hm_def Km_def by (rule comb_in[OF Y Yd])+
  have Ydc: "Y\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF Yc])
  have quad: "\<langle>x|((a \<cdot>\<^sub>m Y + b \<cdot>\<^sub>m (Y\<^sup>\<dagger>)) *\<^sub>v x)\<rangle> = a * \<langle>x|Y *\<^sub>v x\<rangle> + b * cnj \<langle>x|Y *\<^sub>v x\<rangle>"
    if x: "dim_vec x = n" for a b x
  proof -
    have xc: "x \<in> carrier_vec n" by (rule carrier_vecI[OF x])
    have Yx: "(a \<cdot>\<^sub>m Y + b \<cdot>\<^sub>m (Y\<^sup>\<dagger>)) *\<^sub>v x = a \<cdot>\<^sub>v (Y *\<^sub>v x) + b \<cdot>\<^sub>v (Y\<^sup>\<dagger> *\<^sub>v x)"
      unfolding add_mult_distrib_mat_vec[OF smult_carrier_mat[OF Yc] smult_carrier_mat[OF Ydc] xc]
                smult_mat_mult_vec[OF Yc xc] smult_mat_mult_vec[OF Ydc xc] ..
    have sw: "\<langle>x|Y\<^sup>\<dagger> *\<^sub>v x\<rangle> = cnj \<langle>x|Y *\<^sub>v x\<rangle>"
      unfolding inner_prod_adjoint_swap[OF Yc x x] by (rule inner_prod_cnj) (use Yc x in simp)
    have dd: "dim_vec (a \<cdot>\<^sub>v (Y *\<^sub>v x)) = dim_vec (b \<cdot>\<^sub>v (Y\<^sup>\<dagger> *\<^sub>v x))" using Yc Ydc by simp
    show ?thesis unfolding Yx inner_prod_right_add'[OF dd] inner_prod_right_smult' sw ..
  qed
  have Hh: "hermitian Hm" unfolding hermitian_def Hm_def
    using Yc by (auto intro!: eq_matI simp: dagger_def)
  have Kh: "hermitian Km" unfolding hermitian_def Km_def
    using Yc by (auto intro!: eq_matI simp: dagger_def)
  have Hb: "\<bar>Re \<langle>x|Hm *\<^sub>v x\<rangle>\<bar> \<le> ?r * \<parallel>x\<parallel>\<^sup>2" if x: "dim_vec x = n" for x
  proof -
    have "Re \<langle>x|Hm *\<^sub>v x\<rangle> = Re \<langle>x|Y *\<^sub>v x\<rangle>" unfolding Hm_def quad[OF x] by simp
    thus ?thesis using zb[OF x] abs_Re_le_cmod[of "\<langle>x|Y *\<^sub>v x\<rangle>"] by linarith
  qed
  have Kb: "\<bar>Re \<langle>x|Km *\<^sub>v x\<rangle>\<bar> \<le> ?r * \<parallel>x\<parallel>\<^sup>2" if x: "dim_vec x = n" for x
  proof -
    have "Re \<langle>x|Km *\<^sub>v x\<rangle> = Im \<langle>x|Y *\<^sub>v x\<rangle>" unfolding Km_def quad[OF x] by simp
    thus ?thesis using zb[OF x] abs_Im_le_cmod[of "\<langle>x|Y *\<^sub>v x\<rangle>"] by linarith
  qed
  have r0: "0 \<le> ?r" by (rule op_norm_nonneg[OF Ac])
  have fH: "Im (f Hm) = 0" "\<bar>Re (f Hm)\<bar> \<le> ?r"
    using herm_bound[OF pos HK(1) Hh r0 Hb] by simp_all
  have fK: "Im (f Km) = 0" by (rule herm_bound(1)[OF pos HK(2) Kh r0 Kb])
  have eH: "f Hm = (1/2) * f Y + (1/2) * f (Y\<^sup>\<dagger>)" 
    unfolding Hm_def by (rule lin2[OF Y Yd])
  have eK: "f Km = (-\<i>/2) * f Y + (\<i>/2) * f (Y\<^sup>\<dagger>)" 
    unfolding Km_def by (rule lin2[OF Y Yd])
  have "f (Y\<^sup>\<dagger>) = complex_of_real (cmod (f A))"
    using fH(1) fK eH eK fY by (simp add: complex_eq_iff)
  hence "f Hm = complex_of_real (cmod (f A))" using eH fY by simp
  thus ?thesis using fH(2) by simp
qed

text \<open>$(\Leftarrow)$: if $|f(A)|\le\norm A$ on $S$ then $f$ is positive.\<close>

lemma sq_le_norm_quad:
  assumes P: "P \<in> carrier_mat n n" "psd P" and x: "dim_vec x = n"
  shows "\<parallel>P *\<^sub>v x\<parallel>\<^sup>2 \<le> op_norm n P * Re \<langle>x|P *\<^sub>v x\<rangle>"
proof -
  let ?Q = "psd_sqrt P"
  have Q: "?Q \<in> carrier_mat n n" "psd ?Q" "?Q * ?Q = P" using psd_sqrt_props[OF P] by simp_all
  have Qh: "?Q\<^sup>\<dagger> = ?Q" using Q(2) unfolding psd_def hermitian_def by simp
  have xc: "x \<in> carrier_vec n" by (rule carrier_vecI[OF x])
  have qx: "dim_vec (?Q *\<^sub>v x) = n" using Q(1) by simp
  have swap: "\<langle>?Q *\<^sub>v y|z\<rangle> = \<langle>y|?Q *\<^sub>v z\<rangle>" if "dim_vec y = n" "dim_vec z = n" for y z
    using inner_prod_adjoint_swap[OF Q(1) that] Qh by simp
  have Px: "P *\<^sub>v x = ?Q *\<^sub>v (?Q *\<^sub>v x)" using assoc_mult_mat_vec[OF Q(1) Q(1) xc] Q(3) by simp
  have PQ: "?Q *\<^sub>v (P *\<^sub>v x) = P *\<^sub>v (?Q *\<^sub>v x)"
    using Px assoc_mult_mat_vec[OF Q(1) Q(1) mult_mat_vec_carrier[OF Q(1) xc]] Q(3) by simp
  have "complex_of_real (\<parallel>P *\<^sub>v x\<parallel>\<^sup>2) = \<langle>P *\<^sub>v x|P *\<^sub>v x\<rangle>" by (rule cpx_vec_length_inner_prod)
  also have "\<dots> = \<langle>?Q *\<^sub>v x|?Q *\<^sub>v (P *\<^sub>v x)\<rangle>"
    unfolding Px[symmetric, THEN sym] using swap[OF qx, of "P *\<^sub>v x"] P(1) Px qx by auto
  also have "\<dots> = \<langle>?Q *\<^sub>v x|P *\<^sub>v (?Q *\<^sub>v x)\<rangle>" unfolding PQ ..
  finally have e1: "\<parallel>P *\<^sub>v x\<parallel>\<^sup>2 = Re \<langle>?Q *\<^sub>v x|P *\<^sub>v (?Q *\<^sub>v x)\<rangle>" by (rule Re_of_real_eq)
  have "Re \<langle>?Q *\<^sub>v x|P *\<^sub>v (?Q *\<^sub>v x)\<rangle> \<le> cmod \<langle>?Q *\<^sub>v x|P *\<^sub>v (?Q *\<^sub>v x)\<rangle>" by (rule complex_Re_le_cmod)
  also have "\<dots> \<le> \<parallel>?Q *\<^sub>v x\<parallel> * \<parallel>P *\<^sub>v (?Q *\<^sub>v x)\<parallel>" by (rule cauchy_schwarz_norm) (use P(1) qx in simp)
  also have "\<dots> \<le> \<parallel>?Q *\<^sub>v x\<parallel> * (op_norm n P * \<parallel>?Q *\<^sub>v x\<parallel>)"
    by (intro mult_left_mono op_norm_mult[OF P(1) qx] cpx_vec_length_nonneg)
  also have "\<dots> = op_norm n P * \<parallel>?Q *\<^sub>v x\<parallel>\<^sup>2" by (simp add: power2_eq_square)
  also have "\<parallel>?Q *\<^sub>v x\<parallel>\<^sup>2 = Re \<langle>x|P *\<^sub>v x\<rangle>"
  proof -
    have "complex_of_real (\<parallel>?Q *\<^sub>v x\<parallel>\<^sup>2) = \<langle>?Q *\<^sub>v x|?Q *\<^sub>v x\<rangle>" by (rule cpx_vec_length_inner_prod)
    also have "\<dots> = \<langle>x|?Q *\<^sub>v (?Q *\<^sub>v x)\<rangle>" by (rule swap[OF x qx])
    finally show ?thesis unfolding Px[symmetric] by (rule Re_of_real_eq)
  qed
  finally show ?thesis using e1 by simp
qed

lemma bound_imp_positive:
  assumes n: "0 < n" and b: "\<forall>A \<in> TS. cmod (f A) \<le> op_norm n A"
  shows "positive_fun_on TS f"
  unfolding positive_fun_on_def
proof (intro ballI impI)
  fix P assume P: "P \<in> TS" and ps: "psd P"
  have Pc: "P \<in> carrier_mat n n" by (rule TSc[OF P])
  have I: "1\<^sub>m n \<in> TS" by (rule operator_systemD(2)[OF OS])
  let ?c = "op_norm n P"
  define s where "s = ?c / 2"
  have s0: "0 \<le> s" unfolding s_def using op_norm_nonneg[OF Pc] by simp
  have real: "Im \<langle>x|P *\<^sub>v x\<rangle> = 0" if x: "dim_vec x = n" for x
  proof -
    have "\<langle>x|P *\<^sub>v x\<rangle> \<in> \<real>"
      using hermitian_iff_real_quad_form[OF Pc] ps x unfolding psd_def by blast
    thus ?thesis unfolding complex_is_Real_iff .
  qed
  have key: "(Re (f P) - s)\<^sup>2 + (Im (f P) + t)\<^sup>2 \<le> s\<^sup>2 + t\<^sup>2" for t :: real
  proof -
    let ?z = "Complex (- s) t"
    define M where "M = 1 \<cdot>\<^sub>m P + ?z \<cdot>\<^sub>m 1\<^sub>m n"
    have M: "M \<in> TS" unfolding M_def by (rule comb_in[OF P I])
    have Mc: "M \<in> carrier_mat n n" by (rule TSc[OF M])
    have fM: "f M = f P + ?z" unfolding M_def using lin2[OF P I] f1 by simp
    have Mx: "\<parallel>M *\<^sub>v x\<parallel> \<le> sqrt (s\<^sup>2 + t\<^sup>2) * \<parallel>x\<parallel>" if x: "dim_vec x = n" for x
    proof -
      have xc: "x \<in> carrier_vec n" by (rule carrier_vecI[OF x])
      have e: "M *\<^sub>v x = P *\<^sub>v x + ?z \<cdot>\<^sub>v x"
        unfolding M_def using add_mult_distrib_mat_vec[OF smult_carrier_mat[OF Pc] smult_carrier_mat[OF one_carrier_mat] xc]
        by (simp add: smult_mat_mult_vec[OF Pc xc] smult_mat_mult_vec[OF one_carrier_mat xc] xc)
      have px: "\<langle>P *\<^sub>v x|x\<rangle> = \<langle>x|P *\<^sub>v x\<rangle>"
        using adjoint_inner[OF Pc x] ps inner_prod_cnj[of x "P *\<^sub>v x"] Pc x unfolding psd_def hermitian_def by simp
      define q where "q = Re \<langle>x|P *\<^sub>v x\<rangle>"
      have qc: "\<langle>x|P *\<^sub>v x\<rangle> = complex_of_real q" using real[OF x] unfolding q_def by (simp add: complex_eq_iff)
      have "complex_of_real (\<parallel>M *\<^sub>v x\<parallel>\<^sup>2) = \<langle>M *\<^sub>v x|M *\<^sub>v x\<rangle>" by (rule cpx_vec_length_inner_prod)
      also have "\<dots> = \<langle>P *\<^sub>v x|P *\<^sub>v x\<rangle> + ?z * \<langle>P *\<^sub>v x|x\<rangle> + cnj ?z * \<langle>x|P *\<^sub>v x\<rangle> + cnj ?z * ?z * \<langle>x|x\<rangle>"
        unfolding e by (rule inner_add_smult_expand) (use Pc x in simp)
      also have "\<dots> = complex_of_real (\<parallel>P *\<^sub>v x\<parallel>\<^sup>2) + (?z + cnj ?z) * complex_of_real q
                       + (cnj ?z * ?z) * complex_of_real (\<parallel>x\<parallel>\<^sup>2)"
        unfolding px qc cpx_vec_length_inner_prod[symmetric] by (simp only: distrib_right add.assoc)
      also have "?z + cnj ?z = complex_of_real (- 2 * s)" by (simp add: complex_eq_iff)
      also have "cnj ?z * ?z = complex_of_real (s\<^sup>2 + t\<^sup>2)" by (simp add: complex_eq_iff power2_eq_square)
      also have "complex_of_real (\<parallel>P *\<^sub>v x\<parallel>\<^sup>2) + complex_of_real (- 2 * s) * complex_of_real q
                   + complex_of_real (s\<^sup>2 + t\<^sup>2) * complex_of_real (\<parallel>x\<parallel>\<^sup>2)
                 = complex_of_real (\<parallel>P *\<^sub>v x\<parallel>\<^sup>2 - 2 * s * q + (s\<^sup>2 + t\<^sup>2) * \<parallel>x\<parallel>\<^sup>2)"
        by (simp only: of_real_add of_real_mult of_real_diff of_real_minus) (simp del: cpx_vec_length_inner_prod)
      finally have "\<parallel>M *\<^sub>v x\<parallel>\<^sup>2 = \<parallel>P *\<^sub>v x\<parallel>\<^sup>2 - 2 * s * q + (s\<^sup>2 + t\<^sup>2) * \<parallel>x\<parallel>\<^sup>2" unfolding of_real_eq_iff .
      also have "\<dots> \<le> (s\<^sup>2 + t\<^sup>2) * \<parallel>x\<parallel>\<^sup>2" using sq_le_norm_quad[OF Pc ps x] unfolding s_def q_def by simp
      finally have "\<parallel>M *\<^sub>v x\<parallel>\<^sup>2 \<le> (sqrt (s\<^sup>2 + t\<^sup>2) * \<parallel>x\<parallel>)\<^sup>2" by (simp add: power_mult_distrib)
      thus ?thesis
        by (rule power2_le_imp_le) (intro mult_nonneg_nonneg real_sqrt_ge_zero add_nonneg_nonneg zero_le_power2 cpx_vec_length_nonneg)
    qed
    have "op_norm n M \<le> sqrt (s\<^sup>2 + t\<^sup>2)" by (rule op_norm_le[OF Mc _ Mx]) simp_all
    hence "cmod (f P + ?z) \<le> sqrt (s\<^sup>2 + t\<^sup>2)" using b M fM by force
    hence "(cmod (f P + ?z))\<^sup>2 \<le> s\<^sup>2 + t\<^sup>2" using power_mono[of "cmod (f P + ?z)" "sqrt (s\<^sup>2 + t\<^sup>2)" 2] by simp
    moreover have "(cmod (f P + ?z))\<^sup>2 = (Re (f P) - s)\<^sup>2 + (Im (f P) + t)\<^sup>2"
      by (simp only: cmod_power2) simp
    ultimately show ?thesis by simp
  qed
  have im0: "Im (f P) = 0"
  proof (rule ccontr)
    assume b0: "Im (f P) \<noteq> 0"
    let ?t = "(s\<^sup>2 + 1 - (Re (f P) - s)\<^sup>2 - (Im (f P))\<^sup>2) / (2 * Im (f P))"
    have "(Re (f P) - s)\<^sup>2 + (Im (f P) + ?t)\<^sup>2 \<le> s\<^sup>2 + ?t\<^sup>2" by (rule key)
    moreover have "(Re (f P) - s)\<^sup>2 + (Im (f P) + ?t)\<^sup>2 = s\<^sup>2 + 1 + ?t\<^sup>2"
      using b0 by (simp add: power2_eq_square field_simps)
    ultimately show False by simp
  qed
  have "(Re (f P) - s)\<^sup>2 \<le> s\<^sup>2" using key[of 0] im0 by simp
  hence "\<bar>Re (f P) - s\<bar> \<le> s" using s0 by (simp add: power2_le_iff_abs_le)
  hence "0 \<le> Re (f P)" by simp
  thus "0 \<le> f P" using im0 by (simp add: less_eq_complex_def)
qed

lemma fun_norm_one_iff:
  assumes n: "0 < n" and bdd: "\<exists>C. \<forall>A \<in> TS. cmod (f A) \<le> C * op_norm n A"
  shows "fun_norm n TS f = 1 \<longleftrightarrow> (\<forall>A \<in> TS. cmod (f A) \<le> op_norm n A)"
proof -
  let ?S = "{cmod (f A) | A. A \<in> TS \<and> op_norm n A \<le> 1}"
  have I: "1\<^sub>m n \<in> TS" by (rule operator_systemD(2)[OF OS])
  have Iin: "1 \<in> ?S" using I op_norm_one[OF n] f1 by force
  obtain C where C: "\<forall>A \<in> TS. cmod (f A) \<le> C * op_norm n A" using bdd by blast
  have bS: "bdd_above ?S"
  proof (rule bdd_aboveI[of _ "max C 0"])
    fix x assume "x \<in> ?S"
    then obtain A where A: "A \<in> TS" "op_norm n A \<le> 1" and x: "x = cmod (f A)" by blast
    have "C * op_norm n A \<le> max C 0"
      using A(2) op_norm_nonneg[OF TSc[OF A(1)]] by (cases "C \<ge> 0") (auto simp: mult_left_le mult_nonpos_nonneg)
    thus "x \<le> max C 0" using C A(1) x by force
  qed
  show ?thesis
  proof
    assume f1n: "fun_norm n TS f = 1"
    have le1: "cmod (f A) \<le> 1" if "A \<in> TS" "op_norm n A \<le> 1" for A
    proof -
      have "cmod (f A) \<in> ?S" using that by blast
      hence "cmod (f A) \<le> Sup ?S" by (rule cSup_upper[OF _ bS])
      thus ?thesis using f1n unfolding fun_norm_def by simp
    qed
    show "\<forall>A \<in> TS. cmod (f A) \<le> op_norm n A"
    proof
      fix A assume A: "A \<in> TS"
      have Ac: "A \<in> carrier_mat n n" by (rule TSc[OF A])
      show "cmod (f A) \<le> op_norm n A"
      proof (cases "op_norm n A = 0")
        case True
        hence "A = 0\<^sub>m n n" by (rule op_norm_zero_imp[OF Ac])
        thus ?thesis using f_zero True by simp
      next
        case False
        hence r: "0 < op_norm n A" using op_norm_nonneg[OF Ac] by simp
        let ?B = "complex_of_real (1 / op_norm n A) \<cdot>\<^sub>m A"
        have B: "?B \<in> TS" by (rule operator_systemD(5)[OF OS A])
        have "op_norm n ?B \<le> cmod (complex_of_real (1 / op_norm n A)) * op_norm n A" by (rule op_norm_smult_le[OF Ac])
        also have "\<dots> = 1" using r by (simp add: norm_divide)
        finally have "cmod (f ?B) \<le> 1" by (rule le1[OF B])
        moreover have "f ?B = complex_of_real (1 / op_norm n A) * f A" using L A unfolding lin_fun_on_def by blast
        ultimately have "cmod (f A) / op_norm n A \<le> 1" using r by (simp add: norm_mult norm_divide)
        thus ?thesis using r by (simp add: divide_le_eq)
      qed
    qed
  next
    assume le: "\<forall>A \<in> TS. cmod (f A) \<le> op_norm n A"
    have "Sup ?S \<le> 1" by (rule cSup_least) (use Iin le in \<open>auto intro: order_trans\<close>)
    moreover have "1 \<le> Sup ?S" by (rule cSup_upper[OF Iin bS])
    ultimately show "fun_norm n TS f = 1" unfolding fun_norm_def by simp
  qed
qed

text \<open>D25-4.\<close>

theorem unital_positive_iff_norm_one:
  assumes n: "0 < n" and bdd: "\<exists>C. \<forall>A \<in> TS. cmod (f A) \<le> C * op_norm n A"
  shows "positive_fun_on TS f \<longleftrightarrow> fun_norm n TS f = 1"
  unfolding fun_norm_one_iff[OF n bdd]
  using positive_imp_bound bound_imp_positive[OF n] by blast

end

end
