(*  Title:   Day04_Hermitian_Matrices.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 2 September 2011 (Day 4)
*)

theory Day04_Hermitian_Matrices
  imports Day03_Unitary_Matrices
begin

section \<open>Day 4 (2 September 2011): Hermitian matrices; positive semidefinite and positive definite matrices\<close>

subsection \<open>Hermitian matrices\<close>

text \<open>\begin{notesdef}
$H\in M_n$ is \emph{Hermitian} (self-adjoint) if $H=H^*$.
\end{notesdef}
\begin{notestheorem}
The following are equivalent: (a) $H$ is Hermitian; (b) there is a unitary $U$ with
$U^*HU=D$ diagonal with real entries; (c) $\C^n$ has an orthonormal basis of eigenvectors of
$H$ with real eigenvalues; (d) $\braket{x}{Hx}\in\R$ for all $x\in\C^n$.
\end{notestheorem}
Formally \<open>hermitian H\<close> is $H^\dagger=H$; (a)$\Rightarrow$(b) is the spectral theorem
\<open>hermitian_spectral_decomp\<close> below, (a)$\Leftrightarrow$(d) is
\<open>hermitian_iff_real_quad_form\<close>, and (c) is read off from (b): the columns of $U$ are
an orthonormal eigenbasis.  The proof of (d)$\Rightarrow$(a) needs the following lemma,
which the notes note fails over $\R$ (take $T=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$).\<close>

definition hermitian :: "complex Matrix.mat \<Rightarrow> bool" where
  "hermitian A \<equiv> A\<^sup>\<dagger> = A"


lemma hermitian_square:
  assumes "hermitian A"
  shows "dim_row A = dim_col A"
  using assms unfolding hermitian_def
  by (metis dim_row_of_dagger)

lemma hermitian_index:
  assumes "hermitian A"
      and "i < dim_row A" and "j < dim_col A"
  shows "A $$ (i,j) = cnj (A $$ (j,i))"
proof -
  have H: "A\<^sup>\<dagger> = A"
    using assms(1) by (simp add: hermitian_def)
  have sq: "dim_row A = dim_col A"
    using assms(1) by (rule hermitian_square)
  have "A $$ (i,j) = (A\<^sup>\<dagger>) $$ (i,j)"
    using H by simp
  also have "\<dots> = cnj (A $$ (j,i))"
    using assms(2,3) sq by (simp add: dagger_def)
  finally show ?thesis .
qed


text \<open>A matrix is determined by its quadratic form.  In coordinates
$\braket u{Tv}=\sum_{k,l}\overline{u_k}\,T_{kl}\,v_l$, so $\braket{e_p}{Te_q}=T_{pq}$; and with
$q(z)=\braket z{Tz}$ the polarization identity
\[ 4\braket x{Ty}=\sum_{k=0}^{3}i^{-k}\,q(x+i^ky) \]
recovers every entry from the values of $q$.  This is how $q$ real-valued forces $T=T^*$.\<close>

lemma inner_T_double_sum:
  fixes T :: "complex Matrix.mat" and u v :: "complex Matrix.vec"
  assumes T_carr: "T \<in> carrier_mat n n"
      and udim: "dim_vec u = n" and vdim: "dim_vec v = n"
  shows "\<langle>u | T *\<^sub>v v\<rangle> =
         (\<Sum>k = 0..<n. \<Sum>l = 0..<n. cnj (u $ k) * T $$ (k, l) * v $ l)"
proof -
  have "\<langle>u | T *\<^sub>v v\<rangle> = (\<Sum>k = 0..<n. cnj (u $ k) * (T *\<^sub>v v) $ k)"
    using T_carr udim by (simp add: inner_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<n. cnj (u $ k) * (Matrix.row T k \<bullet> v))"
    using T_carr by simp
  also have "\<dots> = (\<Sum>k = 0..<n.
                     cnj (u $ k) * (\<Sum>l = 0..<n. Matrix.row T k $ l * v $ l))"
    using T_carr vdim by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                     cnj (u $ k) * (Matrix.row T k $ l * v $ l))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                     cnj (u $ k) * T $$ (k, l) * v $ l)"
    using T_carr by (intro sum.cong refl) (auto simp: mult.assoc)
  finally show ?thesis .
qed


lemma inner_unit_T_unit:
  fixes T :: "complex Matrix.mat"
  assumes T_carr: "T \<in> carrier_mat n n"
      and p: "p < n" and q: "q < n"
  shows "\<langle>unit_vec n p | T *\<^sub>v unit_vec n q\<rangle> = T $$ (p, q)"
proof -
  have udim: "dim_vec (unit_vec n p :: complex Matrix.vec) = n"
    by simp
  have vdim: "dim_vec (unit_vec n q :: complex Matrix.vec) = n"
    by simp

  have "\<langle>unit_vec n p | T *\<^sub>v unit_vec n q\<rangle> =
        (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
           cnj ((unit_vec n p :: complex Matrix.vec) $ k) * T $$ (k, l) *
           (unit_vec n q :: complex Matrix.vec) $ l)"
    using inner_T_double_sum[OF T_carr udim vdim] .

  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                     (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                     (if l = q then (1 :: complex) else 0))"
    using p q by (intro sum.cong refl) auto

  also have "\<dots> = (\<Sum>k = 0..<n. (if k = p then (1 :: complex) else 0) * T $$ (k, q))"
  proof (rule sum.cong[OF refl])
    fix k
    assume k: "k \<in> {0..<n}"
    have "(\<Sum>l = 0..<n.
             (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
             (if l = q then (1 :: complex) else 0))
        = (if k = p then (1 :: complex) else 0) *
          (\<Sum>l = 0..<n. T $$ (k, l) * (if l = q then (1 :: complex) else 0))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "\<dots> = (if k = p then (1 :: complex) else 0) * T $$ (k, q)"
    proof -
      have "(\<Sum>l = 0..<n. T $$ (k, l) * (if l = q then (1 :: complex) else 0))
          = (\<Sum>l = 0..<n. (if l = q then T $$ (k, l) else 0))"
      proof (rule sum.cong[OF refl])
        fix l
        assume l: "l \<in> {0..<n}"
        show "T $$ (k, l) * (if l = q then (1 :: complex) else 0)
            = (if l = q then T $$ (k, l) else 0)"
        proof (cases "l = q")
          case True
          then show ?thesis
            by simp
        next
          case False
          then show ?thesis
            by simp
        qed
      qed
      also have "\<dots> = T $$ (k, q)"
      proof -
        have "q \<in> {0..<n}"
          using q by simp
        then show ?thesis
          by simp
      qed
      finally show ?thesis
        by argo
    qed
    finally show "(\<Sum>l = 0..<n.
                     (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                     (if l = q then (1 :: complex) else 0))
                = (if k = p then (1 :: complex) else 0) * T $$ (k, q)".
  qed
  also have "\<dots> = (\<Sum>k = 0..<n. (if k = p then T $$ (k, q) else 0))"
  proof (rule sum.cong[OF refl])
    fix k
    assume k: "k \<in> {0..<n}"
    show "(if k = p then (1 :: complex) else 0) * T $$ (k, q)
        = (if k = p then T $$ (k, q) else 0)"
    proof (cases "k = p")
      case True
      then show ?thesis
        by simp
    next
      case False
      then show ?thesis
        by simp
    qed
  qed

  also have "\<dots> = T $$ (p, q)"
  proof -
    have "p \<in> {0..<n}"
      using p by simp
    then show ?thesis
      by simp
  qed
  finally show ?thesis.
qed


lemma sum_indicator_T_indicator:
  fixes T :: "complex Matrix.mat"
  assumes p: "p < n" and q: "q < n"
  shows "(\<Sum>k = 0..<n. \<Sum>l = 0..<n.
            (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
            (if l = q then (1 :: complex) else 0))
       = T $$ (p, q)"
proof -
  have inner: "\<And>k. (\<Sum>l = 0..<n.
                (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                (if l = q then (1 :: complex) else 0))
              = (if k = p then T $$ (k, q) else 0)"
  proof -
    fix k
    show "(\<Sum>l = 0..<n.
            (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
            (if l = q then (1 :: complex) else 0))
          = (if k = p then T $$ (k, q) else 0)"
    proof (cases "k = p")
      case True
      have "(\<Sum>l = 0..<n.
              (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
              (if l = q then (1 :: complex) else 0))
            = (\<Sum>l = 0..<n. T $$ (k, l) * (if l = q then (1 :: complex) else 0))"
        using True by simp
      also have "\<dots> = (\<Sum>l = 0..<n. (if l = q then T $$ (k, l) else 0))"
        by (rule sum.cong[OF refl]) auto
      also have "\<dots> = T $$ (k, q)" using q by simp
      finally show ?thesis using True by simp
    next
      case False
      then have "\<And>l. (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                       (if l = q then (1 :: complex) else 0) = 0" by simp
      then show ?thesis using False by simp
    qed
  qed
  have "(\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                (if k = p then (1 :: complex) else 0) * T $$ (k, l) *
                (if l = q then (1 :: complex) else 0))
       = (\<Sum>k = 0..<n. (if k = p then T $$ (k, q) else 0))"
    using inner by (intro sum.cong refl)
  also have "\<dots> = T $$ (p, q)" using p by simp
  finally show ?thesis .
qed

lemma polarization_helper:
  fixes T :: "complex Matrix.mat" and a b c d :: complex
  assumes sq: "T \<in> carrier_mat n n"
      and i: "i < n" and j: "j < n"
  shows "\<langle>a \<cdot>\<^sub>v unit_vec n i + b \<cdot>\<^sub>v unit_vec n j
         | T *\<^sub>v (c \<cdot>\<^sub>v unit_vec n i + d \<cdot>\<^sub>v unit_vec n j)\<rangle>
        = cnj a * c * T $$ (i, i) + cnj a * d * T $$ (i, j)
        + cnj b * c * T $$ (j, i) + cnj b * d * T $$ (j, j)"
proof -
  let ?u = "a \<cdot>\<^sub>v unit_vec n i + b \<cdot>\<^sub>v unit_vec n j :: complex Matrix.vec"
  let ?v = "c \<cdot>\<^sub>v unit_vec n i + d \<cdot>\<^sub>v unit_vec n j :: complex Matrix.vec"
  have udim: "dim_vec ?u = n" by simp
  have vdim: "dim_vec ?v = n" by simp
  have u_cnj: "\<And>k. k < n \<Longrightarrow>
      cnj (?u $ k) = cnj a * (if k = i then 1 else 0) + cnj b * (if k = j then 1 else 0)"
    using i j by auto
  have v_idx: "\<And>l. l < n \<Longrightarrow>
      ?v $ l = c * (if l = i then 1 else 0) + d * (if l = j then 1 else 0)"
    using i j by auto

  have "\<langle>?u | T *\<^sub>v ?v\<rangle>
      = (\<Sum>k = 0..<n. \<Sum>l = 0..<n. cnj (?u $ k) * T $$ (k, l) * ?v $ l)"
    using inner_T_double_sum[OF sq udim vdim] .
  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                  (cnj a * (if k = i then 1 else 0) + cnj b * (if k = j then 1 else 0)) *
                  T $$ (k, l) *
                  (c * (if l = i then 1 else 0) + d * (if l = j then 1 else 0)))"
    using u_cnj v_idx by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                cnj a * c * ((if k = i then 1 else 0) * T $$ (k, l) * (if l = i then 1 else 0))
              + cnj a * d * ((if k = i then 1 else 0) * T $$ (k, l) * (if l = j then 1 else 0))
              + cnj b * c * ((if k = j then 1 else 0) * T $$ (k, l) * (if l = i then 1 else 0))
              + cnj b * d * ((if k = j then 1 else 0) * T $$ (k, l) * (if l = j then 1 else 0)))"
    by (intro sum.cong refl) (simp add: distrib_left distrib_right ac_simps)
  also have "\<dots> = cnj a * c * (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                                  (if k = i then 1 else 0) * T $$ (k, l) * (if l = i then 1 else 0))
              + cnj a * d * (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                                  (if k = i then 1 else 0) * T $$ (k, l) * (if l = j then 1 else 0))
              + cnj b * c * (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                                  (if k = j then 1 else 0) * T $$ (k, l) * (if l = i then 1 else 0))
              + cnj b * d * (\<Sum>k = 0..<n. \<Sum>l = 0..<n.
                                  (if k = j then 1 else 0) * T $$ (k, l) * (if l = j then 1 else 0))"
    by (simp add: sum.distrib sum_distrib_left)
  also have "\<dots> = cnj a * c * T $$ (i, i) + cnj a * d * T $$ (i, j)
              + cnj b * c * T $$ (j, i) + cnj b * d * T $$ (j, j)"
    using sum_indicator_T_indicator[OF i i, of T]
          sum_indicator_T_indicator[OF i j, of T]
          sum_indicator_T_indicator[OF j i, of T]
          sum_indicator_T_indicator[OF j j, of T]
    by simp
  finally show ?thesis .
qed



text \<open>\begin{noteslemma}
For $T\in M_n$, if $\braket{x}{Tx}=0$ for all $x\in\C^n$, then $T=0$.
\end{noteslemma}\<close>

lemma quadratic_form_zero:
  fixes T :: "complex Matrix.mat"
  assumes sq: "T \<in> carrier_mat n n"
      and zero: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | T *\<^sub>v x\<rangle> = 0"
  shows "T = 0\<^sub>m n n"
proof (rule eq_matI)
  show "dim_row T = dim_row (0\<^sub>m n n)" using sq by simp
  show "dim_col T = dim_col (0\<^sub>m n n)" using sq by simp
next
  fix i j
  assume "i < dim_row (0\<^sub>m n n)" "j < dim_col (0\<^sub>m n n)"
  then have inb: "i < n" "j < n" using sq by simp_all

  let ?ei = "unit_vec n i :: complex Matrix.vec"
  let ?ej = "unit_vec n j :: complex Matrix.vec"

  have ei_dim: "dim_vec ?ei = n" by simp
  have ej_dim: "dim_vec ?ej = n" by simp
  have eiej_dim: "dim_vec (?ei + ?ej) = n" by simp
  have eiiej_dim: "dim_vec (?ei + \<i> \<cdot>\<^sub>v ?ej) = n" by simp

  have diag_i: "T $$ (i, i) = 0"
    using zero[rule_format, of ?ei] inner_unit_T_unit[OF sq inb(1) inb(1)] ei_dim by simp
  have diag_j: "T $$ (j, j) = 0"
    using zero[rule_format, of ?ej] inner_unit_T_unit[OF sq inb(2) inb(2)] ej_dim by simp

  have q_sum_zero: "\<langle>?ei + ?ej | T *\<^sub>v (?ei + ?ej)\<rangle> = 0"
    using zero[rule_format, of "?ei + ?ej"] eiej_dim by simp
  have q_isum_zero: "\<langle>?ei + \<i> \<cdot>\<^sub>v ?ej | T *\<^sub>v (?ei + \<i> \<cdot>\<^sub>v ?ej)\<rangle> = 0"
    using zero[rule_format, of "?ei + \<i> \<cdot>\<^sub>v ?ej"] eiiej_dim by simp

  (* Real polarization: scalars (1,1,1,1).  Note 1\<cdot>v = v, so
     \<langle>?ei + ?ej | T (?ei + ?ej)\<rangle> = \<langle>1\<cdot>?ei + 1\<cdot>?ej | T (1\<cdot>?ei + 1\<cdot>?ej)\<rangle>. *)
  have sum_expand: "\<langle>?ei + ?ej | T *\<^sub>v (?ei + ?ej)\<rangle>
                  = T $$ (i, i) + T $$ (i, j) + T $$ (j, i) + T $$ (j, j)"
    using polarization_helper[OF sq inb(1) inb(2), of 1 1 1 1] by simp

  have sum_eq: "T $$ (i, j) + T $$ (j, i) = 0"
    using q_sum_zero sum_expand diag_i diag_j by simp

  (* Imaginary polarization: scalars (1, \<i>, 1, \<i>). *)
  have isum_expand: "\<langle>?ei + \<i> \<cdot>\<^sub>v ?ej | T *\<^sub>v (?ei + \<i> \<cdot>\<^sub>v ?ej)\<rangle>
                   = T $$ (i, i) + \<i> * T $$ (i, j) - \<i> * T $$ (j, i) + T $$ (j, j)"
    using polarization_helper[OF sq inb(1) inb(2), of 1 \<i> 1 \<i>] by simp

  have diff_eq: "T $$ (i, j) - T $$ (j, i) = 0"
    using q_isum_zero isum_expand diag_i diag_j by (simp add: field_simps)

  have "2 * T $$ (i, j) = 0"
    using sum_eq diff_eq by (simp add: algebra_simps)
  hence "T $$ (i, j) = 0" by simp
  thus "T $$ (i, j) = 0\<^sub>m n n $$ (i, j)" using inb by simp
qed

lemma mult_mat_vec_index:
  fixes A :: "'a::{comm_ring_1} Matrix.mat"
    and x :: "'a Matrix.vec"
  assumes A: "A \<in> carrier_mat m n"
      and x: "x \<in> carrier_vec n"
      and j: "j < m"
  shows "(A *\<^sub>v x) $ j = (\<Sum>i = 0..<n. A $$ (j, i) * x $ i)"
proof -
  have step1: "A *\<^sub>v x = Matrix.vec (dim_row A) (\<lambda>r. Matrix.row A r \<bullet> x)"
    unfolding mult_mat_vec_def
    by simp
  have step2: "(A *\<^sub>v x) $ j = (Matrix.vec (dim_row A) (\<lambda>r. Matrix.row A r \<bullet> x)) $ j"
    using step1 by simp
  have step3: "(Matrix.vec (dim_row A) (\<lambda>r. Matrix.row A r \<bullet> x)) $ j = Matrix.row A j \<bullet> x"
    using A j
    by simp
  have step4: "Matrix.row A j \<bullet> x = (\<Sum>i = 0..<dim_vec x. Matrix.row A j $ i * x $ i)"
    by (simp add: scalar_prod_def)
  have step5: "(\<Sum>i = 0..<dim_vec x. Matrix.row A j $ i * x $ i)
             = (\<Sum>i = 0..<n. Matrix.row A j $ i * x $ i)"
    using x by simp
  have step6: "(\<Sum>i = 0..<n. Matrix.row A j $ i * x $ i)
             = (\<Sum>i = 0..<n. A $$ (j, i) * x $ i)"
  proof (rule sum.cong[OF refl])
    fix i
    assume i: "i \<in> {0..<n}"
    then have "i < n"
      by simp
    moreover have "j < dim_row A"
      using A j by simp
    ultimately have "Matrix.row A j $ i = A $$ (j, i)"
      using A by auto
    then show "Matrix.row A j $ i * x $ i = A $$ (j, i) * x $ i"
      by simp
  qed

  have "(A *\<^sub>v x) $ j = Matrix.row A j \<bullet> x"
    using step2 step3 by simp
  also have "... = (\<Sum>i = 0..<dim_vec x. Matrix.row A j $ i * x $ i)"
    using step4 by simp
  also have "... = (\<Sum>i = 0..<n. Matrix.row A j $ i * x $ i)"
    using step5 by simp
  also have "... = (\<Sum>i = 0..<n. A $$ (j, i) * x $ i)"
    using step6 by simp
  finally show ?thesis.
qed

text \<open>The adjoint moves across the inner product, $\braket{x}{My}=\braket{M^\dagger x}{y}$:
the defining property of $M^\dagger$.\<close>

lemma inner_prod_adjoint_swap:
  fixes M :: "complex Matrix.mat"
    and x y :: "complex Matrix.vec"
  assumes M: "M \<in> carrier_mat n m"
      and x: "dim_vec x = n"
      and y: "dim_vec y = m"
  shows "\<langle>x | M *\<^sub>v y\<rangle> = \<langle>M\<^sup>\<dagger> *\<^sub>v x | y\<rangle>"
proof -
  have Mxy_dim: "dim_vec (M *\<^sub>v y) = n"
    using M y by auto
  have Mdag: "M\<^sup>\<dagger> \<in> carrier_mat m n"
    using M by auto
  have Mdagx_dim: "dim_vec (M\<^sup>\<dagger> *\<^sub>v x) = m"
    using Mdag x by auto

  have lhs: "\<langle>x | M *\<^sub>v y\<rangle> = (\<Sum>j = 0..<n. \<Sum>i = 0..<m. cnj (x $ j) * M $$ (j,i) * y $ i)"
  proof -
    have "\<langle>x | M *\<^sub>v y\<rangle> = (\<Sum>j = 0..<n. cnj (x $ j) * (M *\<^sub>v y) $ j)"
      using x Mxy_dim by (simp add: inner_prod_def)
    also have "\<dots> = (\<Sum>j = 0..<n. cnj (x $ j) * (\<Sum>i = 0..<m. M $$ (j,i) * y $ i))"
    proof (rule sum.cong[OF refl])
      fix j
      assume j: "j \<in> {0..<n}"
      then have jlt: "j < n" by simp
      have "(M *\<^sub>v y) $ j = (\<Sum>i = 0..<dim_col M. M $$ (j,i) * y $ i)"
        using M jlt y mult_mat_vec_index
        by (simp add: scalar_prod_def)
      also have "dim_col M = m"
        using M by simp
      finally show "cnj (x $ j) * (M *\<^sub>v y) $ j
                  = cnj (x $ j) * (\<Sum>i = 0..<m. M $$ (j,i) * y $ i)"
        by simp
    qed
    also have "\<dots> = (\<Sum>j = 0..<n. \<Sum>i = 0..<m. cnj (x $ j) * (M $$ (j,i) * y $ i))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>j = 0..<n. \<Sum>i = 0..<m. cnj (x $ j) * M $$ (j,i) * y $ i)"
      by (intro sum.cong refl, simp)     
    finally show ?thesis .
  qed
  have rhs: "\<langle>M\<^sup>\<dagger> *\<^sub>v x | y\<rangle> = (\<Sum>i = 0..<m. \<Sum>j = 0..<n. cnj (x $ j) * M $$ (j,i) * y $ i)"
  proof -
    have "\<langle>M\<^sup>\<dagger> *\<^sub>v x | y\<rangle> = (\<Sum>i = 0..<m. cnj ((M\<^sup>\<dagger> *\<^sub>v x) $ i) * y $ i)"
      using y Mdagx_dim by (simp add: inner_prod_def)
    also have "\<dots> = (\<Sum>i = 0..<m. cnj (\<Sum>j = 0..<n. (M\<^sup>\<dagger>) $$ (i,j) * x $ j) * y $ i)"
    proof (rule sum.cong[OF refl])
      fix i
      assume i: "i \<in> {0..<m}"
      then have ilt: "i < m"
        by simp
      have "(M\<^sup>\<dagger> *\<^sub>v x) $ i = (\<Sum>j = 0..<dim_col (M\<^sup>\<dagger>). (M\<^sup>\<dagger>) $$ (i,j) * x $ j)"
        using Mdag ilt x mult_mat_vec_index
        by (metis (no_types, lifting) carrier_matD(2) carrier_vec_dim_vec sum.cong)
      also have "dim_col (M\<^sup>\<dagger>) = n"
        using Mxy_dim by auto
      finally show "cnj ((M\<^sup>\<dagger> *\<^sub>v x) $ i) * y $ i
                  = cnj (\<Sum>j = 0..<n. (M\<^sup>\<dagger>) $$ (i,j) * x $ j) * y $ i"
        by simp
    qed
    also have "\<dots> = (\<Sum>i = 0..<m. (\<Sum>j = 0..<n. cnj ((M\<^sup>\<dagger>) $$ (i,j) * x $ j)) * y $ i)"
      by simp
    also have "\<dots> = (\<Sum>i = 0..<m. (\<Sum>j = 0..<n. cnj ((M\<^sup>\<dagger>) $$ (i,j)) * cnj (x $ j)) * y $ i)"
      by simp
    also have "\<dots> = (\<Sum>i = 0..<m. (\<Sum>j = 0..<n. M $$ (j,i) * cnj (x $ j)) * y $ i)"
    proof (intro sum.cong refl)
      fix i
      assume i: "i \<in> {0..<m}"
      show "(\<Sum>j = 0..<n. cnj (M\<^sup>\<dagger> $$ (i, j)) * cnj (x $ j)) * y $ i = (\<Sum>j = 0..<n. M $$ (j, i) * cnj (x $ j)) * y $ i"
        using M i by (intro arg_cong[where f = "\<lambda>s. s * y $ i"] sum.cong refl) (simp add: dagger_def)
    qed
    also have "\<dots> = (\<Sum>i = 0..<m. \<Sum>j = 0..<n. (M $$ (j,i) * cnj (x $ j)) * y $ i)"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>i = 0..<m. \<Sum>j = 0..<n. cnj (x $ j) * M $$ (j,i) * y $ i)"
      by (intro sum.cong refl, simp add: algebra_simps)
    finally show ?thesis.
  qed

  have "(\<Sum>j = 0..<n. \<Sum>i = 0..<m. cnj (x $ j) * M $$ (j,i) * y $ i)
      = (\<Sum>i = 0..<m. \<Sum>j = 0..<n. cnj (x $ j) * M $$ (j,i) * y $ i)"
    by (rule sum.swap)
  thus ?thesis
    using lhs rhs by simp
qed


text \<open>Sums and real multiples of Hermitian matrices are Hermitian; the identity is Hermitian.\<close>

lemma hermitian_plus:
  fixes A B :: "complex Matrix.mat"
  assumes Aherm: "hermitian A" and Bherm: "hermitian B"
      and Ac: "A \<in> carrier_mat k k" and Bc: "B \<in> carrier_mat k k"
  shows "hermitian (A + B)"
  unfolding hermitian_def
proof (rule eq_matI)
  show "dim_row ((A + B)\<^sup>\<dagger>) = dim_row (A + B)" using Ac Bc by simp
  show "dim_col ((A + B)\<^sup>\<dagger>) = dim_col (A + B)" using Ac Bc by simp
  fix i j assume "i < dim_row (A + B)" "j < dim_col (A + B)"
  hence i_lt: "i < k" and j_lt: "j < k" using Ac Bc by auto
  have Ad: "A\<^sup>\<dagger> = A" using Aherm by (simp add: hermitian_def)
  have Bd: "B\<^sup>\<dagger> = B" using Bherm by (simp add: hermitian_def)
  have "((A + B)\<^sup>\<dagger>) $$ (i, j) = cnj ((A + B) $$ (j, i))"
    using i_lt j_lt Ac Bc by (simp add: dagger_def)
  also have "\<dots> = cnj (A $$ (j, i)) + cnj (B $$ (j, i))" using i_lt j_lt Ac Bc by simp
  also have "\<dots> = (A\<^sup>\<dagger>) $$ (i, j) + (B\<^sup>\<dagger>) $$ (i, j)"
    using i_lt j_lt Ac Bc by (simp add: dagger_def)
  also have "\<dots> = A $$ (i, j) + B $$ (i, j)" using Ad Bd by simp
  also have "\<dots> = (A + B) $$ (i, j)" using i_lt j_lt Ac Bc by simp
  finally show "((A + B)\<^sup>\<dagger>) $$ (i, j) = (A + B) $$ (i, j)" .
qed

lemma hermitian_identity:
  "hermitian (1\<^sub>m k :: complex Matrix.mat)"
  unfolding hermitian_def by (rule eq_matI) (auto simp: dagger_def)

lemma hermitian_real_scale:
  fixes A :: "complex Matrix.mat"
  assumes "hermitian A" "A \<in> carrier_mat k k"
  shows "hermitian (complex_of_real d \<cdot>\<^sub>m A)"
  unfolding hermitian_def
proof (rule eq_matI)
  let ?dA = "complex_of_real d \<cdot>\<^sub>m A"
  show "dim_row (?dA\<^sup>\<dagger>) = dim_row ?dA" using assms by simp
  show "dim_col (?dA\<^sup>\<dagger>) = dim_col ?dA" using assms by simp
  fix i j assume "i < dim_row ?dA" "j < dim_col ?dA"
  hence i_lt: "i < k" and j_lt: "j < k" using assms by auto
  have "?dA\<^sup>\<dagger> $$ (i,j) = cnj (?dA $$ (j,i))" using i_lt j_lt assms by (simp add: dagger_def)
  also have "\<dots> = cnj (complex_of_real d * A $$ (j,i))" using i_lt j_lt assms by simp
  also have "\<dots> = complex_of_real d * cnj (A $$ (j,i))" by (simp add: complex_cnj_mult)
  also have "\<dots> = complex_of_real d * (A\<^sup>\<dagger>) $$ (i,j)" using i_lt j_lt assms by (simp add: dagger_def)
  also have "\<dots> = complex_of_real d * A $$ (i,j)" using assms by (simp add: hermitian_def)
  also have "\<dots> = ?dA $$ (i,j)" using i_lt j_lt assms by simp
  finally show "?dA\<^sup>\<dagger> $$ (i,j) = ?dA $$ (i,j)" .
qed

text \<open>The converses (g)$\Rightarrow$(a) and (h)$\Rightarrow$(a) of the Day 3 theorem on unitaries,
postponed until the lemma $\braket{x}{Tx}=0\ \forall x\Rightarrow T=0$ was available: a
square matrix that preserves lengths, or inner products, is unitary (the library proves
the length-preserving case in its own matrix notation as \<open>length_preserving_is_unitary\<close>).\<close>

lemma unitary_of_isometry:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat n n"
      and iso: "\<And>v :: complex Matrix.vec. dim_vec v = n \<Longrightarrow> \<parallel>U *\<^sub>v v\<parallel> = \<parallel>v\<parallel>"
  shows "unitary U"
proof -
  let ?T = "U\<^sup>\<dagger> * U - 1\<^sub>m n"
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" using U by auto
  have UdU: "U\<^sup>\<dagger> * U \<in> carrier_mat n n" using U Ud by auto
  have T_c: "?T \<in> carrier_mat n n" using UdU by auto
  have qf0: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | ?T *\<^sub>v x\<rangle> = 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec" assume xd: "dim_vec x = n"
    have xc: "x \<in> carrier_vec n" using xd by auto
    have Ux: "dim_vec (U *\<^sub>v x) = n" using U xd by auto
    have "\<langle>x | (U\<^sup>\<dagger> * U) *\<^sub>v x\<rangle> = \<langle>x | U\<^sup>\<dagger> *\<^sub>v (U *\<^sub>v x)\<rangle>"
      using U Ud xc by (simp add: assoc_mult_mat_vec)
    also have "\<dots> = \<langle>(U\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | U *\<^sub>v x\<rangle>"
      using inner_prod_adjoint_swap[OF Ud xd Ux] .
    also have "\<dots> = \<langle>U *\<^sub>v x | U *\<^sub>v x\<rangle>"
      by (simp add: dagger_of_dagger_is_id)
    also have "\<dots> = \<langle>x | x\<rangle>"
      by (simp only: cpx_vec_length_inner_prod[symmetric] iso[OF xd])
    finally have A: "\<langle>x | (U\<^sup>\<dagger> * U) *\<^sub>v x\<rangle> = \<langle>x | x\<rangle>" .
    have "?T *\<^sub>v x = (U\<^sup>\<dagger> * U) *\<^sub>v x - 1\<^sub>m n *\<^sub>v x"
      using UdU xc by (simp add: minus_mult_distrib_mat_vec)
    also have "\<dots> = (U\<^sup>\<dagger> * U) *\<^sub>v x - x" using xc by simp
    finally have Tx: "?T *\<^sub>v x = (U\<^sup>\<dagger> * U) *\<^sub>v x - x" .
    have dims: "dim_vec ((U\<^sup>\<dagger> * U) *\<^sub>v x) = dim_vec x" using UdU xd by auto
    have "\<langle>x | ?T *\<^sub>v x\<rangle> = \<langle>x | (U\<^sup>\<dagger> * U) *\<^sub>v x\<rangle> - \<langle>x | x\<rangle>"
      unfolding Tx by (rule inner_prod_right_minus'[OF dims])
    thus "\<langle>x | ?T *\<^sub>v x\<rangle> = 0" using A by simp
  qed
  have T0: "?T = 0\<^sub>m n n" by (rule quadratic_form_zero[OF T_c qf0])
  have UdU1: "U\<^sup>\<dagger> * U = 1\<^sub>m n"
  proof (rule eq_matI)
    show "dim_row (U\<^sup>\<dagger> * U) = dim_row (1\<^sub>m n :: complex Matrix.mat)" using UdU by auto
    show "dim_col (U\<^sup>\<dagger> * U) = dim_col (1\<^sub>m n :: complex Matrix.mat)" using UdU by auto
    fix i j assume "i < dim_row (1\<^sub>m n :: complex Matrix.mat)" "j < dim_col (1\<^sub>m n :: complex Matrix.mat)"
    hence ij: "i < n" "j < n" by auto
    have "?T $$ (i, j) = 0" using T0 ij by simp
    thus "(U\<^sup>\<dagger> * U) $$ (i, j) = (1\<^sub>m n :: complex Matrix.mat) $$ (i, j)"
      using UdU ij by simp
  qed
  have UUd1: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using mat_mult_left_right_inverse[OF Ud U UdU1] .
  show ?thesis unfolding unitary_def using UdU1 UUd1 U by auto
qed

lemma unitary_of_inner_prod_preserving:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat n n"
      and pres: "\<And>u v :: complex Matrix.vec. dim_vec u = n \<Longrightarrow> dim_vec v = n \<Longrightarrow>
                   \<langle>U *\<^sub>v u | U *\<^sub>v v\<rangle> = \<langle>u | v\<rangle>"
  shows "unitary U"
proof (rule unitary_of_isometry[OF U])
  fix v :: "complex Matrix.vec" assume vd: "dim_vec v = n"
  have "complex_of_real (\<parallel>U *\<^sub>v v\<parallel>\<^sup>2) = complex_of_real (\<parallel>v\<parallel>\<^sup>2)"
    using pres[OF vd vd] by (simp only: cpx_vec_length_inner_prod[symmetric])
  hence sq: "\<parallel>U *\<^sub>v v\<parallel>\<^sup>2 = \<parallel>v\<parallel>\<^sup>2" by (simp only: of_real_eq_iff)
  have nn: "0 \<le> \<parallel>U *\<^sub>v v\<parallel>" "0 \<le> \<parallel>v\<parallel>" by (simp_all add: cpx_vec_length_def sum_nonneg)
  show "\<parallel>U *\<^sub>v v\<parallel> = \<parallel>v\<parallel>" using sq nn by (simp add: power2_eq_iff_nonneg)
qed

lemma hermitian_iff_real_quad_form:
  assumes sq: "A \<in> carrier_mat n n"
  shows "hermitian A \<longleftrightarrow> (\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>)"
proof
  assume hA: "hermitian A"
  show "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    have xcar: "x \<in> carrier_vec n"
      by (simp add: carrier_vecI xdim)
    have "cnj \<langle>x | A *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x\<rangle>"
    proof -
      have "cnj \<langle>x | A *\<^sub>v x\<rangle> = \<langle>A *\<^sub>v x | x\<rangle>"
        by (metis carrier_matD(1) dim_mult_mat_vec inner_prod_cnj sq xdim)
      also have "... = \<langle>x | A\<^sup>\<dagger> *\<^sub>v x\<rangle>"
        using hA hermitian_def inner_prod_adjoint_swap sq xdim by auto
      also have "... = \<langle>x | A *\<^sub>v x\<rangle>"
        using hA by (simp add: hermitian_def)
      finally show ?thesis .
    qed
    then show "\<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
      using Reals_cnj_iff by blast
  qed
next
  assume qreal: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
  let ?T = "A - (A\<^sup>\<dagger>)"

  have Tcar: "?T \<in> carrier_mat n n"
    using sq by auto

  have qzero: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | ?T *\<^sub>v x\<rangle> = 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n"
    have xcar: "x \<in> carrier_vec n"
      by (simp add: carrier_dim_vec xdim)

    have qA_real: "\<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
      using qreal xdim by blast
    have "\<langle>x | ?T *\<^sub>v x\<rangle> = \<langle>x | A *\<^sub>v x\<rangle> - \<langle>x | A\<^sup>\<dagger> *\<^sub>v x\<rangle>"
      by (metis carrier_matD(1,2) dagger_def dim_mult_mat_vec inner_prod_right_minus'
          mat_carrier minus_mult_distrib_mat_vec sq xcar)
    also have "... = \<langle>x | A *\<^sub>v x\<rangle> - cnj \<langle>x | A *\<^sub>v x\<rangle>"
    proof -
      have "\<langle>x | A\<^sup>\<dagger> *\<^sub>v x\<rangle> = \<langle>A *\<^sub>v x | x\<rangle>"
        by (metis carrier_matD(1,2) dim_mult_mat_vec dim_row_of_dagger 
            inner_prod_adjoint_swap inner_prod_cnj sq xdim)        
      also have "... = cnj \<langle>x | A *\<^sub>v x\<rangle>"
        by (metis carrier_matD(1) dim_mult_mat_vec inner_prod_cnj sq xdim)
      finally show ?thesis by simp
    qed
    also have "... = 0"
      using Reals_cnj_iff qA_real by force
    finally show "\<langle>x | ?T *\<^sub>v x\<rangle> = 0" .
  qed

  have "?T = 0\<^sub>m n n"
    using quadratic_form_zero[OF Tcar qzero].
  hence "A = (A\<^sup>\<dagger>)"
  proof -
    have Adagcar: "A\<^sup>\<dagger> \<in> carrier_mat n n" using sq by auto
    have "A = (A - (A\<^sup>\<dagger>)) + (A\<^sup>\<dagger>)"
    proof -
      have "A = A + 0\<^sub>m n n"
        using sq by simp
      also have "... = A + (-(A\<^sup>\<dagger>) + (A\<^sup>\<dagger>))"
        using Adagcar by force
      also have "... = (A - (A\<^sup>\<dagger>)) + (A\<^sup>\<dagger>)"
        by (smt (verit, best) Adagcar add_uminus_minus_mat assoc_add_mat sq uminus_carrier_mat)
      finally show ?thesis.
    qed
    also have "\<dots> = (0\<^sub>m n n) + (A\<^sup>\<dagger>)"
      using \<open>?T = 0\<^sub>m n n\<close> by simp
    also have "\<dots> = (A\<^sup>\<dagger>)"
      using Adagcar by auto
    finally show ?thesis.
  qed
  then show "hermitian A"
    by (simp add: hermitian_def)
qed

subsection \<open>The spectral theorem for Hermitian matrices\<close>

text \<open>(a)$\Rightarrow$(b) of the theorem above: by Schur, $U^*HU=T$ is upper triangular,
and $T^*=(U^*HU)^*=T$ forces $T$ to be diagonal with real entries.
\<open>diag_mat_of_real D\<close> is the complex diagonal matrix with the real list $D$ on its
diagonal.\<close>
definition diag_mat_of_real :: "real list \<Rightarrow> complex Matrix.mat" where
  "diag_mat_of_real D = mat_diag (length D) (\<lambda>i. complex_of_real (D ! i))"

lemma dim_row_diag_mat_of_real[simp]: "dim_row (diag_mat_of_real D) = length D"
  unfolding diag_mat_of_real_def mat_diag_def by simp

lemma dim_col_diag_mat_of_real[simp]: "dim_col (diag_mat_of_real D) = length D"
  unfolding diag_mat_of_real_def mat_diag_def by simp

lemma diag_mat_of_real_carrier[simp]:
  "diag_mat_of_real D \<in> carrier_mat (length D) (length D)"
  by (rule carrier_matI) auto

lemma diag_mat_of_real_index[simp]:
  assumes "i < length D" and "j < length D"
  shows "diag_mat_of_real D $$ (i, j) =
         (if i = j then complex_of_real (D ! i) else 0)"
  using assms unfolding diag_mat_of_real_def mat_diag_def by simp

lemma diag_mat_of_real_mult_vec_index:
  fixes y :: "complex Matrix.vec"
  assumes ydim: "dim_vec y = length D"
      and i: "i < length D"
  shows "(diag_mat_of_real D *\<^sub>v y) $ i = complex_of_real (D ! i) * y $ i"
proof -
  have ycar: "y \<in> carrier_vec (length D)"
    by (simp add: carrier_vecI ydim)
  have "(diag_mat_of_real D *\<^sub>v y) $ i =
        (\<Sum>j = 0..<length D. diag_mat_of_real D $$ (i, j) * y $ j)"
    using mult_mat_vec_index[OF diag_mat_of_real_carrier ycar i] .
  also have "\<dots> =
        (\<Sum>j = 0..<length D. (if i = j then complex_of_real (D ! i) * y $ j else 0))"
    using i by (intro sum.cong refl) auto
  also have "\<dots> = complex_of_real (D ! i) * y $ i"
    using i by simp
  finally show ?thesis.
qed

text \<open>For a real diagonal $D=\diag(\lambda_1,\dots,\lambda_n)$,
$\braket y{Dy}=\sum_i\lambda_i|y_i|^2$, which is $\ge0$ when every $\lambda_i\ge0$.\<close>

lemma diag_mat_of_real_quad_Re_nonneg:
  fixes y :: "complex Matrix.vec"
  assumes ydim: "dim_vec y = length D"
      and D_nonneg: "\<And>i. i < length D \<Longrightarrow> 0 \<le> D ! i"
  shows "0 \<le> Re \<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>"
proof -
  have Dy_dim: "dim_vec (diag_mat_of_real D *\<^sub>v y) = length D"
    using ydim by simp

  have inner_expand:
    "\<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
      = (\<Sum>i = 0..<length D. cnj (y $ i) * ((diag_mat_of_real D *\<^sub>v y) $ i))"
    using ydim Dy_dim
    by (simp add: inner_prod_def)

  have diag_action:
    "\<And>i. i < length D \<Longrightarrow> (diag_mat_of_real D *\<^sub>v y) $ i = complex_of_real (D ! i) * y $ i"
  proof -
    fix i
    assume ilt: "i < length D"
    have "(diag_mat_of_real D *\<^sub>v y) $ i
        = (\<Sum>j = 0..<dim_col (diag_mat_of_real D). diag_mat_of_real D $$ (i,j) * y $ j)"
      using ilt ydim
      by (metis (full_types) carrier_vec_dim_vec 
          diag_mat_of_real_carrier dim_col_diag_mat_of_real mult_mat_vec_index)
    also have "... = (\<Sum>j = 0..<length D. diag_mat_of_real D $$ (i,j) * y $ j)"
      by simp
    also have "... = (\<Sum>j = 0..<length D.
             (if i = j then complex_of_real (D ! i) else 0) * y $ j)"
      using ilt
      by (intro sum.cong refl, simp add: diag_mat_of_real_def mat_diag_def)
    also have "... = complex_of_real (D ! i) * y $ i"
      using ilt
      by (metis calculation diag_mat_of_real_mult_vec_index ydim)
    finally show "(diag_mat_of_real D *\<^sub>v y) $ i = complex_of_real (D ! i) * y $ i" .
  qed

  have "\<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
      = (\<Sum>i = 0..<length D. cnj (y $ i) * ((diag_mat_of_real D *\<^sub>v y) $ i))"
    using inner_expand .
  also have "... = (\<Sum>i = 0..<length D. cnj (y $ i) * (complex_of_real (D ! i) * y $ i))"
  proof (intro sum.cong refl)
    fix i
    assume ilt: "i \<in> {0..<length D}"
    then have "i < length D" by simp
    thus "cnj (y $ i) * ((diag_mat_of_real D *\<^sub>v y) $ i)
        = cnj (y $ i) * (complex_of_real (D ! i) * y $ i)"
      using diag_action by simp
  qed
  finally have quad_expand:
    "\<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
      = (\<Sum>i = 0..<length D. cnj (y $ i) * (complex_of_real (D ! i) * y $ i))" .

  have Re_expand:
    "Re \<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
      = (\<Sum>i = 0..<length D. D ! i * Re (cnj (y $ i) * y $ i))"
  proof -
    have "Re \<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>
        = Re (\<Sum>i = 0..<length D. cnj (y $ i) * (complex_of_real (D ! i) * y $ i))"
      using quad_expand by simp
    also have "... = Re (\<Sum>i = 0..<length D. complex_of_real (D ! i) * (cnj (y $ i) * y $ i))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<Sum>i = 0..<length D. Re (complex_of_real (D ! i) * (cnj (y $ i) * y $ i)))"
      by simp
    also have "... = (\<Sum>i = 0..<length D. D ! i * Re (cnj (y $ i) * y $ i))"
      by simp
    finally show ?thesis.
  qed

  have term_nonneg:
    "\<And>i. i \<in> {0..<length D} \<Longrightarrow> 0 \<le> D ! i * Re (cnj (y $ i) * y $ i)"
  proof -
    fix i
    assume i: "i \<in> {0..<length D}"
    then have ilt: "i < length D"
      by simp
    have "0 \<le> D ! i"
      using D_nonneg ilt by simp
    moreover have "0 \<le> Re (cnj (y $ i) * y $ i)"
      by simp
    ultimately show "0 \<le> D ! i * Re (cnj (y $ i) * y $ i)"
      by simp
  qed

  have "0 \<le> (\<Sum>i = 0..<length D. D ! i * Re (cnj (y $ i) * y $ i))"
    by (rule sum_nonneg, rule term_nonneg)
  thus "0 \<le> Re \<langle>y | diag_mat_of_real D *\<^sub>v y\<rangle>"
    using Re_expand by simp
qed

text \<open>The spectral theorem.  If $U^*HU=T$ is a Schur form of a Hermitian $H$, then
$T^*=U^*H^*U=T$; an upper triangular matrix equal to its adjoint is diagonal with real
diagonal.  Hence
\[ H=UDU^*,\qquad D=\diag(\lambda_1,\dots,\lambda_n),\ \lambda_i\in\R, \]
and the columns of $U$ are an orthonormal basis of eigenvectors, $Hu_i=\lambda_iu_i$.\<close>

theorem hermitian_spectral_decomp:
  fixes H :: "complex Matrix.mat"
  assumes sq: "H \<in> carrier_mat n n"
      and herm: "hermitian H"
  shows "\<exists>(U :: complex Matrix.mat) (D :: real list).
         U \<in> carrier_mat n n \<and>
         unitary U \<and>
         length D = n \<and>
         (U\<^sup>\<dagger>) * H * U = diag_mat_of_real D"
proof -
  (* Step 1: Schur gives U unitary, T = U\<dagger>HU upper triangular. *)
  obtain U T where Uc: "U \<in> carrier_mat n n" and Tc: "T \<in> carrier_mat n n"
    and UU: "unitary U" and UT: "upper_triangular T"
    and schur: "U\<^sup>\<dagger> * H * U = T"
    using schur_theorem[OF sq] by blast
  have Udagcar: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have Hdag: "H\<^sup>\<dagger> = H" using herm by (simp add: hermitian_def)

  (* Step 2: T\<dagger> = T using H Hermitian and (AB)\<dagger> = B\<dagger>A\<dagger>. *)
  have Tdag: "T\<^sup>\<dagger> = T"
  proof -
    have HUcar: "H * U \<in> carrier_mat n n" using sq Uc by auto
    have UdagHcar: "U\<^sup>\<dagger> * H \<in> carrier_mat n n" using Udagcar sq by auto
    let ?Ud = "U\<^sup>\<dagger>"
    let ?A = "?Ud * H"
    have dcA: "dim_col ?A = dim_row U" using UdagHcar Uc by auto
    have dcUd: "dim_col ?Ud = dim_row H" using Udagcar sq by auto
    have step1: "dagger (?A * U) = dagger U * dagger ?A"
      by (rule dagger_of_prod[OF dcA])
    have step2: "dagger ?A = (H\<^sup>\<dagger>) * dagger ?Ud"
      by (rule dagger_of_prod[OF dcUd])
    have step3: "dagger ?Ud = U" using Uc by (simp add: dagger_of_dagger_is_id)
    have "T\<^sup>\<dagger> = dagger (?A * U)" using schur by simp
    also have "\<dots> = dagger U * dagger ?A" using step1 .
    also have "\<dots> = dagger U * (H\<^sup>\<dagger> * dagger ?Ud)" using step2 by simp
    also have "\<dots> = dagger U * (H * U)" using step3 Hdag by simp
    also have "\<dots> = ?Ud * H * U"
      using Udagcar sq Uc by simp
    also have "\<dots> = T" using schur by simp
    finally show ?thesis.
  qed

  (* Step 3: T upper triangular + T\<dagger> = T \<Longrightarrow> T diagonal. *)
  have T_off_diag: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> T $$ (i, j) = 0"
  proof -
    fix i j assume i: "i < n" and j: "j < n" and ij: "i \<noteq> j"
    show "T $$ (i, j) = 0"
    proof (cases "i > j")
      case True
      then show ?thesis using upper_triangularD[OF UT True] i Tc by simp
    next
      case False
      then have ji: "j > i" using ij by auto
      have Tji0: "T $$ (j, i) = 0"
        using upper_triangularD[OF UT ji] j Tc by simp
      have "T $$ (i, j) = (T\<^sup>\<dagger>) $$ (i, j)" using Tdag by simp
      also have "\<dots> = cnj (T $$ (j, i))"
        using i j Tc by (simp add: dagger_def)
      also have "\<dots> = 0" using Tji0 by simp
      finally show ?thesis.
    qed
  qed

  (* Step 4: diagonal entries are real. *)
  have T_diag_real: "\<And>i. i < n \<Longrightarrow> T $$ (i, i) \<in> \<real>"
  proof -
    fix i assume i: "i < n"
    have "cnj (T $$ (i, i)) = (T\<^sup>\<dagger>) $$ (i, i)"
      using i Tc by (simp add: dagger_def)
    also have "\<dots> = T $$ (i, i)" using Tdag by simp
    finally have "cnj (T $$ (i, i)) = T $$ (i, i)".
    then show "T $$ (i, i) \<in> \<real>" using Reals_cnj_iff by metis
  qed

  (* Step 5: extract the real diagonal as a list and show T = diag_mat_of_real D. *)
  let ?D = "map (\<lambda>i. Re (T $$ (i, i))) [0..<n]"
  have D_len: "length ?D = n" by simp
  have D_idx: "\<And>i. i < n \<Longrightarrow> ?D ! i = Re (T $$ (i, i))" by simp

  have T_eq_diag: "T = diag_mat_of_real ?D"
  proof (rule eq_matI)
    show "dim_row T = dim_row (diag_mat_of_real ?D)" using Tc by auto
    show "dim_col T = dim_col (diag_mat_of_real ?D)" using Tc by auto
  next
    fix i j
    assume "i < dim_row (diag_mat_of_real ?D)" "j < dim_col (diag_mat_of_real ?D)"
    then have inb: "i < n" "j < n" by auto
    show "T $$ (i, j) = diag_mat_of_real ?D $$ (i, j)"
    proof (cases "i = j")
      case True
      have "T $$ (i, i) = complex_of_real (Re (T $$ (i, i)))"
        using T_diag_real[OF inb(1)]
        by (metis Reals_cases Re_complex_of_real)
      then show ?thesis
        using True inb D_len D_idx[OF inb(1)] by simp
    next
      case False
      have "T $$ (i, j) = 0" using T_off_diag[OF inb(1) inb(2) False].
      moreover have "diag_mat_of_real ?D $$ (i, j) = 0"
        using False inb D_len by simp
      ultimately show ?thesis by simp
    qed
  qed

  show ?thesis
    using Uc UU D_len schur T_eq_diag by metis
qed


corollary hermitian_real_eigenvalues:
  fixes H :: "complex Matrix.mat"
  assumes sq: "H \<in> carrier_mat n n"
      and herm: "hermitian H"
      and eig: "H *\<^sub>v v = lam \<cdot>\<^sub>v v"
      and v_nonzero: "v \<noteq> 0\<^sub>v n"
      and vdim: "dim_vec v = n"
  shows "lam \<in> \<real>"
proof -
  have vcar: "v \<in> carrier_vec n"
    by (simp add: carrier_dim_vec vdim)
  (* From hermitian: \<langle>v|Hv\<rangle> is real.  And \<langle>v|Hv\<rangle> = lam * \<langle>v|v\<rangle>.
     Since \<langle>v|v\<rangle> = \<parallel>v\<parallel>² is a positive real (v \<noteq> 0), lam is real. *)
  have qreal: "\<langle>v | H *\<^sub>v v\<rangle> \<in> \<real>"
    using hermitian_iff_real_quad_form[OF sq] herm vdim by blast
  have q_eq: "\<langle>v | H *\<^sub>v v\<rangle> = lam * \<langle>v | v\<rangle>"
    using eig inner_prod_right_smult' by presburger
  have vv_real: "\<langle>v | v\<rangle> \<in> \<real>"
    using vcar inner_prod_with_itself_real vdim
    by blast 
  have vv_nonzero: "\<langle>v | v\<rangle> \<noteq> 0"
    using vcar v_nonzero
    by (simp add: inner_prod_with_itself_nonneg_reals_non0, 
        metis comm_scalar_prod conjugate_complex_def 
        conjugate_square_eq_0_vec conjugate_vec_def vdim vec_carrier)
  show "lam \<in> \<real>"
    using qreal q_eq
    using Reals_cnj_iff vv_nonzero vv_real by fastforce 
qed


subsection \<open>Positive semidefinite and positive definite matrices\<close>

text \<open>\begin{notesdef}
$P\in M_n$ is \emph{positive semidefinite}, $P\ge 0$, if $\braket{x}{Px}\ge 0$ for all
$x\in\C^n$, and \emph{positive definite}, $P>0$, if $\braket{x}{Px}>0$ for all $x\neq 0$.
\end{notesdef}
By part (d) of the previous theorem, $P\ge 0$ implies $P=P^*$.  The formal predicates
\<open>psd\<close> and \<open>pd\<close> carry Hermiticity as an explicit conjunct together with the real-part
inequality; by \<open>hermitian_iff_real_quad_form\<close> this is equivalent to the notes'
definition.
\begin{notestheorem}
$P\ge 0$ if and only if $P=P^*$ and all eigenvalues of $P$ are non-negative.
\end{notestheorem}
\begin{notescor}
$P>0$ if and only if $P=P^*$ and all eigenvalues of $P$ are strictly positive.
\end{notescor}
\begin{notestheorem}
$P\ge 0$ if and only if $P=\sum_{i=1}^m\ketbra{v_i}{v_i}$ for some vectors $v_1,\dots,v_m$.
\end{notestheorem}
Key: if $P=\sum_i\ketbra{v_i}{v_i}$ then $\braket{x}{Px}=\sum_i|\braket{v_i}{x}|^2$.
\begin{notestheorem}
Let $P=\sum_{i=1}^m\ketbra{v_i}{v_i}\in M_n$.  Then $P>0$ if and only if
$\operatorname{span}\{v_1,\dots,v_m\}=\C^n$.
\end{notestheorem}
The notes' form of the definition is \<open>psd_iff_quad_form_nonneg\<close>; the corollary on positive
definite matrices is \<open>pd_iff_pos_eigenvalues\<close> (proved after the square root); the last
theorem is formalised with ``the $v_i$ span $\C^n$'' phrased as ``no nonzero $x$ is
orthogonal to every $v_i$''.\<close>

definition psd :: "complex Matrix.mat \<Rightarrow> bool" where
  "psd P \<equiv> hermitian P \<and>
            (\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
               Re (\<langle>x | P *\<^sub>v x\<rangle>) \<ge> 0)"

definition pd :: "complex Matrix.mat \<Rightarrow> bool" where
  "pd P \<equiv> hermitian P \<and>
           (\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
              x \<noteq> 0\<^sub>v (dim_row P) \<longrightarrow>
              Re (\<langle>x | P *\<^sub>v x\<rangle>) > 0)"

notation psd ("_ \<ge>\<^sub>M 0")
notation pd  ("_ >\<^sub>M 0")


lemma psd_hermitian: "psd P \<Longrightarrow> hermitian P"
  by (simp add: psd_def)

text \<open>The notes' definition, without the explicit Hermiticity conjunct: $P\ge0$ iff every
quadratic form $\braket{x}{Px}$ is a non-negative real number.\<close>

lemma psd_iff_quad_form_nonneg:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
  shows "psd P \<longleftrightarrow>
         (\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow>
            \<langle>x | P *\<^sub>v x\<rangle> \<in> \<real> \<and> 0 \<le> Re (\<langle>x | P *\<^sub>v x\<rangle>))"
proof -
  have dr: "dim_row P = n" using sq by auto
  show ?thesis
    unfolding psd_def dr using hermitian_iff_real_quad_form[OF sq] by blast
qed

lemma psd_MdagM:
  assumes M: "M \<in> carrier_mat n m"
  shows "psd (M\<^sup>\<dagger> * M)"
proof -
  have MM_car: "M\<^sup>\<dagger> * M \<in> carrier_mat m m"
    using assms by fastforce

  have herm: "hermitian (M\<^sup>\<dagger> * M)"
    unfolding hermitian_def using M
    by (simp add: dagger_of_dagger_is_id dagger_of_prod)


  have nonneg:
    "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row (M\<^sup>\<dagger> * M) \<longrightarrow>  Re \<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> \<ge> 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = dim_row (M\<^sup>\<dagger> * M)"

    have dim_row_MM: "dim_row (M\<^sup>\<dagger> * M) = m"
      using M by simp
    hence xdim': "dim_vec x = m"
      using xdim by simp

    have Mx_dim: "dim_vec (M *\<^sub>v x) = n"
      using M xdim' by simp

    have qf:  "\<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
    proof -
      have "\<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> = \<langle>x | M\<^sup>\<dagger> *\<^sub>v (M *\<^sub>v x)\<rangle>"
        using M xdim'
        by (metis assoc_mult_mat_vec carrier_matD(1) carrier_vec_dim_vec dagger_def mat_carrier)
      also have "... = \<langle>(M\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using M xdim' Mx_dim
        by (metis carrier_matD(2) dagger_of_dagger_is_id dim_mult_mat_vec 
            dim_row_of_dagger inner_prod_adjoint_swap inner_prod_cnj)
      also have "... = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
        using dagger_of_dagger_is_id by presburger
      finally show ?thesis.
    qed
    have "Re \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle> \<ge> 0"
      using Mx_dim using inner_prod_with_itself_Re by blast
    thus "Re \<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> \<ge> 0"
      using qf by simp
  qed
  show ?thesis
    unfolding psd_def using herm nonneg by simp
qed

text \<open>$P\ge 0$ iff $P$ is Hermitian with non-negative eigenvalues:\<close>

theorem psd_iff_nonneg_eigenvalues:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
  shows "psd P \<longleftrightarrow>
         (hermitian P \<and>
          (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0))"
proof
  assume pos: "psd P"
  have herm: "hermitian P"
    using pos by (rule psd_hermitian)

  have eig_nonneg:
    "\<forall>mu v. v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
  proof (intro allI impI)
    fix mu :: complex
    fix v  :: "complex Matrix.vec"
    assume hyp: "v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v"
    then have vneq: "v \<noteq> 0\<^sub>v n"
      and vdim: "dim_vec v = n"
      and eig:  "P *\<^sub>v v = mu \<cdot>\<^sub>v v"
      by auto
    have qf_nonneg: "0 \<le> Re \<langle>v | P *\<^sub>v v\<rangle>"
      using pos vdim  unfolding psd_def  using sq by auto
    have inner_eig: "\<langle>v | P *\<^sub>v v\<rangle> = mu * \<langle>v | v\<rangle>"
      by (simp add: hyp)
    have vv_real: "\<langle>v | v\<rangle> = of_real (Re \<langle>v | v\<rangle>)"
      using inner_prod_with_itself_real of_real_Re by presburger
    have vv_pos: "0 < Re \<langle>v | v\<rangle>"
      using vneq vdim inner_prod_with_itself_Re_non0 by blast
    have "0 \<le> Re (mu * \<langle>v | v\<rangle>)"
      using qf_nonneg by (simp add: inner_eig)
    hence "0 \<le> Re mu * Re \<langle>v | v\<rangle>"
      using inner_prod_with_itself_Im by auto     
    thus "Re mu \<ge> 0"
      by (meson linorder_not_less vv_pos zero_le_mult_iff)
  qed
  show "hermitian P \<and>
        (\<forall>mu::complex. \<forall>v::complex Matrix.vec.
           v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0)"
    using herm eig_nonneg by blast
next
  assume rhs:
    "hermitian P \<and>
     (\<forall>mu::complex. \<forall>v::complex Matrix.vec.
        v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0)"
  then have herm: "hermitian P"
    by blast
  from rhs have eig_nonneg:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    by blast

  have "psd P"
  proof -
    obtain U :: "complex Matrix.mat" and D :: "real list"
      where Uc: "U \<in> carrier_mat n n"
        and UU: "unitary U"
        and Dlen: "length D = n"
        and specD: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
      using hermitian_spectral_decomp[OF sq herm] by blast

    have Udag_c: "U\<^sup>\<dagger> \<in> carrier_mat n n"
      using Uc by auto
    have UdagU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n"
      using Uc UU unfolding unitary_def by auto
    have UUdag: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
      using Uc UU unfolding unitary_def by auto
    have P_eq: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    proof -
      have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = U * ((U\<^sup>\<dagger>) * P * U) * (U\<^sup>\<dagger>)"
        using specD by simp
      also have "\<dots> = P"
        using Uc Udag_c sq UdagU UUdag Dlen 
        by (smt (verit, ccfv_SIG) assoc_mult_mat left_mult_one_mat 
            mult_carrier_mat right_mult_one_mat)
      finally show ?thesis by simp
    qed

    have PU_eq_UD: "P * U = U * diag_mat_of_real D"
    proof -
      have "P * U = (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) * U"
        using P_eq by simp
      also have "\<dots> = U * diag_mat_of_real D"
        using Uc Udag_c UdagU Dlen
        by (smt (verit, del_insts) assoc_mult_mat carrier_mat_triv 
            dim_col_diag_mat_of_real index_mult_mat(3) right_mult_one_mat) 
      finally show ?thesis.
    qed

    have D_nonneg: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
    proof -
      fix i assume i: "i < n"
      let ?ui = "Matrix.col U i"
      have uidim: "dim_vec ?ui = n"
        using Uc by simp
      have ui_nonzero: "?ui \<noteq> 0\<^sub>v n"
      proof
        assume zero: "?ui = 0\<^sub>v n"
        have "\<parallel>?ui\<parallel> = (1 :: real)"
          using UU i Uc by (metis carrier_matD(2) unitary_unit_col)
        moreover have "\<parallel>?ui\<parallel> = 0"
          using zero uidim cpx_vec_length_zero_iff by metis
        ultimately show False by simp
      qed
      have eig: "P *\<^sub>v ?ui = complex_of_real (D ! i) \<cdot>\<^sub>v ?ui"
      proof (rule eq_vecI)
        show "dim_vec (P *\<^sub>v ?ui) = dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
          using sq uidim by simp
      next
        fix k
        assume k: "k < dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
        then have klt: "k < n"
          using uidim by simp
        have "(P *\<^sub>v ?ui) $ k = (P * U) $$ (k, i)"
          using sq Uc i klt by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
        also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
          using PU_eq_UD by simp
        also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
        proof -
          have "(U * diag_mat_of_real D) $$ (k, i) =
                (\<Sum>j = 0..<n. U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
            using Uc Dlen klt i by (simp add: scalar_prod_def lessThan_atLeast0)
          also have "\<dots> =
                (\<Sum>j = 0..<n. (if j = i then U $$ (k, j) * complex_of_real (D ! i) else 0))"
            using Dlen i by (intro sum.cong refl, auto)
          also have "\<dots> = U $$ (k, i) * complex_of_real (D ! i)"
            using i by simp
          also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
            by (simp add: mult.commute)
          finally show ?thesis.
        qed
        also have "\<dots> = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k"
          using klt Uc  by (simp add: i) 
        finally show "(P *\<^sub>v ?ui) $ k = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k" .
      qed
      have "0 \<le> Re (complex_of_real (D ! i))"
        using eig eig_nonneg ui_nonzero uidim by blast
      then show "0 \<le> D ! i"
        by simp
    qed

    have spec: "\<forall>v. dim_vec v = n \<longrightarrow> 0 \<le> Re \<langle>v | P *\<^sub>v v\<rangle>"
    proof (intro allI impI)
      fix v :: "complex Matrix.vec"
      assume vdim: "dim_vec v = n"
      let ?y = "U\<^sup>\<dagger> *\<^sub>v v"
      have ydim: "dim_vec ?y = n"
        using Uc by force
      have v_as_Uy: "U *\<^sub>v ?y = v"
      proof -
        have "U *\<^sub>v ((U\<^sup>\<dagger>) *\<^sub>v v) = (U * (U\<^sup>\<dagger>)) *\<^sub>v v"
          using Uc Udag_c vdim by force
        also have "\<dots> = v"
          using UUdag vdim by force
        finally show ?thesis.
      qed
      have Pv_as: "P *\<^sub>v v = U *\<^sub>v (diag_mat_of_real D *\<^sub>v ?y)"
      proof -
        have "P *\<^sub>v v = (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) *\<^sub>v v"
          using P_eq by simp
        also have "\<dots> = U *\<^sub>v (diag_mat_of_real D *\<^sub>v (U\<^sup>\<dagger> *\<^sub>v v))"
          using Uc Udag_c sq Dlen vdim
          by (smt (verit, ccfv_SIG) assoc_mult_mat_vec 
              carrier_vec_dim_vec diag_mat_of_real_carrier mult_carrier_mat ydim)
        finally show ?thesis.
      qed
      have "\<langle>v | P *\<^sub>v v\<rangle> = \<langle>U *\<^sub>v ?y | U *\<^sub>v (diag_mat_of_real D *\<^sub>v ?y)\<rangle>"
        using v_as_Uy Pv_as by simp
      also have "\<dots> = \<langle>?y | diag_mat_of_real D *\<^sub>v ?y\<rangle>"
        by (metis Uc dim_mult_mat_vec index_mult_mat(2) 
            inner_prod_adjoint_swap specD v_as_Uy vdim ydim)
      finally have qeq: "\<langle>v | P *\<^sub>v v\<rangle> = \<langle>?y | diag_mat_of_real D *\<^sub>v ?y\<rangle>".
      show "0 \<le> Re \<langle>v | P *\<^sub>v v\<rangle>"
        using diag_mat_of_real_quad_Re_nonneg[OF _] D_nonneg Dlen ydim qeq by auto
    qed
    show ?thesis
      unfolding psd_def
      using sq herm spec by auto
  qed
  thus "psd P".
qed

text \<open>$P\ge 0$ iff $P=\sum_i\ketbra{v_i}{v_i}$.  First the direction $\Leftarrow$:\<close>

lemma outer_sum_psd:
  assumes len: "length vs = k"
      and vdim: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "psd (outer_sum n vs)"
proof -
  have herm: "hermitian (outer_sum n vs)"
    unfolding hermitian_def using outer_sum_hermitian by simp
  have dr: "dim_row (outer_sum n vs) = n"
    by simp
  have nonneg: "\<forall>x. dim_vec x = dim_row (outer_sum n vs) \<longrightarrow>
              Re (\<langle>x | outer_sum n vs *\<^sub>v x\<rangle>) \<ge> 0"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = dim_row (outer_sum n vs)"
    let ?M = "mat_of_cols n vs"
    let ?y = "(?M\<^sup>\<dagger>) *\<^sub>v x"
    have M_car: "?M \<in> carrier_mat n k"
      using len vdim by (simp add: mat_of_cols_def)
    have xdim_n: "dim_vec x = n"
      using xdim by simp
    have xcar: "x \<in> carrier_vec n"
      using xdim_n carrier_vec_dim_vec by blast
    have ycar: "?y \<in> carrier_vec k"
      using M_car xcar carrier_dim_vec len by force
    have ydim: "dim_vec ?y = k"
      using ycar carrier_dim_vec by blast
    have outer_as_MMdag: "outer_sum n vs = ?M * (?M\<^sup>\<dagger>)"
      using len vdim outer_sum_def by presburger
    have qf: "\<langle>x | outer_sum n vs *\<^sub>v x\<rangle> = \<langle>?y | ?y\<rangle>"
    proof - 
      have  "\<langle>x | outer_sum n vs *\<^sub>v x\<rangle> = \<langle>x | ((?M * (?M\<^sup>\<dagger>)) *\<^sub>v x)\<rangle>"
        using outer_as_MMdag by simp
      also have  "... = \<langle>x | ?M *\<^sub>v ((?M\<^sup>\<dagger>) *\<^sub>v x)\<rangle>"
        using M_car xcar by (metis assoc_mult_mat_vec carrier_matD(1)
            carrier_mat_triv dim_col_of_dagger dim_mult_mat_vec ydim)
      also have " ...  = \<langle>?y | ?y\<rangle>"
        using inner_prod_adjoint_swap M_car xcar  by simp
      finally show ?thesis.
    qed
    have self_nonneg: "Re \<langle>?y | ?y\<rangle> \<ge> 0"
      using ydim inner_prod_with_itself_Re by blast
    show "Re (\<langle>x | outer_sum n vs *\<^sub>v x\<rangle>) \<ge> 0"
      using qf self_nonneg by simp
  qed
  show ?thesis
    unfolding psd_def using herm nonneg by simp
qed


lemma hermitian_spectral_decomp_eq:
  assumes Uc: "U \<in> carrier_mat n n"
      and Pcar: "P \<in> carrier_mat n n"
      and unit: "unitary U"
      and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
  shows "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
proof -
  have UdagU: "U\<^sup>\<dagger> * U = 1\<^sub>m n"
    using Uc unit unfolding unitary_def by auto
  have UUdag: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
    using Uc unit unfolding unitary_def by auto
  have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = U * ((U\<^sup>\<dagger>) * P * U) * (U\<^sup>\<dagger>)"
    using spec by simp
  also have "... = (U * (U\<^sup>\<dagger>)) * P * (U * (U\<^sup>\<dagger>))"
    by (smt (verit, best) Pcar UUdag UdagU assoc_mult_mat carrier_matD(2) 
        carrier_mat_triv dim_row_of_dagger index_mult_mat(2,3) index_one_mat(2))
  also have "... = (1\<^sub>m n) * P * (1\<^sub>m n)"
    using UUdag by simp
  also have "... = P"
    using Pcar by simp
  finally show ?thesis
    by simp
qed

lemma hermitian_spectral_decomp_right:
  assumes Uc: "U \<in> carrier_mat n n"
      and Pcar: "P \<in> carrier_mat n n"
      and unit: "unitary U"
      and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
  shows "P * U = U * diag_mat_of_real D"
  by (smt (verit, best) hermitian_spectral_decomp_eq Pcar Uc assoc_mult_mat carrier_mat_triv 
      dim_col_of_dagger unitary_def index_mult_mat(2,3) local.spec right_mult_one_mat unit)

text \<open>The direction $\Rightarrow$, from the spectral theorem:
$P=\sum_j\lambda_j\ketbra{u_j}{u_j}=\sum_j\ketbra{\lambda_j^{1/2}u_j}{\lambda_j^{1/2}u_j}$.\<close>
text \<open>The spectral theorem for positive matrices: $P=U\,\mathrm{diag}(D)\,U^\dagger$ with $D\ge0$.\<close>

lemma psd_spectral_decomp_nonneg:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>(U :: complex Matrix.mat) (D :: real list).
           U \<in> carrier_mat n n \<and> unitary U \<and> length D = n \<and>
           (\<forall>i < n. 0 \<le> D ! i) \<and>
           P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
proof -
  have herm: "hermitian P" using pos by (rule psd_hermitian)
  obtain U :: "complex Matrix.mat" and D :: "real list" where
      Uc: "U \<in> carrier_mat n n"
    and UU: "unitary U"
    and Dlen: "length D = n"
    and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast
  have P_eq: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using hermitian_spectral_decomp_eq[OF Uc sq UU spec] .
  have PU_eq_UD: "P * U = U * diag_mat_of_real D"
    using hermitian_spectral_decomp_right[OF Uc sq UU spec] .
  have eig_nonneg:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    using psd_iff_nonneg_eigenvalues[OF sq] pos by blast
  have D_nonneg: "\<forall>i < n. D ! i \<ge> 0"
  proof (intro allI impI)
    fix i assume iltn: "i < n"
    let ?ui = "Matrix.col U i"
    have uidim: "dim_vec ?ui = n" using Uc by simp
    have ui_nonzero: "?ui \<noteq> 0\<^sub>v n"
    proof
      assume zero: "?ui = 0\<^sub>v n"
      have "\<parallel>?ui\<parallel> = (1 :: real)"
        using UU iltn Uc by (metis carrier_matD(2) unitary_unit_col)
      moreover have "\<parallel>?ui\<parallel> = 0"
        using zero uidim cpx_vec_length_zero_iff by metis
      ultimately show False by simp
    qed
    have eig: "P *\<^sub>v ?ui = complex_of_real (D ! i) \<cdot>\<^sub>v ?ui"
    proof (rule eq_vecI)
      show "dim_vec (P *\<^sub>v ?ui) = dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
        using sq uidim by simp
    next
      fix k
      assume k: "k < dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
      then have klt: "k < n" using uidim by simp
      have "(P *\<^sub>v ?ui) $ k = (P * U) $$ (k, i)"
        using sq Uc iltn klt by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using PU_eq_UD by simp
      also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
      proof -
        have "(U * diag_mat_of_real D) $$ (k, i) =
              (\<Sum>j = 0..<n. U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
          using Uc Dlen klt iltn by (simp add: scalar_prod_def lessThan_atLeast0)
        also have "\<dots> =
              (\<Sum>j = 0..<n. (if j = i then U $$ (k, j) * complex_of_real (D ! i) else 0))"
          using Dlen iltn by (intro sum.cong refl, auto)
        also have "\<dots> = U $$ (k, i) * complex_of_real (D ! i)"
          using iltn by simp
        also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
          by (simp add: mult.commute)
        finally show ?thesis .
      qed
      also have "\<dots> = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k"
        using klt Uc by (simp add: iltn)
      finally show "(P *\<^sub>v ?ui) $ k = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k" .
    qed
    have "0 \<le> Re (complex_of_real (D ! i))"
      using eig eig_nonneg ui_nonzero uidim by blast
    thus "D ! i \<ge> 0" by simp
  qed
  show ?thesis using Uc UU Dlen D_nonneg P_eq by blast
qed

theorem psd_kraus_decomp:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>vs :: complex Matrix.vec list.
         length vs = n \<and>
         (\<forall>v \<in> set vs. dim_vec v = n) \<and>
         outer_sum n vs = P"
proof -
  (* By spectral theorem, P = U D U\<dagger> with D diagonal real \<ge> 0.
     Take vᵢ = \<surd>(Dᵢᵢ) \<cdot> col i of U.  Then \<Sum>|vᵢ\<rangle>\<langle>vᵢ| = U D U\<dagger> = P. *)
  have herm: "hermitian P"
    using pos by (rule psd_hermitian)

  obtain U D where
      Uc: "U \<in> carrier_mat n n"
    and UU: "unitary U"
    and Dlen: "length D = n"
    and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast

  have P_eq: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using hermitian_spectral_decomp_eq[OF Uc sq UU spec].   
  have PU_eq_UD: "P * U = U * diag_mat_of_real D"
    using UU Uc hermitian_spectral_decomp_right local.spec sq by presburger
  
  have eig_nonneg:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    using psd_iff_nonneg_eigenvalues[OF sq] pos by blast
  (* All entries of D are \<ge> 0 because P is psd. *)
  have D_nonneg: "\<forall>i < n. D ! i \<ge> 0"
  proof (intro allI impI)
    fix i assume iltn: "i < n"
    let ?ui = "Matrix.col U i"
    have uidim: "dim_vec ?ui = n"
      using Uc by simp
    have ui_nonzero: "?ui \<noteq> 0\<^sub>v n"
    proof
      assume zero: "?ui = 0\<^sub>v n"
      have "\<parallel>?ui\<parallel> = (1 :: real)"
        using UU iltn Uc by (metis carrier_matD(2) unitary_unit_col)
      moreover have "\<parallel>?ui\<parallel> = 0"
        using zero uidim cpx_vec_length_zero_iff by metis
      ultimately show False by simp
    qed
    have eig: "P *\<^sub>v ?ui = complex_of_real (D ! i) \<cdot>\<^sub>v ?ui"
    proof (rule eq_vecI)
      show "dim_vec (P *\<^sub>v ?ui) = dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
        using sq uidim by simp
    next
      fix k
      assume k: "k < dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
      then have klt: "k < n"
        using uidim by simp
      have "(P *\<^sub>v ?ui) $ k = (P * U) $$ (k, i)"
        using sq Uc iltn klt by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using PU_eq_UD by simp
      also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
      proof -
        have "(U * diag_mat_of_real D) $$ (k, i) =
              (\<Sum>j = 0..<n. U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
          using Uc Dlen klt iltn by (simp add: scalar_prod_def lessThan_atLeast0)
        also have "\<dots> =
              (\<Sum>j = 0..<n. (if j = i then U $$ (k, j) * complex_of_real (D ! i) else 0))"
          using Dlen iltn by (intro sum.cong refl, auto)
        also have "\<dots> = U $$ (k, i) * complex_of_real (D ! i)"
          using iltn by simp
        also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
          by (simp add: mult.commute)
        finally show ?thesis.
      qed
      also have "\<dots> = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k"
        using klt Uc by (simp add: iltn)
      finally show "(P *\<^sub>v ?ui) $ k = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k" .
    qed
    have "0 \<le> Re (complex_of_real (D ! i))"
      using eig eig_nonneg ui_nonzero uidim by blast
    thus "D ! i \<ge> 0" by simp
  qed
  (* Construct vᵢ = \<surd>(Dᵢ) \<cdot> col i of U *)
  let ?vs = "map (\<lambda>i. complex_of_real (sqrt (D ! i)) \<cdot>\<^sub>v Matrix.col U i) [0..<n]"
  have vs_dim: "\<forall>v \<in> set ?vs. dim_vec v = n"
    using Uc by auto
  have decomp: "outer_sum n ?vs = P"
  proof -
    (* Step A: outer_sum n ?vs = U * diag_mat_of_real D * U\<^sup>\<dagger>
       because each vᵢ vᵢ\<dagger> = (D!i) \<cdot> (col U i)(col U i)\<dagger>,
       and \<Sum>_{i<n} (D!i) \<cdot> (col U i)(col U i)\<dagger> = U D U\<dagger>. *)
    have stepA: "outer_sum n ?vs = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    proof -
      let ?sqrtD = "map sqrt D"
      let ?S = "diag_mat_of_real ?sqrtD"
      have sqrtDlen: "length ?sqrtD = n"
        using Dlen by simp
      have S_car: "?S \<in> carrier_mat n n"
        using sqrtDlen by force
      have M_eq: "mat_of_cols n ?vs = U * ?S"
      proof (rule eq_matI)
        show "dim_row (mat_of_cols n ?vs) = dim_row (U * ?S)"
          using Uc S_car by simp
        show "dim_col (mat_of_cols n ?vs) = dim_col (U * ?S)"
          using Uc S_car by force
      next
        fix r c
        assume rc: "r < dim_row (U * ?S)" "c < dim_col (U * ?S)"
        then have rlt: "r < n" and clt: "c < n"
          using Uc S_car by auto
        have "(mat_of_cols n ?vs) $$ (r, c) =
              complex_of_real (sqrt (D ! c)) * U $$ (r, c)"
          using Uc rlt clt by (simp add: mat_of_cols_def)
        also have "\<dots> = (U * ?S) $$ (r, c)"
        proof -
          have "(U * ?S) $$ (r, c) =  (\<Sum>j = 0..<n. U $$ (r, j) * ?S $$ (j, c))"
            using Uc S_car sqrtDlen rlt clt by (simp add: scalar_prod_def lessThan_atLeast0)
          also have "\<dots> =
                (\<Sum>j = 0..<n.
                   (if j = c then U $$ (r, j) * complex_of_real (sqrt (D ! c)) else 0))"
            using Dlen clt by (intro sum.cong refl, auto)
          also have "\<dots> = U $$ (r, c) * complex_of_real (sqrt (D ! c))"
            using clt by simp
          also have "\<dots> = complex_of_real (sqrt (D ! c)) * U $$ (r, c)"
            by (simp add: mult.commute)
          finally show ?thesis by simp
        qed
        finally show "(mat_of_cols n ?vs) $$ (r, c) = (U * ?S) $$ (r, c)" .
      qed
      have S_square: "?S * (?S\<^sup>\<dagger>) = diag_mat_of_real D"
      proof (rule eq_matI)
        show "dim_row (?S * (?S\<^sup>\<dagger>)) = dim_row (diag_mat_of_real D)"
          using Dlen sqrtDlen by simp
        show "dim_col (?S * (?S\<^sup>\<dagger>)) = dim_col (diag_mat_of_real D)"
          using Dlen sqrtDlen by simp
      next
        fix r c
        assume rc: "r < dim_row (diag_mat_of_real D)" "c < dim_col (diag_mat_of_real D)"
        then have rlt: "r < n" and clt: "c < n"
          using Dlen by auto
        have "(?S * (?S\<^sup>\<dagger>)) $$ (r, c) = (\<Sum>j = 0..<n. ?S $$ (r, j) * (?S\<^sup>\<dagger>) $$ (j, c))"
          using S_car sqrtDlen rlt clt by (simp add: scalar_prod_def lessThan_atLeast0)
        also have "\<dots> =
              (\<Sum>j = 0..<n.
                 (if r = j \<and> j = c
                  then complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! c))
                  else 0))"
          using Dlen rlt clt by (intro sum.cong refl, auto simp: dagger_def)
        also have "\<dots> = (if r = c then complex_of_real (D ! r) else 0)"
        proof (cases "r = c")
          case True
          then have "0 \<le> D ! r"
            using D_nonneg rlt by simp
          then have sqrt_sq:
            "complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! r)) =
             complex_of_real (D ! r)"
            by (simp add: of_real_mult[symmetric])
          have sum_single:
            "(\<Sum>j = 0..<n.
                 (if r = j \<and> j = c
                  then complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! c))
                  else 0))
             = complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! r))"
            using True rlt by (subst sum.remove[where x=r], auto)
          then show ?thesis
            using True sqrt_sq by argo
        next
          case False
          then show ?thesis by simp
        qed
        also have "\<dots> = diag_mat_of_real D $$ (r, c)"
          using Dlen rlt clt by simp
        finally show "(?S * (?S\<^sup>\<dagger>)) $$ (r, c) = diag_mat_of_real D $$ (r, c)" .
      qed
      have "outer_sum n ?vs = (U * ?S) * ((U * ?S)\<^sup>\<dagger>)"
        using M_eq by (simp add: outer_sum_def)
      also have "\<dots> = U * (?S * (?S\<^sup>\<dagger>)) * (U\<^sup>\<dagger>)"
        by (smt (verit, ccfv_threshold) Uc assoc_mult_mat carrier_matD(2) carrier_mat_triv sqrtDlen
            dagger_of_prod dim_col_of_dagger dim_row_diag_mat_of_real dim_row_of_dagger 
            mult_carrier_mat)        
      also have "\<dots> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
        using S_square by simp
      finally show ?thesis.
    qed
    (* Step B: U * diag_mat_of_real D * U\<^sup>\<dagger> = P
       follows from spec (U\<^sup>\<dagger> * P * U = diag_mat_of_real D)
       by multiplying on left by U and right by U\<^sup>\<dagger> and using U U\<^sup>\<dagger> = 1\<^sub>m n. *)
    have stepB: "U * diag_mat_of_real D * (U\<^sup>\<dagger>) = P"
      using P_eq by blast
    from stepA stepB show ?thesis by simp
  qed
  have vs_len: "length ?vs = n" by simp
  show ?thesis using vs_len vs_dim decomp by blast
qed

text \<open>$P=\sum_i\ketbra{v_i}{v_i}$ is positive definite iff the $v_i$ span $\C^n$:\<close>

text \<open>Entries of $\sum_i\ketbra{v_i}{v_i}$ for an arbitrary list of vectors.\<close>

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

lemma mat_of_cols_dagger_mult_vec_index:
  assumes xdim: "dim_vec x = n"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
      and i: "i < length vs"
  shows "(((mat_of_cols n vs)\<^sup>\<dagger>) *\<^sub>v x) $ i = \<langle>vs ! i | x\<rangle>"
proof -
  let ?M = "mat_of_cols n vs"
  have vi_dim: "dim_vec (vs ! i) = n"
    using assms by simp
  have "(((mat_of_cols n vs)\<^sup>\<dagger>) *\<^sub>v x) $ i =
        (\<Sum>j = 0..<n. cnj ((vs ! i) $ j) * x $ j)"
    using assms
    by (simp add: scalar_prod_def dagger_def mat_of_cols_def lessThan_atLeast0)
  also have "\<dots> = \<langle>vs ! i | x\<rangle>"
    using xdim vi_dim by (simp add: inner_prod_def)
  finally show ?thesis .
qed

lemma inner_prod_outer_sum_general:
  assumes xdim: "dim_vec x = n"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "\<langle>x | outer_sum n vs *\<^sub>v x\<rangle> =
         \<langle>((mat_of_cols n vs)\<^sup>\<dagger>) *\<^sub>v x |
          ((mat_of_cols n vs)\<^sup>\<dagger>) *\<^sub>v x\<rangle>"
proof -
  let ?M = "mat_of_cols n vs"
  let ?y = "(?M\<^sup>\<dagger>) *\<^sub>v x"
  have M_car: "?M \<in> carrier_mat n (length vs)"
    using vs_dim by (simp add: mat_of_cols_def)
  have xcar: "x \<in> carrier_vec n"
    using xdim carrier_vec_dim_vec by blast
  have ydim: "dim_vec ?y = length vs"
    using M_car xcar by force
  have outer_as_MMdag: "outer_sum n vs = ?M * (?M\<^sup>\<dagger>)"
    by (simp add: outer_sum_def)
  have "\<langle>x | outer_sum n vs *\<^sub>v x\<rangle> =
        \<langle>x | ((?M * (?M\<^sup>\<dagger>)) *\<^sub>v x)\<rangle>"
    using outer_as_MMdag by simp
  also have "... = \<langle>x | ?M *\<^sub>v ((?M\<^sup>\<dagger>) *\<^sub>v x)\<rangle>"
    using M_car xcar
    by (metis assoc_mult_mat_vec carrier_matD(1) carrier_mat_triv dim_col_of_dagger
        dim_mult_mat_vec ydim)
  also have "... = \<langle>?y | ?y\<rangle>"
    using inner_prod_adjoint_swap M_car xcar by simp
  finally show ?thesis .
qed

lemma diag_mat_of_real_hermitian:
  shows "hermitian (diag_mat_of_real D)"
  unfolding hermitian_def
proof (rule eq_matI)
  show "dim_row ((diag_mat_of_real D)\<^sup>\<dagger>) = dim_row (diag_mat_of_real D)"
    by simp
  show "dim_col ((diag_mat_of_real D)\<^sup>\<dagger>) = dim_col (diag_mat_of_real D)"
    by simp
next
  fix i j
  assume ij: "i < dim_row (diag_mat_of_real D)" "j < dim_col (diag_mat_of_real D)"
  then have i: "i < length D" and j: "j < length D"
    by simp_all
  show "((diag_mat_of_real D)\<^sup>\<dagger>) $$ (i, j) = diag_mat_of_real D $$ (i, j)"
    using i j by (cases "i = j", simp_all add: dagger_def)
qed

text \<open>$U\,\mathrm{diag}(D)\,U^\dagger$ is positive whenever the real entries of $D$ are non-negative.\<close>

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
    have prep4: "(?D)\<^sup>\<dagger> = ?D" using diag_mat_of_real_hermitian[unfolded hermitian_def] .
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

lemma diag_mat_of_real_sqrt_square:
  assumes D_nonneg: "\<And>i. i < length D \<Longrightarrow> 0 \<le> D ! i"
  shows "diag_mat_of_real (map sqrt D) * diag_mat_of_real (map sqrt D) = diag_mat_of_real D"
proof (rule eq_matI)
  show "dim_row (diag_mat_of_real (map sqrt D) * diag_mat_of_real (map sqrt D)) =
        dim_row (diag_mat_of_real D)"
    by simp
  show "dim_col (diag_mat_of_real (map sqrt D) * diag_mat_of_real (map sqrt D)) =
        dim_col (diag_mat_of_real D)"
    by simp
next
  fix r c
  assume rc: "r < dim_row (diag_mat_of_real D)" "c < dim_col (diag_mat_of_real D)"
  then have rlt: "r < length D" and clt: "c < length D"
    by simp_all
  let ?S = "diag_mat_of_real (map sqrt D)"
  have "(?S * ?S) $$ (r, c) = (\<Sum>j = 0..<length D. ?S $$ (r, j) * ?S $$ (j, c))"
    using rlt clt by (simp add: scalar_prod_def lessThan_atLeast0)
  also have "\<dots> =
        (\<Sum>j = 0..<length D.
           (if r = j \<and> j = c
            then complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! c))
            else 0))"
    using rlt clt by (intro sum.cong refl, auto)
  also have "\<dots> = (if r = c then complex_of_real (D ! r) else 0)"
  proof (cases "r = c")
    case True
    then have sqrt_sq:
      "complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! r)) =
       complex_of_real (D ! r)"
      using D_nonneg rlt by (simp add: of_real_mult[symmetric])
    have "(\<Sum>j = 0..<length D.
           (if r = j \<and> j = c
            then complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! c))
            else 0))
          = complex_of_real (sqrt (D ! r)) * complex_of_real (sqrt (D ! r))"
      using True rlt by (subst sum.remove[where x=r], auto)
    then show ?thesis
      using True sqrt_sq by argo
  next
    case False
    then show ?thesis by simp
  qed
  also have "\<dots> = diag_mat_of_real D $$ (r, c)"
    using rlt clt by simp
  finally show "(?S * ?S) $$ (r, c) = diag_mat_of_real D $$ (r, c)" .
qed

theorem pd_iff_spanning:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and decomp: "P = outer_sum n vs"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "pd P \<longleftrightarrow>
         (\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> x \<noteq> 0\<^sub>v n \<longrightarrow>
            (\<exists>v \<in> set vs. \<langle>v | x\<rangle> \<noteq> 0))"
proof
  (* pd P \<longleftrightarrow> \<langle>x|Px\<rangle> > 0 for all x \<noteq> 0
            \<longleftrightarrow> \<Sum>|\<langle>vᵢ|x\<rangle>|² > 0 for all x \<noteq> 0
            \<longleftrightarrow> some \<langle>vᵢ|x\<rangle> \<noteq> 0 for all x \<noteq> 0
            \<longleftrightarrow> {vs} spans \<complex>^n. *)
  assume pdP: "pd P"
  show "\<forall>x. dim_vec x = n \<longrightarrow> x \<noteq> 0\<^sub>v n \<longrightarrow> (\<exists>v \<in> set vs. \<langle>v | x\<rangle> \<noteq> 0)"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdim: "dim_vec x = n" and xne: "x \<noteq> 0\<^sub>v n"
    show "\<exists>v\<in>set vs. \<langle>v | x\<rangle> \<noteq> 0"
    proof (rule ccontr)
      assume nex: "\<not> (\<exists>v\<in>set vs. \<langle>v | x\<rangle> \<noteq> 0)"
      let ?M = "mat_of_cols n vs"
      let ?y = "(?M\<^sup>\<dagger>) *\<^sub>v x"
      have ydim: "dim_vec ?y = length vs"
        using xdim vs_dim by (simp add: mat_of_cols_def)
      have yzero: "?y = 0\<^sub>v (length vs)"
      proof (rule eq_vecI)
        show "dim_vec ((mat_of_cols n vs)\<^sup>\<dagger> *\<^sub>v x) = dim_vec (0\<^sub>v (length vs))"
          using ydim by simp
      next
        fix i
        assume i: "i < dim_vec (0\<^sub>v (length vs))"
        then have ilt: "i < length vs"
          by simp
        have "?y $ i = \<langle>vs ! i | x\<rangle>"
          using mat_of_cols_dagger_mult_vec_index[OF xdim vs_dim ilt] .
        also have "\<dots> = 0"
          using nex ilt by auto
        finally show "((mat_of_cols n vs)\<^sup>\<dagger> *\<^sub>v x) $ i = 0\<^sub>v (length vs) $ i"
          using ilt by simp
      qed
      have qzero: "\<langle>x | P *\<^sub>v x\<rangle> = 0"
        using inner_prod_outer_sum_general[OF xdim vs_dim] decomp yzero ydim by simp
      have "Re (\<langle>x | P *\<^sub>v x\<rangle>) > 0"
        using pdP xdim xne sq unfolding pd_def by auto
      then show False
        using qzero by simp
    qed
  qed
next
  assume spanning: "\<forall>x. dim_vec x = n \<longrightarrow> x \<noteq> 0\<^sub>v n \<longrightarrow> (\<exists>v \<in> set vs. \<langle>v | x\<rangle> \<noteq> 0)"
  have herm: "hermitian P"
    using decomp outer_sum_hermitian unfolding hermitian_def by simp
  have pos:
    "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row P \<longrightarrow>
       x \<noteq> 0\<^sub>v (dim_row P) \<longrightarrow> 0 < Re \<langle>x | P *\<^sub>v x\<rangle>"
  proof (intro allI impI)
    fix x :: "complex Matrix.vec"
    assume xdimP: "dim_vec x = dim_row P"
      and xneP: "x \<noteq> 0\<^sub>v (dim_row P)"
    have Pdim: "dim_row P = n"
      using sq by simp
    have xdim: "dim_vec x = n"
      using xdimP Pdim by simp
    have xne: "x \<noteq> 0\<^sub>v n"
      using xneP Pdim by simp
    let ?M = "mat_of_cols n vs"
    let ?y = "(?M\<^sup>\<dagger>) *\<^sub>v x"
    have ydim: "dim_vec ?y = length vs"
      using xdim vs_dim by (simp add: mat_of_cols_def)
    obtain v where vset: "v \<in> set vs" and inn_ne: "\<langle>v | x\<rangle> \<noteq> 0"
      using spanning xdim xne by blast
    obtain i where ilt: "i < length vs" and vi: "vs ! i = v"
      using vset by (metis in_set_conv_nth)
    have yi_ne: "?y $ i \<noteq> 0"
      using mat_of_cols_dagger_mult_vec_index[OF xdim vs_dim ilt] inn_ne vi by simp
    have yne: "?y \<noteq> 0\<^sub>v (length vs)"
      using ilt yi_ne by force
    have qeq: "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>?y | ?y\<rangle>"
      using inner_prod_outer_sum_general[OF xdim vs_dim] decomp by simp
    have "0 < Re \<langle>?y | ?y\<rangle>"
      using inner_prod_with_itself_Re_non0 ydim yne by presburger
    thus "0 < Re \<langle>x | P *\<^sub>v x\<rangle>"
      using qeq by presburger
  qed
  show "pd P"
    unfolding pd_def using herm pos by simp
qed

subsection \<open>The positive square root\<close>

text \<open>\begin{notesremark}[Day 8]
Given $P\ge 0$ with $U^*PU=\diag(\lambda_1,\dots,\lambda_n)$, $\lambda_i\ge 0$, put
$P^{1/2}=U\diag(\lambda_1^{1/2},\dots,\lambda_n^{1/2})U^*$.  Then $P^{1/2}\ge 0$ and
$(P^{1/2})^2=P$.
\end{notesremark}
\<open>psd_sqrt P\<close> is defined as a choice of such a square root; \<open>psd_sqrt_exists\<close> is the
existence statement and \<open>psd_sqrt_props\<close> the defining properties.\<close>

definition psd_sqrt :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "psd_sqrt P \<equiv> (SOME Q. Q \<in> carrier_mat (dim_row P) (dim_row P) \<and> psd Q \<and> Q * Q = P)"

theorem psd_sqrt_exists:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>Q :: complex Matrix.mat.
         Q \<in> carrier_mat n n \<and> psd Q \<and> Q * Q = P"
proof -
  have herm: "hermitian P" using pos by (rule psd_hermitian)
  obtain U D where Uc: "U \<in> carrier_mat n n" and UU: "unitary U"
    and Dlen: "length D = n" and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq herm] by blast
  have Udagcar: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by auto
  have P_eq: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using hermitian_spectral_decomp_eq[OF Uc sq UU spec].
  have PU_eq_UD: "P * U = U * diag_mat_of_real D"
    using UU Uc hermitian_spectral_decomp_right local.spec sq by presburger
  have eig_nonneg:
    "\<forall>mu::complex. \<forall>v::complex Matrix.vec.
       v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0"
    using psd_iff_nonneg_eigenvalues[OF sq] pos by blast
  have D_nonneg: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  proof -
    fix i assume iltn: "i < n"
    let ?ui = "Matrix.col U i"
    have uidim: "dim_vec ?ui = n"
      using Uc by simp
    have ui_nonzero: "?ui \<noteq> 0\<^sub>v n"
    proof
      assume zero: "?ui = 0\<^sub>v n"
      have "\<parallel>?ui\<parallel> = (1 :: real)"
        using UU iltn Uc by (metis carrier_matD(2) unitary_unit_col)
      moreover have "\<parallel>?ui\<parallel> = 0"
        using zero uidim cpx_vec_length_zero_iff by metis
      ultimately show False by simp
    qed
    have eig: "P *\<^sub>v ?ui = complex_of_real (D ! i) \<cdot>\<^sub>v ?ui"
    proof (rule eq_vecI)
      show "dim_vec (P *\<^sub>v ?ui) = dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
        using sq uidim by simp
    next
      fix k
      assume k: "k < dim_vec (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui)"
      then have klt: "k < n"
        using uidim by simp
      have "(P *\<^sub>v ?ui) $ k = (P * U) $$ (k, i)"
        using sq Uc iltn klt by (metis carrier_matD(1,2) index_mult_mat(1) index_mult_mat_vec)
      also have "\<dots> = (U * diag_mat_of_real D) $$ (k, i)"
        using PU_eq_UD by simp
      also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
      proof -
        have "(U * diag_mat_of_real D) $$ (k, i) =
              (\<Sum>j = 0..<n. U $$ (k, j) * diag_mat_of_real D $$ (j, i))"
          using Uc Dlen klt iltn by (simp add: scalar_prod_def lessThan_atLeast0)
        also have "\<dots> =
              (\<Sum>j = 0..<n. (if j = i then U $$ (k, j) * complex_of_real (D ! i) else 0))"
          using Dlen iltn by (intro sum.cong refl, auto)
        also have "\<dots> = U $$ (k, i) * complex_of_real (D ! i)"
          using iltn by simp
        also have "\<dots> = complex_of_real (D ! i) * U $$ (k, i)"
          by (simp add: mult.commute)
        finally show ?thesis.
      qed
      also have "\<dots> = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k"
        using klt Uc by (simp add: iltn)
      finally show "(P *\<^sub>v ?ui) $ k = (complex_of_real (D ! i) \<cdot>\<^sub>v ?ui) $ k" .
    qed
    have "0 \<le> Re (complex_of_real (D ! i))"
      using eig eig_nonneg ui_nonzero uidim by blast
    thus "0 \<le> D ! i" by simp
  qed
  let ?sqrtD = "map sqrt D"
  have sqrtD_len: "length ?sqrtD = n" using Dlen by simp
  let ?S = "diag_mat_of_real ?sqrtD"
  let ?Q = "U * diag_mat_of_real ?sqrtD * (U\<^sup>\<dagger>)"
  (* Q \<in> carrier_mat n n by mult_carrier_mat. *)
  have Qcar: "?Q \<in> carrier_mat n n"
    using Uc Udagcar sqrtD_len by auto
  (* Q is hermitian: Q\<^sup>\<dagger> = U \<sqdot> \<surd>D\<^sup>\<dagger> \<sqdot> U\<^sup>\<dagger> = Q (since \<surd>D real-diagonal). *)
  have S_herm: "?S\<^sup>\<dagger> = ?S"
    using diag_mat_of_real_hermitian unfolding hermitian_def by simp
  have Q_herm: "hermitian ?Q"
  proof -
    have Qdag: "(?Q\<^sup>\<dagger>) = U * ?S * (U\<^sup>\<dagger>)"
    proof -
      have "(?Q\<^sup>\<dagger>) =  ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * (?S\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
        using Uc Udagcar sqrtD_len
        by (smt (verit, best) assoc_mult_mat carrier_matD(1) dagger_of_dagger_is_id dagger_of_prod
            diag_mat_of_real_carrier dim_col_diag_mat_of_real dim_col_of_dagger index_mult_mat(2))
      also have "... = U * ?S * (U\<^sup>\<dagger>)"
        using S_herm dagger_of_dagger_is_id by presburger
      finally show ?thesis.
    qed
    show ?thesis
      unfolding hermitian_def
      using Qcar Qdag by simp
  qed

  (* PSD: \<langle>x | Q x\<rangle> = \<langle>U\<^sup>\<dagger>x | \<surd>D U\<^sup>\<dagger>x\<rangle> \<ge> 0 since \<surd>D entries \<ge> 0. *)
  have Q_psd: "psd ?Q"
  proof -
    have sqrtD_nonneg: "\<And>i. i < length ?sqrtD \<Longrightarrow> 0 \<le> ?sqrtD ! i"
      by (simp add: D_nonneg Dlen)
    have nonneg: "\<forall>x :: complex Matrix.vec. dim_vec x = dim_row ?Q \<longrightarrow> 0 \<le> Re \<langle>x | ?Q *\<^sub>v x\<rangle>"
    proof (intro allI impI)
      fix x :: "complex Matrix.vec"
      assume xdimQ: "dim_vec x = dim_row ?Q"
      then have xdim: "dim_vec x = n"
        using Qcar by force
      let ?y = "U\<^sup>\<dagger> *\<^sub>v x"
      have ydim: "dim_vec ?y = n"
        using Uc by force
      have v_as_Uy: "U *\<^sub>v ?y = x"
      proof -
        have UdagU: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n"
          using Uc UU unfolding unitary_def by auto
        have "U *\<^sub>v ((U\<^sup>\<dagger>) *\<^sub>v x) = (U * (U\<^sup>\<dagger>)) *\<^sub>v x"
          using Uc Udagcar xdim by force
        also have "\<dots> = x"
          using UdagU xdim by force
        finally show ?thesis.
      qed
      have Qx_as: "?Q *\<^sub>v x = U *\<^sub>v (?S *\<^sub>v ?y)"
        using Uc Udagcar Qcar sqrtD_len xdim ydim
            by (smt (verit, ccfv_SIG) assoc_mult_mat_vec carrier_vec_dim_vec
                diag_mat_of_real_carrier mult_carrier_mat)
      have "\<langle>x | ?Q *\<^sub>v x\<rangle> = \<langle>U *\<^sub>v ?y | U *\<^sub>v (?S *\<^sub>v ?y)\<rangle>"
        using v_as_Uy Qx_as by simp
      also have "\<dots> = \<langle>?y | ?S *\<^sub>v ?y\<rangle>"
        using Uc inner_prod_adjoint_swap sqrtD_len v_as_Uy xdim by force
      finally have qeq: "\<langle>x | ?Q *\<^sub>v x\<rangle> = \<langle>?y | ?S *\<^sub>v ?y\<rangle>".
      show "0 \<le> Re \<langle>x | ?Q *\<^sub>v x\<rangle>"
        using diag_mat_of_real_quad_Re_nonneg[OF _ sqrtD_nonneg] sqrtD_len ydim qeq by auto
    qed
    show ?thesis
      unfolding psd_def using Q_herm nonneg by simp
  qed
  (* Q\<^sup>2 = U \<sqdot> \<surd>D \<sqdot> (U\<^sup>\<dagger>U) \<sqdot> \<surd>D \<sqdot> U\<^sup>\<dagger> = U \<sqdot> D \<sqdot> U\<^sup>\<dagger> = P. *)
  have S_square: "?S * ?S = diag_mat_of_real D"
    using diag_mat_of_real_sqrt_square[of D] D_nonneg Dlen by auto
  have UdagU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n"
    using Uc UU unfolding unitary_def by auto
  have QQ_eq: "?Q * ?Q = P"
  proof -
    have "?Q * ?Q = U * (?S * ?S) * (U\<^sup>\<dagger>)"
      by (smt (verit, best) Uc UdagU Udagcar assoc_mult_mat diag_mat_of_real_carrier
          mult_carrier_mat right_mult_one_mat sqrtD_len)
    also have "\<dots> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
      using S_square by simp
    also have "\<dots> = P"
      using P_eq by simp
    finally show ?thesis.
  qed
  show ?thesis using Qcar Q_psd QQ_eq by blast
qed
lemma psd_sqrt_props:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "psd_sqrt P \<in> carrier_mat n n"
    and "psd (psd_sqrt P)"
    and "psd_sqrt P * psd_sqrt P = P"
proof -
  have n: "dim_row P = n" using sq by auto
  have "\<exists>Q :: complex Matrix.mat.
          Q \<in> carrier_mat (dim_row P) (dim_row P) \<and> psd Q \<and> Q * Q = P"
    using psd_sqrt_exists[OF sq pos] n by simp
  from someI_ex[OF this]
  show "psd_sqrt P \<in> carrier_mat n n" and "psd (psd_sqrt P)" and "psd_sqrt P * psd_sqrt P = P"
    unfolding psd_sqrt_def using n by auto
qed


text \<open>The corollary of Day 4: $P>0$ iff $P=P^*$ and all eigenvalues are strictly positive.\<close>

lemma pd_iff_pos_eigenvalues:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
  shows "pd P \<longleftrightarrow>
         (hermitian P \<and>
          (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu))"
proof
  assume pd: "pd P"
  have dr: "dim_row P = n" using sq by auto
  have herm: "hermitian P" using pd by (simp add: pd_def)
  have ev: "\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu"
  proof (intro allI impI, elim conjE)
    fix mu :: complex and v :: "complex Matrix.vec"
    assume vnz: "v \<noteq> 0\<^sub>v n" and vd: "dim_vec v = n" and eig: "P *\<^sub>v v = mu \<cdot>\<^sub>v v"
    have pos: "0 < Re \<langle>v | P *\<^sub>v v\<rangle>" using pd vd vnz dr unfolding pd_def by auto
    have vv_re: "0 < Re \<langle>v | v\<rangle>"
    proof -
      have "\<langle>v | v\<rangle> \<noteq> 0" using vnz vd inner_prod_self_eq_zero_iff[of v] by simp
      moreover have "Im \<langle>v | v\<rangle> = 0" by (rule inner_prod_with_itself_Im)
      moreover have "0 \<le> Re \<langle>v | v\<rangle>" by (rule inner_prod_with_itself_Re)
      ultimately show ?thesis by (metis complex_eq_iff less_eq_real_def zero_complex.simps(1) zero_complex.simps(2))
    qed
    have "\<langle>v | P *\<^sub>v v\<rangle> = mu * \<langle>v | v\<rangle>" using eig by (simp add: inner_prod_right_smult')
    hence "Re \<langle>v | P *\<^sub>v v\<rangle> = Re mu * Re \<langle>v | v\<rangle>"
      using inner_prod_with_itself_Im[of v] by simp
    with pos have "0 < Re mu * Re \<langle>v | v\<rangle>" by simp
    thus "0 < Re mu" using vv_re zero_less_mult_pos2 by blast
  qed
  show "hermitian P \<and> (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu)"
    using herm ev by blast
next
  assume rhs: "hermitian P \<and> (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu)"
  have herm: "hermitian P" using rhs by blast
  have ev: "\<And>mu v. v \<noteq> 0\<^sub>v n \<Longrightarrow> dim_vec v = n \<Longrightarrow> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<Longrightarrow> 0 < Re mu"
    using rhs by blast
  have psd: "psd P"
  proof -
    have "\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
            v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 \<le> Re mu"
    proof (intro allI impI, elim conjE)
      fix mu :: complex and v :: "complex Matrix.vec"
      assume "v \<noteq> 0\<^sub>v n" "dim_vec v = n" "P *\<^sub>v v = mu \<cdot>\<^sub>v v"
      from ev[OF this] show "0 \<le> Re mu" by simp
    qed
    thus ?thesis using psd_iff_nonneg_eigenvalues[OF sq] herm by blast
  qed
  let ?Q = "psd_sqrt P"
  have Qc: "?Q \<in> carrier_mat n n" and Qpsd: "psd ?Q" and QQ: "?Q * ?Q = P"
    using psd_sqrt_props[OF sq psd] by auto
  have Qh: "?Q\<^sup>\<dagger> = ?Q" using psd_hermitian[OF Qpsd] by (simp add: hermitian_def)
  have dr: "dim_row P = n" using sq by auto
  show "pd P"
    unfolding pd_def dr
  proof (intro conjI allI impI)
    show "hermitian P" by (rule herm)
    fix x :: "complex Matrix.vec" assume xd: "dim_vec x = n" and xnz: "x \<noteq> 0\<^sub>v n"
    have xc: "x \<in> carrier_vec n" using xd by auto
    have Qx: "dim_vec (?Q *\<^sub>v x) = n" using Qc xd by auto
    have qf: "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle>"
    proof -
      have "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>x | ?Q *\<^sub>v (?Q *\<^sub>v x)\<rangle>"
        using QQ Qc xc by (metis assoc_mult_mat_vec)
      also have "\<dots> = \<langle>?Q\<^sup>\<dagger> *\<^sub>v x | ?Q *\<^sub>v x\<rangle>"
        using inner_prod_adjoint_swap[OF Qc xd Qx] .
      finally show ?thesis using Qh by simp
    qed
    have "?Q *\<^sub>v x \<noteq> 0\<^sub>v n"
    proof
      assume Qx0: "?Q *\<^sub>v x = 0\<^sub>v n"
      have "P *\<^sub>v x = ?Q *\<^sub>v (?Q *\<^sub>v x)" using QQ Qc xc by (metis assoc_mult_mat_vec)
      also have "\<dots> = 0\<^sub>v n" using Qx0 Qc by auto
      also have "\<dots> = (0 :: complex) \<cdot>\<^sub>v x" using xd by auto
      finally have "P *\<^sub>v x = (0 :: complex) \<cdot>\<^sub>v x" .
      from ev[OF xnz xd this] show False by simp
    qed
    hence "\<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle> \<noteq> 0" using Qx inner_prod_self_eq_zero_iff[of "?Q *\<^sub>v x"] by simp
    moreover have "Im \<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle> = 0" by (rule inner_prod_with_itself_Im)
    moreover have "0 \<le> Re \<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle>" by (rule inner_prod_with_itself_Re)
    ultimately show "0 < Re \<langle>x | P *\<^sub>v x\<rangle>"
      using qf by (metis complex_eq_iff less_eq_real_def zero_complex.simps(1) zero_complex.simps(2))
  qed
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

text \<open>Carrier of @{term \<open>outer_sum k vs\<close>}.\<close>

lemma outer_sum_carrier:
  "outer_sum k vs \<in> carrier_mat k k"
  by (auto simp: outer_sum_def)

lemma outer_sum_Nil: "outer_sum n [] = 0\<^sub>m n n"
  by (rule eq_matI) (auto simp: outer_sum_def scalar_prod_def)

lemma outer_sum_singleton_eq:
  assumes vd: "dim_vec v = n"
  shows "outer_sum n [v] = v \<oslash> v"
proof (rule eq_matI)
  have c: "v \<oslash> v \<in> carrier_mat n n" by (rule outer_prod_carrier[OF vd vd])
  fix i j assume "i < dim_row (v \<oslash> v)" "j < dim_col (v \<oslash> v)"
  hence i: "i < n" and j: "j < n" using carrier_matD[OF c] by auto
  show "outer_sum n [v] $$ (i,j) = (v \<oslash> v) $$ (i,j)"
    unfolding outer_sum_singleton_index[OF i j] using i j vd by (simp add: outer_prod_index)
qed (use carrier_matD[OF outer_prod_carrier[OF vd vd]] in auto)

text \<open>Cons-recursion for @{const outer_sum}: adds a rank-1 piece.\<close>

lemma outer_sum_Cons_split:
  assumes "\<forall>v \<in> set (u # us). dim_vec v = k"
  shows "outer_sum k (u # us)
           = outer_sum k [u] + outer_sum k us"
proof (rule eq_matI)
  let ?L = "outer_sum k (u # us)"
  let ?R1 = "outer_sum k [u]"
  let ?R2 = "outer_sum k us"
  have L_c: "?L \<in> carrier_mat k k" by (rule outer_sum_carrier)
  have R1_c: "?R1 \<in> carrier_mat k k" by (rule outer_sum_carrier)
  have R2_c: "?R2 \<in> carrier_mat k k" by (rule outer_sum_carrier)
  show "dim_row ?L = dim_row (?R1 + ?R2)" using L_c R1_c R2_c by simp
  show "dim_col ?L = dim_col (?R1 + ?R2)" using L_c R1_c R2_c by simp
  fix i j assume "i < dim_row (?R1 + ?R2)" "j < dim_col (?R1 + ?R2)"
  hence i_lt: "i < k" and j_lt: "j < k" using R1_c R2_c by auto
  have u_dim: "dim_vec u = k" using assms by simp
  have us_dim: "\<forall>v \<in> set us. dim_vec v = k" using assms by simp
  have uus_dim: "\<forall>v \<in> set (u # us). dim_vec v = k" using assms by simp
  have eqL: "?L $$ (i, j)
               = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) (u # us))"
    by (rule outer_sum_entry_sum_list[OF uus_dim i_lt j_lt])
  have eqR1: "?R1 $$ (i, j) = u $ i * cnj (u $ j)"
  proof -
    have "\<forall>v \<in> set [u]. dim_vec v = k" using u_dim by simp
    hence "?R1 $$ (i, j) = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) [u])"
      by (rule outer_sum_entry_sum_list[OF _ i_lt j_lt])
    thus ?thesis by simp
  qed
  have eqR2: "?R2 $$ (i, j) = sum_list (map (\<lambda>v. v $ i * cnj (v $ j)) us)"
    by (rule outer_sum_entry_sum_list[OF us_dim i_lt j_lt])
  show "?L $$ (i, j) = (?R1 + ?R2) $$ (i, j)"
    using eqL eqR1 eqR2 R1_c R2_c i_lt j_lt by simp
qed

lemma outer_sum_as_foldr:
  assumes "\<forall>v \<in> set vs. dim_vec v = n"
  shows "outer_sum n vs = foldr (\<lambda>v acc. v \<oslash> v + acc) vs (0\<^sub>m n n)"
  using assms
proof (induction vs)
  case Nil show ?case by (simp add: outer_sum_Nil)
next
  case (Cons v vs)
  have "outer_sum n (v # vs) = outer_sum n [v] + outer_sum n vs"
    using Cons.prems by (intro outer_sum_Cons_split) simp
  also have "outer_sum n [v] = v \<oslash> v" using Cons.prems by (intro outer_sum_singleton_eq) simp
  finally show ?case using Cons by simp
qed

lemma Tr_hermitian_Im_zero:
  assumes Pc: "P \<in> carrier_mat n n" and herm: "hermitian P"
  shows "Im (Tr P) = 0"
proof -
  have "Tr P = (\<Sum>r<n. P $$ (r,r))" using Pc by (simp add: Tr_def)
  moreover have "\<And>r. r < n \<Longrightarrow> Im (P $$ (r,r)) = 0"
  proof -
    fix r assume r: "r < n"
    have eq: "P $$ (r,r) = cnj (P $$ (r,r))"
      using hermitian_index[OF herm, of r r] r Pc by auto
    have "Im (P $$ (r,r)) = Im (cnj (P $$ (r,r)))" using eq by (rule arg_cong)
    also have "\<dots> = - Im (P $$ (r,r))" by simp
    finally show "Im (P $$ (r,r)) = 0" by simp
  qed
  ultimately show ?thesis by simp
qed

lemma Tr_hermitian_real:
  assumes Pc: "P \<in> carrier_mat n n" and herm: "hermitian P"
  shows "Tr P = complex_of_real (Re (Tr P))"
  using Tr_hermitian_Im_zero[OF assms] by (simp add: complex_eq_iff)

text \<open>A positive semidefinite matrix of trace zero is zero (the notes: ``given a non-zero
$P\ge0$, $\Tr(P)\ne0$'').\<close>

lemma psd_Tr_zero_imp_zero:
  assumes Pc: "P \<in> carrier_mat n n" and pos: "psd P" and tr0: "Tr P = 0"
  shows "P = 0\<^sub>m n n"
proof -
  obtain U :: "complex Matrix.mat" and D :: "real list"
    where Uc: "U \<in> carrier_mat n n" and UU: "unitary U" and Dlen: "length D = n"
      and Dnn: "\<forall>i < n. 0 \<le> D ! i"
      and PUD: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF Pc pos] by blast
  let ?D = "diag_mat_of_real D"
  have Dc: "?D \<in> carrier_mat n n" by (rule diag_mat_of_real_carrier[of D, unfolded Dlen])
  have Udc: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by (rule dagger_carrier)
  have UdU: "(U\<^sup>\<dagger>) * U = 1\<^sub>m n" using UU Uc by (simp add: unitary_def)
  have UDc: "U * ?D \<in> carrier_mat n n" using Uc Dc by simp
  have "Tr P = Tr ((U * ?D) * (U\<^sup>\<dagger>))" using PUD by simp
  also have "\<dots> = Tr ((U\<^sup>\<dagger>) * (U * ?D))"
    using UDc Udc Dlen Uc by (intro Tr_cyclic) auto
  also have "\<dots> = Tr (((U\<^sup>\<dagger>) * U) * ?D)"
    using assoc_mult_mat[OF Udc Uc Dc] by simp
  also have "\<dots> = Tr ?D" unfolding UdU left_mult_one_mat[OF Dc] ..
  also have "\<dots> = (\<Sum>i<n. complex_of_real (D ! i))"
    using Dlen by (simp add: Tr_def)
  finally have "(\<Sum>i<n. D ! i) = 0" using tr0 by (simp flip: of_real_sum)
  hence D0: "\<And>i. i < n \<Longrightarrow> D ! i = 0"
    using Dnn sum_nonneg_eq_0_iff[of "{..<n}" "\<lambda>i. D ! i"] by auto
  have Dz: "?D = 0\<^sub>m n n"
    by (rule eq_matI) (use Dlen D0 in auto)
  have "P = U * 0\<^sub>m n n * (U\<^sup>\<dagger>)" using PUD Dz by simp
  also have "\<dots> = 0\<^sub>m n n" using Uc Udc by simp
  finally show ?thesis .
qed

lemma outer_prod_self_psd:
  assumes "dim_vec v = n"
  shows "psd (v \<oslash> v)"
proof -
  have c: "v \<oslash> v \<in> carrier_mat n n" by (rule outer_prod_carrier[OF assms assms])
  have "v \<oslash> v = outer_sum n [v]"
  proof (rule eq_matI)
    fix i j assume "i < dim_row (outer_sum n [v])" "j < dim_col (outer_sum n [v])"
    hence i: "i < n" and j: "j < n" by simp_all
    show "(v \<oslash> v) $$ (i,j) = outer_sum n [v] $$ (i,j)"
      unfolding outer_sum_singleton_index[OF i j] using i j assms by (simp add: outer_prod_index)
  qed (use carrier_matD[OF c] in auto)
  thus ?thesis using outer_sum_psd[of "[v]" 1 n] assms by simp
qed

lemma hermitian_smult_real_mat:
  fixes M :: "complex Matrix.mat" and c :: real
  assumes Mcar: "M \<in> carrier_mat n n" and Mherm: "hermitian M"
  shows "hermitian (complex_of_real c \<cdot>\<^sub>m M)"
proof -
  let ?cM = "complex_of_real c \<cdot>\<^sub>m M"
  have cM_car: "?cM \<in> carrier_mat n n" using Mcar by simp
  have Mdag: "M\<^sup>\<dagger> = M" using Mherm by (simp add: hermitian_def)
  have "?cM\<^sup>\<dagger> = ?cM"
  proof (rule eq_matI)
    show "dim_row (?cM\<^sup>\<dagger>) = dim_row ?cM"
      using cM_car Mcar by (simp add: dim_row_of_dagger)
    show "dim_col (?cM\<^sup>\<dagger>) = dim_col ?cM"
      using cM_car Mcar by (simp add: dim_col_of_dagger)
  next
    fix i j
    assume i: "i < dim_row ?cM" and j: "j < dim_col ?cM"
    hence ij: "i < n" "j < n" using cM_car Mcar by simp_all
    have eq1: "?cM\<^sup>\<dagger> $$ (i, j) = cnj (?cM $$ (j, i))"
      unfolding dagger_def using ij cM_car Mcar by simp
    have eq2: "?cM $$ (j, i) = complex_of_real c * M $$ (j, i)"
      using ij Mcar by simp
    have eq3: "cnj (M $$ (j, i)) = M\<^sup>\<dagger> $$ (i, j)"
      unfolding dagger_def using ij Mcar by simp
    have "?cM\<^sup>\<dagger> $$ (i, j) = cnj (complex_of_real c) * cnj (M $$ (j, i))"
      using eq1 eq2 by simp
    also have "\<dots> = complex_of_real c * cnj (M $$ (j, i))" by simp
    also have "\<dots> = complex_of_real c * (M\<^sup>\<dagger>) $$ (i, j)" using eq3 by simp
    also have "\<dots> = complex_of_real c * M $$ (i, j)" using Mdag by simp
    also have "\<dots> = ?cM $$ (i, j)" using ij Mcar by simp
    finally show "?cM\<^sup>\<dagger> $$ (i, j) = ?cM $$ (i, j)" .
  qed
  thus ?thesis by (simp add: hermitian_def)
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

end
