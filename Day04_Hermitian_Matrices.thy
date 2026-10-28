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
  let ?w = "T *\<^sub>v unit_vec n q"
  have w: "dim_vec ?w = n" using T_carr by simp
  have "\<langle>unit_vec n p | ?w\<rangle> = (\<Sum>i = 0..<n. cnj (unit_vec n p $ i) * ?w $ i)"
    by (rule inner_prod_sum[OF _ w]) simp
  also have "\<dots> = (\<Sum>i = 0..<n. if i = p then ?w $ i else 0)"
    using p by (intro sum.cong refl) simp
  also have "\<dots> = ?w $ p" using p by simp
  also have "\<dots> = T $$ (p, q)" using T_carr p q by (simp add: scalar_prod_right_unit)
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
  have Tv: "T *\<^sub>v (c \<cdot>\<^sub>v unit_vec n i + d \<cdot>\<^sub>v unit_vec n j)
        = c \<cdot>\<^sub>v (T *\<^sub>v unit_vec n i) + d \<cdot>\<^sub>v (T *\<^sub>v unit_vec n j)"
    by (simp add: mult_add_distrib_mat_vec[OF sq] mult_mat_vec_smult_vec[OF sq])
  have "\<langle>a \<cdot>\<^sub>v unit_vec n i + b \<cdot>\<^sub>v unit_vec n j | T *\<^sub>v (c \<cdot>\<^sub>v unit_vec n i + d \<cdot>\<^sub>v unit_vec n j)\<rangle>
        = cnj a * c * \<langle>unit_vec n i | T *\<^sub>v unit_vec n i\<rangle> + cnj a * d * \<langle>unit_vec n i | T *\<^sub>v unit_vec n j\<rangle>
        + cnj b * c * \<langle>unit_vec n j | T *\<^sub>v unit_vec n i\<rangle> + cnj b * d * \<langle>unit_vec n j | T *\<^sub>v unit_vec n j\<rangle>"
    unfolding Tv
    by (subst inner_prod_expand)
       (simp_all only: inner_prod_distrib_left inner_prod_right_smult' index_unit_vec(3) index_smult_vec(2)
                       dim_mult_mat_vec carrier_matD[OF sq] mult_ac)
  thus ?thesis
    unfolding inner_unit_T_unit[OF sq i i] inner_unit_T_unit[OF sq i j] inner_unit_T_unit[OF sq j i] inner_unit_T_unit[OF sq j j] .
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
  fix i j assume "i < dim_row (0\<^sub>m n n)" "j < dim_col (0\<^sub>m n n)"
  hence ij: "i < n" "j < n" by simp_all
  have q: "cnj a * c * T $$ (i, i) + cnj a * d * T $$ (i, j) + cnj b * c * T $$ (j, i) + cnj b * d * T $$ (j, j) = 0"
    if "a = c" "b = d" for a b c d
    using zero[rule_format, of "a \<cdot>\<^sub>v unit_vec n i + b \<cdot>\<^sub>v unit_vec n j"] that
    unfolding polarization_helper[OF sq ij] by simp
  have Tii: "T $$ (i, i) = 0" using q[of 1 1 0 0] by simp
  have Tjj: "T $$ (j, j) = 0" using q[of 0 0 1 1] by simp
  have s: "T $$ (i, j) + T $$ (j, i) = 0" using q[of 1 1 1 1] by (simp add: Tii Tjj)
  have d: "T $$ (i, j) = T $$ (j, i)" using q[of 1 1 \<i> \<i>] by (simp add: Tii Tjj algebra_simps)
  have "T $$ (j, i) * 2 = 0" using s unfolding d mult_2_right .
  thus "T $$ (i, j) = 0\<^sub>m n n $$ (i, j)" using ij d by simp
qed (use sq in auto)

lemma mult_mat_vec_index:
  fixes A :: "'a::{comm_ring_1} Matrix.mat"
    and x :: "'a Matrix.vec"
  assumes A: "A \<in> carrier_mat m n"
      and x: "x \<in> carrier_vec n"
      and j: "j < m"
  shows "(A *\<^sub>v x) $ j = (\<Sum>i = 0..<n. A $$ (j, i) * x $ i)"
proof -
  have "(A *\<^sub>v x) $ j = (\<Sum>i = 0..<n. Matrix.row A j $ i * x $ i)" using A x j by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>i = 0..<n. A $$ (j, i) * x $ i)" using A j by (intro sum.cong refl) simp
  finally show ?thesis .
qed

lemma mult_mat_vec_unit_vec:
  fixes U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat n m" and i: "i < m"
  shows "U *\<^sub>v unit_vec m i = Matrix.col U i"
  using U i by (intro eq_vecI) auto

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
  have "\<langle>x | M *\<^sub>v y\<rangle> = (\<Sum>j<n. \<Sum>i<m. cnj (x $ j) * (M $$ (j, i) * y $ i))"
    unfolding inner_prod_sum[OF x dim_mult_mat_vec[of M y, unfolded carrier_matD(1)[OF M]]] atLeast0LessThan
    by (rule sum.cong[OF refl]) (simp add: mult_mat_vec_index[OF M carrier_vecI[OF y]] atLeast0LessThan sum_distrib_left)
  also have "\<dots> = (\<Sum>i<m. \<Sum>j<n. cnj (M\<^sup>\<dagger> $$ (i, j) * x $ j) * y $ i)"
    by (simp add: sum.swap[of _ "{..<n}" "{..<m}"] dagger_def carrier_matD[OF M] mult_ac)
  also have "\<dots> = \<langle>M\<^sup>\<dagger> *\<^sub>v x | y\<rangle>"
    unfolding inner_prod_sum[OF dim_mult_mat_vec[of "M\<^sup>\<dagger>" x, unfolded carrier_matD(1)[OF dagger_carrier[OF M]]] y]
              atLeast0LessThan
    by (rule sum.cong[OF refl])
       (simp add: mult_mat_vec_index[OF dagger_carrier[OF M] carrier_vecI[OF x]] atLeast0LessThan cnj_sum sum_distrib_right)
  finally show ?thesis .
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
proof -
  have swap: "cnj \<langle>x | A *\<^sub>v x\<rangle> = \<langle>x | A\<^sup>\<dagger> *\<^sub>v x\<rangle>" if x: "dim_vec x = n" for x
    using inner_prod_cnj[of x "A *\<^sub>v x"] inner_prod_adjoint_swap[OF dagger_carrier[OF sq] x x] sq x
    by (simp add: dagger_of_dagger_is_id)
  show ?thesis
  proof
    assume "hermitian A"
    thus "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
      unfolding hermitian_def Reals_cnj_iff using swap by simp
  next
    assume real: "\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> \<langle>x | A *\<^sub>v x\<rangle> \<in> \<real>"
    have "\<langle>x | (A - (A\<^sup>\<dagger>)) *\<^sub>v x\<rangle> = 0" if x: "dim_vec x = n" for x
    proof -
      have d: "dim_vec (A *\<^sub>v x) = dim_vec (A\<^sup>\<dagger> *\<^sub>v x)" using sq by simp
      show ?thesis
        unfolding minus_mult_distrib_mat_vec[OF sq dagger_carrier[OF sq] carrier_vecI[OF x]]
                  inner_prod_right_minus'[OF d] swap[OF x, symmetric]
        using real[rule_format, OF x] unfolding Reals_cnj_iff by simp
    qed
    hence z: "A - (A\<^sup>\<dagger>) = 0\<^sub>m n n"
      by (intro quadratic_form_zero[OF minus_carrier_mat[OF dagger_carrier[OF sq]]]) blast
    show "hermitian A" unfolding hermitian_def
    proof (intro eq_matI)
      fix i j assume "i < dim_row A" "j < dim_col A"
      with z show "A\<^sup>\<dagger> $$ (i, j) = A $$ (i, j)"
        using sq by (auto dest!: arg_cong[where f = "\<lambda>M. M $$ (i, j)"])
    qed (use sq in auto)
  qed
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

lemma col_diag_mat_of_real:
  assumes i: "i < length D"
  shows "Matrix.col (diag_mat_of_real D) i = complex_of_real (D ! i) \<cdot>\<^sub>v unit_vec (length D) i"
  using i by (intro eq_vecI) (auto simp: diag_mat_of_real_def mat_diag_def)

lemma diag_mat_of_real_hermitian: "hermitian (diag_mat_of_real D)"
  unfolding hermitian_def by (rule eq_matI) (auto simp: dagger_def)

lemma diag_mat_of_real_sqrt_square:
  assumes D_nonneg: "\<And>i. i < length D \<Longrightarrow> 0 \<le> D ! i"
  shows "diag_mat_of_real (map sqrt D) * diag_mat_of_real (map sqrt D) = diag_mat_of_real D"
proof (rule eq_matI)
  let ?S = "diag_mat_of_real (map sqrt D)"
  fix i j assume "i < dim_row (diag_mat_of_real D)" "j < dim_col (diag_mat_of_real D)"
  hence ij: "i < length D" "j < length D" by simp_all
  have "(?S * ?S) $$ (i, j) = (\<Sum>k = 0..<length D. ?S $$ (i, k) * ?S $$ (k, j))"
    using ij by (simp add: scalar_prod_def lessThan_atLeast0)
  also have "\<dots> = (\<Sum>k = 0..<length D. if k = i then ?S $$ (i, i) * ?S $$ (i, j) else 0)"
    using ij by (intro sum.cong refl) auto
  also have "\<dots> = ?S $$ (i, i) * ?S $$ (i, j)" using ij by (simp add: sum.delta)
  finally show "(?S * ?S) $$ (i, j) = diag_mat_of_real D $$ (i, j)"
    using ij D_nonneg by (simp add: of_real_mult[symmetric])
qed simp_all

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
  obtain U T where U: "U \<in> carrier_mat n n" and T: "T \<in> carrier_mat n n" and uU: "unitary U"
    and ut: "upper_triangular T" and UHU: "(U\<^sup>\<dagger>) * H * U = T"
    using schur_theorem[OF sq] by blast
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have d1: "dim_col (U\<^sup>\<dagger> * H) = dim_row U" using Ud sq U by simp
  have d2: "dim_col (U\<^sup>\<dagger>) = dim_row H" using U sq by simp
  have "T\<^sup>\<dagger> = U\<^sup>\<dagger> * (H\<^sup>\<dagger> * U)"
    unfolding UHU[symmetric] dagger_of_prod[OF d1] dagger_of_prod[OF d2] dagger_of_dagger_is_id ..
  also have "\<dots> = T" unfolding herm[unfolded hermitian_def] assoc_mult_mat[OF Ud sq U, symmetric] UHU ..
  finally have hT: "hermitian T" unfolding hermitian_def .
  have Tij: "T $$ (i, j) = cnj (T $$ (j, i))" if "i < n" "j < n" for i j
    by (rule hermitian_index[OF hT]) (use that T in simp_all)
  have off: "T $$ (i, j) = 0" if "i < n" "j < n" "i \<noteq> j" for i j
  proof (cases "j < i")
    case True thus ?thesis using ut that T unfolding upper_triangular_def by simp
  next
    case False
    hence "T $$ (j, i) = 0" using ut that T unfolding upper_triangular_def by simp
    thus ?thesis unfolding Tij[OF that(1,2)] by simp
  qed
  have diag: "complex_of_real (Re (T $$ (i, i))) = T $$ (i, i)" if "i < n" for i
  proof -
    have "Im (T $$ (i, i)) = 0" using arg_cong[OF Tij[OF that that], of Im] by simp
    thus ?thesis by (simp add: complex_eq_iff)
  qed
  let ?D = "map (\<lambda>i. Re (T $$ (i, i))) [0..<n]"
  have "T = diag_mat_of_real ?D" using T by (intro eq_matI) (auto simp: off diag)
  thus ?thesis using U uU UHU by (intro exI[of _ U] exI[of _ ?D]) simp
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

text \<open>The spectral decomposition as $P=UDU^*$ and $PU=UD$: the columns of $U$ are eigenvectors of
$P$ for the eigenvalues $D_i$.\<close>

lemma hermitian_spectral_decomp_eq:
  assumes Uc: "U \<in> carrier_mat n n"
      and Pcar: "P \<in> carrier_mat n n"
      and unit: "unitary U"
      and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
  shows "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
proof -
  have "U * (U\<^sup>\<dagger> * P * U) * (U\<^sup>\<dagger>) = P"
    using unitary_conj_cancel[OF dagger_carrier[OF Uc] unitary_dagger[OF unit] Pcar]
    by (simp add: dagger_of_dagger_is_id)
  thus ?thesis unfolding spec by (rule sym)
qed

lemma hermitian_spectral_decomp_right:
  assumes Uc: "U \<in> carrier_mat n n"
      and Pcar: "P \<in> carrier_mat n n"
      and unit: "unitary U"
      and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
  shows "P * U = U * diag_mat_of_real D"
proof -
  have D: "length D = n" using arg_cong[OF spec, of dim_row] Uc Pcar by simp
  have UD: "U * diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] D Uc by simp
  have UdU: "U\<^sup>\<dagger> * U = 1\<^sub>m n" using unit Uc by (simp add: unitary_def)
  have "P * U = U * diag_mat_of_real D * (U\<^sup>\<dagger>) * U"
    by (simp only: hermitian_spectral_decomp_eq[OF Uc Pcar unit spec])
  also have "\<dots> = U * diag_mat_of_real D * (U\<^sup>\<dagger> * U)"
    by (rule assoc_mult_mat[OF UD dagger_carrier[OF Uc] Uc])
  finally show ?thesis unfolding UdU by (simp add: right_mult_one_mat[OF UD])
qed

lemma spectral_col_eigenvector:
  assumes U: "U \<in> carrier_mat n n" and H: "H \<in> carrier_mat n n" and Uu: "unitary U"
      and spec: "U\<^sup>\<dagger> * H * U = diag_mat_of_real D" and i: "i < n"
  shows "H *\<^sub>v Matrix.col U i = complex_of_real (D ! i) \<cdot>\<^sub>v Matrix.col U i"
proof -
  have D: "length D = n" using arg_cong[OF spec, of dim_row] U H by simp
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] D by simp
  have "H *\<^sub>v Matrix.col U i = Matrix.col (H * U) i" using col_mult2[OF H U i] by simp
  also have "H * U = U * diag_mat_of_real D" by (rule hermitian_spectral_decomp_right[OF U H Uu spec])
  also have "Matrix.col (U * diag_mat_of_real D) i = U *\<^sub>v (complex_of_real (D ! i) \<cdot>\<^sub>v unit_vec n i)"
    using col_mult2[OF U Dc i] col_diag_mat_of_real[of i D] i D by simp
  also have "\<dots> = complex_of_real (D ! i) \<cdot>\<^sub>v Matrix.col U i"
    using mult_mat_vec_unit_vec[OF U i] U i by (simp add: mult_mat_vec_smult_vec)
  finally show ?thesis .
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
orthogonal to every $v_i$''.  Formally $P\ge0$ and $P>0$ are \<open>psd P\<close> and \<open>pd P\<close>,
displayed \<open>P \<ge>\<^sub>M 0\<close> and \<open>P >\<^sub>M 0\<close>.\<close>

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

text \<open>A positive $1\times1$ matrix is a non-negative real number.\<close>

lemma psd_one_by_one:
  fixes A :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat 1 1" and psd: "psd A"
  shows "A $$ (0, 0) \<in> \<real>" and "0 \<le> Re (A $$ (0, 0))"
proof -
  have "cnj (A $$ (0, 0)) = A $$ (0, 0)"
    by (rule hermitian_index[OF psd_hermitian[OF psd], symmetric]) (simp_all add: carrier_matD[OF A])
  thus "A $$ (0, 0) \<in> \<real>" unfolding Reals_cnj_iff .
  have e: "dim_vec (unit_vec 1 0 :: complex Matrix.vec) = 1" by simp
  have "\<langle>unit_vec 1 0 | A *\<^sub>v unit_vec 1 0\<rangle> = A $$ (0, 0)"
    unfolding inner_prod_sum[OF e dim_mult_mat_vec[of A "unit_vec 1 0", unfolded carrier_matD(1)[OF A]]]
    by (simp add: mult_mat_vec_index[OF A] eval_nat_numeral)
  thus "0 \<le> Re (A $$ (0, 0))"
    using psd[unfolded psd_def, THEN conjunct2, rule_format, of "unit_vec 1 0"] A by simp
qed

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
  unfolding psd_iff_quad_form_nonneg[OF mult_carrier_mat[OF dagger_carrier[OF M] M]]
proof (intro allI impI)
  fix x :: "complex Matrix.vec" assume x: "dim_vec x = m"
  have "\<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> = \<langle>M *\<^sub>v x | M *\<^sub>v x\<rangle>"
    unfolding assoc_mult_mat_vec[OF dagger_carrier[OF M] M carrier_vecI[OF x]]
              inner_prod_adjoint_swap[OF dagger_carrier[OF M] x dim_mult_mat_vec[of M x, unfolded carrier_matD(1)[OF M]]]
              dagger_of_dagger_is_id ..
  thus "\<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle> \<in> \<real> \<and> 0 \<le> Re \<langle>x | (M\<^sup>\<dagger> * M) *\<^sub>v x\<rangle>"
    using inner_prod_with_itself_Re[of "M *\<^sub>v x"] inner_prod_cnj[of "M *\<^sub>v x" "M *\<^sub>v x"]
    by (simp add: Reals_cnj_iff)
qed

text \<open>Congruence preserves positivity: $P\ge0$ implies $M^*PM\ge0$, since
$\braket x{M^*PMx}=\braket{Mx}{P\,Mx}$.\<close>

lemma psd_conjugate:
  fixes P :: "complex Matrix.mat" and M :: "complex Matrix.mat"
  assumes P_c: "P \<in> carrier_mat k k"
      and P_psd: "psd P"
      and M_c: "M \<in> carrier_mat k n"
  shows "psd (M\<^sup>\<dagger> * P * M)"
  unfolding psd_iff_quad_form_nonneg[OF mult_carrier_mat[OF mult_carrier_mat[OF dagger_carrier[OF M_c] P_c] M_c]]
proof (intro allI impI)
  fix x :: "complex Matrix.vec" assume x: "dim_vec x = n"
  have Mx: "dim_vec (M *\<^sub>v x) = k" and PMx: "dim_vec (P *\<^sub>v (M *\<^sub>v x)) = k" using M_c P_c by simp_all
  have "\<langle>x | (M\<^sup>\<dagger> * P * M) *\<^sub>v x\<rangle> = \<langle>M *\<^sub>v x | P *\<^sub>v (M *\<^sub>v x)\<rangle>"
    unfolding assoc_mult_mat_vec[OF mult_carrier_mat[OF dagger_carrier[OF M_c] P_c] M_c carrier_vecI[OF x]]
              assoc_mult_mat_vec[OF dagger_carrier[OF M_c] P_c carrier_vecI[OF Mx]]
              inner_prod_adjoint_swap[OF dagger_carrier[OF M_c] x PMx] dagger_of_dagger_is_id ..
  thus "\<langle>x | (M\<^sup>\<dagger> * P * M) *\<^sub>v x\<rangle> \<in> \<real> \<and> 0 \<le> Re \<langle>x | (M\<^sup>\<dagger> * P * M) *\<^sub>v x\<rangle>"
    using P_psd[unfolded psd_iff_quad_form_nonneg[OF P_c], rule_format, OF Mx] by simp
qed

text \<open>$U\,\mathrm{diag}(D)\,U^\dagger$ is positive whenever the real entries of $D$ are non-negative.\<close>

lemma psd_diag_mat_of_real:
  assumes Dnn: "\<And>i. i < length D \<Longrightarrow> 0 \<le> D ! i"
  shows "psd (diag_mat_of_real D)"
proof -
  have "diag_mat_of_real D = (diag_mat_of_real (map sqrt D))\<^sup>\<dagger> * diag_mat_of_real (map sqrt D)"
    using diag_mat_of_real_hermitian[of "map sqrt D"] diag_mat_of_real_sqrt_square[OF Dnn] by (simp add: hermitian_def)
  thus ?thesis using psd_MdagM[OF diag_mat_of_real_carrier] by simp
qed

lemma psd_U_diag_Udag:
  fixes U :: "complex Matrix.mat" and D :: "real list"
  assumes Uc: "U \<in> carrier_mat n n"
      and Dlen: "length D = n"
      and Dnn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D ! i"
  shows "psd (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
proof -
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] Dlen by simp
  have "psd ((U\<^sup>\<dagger>)\<^sup>\<dagger> * diag_mat_of_real D * (U\<^sup>\<dagger>))"
    by (rule psd_conjugate[OF Dc psd_diag_mat_of_real dagger_carrier[OF Uc]]) (use Dnn Dlen in simp)
  thus ?thesis by (simp add: dagger_of_dagger_is_id)
qed

text \<open>$\Tr(UDU^*)=\sum_iD_i$.\<close>

lemma Tr_unitary_diag:
  assumes U: "U \<in> carrier_mat n n" and Uu: "unitary U" and D: "length D = n"
  shows "Tr (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) = complex_of_real (sum_list D)"
proof -
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] D by simp
  have "Tr (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) = Tr (diag_mat_of_real D)"
    using Tr_unitary_conjugation[OF unitary_dagger[OF Uu], of "diag_mat_of_real D"] U D
    by (simp add: dagger_of_dagger_is_id)
  also have "\<dots> = complex_of_real (sum_list D)"
    using D by (simp add: Tr_def diag_mat_of_real_def mat_diag_def sum_list_sum_nth atLeast0LessThan)
  finally show ?thesis .
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
  have "Re mu \<ge> 0" if v: "v \<noteq> 0\<^sub>v n" "dim_vec v = n" and eig: "P *\<^sub>v v = mu \<cdot>\<^sub>v v" for mu v
  proof -
    have "\<parallel>v\<parallel> \<noteq> 0" using v by (simp add: cpx_vec_length_zero_iff)
    hence pos': "0 < (\<parallel>v\<parallel>)\<^sup>2" by simp
    have R: "\<And>r. Re (mu * complex_of_real r) = Re mu * r" by simp
    have "\<langle>v | P *\<^sub>v v\<rangle> = mu * \<langle>v|v\<rangle>" by (simp only: eig inner_prod_right_smult')
    also have "\<langle>v|v\<rangle> = complex_of_real ((\<parallel>v\<parallel>)\<^sup>2)" by (simp only: cpx_vec_length_inner_prod)
    finally have "Re \<langle>v | P *\<^sub>v v\<rangle> = Re mu * (\<parallel>v\<parallel>)\<^sup>2" by (simp only: R)
    moreover have "dim_vec v = dim_row P" using v sq by simp
    hence "0 \<le> Re \<langle>v | P *\<^sub>v v\<rangle>" using pos unfolding psd_def by blast
    ultimately show ?thesis using pos' by (auto simp: zero_le_mult_iff)
  qed
  thus "hermitian P \<and> (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
          v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0)"
    using psd_hermitian[OF pos] by blast
next
  assume rhs: "hermitian P \<and> (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
          v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> Re mu \<ge> 0)"
  obtain U D where U: "U \<in> carrier_mat n n" and Uu: "unitary U" and D: "length D = n"
    and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq conjunct1[OF rhs]] by blast
  have nn: "0 \<le> D ! i" if i: "i < n" for i
  proof -
    have "\<langle>Matrix.col U i | Matrix.col U i\<rangle> = 1" using unitary_cols_orthonormal[OF Uu] i U by simp
    hence "Matrix.col U i \<noteq> 0\<^sub>v n" using U by (auto simp: scalar_prod_right_zero)
    thus ?thesis
      using conjunct2[OF rhs, rule_format, where mu = "complex_of_real (D ! i)" and v = "Matrix.col U i"]
            spectral_col_eigenvector[OF U sq Uu spec i] U by simp
  qed
  show "psd P" unfolding hermitian_spectral_decomp_eq[OF U sq Uu spec] by (rule psd_U_diag_Udag[OF U D nn])
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

text \<open>The spectral theorem for positive matrices: $P=U\,\mathrm{diag}(D)\,U^\dagger$ with $D\ge0$, since
$D_i=\braket{u_i}{Pu_i}$ for the columns $u_i$ of $U$.\<close>

lemma psd_spectral_decomp_nonneg:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>(U :: complex Matrix.mat) (D :: real list).
           U \<in> carrier_mat n n \<and> unitary U \<and> length D = n \<and>
           (\<forall>i < n. 0 \<le> D ! i) \<and>
           P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
proof -
  obtain U D where U: "U \<in> carrier_mat n n" and Uu: "unitary U" and D: "length D = n"
    and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF sq psd_hermitian[OF pos]] by blast
  have nn: "0 \<le> D ! i" if i: "i < n" for i
  proof -
    let ?u = "Matrix.col U i"
    have "\<langle>?u | P *\<^sub>v ?u\<rangle> = complex_of_real (D ! i) * \<langle>?u|?u\<rangle>"
      by (simp add: spectral_col_eigenvector[OF U sq Uu spec i] inner_prod_right_smult')
    also have "\<langle>?u|?u\<rangle> = 1" using unitary_cols_orthonormal[OF Uu] i U by simp
    finally have "Re \<langle>?u | P *\<^sub>v ?u\<rangle> = D ! i" by simp
    moreover have "dim_vec ?u = dim_row P" using U sq by simp
    hence "0 \<le> Re \<langle>?u | P *\<^sub>v ?u\<rangle>" using pos unfolding psd_def by blast
    ultimately show ?thesis by simp
  qed
  show ?thesis
    using U Uu D nn hermitian_spectral_decomp_eq[OF U sq Uu spec] by (intro exI[of _ U] exI[of _ D]) simp
qed

text \<open>A positive matrix is dominated by a multiple of $I$: $I-cA\ge0$ for some $c>0$.\<close>

lemma psd_scale_below_one:
  fixes A :: "complex Matrix.mat"
  assumes A: "A \<in> carrier_mat n n" and psd: "psd A"
  shows "\<exists>c > 0. psd (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m A)"
proof -
  obtain U D where U: "U \<in> carrier_mat n n" and UU: "unitary U" and D: "length D = n"
    and AUDU: "A = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF A psd] by blast
  define c where "c = 1 / (1 + sum_list (map abs D))"
  have S: "0 \<le> sum_list (map abs D)" by (rule sum_list_nonneg) auto
  have c: "0 < c" unfolding c_def using S by (auto intro: add_pos_nonneg)
  have cD: "c * D ! i \<le> 1" if "i < n" for i
  proof -
    have "\<bar>D ! i\<bar> \<le> sum_list (map abs D)" using that D by (intro member_le_sum_list) auto
    hence "D ! i \<le> 1 + sum_list (map abs D)" by linarith
    thus ?thesis unfolding c_def using S by (simp add: pos_divide_le_eq add_pos_nonneg)
  qed
  define D' where "D' = map (\<lambda>d. 1 - c * d) D"
  have D': "length D' = n" "\<And>i. i < n \<Longrightarrow> 0 \<le> D' ! i" using cD D by (simp_all add: D'_def)
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] unfolding D .
  have diagD': "diag_mat_of_real D' = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D"
    using D D' by (intro eq_matI) (auto simp: diag_mat_of_real_def mat_diag_def D'_def)
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have "U * diag_mat_of_real D' * (U\<^sup>\<dagger>) = U * (U\<^sup>\<dagger>) - complex_of_real c \<cdot>\<^sub>m (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
    unfolding diagD'
    by (simp only: mult_minus_distrib_mat[OF U one_carrier_mat smult_carrier_mat[OF Dc]]
                   minus_mult_distrib_mat[OF U smult_carrier_mat[OF mult_carrier_mat[OF U Dc]] Ud]
                   right_mult_one_mat[OF U] mult_smult_distrib[OF U Dc] mult_smult_assoc_mat[OF mult_carrier_mat[OF U Dc] Ud])
  hence eq: "1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m A = U * diag_mat_of_real D' * (U\<^sup>\<dagger>)"
    using unitary_inv_r_dimrow[OF UU] U AUDU by simp
  have "psd (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m A)"
    unfolding eq by (rule psd_U_diag_Udag[OF U D'(1) D'(2)])
  thus ?thesis using c by blast
qed

text \<open>The direction $\Rightarrow$, from the spectral theorem:
$P=\sum_j\lambda_j\ketbra{u_j}{u_j}=\sum_j\ketbra{\lambda_j^{1/2}u_j}{\lambda_j^{1/2}u_j}$, the columns of
$U\sqrt D$.\<close>

theorem psd_kraus_decomp:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and pos: "psd P"
  shows "\<exists>vs :: complex Matrix.vec list.
         length vs = n \<and>
         (\<forall>v \<in> set vs. dim_vec v = n) \<and>
         outer_sum n vs = P"
proof -
  obtain U D where U: "U \<in> carrier_mat n n" and Uu: "unitary U" and D: "length D = n"
    and Dnn: "\<forall>i < n. 0 \<le> D ! i" and P: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF sq pos] by blast
  let ?S = "diag_mat_of_real (map sqrt D)"
  let ?vs = "map (\<lambda>i. complex_of_real (sqrt (D ! i)) \<cdot>\<^sub>v Matrix.col U i) [0..<n]"
  have Sc: "?S \<in> carrier_mat n n" using diag_mat_of_real_carrier[of "map sqrt D"] D by simp
  have Sh: "?S\<^sup>\<dagger> = ?S" using diag_mat_of_real_hermitian[of "map sqrt D"] by (simp add: hermitian_def)
  have dc: "dim_col U = dim_row ?S" using carrier_matD[OF U] carrier_matD[OF Sc] by simp
  have M: "mat_of_cols n ?vs = U * ?S"
    using U D by (intro eq_matI) (auto simp: mat_of_cols_index mat_diag_mult_right[OF U] diag_mat_of_real_def mult.commute)
  have "outer_sum n ?vs = (U * ?S) * (?S * (U\<^sup>\<dagger>))"
    unfolding outer_sum_def M by (simp only: dagger_of_prod[OF dc] Sh)
  also have "\<dots> = U * (?S * ?S) * (U\<^sup>\<dagger>)"
    by (simp only: assoc_mult_mat[OF U Sc mult_carrier_mat[OF Sc dagger_carrier[OF U]]]
                   assoc_mult_mat[OF Sc Sc dagger_carrier[OF U], symmetric] assoc_mult_mat[OF U mult_carrier_mat[OF Sc Sc] dagger_carrier[OF U]])
  also have "?S * ?S = diag_mat_of_real D" by (rule diag_mat_of_real_sqrt_square) (use Dnn D in simp)
  finally have "outer_sum n ?vs = P" by (simp add: P)
  thus ?thesis using U by (intro exI[of _ ?vs]) simp
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

theorem pd_iff_spanning:
  fixes P :: "complex Matrix.mat"
  assumes sq: "P \<in> carrier_mat n n"
      and decomp: "P = outer_sum n vs"
      and vs_dim: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "pd P \<longleftrightarrow>
         (\<forall>x :: complex Matrix.vec. dim_vec x = n \<longrightarrow> x \<noteq> 0\<^sub>v n \<longrightarrow>
            (\<exists>v \<in> set vs. \<langle>v | x\<rangle> \<noteq> 0))"
proof -
  let ?y = "\<lambda>x. (mat_of_cols n vs)\<^sup>\<dagger> *\<^sub>v x"
  have yd: "dim_vec (?y x) = length vs" for x by (simp add: mat_of_cols_def)
  have yi: "?y x $ i = \<langle>vs ! i | x\<rangle>" if "dim_vec x = n" "i < length vs" for x i
    by (rule mat_of_cols_dagger_mult_vec_index[OF that(1) vs_dim that(2)])
  have y0: "?y x = 0\<^sub>v (length vs) \<longleftrightarrow> (\<forall>v \<in> set vs. \<langle>v | x\<rangle> = 0)" if x: "dim_vec x = n" for x
    unfolding all_set_conv_all_nth
  proof (intro iffI allI impI)
    fix i assume z: "?y x = 0\<^sub>v (length vs)" and i: "i < length vs"
    from arg_cong[OF z, where f = "\<lambda>z. z $ i"] show "\<langle>vs ! i | x\<rangle> = 0" unfolding yi[OF x i] using i by simp
  next
    assume a: "\<forall>i<length vs. \<langle>vs ! i | x\<rangle> = 0"
    show "?y x = 0\<^sub>v (length vs)"
    proof (intro eq_vecI)
      fix i assume "i < dim_vec (0\<^sub>v (length vs))"
      hence i: "i < length vs" by simp
      show "?y x $ i = 0\<^sub>v (length vs) $ i" unfolding yi[OF x i] using a i by simp
    qed (simp add: yd)
  qed
  have q: "\<langle>x | P *\<^sub>v x\<rangle> = \<langle>?y x | ?y x\<rangle>" if "dim_vec x = n" for x
    unfolding decomp by (rule inner_prod_outer_sum_general[OF that vs_dim])
  have pos_iff: "0 < Re \<langle>?y x | ?y x\<rangle> \<longleftrightarrow> ?y x \<noteq> 0\<^sub>v (length vs)" for x
    using inner_prod_with_itself_Re_non0[of "?y x"] inner_prod_self_eq_zero_iff[of "?y x"] yd[of x] by auto
  have herm: "hermitian P" unfolding decomp hermitian_def by (rule outer_sum_hermitian)
  have key: "0 < Re \<langle>x | P *\<^sub>v x\<rangle> \<longleftrightarrow> (\<exists>v \<in> set vs. \<langle>v | x\<rangle> \<noteq> 0)" if x: "dim_vec x = n" for x
    unfolding q[OF x] pos_iff y0[OF x] by blast
  show ?thesis unfolding pd_def carrier_matD(1)[OF sq] using herm key by blast
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
  obtain U D where U: "U \<in> carrier_mat n n" and Uu: "unitary U" and D: "length D = n"
    and Dnn: "\<forall>i < n. 0 \<le> D ! i" and P: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF sq pos] by blast
  let ?S = "diag_mat_of_real (map sqrt D)"
  have Sc: "?S \<in> carrier_mat n n" using diag_mat_of_real_carrier[of "map sqrt D"] D by simp
  have "(U * ?S * (U\<^sup>\<dagger>)) * (U * ?S * (U\<^sup>\<dagger>)) = U * (?S * ?S) * (U\<^sup>\<dagger>)"
    by (rule unitary_conj_mult[OF U Uu Sc Sc])
  also have "?S * ?S = diag_mat_of_real D" by (rule diag_mat_of_real_sqrt_square) (use Dnn D in simp)
  finally have QQ: "(U * ?S * (U\<^sup>\<dagger>)) * (U * ?S * (U\<^sup>\<dagger>)) = P" by (simp add: P)
  have "psd (U * ?S * (U\<^sup>\<dagger>))" by (rule psd_U_diag_Udag[OF U]) (use Dnn D in auto)
  thus ?thesis using QQ U Sc by (intro exI[of _ "U * ?S * (U\<^sup>\<dagger>)"]) auto
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
  have "0 < Re mu" if vnz: "v \<noteq> 0\<^sub>v n" and vd: "dim_vec v = n" and eig: "P *\<^sub>v v = mu \<cdot>\<^sub>v v"
    for mu :: complex and v :: "complex Matrix.vec"
  proof -
    have "0 < Re \<langle>v | P *\<^sub>v v\<rangle>" using pd vd vnz sq unfolding pd_def by auto
    also have "Re \<langle>v | P *\<^sub>v v\<rangle> = Re mu * Re \<langle>v | v\<rangle>"
      unfolding eig inner_prod_right_smult' using inner_prod_with_itself_Im[of v] by simp
    finally show ?thesis
      using inner_prod_with_itself_Re_non0[of v] vnz vd zero_less_mult_pos2 by auto
  qed
  thus "hermitian P \<and> (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu)"
    using pd unfolding pd_def by blast
next
  assume rhs: "hermitian P \<and> (\<forall>mu :: complex. \<forall>v :: complex Matrix.vec.
             v \<noteq> 0\<^sub>v n \<and> dim_vec v = n \<and> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<longrightarrow> 0 < Re mu)"
  hence ev: "\<And>mu v. v \<noteq> 0\<^sub>v n \<Longrightarrow> dim_vec v = n \<Longrightarrow> P *\<^sub>v v = mu \<cdot>\<^sub>v v \<Longrightarrow> 0 < Re mu"
    by blast
  have psd: "psd P"
    unfolding psd_iff_nonneg_eigenvalues[OF sq] using rhs ev by (auto simp: less_imp_le)
  let ?Q = "psd_sqrt P"
  have Qc: "?Q \<in> carrier_mat n n" and Qpsd: "psd ?Q" and QQ: "?Q * ?Q = P"
    using psd_sqrt_props[OF sq psd] by auto
  have Qh: "?Q\<^sup>\<dagger> = ?Q" using psd_hermitian[OF Qpsd] by (simp add: hermitian_def)
  show "pd P" unfolding pd_def carrier_matD(1)[OF sq]
  proof (intro conjI allI impI)
    fix x :: "complex Matrix.vec" assume xd: "dim_vec x = n" and xnz: "x \<noteq> 0\<^sub>v n"
    have Px: "P *\<^sub>v x = ?Q *\<^sub>v (?Q *\<^sub>v x)"
      using assoc_mult_mat_vec[OF Qc Qc carrier_vecI[OF xd]] unfolding QQ .
    have Qx: "dim_vec (?Q *\<^sub>v x) = n" using Qc by simp
    have "?Q *\<^sub>v x \<noteq> 0\<^sub>v n"
    proof
      assume "?Q *\<^sub>v x = 0\<^sub>v n"
      hence "P *\<^sub>v x = (0 :: complex) \<cdot>\<^sub>v x" unfolding Px using Qc xd by (intro eq_vecI) auto
      from ev[OF xnz xd this] show False by simp
    qed
    hence "0 < Re \<langle>?Q *\<^sub>v x | ?Q *\<^sub>v x\<rangle>" using inner_prod_with_itself_Re_non0[of "?Q *\<^sub>v x"] Qx by simp
    thus "0 < Re \<langle>x | P *\<^sub>v x\<rangle>"
      unfolding Px inner_prod_adjoint_swap[OF Qc xd Qx] Qh .
  qed (use rhs in blast)
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
  unfolding psd_iff_quad_form_nonneg[OF smult_carrier_mat[OF Ac]]
proof (intro allI impI)
  fix x :: "complex Matrix.vec" assume x: "dim_vec x = n"
  have "\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle> = complex_of_real c * \<langle>x | A *\<^sub>v x\<rangle>"
    unfolding smult_mat_mult_vec[OF Ac carrier_vecI[OF x]] inner_prod_right_smult' ..
  thus "\<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle> \<in> \<real> \<and>
        0 \<le> Re \<langle>x | (complex_of_real c \<cdot>\<^sub>m A) *\<^sub>v x\<rangle>"
    using A[unfolded psd_iff_quad_form_nonneg[OF Ac], rule_format, OF x] c by auto
qed

subsection \<open>The converse directions for Hermitian matrices (D4-1)\<close>

lemma unitary_real_diag_imp_hermitian:
  assumes U: "U \<in> carrier_mat n n" and u: "unitary U" and H: "H \<in> carrier_mat n n"
      and D: "length D = n" and spec: "U\<^sup>\<dagger> * H * U = diag_mat_of_real D"
  shows "hermitian H"
proof -
  have He: "H = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF U H u spec])
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using D by (intro carrier_matI) simp_all
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have "(U * diag_mat_of_real D * (U\<^sup>\<dagger>))\<^sup>\<dagger> = ((U\<^sup>\<dagger>)\<^sup>\<dagger>) * ((U * diag_mat_of_real D)\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use U Dc Ud in auto)
  also have "(U * diag_mat_of_real D)\<^sup>\<dagger> = ((diag_mat_of_real D)\<^sup>\<dagger>) * (U\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (use U Dc in auto)
  also have "(diag_mat_of_real D)\<^sup>\<dagger> = diag_mat_of_real D"
    by (rule diag_mat_of_real_hermitian[unfolded hermitian_def])
  also have "(U\<^sup>\<dagger>)\<^sup>\<dagger> = U" by (rule dagger_of_dagger_is_id)
  finally have "(U * diag_mat_of_real D * (U\<^sup>\<dagger>))\<^sup>\<dagger> = U * (diag_mat_of_real D * (U\<^sup>\<dagger>))" .
  also have "\<dots> = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" using U Dc Ud by (simp add: assoc_mult_mat)
  finally show ?thesis unfolding hermitian_def using He by simp
qed

lemma eigenbasis_real_imp_hermitian:
  assumes H: "H \<in> carrier_mat n n" and orth: "orthonormal_list n vs" and len: "length vs = n"
      and eig: "\<And>i. i < n \<Longrightarrow> H *\<^sub>v vs ! i = complex_of_real (lam ! i) \<cdot>\<^sub>v vs ! i" and lam: "length lam = n"
  shows "hermitian H"
proof -
  let ?U = "mat_of_cols n vs"
  have U: "?U \<in> carrier_mat n n" using mat_of_cols_carrier(1)[of n vs] len by simp
  have u: "unitary ?U" by (rule orthonormal_mat_unitary[OF orth len])
  have vd: "\<And>i. i < n \<Longrightarrow> dim_vec (vs ! i) = n" using orth len unfolding orthonormal_list_def by auto
  have HU: "H * ?U = ?U * diag_mat_of_real lam"
  proof (rule eq_matI)
    fix r c assume "r < dim_row (?U * diag_mat_of_real lam)" "c < dim_col (?U * diag_mat_of_real lam)"
    hence r: "r < n" and c: "c < n" using len lam by simp_all
    have "(H * ?U) $$ (r, c) = (H *\<^sub>v vs ! c) $ r"
      using carrier_matD[OF H] len r c vd[OF c] by (simp add: mat_of_cols_def Matrix.col_def Matrix.row_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = complex_of_real (lam ! c) * vs ! c $ r" using eig[OF c] vd[OF c] r by simp
    also have "\<dots> = (?U * diag_mat_of_real lam) $$ (r, c)"
    proof -
      have "(?U * diag_mat_of_real lam) $$ (r, c) = (\<Sum>k<n. ?U $$ (r, k) * diag_mat_of_real lam $$ (k, c))"
        using carrier_matD[OF U] r c lam by (auto simp: scalar_prod_def atLeast0LessThan intro!: sum.cong)
      also have "\<dots> = (\<Sum>k<n. if k = c then vs ! c $ r * complex_of_real (lam ! c) else 0)"
        by (rule sum.cong) (use r c lam len in \<open>auto simp: diag_mat_of_real_def mat_diag_def mat_of_cols_def\<close>)
      also have "\<dots> = vs ! c $ r * complex_of_real (lam ! c)" using c by simp
      finally show ?thesis by (simp add: mult.commute)
    qed
    finally show "(H * ?U) $$ (r, c) = (?U * diag_mat_of_real lam) $$ (r, c)" .
  qed (use carrier_matD[OF H] len lam in simp_all)
  have Ud: "?U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U])
  have UdU: "?U\<^sup>\<dagger> * ?U = 1\<^sub>m n" using u U len unfolding unitary_def by (simp add: inverts_mat_def)
  have "?U\<^sup>\<dagger> * H * ?U = ?U\<^sup>\<dagger> * (H * ?U)" using Ud H U by (simp add: assoc_mult_mat)
  also have "\<dots> = ?U\<^sup>\<dagger> * ?U * diag_mat_of_real lam"
  proof -
    have Dc: "diag_mat_of_real lam \<in> carrier_mat n n" using lam by (intro carrier_matI) simp_all
    show ?thesis unfolding HU by (rule assoc_mult_mat[OF Ud U Dc, symmetric])
  qed
  also have "\<dots> = diag_mat_of_real lam" unfolding UdU using lam by simp
  finally show ?thesis by (rule unitary_real_diag_imp_hermitian[OF U u H lam])
qed

subsection \<open>Ranges; positive definiteness and spanning (D4-8)\<close>

text \<open>The notes write $R(P)$ for the range of $P$ (here \<open>mat_range k P\<close>).  For Hermitian $P$,
every vector orthogonal to $\ker P$ lies in $R(P)$, by the spectral decomposition $P=UDU^*$ with
the nonzero eigenvalues inverted; hence $R(\sum_lw_lw_l^*)=\operatorname{span}\{w_l\}$
(\<open>col_span\<close>), and so the notes' form of D4-8.  Day 21 uses the same lemma for
$0\le ww^*\le P\Rightarrow w\in R(P)$.\<close>

definition mat_range :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec set" where
  "mat_range k P = {P *\<^sub>v h | h. dim_vec h = k}"

lemma diag_mat_of_real_mult_vec:
  assumes "length D = k" "dim_vec v = k"
  shows "diag_mat_of_real D *\<^sub>v v = Matrix.vec k (\<lambda>i. complex_of_real (D ! i) * v $ i)"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (Matrix.vec k (\<lambda>i. complex_of_real (D ! i) * v $ i))"
  hence i: "i < k" by simp
  have "(diag_mat_of_real D *\<^sub>v v) $ i = (\<Sum>j<k. (if i = j then complex_of_real (D ! i) else 0) * v $ j)"
    using assms i by (simp add: diag_mat_of_real_def mat_diag_def scalar_prod_def atLeast0LessThan cong: if_cong)
  also have "\<dots> = (\<Sum>j<k. if j = i then complex_of_real (D ! i) * v $ j else 0)" by (rule sum.cong) auto
  also have "\<dots> = complex_of_real (D ! i) * v $ i" using i by simp
  finally show "(diag_mat_of_real D *\<^sub>v v) $ i = Matrix.vec k (\<lambda>i. complex_of_real (D ! i) * v $ i) $ i" using i by simp
qed (use assms in simp)

text \<open>For Hermitian $P$, a vector orthogonal to $\ker P$ lies in the range of $P$.\<close>

lemma hermitian_perp_ker_in_range:
  assumes P: "P \<in> carrier_mat k k" and h: "hermitian P" and w: "dim_vec w = k"
      and perp: "\<And>x. dim_vec x = k \<Longrightarrow> P *\<^sub>v x = 0\<^sub>v k \<Longrightarrow> Quantum.inner_prod x w = 0"
  shows "w \<in> mat_range k P"
proof -
  obtain U D where U: "U \<in> carrier_mat k k" and u: "unitary U" and D: "length D = k"
    and spec: "U\<^sup>\<dagger> * P * U = diag_mat_of_real D"
    using hermitian_spectral_decomp[OF P h] by blast
  have Pe: "P = U * diag_mat_of_real D * (U\<^sup>\<dagger>)" by (rule hermitian_spectral_decomp_eq[OF U P u spec])
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat k k" by (rule dagger_carrier[OF U])
  have Dc: "diag_mat_of_real D \<in> carrier_mat k k" using D by (intro carrier_matI) simp_all
  have UdU: "U\<^sup>\<dagger> * U = 1\<^sub>m k" and UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m k"
    using u U unfolding unitary_def by (simp_all add: inverts_mat_def)
  have Papp: "P *\<^sub>v (U *\<^sub>v z) = U *\<^sub>v (diag_mat_of_real D *\<^sub>v z)" if z: "dim_vec z = k" for z
  proof -
    have zc: "z \<in> carrier_vec k" using z by (rule carrier_vecI)
    have "P *\<^sub>v (U *\<^sub>v z) = (U * diag_mat_of_real D * (U\<^sup>\<dagger>)) *\<^sub>v (U *\<^sub>v z)" using Pe by simp
    also have "\<dots> = (U * diag_mat_of_real D * (U\<^sup>\<dagger>) * U) *\<^sub>v z"
    proof -
      have Mc: "U * diag_mat_of_real D * (U\<^sup>\<dagger>) \<in> carrier_mat k k" using U Dc Ud by simp
      show ?thesis by (rule assoc_mult_mat_vec[OF Mc U zc, symmetric])
    qed
    also have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) * U = U * diag_mat_of_real D"
    proof -
      have "U * diag_mat_of_real D * (U\<^sup>\<dagger>) * U = U * diag_mat_of_real D * ((U\<^sup>\<dagger>) * U)"
        by (rule assoc_mult_mat[OF mult_carrier_mat[OF U Dc] Ud U])
      thus ?thesis unfolding UdU using right_mult_one_mat[OF mult_carrier_mat[OF U Dc]] by simp
    qed
    also have "(U * diag_mat_of_real D) *\<^sub>v z = U *\<^sub>v (diag_mat_of_real D *\<^sub>v z)"
      using U Dc zc by (simp add: assoc_mult_mat_vec)
    finally show ?thesis .
  qed
  define y where "y = U\<^sup>\<dagger> *\<^sub>v w"
  have yd: "dim_vec y = k" using carrier_matD[OF U] by (simp add: y_def)
  have y0: "y $ i = 0" if i: "i < k" and Di: "D ! i = 0" for i
  proof -
    let ?e = "unit_vec k i :: complex Matrix.vec"
    have "P *\<^sub>v (U *\<^sub>v ?e) = U *\<^sub>v (diag_mat_of_real D *\<^sub>v ?e)" by (rule Papp) simp
    also have "diag_mat_of_real D *\<^sub>v ?e = 0\<^sub>v k"
      using diag_mat_of_real_mult_vec[OF D, of ?e] i Di by (auto simp: unit_vec_def)
    also have "U *\<^sub>v 0\<^sub>v k = 0\<^sub>v k"
      by (rule eq_vecI) (use carrier_matD[OF U] in \<open>simp_all add: scalar_prod_def\<close>)
    finally have "P *\<^sub>v (U *\<^sub>v ?e) = 0\<^sub>v k" .
    hence "Quantum.inner_prod (U *\<^sub>v ?e) w = 0" using perp carrier_matD[OF U] by simp
    moreover have "Quantum.inner_prod (U *\<^sub>v ?e) w = y $ i"
    proof -
      have Ue: "U *\<^sub>v ?e = Matrix.vec k (\<lambda>j. U $$ (j, i))"
      proof (rule eq_vecI)
        fix j assume "j < dim_vec (Matrix.vec k (\<lambda>j. U $$ (j, i)))"
        hence j: "j < k" by simp
        have "(U *\<^sub>v ?e) $ j = (\<Sum>l<k. U $$ (j, l) * (if l = i then 1 else 0))"
          using carrier_matD[OF U] j i by (simp add: scalar_prod_def unit_vec_def atLeast0LessThan)
        also have "\<dots> = (\<Sum>l<k. if l = i then U $$ (j, l) else 0)" by (rule sum.cong) simp_all
        also have "\<dots> = U $$ (j, i)" using i by simp
        finally show "(U *\<^sub>v ?e) $ j = Matrix.vec k (\<lambda>j. U $$ (j, i)) $ j" using j by simp
      qed (use carrier_matD[OF U] in simp)
      have "Quantum.inner_prod (Matrix.vec k (\<lambda>j. U $$ (j, i))) w = (\<Sum>j<k. cnj (U $$ (j, i)) * w $ j)"
        using w by (simp add: Quantum.inner_prod_def atLeast0LessThan)
      also have "\<dots> = y $ i"
        using carrier_matD[OF U] w i by (simp add: y_def scalar_prod_def dagger_def atLeast0LessThan)
      finally show ?thesis unfolding Ue .
    qed
    ultimately show ?thesis by simp
  qed
  define z where "z = Matrix.vec k (\<lambda>i. if D ! i = 0 then 0 else y $ i / complex_of_real (D ! i))"
  have zd: "dim_vec z = k" by (simp add: z_def)
  have Dz: "diag_mat_of_real D *\<^sub>v z = y"
  proof (rule eq_vecI)
    fix i assume "i < dim_vec y" hence i: "i < k" using yd by simp
    show "(diag_mat_of_real D *\<^sub>v z) $ i = y $ i"
      using diag_mat_of_real_mult_vec[OF D zd] i y0[OF i] by (simp add: z_def)
  qed (use D yd in simp)
  have "P *\<^sub>v (U *\<^sub>v z) = U *\<^sub>v y" unfolding Papp[OF zd] Dz ..
  also have "\<dots> = (U * (U\<^sup>\<dagger>)) *\<^sub>v w"
    unfolding y_def by (rule assoc_mult_mat_vec[OF U Ud carrier_vecI[OF w], symmetric])
  also have "\<dots> = w" unfolding UUd by (rule one_mult_mat_vec[OF carrier_vecI[OF w]])
  finally have "w = P *\<^sub>v (U *\<^sub>v z)" ..
  moreover have "dim_vec (U *\<^sub>v z) = k" using carrier_matD[OF U] by simp
  ultimately show ?thesis unfolding mat_range_def by blast
qed

text \<open>The notes: if $P=\sum_l w_lw_l^*$ then $R(P)=\operatorname{span}\{w_1,\dots,w_m\}$.\<close>

theorem outer_sum_range:
  assumes vs: "\<forall>v \<in> set vs. dim_vec v = k"
  shows "mat_range k (outer_sum k vs) = col_span k vs"
proof (intro equalityI subsetI)
  let ?V = "mat_of_cols k vs" and ?m = "length vs"
  have Vc: "?V \<in> carrier_mat k ?m" by (rule mat_of_cols_carrier(1))
  have Vd: "?V\<^sup>\<dagger> \<in> carrier_mat ?m k" by (rule dagger_carrier[OF Vc])
  fix y assume "y \<in> mat_range k (outer_sum k vs)"
  then obtain h where h: "dim_vec h = k" and y: "y = outer_sum k vs *\<^sub>v h" unfolding mat_range_def by blast
  have "y = ?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v h)"
    unfolding y outer_sum_def by (rule assoc_mult_mat_vec[OF Vc Vd carrier_vecI[OF h]])
  moreover have "dim_vec (?V\<^sup>\<dagger> *\<^sub>v h) = ?m" using carrier_matD[OF Vd] by simp
  ultimately show "y \<in> col_span k vs" unfolding col_span_def by blast
next
  let ?V = "mat_of_cols k vs" and ?m = "length vs" and ?P = "outer_sum k vs"
  have Vc: "?V \<in> carrier_mat k ?m" by (rule mat_of_cols_carrier(1))
  have Vd: "?V\<^sup>\<dagger> \<in> carrier_mat ?m k" by (rule dagger_carrier[OF Vc])
  have Pc: "?P \<in> carrier_mat k k" by (rule outer_sum_carrier)
  have Ph: "hermitian ?P" unfolding hermitian_def by (rule outer_sum_hermitian)
  fix y assume "y \<in> col_span k vs"
  then obtain c where c: "dim_vec c = ?m" and y: "y = ?V *\<^sub>v c" unfolding col_span_def by blast
  have yd: "dim_vec y = k" using carrier_matD[OF Vc] y by simp
  show "y \<in> mat_range k ?P"
  proof (rule hermitian_perp_ker_in_range[OF Pc Ph yd])
    fix x assume x: "dim_vec x = k" and Px: "?P *\<^sub>v x = 0\<^sub>v k"
    have "?P *\<^sub>v x = ?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x)"
      unfolding outer_sum_def by (rule assoc_mult_mat_vec[OF Vc Vd carrier_vecI[OF x]])
    hence z: "?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x) = 0\<^sub>v k" using Px by simp
    have "Quantum.inner_prod x (?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x)) = 0" unfolding z by (simp add: Quantum.inner_prod_def)
    moreover have "Quantum.inner_prod x (?V *\<^sub>v (?V\<^sup>\<dagger> *\<^sub>v x)) = Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) (?V\<^sup>\<dagger> *\<^sub>v x)"
      by (rule inner_prod_adjoint_swap[OF Vc x]) (use carrier_matD[OF Vd] in simp)
    ultimately have "Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) (?V\<^sup>\<dagger> *\<^sub>v x) = 0" by simp
    hence Vx: "?V\<^sup>\<dagger> *\<^sub>v x = 0\<^sub>v ?m" using inner_prod_self_eq_zero_iff[of "?V\<^sup>\<dagger> *\<^sub>v x"] carrier_matD[OF Vd] by simp
    have "Quantum.inner_prod x y = Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) c"
      unfolding y by (rule inner_prod_adjoint_swap[OF Vc x c])
    also have "\<dots> = 0" unfolding Vx by (simp add: Quantum.inner_prod_def c)
    finally show "Quantum.inner_prod x y = 0" .
  qed
qed

text \<open>The notes: $P=\sum_i|v_i\rangle\langle v_i|>0$ iff $\operatorname{span}\{v_i\}=\mathbb C^n$.\<close>

theorem pd_iff_span_all:
  assumes vs: "\<forall>v \<in> set vs. dim_vec v = n"
  shows "pd (outer_sum n vs) \<longleftrightarrow> col_span n vs = carrier_vec n"
proof
  let ?P = "outer_sum n vs"
  have Pc: "?P \<in> carrier_mat n n" by (rule outer_sum_carrier)
  assume pd: "pd ?P"
  have Ph: "hermitian ?P" unfolding hermitian_def by (rule outer_sum_hermitian)
  show "col_span n vs = carrier_vec n"
  proof (intro equalityI subsetI)
    fix y assume "y \<in> col_span n vs"
    then obtain c where y: "y = mat_of_cols n vs *\<^sub>v c" unfolding col_span_def by blast
    show "y \<in> carrier_vec n" unfolding y by (intro carrier_vecI) simp
  next
    fix w :: "complex Matrix.vec" assume "w \<in> carrier_vec n"
    hence w: "dim_vec w = n" by simp
    have "w \<in> mat_range n ?P"
    proof (rule hermitian_perp_ker_in_range[OF Pc Ph w])
      fix x assume x: "dim_vec x = n" and Px: "?P *\<^sub>v x = 0\<^sub>v n"
      have "x = 0\<^sub>v n"
      proof (rule ccontr)
        assume "x \<noteq> 0\<^sub>v n"
        hence "0 < Re (Quantum.inner_prod x (?P *\<^sub>v x))" using pd x carrier_matD(1)[OF Pc] unfolding pd_def by auto
        thus False unfolding Px by (simp add: Quantum.inner_prod_def)
      qed
      thus "Quantum.inner_prod x w = 0" using w by (simp add: Quantum.inner_prod_def)
    qed
    thus "w \<in> col_span n vs" using outer_sum_range[OF vs] by simp
  qed
next
  let ?P = "outer_sum n vs" and ?V = "mat_of_cols n vs"
  have Pc: "?P \<in> carrier_mat n n" by (rule outer_sum_carrier)
  assume span: "col_span n vs = carrier_vec n"
  show "pd ?P"
    unfolding pd_iff_spanning[OF Pc refl vs]
  proof (intro allI impI)
    fix x :: "complex Matrix.vec" assume x: "dim_vec x = n" and x0: "x \<noteq> 0\<^sub>v n"
    show "\<exists>v \<in> set vs. Quantum.inner_prod v x \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> (\<exists>v \<in> set vs. Quantum.inner_prod v x \<noteq> 0)"
      hence all: "\<And>v. v \<in> set vs \<Longrightarrow> Quantum.inner_prod v x = 0" by blast
      have Vc: "?V \<in> carrier_mat n (length vs)" by (rule mat_of_cols_carrier(1))
      have Vx: "?V\<^sup>\<dagger> *\<^sub>v x = 0\<^sub>v (length vs)"
      proof (rule eq_vecI)
        fix j assume "j < dim_vec (0\<^sub>v (length vs) :: complex Matrix.vec)"
        hence j: "j < length vs" by simp
        have "(?V\<^sup>\<dagger> *\<^sub>v x) $ j = (\<Sum>i<n. cnj (vs ! j $ i) * x $ i)"
          using j x by (simp add: dagger_def mat_of_cols_def scalar_prod_def atLeast0LessThan)
        also have "\<dots> = Quantum.inner_prod (vs ! j) x"
          using vs j x by (simp add: Quantum.inner_prod_def atLeast0LessThan)
        also have "\<dots> = 0" using all j by simp
        finally show "(?V\<^sup>\<dagger> *\<^sub>v x) $ j = 0\<^sub>v (length vs) $ j" using j by simp
      qed (simp add: dagger_def)
      have "x \<in> col_span n vs" using span carrier_vecI[OF x] by simp
      then obtain c where c: "dim_vec c = length vs" and xc: "x = ?V *\<^sub>v c" unfolding col_span_def by blast
      have "Quantum.inner_prod x x = Quantum.inner_prod (?V\<^sup>\<dagger> *\<^sub>v x) c"
        using inner_prod_adjoint_swap[OF Vc x c] xc by simp
      also have "\<dots> = 0" unfolding Vx using c by (simp add: Quantum.inner_prod_def)
      finally have "x = 0\<^sub>v (dim_vec x)" using inner_prod_self_eq_zero_iff by blast
      thus False using x0 x by simp
    qed
  qed
qed

subsection \<open>Projections\<close>

text \<open>A \emph{projection} on $\C^n$ is a Hermitian idempotent, the notion of Day 2; projections
are the building blocks of syndrome measurements and recovery maps (Days 30--34).  Day 2's
theorem that such a $P$ is the orthogonal projection onto its range follows the basic facts.\<close>

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

lemma projection_one: "projection n (1\<^sub>m n)"
  by (auto simp: projection_def hermitian_def dagger_def)

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

text \<open>The theorem of Day 2: a Hermitian idempotent $P$ is the orthogonal projection onto its
range, i.e. $Pv=v$ for $v$ in the range and $Pw=0$ for $w$ orthogonal to the range.\<close>

lemma projection_fixes_range:
  fixes P :: "complex Matrix.mat" and x :: "complex Matrix.vec"
  assumes P: "projection n P" and x: "dim_vec x = n"
  shows "P *\<^sub>v (P *\<^sub>v x) = P *\<^sub>v x"
proof -
  have Pc: "P \<in> carrier_mat n n" and idem: "P * P = P" using P by (auto simp: projection_def)
  have xc: "x \<in> carrier_vec n" using x by auto
  have "P *\<^sub>v (P *\<^sub>v x) = (P * P) *\<^sub>v x" using assoc_mult_mat_vec[OF Pc Pc xc] by simp
  thus ?thesis using idem by simp
qed

lemma projection_annihilates_orthogonal:
  fixes P :: "complex Matrix.mat" and w :: "complex Matrix.vec"
  assumes P: "projection n P" and w: "dim_vec w = n"
      and orth: "\<And>x :: complex Matrix.vec. dim_vec x = n \<Longrightarrow> \<langle>P *\<^sub>v x | w\<rangle> = 0"
  shows "P *\<^sub>v w = 0\<^sub>v n"
proof -
  have Pc: "P \<in> carrier_mat n n" and herm: "hermitian P" and idem: "P * P = P"
    using P by (auto simp: projection_def)
  have Ph: "P\<^sup>\<dagger> = P" using herm by (simp add: hermitian_def)
  have Pw: "dim_vec (P *\<^sub>v w) = n" using Pc w by auto
  have "\<langle>P *\<^sub>v w | P *\<^sub>v w\<rangle> = \<langle>P\<^sup>\<dagger> *\<^sub>v w | P *\<^sub>v w\<rangle>" using Ph by simp
  also have "\<dots> = \<langle>w | P *\<^sub>v (P *\<^sub>v w)\<rangle>"
    using inner_prod_adjoint_swap[OF Pc w Pw] by simp
  also have "\<dots> = \<langle>w | P *\<^sub>v w\<rangle>" using projection_fixes_range[OF P w] by simp
  also have "\<dots> = cnj \<langle>P *\<^sub>v w | w\<rangle>"
  proof -
    have dims: "dim_vec (P *\<^sub>v w) = dim_vec w" using Pw w by simp
    show ?thesis using inner_prod_cnj[OF dims] .
  qed
  also have "\<dots> = 0" using orth[OF w] by simp
  finally have "\<langle>P *\<^sub>v w | P *\<^sub>v w\<rangle> = 0" .
  thus ?thesis using inner_prod_self_eq_zero_iff[of "P *\<^sub>v w"] Pw by simp
qed

lemma projection_complement_idempotent:
  assumes "projection n P"
  shows "(1\<^sub>m n - P) * (1\<^sub>m n - P) = 1\<^sub>m n - P"
  using assms unfolding projection_def by (intro complement_projection) auto

end
