(*  Title:   Day25_Hahn_Banach.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 26 October 2011 (Day 25)
*)

theory Day25_Hahn_Banach
  imports Matrix_Analysis_Prerequisites.Matrix_Typed
begin

section \<open>Day 25 (26 October 2011): the Hahn--Banach theorem\<close>

text \<open>\begin{notesdef}
Let $W$ be a normed space.  A linear functional $f:W\to\C$ is \emph{bounded} if
$|f(w)|\le C\norm w$ for some constant $C$; the least such $C$ is the norm
$\norm f=\sup\{|f(w)|:\norm w\le1\}$.
\end{notesdef}
\begin{notestheorem}[Hahn--Banach]
Let $W$ be a normed space, $V\subseteq W$ a subspace and $g:V\to\C$ a bounded linear
functional.  Then there is a bounded linear functional $f:W\to\C$ with $\norm f=\norm g$ and
$f(v)=g(v)$ for all $v\in V$.
\end{notestheorem}
In the notes the theorem is used (Day 26) to extend the state $S_\Phi$ from $M_d(S)$ to
$M_d(M_n)$ in the proof of Arveson's extension theorem, which is not formalised.  Here it is
proved for $W=(\C$-valued $m\times n$ matrices$)$ with the Hilbert--Schmidt norm: HOL's
Hahn--Banach gives a real-linear norm-preserving extension of $\Re g$, and the
Bohnenblust--Sobczyk construction $f(x)=F(x)-iF(ix)$ recovers a complex-linear extension with
the same bound.\<close>

subsection \<open>Bounded complex-linear functionals on lmat\<close>

definition clinear_functional_on ::
    "(complex, 'm :: finite, 'n :: finite) lmat set
     \<Rightarrow> ((complex, 'm, 'n) lmat \<Rightarrow> complex) \<Rightarrow> bool"
where
  "clinear_functional_on V g \<equiv>
     (\<forall>x \<in> V. \<forall>y \<in> V. g (x + y) = g x + g y) \<and>
     (\<forall>x \<in> V. \<forall>c. g (cmult_lmat c x) = c * g x)"

definition bounded_clinear_functional_on ::
    "(complex, 'm :: finite, 'n :: finite) lmat set
     \<Rightarrow> ((complex, 'm, 'n) lmat \<Rightarrow> complex) \<Rightarrow> bool"
where
  "bounded_clinear_functional_on V g \<equiv>
     clinear_functional_on V g \<and>
     (\<exists>C \<ge> 0. \<forall>x \<in> V. cmod (g x) \<le> C * hs_norm_lmat x)"

subsection \<open>Real-part functional and linearform/continuous instances\<close>

definition re_part_lmat ::
    "((complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> complex)
     \<Rightarrow> ((complex, 'm, 'n) lmat \<Rightarrow> real)"
where
  "re_part_lmat g x = Re (g x)"

lemma linearform_re_part_lmat:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
  assumes V_sub: "Subspace.subspace V UNIV"
      and g_clin: "clinear_functional_on V g"
  shows "linearform V (re_part_lmat g)"
proof
  fix x y :: "(complex, 'm, 'n) lmat" and a :: real
  assume xV: "x \<in> V" and yV: "y \<in> V"
  show "re_part_lmat g (x + y) = re_part_lmat g x + re_part_lmat g y"
    using g_clin xV yV
    unfolding clinear_functional_on_def re_part_lmat_def
    by simp
next
  fix x :: "(complex, 'm, 'n) lmat" and a :: real
  assume xV: "x \<in> V"
  have prod_as_cmult: "Vector_Space.prod a x = cmult_lmat (complex_of_real a) x"
    by (simp add: cmult_lmat_real)
  have "g (Vector_Space.prod a x) = complex_of_real a * g x"
    using g_clin xV prod_as_cmult
    unfolding clinear_functional_on_def by simp
  thus "re_part_lmat g (Vector_Space.prod a x) = a * re_part_lmat g x"
    unfolding re_part_lmat_def by simp
qed

lemma continuous_re_part_lmat:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
  assumes V_sub: "Subspace.subspace V UNIV"
      and g_bnd: "bounded_clinear_functional_on V g"
  shows "continuous V (re_part_lmat g) hs_norm_lmat"
proof -
  have lin: "linearform V (re_part_lmat g)"
    using V_sub g_bnd
    unfolding bounded_clinear_functional_on_def
    by (intro linearform_re_part_lmat) auto
  obtain C where C_nn: "C \<ge> 0"
            and C_bnd: "\<forall>x \<in> V. cmod (g x) \<le> C * hs_norm_lmat x"
    using g_bnd unfolding bounded_clinear_functional_on_def by blast
  have re_bnd: "\<And>x. x \<in> V \<Longrightarrow> \<bar>re_part_lmat g x\<bar> \<le> C * hs_norm_lmat x"
  proof -
    fix x assume xV: "x \<in> V"
    have "\<bar>re_part_lmat g x\<bar> = \<bar>Re (g x)\<bar>"
      unfolding re_part_lmat_def by simp
    also have "\<dots> \<le> cmod (g x)"
      by (rule abs_Re_le_cmod)
    also have "\<dots> \<le> C * hs_norm_lmat x"
      using C_bnd xV by simp
    finally show "\<bar>re_part_lmat g x\<bar> \<le> C * hs_norm_lmat x" .
  qed
  show ?thesis using lin re_bnd by (rule continuousI)
qed

subsection \<open>Application of HOL/Hahn\_Banach (norm-preserving extension)\<close>

text \<open>Apply HOL/Hahn\_Banach to extend the real-linearform
\<open>re_part_lmat g\<close> to all of UNIV preserving the function norm.\<close>

theorem hahn_banach_re_part_lmat:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
  assumes V_sub: "Subspace.subspace V (UNIV :: (complex, 'm, 'n) lmat set)"
      and g_bnd: "bounded_clinear_functional_on V g"
  shows
    "\<exists>F :: (complex, 'm, 'n) lmat \<Rightarrow> real.
        linearform UNIV F
      \<and> continuous UNIV F hs_norm_lmat
      \<and> (\<forall>x \<in> V. F x = re_part_lmat g x)"
proof -
  have nv: "normed_vectorspace UNIV hs_norm_lmat"
    by (rule normed_vectorspace_UNIV_lmat)
  have lin: "linearform V (re_part_lmat g)"
    using V_sub g_bnd
    unfolding bounded_clinear_functional_on_def
    by (intro linearform_re_part_lmat) auto
  have cont: "continuous V (re_part_lmat g) hs_norm_lmat"
    by (rule continuous_re_part_lmat[OF V_sub g_bnd])
  obtain F where
      F_lin: "linearform UNIV F"
    and F_cont: "continuous UNIV F hs_norm_lmat"
    and F_ext: "\<forall>x \<in> V. F x = re_part_lmat g x"
    using norm_Hahn_Banach[OF nv V_sub lin cont] by blast
  show ?thesis using F_lin F_cont F_ext by blast
qed

subsection \<open>Bohnenblust-Sobczyk: complex extension from real extension\<close>

text \<open>Given a real-linear extension \<open>F\<close> of \<open>re_part_lmat g\<close> on
all of UNIV, define the complex-linear extension
\<open>f x = F x - i \<cdot> F (i \<cdot> x)\<close>.\<close>

definition bs_complex_extension ::
    "((complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real)
     \<Rightarrow> ((complex, 'm, 'n) lmat \<Rightarrow> complex)"
where
  "bs_complex_extension F x =
     complex_of_real (F x) - \<i> * complex_of_real (F (cmult_lmat \<i> x))"

lemma bs_complex_extension_add:
  fixes F :: "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
  assumes F_lin: "linearform UNIV F"
  shows "bs_complex_extension F (x + y)
         = bs_complex_extension F x + bs_complex_extension F y"
proof -
  interpret F_int: linearform UNIV F using F_lin .
  have F_xy: "F (x + y) = F x + F y" by simp
  have ixy: "cmult_lmat \<i> (x + y) = cmult_lmat \<i> x + cmult_lmat \<i> y"
    by (rule cmult_lmat_add)
  have F_ixy: "F (cmult_lmat \<i> (x + y)) = F (cmult_lmat \<i> x) + F (cmult_lmat \<i> y)"
    using ixy by simp
  show ?thesis
    unfolding bs_complex_extension_def
    by (simp only: F_xy F_ixy algebra_simps of_real_add)
qed

lemma bs_complex_extension_real_smult:
  fixes F :: "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
  assumes F_lin: "linearform UNIV F"
  shows "bs_complex_extension F (Vector_Space.prod a x)
         = complex_of_real a * bs_complex_extension F x"
proof -
  interpret F_int: linearform UNIV F using F_lin .
  have F_ax: "F (Vector_Space.prod a x) = a * F x" by simp
  have swap: "cmult_lmat \<i> (Vector_Space.prod a x)
              = Vector_Space.prod a (cmult_lmat \<i> x)"
  proof -
    have "cmult_lmat \<i> (Vector_Space.prod a x)
          = cmult_lmat \<i> (cmult_lmat (complex_of_real a) x)"
      by (simp add: cmult_lmat_real)
    also have "\<dots> = cmult_lmat (\<i> * complex_of_real a) x"
      by (rule cmult_lmat_scalar_mult[symmetric])
    also have "\<dots> = cmult_lmat (complex_of_real a * \<i>) x"
      by (simp add: ac_simps)
    also have "\<dots> = cmult_lmat (complex_of_real a) (cmult_lmat \<i> x)"
      by (rule cmult_lmat_scalar_mult)
    also have "\<dots> = Vector_Space.prod a (cmult_lmat \<i> x)"
      by (simp add: cmult_lmat_real)
    finally show ?thesis .
  qed
  have F_iax:
    "F (cmult_lmat \<i> (Vector_Space.prod a x)) = a * F (cmult_lmat \<i> x)"
    using swap by simp
  show ?thesis
    unfolding bs_complex_extension_def
    by (simp add: F_ax F_iax algebra_simps)
qed

lemma bs_complex_extension_i_smult:
  fixes F :: "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
  assumes F_lin: "linearform UNIV F"
  shows "bs_complex_extension F (cmult_lmat \<i> x)
         = \<i> * bs_complex_extension F x"
proof -
  interpret F_int: linearform UNIV F using F_lin .
  have vs: "Vector_Space.vectorspace (UNIV :: (complex, 'm, 'n) lmat set)"
    by (rule vectorspace_UNIV_lmat)
  have ii_x: "cmult_lmat \<i> (cmult_lmat \<i> x) = - x"
    by (rule cmult_lmat_i_sq)
  have F_neg: "F (- x) = - F x"
    using vs by (simp add: F_int.neg)
  have F_ix2: "F (cmult_lmat \<i> (cmult_lmat \<i> x)) = - F x"
    using ii_x F_neg by simp
  show ?thesis
    unfolding bs_complex_extension_def
    using F_ix2 by (simp add: algebra_simps power2_eq_square)
qed

lemma bs_complex_extension_csmult:
  fixes F :: "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
  assumes F_lin: "linearform UNIV F"
  shows "bs_complex_extension F (cmult_lmat c x)
         = c * bs_complex_extension F x"
proof -
  let ?a = "Re c"
  let ?b = "Im c"
  have c_eq: "c = complex_of_real ?a + \<i> * complex_of_real ?b"
    by (simp add: complex_eq_iff)
  have decomp:
    "cmult_lmat c x
       = Vector_Space.prod ?a x
         + cmult_lmat \<i> (Vector_Space.prod ?b x)"
  proof -
    have step1:
      "cmult_lmat c x
         = cmult_lmat (complex_of_real ?a) x
           + cmult_lmat (\<i> * complex_of_real ?b) x"
      using cmult_lmat_scalar_add[of "complex_of_real ?a" "\<i> * complex_of_real ?b" x]
            c_eq by simp
    have step2: "cmult_lmat (complex_of_real ?a) x = Vector_Space.prod ?a x"
      by (rule cmult_lmat_real)
    have step3:
      "cmult_lmat (\<i> * complex_of_real ?b) x
         = cmult_lmat \<i> (Vector_Space.prod ?b x)"
      by (simp only: cmult_lmat_scalar_mult cmult_lmat_real)
    show ?thesis using step1 step2 step3 by simp
  qed
  have "bs_complex_extension F (cmult_lmat c x)
        = bs_complex_extension F (Vector_Space.prod ?a x
                                  + cmult_lmat \<i> (Vector_Space.prod ?b x))"
    using decomp by simp
  also have "\<dots> = bs_complex_extension F (Vector_Space.prod ?a x)
                  + bs_complex_extension F
                      (cmult_lmat \<i> (Vector_Space.prod ?b x))"
    by (rule bs_complex_extension_add[OF F_lin])
  also have "\<dots> = complex_of_real ?a * bs_complex_extension F x
                  + \<i> * bs_complex_extension F (Vector_Space.prod ?b x)"
    by (simp only: bs_complex_extension_real_smult[OF F_lin]
                  bs_complex_extension_i_smult[OF F_lin])
  also have "\<dots> = complex_of_real ?a * bs_complex_extension F x
                  + \<i> * (complex_of_real ?b * bs_complex_extension F x)"
    by (simp only: bs_complex_extension_real_smult[OF F_lin])
  also have "\<dots> = (complex_of_real ?a + \<i> * complex_of_real ?b)
                  * bs_complex_extension F x"
    by (simp only: algebra_simps)
  also have "\<dots> = c * bs_complex_extension F x"
    using c_eq by simp
  finally show ?thesis.
qed

lemma bs_complex_extension_clinear:
  fixes F :: "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
  assumes F_lin: "linearform UNIV F"
  shows "clinear_functional_on UNIV (bs_complex_extension F)"
  unfolding clinear_functional_on_def
  using bs_complex_extension_add[OF F_lin]
        bs_complex_extension_csmult[OF F_lin]
  by blast

text \<open>The exact Bohnenblust-Sobczyk bound: any \<open>C\<close> bound on \<open>F\<close> lifts
verbatim to a bound on \<open>bs_complex_extension F\<close>. This is the standard
\<open>e^{-i\<theta>}\<close>-rotation argument used to prove the complex
Hahn-Banach theorem from the real one.\<close>

lemma bs_complex_extension_tight_bound:
  fixes F :: "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
  assumes F_lin: "linearform UNIV F"
      and F_C: "\<And>x. \<bar>F x\<bar> \<le> C * hs_norm_lmat x"
  shows "cmod (bs_complex_extension F x) \<le> C * hs_norm_lmat x"
proof (cases "bs_complex_extension F x = 0")
  case True
  have "0 \<le> C * hs_norm_lmat x" by (rule order_trans[OF abs_ge_zero F_C])
  thus ?thesis using True by simp
next
  case False
  let ?z = "bs_complex_extension F x"
  let ?c = "cnj (sgn ?z)"
  have c_mod: "cmod ?c = 1"
    using False by (simp add: norm_sgn)
  have nz: "cmod ?z \<noteq> 0" using False by simp
  have cz: "?c * ?z = complex_of_real (cmod ?z)"
  proof -
    have "?c * ?z = (cnj ?z / complex_of_real (cmod ?z)) * ?z"
      by (simp add: sgn_eq)
    also have "\<dots> = (cnj ?z * ?z) / complex_of_real (cmod ?z)"
      by simp
    also have "\<dots> = complex_of_real ((cmod ?z)\<^sup>2) / complex_of_real (cmod ?z)"
      unfolding complex_norm_square by (simp only: mult.commute)
    also have "\<dots> = complex_of_real (cmod ?z)"
      using nz by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  let ?y = "cmult_lmat ?c x"
  have h_y: "hs_norm_lmat ?y = hs_norm_lmat x"
    using c_mod by (simp add: hs_norm_lmat_cmult)
  have f_y: "bs_complex_extension F ?y = ?c * ?z"
    using bs_complex_extension_csmult[OF F_lin, of ?c x] .
  have f_y_real: "bs_complex_extension F ?y = complex_of_real (cmod ?z)"
    using f_y cz by simp
  have F_y: "F ?y = cmod ?z"
  proof -
    have "Re (bs_complex_extension F ?y) = F ?y"
      unfolding bs_complex_extension_def by simp
    moreover have "Re (bs_complex_extension F ?y) = cmod ?z"
      using f_y_real by simp
    ultimately show ?thesis by simp
  qed
  have "cmod ?z = F ?y" using F_y by simp
  also have "\<dots> \<le> \<bar>F ?y\<bar>" by simp
  also have "\<dots> \<le> C * hs_norm_lmat ?y" by (rule F_C)
  also have "\<dots> = C * hs_norm_lmat x" using h_y by simp
  finally show ?thesis .
qed

lemma bs_complex_extension_bounded:
  fixes F :: "(complex, 'm :: finite, 'n :: finite) lmat \<Rightarrow> real"
  assumes F_lin: "linearform UNIV F"
      and F_cont: "continuous UNIV F hs_norm_lmat"
  shows "\<exists>C \<ge> 0. \<forall>x. cmod (bs_complex_extension F x) \<le> C * hs_norm_lmat x"
proof -
  obtain c where c_bnd: "\<forall>x \<in> UNIV. \<bar>F x\<bar> \<le> c * hs_norm_lmat x"
    using F_cont continuous.bounded by blast
  let ?C = "\<bar>c\<bar>"
  have C_nn: "?C \<ge> 0" by simp
  have F_C: "\<And>x. \<bar>F x\<bar> \<le> ?C * hs_norm_lmat x"
  proof -
    fix x :: "(complex, 'm, 'n) lmat"
    have h_nn: "0 \<le> hs_norm_lmat x" by (rule hs_norm_lmat_nonneg)
    have "\<bar>F x\<bar> \<le> c * hs_norm_lmat x" using c_bnd by simp
    also have "\<dots> \<le> ?C * hs_norm_lmat x"
      using h_nn by (simp add: mult_right_mono)
    finally show "\<bar>F x\<bar> \<le> ?C * hs_norm_lmat x" .
  qed
  have main_bnd:
    "\<And>x. cmod (bs_complex_extension F x) \<le> ?C * hs_norm_lmat x"
    using bs_complex_extension_tight_bound[OF F_lin F_C] by simp
  show ?thesis using C_nn main_bnd by blast
qed

lemma bs_complex_extension_extends:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
      and F :: "(complex, 'm, 'n) lmat \<Rightarrow> real"
  assumes g_clin: "clinear_functional_on V g"
      and V_clos_i: "\<forall>x \<in> V. cmult_lmat \<i> x \<in> V"
      and F_ext: "\<forall>x \<in> V. F x = re_part_lmat g x"
  shows "\<forall>x \<in> V. bs_complex_extension F x = g x"
proof
  fix x assume xV: "x \<in> V"
  have ixV: "cmult_lmat \<i> x \<in> V" using V_clos_i xV by simp
  have Fx: "F x = Re (g x)"
    using F_ext xV by (simp add: re_part_lmat_def)
  have g_ix: "g (cmult_lmat \<i> x) = \<i> * g x"
    using g_clin xV unfolding clinear_functional_on_def by simp
  have Fix: "F (cmult_lmat \<i> x) = Re (\<i> * g x)"
    using F_ext ixV g_ix by (simp add: re_part_lmat_def)
  have re_i: "Re (\<i> * g x) = - Im (g x)" by simp
  have "bs_complex_extension F x
        = complex_of_real (Re (g x))
          - \<i> * complex_of_real (- Im (g x))"
    unfolding bs_complex_extension_def using Fx Fix re_i by simp
  also have "\<dots> = complex_of_real (Re (g x)) + \<i> * complex_of_real (Im (g x))"
    by simp
  also have "\<dots> = g x"
    by (simp add: complex_eq_iff)
  finally show "bs_complex_extension F x = g x" .
qed

subsection \<open>The matrix-space Hahn-Banach theorem\<close>

text \<open>Combine all the steps: a bounded complex-linear functional on
a complex-linear subspace V of \<open>(complex, 'm, 'n) lmat\<close> extends to a
bounded complex-linear functional on all of \<open>(complex, 'm, 'n) lmat\<close>
(without claiming norm preservation; for the application to Arveson
Extension this is enough together with the bound chase).\<close>

theorem matrix_hahn_banach_lmat:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
  assumes V_csub: "cmat_subspace_lmat V"
      and g_bnd: "bounded_clinear_functional_on V g"
  shows "\<exists>f :: (complex, 'm, 'n) lmat \<Rightarrow> complex.
            bounded_clinear_functional_on UNIV f
          \<and> (\<forall>x \<in> V. f x = g x)"
proof -
  have V_sub: "Subspace.subspace V (UNIV :: (complex, 'm, 'n) lmat set)"
    using V_csub by (rule subspace_of_cmat_subspace_lmat)
  have V_clos_i: "\<forall>x \<in> V. cmult_lmat \<i> x \<in> V"
    using V_csub unfolding cmat_subspace_lmat_def cmult_lmat_def by simp
  have g_clin: "clinear_functional_on V g"
    using g_bnd unfolding bounded_clinear_functional_on_def by simp
  obtain F where
      F_lin: "linearform UNIV F"
    and F_cont: "continuous UNIV F hs_norm_lmat"
    and F_ext: "\<forall>x \<in> V. F x = re_part_lmat g x"
    using hahn_banach_re_part_lmat[OF V_sub g_bnd] by blast
  let ?f = "bs_complex_extension F"
  have f_clin: "clinear_functional_on UNIV ?f"
    by (rule bs_complex_extension_clinear[OF F_lin])
  have f_bnd: "\<exists>C \<ge> 0. \<forall>x \<in> UNIV. cmod (?f x) \<le> C * hs_norm_lmat x"
    using bs_complex_extension_bounded[OF F_lin F_cont] by blast
  have f_bclin: "bounded_clinear_functional_on UNIV ?f"
    using f_clin f_bnd unfolding bounded_clinear_functional_on_def by blast
  have f_ext: "\<forall>x \<in> V. ?f x = g x"
    by (rule bs_complex_extension_extends[OF g_clin V_clos_i F_ext])
  show ?thesis using f_bclin f_ext by blast
qed

text \<open>The explicit-bound form of the matrix Hahn-Banach theorem:
any \<open>C\<close>-bound on \<open>\<bar>Re \<circ> g\<bar>\<close> over the subspace \<open>V\<close> lifts
verbatim to a \<open>C\<close>-bound on \<open>cmod \<circ> f\<close> over the whole space.

The proof unfolds HOL/Hahn\_Banach's locale-local \<open>fn_norm\<close>
to its \<open>Sup\<close>-based definition, bounds the supremum on the
subspace side by \<open>C\<close> via \<open>g_re_C\<close>, transports the bound to
the extension side via \<open>norm_Hahn_Banach\<close>'s norm-preservation
conclusion, then uses \<open>bs_complex_extension_tight_bound\<close> to
turn the bound on the real extension into a bound on the
complex extension.\<close>

theorem matrix_hahn_banach_lmat_with_bound:
  fixes V :: "(complex, 'm :: finite, 'n :: finite) lmat set"
      and g :: "(complex, 'm, 'n) lmat \<Rightarrow> complex"
      and C :: real
  assumes V_csub: "cmat_subspace_lmat V"
      and g_clin: "clinear_functional_on V g"
      and g_re_C: "\<forall>x \<in> V. \<bar>Re (g x)\<bar> \<le> C * hs_norm_lmat x"
      and C_nn: "0 \<le> C"
  shows "\<exists>f :: (complex, 'm, 'n) lmat \<Rightarrow> complex.
            clinear_functional_on UNIV f
          \<and> (\<forall>x \<in> V. f x = g x)
          \<and> (\<forall>x. cmod (f x) \<le> C * hs_norm_lmat x)"
proof -
  have V_sub: "Subspace.subspace V (UNIV :: (complex, 'm, 'n) lmat set)"
    using V_csub by (rule subspace_of_cmat_subspace_lmat)
  have V_clos_i: "\<forall>x \<in> V. cmult_lmat \<i> x \<in> V"
    using V_csub unfolding cmat_subspace_lmat_def cmult_lmat_def by simp
  have re_lin: "linearform V (re_part_lmat g)"
    using V_sub g_clin by (rule linearform_re_part_lmat)
  have re_C: "\<And>x. x \<in> V \<Longrightarrow> \<bar>re_part_lmat g x\<bar> \<le> C * hs_norm_lmat x"
    using g_re_C unfolding re_part_lmat_def by simp
  have re_cont: "continuous V (re_part_lmat g) hs_norm_lmat"
    using re_lin re_C by (rule continuousI)
  have nv: "normed_vectorspace UNIV hs_norm_lmat"
    by (rule normed_vectorspace_UNIV_lmat)

  text \<open>Interpret HOL/Hahn\_Banach's
\<open>normed_vectorspace_with_fn_norm\<close> locale on our setting. Inside
the interpretation we get \<open>fn_norm_le_cong\<close> (\<open>\<bar>F x\<bar> \<le>
\<parallel>F\<parallel> \<cdot> \<parallel>x\<parallel>\<close>) and \<open>fn_norm_leastB\<close>
(\<open>\<parallel>F\<parallel> \<le> y\<close> from a uniform bound on \<open>B\<close>).\<close>

  interpret nvfn_E: normed_vectorspace_with_fn_norm
    "UNIV :: (complex, 'm, 'n) lmat set" hs_norm_lmat
    "\<lambda>V f. {0::real} \<union>
            {\<bar>f x\<bar> / hs_norm_lmat x | x. x \<noteq> 0 \<and> x \<in> V}"
    "\<lambda>f V. \<Squnion>({0::real} \<union>
              {\<bar>f x\<bar> / hs_norm_lmat x | x. x \<noteq> 0 \<and> x \<in> V})"
    using nv
    by (intro_locales)
       (auto dest: normed_vectorspace.axioms norm.axioms)

  have nv_V: "normed_vectorspace V hs_norm_lmat"
    using V_sub nv by (rule subspace_normed_vs)
  interpret nvfn_V: normed_vectorspace_with_fn_norm
    V hs_norm_lmat
    "\<lambda>V f. {0::real} \<union>
            {\<bar>f x\<bar> / hs_norm_lmat x | x. x \<noteq> 0 \<and> x \<in> V}"
    "\<lambda>f V. \<Squnion>({0::real} \<union>
              {\<bar>f x\<bar> / hs_norm_lmat x | x. x \<noteq> 0 \<and> x \<in> V})"
    using nv_V
    by (intro_locales)
       (auto dest: normed_vectorspace.axioms norm.axioms)

  obtain F where
      F_lin: "linearform UNIV F"
    and F_cont: "continuous UNIV F hs_norm_lmat"
    and F_ext_V: "\<forall>x \<in> V. F x = re_part_lmat g x"
    and F_fn_eq:
      "\<Squnion>({0::real} \<union>
          {\<bar>F x\<bar> / hs_norm_lmat x | x. x \<noteq> 0 \<and> x \<in> (UNIV :: (complex, 'm, 'n) lmat set)})
       = \<Squnion>({0::real} \<union>
              {\<bar>re_part_lmat g x\<bar> / hs_norm_lmat x | x. x \<noteq> 0 \<and> x \<in> V})"
    using norm_Hahn_Banach[OF nv V_sub re_lin re_cont] by blast

  let ?B_F = "{0::real} \<union>
              {\<bar>F x\<bar> / hs_norm_lmat x | x. x \<noteq> 0
                                          \<and> x \<in> (UNIV :: (complex, 'm, 'n) lmat set)}"
  let ?B_re = "{0::real} \<union>
                {\<bar>re_part_lmat g x\<bar> / hs_norm_lmat x | x. x \<noteq> 0 \<and> x \<in> V}"

  text \<open>Bound the subspace-side \<open>fn_norm\<close> by \<open>C\<close>.\<close>
  have re_fn_le_C: "\<Squnion>(?B_re) \<le> C"
  proof (rule nvfn_V.fn_norm_leastB[OF re_cont])
    fix b assume "b \<in> {0} \<union>
                  {\<bar>re_part_lmat g x\<bar> / hs_norm_lmat x | x. x \<noteq> 0 \<and> x \<in> V}"
    then consider "b = 0" |
                  x where "b = \<bar>re_part_lmat g x\<bar> / hs_norm_lmat x"
                          "x \<noteq> 0" "x \<in> V"
      by blast
    thus "b \<le> C"
    proof cases
      case 1 thus ?thesis using C_nn by simp
    next
      case (2 x)
      have h_pos: "0 < hs_norm_lmat x"
        using \<open>x \<noteq> 0\<close> hs_norm_lmat_nonneg[of x] by (simp add: hs_norm_lmat_zero_iff order_le_less)
      have re_bnd: "\<bar>re_part_lmat g x\<bar> \<le> C * hs_norm_lmat x"
        using re_C \<open>x \<in> V\<close> by blast
      have "b = \<bar>re_part_lmat g x\<bar> / hs_norm_lmat x" using 2 by simp
      also have "\<dots> \<le> C"
        using re_bnd h_pos by (auto simp: divide_le_eq)
      finally show ?thesis .
    qed
  qed
  have F_fn_le_C: "\<Squnion>(?B_F) \<le> C" using F_fn_eq re_fn_le_C by simp

  text \<open>Use \<open>fn_norm_le_cong\<close> to extract the explicit \<open>C\<close> bound on
  \<open>F\<close>.\<close>
  have F_C: "\<And>x. \<bar>F x\<bar> \<le> C * hs_norm_lmat x"
  proof -
    fix x :: "(complex, 'm, 'n) lmat"
    have h_nn: "0 \<le> hs_norm_lmat x" by (rule hs_norm_lmat_nonneg)
    have step1: "\<bar>F x\<bar> \<le> \<Squnion>(?B_F) * hs_norm_lmat x"
      using F_cont F_lin
      by (intro nvfn_E.fn_norm_le_cong) auto
    also have "\<dots> \<le> C * hs_norm_lmat x"
      using F_fn_le_C h_nn by (rule mult_right_mono)
    finally show "\<bar>F x\<bar> \<le> C * hs_norm_lmat x" .
  qed

  let ?f = "bs_complex_extension F"
  have f_clin: "clinear_functional_on UNIV ?f"
    by (rule bs_complex_extension_clinear[OF F_lin])
  have f_C: "\<forall>x. cmod (?f x) \<le> C * hs_norm_lmat x"
    using bs_complex_extension_tight_bound[OF F_lin F_C] by simp
  have f_ext: "\<forall>x \<in> V. ?f x = g x"
    by (rule bs_complex_extension_extends[OF g_clin V_clos_i F_ext_V])
  show ?thesis using f_clin f_ext f_C by blast
qed

end
