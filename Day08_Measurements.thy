(*  Title:   Day08_Measurements.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 14 September 2011 (Day 8)
*)

theory Day08_Measurements
  imports Day07_Postulates
begin

section \<open>Day 8 (14 September 2011): the quantum game; projective measurements and expected values\<close>

subsection \<open>Distinguishing states\<close>

text \<open>Alice has two states $\psi_1,\psi_2$ known to Bob; she sends one.  Can Bob build a
measurement system that decides with certainty which one he received?  Formally one wants
$M_1,M_2$ with $\norm{M_1\psi_2}=0$, $\norm{M_1\psi_1}^2=1$, $\norm{M_2\psi_1}=0$,
$\norm{M_2\psi_2}^2=1$.

Case I, $\psi_1\perp\psi_2$: take $M_1=\ketbra{\psi_1}{\psi_1}$, $M_2=\ketbra{\psi_2}{\psi_2}$
and $M_3=I-M_1-M_2$; this distinguishes with certainty (formalised below).

Case II, $\psi_1\not\perp\psi_2$: write $\psi_2=\alpha\psi_1+\beta\gamma$ with
$\gamma\perp\psi_1$ a unit vector, so $\alpha\neq 0$; any measurement system with
$\norm{M_1\psi_1}=1$ satisfies $|\alpha|^2\le\norm{M_1\psi_2}^2$, so outcome $1$ also
occurs with probability at least $|\alpha|^2$ when $\psi_2$ is sent
(\<open>nonorthogonal_outcome_prob\<close> in theory Day02\_11\_Supplement).

\begin{notestheorem}
Given linearly independent states $\psi_1,\dots,\psi_n$ there is a measurement system
$M_0,\dots,M_n$ such that if outcome $i\ge 1$ occurs then $\psi_i$ was received.
\end{notestheorem}
The notes' proof takes $E_i$ the projection onto $\operatorname{span}\{\psi_j:j\neq i\}^\perp$,
$M_i=E_i/\sqrt n$, and $M_0=(I-\sum_i M_i^*M_i)^{1/2}$; the remark that follows observes
that the inconclusive outcome $0$ then has probability at least $(n-1)/n$.  Formally this is
\<open>lin_indep_states_unambiguous\<close> below.\<close>

lemma outer_proj_self:
  assumes q: "quantum_state n \<psi>"
  shows "outer_prod \<psi> \<psi> *\<^sub>v \<psi> = \<psi>"
proof -
  have \<psi>dim: "dim_vec \<psi> = n"
    using q by (simp add: quantum_state_def)
  have \<psi>norm: "\<langle>\<psi> | \<psi>\<rangle> = 1"
    by (metis (no_types) csqrt_eq_1 inner_prod_csqrt of_real_1 q quantum_state_def)
  show ?thesis
  proof (rule eq_vecI)
    show "dim_vec (outer_prod \<psi> \<psi> *\<^sub>v \<psi>) = dim_vec \<psi>"
      by (simp add: outer_prod_mult_vec)

  next
    fix i
    assume i: "i < dim_vec \<psi>"
    then have ilt: "i < n"
      using \<psi>dim by simp
    have "(outer_prod \<psi> \<psi> *\<^sub>v \<psi>) $ i
        = (\<Sum>j = 0..<n. (outer_prod \<psi> \<psi>) $$ (i,j) * \<psi> $ j)"
      using \<psi>dim ilt
      by (metis (no_types, lifting) bra_bra_vec carrier_mat_triv carrier_vec_dim_vec dagger_of_ket_is_bra dim_col_of_dagger
          dim_row_mat(1) index_mult_mat(2,3) ket_vec_def mult_mat_vec_index sum.cong)
    also have "... = (\<Sum>j = 0..<n. (\<psi> $ i * cnj (\<psi> $ j)) * \<psi> $ j)"
      using \<psi>dim ilt
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) 
          calculation inner_prod_def outer_prod_mult_vec_index sum.cong sum_distrib_left)
    also have "... = (\<psi> $ i) * (\<Sum>j = 0..<n. cnj (\<psi> $ j) * \<psi> $ j)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<psi> $ i) * \<langle>\<psi> | \<psi>\<rangle>"
      using \<psi>dim by (simp add: inner_prod_def)
    also have "... = \<psi> $ i"
      using \<psi>norm by simp
    finally show "(outer_prod \<psi> \<psi> *\<^sub>v \<psi>) $ i = \<psi> $ i" .
  qed
qed

lemma outer_proj_orth_zero:
  assumes q1: "quantum_state n \<psi>1"
      and q2: "quantum_state n \<psi>2"
      and orth: "\<langle>\<psi>1 | \<psi>2\<rangle> = 0"
  shows "outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2 = 0\<^sub>v n"
proof -
  have d1: "dim_vec \<psi>1 = n"
    using q1 by (simp add: quantum_state_def)
  have d2: "dim_vec \<psi>2 = n"
    using q2 by (simp add: quantum_state_def)

  show ?thesis
  proof (rule eq_vecI)
    show "dim_vec (outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2) = dim_vec (0\<^sub>v n)"
      by (simp add: d1 d2 outer_prod_mult_vec)
  next
    fix i
    assume i: "i < dim_vec (0\<^sub>v n)"
    then have ilt: "i < n"
      by simp
    have "(outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2) $ i
        = (\<Sum>j = 0..<n. (outer_prod \<psi>1 \<psi>1) $$ (i,j) * \<psi>2 $ j)"
      using d1 d2 ilt
      by (metis (no_types, lifting) bra_bra_vec carrier_mat_triv carrier_vec_dim_vec dagger_of_ket_is_bra dim_col_of_dagger
          dim_row_mat(1) index_mult_mat(2,3) ket_vec_def mult_mat_vec_index sum.cong)
    also have "... = (\<Sum>j = 0..<n. (\<psi>1 $ i * cnj (\<psi>1 $ j)) * \<psi>2 $ j)"
      using d1 ilt
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) calculation d2 inner_prod_def
          outer_prod_mult_vec_index sum.cong sum_distrib_left)
    also have "... = (\<psi>1 $ i) * (\<Sum>j = 0..<n. cnj (\<psi>1 $ j) * \<psi>2 $ j)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... = (\<psi>1 $ i) * \<langle>\<psi>1 | \<psi>2\<rangle>"
      using d1 d2 by (simp add: inner_prod_def)
    also have "... = 0"
      using orth by simp
    also have "... = (0\<^sub>v n) $ i"
      using ilt by simp
    finally show "(outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2) $ i = (0\<^sub>v n) $ i" .
  qed
qed

lemma outer_proj_idem:
  assumes q: "quantum_state n \<psi>"
  shows "(outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>) = outer_prod \<psi> \<psi>"
proof -
  have \<psi>dim: "dim_vec \<psi> = n"
    using q by (simp add: quantum_state_def)
  have \<psi>norm: "\<langle>\<psi> | \<psi>\<rangle> = 1"
    by (metis (full_types) csqrt_eq_1 inner_prod_csqrt of_real_1 q quantum_state_def)
  show ?thesis
  proof (rule eq_matI)
    show "dim_row ((outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>)) = dim_row (outer_prod \<psi> \<psi>)"
      using \<psi>dim by simp
    show "dim_col ((outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>)) = dim_col (outer_prod \<psi> \<psi>)"
      using \<psi>dim by simp
  next
    fix r c
    assume r: "r < dim_row (outer_prod \<psi> \<psi>)"
    assume c: "c < dim_col (outer_prod \<psi> \<psi>)"
    then have rlt: "r < n" and clt: "c < n"
      by (metis \<psi>dim dim_col index_mult_mat(2) ket_vec_col r,
          metis \<psi>dim c dim_vec index_mult_mat(3) index_row(2) row_bra_vec)
    have "((outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>)) $$ (r,c)
      = (\<Sum>j = 0..<n. (outer_prod \<psi> \<psi>) $$ (r,j) * (outer_prod \<psi> \<psi>) $$ (j,c))"
      by (metis (no_types, lifting) ext \<psi>dim atLeast0LessThan bra_bra_vec clt dagger_of_ket_is_bra 
          dim_col dim_col_of_dagger index_matrix_prod index_mult_mat(2,3) ket_vec_col rlt)  
    also have "... = (\<Sum>j = 0..<n. (\<psi> $ r * cnj (\<psi> $ j)) * (\<psi> $ j * cnj (\<psi> $ c)))"
    proof (rule sum.cong[OF refl])
      fix j assume "j \<in> {0..<n}"
      then have jn: "j < n" by simp
      have rv: "r < dim_vec \<psi>" using \<psi>dim rlt by simp
      have jv: "j < dim_vec \<psi>" using \<psi>dim jn by simp
      have cv: "c < dim_vec \<psi>" using \<psi>dim clt by simp
      have step_rj: "(outer_prod \<psi> \<psi>) $$ (r,j) = \<psi> $ r * cnj (\<psi> $ j)"
        using outer_prod_index[OF rv jv] .
      have step_jc: "(outer_prod \<psi> \<psi>) $$ (j,c) = \<psi> $ j * cnj (\<psi> $ c)"
        using outer_prod_index[OF jv cv] .
      show "(outer_prod \<psi> \<psi>) $$ (r,j) * (outer_prod \<psi> \<psi>) $$ (j,c)
          = (\<psi> $ r * cnj (\<psi> $ j)) * (\<psi> $ j * cnj (\<psi> $ c))"
        using step_rj step_jc by simp
    qed
    also have "... = (\<psi> $ r) * (\<Sum>j = 0..<n. cnj (\<psi> $ j) * \<psi> $ j) * cnj (\<psi> $ c)"
      by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
    also have "... = (\<psi> $ r) * \<langle>\<psi> | \<psi>\<rangle> * cnj (\<psi> $ c)"
      using \<psi>dim by (simp add: inner_prod_def)
    also have "... = \<psi> $ r * cnj (\<psi> $ c)"
      using \<psi>norm by simp
    also have "... = (outer_prod \<psi> \<psi>) $$ (r,c)"
      using \<psi>dim rlt clt outer_prod_index by presburger
    finally show "((outer_prod \<psi> \<psi>) * (outer_prod \<psi> \<psi>)) $$ (r,c) = (outer_prod \<psi> \<psi>) $$ (r,c)".
  qed
qed

lemma outer_proj_hermitian:
  assumes "dim_vec \<psi> = n"
  shows "(outer_prod \<psi> \<psi>)\<^sup>\<dagger> = outer_prod \<psi> \<psi>"
proof (rule eq_matI)
  show "dim_row ((outer_prod \<psi> \<psi>)\<^sup>\<dagger>) = dim_row (outer_prod \<psi> \<psi>)"
    by (metis (no_types) bra_bra_vec bra_def dim_col_mat(1) dim_row_of_dagger index_mult_mat(2,3))
  show "dim_col ((outer_prod \<psi> \<psi>)\<^sup>\<dagger>) = dim_col (outer_prod \<psi> \<psi>)"
    by (simp add: bra_vec_def cpx_mat_cnj_def ket_vec_def row_vec_def)
next
  fix i j
  assume i: "i < dim_row (outer_prod \<psi> \<psi>)"
  assume j: "j < dim_col (outer_prod \<psi> \<psi>)"
  then have ilt: "i < n" and jlt: "j < n"
    using assms i ket_vec_def  
    by (auto, metis bra_bra_vec dagger_of_ket_is_bra dim_col_of_dagger dim_row_mat(1))
  have "((outer_prod \<psi> \<psi>)\<^sup>\<dagger>) $$ (i,j) = cnj ((outer_prod \<psi> \<psi>) $$ (j,i))"
    using assms ilt jlt
    by (simp add: bra_vec_def cpx_mat_cnj_def dagger_def ket_vec_def row_vec_def)
  also have "... = cnj (\<psi> $ j * cnj (\<psi> $ i))"
    using assms ilt jlt outer_prod_index by presburger
  also have "... = \<psi> $ i * cnj (\<psi> $ j)"
    by simp
  also have "... = (outer_prod \<psi> \<psi>) $$ (i,j)"
    using assms ilt jlt outer_prod_index by presburger
  finally show "((outer_prod \<psi> \<psi>)\<^sup>\<dagger>) $$ (i,j) = (outer_prod \<psi> \<psi>) $$ (i,j)".
qed

lemma outer_proj_cross_zero:
  assumes q1: "quantum_state n \<psi>1"
      and q2: "quantum_state n \<psi>2"
      and orth: "\<langle>\<psi>1 | \<psi>2\<rangle> = 0"
  shows "(outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2) = 0\<^sub>m n n"
proof -
  have d1: "dim_vec \<psi>1 = n"
    using q1 by (simp add: quantum_state_def)
  have d2: "dim_vec \<psi>2 = n"
    using q2 by (simp add: quantum_state_def)
  show ?thesis
  proof (rule eq_matI)
    show "dim_row ((outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2)) = dim_row (0\<^sub>m n n)"
      by (simp add: d1 ket_vec_def)
    show "dim_col ((outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2)) = dim_col (0\<^sub>m n n)"
      by (simp add: bra_vec_def cpx_mat_cnj_def d2 row_vec_def)
  next
    fix r c
    assume r: "r < dim_row (0\<^sub>m n n)"
    assume c: "c < dim_col (0\<^sub>m n n)"
    then have rlt: "r < n" and clt: "c < n"
      using r by auto
    have "((outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2)) $$ (r,c)
        = (\<Sum>j = 0..<n. (outer_prod \<psi>1 \<psi>1) $$ (r,j) * (outer_prod \<psi>2 \<psi>2) $$ (j,c))"
      using d1 d2 rlt clt
      by (metis (no_types, lifting) ext atLeast0LessThan bra_bra_vec dagger_of_ket_is_bra dim_col 
          dim_col_of_dagger index_matrix_prod index_mult_mat(2,3) ket_vec_col)
    also have "... = (\<Sum>j = 0..<n. (\<psi>1 $ r * cnj (\<psi>1 $ j)) * (\<psi>2 $ j * cnj (\<psi>2 $ c)))"
    proof (rule sum.cong[OF refl])
      fix j assume "j \<in> {0..<n}"
      then have jn: "j < n" by simp
      have rv: "r < dim_vec \<psi>1" using d1 rlt by simp
      have jv1: "j < dim_vec \<psi>1" using d1 jn by simp
      have jv2: "j < dim_vec \<psi>2" using d2 jn by simp
      have cv: "c < dim_vec \<psi>2" using d2 clt by simp
      have step_rj: "(outer_prod \<psi>1 \<psi>1) $$ (r,j) = \<psi>1 $ r * cnj (\<psi>1 $ j)"
        using outer_prod_index[OF rv jv1] .
      have step_jc: "(outer_prod \<psi>2 \<psi>2) $$ (j,c) = \<psi>2 $ j * cnj (\<psi>2 $ c)"
        using outer_prod_index[OF jv2 cv] .
      show "(outer_prod \<psi>1 \<psi>1) $$ (r,j) * (outer_prod \<psi>2 \<psi>2) $$ (j,c)
          = (\<psi>1 $ r * cnj (\<psi>1 $ j)) * (\<psi>2 $ j * cnj (\<psi>2 $ c))"
        using step_rj step_jc by simp
    qed
    also have "... = (\<psi>1 $ r) * (\<Sum>j = 0..<n. cnj (\<psi>1 $ j) * \<psi>2 $ j) * cnj (\<psi>2 $ c)"
      by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
    also have "... = (\<psi>1 $ r) * \<langle>\<psi>1 | \<psi>2\<rangle> * cnj (\<psi>2 $ c)"
      using d1 d2 by (simp add: inner_prod_def)
    also have "... = 0"
      using orth by simp
    also have "... = (0\<^sub>m n n) $$ (r,c)"
      using rlt clt by simp
    finally show "((outer_prod \<psi>1 \<psi>1) * (outer_prod \<psi>2 \<psi>2)) $$ (r,c) = (0\<^sub>m n n) $$ (r,c)".
  qed
qed

text \<open>Case I: orthogonal states can be distinguished perfectly.\<close>

lemma orthogonal_states_distinguishable:
  fixes \<psi>1 \<psi>2 :: "complex Matrix.vec"
  assumes q1: "quantum_state n \<psi>1"
      and q2: "quantum_state n \<psi>2"
      and orth: "\<langle>\<psi>1 | \<psi>2\<rangle> = 0"
  shows "\<exists>Ms :: complex Matrix.mat list.
         measurement_system n Ms \<and>
         (\<exists>M1 M2. M1 \<in> set Ms \<and> M2 \<in> set Ms \<and>
            meas_prob M1 \<psi>1 = 1 \<and> meas_prob M2 \<psi>1 = 0 \<and>
            meas_prob M1 \<psi>2 = 0 \<and> meas_prob M2 \<psi>2 = 1)"
proof -
  have \<psi>1dim: "dim_vec \<psi>1 = n"
    using q1 by (simp add: quantum_state_def)
  have \<psi>2dim: "dim_vec \<psi>2 = n"
    using q2 by (simp add: quantum_state_def)

  let ?P1 = "outer_prod \<psi>1 \<psi>1"
  let ?Q = "1\<^sub>m n - ?P1"
  let ?Ms = "[?P1, ?Q]"

  have P1car: "?P1 \<in> carrier_mat n n"
    by (metis \<psi>1dim carrier_mat_triv dim_mult_mat_vec dim_row_of_dagger outer_proj_hermitian outer_proj_self q1)
  have Qcar: "?Q \<in> carrier_mat n n"
    by (simp add: P1car minus_carrier_mat)
  have P1herm: "?P1\<^sup>\<dagger> = ?P1"
    using outer_proj_hermitian[OF \<psi>1dim].

  have P1idem: "?P1 * ?P1 = ?P1"
    using outer_proj_idem[OF q1].

  have Qherm: "?Q\<^sup>\<dagger> = ?Q"
  proof (rule eq_matI)
    show "dim_row (?Q\<^sup>\<dagger>) = dim_row ?Q"
      by (metis Qcar carrier_matD(1,2) dim_row_of_dagger)
    show "dim_col (?Q\<^sup>\<dagger>) = dim_col ?Q"
      by (metis Qcar carrier_matD(1,2) dim_col_of_dagger)
  next
    fix i j
    assume i: "i < dim_row ?Q" and j: "j < dim_col ?Q"
    have iln: "i < n" and jln: "j < n"
      using i j Qcar by auto
    have "?Q\<^sup>\<dagger> $$ (i,j) = cnj (?Q $$ (j,i))"
      using iln jln Qcar
      by (simp add: dagger_def,
          metis P1car carrier_matD(1,2) case_prod_conv index_mat(1) index_mult_mat(2,3))
    also have "... = cnj ((1\<^sub>m n) $$ (j,i) - ?P1 $$ (j,i))"
      using P1car iln jln
      by (metis carrier_matD(1,2) index_minus_mat(1))
    also have "... = cnj ((1\<^sub>m n) $$ (j,i)) - cnj (?P1 $$ (j,i))"
      by simp
    also have "... = (1\<^sub>m n) $$ (i,j) - cnj (?P1 $$ (j,i))"
      using iln jln by simp
    also have "... = (1\<^sub>m n) $$ (i,j) - ?P1 $$ (i,j)"
      using P1herm P1car iln jln
      by (simp add: dagger_def,
          metis P1herm carrier_matD(1,2) hermitian_def hermitian_index)
    also have "... = ?Q $$ (i,j)"
      using P1car iln jln
      by (metis carrier_matD(1,2) index_minus_mat(1))
    finally show "?Q\<^sup>\<dagger> $$ (i,j) = ?Q $$ (i,j)".
  qed

  have Qidem: "?Q * ?Q = ?Q"
  proof (rule eq_matI)
    show "dim_row (?Q * ?Q) = dim_row ?Q"
      using Qcar by simp
    show "dim_col (?Q * ?Q) = dim_col ?Q"
      using Qcar by simp
  next
    fix r c
    assume r: "r < dim_row ?Q" and c: "c < dim_col ?Q"
    have rln: "r < n" and cln: "c < n"
      using r c Qcar by auto

    have qq_expand:
      "?Q * ?Q =
        ((1\<^sub>m n) * (1\<^sub>m n)) - ((1\<^sub>m n) * ?P1) - (?P1 * (1\<^sub>m n)) + (?P1 * ?P1)"
    proof -
      have "?Q * ?Q = (1\<^sub>m n) * (1\<^sub>m n - ?P1) - ?P1 * (1\<^sub>m n - ?P1)"
        using P1car by (meson Qcar minus_mult_distrib_mat one_carrier_mat)
      also have "... = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * ?P1)
                       - (?P1 * (1\<^sub>m n) - ?P1 * ?P1)"
        using P1car by (simp add: right_diff_distrib,
                        metis left_mult_one_mat mult_minus_distrib_mat one_carrier_mat)
      also have "... = ((1\<^sub>m n) * (1\<^sub>m n)) - ((1\<^sub>m n) * ?P1) - (?P1 * (1\<^sub>m n)) + (?P1 * ?P1)"
      proof -
        have "((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * ?P1)
              - (?P1 * (1\<^sub>m n) - ?P1 * ?P1)
            = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * ?P1)
              + (-(?P1 * (1\<^sub>m n) - ?P1 * ?P1))"
          by auto
        also have "... = ((1\<^sub>m n) * (1\<^sub>m n) - (1\<^sub>m n) * ?P1)
                         + (-(?P1 * (1\<^sub>m n)) + (?P1 * ?P1))"
          using P1car by fastforce
        also have "... = ((1\<^sub>m n) * (1\<^sub>m n)) - ((1\<^sub>m n) * ?P1) - (?P1 * (1\<^sub>m n)) + (?P1 * ?P1)"
          using Qcar by fastforce
        finally show ?thesis .
      qed
      finally show ?thesis .
    qed

    have "(?Q * ?Q) $$ (r,c)
        = (((1\<^sub>m n) * (1\<^sub>m n)) - ((1\<^sub>m n) * ?P1) - (?P1 * (1\<^sub>m n)) + (?P1 * ?P1)) $$ (r,c)"
      using qq_expand by simp
    also have "... = ((1\<^sub>m n) $$ (r,c) - ((1\<^sub>m n) * ?P1) $$ (r,c) - (?P1 * (1\<^sub>m n)) $$ (r,c)
                     + (?P1 * ?P1) $$ (r,c))"
      using rln cln P1car by(simp, smt (verit, ccfv_SIG) P1idem carrier_matD(1,2) diff_0 
          index_add_mat(1) index_minus_mat(1) index_one_mat(1) left_mult_one_mat right_mult_one_mat)
    also have "... = ((1\<^sub>m n) $$ (r,c) - ?P1 $$ (r,c) - ?P1 $$ (r,c) + (?P1 * ?P1) $$ (r,c))"
      using rln cln P1car
      by (simp add: left_mult_one_mat right_mult_one_mat)
    also have "... = ((1\<^sub>m n) $$ (r,c) - ?P1 $$ (r,c) - ?P1 $$ (r,c) + ?P1 $$ (r,c))"
      using P1idem rln cln P1car by simp
    also have "... = ((1\<^sub>m n) $$ (r,c) - ?P1 $$ (r,c))"
      by simp      
    also have "... = ?Q $$ (r,c)"
      using rln cln P1car
      by (metis carrier_matD(1,2) index_minus_mat(1)) 
    finally show "(?Q * ?Q) $$ (r,c) = ?Q $$ (r,c)".
  qed

  have meas_sys: "measurement_system n ?Ms"
  proof -
    have carrs: "\<forall>M \<in> set ?Ms. M \<in> carrier_mat n n"
      using P1car Qcar by simp
    have fold_eq: "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) ?Ms (0\<^sub>m n n) = 1\<^sub>m n"
    proof -
      have "foldr (\<lambda>M acc. M\<^sup>\<dagger> * M + acc) ?Ms (0\<^sub>m n n)
          = ?P1\<^sup>\<dagger> * ?P1 + (?Q\<^sup>\<dagger> * ?Q + 0\<^sub>m n n)"
        by simp
      also have "... = ?P1 * ?P1 + (?Q * ?Q + 0\<^sub>m n n)"
        using P1herm Qherm by simp
      also have "... = ?P1 + (?Q + 0\<^sub>m n n)"
        using P1idem Qidem by simp
      also have "... = ?P1 + ?Q"
        using P1car Qcar by simp
      also have "... = 1\<^sub>m n"
      proof (rule eq_matI)
        show "dim_row (?P1 + (1\<^sub>m n - ?P1)) = dim_row (1\<^sub>m n)"
          using P1car by auto
        show "dim_col (?P1 + (1\<^sub>m n - ?P1)) = dim_col (1\<^sub>m n)"
          using P1car by auto
      next
        fix i j
        assume i: "i < dim_row (1\<^sub>m n)" and j: "j < dim_col (1\<^sub>m n)"
        then have iln: "i < n" and jln: "j < n" by auto
        show "(?P1 + (1\<^sub>m n - ?P1)) $$ (i,j) = (1\<^sub>m n) $$ (i,j)"
          using iln jln P1car
          by (metis Qcar add.commute carrier_matD(1,2) 
              diff_add_cancel index_add_mat(1) index_minus_mat(1))
      qed
      finally show ?thesis.
    qed
    show ?thesis
      unfolding measurement_system_def
      using carrs fold_eq by blast
  qed

  have P1_on_\<psi>1: "?P1 *\<^sub>v \<psi>1 = \<psi>1"
    using outer_proj_self[OF q1] .
  have P1_on_\<psi>2: "?P1 *\<^sub>v \<psi>2 = 0\<^sub>v n"
    using outer_proj_orth_zero[OF q1 q2 orth] .

  have Q_on_\<psi>1: "?Q *\<^sub>v \<psi>1 = 0\<^sub>v n"
  proof -
    have "?Q *\<^sub>v \<psi>1 = (1\<^sub>m n) *\<^sub>v \<psi>1 - ?P1 *\<^sub>v \<psi>1"
      using P1car \<psi>1dim carrier_vec_dim_vec minus_mult_distrib_mat_vec one_carrier_mat by blast
    also have "... = \<psi>1 - ?P1 *\<^sub>v \<psi>1"
      using \<psi>1dim by fastforce
    also have "... = 0\<^sub>v n"
      using P1_on_\<psi>1 \<psi>1dim by fastforce
    finally show ?thesis.
  qed

  have Q_on_\<psi>2: "?Q *\<^sub>v \<psi>2 = \<psi>2"
  proof -
    have "?Q *\<^sub>v \<psi>2 = (1\<^sub>m n) *\<^sub>v \<psi>2 - ?P1 *\<^sub>v \<psi>2"
      using P1car \<psi>2dim carrier_vec_dim_vec minus_mult_distrib_mat_vec one_carrier_mat by blast
    also have "... = \<psi>2 - ?P1 *\<^sub>v \<psi>2"
      using \<psi>2dim by fastforce
    also have "... = \<psi>2"
      using P1_on_\<psi>2 \<psi>2dim by fastforce
    finally show ?thesis.
  qed

  have prob_P1_\<psi>1: "meas_prob ?P1 \<psi>1 = 1"
    using P1_on_\<psi>1 q1
    by (simp add: meas_prob_def quantum_state_def)
  have prob_Q_\<psi>1: "meas_prob ?Q \<psi>1 = 0"
    using Q_on_\<psi>1 \<psi>1dim
    by (simp add: cpx_vec_length_zero_iff meas_prob_def)
  have prob_P1_\<psi>2: "meas_prob ?P1 \<psi>2 = 0"
    using P1_on_\<psi>2 \<psi>2dim
    by (simp add: meas_prob_def, simp add: cpx_vec_length_zero_iff)
  have prob_Q_\<psi>2: "meas_prob ?Q \<psi>2 = 1"
    using Q_on_\<psi>2 q2
    by (simp add: meas_prob_def quantum_state_def)
  show ?thesis
    by (intro exI[of _ ?Ms], use meas_sys prob_P1_\<psi>1 prob_Q_\<psi>1 prob_P1_\<psi>2 prob_Q_\<psi>2 in auto)
qed
text \<open>The theorem on linearly independent states.  Linear independence of a list of vectors is
injectivity of the matrix with those columns; the formal statement produces the measurement
system $M_0,\dots,M_k$ in the order $M_1,\dots,M_k,M_0$ (outcome $i<k$ identifies $\psi_i$,
outcome $k$ is inconclusive).  The proof follows the notes with one change: instead of the
projections $E_i$ onto $\{\psi_j:j\neq i\}^\perp$ it uses the dual vectors
$\phi_i$ with $\braket{\phi_i}{\psi_j}=\delta_{ij}$ (columns of $V(V^*V)^{-1}$) and the
operators $M_i=\sqrt c\,\ketbra{e_0}{\phi_i}$, where $c>0$ makes $I-c\sum_i\ketbra{\phi_i}{\phi_i}$
positive; $M_0$ is its square root.\<close>

definition lin_indep_vecs :: "nat \<Rightarrow> complex Matrix.vec list \<Rightarrow> bool" where
  "lin_indep_vecs n vs \<equiv> (\<forall>v \<in> set vs. dim_vec v = n) \<and>
     (\<forall>x :: complex Matrix.vec. x \<in> carrier_vec (length vs) \<longrightarrow>
         mat_of_cols n vs *\<^sub>v x = 0\<^sub>v n \<longrightarrow> x = 0\<^sub>v (length vs))"

lemma outer_prod_carrier:
  fixes v w :: "complex Matrix.vec"
  assumes "dim_vec v = n" and "dim_vec w = m"
  shows "v \<oslash> w \<in> carrier_mat n m"
  using assms by (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def carrier_matI)

lemma outer_prod_dagger:
  fixes v w :: "complex Matrix.vec"
  shows "(v \<oslash> w)\<^sup>\<dagger> = w \<oslash> v"
proof -
  have "(v \<oslash> w)\<^sup>\<dagger> = ((bra_vec w)\<^sup>\<dagger>) * (( |v\<rangle> )\<^sup>\<dagger>)"
    by (rule dagger_of_prod) (simp add: ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def)
  also have "(bra_vec w)\<^sup>\<dagger> = |w\<rangle>"
  proof -
    have "bra_vec w = ( |w\<rangle> )\<^sup>\<dagger>" by (simp add: dagger_of_ket_is_bra)
    thus ?thesis by (simp add: dagger_of_dagger_is_id)
  qed
  also have "( |v\<rangle> )\<^sup>\<dagger> = bra_vec v" by (simp add: dagger_of_ket_is_bra)
  finally show ?thesis .
qed

lemma foldr_add_mat_carrier:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat n n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n"
  using assms by (induction xs) auto

lemma foldr_add_mat_index:
  fixes f :: "'a \<Rightarrow> complex Matrix.mat"
  assumes "\<forall>x \<in> set xs. f x \<in> carrier_mat n n" and "i < n" and "j < n"
  shows "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) $$ (i, j) = sum_list (map (\<lambda>x. f x $$ (i, j)) xs)"
  using assms
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have fx: "f x \<in> carrier_mat n n" and rest: "\<forall>y \<in> set xs. f y \<in> carrier_mat n n" using Cons.prems by auto
  have rc: "foldr (\<lambda>x acc. f x + acc) xs (0\<^sub>m n n) \<in> carrier_mat n n" by (rule foldr_add_mat_carrier[OF rest])
  show ?case using Cons.IH[OF rest] Cons.prems fx rc by simp
qed

lemma foldr_MdagM_shift:
  assumes Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n" and z: "z \<in> carrier_mat n n"
  shows "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms z
           = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) + z"
  using Ms_c
proof (induction Ms)
  case Nil thus ?case using z by auto
next
  case (Cons M Ms)
  have Mc: "M \<in> carrier_mat n n" and rest: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n" using Cons.prems by auto
  have MM: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n" by (rule mult_carrier_mat[OF dagger_carrier[OF Mc] Mc])
  have carr: "\<forall>M \<in> set Ms. (M\<^sup>\<dagger>) * M \<in> carrier_mat n n"
    using rest by (meson mult_carrier_mat dagger_carrier)
  have rc: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n) \<in> carrier_mat n n"
    using foldr_add_mat_carrier[OF carr] .
  show ?case using Cons.IH[OF rest] MM rc z by (simp add: assoc_add_mat)
qed

theorem lin_indep_states_unambiguous:
  fixes \<psi>s :: "complex Matrix.vec list"
  assumes qs: "\<forall>\<psi> \<in> set \<psi>s. quantum_state n \<psi>"
      and li: "lin_indep_vecs n \<psi>s"
      and k: "length \<psi>s = k" and kpos: "0 < k"
  shows "\<exists>Ms :: complex Matrix.mat list.
           measurement_system n Ms \<and> length Ms = k + 1 \<and>
           (\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> meas_prob (Ms ! i) (\<psi>s ! j) = 0) \<and>
           (\<forall>i<k. 0 < meas_prob (Ms ! i) (\<psi>s ! i))"
proof -
  have \<psi>d: "\<forall>\<psi> \<in> set \<psi>s. dim_vec \<psi> = n" using qs by (simp add: quantum_state_def)
  have npos: "0 < n"
  proof -
    have "\<psi>s ! 0 \<in> set \<psi>s" using k kpos by simp
    hence "\<parallel>\<psi>s ! 0\<parallel> = 1" "dim_vec (\<psi>s ! 0) = n" using qs by (auto simp: quantum_state_def)
    thus ?thesis by (cases n) (auto simp: cpx_vec_length_def)
  qed
  \<comment> \<open>The Gram matrix of the states is invertible.\<close>
  let ?V = "mat_of_cols n \<psi>s"
  have Vc: "?V \<in> carrier_mat n k" using mat_of_cols_carrier(1)[of n \<psi>s] k by simp
  let ?G = "?V\<^sup>\<dagger> * ?V"
  have Vd_c: "?V\<^sup>\<dagger> \<in> carrier_mat k n" using dagger_carrier[OF Vc] .
  have Gc: "?G \<in> carrier_mat k k" using Vc Vd_c by auto
  have Gh: "?G\<^sup>\<dagger> = ?G" by (simp add: dagger_of_prod dagger_of_dagger_is_id)
  have inj: "\<And>x :: complex Matrix.vec. x \<in> carrier_vec k \<Longrightarrow> ?V *\<^sub>v x = 0\<^sub>v n \<Longrightarrow> x = 0\<^sub>v k"
    using li k unfolding lin_indep_vecs_def by auto
  have dG: "det ?G \<noteq> 0"
  proof
    assume "det ?G = 0"
    then obtain x :: "complex Matrix.vec"
      where xc: "x \<in> carrier_vec k" and xnz: "x \<noteq> 0\<^sub>v k" and Gx: "?G *\<^sub>v x = 0\<^sub>v k"
      using det_0_iff_vec_prod_zero_field[OF Gc] by auto
    have xd: "dim_vec x = k" using xc by auto
    have Vx: "dim_vec (?V *\<^sub>v x) = n" using Vc xd by auto
    have "\<langle>?V *\<^sub>v x | ?V *\<^sub>v x\<rangle> = \<langle>(?V\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v x | ?V *\<^sub>v x\<rangle>"
      by (simp add: dagger_of_dagger_is_id)
    also have "\<dots> = \<langle>x | ?V\<^sup>\<dagger> *\<^sub>v (?V *\<^sub>v x)\<rangle>"
      using inner_prod_adjoint_swap[OF Vd_c xd Vx] by simp
    also have "\<dots> = \<langle>x | ?G *\<^sub>v x\<rangle>" using Vc Vd_c xc by (simp add: assoc_mult_mat_vec)
    also have "\<dots> = 0" unfolding inner_prod_def using Gx xd by simp
    finally have "?V *\<^sub>v x = 0\<^sub>v n" using Vx inner_prod_self_eq_zero_iff[of "?V *\<^sub>v x"] by simp
    with inj[OF xc] xnz show False by simp
  qed
  obtain B :: "complex Matrix.mat"
    where Bc: "B \<in> carrier_mat k k" and GB: "?G * B = 1\<^sub>m k" and BG: "B * ?G = 1\<^sub>m k"
    using det_non_zero_imp_unit[OF Gc dG, of "()"] by (auto simp: Units_def ring_mat_def)
  \<comment> \<open>The dual vectors: columns of \<open>V B\<close>.\<close>
  let ?P = "?V * B"
  have Pc: "?P \<in> carrier_mat n k" using Vc Bc by auto
  have Pd_c: "?P\<^sup>\<dagger> \<in> carrier_mat k n" using dagger_carrier[OF Pc] .
  let ?\<phi>s = "cols ?P"
  have \<phi>len: "length ?\<phi>s = k" using Pc Bc by simp
  have \<phi>d: "\<forall>\<phi> \<in> set ?\<phi>s. dim_vec \<phi> = n" using Pc by (auto simp: cols_def)
  have P_eq: "mat_of_cols n ?\<phi>s = ?P" using Pc mat_of_cols_cols[of ?P] by auto
  have Bd_G: "B\<^sup>\<dagger> * ?G = 1\<^sub>m k"
  proof -
    have "B\<^sup>\<dagger> * ?G = (B\<^sup>\<dagger>) * (?G\<^sup>\<dagger>)" using Gh by simp
    also have "\<dots> = (?G * B)\<^sup>\<dagger>" using dagger_of_prod[of ?G B] Gc Bc by auto
    also have "\<dots> = (1\<^sub>m k :: complex Matrix.mat)\<^sup>\<dagger>" using GB by simp
    also have "\<dots> = 1\<^sub>m k" by (rule eq_matI) (auto simp: dagger_def)
    finally show ?thesis .
  qed
  have dual: "\<And>i j. i < k \<Longrightarrow> j < k \<Longrightarrow> \<langle>?\<phi>s ! i | \<psi>s ! j\<rangle> = (if i = j then 1 else 0)"
  proof -
    fix i j assume i: "i < k" and j: "j < k"
    have \<psi>j: "\<psi>s ! j \<in> set \<psi>s" using j k by simp
    have \<psi>jd: "dim_vec (\<psi>s ! j) = n" using \<psi>d \<psi>j by simp
    have "\<langle>?\<phi>s ! i | \<psi>s ! j\<rangle> = (((mat_of_cols n ?\<phi>s)\<^sup>\<dagger>) *\<^sub>v (\<psi>s ! j)) $ i"
      using mat_of_cols_dagger_mult_vec_index[OF \<psi>jd \<phi>d, of i] \<phi>len i by simp
    also have "\<dots> = ((?P\<^sup>\<dagger>) *\<^sub>v Matrix.col ?V j) $ i"
      using P_eq col_mat_of_cols[of j \<psi>s n] j k \<psi>jd by auto
    also have "(?P\<^sup>\<dagger>) *\<^sub>v Matrix.col ?V j = Matrix.col ((?P\<^sup>\<dagger>) * ?V) j"
      using col_mult2[OF Pd_c Vc j] by simp
    also have "Matrix.col ((?P\<^sup>\<dagger>) * ?V) j $ i = ((?P\<^sup>\<dagger>) * ?V) $$ (i, j)"
    proof -
      have PV_c: "(?P\<^sup>\<dagger>) * ?V \<in> carrier_mat k k" using Pd_c Vc by auto
      thus ?thesis using i j carrier_matD[OF PV_c] by (simp add: Matrix.col_def)
    qed
    also have "(?P\<^sup>\<dagger>) * ?V = B\<^sup>\<dagger> * ?G"
    proof -
      have "?P\<^sup>\<dagger> = (B\<^sup>\<dagger>) * (?V\<^sup>\<dagger>)" using dagger_of_prod[of ?V B] Vc Bc by auto
      hence "(?P\<^sup>\<dagger>) * ?V = ((B\<^sup>\<dagger>) * (?V\<^sup>\<dagger>)) * ?V" by simp
      also have "\<dots> = (B\<^sup>\<dagger>) * ((?V\<^sup>\<dagger>) * ?V)"
        using assoc_mult_mat[OF dagger_carrier[OF Bc] Vd_c Vc] .
      finally show ?thesis .
    qed
    also have "\<dots> = 1\<^sub>m k" by (rule Bd_G)
    finally show "\<langle>?\<phi>s ! i | \<psi>s ! j\<rangle> = (if i = j then 1 else 0)" using i j by simp
  qed
  \<comment> \<open>Scale so that \<open>I - c T\<close> is positive, with \<open>T = \<Sum> |\<phi>\<^sub>i\<rangle>\<langle>\<phi>\<^sub>i|\<close>.\<close>
  let ?T = "outer_sum n ?\<phi>s"
  have Tc: "?T \<in> carrier_mat n n" by (intro carrier_matI) auto
  have Tpsd: "psd ?T" using outer_sum_psd[OF \<phi>len \<phi>d] .
  obtain U :: "complex Matrix.mat" and D :: "real list"
    where Uc: "U \<in> carrier_mat n n" and UU: "unitary U" and Dlen: "length D = n"
      and Dnn: "\<forall>i<n. 0 \<le> D ! i" and TUDU: "?T = U * diag_mat_of_real D * (U\<^sup>\<dagger>)"
    using psd_spectral_decomp_nonneg[OF Tc Tpsd] by blast
  define Dmax where "Dmax = sum_list (map abs D)"
  define c where "c = 1 / (1 + Dmax)"
  have Dmax0: "0 \<le> Dmax" unfolding Dmax_def by (rule sum_list_nonneg) auto
  have cpos: "0 < c" unfolding c_def using Dmax0 by simp
  have cD1: "\<And>i. i < n \<Longrightarrow> c * D ! i \<le> 1"
  proof -
    fix i assume i: "i < n"
    have "\<bar>D ! i\<bar> \<in> set (map abs D)" using i Dlen by auto
    hence "\<bar>D ! i\<bar> \<le> Dmax" unfolding Dmax_def by (intro member_le_sum_list) auto
    hence "D ! i \<le> Dmax" by linarith
    hence "c * D ! i \<le> c * Dmax" using cpos by (simp add: mult_left_mono)
    also have "\<dots> = Dmax / (1 + Dmax)" unfolding c_def by simp
    also have "\<dots> \<le> 1" using Dmax0 by (simp add: divide_le_eq)
    finally show "c * D ! i \<le> 1" .
  qed
  define D' where "D' = map (\<lambda>d. 1 - c * d) D"
  have D'len: "length D' = n" using Dlen by (simp add: D'_def)
  have D'nn: "\<And>i. i < n \<Longrightarrow> 0 \<le> D' ! i" using cD1 Dlen by (simp add: D'_def)
  have Dc: "diag_mat_of_real D \<in> carrier_mat n n" using diag_mat_of_real_carrier[of D] Dlen by metis
  have diagD': "diag_mat_of_real D' = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D"
  proof (rule eq_matI)
    show "dim_row (diag_mat_of_real D') = dim_row (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)"
      using D'len Dlen by simp
    show "dim_col (diag_mat_of_real D') = dim_col (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)"
      using D'len Dlen by simp
    fix i j assume "i < dim_row (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)"
                   "j < dim_col (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)"
    hence ij: "i < n" "j < n" using Dlen by auto
    show "diag_mat_of_real D' $$ (i, j) = (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) $$ (i, j)"
      using ij Dlen D'len by (cases "i = j") (auto simp: D'_def)
  qed
  have UUd: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using unitary_inv_r_dimrow[OF UU] Uc by auto
  have Ud_c: "U\<^sup>\<dagger> \<in> carrier_mat n n" using Uc by (simp add: dagger_def)
  have ImcT: "1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T = U * diag_mat_of_real D' * (U\<^sup>\<dagger>)"
  proof -
    have one_c: "(1\<^sub>m n :: complex Matrix.mat) \<in> carrier_mat n n" by simp
    have cDc: "complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D \<in> carrier_mat n n" using Dc by auto
    have U1c: "U * 1\<^sub>m n \<in> carrier_mat n n" using Uc by auto
    have UcDc: "U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) \<in> carrier_mat n n" using Uc cDc by auto
    have UDc: "U * diag_mat_of_real D \<in> carrier_mat n n" using Uc Dc by auto
    have "U * diag_mat_of_real D' * (U\<^sup>\<dagger>)
            = U * (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>)"
      by (simp only: diagD')
    also have "\<dots> = (U * 1\<^sub>m n - U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D)) * (U\<^sup>\<dagger>)"
      by (simp only: mult_minus_distrib_mat[OF Uc one_c cDc])
    also have "\<dots> = U * 1\<^sub>m n * (U\<^sup>\<dagger>) - U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>)"
      by (simp only: minus_mult_distrib_mat[OF U1c UcDc Ud_c])
    also have "U * 1\<^sub>m n * (U\<^sup>\<dagger>) = 1\<^sub>m n" using Uc UUd by simp
    also have "U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>) = complex_of_real c \<cdot>\<^sub>m ?T"
    proof -
      have "U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) = complex_of_real c \<cdot>\<^sub>m (U * diag_mat_of_real D)"
        by (rule mult_smult_distrib[OF Uc Dc])
      hence "U * (complex_of_real c \<cdot>\<^sub>m diag_mat_of_real D) * (U\<^sup>\<dagger>)
               = (complex_of_real c \<cdot>\<^sub>m (U * diag_mat_of_real D)) * (U\<^sup>\<dagger>)" by simp
      also have "\<dots> = complex_of_real c \<cdot>\<^sub>m (U * diag_mat_of_real D * (U\<^sup>\<dagger>))"
        by (rule mult_smult_assoc_mat[OF UDc Ud_c])
      finally show ?thesis using TUDU by simp
    qed
    finally show ?thesis by simp
  qed

  have ImcT_c: "1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T \<in> carrier_mat n n" using Tc by auto
  have ImcT_psd: "psd (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
    unfolding ImcT using psd_U_diag_Udag[OF Uc D'len] D'nn by blast
  let ?Q = "psd_sqrt (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
  have Qc: "?Q \<in> carrier_mat n n" and Qpsd: "psd ?Q" and QQ: "?Q * ?Q = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T"
    using psd_sqrt_props[OF ImcT_c ImcT_psd] by auto
  have Qh: "?Q\<^sup>\<dagger> = ?Q" using psd_hermitian[OF Qpsd] by (simp add: hermitian_def)
  \<comment> \<open>The measurement operators \<open>M\<^sub>i = \<surd>c |e\<^sub>0\<rangle>\<langle>\<phi>\<^sub>i|\<close> and \<open>M\<^sub>k = Q\<close>.\<close>
  let ?u = "unit_vec n 0"
  have ud: "dim_vec ?u = n" by simp
  have un: "\<parallel>?u\<parallel> = 1" using npos by simp
  have uu: "\<langle>?u | ?u\<rangle> = 1"
  proof -
    have "\<langle>?u | ?u\<rangle> = complex_of_real (\<parallel>?u\<parallel>\<^sup>2)" by (simp only: cpx_vec_length_inner_prod[symmetric])
    thus ?thesis using un by simp
  qed
  define Mi where "Mi = (\<lambda>\<phi> :: complex Matrix.vec. complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>))"
  define Ms where "Ms = map Mi ?\<phi>s @ [?Q]"
  have lenMs: "length Ms = k + 1" by (simp add: Ms_def \<phi>len carrier_matD[OF Bc])
  have Ms_nth: "\<And>i. i < k \<Longrightarrow> Ms ! i = Mi (?\<phi>s ! i)" by (simp add: Ms_def \<phi>len nth_append carrier_matD[OF Bc])
  have Mi_c: "\<And>\<phi>. dim_vec \<phi> = n \<Longrightarrow> Mi \<phi> \<in> carrier_mat n n"
    using outer_prod_carrier[OF ud] by (auto simp: Mi_def)
  have sqc: "sqrt c * sqrt c = c" using cpos by simp
  have MiMi: "\<And>\<phi>. dim_vec \<phi> = n \<Longrightarrow> (Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> = complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)"
  proof -
    fix \<phi> :: "complex Matrix.vec" assume \<phi>: "dim_vec \<phi> = n"
    have c1: "?u \<oslash> \<phi> \<in> carrier_mat n n" using outer_prod_carrier[OF ud \<phi>] .
    have c2: "\<phi> \<oslash> ?u \<in> carrier_mat n n" using outer_prod_carrier[OF \<phi> ud] .
    have dag: "(Mi \<phi>)\<^sup>\<dagger> = complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> ?u)"
      unfolding Mi_def by (simp add: dagger_of_smult outer_prod_dagger)
    have prod: "(\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>) = \<phi> \<oslash> \<phi>"
    proof (rule eq_matI)
      show "dim_row ((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>)) = dim_row (\<phi> \<oslash> \<phi>)"
        using c1 c2 outer_prod_carrier[OF \<phi> \<phi>] by auto
      show "dim_col ((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>)) = dim_col (\<phi> \<oslash> \<phi>)"
        using c1 c2 outer_prod_carrier[OF \<phi> \<phi>] by auto
      fix i j assume "i < dim_row (\<phi> \<oslash> \<phi>)" "j < dim_col (\<phi> \<oslash> \<phi>)"
      hence ij: "i < n" "j < n" using outer_prod_carrier[OF \<phi> \<phi>] by auto
      have dA: "dim_row (\<phi> \<oslash> ?u) = n" "dim_col (\<phi> \<oslash> ?u) = n" using c2 by auto
      have dB: "dim_row (?u \<oslash> \<phi>) = n" "dim_col (?u \<oslash> \<phi>) = n" using c1 by auto
      have "((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>)) $$ (i, j) = Matrix.row (\<phi> \<oslash> ?u) i \<bullet> Matrix.col (?u \<oslash> \<phi>) j"
        using ij by (simp only: index_mult_mat(1) dA dB)
      also have "\<dots> = (\<Sum>l = 0..<n. Matrix.row (\<phi> \<oslash> ?u) i $ l * Matrix.col (?u \<oslash> \<phi>) j $ l)"
        by (simp only: scalar_prod_def dim_col dB)
      also have "\<dots> = (\<Sum>l = 0..<n. (\<phi> $ i * cnj (?u $ l)) * (?u $ l * cnj (\<phi> $ j)))"
      proof (rule sum.cong[OF refl])
        fix l assume "l \<in> {0..<n}"
        hence l: "l < n" by simp
        have r: "Matrix.row (\<phi> \<oslash> ?u) i $ l = (\<phi> \<oslash> ?u) $$ (i, l)"
          using ij l by (simp only: index_row(1) dA)
        have cc: "Matrix.col (?u \<oslash> \<phi>) j $ l = (?u \<oslash> \<phi>) $$ (l, j)"
          using ij l by (simp only: index_col dB)
        have o1: "(\<phi> \<oslash> ?u) $$ (i, l) = \<phi> $ i * cnj (?u $ l)"
          by (rule outer_prod_index) (simp only: \<phi> ij, simp only: ud l)
        have o2: "(?u \<oslash> \<phi>) $$ (l, j) = ?u $ l * cnj (\<phi> $ j)"
          by (rule outer_prod_index) (simp only: ud l, simp only: \<phi> ij)
        show "Matrix.row (\<phi> \<oslash> ?u) i $ l * Matrix.col (?u \<oslash> \<phi>) j $ l
                = (\<phi> $ i * cnj (?u $ l)) * (?u $ l * cnj (\<phi> $ j))"
          by (simp only: r cc o1 o2)
      qed
      also have "\<dots> = \<phi> $ i * cnj (\<phi> $ j) * (\<Sum>l = 0..<n. cnj (?u $ l) * ?u $ l)"
        by (simp add: sum_distrib_left algebra_simps)
      also have "(\<Sum>l = 0..<n. cnj (?u $ l) * ?u $ l) = (\<Sum>l = 0..<n. if l = 0 then 1 else 0)"
        by (rule sum.cong[OF refl]) simp
      also have "\<dots> = 1" using npos by simp
      also have "\<phi> $ i * cnj (\<phi> $ j) * 1 = (\<phi> \<oslash> \<phi>) $$ (i, j)"
        using outer_prod_index[of i \<phi> j \<phi>] ij \<phi> by simp
      finally show "((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>)) $$ (i, j) = (\<phi> \<oslash> \<phi>) $$ (i, j)" .
    qed
    have sc: "complex_of_real (sqrt c) * complex_of_real (sqrt c) = complex_of_real c"
      using sqc cpos by (simp flip: of_real_mult)
    have smm: "\<And>a b (A :: complex Matrix.mat). a \<cdot>\<^sub>m (b \<cdot>\<^sub>m A) = (a * b) \<cdot>\<^sub>m A"
      by (rule eq_matI) (simp_all add: mult.assoc)
    have "(Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> = (complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> ?u)) * Mi \<phi>"
      by (simp only: dag)
    also have "\<dots> = (complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> ?u)) * (complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>))"
      by (simp only: Mi_def)
    also have "\<dots> = complex_of_real (sqrt c) \<cdot>\<^sub>m ((\<phi> \<oslash> ?u) * (complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>)))"
      by (rule mult_smult_assoc_mat[OF c2 smult_carrier_mat[OF c1]])
    also have "(\<phi> \<oslash> ?u) * (complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>))
                 = complex_of_real (sqrt c) \<cdot>\<^sub>m ((\<phi> \<oslash> ?u) * (?u \<oslash> \<phi>))"
      by (rule mult_smult_distrib[OF c2 c1])
    also have "\<dots> = complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)" by (simp only: prod)
    also have "complex_of_real (sqrt c) \<cdot>\<^sub>m (complex_of_real (sqrt c) \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>))
                 = (complex_of_real (sqrt c) * complex_of_real (sqrt c)) \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)"
      by (rule smm)
    also have "\<dots> = complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)" by (simp only: sc)
    finally show "(Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> = complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)" .
  qed
  have Mi_prob: "\<And>\<phi> \<psi>. dim_vec \<phi> = n \<Longrightarrow> dim_vec \<psi> = n \<Longrightarrow>
                   meas_prob (Mi \<phi>) \<psi> = c * (cmod \<langle>\<phi> | \<psi>\<rangle>)\<^sup>2"
  proof -
    fix \<phi> \<psi> :: "complex Matrix.vec" assume \<phi>: "dim_vec \<phi> = n" and \<psi>: "dim_vec \<psi> = n"
    have c1: "?u \<oslash> \<phi> \<in> carrier_mat n n" using outer_prod_carrier[OF ud \<phi>] .
    have "Mi \<phi> *\<^sub>v \<psi> = complex_of_real (sqrt c) \<cdot>\<^sub>v ((?u \<oslash> \<phi>) *\<^sub>v \<psi>)"
      unfolding Mi_def using smult_mat_mult_vec[OF c1] \<psi> by auto
    also have "(?u \<oslash> \<phi>) *\<^sub>v \<psi> = \<langle>\<phi> | \<psi>\<rangle> \<cdot>\<^sub>v ?u"
      using outer_prod_mult_vec[of \<psi> \<phi> ?u] \<phi> \<psi> by simp
    finally have "\<parallel>Mi \<phi> *\<^sub>v \<psi>\<parallel> = sqrt c * (cmod \<langle>\<phi> | \<psi>\<rangle> * 1)"
      using cpos un by (simp add: cpx_vec_length_smult)
    thus "meas_prob (Mi \<phi>) \<psi> = c * (cmod \<langle>\<phi> | \<psi>\<rangle>)\<^sup>2"
      unfolding meas_prob_def using sqc by (simp add: power_mult_distrib power2_eq_square)
  qed
  \<comment> \<open>The operators form a measurement system.\<close>
  have Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n"
    using Mi_c \<phi>d Qc by (auto simp: Ms_def)
  have fold_map: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) = complex_of_real c \<cdot>\<^sub>m ?T"
  proof (rule eq_matI)
    have carr: "\<forall>\<phi> \<in> set ?\<phi>s. (Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> \<in> carrier_mat n n"
      using Mi_c \<phi>d by (meson mult_carrier_mat dagger_carrier)
    have fold_c: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) \<in> carrier_mat n n"
      using foldr_add_mat_carrier[OF carr] by (simp add: foldr_map o_def)
    show "dim_row (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n)) = dim_row (complex_of_real c \<cdot>\<^sub>m ?T)"
      using fold_c Tc by auto
    show "dim_col (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n)) = dim_col (complex_of_real c \<cdot>\<^sub>m ?T)"
      using fold_c Tc by auto
    fix i j assume "i < dim_row (complex_of_real c \<cdot>\<^sub>m ?T)" "j < dim_col (complex_of_real c \<cdot>\<^sub>m ?T)"
    hence ij: "i < n" "j < n" using Tc by auto
    have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) $$ (i, j)
            = foldr (\<lambda>\<phi> acc. (Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> + acc) ?\<phi>s (0\<^sub>m n n) $$ (i, j)"
      by (simp add: foldr_map o_def)
    also have "\<dots> = sum_list (map (\<lambda>\<phi>. ((Mi \<phi>)\<^sup>\<dagger> * Mi \<phi>) $$ (i, j)) ?\<phi>s)"
      using foldr_add_mat_index[OF carr ij] .
    also have "\<dots> = sum_list (map (\<lambda>\<phi>. complex_of_real c * (\<phi> $ i * cnj (\<phi> $ j))) ?\<phi>s)"
    proof (intro arg_cong[where f = sum_list] map_cong refl)
      fix \<phi> assume "\<phi> \<in> set ?\<phi>s"
      hence d: "dim_vec \<phi> = n" using \<phi>d by blast
      have cc: "\<phi> \<oslash> \<phi> \<in> carrier_mat n n" using outer_prod_carrier[OF d d] .
      have "((Mi \<phi>)\<^sup>\<dagger> * Mi \<phi>) $$ (i, j) = (complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)) $$ (i, j)"
        by (simp only: MiMi[OF d])
      also have "\<dots> = complex_of_real c * (\<phi> \<oslash> \<phi>) $$ (i, j)"
        by (rule index_smult_mat(1)) (simp_all only: carrier_matD[OF cc] ij)
      also have "(\<phi> \<oslash> \<phi>) $$ (i, j) = \<phi> $ i * cnj (\<phi> $ j)"
        using outer_prod_index[of i \<phi> j \<phi>] ij d by simp
      finally show "((Mi \<phi>)\<^sup>\<dagger> * Mi \<phi>) $$ (i, j) = complex_of_real c * (\<phi> $ i * cnj (\<phi> $ j))" .
    qed
    also have "\<dots> = complex_of_real c * sum_list (map (\<lambda>\<phi>. \<phi> $ i * cnj (\<phi> $ j)) ?\<phi>s)"
      by (simp add: sum_list_const_mult)
    also have "\<dots> = complex_of_real c * ?T $$ (i, j)"
      using outer_sum_entry_sum_list[OF \<phi>d ij] by simp
    finally show "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) $$ (i, j)
                    = (complex_of_real c \<cdot>\<^sub>m ?T) $$ (i, j)"
      using ij Tc by simp
  qed
  have ms: "measurement_system n Ms"
  proof -
    have QdQ: "(?Q\<^sup>\<dagger>) * ?Q + 0\<^sub>m n n = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T"
      using Qh QQ ImcT_c by simp
    have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)
            = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s)
                (foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) [?Q] (0\<^sub>m n n))"
      unfolding Ms_def by (rule foldr_append)
    also have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) [?Q] (0\<^sub>m n n) = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T"
      by (simp only: foldr.simps o_apply id_apply QdQ)
    also have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)
                 = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n)
                     + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
      using Mi_c \<phi>d ImcT_c by (intro foldr_MdagM_shift) auto
    also have "\<dots> = complex_of_real c \<cdot>\<^sub>m ?T + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
      using fold_map by simp
    also have "\<dots> = 1\<^sub>m n"
    proof (rule eq_matI)
      show "dim_row (complex_of_real c \<cdot>\<^sub>m ?T + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)) = dim_row (1\<^sub>m n :: complex Matrix.mat)" using Tc by auto
      show "dim_col (complex_of_real c \<cdot>\<^sub>m ?T + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)) = dim_col (1\<^sub>m n :: complex Matrix.mat)" using Tc by auto
      fix i j assume "i < dim_row (1\<^sub>m n :: complex Matrix.mat)" "j < dim_col (1\<^sub>m n :: complex Matrix.mat)"
      thus "(complex_of_real c \<cdot>\<^sub>m ?T + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)) $$ (i, j) = (1\<^sub>m n :: complex Matrix.mat) $$ (i, j)"
        using Tc by (simp add: algebra_simps)
    qed
    finally show ?thesis unfolding measurement_system_def using Ms_c by blast
  qed
  \<comment> \<open>Outcome \<open>i < k\<close> occurs only for \<open>\<psi>\<^sub>i\<close>, and then with positive probability.\<close>
  have off: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> meas_prob (Ms ! i) (\<psi>s ! j) = 0"
  proof (intro allI impI)
    fix i j assume i: "i < k" and j: "j < k" and ij: "i \<noteq> j"
    have \<phi>i: "dim_vec (?\<phi>s ! i) = n" using \<phi>d \<phi>len i by (simp add: carrier_matD[OF Bc] carrier_matD[OF Pc])
    have \<psi>j: "dim_vec (\<psi>s ! j) = n" using \<psi>d k j by simp
    show "meas_prob (Ms ! i) (\<psi>s ! j) = 0"
      using Ms_nth[OF i] Mi_prob[OF \<phi>i \<psi>j] dual[OF i j] ij by simp
  qed
  have diag: "\<forall>i<k. 0 < meas_prob (Ms ! i) (\<psi>s ! i)"
  proof (intro allI impI)
    fix i assume i: "i < k"
    have \<phi>i: "dim_vec (?\<phi>s ! i) = n" using \<phi>d \<phi>len i by (simp add: carrier_matD[OF Bc] carrier_matD[OF Pc])
    have \<psi>i: "dim_vec (\<psi>s ! i) = n" using \<psi>d k i by simp
    show "0 < meas_prob (Ms ! i) (\<psi>s ! i)"
      using Ms_nth[OF i] Mi_prob[OF \<phi>i \<psi>i] dual[OF i i] cpos by simp
  qed
  show ?thesis using ms lenMs off diag by blast
qed

subsection \<open>Projective measurements, expected values and self-adjoint operators\<close>

text \<open>If a measurement $\{M_m\}$ has real outcomes $\lambda_m$, the expected value of the
outcome in state $\psi$ is
$E=\sum_m p_m(\psi)\lambda_m=\bigl\langle\psi\big|\bigl(\textstyle\sum_m\lambda_mM_m^*M_m\bigr)\psi\bigr\rangle
=\braket{\psi}{H\psi}$ with $H=\sum_m\lambda_mM_m^*M_m$ self-adjoint: expected values of
observables are quadratic forms of Hermitian matrices (\<open>expected_value_eq_quad_form\<close> below).\<close>

text \<open>Formally: a measurement whose operator is the rank-one projection $\ketbra\gamma\gamma$
has $p(\psi)=|\braket\gamma\psi|^2$ (the proposition of Day 12); an \emph{observable} with
outcomes $\lambda_m$ attached to the measurement operators $M_m$ is
$H=\sum_m\lambda_mM_m^*M_m$, which is Hermitian, and the expected outcome
$\sum_m\lambda_mp_m(\psi)$ equals $\braket{\psi}{H\psi}$.\<close>

lemma rank_one_meas_prob:
  fixes \<gamma> \<psi> :: "complex Matrix.vec"
  assumes g: "quantum_state n \<gamma>" and \<psi>: "dim_vec \<psi> = n"
  shows "meas_prob (\<gamma> \<oslash> \<gamma>) \<psi> = (cmod \<langle>\<gamma> | \<psi>\<rangle>)\<^sup>2"
proof -
  have gd: "dim_vec \<gamma> = n" and gn: "\<parallel>\<gamma>\<parallel> = 1" using g by (auto simp: quantum_state_def)
  have "(\<gamma> \<oslash> \<gamma>) *\<^sub>v \<psi> = \<langle>\<gamma> | \<psi>\<rangle> \<cdot>\<^sub>v \<gamma>"
    using outer_prod_mult_vec[of \<psi> \<gamma> \<gamma>] gd \<psi> by simp
  hence "\<parallel>(\<gamma> \<oslash> \<gamma>) *\<^sub>v \<psi>\<parallel> = cmod \<langle>\<gamma> | \<psi>\<rangle> * \<parallel>\<gamma>\<parallel>"
    by (simp add: cpx_vec_length_smult)
  thus ?thesis unfolding meas_prob_def using gn by (simp add: power_mult_distrib)
qed

definition observable :: "nat \<Rightarrow> (real \<times> complex Matrix.mat) list \<Rightarrow> complex Matrix.mat" where
  "observable n lMs \<equiv>
     foldr (\<lambda>(l, M) acc. complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M) + acc) lMs (0\<^sub>m n n)"

definition expected_value :: "(real \<times> complex Matrix.mat) list \<Rightarrow> complex Matrix.vec \<Rightarrow> real" where
  "expected_value lMs \<psi> \<equiv> (\<Sum>(l, M) \<leftarrow> lMs. l * meas_prob M \<psi>)"

lemma observable_Nil [simp]: "observable n [] = 0\<^sub>m n n"
  by (simp add: observable_def)

lemma observable_Cons [simp]:
  "observable n ((l, M) # lMs) = complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M) + observable n lMs"
  by (simp add: observable_def)

lemma observable_carrier:
  assumes "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n"
  shows "observable n lMs \<in> carrier_mat n n"
  using assms by (induction lMs) auto

lemma observable_hermitian:
  assumes "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n"
  shows "hermitian (observable n lMs)"
  using assms
proof (induction lMs)
  case Nil
  show ?case unfolding hermitian_def by (rule eq_matI) (auto simp: dagger_def)
next
  case (Cons lM lMs)
  obtain l M where lM: "lM = (l, M)" by (cases lM)
  have Mc: "M \<in> carrier_mat n n" using Cons.prems lM by auto
  have rest: "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n" using Cons.prems by auto
  have h1: "hermitian (complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M))"
    using psd_hermitian[OF psd_MdagM[OF Mc]] Mc
    by (intro hermitian_real_scale) auto
  have h2: "hermitian (observable n lMs)" using Cons.IH[OF rest] .
  have c1: "complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M) \<in> carrier_mat n n" using Mc by auto
  show ?case unfolding lM observable_Cons
    by (rule hermitian_plus[OF h1 h2 c1 observable_carrier[OF rest]])
qed

lemma expected_value_eq_quad_form:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>: "dim_vec \<psi> = n"
      and lMs: "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n"
  shows "expected_value lMs \<psi> = Re \<langle>\<psi> | observable n lMs *\<^sub>v \<psi>\<rangle>"
  using lMs
proof (induction lMs)
  case Nil
  have "observable n [] *\<^sub>v \<psi> = 0\<^sub>v n" using \<psi> by auto
  moreover have "\<langle>\<psi> | 0\<^sub>v n\<rangle> = 0"
  proof -
    have "(0\<^sub>v n :: complex Matrix.vec) = (0 :: complex) \<cdot>\<^sub>v \<psi>" using \<psi> by auto
    thus ?thesis by (simp only: inner_prod_right_smult') simp
  qed
  ultimately show ?case by (simp add: expected_value_def)
next
  case (Cons lM lMs)
  obtain l M where lM: "lM = (l, M)" by (cases lM)
  have Mc: "M \<in> carrier_mat n n" using Cons.prems lM by auto
  have rest: "\<forall>(l, M) \<in> set lMs. M \<in> carrier_mat n n" using Cons.prems by auto
  have \<psi>c: "\<psi> \<in> carrier_vec n" using \<psi> by auto
  have MM: "(M\<^sup>\<dagger>) * M \<in> carrier_mat n n" using Mc by auto
  have obs: "observable n lMs \<in> carrier_mat n n" by (rule observable_carrier[OF rest])
  have c1: "complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M) \<in> carrier_mat n n" using MM by auto
  have "observable n (lM # lMs) *\<^sub>v \<psi>
          = (complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M)) *\<^sub>v \<psi> + observable n lMs *\<^sub>v \<psi>"
    unfolding lM observable_Cons by (rule add_mult_distrib_mat_vec[OF c1 obs \<psi>c])
  also have "(complex_of_real l \<cdot>\<^sub>m ((M\<^sup>\<dagger>) * M)) *\<^sub>v \<psi>
               = complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>)"
    using smult_mat_mult_vec[OF MM \<psi>c] .
  finally have obs_eq: "observable n (lM # lMs) *\<^sub>v \<psi>
      = complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>) + observable n lMs *\<^sub>v \<psi>" .
  have d1: "dim_vec (complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>)) = dim_vec (observable n lMs *\<^sub>v \<psi>)"
    using Mc MM obs \<psi> by simp
  have "\<langle>\<psi> | observable n (lM # lMs) *\<^sub>v \<psi>\<rangle>
      = \<langle>\<psi> | complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>)\<rangle> + \<langle>\<psi> | observable n lMs *\<^sub>v \<psi>\<rangle>"
    unfolding obs_eq by (rule inner_prod_right_add'[OF d1])
  also have "\<langle>\<psi> | complex_of_real l \<cdot>\<^sub>v (((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>)\<rangle>
      = complex_of_real l * \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle>"
    by (rule inner_prod_right_smult')
  finally have split: "\<langle>\<psi> | observable n (lM # lMs) *\<^sub>v \<psi>\<rangle>
      = complex_of_real l * \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle> + \<langle>\<psi> | observable n lMs *\<^sub>v \<psi>\<rangle>" .
  have "expected_value (lM # lMs) \<psi> = l * meas_prob M \<psi> + expected_value lMs \<psi>"
    unfolding lM expected_value_def by simp
  also have "\<dots> = l * Re \<langle>\<psi> | ((M\<^sup>\<dagger>) * M) *\<^sub>v \<psi>\<rangle> + Re \<langle>\<psi> | observable n lMs *\<^sub>v \<psi>\<rangle>"
    using meas_prob_quad_form[OF Mc \<psi>] Cons.IH[OF rest] by simp
  also have "\<dots> = Re \<langle>\<psi> | observable n (lM # lMs) *\<^sub>v \<psi>\<rangle>"
    using split by simp
  finally show ?case .
qed

end
