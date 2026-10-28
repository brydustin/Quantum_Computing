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
(\<open>nonorthogonal_outcome_prob\<close> below).

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
  have "\<langle>\<psi>|\<psi>\<rangle> = 1"
    using q unfolding quantum_state_def by (simp flip: cpx_vec_length_inner_prod)
  thus ?thesis by (simp add: outer_prod_mult_vec)
qed

lemma outer_proj_orth_zero:
  assumes q1: "quantum_state n \<psi>1"
      and q2: "quantum_state n \<psi>2"
      and orth: "\<langle>\<psi>1 | \<psi>2\<rangle> = 0"
  shows "outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2 = 0\<^sub>v n"
proof -
  have "outer_prod \<psi>1 \<psi>1 *\<^sub>v \<psi>2 = \<langle>\<psi>1 | \<psi>2\<rangle> \<cdot>\<^sub>v \<psi>1"
    using q1 q2 by (intro outer_prod_mult_vec) (simp add: quantum_state_def)
  thus ?thesis using q1 unfolding orth by (intro eq_vecI) (auto simp: quantum_state_def)
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
  have d: "dim_vec \<psi>1 = n" "dim_vec \<psi>2 = n" and n1: "\<parallel>\<psi>1\<parallel> = 1" "\<parallel>\<psi>2\<parallel> = 1"
    using q1 q2 by (auto simp: quantum_state_def)
  have c: "\<psi>1 \<in> carrier_vec n" "\<psi>2 \<in> carrier_vec n"
    by (rule carrier_vecI[OF d(1)], rule carrier_vecI[OF d(2)])
  define P where "P = \<psi>1 \<oslash> \<psi>1"
  define Q where "Q = 1\<^sub>m n - P"
  have P: "P \<in> carrier_mat n n" unfolding P_def by (rule outer_prod_carrier[OF d(1) d(1)])
  have Q: "Q \<in> carrier_mat n n" unfolding Q_def by (rule minus_carrier_mat[OF P])
  have Ph: "P\<^sup>\<dagger> = P" and Pi: "P * P = P"
    unfolding P_def by (rule outer_prod_dagger, rule outer_prod_idempotent[OF n1(1)])
  have PP: "P\<^sup>\<dagger> * P = P" and QQ: "Q\<^sup>\<dagger> * Q = Q"
    unfolding Q_def by (simp_all add: Ph Pi complement_dagger[OF P] complement_projection[OF P Pi])
  have PQ: "P + Q = 1\<^sub>m n" unfolding Q_def using P by (intro eq_matI) auto
  have ms: "measurement_system n [P, Q]"
    unfolding measurement_system_def using P Q by (simp add: PP QQ PQ)
  have P1: "P *\<^sub>v \<psi>1 = \<psi>1" and P2: "P *\<^sub>v \<psi>2 = 0\<^sub>v n"
    unfolding P_def by (rule outer_proj_self[OF q1], rule outer_proj_orth_zero[OF q1 q2 orth])
  have Q1: "Q *\<^sub>v \<psi>1 = 0\<^sub>v n" and Q2: "Q *\<^sub>v \<psi>2 = \<psi>2"
    unfolding Q_def minus_mult_distrib_mat_vec[OF one_carrier_mat P c(1)]
              minus_mult_distrib_mat_vec[OF one_carrier_mat P c(2)] P1 P2
    using c d by (auto intro!: eq_vecI)
  have probs: "meas_prob P \<psi>1 = 1" "meas_prob Q \<psi>1 = 0" "meas_prob P \<psi>2 = 0" "meas_prob Q \<psi>2 = 1"
    unfolding meas_prob_def P1 P2 Q1 Q2 n1 by (simp_all add: cpx_vec_length_def)
  show ?thesis
    by (rule exI[of _ "[P, Q]"], rule conjI[OF ms], rule exI[of _ P], rule exI[of _ Q]) (simp add: probs)
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
    have "\<langle>?V *\<^sub>v x | ?V *\<^sub>v x\<rangle> = \<langle>x | ?G *\<^sub>v x\<rangle>"
      using inner_prod_adjoint_swap[OF Vd_c xd Vx] Vc Vd_c xc by (simp add: dagger_of_dagger_is_id assoc_mult_mat_vec)
    also have "\<dots> = 0" unfolding inner_prod_def using Gx xd by simp
    finally have "?V *\<^sub>v x = 0\<^sub>v n" using Vx inner_prod_self_eq_zero_iff[of "?V *\<^sub>v x"] by simp
    with inj[OF xc] xnz show False by simp
  qed
  obtain B :: "complex Matrix.mat"
    where Bc: "B \<in> carrier_mat k k" and GB: "?G * B = 1\<^sub>m k"
    using det_non_zero_imp_unit[OF Gc dG, of "()"] by (auto simp: Units_def ring_mat_def)
  \<comment> \<open>The dual vectors: columns of \<open>V B\<close>.\<close>
  let ?P = "?V * B"
  have Pc: "?P \<in> carrier_mat n k" using Vc Bc by auto
  let ?\<phi>s = "cols ?P"
  have \<phi>len: "length ?\<phi>s = k" using Pc Bc by simp
  have \<phi>d: "\<forall>\<phi> \<in> set ?\<phi>s. dim_vec \<phi> = n" using Pc by (auto simp: cols_def)
  have P_eq: "mat_of_cols n ?\<phi>s = ?P" using Pc mat_of_cols_cols[of ?P] by auto
  have Bd_G: "B\<^sup>\<dagger> * ?G = 1\<^sub>m k"
  proof -
    have "B\<^sup>\<dagger> * ?G = (?G * B)\<^sup>\<dagger>" using dagger_of_prod[of ?G B] Gc Bc Gh by auto
    thus ?thesis unfolding GB using Bc by (intro eq_matI) (auto simp: dagger_def)
  qed
  have dual: "\<langle>?\<phi>s ! i | \<psi>s ! j\<rangle> = (if i = j then 1 else 0)" if i: "i < k" and j: "j < k" for i j
  proof -
    have \<psi>j: "dim_vec (\<psi>s ! j) = n" using \<psi>d j k by simp
    have PV_c: "(?P\<^sup>\<dagger>) * ?V \<in> carrier_mat k k" using dagger_carrier[OF Pc] Vc by auto
    have "\<langle>?\<phi>s ! i | \<psi>s ! j\<rangle> = (((mat_of_cols n ?\<phi>s)\<^sup>\<dagger>) *\<^sub>v (\<psi>s ! j)) $ i"
      using mat_of_cols_dagger_mult_vec_index[OF \<psi>j \<phi>d, of i] \<phi>len i by simp
    also have "\<dots> = ((?P\<^sup>\<dagger>) *\<^sub>v Matrix.col ?V j) $ i"
      using P_eq col_mat_of_cols[of j \<psi>s n] j k \<psi>j by auto
    also have "(?P\<^sup>\<dagger>) *\<^sub>v Matrix.col ?V j = Matrix.col ((?P\<^sup>\<dagger>) * ?V) j"
      using col_mult2[OF dagger_carrier[OF Pc] Vc j] by simp
    also have "Matrix.col ((?P\<^sup>\<dagger>) * ?V) j $ i = ((?P\<^sup>\<dagger>) * ?V) $$ (i, j)"
      using i j carrier_matD[OF PV_c] by (simp add: Matrix.col_def)
    also have "(?P\<^sup>\<dagger>) * ?V = B\<^sup>\<dagger> * ?G"
      using dagger_of_prod[of ?V B] Vc Bc assoc_mult_mat[OF dagger_carrier[OF Bc] Vd_c Vc] by auto
    finally show ?thesis unfolding Bd_G using i j by simp
  qed
  \<comment> \<open>Scale \<open>T = \<Sum>|\<phi>\<^sub>i\<rangle>\<langle>\<phi>\<^sub>i|\<close> so that \<open>I - c T\<close> is positive; \<open>Q\<close> is its square root.\<close>
  let ?T = "outer_sum n ?\<phi>s"
  have Tc: "?T \<in> carrier_mat n n" by (intro carrier_matI) auto
  obtain c where cpos: "0 < c" and ImcT_psd: "psd (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
    using psd_scale_below_one[OF Tc outer_sum_psd[OF \<phi>len \<phi>d]] by blast
  have ImcT_c: "1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T \<in> carrier_mat n n" using Tc by auto
  let ?Q = "psd_sqrt (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
  have Qc: "?Q \<in> carrier_mat n n" and Qpsd: "psd ?Q" and QQ: "?Q * ?Q = 1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T"
    using psd_sqrt_props[OF ImcT_c ImcT_psd] by auto
  have Qh: "?Q\<^sup>\<dagger> = ?Q" using psd_hermitian[OF Qpsd] by (simp add: hermitian_def)
  \<comment> \<open>The measurement operators \<open>M\<^sub>i = \<surd>c |e\<^sub>0\<rangle>\<langle>\<phi>\<^sub>i|\<close> and \<open>M\<^sub>k = Q\<close>.\<close>
  let ?u = "unit_vec n 0"
  have ud: "dim_vec ?u = n" and un: "\<parallel>?u\<parallel> = 1" using npos by simp_all
  have uu: "\<langle>?u | ?u\<rangle> = 1" using un by (simp flip: cpx_vec_length_inner_prod)
  define Mi where "Mi = (\<lambda>\<phi> :: complex Matrix.vec. complex_of_real (sqrt c) \<cdot>\<^sub>m (?u \<oslash> \<phi>))"
  define Ms where "Ms = map Mi ?\<phi>s @ [?Q]"
  have lenMs: "length Ms = k + 1" by (simp add: Ms_def carrier_matD[OF Bc])
  have Ms_nth: "Ms ! i = Mi (?\<phi>s ! i)" if "i < k" for i by (simp add: Ms_def carrier_matD[OF Bc] nth_append that)
  have Mi_c: "Mi \<phi> \<in> carrier_mat n n" if "dim_vec \<phi> = n" for \<phi>
    using outer_prod_carrier[OF ud that] by (auto simp: Mi_def)
  have sc: "complex_of_real (sqrt c) * complex_of_real (sqrt c) = complex_of_real c"
    using cpos by (simp flip: of_real_mult)
  have MiMi: "(Mi \<phi>)\<^sup>\<dagger> * Mi \<phi> = complex_of_real c \<cdot>\<^sub>m (\<phi> \<oslash> \<phi>)" if that: "dim_vec \<phi> = n" for \<phi>
    unfolding Mi_def smult_dagger_mult[OF outer_prod_carrier[OF ud that]] outer_prod_dagger
              outer_prod_mult[OF refl] uu
    by (intro eq_matI) (auto simp: sc)
  have Mi_prob: "meas_prob (Mi \<phi>) \<psi> = c * (cmod \<langle>\<phi> | \<psi>\<rangle>)\<^sup>2"
    if \<phi>: "dim_vec \<phi> = n" and \<psi>: "dim_vec \<psi> = n" for \<phi> \<psi>
  proof -
    have "Mi \<phi> *\<^sub>v \<psi> = complex_of_real (sqrt c) \<cdot>\<^sub>v (\<langle>\<phi> | \<psi>\<rangle> \<cdot>\<^sub>v ?u)"
      unfolding Mi_def
      using smult_mat_mult_vec[OF outer_prod_carrier[OF ud \<phi>] carrier_vecI[OF \<psi>]] outer_prod_mult_vec[of \<psi> \<phi> ?u] \<phi> \<psi>
      by simp
    hence "\<parallel>Mi \<phi> *\<^sub>v \<psi>\<parallel> = sqrt c * cmod \<langle>\<phi> | \<psi>\<rangle>" using cpos un by (simp add: cpx_vec_length_smult)
    thus ?thesis unfolding meas_prob_def using cpos by (simp add: power_mult_distrib)
  qed
  \<comment> \<open>The operators form a measurement system.\<close>
  have Ms_c: "\<forall>M \<in> set Ms. M \<in> carrier_mat n n" using Mi_c \<phi>d Qc by (auto simp: Ms_def)
  have oc: "\<forall>\<phi> \<in> set ?\<phi>s. \<phi> \<oslash> \<phi> \<in> carrier_mat n n" using \<phi>d by (auto intro: outer_prod_carrier)
  have fold_map: "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) = complex_of_real c \<cdot>\<^sub>m ?T"
    by (simp only: foldr_map o_def foldr_add_mat_cong[OF MiMi[OF \<phi>d[rule_format]]]
                   foldr_add_mat_smult[OF oc] outer_sum_as_foldr[OF \<phi>d, symmetric])
  have ms: "measurement_system n Ms"
  proof -
    have "foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) Ms (0\<^sub>m n n)
            = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
      unfolding Ms_def foldr_append by (simp add: Qh QQ ImcT_c)
    also have "\<dots> = foldr (\<lambda>M acc. (M\<^sup>\<dagger>) * M + acc) (map Mi ?\<phi>s) (0\<^sub>m n n) + (1\<^sub>m n - complex_of_real c \<cdot>\<^sub>m ?T)"
      using Mi_c \<phi>d by (intro foldr_MdagM_shift[OF _ ImcT_c]) auto
    also have "\<dots> = 1\<^sub>m n" unfolding fold_map using Tc by (intro eq_matI) auto
    finally show ?thesis unfolding measurement_system_def using Ms_c by blast
  qed
  \<comment> \<open>Outcome \<open>i < k\<close> occurs only for \<open>\<psi>\<^sub>i\<close>, and then with positive probability.\<close>
  have \<phi>i: "dim_vec (?\<phi>s ! i) = n" if "i < k" for i
    using \<phi>d[rule_format, OF nth_mem] that by (simp add: carrier_matD[OF Bc])
  have \<psi>i: "dim_vec (\<psi>s ! i) = n" if "i < k" for i using \<psi>d[rule_format, OF nth_mem] k that by simp
  have off: "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> meas_prob (Ms ! i) (\<psi>s ! j) = 0"
    by (simp add: Ms_nth Mi_prob[OF \<phi>i \<psi>i] dual)
  have diag: "\<forall>i<k. 0 < meas_prob (Ms ! i) (\<psi>s ! i)"
    by (simp add: Ms_nth Mi_prob[OF \<phi>i \<psi>i] dual cpos)
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

text \<open>For the rank-one operator $M=\ketbra\gamma\gamma$ of a unit vector $\gamma$,
$M\psi=\braket\gamma\psi\,\gamma$ and so $p=|\braket\gamma\psi|^2$.\<close>

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

text \<open>An observable assigns a real value $\lambda_i$ to each outcome.  Its operator
$A=\sum_i\lambda_iM_i^*M_i$ is Hermitian, and the expected value is its quadratic form:
\[ \sum_i\lambda_i\,p_i=\sum_i\lambda_i\braket{\psi}{M_i^*M_i\psi}=\braket{\psi}{A\psi}. \]\<close>

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

subsection \<open>Non-orthogonal states cannot be distinguished\<close>

lemma meas_sum_norm:
  assumes ms: "measurement_system n Ms" and v: "dim_vec v = n"
  shows "(\<Sum>l<length Ms. \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2) = \<parallel>v\<parallel>\<^sup>2"
proof (cases "\<parallel>v\<parallel> = 0")
  case True
  hence v0: "v = 0\<^sub>v n" using v cpx_vec_length_zero_iff by fastforce
  have Mc: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have z: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l *\<^sub>v v = 0\<^sub>v n"
  proof -
    fix l assume "l < length Ms"
    hence M: "Ms ! l \<in> carrier_mat n n" by (rule Mc)
    show "Ms ! l *\<^sub>v v = 0\<^sub>v n" by (rule eq_vecI) (use M in \<open>auto simp: v0 scalar_prod_def\<close>)
  qed
  show ?thesis using True by (simp add: z cpx_vec_length_def)
next
  case False
  let ?c = "complex_of_real (1 / \<parallel>v\<parallel>)"
  have st: "quantum_state n (?c \<cdot>\<^sub>v v)"
  proof -
    have "\<parallel>v\<parallel> \<ge> 0" unfolding cpx_vec_length_def by (simp add: sum_nonneg)
    thus ?thesis unfolding quantum_state_def using v False by (simp add: cpx_vec_length_smult norm_divide)
  qed
  have Mc: "\<And>l. l < length Ms \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
  have tm: "\<And>l. l < length Ms \<Longrightarrow> meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v) = \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2 / \<parallel>v\<parallel>\<^sup>2"
  proof -
    fix l assume l: "l < length Ms"
    have vn: "\<parallel>v\<parallel> \<ge> 0" unfolding cpx_vec_length_def by (simp add: sum_nonneg)
    show "meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v) = \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2 / \<parallel>v\<parallel>\<^sup>2"
      unfolding meas_prob_def mult_mat_vec[OF Mc[OF l] vc]
      by (simp add: cpx_vec_length_smult norm_divide abs_of_nonneg[OF vn] power_mult_distrib power_divide)
  qed
  have "1 = (\<Sum>M \<leftarrow> Ms. meas_prob M (?c \<cdot>\<^sub>v v))" by (rule measurement_probs_sum_one[OF ms st, symmetric])
  also have "\<dots> = (\<Sum>l<length Ms. meas_prob (Ms ! l) (?c \<cdot>\<^sub>v v))"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = (\<Sum>l<length Ms. \<parallel>Ms ! l *\<^sub>v v\<parallel>\<^sup>2) / \<parallel>v\<parallel>\<^sup>2"
    unfolding sum_divide_distrib by (rule sum.cong[OF refl], rule tm, simp)
  finally show ?thesis using False by (simp add: field_simps)
qed

lemma inner_minus_smult:
  assumes d1: "dim_vec u = n" and d2: "dim_vec w = n"
  shows "\<langle>w - a \<cdot>\<^sub>v u | w - a \<cdot>\<^sub>v u\<rangle> = \<langle>w|w\<rangle> - a * \<langle>w|u\<rangle> - cnj a * \<langle>u|w\<rangle> + a * cnj a * \<langle>u|u\<rangle>"
  unfolding inner_prod_def using d1 d2
  by (simp add: sum.distrib sum_subtractf sum_distrib_left algebra_simps)

lemma norm_sq_minus_component:
  assumes d1: "dim_vec u = n" and d2: "dim_vec w = n" and u: "\<parallel>u\<parallel> = 1"
  shows "\<parallel>w - \<langle>u|w\<rangle> \<cdot>\<^sub>v u\<parallel>\<^sup>2 = \<parallel>w\<parallel>\<^sup>2 - (cmod \<langle>u|w\<rangle>)\<^sup>2"
proof -
  let ?a = "\<langle>u|w\<rangle>"
  have uu: "\<langle>u|u\<rangle> = 1" using u unfolding cpx_vec_length_one_iff .
  have wu: "\<langle>w|u\<rangle> = cnj ?a" by (rule inner_prod_cnj) (use d1 d2 in simp)
  have e: "\<langle>w - ?a \<cdot>\<^sub>v u | w - ?a \<cdot>\<^sub>v u\<rangle> = \<langle>w|w\<rangle> - ?a * \<langle>w|u\<rangle> - cnj ?a * ?a + ?a * cnj ?a * \<langle>u|u\<rangle>"
    by (rule inner_minus_smult[OF d1 d2])
  have "complex_of_real (\<parallel>w - ?a \<cdot>\<^sub>v u\<parallel>\<^sup>2) = complex_of_real (\<parallel>w\<parallel>\<^sup>2) - ?a * cnj ?a"
    unfolding cpx_vec_length_inner_prod e wu uu by simp
  also have "?a * cnj ?a = complex_of_real ((cmod ?a)\<^sup>2)" using complex_norm_square[of ?a] by simp
  finally show ?thesis unfolding of_real_diff[symmetric] of_real_eq_iff .
qed

text \<open>D8-2: if outcome $i$ certainly occurs on $\psi_1$, it occurs on $\psi_2$ with probability
at least $|\langle\psi_1|\psi_2\rangle|^2$.\<close>

theorem nonorthogonal_outcome_prob:
  assumes ms: "measurement_system n Ms" and q1: "quantum_state n \<psi>1" and q2: "quantum_state n \<psi>2"
      and i: "i < length Ms" and p1: "meas_prob (Ms ! i) \<psi>1 = 1"
  shows "(cmod \<langle>\<psi>1|\<psi>2\<rangle>)\<^sup>2 \<le> meas_prob (Ms ! i) \<psi>2"
proof -
  let ?N = "length Ms" and ?a = "\<langle>\<psi>1|\<psi>2\<rangle>"
  let ?g = "\<psi>2 - ?a \<cdot>\<^sub>v \<psi>1"
  have d1: "dim_vec \<psi>1 = n" and n1: "\<parallel>\<psi>1\<parallel> = 1" and d2: "dim_vec \<psi>2 = n" and n2: "\<parallel>\<psi>2\<parallel> = 1"
    using q1 q2 unfolding quantum_state_def by auto
  have Mc: "\<And>l. l < ?N \<Longrightarrow> Ms ! l \<in> carrier_mat n n"
    using ms unfolding measurement_system_def by auto
  have rem: "\<And>f :: nat \<Rightarrow> real. (\<Sum>l<?N. f l) = f i + (\<Sum>l\<in>{..<?N} - {i}. f l)"
    by (rule sum.remove) (use i in simp_all)
  have S1: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2) = 1" using meas_sum_norm[OF ms d1] n1 by simp
  have rest0: "(\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2) = 0"
    using S1 rem[of "\<lambda>l. \<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2"] p1 unfolding meas_prob_def by simp
  have z: "\<And>l. l < ?N \<Longrightarrow> l \<noteq> i \<Longrightarrow> Ms ! l *\<^sub>v \<psi>1 = 0\<^sub>v n"
  proof -
    fix l assume l: "l < ?N" "l \<noteq> i"
    have "\<forall>x\<in>{..<?N} - {i}. \<parallel>Ms ! x *\<^sub>v \<psi>1\<parallel>\<^sup>2 = 0"
      using rest0 by (subst (asm) sum_nonneg_eq_0_iff) auto
    hence "\<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel>\<^sup>2 = 0" using l by auto
    hence "\<parallel>Ms ! l *\<^sub>v \<psi>1\<parallel> = 0" by simp
    thus "Ms ! l *\<^sub>v \<psi>1 = 0\<^sub>v n" using cpx_vec_length_zero_iff Mc[OF l(1)] by fastforce
  qed
  have gd: "dim_vec ?g = n" using d1 d2 by simp
  have Mg: "\<And>l. l < ?N \<Longrightarrow> l \<noteq> i \<Longrightarrow> Ms ! l *\<^sub>v \<psi>2 = Ms ! l *\<^sub>v ?g"
  proof -
    fix l assume l: "l < ?N" "l \<noteq> i"
    have c1: "\<psi>1 \<in> carrier_vec n" by (rule carrier_vecI[OF d1])
    have c2: "\<psi>2 \<in> carrier_vec n" by (rule carrier_vecI[OF d2])
    have "Ms ! l *\<^sub>v ?g = Ms ! l *\<^sub>v \<psi>2 - ?a \<cdot>\<^sub>v (Ms ! l *\<^sub>v \<psi>1)"
      using mult_minus_distrib_mat_vec[OF Mc[OF l(1)] c2 smult_carrier_vec[THEN iffD2, OF c1]] mult_mat_vec[OF Mc[OF l(1)] c1] by simp
    thus "Ms ! l *\<^sub>v \<psi>2 = Ms ! l *\<^sub>v ?g" using z[OF l] Mc[OF l(1)] by auto
  qed
  have S2: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2) = 1" using meas_sum_norm[OF ms d2] n2 by simp
  have Sg: "(\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2) = 1 - (cmod ?a)\<^sup>2"
    using meas_sum_norm[OF ms gd] norm_sq_minus_component[OF d1 d2 n1] n2 by simp
  have "(\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2) = (\<Sum>l\<in>{..<?N} - {i}. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2)"
    by (rule sum.cong) (simp_all add: Mg)
  also have "\<dots> \<le> (\<Sum>l<?N. \<parallel>Ms ! l *\<^sub>v ?g\<parallel>\<^sup>2)" by (rule sum_mono2) auto
  finally show ?thesis using S2 Sg rem[of "\<lambda>l. \<parallel>Ms ! l *\<^sub>v \<psi>2\<parallel>\<^sup>2"] unfolding meas_prob_def by linarith
qed

corollary nonorthogonal_not_distinguishable:
  assumes ms: "measurement_system n Ms" and q1: "quantum_state n \<psi>1" and q2: "quantum_state n \<psi>2"
      and no: "\<langle>\<psi>1|\<psi>2\<rangle> \<noteq> 0" and i: "i < length Ms" and p1: "meas_prob (Ms ! i) \<psi>1 = 1"
  shows "meas_prob (Ms ! i) \<psi>2 > 0"
  by (rule less_le_trans[OF _ nonorthogonal_outcome_prob[OF ms q1 q2 i p1]]) (simp add: no)

end
