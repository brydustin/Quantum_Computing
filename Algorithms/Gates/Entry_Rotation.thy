theory Entry_Rotation
  imports Simulation_Comparator HHL_Algorithm.HHL_Suzuki
begin

section \<open>The entry rotation from phases\<close>

text \<open>With $\theta = d|a|$ and $\varphi = \arg a$ the entry block is
$P(\varphi)\,H\,Z(\theta)\,H\,P(-\varphi)$ with $P(\varphi) = \mathrm{diag}(e^{i\varphi},1)$ and
$Z(\theta) = \mathrm{diag}(e^{i\theta},e^{-i\theta})$: diagonal phases and two Hadamards.\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{quantikz}[row sep=0.3cm, column sep=0.35cm]
\lstick{ancilla} & \gate{P(-\varphi)} & \gate{H} & \gate{Z(\theta)} & \gate{H} & \gate{P(\varphi)} & \qw
\end{quantikz}
\end{center}
\<close>

definition zp :: "real \<Rightarrow> complex Matrix.mat" where "zp \<theta> = dmat 2 (\<lambda>b. if b = 0 then \<theta> else - \<theta>)"
definition pp :: "real \<Rightarrow> complex Matrix.mat" where "pp \<phi> = dmat 2 (\<lambda>b. if b = 0 then \<phi> else 0)"

definition rblock :: "real \<Rightarrow> real \<Rightarrow> complex Matrix.mat" where
  "rblock \<theta> \<phi> = pp \<phi> * (Hadamard * zp \<theta> * Hadamard) * pp (- \<phi>)"

lemma hzh: "Hadamard * zp \<theta> * Hadamard =
  Matrix.mat 2 2 (\<lambda>(i, j). if i = j then complex_of_real (cos \<theta>) else \<i> * complex_of_real (sin \<theta>))"
proof -
  have s: "complex_of_real (1 / sqrt 2) * complex_of_real (1 / sqrt 2) = 1 / 2" by (simp flip: of_real_mult)
  show ?thesis
    by (rule eq_matI) (auto simp: Hadamard_def H_without_scalar_prod zp_def dmat_def mat_diag_def scalar_prod_def
        atLeast0LessThan sumof2 less_Suc_eq numeral_2_eq_2 s cis.ctr complex_eq_iff algebra_simps)
qed

lemma rblock_explicit: "rblock \<theta> \<phi> = Matrix.mat 2 2 (\<lambda>(i, j). if i = j then complex_of_real (cos \<theta>)
    else if i = 0 then \<i> * complex_of_real (sin \<theta>) * cis \<phi> else \<i> * complex_of_real (sin \<theta>) * cis (- \<phi>))"
  unfolding rblock_def hzh
  by (rule eq_matI) (auto simp: pp_def dmat_def mat_diag_def scalar_prod_def atLeast0LessThan sumof2
      less_Suc_eq numeral_2_eq_2 cis_mult algebra_simps)

lemma rblock_entry: "rblock (d * cmod a) (Arg a) = Matrix.mat 2 2 (\<lambda>(i, j). if i = j then complex_of_real (cos (d * cmod a))
    else if i = 0 then \<i> * complex_of_real (sin (d * cmod a)) * (a / complex_of_real (cmod a))
    else \<i> * complex_of_real (sin (d * cmod a)) * cnj (a / complex_of_real (cmod a)))"
proof (cases "a = 0")
  case True
  show ?thesis unfolding True rblock_explicit by (rule eq_matI) simp_all
next
  case False
  have u: "a / complex_of_real (cmod a) = cis (Arg a)"
    using cis_Arg[OF False] by (simp add: sgn_div_norm scaleR_conv_of_real divide_inverse mult.commute)
  show ?thesis unfolding rblock_explicit u cis_cnj ..
qed

text \<open>The entry block is the rotation with the angle $d|a|$ and the phase $\arg a$.\<close>

lemma ent_block_rblock:
  "ent_block d A x y = rblock (d * cmod (if x = y then 0 else A $$ (x, y))) (Arg (if x = y then 0 else A $$ (x, y)))"
  unfolding ent_block_def Let_def rblock_entry ..

subsection \<open>Closeness\<close>

lemma dmat_close:
  assumes c: "\<And>x. x < N \<Longrightarrow> cmod (cis (f x) - cis (g x)) \<le> \<epsilon>" and e: "0 \<le> \<epsilon>"
  shows "dmat N f \<approx>\<^bsub>\<epsilon>\<^esub> dmat N g"
proof (rule op_closeI[OF dmat_carrier])
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = N"
  have d: "dmat N f *\<^sub>v v - dmat N g *\<^sub>v v = Matrix.vec N (\<lambda>x. (cis (f x) - cis (g x)) * v $ x)"
    using v by (intro eq_vecI) (simp_all add: dmat_mult_vec algebra_simps)
  have "(\<Sum>x<N. (cmod ((cis (f x) - cis (g x)) * v $ x))\<^sup>2) \<le> (\<Sum>x<N. \<epsilon>\<^sup>2 * (cmod (v $ x))\<^sup>2)"
  proof (rule sum_mono)
    fix x assume "x \<in> {..<N}"
    hence "cmod (cis (f x) - cis (g x)) \<le> \<epsilon>" using c by simp
    hence "(cmod (cis (f x) - cis (g x)))\<^sup>2 \<le> \<epsilon>\<^sup>2" by (rule power_mono) simp
    thus "(cmod ((cis (f x) - cis (g x)) * v $ x))\<^sup>2 \<le> \<epsilon>\<^sup>2 * (cmod (v $ x))\<^sup>2"
      by (simp add: norm_mult power_mult_distrib mult_right_mono)
  qed
  hence "sqrt (\<Sum>x<N. (cmod ((cis (f x) - cis (g x)) * v $ x))\<^sup>2) \<le> sqrt (\<epsilon>\<^sup>2 * (\<Sum>x<N. (cmod (v $ x))\<^sup>2))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = \<epsilon> * sqrt (\<Sum>x<N. (cmod (v $ x))\<^sup>2)" using e by (simp add: real_sqrt_mult)
  finally show "\<parallel>dmat N f *\<^sub>v v - dmat N g *\<^sub>v v\<parallel> \<le> \<epsilon> * \<parallel>v\<parallel>"
    unfolding d using v by (simp add: cpx_vec_length_def)
qed

lemma op_close_mult_left:
  assumes U: "U \<in> carrier_mat n n" "Quantum.unitary U" and A: "A \<in> carrier_mat n k" and B: "B \<in> carrier_mat n k"
    and c: "A \<approx>\<^bsub>\<epsilon>\<^esub> B"
  shows "U * A \<approx>\<^bsub>\<epsilon>\<^esub> U * B"
proof (rule op_closeI[OF mult_carrier_mat[OF U(1) A]])
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = k"
  have vc: "v \<in> carrier_vec k" by (rule carrier_vecI[OF v])
  have e1: "U * A *\<^sub>v v = U *\<^sub>v (A *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF U(1) A vc])
  have e2: "U * B *\<^sub>v v = U *\<^sub>v (B *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF U(1) B vc])
  have e3: "U *\<^sub>v (A *\<^sub>v v - B *\<^sub>v v) = U *\<^sub>v (A *\<^sub>v v) - U *\<^sub>v (B *\<^sub>v v)"
    by (rule mult_minus_distrib_mat_vec[OF U(1)]) (use A B vc in \<open>auto intro: mult_mat_vec_carrier\<close>)
  have "U * A *\<^sub>v v - U * B *\<^sub>v v = U *\<^sub>v (A *\<^sub>v v - B *\<^sub>v v)" unfolding e1 e2 e3 ..
  also have "\<parallel>\<dots>\<parallel> = \<parallel>A *\<^sub>v v - B *\<^sub>v v\<parallel>" by (rule unitary_vnorm[OF U]) (use A B in simp)
  also have "\<dots> \<le> \<epsilon> * \<parallel>v\<parallel>" by (rule op_closeD[OF c A v])
  finally show "\<parallel>U * A *\<^sub>v v - U * B *\<^sub>v v\<parallel> \<le> \<epsilon> * \<parallel>v\<parallel>" .
qed

lemma op_close_mult_right:
  assumes U: "U \<in> carrier_mat k k" "Quantum.unitary U" and A: "A \<in> carrier_mat n k" and B: "B \<in> carrier_mat n k"
    and c: "A \<approx>\<^bsub>\<epsilon>\<^esub> B"
  shows "A * U \<approx>\<^bsub>\<epsilon>\<^esub> B * U"
proof (rule op_closeI[OF mult_carrier_mat[OF A U(1)]])
  fix v :: "complex Matrix.vec" assume v: "dim_vec v = k"
  have vc: "v \<in> carrier_vec k" by (rule carrier_vecI[OF v])
  have "A * U *\<^sub>v v - B * U *\<^sub>v v = A *\<^sub>v (U *\<^sub>v v) - B *\<^sub>v (U *\<^sub>v v)"
    using assoc_mult_mat_vec[OF A U(1) vc] assoc_mult_mat_vec[OF B U(1) vc] by simp
  also have "\<parallel>\<dots>\<parallel> \<le> \<epsilon> * \<parallel>U *\<^sub>v v\<parallel>" by (rule op_closeD[OF c A]) (use U(1) in simp)
  also have "\<parallel>U *\<^sub>v v\<parallel> = \<parallel>v\<parallel>" by (rule unitary_vnorm[OF U v])
  finally show "\<parallel>A * U *\<^sub>v v - B * U *\<^sub>v v\<parallel> \<le> \<epsilon> * \<parallel>v\<parallel>" .
qed


lemma hadamard_facts: "Hadamard \<in> carrier_mat 2 2" "Quantum.unitary Hadamard"
  using H_is_gate unfolding Hadamard_def gate_def by (simp_all add: H_def)

lemma cis_neg_dist: "cmod (cis (- a) - cis (- b)) = cmod (cis a - cis b)"
proof -
  have "cis (- a) - cis (- b) = cnj (cis a - cis b)" by (simp add: cis_cnj)
  thus ?thesis by (simp only: complex_mod_cnj)
qed

lemma zp_close: "cmod (cis \<theta> - cis \<theta>') \<le> e \<Longrightarrow> zp \<theta> \<approx>\<^bsub>e\<^esub> zp \<theta>'"
  unfolding zp_def by (rule dmat_close) (auto simp: cis_neg_dist intro: order_trans[OF norm_ge_zero])

lemma pp_close: "cmod (cis \<phi> - cis \<phi>') \<le> e \<Longrightarrow> pp \<phi> \<approx>\<^bsub>e\<^esub> pp \<phi>'"
  and ppn_close: "cmod (cis \<phi> - cis \<phi>') \<le> e \<Longrightarrow> pp (- \<phi>) \<approx>\<^bsub>e\<^esub> pp (- \<phi>')"
  unfolding pp_def by (rule dmat_close; auto simp: cis_neg_dist intro: order_trans[OF norm_ge_zero])+

text \<open>A rotation is moved by at most its angle error plus twice its phase error.\<close>

lemma rblock_close:
  assumes t: "cmod (cis \<theta> - cis \<theta>') \<le> et" and f: "cmod (cis \<phi> - cis \<phi>') \<le> ef"
  shows "rblock \<theta> \<phi> \<approx>\<^bsub>ef + ef + et\<^esub> rblock \<theta>' \<phi>'"
proof -
  note Hd = hadamard_facts
  have pc: "pp s \<in> carrier_mat 2 2" "Quantum.unitary (pp s)" for s by (simp_all add: pp_def dmat_unitary)
  have zc: "zp s \<in> carrier_mat 2 2" "Quantum.unitary (zp s)" for s by (simp_all add: zp_def dmat_unitary)
  have Mc: "Hadamard * zp s * Hadamard \<in> carrier_mat 2 2" "Quantum.unitary (Hadamard * zp s * Hadamard)" for s
  proof -
    have c: "Hadamard * zp s \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF Hd(1) zc(1)])
    show "Hadamard * zp s * Hadamard \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF c Hd(1)])
    have "Quantum.unitary (Hadamard * zp s)" by (rule unitary_mult[OF Hd(2) zc(2) Hd(1) zc(1)])
    thus "Quantum.unitary (Hadamard * zp s * Hadamard)" by (rule unitary_mult[OF _ Hd(2) c Hd(1)])
  qed
  have PMc: "pp s * (Hadamard * zp u * Hadamard) \<in> carrier_mat 2 2" "Quantum.unitary (pp s * (Hadamard * zp u * Hadamard))" for s u
  proof -
    show "pp s * (Hadamard * zp u * Hadamard) \<in> carrier_mat 2 2" by (rule mult_carrier_mat[OF pc(1) Mc(1)])
    show "Quantum.unitary (pp s * (Hadamard * zp u * Hadamard))" by (rule unitary_mult[OF pc(2) Mc(2) pc(1) Mc(1)])
  qed
  have T: "pp s * (Hadamard * zp u * Hadamard) * pp t \<in> carrier_mat 2 2" for s u t by (rule mult_carrier_mat[OF PMc(1) pc(1)])
  have M: "Hadamard * zp \<theta> * Hadamard \<approx>\<^bsub>et\<^esub> Hadamard * zp \<theta>' * Hadamard"
  proof -
    have "Hadamard * zp \<theta> \<approx>\<^bsub>et\<^esub> Hadamard * zp \<theta>'" by (rule op_close_mult_left[OF Hd zc(1) zc(1) zp_close[OF t]])
    thus ?thesis by (rule op_close_mult_right[OF Hd mult_carrier_mat[OF Hd(1) zc(1)] mult_carrier_mat[OF Hd(1) zc(1)]])
  qed
  let ?M = "\<lambda>s. Hadamard * zp s * Hadamard"
  have c1: "pp \<phi> * ?M \<theta> * pp (- \<phi>) \<approx>\<^bsub>ef\<^esub> pp \<phi>' * ?M \<theta> * pp (- \<phi>)"
  proof -
    have "pp \<phi> * ?M \<theta> \<approx>\<^bsub>ef\<^esub> pp \<phi>' * ?M \<theta>" by (rule op_close_mult_right[OF Mc pc(1) pc(1) pp_close[OF f]])
    thus ?thesis by (rule op_close_mult_right[OF pc PMc(1) PMc(1)])
  qed
  have c2: "pp \<phi>' * ?M \<theta> * pp (- \<phi>) \<approx>\<^bsub>ef\<^esub> pp \<phi>' * ?M \<theta> * pp (- \<phi>')"
    by (rule op_close_mult_left[OF PMc pc(1) pc(1) ppn_close[OF f]])
  have c3: "pp \<phi>' * ?M \<theta> * pp (- \<phi>') \<approx>\<^bsub>et\<^esub> pp \<phi>' * ?M \<theta>' * pp (- \<phi>')"
  proof -
    have "pp \<phi>' * ?M \<theta> \<approx>\<^bsub>et\<^esub> pp \<phi>' * ?M \<theta>'" by (rule op_close_mult_left[OF pc Mc(1) Mc(1) M])
    thus ?thesis by (rule op_close_mult_right[OF pc PMc(1) PMc(1)])
  qed
  have "pp \<phi> * ?M \<theta> * pp (- \<phi>) \<approx>\<^bsub>ef + ef\<^esub> pp \<phi>' * ?M \<theta> * pp (- \<phi>')"
    by (rule op_close_trans[OF c1 c2 T T T])
  hence "pp \<phi> * ?M \<theta> * pp (- \<phi>) \<approx>\<^bsub>ef + ef + et\<^esub> pp \<phi>' * ?M \<theta>' * pp (- \<phi>')"
    by (rule op_close_trans[OF _ c3 T T T])
  thus ?thesis unfolding rblock_def .
qed

lemma ctrl_blocks_op_close:
  assumes B: "\<And>k. k < N \<Longrightarrow> B k \<in> carrier_mat m m" and B': "\<And>k. k < N \<Longrightarrow> B' k \<in> carrier_mat m m"
    and c: "\<And>k. k < N \<Longrightarrow> B k \<approx>\<^bsub>\<epsilon>\<^esub> B' k"
  shows "ctrl_blocks N m B \<approx>\<^bsub>\<epsilon>\<^esub> ctrl_blocks N m B'"
proof (rule op_closeI[OF ctrl_blocks_carrier])
  fix x :: "complex Matrix.vec" assume x: "dim_vec x = N * m"
  have cl: "\<parallel>B k *\<^sub>v v - B' k *\<^sub>v v\<parallel> \<le> \<epsilon> * \<parallel>v\<parallel>" if "k < N" "dim_vec v = m" for k v
    by (rule op_closeD[OF c[OF that(1)] B[OF that(1)] that(2)])
  show "\<parallel>ctrl_blocks N m B *\<^sub>v x - ctrl_blocks N m B' *\<^sub>v x\<parallel> \<le> \<epsilon> * \<parallel>x\<parallel>"
    using B B' cl x by (rule ctrl_blocks_close)
qed

end
