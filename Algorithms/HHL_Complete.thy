theory HHL_Complete
  imports HHL_Simulation
begin

section \<open>Readout, amplitude amplification and the complete algorithm\<close>

text \<open>The answer is read by post-selecting the ancilla on $\ket1$; the post-selected state is
$\psi\otimes A^{-1}b/\norm{A^{-1}b}\otimes\ket1$ up to $2\delta/(C\norm{A^{-1}b})$ when the output is
within $\delta$ of the exact one.  Amplitude amplification raises the success probability
$p$ to at least $1-p$ with $O(1/\sqrt p)=O(\kappa)$ rounds, each using the circuit and its
inverse once.  Theorem \<open>hhl_complete\<close> puts state preparation, the window register, the
simulation oracle, amplification and readout together and counts the oracle calls.\<close>

subsection \<open>Reading out the answer\<close>

subsection \<open>Normalisation is stable\<close>

lemma normalize_stable:
  assumes d: "dim_vec a = dim_vec b" and a: "\<parallel>a\<parallel> \<noteq> 0" and b: "\<parallel>b\<parallel> \<noteq> 0"
  shows "\<parallel>complex_of_real (1 / \<parallel>a\<parallel>) \<cdot>\<^sub>v a - complex_of_real (1 / \<parallel>b\<parallel>) \<cdot>\<^sub>v b\<parallel> \<le> 2 * \<parallel>a - b\<parallel> / \<parallel>b\<parallel>"
proof -
  have a0: "0 < \<parallel>a\<parallel>" and b0: "0 < \<parallel>b\<parallel>" using a b vnorm_ge0 by (simp_all add: order_le_neq_trans)
  let ?u = "complex_of_real (1 / \<parallel>b\<parallel>) \<cdot>\<^sub>v (a - b)" and ?w = "complex_of_real (1 / \<parallel>a\<parallel> - 1 / \<parallel>b\<parallel>) \<cdot>\<^sub>v a"
  have split: "complex_of_real (1 / \<parallel>a\<parallel>) \<cdot>\<^sub>v a - complex_of_real (1 / \<parallel>b\<parallel>) \<cdot>\<^sub>v b = ?u + ?w"
    using d by (intro eq_vecI) (simp_all add: algebra_simps)
  have u: "\<parallel>?u\<parallel> = \<parallel>a - b\<parallel> / \<parallel>b\<parallel>" unfolding cpx_vec_length_smult norm_of_real using b0 by simp
  have "\<parallel>?w\<parallel> = \<bar>1 / \<parallel>a\<parallel> - 1 / \<parallel>b\<parallel>\<bar> * \<parallel>a\<parallel>" unfolding cpx_vec_length_smult norm_of_real ..
  also have "\<dots> = \<bar>\<parallel>b\<parallel> - \<parallel>a\<parallel>\<bar> / \<parallel>b\<parallel>"
  proof -
    have e: "1 / \<parallel>a\<parallel> - 1 / \<parallel>b\<parallel> = (\<parallel>b\<parallel> - \<parallel>a\<parallel>) / (\<parallel>a\<parallel> * \<parallel>b\<parallel>)" using a0 b0 by (simp add: diff_divide_distrib)
    have ab: "\<bar>\<parallel>a\<parallel> * \<parallel>b\<parallel>\<bar> = \<parallel>a\<parallel> * \<parallel>b\<parallel>" using a0 b0 by simp
    have "\<bar>\<parallel>b\<parallel> - \<parallel>a\<parallel>\<bar> / (\<parallel>a\<parallel> * \<parallel>b\<parallel>) * \<parallel>a\<parallel> = \<bar>\<parallel>b\<parallel> - \<parallel>a\<parallel>\<bar> / \<parallel>b\<parallel>"
      using a0 by (simp add: field_simps)
    thus ?thesis unfolding e abs_divide ab .
  qed
  also have "\<dots> \<le> \<parallel>a - b\<parallel> / \<parallel>b\<parallel>"
    using vnorm_reverse[OF d] b0 by (intro divide_right_mono) (simp_all add: abs_minus_commute)
  finally have w: "\<parallel>?w\<parallel> \<le> \<parallel>a - b\<parallel> / \<parallel>b\<parallel>" .
  have "\<parallel>?u + ?w\<parallel> \<le> \<parallel>?u\<parallel> + \<parallel>?w\<parallel>" by (rule vnorm_add_le) (simp add: d)
  also have "\<dots> \<le> 2 * \<parallel>a - b\<parallel> / \<parallel>b\<parallel>" using u w by simp
  finally show ?thesis unfolding split .
qed

subsection \<open>Post-selecting a flag register\<close>

text \<open>The flag (the ancilla, or a register of $d$ levels) is the last tensor factor:
\<^term>\<open>pflag d P v\<close> keeps the components whose flag value $c$ satisfies $P\,c$.  Post-selection on
ancilla value $1$ is \<^term>\<open>post1\<close>; its success probability is $\norm{\mathrm{post1}\,v}^2$.\<close>

definition pflag :: "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "pflag d P v = Matrix.vec (dim_vec v) (\<lambda>r. if P (r mod d) then v $ r else 0)"

abbreviation post1 :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "post1 \<equiv> pflag 2 (\<lambda>c. c = 1)"

lemma dim_pflag [simp]: "dim_vec (pflag d P v) = dim_vec v"
  by (simp add: pflag_def)

lemma pflag_minus: "dim_vec u = dim_vec v \<Longrightarrow> pflag d P (u - v) = pflag d P u - pflag d P v"
  by (intro eq_vecI) (simp_all add: pflag_def)

lemma vnorm_pflag_le: "\<parallel>pflag d P v\<parallel> \<le> \<parallel>v\<parallel>"
proof -
  have "\<parallel>pflag d P v\<parallel>\<^sup>2 \<le> \<parallel>v\<parallel>\<^sup>2" unfolding vnorm_sq dim_pflag by (intro sum_mono) (simp add: pflag_def)
  thus ?thesis by (rule power2_le_imp_le) (simp add: vnorm_ge0)
qed

lemma post1_ideal:
  assumes w: "dim_vec w = N" and u: "dim_vec u = n" and v: "dim_vec v = n"
  shows "post1 (tensor_vec w (tensor_vec u (unit_vec 2 0) + tensor_vec v (unit_vec 2 1))) =
         tensor_vec w (tensor_vec v (unit_vec 2 1))"
proof -
  have zu: "dim_vec (tensor_vec u (unit_vec 2 0)) = n * 2" using tensor_vec_dim[OF u, of _ 2] by simp
  have zv: "dim_vec (tensor_vec v (unit_vec 2 1)) = n * 2" using tensor_vec_dim[OF v, of _ 2] by simp
  have z: "dim_vec (tensor_vec u (unit_vec 2 0) + tensor_vec v (unit_vec 2 1)) = n * 2" using zv by simp
  show ?thesis
  proof (rule eq_vecI)
    show "dim_vec (post1 (tensor_vec w (tensor_vec u (unit_vec 2 0) + tensor_vec v (unit_vec 2 1)))) =
          dim_vec (tensor_vec w (tensor_vec v (unit_vec 2 1)))"
      using tensor_vec_dim[OF w z] tensor_vec_dim[OF w zv] by simp
    fix r assume "r < dim_vec (tensor_vec w (tensor_vec v (unit_vec 2 1)))"
    hence r: "r < N * (n * 2)" using tensor_vec_dim[OF w zv] by simp
    hence n0: "0 < n" by (cases n) auto
    have s: "r mod (n * 2) < n * 2" using n0 by simp
    have mm: "r mod (n * 2) mod 2 = r mod 2" by (rule mod_mod_cancel) simp
    let ?Z = "tensor_vec u (unit_vec 2 0) + tensor_vec v (unit_vec 2 1)"
    have Zr: "?Z $ (r mod (n * 2)) = u $ (r mod (n * 2) div 2) * unit_vec 2 0 $ (r mod 2) + v $ (r mod (n * 2) div 2) * unit_vec 2 1 $ (r mod 2)"
      using s zv tensor_vec_index[OF u _ s, of "unit_vec 2 0"] tensor_vec_index[OF v _ s, of "unit_vec 2 1"] unfolding mm by simp
    have Vr: "tensor_vec v (unit_vec 2 1) $ (r mod (n * 2)) = v $ (r mod (n * 2) div 2) * unit_vec 2 1 $ (r mod 2)"
      using tensor_vec_index[OF v _ s, of "unit_vec 2 1"] unfolding mm by simp
    have L: "post1 (tensor_vec w ?Z) $ r = (if odd r then w $ (r div (n * 2)) * ?Z $ (r mod (n * 2)) else 0)"
      using r tensor_vec_index[OF w z r] tensor_vec_dim[OF w z] by (simp add: pflag_def odd_iff_mod_2_eq_one)
    have R: "tensor_vec w (tensor_vec v (unit_vec 2 1)) $ r = w $ (r div (n * 2)) * tensor_vec v (unit_vec 2 1) $ (r mod (n * 2))"
      by (rule tensor_vec_index[OF w zv r])
    show "post1 (tensor_vec w ?Z) $ r = tensor_vec w (tensor_vec v (unit_vec 2 1)) $ r"
    proof (cases "odd r")
      case True
      hence "r mod 2 = 1" by (simp add: odd_iff_mod_2_eq_one)
      thus ?thesis unfolding L R Zr Vr using True by simp
    next
      case False
      hence "r mod 2 = 0" by (simp add: even_iff_mod_2_eq_zero)
      thus ?thesis unfolding L R Vr using False by simp
    qed
  qed
qed

subsection \<open>The answer register\<close>

text \<open>For any output $\tilde y$ within $\delta$ of the exact output $y$: the success amplitude
$\norm{\mathrm{post1}\,\tilde y}$ is within $\delta$ of $C\norm{A^{-1}b}$, and once
$\delta<C\norm{A^{-1}b}$ the post-selected state is within $2\delta/(C\norm{A^{-1}b})$ of
$\psi\otimes\frac{A^{-1}b}{\norm{A^{-1}b}}\otimes\ket1$.\<close>

theorem hhl_readout:
  fixes A :: "complex Matrix.mat" and b y' :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and N: "2 \<le> N" and C: "0 < C"
      and b: "dim_vec b = n" and x0: "herm_inv A *\<^sub>v b \<noteq> 0\<^sub>v n"
      and y': "dim_vec y' = N * (n * 2)"
      and close: "\<parallel>y' - tensor_vec (win_state N)
                    (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
                     tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))\<parallel> \<le> \<delta>"
  shows "\<bar>\<parallel>post1 y'\<parallel> - C * \<parallel>herm_inv A *\<^sub>v b\<parallel>\<bar> \<le> \<delta>"
    and "\<delta> < C * \<parallel>herm_inv A *\<^sub>v b\<parallel> \<Longrightarrow>
         \<parallel>complex_of_real (1 / \<parallel>post1 y'\<parallel>) \<cdot>\<^sub>v post1 y' -
           tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>herm_inv A *\<^sub>v b\<parallel>) \<cdot>\<^sub>v (herm_inv A *\<^sub>v b)) (unit_vec 2 1))\<parallel>
         \<le> 2 * \<delta> / (C * \<parallel>herm_inv A *\<^sub>v b\<parallel>)"
proof -
  let ?G0 = "mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A"
  let ?x = "herm_inv A *\<^sub>v b"
  let ?y = "tensor_vec (win_state N) (tensor_vec (?G0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))"
  let ?p = "tensor_vec (win_state N) (tensor_vec ?x (unit_vec 2 1))"
  have Hi: "herm_inv A \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
  have G0: "?G0 \<in> carrier_mat n n" using A by simp
  have dx: "dim_vec ?x = n" using Hi by simp
  have d0: "dim_vec (?G0 *\<^sub>v b) = n" using G0 by simp
  have Cx: "(complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b = complex_of_real C \<cdot>\<^sub>v ?x" by (rule smult_mat_mult_vec[OF Hi carrier_vecI[OF b]])
  have dCx: "dim_vec (complex_of_real C \<cdot>\<^sub>v ?x) = n" using dx by simp
  have dx1: "dim_vec (tensor_vec ?x (unit_vec 2 1)) = n * 2" using tensor_vec_dim[OF dx, of _ 2] by simp
  have sl: "tensor_vec (c \<cdot>\<^sub>v ?x) (unit_vec 2 1) = c \<cdot>\<^sub>v tensor_vec ?x (unit_vec 2 1)" for c
    by (rule tensor_vec_smult_left[OF dx]) simp
  have sr: "tensor_vec (win_state N) (c \<cdot>\<^sub>v tensor_vec ?x (unit_vec 2 1)) = c \<cdot>\<^sub>v ?p" for c
    by (rule tensor_vec_smult_right[OF dim_win_state dx1])
  have py: "post1 ?y = complex_of_real C \<cdot>\<^sub>v ?p"
  proof -
    have "post1 ?y = tensor_vec (win_state N) (tensor_vec (complex_of_real C \<cdot>\<^sub>v ?x) (unit_vec 2 1))"
      unfolding Cx by (rule post1_ideal[OF dim_win_state d0 dCx])
    thus ?thesis unfolding sl sr .
  qed
  have np: "\<parallel>?p\<parallel> = \<parallel>?x\<parallel>"
  proof -
    have t1: "\<parallel>tensor_vec ?x (unit_vec 2 1)\<parallel> = \<parallel>?x\<parallel>" using vnorm_tensor[OF dx, where b = "unit_vec 2 1" and m = 2] by simp
    show ?thesis unfolding vnorm_tensor[OF dim_win_state dx1] t1 win_state_norm[OF N] by simp
  qed
  have npy: "\<parallel>post1 ?y\<parallel> = C * \<parallel>?x\<parallel>" unfolding py cpx_vec_length_smult np using C by simp
  have dy: "dim_vec ?y = N * (n * 2)"
  proof -
    have "dim_vec (tensor_vec (?G0 *\<^sub>v b) (unit_vec 2 0) + tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1)) = n * 2"
      unfolding Cx using tensor_vec_dim[OF dCx, of "unit_vec 2 1" 2] by simp
    thus ?thesis using tensor_vec_dim[OF dim_win_state] by simp
  qed
  have pd: "\<parallel>post1 y' - post1 ?y\<parallel> \<le> \<delta>"
    unfolding pflag_minus[OF y'[folded dy], symmetric] using vnorm_pflag_le close by (rule order_trans)
  show "\<bar>\<parallel>post1 y'\<parallel> - C * \<parallel>?x\<parallel>\<bar> \<le> \<delta>"
    unfolding npy[symmetric] using vnorm_reverse[of "post1 y'" "post1 ?y"] pd y' dy by simp
  assume small: "\<delta> < C * \<parallel>?x\<parallel>"
  have xn: "\<parallel>?x\<parallel> \<noteq> 0" using cpx_vec_length_zero_iff[of ?x] x0 dx by simp
  have xp: "0 < \<parallel>?x\<parallel>" using xn vnorm_ge0 by (simp add: order_le_neq_trans)
  have yn: "\<parallel>post1 ?y\<parallel> \<noteq> 0" using npy C xp by simp
  have y'n: "\<parallel>post1 y'\<parallel> \<noteq> 0"
  proof
    assume "\<parallel>post1 y'\<parallel> = 0"
    hence "C * \<parallel>?x\<parallel> \<le> \<delta>" using vnorm_reverse[of "post1 y'" "post1 ?y"] pd y' dy npy by simp
    thus False using small by simp
  qed
  have norm_y: "complex_of_real (1 / \<parallel>post1 ?y\<parallel>) \<cdot>\<^sub>v post1 ?y =
                tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?x) (unit_vec 2 1))"
  proof -
    have "complex_of_real (1 / \<parallel>post1 ?y\<parallel>) \<cdot>\<^sub>v post1 ?y = complex_of_real (1 / \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?p"
    proof -
      have e1: "complex_of_real (1 / \<parallel>post1 ?y\<parallel>) = complex_of_real (1 / (C * \<parallel>?x\<parallel>))" using npy by simp
      have e2: "complex_of_real (1 / (C * \<parallel>?x\<parallel>)) * complex_of_real C = complex_of_real (1 / \<parallel>?x\<parallel>)"
      proof -
        have "1 / (C * \<parallel>?x\<parallel>) * C = 1 / \<parallel>?x\<parallel>" using C xp by simp
        thus ?thesis by (metis of_real_mult)
      qed
      show ?thesis unfolding e1 unfolding py smult_smult_assoc e2 ..
    qed
    also have "\<dots> = tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?x) (unit_vec 2 1))"
      unfolding sl sr ..
    finally show ?thesis .
  qed
  have "\<parallel>complex_of_real (1 / \<parallel>post1 y'\<parallel>) \<cdot>\<^sub>v post1 y' - complex_of_real (1 / \<parallel>post1 ?y\<parallel>) \<cdot>\<^sub>v post1 ?y\<parallel>
        \<le> 2 * \<parallel>post1 y' - post1 ?y\<parallel> / \<parallel>post1 ?y\<parallel>"
    by (rule normalize_stable[OF _ y'n yn]) (simp only: dim_pflag y' dy)
  also have "\<dots> \<le> 2 * \<delta> / (C * \<parallel>?x\<parallel>)"
    unfolding npy using pd C xp by (intro divide_right_mono) simp_all
  finally show "\<parallel>complex_of_real (1 / \<parallel>post1 y'\<parallel>) \<cdot>\<^sub>v post1 y' -
           tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>?x\<parallel>) \<cdot>\<^sub>v ?x) (unit_vec 2 1))\<parallel>
         \<le> 2 * \<delta> / (C * \<parallel>?x\<parallel>)" unfolding norm_y .
qed

subsection \<open>Amplitude amplification\<close>

text \<open>$g$ is the good and $h$ the bad unit vector, $Pg=g$, $Ph=0$, and the state is
$\psi=\sin\theta\,g+\cos\theta\,h$.  The Grover operator $Q=(2\ketbra\psi\psi-I)(I-2P)$ rotates
the plane spanned by $g,h$ by $2\theta$, so after $k$ rounds the good amplitude is
$\sin((2k+1)\theta)$.\<close>

text \<open>The outer product $\ketbra vw$ of the notes as an explicit matrix.\<close>

lemma outer_prod_mat: "v \<oslash> w = Matrix.mat (dim_vec v) (dim_vec w) (\<lambda>(i, j). v $ i * cnj (w $ j))"
  by (rule eq_matI) (simp_all add: outer_prod_index ket_vec_def bra_vec_def row_vec_def cpx_mat_cnj_def)

definition grover :: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "grover K P psi = (2 \<cdot>\<^sub>m (psi \<oslash> psi) - 1\<^sub>m K) * (1\<^sub>m K - 2 \<cdot>\<^sub>m P)"

context
  fixes K :: nat and P :: "complex Matrix.mat" and g h :: "complex Matrix.vec"
  assumes P: "P \<in> carrier_mat K K" and g: "dim_vec g = K" and h: "dim_vec h = K"
      and gg: "\<langle>g|g\<rangle> = 1" and hh: "\<langle>h|h\<rangle> = 1" and gh: "\<langle>g|h\<rangle> = 0"
      and Pg: "P *\<^sub>v g = g" and Ph: "P *\<^sub>v h = 0\<^sub>v K"
begin

definition comb :: "real \<Rightarrow> real \<Rightarrow> complex Matrix.vec" where
  "comb a c = complex_of_real a \<cdot>\<^sub>v g + complex_of_real c \<cdot>\<^sub>v h"

lemma dim_comb [simp]: "dim_vec (comb a c) = K"
  by (simp add: comb_def h)

lemma hg: "\<langle>h|g\<rangle> = 0"
  using gh inner_prod_cnj[of g h] g h by simp

lemma comb_inner: "\<langle>comb a c|comb a' c'\<rangle> = complex_of_real (a * a' + c * c')"
  unfolding comb_def inner_prod_is_sesquilinear[OF g h g h] gg hh gh hg by simp

lemma comb_lin: "complex_of_real z \<cdot>\<^sub>v comb a c + complex_of_real z' \<cdot>\<^sub>v comb a' c' = comb (z * a + z' * a') (z * c + z' * c')"
  using g h by (intro eq_vecI) (simp_all add: comb_def algebra_simps)

lemma P_comb: "P *\<^sub>v comb a c = comb a 0"
proof -
  have gc: "complex_of_real a \<cdot>\<^sub>v g \<in> carrier_vec K" by (rule carrier_vecI) (simp add: g)
  have hc: "complex_of_real c \<cdot>\<^sub>v h \<in> carrier_vec K" by (rule carrier_vecI) (simp add: h)
  have gc': "g \<in> carrier_vec K" by (rule carrier_vecI[OF g])
  have hc': "h \<in> carrier_vec K" by (rule carrier_vecI[OF h])
  have "P *\<^sub>v comb a c = P *\<^sub>v (complex_of_real a \<cdot>\<^sub>v g) + P *\<^sub>v (complex_of_real c \<cdot>\<^sub>v h)"
    unfolding comb_def by (rule mult_add_distrib_mat_vec[OF P gc hc])
  also have "P *\<^sub>v (complex_of_real a \<cdot>\<^sub>v g) = complex_of_real a \<cdot>\<^sub>v g"
    using mult_mat_vec[OF P gc', of "complex_of_real a"] Pg by simp
  also have "P *\<^sub>v (complex_of_real c \<cdot>\<^sub>v h) = 0\<^sub>v K"
  proof -
    have z: "complex_of_real c \<cdot>\<^sub>v 0\<^sub>v K = 0\<^sub>v K" by (intro eq_vecI) simp_all
    show ?thesis using mult_mat_vec[OF P hc', of "complex_of_real c"] Ph z by simp
  qed
  also have "complex_of_real a \<cdot>\<^sub>v g + 0\<^sub>v K = comb a 0" using g h by (intro eq_vecI) (simp_all add: comb_def)
  finally show ?thesis .
qed

lemma reflP_comb: "(1\<^sub>m K - 2 \<cdot>\<^sub>m P) *\<^sub>v comb a c = comb (- a) c"
proof -
  have cc: "comb a c \<in> carrier_vec K" by (rule carrier_vecI) simp
  have "(1\<^sub>m K - 2 \<cdot>\<^sub>m P) *\<^sub>v comb a c = 1\<^sub>m K *\<^sub>v comb a c - (2 \<cdot>\<^sub>m P) *\<^sub>v comb a c"
    by (rule minus_mult_distrib_mat_vec[OF one_carrier_mat smult_carrier_mat[OF P] cc])
  also have "(2 \<cdot>\<^sub>m P) *\<^sub>v comb a c = 2 \<cdot>\<^sub>v comb a 0" using smult_mat_mult_vec[OF P carrier_vecI, of "comb a c" 2] P_comb by simp
  also have "1\<^sub>m K *\<^sub>v comb a c - 2 \<cdot>\<^sub>v comb a 0 = comb (- a) c"
    using cc g h by (intro eq_vecI) (simp_all add: comb_def algebra_simps)
  finally show ?thesis .
qed

lemma reflpsi_comb:
  "(2 \<cdot>\<^sub>m (comb s c \<oslash> comb s c) - 1\<^sub>m K) *\<^sub>v comb a d = comb (2 * (s * a + c * d) * s - a) (2 * (s * a + c * d) * c - d)"
proof -
  have O: "(comb s c \<oslash> comb s c) \<in> carrier_mat K K" by (rule outer_prod_carrier) simp_all
  have cc: "comb a d \<in> carrier_vec K" by (rule carrier_vecI) simp
  have "(2 \<cdot>\<^sub>m (comb s c \<oslash> comb s c) - 1\<^sub>m K) *\<^sub>v comb a d = (2 \<cdot>\<^sub>m (comb s c \<oslash> comb s c)) *\<^sub>v comb a d - 1\<^sub>m K *\<^sub>v comb a d"
    by (rule minus_mult_distrib_mat_vec[OF smult_carrier_mat[OF O] one_carrier_mat cc])
  also have "(2 \<cdot>\<^sub>m (comb s c \<oslash> comb s c)) *\<^sub>v comb a d = 2 \<cdot>\<^sub>v (complex_of_real (s * a + c * d) \<cdot>\<^sub>v comb s c)"
    using smult_mat_mult_vec[OF O carrier_vecI, of "comb a d" 2] outer_prod_mult_vec[of "comb a d" "comb s c" "comb s c"] comb_inner by simp
  also have "\<dots> - 1\<^sub>m K *\<^sub>v comb a d = comb (2 * (s * a + c * d) * s - a) (2 * (s * a + c * d) * c - d)"
    using cc g h by (intro eq_vecI) (simp_all add: comb_def algebra_simps)
  finally show ?thesis .
qed

lemma grover_comb:
  "grover K P (comb (sin \<theta>) (cos \<theta>)) *\<^sub>v comb (sin \<phi>) (cos \<phi>) = comb (sin (\<phi> + 2 * \<theta>)) (cos (\<phi> + 2 * \<theta>))"
proof -
  have O: "(comb (sin \<theta>) (cos \<theta>) \<oslash> comb (sin \<theta>) (cos \<theta>)) \<in> carrier_mat K K" by (rule outer_prod_carrier) simp_all
  have R: "1\<^sub>m K - 2 \<cdot>\<^sub>m P \<in> carrier_mat K K" by (rule minus_carrier_mat[OF smult_carrier_mat[OF P]])
  have S: "2 \<cdot>\<^sub>m (comb (sin \<theta>) (cos \<theta>) \<oslash> comb (sin \<theta>) (cos \<theta>)) - 1\<^sub>m K \<in> carrier_mat K K" by (rule minus_carrier_mat[OF one_carrier_mat])
  have "grover K P (comb (sin \<theta>) (cos \<theta>)) *\<^sub>v comb (sin \<phi>) (cos \<phi>) =
        (2 \<cdot>\<^sub>m (comb (sin \<theta>) (cos \<theta>) \<oslash> comb (sin \<theta>) (cos \<theta>)) - 1\<^sub>m K) *\<^sub>v ((1\<^sub>m K - 2 \<cdot>\<^sub>m P) *\<^sub>v comb (sin \<phi>) (cos \<phi>))"
    unfolding grover_def by (rule assoc_mult_mat_vec[OF S R]) (rule carrier_vecI, simp)
  also have "\<dots> = comb (2 * (sin \<theta> * - sin \<phi> + cos \<theta> * cos \<phi>) * sin \<theta> + sin \<phi>)
                       (2 * (sin \<theta> * - sin \<phi> + cos \<theta> * cos \<phi>) * cos \<theta> - cos \<phi>)"
    unfolding reflP_comb reflpsi_comb by simp
  also have "\<dots> = comb (sin (\<phi> + 2 * \<theta>)) (cos (\<phi> + 2 * \<theta>))"
  proof -
    have e: "sin \<theta> * - sin \<phi> + cos \<theta> * cos \<phi> = cos (\<phi> + \<theta>)" by (simp add: cos_add)
    have a: "2 * cos (\<phi> + \<theta>) * sin \<theta> + sin \<phi> = sin (\<phi> + 2 * \<theta>)"
      using sin_add[of "\<phi> + \<theta>" \<theta>] sin_diff[of "\<phi> + \<theta>" \<theta>] by (simp add: algebra_simps)
    have b: "2 * cos (\<phi> + \<theta>) * cos \<theta> - cos \<phi> = cos (\<phi> + 2 * \<theta>)"
      using cos_add[of "\<phi> + \<theta>" \<theta>] cos_diff[of "\<phi> + \<theta>" \<theta>] by (simp add: algebra_simps)
    show ?thesis unfolding e a b ..
  qed
  finally show ?thesis .
qed

theorem grover_iterate:
  "(grover K P (comb (sin \<theta>) (cos \<theta>)) ^\<^sub>m k) *\<^sub>v comb (sin \<theta>) (cos \<theta>) =
   comb (sin ((2 * real k + 1) * \<theta>)) (cos ((2 * real k + 1) * \<theta>))"
proof -
  let ?Q = "grover K P (comb (sin \<theta>) (cos \<theta>))"
  have Q: "?Q \<in> carrier_mat K K"
    unfolding grover_def by (rule mult_carrier_mat[OF minus_carrier_mat[OF one_carrier_mat] minus_carrier_mat[OF smult_carrier_mat[OF P]]])
  have "\<forall>\<phi>. (?Q ^\<^sub>m k) *\<^sub>v comb (sin \<phi>) (cos \<phi>) = comb (sin (\<phi> + 2 * real k * \<theta>)) (cos (\<phi> + 2 * real k * \<theta>))"
  proof (induction k)
    case 0
    show ?case using Q one_mult_mat_vec[OF carrier_vecI[OF dim_comb]] by simp
  next
    case (Suc k)
    show ?case
    proof
      fix \<phi>
      have "(?Q ^\<^sub>m Suc k) *\<^sub>v comb (sin \<phi>) (cos \<phi>) = (?Q ^\<^sub>m k) *\<^sub>v (?Q *\<^sub>v comb (sin \<phi>) (cos \<phi>))"
        using assoc_mult_mat_vec[OF pow_carrier_mat[OF Q] Q carrier_vecI[OF dim_comb]] by simp
      also have "\<dots> = comb (sin (\<phi> + 2 * \<theta> + 2 * real k * \<theta>)) (cos (\<phi> + 2 * \<theta> + 2 * real k * \<theta>))"
        unfolding grover_comb using Suc.IH by blast
      finally show "(?Q ^\<^sub>m Suc k) *\<^sub>v comb (sin \<phi>) (cos \<phi>) = comb (sin (\<phi> + 2 * real (Suc k) * \<theta>)) (cos (\<phi> + 2 * real (Suc k) * \<theta>))"
        by (simp add: algebra_simps)
    qed
  qed
  thus ?thesis by (simp add: algebra_simps)
qed

text \<open>The success probability after $k$ rounds is $\sin^2((2k+1)\theta)$.\<close>

corollary grover_success:
  "\<parallel>P *\<^sub>v ((grover K P (comb (sin \<theta>) (cos \<theta>)) ^\<^sub>m k) *\<^sub>v comb (sin \<theta>) (cos \<theta>))\<parallel>\<^sup>2 = (sin ((2 * real k + 1) * \<theta>))\<^sup>2"
proof -
  have "complex_of_real (\<parallel>comb (sin ((2 * real k + 1) * \<theta>)) 0\<parallel>\<^sup>2) = complex_of_real ((sin ((2 * real k + 1) * \<theta>))\<^sup>2)"
    unfolding cpx_vec_length_inner_prod comb_inner by (simp add: power2_eq_square)
  thus ?thesis unfolding grover_iterate P_comb of_real_eq_iff .
qed

end

subsection \<open>The number of rounds\<close>

text \<open>With $k=\lfloor\pi/(4\theta)\rfloor$ rounds the success probability is at least
$\cos^2\theta=1-\sin^2\theta$, and $k\le\pi/(4\theta)$.\<close>

lemma grover_rounds:
  assumes t0: "0 < \<theta>" and t1: "\<theta> < pi / 2"
  defines "k \<equiv> nat \<lfloor>pi / (4 * \<theta>)\<rfloor>"
  shows "1 - (sin \<theta>)\<^sup>2 \<le> (sin ((2 * real k + 1) * \<theta>))\<^sup>2" and "real k \<le> pi / (4 * \<theta>)"
    and "0 < sin ((2 * real k + 1) * \<theta>)"
proof -
  have q0: "0 \<le> pi / (4 * \<theta>)" using t0 by simp
  have kr: "real k = real_of_int \<lfloor>pi / (4 * \<theta>)\<rfloor>" unfolding k_def using q0 by simp
  show kle: "real k \<le> pi / (4 * \<theta>)" unfolding kr by simp
  have kgt: "pi / (4 * \<theta>) < real k + 1" unfolding kr by linarith
  define d where "d = (2 * real k + 1) * \<theta> - pi / 2"
  have "2 * real k * \<theta> \<le> pi / 2" using kle t0 by (simp add: field_simps)
  hence d1: "d \<le> \<theta>" unfolding d_def by (simp add: algebra_simps)
  have "pi / 2 < (2 * real k + 2) * \<theta>" using kgt t0 by (simp add: field_simps)
  hence d2: "- \<theta> < d" unfolding d_def by (simp add: algebra_simps)
  have "sin ((2 * real k + 1) * \<theta>) = cos d" unfolding d_def by (simp add: cos_diff)
  also have "cos d = cos \<bar>d\<bar>" by (simp add: abs_if)
  finally have sd: "sin ((2 * real k + 1) * \<theta>) = cos \<bar>d\<bar>" .
  have ad: "\<bar>d\<bar> \<le> \<theta>" using d1 d2 by linarith
  have "cos \<theta> \<le> cos \<bar>d\<bar>" by (rule cos_monotone_0_pi_le) (use ad t1 in simp_all)
  moreover have "0 < cos \<theta>" using t0 t1 by (intro cos_gt_zero_pi) simp_all
  ultimately show "0 < sin ((2 * real k + 1) * \<theta>)" unfolding sd by linarith
  have "cos \<theta> \<le> cos \<bar>d\<bar>" by (rule cos_monotone_0_pi_le) (use ad t1 in simp_all)
  moreover have "0 \<le> cos \<theta>" using t0 t1 by (simp add: cos_ge_zero)
  ultimately have "(cos \<theta>)\<^sup>2 \<le> (sin ((2 * real k + 1) * \<theta>))\<^sup>2" unfolding sd by (intro power_mono) simp_all
  thus "1 - (sin \<theta>)\<^sup>2 \<le> (sin ((2 * real k + 1) * \<theta>))\<^sup>2" by (simp add: cos_squared_eq)
qed

subsection \<open>Good and bad components of a state\<close>

lemma projector_split:
  assumes P: "P \<in> carrier_mat K K" "P * P = P" "P\<^sup>\<dagger> = P"
      and psi: "dim_vec psi = K" "\<parallel>psi\<parallel> = 1" and a0: "0 < \<parallel>P *\<^sub>v psi\<parallel>" and a1: "\<parallel>P *\<^sub>v psi\<parallel> < 1"
  obtains g h \<theta> where "dim_vec g = K" "dim_vec h = K" "\<langle>g|g\<rangle> = 1" "\<langle>h|h\<rangle> = 1" "\<langle>g|h\<rangle> = 0"
      "P *\<^sub>v g = g" "P *\<^sub>v h = 0\<^sub>v K" "0 < \<theta>" "\<theta> < pi / 2" "sin \<theta> = \<parallel>P *\<^sub>v psi\<parallel>"
      "psi = complex_of_real (sin \<theta>) \<cdot>\<^sub>v g + complex_of_real (cos \<theta>) \<cdot>\<^sub>v h"
proof -
  let ?p = "P *\<^sub>v psi" and ?r = "psi - P *\<^sub>v psi"
  define a where "a = \<parallel>?p\<parallel>"
  have pc: "psi \<in> carrier_vec K" using psi(1) by (rule carrier_vecI)
  have dp: "dim_vec ?p = K" using P(1) by simp
  have dr: "dim_vec ?r = K" using psi(1) P(1) by simp
  have rc: "?r \<in> carrier_vec K" using dr by (rule carrier_vecI)
  have PP: "P *\<^sub>v ?p = ?p" using assoc_mult_mat_vec[OF P(1) P(1) pc] P(2) by simp
  have Pr: "P *\<^sub>v ?r = 0\<^sub>v K"
  proof -
    have "P *\<^sub>v ?r = P *\<^sub>v psi - P *\<^sub>v ?p" by (rule mult_minus_distrib_mat_vec[OF P(1) pc carrier_vecI[OF dp]])
    thus ?thesis unfolding PP using carrier_matD[OF P(1)] by (intro eq_vecI) simp_all
  qed
  have pr: "\<langle>?p|?r\<rangle> = 0"
  proof -
    have Pd: "P\<^sup>\<dagger> \<in> carrier_mat K K" by (rule dagger_carrier[OF P(1)])
    have "\<langle>?p|P\<^sup>\<dagger> *\<^sub>v ?r\<rangle> = \<langle>(P\<^sup>\<dagger>)\<^sup>\<dagger> *\<^sub>v ?p|?r\<rangle>" by (rule inner_prod_adjoint_swap[OF Pd dp dr])
    hence "\<langle>P *\<^sub>v ?p|?r\<rangle> = \<langle>?p|P *\<^sub>v ?r\<rangle>" unfolding P(3) dagger_of_dagger_is_id ..
    moreover have "\<langle>?p|0\<^sub>v K\<rangle> = 0" using dp by (simp add: inner_prod_def scalar_prod_def)
    ultimately show ?thesis unfolding PP Pr by simp
  qed
  have rp: "\<langle>?r|?p\<rangle> = 0" using inner_prod_cnj[of ?p ?r] pr dp dr by simp
  have split: "psi = ?p + ?r" using psi(1) dp by (intro eq_vecI) simp_all
  define c where "c = \<parallel>?r\<parallel>"
  have pyth: "a\<^sup>2 + c\<^sup>2 = 1"
  proof -
    have "complex_of_real (\<parallel>psi\<parallel>\<^sup>2) = \<langle>?p + ?r|?p + ?r\<rangle>" unfolding cpx_vec_length_inner_prod using split by simp
    also have "\<dots> = \<langle>?p|?p\<rangle> + \<langle>?r|?r\<rangle>" using No_Cloning.inner_prod_expand[of ?p ?r ?p ?r] dp dr pr rp by simp
    finally have "complex_of_real 1 = complex_of_real (a\<^sup>2 + c\<^sup>2)" unfolding cpx_vec_length_inner_prod[symmetric] a_def c_def psi(2) by simp
    thus ?thesis by (simp only: of_real_eq_iff)
  qed
  have a0': "0 < a" and a1': "a < 1" using a0 a1 by (simp_all add: a_def)
  have c_eq: "c = sqrt (1 - a\<^sup>2)" using pyth vnorm_ge0[of ?r] by (simp add: c_def real_sqrt_unique[symmetric])
  have c0: "0 < c"
  proof -
    have "a\<^sup>2 < 1" using a0' a1' by (simp add: power_less_one_iff)
    thus ?thesis unfolding c_eq by simp
  qed
  define \<theta> where "\<theta> = arcsin a"
  have st: "sin \<theta> = a" unfolding \<theta>_def using a0' a1' by simp
  have ct: "cos \<theta> = c" unfolding \<theta>_def c_eq using a0' a1' by (simp add: cos_arcsin)
  have t0: "0 < \<theta>" unfolding \<theta>_def using a0' a1' by (simp add: arcsin_less_arcsin[of 0 a, simplified])
  have t1: "\<theta> < pi / 2" unfolding \<theta>_def using a0' a1' arcsin_less_arcsin[of a 1] by simp
  define g where "g = complex_of_real (1 / a) \<cdot>\<^sub>v ?p"
  define h where "h = complex_of_real (1 / c) \<cdot>\<^sub>v ?r"
  have dg: "dim_vec g = K" and dh: "dim_vec h = K" using dp dr by (simp_all add: g_def h_def)
  have gg: "\<langle>g|g\<rangle> = 1"
    unfolding g_def cpx_vec_length_inner_prod[symmetric] cpx_vec_length_smult norm_of_real a_def[symmetric] using a0' by simp
  have hh: "\<langle>h|h\<rangle> = 1"
    unfolding h_def cpx_vec_length_inner_prod[symmetric] cpx_vec_length_smult norm_of_real c_def[symmetric] using c0 by simp
  have gh: "\<langle>g|h\<rangle> = 0"
  proof -
    have "\<langle>g|h\<rangle> = cnj (complex_of_real (1 / a)) * (complex_of_real (1 / c) * \<langle>?p|?r\<rangle>)"
      unfolding g_def h_def
      using inner_prod_distrib_left[of ?p "complex_of_real (1 / c) \<cdot>\<^sub>v ?r" "complex_of_real (1 / a)"]
            inner_prod_distrib_right[of ?p ?r "complex_of_real (1 / c)"] dp dr by simp
    thus ?thesis unfolding pr by simp
  qed
  have Pg: "P *\<^sub>v g = g" unfolding g_def using mult_mat_vec[OF P(1) carrier_vecI[OF dp]] PP by simp
  have Ph: "P *\<^sub>v h = 0\<^sub>v K"
  proof -
    have "P *\<^sub>v h = complex_of_real (1 / c) \<cdot>\<^sub>v 0\<^sub>v K" unfolding h_def using mult_mat_vec[OF P(1) rc] Pr by simp
    moreover have "complex_of_real (1 / c) \<cdot>\<^sub>v 0\<^sub>v K = 0\<^sub>v K" by (intro eq_vecI) simp_all
    ultimately show ?thesis by simp
  qed
  have psi_eq: "psi = complex_of_real (sin \<theta>) \<cdot>\<^sub>v g + complex_of_real (cos \<theta>) \<cdot>\<^sub>v h"
    unfolding st ct g_def h_def using a0' c0 dp dr psi(1) by (intro eq_vecI) simp_all
  show ?thesis by (rule that[OF dg dh gg hh gh Pg Ph t0 t1 st[unfolded a_def] psi_eq])
qed

subsection \<open>Diagonal projectors and reflections\<close>

text \<open>The projector onto the basis vectors with index in $A$, and the diagonal sign matrix that
reflects them: both are diagonal matrices (\<^const>\<open>mat_diag\<close>).  The projector onto ancilla value
$j$ and the one onto the flag values satisfying $P$ are instances.\<close>

definition proj_set :: "nat \<Rightarrow> nat set \<Rightarrow> complex Matrix.mat" where
  "proj_set n A = mat_diag n (\<lambda>i. if i \<in> A then 1 else 0)"

abbreviation anc_proj :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "anc_proj K j \<equiv> proj_set K {r. r mod 2 = j}"

abbreviation pflag_mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> complex Matrix.mat" where
  "pflag_mat K d P \<equiv> proj_set K {r. P (r mod d)}"

definition sign_diag :: "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> complex Matrix.mat" where
  "sign_diag K f = mat_diag K (\<lambda>i. if f i then - 1 else 1)"

lemma proj_set_carrier [simp]: "proj_set n A \<in> carrier_mat n n"
  by (simp add: proj_set_def)

lemma dim_proj_set [simp]: "dim_row (proj_set n A) = n" "dim_col (proj_set n A) = n"
  by (simp_all add: proj_set_def mat_diag_def)

lemma proj_set_index: "i < n \<Longrightarrow> j < n \<Longrightarrow> proj_set n A $$ (i, j) = (if i = j \<and> i \<in> A then 1 else 0)"
  by (simp add: proj_set_def mat_diag_def)

lemma proj_set_dagger: "(proj_set n A)\<^sup>\<dagger> = proj_set n A"
  by (rule eq_matI) (auto simp: proj_set_def mat_diag_def dagger_def)

lemma proj_set_idem: "proj_set n A * proj_set n A = proj_set n A"
  unfolding proj_set_def mat_diag_diag by (rule arg_cong[where f = "mat_diag n"]) auto

lemma proj_set_mult_vec: "dim_vec v = n \<Longrightarrow> proj_set n A *\<^sub>v v = Matrix.vec n (\<lambda>i. if i \<in> A then v $ i else 0)"
  by (intro eq_vecI) (auto simp: proj_set_def mat_diag_def scalar_prod_def if_distrib[of "\<lambda>x. x * _"] sum.delta cong: if_cong)

lemma proj_set_compl: "1\<^sub>m n - proj_set n A = proj_set n (- A)"
  by (rule eq_matI) (auto simp: proj_set_def mat_diag_def)

lemma pflag_mat_mult: "dim_vec v = K \<Longrightarrow> pflag_mat K d P *\<^sub>v v = pflag d P v"
  by (simp add: proj_set_mult_vec pflag_def)

lemma sign_diag_carrier: "sign_diag K f \<in> carrier_mat K K"
  by (simp add: sign_diag_def)

lemma sign_diag_dagger: "(sign_diag K f)\<^sup>\<dagger> = sign_diag K f"
  by (rule eq_matI) (auto simp: sign_diag_def mat_diag_def dagger_def)

lemma sign_diag_sq: "sign_diag K f * sign_diag K f = 1\<^sub>m K"
proof -
  have "(\<lambda>i. (if f i then - 1 else 1) * (if f i then - 1 else 1)) = (\<lambda>_. 1 :: complex)" by auto
  thus ?thesis unfolding sign_diag_def mat_diag_diag by simp
qed

lemma sign_diag_unitary: "unitary (sign_diag K f)"
proof -
  have d: "dim_row (sign_diag K f) = K" "dim_col (sign_diag K f) = K" by (simp_all add: sign_diag_def mat_diag_def)
  show ?thesis unfolding unitary_def sign_diag_dagger d sign_diag_sq by simp
qed

lemma refl_proj_set: "1\<^sub>m n - 2 \<cdot>\<^sub>m proj_set n A = sign_diag n (\<lambda>i. i \<in> A)"
  by (rule eq_matI) (auto simp: proj_set_def sign_diag_def mat_diag_def)

lemma refl_anc_one: "1\<^sub>m K - 2 \<cdot>\<^sub>m anc_proj K 1 = sign_diag K odd"
  unfolding refl_proj_set by (simp add: odd_iff_mod_2_eq_one)

lemma refl_zero: "2 \<cdot>\<^sub>m (unit_vec K 0 \<oslash> unit_vec K 0) - 1\<^sub>m K = sign_diag K (\<lambda>i. i \<noteq> 0)"
  by (intro eq_matI) (auto simp: outer_prod_mat sign_diag_def mat_diag_def unit_vec_def)

text \<open>Reflection about $U\ket0$: $U(2\ketbra00-I)U^*=2\ketbra\psi\psi-I$ for $\psi=U\ket0$.\<close>

lemma outer_conj:
  assumes U: "U \<in> carrier_mat K K" and K: "0 < K"
  shows "U * (unit_vec K 0 \<oslash> unit_vec K 0) * (U\<^sup>\<dagger>) = ((U *\<^sub>v unit_vec K 0) \<oslash> (U *\<^sub>v unit_vec K 0))"
proof -
  have E: "(unit_vec K 0 \<oslash> unit_vec K 0) \<in> carrier_mat K K" by (rule outer_prod_carrier) simp_all
  have UE: "U * (unit_vec K 0 \<oslash> unit_vec K 0) = Matrix.mat K K (\<lambda>(i, k). if k = 0 then U $$ (i, 0) else 0)"
  proof (rule eq_matI)
    fix i k assume "i < dim_row (Matrix.mat K K (\<lambda>(i, k). if k = 0 then U $$ (i, 0) else 0))"
        "k < dim_col (Matrix.mat K K (\<lambda>(i, k). if k = 0 then U $$ (i, 0) else 0))"
    hence i: "i < K" and k: "k < K" by simp_all
    have "(U * (unit_vec K 0 \<oslash> unit_vec K 0)) $$ (i, k) = (\<Sum>l<K. U $$ (i, l) * ((if l = 0 then 1 else 0) * cnj (if k = 0 then 1 else 0)))"
      using U i k by (simp add: outer_prod_mat scalar_prod_def unit_vec_def atLeast0LessThan)
    also have "\<dots> = (if k = 0 then U $$ (i, 0) else 0)"
      using K by (simp add: if_distrib[of "\<lambda>x. _ * x"] if_distrib[of "\<lambda>x. x * _"] sum.delta cong: if_cong)
    finally show "(U * (unit_vec K 0 \<oslash> unit_vec K 0)) $$ (i, k) = Matrix.mat K K (\<lambda>(i, k). if k = 0 then U $$ (i, 0) else 0) $$ (i, k)"
      using i k by simp
  qed (use U in \<open>simp_all add: outer_prod_mat\<close>)
  show ?thesis
  proof (rule eq_matI)
    fix i j assume "i < dim_row (((U *\<^sub>v unit_vec K 0) \<oslash> (U *\<^sub>v unit_vec K 0)))" "j < dim_col (((U *\<^sub>v unit_vec K 0) \<oslash> (U *\<^sub>v unit_vec K 0)))"
    hence i: "i < K" and j: "j < K" using U by (simp_all add: outer_prod_mat)
    have col: "(U *\<^sub>v unit_vec K 0) $ r = U $$ (r, 0)" if "r < K" for r
      using U that K by (simp add: scalar_prod_def unit_vec_def atLeast0LessThan if_distrib[of "\<lambda>x. _ * x"] sum.delta cong: if_cong)
    have "(U * (unit_vec K 0 \<oslash> unit_vec K 0) * (U\<^sup>\<dagger>)) $$ (i, j) = (\<Sum>k<K. (if k = 0 then U $$ (i, 0) else 0) * cnj (U $$ (j, k)))"
      unfolding UE using U i j by (simp add: dagger_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = U $$ (i, 0) * cnj (U $$ (j, 0))"
      using K by (simp add: if_distrib[of "\<lambda>x. x * _"] sum.delta cong: if_cong)
    finally show "(U * (unit_vec K 0 \<oslash> unit_vec K 0) * (U\<^sup>\<dagger>)) $$ (i, j) = ((U *\<^sub>v unit_vec K 0) \<oslash> (U *\<^sub>v unit_vec K 0)) $$ (i, j)"
      using i j U col by (simp add: outer_prod_mat)
  qed (use U in \<open>simp_all add: outer_prod_mat\<close>)
qed

lemma reflection_conj:
  assumes U: "U \<in> carrier_mat K K" "unitary U" and K: "0 < K"
  shows "U * (sign_diag K (\<lambda>i. i \<noteq> 0) * (U\<^sup>\<dagger>)) = 2 \<cdot>\<^sub>m ((U *\<^sub>v unit_vec K 0) \<oslash> (U *\<^sub>v unit_vec K 0)) - 1\<^sub>m K"
proof -
  let ?E = "(unit_vec K 0 \<oslash> unit_vec K 0)"
  have E: "?E \<in> carrier_mat K K" by (rule outer_prod_carrier) simp_all
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat K K" by (rule dagger_carrier[OF U(1)])
  have UU: "U * (U\<^sup>\<dagger>) = 1\<^sub>m K" using U unfolding unitary_def by auto
  have "U * (sign_diag K (\<lambda>i. i \<noteq> 0) * (U\<^sup>\<dagger>)) = U * ((2 \<cdot>\<^sub>m ?E - 1\<^sub>m K) * (U\<^sup>\<dagger>))" unfolding refl_zero ..
  also have "(2 \<cdot>\<^sub>m ?E - 1\<^sub>m K) * (U\<^sup>\<dagger>) = 2 \<cdot>\<^sub>m (?E * (U\<^sup>\<dagger>)) - (U\<^sup>\<dagger>)"
    using minus_mult_distrib_mat[OF smult_carrier_mat[OF E] one_carrier_mat Ud, of 2] mult_smult_assoc_mat[OF E Ud, of 2] left_mult_one_mat[OF Ud] by simp
  also have "U * (2 \<cdot>\<^sub>m (?E * (U\<^sup>\<dagger>)) - (U\<^sup>\<dagger>)) = 2 \<cdot>\<^sub>m (U * (?E * (U\<^sup>\<dagger>))) - U * (U\<^sup>\<dagger>)"
    using mult_minus_distrib_mat[OF U(1) smult_carrier_mat[OF mult_carrier_mat[OF E Ud]] Ud]
          mult_smult_distrib[OF U(1) mult_carrier_mat[OF E Ud]] by simp
  also have "U * (?E * (U\<^sup>\<dagger>)) = U * ?E * (U\<^sup>\<dagger>)" by (rule assoc_mult_mat[OF U(1) E Ud, symmetric])
  finally show ?thesis unfolding outer_conj[OF U(1) K] UU .
qed

subsection \<open>Amplitude amplification as a circuit\<close>

text \<open>One round: reflect about the bad subspace, then about $U\ket0$; it uses $U$ and $U^*$.\<close>

definition grover_prog :: "nat \<Rightarrow> qcirc \<Rightarrow> qcirc" where
  "grover_prog K u = Seq (Gate (sign_diag K odd)) (Seq (adj u) (Seq (Gate (sign_diag K (\<lambda>i. i \<noteq> 0))) u))"

primrec aa_prog :: "nat \<Rightarrow> qcirc \<Rightarrow> nat \<Rightarrow> qcirc" where
  "aa_prog K u 0 = u"
| "aa_prog K u (Suc k) = Seq (aa_prog K u k) (grover_prog K u)"

lemma calls_aa_prog: "calls (aa_prog K u k) = (2 * k + 1) * calls u"
  by (induction k) (simp_all add: grover_prog_def)

lemma gates_ok_aa_prog: "gates_ok K u \<Longrightarrow> gates_ok K (aa_prog K u k)"
  by (induction k) (simp_all add: grover_prog_def gates_ok_adj sign_diag_carrier sign_diag_unitary)

lemma sem_grover_prog:
  assumes V: "V \<in> carrier_mat m m" "unitary V" and g: "gates_ok (N * m) u" and K: "0 < N * m"
  shows "sem N m V (grover_prog (N * m) u) = grover (N * m) (anc_proj (N * m) 1) (sem N m V u *\<^sub>v unit_vec (N * m) 0)"
proof -
  let ?K = "N * m" and ?U = "sem N m V u"
  have U: "?U \<in> carrier_mat ?K ?K" "unitary ?U" using sem_carrier[OF V g] sem_unitary[OF V g] by simp_all
  have Ud: "(?U\<^sup>\<dagger>) \<in> carrier_mat ?K ?K" by (rule dagger_carrier[OF U(1)])
  have D0: "sign_diag ?K (\<lambda>i. i \<noteq> 0) \<in> carrier_mat ?K ?K" and D1: "sign_diag ?K odd \<in> carrier_mat ?K ?K"
    by (simp_all add: sign_diag_carrier)
  have "sem N m V (grover_prog ?K u) = ?U * (sign_diag ?K (\<lambda>i. i \<noteq> 0) * (?U\<^sup>\<dagger>)) * sign_diag ?K odd"
    unfolding grover_prog_def sem.simps sem_adj[OF V g]
    using assoc_mult_mat[OF U(1) D0 Ud] by simp
  also have "\<dots> = grover ?K (anc_proj ?K 1) (?U *\<^sub>v unit_vec ?K 0)"
    unfolding reflection_conj[OF U K] grover_def refl_anc_one ..
  finally show ?thesis .
qed

lemma pow_mat_comm:
  assumes A: "A \<in> carrier_mat n n"
  shows "A * A ^\<^sub>m k = A ^\<^sub>m k * A"
proof (induction k)
  case 0
  show ?case using A by simp
next
  case (Suc k)
  have "A * A ^\<^sub>m Suc k = (A * A ^\<^sub>m k) * A" using assoc_mult_mat[OF A pow_carrier_mat[OF A] A] by simp
  also have "\<dots> = A ^\<^sub>m Suc k * A" unfolding Suc by simp
  finally show ?case .
qed

lemma sem_aa_prog:
  assumes V: "V \<in> carrier_mat m m" "unitary V" and g: "gates_ok (N * m) u" and K: "0 < N * m"
  shows "sem N m V (aa_prog (N * m) u k) = grover (N * m) (anc_proj (N * m) 1) (sem N m V u *\<^sub>v unit_vec (N * m) 0) ^\<^sub>m k * sem N m V u"
proof (induction k)
  case 0
  have "sem N m V u \<in> carrier_mat (N * m) (N * m)" by (rule sem_carrier[OF V g])
  moreover have "grover (N * m) (anc_proj (N * m) 1) (sem N m V u *\<^sub>v unit_vec (N * m) 0) \<in> carrier_mat (N * m) (N * m)"
    unfolding grover_def by (rule mult_carrier_mat[OF minus_carrier_mat[OF one_carrier_mat] minus_carrier_mat[OF smult_carrier_mat[OF proj_set_carrier]]])
  ultimately show ?case by simp
next
  case (Suc k)
  let ?Q = "grover (N * m) (anc_proj (N * m) 1) (sem N m V u *\<^sub>v unit_vec (N * m) 0)"
  have Q: "?Q \<in> carrier_mat (N * m) (N * m)"
    unfolding grover_def by (rule mult_carrier_mat[OF minus_carrier_mat[OF one_carrier_mat] minus_carrier_mat[OF smult_carrier_mat[OF proj_set_carrier]]])
  have U: "sem N m V u \<in> carrier_mat (N * m) (N * m)" by (rule sem_carrier[OF V g])
  have "sem N m V (aa_prog (N * m) u (Suc k)) = ?Q * (?Q ^\<^sub>m k * sem N m V u)"
    using Suc sem_grover_prog[OF V g K] by simp
  also have "\<dots> = ?Q ^\<^sub>m Suc k * sem N m V u"
    using assoc_mult_mat[OF Q pow_carrier_mat[OF Q] U, symmetric] pow_mat_comm[OF Q, of k] by simp
  finally show ?case .
qed

subsection \<open>The amplification theorem\<close>

theorem amplitude_amplification:
  assumes P: "P \<in> carrier_mat K K" "P * P = P" "P\<^sup>\<dagger> = P"
      and psi: "dim_vec psi = K" "\<parallel>psi\<parallel> = 1" and a0: "0 < \<parallel>P *\<^sub>v psi\<parallel>" and a1: "\<parallel>P *\<^sub>v psi\<parallel> < 1"
  obtains \<theta> where "0 < \<theta>" "\<theta> < pi / 2" "sin \<theta> = \<parallel>P *\<^sub>v psi\<parallel>"
    "\<And>k. P *\<^sub>v (grover K P psi ^\<^sub>m k *\<^sub>v psi) = complex_of_real (sin ((2 * real k + 1) * \<theta>) / sin \<theta>) \<cdot>\<^sub>v (P *\<^sub>v psi)"
proof -
  obtain g h \<theta> where g: "dim_vec g = K" and h: "dim_vec h = K" and gg: "\<langle>g|g\<rangle> = 1" and hh: "\<langle>h|h\<rangle> = 1"
      and gh: "\<langle>g|h\<rangle> = 0" and Pg: "P *\<^sub>v g = g" and Ph: "P *\<^sub>v h = 0\<^sub>v K" and t0: "0 < \<theta>" and t1: "\<theta> < pi / 2"
      and st: "sin \<theta> = \<parallel>P *\<^sub>v psi\<parallel>" and pe: "psi = complex_of_real (sin \<theta>) \<cdot>\<^sub>v g + complex_of_real (cos \<theta>) \<cdot>\<^sub>v h"
    by (rule projector_split[OF P psi a0 a1])
  note cd = comb_def[OF P(1) g h gg hh gh Pg Ph]
  have pc: "psi = comb g h (sin \<theta>) (cos \<theta>)" unfolding cd pe ..
  have s0: "0 < sin \<theta>" using st a0 by simp
  have Ppsi: "P *\<^sub>v psi = complex_of_real (sin \<theta>) \<cdot>\<^sub>v g"
  proof -
    have "P *\<^sub>v psi = comb g h (sin \<theta>) 0" unfolding pc by (rule P_comb[OF P(1) g h gg hh gh Pg Ph])
    thus ?thesis unfolding cd using g h by (intro eq_vecI) simp_all
  qed
  show ?thesis
  proof (rule that[OF t0 t1 st])
    fix k
    have "P *\<^sub>v (grover K P psi ^\<^sub>m k *\<^sub>v psi) = comb g h (sin ((2 * real k + 1) * \<theta>)) 0"
      unfolding pc grover_iterate[OF P(1) g h gg hh gh Pg Ph] by (rule P_comb[OF P(1) g h gg hh gh Pg Ph])
    also have "\<dots> = complex_of_real (sin ((2 * real k + 1) * \<theta>) / sin \<theta>) \<cdot>\<^sub>v (P *\<^sub>v psi)"
      unfolding cd Ppsi using g h s0 by (intro eq_vecI) simp_all
    finally show "P *\<^sub>v (grover K P psi ^\<^sub>m k *\<^sub>v psi) = complex_of_real (sin ((2 * real k + 1) * \<theta>) / sin \<theta>) \<cdot>\<^sub>v (P *\<^sub>v psi)" .
  qed
qed

lemma normalize_smult_pos:
  assumes r: "0 < r" and v: "\<parallel>v\<parallel> \<noteq> 0"
  shows "complex_of_real (1 / \<parallel>complex_of_real r \<cdot>\<^sub>v v\<parallel>) \<cdot>\<^sub>v (complex_of_real r \<cdot>\<^sub>v v) = complex_of_real (1 / \<parallel>v\<parallel>) \<cdot>\<^sub>v v"
proof -
  have "\<parallel>complex_of_real r \<cdot>\<^sub>v v\<parallel> = r * \<parallel>v\<parallel>" unfolding cpx_vec_length_smult norm_of_real using r by simp
  thus ?thesis using r v by (intro eq_vecI) simp_all
qed

text \<open>Amplifying a circuit $u$: with $k=\lfloor\pi/(4\theta)\rfloor$ rounds, $\sin\theta=\norm{\mathrm{post1}\,u\ket0}$,
the success probability is at least $1-\sin^2\theta$, the post-selected state is unchanged, and the
oracle is called $(2k+1)\cdot\mathrm{calls}(u)$ times with $k\le\pi/(4\sin\theta)$.\<close>

theorem circuit_amplification:
  assumes V: "V \<in> carrier_mat m m" "unitary V" and g: "gates_ok (N * m) u" and K: "0 < N * m"
      and a0: "0 < \<parallel>post1 (sem N m V u *\<^sub>v unit_vec (N * m) 0)\<parallel>"
      and a1: "\<parallel>post1 (sem N m V u *\<^sub>v unit_vec (N * m) 0)\<parallel> < 1"
  obtains k where
    "1 - \<parallel>post1 (sem N m V u *\<^sub>v unit_vec (N * m) 0)\<parallel>\<^sup>2 \<le> \<parallel>post1 (sem N m V (aa_prog (N * m) u k) *\<^sub>v unit_vec (N * m) 0)\<parallel>\<^sup>2"
    "complex_of_real (1 / \<parallel>post1 (sem N m V (aa_prog (N * m) u k) *\<^sub>v unit_vec (N * m) 0)\<parallel>) \<cdot>\<^sub>v post1 (sem N m V (aa_prog (N * m) u k) *\<^sub>v unit_vec (N * m) 0)
       = complex_of_real (1 / \<parallel>post1 (sem N m V u *\<^sub>v unit_vec (N * m) 0)\<parallel>) \<cdot>\<^sub>v post1 (sem N m V u *\<^sub>v unit_vec (N * m) 0)"
    "calls (aa_prog (N * m) u k) = (2 * k + 1) * calls u"
    "real k \<le> pi / (4 * \<parallel>post1 (sem N m V u *\<^sub>v unit_vec (N * m) 0)\<parallel>)"
proof -
  let ?K = "N * m" and ?U = "sem N m V u"
  let ?psi = "?U *\<^sub>v unit_vec ?K 0"
  have U: "?U \<in> carrier_mat ?K ?K" "unitary ?U" using sem_carrier[OF V g] sem_unitary[OF V g] by simp_all
  have e0: "dim_vec (unit_vec ?K 0) = ?K" by simp
  have dpsi: "dim_vec ?psi = ?K" using U(1) by simp
  have npsi: "\<parallel>?psi\<parallel> = 1" using unitary_vnorm[OF U e0] K by simp
  have Pv: "anc_proj ?K 1 *\<^sub>v v = post1 v" if "dim_vec v = ?K" for v using pflag_mat_mult[OF that] .
  have a0': "0 < \<parallel>anc_proj ?K 1 *\<^sub>v ?psi\<parallel>" and a1': "\<parallel>anc_proj ?K 1 *\<^sub>v ?psi\<parallel> < 1" using a0 a1 Pv[OF dpsi] by simp_all
  obtain \<theta> where t0: "0 < \<theta>" and t1: "\<theta> < pi / 2" and st: "sin \<theta> = \<parallel>anc_proj ?K 1 *\<^sub>v ?psi\<parallel>"
      and it: "\<And>k. anc_proj ?K 1 *\<^sub>v (grover ?K (anc_proj ?K 1) ?psi ^\<^sub>m k *\<^sub>v ?psi) =
                    complex_of_real (sin ((2 * real k + 1) * \<theta>) / sin \<theta>) \<cdot>\<^sub>v (anc_proj ?K 1 *\<^sub>v ?psi)"
    by (rule amplitude_amplification[OF proj_set_carrier proj_set_idem proj_set_dagger dpsi npsi a0' a1']) blast
  define k where "k = nat \<lfloor>pi / (4 * \<theta>)\<rfloor>"
  note r = grover_rounds[OF t0 t1, folded k_def]
  let ?Q = "grover ?K (anc_proj ?K 1) ?psi"
  have Q: "?Q \<in> carrier_mat ?K ?K"
    unfolding grover_def by (rule mult_carrier_mat[OF minus_carrier_mat[OF one_carrier_mat] minus_carrier_mat[OF smult_carrier_mat[OF proj_set_carrier]]])
  have aa: "sem N m V (aa_prog ?K u k) *\<^sub>v unit_vec ?K 0 = ?Q ^\<^sub>m k *\<^sub>v ?psi"
    unfolding sem_aa_prog[OF V g K] using assoc_mult_mat_vec[OF pow_carrier_mat[OF Q] U(1), of "unit_vec ?K 0"] by (simp add: carrier_vecI)
  have dq: "dim_vec (?Q ^\<^sub>m k *\<^sub>v ?psi) = ?K" using carrier_matD(1)[OF pow_carrier_mat[OF Q, of k]] by (simp only: dim_mult_mat_vec)
  have s0: "0 < sin \<theta>" using st a0' by simp
  have post: "post1 (sem N m V (aa_prog ?K u k) *\<^sub>v unit_vec ?K 0) = complex_of_real (sin ((2 * real k + 1) * \<theta>) / sin \<theta>) \<cdot>\<^sub>v post1 ?psi"
    unfolding aa Pv[OF dq, symmetric] Pv[OF dpsi, symmetric] by (rule it)
  have np: "\<parallel>post1 ?psi\<parallel> = sin \<theta>" using st Pv[OF dpsi] by simp
  show ?thesis
  proof (rule that)
    have "\<parallel>post1 (sem N m V (aa_prog ?K u k) *\<^sub>v unit_vec ?K 0)\<parallel> = sin ((2 * real k + 1) * \<theta>)"
      unfolding post cpx_vec_length_smult norm_of_real np using s0 r(3) by simp
    thus "1 - \<parallel>post1 ?psi\<parallel>\<^sup>2 \<le> \<parallel>post1 (sem N m V (aa_prog ?K u k) *\<^sub>v unit_vec ?K 0)\<parallel>\<^sup>2"
      unfolding np using r(1) by simp
    show "complex_of_real (1 / \<parallel>post1 (sem N m V (aa_prog ?K u k) *\<^sub>v unit_vec ?K 0)\<parallel>) \<cdot>\<^sub>v post1 (sem N m V (aa_prog ?K u k) *\<^sub>v unit_vec ?K 0)
          = complex_of_real (1 / \<parallel>post1 ?psi\<parallel>) \<cdot>\<^sub>v post1 ?psi"
      unfolding post by (rule normalize_smult_pos) (use s0 r(3) np in simp_all)
    show "calls (aa_prog ?K u k) = (2 * k + 1) * calls u" by (rule calls_aa_prog)
    have "real k \<le> pi / (4 * \<theta>)" by (rule r(2))
    also have "\<dots> \<le> pi / (4 * sin \<theta>)" using s0 sin_x_le_x[of \<theta>] t0 by (intro divide_left_mono) simp_all
    finally show "real k \<le> pi / (4 * \<parallel>post1 ?psi\<parallel>)" unfolding np .
  qed
qed

subsection \<open>The complete algorithm\<close>

text \<open>State preparation $\mathit{Prep}\ket0=\psi\otimes b\otimes\ket0$ (a fixed gate), the HHL
circuit with oracle $V$, amplitude amplification and post-selection on the ancilla.\<close>

definition hhl_full_prog :: "complex Matrix.mat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> qcirc" where
  "hhl_full_prog A t0 N C Prep = Seq (Gate Prep) (hhl_prog N (dim_row A * 2) (hhl_rot_stage A t0 N C))"

lemma calls_hhl_full_prog: "calls (hhl_full_prog A t0 N C Prep) = 2 * (N - 1)"
  by (simp add: hhl_full_prog_def calls_hhl_prog)

theorem hhl_complete:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and t0: "0 < t0" and N: "2 \<le> N"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" "\<parallel>b\<parallel> = 1" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real N"
      and V: "V \<in> carrier_mat n n" "unitary V" and Vc: "op_close n \<eta> V (evolution A t0)" and eta: "0 \<le> \<eta>"
      and Prep: "Prep \<in> carrier_mat (N * (n * 2)) (N * (n * 2))" "unitary Prep"
        "Prep *\<^sub>v unit_vec (N * (n * 2)) 0 = tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0))"
      and small: "\<epsilon> + 2 * real (N - 1) * \<eta> \<le> C * t0 / pi"
  defines "out \<equiv> sem N (n * 2) (V \<Otimes> 1\<^sub>m 2) (hhl_full_prog A t0 N C Prep) *\<^sub>v unit_vec (N * (n * 2)) 0"
      and "x \<equiv> herm_inv A *\<^sub>v b"
  shows "C * t0 / pi \<le> \<parallel>post1 out\<parallel>"
    and "\<parallel>complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out -
          tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x) (unit_vec 2 1))\<parallel>
         \<le> 2 * (\<epsilon> + 2 * real (N - 1) * \<eta>) / (C * \<parallel>x\<parallel>)"
    and "\<parallel>post1 out\<parallel> < 1 \<Longrightarrow> \<exists>k.
           1 - \<parallel>post1 out\<parallel>\<^sup>2 \<le> \<parallel>post1 (sem N (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog (N * (n * 2)) (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec (N * (n * 2)) 0)\<parallel>\<^sup>2
         \<and> complex_of_real (1 / \<parallel>post1 (sem N (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog (N * (n * 2)) (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec (N * (n * 2)) 0)\<parallel>) \<cdot>\<^sub>v
             post1 (sem N (n * 2) (V \<Otimes> 1\<^sub>m 2) (aa_prog (N * (n * 2)) (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec (N * (n * 2)) 0)
           = complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out
         \<and> calls (aa_prog (N * (n * 2)) (hhl_full_prog A t0 N C Prep) k) = (2 * k + 1) * (2 * (N - 1))
         \<and> real k \<le> pi\<^sup>2 / (4 * C * t0)"
proof -
  let ?K = "N * (n * 2)" and ?O = "V \<Otimes> 1\<^sub>m 2"
  let ?I = "tensor_vec (win_state N)
             (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
              tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))"
  let ?\<delta> = "\<epsilon> + 2 * real (N - 1) * \<eta>"
  have N0: "0 < N" using N by simp
  have nA: "dim_row A = n" using A(1) by simp
  have K0: "0 < ?K"
  proof -
    have "n \<noteq> 0"
    proof
      assume "n = 0"
      hence "\<parallel>b\<parallel> = 0" using b(1) by (simp add: cpx_vec_length_def)
      thus False using b(2) by simp
    qed
    thus ?thesis using N0 by simp
  qed
  have O: "?O \<in> carrier_mat (n * 2) (n * 2)" "unitary ?O" using V by (auto intro!: carrier_matI tensor_mat_unitary_one_right)
  have g: "gates_ok ?K (hhl_full_prog A t0 N C Prep)"
    using gates_ok_pe_prog[OF N0, of "n * 2"] gates_ok_adj[OF gates_ok_pe_prog[OF N0, of "n * 2"]] hhl_rot_stage_ok[of A t0 N C] Prep(1,2)
    unfolding hhl_full_prog_def hhl_prog_def nA by simp
  have Sc: "hhl_sim A t0 N C V \<in> carrier_mat ?K ?K"
  proof -
    have "gates_ok ?K (hhl_prog N (n * 2) (hhl_rot_stage A t0 N C))" using g unfolding hhl_full_prog_def nA by simp
    thus ?thesis unfolding hhl_sim_def nA by (rule sem_carrier[OF O])
  qed
  have out: "out = hhl_sim A t0 N C V *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0))"
  proof -
    have e0: "unit_vec ?K 0 \<in> carrier_vec ?K" by (rule carrier_vecI) simp
    show ?thesis unfolding out_def hhl_full_prog_def sem.simps
      using assoc_mult_mat_vec[OF Sc[unfolded hhl_sim_def nA] Prep(1) e0] Prep(3) by (simp add: hhl_sim_def nA)
  qed
  have close: "\<parallel>out - ?I\<parallel> \<le> ?\<delta>"
    using hhl_sim_window_error[OF A t0 N C th lmin spec b(1) e NQ V Vc eta] unfolding out[symmetric] b(2) by simp
  have dout: "dim_vec out = ?K" using Sc out by simp
  have lmin0: "0 < lmin"
  proof -
    have "0 < 2 * C / \<theta>" using C th by simp
    thus ?thesis using lmin by linarith
  qed
  have z: "0 \<notin> herm_spectrum A" using spec lmin0 by force
  have Hi: "herm_inv A \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
  have Ax: "A *\<^sub>v x = b"
    unfolding x_def using assoc_mult_mat_vec[OF A(1) Hi carrier_vecI[OF b(1)], symmetric] herm_inv(2)[OF A z]
      one_mult_mat_vec[OF carrier_vecI[OF b(1)]] by simp
  have x0: "x \<noteq> 0\<^sub>v n"
  proof
    assume "x = 0\<^sub>v n"
    moreover have "A *\<^sub>v 0\<^sub>v n = 0\<^sub>v n" using A(1) by (intro eq_vecI) (simp_all add: scalar_prod_def)
    ultimately have "A *\<^sub>v x = 0\<^sub>v n" by simp
    hence "b = 0\<^sub>v n" using Ax by simp
    thus False using b(2) by (simp add: cpx_vec_length_def)
  qed
  define \<Lambda> where "\<Lambda> = pi / (2 * t0)"
  have Lam: "\<Lambda> = pi / (2 * t0)" by (rule \<Lambda>_def)
  have Cx: "2 * C * t0 / pi \<le> C * \<parallel>x\<parallel>"
  proof -
    have sp: "C \<le> \<bar>l\<bar> \<and> \<bar>l\<bar> \<le> \<Lambda>" if "l \<in> herm_spectrum A" for l
    proof -
      have "lmin \<le> l" "t0 * l \<le> pi / 2" using spec[OF that] by simp_all
      moreover have "C \<le> lmin"
      proof -
        have "C \<le> 2 * C / \<theta>" using C th by (simp add: field_simps)
        thus ?thesis using lmin by linarith
      qed
      ultimately show ?thesis unfolding \<Lambda>_def using t0 C by (auto simp: field_simps)
    qed
    have "(C / \<Lambda>)\<^sup>2 * Re \<langle>b|b\<rangle> \<le> C\<^sup>2 * Re \<langle>x|x\<rangle>" unfolding x_def by (rule hhl_success_bound[OF A C sp b(1)])
    hence "(C / \<Lambda>)\<^sup>2 \<le> (C * \<parallel>x\<parallel>)\<^sup>2" unfolding vnorm_Re_inner b(2) by (simp add: power_mult_distrib)
    hence "C / \<Lambda> \<le> C * \<parallel>x\<parallel>" by (rule power2_le_imp_le) (use C vnorm_ge0[of x] in simp)
    thus ?thesis unfolding \<Lambda>_def using t0 by (simp add: field_simps)
  qed
  have Ct: "0 < C * t0 / pi" using C t0 by simp
  note ro = hhl_readout[OF A N C b(1) x0[unfolded x_def] dout close]
  have p_lo: "C * t0 / pi \<le> \<parallel>post1 out\<parallel>" using ro(1) Cx small unfolding x_def by linarith
  show "C * t0 / pi \<le> \<parallel>post1 out\<parallel>" by (rule p_lo)
  have dlt: "?\<delta> < C * \<parallel>x\<parallel>" using Cx small Ct by linarith
  show "\<parallel>complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out -
          tensor_vec (win_state N) (tensor_vec (complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x) (unit_vec 2 1))\<parallel>
         \<le> 2 * ?\<delta> / (C * \<parallel>x\<parallel>)" using ro(2) dlt unfolding x_def by simp
  assume p1: "\<parallel>post1 out\<parallel> < 1"
  have p0: "0 < \<parallel>post1 out\<parallel>" using p_lo Ct by linarith
  obtain k where k1: "1 - \<parallel>post1 out\<parallel>\<^sup>2 \<le> \<parallel>post1 (sem N (n * 2) ?O (aa_prog ?K (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec ?K 0)\<parallel>\<^sup>2"
      and k2: "complex_of_real (1 / \<parallel>post1 (sem N (n * 2) ?O (aa_prog ?K (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec ?K 0)\<parallel>) \<cdot>\<^sub>v
             post1 (sem N (n * 2) ?O (aa_prog ?K (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec ?K 0)
           = complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out"
      and k3: "calls (aa_prog ?K (hhl_full_prog A t0 N C Prep) k) = (2 * k + 1) * calls (hhl_full_prog A t0 N C Prep)"
      and k4: "real k \<le> pi / (4 * \<parallel>post1 out\<parallel>)"
    by (rule circuit_amplification[OF O g K0 p0[unfolded out_def] p1[unfolded out_def], folded out_def])
  have "pi / (4 * \<parallel>post1 out\<parallel>) \<le> pi / (4 * (C * t0 / pi))" using p_lo Ct p0 C t0 by (intro divide_left_mono) simp_all
  also have "\<dots> = pi\<^sup>2 / (4 * C * t0)" using C t0 by (simp add: field_simps power2_eq_square)
  finally have "real k \<le> pi\<^sup>2 / (4 * C * t0)" using k4 by linarith
  thus "\<exists>k. 1 - \<parallel>post1 out\<parallel>\<^sup>2 \<le> \<parallel>post1 (sem N (n * 2) ?O (aa_prog ?K (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec ?K 0)\<parallel>\<^sup>2
         \<and> complex_of_real (1 / \<parallel>post1 (sem N (n * 2) ?O (aa_prog ?K (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec ?K 0)\<parallel>) \<cdot>\<^sub>v
             post1 (sem N (n * 2) ?O (aa_prog ?K (hhl_full_prog A t0 N C Prep) k) *\<^sub>v unit_vec ?K 0)
           = complex_of_real (1 / \<parallel>post1 out\<parallel>) \<cdot>\<^sub>v post1 out
         \<and> calls (aa_prog ?K (hhl_full_prog A t0 N C Prep) k) = (2 * k + 1) * (2 * (N - 1))
         \<and> real k \<le> pi\<^sup>2 / (4 * C * t0)"
    using k1 k2 k3[unfolded calls_hhl_full_prog] by (intro exI[of _ k] conjI)
qed

end
