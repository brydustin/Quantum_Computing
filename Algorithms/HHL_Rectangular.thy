theory HHL_Rectangular
  imports HHL_Reduction
begin


section \<open>Rectangular matrices\<close>

text \<open>App.~A4 of the paper: for $A\in\C^{M\times N}$ the algorithm runs on
$H=\left(\begin{smallmatrix}0&A\\A^*&0\end{smallmatrix}\right)$ and inverts it on its non-zero eigenspaces.
The pseudo-inverse is $H^+=$ \<^const>\<open>herm_inv\<close> $H=g(H)$ with $g(\lambda)=1/\lambda$, since
$1/0=0$ in HOL; the input $b\oplus0$ is mapped to $0\oplus x$ where $x$ solves the normal equations $A^*Ax=A^*b$ and lies in
the range of $A^*$: the least-squares solution, of minimum norm.\<close>

abbreviation parity :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "parity M N \<equiv> sign_diag (M + N) (\<lambda>i. M \<le> i)"

definition inv_sq :: "real \<Rightarrow> complex" where
  "inv_sq l = (if l = 0 then 0 else complex_of_real (1 / l\<^sup>2))"
definition nz_ind :: "real \<Rightarrow> complex" where
  "nz_ind l = (if l = (0::real) then 0 else (1::complex))"

lemma append_vec_eq_lower:
  assumes "a @\<^sub>v c = a' @\<^sub>v c'" "dim_vec a = M" "dim_vec a' = M" "dim_vec c = N" "dim_vec c' = N"
  shows "c = c'"
proof (rule eq_vecI)
  fix i assume "i < dim_vec c'"
  hence i: "i < N" using assms by simp
  have "(a @\<^sub>v c) $ (M + i) = (a' @\<^sub>v c') $ (M + i)" using assms(1) by simp
  thus "c $ i = c' $ i" using assms(2-5) i by (simp add: index_append_vec)
qed (use assms in simp)

lemma append_vec_eq_upper:
  assumes "a @\<^sub>v c = a' @\<^sub>v c'" "dim_vec a = M" "dim_vec a' = M" "dim_vec c = N" "dim_vec c' = N"
  shows "a = a'"
proof (rule eq_vecI)
  fix i assume "i < dim_vec a'"
  hence i: "i < M" using assms by simp
  have "(a @\<^sub>v c) $ i = (a' @\<^sub>v c') $ i" using assms(1) by simp
  thus "a $ i = a' $ i" using assms(2-5) i by (simp add: index_append_vec)
qed (use assms in simp)

lemma vnorm_pythagoras:
  assumes u: "dim_vec u = n" and w: "dim_vec w = n" and o: "\<langle>u|w\<rangle> = 0"
  shows "\<parallel>u + w\<parallel>\<^sup>2 = \<parallel>u\<parallel>\<^sup>2 + \<parallel>w\<parallel>\<^sup>2"
proof -
  have rev: "\<langle>w|u\<rangle> = 0" using inner_prod_cnj[of u w] o u w by simp
  have "complex_of_real (\<parallel>u + w\<parallel>\<^sup>2) = \<langle>u + w|u + w\<rangle>" by (rule cpx_vec_length_inner_prod)
  also have "\<dots> = \<langle>u|u\<rangle> + \<langle>w|w\<rangle>" using No_Cloning.inner_prod_expand[of u w u w] u w o rev by simp
  finally have "complex_of_real (\<parallel>u + w\<parallel>\<^sup>2) = complex_of_real (\<parallel>u\<parallel>\<^sup>2 + \<parallel>w\<parallel>\<^sup>2)" unfolding cpx_vec_length_inner_prod[symmetric] by simp
  thus ?thesis by (simp only: of_real_eq_iff)
qed

context
  fixes A :: "complex Matrix.mat" and M N :: nat
  assumes A: "A \<in> carrier_mat M N"
begin

abbreviation "Hd \<equiv> herm_embed A"

text \<open>Eigenvectors of $H$ from singular pairs, and the kernel.\<close>

lemma H_singular_pair:
  assumes u: "dim_vec u = M" and v: "dim_vec v = N"
      and Av: "A *\<^sub>v v = complex_of_real s \<cdot>\<^sub>v u" and Au: "A\<^sup>\<dagger> *\<^sub>v u = complex_of_real s \<cdot>\<^sub>v v"
  shows "Hd *\<^sub>v (u @\<^sub>v v) = complex_of_real s \<cdot>\<^sub>v (u @\<^sub>v v)"
    and "Hd *\<^sub>v (u @\<^sub>v (- v)) = complex_of_real (- s) \<cdot>\<^sub>v (u @\<^sub>v (- v))"
proof -
  show "Hd *\<^sub>v (u @\<^sub>v v) = complex_of_real s \<cdot>\<^sub>v (u @\<^sub>v v)"
    unfolding herm_embed_mult[OF A u v] Av Au by (intro eq_vecI) (auto simp: u v)
  have nv: "dim_vec (- v) = N" using v by simp
  have "A *\<^sub>v (- v) = - (A *\<^sub>v v)" using A v by (intro eq_vecI) (simp_all add: scalar_prod_def sum_negf)
  hence "A *\<^sub>v (- v) = - (complex_of_real s \<cdot>\<^sub>v u)" unfolding Av .
  thus "Hd *\<^sub>v (u @\<^sub>v (- v)) = complex_of_real (- s) \<cdot>\<^sub>v (u @\<^sub>v (- v))"
    unfolding herm_embed_mult[OF A u nv] Au by (intro eq_vecI) (auto simp: u v)
qed

lemma H_kernel: "dim_vec w = N \<Longrightarrow> A *\<^sub>v w = 0\<^sub>v M \<Longrightarrow> Hd *\<^sub>v (0\<^sub>v M @\<^sub>v w) = 0\<^sub>v (M + N)"
proof -
  assume w: "dim_vec w = N" and Aw: "A *\<^sub>v w = 0\<^sub>v M"
  have "A\<^sup>\<dagger> *\<^sub>v 0\<^sub>v M = 0\<^sub>v N" using A by (intro eq_vecI) (simp_all add: scalar_prod_def)
  thus ?thesis unfolding herm_embed_mult[OF A _ w, of "0\<^sub>v M", simplified] Aw by (intro eq_vecI) simp_all
qed


abbreviation "J \<equiv> parity M N"

lemma parity_mult: "dim_vec v = M + N \<Longrightarrow> J *\<^sub>v v = Matrix.vec (M + N) (\<lambda>i. (if i < M then 1 else - 1) * v $ i)"
  by (intro eq_vecI) (auto simp: sign_diag_def mat_diag_def scalar_prod_def if_distrib[of "\<lambda>x. x * _"] sum.delta cong: if_cong)

lemma parity_parity: "dim_vec v = M + N \<Longrightarrow> J *\<^sub>v (J *\<^sub>v v) = v"
  by (intro eq_vecI) (simp_all add: parity_mult)

lemma H_entry_zero:
  assumes r: "r < M + N" and s: "s < M + N" and rs: "(r < M) = (s < M)"
  shows "Hd $$ (r, s) = 0"
proof -
  have e: "Hd $$ (r, s) = (if r < M then if s < M then 0\<^sub>m M M $$ (r, s) else A $$ (r, s - M)
                         else if s < M then (A\<^sup>\<dagger>) $$ (r - M, s) else 0\<^sub>m N N $$ (r - M, s - M))"
    unfolding herm_embed_def using A r s by (subst index_mat_four_block) simp_all
  show ?thesis unfolding e using r s rs by auto
qed

lemma H_anti: "dim_vec v = M + N \<Longrightarrow> Hd *\<^sub>v (J *\<^sub>v v) = - (J *\<^sub>v (Hd *\<^sub>v v))"
proof (rule eq_vecI)
  assume v: "dim_vec v = M + N"
  fix r assume "r < dim_vec (- (J *\<^sub>v (Hd *\<^sub>v v)))"
  hence r: "r < M + N" using sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] by simp
  have dHv: "dim_vec (Hd *\<^sub>v v) = M + N" using herm_embed_carrier[OF A] by simp
  have "(Hd *\<^sub>v (J *\<^sub>v v)) $ r = (\<Sum>s<M + N. Hd $$ (r, s) * ((if s < M then 1 else - 1) * v $ s))"
    using r herm_embed_carrier[OF A] v by (simp add: parity_mult scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>s<M + N. - ((if r < M then 1 else - 1) * (Hd $$ (r, s) * v $ s)))"
  proof (rule sum.cong[OF refl])
    fix s assume "s \<in> {..<M + N}"
    hence s: "s < M + N" by simp
    show "Hd $$ (r, s) * ((if s < M then 1 else - 1) * v $ s) = - ((if r < M then 1 else - 1) * (Hd $$ (r, s) * v $ s))"
    proof (cases "(r < M) = (s < M)")
      case True thus ?thesis using H_entry_zero[OF r s True] by simp
    next
      case False thus ?thesis by auto
    qed
  qed
  also have "\<dots> = (- (J *\<^sub>v (Hd *\<^sub>v v))) $ r"
    using r herm_embed_carrier[OF A] v dHv by (simp add: parity_mult scalar_prod_def atLeast0LessThan sum_negf sum_distrib_left)
  finally show "(Hd *\<^sub>v (J *\<^sub>v v)) $ r = (- (J *\<^sub>v (Hd *\<^sub>v v))) $ r" .
qed (use herm_embed_carrier[OF A] sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] in simp)

text \<open>$Jg(H)J=g(-H)$; for even $g$, $g(H)$ commutes with $J$.\<close>

lemma mat_fun_parity:
  shows "mat_fun g Hd = J * mat_fun (\<lambda>l. g (- l)) Hd * J"
proof (rule mat_fun_eqI[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]])
  let ?G = "mat_fun (\<lambda>l. g (- l)) Hd"
  have G: "?G \<in> carrier_mat (M + N) (M + N)" by (rule mat_fun_carrier[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]])
  show "J * ?G * J \<in> carrier_mat (M + N) (M + N)" using G sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] by simp
  show "acts_on_eigenvectors Hd g (J * ?G * J)" unfolding acts_on_eigenvectors_def
  proof (intro allI impI)
    fix u l assume u: "dim_vec u = dim_row Hd" and ev: "Hd *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
    have u': "dim_vec u = M + N" using u herm_embed_carrier[OF A] by simp
    have uc: "u \<in> carrier_vec (M + N)" by (rule carrier_vecI[OF u'])
    have Ju: "dim_vec (J *\<^sub>v u) = M + N" using sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] by simp
    have evJ: "Hd *\<^sub>v (J *\<^sub>v u) = complex_of_real (- l) \<cdot>\<^sub>v (J *\<^sub>v u)"
    proof -
      have "Hd *\<^sub>v (J *\<^sub>v u) = - (J *\<^sub>v (complex_of_real l \<cdot>\<^sub>v u))" unfolding H_anti[OF u'] ev ..
      also have "J *\<^sub>v (complex_of_real l \<cdot>\<^sub>v u) = complex_of_real l \<cdot>\<^sub>v (J *\<^sub>v u)" by (rule mult_mat_vec[OF sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] uc])
      finally show ?thesis by (intro eq_vecI) (use sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] in simp_all)
    qed
    have "?G *\<^sub>v (J *\<^sub>v u) = g (- (- l)) \<cdot>\<^sub>v (J *\<^sub>v u)" by (rule mat_fun_eigen[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A] Ju evJ])
    hence gJ: "?G *\<^sub>v (J *\<^sub>v u) = g l \<cdot>\<^sub>v (J *\<^sub>v u)" by simp
    have "(J * ?G * J) *\<^sub>v u = J *\<^sub>v (?G *\<^sub>v (J *\<^sub>v u))"
      using assoc_mult_mat_vec[OF mult_carrier_mat[OF sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] G] sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] uc] assoc_mult_mat_vec[OF sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] G carrier_vecI[OF Ju]] by simp
    also have "\<dots> = g l \<cdot>\<^sub>v (J *\<^sub>v (J *\<^sub>v u))" unfolding gJ by (rule mult_mat_vec[OF sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] carrier_vecI[OF Ju]])
    also have "J *\<^sub>v (J *\<^sub>v u) = u" by (rule parity_parity[OF u'])
    finally show "(J * ?G * J) *\<^sub>v u = g l \<cdot>\<^sub>v u" .
  qed
qed

lemma even_fun_upper:
  assumes even: "\<And>l. g (- l) = g l" and b: "dim_vec b = M"
  shows "mat_fun g Hd *\<^sub>v (b @\<^sub>v 0\<^sub>v N) = Matrix.vec M (\<lambda>i. (mat_fun g Hd *\<^sub>v (b @\<^sub>v 0\<^sub>v N)) $ i) @\<^sub>v 0\<^sub>v N"
proof -
  let ?G = "mat_fun g Hd" and ?v = "b @\<^sub>v 0\<^sub>v N"
  have G: "?G \<in> carrier_mat (M + N) (M + N)" by (rule mat_fun_carrier[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]])
  have dv: "dim_vec ?v = M + N" using b by simp
  have Jv: "J *\<^sub>v ?v = ?v" using b by (intro eq_vecI) (simp_all add: parity_mult dv)
  have GJ: "?G = J * ?G * J" using mat_fun_parity[of g] unfolding even .
  have w: "?G *\<^sub>v ?v = J *\<^sub>v (?G *\<^sub>v ?v)"
  proof -
    have "?G *\<^sub>v ?v = (J * ?G * J) *\<^sub>v ?v" using GJ by simp
    also have "\<dots> = J *\<^sub>v (?G *\<^sub>v (J *\<^sub>v ?v))"
      using assoc_mult_mat_vec[OF mult_carrier_mat[OF sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] G] sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] carrier_vecI[OF dv]]
            assoc_mult_mat_vec[OF sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] G carrier_vecI[of "J *\<^sub>v ?v"]] sign_diag_carrier[of "M + N" "\<lambda>i. M \<le> i"] by simp
    finally show ?thesis unfolding Jv .
  qed
  have dw: "dim_vec (?G *\<^sub>v ?v) = M + N" using G by simp
  show ?thesis
  proof (rule eq_vecI)
    fix r assume "r < dim_vec (Matrix.vec M (\<lambda>i. (?G *\<^sub>v ?v) $ i) @\<^sub>v 0\<^sub>v N)"
    hence r: "r < M + N" by simp
    show "(?G *\<^sub>v ?v) $ r = (Matrix.vec M (\<lambda>i. (?G *\<^sub>v ?v) $ i) @\<^sub>v 0\<^sub>v N) $ r"
    proof (cases "r < M")
      case True thus ?thesis using r by simp
    next
      case False
      have "(?G *\<^sub>v ?v) $ r = - ((?G *\<^sub>v ?v) $ r)" using arg_cong[OF w, of "\<lambda>x. x $ r"] r False dw by (simp add: parity_mult)
      hence "(?G *\<^sub>v ?v) $ r = 0" by simp
      thus ?thesis using r False by simp
    qed
  qed (use dw in simp)
qed


lemma pinv_factor: "herm_inv Hd = Hd * mat_fun inv_sq Hd"
proof -
  have "Hd * mat_fun inv_sq Hd = mat_fun complex_of_real Hd * mat_fun inv_sq Hd" using mat_fun_id[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]] by simp
  also have "\<dots> = mat_fun (\<lambda>x. complex_of_real x * inv_sq x) Hd" by (rule mat_fun_mult[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]])
  also have "\<dots> = herm_inv Hd" unfolding herm_inv_def
    by (rule mat_fun_cong[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]]) (auto simp: inv_sq_def power2_eq_square field_simps inverse_eq_divide)
  finally show ?thesis ..
qed

lemma H_pinv: "Hd * herm_inv Hd = mat_fun nz_ind Hd"
proof -
  have "Hd * herm_inv Hd = mat_fun complex_of_real Hd * herm_inv Hd" using mat_fun_id[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]] by simp
  also have "\<dots> = mat_fun (\<lambda>x. complex_of_real x * complex_of_real (inverse x)) Hd"
    unfolding herm_inv_def by (rule mat_fun_mult[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]])
  also have "\<dots> = mat_fun nz_ind Hd" by (rule mat_fun_cong[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]]) (simp add: nz_ind_def flip: of_real_mult)
  finally show ?thesis .
qed

lemma H_nz_ind: "Hd * mat_fun nz_ind Hd = Hd" "mat_fun nz_ind Hd * Hd = Hd"
proof -
  have "Hd * mat_fun nz_ind Hd = mat_fun complex_of_real Hd * mat_fun nz_ind Hd" using mat_fun_id[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]] by simp
  also have "\<dots> = mat_fun (\<lambda>x. complex_of_real x * nz_ind x) Hd" by (rule mat_fun_mult[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]])
  also have "\<dots> = mat_fun complex_of_real Hd" by (rule mat_fun_cong[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]]) (simp add: nz_ind_def)
  finally show "Hd * mat_fun nz_ind Hd = Hd" using mat_fun_id[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]] by simp
  have "mat_fun nz_ind Hd * Hd = mat_fun nz_ind Hd * mat_fun complex_of_real Hd" using mat_fun_id[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]] by simp
  also have "\<dots> = mat_fun (\<lambda>x. nz_ind x * complex_of_real x) Hd" by (rule mat_fun_mult[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]])
  also have "\<dots> = mat_fun complex_of_real Hd" by (rule mat_fun_cong[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]]) (simp add: nz_ind_def)
  finally show "mat_fun nz_ind Hd * Hd = Hd" using mat_fun_id[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]] by simp
qed

text \<open>The pseudo-inverse solution (App.~A4).\<close>

theorem pinv_solution:
  assumes b: "dim_vec b = M"
  obtains x c where "dim_vec x = N" "dim_vec c = M" "herm_inv Hd *\<^sub>v (b @\<^sub>v 0\<^sub>v N) = 0\<^sub>v M @\<^sub>v x" "x = A\<^sup>\<dagger> *\<^sub>v c"
    "A\<^sup>\<dagger> *\<^sub>v (A *\<^sub>v x) = A\<^sup>\<dagger> *\<^sub>v b"
    "\<And>z. dim_vec z = N \<Longrightarrow> A *\<^sub>v z = b \<Longrightarrow> A *\<^sub>v x = b \<and> \<parallel>x\<parallel> \<le> \<parallel>z\<parallel>"
proof -
  let ?v = "b @\<^sub>v 0\<^sub>v N" and ?Q = "mat_fun inv_sq Hd" and ?P = "mat_fun nz_ind Hd"
  have dv: "dim_vec ?v = M + N" using b by simp
  have vc: "?v \<in> carrier_vec (M + N)" by (rule carrier_vecI[OF dv])
  have Qc: "?Q \<in> carrier_mat (M + N) (M + N)" and Pc: "?P \<in> carrier_mat (M + N) (M + N)" using mat_fun_carrier[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]] by blast+
  have Ad: "A\<^sup>\<dagger> \<in> carrier_mat N M" by (rule dagger_carrier[OF A])
  define c where "c = Matrix.vec M (\<lambda>i. (?Q *\<^sub>v ?v) $ i)"
  define p where "p = Matrix.vec M (\<lambda>i. (?P *\<^sub>v ?v) $ i)"
  have dc: "dim_vec c = M" and dp: "dim_vec p = M" by (simp_all add: c_def p_def)
  have Qv: "?Q *\<^sub>v ?v = c @\<^sub>v 0\<^sub>v N" unfolding c_def by (rule even_fun_upper[OF _ b]) (simp add: inv_sq_def)
  have Pv: "?P *\<^sub>v ?v = p @\<^sub>v 0\<^sub>v N" unfolding p_def by (rule even_fun_upper[OF _ b]) (simp add: nz_ind_def)
  define x where "x = A\<^sup>\<dagger> *\<^sub>v c"
  have dx: "dim_vec x = N" unfolding x_def using A by simp
  have A0: "A *\<^sub>v 0\<^sub>v N = 0\<^sub>v M" using A by (intro eq_vecI) (simp_all add: scalar_prod_def)
  have Ad0: "A\<^sup>\<dagger> *\<^sub>v 0\<^sub>v M = 0\<^sub>v N" using A Ad by (intro eq_vecI) (simp_all add: scalar_prod_def)
  have y: "herm_inv Hd *\<^sub>v ?v = 0\<^sub>v M @\<^sub>v x"
  proof -
    have "herm_inv Hd *\<^sub>v ?v = Hd *\<^sub>v (?Q *\<^sub>v ?v)" unfolding pinv_factor by (rule assoc_mult_mat_vec[OF herm_embed_carrier[OF A] Qc vc])
    also have "\<dots> = (A *\<^sub>v 0\<^sub>v N) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v c)" unfolding Qv by (rule herm_embed_mult[OF A dc]) simp
    finally show ?thesis unfolding A0 x_def .
  qed
  have Hy: "Hd *\<^sub>v (0\<^sub>v M @\<^sub>v x) = p @\<^sub>v 0\<^sub>v N"
  proof -
    have "Hd *\<^sub>v (0\<^sub>v M @\<^sub>v x) = Hd *\<^sub>v (herm_inv Hd *\<^sub>v ?v)" unfolding y ..
    also have "\<dots> = (Hd * herm_inv Hd) *\<^sub>v ?v"
      by (rule assoc_mult_mat_vec[OF herm_embed_carrier[OF A] _ vc, symmetric]) (simp add: herm_inv_def mat_fun_carrier[OF herm_embed_carrier[OF A] herm_embed_hermitian[OF A]])
    finally show ?thesis unfolding H_pinv Pv .
  qed
  have Ax: "A *\<^sub>v x = p"
  proof -
    have "(A *\<^sub>v x) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v 0\<^sub>v M) = p @\<^sub>v 0\<^sub>v N" using Hy herm_embed_mult[OF A, of "0\<^sub>v M" x] dx by simp
    thus ?thesis by (rule append_vec_eq_upper[where M = M and N = N]) (use A dx dp Ad in simp_all)
  qed
  have Adp: "A\<^sup>\<dagger> *\<^sub>v p = A\<^sup>\<dagger> *\<^sub>v b"
  proof -
    have "Hd *\<^sub>v (?P *\<^sub>v ?v) = (Hd * ?P) *\<^sub>v ?v" by (rule assoc_mult_mat_vec[OF herm_embed_carrier[OF A] Pc vc, symmetric])
    hence "Hd *\<^sub>v (p @\<^sub>v 0\<^sub>v N) = Hd *\<^sub>v ?v" unfolding Pv H_nz_ind(1) .
    moreover have "Hd *\<^sub>v (p @\<^sub>v 0\<^sub>v N) = (A *\<^sub>v 0\<^sub>v N) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v p)" by (rule herm_embed_mult[OF A dp]) simp
    moreover have "Hd *\<^sub>v ?v = (A *\<^sub>v 0\<^sub>v N) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v b)" by (rule herm_embed_mult[OF A b]) simp
    ultimately have "(A *\<^sub>v 0\<^sub>v N) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v p) = (A *\<^sub>v 0\<^sub>v N) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v b)" by simp
    thus ?thesis by (rule append_vec_eq_lower[where M = M and N = N]) (use A Ad dp b in simp_all)
  qed
  show ?thesis
  proof (rule that[OF dx dc y x_def])
    show "A\<^sup>\<dagger> *\<^sub>v (A *\<^sub>v x) = A\<^sup>\<dagger> *\<^sub>v b" unfolding Ax by (rule Adp)
    fix z assume dz: "dim_vec z = N" and Az: "A *\<^sub>v z = b"
    have pb: "p = b"
    proof -
      have as: "?P *\<^sub>v (Hd *\<^sub>v (0\<^sub>v M @\<^sub>v z)) = (?P * Hd) *\<^sub>v (0\<^sub>v M @\<^sub>v z)"
        by (rule assoc_mult_mat_vec[OF Pc herm_embed_carrier[OF A] carrier_vecI, symmetric]) (use dz in simp)
      have Hz: "Hd *\<^sub>v (0\<^sub>v M @\<^sub>v z) = (A *\<^sub>v z) @\<^sub>v (A\<^sup>\<dagger> *\<^sub>v 0\<^sub>v M)" by (rule herm_embed_mult[OF A _ dz]) simp
      hence Hz': "Hd *\<^sub>v (0\<^sub>v M @\<^sub>v z) = ?v" unfolding Az Ad0 .
      from as have "?P *\<^sub>v ?v = Hd *\<^sub>v (0\<^sub>v M @\<^sub>v z)" unfolding H_nz_ind(2) Hz' .
      also have "\<dots> = ?v" by (rule Hz')
      finally have "p @\<^sub>v 0\<^sub>v N = b @\<^sub>v 0\<^sub>v N" unfolding Pv .
      thus ?thesis by (rule append_vec_eq_upper[where M = M and N = N]) (use dp b in simp_all)
    qed
    have Axb: "A *\<^sub>v x = b" unfolding Ax pb ..
    have orth: "\<langle>x|z - x\<rangle> = 0"
    proof -
      have dzx: "dim_vec (z - x) = N" using dx by simp
      have "\<langle>x|z - x\<rangle> = \<langle>A\<^sup>\<dagger> *\<^sub>v c|z - x\<rangle>" unfolding x_def ..
      also have "\<dots> = \<langle>c|A *\<^sub>v (z - x)\<rangle>"
        using inner_prod_adjoint_swap[OF A dc dzx] by simp
      also have "A *\<^sub>v (z - x) = A *\<^sub>v z - A *\<^sub>v x" by (rule mult_minus_distrib_mat_vec[OF A carrier_vecI carrier_vecI]) (use dz dx in simp_all)
      also have "A *\<^sub>v z - A *\<^sub>v x = 0\<^sub>v M" unfolding Az Axb using b by (intro eq_vecI) simp_all
      finally show ?thesis by (simp add: Quantum.inner_prod_def)
    qed
    have "\<parallel>z\<parallel>\<^sup>2 = \<parallel>x\<parallel>\<^sup>2 + \<parallel>z - x\<parallel>\<^sup>2"
    proof -
      have zx: "z = x + (z - x)" using dz dx by (intro eq_vecI) simp_all
      have dzx: "dim_vec (z - x) = N" using dx by simp
      have rev: "\<langle>z - x|x\<rangle> = 0" using inner_prod_cnj[of x "z - x"] orth dzx dx by simp
      have "complex_of_real (\<parallel>z\<parallel>\<^sup>2) = \<langle>x + (z - x)|x + (z - x)\<rangle>" unfolding cpx_vec_length_inner_prod using zx by simp
      also have "\<dots> = \<langle>x|x\<rangle> + \<langle>z - x|z - x\<rangle>"
        using No_Cloning.inner_prod_expand[of x "z - x" x "z - x"] dx dzx orth rev by simp
      finally have "complex_of_real (\<parallel>z\<parallel>\<^sup>2) = complex_of_real (\<parallel>x\<parallel>\<^sup>2 + \<parallel>z - x\<parallel>\<^sup>2)" unfolding cpx_vec_length_inner_prod[symmetric] by simp
      thus ?thesis by (simp only: of_real_eq_iff)
    qed
    hence "\<parallel>x\<parallel>\<^sup>2 \<le> \<parallel>z\<parallel>\<^sup>2" by simp
    hence "\<parallel>x\<parallel> \<le> \<parallel>z\<parallel>" by (rule power2_le_imp_le) (simp add: vnorm_ge0)
    thus "A *\<^sub>v x = b \<and> \<parallel>x\<parallel> \<le> \<parallel>z\<parallel>" using Axb by simp
  qed
qed

text \<open>Over-constrained case ($M\ge N$): the normal equations make $Ax$ the orthogonal projection of $b$
onto the range of $A$, so $x$ is a least-squares solution.\<close>

lemma normal_eq_least_squares:
  assumes b: "dim_vec b = M" and x: "dim_vec x = N" and ne: "A\<^sup>\<dagger> *\<^sub>v (A *\<^sub>v x) = A\<^sup>\<dagger> *\<^sub>v b"
      and z: "dim_vec z = N"
  shows "\<parallel>A *\<^sub>v x - b\<parallel> \<le> \<parallel>A *\<^sub>v z - b\<parallel>"
proof -
  let ?r = "A *\<^sub>v x - b" and ?d = "A *\<^sub>v (z - x)"
  have Ad: "A\<^sup>\<dagger> \<in> carrier_mat N M" by (rule dagger_carrier[OF A])
  have dr: "dim_vec ?r = M" and dd: "dim_vec ?d = M" using A b by simp_all
  have dzx: "dim_vec (z - x) = N" using x by simp
  have Azx: "?d = A *\<^sub>v z - A *\<^sub>v x"
    by (rule mult_minus_distrib_mat_vec[OF A carrier_vecI carrier_vecI]) (use z x in simp_all)
  have split: "A *\<^sub>v z - b = ?r + ?d" unfolding Azx using A b by (intro eq_vecI) simp_all
  have res: "A\<^sup>\<dagger> *\<^sub>v ?r = 0\<^sub>v N"
  proof -
    have "A\<^sup>\<dagger> *\<^sub>v ?r = A\<^sup>\<dagger> *\<^sub>v (A *\<^sub>v x) - A\<^sup>\<dagger> *\<^sub>v b"
      by (rule mult_minus_distrib_mat_vec[OF Ad carrier_vecI carrier_vecI]) (use A b in simp_all)
    also have "\<dots> = 0\<^sub>v N" unfolding ne using A by (intro eq_vecI) simp_all
    finally show ?thesis .
  qed
  have o: "\<langle>?r|?d\<rangle> = 0"
  proof -
    have "\<langle>A\<^sup>\<dagger> *\<^sub>v ?r|z - x\<rangle> = \<langle>?r|?d\<rangle>" using inner_prod_adjoint_swap[OF A dr dzx] by simp
    hence "\<langle>0\<^sub>v N|z - x\<rangle> = \<langle>?r|?d\<rangle>" unfolding res .
    moreover have "\<langle>0\<^sub>v N|z - x\<rangle> = 0" using x by (simp add: Quantum.inner_prod_def)
    ultimately show ?thesis by simp
  qed
  have "\<parallel>A *\<^sub>v z - b\<parallel>\<^sup>2 = \<parallel>?r\<parallel>\<^sup>2 + \<parallel>?d\<parallel>\<^sup>2" unfolding split by (rule vnorm_pythagoras[OF dr dd o])
  hence "\<parallel>?r\<parallel>\<^sup>2 \<le> \<parallel>A *\<^sub>v z - b\<parallel>\<^sup>2" by simp
  thus ?thesis by (rule power2_le_imp_le) (simp add: vnorm_ge0)
qed

end

end
