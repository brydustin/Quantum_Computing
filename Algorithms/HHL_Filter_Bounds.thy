theory HHL_Filter_Bounds
  imports HHL_Filter
begin

section \<open>Theorem 1 of the HHL paper for every right-hand side\<close>

text \<open>The error vectors of distinct eigenvectors are orthogonal, also after post-selecting the
flag, so the eigenvector bounds of \<open>HHL_Filter\<close> extend to every $b$ with no loss.  This gives
all three parts of Theorem 1 of the paper: (1) $\norm{(\tilde U-U)b}=O(\kappa/t)\norm b$, (2) the state
post-selected on $\{\mathrm{well},\mathrm{ill}\}$ is within $O(\kappa/t)$ of the ideal one, (3) if $b$ has
no ill-conditioned component the state post-selected on $\ket{\mathrm{well}}$ is within $O(\kappa/t)$
of $f(A)b/\norm{f(A)b}$, which is $\propto A^{-1}b$ when $A$ is well conditioned; here $t=Nt_0$ is
the total evolution time.  Householder reflections provide the flag gates.\<close>

subsection \<open>Every right-hand side\<close>

text \<open>$b\mapsto a\otimes\sum_{c<3}H_c\,b\otimes\ket c$ as an $(\dim a\cdot3n)\times n$ matrix.\<close>

definition lift3 :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> (nat \<Rightarrow> complex Matrix.mat) \<Rightarrow> complex Matrix.mat" where
  "lift3 n a H = Matrix.mat (dim_vec a * (n * 3)) n
     (\<lambda>(r, s). a $ (r div (n * 3)) * H (r mod (n * 3) mod 3) $$ (r mod (n * 3) div 3, s))"

lemma lift3_carrier [simp]: "lift3 n a H \<in> carrier_mat (dim_vec a * (n * 3)) n"
  by (simp add: lift3_def)

lemma lift3_mult_vec:
  assumes H: "\<And>c. c < 3 \<Longrightarrow> H c \<in> carrier_mat n n" and v: "dim_vec v = n"
  shows "lift3 n a H *\<^sub>v v = tensor_vec a (Matrix.vec (n * 3) (\<lambda>j. (H (j mod 3) *\<^sub>v v) $ (j div 3)))"
proof (rule eq_vecI)
  let ?z = "Matrix.vec (n * 3) (\<lambda>j. (H (j mod 3) *\<^sub>v v) $ (j div 3))"
  have dz: "dim_vec ?z = n * 3" by simp
  show "dim_vec (lift3 n a H *\<^sub>v v) = dim_vec (tensor_vec a ?z)" using tensor_vec_dim[OF refl dz] by (simp add: lift3_def)
  fix r assume "r < dim_vec (tensor_vec a ?z)"
  hence r: "r < dim_vec a * (n * 3)" using tensor_vec_dim[OF refl dz] by simp
  have n3: "0 < n * 3" using r by (cases "n * 3") simp_all
  have j: "r mod (n * 3) < n * 3" using n3 by simp
  have c: "r mod (n * 3) mod 3 < 3" by simp
  have i: "r mod (n * 3) div 3 < n" using j by (simp add: less_mult_imp_div_less)
  have "(lift3 n a H *\<^sub>v v) $ r = (\<Sum>s<n. a $ (r div (n * 3)) * H (r mod (n * 3) mod 3) $$ (r mod (n * 3) div 3, s) * v $ s)"
    using r v by (simp add: lift3_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = a $ (r div (n * 3)) * (H (r mod (n * 3) mod 3) *\<^sub>v v) $ (r mod (n * 3) div 3)"
    using H[OF c] i v by (simp add: scalar_prod_def atLeast0LessThan sum_distrib_left mult_ac)
  also have "\<dots> = tensor_vec a ?z $ r" using tensor_vec_index[OF refl dz r] j by simp
  finally show "(lift3 n a H *\<^sub>v v) $ r = tensor_vec a ?z $ r" .
qed

lemma flag_vec_eigen:
  assumes u: "dim_vec u = n"
  shows "Matrix.vec (n * 3) (\<lambda>j. (z (j mod 3) \<cdot>\<^sub>v u) $ (j div 3)) = tensor_vec u (Matrix.vec 3 z)"
proof (rule eq_vecI)
  have dt: "dim_vec (tensor_vec u (Matrix.vec 3 z)) = n * 3" by (rule tensor_vec_dim[OF u]) simp
  show "dim_vec (Matrix.vec (n * 3) (\<lambda>j. (z (j mod 3) \<cdot>\<^sub>v u) $ (j div 3))) = dim_vec (tensor_vec u (Matrix.vec 3 z))" using dt by simp
  fix j assume "j < dim_vec (tensor_vec u (Matrix.vec 3 z))"
  hence j: "j < n * 3" using dt by simp
  have i: "j div 3 < n" using j by (simp add: less_mult_imp_div_less)
  show "Matrix.vec (n * 3) (\<lambda>j. (z (j mod 3) \<cdot>\<^sub>v u) $ (j div 3)) $ j = tensor_vec u (Matrix.vec 3 z) $ j"
    using j i u tensor_vec_index[OF u _ j, of "Matrix.vec 3 z"] by (simp add: mult.commute)
qed

lemma flag_vec_split:
  assumes H: "\<And>c. c < 3 \<Longrightarrow> H c \<in> carrier_mat n n" and v: "dim_vec v = n"
  shows "Matrix.vec (n * 3) (\<lambda>j. (H (j mod 3) *\<^sub>v v) $ (j div 3)) =
         tensor_vec (H 0 *\<^sub>v v) (unit_vec 3 0) + tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1) + tensor_vec (H 2 *\<^sub>v v) (unit_vec 3 2)"
proof (rule eq_vecI)
  have dH: "dim_vec (H c *\<^sub>v v) = n" if "c < 3" for c using H[OF that] by simp
  have dt: "dim_vec (tensor_vec (H c *\<^sub>v v) (unit_vec 3 c')) = n * 3" if "c < 3" for c c' by (rule tensor_vec_dim[OF dH[OF that]]) simp
  show "dim_vec (Matrix.vec (n * 3) (\<lambda>j. (H (j mod 3) *\<^sub>v v) $ (j div 3))) =
        dim_vec (tensor_vec (H 0 *\<^sub>v v) (unit_vec 3 0) + tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1) + tensor_vec (H 2 *\<^sub>v v) (unit_vec 3 2))"
    using dt[of 2 2] by simp
  fix j assume "j < dim_vec (tensor_vec (H 0 *\<^sub>v v) (unit_vec 3 0) + tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1) + tensor_vec (H 2 *\<^sub>v v) (unit_vec 3 2))"
  hence j: "j < n * 3" using dt[of 2 2] by simp
  have m: "j mod 3 = 0 \<or> j mod 3 = 1 \<or> j mod 3 = 2" by arith
  show "Matrix.vec (n * 3) (\<lambda>j. (H (j mod 3) *\<^sub>v v) $ (j div 3)) $ j =
        (tensor_vec (H 0 *\<^sub>v v) (unit_vec 3 0) + tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1) + tensor_vec (H 2 *\<^sub>v v) (unit_vec 3 2)) $ j"
    using j m dt[of 0 0] dt[of 1 1] dt[of 2 2]
      tensor_vec_index[OF dH[of 0] _ j, of "unit_vec 3 0"] tensor_vec_index[OF dH[of 1] _ j, of "unit_vec 3 1"]
      tensor_vec_index[OF dH[of 2] _ j, of "unit_vec 3 2"]
    by (auto simp: unit_vec_def)
qed

definition flag_H :: "real \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "flag_H \<kappa> A c = mat_fun (\<lambda>x. complex_of_real (if c = 0 then filt_s \<kappa> x else if c = 1 then filt_f \<kappa> x else filt_g \<kappa> x)) A"

definition flag_idl :: "nat \<Rightarrow> real \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "flag_idl n \<kappa> A a = lift3 n a (flag_H \<kappa> A)"

definition flag_emb :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.mat" where
  "flag_emb n a = lift3 n a (\<lambda>c. if c = 0 then 1\<^sub>m n else 0\<^sub>m n n)"

lemma flag_H_carrier: "A \<in> carrier_mat n n \<Longrightarrow> hermitian A \<Longrightarrow> flag_H \<kappa> A c \<in> carrier_mat n n"
  unfolding flag_H_def by simp

lemma flag_emb_mult:
  assumes v: "dim_vec v = n"
  shows "flag_emb n a *\<^sub>v v = tensor_vec a (tensor_vec v (unit_vec 3 0))"
proof -
  let ?z = "\<lambda>c::nat. if c = 0 then (1::complex) else 0"
  have H: "(if c = 0 then 1\<^sub>m n else 0\<^sub>m n n) \<in> carrier_mat n n" for c by simp
  have vc: "v \<in> carrier_vec n" using v by (rule carrier_vecI)
  have e: "(if c = 0 then 1\<^sub>m n else 0\<^sub>m n n) *\<^sub>v v = ?z c \<cdot>\<^sub>v v" for c
  proof (cases "c = 0")
    case True thus ?thesis using vc by simp
  next
    case False
    have "0\<^sub>m n n *\<^sub>v v = 0\<^sub>v n" using v by (intro eq_vecI) (simp_all add: scalar_prod_def)
    moreover have "(0::complex) \<cdot>\<^sub>v v = 0\<^sub>v n" using v by (intro eq_vecI) simp_all
    ultimately show ?thesis using False by simp
  qed
  have u3: "Matrix.vec 3 ?z = unit_vec 3 0" by (intro eq_vecI) (simp_all add: unit_vec_def)
  show ?thesis unfolding flag_emb_def lift3_mult_vec[OF H v] e flag_vec_eigen[where z = ?z, OF v] u3 ..
qed

lemma flag_idl_eigen:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
  shows "flag_idl n \<kappa> A a *\<^sub>v u = tensor_vec a (tensor_vec u (hflag \<kappa> l))"
proof -
  let ?z = "\<lambda>c::nat. complex_of_real (if c = 0 then filt_s \<kappa> l else if c = 1 then filt_f \<kappa> l else filt_g \<kappa> l)"
  have e: "flag_H \<kappa> A c *\<^sub>v u = ?z c \<cdot>\<^sub>v u" for c unfolding flag_H_def by (rule mat_fun_eigen[OF A u ev])
  have h: "Matrix.vec 3 ?z = hflag \<kappa> l" by (simp add: hflag_def)
  show ?thesis unfolding flag_idl_def lift3_mult_vec[where H = "flag_H \<kappa> A", OF flag_H_carrier[OF A] u] e flag_vec_eigen[where z = ?z, OF u] h ..
qed

lemma flag_idl_mult:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and b: "dim_vec b = n"
  shows "flag_idl n \<kappa> A a *\<^sub>v b = tensor_vec a
           (tensor_vec (flag_H \<kappa> A 0 *\<^sub>v b) (unit_vec 3 0) + tensor_vec (flag_H \<kappa> A 1 *\<^sub>v b) (unit_vec 3 1)
            + tensor_vec (flag_H \<kappa> A 2 *\<^sub>v b) (unit_vec 3 2))"
  unfolding flag_idl_def lift3_mult_vec[where H = "flag_H \<kappa> A", OF flag_H_carrier[OF A] b] flag_vec_split[where H = "flag_H \<kappa> A", OF flag_H_carrier[OF A] b] ..

text \<open>The post-selected error vector as a branch sum behind $W^*$.\<close>

lemma flag_perr:
  fixes A :: "complex Matrix.mat" and u :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and t0: "0 < t0" and N0: "0 < N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u" and psi: "dim_vec psi = N"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3" and h: "dim_vec h = 3"
  shows "pflag 3 P (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec 3 0)) - tensor_vec psi (tensor_vec u h))
         = (hhl_Wd A t0 N 3)\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 3)
             (\<lambda>k. pe_amp_reg N psi (hhl_phi t0 l) k \<cdot>\<^sub>v tensor_vec u (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h)))"
proof -
  have d3: "0 < (3::nat)" by simp
  note ctx = A t0 N0 u ev psi d3 G h
  let ?W = "hhl_Wd A t0 N 3"
  let ?w = "\<lambda>k. G k *\<^sub>v unit_vec 3 0 - h"
  let ?a = "\<lambda>k. pe_amp_reg N psi (hhl_phi t0 l) k"
  have Wc: "?W \<in> carrier_mat (N * (n * 3)) (N * (n * 3))"
    by (rule hhl_Wd_carrier[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = psi and d = 3 and G = G and hid = h, OF ctx])
  have Wd: "?W\<^sup>\<dagger> \<in> carrier_mat (N * (n * 3)) (N * (n * 3))" by (rule dagger_carrier[OF Wc])
  have Wf: "flagdiag 3 (?W\<^sup>\<dagger>)" by (rule flagdiag_dagger[OF hhl_Wd_flagdiag[OF A n0]])
  have wk: "dim_vec (?w k) = 3" for k using h by simp
  have err: "flag_circuit A t0 N 3 G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec 3 0)) - tensor_vec psi (tensor_vec u h)
             = ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 3) (\<lambda>k. Matrix.vec N ?a $ k \<cdot>\<^sub>v tensor_vec u (?w k))"
    using flag_err_vec[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = psi and d = 3 and G = G and hid = h, OF ctx]
    by (simp add: dalpha_def[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = psi and d = 3 and G = G and hid = h, OF ctx])
  have rs: "reg_sum N (n * 3) (\<lambda>k. Matrix.vec N ?a $ k \<cdot>\<^sub>v tensor_vec u (?w k)) = reg_sum N (n * 3) (\<lambda>k. ?a k \<cdot>\<^sub>v tensor_vec u (?w k))"
    by (rule reg_sum_cong) simp
  have dreg: "dim_vec (?a k \<cdot>\<^sub>v tensor_vec u (?w k)) = n * 3" for k using tensor_vec_dim[OF u wk[of k]] by simp
  show ?thesis
    unfolding err rs pflag_commute[OF Wd Wf dim_reg_sum] pflag_reg_sum[OF dreg d3] pflag_smult pflag_tensor[OF u wk d3] ..
qed

text \<open>Error vectors of orthogonal eigenvectors stay orthogonal after post-selection.\<close>

lemma flag_perr_orth:
  fixes A :: "complex Matrix.mat" and u u' :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and t0: "0 < t0" and N0: "0 < N"
      and u: "dim_vec u = n" and ev: "A *\<^sub>v u = complex_of_real l \<cdot>\<^sub>v u"
      and u': "dim_vec u' = n" and ev': "A *\<^sub>v u' = complex_of_real l' \<cdot>\<^sub>v u'"
      and orth: "\<langle>u|u'\<rangle> = 0" and psi: "dim_vec psi = N"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3" and h: "dim_vec h = 3" and h': "dim_vec h' = 3"
  shows "\<langle>pflag 3 P (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec 3 0)) - tensor_vec psi (tensor_vec u h)) |
          pflag 3 P (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec psi (tensor_vec u' (unit_vec 3 0)) - tensor_vec psi (tensor_vec u' h'))\<rangle> = 0"
proof -
  have d3: "0 < (3::nat)" by simp
  let ?W = "hhl_Wd A t0 N 3"
  let ?F = "\<lambda>k. pe_amp_reg N psi (hhl_phi t0 l) k \<cdot>\<^sub>v tensor_vec u (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h))"
  let ?H = "\<lambda>k. pe_amp_reg N psi (hhl_phi t0 l') k \<cdot>\<^sub>v tensor_vec u' (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h'))"
  have Wc: "?W \<in> carrier_mat (N * (n * 3)) (N * (n * 3))"
    by (rule hhl_Wd_carrier[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = psi and d = 3 and G = G and hid = h, OF A t0 N0 u ev psi d3 G h])
  have Wu: "unitary ?W"
    by (rule hhl_Wd_unitary[where A = A and n = n and N = N and ?t0.0 = t0 and l = l and u = u and psi = psi and d = 3 and G = G and hid = h, OF A t0 N0 u ev psi d3 G h])
  have p3: "dim_vec (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h)) = 3" "dim_vec (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h')) = 3" for k
    using h h' by simp_all
  have dF: "dim_vec (tensor_vec u (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h))) = n * 3" for k by (rule tensor_vec_dim[OF u p3(1)])
  have dH: "dim_vec (tensor_vec u' (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h'))) = n * 3" for k by (rule tensor_vec_dim[OF u' p3(2)])
  have "\<langle>?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 3) ?F|?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 3) ?H\<rangle> = \<langle>reg_sum N (n * 3) ?F|reg_sum N (n * 3) ?H\<rangle>"
    by (rule unitary_inner_pres[OF Wc Wu]) simp_all
  also have "\<dots> = (\<Sum>k<N. \<langle>?F k|?H k\<rangle>)" by (rule reg_sum_inner) (simp_all add: dF dH)
  also have "\<dots> = 0"
  proof (rule sum.neutral[OF ballI])
    fix k assume "k \<in> {..<N}"
    have "\<langle>?F k|?H k\<rangle> = cnj (pe_amp_reg N psi (hhl_phi t0 l) k) * (pe_amp_reg N psi (hhl_phi t0 l') k *
            \<langle>tensor_vec u (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h))|tensor_vec u' (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h'))\<rangle>)"
      using inner_prod_distrib_left[of "tensor_vec u (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h))" "?H k" "pe_amp_reg N psi (hhl_phi t0 l) k"]
            inner_prod_distrib_right[of "tensor_vec u (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h))"
              "tensor_vec u' (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h'))" "pe_amp_reg N psi (hhl_phi t0 l') k"] dF dH
      by simp
    also have "\<langle>tensor_vec u (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h))|tensor_vec u' (pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h'))\<rangle> =
               \<langle>u|u'\<rangle> * \<langle>pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h)|pflag 3 P (G k *\<^sub>v unit_vec 3 0 - h')\<rangle>"
      by (rule tensor_inner_prod[OF u u' p3(1) p3(2)])
    finally show "\<langle>?F k|?H k\<rangle> = 0" unfolding orth by simp
  qed
  moreover have "pflag 3 P (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec psi (tensor_vec u (unit_vec 3 0)) - tensor_vec psi (tensor_vec u h)) = ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 3) ?F"
    by (rule flag_perr[OF A n0 t0 N0 u ev psi G h])
  moreover have "pflag 3 P (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec psi (tensor_vec u' (unit_vec 3 0)) - tensor_vec psi (tensor_vec u' h')) = ?W\<^sup>\<dagger> *\<^sub>v reg_sum N (n * 3) ?H"
    by (rule flag_perr[OF A n0 t0 N0 u' ev' psi G h'])
  ultimately show ?thesis by simp
qed

lemma inner_as_sum: "dim_vec y = n \<Longrightarrow> \<langle>x|y\<rangle> = (\<Sum>i<n. cnj (x $ i) * y $ i)"
  by (simp add: Quantum.inner_prod_def atLeast0LessThan)

text \<open>If $M$ maps the orthonormal columns $u_j$ of $U$ to mutually orthogonal vectors then
$\norm{Mb}^2=\sum_j\norm{Mu_j}^2\,|\langle u_j|b\rangle|^2$.\<close>

lemma orth_image_eq:
  fixes M U :: "complex Matrix.mat"
  assumes U: "U \<in> carrier_mat n n" "unitary U" and M: "M \<in> carrier_mat K n"
      and orth: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<langle>M *\<^sub>v Matrix.col U i|M *\<^sub>v Matrix.col U j\<rangle> = 0"
      and b: "dim_vec b = n"
  shows "\<parallel>M *\<^sub>v b\<parallel>\<^sup>2 = (\<Sum>j<n. \<parallel>M *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 * (cmod (((U\<^sup>\<dagger>) *\<^sub>v b) $ j))\<^sup>2)"
proof -
  define \<beta> where "\<beta> = (U\<^sup>\<dagger>) *\<^sub>v b"
  let ?MU = "M * U"
  let ?m = "\<lambda>j. \<parallel>M *\<^sub>v Matrix.col U j\<parallel>\<^sup>2"
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U(1)])
  have MU: "?MU \<in> carrier_mat K n" by (rule mult_carrier_mat[OF M U(1)])
  have bc: "b \<in> carrier_vec n" using b by (rule carrier_vecI)
  have db: "dim_vec \<beta> = n" using U(1) unfolding \<beta>_def by simp
  have UU: "U * (U\<^sup>\<dagger>) = 1\<^sub>m n" using U unfolding unitary_def by auto
  have Ub: "U *\<^sub>v \<beta> = b" unfolding \<beta>_def using assoc_mult_mat_vec[OF U(1) Ud bc, symmetric] UU bc by simp
  have Mb: "M *\<^sub>v b = ?MU *\<^sub>v \<beta>" using assoc_mult_mat_vec[OF M U(1) carrier_vecI[OF db]] Ub by simp
  define D where "D = Matrix.mat n n (\<lambda>(i, j). if i = j then complex_of_real (?m i) else 0)"
  have DD: "?MU\<^sup>\<dagger> * ?MU = D"
  proof (rule eq_matI)
    fix i j assume "i < dim_row D" "j < dim_col D"
    hence i: "i < n" and j: "j < n" by (simp_all add: D_def)
    have "(?MU\<^sup>\<dagger> * ?MU) $$ (i, j) = \<langle>Matrix.col ?MU i|Matrix.col ?MU j\<rangle>" by (rule dagger_mult_entry[OF MU i j])
    also have "\<dots> = \<langle>M *\<^sub>v Matrix.col U i|M *\<^sub>v Matrix.col U j\<rangle>" unfolding col_mult2[OF M U(1) i] col_mult2[OF M U(1) j] ..
    also have "\<dots> = D $$ (i, j)"
    proof (cases "i = j")
      case True thus ?thesis unfolding D_def using i by (simp add: cpx_vec_length_inner_prod[symmetric])
    next
      case False thus ?thesis unfolding D_def using i j orth by simp
    qed
    finally show "(?MU\<^sup>\<dagger> * ?MU) $$ (i, j) = D $$ (i, j)" .
  qed (use MU U(1) in \<open>simp_all add: D_def\<close>)
  have dMU: "dim_vec (?MU *\<^sub>v \<beta>) = K" using M by simp
  have MUd: "?MU\<^sup>\<dagger> \<in> carrier_mat n K" by (rule dagger_carrier[OF MU])
  have "\<langle>?MU *\<^sub>v \<beta>|?MU *\<^sub>v \<beta>\<rangle> = \<langle>\<beta>|?MU\<^sup>\<dagger> *\<^sub>v (?MU *\<^sub>v \<beta>)\<rangle>"
    using inner_prod_adjoint_swap[OF MUd db dMU] by (simp add: dagger_of_dagger_is_id)
  also have "?MU\<^sup>\<dagger> *\<^sub>v (?MU *\<^sub>v \<beta>) = D *\<^sub>v \<beta>" unfolding DD[symmetric] by (rule assoc_mult_mat_vec[OF MUd MU carrier_vecI[OF db], symmetric])
  also have "\<langle>\<beta>|D *\<^sub>v \<beta>\<rangle> = (\<Sum>j<n. complex_of_real (?m j * (cmod (\<beta> $ j))\<^sup>2))"
  proof -
    have Dv: "(D *\<^sub>v \<beta>) $ i = complex_of_real (?m i) * \<beta> $ i" if "i < n" for i
      using that db by (simp add: D_def scalar_prod_def atLeast0LessThan if_distrib[of "\<lambda>x. x * _"] sum.delta cong: if_cong)
    have "\<langle>\<beta>|D *\<^sub>v \<beta>\<rangle> = (\<Sum>j<n. cnj (\<beta> $ j) * (complex_of_real (?m j) * \<beta> $ j))"
    proof -
      have dD: "dim_vec (D *\<^sub>v \<beta>) = n" by (simp add: D_def)
      show ?thesis unfolding inner_as_sum[OF dD] by (rule sum.cong[OF refl]) (simp add: Dv)
    qed
    also have "\<dots> = (\<Sum>j<n. complex_of_real (?m j * (cmod (\<beta> $ j))\<^sup>2))"
    proof (rule sum.cong[OF refl])
      fix j
      have "cnj (\<beta> $ j) * \<beta> $ j = complex_of_real ((cmod (\<beta> $ j))\<^sup>2)" by (metis complex_norm_square mult.commute)
      thus "cnj (\<beta> $ j) * (complex_of_real (?m j) * \<beta> $ j) = complex_of_real (?m j * (cmod (\<beta> $ j))\<^sup>2)"
        by (simp add: mult_ac)
    qed
    finally show ?thesis .
  qed
  finally have "complex_of_real (\<parallel>M *\<^sub>v b\<parallel>\<^sup>2) = complex_of_real (\<Sum>j<n. ?m j * (cmod (\<beta> $ j))\<^sup>2)"
    unfolding cpx_vec_length_inner_prod Mb by (simp add: of_real_sum)
  thus ?thesis unfolding \<beta>_def by (simp only: of_real_eq_iff)
qed

lemma unitary_dagger_norm:
  assumes U: "U \<in> carrier_mat n n" "unitary U" and b: "dim_vec b = n"
  shows "(\<Sum>j<n. (cmod (((U\<^sup>\<dagger>) *\<^sub>v b) $ j))\<^sup>2) = \<parallel>b\<parallel>\<^sup>2"
proof -
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat n n" by (rule dagger_carrier[OF U(1)])
  have "\<parallel>(U\<^sup>\<dagger>) *\<^sub>v b\<parallel> = \<parallel>b\<parallel>" by (rule unitary_vnorm[OF Ud unitary_dagger[OF U(2)] b])
  hence "\<parallel>(U\<^sup>\<dagger>) *\<^sub>v b\<parallel>\<^sup>2 = \<parallel>b\<parallel>\<^sup>2" by simp
  thus ?thesis unfolding vnorm_sq using U(1) by simp
qed

definition pflag_mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> complex Matrix.mat" where
  "pflag_mat K d P = Matrix.mat K K (\<lambda>(r, s). if r = s \<and> P (r mod d) then 1 else 0)"

lemma pflag_mat_carrier [simp]: "pflag_mat K d P \<in> carrier_mat K K"
  by (simp add: pflag_mat_def)

lemma pflag_mat_mult: "dim_vec v = K \<Longrightarrow> pflag_mat K d P *\<^sub>v v = pflag d P v"
  by (intro eq_vecI) (auto simp: pflag_mat_def pflag_def scalar_prod_def if_distrib[of "\<lambda>x. x * _"] sum.delta cong: if_cong)

lemma pflag_all: "pflag d (\<lambda>_. True) v = v"
  by (intro eq_vecI) (simp_all add: pflag_def)

text \<open>Theorem 1(1) for every right-hand side: $\norm{(\tilde U-U)b}\le
3\pi^2\sqrt{4+2\pi^2}\,\kappa\norm b/(Nt_0)$, i.e.\ $\norm{\tilde U-U}=O(\kappa/t)$ for the total
evolution time $t=Nt_0$.\<close>

theorem flag_bound:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and t0: "0 < t0" and N: "2 \<le> N"
      and k0: "0 < \<kappa>" and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<bar>t0 * l\<bar> \<le> pi / 2"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
      and b: "dim_vec b = n"
  shows "\<parallel>flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 3 0)) - flag_idl n \<kappa> A (win_state N) *\<^sub>v b\<parallel>\<^sup>2
         \<le> 9 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2) * \<parallel>b\<parallel>\<^sup>2"
proof -
  let ?\<psi> = "win_state N" and ?K = "N * (n * 3)"
  let ?C = "flag_circuit A t0 N 3 G" and ?E = "flag_emb n (win_state N)" and ?I = "flag_idl n \<kappa> A (win_state N)"
  let ?M = "?C * ?E - ?I"
  let ?e = "9 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2)"
  have N0: "0 < N" using N by simp
  have nA: "dim_row A = n" using A(1) by simp
  obtain U D where sd: "spectral_decomp A U D" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have Cc: "?C \<in> carrier_mat ?K ?K"
    unfolding flag_circuit_def hhl_Wd_def nA
    by (rule mult_carrier_mat[OF dagger_carrier[OF pe_unitary_carrier] mult_carrier_mat[OF ctrl_blocks_carrier pe_unitary_carrier]])
  have Ec: "?E \<in> carrier_mat ?K n" using lift3_carrier[of n ?\<psi>] by (simp add: flag_emb_def)
  have Ic: "?I \<in> carrier_mat ?K n" using lift3_carrier[of n ?\<psi>] by (simp add: flag_idl_def)
  have Mc: "?M \<in> carrier_mat ?K n" by (rule minus_carrier_mat[OF Ic])
  have Mv: "?M *\<^sub>v v = ?C *\<^sub>v tensor_vec ?\<psi> (tensor_vec v (unit_vec 3 0)) - ?I *\<^sub>v v" if v: "dim_vec v = n" for v
  proof -
    have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
    have "?M *\<^sub>v v = (?C * ?E) *\<^sub>v v - ?I *\<^sub>v v" by (rule minus_mult_distrib_mat_vec[OF mult_carrier_mat[OF Cc Ec] Ic vc])
    also have "(?C * ?E) *\<^sub>v v = ?C *\<^sub>v (?E *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF Cc Ec vc])
    finally show ?thesis unfolding flag_emb_mult[OF v] .
  qed
  have col: "dim_vec (Matrix.col U j) = n" "A *\<^sub>v Matrix.col U j = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j"
            "\<bar>t0 * D ! j\<bar> \<le> pi / 2" if j: "j < n" for j
  proof -
    show "dim_vec (Matrix.col U j) = n" using d(1) by simp
    show "A *\<^sub>v Matrix.col U j = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j" by (rule spectral_decomp_col[OF A(1) sd j])
    show "\<bar>t0 * D ! j\<bar> \<le> pi / 2" by (rule spec[OF spectral_decomp_eig_in_spectrum[OF A(1) sd j]])
  qed
  have MU: "?M *\<^sub>v Matrix.col U j = ?C *\<^sub>v tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (unit_vec 3 0))
                                      - tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (hflag \<kappa> (D ! j)))" if j: "j < n" for j
    unfolding Mv[OF col(1)[OF j]] flag_idl_eigen[OF A col(1,2)[OF j]] ..
  have orth: "\<langle>?M *\<^sub>v Matrix.col U i|?M *\<^sub>v Matrix.col U j\<rangle> = 0" if i: "i < n" and j: "j < n" and ij: "i \<noteq> j" for i j
  proof -
    have o: "\<langle>Matrix.col U i|Matrix.col U j\<rangle> = 0" using unitary_cols_orthonormal[OF d(2), of i j] d(1) i j ij by simp
    show ?thesis unfolding MU[OF i] MU[OF j]
      using flag_perr_orth[where P = "\<lambda>_. True" and G = G and h = "hflag \<kappa> (D ! i)" and h' = "hflag \<kappa> (D ! j)",
              OF A n0 t0 N0 col(1,2)[OF i] col(1,2)[OF j] o dim_win_state G dim_hflag dim_hflag]
      unfolding pflag_all .
  qed
  have me: "\<parallel>?M *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 \<le> ?e" if j: "j < n" for j
  proof -
    have one: "\<parallel>Matrix.col U j\<parallel>\<^sup>2 = 1"
    proof -
      have "\<langle>Matrix.col U j|Matrix.col U j\<rangle> = 1" using unitary_cols_orthonormal[OF d(2), of j j] d(1) j by simp
      hence "complex_of_real (\<parallel>Matrix.col U j\<parallel>\<^sup>2) = complex_of_real 1" unfolding cpx_vec_length_inner_prod[symmetric] by simp
      thus ?thesis by (simp only: of_real_eq_iff)
    qed
    have "\<parallel>?M *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 \<le> \<parallel>Matrix.col U j\<parallel>\<^sup>2 * ?e"
      using flag_window_eigen[OF A t0 N col(1,2)[OF j] k0 col(3)[OF j] G Gh] unfolding MU[OF j] vnorm_Re_inner .
    thus ?thesis unfolding one by simp
  qed
  have "\<parallel>?M *\<^sub>v b\<parallel>\<^sup>2 = (\<Sum>j<n. \<parallel>?M *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 * (cmod (((U\<^sup>\<dagger>) *\<^sub>v b) $ j))\<^sup>2)"
    by (rule orth_image_eq[OF d(1,2) Mc orth b])
  also have "\<dots> \<le> (\<Sum>j<n. ?e * (cmod (((U\<^sup>\<dagger>) *\<^sub>v b) $ j))\<^sup>2)"
    by (rule sum_mono) (intro mult_right_mono me, simp_all)
  also have "\<dots> = ?e * \<parallel>b\<parallel>\<^sup>2" unfolding sum_distrib_left[symmetric] unitary_dagger_norm[OF d(1,2) b] ..
  finally show ?thesis unfolding Mv[OF b] .
qed

lemma sum_factor3: "(\<Sum>j\<in>S. (r::real) * a j * c j) = r * (\<Sum>j\<in>S. a j * c j)"
  unfolding sum_distrib_left by (rule sum.cong[OF refl]) (simp add: algebra_simps)

text \<open>Theorem 1(2) for every right-hand side: post-selecting the flag on $\{\mathrm{well},\mathrm{ill}\}$
the error is at most $\rho$ times the post-selected ideal, $\rho=6\pi^2\sqrt{4+2\pi^2}\,\kappa/(Nt_0)$.\<close>

theorem flag_post_bound:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and t0: "0 < t0" and N: "2 \<le> N"
      and k0: "0 < \<kappa>" and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<bar>t0 * l\<bar> \<le> pi / 2"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
      and b: "dim_vec b = n"
  defines "P \<equiv> \<lambda>c::nat. c \<noteq> 0"
  shows "\<parallel>pflag 3 P (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 3 0))) - pflag 3 P (flag_idl n \<kappa> A (win_state N) *\<^sub>v b)\<parallel>\<^sup>2
         \<le> 36 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2) * \<parallel>pflag 3 P (flag_idl n \<kappa> A (win_state N) *\<^sub>v b)\<parallel>\<^sup>2"
proof -
  let ?\<psi> = "win_state N" and ?K = "N * (n * 3)"
  let ?C = "flag_circuit A t0 N 3 G" and ?E = "flag_emb n (win_state N)" and ?I = "flag_idl n \<kappa> A (win_state N)"
  let ?Pm = "pflag_mat ?K 3 P"
  let ?M = "?Pm * (?C * ?E - ?I)" and ?Q = "?Pm * ?I"
  let ?r = "36 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2)"
  have N0: "0 < N" using N by simp
  have d3: "0 < (3::nat)" by simp
  have nA: "dim_row A = n" using A(1) by simp
  obtain U D where sd: "spectral_decomp A U D" using spectral_decomp_exists[OF A] by blast
  note d = spectral_decompD[OF A(1) sd]
  have Cc: "?C \<in> carrier_mat ?K ?K"
    unfolding flag_circuit_def hhl_Wd_def nA
    by (rule mult_carrier_mat[OF dagger_carrier[OF pe_unitary_carrier] mult_carrier_mat[OF ctrl_blocks_carrier pe_unitary_carrier]])
  have Ec: "?E \<in> carrier_mat ?K n" using lift3_carrier[of n ?\<psi>] by (simp add: flag_emb_def)
  have Ic: "?I \<in> carrier_mat ?K n" using lift3_carrier[of n ?\<psi>] by (simp add: flag_idl_def)
  have Mc: "?M \<in> carrier_mat ?K n" by (rule mult_carrier_mat[OF pflag_mat_carrier minus_carrier_mat[OF Ic]])
  have Qc: "?Q \<in> carrier_mat ?K n" by (rule mult_carrier_mat[OF pflag_mat_carrier Ic])
  have dCx: "dim_vec (?C *\<^sub>v tensor_vec ?\<psi> (tensor_vec v (unit_vec 3 0))) = ?K" for v using Cc by simp
  have dIv: "dim_vec (?I *\<^sub>v v) = ?K" for v using Ic by simp
  have Mv: "?M *\<^sub>v v = pflag 3 P (?C *\<^sub>v tensor_vec ?\<psi> (tensor_vec v (unit_vec 3 0))) - pflag 3 P (?I *\<^sub>v v)" if v: "dim_vec v = n" for v
  proof -
    have vc: "v \<in> carrier_vec n" by (rule carrier_vecI[OF v])
    have MM: "?C * ?E - ?I \<in> carrier_mat ?K n" by (rule minus_carrier_mat[OF Ic])
    have "?M *\<^sub>v v = ?Pm *\<^sub>v ((?C * ?E - ?I) *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF pflag_mat_carrier MM vc])
    also have "(?C * ?E - ?I) *\<^sub>v v = (?C * ?E) *\<^sub>v v - ?I *\<^sub>v v" by (rule minus_mult_distrib_mat_vec[OF mult_carrier_mat[OF Cc Ec] Ic vc])
    also have "(?C * ?E) *\<^sub>v v = ?C *\<^sub>v (?E *\<^sub>v v)" by (rule assoc_mult_mat_vec[OF Cc Ec vc])
    also have "?Pm *\<^sub>v (?C *\<^sub>v (?E *\<^sub>v v) - ?I *\<^sub>v v) = pflag 3 P (?C *\<^sub>v (?E *\<^sub>v v) - ?I *\<^sub>v v)"
      by (rule pflag_mat_mult) (simp add: flag_emb_mult[OF v] dCx carrier_matD(1)[OF Ic])
    finally show ?thesis unfolding flag_emb_mult[OF v] by (simp only: pflag_minus dCx dIv)
  qed
  have Qv: "?Q *\<^sub>v v = pflag 3 P (?I *\<^sub>v v)" if v: "dim_vec v = n" for v
    using assoc_mult_mat_vec[OF pflag_mat_carrier Ic carrier_vecI[OF v]] pflag_mat_mult[OF dIv] by simp
  have col: "dim_vec (Matrix.col U j) = n" "A *\<^sub>v Matrix.col U j = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j"
            "\<bar>t0 * D ! j\<bar> \<le> pi / 2" if j: "j < n" for j
  proof -
    show "dim_vec (Matrix.col U j) = n" using d(1) by simp
    show "A *\<^sub>v Matrix.col U j = complex_of_real (D ! j) \<cdot>\<^sub>v Matrix.col U j" by (rule spectral_decomp_col[OF A(1) sd j])
    show "\<bar>t0 * D ! j\<bar> \<le> pi / 2" by (rule spec[OF spectral_decomp_eig_in_spectrum[OF A(1) sd j]])
  qed
  have IU: "?I *\<^sub>v Matrix.col U j = tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (hflag \<kappa> (D ! j)))" if j: "j < n" for j
    by (rule flag_idl_eigen[OF A col(1,2)[OF j]])
  have MU: "?M *\<^sub>v Matrix.col U j = pflag 3 P (?C *\<^sub>v tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (unit_vec 3 0)) - tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (hflag \<kappa> (D ! j))))" if j: "j < n" for j
  proof -
    have dI: "dim_vec (tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (hflag \<kappa> (D ! j)))) = ?K"
      using IU[OF j] dIv by metis
    show ?thesis unfolding Mv[OF col(1)[OF j]] IU[OF j] by (rule pflag_minus[symmetric]) (simp only: dCx dI)
  qed
  have QU: "?Q *\<^sub>v Matrix.col U j = pflag 3 P (tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (hflag \<kappa> (D ! j))))" if j: "j < n" for j
    unfolding Qv[OF col(1)[OF j]] IU[OF j] ..
  have oU: "\<langle>Matrix.col U i|Matrix.col U j\<rangle> = 0" if "i < n" "j < n" "i \<noteq> j" for i j
    using unitary_cols_orthonormal[OF d(2), of i j] d(1) that by simp
  have orthM: "\<langle>?M *\<^sub>v Matrix.col U i|?M *\<^sub>v Matrix.col U j\<rangle> = 0" if i: "i < n" and j: "j < n" and ij: "i \<noteq> j" for i j
    unfolding MU[OF i] MU[OF j]
    by (rule flag_perr_orth[where G = G, OF A n0 t0 N0 col(1,2)[OF i] col(1,2)[OF j] oU[OF i j ij] dim_win_state G dim_hflag dim_hflag])
  have orthQ: "\<langle>?Q *\<^sub>v Matrix.col U i|?Q *\<^sub>v Matrix.col U j\<rangle> = 0" if i: "i < n" and j: "j < n" and ij: "i \<noteq> j" for i j
  proof -
    have h3: "dim_vec (hflag \<kappa> x) = 3" for x by simp
    have pt: "pflag 3 P (tensor_vec ?\<psi> (tensor_vec (Matrix.col U k) (hflag \<kappa> x))) = tensor_vec ?\<psi> (tensor_vec (Matrix.col U k) (pflag 3 P (hflag \<kappa> x)))"
      if k: "k < n" for k x
    proof -
      have u1: "dim_vec (tensor_vec (Matrix.col U k) (hflag \<kappa> x)) = n * 3" by (rule tensor_vec_dim[OF col(1)[OF k] h3])
      show ?thesis unfolding pflag_tensor_left[OF dim_win_state u1 d3] pflag_tensor[OF col(1)[OF k] h3 d3] ..
    qed
    have p3: "dim_vec (pflag 3 P (hflag \<kappa> x)) = 3" for x by simp
    have ui: "dim_vec (tensor_vec (Matrix.col U i) (pflag 3 P (hflag \<kappa> (D ! i)))) = n * 3" by (rule tensor_vec_dim[OF col(1)[OF i] p3])
    have uj: "dim_vec (tensor_vec (Matrix.col U j) (pflag 3 P (hflag \<kappa> (D ! j)))) = n * 3" by (rule tensor_vec_dim[OF col(1)[OF j] p3])
    show ?thesis unfolding QU[OF i] QU[OF j] pt[OF i] pt[OF j]
      tensor_inner_prod[OF dim_win_state dim_win_state ui uj] tensor_inner_prod[OF col(1)[OF i] col(1)[OF j] p3 p3] oU[OF i j ij] by simp
  qed
  have mq: "\<parallel>?M *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 \<le> ?r * \<parallel>?Q *\<^sub>v Matrix.col U j\<parallel>\<^sup>2" if j: "j < n" for j
  proof -
    have dI: "dim_vec (tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (hflag \<kappa> (D ! j)))) = ?K"
      using IU[OF j] dIv by metis
    have eq: "pflag 3 P (?C *\<^sub>v tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (unit_vec 3 0)) - tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (hflag \<kappa> (D ! j))))
              = pflag 3 P (?C *\<^sub>v tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (unit_vec 3 0))) - pflag 3 P (tensor_vec ?\<psi> (tensor_vec (Matrix.col U j) (hflag \<kappa> (D ! j))))"
      by (rule pflag_minus) (simp only: dCx dI)
    show ?thesis unfolding MU[OF j] QU[OF j] eq unfolding P_def
      by (rule flag_post_eigen(1)[OF A n0 t0 N col(1,2)[OF j] k0 col(3)[OF j] G Gh])
  qed
  have "\<parallel>?M *\<^sub>v b\<parallel>\<^sup>2 = (\<Sum>j<n. \<parallel>?M *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 * (cmod (((U\<^sup>\<dagger>) *\<^sub>v b) $ j))\<^sup>2)"
    by (rule orth_image_eq[OF d(1,2) Mc orthM b])
  also have "\<dots> \<le> (\<Sum>j<n. ?r * \<parallel>?Q *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 * (cmod (((U\<^sup>\<dagger>) *\<^sub>v b) $ j))\<^sup>2)"
    by (rule sum_mono) (intro mult_right_mono mq, simp_all)
  also have "\<dots> = ?r * (\<Sum>j<n. \<parallel>?Q *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 * (cmod (((U\<^sup>\<dagger>) *\<^sub>v b) $ j))\<^sup>2)"
    by (rule sum_factor3)
  also have "(\<Sum>j<n. \<parallel>?Q *\<^sub>v Matrix.col U j\<parallel>\<^sup>2 * (cmod (((U\<^sup>\<dagger>) *\<^sub>v b) $ j))\<^sup>2) = \<parallel>?Q *\<^sub>v b\<parallel>\<^sup>2"
    by (rule orth_image_eq[OF d(1,2) Qc orthQ b, symmetric])
  finally show ?thesis unfolding Mv[OF b] Qv[OF b] .
qed

lemma normalized_close:
  assumes d: "dim_vec a = dim_vec c" and cl: "\<parallel>a - c\<parallel> \<le> \<rho> * \<parallel>c\<parallel>" and r1: "\<rho> < 1" and c0: "\<parallel>c\<parallel> \<noteq> 0"
  shows "\<parallel>complex_of_real (1 / \<parallel>a\<parallel>) \<cdot>\<^sub>v a - complex_of_real (1 / \<parallel>c\<parallel>) \<cdot>\<^sub>v c\<parallel> \<le> 2 * \<rho>"
proof -
  have cp: "0 < \<parallel>c\<parallel>" using c0 vnorm_ge0 by (simp add: order_le_neq_trans)
  have a0: "\<parallel>a\<parallel> \<noteq> 0"
  proof
    assume "\<parallel>a\<parallel> = 0"
    hence "\<parallel>c\<parallel> \<le> \<parallel>a - c\<parallel>" using vnorm_reverse[OF d] by simp
    hence "\<parallel>c\<parallel> \<le> \<rho> * \<parallel>c\<parallel>" using cl by linarith
    thus False using r1 cp by (simp add: mult_le_cancel_right1)
  qed
  have "\<parallel>complex_of_real (1 / \<parallel>a\<parallel>) \<cdot>\<^sub>v a - complex_of_real (1 / \<parallel>c\<parallel>) \<cdot>\<^sub>v c\<parallel> \<le> 2 * \<parallel>a - c\<parallel> / \<parallel>c\<parallel>"
    by (rule normalize_stable[OF d a0 c0])
  also have "\<dots> \<le> 2 * (\<rho> * \<parallel>c\<parallel>) / \<parallel>c\<parallel>" using cl cp by (intro divide_right_mono) simp_all
  also have "\<dots> = 2 * \<rho>" using cp by simp
  finally show ?thesis .
qed

text \<open>Theorem 1(2), normalised: the post-selected state is within $2\rho$ of the ideal one.\<close>

corollary flag_post_normalized:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and t0: "0 < t0" and N: "2 \<le> N"
      and k0: "0 < \<kappa>" and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<bar>t0 * l\<bar> \<le> pi / 2"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
      and b: "dim_vec b = n"
  defines "P \<equiv> \<lambda>c::nat. c \<noteq> 0" and "\<rho> \<equiv> 6 * pi\<^sup>2 * sqrt (4 + 2 * pi\<^sup>2) * \<kappa> / (real N * t0)"
  defines "y \<equiv> pflag 3 P (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 3 0)))"
      and "x \<equiv> pflag 3 P (flag_idl n \<kappa> A (win_state N) *\<^sub>v b)"
  assumes r1: "\<rho> < 1" and x0: "\<parallel>x\<parallel> \<noteq> 0"
  shows "\<parallel>complex_of_real (1 / \<parallel>y\<parallel>) \<cdot>\<^sub>v y - complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x\<parallel> \<le> 2 * \<rho>"
proof (rule normalized_close[OF _ _ r1 x0])
  have NR: "0 < real N" using N by simp
  have Cc: "flag_circuit A t0 N 3 G \<in> carrier_mat (N * (n * 3)) (N * (n * 3))"
  proof -
    have nA: "dim_row A = n" using A(1) by simp
    show ?thesis unfolding flag_circuit_def hhl_Wd_def nA
      by (rule mult_carrier_mat[OF dagger_carrier[OF pe_unitary_carrier] mult_carrier_mat[OF ctrl_blocks_carrier pe_unitary_carrier]])
  qed
  show "dim_vec y = dim_vec x" unfolding x_def y_def using Cc carrier_matD(1)[OF lift3_carrier[of n "win_state N" "flag_H \<kappa> A"]] by (simp add: flag_idl_def)
  have sq: "\<parallel>y - x\<parallel>\<^sup>2 \<le> \<rho>\<^sup>2 * \<parallel>x\<parallel>\<^sup>2"
  proof -
    have "\<rho>\<^sup>2 = 36 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2)"
      unfolding \<rho>_def using NR t0 by (simp add: power_mult_distrib power_divide field_simps power2_eq_square power4_eq_xxxx)
    thus ?thesis using flag_post_bound[OF A n0 t0 N k0 spec G Gh b] unfolding x_def y_def P_def by simp
  qed
  show "\<parallel>y - x\<parallel> \<le> \<rho> * \<parallel>x\<parallel>"
  proof (rule power2_le_imp_le)
    show "\<parallel>y - x\<parallel>\<^sup>2 \<le> (\<rho> * \<parallel>x\<parallel>)\<^sup>2" using sq by (simp add: power_mult_distrib)
    show "0 \<le> \<rho> * \<parallel>x\<parallel>" unfolding \<rho>_def using k0 NR t0 vnorm_ge0[of x] by simp
  qed
qed

lemma pflag_sub: "(\<And>c. Q c \<Longrightarrow> P c) \<Longrightarrow> pflag d Q v = pflag d Q (pflag d P v)"
  by (intro eq_vecI) (auto simp: pflag_def)

lemma lift3_post:
  assumes H: "\<And>c. c < 3 \<Longrightarrow> H c \<in> carrier_mat n n" and v: "dim_vec v = n" and a: "dim_vec a = N"
  shows "pflag 3 (\<lambda>c. c = 1) (lift3 n a H *\<^sub>v v) = tensor_vec a (tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1))"
    and "H 2 *\<^sub>v v = 0\<^sub>v n \<Longrightarrow> pflag 3 (\<lambda>c. c \<noteq> 0) (lift3 n a H *\<^sub>v v) = pflag 3 (\<lambda>c. c = 1) (lift3 n a H *\<^sub>v v)"
proof -
  let ?z = "Matrix.vec (n * 3) (\<lambda>j. (H (j mod 3) *\<^sub>v v) $ (j div 3))"
  have dz: "dim_vec ?z = n * 3" by simp
  have d3: "0 < (3::nat)" by simp
  have dH: "dim_vec (H c *\<^sub>v v) = n" if "c < 3" for c using H[OF that] by simp
  have L: "lift3 n a H *\<^sub>v v = tensor_vec a ?z" by (rule lift3_mult_vec[OF H v])
  have z1: "pflag 3 (\<lambda>c. c = 1) ?z = tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1)"
  proof (rule eq_vecI)
    have dt: "dim_vec (tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1)) = n * 3" by (rule tensor_vec_dim[OF dH]) simp_all
    show "dim_vec (pflag 3 (\<lambda>c. c = 1) ?z) = dim_vec (tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1))" using dt by simp
    fix j assume "j < dim_vec (tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1))"
    hence j: "j < n * 3" using dt by simp
    have i: "j div 3 < n" using j by (simp add: less_mult_imp_div_less)
    show "pflag 3 (\<lambda>c. c = 1) ?z $ j = tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1) $ j"
      using j i tensor_vec_index[OF dH[of 1] _ j, of "unit_vec 3 1"] by (simp add: pflag_def unit_vec_def)
  qed
  show "pflag 3 (\<lambda>c. c = 1) (lift3 n a H *\<^sub>v v) = tensor_vec a (tensor_vec (H 1 *\<^sub>v v) (unit_vec 3 1))"
    unfolding L pflag_tensor_left[OF a dz d3] z1 ..
  assume h2: "H 2 *\<^sub>v v = 0\<^sub>v n"
  have z2: "pflag 3 (\<lambda>c. c \<noteq> 0) ?z = pflag 3 (\<lambda>c. c = 1) ?z"
  proof (rule eq_vecI)
    fix j assume "j < dim_vec (pflag 3 (\<lambda>c. c = 1) ?z)"
    hence j: "j < n * 3" by simp
    have i: "j div 3 < n" using j by (simp add: less_mult_imp_div_less)
    have "j mod 3 = 0 \<or> j mod 3 = 1 \<or> j mod 3 = 2" by arith
    thus "pflag 3 (\<lambda>c. c \<noteq> 0) ?z $ j = pflag 3 (\<lambda>c. c = 1) ?z $ j"
      using j i h2 by (auto simp: pflag_def)
  qed simp
  show "pflag 3 (\<lambda>c. c \<noteq> 0) (lift3 n a H *\<^sub>v v) = pflag 3 (\<lambda>c. c = 1) (lift3 n a H *\<^sub>v v)"
    unfolding L pflag_tensor_left[OF a dz d3] z2 ..
qed

text \<open>Theorem 1(3): if $b$ has no ill-conditioned component ($g(A)b=0$), the state post-selected
on $\ket{\mathrm{well}}$ is within $2\rho$ of $\psi\otimes f(A)b/\norm{f(A)b}\otimes\ket{\mathrm{well}}$.\<close>

theorem flag_well_normalized:
  fixes A :: "complex Matrix.mat" and b :: "complex Matrix.vec"
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and n0: "0 < n" and t0: "0 < t0" and N: "2 \<le> N"
      and k0: "0 < \<kappa>" and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> \<bar>t0 * l\<bar> \<le> pi / 2"
      and G: "\<And>k. k < N \<Longrightarrow> G k \<in> carrier_mat 3 3"
      and Gh: "\<And>k. k < N \<Longrightarrow> G k *\<^sub>v unit_vec 3 0 = hflag \<kappa> (reg_eig t0 N k)"
      and b: "dim_vec b = n" and ill: "flag_H \<kappa> A 2 *\<^sub>v b = 0\<^sub>v n" and well: "flag_H \<kappa> A 1 *\<^sub>v b \<noteq> 0\<^sub>v n"
  defines "\<rho> \<equiv> 6 * pi\<^sup>2 * sqrt (4 + 2 * pi\<^sup>2) * \<kappa> / (real N * t0)"
  defines "y \<equiv> pflag 3 (\<lambda>c. c = 1) (flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 3 0)))"
      and "x \<equiv> tensor_vec (win_state N) (tensor_vec (flag_H \<kappa> A 1 *\<^sub>v b) (unit_vec 3 1))"
  assumes r1: "\<rho> < 1"
  shows "\<parallel>complex_of_real (1 / \<parallel>y\<parallel>) \<cdot>\<^sub>v y - complex_of_real (1 / \<parallel>x\<parallel>) \<cdot>\<^sub>v x\<parallel> \<le> 2 * \<rho>"
proof -
  let ?P = "\<lambda>c::nat. c \<noteq> 0" and ?Pw = "\<lambda>c::nat. c = 1"
  let ?Cx = "flag_circuit A t0 N 3 G *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 3 0))"
  let ?Ib = "flag_idl n \<kappa> A (win_state N) *\<^sub>v b"
  have NR: "0 < real N" using N by simp
  have nA: "dim_row A = n" using A(1) by simp
  have Cc: "flag_circuit A t0 N 3 G \<in> carrier_mat (N * (n * 3)) (N * (n * 3))"
    unfolding flag_circuit_def hhl_Wd_def nA
    by (rule mult_carrier_mat[OF dagger_carrier[OF pe_unitary_carrier] mult_carrier_mat[OF ctrl_blocks_carrier pe_unitary_carrier]])
  have dCx: "dim_vec ?Cx = N * (n * 3)" using Cc by simp
  have dIb: "dim_vec ?Ib = N * (n * 3)" using carrier_matD(1)[OF lift3_carrier[of n "win_state N" "flag_H \<kappa> A"]] by (simp add: flag_idl_def)
  note lp = lift3_post[where H = "flag_H \<kappa> A", OF flag_H_carrier[OF A] b dim_win_state, folded flag_idl_def]
  have xI: "x = pflag 3 ?Pw ?Ib" unfolding x_def lp(1) ..
  have PI: "pflag 3 ?P ?Ib = x" unfolding xI by (rule lp(2)[OF ill])
  have x0: "\<parallel>x\<parallel> \<noteq> 0"
  proof -
    have f3: "dim_vec (flag_H \<kappa> A 1 *\<^sub>v b) = n" using carrier_matD(1)[OF flag_H_carrier[OF A, of \<kappa> 1]] by simp
    have ft: "dim_vec (tensor_vec (flag_H \<kappa> A 1 *\<^sub>v b) (unit_vec 3 1)) = n * 3" by (rule tensor_vec_dim[OF f3]) simp
    have "\<parallel>x\<parallel> = \<parallel>flag_H \<kappa> A 1 *\<^sub>v b\<parallel>"
    proof -
      have t1: "\<parallel>tensor_vec (flag_H \<kappa> A 1 *\<^sub>v b) (unit_vec 3 1)\<parallel> = \<parallel>flag_H \<kappa> A 1 *\<^sub>v b\<parallel>"
        using vnorm_tensor[OF f3, where b = "unit_vec 3 1" and m = 3] by simp
      show ?thesis unfolding x_def vnorm_tensor[OF dim_win_state ft] t1 win_state_norm[OF N] by simp
    qed
    moreover have "\<parallel>flag_H \<kappa> A 1 *\<^sub>v b\<parallel> \<noteq> 0" using cpx_vec_length_zero_iff[of "flag_H \<kappa> A 1 *\<^sub>v b"] well f3 by simp
    ultimately show ?thesis by simp
  qed
  have dyx: "dim_vec y = dim_vec x" unfolding y_def xI using dCx dIb by simp
  have cl: "\<parallel>y - x\<parallel> \<le> \<rho> * \<parallel>x\<parallel>"
  proof -
    have "y - x = pflag 3 ?Pw (?Cx - ?Ib)" unfolding y_def xI by (rule pflag_minus[symmetric]) (simp only: dCx dIb)
    also have "\<dots> = pflag 3 ?Pw (pflag 3 ?P (?Cx - ?Ib))" by (rule pflag_sub) simp
    finally have "\<parallel>y - x\<parallel> \<le> \<parallel>pflag 3 ?P (?Cx - ?Ib)\<parallel>" using vnorm_pflag_le by metis
    also have "pflag 3 ?P (?Cx - ?Ib) = pflag 3 ?P ?Cx - pflag 3 ?P ?Ib" by (rule pflag_minus) (simp only: dCx dIb)
    also have "\<parallel>pflag 3 ?P ?Cx - pflag 3 ?P ?Ib\<parallel> \<le> \<rho> * \<parallel>pflag 3 ?P ?Ib\<parallel>"
    proof (rule power2_le_imp_le)
      have "\<rho>\<^sup>2 = 36 * pi ^ 4 * (4 + 2 * pi\<^sup>2) * \<kappa>\<^sup>2 / ((real N)\<^sup>2 * t0\<^sup>2)"
        unfolding \<rho>_def using NR t0 by (simp add: power_mult_distrib power_divide field_simps power2_eq_square power4_eq_xxxx)
      thus "\<parallel>pflag 3 ?P ?Cx - pflag 3 ?P ?Ib\<parallel>\<^sup>2 \<le> (\<rho> * \<parallel>pflag 3 ?P ?Ib\<parallel>)\<^sup>2"
        using flag_post_bound[OF A n0 t0 N k0 spec G Gh b] by (simp add: power_mult_distrib)
      show "0 \<le> \<rho> * \<parallel>pflag 3 ?P ?Ib\<parallel>" unfolding \<rho>_def using k0 NR t0 vnorm_ge0[of "pflag 3 ?P ?Ib"] by simp
    qed
    finally show ?thesis unfolding PI .
  qed
  show ?thesis by (rule normalized_close[OF dyx cl r1 x0])
qed

text \<open>If every eigenvalue is at least $1/\kappa$ then $g(A)=0$ and $f(A)=A^{-1}/(2\kappa)$: the
post-selected state is close to $\psi\otimes A^{-1}b/\norm{A^{-1}b}\otimes\ket{\mathrm{well}}$.\<close>

lemma flag_H_well_conditioned:
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and k0: "0 < \<kappa>" and wc: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> 1 / \<kappa> \<le> l"
  shows "flag_H \<kappa> A 2 = 0\<^sub>m n n" and "flag_H \<kappa> A 1 = complex_of_real (1 / (2 * \<kappa>)) \<cdot>\<^sub>m herm_inv A"
proof -
  have "flag_H \<kappa> A 2 = mat_fun (\<lambda>_. 0) A"
    unfolding flag_H_def by (rule mat_fun_cong[OF A]) (simp add: region1[OF k0] wc)
  also have "\<dots> = 0\<^sub>m n n" unfolding mat_fun_const[OF A] by (intro eq_matI) simp_all
  finally show "flag_H \<kappa> A 2 = 0\<^sub>m n n" .
  have "flag_H \<kappa> A 1 = mat_fun (\<lambda>x. complex_of_real (1 / (2 * \<kappa>)) * complex_of_real (inverse x)) A"
    unfolding flag_H_def
  proof (rule mat_fun_cong[OF A])
    fix l assume l: "l \<in> herm_spectrum A"
    have e: "1 / (2 * \<kappa> * l) = 1 / (2 * \<kappa>) * inverse l" by (simp add: field_simps)
    show "complex_of_real (if (1::nat) = 0 then filt_s \<kappa> l else if (1::nat) = 1 then filt_f \<kappa> l else filt_g \<kappa> l)
          = complex_of_real (1 / (2 * \<kappa>)) * complex_of_real (inverse l)"
      using region1(1)[OF k0 wc[OF l]] unfolding e by simp
  qed
  also have "\<dots> = mat_fun (\<lambda>_. complex_of_real (1 / (2 * \<kappa>))) A * herm_inv A"
    unfolding herm_inv_def by (rule mat_fun_mult[OF A, symmetric])
  also have "\<dots> = complex_of_real (1 / (2 * \<kappa>)) \<cdot>\<^sub>m herm_inv A"
  proof -
    have Hi: "herm_inv A \<in> carrier_mat n n" using A unfolding herm_inv_def by simp
    show ?thesis unfolding mat_fun_const[OF A]
      using mult_smult_assoc_mat[OF one_carrier_mat Hi, of "complex_of_real (1 / (2 * \<kappa>))"] left_mult_one_mat[OF Hi] by simp
  qed
  finally show "flag_H \<kappa> A 1 = complex_of_real (1 / (2 * \<kappa>)) \<cdot>\<^sub>m herm_inv A" .
qed

subsection \<open>The flag gates exist\<close>

lemma hflag_unit: "0 < \<kappa> \<Longrightarrow> \<parallel>hflag \<kappa> x\<parallel> = 1"
proof -
  assume k0: "0 < \<kappa>"
  have q: "(filt_f \<kappa> x)\<^sup>2 + (filt_g \<kappa> x)\<^sup>2 \<le> 1 / 4" by (rule fg_sq_le[OF k0])
  have s: "(filt_s \<kappa> x)\<^sup>2 = 1 - (filt_f \<kappa> x)\<^sup>2 - (filt_g \<kappa> x)\<^sup>2" unfolding filt_s_def using q by simp
  have "\<parallel>hflag \<kappa> x\<parallel>\<^sup>2 = (filt_s \<kappa> x)\<^sup>2 + (filt_f \<kappa> x)\<^sup>2 + (filt_g \<kappa> x)\<^sup>2"
    unfolding vnorm3_sq[OF dim_hflag] by (simp add: hflag_def numeral_2_eq_2)
  also have "\<dots> = 1" unfolding s by simp
  finally have "\<parallel>hflag \<kappa> x\<parallel>\<^sup>2 = 1\<^sup>2" by simp
  thus ?thesis using power2_eq_iff_nonneg[OF vnorm_ge0 zero_le_one] by simp
qed

text \<open>The Householder unitary of Lecture 3 for $w=(\ket0-h)/\norm{\ket0-h}$ maps $\ket0$ to any
unit vector $h$ with real $h_0<1$.\<close>

lemma householder_props:
  assumes h: "dim_vec h = d" "\<parallel>h\<parallel> = 1" and h0: "h $ 0 = complex_of_real r" "r < 1" and d0: "0 < d"
  defines "w \<equiv> vec_normalize (unit_vec d 0 - h)"
  shows "householder w \<in> carrier_mat d d" "unitary (householder w)" "householder w *\<^sub>v unit_vec d 0 = h"
proof -
  let ?v = "unit_vec d 0 - h"
  have dv: "dim_vec ?v = d" using h by simp
  have nv: "\<parallel>?v\<parallel>\<^sup>2 = 2 * (1 - r)"
  proof -
    have "complex_of_real (\<parallel>?v\<parallel>\<^sup>2) = \<langle>unit_vec d 0 - h|unit_vec d 0 - h\<rangle>" by (simp add: cpx_vec_length_inner_prod[symmetric])
    also have "\<dots> = \<langle>unit_vec d 0|unit_vec d 0\<rangle> - \<langle>unit_vec d 0|h\<rangle> - \<langle>h|unit_vec d 0\<rangle> + \<langle>h|h\<rangle>"
      using h by (simp add: Quantum.inner_prod_def atLeast0LessThan sum_subtractf algebra_simps sum.distrib)
    also have "\<langle>unit_vec d 0|unit_vec d 0\<rangle> = 1" using d0 by (simp add: Quantum.inner_prod_def atLeast0LessThan unit_vec_def if_distrib[of cnj] if_distrib[of "\<lambda>x. x * _"] if_distrib[of "\<lambda>x. _ * x"] sum.delta cong: if_cong)
    also have "\<langle>unit_vec d 0|h\<rangle> = complex_of_real r" using d0 h h0 by (simp add: Quantum.inner_prod_def atLeast0LessThan unit_vec_def if_distrib[of cnj] if_distrib[of "\<lambda>x. x * _"] if_distrib[of "\<lambda>x. _ * x"] sum.delta cong: if_cong)
    also have "\<langle>h|unit_vec d 0\<rangle> = complex_of_real r" using d0 h h0 by (simp add: Quantum.inner_prod_def atLeast0LessThan unit_vec_def if_distrib[of cnj] if_distrib[of "\<lambda>x. x * _"] if_distrib[of "\<lambda>x. _ * x"] sum.delta cong: if_cong)
    also have "\<langle>h|h\<rangle> = 1" unfolding cpx_vec_length_inner_prod[symmetric] h(2) by simp
    finally have "complex_of_real (\<parallel>?v\<parallel>\<^sup>2) = complex_of_real (2 * (1 - r))" by simp
    thus ?thesis by (simp only: of_real_eq_iff)
  qed
  have nv0: "0 < \<parallel>?v\<parallel>" using nv h0 vnorm_ge0[of ?v] by (cases "\<parallel>?v\<parallel> = 0") auto
  have v0: "?v \<noteq> 0\<^sub>v d" using nv0 cpx_vec_length_zero_iff[of ?v] dv by auto
  have w: "w = complex_of_real (1 / \<parallel>?v\<parallel>) \<cdot>\<^sub>v ?v" unfolding w_def vec_normalize_def using v0 dv by simp
  have dw: "dim_vec w = d" unfolding w_def using dv by simp
  show "householder w \<in> carrier_mat d d" unfolding householder_def using dw by simp
  have nw: "\<parallel>w\<parallel> = 1" unfolding w_def by (rule normalized_vec_norm[OF carrier_vecI[OF dv] v0])
  show "unitary (householder w)" by (rule householder_unitary[OF nw])
  have v_e0: "\<langle>?v|unit_vec d 0\<rangle> = complex_of_real (1 - r)"
    using d0 h h0 by (simp add: Quantum.inner_prod_def atLeast0LessThan unit_vec_def if_distrib[of cnj] if_distrib[of "\<lambda>x. x * _"] if_distrib[of "\<lambda>x. _ * x"] sum.delta cong: if_cong)
  have "householder w *\<^sub>v unit_vec d 0 = unit_vec d 0 - (2 * \<langle>w|unit_vec d 0\<rangle>) \<cdot>\<^sub>v w"
    by (rule householder_mult_vec) (simp add: dw)
  also have "(2 * \<langle>w|unit_vec d 0\<rangle>) \<cdot>\<^sub>v w = ?v"
  proof -
    have "\<langle>w|unit_vec d 0\<rangle> = cnj (complex_of_real (1 / \<parallel>?v\<parallel>)) * \<langle>?v|unit_vec d 0\<rangle>"
      unfolding w by (rule inner_prod_left_smult') (simp add: h)
    hence "\<langle>w|unit_vec d 0\<rangle> = complex_of_real (1 / \<parallel>?v\<parallel>) * complex_of_real (1 - r)"
      unfolding v_e0 by simp
    hence "2 * \<langle>w|unit_vec d 0\<rangle> * complex_of_real (1 / \<parallel>?v\<parallel>) = complex_of_real (2 * (1 - r) / \<parallel>?v\<parallel>\<^sup>2)"
      by (simp add: power2_eq_square field_simps)
    also have "2 * (1 - r) / \<parallel>?v\<parallel>\<^sup>2 = 1" unfolding nv using h0 by simp
    finally have c: "2 * \<langle>w|unit_vec d 0\<rangle> * complex_of_real (1 / \<parallel>?v\<parallel>) = 1" by simp
    have "(2 * \<langle>w|unit_vec d 0\<rangle>) \<cdot>\<^sub>v w = (2 * \<langle>w|unit_vec d 0\<rangle>) \<cdot>\<^sub>v (complex_of_real (1 / \<parallel>?v\<parallel>) \<cdot>\<^sub>v ?v)"
      by (rule arg_cong[where f = "\<lambda>x. (2 * \<langle>w|unit_vec d 0\<rangle>) \<cdot>\<^sub>v x", OF w])
    also have "\<dots> = (2 * \<langle>w|unit_vec d 0\<rangle> * complex_of_real (1 / \<parallel>?v\<parallel>)) \<cdot>\<^sub>v ?v" by (rule smult_smult_assoc)
    also have "\<dots> = ?v" unfolding c by simp
    finally show ?thesis .
  qed
  also have "unit_vec d 0 - ?v = h" using h by (intro eq_vecI) simp_all
  finally show "householder w *\<^sub>v unit_vec d 0 = h" .
qed

text \<open>So gates with $G_k\ket0=\ket{h(\tilde\lambda_k)}$ exist: the hypotheses of Theorem 1 are met.\<close>

lemma flag_gates_exist:
  assumes k0: "0 < \<kappa>"
  shows "\<exists>G. \<forall>x. G x \<in> carrier_mat 3 3 \<and> unitary (G x) \<and> G x *\<^sub>v unit_vec 3 0 = hflag \<kappa> x"
proof -
  have g: "\<exists>M. M \<in> carrier_mat 3 3 \<and> unitary M \<and> M *\<^sub>v unit_vec 3 0 = hflag \<kappa> x" for x
  proof (cases "filt_s \<kappa> x < 1")
    case True
    have h0: "hflag \<kappa> x $ 0 = complex_of_real (filt_s \<kappa> x)" by (simp add: hflag_def)
    have d3: "0 < (3::nat)" by simp
    note hp = householder_props[OF dim_hflag hflag_unit[OF k0] h0 True d3]
    show ?thesis by (rule exI[of _ "householder (vec_normalize (unit_vec 3 0 - hflag \<kappa> x))"]) (intro conjI hp)
  next
    case False
    have f1: "filt_s \<kappa> x \<le> 1" unfolding filt_s_def using fg_sq_le[OF k0, of x] by simp
    hence s1: "filt_s \<kappa> x = 1" using False by simp
    have "(filt_f \<kappa> x)\<^sup>2 + (filt_g \<kappa> x)\<^sup>2 = 0"
    proof -
      have "1 = sqrt (1 - (filt_f \<kappa> x)\<^sup>2 - (filt_g \<kappa> x)\<^sup>2)" using s1 unfolding filt_s_def by simp
      hence "1 - (filt_f \<kappa> x)\<^sup>2 - (filt_g \<kappa> x)\<^sup>2 = 1" using fg_sq_le[OF k0, of x] by (metis real_sqrt_eq_1_iff)
      thus ?thesis by linarith
    qed
    hence "filt_f \<kappa> x = 0" "filt_g \<kappa> x = 0" by (simp_all add: sum_power2_eq_zero_iff)
    hence "hflag \<kappa> x = unit_vec 3 0" using s1 by (intro eq_vecI) (auto simp: hflag_def unit_vec_def)
    moreover have "(1\<^sub>m 3 :: complex Matrix.mat) *\<^sub>v unit_vec 3 0 = unit_vec 3 0" using one_mult_mat_vec[of "unit_vec 3 0 :: complex Matrix.vec" 3] by simp
    ultimately show ?thesis by (intro exI[of _ "1\<^sub>m 3"] conjI one_carrier_mat id_is_unitary) simp
  qed
  thus ?thesis by metis
qed

end
