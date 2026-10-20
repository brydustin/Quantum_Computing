theory QFT_Fourier
  imports Phase_Estimation
begin

section \<open>The AFP Fourier transform circuit is the Fourier matrix\<close>

text \<open>The circuit \<^const>\<open>ordered_QFT\<close> of the AFP entry \<open>Quantum_Fourier_Transform\<close> is shown
there to map $\ket j$ to the product state
$2^{-n/2}\bigotimes_{l=1}^n(\ket0+e^{2\pi ij/2^l}\ket1)$.  Its $k$-th entry is
$2^{-n/2}e^{2\pi ijk/2^n}$ (the binary digits of $k$ select the factors), so the circuit is
$F_{2^n}$ and phase estimation runs on it.\<close>

lemma kron_phase_index:
  fixes f :: "nat \<Rightarrow> complex Matrix.mat" and j :: nat
  assumes f: "\<And>l. f l \<in> carrier_mat 2 1"
      and fi: "\<And>l c. c < 2 \<Longrightarrow> f l $$ (c, 0) = exp (2 * \<i> * pi * of_nat j * of_nat c / 2 ^ l)"
  shows "1 \<le> a \<Longrightarrow> nat (b - a + 1) = m \<Longrightarrow> k < 2 ^ m \<Longrightarrow>
         kron f (map nat [a..b]) $$ (k, 0) = exp (2 * \<i> * pi * of_nat j * of_nat k / 2 ^ nat b)"
proof (induction m arbitrary: a k)
  case 0
  hence "[a..b] = []" by simp
  moreover have "k = 0" using 0 by simp
  ultimately show ?case by simp
next
  case (Suc m)
  have ab: "a \<le> b" using Suc.prems by linarith
  have l: "map nat [a..b] = nat a # map nat [a + 1..b]" using upto_rec1[OF ab] by simp
  have fd: "\<forall>l. dim_row (f l) = 2 \<and> dim_col (f l) = 1" using f by auto
  have len: "length (map nat [a + 1..b]) = m" using Suc.prems by simp
  have Kc: "kron f (map nat [a + 1..b]) \<in> carrier_mat (2 ^ m) 1"
    using kron_carrier_mat[OF fd, of "map nat [a + 1..b]"] len by simp
  define c r where "c = k div 2 ^ m" and "r = k mod 2 ^ m"
  have c: "c < 2" unfolding c_def using Suc.prems(3) by (simp add: less_mult_imp_div_less mult.commute)
  have r: "r < 2 ^ m" unfolding r_def by simp
  have kcr: "k = c * 2 ^ m + r" unfolding c_def r_def by (rule div_mult_mod_eq[symmetric])
  have bm: "nat b = nat a + m" using Suc.prems by linarith
  have IH: "kron f (map nat [a + 1..b]) $$ (r, 0) = exp (2 * \<i> * pi * of_nat j * of_nat r / 2 ^ nat b)"
    by (rule Suc.IH) (use Suc.prems r in simp_all)
  have "(f (nat a) \<Otimes> kron f (map nat [a + 1..b])) $$ (k, 0) =
        f (nat a) $$ (k div 2 ^ m, 0 div 1) * kron f (map nat [a + 1..b]) $$ (k mod 2 ^ m, 0 mod 1)"
    by (rule index_tensor_mat) (use carrier_matD[OF f[of "nat a"]] carrier_matD[OF Kc] Suc.prems(3) in \<open>auto simp: mult.commute\<close>)
  hence "kron f (map nat [a..b]) $$ (k, 0) = f (nat a) $$ (c, 0) * kron f (map nat [a + 1..b]) $$ (r, 0)"
    unfolding l kron.simps c_def r_def by simp
  also have "\<dots> = exp (2 * \<i> * pi * of_nat j * of_nat c / 2 ^ nat a + 2 * \<i> * pi * of_nat j * of_nat r / 2 ^ nat b)"
    unfolding fi[OF c] IH by (simp add: exp_add)
  also have "2 * \<i> * pi * of_nat j * of_nat c / 2 ^ nat a + 2 * \<i> * pi * of_nat j * of_nat r / 2 ^ nat b =
             2 * \<i> * pi * of_nat j * of_nat k / (2 ^ nat b :: complex)"
    unfolding kcr bm by (simp add: power_add field_simps)
  finally show ?case .
qed

lemma QFT_product_representation_index:
  assumes k: "k < 2 ^ n"
  shows "QFT_product_representation j n $$ (k, 0) =
         cis (2 * pi * real j * real k / 2 ^ n) / complex_of_real (sqrt (2 ^ n))"
proof -
  let ?f = "\<lambda>l::nat. |zero\<rangle> + exp (2 * \<i> * pi * j / 2 ^ l) \<cdot>\<^sub>m |one\<rangle>"
  have f: "?f l \<in> carrier_mat 2 1" for l by (auto simp: ket_vec_def)
  have fi: "?f l $$ (c, 0) = exp (2 * \<i> * pi * of_nat j * of_nat c / 2 ^ l)" if "c < 2" for l c
    using less_2_cases[OF that] by (auto simp: ket_vec_def)
  have len: "nat (int n - 1 + 1) = n" by simp
  have fd: "\<forall>l. dim_row (?f l) = 2 \<and> dim_col (?f l) = 1"
    by (intro allI conjI) (rule carrier_matD[OF f])+
  have Kc: "kron ?f (map nat [1..int n]) \<in> carrier_mat (2 ^ n) 1"
    using kron_carrier_mat[OF fd, of "map nat [1..int n]"] by simp
  have "QFT_product_representation j n $$ (k, 0) = 1 / sqrt (2 ^ n) * kron ?f (map nat [1..int n]) $$ (k, 0)"
    unfolding QFT_product_representation_def using Kc k by simp
  also have "kron ?f (map nat [1..int n]) $$ (k, 0) = exp (2 * \<i> * pi * of_nat j * of_nat k / 2 ^ n)"
    using kron_phase_index[OF f fi, of 1 "int n" n k] k by simp
  also have "exp (2 * \<i> * pi * of_nat j * of_nat k / 2 ^ n) = cis (2 * pi * real j * real k / 2 ^ n)"
    by (simp add: cis_conv_exp mult_ac)
  finally show ?thesis by simp
qed

theorem ordered_QFT_fourier: "ordered_QFT n = fourier (2 ^ n)"
proof (rule eq_matI)
  fix k j assume "k < dim_row (fourier (2 ^ n))" "j < dim_col (fourier (2 ^ n))"
  hence k: "k < 2 ^ n" and j: "j < 2 ^ n" by simp_all
  have Qc: "ordered_QFT n \<in> carrier_mat (2 ^ n) (2 ^ n)"
    unfolding ordered_QFT_def by (rule mult_carrier_mat[OF reverse_qubits_carrier_mat QFT_carrier_mat])
  have "(ordered_QFT n * |state_basis n j\<rangle>) $$ (k, 0) =
        (\<Sum>ka<2 ^ n. ordered_QFT n $$ (k, ka) * (if ka = j then 1 else 0))"
    using Qc k j by (simp add: state_basis_def ket_vec_def scalar_prod_def)
  also have "\<dots> = (\<Sum>ka<2 ^ n. if ka = j then ordered_QFT n $$ (k, j) else 0)" by (rule sum.cong) auto
  also have "\<dots> = ordered_QFT n $$ (k, j)" using j by simp
  finally have "ordered_QFT n $$ (k, j) = (ordered_QFT n * |state_basis n j\<rangle>) $$ (k, 0)" ..
  also have "\<dots> = QFT_product_representation j n $$ (k, 0)" by (simp add: ordered_QFT_is_correct j)
  also have "\<dots> = fourier (2 ^ n) $$ (k, j)"
    using k j by (simp add: QFT_product_representation_index fourier_index mult_ac)
  finally show "ordered_QFT n $$ (k, j) = fourier (2 ^ n) $$ (k, j)" .
qed (use carrier_matD[OF mult_carrier_mat[OF reverse_qubits_carrier_mat QFT_carrier_mat]] in \<open>simp_all add: ordered_QFT_def\<close>)

text \<open>Phase estimation with the AFP circuit: the theorems of \<open>Phase_Estimation\<close> hold with
$F_{2^t}$ replaced by \<^term>\<open>ordered_QFT t\<close>.\<close>

corollary phase_estimation_circuit:
  fixes U :: "complex Matrix.mat"
  assumes "U \<in> carrier_mat m m" "dim_vec u = m" "U *\<^sub>v u = cis (2 * pi * \<phi>) \<cdot>\<^sub>v u"
  shows "(((ordered_QFT t)\<^sup>\<dagger>) \<Otimes> 1\<^sub>m m) *\<^sub>v (ctrl_pow (2 ^ t) m U *\<^sub>v tensor_vec (uniform_state (2 ^ t)) u) =
         tensor_vec (Matrix.vec (2 ^ t) (pe_amp (2 ^ t) \<phi>)) u"
  unfolding ordered_QFT_fourier by (rule phase_estimation[OF assms])

end
