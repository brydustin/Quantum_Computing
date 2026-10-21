theory QPE_Register
  imports Phase_Estimation Isabelle_Marries_Dirac.Deutsch_Jozsa
begin

section \<open>Preparing the phase-estimation register\<close>

text \<open>The clock register of phase estimation and HHL starts in $\frac1{\sqrt N}\sum_k\ket k$.  It is
prepared from $\ket{0\cdots0}$ by the Hadamard layer $H^{\otimes n}$ ($N=2^n$), or by $F_N$;
\<open>iter_tensor_of_H_on_zero_tensor\<close> of the AFP entry \<open>Isabelle_Marries_Dirac\<close> gives the
first in column-matrix form.  The layer is its own inverse, so it also resets the register.\<close>

lemma fourier_zero:
  assumes N: "0 < N"
  shows "fourier N *\<^sub>v unit_vec N 0 = uniform_state N"
proof (rule eq_vecI)
  fix i assume "i < dim_vec (uniform_state N)"
  hence i: "i < N" by (simp add: uniform_state_def)
  have "(fourier N *\<^sub>v unit_vec N 0) $ i = (\<Sum>k<N. fourier N $$ (i, k) * unit_vec N 0 $ k)"
    using i by (simp add: scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k\<in>{0}. fourier N $$ (i, k) * unit_vec N 0 $ k)"
    using N by (intro sum.mono_neutral_cong_right) auto
  also have "\<dots> = uniform_state N $ i" using i N by (simp add: fourier_index uniform_state_def)
  finally show "(fourier N *\<^sub>v unit_vec N 0) $ i = uniform_state N $ i" .
qed (simp add: uniform_state_def)

lemma iter_tensor_zero: "1 \<le> n \<Longrightarrow> |zero\<rangle> \<otimes>\<^bsup>n\<^esup> = |unit_vec (2 ^ n) 0\<rangle>"
proof (induction n rule: nat_induct_at_least)
  case base
  show ?case by simp
next
  case (Suc n)
  have "|zero\<rangle> \<otimes>\<^bsup>Suc n\<^esup> = |zero\<rangle> \<Otimes> |unit_vec (2 ^ n) 0\<rangle>" using Suc by (simp add: iter_tensor_suc)
  also have "\<dots> = |unit_vec (2 ^ Suc n) 0\<rangle>"
  proof (rule eq_matI)
    fix i j assume "i < dim_row |unit_vec (2 ^ Suc n) 0\<rangle>" "j < dim_col |unit_vec (2 ^ Suc n) 0\<rangle>"
    hence ij: "i < 2 * 2 ^ n" "j = 0" by (simp_all add: ket_vec_def)
    have "( |zero\<rangle> \<Otimes> |unit_vec (2 ^ n) 0\<rangle>) $$ (i, j) = |zero\<rangle> $$ (i div 2 ^ n, 0) * |unit_vec (2 ^ n) 0\<rangle> $$ (i mod 2 ^ n, 0)"
      using index_tensor_mat[of "|zero\<rangle>" 2 1 "|unit_vec (2 ^ n) 0\<rangle>" "2 ^ n" 1 i 0] ij by (simp add: ket_vec_def)
    also have "\<dots> = (if i = 0 then 1 else 0)"
    proof -
      have "i div 2 ^ n < 2" using ij by (simp add: less_mult_imp_div_less mult.commute)
      moreover have "i div 2 ^ n = 0 \<and> i mod 2 ^ n = 0 \<longleftrightarrow> i = 0" by (metis div_mult_mod_eq mult_0_right add_0 div_0 mod_0)
      ultimately show ?thesis by (auto simp: ket_vec_def unit_vec_def)
    qed
    finally show "( |zero\<rangle> \<Otimes> |unit_vec (2 ^ n) 0\<rangle>) $$ (i, j) = |unit_vec (2 ^ Suc n) 0\<rangle> $$ (i, j)"
      using ij by (simp add: ket_vec_def unit_vec_def)
  qed (simp_all add: ket_vec_def)
  finally show ?case .
qed

text \<open>The Hadamard layer prepares the uniform register: $H^{\otimes n}\ket{0\cdots0}=\frac1{\sqrt{2^n}}\sum_k\ket k$.\<close>

theorem hadamard_layer_zero:
  assumes n: "1 \<le> n"
  shows "(Hadamard \<otimes>\<^bsup>n\<^esup>) *\<^sub>v unit_vec (2 ^ n) 0 = uniform_state (2 ^ n)"
proof -
  have dH: "dim_col (H \<otimes>\<^bsup>n\<^esup>) = 2 ^ n" "dim_row (H \<otimes>\<^bsup>n\<^esup>) = 2 ^ n" using n by (simp_all add: H_def)
  have m: "(H \<otimes>\<^bsup>n\<^esup>) * |unit_vec (2 ^ n) 0\<rangle> = \<psi>\<^sub>1\<^sub>0 n"
    using iter_tensor_of_H_on_zero_tensor[OF n] iter_tensor_zero[OF n] by simp
  show ?thesis unfolding Hadamard_def
  proof (rule eq_vecI)
    fix i assume "i < dim_vec (uniform_state (2 ^ n))"
    hence i: "i < 2 ^ n" by (simp add: uniform_state_def)
    have "((H \<otimes>\<^bsup>n\<^esup>) *\<^sub>v unit_vec (2 ^ n) 0) $ i = ((H \<otimes>\<^bsup>n\<^esup>) * |unit_vec (2 ^ n) 0\<rangle>) $$ (i, 0)"
      using i dH by (simp add: ket_vec_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = uniform_state (2 ^ n) $ i" unfolding m using i by (simp add: uniform_state_def real_sqrt_power)
    finally show "((H \<otimes>\<^bsup>n\<^esup>) *\<^sub>v unit_vec (2 ^ n) 0) $ i = uniform_state (2 ^ n) $ i" .
  qed (use dH in \<open>simp add: uniform_state_def\<close>)
qed

lemma hadamard_layer_carrier: "1 \<le> n \<Longrightarrow> Hadamard \<otimes>\<^bsup>n\<^esup> \<in> carrier_mat (2 ^ n) (2 ^ n)"
  by (rule carrier_matI) (simp_all add: Hadamard_def H_def)

lemma hadamard_layer_square: "1 \<le> n \<Longrightarrow> (Hadamard \<otimes>\<^bsup>n\<^esup>) * (Hadamard \<otimes>\<^bsup>n\<^esup>) = 1\<^sub>m (2 ^ n)"
proof (induction n rule: nat_induct_at_least)
  case base
  show ?case using hadamard_squared by simp
next
  case (Suc n)
  have "(Hadamard \<otimes>\<^bsup>Suc n\<^esup>) * (Hadamard \<otimes>\<^bsup>Suc n\<^esup>) = (Hadamard * Hadamard) \<Otimes> ((Hadamard \<otimes>\<^bsup>n\<^esup>) * (Hadamard \<otimes>\<^bsup>n\<^esup>))"
    by (rule iter_tensor_mult_distr) (use Suc in \<open>simp_all add: Hadamard_def H_def\<close>)
  also have "\<dots> = 1\<^sub>m 2 \<Otimes> 1\<^sub>m (2 ^ n)" unfolding hadamard_squared Suc.IH ..
  also have "\<dots> = 1\<^sub>m (2 ^ Suc n)" using tensor_mat_id[of 2 "2 ^ n"] by simp
  finally show ?case .
qed

lemma hadamard_layer_unitary: "1 \<le> n \<Longrightarrow> unitary (Hadamard \<otimes>\<^bsup>n\<^esup>)"
  using iter_tensor_of_H_is_gate by (simp add: gate_def Hadamard_def)

text \<open>Applied to the uniform register, the layer returns it to $\ket{0\cdots0}$.\<close>

lemma hadamard_layer_uniform: "1 \<le> n \<Longrightarrow> (Hadamard \<otimes>\<^bsup>n\<^esup>) *\<^sub>v uniform_state (2 ^ n) = unit_vec (2 ^ n) 0"
proof -
  assume n: "1 \<le> n"
  have "(Hadamard \<otimes>\<^bsup>n\<^esup>) *\<^sub>v uniform_state (2 ^ n) = (Hadamard \<otimes>\<^bsup>n\<^esup>) *\<^sub>v ((Hadamard \<otimes>\<^bsup>n\<^esup>) *\<^sub>v unit_vec (2 ^ n) 0)"
    unfolding hadamard_layer_zero[OF n] ..
  also have "\<dots> = ((Hadamard \<otimes>\<^bsup>n\<^esup>) * (Hadamard \<otimes>\<^bsup>n\<^esup>)) *\<^sub>v unit_vec (2 ^ n) 0"
    by (rule assoc_mult_mat_vec[symmetric]) (use hadamard_layer_carrier[OF n] in auto)
  also have "\<dots> = unit_vec (2 ^ n) 0" unfolding hadamard_layer_square[OF n] by simp
  finally show ?thesis .
qed

end
