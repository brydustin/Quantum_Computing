theory HHL_Suzuki
  imports Hermitian_Functional_Calculus.Suzuki_Error HHL_Sparse_Split
begin

section \<open>Higher-order simulation for HHL\<close>

text \<open>HHL with $e^{it_0A}$, $A=H_1+\dots+H_m$, simulated by Suzuki's formula.\<close>

theorem hhl_suzuki_window_error:
  fixes Hs :: "complex Matrix.mat list" and b :: "complex Matrix.vec" and n k r :: nat and t0 L :: real
  defines "A \<equiv> hsum n Hs"
  assumes Hs: "\<forall>H \<in> set Hs. herm_bounded n L H" and L: "0 \<le> L" and t0: "0 < t0" and N: "2 \<le> N"
      and C: "0 < C" and th: "0 < \<theta>" "\<theta> < 1" and lmin: "2 * C / \<theta> \<le> lmin"
      and spec: "\<And>l. l \<in> herm_spectrum A \<Longrightarrow> lmin \<le> l \<and> t0 * l \<le> pi / 2"
      and b: "dim_vec b = n" and e: "0 < \<epsilon>"
      and NQ: "sqrt (8 * pi\<^sup>2 * (2 + pi\<^sup>2) * \<theta> ^ 4 / (t0\<^sup>2 * C\<^sup>2 * (1 - \<theta>\<^sup>2)) + 512 * pi ^ 6 / (t0 ^ 4 * lmin ^ 4)) / \<epsilon> \<le> real N"
      and r: "0 < r"
  defines "V \<equiv> sprod n (t0 / real r) (suzuki k Hs) ^\<^sub>m r"
    and "\<eta> \<equiv> real r * ((2 * real (length (suzuki k Hs)) + 1) * (lam L (suzuki k Hs) * t0 / real r) ^ (2 * k + 3)
             * exp (lam L (suzuki k Hs) * t0 / real r) / fact (2 * k + 3))"
  shows "\<parallel>hhl_sim A t0 N C V *\<^sub>v tensor_vec (win_state N) (tensor_vec b (unit_vec 2 0)) -
           tensor_vec (win_state N)
             (tensor_vec (mat_fun (\<lambda>x. complex_of_real (sqrt (1 - (C / x)\<^sup>2))) A *\<^sub>v b) (unit_vec 2 0) +
              tensor_vec ((complex_of_real C \<cdot>\<^sub>m herm_inv A) *\<^sub>v b) (unit_vec 2 1))\<parallel>
         \<le> (\<epsilon> + 2 * real (N - 1) * \<eta>) * \<parallel>b\<parallel>"
proof -
  have Fh: "\<forall>x \<in> set (suzuki k Hs). herm_bounded n L (snd x)" using Hs suzuki_snd by blast
  note Hh = herm_boundedD[OF hsum_herm_bounded[OF Hs]]
  note U = sprod_carrier_unitary[OF Fh, of "t0 / real r"]
  have Vc: "V \<in> carrier_mat n n" unfolding V_def by (rule pow_carrier_mat[OF conjunct1[OF U]])
  have Vu: "Quantum.unitary V" unfolding V_def by (rule unitary_pow[OF conjunct1[OF U] conjunct2[OF U]])
  have c: "op_close n \<eta> V (evolution A t0)"
    using suzuki_error[OF Hs L r, of k t0] unfolding V_def \<eta>_def A_def abs_of_pos[OF t0] .
  have l: "0 \<le> lam L (suzuki k Hs) * t0 / real r" using lam_nonneg[OF L, of "suzuki k Hs"] t0 by simp
  have eta: "0 \<le> \<eta>" unfolding \<eta>_def using l by simp
  show ?thesis
    by (rule hhl_sim_window_error[OF Hh(1,2)[folded A_def] t0 N C th lmin spec b e NQ Vc Vu c eta])
qed

text \<open>For $s$-sparse $A$, Suzuki's formula over the $2s$ one-sparse parts of \<open>sparse_split\<close>.\<close>

theorem sparse_suzuki:
  fixes k :: nat and t :: real
  assumes A: "A \<in> carrier_mat n n" "hermitian A" and s: "1 \<le> s"
      and L: "0 \<le> L" and Lb: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> cmod (A $$ (i, j)) \<le> L"
      and cov: "edge_cover n (2 * s - 1) p (edges n A)" and r: "0 < r"
  defines "F \<equiv> suzuki k (sparse_parts n A (2 * s - 1) p)"
  shows "op_close n (real r * ((4 * 5 ^ k * real (2 * s) + 1) * (lam L F * \<bar>t\<bar> / real r) ^ (2 * k + 3)
             * exp (lam L F * \<bar>t\<bar> / real r) / fact (2 * k + 3)))
           (sprod n (t / real r) F ^\<^sub>m r) (evolution A t)"
    and "2 * real s * L \<le> lam L F"
proof -
  have pinv: "\<And>c. c < 2 * s - 1 \<Longrightarrow> invol n (p c)" using cov unfolding edge_cover_def by blast
  have len: "length (sparse_parts n A (2 * s - 1) p) = 2 * s" using s by (simp add: sparse_parts_def)
  have sum: "hsum n (sparse_parts n A (2 * s - 1) p) = A"
    by (rule sparse_parts_sum[OF A(1) hermitian_zero_sym[OF A] cov])
  have Hs: "\<forall>H \<in> set (sparse_parts n A (2 * s - 1) p). herm_bounded n L H"
    using sparse_parts_bounded[where K = "2 * s - 1" and p = p, OF A pinv L Lb] by blast
  have lF: "2 * real (length F) = 4 * 5 ^ k * real (2 * s)" unfolding F_def length_suzuki len by simp
  show "op_close n (real r * ((4 * 5 ^ k * real (2 * s) + 1) * (lam L F * \<bar>t\<bar> / real r) ^ (2 * k + 3)
             * exp (lam L F * \<bar>t\<bar> / real r) / fact (2 * k + 3)))
           (sprod n (t / real r) F ^\<^sub>m r) (evolution A t)"
    using suzuki_error[OF Hs L r, of k t] unfolding F_def[symmetric] sum lF .
  show "2 * real s * L \<le> lam L F" using lam_suzuki[OF L, of _ k] len unfolding F_def by (metis of_nat_mult of_nat_numeral)
qed

end
