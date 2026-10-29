theory Phase_Estimation_Gates
  imports Controlled_Laplacian
begin

section \<open>Phase estimation from compiled controlled calls\<close>

subsection \<open>Adjoints and blocks\<close>

lemma stands_for_dagger:
  assumes S: "stands_for A N U G" and U: "(U\<^sup>\<dagger>) * U = 1\<^sub>m (A * N)" and G: "G * (G\<^sup>\<dagger>) = 1\<^sub>m N"
  shows "stands_for A N (U\<^sup>\<dagger>) (G\<^sup>\<dagger>)"
proof -
  have Uc: "U \<in> carrier_mat (A * N) (A * N)" and Gc: "G \<in> carrier_mat N N" and e: "U * anc A N = anc A N * G"
    using S by (simp_all add: stands_for_def)
  have Ud: "U\<^sup>\<dagger> \<in> carrier_mat (A * N) (A * N)" and Gd: "G\<^sup>\<dagger> \<in> carrier_mat N N" using Uc Gc by (simp_all add: dagger_carrier)
  have ac: "anc A N \<in> carrier_mat (A * N) N" by simp
  have "U\<^sup>\<dagger> * anc A N = U\<^sup>\<dagger> * (anc A N * (G * (G\<^sup>\<dagger>)))" unfolding G by simp
  also have "\<dots> = U\<^sup>\<dagger> * ((anc A N * G) * (G\<^sup>\<dagger>))" by (simp only: assoc_mult_mat[OF ac Gc Gd])
  also have "\<dots> = U\<^sup>\<dagger> * (U * (anc A N * (G\<^sup>\<dagger>)))" unfolding e[symmetric] by (simp only: assoc_mult_mat[OF Uc ac Gd])
  also have "\<dots> = (U\<^sup>\<dagger> * U) * (anc A N * (G\<^sup>\<dagger>))" by (rule assoc_mult_mat[OF Ud Uc mult_carrier_mat[OF ac Gd], symmetric])
  also have "\<dots> = anc A N * (G\<^sup>\<dagger>)" unfolding U using ac Gd by simp
  finally show ?thesis using Ud Gd by (simp add: stands_for_def)
qed

lemma list_all2_replicate': "P x y \<Longrightarrow> list_all2 P (replicate n x) (replicate n y)"
  by (induction n) simp_all

lemma list_all2_blocks:
  assumes "\<And>j. j < k \<Longrightarrow> P (Us j) (Gs j)"
  shows "list_all2 P (concat (map (\<lambda>j. replicate (c j) (Us j)) [0..<k])) (concat (map (\<lambda>j. replicate (c j) (Gs j)) [0..<k]))"
  using assms by (induction k) (auto intro!: list_all2_appendI list_all2_replicate')

subsection \<open>The controlled powers\<close>

text \<open>Given gate lists \<open>Cs j\<close> for the singly controlled calls $\mathrm{C}_jV$, phase estimation runs
\<open>Cs j\<close> $2^j$ times for each clock qubit $j$.\<close>

definition pe_list :: "(nat \<Rightarrow> complex Matrix.mat list) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "pe_list Cs k = concat (concat (map (\<lambda>j. replicate (2 ^ j) (Cs j)) [0..<k]))"

lemma length_pe_list: "length (pe_list Cs k) = (\<Sum>j<k. 2 ^ j * length (Cs j))"
  by (induction k) (simp_all add: pe_list_def length_concat sum_list_replicate)

theorem pe_list_props:
  assumes C: "\<And>j. j < k \<Longrightarrow> stands_for A (2 ^ k * M) (circuit_mat (A * (2 ^ k * M)) (Cs j)) (ctrl_bit (2 ^ k) M j G)"
    and el: "\<And>j U. j < k \<Longrightarrow> U \<in> set (Cs j) \<Longrightarrow> U \<in> carrier_mat (A * (2 ^ k * M)) (A * (2 ^ k * M))"
    and G: "G \<in> carrier_mat M M"
  shows "stands_for A (2 ^ k * M) (circuit_mat (A * (2 ^ k * M)) (pe_list Cs k)) (ctrl_pow (2 ^ k) M G)"
proof -
  let ?K = "A * (2 ^ k * M)"
  let ?B = "concat (map (\<lambda>j. replicate (2 ^ j) (Cs j)) [0..<k])"
  have "circuit_mat ?K (pe_list Cs k) = circuit_mat ?K (map (circuit_mat ?K) ?B)"
    unfolding pe_list_def by (rule circuit_mat_concat) (use el in auto)
  also have "map (circuit_mat ?K) ?B = concat (map (\<lambda>j. replicate (2 ^ j) (circuit_mat ?K (Cs j))) [0..<k])"
    by (simp add: map_concat comp_def)
  finally have c: "circuit_mat ?K (pe_list Cs k) = circuit_mat ?K (concat (map (\<lambda>j. replicate (2 ^ j) (circuit_mat ?K (Cs j))) [0..<k]))" .
  have "stands_for A (2 ^ k * M) (circuit_mat ?K (concat (map (\<lambda>j. replicate (2 ^ j) (circuit_mat ?K (Cs j))) [0..<k])))
      (circuit_mat (2 ^ k * M) (concat (map (\<lambda>j. replicate (2 ^ j) (ctrl_bit (2 ^ k) M j G)) [0..<k])))"
    by (rule stands_for_circuit[OF list_all2_blocks[where P = "stands_for A (2 ^ k * M)" and Us = "\<lambda>j. circuit_mat ?K (Cs j)"
          and Gs = "\<lambda>j. ctrl_bit (2 ^ k) M j G", OF C]])
  thus ?thesis unfolding c ctrl_pow_queries(1)[OF G] .
qed

subsection \<open>Phase estimation for the shifted Laplacian\<close>

text \<open>The controlled call $\mathrm{C}_jV$ with $V$ the $r$-step Trotter product for $L+\mu I$.\<close>

definition cvl :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "cvl m k a \<mu> t r j = concat (replicate r (clap_step m k a j \<mu> (t / real r)))"

lemma tensor_pow_one:
  assumes E: "E \<in> carrier_mat n n" and n: "0 < n"
  shows "(E \<Otimes> 1\<^sub>m 2) ^\<^sub>m r = E ^\<^sub>m r \<Otimes> 1\<^sub>m 2"
proof (induction r)
  case 0
  show ?case using E by (simp add: tensor_mat_id)
next
  case (Suc r)
  have "(E \<Otimes> 1\<^sub>m 2) ^\<^sub>m Suc r = (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2) * (E \<Otimes> 1\<^sub>m 2)" using Suc by simp
  also have "\<dots> = (E ^\<^sub>m r * E) \<Otimes> (1\<^sub>m 2 * 1\<^sub>m 2)"
    by (rule mult_distr_tensor[symmetric]) (use E n in simp_all)
  finally show ?case by simp
qed

theorem cvl_props:
  fixes t :: real and r :: nat
  assumes m: "2 \<le> m" and a: "m \<le> a" and j: "j < k" and mu: "0 \<le> \<mu>"
  defines "E \<equiv> evolution_product (2 ^ m) (t / real r) (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m)))"
  shows "stands_for (2 ^ a) (2 ^ Suc (m + k)) (circuit_mat (2 ^ (Suc (m + k) + a)) (cvl m k a \<mu> t r j))
      (ctrl_bit (2 ^ k) (2 ^ m * 2) j (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2))"
    "\<forall>U \<in> set (cvl m k a \<mu> t r j). elementary (2 ^ (Suc (m + k) + a)) U"
    "length (cvl m k a \<mu> t r j) \<le> r * (2 * (m * (m + 2) * (6 * (Suc (m + k) + a) + 7)) + 3 * (4 * (Suc (m + k) + a) + 1))"
proof -
  let ?K = "Suc (m + k) + a" and ?S = "clap_step m k a j \<mu> (t / real r)"
  note S = clap_step_props[OF m a j mu, of "t / real r", folded E_def]
  have Sc: "\<And>U. U \<in> set ?S \<Longrightarrow> U \<in> carrier_mat (2 ^ ?K) (2 ^ ?K)" using S(2) elementary_carrier by blast
  have Ec: "E \<in> carrier_mat (2 ^ m) (2 ^ m)" unfolding E_def slap_factors[OF m mu]
    by (rule mult_carrier_mat[OF qw_carrier[OF gph_carrier] mult_carrier_mat[OF qw_carrier[OF xrot_carrier]
        mult_carrier_mat[OF mult_carrier_mat[OF pmat_carrier qw_carrier[OF xrot_carrier]] pmat_carrier]]]) (use m in simp_all)
  have Gc: "E \<Otimes> 1\<^sub>m 2 \<in> carrier_mat (2 ^ m * 2) (2 ^ m * 2)" using Ec by simp
  have "circuit_mat (2 ^ ?K) (cvl m k a \<mu> t r j) = circuit_mat (2 ^ ?K) ?S ^\<^sub>m r"
    unfolding cvl_def by (rule circuit_mat_concat_replicate[OF Sc])
  moreover have "stands_for (2 ^ a) (2 ^ Suc (m + k)) (circuit_mat (2 ^ ?K) ?S ^\<^sub>m r) (ctrl_bit (2 ^ k) (2 ^ m * 2) j (E \<Otimes> 1\<^sub>m 2) ^\<^sub>m r)"
    by (rule stands_for_pow[OF S(1)])
  moreover have "ctrl_bit (2 ^ k) (2 ^ m * 2) j (E \<Otimes> 1\<^sub>m 2) ^\<^sub>m r = ctrl_bit (2 ^ k) (2 ^ m * 2) j (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2)"
    using ctrl_bit_pow[OF Gc, of "2 ^ k" j r] tensor_pow_one[OF Ec, of r] by simp
  ultimately show "stands_for (2 ^ a) (2 ^ Suc (m + k)) (circuit_mat (2 ^ ?K) (cvl m k a \<mu> t r j))
      (ctrl_bit (2 ^ k) (2 ^ m * 2) j (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2))" by simp
  show "\<forall>U \<in> set (cvl m k a \<mu> t r j). elementary (2 ^ ?K) U" using S(2) by (auto simp: cvl_def)
  show "length (cvl m k a \<mu> t r j) \<le> r * (2 * (m * (m + 2) * (6 * ?K + 7)) + 3 * (4 * ?K + 1))"
    using S(3) by (simp add: cvl_def length_concat sum_list_replicate)
qed

definition lap_pe :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
  "lap_pe m k a \<mu> t r = pe_list (cvl m k a \<mu> t r) k"

theorem lap_pe_props:
  fixes t :: real and r :: nat
  assumes m: "2 \<le> m" and a: "m \<le> a" and mu: "0 \<le> \<mu>"
  defines "E \<equiv> evolution_product (2 ^ m) (t / real r) (sparse_parts (2 ^ m) (slap (2 ^ m) \<mu>) 2 (lp (2 ^ m)))"
  shows "stands_for (2 ^ a) (2 ^ Suc (m + k)) (circuit_mat (2 ^ (Suc (m + k) + a)) (lap_pe m k a \<mu> t r))
      (ctrl_pow (2 ^ k) (2 ^ m * 2) (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2))"
    "\<forall>U \<in> set (lap_pe m k a \<mu> t r). elementary (2 ^ (Suc (m + k) + a)) U"
    "length (lap_pe m k a \<mu> t r) \<le> (2 ^ k - 1) * (r * (2 * (m * (m + 2) * (6 * (Suc (m + k) + a) + 7)) + 3 * (4 * (Suc (m + k) + a) + 1)))"
proof -
  let ?K = "Suc (m + k) + a" and ?M = "2 ^ m * 2 :: nat"
  let ?B = "r * (2 * (m * (m + 2) * (6 * ?K + 7)) + 3 * (4 * ?K + 1))"
  have C1: "stands_for (2 ^ a) (2 ^ Suc (m + k)) (circuit_mat (2 ^ ?K) (cvl m k a \<mu> t r j)) (ctrl_bit (2 ^ k) ?M j (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2))"
    if "j < k" for j using cvl_props(1)[OF m a that mu, where t = t and r = r] unfolding E_def .
  have C2: "\<forall>U \<in> set (cvl m k a \<mu> t r j). elementary (2 ^ ?K) U" if "j < k" for j
    using cvl_props(2)[OF m a that mu, where t = t and r = r] .
  have C3: "length (cvl m k a \<mu> t r j) \<le> ?B" if "j < k" for j
    using cvl_props(3)[OF m a that mu, where t = t and r = r] .
  have KK: "(2::nat) ^ k * ?M = 2 ^ Suc (m + k)" "(2::nat) ^ a * 2 ^ Suc (m + k) = 2 ^ ?K" by (simp_all add: power_add ac_simps)
  have Ec: "E \<in> carrier_mat (2 ^ m) (2 ^ m)" unfolding E_def slap_factors[OF m mu]
    by (rule mult_carrier_mat[OF qw_carrier[OF gph_carrier] mult_carrier_mat[OF qw_carrier[OF xrot_carrier]
        mult_carrier_mat[OF mult_carrier_mat[OF pmat_carrier qw_carrier[OF xrot_carrier]] pmat_carrier]]]) (use m in simp_all)
  have G: "E ^\<^sub>m r \<Otimes> 1\<^sub>m 2 \<in> carrier_mat ?M ?M" using pow_carrier_mat[OF Ec] by simp
  have "stands_for (2 ^ a) (2 ^ k * ?M) (circuit_mat (2 ^ a * (2 ^ k * ?M)) (pe_list (cvl m k a \<mu> t r) k)) (ctrl_pow (2 ^ k) ?M (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2))"
  proof (rule pe_list_props[OF _ _ G])
    fix j assume "j < k"
    thus "stands_for (2 ^ a) (2 ^ k * ?M) (circuit_mat (2 ^ a * (2 ^ k * ?M)) (cvl m k a \<mu> t r j)) (ctrl_bit (2 ^ k) ?M j (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2))"
      unfolding KK by (rule C1)
  next
    fix j U assume "j < k" "U \<in> set (cvl m k a \<mu> t r j)"
    thus "U \<in> carrier_mat (2 ^ a * (2 ^ k * ?M)) (2 ^ a * (2 ^ k * ?M))" using C2 elementary_carrier unfolding KK by blast
  qed
  thus "stands_for (2 ^ a) (2 ^ Suc (m + k)) (circuit_mat (2 ^ ?K) (lap_pe m k a \<mu> t r)) (ctrl_pow (2 ^ k) ?M (E ^\<^sub>m r \<Otimes> 1\<^sub>m 2))"
    unfolding lap_pe_def KK .
  show "\<forall>U \<in> set (lap_pe m k a \<mu> t r). elementary (2 ^ ?K) U"
    using C2 by (auto simp: lap_pe_def pe_list_def)
  have "length (lap_pe m k a \<mu> t r) = (\<Sum>j<k. 2 ^ j * length (cvl m k a \<mu> t r j))" by (simp add: lap_pe_def length_pe_list)
  also have "\<dots> \<le> (\<Sum>j<k. 2 ^ j * ?B)" by (rule sum_mono) (use C3 in simp)
  also have "\<dots> = (\<Sum>j<k. 2 ^ j) * ?B" by (simp add: sum_distrib_right)
  also have "(\<Sum>j<k. (2::nat) ^ j) = 2 ^ k - 1" by (induction k) simp_all
  finally show "length (lap_pe m k a \<mu> t r) \<le> (2 ^ k - 1) * ?B" .
qed

end
