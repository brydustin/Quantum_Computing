theory Day19_Choi_Positivity
  imports
    Day27_Entangled_Examples
    Day23_ChoiExtremeUCP
begin

section \<open>Day 19: Choi's theorem with (2) isolated (D19-1)\<close>

lemma choi_seed_psd: "psd (choi_seed n)"
  unfolding choi_seed_unit_blocks by (rule unit_blocks_psd)

lemma choi_psd_if_n_positive:
  assumes n: "0 < n" and d: "0 < d" and pp: "p_positive n d n \<Phi>"
  shows "psd (choi_matrix n d \<Phi>)"
proof -
  have "choi_seed n \<in> carrier_mat (n * n) (n * n)" by (rule choi_seed_carrier)
  hence "psd (amplification n d n \<Phi> (choi_seed n))" using pp choi_seed_psd by (simp add: p_positive_def)
  thus ?thesis by (simp add: choi_matrix_as_amplification[OF n d])
qed

theorem choi_four_conditions:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult: "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and n: "0 < n" and d: "0 < d"
  shows "(completely_positive n d \<Phi> \<longleftrightarrow> p_positive n d n \<Phi>)
       \<and> (p_positive n d n \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>))
       \<and> (psd (choi_matrix n d \<Phi>) \<longleftrightarrow>
           (\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)))"
proof -
  have cp_choi: "completely_positive n d \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>)"
    by (rule choi_theorem[OF linear smult range n d])
  have np: "p_positive n d n \<Phi> \<longleftrightarrow> psd (choi_matrix n d \<Phi>)"
  proof
    assume "p_positive n d n \<Phi>" thus "psd (choi_matrix n d \<Phi>)" by (rule choi_psd_if_n_positive[OF n d])
  next
    assume "psd (choi_matrix n d \<Phi>)"
    hence "completely_positive n d \<Phi>" using cp_choi by simp
    thus "p_positive n d n \<Phi>" using n by (simp add: completely_positive_def)
  qed
  have kraus: "psd (choi_matrix n d \<Phi>) \<longleftrightarrow>
           (\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A))"
  proof
    assume "psd (choi_matrix n d \<Phi>)"
    thus "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
      using kraus_rep_of_psd_choi[OF linear smult range n d] by blast
  next
    assume "\<exists>Ws. (\<forall>W \<in> set Ws. W \<in> carrier_mat d n) \<and> (\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A)"
    then obtain Ws where Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Wk: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A" by blast
    have "completely_positive n d (kraus_map_dim d Ws)" by (rule kraus_cp_no_tp[OF Wc n d])
    hence "completely_positive n d \<Phi>" using completely_positive_cong[of n \<Phi> "kraus_map_dim d Ws" d] Wk by blast
    thus "psd (choi_matrix n d \<Phi>)" using cp_choi by simp
  qed
  have "completely_positive n d \<Phi> \<longleftrightarrow> p_positive n d n \<Phi>" using cp_choi np by simp
  thus ?thesis using np kraus by blast
qed

end
