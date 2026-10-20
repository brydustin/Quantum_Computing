theory Day19_Choi_TP_Unital
  imports Day25_Arveson_Correspondence
begin

text \<open>Day 19, notes (4) and (5) after Choi's theorem: write $P_\Phi=(R_{ij})$ with
$R_{ij}=\Phi(E_{ij})\in M_d$.  Then $\Phi$ is trace preserving iff $\Tr R_{ij}=\delta_{ij}$, and
unital iff $\sum_iR_{ii}=I_d$; with \<open>choi_theorem\<close> this characterises CPTP and UCP maps by
their Choi matrix.  Linearity on $M_n$ is \<^term>\<open>lin_on n d (carrier_mat n n) \<Phi>\<close>.\<close>

lemma mat_unit_carrier' [simp]: "E\<lbrakk>i,j ; n,n\<rbrakk> \<in> carrier_mat n n"
  by (simp add: mat_unit_def)

lemma choi_block:
  assumes range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d" and i: "i < n" and j: "j < n"
  shows "block_of_mat d (choi_matrix n d \<Phi>) i j = \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)"
proof -
  have c: "\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) \<in> carrier_mat d d" using range by simp
  show ?thesis
  proof (rule eq_matI)
    fix r s assume "r < dim_row (\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>))" "s < dim_col (\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>))"
    hence r: "r < d" and s: "s < d" using c by auto
    have "i * d + r < n * d" "j * d + s < n * d" using mult_index_lt i j r s by auto
    thus "block_of_mat d (choi_matrix n d \<Phi>) i j $$ (r,s) = \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>) $$ (r,s)"
      using r s by (simp add: block_of_mat_def choi_matrix_def mult.commute[of n d])
  qed (use c in \<open>auto simp: block_of_mat_def\<close>)
qed

lemma msum_cong: "(\<And>x. x \<in> set xs \<Longrightarrow> g x = h x) \<Longrightarrow> msum r c g xs = msum r c h xs"
  by (induction xs) auto

lemma Tr_msum:
  assumes "\<forall>x \<in> set xs. g x \<in> carrier_mat d d"
  shows "Tr (msum d d g xs) = (\<Sum>x\<leftarrow>xs. Tr (g x))"
  using assms
proof (induction xs)
  case Nil show ?case by (simp add: Tr_def)
next
  case (Cons x xs)
  have gx: "g x \<in> carrier_mat d d" and rest: "\<forall>x \<in> set xs. g x \<in> carrier_mat d d" using Cons.prems by auto
  have "Tr (g x + msum d d g xs) = Tr (g x) + Tr (msum d d g xs)"
    by (rule Tr_add) (use gx msum_carrier[OF rest] in auto)
  thus ?case using Cons.IH[OF rest] by simp
qed

lemma unit_expansion:
  assumes A: "A \<in> carrier_mat n n"
  shows "A = msum n n (\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m E\<lbrakk>i,j ; n,n\<rbrakk>) (List.product [0..<n] [0..<n])"
proof -
  let ?g = "\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m E\<lbrakk>i,j ; n,n\<rbrakk>"
  have g: "\<forall>x \<in> set (List.product [0..<n] [0..<n]). ?g x \<in> carrier_mat n n" by auto
  show ?thesis
  proof (rule eq_matI)
    fix r c assume "r < dim_row (msum n n ?g (List.product [0..<n] [0..<n]))"
                   "c < dim_col (msum n n ?g (List.product [0..<n] [0..<n]))"
    hence r: "r < n" and c: "c < n" using msum_carrier[OF g] by auto
    have "msum n n ?g (List.product [0..<n] [0..<n]) $$ (r,c)
        = (\<Sum>i<n. \<Sum>j<n. if i = r \<and> j = c then A $$ (r,c) else 0)"
      unfolding msum_index[OF g r c] sum_list_product_upt using r c
      by (intro sum.cong refl) auto
    also have "\<dots> = A $$ (r,c)" by (rule sum_delta2[OF r c])
    finally show "A $$ (r,c) = msum n n ?g (List.product [0..<n] [0..<n]) $$ (r,c)" by simp
  qed (use A msum_carrier[OF g] in auto)
qed

lemma id_expansion: "1\<^sub>m n = msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n]"
proof -
  have g: "\<forall>x \<in> set [0..<n]. E\<lbrakk>x,x ; n,n\<rbrakk> \<in> carrier_mat n n" by simp
  show ?thesis
  proof (rule eq_matI)
    fix r c assume "r < dim_row (msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n])"
                   "c < dim_col (msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n])"
    hence r: "r < n" and c: "c < n" using msum_carrier[OF g] by auto
    have "msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n] $$ (r,c) = (\<Sum>i<n. if i = r \<and> r = c then 1 else 0)"
      unfolding msum_index[OF g r c] interv_sum_list_conv_sum_set_nat set_upt atLeast0LessThan
      using r c by (intro sum.cong refl) auto
    also have "\<dots> = (if r = c then 1 else 0)" using r by (simp add: sum.delta)
    finally show "1\<^sub>m n $$ (r,c) = msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n] $$ (r,c)" using r c by simp
  qed (use msum_carrier[OF g] in auto)
qed

lemma lin_expansion:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and A: "A \<in> carrier_mat n n"
  shows "\<Phi> A = msum d d (\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) (List.product [0..<n] [0..<n])"
proof -
  let ?xs = "List.product [0..<n] [0..<n]" and ?g = "\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m E\<lbrakk>i,j ; n,n\<rbrakk>"
  have "\<Phi> A = \<Phi> (msum n n ?g ?xs)" by (rule arg_cong[OF unit_expansion[OF A]])
  also have "\<dots> = msum d d (\<lambda>x. \<Phi> (?g x)) ?xs"
    by (rule lin_on_msum[OF operator_system_full L]) auto
  also have "\<dots> = msum d d (\<lambda>(i,j). A $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) ?xs"
    by (rule msum_cong) (use L in \<open>auto simp: lin_on_def\<close>)
  finally show ?thesis .
qed

text \<open>D19-3, note (4): trace preservation in Choi-matrix form.\<close>

theorem choi_trace_preserving_iff:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>"
  shows "trace_preserving n \<Phi> \<longleftrightarrow>
         (\<forall>i < n. \<forall>j < n. Tr (block_of_mat d (choi_matrix n d \<Phi>) i j) = (if i = j then 1 else 0))"
proof -
  have range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d" using L unfolding lin_on_def by auto
  have R: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> block_of_mat d (choi_matrix n d \<Phi>) i j = \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)"
    by (rule choi_block[OF range])
  show ?thesis
  proof
    assume "trace_preserving n \<Phi>"
    thus "\<forall>i < n. \<forall>j < n. Tr (block_of_mat d (choi_matrix n d \<Phi>) i j) = (if i = j then 1 else 0)"
      using R by (simp add: trace_preserving_def Tr_mat_unit)
  next
    assume "\<forall>i < n. \<forall>j < n. Tr (block_of_mat d (choi_matrix n d \<Phi>) i j) = (if i = j then 1 else 0)"
    hence h: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> Tr (\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) = (if i = j then 1 else 0)"
      using R by simp
    show "trace_preserving n \<Phi>" unfolding trace_preserving_def
    proof (intro allI impI)
      fix X :: "complex Matrix.mat" assume X: "X \<in> carrier_mat n n"
      let ?xs = "List.product [0..<n] [0..<n]"
      have gc: "\<forall>x \<in> set ?xs. (\<lambda>(i,j). X $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) x \<in> carrier_mat d d"
        using range by auto
      have "Tr (\<Phi> X) = (\<Sum>x\<leftarrow>?xs. Tr ((\<lambda>(i,j). X $$ (i,j) \<cdot>\<^sub>m \<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)) x))"
        unfolding lin_expansion[OF L X] by (rule Tr_msum[OF gc])
      also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. X $$ (i,j) * Tr (\<Phi> (E\<lbrakk>i,j ; n,n\<rbrakk>)))"
        by (simp add: sum_list_product_upt Tr_smult)
      also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. if j = i then X $$ (i,i) else 0)"
        by (intro sum.cong refl) (simp add: h)
      also have "\<dots> = (\<Sum>i<n. X $$ (i,i))" by simp
      also have "\<dots> = Tr X" using X by (simp add: Tr_def)
      finally show "Tr (\<Phi> X) = Tr X" .
    qed
  qed
qed

text \<open>D19-3, note (5): unitality in Choi-matrix form, $\sum_iR_{ii}=I_d$.\<close>

theorem choi_unital_iff:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>"
  shows "unital_map n d \<Phi> \<longleftrightarrow> msum d d (\<lambda>i. block_of_mat d (choi_matrix n d \<Phi>) i i) [0..<n] = 1\<^sub>m d"
proof -
  have range: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d" using L unfolding lin_on_def by auto
  have "\<Phi> (1\<^sub>m n) = \<Phi> (msum n n (\<lambda>i. E\<lbrakk>i,i ; n,n\<rbrakk>) [0..<n])" by (rule arg_cong[OF id_expansion])
  also have "\<dots> = msum d d (\<lambda>i. \<Phi> (E\<lbrakk>i,i ; n,n\<rbrakk>)) [0..<n]"
    by (rule lin_on_msum[OF operator_system_full L]) simp
  also have "\<dots> = msum d d (\<lambda>i. block_of_mat d (choi_matrix n d \<Phi>) i i) [0..<n]"
    by (rule msum_cong) (simp add: choi_block[OF range])
  finally show ?thesis unfolding unital_map_def by simp
qed

lemma lin_on_choi_hyps:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>"
  shows "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
    and "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
    and "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
  using L unfolding lin_on_def by auto

text \<open>Notes (4) and (5) with Choi's theorem: CPTP iff $P_\Phi\ge0$ and $\Tr R_{ij}=\delta_{ij}$;
UCP iff $P_\Phi\ge0$ and $\sum_iR_{ii}=I_d$.\<close>

corollary choi_cptp_iff:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and n: "n > 0" and d: "d > 0"
  shows "completely_positive n d \<Phi> \<and> trace_preserving n \<Phi> \<longleftrightarrow>
         psd (choi_matrix n d \<Phi>) \<and>
         (\<forall>i < n. \<forall>j < n. Tr (block_of_mat d (choi_matrix n d \<Phi>) i j) = (if i = j then 1 else 0))"
  using choi_theorem[OF lin_on_choi_hyps[OF L] n d] choi_trace_preserving_iff[OF L] by simp

corollary choi_ucp_iff:
  assumes L: "lin_on n d (carrier_mat n n) \<Phi>" and n: "n > 0" and d: "d > 0"
  shows "completely_positive n d \<Phi> \<and> unital_map n d \<Phi> \<longleftrightarrow>
         psd (choi_matrix n d \<Phi>) \<and> msum d d (\<lambda>i. block_of_mat d (choi_matrix n d \<Phi>) i i) [0..<n] = 1\<^sub>m d"
  using choi_theorem[OF lin_on_choi_hyps[OF L] n d] choi_unital_iff[OF L] by simp

end
