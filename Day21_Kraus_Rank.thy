(*  Title:   Day21_Kraus_Rank.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 14 October 2011 (Day 21)
*)

theory Day21_Kraus_Rank
  imports Day20_Positive_Functionals
begin

section \<open>Day 21 (14 October 2011): the Kraus rank bound; unitary freedom of representations\<close>

text \<open>\begin{notescor}
A completely positive $\Phi:M_n\to M_d$ has a Kraus representation $\Phi(X)=\sum_{l=1}^KA_lXA_l^*$
with $K\le nd$.
\end{notescor}
The notes then record a conjecture (every CP map is an average of $n$ UCP maps of Choi rank
$\le d$) and develop the uniqueness theory:
\begin{noteslemma}
If $T:\C^r\to\C^m$ is one-to-one then $T^*$ is onto.
\end{noteslemma}
\begin{notesprop}
If $v_1,\dots,v_r\in\C^k$ are linearly independent then so are $\{v_iv_j^*\}_{i,j}\subseteq M_k$.
\end{notesprop}
\begin{noteslemma}
If $0\le ww^*\le P$ then $w\in\range(P)$; hence for $P=\sum_lw_lw_l^*\ge0$,
$\range(P)=\operatorname{span}\{w_l\}$.
\end{noteslemma}
\begin{notestheorem}
If $P=\sum_{j=1}^rv_jv_j^*=\sum_{l=1}^mw_lw_l^*$ with $\rank P=r$, there is $U=(\alpha_{ij})_{m\times r}$
with $w_i=\sum_j\alpha_{ij}v_j$ and $U^*U=I_r$.
\end{notestheorem}
\begin{notestheorem}[Choi 2]
If $\Phi$ is completely positive with $\crk(\Phi)=r$ and
$\Phi(X)=\sum_{j=1}^rV_jXV_j^*=\sum_{l=1}^mW_lXW_l^*$, then $W_i=\sum_j\alpha_{ij}V_j$ for a unique
$U=(\alpha_{ij})$ with $U^*U=I_r$.
\end{notestheorem}
Only the Kraus rank bound is formalised here.  The kernel form of the lemma
($\ker A\subseteq\ker B$ when $0\le B\le A$) is proved in theory Day23 and used there to
prove Choi's Theorem 3 without the unitary-freedom theorem; the remaining statements are
audit items D21-3, D21-5, D21-6.\<close>

corollary kraus_rank_bound:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n
                      \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp:     "completely_positive n d \<Phi>"
      and npos:   "0 < n"
      and dpos:   "0 < d"
  shows "\<exists>As :: complex Matrix.mat list.
           length As \<le> n * d \<and>
           (\<forall>A \<in> set As. A \<in> carrier_mat d n) \<and>
           (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X)"
proof -
  have psd_choi: "psd (choi_matrix n d \<Phi>)"
    using choi_theorem[OF linear smult range npos dpos] cp by simp
  obtain Ws :: "complex Matrix.mat list"
    where Ws_len: "length Ws = n * d"
      and Ws_c: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
      and Ws_eq: "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A = kraus_map_dim d Ws A"
    using kraus_rep_of_psd_choi[OF linear smult range npos dpos psd_choi]
    by blast
  have Ws_len_le: "length Ws \<le> n * d" using Ws_len by simp
  show ?thesis using Ws_len_le Ws_c Ws_eq by blast
qed


text \<open>Dimension bookkeeping for $T^\dagger$ (the onto statement is not formalised).\<close>

lemma adjoint_image_in_dom:
  fixes T :: "complex Matrix.mat"
  assumes sq: "T \<in> carrier_mat m r"
  shows "\<forall>w :: complex Matrix.vec. dim_vec w = m
           \<longrightarrow> dim_vec (T\<^sup>\<dagger> *\<^sub>v w) = r"
  using sq by auto


text \<open>$\crk(\Phi)\le nd$: the defining set of the Choi rank is non-empty.\<close>

corollary choi_rank_le:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes linear: "\<And>A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n
                      \<Longrightarrow> \<Phi> (A + B) = \<Phi> A + \<Phi> B"
      and smult:  "\<And>c A. A \<in> carrier_mat n n \<Longrightarrow> \<Phi> (c \<cdot>\<^sub>m A) = c \<cdot>\<^sub>m \<Phi> A"
      and range:  "\<forall>A. A \<in> carrier_mat n n \<longrightarrow> \<Phi> A \<in> carrier_mat d d"
      and cp:     "completely_positive n d \<Phi>"
      and npos:   "0 < n"
      and dpos:   "0 < d"
  shows "choi_rank n d \<Phi> \<le> n * d"
proof -
  obtain As where As_len: "length As \<le> n * d"
              and As_c: "\<forall>A \<in> set As. A \<in> carrier_mat d n"
              and As_eq: "\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d As X"
    using kraus_rank_bound[OF linear smult range cp npos dpos] by blast
  have len_in:
    "length As
       \<in> { length Bs | Bs :: complex Matrix.mat list.
              (\<forall>B \<in> set Bs. B \<in> carrier_mat d n)
              \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Bs X) }"
    using As_c As_eq by blast
  have "Inf { length Bs | Bs :: complex Matrix.mat list.
                 (\<forall>B \<in> set Bs. B \<in> carrier_mat d n)
                 \<and> (\<forall>X. X \<in> carrier_mat n n \<longrightarrow> \<Phi> X = kraus_map_dim d Bs X) }
        \<le> length As"
    using len_in by (intro cInf_lower) auto
  also have "\<dots> \<le> n * d" using As_len .
  finally show ?thesis unfolding choi_rank_def .
qed

end
