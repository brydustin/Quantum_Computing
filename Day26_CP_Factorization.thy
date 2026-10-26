theory Day26_CP_Factorization
  imports Day26_Arveson_Extension Day32_Recovery_Proposition
begin

section \<open>Day 26: factoring a CP map through a unital or a trace-preserving one (D26-1)\<close>

text \<open>The $i$-th block embedding $B_i:\mathbb C^n\to\mathbb C^{kn}$.  The $B_i$ are isometries with
orthogonal ranges, $\sum_iB_iB_i^*=I$, so a Kraus representation $\Phi(X)=\sum_iW_iXW_i^*$ gives
$\Phi(X)=V^*\psi(X)V$ with $\psi(X)=\sum_iB_iXB_i^*$ unital and $V=\sum_iB_iW_i^*$.\<close>

definition blk_emb :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
  "blk_emb k n i = Matrix.mat (k * n) n (\<lambda>(x, y). if x div n = i \<and> x mod n = y then 1 else 0)"

lemma blk_emb_carrier [simp]: "blk_emb k n i \<in> carrier_mat (k * n) n"
  by (simp add: blk_emb_def)

lemma blk_emb_dims [simp]: "dim_row (blk_emb k n i) = k * n" "dim_col (blk_emb k n i) = n"
  by (simp_all add: blk_emb_def)

lemma blk_cond:
  fixes x y i n :: nat
  assumes y: "y < n"
  shows "(x div n = i \<and> x mod n = y) \<longleftrightarrow> x = i * n + y"
proof
  assume "x div n = i \<and> x mod n = y"
  thus "x = i * n + y" using div_mult_mod_eq[of x n] by simp
next
  assume x: "x = i * n + y"
  have n: "0 < n" using y by simp
  show "x div n = i \<and> x mod n = y" unfolding x using y n by simp
qed

text \<open>$J_i=e_i\otimes I_n:\C^n\to\C^k\otimes\C^n$ embeds $\C^n$ as the $i$-th block, and the blocks fill
the space: $\sum_iJ_iJ_i^*=I_{kn}$.\<close>

lemma blk_emb_gram_entry:
  assumes x: "x < k * n" and y: "y < k * n"
  shows "(blk_emb k n i * ((blk_emb k n i)\<^sup>\<dagger>)) $$ (x, y) =
         (if x div n = i \<and> y div n = i \<and> x mod n = y mod n then 1 else 0)"
proof -
  have n: "0 < n" using x by (cases n) auto
  have "(blk_emb k n i * ((blk_emb k n i)\<^sup>\<dagger>)) $$ (x, y) =
        (\<Sum>t<n. blk_emb k n i $$ (x, t) * cnj (blk_emb k n i $$ (y, t)))"
    using x y by (simp add: scalar_prod_def dagger_def)
  also have "\<dots> = (\<Sum>t<n. if t = x mod n then (if x div n = i \<and> y div n = i \<and> x mod n = y mod n then 1 else 0) else 0)"
    by (rule sum.cong) (use x y in \<open>auto simp: blk_emb_def\<close>)
  also have "\<dots> = (if x div n = i \<and> y div n = i \<and> x mod n = y mod n then 1 else 0)"
    using n by simp
  finally show ?thesis .
qed

lemma blk_emb_gram:
  "foldr (\<lambda>B acc. B * (B\<^sup>\<dagger>) + acc) (map (blk_emb k n) [0..<k]) (0\<^sub>m (k * n) (k * n)) = 1\<^sub>m (k * n)"
proof -
  let ?f = "\<lambda>i. blk_emb k n i * ((blk_emb k n i)\<^sup>\<dagger>)"
  let ?F = "foldr (\<lambda>i acc. ?f i + acc) [0..<k] (0\<^sub>m (k * n) (k * n))"
  have fc: "\<forall>i \<in> set [0..<k]. ?f i \<in> carrier_mat (k * n) (k * n)"
    by (auto intro!: mult_carrier_mat dagger_carrier)
  have e: "foldr (\<lambda>B acc. B * (B\<^sup>\<dagger>) + acc) (map (blk_emb k n) [0..<k]) (0\<^sub>m (k * n) (k * n)) = ?F"
    by (simp add: foldr_map o_def)
  have Fc: "?F \<in> carrier_mat (k * n) (k * n)" by (rule foldr_add_mat_carrier_rect[OF fc])
  have "?F = 1\<^sub>m (k * n)"
  proof (rule eq_matI)
    fix x y assume "x < dim_row (1\<^sub>m (k * n))" "y < dim_col (1\<^sub>m (k * n))"
    hence x: "x < k * n" and y: "y < k * n" by simp_all
    have xk: "x div n < k" "y div n < k" using x y by (simp_all add: less_mult_imp_div_less)
    have "?F $$ (x, y) = (\<Sum>i\<leftarrow>[0..<k]. ?f i $$ (x, y))"
      by (rule foldr_add_mat_index_rect[OF fc x y])
    also have "\<dots> = (\<Sum>i<k. ?f i $$ (x, y))" by (simp add: sum_list_distinct_conv_sum_set atLeast0LessThan)
    also have "\<dots> = (\<Sum>i<k. if i = x div n then (if y div n = x div n \<and> x mod n = y mod n then 1 else 0) else 0)"
      by (rule sum.cong) (unfold blk_emb_gram_entry[OF x y], auto)
    also have "\<dots> = (if y div n = x div n \<and> x mod n = y mod n then 1 else 0)" using xk by simp
    also have "\<dots> = 1\<^sub>m (k * n) $$ (x, y)"
    proof -
      have "(y div n = x div n \<and> x mod n = y mod n) \<longleftrightarrow> x = y"
      proof
        assume h: "y div n = x div n \<and> x mod n = y mod n"
        show "x = y" using div_mult_mod_eq[of x n] div_mult_mod_eq[of y n] h by simp
      qed simp
      thus ?thesis using x y by simp
    qed
    finally show "?F $$ (x, y) = 1\<^sub>m (k * n) $$ (x, y)" .
  qed (use Fc in simp_all)
  thus ?thesis unfolding e .
qed

lemma kraus_lin_on:
  assumes "\<forall>W \<in> set Ws. W \<in> carrier_mat d n"
  shows "lin_on n d (carrier_mat n n) (kraus_map_dim d Ws)"
  unfolding lin_on_def using assms
  by (auto intro: kraus_map_dim_carrier kraus_map_dim_add kraus_map_dim_smult)

lemma kraus_compose_single: "kraus_compose [A] Es = map (\<lambda>E. A * E) Es"
  by (induction Es) (simp_all add: kraus_compose_Cons)

text \<open>$V$ has the blocks $W_i^*$ stacked vertically, so $V^*B_i=W_i$.\<close>

definition kraus_stack_dag :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "kraus_stack_dag n d Ws = Matrix.mat (length Ws * n) d (\<lambda>(x, c). cnj (Ws ! (x div n) $$ (c, x mod n)))"

lemma kraus_stack_dag_blk:
  assumes Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and i: "i < length Ws"
  shows "(kraus_stack_dag n d Ws)\<^sup>\<dagger> * blk_emb (length Ws) n i = Ws ! i"
proof (rule eq_matI)
  let ?k = "length Ws"
  have Wi: "Ws ! i \<in> carrier_mat d n" using Wc i by simp
  fix c y assume "c < dim_row (Ws ! i)" "y < dim_col (Ws ! i)"
  hence c: "c < d" and y: "y < n" using Wi by auto
  have iy: "i * n + y < ?k * n" by (rule mult_index_lt[OF i y])
  have "((kraus_stack_dag n d Ws)\<^sup>\<dagger> * blk_emb ?k n i) $$ (c, y) =
        (\<Sum>x<?k * n. Ws ! (x div n) $$ (c, x mod n) * blk_emb ?k n i $$ (x, y))"
    using c y by (simp add: scalar_prod_def dagger_def kraus_stack_dag_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>x<?k * n. if x = i * n + y then Ws ! (x div n) $$ (c, x mod n) else 0)"
    by (rule sum.cong) (use y in \<open>auto simp: blk_emb_def blk_cond\<close>)
  also have "\<dots> = Ws ! i $$ (c, y)" using iy y by simp
  finally show "((kraus_stack_dag n d Ws)\<^sup>\<dagger> * blk_emb ?k n i) $$ (c, y) = Ws ! i $$ (c, y)" .
qed (use Wc i in \<open>auto simp: kraus_stack_dag_def\<close>)

text \<open>Proposition (Day 26): a CP map $\Phi:S\to M_d$ on an operator system with $\Phi(I)=P$ is
$\Phi(X)=V^*\psi(X)V$ with $\psi$ unital and completely positive (here even on all of $M_n$) and
$V^*V=P$.  The notes compress $\Phi$ to the range of $P$; here the Kraus form of
@{thm [source] arveson_kraus} is used.\<close>

theorem cp_unital_factor:
  fixes OS :: "complex Matrix.mat set" and \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes OS: "operator_system CARD('n::finite) OS" and L: "lin_on CARD('n) CARD('d::finite) OS \<Phi>"
      and CP: "cp_on CARD('n) CARD('d) OS \<Phi>"
  shows "\<exists>r V \<psi>. 0 < r \<and> V \<in> carrier_mat r CARD('d) \<and> \<psi> \<in> UCP CARD('n) r
               \<and> lin_on CARD('n) r (carrier_mat CARD('n) CARD('n)) \<psi>
               \<and> (\<forall>X \<in> OS. \<Phi> X = (V\<^sup>\<dagger>) * \<psi> X * V) \<and> (V\<^sup>\<dagger>) * V = \<Phi> (1\<^sub>m CARD('n))"
proof -
  let ?n = "CARD('n)" and ?d = "CARD('d)"
  obtain Ws0 where W0c: "\<forall>W \<in> set Ws0. W \<in> carrier_mat ?d ?n" and W0: "\<forall>M \<in> OS. \<Phi> M = kraus_map_dim ?d Ws0 M"
    using arveson_kraus[OF OS L CP] by blast
  define Ws where "Ws = 0\<^sub>m ?d ?n # Ws0"
  define k where "k = length Ws"
  have Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat ?d ?n" using W0c by (simp add: Ws_def)
  have k: "0 < k" by (simp add: k_def Ws_def)
  have OSc: "\<And>M. M \<in> OS \<Longrightarrow> M \<in> carrier_mat ?n ?n" using operator_systemD(1)[OF OS] by auto
  have W: "\<forall>M \<in> OS. \<Phi> M = kraus_map_dim ?d Ws M"
  proof
    fix M assume M: "M \<in> OS"
    have "kraus_map_dim ?d Ws M = kraus_map_dim ?d Ws0 M"
      unfolding Ws_def by (rule kraus_map_dim_zero_head[OF W0c OSc[OF M]])
    thus "\<Phi> M = kraus_map_dim ?d Ws M" using W0 M by simp
  qed
  define Bs where "Bs = map (blk_emb k ?n) [0..<k]"
  define V where "V = kraus_stack_dag ?n ?d Ws"
  define \<psi> where "\<psi> = kraus_map_dim (k * ?n) Bs"
  have Bc: "\<forall>B \<in> set Bs. B \<in> carrier_mat (k * ?n) ?n" by (auto simp: Bs_def)
  have Vc: "V \<in> carrier_mat (k * ?n) ?d" by (simp add: V_def kraus_stack_dag_def k_def)
  have Vd: "V\<^sup>\<dagger> \<in> carrier_mat ?d (k * ?n)" by (rule dagger_carrier[OF Vc])
  have r: "0 < k * ?n" using k by simp
  have cp: "completely_positive ?n (k * ?n) \<psi>" unfolding \<psi>_def by (rule kraus_cp_no_tp[OF Bc]) (use r in simp_all)
  have un: "\<psi> (1\<^sub>m ?n) = 1\<^sub>m (k * ?n)"
  proof -
    have "\<psi> (1\<^sub>m ?n) = foldr (\<lambda>W acc. W * (W\<^sup>\<dagger>) + acc) Bs (0\<^sub>m (k * ?n) (k * ?n))"
      unfolding \<psi>_def by (rule kraus_map_dim_one[OF Bc])
    also have "\<dots> = 1\<^sub>m (k * ?n)" unfolding Bs_def by (rule blk_emb_gram)
    finally show ?thesis .
  qed
  have comp: "kraus_compose [V\<^sup>\<dagger>] Bs = Ws"
  proof (rule nth_equalityI)
    show "length (kraus_compose [V\<^sup>\<dagger>] Bs) = length Ws" by (simp add: Bs_def k_def)
    fix i assume "i < length (kraus_compose [V\<^sup>\<dagger>] Bs)"
    hence i: "i < k" by (simp add: Bs_def)
    have "kraus_compose [V\<^sup>\<dagger>] Bs ! i = V\<^sup>\<dagger> * blk_emb k ?n i"
      using i by (simp add: kraus_compose_single Bs_def)
    also have "\<dots> = Ws ! i" unfolding V_def k_def by (rule kraus_stack_dag_blk[OF Wc]) (use i in \<open>simp add: k_def\<close>)
    finally show "kraus_compose [V\<^sup>\<dagger>] Bs ! i = Ws ! i" .
  qed
  have fac: "\<Phi> X = (V\<^sup>\<dagger>) * \<psi> X * V" if X: "X \<in> OS" for X
  proof -
    have Xc: "X \<in> carrier_mat ?n ?n" by (rule OSc[OF X])
    have pc: "\<psi> X \<in> carrier_mat (k * ?n) (k * ?n)" unfolding \<psi>_def by (rule kraus_map_dim_carrier[OF Bc Xc])
    have "\<Phi> X = kraus_map_dim ?d (kraus_compose [V\<^sup>\<dagger>] Bs) X" using W X unfolding comp by simp
    also have "\<dots> = kraus_map_dim ?d [V\<^sup>\<dagger>] (\<psi> X)"
      unfolding \<psi>_def by (rule kraus_map_dim_compose) (use Vd Bc Xc in simp_all)
    also have "\<dots> = (V\<^sup>\<dagger>) * \<psi> X * V"
      using right_add_zero_mat[OF mult_carrier_mat[OF mult_carrier_mat[OF Vd pc] Vc]]
      by (simp add: dagger_of_dagger_is_id)
    finally show ?thesis .
  qed
  have one: "1\<^sub>m ?n \<in> OS" using operator_systemD(2)[OF OS] .
  have "(V\<^sup>\<dagger>) * V = \<Phi> (1\<^sub>m ?n)" using fac[OF one] right_mult_one_mat[OF Vd] by (simp add: un)
  moreover have "\<psi> \<in> UCP ?n (k * ?n)" using cp un by (simp add: UCP_def unital_map_def)
  moreover have "lin_on ?n (k * ?n) (carrier_mat ?n ?n) \<psi>" unfolding \<psi>_def by (rule kraus_lin_on[OF Bc])
  ultimately show ?thesis using r Vc fac by blast
qed

text \<open>$V$ with the blocks $W_i$ stacked vertically, so $B_i^*V=W_i$.\<close>

definition kraus_stack :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list \<Rightarrow> complex Matrix.mat" where
  "kraus_stack n d Ws = Matrix.mat (length Ws * d) n (\<lambda>(x, c). Ws ! (x div d) $$ (x mod d, c))"

lemma kraus_stack_blk:
  assumes Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat d n" and i: "i < length Ws"
  shows "(blk_emb (length Ws) d i)\<^sup>\<dagger> * kraus_stack n d Ws = Ws ! i"
proof (rule eq_matI)
  let ?k = "length Ws"
  have Wi: "Ws ! i \<in> carrier_mat d n" using Wc i by simp
  fix a c assume "a < dim_row (Ws ! i)" "c < dim_col (Ws ! i)"
  hence a: "a < d" and c: "c < n" using Wi by auto
  have ia: "i * d + a < ?k * d" by (rule mult_index_lt[OF i a])
  have "((blk_emb ?k d i)\<^sup>\<dagger> * kraus_stack n d Ws) $$ (a, c) =
        (\<Sum>x<?k * d. cnj (blk_emb ?k d i $$ (x, a)) * Ws ! (x div d) $$ (x mod d, c))"
    using a c by (simp add: scalar_prod_def dagger_def kraus_stack_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>x<?k * d. if x = i * d + a then Ws ! (x div d) $$ (x mod d, c) else 0)"
    by (rule sum.cong) (use a in \<open>auto simp: blk_emb_def blk_cond\<close>)
  also have "\<dots> = Ws ! i $$ (a, c)" using ia a by simp
  finally show "((blk_emb ?k d i)\<^sup>\<dagger> * kraus_stack n d Ws) $$ (a, c) = Ws ! i $$ (a, c)" .
qed (use Wc i in \<open>auto simp: kraus_stack_def\<close>)

text \<open>Proposition (Day 26): a CP map $\Phi:M_n\to M_d$ is $\Phi(X)=\psi(VXV^*)$ with $\psi:M_r\to M_d$
completely positive and trace preserving.  The notes dualise the previous proposition; here
$\psi(Y)=\sum_iB_i^*YB_i$ and $V=\sum_iB_iW_i$ directly.\<close>

theorem cp_tp_factor:
  fixes \<Phi> :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes L: "lin_on CARD('n::finite) CARD('d::finite) (carrier_mat CARD('n) CARD('n)) \<Phi>"
      and CP: "completely_positive CARD('n) CARD('d) \<Phi>"
  shows "\<exists>r V \<psi>. 0 < r \<and> V \<in> carrier_mat r CARD('n) \<and> \<psi> \<in> CPTP r CARD('d)
               \<and> lin_on r CARD('d) (carrier_mat r r) \<psi>
               \<and> (\<forall>X \<in> carrier_mat CARD('n) CARD('n). \<Phi> X = \<psi> (V * X * (V\<^sup>\<dagger>)))"
proof -
  let ?n = "CARD('n)" and ?d = "CARD('d)"
  have CP': "cp_on ?n ?d (carrier_mat ?n ?n) \<Phi>" using CP by (simp add: cp_on_full)
  obtain Ws0 where W0c: "\<forall>W \<in> set Ws0. W \<in> carrier_mat ?d ?n"
    and W0: "\<forall>M \<in> carrier_mat ?n ?n. \<Phi> M = kraus_map_dim ?d Ws0 M"
    using arveson_kraus[OF operator_system_full L CP'] by blast
  define Ws where "Ws = 0\<^sub>m ?d ?n # Ws0"
  define k where "k = length Ws"
  have Wc: "\<forall>W \<in> set Ws. W \<in> carrier_mat ?d ?n" using W0c by (simp add: Ws_def)
  have k: "0 < k" by (simp add: k_def Ws_def)
  have W: "\<forall>M \<in> carrier_mat ?n ?n. \<Phi> M = kraus_map_dim ?d Ws M"
  proof
    fix M :: "complex Matrix.mat" assume M: "M \<in> carrier_mat ?n ?n"
    have "kraus_map_dim ?d Ws M = kraus_map_dim ?d Ws0 M"
      unfolding Ws_def by (rule kraus_map_dim_zero_head[OF W0c M])
    thus "\<Phi> M = kraus_map_dim ?d Ws M" using W0 M by simp
  qed
  define Cs where "Cs = map (\<lambda>i. (blk_emb k ?d i)\<^sup>\<dagger>) [0..<k]"
  define V where "V = kraus_stack ?n ?d Ws"
  define \<psi> where "\<psi> = kraus_map_dim ?d Cs"
  have Cc: "\<forall>C \<in> set Cs. C \<in> carrier_mat ?d (k * ?d)" by (auto simp: Cs_def intro!: dagger_carrier)
  have Vc: "V \<in> carrier_mat (k * ?d) ?n" by (simp add: V_def kraus_stack_def k_def)
  have r: "0 < k * ?d" using k by simp
  have tp: "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Cs (0\<^sub>m (k * ?d) (k * ?d)) = 1\<^sub>m (k * ?d)"
  proof -
    have "foldr (\<lambda>W acc. (W\<^sup>\<dagger>) * W + acc) Cs (0\<^sub>m (k * ?d) (k * ?d)) =
          foldr (\<lambda>B acc. B * (B\<^sup>\<dagger>) + acc) (map (blk_emb k ?d) [0..<k]) (0\<^sub>m (k * ?d) (k * ?d))"
      by (simp add: Cs_def foldr_map o_def dagger_of_dagger_is_id)
    thus ?thesis using blk_emb_gram by simp
  qed
  have ko: "kraus_operators (k * ?d) ?d Cs" unfolding kraus_operators_def using Cc tp by simp
  have "\<psi> \<in> CPTP (k * ?d) ?d"
    unfolding CPTP_def \<psi>_def using kraus_cp_no_tp[OF Cc r] kraus_is_trace_preserving[OF ko] by simp
  moreover have "lin_on (k * ?d) ?d (carrier_mat (k * ?d) (k * ?d)) \<psi>" unfolding \<psi>_def by (rule kraus_lin_on[OF Cc])
  moreover have "\<Phi> X = \<psi> (V * X * (V\<^sup>\<dagger>))" if X: "X \<in> carrier_mat ?n ?n" for X
  proof -
    have mp: "map (\<lambda>C. C * V) Cs = Ws"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>C. C * V) Cs) = length Ws" by (simp add: Cs_def k_def)
      fix i assume "i < length (map (\<lambda>C. C * V) Cs)"
      hence i: "i < k" by (simp add: Cs_def)
      have "map (\<lambda>C. C * V) Cs ! i = (blk_emb k ?d i)\<^sup>\<dagger> * V" using i by (simp add: Cs_def)
      also have "\<dots> = Ws ! i" unfolding V_def k_def by (rule kraus_stack_blk[OF Wc]) (use i in \<open>simp add: k_def\<close>)
      finally show "map (\<lambda>C. C * V) Cs ! i = Ws ! i" .
    qed
    have "\<Phi> X = kraus_map_dim ?d (map (\<lambda>C. C * V) Cs) X" using W X unfolding mp by simp
    also have "\<dots> = \<psi> (V * X * (V\<^sup>\<dagger>))" unfolding \<psi>_def by (rule kraus_map_dim_map_mult_right[OF Cc Vc X])
    finally show ?thesis .
  qed
  ultimately show ?thesis using r Vc by blast
qed

end
