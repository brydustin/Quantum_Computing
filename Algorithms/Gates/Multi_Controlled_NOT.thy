theory Multi_Controlled_NOT
  imports Reversible_Compile Bennett_Uncompute
begin

section \<open>Multi-controlled NOT and table lookup\<close>

subsection \<open>Flipping a list of bits\<close>

definition flips :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where "flips ws x = fold flip_bit ws x"

lemma flips_Nil [simp]: "flips [] x = x" and flips_Cons [simp]: "flips (w # ws) x = flips ws (flip_bit w x)"
  and flips_append: "flips (ws @ vs) x = flips vs (flips ws x)"
  by (simp_all add: flips_def)

lemma bit_flips_other: "q \<notin> set ws \<Longrightarrow> bit (flips ws x) q \<longleftrightarrow> bit x q"
  by (induction ws arbitrary: x) (auto simp: bit_flip_bit_iff)

lemma bit_flips: "distinct ws \<Longrightarrow> bit (flips ws x) q \<longleftrightarrow> (if q \<in> set ws then \<not> bit x q else bit x q)"
  by (induction ws arbitrary: x) (auto simp: bit_flip_bit_iff bit_flips_other)

lemma flips_flips: "distinct ws \<Longrightarrow> flips ws (flips ws x) = x"
  by (rule bit_eqI) (simp add: bit_flips)

lemma flip_flips: "flip_bit p (flips ws x) = flips ws (flip_bit p x)"
  by (induction ws arbitrary: x) (simp_all add: flip_bit_commute)

lemma flips_commute: "flips ts (flips ws x) = flips ws (flips ts x)"
  by (induction ts arbitrary: x) (simp_all add: flip_flips)

lemma rcirc_nots: "rcirc (map NOT ws) x = flips ws x"
  by (induction ws arbitrary: x) simp_all

lemma rcirc_flips_other: "\<forall>g \<in> set rs. \<forall>w \<in> set ws. w \<notin> wires g \<Longrightarrow> rcirc rs (flips ws x) = flips ws (rcirc rs x)"
  by (induction ws arbitrary: x) (simp_all add: rcirc_flip_other)

lemma rcirc_cnots: "a \<notin> set ts \<Longrightarrow> rcirc (map (CX a) ts) y = (if bit y a then flips ts y else y)"
  by (induction ts arbitrary: y) (auto simp: bit_flip_bit_iff)

subsection \<open>The Toffoli ladder\<close>

text \<open>Ancilla $a_0$ is set to $1$, then $a_{l+1} = a_l \wedge c_l$: on clean ancillas, $a_i$ ends up
holding the AND of the first $i$ controls.\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{quantikz}[row sep=0.25cm, column sep=0.35cm]
\lstick{$c_0$} & \qw & \ctrl{4} & \qw & \qw & \qw & \qw & \qw & \ctrl{4} & \qw & \qw\\
\lstick{$c_1$} & \qw & \qw & \ctrl{4} & \qw & \qw & \qw & \ctrl{4} & \qw & \qw & \qw\\
\lstick{$c_2$} & \qw & \qw & \qw & \ctrl{4} & \qw & \ctrl{4} & \qw & \qw & \qw & \qw\\
\lstick{target} & \qw & \qw & \qw & \qw & \targ{} & \qw & \qw & \qw & \qw & \qw\\
\lstick{$a_0=\ket0$} & \targ{} & \ctrl{1} & \qw & \qw & \qw & \qw & \qw & \ctrl{1} & \targ{} & \qw\\
\lstick{$a_1=\ket0$} & \qw & \targ{} & \ctrl{1} & \qw & \qw & \qw & \ctrl{1} & \targ{} & \qw & \qw\\
\lstick{$a_2=\ket0$} & \qw & \qw & \targ{} & \ctrl{1} & \qw & \ctrl{1} & \targ{} & \qw & \qw & \qw\\
\lstick{$a_3=\ket0$} & \qw & \qw & \qw & \targ{} & \ctrl{-4} & \targ{} & \qw & \qw & \qw & \qw
\end{quantikz}\\[0.2em]
{\small The ladder computes $a_3 = c_0 \wedge c_1 \wedge c_2$, the target flips, and the ladder is undone.}
\end{center}
\<close>

definition ladder :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> rgate list" where
  "ladder cw aw n = NOT (aw 0) # map (\<lambda>l. TOF (cw l) (aw l) (aw (Suc l))) [0..<n]"

lemma ladder_Suc: "ladder cw aw (Suc n) = ladder cw aw n @ [TOF (cw n) (aw n) (aw (Suc n))]"
  by (simp add: ladder_def)

definition ladder_ok :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "ladder_ok K cw aw n \<longleftrightarrow> inj_on aw {..n} \<and> (\<forall>l<n. \<forall>i\<le>n. cw l \<noteq> aw i) \<and> (\<forall>l<n. cw l < K) \<and> (\<forall>i\<le>n. aw i < K)"

lemma ladder_ok_Suc: "ladder_ok K cw aw (Suc n) \<Longrightarrow> ladder_ok K cw aw n"
  unfolding ladder_ok_def by (auto intro: inj_on_subset)

lemma ladder_rg_ok:
  assumes ok: "ladder_ok K cw aw n"
  shows "\<forall>g \<in> set (ladder cw aw n). rg_ok K g"
proof -
  have inj: "inj_on aw {..n}" using ok by (simp add: ladder_ok_def)
  have "aw l \<noteq> aw (Suc l)" if "l < n" for l
  proof
    assume "aw l = aw (Suc l)"
    from inj_onD[OF inj this] that show False by simp
  qed
  thus ?thesis using ok by (auto simp: ladder_def ladder_ok_def)
qed

lemma ladder_bits:
  assumes ok: "ladder_ok K cw aw n" and x: "\<And>i. i \<le> n \<Longrightarrow> \<not> bit x (aw i)"
  shows "i \<le> n \<Longrightarrow> bit (rcirc (ladder cw aw n) x) (aw i) \<longleftrightarrow> (\<forall>l<i. bit x (cw l))"
    "q \<notin> aw ` {..n} \<Longrightarrow> bit (rcirc (ladder cw aw n) x) q \<longleftrightarrow> bit x q"
proof -
  have "(\<forall>i\<le>n. bit (rcirc (ladder cw aw n) x) (aw i) \<longleftrightarrow> (\<forall>l<i. bit x (cw l)))
      \<and> (\<forall>q. q \<notin> aw ` {..n} \<longrightarrow> (bit (rcirc (ladder cw aw n) x) q \<longleftrightarrow> bit x q))"
    using ok x
  proof (induction n)
    case 0
    show ?case using "0.prems"(2)[of 0] by (auto simp: ladder_def bit_flip_bit_iff)
  next
    case (Suc n)
    have okn: "ladder_ok K cw aw n" by (rule ladder_ok_Suc[OF Suc.prems(1)])
    have xn: "\<And>i. i \<le> n \<Longrightarrow> \<not> bit x (aw i)" using Suc.prems(2) by simp
    let ?y = "rcirc (ladder cw aw n) x"
    have A: "\<And>i. i \<le> n \<Longrightarrow> bit ?y (aw i) \<longleftrightarrow> (\<forall>l<i. bit x (cw l))"
      and B: "\<And>q. q \<notin> aw ` {..n} \<Longrightarrow> bit ?y q \<longleftrightarrow> bit x q" using Suc.IH[OF okn xn] by blast+
    have inj: "inj_on aw {..Suc n}" and cw: "\<And>l i. l < Suc n \<Longrightarrow> i \<le> Suc n \<Longrightarrow> cw l \<noteq> aw i"
      using Suc.prems(1) unfolding ladder_ok_def by blast+
    have ne: "aw i \<noteq> aw (Suc n)" if "i \<le> n" for i
    proof
      assume "aw i = aw (Suc n)"
      from inj_onD[OF inj this] that show False by simp
    qed
    have nS: "aw (Suc n) \<notin> aw ` {..n}"
    proof
      assume "aw (Suc n) \<in> aw ` {..n}"
      then obtain i where "i \<le> n" "aw (Suc n) = aw i" by auto
      thus False using ne[of i] by simp
    qed
    have c: "bit ?y (cw n) \<longleftrightarrow> bit x (cw n)" by (rule B) (use cw in auto)
    have a0: "\<not> bit ?y (aw (Suc n))" using B[OF nS] Suc.prems(2)[of "Suc n"] by simp
    have r: "rcirc (ladder cw aw (Suc n)) x = rg (TOF (cw n) (aw n) (aw (Suc n))) ?y"
      by (simp add: ladder_Suc rcirc_append)
    show ?case
    proof (intro conjI allI impI)
      fix i assume i: "i \<le> Suc n"
      show "bit (rcirc (ladder cw aw (Suc n)) x) (aw i) \<longleftrightarrow> (\<forall>l<i. bit x (cw l))"
      proof (cases "i = Suc n")
        case True
        thus ?thesis unfolding r using A[of n] c a0 by (auto simp: bit_rg less_Suc_eq bit_flip_bit_iff)
      next
        case False
        hence "i \<le> n" using i by simp
        thus ?thesis unfolding r using A[of i] ne[of i] by (simp add: bit_rg bit_flip_bit_iff)
      qed
    next
      fix q assume q: "q \<notin> aw ` {..Suc n}"
      hence "q \<noteq> aw (Suc n)" "q \<notin> aw ` {..n}" by auto
      thus "bit (rcirc (ladder cw aw (Suc n)) x) q \<longleftrightarrow> bit x q" unfolding r using B[of q] by (simp add: bit_rg bit_flip_bit_iff)
    qed
  qed
  thus "i \<le> n \<Longrightarrow> bit (rcirc (ladder cw aw n) x) (aw i) \<longleftrightarrow> (\<forall>l<i. bit x (cw l))"
    "q \<notin> aw ` {..n} \<Longrightarrow> bit (rcirc (ladder cw aw n) x) q \<longleftrightarrow> bit x q" by blast+
qed

subsection \<open>Multi-controlled NOT\<close>

text \<open>Targets must avoid the controls and the ancillas.\<close>

definition targets_ok :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "targets_ok K cw aw n ts \<longleftrightarrow> (\<forall>t \<in> set ts. t < K \<and> t \<notin> aw ` {..n} \<and> (\<forall>l<n. t \<noteq> cw l))"

definition mcx :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> rgate list" where
  "mcx cw aw n ts = ladder cw aw n @ map (CX (aw n)) ts @ rev (ladder cw aw n)"

lemma mcx_rcirc:
  assumes ok: "ladder_ok K cw aw n" and x: "\<And>i. i \<le> n \<Longrightarrow> \<not> bit x (aw i)" and t: "targets_ok K cw aw n ts"
  shows "rcirc (mcx cw aw n ts) x = (if \<forall>l<n. bit x (cw l) then flips ts x else x)"
proof -
  let ?L = "ladder cw aw n" and ?y = "rcirc (ladder cw aw n) x"
  have inv: "rcirc (rev ?L) ?y = x" by (rule rcirc_rev[OF ladder_rg_ok[OF ok]])
  have fl: "bit ?y (aw n) \<longleftrightarrow> (\<forall>l<n. bit x (cw l))" using ladder_bits(1)[OF ok x, of n] by simp
  have an: "aw n \<notin> set ts" using t by (auto simp: targets_ok_def)
  have tw: "\<forall>g \<in> set (rev ?L). \<forall>w \<in> set ts. w \<notin> wires g" using t by (fastforce simp: ladder_def targets_ok_def)
  have "rcirc (mcx cw aw n ts) x = rcirc (rev ?L) (if bit ?y (aw n) then flips ts ?y else ?y)"
    by (simp add: mcx_def rcirc_append rcirc_cnots[OF an])
  also have "\<dots> = (if \<forall>l<n. bit x (cw l) then flips ts x else x)"
    using fl inv by (auto simp: rcirc_flips_other[OF tw])
  finally show ?thesis .
qed

lemma mcx_rg_ok: "ladder_ok K cw aw n \<Longrightarrow> targets_ok K cw aw n ts \<Longrightarrow> \<forall>g \<in> set (mcx cw aw n ts). rg_ok K g"
  using ladder_rg_ok[of K cw aw n] by (fastforce simp: mcx_def targets_ok_def ladder_ok_def)

lemma length_mcx: "length (mcx cw aw n ts) = 2 * n + 2 + length ts"
  by (simp add: mcx_def ladder_def)

subsection \<open>Table lookup\<close>

text \<open>Entry $c$ fires when the controls spell $c$: NOT the controls where $c$ has a $0$, run the
multi-controlled NOT, NOT them back.\<close>

definition sel :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "sel cw n c = map cw (filter (\<lambda>l. \<not> bit c l) [0..<n])"

definition lk_step :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> rgate list" where
  "lk_step cw aw n c ts = map NOT (sel cw n c) @ mcx cw aw n ts @ map NOT (sel cw n c)"

definition spells :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "spells cw n x c \<longleftrightarrow> (\<forall>l<n. bit x (cw l) = bit c l)"

lemma lk_step_rcirc:
  assumes ok: "ladder_ok K cw aw n" and inj: "inj_on cw {..<n}" and x: "\<And>i. i \<le> n \<Longrightarrow> \<not> bit x (aw i)"
    and t: "targets_ok K cw aw n ts"
  shows "rcirc (lk_step cw aw n c ts) x = flips (if spells cw n x c then ts else []) x"
proof -
  let ?w = "sel cw n c"
  have dw: "distinct ?w" using inj by (auto simp: sel_def distinct_map intro: inj_on_subset)
  have x': "\<not> bit (flips ?w x) (aw i)" if "i \<le> n" for i
  proof -
    have "aw i \<notin> set ?w"
    proof
      assume "aw i \<in> set ?w"
      then obtain l where l: "l < n" "aw i = cw l" by (auto simp: sel_def)
      have "cw l \<noteq> aw i" using ok l(1) that unfolding ladder_ok_def by blast
      thus False using l(2) by simp
    qed
    thus ?thesis using x[OF that] by (simp add: bit_flips_other)
  qed
  have cb: "bit (flips ?w x) (cw l) \<longleftrightarrow> bit x (cw l) = bit c l" if "l < n" for l
  proof -
    have "cw l \<in> set ?w \<longleftrightarrow> \<not> bit c l"
    proof
      assume "cw l \<in> set ?w"
      then obtain l' where l': "l' < n" "\<not> bit c l'" "cw l = cw l'" by (auto simp: sel_def)
      have "l = l'" using inj_onD[OF inj l'(3)] that l'(1) by simp
      thus "\<not> bit c l" using l'(2) by simp
    qed (use that in \<open>auto simp: sel_def\<close>)
    thus ?thesis by (auto simp: bit_flips[OF dw])
  qed
  have m: "rcirc (mcx cw aw n ts) (flips ?w x) = (if \<forall>l<n. bit (flips ?w x) (cw l) then flips ts (flips ?w x) else flips ?w x)"
    by (rule mcx_rcirc[OF ok x' t])
  have "rcirc (lk_step cw aw n c ts) x = flips ?w (rcirc (mcx cw aw n ts) (flips ?w x))"
    by (simp add: lk_step_def rcirc_append rcirc_nots)
  also have "\<dots> = flips (if spells cw n x c then ts else []) x"
    unfolding m spells_def using cb by (auto simp: flips_commute[of ts ?w x] flips_flips[OF dw])
  finally show ?thesis .
qed

definition lookup :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> rgate list" where
  "lookup cw aw n cs ts = concat (map (\<lambda>c. lk_step cw aw n c (ts c)) cs)"

theorem lookup_rcirc:
  assumes ok: "ladder_ok K cw aw n" and inj: "inj_on cw {..<n}" and x: "\<And>i. i \<le> n \<Longrightarrow> \<not> bit x (aw i)"
    and t: "\<And>c. c \<in> set cs \<Longrightarrow> targets_ok K cw aw n (ts c)"
  shows "rcirc (lookup cw aw n cs ts) x = flips (concat (map (\<lambda>c. if spells cw n x c then ts c else []) cs)) x"
  using x t
proof (induction cs arbitrary: x)
  case Nil
  show ?case by (simp add: lookup_def)
next
  case (Cons c cs)
  let ?y = "rcirc (lk_step cw aw n c (ts c)) x" and ?u = "if spells cw n x c then ts c else []"
  have tc: "targets_ok K cw aw n (ts c)" using Cons.prems(2) by simp
  have y: "?y = flips ?u x" by (rule lk_step_rcirc[OF ok inj Cons.prems(1) tc])
  have keep: "bit ?y q \<longleftrightarrow> bit x q" if "q \<notin> set (ts c)" for q
    unfolding y using that by (simp add: bit_flips_other)
  have tcs: "\<And>c'. c' \<in> set cs \<Longrightarrow> targets_ok K cw aw n (ts c')" using Cons.prems(2) by simp
  have ya: "\<And>i. i \<le> n \<Longrightarrow> \<not> bit ?y (aw i)" using keep Cons.prems(1) tc by (auto simp: targets_ok_def)
  have sp: "spells cw n ?y c' \<longleftrightarrow> spells cw n x c'" for c'
    using keep tc by (auto simp: spells_def targets_ok_def)
  have "rcirc (lookup cw aw n (c # cs) ts) x = rcirc (lookup cw aw n cs ts) ?y"
    by (simp add: lookup_def rcirc_append)
  also have "\<dots> = flips (concat (map (\<lambda>c. if spells cw n ?y c then ts c else []) cs)) ?y"
    by (rule Cons.IH[OF ya tcs])
  also have "\<dots> = flips (concat (map (\<lambda>c. if spells cw n x c then ts c else []) (c # cs))) x"
    unfolding sp unfolding y by (simp add: flips_append)
  finally show ?case .
qed

lemma lookup_rg_ok:
  assumes ok: "ladder_ok K cw aw n" and t: "\<And>c. c \<in> set cs \<Longrightarrow> targets_ok K cw aw n (ts c)"
  shows "\<forall>g \<in> set (lookup cw aw n cs ts). rg_ok K g"
proof -
  have "\<forall>g \<in> set (mcx cw aw n (ts c)). rg_ok K g" if "c \<in> set cs" for c by (rule mcx_rg_ok[OF ok t[OF that]])
  thus ?thesis using ok by (fastforce simp: lookup_def lk_step_def sel_def ladder_ok_def)
qed

lemma length_lookup:
  assumes "\<And>c. c \<in> set cs \<Longrightarrow> length (ts c) \<le> nt"
  shows "length (lookup cw aw n cs ts) \<le> length cs * (4 * n + 2 + nt)"
proof -
  have "length (lk_step cw aw n c (ts c)) \<le> 4 * n + 2 + nt" if "c \<in> set cs" for c
  proof -
    have "length (sel cw n c) \<le> n" using length_filter_le[of _ "[0..<n]"] by (simp add: sel_def)
    thus ?thesis using assms[OF that] by (simp add: lk_step_def length_mcx)
  qed
  hence "(\<Sum>c\<leftarrow>cs. length (lk_step cw aw n c (ts c))) \<le> (\<Sum>c\<leftarrow>cs. 4 * n + 2 + nt)" by (rule sum_list_mono)
  thus ?thesis by (simp add: lookup_def length_concat comp_def sum_list_triv)
qed

end
