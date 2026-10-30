theory Wire_Gates
  imports Cycle_Laplacian
begin

section \<open>Gates on arbitrary wires\<close>

text \<open>\<open>dig ws x\<close> reads the bits of $x$ on the wires \<open>ws\<close>, \<open>ws ! 0\<close> lowest.  \<open>wg K ws Q\<close> is
the gate $Q$ on the wires \<open>ws\<close> of a $K$-wire register, the identity on the others.\<close>

fun dig :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "dig [] x = 0"
| "dig (w # ws) x = of_bool (bit x w) + 2 * dig ws x"

lemma bit_dig: "bit (dig ws x) l \<longleftrightarrow> l < length ws \<and> bit x (ws ! l)"
proof (induction ws arbitrary: l)
  case (Cons w ws)
  have d: "(of_bool (bit x w) + 2 * dig ws x) div 2 = dig ws x" by (cases "bit x w") simp_all
  show ?case
  proof (cases l)
    case 0
    thus ?thesis by (cases "bit x w") (simp_all add: bit_0)
  next
    case (Suc l')
    thus ?thesis using Cons.IH[of l'] d by (simp add: bit_Suc)
  qed
qed simp

lemma dig_lt: "dig ws x < 2 ^ length ws"
proof (induction ws)
  case (Cons w ws)
  thus ?case by (cases "bit x w") simp_all
qed simp

definition wg :: "nat \<Rightarrow> nat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "wg K ws Q = Matrix.mat (2 ^ K) (2 ^ K)
     (\<lambda>(x, y). if \<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i then Q $$ (dig ws x, dig ws y) else 0)"

lemma wg_carrier [simp]: "wg K ws Q \<in> carrier_mat (2 ^ K) (2 ^ K)" by (simp add: wg_def)
lemma dim_wg [simp]: "dim_row (wg K ws Q) = 2 ^ K" "dim_col (wg K ws Q) = 2 ^ K" by (simp_all add: wg_def)

lemma wg_index: "x < 2 ^ K \<Longrightarrow> y < 2 ^ K \<Longrightarrow>
    wg K ws Q $$ (x, y) = (if \<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i then Q $$ (dig ws x, dig ws y) else 0)"
  by (simp add: wg_def)

lemma bits_eq_nat:
  fixes x y :: nat
  assumes "x < 2 ^ K" "y < 2 ^ K" "\<And>i. i < K \<Longrightarrow> bit x i = bit y i"
  shows "x = y"
proof (rule bit_eqI)
  fix i
  show "bit x i \<longleftrightarrow> bit y i"
  proof (cases "i < K")
    case False
    hence "\<not> bit x i" "\<not> bit y i" using assms(1,2) bit_above[of x K i] bit_above[of y K i] by auto
    thus ?thesis by simp
  qed (use assms(3) in simp)
qed

subsection \<open>Routes of wire lists\<close>

text \<open>\<open>wroute p ws\<close> carries the wires \<open>ws\<close> down to positions $p, p+1, \dots$ by adjacent swaps.\<close>

fun wroute :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "wroute p [] = []"
| "wroute p (w # ws) = dn w p @ wroute (Suc p) (map (np w p) ws)"

lemma wroute_ge: "j \<in> set (wroute p ws) \<Longrightarrow> p \<le> j"
  by (induction p ws rule: wroute.induct) (auto simp: dn_def)

lemma pm_fix: "(\<And>j. j \<in> set js \<Longrightarrow> p < j) \<Longrightarrow> pm js p = p"
proof (induction js)
  case (Cons j js)
  have "p < j" "pm js p = p" using Cons by simp_all
  thus ?case by (simp add: Transposition.transpose_def)
qed simp

lemma pm_ge: "(\<And>j. j \<in> set js \<Longrightarrow> j + 2 \<le> K) \<Longrightarrow> K \<le> i \<Longrightarrow> pm js i = i"
proof (induction js)
  case (Cons j js)
  have "j + 2 \<le> K" "pm js i = i" using Cons by simp_all
  thus ?case using Cons.prems(2) by (simp add: Transposition.transpose_def)
qed simp

lemma pm_lt: "(\<And>j. j \<in> set js \<Longrightarrow> j + 2 \<le> K) \<Longrightarrow> i < K \<Longrightarrow> pm js i < K"
proof (induction js)
  case (Cons j js)
  have "j + 2 \<le> K" "pm js i < K" using Cons by simp_all
  thus ?case by (simp add: Transposition.transpose_def)
qed simp

lemma np_inj_on:
  assumes "w \<notin> A"
  shows "inj_on (np w p) A"
proof (rule inj_onI)
  fix a b assume ab: "a \<in> A" "b \<in> A" "np w p a = np w p b"
  show "a = b"
  proof (rule ccontr)
    assume "a \<noteq> b"
    moreover have "a \<noteq> w" "b \<noteq> w" using assms ab by auto
    ultimately show False using np_inj[of a w b p] ab(3) by simp
  qed
qed

lemma bit_div_pow: "bit (z div 2 ^ q) n \<longleftrightarrow> bit z (q + n)" for z :: nat
  by (simp flip: drop_bit_eq_div add: bit_drop_bit_eq)

lemma np_shift:
  assumes "w \<noteq> i" "p \<le> w" "p \<le> i"
  shows "Suc p \<le> np w p i"
  using assms by (auto simp: np_def)

lemma pm_wroute:
  assumes "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> p \<le> w" "l < length ws"
  shows "pm (wroute p ws) (p + l) = ws ! l"
  using assms
proof (induction p ws arbitrary: l rule: wroute.induct)
  case (2 p w ws)
  let ?R = "wroute (Suc p) (map (np w p) ws)"
  have pw: "p \<le> w" using "2.prems"(2) by simp
  have dws: "distinct (map (np w p) ws)"
    using "2.prems"(1) np_inj_on[of w "set ws" p] by (simp add: distinct_map)
  have ge: "Suc p \<le> v" if v: "v \<in> set (map (np w p) ws)" for v
  proof -
    obtain i where i: "i \<in> set ws" "v = np w p i" using v by auto
    have "w \<noteq> i" "p \<le> i" using i(1) "2.prems"(1,2) by auto
    thus ?thesis using np_shift[OF _ pw] i(2) by simp
  qed
  show ?case
  proof (cases l)
    case 0
    have "pm ?R p = p" by (rule pm_fix) (use wroute_ge in fastforce)
    thus ?thesis using 0 pw by (simp add: pm_append pm_dn)
  next
    case (Suc l')
    have l': "l' < length ws" using "2.prems"(3) Suc by simp
    have "pm ?R (Suc p + l') = map (np w p) ws ! l'" by (rule "2.IH"[OF dws ge]) (use l' in simp_all)
    hence "pm ?R (p + l) = np w p (ws ! l')" using Suc l' by simp
    moreover have "ws ! l' \<noteq> w" using "2.prems"(1) l' by auto
    ultimately show ?thesis using Suc pm_dn_np[OF pw] by (simp add: pm_append)
  qed
qed simp

lemma wroute_range:
  assumes "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < K" "j \<in> set (wroute p ws)"
  shows "j + 2 \<le> K"
  using assms
proof (induction p ws rule: wroute.induct)
  case (2 p w ws)
  have r: "\<And>v. v \<in> set (map (np w p) ws) \<Longrightarrow> v < K"
    using "2.prems"(1,2) np_lt[of _ K w p] by auto
  have d: "distinct (map (np w p) ws)"
    using "2.prems"(1) np_inj_on[of w "set ws" p] by (simp add: distinct_map)
  show ?case using "2.prems"(3) "2.IH"[OF d r] dn_range[of j w p K] "2.prems"(2) by auto
qed simp

lemma length_wroute:
  assumes "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < K"
  shows "length (wroute p ws) \<le> length ws * K"
  using assms
proof (induction p ws rule: wroute.induct)
  case (2 p w ws)
  have r: "\<And>v. v \<in> set (map (np w p) ws) \<Longrightarrow> v < K"
    using "2.prems"(1,2) np_lt[of _ K w p] by auto
  have d: "distinct (map (np w p) ws)"
    using "2.prems"(1) np_inj_on[of w "set ws" p] by (simp add: distinct_map)
  have "length (wroute (Suc p) (map (np w p) ws)) \<le> length ws * K" using "2.IH"[OF d r] by simp
  moreover have "w - p \<le> K" using "2.prems"(2)[of w] by simp
  ultimately show ?case by simp
qed simp

subsection \<open>A wire gate is a conjugated low gate\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{quantikz}[row sep=0.3cm, column sep=0.4cm]
\lstick{$w_1$} & \gate{Q}\vqw{2} & \qw \\
\lstick{} & \qw & \qw \\
\lstick{$w_0$} & \gate{\phantom{Q}} & \qw
\end{quantikz}
\;=\;
\begin{quantikz}[row sep=0.3cm, column sep=0.4cm]
\lstick{$w_1$} & \gate[3]{\text{swaps}} & \qw & \gate[3]{\text{swaps}^{-1}} & \qw\\
\lstick{} & & \gate[2]{Q} & & \qw\\
\lstick{$w_0$} & & & & \qw
\end{quantikz}\\[0.2em]
{\small A gate on any wires is a gate on the low wires, conjugated by chains of adjacent swaps (\texttt{wg\_conj}).}
\end{center}
\<close>

lemma pmat_conj_index:
  assumes M: "M \<in> carrier_mat N N" and f: "\<And>x. x < N \<Longrightarrow> f x < N" and g: "\<And>x. x < N \<Longrightarrow> g x < N"
    and gf: "\<And>x. x < N \<Longrightarrow> g (f x) = x" and fg: "\<And>x. x < N \<Longrightarrow> f (g x) = x"
    and x: "x < N" and y: "y < N"
  shows "(pmat N g * M * pmat N f) $$ (x, y) = M $$ (f x, f y)"
proof -
  have L: "pmat N g * M = Matrix.mat N N (\<lambda>(r, t). M $$ (f r, t))"
  proof (rule eq_matI)
    fix r t assume "r < dim_row (Matrix.mat N N (\<lambda>(r, t). M $$ (f r, t)))" "t < dim_col (Matrix.mat N N (\<lambda>(r, t). M $$ (f r, t)))"
    hence rt: "r < N" "t < N" by simp_all
    have "(pmat N g * M) $$ (r, t) = (\<Sum>u<N. (if r = g u then 1 else 0) * M $$ (u, t))"
      using rt M by (simp add: pmat_def scalar_prod_def atLeast0LessThan)
    also have "\<dots> = (\<Sum>u<N. if u = f r then M $$ (f r, t) else 0)"
      by (rule sum.cong) (use gf fg rt in auto)
    also have "\<dots> = M $$ (f r, t)" using f[OF rt(1)] by simp
    finally show "(pmat N g * M) $$ (r, t) = Matrix.mat N N (\<lambda>(r, t). M $$ (f r, t)) $$ (r, t)" using rt by simp
  qed (use M in simp_all)
  have "(pmat N g * M * pmat N f) $$ (x, y) = (\<Sum>t<N. M $$ (f x, t) * (if t = f y then 1 else 0))"
    unfolding L using x y by (simp add: pmat_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>t<N. if t = f y then M $$ (f x, f y) else 0)" by (rule sum.cong) auto
  also have "\<dots> = M $$ (f x, f y)" using f[OF y] by simp
  finally show ?thesis .
qed

lemma wg_conj:
  assumes js: "\<And>j. j \<in> set js \<Longrightarrow> j + 2 \<le> K" and ws: "\<And>l. l < length ws \<Longrightarrow> pm js l = ws ! l"
    and q: "length ws \<le> K" and Q: "Q \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)"
  shows "wg K ws Q = pmat (2 ^ K) (apply_ops (swops (rev js))) * (1\<^sub>m (2 ^ (K - length ws)) \<Otimes> Q)
           * pmat (2 ^ K) (apply_ops (swops js))"
proof -
  let ?q = "length ws" and ?F = "apply_ops (swops js)" and ?G = "apply_ops (swops (rev js))"
  let ?M = "1\<^sub>m (2 ^ (K - ?q)) \<Otimes> Q"
  have KK: "(2::nat) ^ (K - ?q) * 2 ^ ?q = 2 ^ K" using q by (simp flip: power_add)
  have Mc: "?M \<in> carrier_mat (2 ^ K) (2 ^ K)" by (rule carrier_matI) (use Q KK in simp_all)
  have js': "\<And>b j. (b, j) \<in> set (swops js) \<Longrightarrow> j + 2 \<le> K" using js by auto
  have jsr: "\<And>b j. (b, j) \<in> set (swops (rev js)) \<Longrightarrow> j + 2 \<le> K" using js by auto
  have Flt: "\<And>x. x < 2 ^ K \<Longrightarrow> ?F x < 2 ^ K" by (rule apply_ops_lt[OF js'])
  have Glt: "\<And>x. x < 2 ^ K \<Longrightarrow> ?G x < 2 ^ K" by (rule apply_ops_lt[OF jsr])
  have GF: "\<And>x. ?G (?F x) = x" using apply_ops_rev[of "swops js"] by (simp add: rev_map)
  have FG: "\<And>x. ?F (?G x) = x" using apply_ops_rev[of "swops (rev js)"] by (simp add: rev_map)
  have pmK: "\<And>i. i < K \<Longrightarrow> pm js i < K" by (rule pm_lt[OF js])
  have pmrK: "\<And>i. i < K \<Longrightarrow> pm (rev js) i < K" by (rule pm_lt) (use js in auto)
  show ?thesis
  proof (rule eq_matI)
    fix x y assume "x < dim_row (pmat (2 ^ K) ?G * ?M * pmat (2 ^ K) ?F)" "y < dim_col (pmat (2 ^ K) ?G * ?M * pmat (2 ^ K) ?F)"
    hence x: "x < 2 ^ K" and y: "y < 2 ^ K" by simp_all
    have Fx: "?F x < 2 ^ (K - ?q) * 2 ^ ?q" and Fy: "?F y < 2 ^ (K - ?q) * 2 ^ ?q" using Flt[OF x] Flt[OF y] KK by simp_all
    have dv: "?F x div 2 ^ ?q < 2 ^ (K - ?q)" "?F y div 2 ^ ?q < 2 ^ (K - ?q)"
      using Fx Fy by (simp_all add: div_less_iff_less_mult)
    have md: "\<And>z. ?F z mod 2 ^ ?q = dig ws z"
    proof (rule bit_eqI)
      fix z l
      show "bit (?F z mod 2 ^ ?q) l \<longleftrightarrow> bit (dig ws z) l"
        using ws[of l] by (auto simp: bit_dig bit_swops simp flip: take_bit_eq_mod simp add: bit_take_bit_iff)
    qed
    have hi: "?F x div 2 ^ ?q = ?F y div 2 ^ ?q \<longleftrightarrow> (\<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i)"
    proof
      assume e: "?F x div 2 ^ ?q = ?F y div 2 ^ ?q"
      show "\<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i"
      proof (intro allI impI)
        fix p assume p: "p < K" "p \<notin> set ws"
        let ?i = "pm (rev js) p"
        have pi: "pm js ?i = p" by (rule pm_rev(2))
        have iK: "?i < K" by (rule pmrK[OF p(1)])
        have qi: "?q \<le> ?i"
        proof (rule ccontr)
          assume "\<not> ?q \<le> ?i"
          hence "pm js ?i = ws ! ?i" using ws by simp
          thus False using pi p(2) \<open>\<not> ?q \<le> ?i\<close> nth_mem[of ?i ws] by auto
        qed
        have "bit (?F x div 2 ^ ?q) (?i - ?q) = bit (?F y div 2 ^ ?q) (?i - ?q)" unfolding e ..
        hence "bit (?F x) ?i = bit (?F y) ?i" using qi by (simp add: bit_div_pow)
        thus "bit x p = bit y p" unfolding bit_swops pi .
      qed
    next
      assume h: "\<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i"
      show "?F x div 2 ^ ?q = ?F y div 2 ^ ?q"
      proof (rule bit_eqI)
        fix n
        show "bit (?F x div 2 ^ ?q) n \<longleftrightarrow> bit (?F y div 2 ^ ?q) n"
        proof (cases "?q + n < K")
          case True
          let ?p = "pm js (?q + n)"
          have pK: "?p < K" by (rule pmK[OF True])
          have "?p \<notin> set ws"
          proof
            assume "?p \<in> set ws"
            then obtain l where l: "l < ?q" "ws ! l = ?p" by (auto simp: in_set_conv_nth)
            hence "pm js l = pm js (?q + n)" using ws by simp
            hence "pm (rev js) (pm js l) = pm (rev js) (pm js (?q + n))" by simp
            hence "l = ?q + n" by (simp add: pm_rev(1))
            thus False using l(1) by simp
          qed
          hence "bit x ?p = bit y ?p" using h pK by blast
          thus ?thesis by (simp add: bit_div_pow bit_swops)
        next
          case False
          have "\<not> bit (?F x) (?q + n)" "\<not> bit (?F y) (?q + n)"
            using Flt[OF x] Flt[OF y] False bit_above by (auto dest: bit_above)
          thus ?thesis by (simp add: bit_div_pow)
        qed
      qed
    qed
    have "(pmat (2 ^ K) ?G * ?M * pmat (2 ^ K) ?F) $$ (x, y) = ?M $$ (?F x, ?F y)"
      by (rule pmat_conj_index[OF Mc Flt Glt GF FG x y])
    also have "\<dots> = 1\<^sub>m (2 ^ (K - ?q)) $$ (?F x div 2 ^ ?q, ?F y div 2 ^ ?q) * Q $$ (?F x mod 2 ^ ?q, ?F y mod 2 ^ ?q)"
      using index_tensor_mat[of "1\<^sub>m (2 ^ (K - ?q))" "2 ^ (K - ?q)" "2 ^ (K - ?q)" Q "2 ^ ?q" "2 ^ ?q" "?F x" "?F y"] Q Fx Fy
      by simp
    also have "\<dots> = wg K ws Q $$ (x, y)"
    proof (cases "\<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i")
      case True
      hence "?F x div 2 ^ ?q = ?F y div 2 ^ ?q" using hi by blast
      thus ?thesis unfolding wg_index[OF x y] using True dv by (simp add: md)
    next
      case False
      hence "?F x div 2 ^ ?q \<noteq> ?F y div 2 ^ ?q" using hi by blast
      thus ?thesis unfolding wg_index[OF x y] using False dv by (auto simp: md)
    qed
    finally show "wg K ws Q $$ (x, y) = (pmat (2 ^ K) ?G * ?M * pmat (2 ^ K) ?F) $$ (x, y)" ..
  qed (use Mc in simp_all)
qed

lemma length_distinct_le:
  assumes "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < K"
  shows "length ws \<le> K"
proof -
  have "card (set ws) \<le> card {..<K}" by (rule card_mono) (use assms(2) in auto)
  thus ?thesis using distinct_card[OF assms(1)] by simp
qed

lemma wg_route:
  assumes ws: "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < K" and Q: "Q \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)"
  shows "wg K ws Q = pmat (2 ^ K) (apply_ops (swops (rev (wroute 0 ws)))) * (1\<^sub>m (2 ^ (K - length ws)) \<Otimes> Q)
           * pmat (2 ^ K) (apply_ops (swops (wroute 0 ws)))"
proof (rule wg_conj)
  show "\<And>j. j \<in> set (wroute 0 ws) \<Longrightarrow> j + 2 \<le> K" by (rule wroute_range[OF ws])
  show "\<And>l. l < length ws \<Longrightarrow> pm (wroute 0 ws) l = ws ! l" using pm_wroute[OF ws(1), of 0] by simp
qed (use length_distinct_le[OF ws] Q in simp_all)

subsection \<open>Algebra of wire gates\<close>

lemma conj_mult:
  fixes P P' A B :: "complex Matrix.mat"
  assumes P: "P \<in> carrier_mat N N" and P': "P' \<in> carrier_mat N N" and A: "A \<in> carrier_mat N N"
    and B: "B \<in> carrier_mat N N" and PP: "P' * P = 1\<^sub>m N"
  shows "(P * A * P') * (P * B * P') = P * (A * B) * P'"
proof -
  have "(P * A * P') * (P * B * P') = P * (A * ((P' * P) * (B * P')))"
    using P P' A B by (simp add: assoc_mult_mat[of _ N N _ N _ N])
  also have "\<dots> = P * (A * B) * P'" unfolding PP using P P' A B
    by (simp add: assoc_mult_mat[of _ N N _ N _ N] left_mult_one_mat[OF mult_carrier_mat[OF B P']])
  finally show ?thesis .
qed

lemma wg_mult:
  assumes ws: "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < K"
    and Q: "Q \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)" and Q2: "Q2 \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)"
  shows "wg K ws Q * wg K ws Q2 = wg K ws (Q * Q2)"
proof -
  let ?q = "length ws" and ?js = "wroute 0 ws"
  let ?F = "apply_ops (swops ?js)" and ?G = "apply_ops (swops (rev ?js))"
  have KK: "(2::nat) ^ (K - ?q) * 2 ^ ?q = 2 ^ K" using length_distinct_le[OF ws] by (simp flip: power_add)
  have js': "\<And>b j. (b, j) \<in> set (swops (rev ?js)) \<Longrightarrow> j + 2 \<le> K" using wroute_range[OF ws] by auto
  have Glt: "\<And>x. x < 2 ^ K \<Longrightarrow> ?G x < 2 ^ K" by (rule apply_ops_lt[OF js'])
  have FG: "\<And>x. ?F (?G x) = x" using apply_ops_rev[of "swops (rev ?js)"] by (simp add: rev_map)
  have "pmat (2 ^ K) ?F * pmat (2 ^ K) ?G = pmat (2 ^ K) (?F \<circ> ?G)" by (rule pmat_mult[OF Glt])
  also have "\<dots> = pmat (2 ^ K) id" by (rule pmat_cong) (simp add: FG)
  finally have PP: "pmat (2 ^ K) ?F * pmat (2 ^ K) ?G = 1\<^sub>m (2 ^ K)" by (simp add: pmat_id)
  have T: "\<And>M. M \<in> carrier_mat (2 ^ ?q) (2 ^ ?q) \<Longrightarrow> 1\<^sub>m (2 ^ (K - ?q)) \<Otimes> M \<in> carrier_mat (2 ^ K) (2 ^ K)"
    by (rule carrier_matI) (use KK in simp_all)
  have eQ: "wg K ws Q = pmat (2 ^ K) ?G * (1\<^sub>m (2 ^ (K - ?q)) \<Otimes> Q) * pmat (2 ^ K) ?F" by (rule wg_route[OF ws Q])
  have eQ2: "wg K ws Q2 = pmat (2 ^ K) ?G * (1\<^sub>m (2 ^ (K - ?q)) \<Otimes> Q2) * pmat (2 ^ K) ?F" by (rule wg_route[OF ws Q2])
  have "wg K ws Q * wg K ws Q2 = pmat (2 ^ K) ?G * ((1\<^sub>m (2 ^ (K - ?q)) \<Otimes> Q) * (1\<^sub>m (2 ^ (K - ?q)) \<Otimes> Q2)) * pmat (2 ^ K) ?F"
    unfolding eQ eQ2 by (rule conj_mult[OF pmat_carrier pmat_carrier T[OF Q] T[OF Q2] PP])
  also have "(1\<^sub>m (2 ^ (K - ?q)) \<Otimes> Q) * (1\<^sub>m (2 ^ (K - ?q)) \<Otimes> Q2) = 1\<^sub>m (2 ^ (K - ?q)) \<Otimes> (Q * Q2)"
    using mult_distr_tensor[of "1\<^sub>m (2 ^ (K - ?q))" "1\<^sub>m (2 ^ (K - ?q))" Q Q2] Q Q2 by simp
  finally show ?thesis using wg_route[OF ws mult_carrier_mat[OF Q Q2]] by simp
qed

lemma wg_one:
  assumes ws: "\<And>w. w \<in> set ws \<Longrightarrow> w < K"
  shows "wg K ws (1\<^sub>m (2 ^ length ws)) = 1\<^sub>m (2 ^ K)"
proof (rule eq_matI)
  fix x y assume "x < dim_row (1\<^sub>m (2 ^ K) :: complex Matrix.mat)" "y < dim_col (1\<^sub>m (2 ^ K) :: complex Matrix.mat)"
  hence x: "x < 2 ^ K" and y: "y < 2 ^ K" by simp_all
  have "(\<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i) \<and> dig ws x = dig ws y \<longleftrightarrow> x = y"
  proof
    assume h: "(\<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i) \<and> dig ws x = dig ws y"
    show "x = y"
    proof (rule bits_eq_nat[OF x y])
      fix i assume i: "i < K"
      show "bit x i = bit y i"
      proof (cases "i \<in> set ws")
        case True
        then obtain l where l: "l < length ws" "ws ! l = i" by (auto simp: in_set_conv_nth)
        have "bit (dig ws x) l = bit (dig ws y) l" using h by simp
        thus ?thesis using l by (simp add: bit_dig)
      qed (use h i in simp)
    qed
  qed simp
  thus "wg K ws (1\<^sub>m (2 ^ length ws)) $$ (x, y) = 1\<^sub>m (2 ^ K) $$ (x, y)"
    using x y dig_lt[of ws] by (auto simp: wg_index)
qed simp_all

lemma wg_dagger:
  assumes Q: "Q \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)"
  shows "(wg K ws Q)\<^sup>\<dagger> = wg K ws (Q\<^sup>\<dagger>)"
proof (rule eq_matI)
  fix x y assume "x < dim_row (wg K ws (Q\<^sup>\<dagger>))" "y < dim_col (wg K ws (Q\<^sup>\<dagger>))"
  hence x: "x < 2 ^ K" and y: "y < 2 ^ K" by simp_all
  have s: "(\<forall>i<K. i \<notin> set ws \<longrightarrow> bit y i = bit x i) \<longleftrightarrow> (\<forall>i<K. i \<notin> set ws \<longrightarrow> bit x i = bit y i)" by auto
  show "(wg K ws Q)\<^sup>\<dagger> $$ (x, y) = wg K ws (Q\<^sup>\<dagger>) $$ (x, y)"
    using x y Q dig_lt[of ws] by (auto simp: dagger_def wg_index s)
qed (simp_all add: dagger_def)

lemma wg_unitary:
  assumes ws: "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < K"
    and Q: "Q \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)" "Quantum.unitary Q"
  shows "Quantum.unitary (wg K ws Q)"
proof -
  have Qd: "Q\<^sup>\<dagger> \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)" by (rule dagger_carrier[OF Q(1)])
  have u: "(Q\<^sup>\<dagger>) * Q = 1\<^sub>m (2 ^ length ws)" "Q * (Q\<^sup>\<dagger>) = 1\<^sub>m (2 ^ length ws)"
    using Q unfolding Quantum.unitary_def by auto
  show ?thesis unfolding Quantum.unitary_def wg_dagger[OF Q(1)]
    by (simp add: wg_mult[OF ws Qd Q(1)] wg_mult[OF ws Q(1) Qd] u wg_one ws(2))
qed

subsection \<open>Wire gates in elementary gates\<close>

definition wg_gates :: "nat \<Rightarrow> nat list \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat list" where
  "wg_gates K ws Q = map (cgate K 1) (swops (wroute 0 ws)) @ [1\<^sub>m (2 ^ (K - length ws)) \<Otimes> Q]
     @ map (cgate K 1) (swops (rev (wroute 0 ws)))"

theorem wg_gates_props:
  assumes ws: "distinct ws" "\<And>w. w \<in> set ws \<Longrightarrow> w < K" and q: "length ws \<in> {1, 2}"
    and Q: "Q \<in> carrier_mat (2 ^ length ws) (2 ^ length ws)" "Quantum.unitary Q"
  shows "circuit_mat (2 ^ K) (wg_gates K ws Q) = wg K ws Q"
    "\<forall>U \<in> set (wg_gates K ws Q). elementary (2 ^ K) U"
    "length (wg_gates K ws Q) \<le> 4 * K + 1"
proof -
  let ?q = "length ws" and ?js = "wroute 0 ws"
  let ?M = "1\<^sub>m (2 ^ (K - ?q)) \<Otimes> Q"
  have rj: "\<And>j. j \<in> set ?js \<Longrightarrow> j + 2 \<le> K" by (rule wroute_range[OF ws])
  have rj': "\<And>j. j \<in> set (rev ?js) \<Longrightarrow> j + 2 \<le> K" using rj by simp
  note A = swops_circuit[OF rj] and C = swops_circuit[OF rj']
  have KK: "(2::nat) ^ K = 2 ^ (K - ?q) * (2 ^ ?q * 1)" using length_distinct_le[OF ws] by (simp flip: power_add)
  have eM: "elementary (2 ^ K) ?M"
    unfolding elementary_def KK using q Q
    by (intro exI[of _ "2 ^ (K - ?q)"] exI[of _ 1] exI[of _ ?q] exI[of _ Q]) (simp add: right_tensor_id[OF Q(1), unfolded One_nat_def])
  have Mc: "?M \<in> carrier_mat (2 ^ K) (2 ^ K)" by (rule elementary_unitary(1)[OF eM])
  show el: "\<forall>U \<in> set (wg_gates K ws Q). elementary (2 ^ K) U" using A(2) C(2) eM by (auto simp: wg_gates_def)
  let ?A = "map (cgate K 1) (swops ?js)" and ?C = "map (cgate K 1) (swops (rev ?js))"
  have e1: "circuit_mat (2 ^ K) (?A @ [?M] @ ?C) = circuit_mat (2 ^ K) ([?M] @ ?C) * circuit_mat (2 ^ K) ?A"
    by (rule circuit_mat_append) (use A(2) C(2) Mc elementary_unitary(1) in auto)
  have e2: "circuit_mat (2 ^ K) ([?M] @ ?C) = circuit_mat (2 ^ K) ?C * ?M"
    using circuit_mat_append[of "[?M]" "2 ^ K" ?C] C(2) Mc elementary_unitary(1) by auto
  have "circuit_mat (2 ^ K) (wg_gates K ws Q) = circuit_mat (2 ^ K) ?C * ?M * circuit_mat (2 ^ K) ?A"
    unfolding wg_gates_def using e1 e2 by simp
  thus "circuit_mat (2 ^ K) (wg_gates K ws Q) = wg K ws Q" by (simp only: A(1) C(1) wg_route[OF ws Q(1)])
  have "length ?js \<le> 2 * K" using length_wroute[OF ws, of 0] q by auto
  thus "length (wg_gates K ws Q) \<le> 4 * K + 1" by (simp add: wg_gates_def)
qed

subsection \<open>Composition and adjacent gates\<close>

lemma dig_dig: "(\<And>w. w \<in> set ws \<Longrightarrow> w < length vs) \<Longrightarrow> dig ws (dig vs x) = dig (map ((!) vs) ws) x"
  by (rule bit_eqI) (auto simp: bit_dig)

lemma wg_wg:
  assumes vs: "distinct vs" "\<And>v. v \<in> set vs \<Longrightarrow> v < K'" "length vs = K"
    and ws: "\<And>w. w \<in> set ws \<Longrightarrow> w < K"
  shows "wg K' vs (wg K ws Q) = wg K' (map ((!) vs) ws) Q"
proof (rule eq_matI)
  fix x y assume "x < dim_row (wg K' (map ((!) vs) ws) Q)" "y < dim_col (wg K' (map ((!) vs) ws) Q)"
  hence x: "x < 2 ^ K'" and y: "y < 2 ^ K'" by simp_all
  have dv: "dig vs x < 2 ^ K" "dig vs y < 2 ^ K" using dig_lt[of vs] vs(3) by auto
  have dd: "dig ws (dig vs x) = dig (map ((!) vs) ws) x" "dig ws (dig vs y) = dig (map ((!) vs) ws) y"
    using dig_dig[of ws vs] ws vs(3) by auto
  have c: "((\<forall>i<K'. i \<notin> set vs \<longrightarrow> bit x i = bit y i) \<and> (\<forall>i<K. i \<notin> set ws \<longrightarrow> bit (dig vs x) i = bit (dig vs y) i))
      \<longleftrightarrow> (\<forall>i<K'. i \<notin> set (map ((!) vs) ws) \<longrightarrow> bit x i = bit y i)"
  proof
    assume h: "(\<forall>i<K'. i \<notin> set vs \<longrightarrow> bit x i = bit y i) \<and> (\<forall>i<K. i \<notin> set ws \<longrightarrow> bit (dig vs x) i = bit (dig vs y) i)"
    show "\<forall>i<K'. i \<notin> set (map ((!) vs) ws) \<longrightarrow> bit x i = bit y i"
    proof (intro allI impI)
      fix p assume p: "p < K'" "p \<notin> set (map ((!) vs) ws)"
      show "bit x p = bit y p"
      proof (cases "p \<in> set vs")
        case True
        then obtain i where i: "i < K" "vs ! i = p" using vs(3) by (auto simp: in_set_conv_nth)
        have "i \<notin> set ws" using p(2) i(2) by auto
        hence "bit (dig vs x) i = bit (dig vs y) i" using h i(1) by blast
        thus ?thesis using i vs(3) by (simp add: bit_dig)
      qed (use h p in blast)
    qed
  next
    assume h: "\<forall>i<K'. i \<notin> set (map ((!) vs) ws) \<longrightarrow> bit x i = bit y i"
    have "\<forall>i<K'. i \<notin> set vs \<longrightarrow> bit x i = bit y i"
    proof (intro allI impI)
      fix p assume p: "p < K'" "p \<notin> set vs"
      have "p \<notin> set (map ((!) vs) ws)" using p(2) ws vs(3) by auto
      thus "bit x p = bit y p" using h p(1) by blast
    qed
    moreover have "\<forall>i<K. i \<notin> set ws \<longrightarrow> bit (dig vs x) i = bit (dig vs y) i"
    proof (intro allI impI)
      fix i assume i: "i < K" "i \<notin> set ws"
      have "vs ! i \<notin> set (map ((!) vs) ws)"
      proof
        assume "vs ! i \<in> set (map ((!) vs) ws)"
        then obtain w where w: "w \<in> set ws" "vs ! w = vs ! i" by auto
        hence "w = i" using nth_eq_iff_index_eq[OF vs(1)] ws vs(3) i(1) by auto
        thus False using w(1) i(2) by simp
      qed
      moreover have "vs ! i < K'" using vs(2,3) i(1) by simp
      ultimately have "bit x (vs ! i) = bit y (vs ! i)" using h by blast
      thus "bit (dig vs x) i = bit (dig vs y) i" using i(1) vs(3) by (simp add: bit_dig)
    qed
    ultimately show "(\<forall>i<K'. i \<notin> set vs \<longrightarrow> bit x i = bit y i) \<and> (\<forall>i<K. i \<notin> set ws \<longrightarrow> bit (dig vs x) i = bit (dig vs y) i)" ..
  qed
  show "wg K' vs (wg K ws Q) $$ (x, y) = wg K' (map ((!) vs) ws) Q $$ (x, y)"
    unfolding wg_index[OF x y] wg_index[OF dv] dd using c by auto
qed simp_all

lemma div_eq_bits: "x div 2 ^ n = y div 2 ^ n \<longleftrightarrow> (\<forall>i\<ge>n. bit x i = bit y i)" for x y :: nat
proof
  assume e: "x div 2 ^ n = y div 2 ^ n"
  show "\<forall>i\<ge>n. bit x i = bit y i"
  proof (intro allI impI)
    fix i assume "n \<le> i"
    hence "bit x i = bit (x div 2 ^ n) (i - n)" "bit y i = bit (y div 2 ^ n) (i - n)" by (simp_all add: bit_div_pow)
    thus "bit x i = bit y i" unfolding e by simp
  qed
qed (auto intro: bit_eqI simp: bit_div_pow)

lemma mod_eq_bits: "x mod 2 ^ n = y mod 2 ^ n \<longleftrightarrow> (\<forall>i<n. bit x i = bit y i)" for x y :: nat
proof -
  have "take_bit n x = take_bit n y \<longleftrightarrow> (\<forall>i<n. bit x i = bit y i)"
    by (auto simp: bit_eq_iff bit_take_bit_iff)
  thus ?thesis by (simp add: take_bit_eq_mod)
qed

lemma tensor_wg:
  assumes Q: "Q \<in> carrier_mat (2 ^ q) (2 ^ q)"
  shows "1\<^sub>m (2 ^ a) \<Otimes> (Q \<Otimes> 1\<^sub>m (2 ^ w)) = wg (a + q + w) [w..<w + q] Q"
proof (rule eq_matI)
  let ?K = "a + q + w" and ?n = "(2::nat) ^ q * 2 ^ w"
  fix x y assume "x < dim_row (wg ?K [w..<w + q] Q)" "y < dim_col (wg ?K [w..<w + q] Q)"
  hence x: "x < 2 ^ ?K" and y: "y < 2 ^ ?K" by simp_all
  have n: "?n = 2 ^ (q + w)" by (simp add: power_add)
  have K: "(2::nat) ^ ?K = 2 ^ a * ?n" by (simp add: power_add ac_simps)
  have xa: "x div ?n < 2 ^ a" "y div ?n < 2 ^ a" using x y K by (simp_all add: div_less_iff_less_mult)
  have xm: "x mod ?n < ?n" "y mod ?n < ?n" by simp_all
  have md: "(z mod ?n) div 2 ^ w = dig [w..<w + q] z" for z :: nat
  proof (rule bit_eqI)
    fix l
    show "bit (z mod ?n div 2 ^ w) l \<longleftrightarrow> bit (dig [w..<w + q] z) l"
      unfolding n bit_div_pow bit_dig by (auto simp flip: take_bit_eq_mod simp: bit_take_bit_iff ac_simps)
  qed
  have mm: "(z mod ?n) mod 2 ^ w = z mod 2 ^ w" for z :: nat
    by (simp add: mod_mod_cancel)
  have dq: "(z mod ?n) div 2 ^ w < 2 ^ q" for z :: nat using md dig_lt[of "[w..<w + q]" z] by simp
  have cond: "(x div ?n = y div ?n \<and> x mod 2 ^ w = y mod 2 ^ w) \<longleftrightarrow> (\<forall>i<?K. i \<notin> set [w..<w + q] \<longrightarrow> bit x i = bit y i)"
  proof
    assume h: "x div ?n = y div ?n \<and> x mod 2 ^ w = y mod 2 ^ w"
    show "\<forall>i<?K. i \<notin> set [w..<w + q] \<longrightarrow> bit x i = bit y i"
      using h unfolding n div_eq_bits mod_eq_bits by auto
  next
    assume h: "\<forall>i<?K. i \<notin> set [w..<w + q] \<longrightarrow> bit x i = bit y i"
    have hi: "\<forall>i\<ge>q + w. bit x i = bit y i"
    proof (intro allI impI)
      fix i assume i: "q + w \<le> i"
      show "bit x i = bit y i"
      proof (cases "i < ?K")
        case False
        thus ?thesis using x y bit_above[of x ?K i] bit_above[of y ?K i] by auto
      qed (use h i in auto)
    qed
    have lo: "\<forall>i<w. bit x i = bit y i" using h by auto
    show "x div ?n = y div ?n \<and> x mod 2 ^ w = y mod 2 ^ w" unfolding n div_eq_bits mod_eq_bits using hi lo by blast
  qed
  have "(1\<^sub>m (2 ^ a) \<Otimes> (Q \<Otimes> 1\<^sub>m (2 ^ w))) $$ (x, y)
      = 1\<^sub>m (2 ^ a) $$ (x div ?n, y div ?n) * (Q \<Otimes> 1\<^sub>m (2 ^ w)) $$ (x mod ?n, y mod ?n)"
    using index_tensor_mat[of "1\<^sub>m (2 ^ a)" "2 ^ a" "2 ^ a" "Q \<Otimes> 1\<^sub>m (2 ^ w)" ?n ?n x y] Q x y K by simp
  also have "(Q \<Otimes> 1\<^sub>m (2 ^ w)) $$ (x mod ?n, y mod ?n)
      = Q $$ (x mod ?n div 2 ^ w, y mod ?n div 2 ^ w) * 1\<^sub>m (2 ^ w) $$ (x mod 2 ^ w, y mod 2 ^ w)"
    using index_tensor_mat[of Q "2 ^ q" "2 ^ q" "1\<^sub>m (2 ^ w)" "2 ^ w" "2 ^ w" "x mod ?n" "y mod ?n"] Q xm
    by (simp add: mm)
  finally show "(1\<^sub>m (2 ^ a) \<Otimes> (Q \<Otimes> 1\<^sub>m (2 ^ w))) $$ (x, y) = wg ?K [w..<w + q] Q $$ (x, y)"
    unfolding wg_index[OF x y] md using xa cond by (auto simp: md)
qed (use Q in \<open>simp_all add: power_add\<close>)

lemma qw_wg:
  assumes w: "w < K" and G: "G \<in> carrier_mat 2 2"
  shows "qw K w G = wg K [w] G"
proof -
  have e: "K - Suc w + 1 + w = K" using w by simp
  have "qw K w G = wg (K - Suc w + 1 + w) [w..<w + 1] G" unfolding qw_def by (rule tensor_wg) (use G in simp)
  thus ?thesis unfolding e by simp
qed

end
