theory Gate_Routing
  imports Reversible_Gates HHL_Algorithm.HHL_Uniform_Rotation
begin

section \<open>Routing reversible gates to the bottom wires\<close>

text \<open>The HHL entry already compiles the adjacent swap \<open>opf (False, j)\<close> and the adjacent CNOT
\<open>opf (True, j)\<close> to elementary gates.  Here every reversible gate is moved to wires $0,1,2$ by
chains of adjacent swaps, applied there, and moved back.\<close>

subsection \<open>Bits of an adjacent two-bit rewrite\<close>

lemma bit_digit: "k < 2 \<Longrightarrow> bit (c div 2 ^ j mod 4) k \<longleftrightarrow> bit c (j + k)" for c :: nat
proof -
  have "c div 2 ^ j mod 4 = take_bit 2 (drop_bit j c)" by (simp add: take_bit_eq_mod drop_bit_eq_div)
  thus "k < 2 \<Longrightarrow> ?thesis" by (simp add: bit_take_bit_iff bit_drop_bit_eq)
qed

lemma bit_lift2:
  assumes g: "\<And>x. x < 4 \<Longrightarrow> g x < 4"
  shows "bit (lift2 g j c) i \<longleftrightarrow> (if j \<le> i \<and> i < j + 2 then bit (g (c div 2 ^ j mod 4)) (i - j) else bit c i)"
proof -
  have d1: "lift2 g j c div (4 * 2 ^ j) = c div (4 * 2 ^ j)" by (rule lift2_digits(1)) (use g in blast)
  have d2: "lift2 g j c div 2 ^ j mod 4 = g (c div 2 ^ j mod 4)" by (rule lift2_digits(2)) (use g in blast)
  have d3: "lift2 g j c mod 2 ^ j = c mod 2 ^ j" by (rule lift2_digits(3)) (use g in blast)
  note d = d1 d2 d3
  consider "i < j" | "j \<le> i" "i < j + 2" | "j + 2 \<le> i" by linarith
  thus ?thesis
  proof cases
    case 1
    have lo: "bit x i \<longleftrightarrow> bit (x mod 2 ^ j) i" for x :: nat using 1 by (simp add: bit_take_bit_iff flip: take_bit_eq_mod)
    show ?thesis using 1 lo[of "lift2 g j c"] lo[of c] d(3) by simp
  next
    case 2
    have "bit (lift2 g j c) i \<longleftrightarrow> bit (lift2 g j c div 2 ^ j mod 4) (i - j)" using 2 by (simp add: bit_digit)
    thus ?thesis using 2 d(2) by simp
  next
    case 3
    have "bit x i \<longleftrightarrow> bit (x div (4 * 2 ^ j)) (i - (j + 2))" for x :: nat
    proof -
      have dd: "x div (4 * 2 ^ j) = drop_bit (j + 2) x" by (simp add: drop_bit_eq_div power_add ac_simps)
      have e: "(j + 2) + (i - (j + 2)) = i" using 3 by simp
      have "bit (x div (4 * 2 ^ j)) (i - (j + 2)) \<longleftrightarrow> bit x ((j + 2) + (i - (j + 2)))"
        unfolding dd by (simp only: bit_drop_bit_eq comp_def)
      thus ?thesis unfolding e by simp
    qed
    thus ?thesis using 3 d(1) by simp
  qed
qed

lemma four_cases: "d < 4 \<Longrightarrow> d = 0 \<or> d = 1 \<or> d = 2 \<or> d = (3 :: nat)" by auto
lemma two_cases: "k < 2 \<Longrightarrow> k = 0 \<or> k = (1 :: nat)" by auto

lemma bit_gs:
  assumes "d < 4" "k < 2"
  shows "bit (gs d) k \<longleftrightarrow> bit d (1 - k)"
  using four_cases[OF assms(1)] two_cases[OF assms(2)] by (elim disjE) (simp_all add: Transposition.transpose_def bit_iff_odd)

lemma bit_gc:
  assumes "d < 4" "k < 2"
  shows "bit (gc d) k \<longleftrightarrow> (if k = 0 \<and> bit d 1 then \<not> bit d 0 else bit d k)"
  using four_cases[OF assms(1)] two_cases[OF assms(2)] by (elim disjE) (simp_all add: Transposition.transpose_def bit_iff_odd)

text \<open>The adjacent swap exchanges bits $j$ and $j+1$; the adjacent CNOT is \<open>CX (j+1) j\<close>.\<close>

lemma bit_swap_op: "bit (opf (False, j) c) i \<longleftrightarrow> bit c (Transposition.transpose j (Suc j) i)"
proof -
  have "bit (opf (False, j) c) i \<longleftrightarrow> (if j \<le> i \<and> i < j + 2 then bit (gs (c div 2 ^ j mod 4)) (i - j) else bit c i)"
    unfolding opf_def opg_def using bit_lift2[of gs, OF gs_props(1)] by simp
  also have "\<dots> \<longleftrightarrow> bit c (Transposition.transpose j (Suc j) i)"
  proof -
    let ?d = "c div 2 ^ j mod 4"
    have d0: "bit ?d 0 \<longleftrightarrow> bit c j" and d1: "bit ?d 1 \<longleftrightarrow> bit c (Suc j)"
      using bit_digit[of 0 c j] bit_digit[of 1 c j] by simp_all
    have g0: "bit (gs ?d) 0 \<longleftrightarrow> bit ?d 1" and g1: "bit (gs ?d) 1 \<longleftrightarrow> bit ?d 0"
      using bit_gs[of ?d 0] bit_gs[of ?d 1] by simp_all
    consider "i = j" | "i = Suc j" | "i < j" | "Suc (Suc j) \<le> i" by linarith
    thus ?thesis using d0 d1 g0 g1 by cases (simp_all add: Transposition.transpose_def)
  qed
  finally show ?thesis .
qed

lemma cx_op: "opf (True, j) c = rg (CX (Suc j) j) c"
proof (rule bit_eqI)
  fix i
  have "bit (opf (True, j) c) i \<longleftrightarrow> (if j \<le> i \<and> i < j + 2 then bit (gc (c div 2 ^ j mod 4)) (i - j) else bit c i)"
    unfolding opf_def opg_def using bit_lift2[of gc, OF gc_props(1)] by simp
  also have "\<dots> \<longleftrightarrow> bit (rg (CX (Suc j) j) c) i"
  proof -
    let ?d = "c div 2 ^ j mod 4"
    have d0: "bit ?d 0 \<longleftrightarrow> bit c j" and d1: "bit ?d 1 \<longleftrightarrow> bit c (Suc j)"
      using bit_digit[of 0 c j] bit_digit[of 1 c j] by simp_all
    have g0: "bit (gc ?d) 0 \<longleftrightarrow> (if bit ?d 1 then \<not> bit ?d 0 else bit ?d 0)" and g1: "bit (gc ?d) 1 \<longleftrightarrow> bit ?d 1"
      using bit_gc[of ?d 0] bit_gc[of ?d 1] by simp_all
    consider "i = j" | "i = Suc j" | "i < j" | "Suc (Suc j) \<le> i" by linarith
    thus ?thesis using d0 d1 g0 g1 by cases (simp_all add: bit_rg del: rg.simps)
  qed
  finally show "bit (opf (True, j) c) i \<longleftrightarrow> bit (rg (CX (Suc j) j) c) i" .
qed

subsection \<open>Chains of adjacent swaps\<close>

abbreviation swops :: "nat list \<Rightarrow> (bool \<times> nat) list" where "swops js \<equiv> map (Pair False) js"

text \<open>After the swaps \<open>js\<close>, position $i$ holds the bit that was at \<open>pm js i\<close>.\<close>

fun pm :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "pm [] i = i"
| "pm (j # js) i = Transposition.transpose j (Suc j) (pm js i)"

lemma bit_swops: "bit (apply_ops (swops js) c) i \<longleftrightarrow> bit c (pm js i)"
  by (induction js arbitrary: c) (simp_all add: bit_swap_op)

lemma pm_append: "pm (js @ ks) i = pm js (pm ks i)"
  by (induction js) simp_all

lemma pm_rev: "pm (rev js) (pm js i) = i" "pm js (pm (rev js) i) = i"
  by (induction js arbitrary: i) (simp_all add: pm_append)

text \<open>\<open>dn x y\<close> carries the bit at $x$ down to $y$ and shifts the bits in between up by one.\<close>

text_raw \<open>
\begin{center}\normalfont
\begin{quantikz}[row sep={0.75cm,between origins}, column sep=0.6cm]
\lstick{$0$} & \qw & \qw & \swap{1} & \targ{} & \swap{1} & \qw & \qw & \qw\\
\lstick{$1$} & \qw & \swap{1} & \targX{} & \qw & \targX{} & \swap{1} & \qw & \qw\\
\lstick{$2$} & \swap{1} & \targX{} & \qw & \qw & \qw & \targX{} & \swap{1} & \qw\\
\lstick{$3$} & \targX{} & \qw & \qw & \qw & \qw & \qw & \targX{} & \qw
\end{quantikz}
\;=\;
\begin{quantikz}[row sep={0.75cm,between origins}, column sep=0.6cm]
\lstick{$0$} & \qw & \qw\\ \lstick{$1$} & \qw & \qw\\ \lstick{$2$} & \qw & \qw\\ \lstick{$3$} & \targ{} & \qw
\end{quantikz}\\[0.2em]
{\small \texttt{dn 3 0}: the bit on wire $3$ is carried down to wire $0$ by adjacent swaps, the gate acts there, and the swaps are undone.}
\end{center}
\<close>

definition dn :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where "dn x y = rev [y..<x]"

lemma length_dn [simp]: "length (dn x y) = x - y" by (simp add: dn_def)

lemma pm_dn: "y \<le> x \<Longrightarrow> pm (dn x y) i = (if i = y then x else if y < i \<and> i \<le> x then i - 1 else i)"
proof (induction x)
  case (Suc x)
  show ?case
  proof (cases "y \<le> x")
    case True
    have "dn (Suc x) y = x # dn x y" using True by (simp add: dn_def)
    thus ?thesis using Suc.IH[OF True] True by (auto simp: Transposition.transpose_def)
  next
    case False
    hence "y = Suc x" using Suc.prems by simp
    thus ?thesis by (simp add: dn_def)
  qed
qed (simp add: dn_def)

text \<open>Where wire $i \ne x$ sits after \<open>dn x y\<close>.\<close>

definition np :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where "np x y i = (if y \<le> i \<and> i < x then Suc i else i)"

lemma pm_dn_np: "y \<le> x \<Longrightarrow> i \<noteq> x \<Longrightarrow> pm (dn x y) (np x y i) = i"
  by (auto simp: pm_dn np_def)

lemma np_inj: "i \<noteq> x \<Longrightarrow> i' \<noteq> x \<Longrightarrow> i \<noteq> i' \<Longrightarrow> np x y i \<noteq> np x y i'"
  by (auto simp: np_def)

lemma np_ne: "y \<le> x \<Longrightarrow> i \<noteq> x \<Longrightarrow> y \<le> i \<Longrightarrow> np x y i \<noteq> y"
  by (auto simp: np_def)

lemma np_lt: "i < K \<Longrightarrow> x < K \<Longrightarrow> i \<noteq> x \<Longrightarrow> np x y i < K"
  by (auto simp: np_def)

subsection \<open>Conjugating a gate by swaps\<close>

fun rename :: "(nat \<Rightarrow> nat) \<Rightarrow> rgate \<Rightarrow> rgate" where
  "rename f (NOT p) = NOT (f p)"
| "rename f (CX c p) = CX (f c) (f p)"
| "rename f (TOF a b p) = TOF (f a) (f b) (f p)"

lemma conj_swops:
  "apply_ops (swops (rev js)) (rg g (apply_ops (swops js) c)) = rg (rename (pm js) g) c"
proof (rule bit_eqI)
  fix i
  let ?w = "apply_ops (swops js) c"
  have a: "active g ?w \<longleftrightarrow> active (rename (pm js) g) c" by (cases g) (simp_all add: bit_swops)
  have t: "pm (rev js) i = targ g \<longleftrightarrow> i = targ (rename (pm js) g)"
    using pm_rev[of js] by (cases g) auto
  show "bit (apply_ops (swops (rev js)) (rg g ?w)) i \<longleftrightarrow> bit (rg (rename (pm js) g) c) i"
    unfolding bit_swops bit_rg a t by (simp add: bit_swops pm_rev)
qed

subsection \<open>The route of one gate\<close>

text \<open>The target goes to wire 0, the controls to wires 1 and 2.\<close>

fun gate_route :: "rgate \<Rightarrow> nat list \<times> rgate" where
  "gate_route (NOT p) = (dn p 0, NOT 0)"
| "gate_route (CX c p) = (dn p 0 @ dn (np p 0 c) 1, CX 1 0)"
| "gate_route (TOF a b p) = (if a = b then (dn p 0 @ dn (np p 0 a) 1, CX 1 0) else
     (dn p 0 @ dn (np p 0 b) 1 @ dn (np (np p 0 b) 1 (np p 0 a)) 2, TOF 2 1 0))"

lemma np_ge1: "i \<noteq> p \<Longrightarrow> 1 \<le> np p 0 i" by (auto simp: np_def)

lemma route_cnot:
  assumes cp: "c \<noteq> p"
  shows "rename (pm (dn p 0 @ dn (np p 0 c) 1)) (CX 1 0) = CX c p"
proof -
  have c1: "1 \<le> np p 0 c" by (rule np_ge1[OF cp])
  have "pm (dn (np p 0 c) 1) 0 = 0" "pm (dn (np p 0 c) 1) 1 = np p 0 c" using c1 by (simp_all add: pm_dn)
  thus ?thesis using pm_dn_np[of 0 p c] cp by (simp add: pm_append pm_dn)
qed

lemma route_tof:
  assumes ap: "a \<noteq> p" and bp: "b \<noteq> p" and ab: "a \<noteq> b"
  defines "b1 \<equiv> np p 0 b" and "a1 \<equiv> np p 0 a"
  shows "rename (pm (dn p 0 @ dn b1 1 @ dn (np b1 1 a1) 2)) (TOF 2 1 0) = TOF a b p"
proof -
  let ?a2 = "np b1 1 a1"
  have b1: "1 \<le> b1" unfolding b1_def by (rule np_ge1[OF bp])
  have a1: "1 \<le> a1" unfolding a1_def by (rule np_ge1[OF ap])
  have ab1: "a1 \<noteq> b1" unfolding a1_def b1_def using ap bp ab by (rule np_inj)
  have a2: "2 \<le> ?a2" using a1 b1 ab1 by (auto simp: np_def)
  have p0: "pm (dn p 0) 0 = p" and p1: "pm (dn p 0) b1 = b" and p2: "pm (dn p 0) a1 = a"
    using pm_dn_np[of 0 p b] pm_dn_np[of 0 p a] ap bp by (simp_all add: pm_dn a1_def b1_def)
  have q0: "pm (dn b1 1) 0 = 0" and q1: "pm (dn b1 1) 1 = b1" and q2: "pm (dn b1 1) ?a2 = a1"
    using b1 pm_dn_np[of 1 b1 a1] ab1 by (simp_all add: pm_dn)
  have r: "pm (dn ?a2 2) 0 = 0" "pm (dn ?a2 2) 1 = 1" "pm (dn ?a2 2) 2 = ?a2" using a2 by (simp_all add: pm_dn)
  show ?thesis using r q0 q1 q2 p0 p1 p2 by (simp add: pm_append)
qed

theorem route_correct:
  assumes ok: "rg_ok K g" and r: "gate_route g = (js, h)"
  shows "apply_ops (swops (rev js)) (rg h (apply_ops (swops js) c)) = rg g c"
proof -
  have "rg (rename (pm js) h) c = rg g c"
  proof (cases g)
    case (NOT p)
    thus ?thesis using r by (auto simp: pm_dn)
  next
    case (CX c' p)
    thus ?thesis using r ok route_cnot[of c' p] by auto
  next
    case (TOF a b p)
    show ?thesis
    proof (cases "a = b")
      case True
      thus ?thesis using TOF r ok route_cnot[of a p] by auto
    next
      case False
      thus ?thesis using TOF r ok route_tof[of a p b] by auto
    qed
  qed
  thus ?thesis by (simp add: conj_swops)
qed

text \<open>Cost and range of a route on $K$ wires.\<close>

lemma dn_range: "j \<in> set (dn x y) \<Longrightarrow> x < K \<Longrightarrow> j + 2 \<le> K" by (auto simp: dn_def)

lemma np_le: "np x y i \<le> max i x" by (auto simp: np_def)

lemma route_range:
  assumes ok: "rg_ok K g" and r: "gate_route g = (js, h)" and j: "j \<in> set js"
  shows "j + 2 \<le> K"
  using ok r j by (cases g) (auto simp: dn_def np_def split: if_splits)

lemma route_length:
  assumes ok: "rg_ok K g" and r: "gate_route g = (js, h)"
  shows "length js \<le> 3 * K"
  using ok r by (cases g) (auto simp: np_def split: if_splits)

lemma route_core: "snd (gate_route g) \<in> {NOT 0, CX 1 0, TOF 2 1 0}"
  by (cases g) auto

end
