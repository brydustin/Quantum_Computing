theory Reversible_Gates
  imports HHL_Algorithm.HHL_Sparse_Split
begin

section \<open>Reversible gates on bits\<close>

text \<open>Basis states of $m$ qubits are the numbers below $2^m$; a reversible gate flips one bit
of the index, possibly controlled by others.  Bit $p$ is the coefficient of $2^p$.\<close>

datatype rgate = NOT nat | CNOT nat nat | TOF nat nat nat

fun rg :: "rgate \<Rightarrow> nat \<Rightarrow> nat" where
  "rg (NOT p) x = flip_bit p x"
| "rg (CNOT c p) x = (if bit x c then flip_bit p x else x)"
| "rg (TOF a b p) x = (if bit x a \<and> bit x b then flip_bit p x else x)"

fun targ :: "rgate \<Rightarrow> nat" where
  "targ (NOT p) = p" | "targ (CNOT c p) = p" | "targ (TOF a b p) = p"

fun wires :: "rgate \<Rightarrow> nat set" where
  "wires (NOT p) = {p}" | "wires (CNOT c p) = {c, p}" | "wires (TOF a b p) = {a, b, p}"

fun rg_ok :: "nat \<Rightarrow> rgate \<Rightarrow> bool" where
  "rg_ok m (NOT p) \<longleftrightarrow> p < m"
| "rg_ok m (CNOT c p) \<longleftrightarrow> c < m \<and> p < m \<and> c \<noteq> p"
| "rg_ok m (TOF a b p) \<longleftrightarrow> a < m \<and> b < m \<and> p < m \<and> a \<noteq> p \<and> b \<noteq> p"

lemma flip_bit_twice [simp]: "flip_bit p (flip_bit p x) = (x :: nat)"
  by (rule bit_eqI) (auto simp: bit_flip_bit_iff)

lemma flip_bit_neq: "flip_bit p x \<noteq> (x :: nat)"
  using bit_flip_bit_iff[of p x p] by auto

lemma flip_bit_lt:
  fixes x :: nat
  assumes x: "x < 2 ^ m" and p: "p < m"
  shows "flip_bit p x < 2 ^ m"
proof -
  have "take_bit m x = x" using x by (simp add: take_bit_nat_eq_self_iff)
  hence "take_bit m (flip_bit p x) = flip_bit p x" using p by (simp add: take_bit_flip_bit_eq)
  thus ?thesis by (simp add: take_bit_nat_eq_self_iff)
qed

text \<open>A gate is active on $x$ when its controls are set; then it flips its target.\<close>

fun active :: "rgate \<Rightarrow> nat \<Rightarrow> bool" where
  "active (NOT p) x = True"
| "active (CNOT c p) x = bit x c"
| "active (TOF a b p) x = (bit x a \<and> bit x b)"

lemma rg_active: "rg g x = (if active g x then flip_bit (targ g) x else x)"
  by (cases g) simp_all

lemma active_rg: "rg_ok m g \<Longrightarrow> active g (rg g x) = active g x"
  by (cases g) (auto simp: bit_flip_bit_iff)

lemma rg_lt: "rg_ok m g \<Longrightarrow> x < 2 ^ m \<Longrightarrow> rg g x < 2 ^ m"
  by (cases g) (auto intro: flip_bit_lt)

lemma rg_invol: "rg_ok m g \<Longrightarrow> rg g (rg g x) = x"
  using active_rg[of m g x] by (simp add: rg_active)

lemma bit_rg: "bit (rg g x) q \<longleftrightarrow> (if q = targ g \<and> active g x then \<not> bit x q else bit x q)"
  by (simp add: rg_active bit_flip_bit_iff)

text \<open>A circuit applies its gates left to right.\<close>

definition rcirc :: "rgate list \<Rightarrow> nat \<Rightarrow> nat" where
  "rcirc gs = fold rg gs"

lemma rcirc_Nil [simp]: "rcirc [] x = x" and rcirc_Cons [simp]: "rcirc (g # gs) x = rcirc gs (rg g x)"
  and rcirc_append: "rcirc (gs @ hs) x = rcirc hs (rcirc gs x)"
  by (simp_all add: rcirc_def)

lemma rcirc_lt: "\<forall>g \<in> set gs. rg_ok m g \<Longrightarrow> x < 2 ^ m \<Longrightarrow> rcirc gs x < 2 ^ m"
  by (induction gs arbitrary: x) (auto intro: rg_lt)

text \<open>Running a circuit backwards undoes it.\<close>

lemma rcirc_rev: "\<forall>g \<in> set gs. rg_ok m g \<Longrightarrow> rcirc (rev gs) (rcirc gs x) = x"
  by (induction gs arbitrary: x) (auto simp: rcirc_append rg_invol)

end
