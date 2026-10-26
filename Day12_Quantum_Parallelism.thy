(*  Title:   Day12_Quantum_Parallelism.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 23 September 2011 (Day 12)
*)

theory Day12_Quantum_Parallelism
  imports Day11_Gates_No_Cloning
begin

section \<open>Day 12 (23 September 2011): quantum parallelism\<close>

text \<open>Since $He_0=(e_0+e_1)/\sqrt2$,
\[ H^{\otimes N}(e_0\otimes\cdots\otimes e_0)=\Bigl(\tfrac1{\sqrt2}\Bigr)^N\sum_{J\in\Z_2^N}e_J
   =\Bigl(\tfrac1{\sqrt2}\Bigr)^N\sum_J\ket J . \]
Only the case $N=1$ is stated here; the general identity is \<open>hadamard_uniform_N\<close> in
\<open>Day12_Counting_Probability\<close> (with \<open>tensor_pow_mat\<close> for $H^{\otimes N}$).

\begin{notesdef}[Oracle]
For $f:\Z_2^N\to\Z_2$, the vectors $e_J\otimes e_{i+f(J)}$ form an orthonormal basis of
$(\C^2)^{\otimes N}\otimes\C^2$, so there is a unitary $U_f$ with
$U_f(e_J\otimes e_i)=e_J\otimes e_{i+f(J)}$, the \emph{oracle} for $f$.
\end{notesdef}
\begin{notesprop}
For a unit vector $\gamma$, the measurement $P_0=\ketbra\gamma\gamma$, $P_1=I-P_0$ has
$p_0(\psi)=|\braket\gamma\psi|^2$ and $p_1(\psi)=1-|\braket\gamma\psi|^2$.
\end{notesprop}
Application: with $x=(He_0)^{\otimes N}$, $U_f(x\otimes e_0)=2^{-N/2}\sum_J e_J\otimes e_{f(J)}$,
and measuring against $\gamma=x\otimes e_0$ gives $\braket\gamma{U_f(x\otimes e_0)}=M/2^N$ with
$M=\#\{J:f(J)=0\}$, hence $p_0=(M/2^N)^2$: repeating the experiment estimates $M$ (a
Bernoulli trial).  The existence of the oracle is formalised below; the proposition is
\<open>rank_one_meas_prob\<close> (Day 8); the counting identity is \<open>counting_probability\<close> in
\<open>Day12_Counting_Probability\<close>.\<close>

definition oracle_unitary :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "oracle_unitary f N \<equiv>
     \<exists>U :: complex Matrix.mat.
       U \<in> carrier_mat (2^(N+1)) (2^(N+1)) \<and>
       unitary U \<and>
       (\<forall>J < 2^N. \<forall>i < 2.
          U *\<^sub>v (tensor_vec (unit_vec (2^N) J) (unit_vec 2 i)) =
          tensor_vec (unit_vec (2^N) J) (unit_vec 2 ((i + f J) mod 2)))"


theorem oracle_exists:
  fixes f :: "nat \<Rightarrow> nat"
  assumes f_range: "\<forall>J < 2^(N :: nat). f J < 2"
  shows "oracle_unitary f N"
proof -
  define d :: nat where "d = (2::nat)^(N+1)"
  define d0 :: nat where "d0 = (2::nat)^N"
  have d_eq: "d = d0 * 2"
    unfolding d_def d0_def
  proof -
    have "(2::nat)^(N+1) = (2::nat)^N * (2::nat)^1"
      by (rule power_add)
    also have "(2::nat)^N * (2::nat)^1 = (2::nat)^N * 2"
      by simp
    finally show "(2::nat)^(N+1) = (2::nat)^N * 2" .
  qed
  have d0_pos: "0 < d0" by (simp add: d0_def)
  have d_pos: "0 < d" by (simp add: d_def)

  \<comment> \<open>The oracle permutes basis indices by flipping bit 0 (target qubit) when
      \<open>f (l div 2) = 1\<close>.  We express it as a function \<open>\<sigma>\<close>.\<close>
  define \<sigma> :: "nat \<Rightarrow> nat" where
    "\<sigma> l = (l div 2) * 2 + ((l mod 2) + f (l div 2)) mod 2" for l

  \<comment> \<open>The function \<open>\<sigma>\<close> stays inside the index range.\<close>
  have \<sigma>_bound: "\<And>l. l < d \<Longrightarrow> \<sigma> l < d"
  proof -
    fix l :: nat assume l: "l < d"
    have div_lt: "l div 2 < d0"
      using l d_eq by (simp add: less_mult_imp_div_less)
    hence "(l div 2) * 2 \<le> (d0 - 1) * 2"
      by (simp add: mult_le_mono1)
    also have "\<dots> = d - 2" using d_eq d0_pos by (simp add: mult.commute)
    finally have bound1: "(l div 2) * 2 \<le> d - 2" .
    have bound2: "((l mod 2) + f (l div 2)) mod 2 < 2" by simp
    have "\<sigma> l < (l div 2) * 2 + 2"
      unfolding \<sigma>_def using bound2 by linarith
    also have "\<dots> \<le> d" using bound1 d_eq d0_pos by linarith
    finally show "\<sigma> l < d" .
  qed

  \<comment> \<open>The function \<open>\<sigma>\<close> is an involution: \<open>\<sigma> \<circ> \<sigma> = id\<close>.\<close>
  have \<sigma>_invol: "\<And>l. l < d \<Longrightarrow> \<sigma> (\<sigma> l) = l"
  proof -
    fix l :: nat assume l: "l < d"
    define J where "J = l div 2"
    define i where "i = l mod 2"
    have J_lt: "J < d0" using l d_eq J_def by (simp add: less_mult_imp_div_less)
    have i_lt: "i < 2" using i_def by simp
    have l_eq: "l = J * 2 + i"
      using J_def i_def by (metis mult_div_mod_eq mult.commute)
    have fJ_lt: "f J < 2" using f_range J_lt d0_def by blast

    \<comment> \<open>Compute \<open>\<sigma> l\<close>.\<close>      
    have s1: "\<sigma> l = J * 2 + (i + f J) mod 2"
      unfolding \<sigma>_def J_def[symmetric] i_def[symmetric] by simp
    let ?i1 = "(i + f J) mod 2"
    have i1_lt: "?i1 < 2" by simp

    \<comment> \<open>Decompose \<open>\<sigma> l\<close> in the same div/mod form.\<close>
    have div_sub: "(J * 2 + ?i1) div 2 = J"
      using i1_lt by simp
    have mod_sub: "(J * 2 + ?i1) mod 2 = ?i1"
      using i1_lt by simp

    have "\<sigma> (\<sigma> l) = J * 2 + (?i1 + f J) mod 2"
      using s1 unfolding \<sigma>_def
      using div_sub mod_sub by presburger
    also have "(?i1 + f J) mod 2 = (i + 2 * f J) mod 2"
      by (simp add: mod_add_left_eq mult_2, presburger)
    also have "\<dots> = i mod 2" by simp
    also have "i mod 2 = i" using i_lt by simp
    finally show "\<sigma> (\<sigma> l) = l" using l_eq by simp
  qed

  \<comment> \<open>Define the oracle matrix as the permutation matrix for \<open>\<sigma>\<close>.\<close>
  define U :: "complex Matrix.mat" where
    "U = Matrix.mat d d (\<lambda>(k, l). if k = \<sigma> l then 1 else 0)"
  have U_dr: "dim_row U = d" by (simp add: U_def)
  have U_dc: "dim_col U = d" by (simp add: U_def)
  have U_carr: "U \<in> carrier_mat d d"
    using U_dr U_dc by auto

  have U_entry: "\<And>k l. k < d \<Longrightarrow> l < d \<Longrightarrow>
      U $$ (k, l) = (if k = \<sigma> l then 1 else 0)"
    by (simp add: U_def)

  \<comment> \<open>Column \<open>l\<close> of \<open>U\<close> has a unique 1 at row \<open>\<sigma> l\<close>; row \<open>k\<close> has a unique 1
      at column \<open>\<sigma> k\<close> (by involution).\<close>
  have U_row: "\<And>k m. k < d \<Longrightarrow> m < d \<Longrightarrow>
      U $$ (k, m) = (if m = \<sigma> k then 1 else 0)"
  proof -
    fix k m :: nat 
    assume k: "k < d" and m: "m < d"
    show "U $$ (k, m) = (if m = \<sigma> k then 1 else 0)"
    proof (cases "k = \<sigma> m")
      assume k_eqs: "k = \<sigma> m"
      then have "\<sigma> k = m" using \<sigma>_invol[OF m] by auto
      with k_eqs U_entry[OF k m] 
      show ?thesis 
        by simp
    next
      assume kne: "k \<noteq> \<sigma> m"
      \<comment> \<open>We also cannot have \<open>m = \<sigma> k\<close>, since otherwise
          \<open>\<sigma> m\<close> would equal \<open>\<sigma> (\<sigma> k)\<close>, which by
          involution equals \<open>k\<close>, contradicting \<open>kne\<close>.\<close>
      have "m \<noteq> \<sigma> k"
      proof
        assume "m = \<sigma> k"
        hence "\<sigma> m = \<sigma> (\<sigma> k)" by simp
        also have "\<dots> = k" using \<sigma>_invol[OF k].
        finally have "\<sigma> m = k".
        thus False using kne by simp
      qed
      with kne U_entry[OF k m] show ?thesis by simp
    qed
  qed

  \<comment> \<open>Unitarity of \<open>U\<close>: \<open>U\<^sup>\<dagger> = U\<close> and \<open>U * U = 1\<^sub>m d\<close>.\<close>
  have U_dagger: "U\<^sup>\<dagger> = U"
  proof (rule eq_matI)
    show "dim_row (U\<^sup>\<dagger>) = dim_row U" by (simp add: U_def dagger_def)
    show "dim_col (U\<^sup>\<dagger>) = dim_col U" by (simp add: U_def dagger_def)
  next
    fix k l
    assume "k < dim_row U" and "l < dim_col U"
    then have k: "k < d" and l: "l < d" by (simp_all add: U_dr U_dc)
    have "U\<^sup>\<dagger> $$ (k, l) = cnj (U $$ (l, k))"
      using k l by (simp add: dagger_def U_def)
    also have "\<dots> = cnj (if l = \<sigma> k then 1 else 0)"
      using d_eq U_row \<sigma>_invol k l by force  
    also have "\<dots> = (if l = \<sigma> k then 1 else 0)"
      by (simp add: if_distrib [where f = cnj] cong: if_cong)
    also have "\<dots> = U $$ (k, l)"
      using U_row[OF k l] by simp
    finally show "U\<^sup>\<dagger> $$ (k, l) = U $$ (k, l)".
  qed

  have U_sq: "U * U = 1\<^sub>m d"
  proof (rule eq_matI)
    show "dim_row (U * U) = dim_row (1\<^sub>m d)" by (simp add: U_dr)
    show "dim_col (U * U) = dim_col (1\<^sub>m d)" by (simp add: U_dc)
  next
    fix k l
    assume "k < dim_row (1\<^sub>m d)" and "l < dim_col (1\<^sub>m d)"
    then have k: "k < d" and l: "l < d" by simp_all
    have \<sigma>l_lt: "\<sigma> l < d" using \<sigma>_bound l by blast

    have "(U * U) $$ (k, l) = (\<Sum>m = 0..<d. U $$ (k, m) * U $$ (m, l))"
      using k l U_dr U_dc by (simp add: times_mat_def scalar_prod_def)
    also have "\<dots> = (\<Sum>m = 0..<d.
          (if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0))"
    proof (rule sum.cong, simp)
      fix m assume "m \<in> {0..<d}"
      hence m: "m < d" by simp
      have hk: "U $$ (k, m) = (if m = \<sigma> k then 1 else 0)"
        using U_row[OF k m] .
      have hl: "U $$ (m, l) = (if m = \<sigma> l then 1 else 0)"
        using U_entry[OF m l] .
      show "U $$ (k, m) * U $$ (m, l)
              = (if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0)"
        by (simp add: hk hl)
    qed
    also have "\<dots> = (if \<sigma> k = \<sigma> l then 1 else 0)"
    proof (cases "\<sigma> k = \<sigma> l")
      case True
      have pw: "(if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0)
              = (if m = \<sigma> k then 1 else 0)" for m
        using True by simp
      have "(\<Sum>m = 0..<d.
             (if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0))
          = (\<Sum>m = 0..<d. if m = \<sigma> k then (1::complex) else 0)"
        by (rule sum.cong, simp_all add: pw)
      also have "\<dots> = 1"
        using \<sigma>_bound[OF k] by simp
      finally show ?thesis using True by simp
    next
      case False
      have pw: "(if m = \<sigma> k then (1::complex) else 0) * (if m = \<sigma> l then 1 else 0) = 0" for m
        using False by auto
      with False show ?thesis by simp
    qed
    also have "\<dots> = (1\<^sub>m d) $$ (k, l)"
    proof (cases "k = l")
      case True
      then show ?thesis using k l by simp
    next
      case False
      have "\<sigma> k \<noteq> \<sigma> l"
      proof
        assume "\<sigma> k = \<sigma> l"
        then have "\<sigma> (\<sigma> k) = \<sigma> (\<sigma> l)" by simp
        with \<sigma>_invol[OF k] \<sigma>_invol[OF l] have "k = l"
          by argo 
        with False show False by simp
      qed
      with False show ?thesis using k l by simp
    qed
    finally show "(U * U) $$ (k, l) = (1\<^sub>m d) $$ (k, l)".
  qed

  have U_unitary: "unitary U"
    unfolding unitary_def
    using U_dagger U_sq U_dr U_dc by simp

  \<comment> \<open>Action on tensor-product basis vectors.\<close>
  have U_acts: "\<And>J i. J < d0 \<Longrightarrow> i < 2 \<Longrightarrow>
     U *\<^sub>v tensor_vec (unit_vec d0 J) (unit_vec 2 i) =
     tensor_vec (unit_vec d0 J) (unit_vec 2 ((i + f J) mod 2))"
  proof -
    fix J i :: nat
    assume J: "J < d0" and i: "i < 2"

    let ?v = "tensor_vec (unit_vec d0 J) (unit_vec 2 i)"
    let ?i1 = "(i + f J) mod 2"
    let ?w = "tensor_vec (unit_vec d0 J) (unit_vec 2 ?i1)"

    have i1_lt: "?i1 < 2" by simp
    have idx_lt: "J * 2 + i < d" 
      using J i d_eq by simp

    have idx1_lt: "J * 2 + ?i1 < d" 
      using J i1_lt d_eq by simp


    have v_dim: "dim_vec ?v = d"
      using tensor_vec_dim d_eq by simp
    have w_dim: "dim_vec ?w = d"
      using tensor_vec_dim d_eq by simp

    \<comment> \<open>Entries of \<open>?v\<close>: 1 at index \<open>J * 2 + i\<close>, 0 elsewhere.\<close>
    have v_entry: "\<And>k. k < d \<Longrightarrow> ?v $ k = (if k = J * 2 + i then 1 else 0)"
    proof -
      fix k assume k: "k < d"
      have "?v $ k = unit_vec d0 J $ (k div 2) * unit_vec 2 i $ (k mod 2)"
        using tensor_vec_index[of "unit_vec d0 J" d0 "unit_vec 2 i" 2 k] k d_eq
        by simp
      also have "\<dots> = (if k div 2 = J then 1 else 0) * (if k mod 2 = i then 1 else 0)"
        using J i d_eq k by auto 
      also have "\<dots> = (if k div 2 = J \<and> k mod 2 = i then 1 else 0)" by auto
      also have "\<dots> = (if k = J * 2 + i then 1 else 0)"
        using i by (auto simp: mult.commute)
      finally show "?v $ k = (if k = J * 2 + i then 1 else 0)".
    qed

    have w_entry: "\<And>k. k < d \<Longrightarrow> ?w $ k = (if k = J * 2 + ?i1 then 1 else 0)"
    proof -
      fix k assume k: "k < d"
      have "?w $ k = unit_vec d0 J $ (k div 2) * unit_vec 2 ?i1 $ (k mod 2)"
        using tensor_vec_index[of "unit_vec d0 J" d0 "unit_vec 2 ?i1" 2 k] k d_eq by simp
      also have "\<dots> = (if k div 2 = J then 1 else 0) * (if k mod 2 = ?i1 then 1 else 0)"
        using J i1_lt d_eq k by auto
      also have "\<dots> = (if k div 2 = J \<and> k mod 2 = ?i1 then 1 else 0)" 
        by auto
      also have "\<dots> = (if k = J * 2 + ?i1 then 1 else 0)"
        using i1_lt by (auto simp: mult.commute, metis mult_div_mod_eq)
      finally show "?w $ k = (if k = J * 2 + ?i1 then 1 else 0)".
    qed

    \<comment> \<open>\<open>\<sigma> (J * 2 + i) = J * 2 + ?i1\<close>.\<close>
    have \<sigma>_at: "\<sigma> (J * 2 + i) = J * 2 + ?i1"
      unfolding \<sigma>_def using i by simp

    \<comment> \<open>Show equality entry-by-entry.\<close>
    show "U *\<^sub>v ?v = ?w"
    proof (rule eq_vecI)
      show "dim_vec (U *\<^sub>v ?v) = dim_vec ?w"
        using U_dr U_dc v_dim w_dim by simp
    next
      fix k assume "k < dim_vec ?w"
      then have k: "k < d" using w_dim by simp
      have "(U *\<^sub>v ?v) $ k = (\<Sum>m = 0..<d. U $$ (k, m) * ?v $ m)"
        using k U_dr U_dc v_dim
        by (simp add: mult_mat_vec_def scalar_prod_def)
      also have "\<dots> = (\<Sum>m = 0..<d.
            (if m = \<sigma> k then (1::complex) else 0) *
            (if m = J * 2 + i then 1 else 0))"
        using U_row[OF k] v_entry
        by (intro sum.cong refl, simp)
      also have "\<dots> = (if \<sigma> k = J * 2 + i then 1 else 0)"
      proof (cases "\<sigma> k = J * 2 + i")
        case True
        hence pw: "(if m = \<sigma> k then (1::complex) else 0) *
                    (if m = J * 2 + i then 1 else 0)
                  = (if m = \<sigma> k then 1 else 0)" for m
          by simp
        have "(\<Sum>m = 0..<d.
               (if m = \<sigma> k then (1::complex) else 0) *
               (if m = J * 2 + i then 1 else 0))
            = (\<Sum>m = 0..<d. if m = \<sigma> k then (1::complex) else 0)"
          by (rule sum.cong) (simp_all add: pw)
        also have "\<dots> = 1"
          using \<sigma>_bound[OF k] by simp
        finally show ?thesis using True by simp
      next
        case False
        hence "(if m = \<sigma> k then (1::complex) else 0) * (if m = J * 2 + i then 1 else 0) = 0" for m
          by auto
        thus ?thesis 
          using False by simp
      qed
      also have "\<dots> = (if k = J * 2 + ?i1 then 1 else 0)"
      proof (cases "\<sigma> k = J * 2 + i")
        case True
        hence "k = \<sigma> (J * 2 + i)" using \<sigma>_invol[OF k] by (metis)
        also have "\<dots> = J * 2 + ?i1" using \<sigma>_at.
        finally have "k = J * 2 + ?i1".
        with True show ?thesis by simp
      next
        case False
        moreover have "k \<noteq> J * 2 + ?i1"
        proof
          assume kk: "k = J * 2 + ?i1"
          have "\<sigma> k = \<sigma> (J * 2 + ?i1)" using kk by simp
          also have "\<dots> = J * 2 + i"
          proof -
            have "\<sigma> (J * 2 + ?i1) = \<sigma> (\<sigma> (J * 2 + i))"
              using \<sigma>_at by simp
            also have "\<dots> = J * 2 + i"
              using \<sigma>_invol[OF idx_lt].
            finally show ?thesis.
          qed
          finally have "\<sigma> k = J * 2 + i".
          thus False using False by simp
        qed
        ultimately show ?thesis by simp
      qed
      also have "\<dots> = ?w $ k"
        using w_entry[OF k] by simp
      finally show "(U *\<^sub>v ?v) $ k = ?w $ k".
    qed
  qed

  show "oracle_unitary f N"
    unfolding oracle_unitary_def
    using U_carr U_unitary U_acts d_eq d_pos
    by (metis d0_def d_def) 
qed

text \<open>$M=\#\{J<2^N : f(J)=0\}$, the quantity estimated by the counting experiment.\<close>

definition count_zeros :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "count_zeros f N \<equiv> card {J. J < 2^N \<and> f J = 0}"

end
