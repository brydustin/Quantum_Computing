theory Nonemptiness_Array_Factor
  imports "HOL-Analysis.Analysis"
begin

section \<open>The Array Factor and Power Pattern\<close>

text \<open>
  This theory develops the concrete radiation-pattern functions from
  \<open>Applied Math/nonemptiness_unified_singlefile_complete.tex\<close> and the elementary
  odd-\<open>N\<close> geometry that makes the whole nonemptiness argument work.

  No locales are used: every object is a plain definition, and every lemma is a
  genuine statement about those definitions. The mathematical heart recorded here
  is Lemma \<open>lem:Azero-surj\<close>: writing \<open>z\<^sub>n = e\<^sup>-\<^sup>i\<^sup>c\<^sup>\<cdot>\<^sup>p\<^sup>n\<close> (each of unit modulus), if the
  array factor vanishes and \<open>N\<close> is odd then the \<open>z\<^sub>n\<close> cannot all be real-collinear,
  because a real-collinear family would give \<open>z\<^sub>n = \<epsilon>\<^sub>n e\<^sup>i\<^sup>\<xi>\<close> with \<open>\<epsilon>\<^sub>n = \<plusminus>1\<close> and then
  \<open>\<Sum> \<epsilon>\<^sub>n = 0\<close>, impossible for an odd number of \<open>\<plusminus>1\<close>s.
\<close>

type_synonym planar_point = "real^2"
type_synonym angle_point = "real^2"
type_synonym raw_configuration = "planar_point list"

definition array_factor ::
  "(angle_point \<Rightarrow> planar_point) \<Rightarrow> raw_configuration \<Rightarrow> angle_point \<Rightarrow> complex"
where
  "array_factor cvec ps \<omega> =
     sum_list (map (\<lambda>p. cis (-(cvec \<omega> \<bullet> p))) ps)"

definition power_pattern ::
  "(angle_point \<Rightarrow> planar_point) \<Rightarrow> (angle_point \<Rightarrow> real) \<Rightarrow>
  raw_configuration \<Rightarrow> angle_point \<Rightarrow> real"
where
  "power_pattern cvec g ps \<omega> =
     g \<omega> * (cmod (array_factor cvec ps \<omega>))\<^sup>2"


subsection \<open>Elementary algebra of the array factor\<close>

lemma array_factor_Nil [simp]:
  "array_factor cvec [] \<omega> = 0"
  by (simp add: array_factor_def)

lemma array_factor_Cons:
  "array_factor cvec (p # ps) \<omega> =
     cis (-(cvec \<omega> \<bullet> p)) + array_factor cvec ps \<omega>"
  by (simp add: array_factor_def)

lemma array_factor_append:
  "array_factor cvec (ps @ qs) \<omega> =
     array_factor cvec ps \<omega> + array_factor cvec qs \<omega>"
  by (simp add: array_factor_def)

lemma cmod_array_factor_le:
  "cmod (array_factor cvec ps \<omega>) \<le> real (length ps)"
proof (induction ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  have "cmod (array_factor cvec (p # ps) \<omega>)
          = cmod (cis (-(cvec \<omega> \<bullet> p)) + array_factor cvec ps \<omega>)"
    by (simp add: array_factor_Cons)
  also have "\<dots> \<le> cmod (cis (-(cvec \<omega> \<bullet> p))) + cmod (array_factor cvec ps \<omega>)"
    by (rule norm_triangle_ineq)
  also have "\<dots> = 1 + cmod (array_factor cvec ps \<omega>)"
    by (simp add: norm_cis)
  also have "\<dots> \<le> 1 + real (length ps)"
    using Cons.IH by simp
  finally show ?case by simp
qed

lemma power_pattern_nonneg:
  assumes "0 \<le> g \<omega>"
  shows "0 \<le> power_pattern cvec g ps \<omega>"
  using assms by (simp add: power_pattern_def)


section \<open>Odd-\<open>N\<close> Geometry of the Zeros\<close>

text \<open>
  The combinatorial nucleus: a sum of an odd number of \<open>\<plusminus>1\<close>s is odd, hence nonzero.
\<close>

lemma sum_pm_one_parity:
  fixes \<epsilon> :: "nat \<Rightarrow> int"
  assumes "\<And>n. n < N \<Longrightarrow> \<epsilon> n \<in> {-1, 1}"
  shows "odd (\<Sum>n<N. \<epsilon> n) = odd N"
  using assms
proof (induction N)
  case 0
  show ?case by simp
next
  case (Suc N)
  have hIH: "odd (\<Sum>n<N. \<epsilon> n) = odd N"
    using Suc.IH Suc.prems by simp
  have h\<epsilon>: "odd (\<epsilon> N)"
    using Suc.prems[of N] by auto
  have "(\<Sum>n<Suc N. \<epsilon> n) = (\<Sum>n<N. \<epsilon> n) + \<epsilon> N"
    by simp
  then show ?case
    using hIH h\<epsilon> by (simp add: even_add)
qed

lemma sum_pm_one_odd_nonzero:
  fixes \<epsilon> :: "nat \<Rightarrow> int"
  assumes "odd N" and "\<And>n. n < N \<Longrightarrow> \<epsilon> n \<in> {-1, 1}"
  shows "(\<Sum>n<N. \<epsilon> n) \<noteq> 0"
proof -
  have "odd (\<Sum>n<N. \<epsilon> n)"
    using sum_pm_one_parity[OF assms(2)] assms(1) by simp
  then show ?thesis by force
qed

text \<open>
  A real-collinear family of unit-modulus terms sums to an integer multiple of the
  common direction, with that integer's parity equal to the number of terms.
\<close>

lemma sum_list_collinear_units:
  fixes ps :: "'a list" and f :: "'a \<Rightarrow> complex" and u :: complex
  assumes "u \<noteq> 0"
    and "\<And>p. p \<in> set ps \<Longrightarrow> \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> f p = of_int \<epsilon> * u"
  shows "\<exists>m::int. sum_list (map f ps) = of_int m * u \<and> odd m = odd (length ps)"
  using assms
proof (induction ps)
  case Nil
  show ?case by (intro exI[of _ 0]) simp
next
  case (Cons p ps)
  obtain \<epsilon> :: int where h\<epsilon>: "\<epsilon> \<in> {-1, 1}" "f p = of_int \<epsilon> * u"
    using Cons.prems(2)[of p] by auto
  obtain m :: int where hm: "sum_list (map f ps) = of_int m * u" "odd m = odd (length ps)"
    using Cons.IH Cons.prems by auto
  have "sum_list (map f (p # ps)) = of_int (\<epsilon> + m) * u"
    using h\<epsilon> hm by (simp add: of_int_add ring_distribs)
  moreover have "odd (\<epsilon> + m) = odd (length (p # ps))"
    using h\<epsilon> hm by (auto simp: even_add)
  ultimately show ?case by blast
qed

lemma sum_list_collinear_units_odd_nonzero:
  fixes ps :: "'a list" and f :: "'a \<Rightarrow> complex" and u :: complex
  assumes "odd (length ps)" and "u \<noteq> 0"
    and "\<And>p. p \<in> set ps \<Longrightarrow> \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> f p = of_int \<epsilon> * u"
  shows "sum_list (map f ps) \<noteq> 0"
proof -
  have "\<exists>m::int. sum_list (map f ps) = of_int m * u \<and> odd m = odd (length ps)"
    by (rule sum_list_collinear_units[OF assms(2)]) (use assms(3) in blast)
  then obtain m :: int where hm:
      "sum_list (map f ps) = of_int m * u" "odd m = odd (length ps)"
    by blast
  from hm assms(1) have "m \<noteq> 0" by auto
  with hm assms(2) show ?thesis by simp
qed

text \<open>
  Lemma \<open>lem:Azero-surj\<close> (geometric core). When \<open>N\<close> is odd and the array factor
  vanishes, the unit-modulus summands \<open>cis(-(cvec \<omega> \<cdot> p))\<close> cannot all lie on a common
  real line through the origin. Equivalently, their real span is two-dimensional, so
  the partial differential \<open>D\<^sub>x A\<close> (which equals \<open>-\<i>\<close> times that span) is onto \<open>\<complex>\<close>.
\<close>

theorem array_factor_zero_odd_not_collinear:
  assumes "odd (length ps)"
    and "array_factor cvec ps \<omega> = 0"
  shows "\<not> (\<exists>u. u \<noteq> 0 \<and>
              (\<forall>p\<in>set ps. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (-(cvec \<omega> \<bullet> p)) = of_int \<epsilon> * u))"
proof
  assume "\<exists>u. u \<noteq> 0 \<and>
            (\<forall>p\<in>set ps. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (-(cvec \<omega> \<bullet> p)) = of_int \<epsilon> * u)"
  then obtain u where hu: "u \<noteq> 0"
    and hcol: "\<And>p. p \<in> set ps \<Longrightarrow>
                 \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (-(cvec \<omega> \<bullet> p)) = of_int \<epsilon> * u"
    by blast
  have "sum_list (map (\<lambda>p. cis (-(cvec \<omega> \<bullet> p))) ps) \<noteq> 0"
    by (rule sum_list_collinear_units_odd_nonzero[OF assms(1) hu]) (use hcol in blast)
  then show False
    using assms(2) by (simp add: array_factor_def)
qed

end
