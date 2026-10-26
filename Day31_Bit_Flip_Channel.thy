(*  Title:   Day31_Bit_Flip_Channel.thy
    Author:  Dustin Bryant, after Vern Paulsen's lecture of 11 November 2011 (Day 31)
*)

theory Day31_Bit_Flip_Channel
  imports Day30_Error_Probabilities
begin

section \<open>Day 31 (11 November 2011): the bit-flip code as a channel; fidelity\<close>

text \<open>Encoding $\tilde\psi=a\ket{000}+b\ket{111}$ and flipping each qubit independently with
probability $p$ gives the error map
$E(Y)=(1-p)^3Y+p(1-p)^2\sum_j(X_j)Y(X_j)^*+\cdots+p^3(X\otimes X\otimes X)Y(X\otimes X\otimes X)^*$,
and with the recovery $R$ of Day 30,
\[ R\circ E(Y)=\bigl((1-p)^3+3p(1-p)^2\bigr)Y+\bigl(3p^2(1-p)+p^3\bigr)(X\otimes X\otimes X)Y(X\otimes X\otimes X). \]
The code helps iff $(1-p)^3+3p(1-p)^2\ge1-p$ iff $p\le\tfrac12$ (theory Day31\_Code\_Fidelity, where the formula for $R\circ E$ holds for $Y$ supported on
the code space).
Below: the encoding isometry.\<close>

definition encode_mat :: "complex Matrix.mat" where
  "encode_mat \<equiv> Matrix.mat 8 2 (\<lambda>(i,j).
     if i = 0 \<and> j = 0 then 1
     else if i = 7 \<and> j = 1 then 1
     else 0)"

lemma encode_mat_carrier [simp]: "encode_mat \<in> carrier_mat 8 2"
  by (auto simp: encode_mat_def)

subsection \<open>Fidelity\<close>

text \<open>A state $\psi$ perturbed to $\psi'=a\psi+b\psi^\perp$ is close to $\psi$ when $|a|$ is
close to $1$, so the \emph{fidelity} of states is $F=|\braket{\psi'}\psi|$; for the density
matrices $\rho=\ketbra\psi\psi$, $\rho'=\ketbra{\psi'}{\psi'}$ one has
$\langle\rho|\rho'\rangle=\Tr(\rho\rho')=|\braket{\psi'}\psi|^2$, so $F=\sqrt{\Tr(\rho\rho')}$.
Error correction is compared by $F=\sqrt{\braket\psi{R\circ E(\ketbra\psi\psi)\psi}}$, minimised
or averaged over $\psi$: doing nothing gives $\min F=\sqrt{1-p}$, the bit-flip code gives
$\min F=\sqrt{(1-p)^3+3p(1-p)^2}$ (theory Day31\_Code\_Fidelity).  Formally
\<open>fidelity \<psi> \<rho>\<close> is $\sqrt{\Re\braket\psi{\rho\psi}}$.\<close>

definition fidelity ::
  "complex Matrix.vec \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where
  "fidelity \<psi> \<rho> \<equiv> sqrt (Re (\<langle>\<psi> | \<rho> *\<^sub>v \<psi>\<rangle>))"

lemma fidelity_def_eq:
  "fidelity \<psi> \<rho> = sqrt (Re (\<langle>\<psi> | \<rho> *\<^sub>v \<psi>\<rangle>))"
  by (simp add: fidelity_def)


lemma fidelity_pure_states:
  fixes \<psi> \<psi>' :: "complex Matrix.vec"
  assumes \<psi>_qs:  "quantum_state n \<psi>"
      and \<psi>'_qs: "quantum_state n \<psi>'"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>))
           = cmod (\<langle>\<psi> | \<psi>'\<rangle>)"
proof -
  let ?\<rho> = "(mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>)"
  have \<psi>_dim: "dim_vec \<psi> = n" using \<psi>_qs by (simp add: quantum_state_def)
  have \<psi>'_dim: "dim_vec \<psi>' = n" using \<psi>'_qs by (simp add: quantum_state_def)

  have rho_eq: "?\<rho> = outer_sum n [\<psi>']"
    by (simp add: outer_sum_def)

  (* ?\<rho> *_v \<psi> = \<langle>\<psi>'|\<psi>\<rangle> \<cdot>\<^sub>v \<psi>' *)
  have \<rho>\<psi>: "?\<rho> *\<^sub>v \<psi> = \<langle>\<psi>' | \<psi>\<rangle> \<cdot>\<^sub>v \<psi>'"
    using outer_sum_singleton_mult_vec[OF \<psi>'_dim \<psi>_dim] rho_eq by simp

  (* \<langle>\<psi> | ?\<rho> *_v \<psi>\<rangle> = \<langle>\<psi>|\<psi>'\<rangle> * \<langle>\<psi>'|\<psi>\<rangle> = (cmod \<langle>\<psi>|\<psi>'\<rangle>)^2 *)
  have inner_eq: "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<psi>'\<rangle> * \<langle>\<psi>' | \<psi>\<rangle>"
  proof -
    have "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<langle>\<psi>'|\<psi>\<rangle> \<cdot>\<^sub>v \<psi>'\<rangle>"
      using \<rho>\<psi> by simp
    also have "\<dots> = \<langle>\<psi>'|\<psi>\<rangle> * \<langle>\<psi> | \<psi>'\<rangle>"
      by (rule inner_prod_right_smult')
    finally show ?thesis by (simp add: mult.commute)
  qed

  have conj_swap: "\<langle>\<psi>' | \<psi>\<rangle> = cnj (\<langle>\<psi> | \<psi>'\<rangle>)"
    by (metis \<psi>_dim \<psi>'_dim inner_prod_cnj)

  have sq_real:
    "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = complex_of_real ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
  proof -
    have "\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi> | \<psi>'\<rangle> * cnj (\<langle>\<psi> | \<psi>'\<rangle>)"
      using inner_eq conj_swap by simp
    also have "\<dots> = complex_of_real ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
      by (simp add: complex_norm_square mult.commute, metis complex_norm_square of_real_power)
    finally show ?thesis.
  qed

  have re_eq: "Re (\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle>) = (cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2"
    using sq_real by simp

  have nn: "0 \<le> cmod (\<langle>\<psi> | \<psi>'\<rangle>)" by simp

  have "fidelity \<psi> ?\<rho> = sqrt (Re (\<langle>\<psi> | ?\<rho> *\<^sub>v \<psi>\<rangle>))"
    by (simp add: fidelity_def)
  also have "\<dots> = sqrt ((cmod (\<langle>\<psi> | \<psi>'\<rangle>))\<^sup>2)"
    using re_eq by simp
  also have "\<dots> = cmod (\<langle>\<psi> | \<psi>'\<rangle>)"
    using nn by simp
  finally show ?thesis.
qed


lemma fidelity_self:
  fixes \<psi> :: "complex Matrix.vec"
  assumes \<psi>_qs: "quantum_state n \<psi>"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>]) * ((mat_of_cols n [\<psi>])\<^sup>\<dagger>)) = 1"
proof -
  have norm1: "\<parallel>\<psi>\<parallel> = 1"
    using \<psi>_qs by (simp add: quantum_state_def)
  have "fidelity \<psi> ((mat_of_cols n [\<psi>]) * ((mat_of_cols n [\<psi>])\<^sup>\<dagger>))
          = cmod (\<langle>\<psi> | \<psi>\<rangle>)"
    using fidelity_pure_states[OF \<psi>_qs \<psi>_qs] .
  also have "\<dots> = cmod (complex_of_real ((\<parallel>\<psi>\<parallel>)\<^sup>2))"
    by (metis cpx_vec_length_inner_prod)
  also have "\<dots> = cmod (complex_of_real (1\<^sup>2))"
    using norm1 by simp
  also have "\<dots> = 1"
    by simp
  finally show ?thesis .
qed


lemma fidelity_orthogonal:
  fixes \<psi> \<psi>' :: "complex Matrix.vec"
  assumes \<psi>_qs:  "quantum_state n \<psi>"
      and \<psi>'_qs: "quantum_state n \<psi>'"
      and ortho: "\<langle>\<psi> | \<psi>'\<rangle> = 0"
  shows "fidelity \<psi> ((mat_of_cols n [\<psi>']) * ((mat_of_cols n [\<psi>'])\<^sup>\<dagger>)) = 0"
  using fidelity_pure_states[OF \<psi>_qs \<psi>'_qs] ortho by simp

end
