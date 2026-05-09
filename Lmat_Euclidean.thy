(*
  Title:    Lmat_Euclidean.thy
  Purpose:  Equip the typed-dimension matrix wrapper lmat with the
            HOL-Analysis typeclass tower:
              real_vector \<subseteq> real_normed_vector \<subseteq> real_inner
              \<subseteq> euclidean_space \<subseteq> heine_borel.
            With these instances the AFP/HOL-Analysis library results
            (in particular Caratheodory's theorem and closed-set
            convex-separation theorems) apply directly to matrix
            sequences in (complex, 'm, 'n) lmat.
*)

theory Lmat_Euclidean
  imports
    Matrix_Typed
    "HOL-Analysis.Euclidean_Space"
    "HOL-Analysis.L2_Norm"
begin

text \<open>This theory is a placeholder: it just verifies that
\<^session>\<open>HOL-Analysis\<close> can be loaded on top of \<^session>\<open>HOL-Algebra\<close>
in the current session.  The actual typeclass instances will be
added in subsequent commits.\<close>

end
