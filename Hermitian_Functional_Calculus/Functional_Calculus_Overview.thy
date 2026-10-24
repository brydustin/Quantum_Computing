(*  Title:   Functional_Calculus_Overview.thy
    Author:  Dustin Bryant
*)

theory Functional_Calculus_Overview
  imports
    Hermitian_Functional_Calculus
    Matrix_Sums
    Trotter_Product_Formula
    Suzuki_Order
    Suzuki_Error
begin

section \<open>Overview\<close>

text \<open>
\begin{center}
\begin{tabular}{lp{0.62\linewidth}}
\textbf{Theory} & \textbf{Contents}\\\hline
\texttt{Hermitian\_Functional\_Calculus} & $g(A)$ for Hermitian $A$ (\<open>mat_fun_eigen\<close>,
  \<open>mat_fun_decomp\<close>), $g(A)h(A)=(gh)(A)$ (\<open>mat_fun_mult\<close>), $g(A)^*=\bar g(A)$
  (\<open>mat_fun_dagger\<close>), unitarity (\<open>mat_fun_unitary\<close>), the inverse (\<open>herm_inv\<close>)\\
\texttt{Matrix\_Sums} & finite sums of matrices\\
\texttt{Trotter\_Product\_Formula} & the Lie--Trotter formula with error bound (\<open>trotter\<close>)\\
\texttt{Suzuki\_Order} & Suzuki's recursion and its order conditions (\<open>suzuki_order\<close>)\\
\texttt{Suzuki\_Error} & the error of a product formula (\<open>sprod_approx\<close>, \<open>suzuki_error\<close>)
\end{tabular}
\end{center}
\<close>

end
