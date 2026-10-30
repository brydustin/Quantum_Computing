# AFP submission: HHL_Algorithm

Fields of the submission form at https://isa-afp.org/submission/

- **Title:** Quantum Phase Estimation and the HHL Algorithm
- **Short name:** HHL_Algorithm
- **Author:** Dustin Bryant (brydustin@gmail.com)
- **Topics (suggested):** Computer science/Algorithms/Quantum computing; Computer science/Programming languages/Logics; Mathematics/Physics/Quantum information
- **License:** BSD
- **Archive:** `HHL_Algorithm.tar.gz` (the folder `HHL_Algorithm/`)
- **Depends on (AFP):** Hermitian_Functional_Calculus (submitted 2026-10-24, under review) and
  Quantum_Computing_CP_Maps (submitted at the same time), QHLProver, Isabelle_Marries_Dirac, Jordan_Normal_Form, Quantum_Fourier_Transform;
  for the two extra sessions Real_Impl (HHL_Explicit_Demo) and Compressed_Oracles (Quantum_Search_Bound)

## Abstract

We verify quantum phase estimation and the algorithm of Harrow, Hassidim and Lloyd (HHL) for
solving linear systems $Ax=b$. For phase estimation we prove the exact output state, the
$4/\pi^2$ bound for every phase, the textbook precision bound and the clock size needed for $n$
correct bits, and verify it as a program of quantum Hoare logic. For HHL we prove the output
state and success probability in the exact case, explicit error bounds for every right-hand side
when the eigenvalues are not register values (with the uniform and with the sine-window clock
state), the paper's filter functions, Theorem 1 and the run time, approximate Hamiltonian
simulation (an oracle with error $\eta$ moves the output by at most the number of calls times
$\eta$; sparse matrices simulated by Trotter and Suzuki product formulas), the reduction from
circuits to matrix inversion, rectangular and preconditioned systems, and the optimality
results. The algorithm is a program of the quantum while-language of QHLProver, verified for
partial and total correctness (the repeat-until-success loop terminates with probability one),
and compiled to elementary gates; loop-free programs denote completely positive
trace-preserving maps. The black boxes are compiled too: a reversible comparator gives the
sparse simulation from oracles, state preparation is built from an angle oracle and, without
oracles, for sparse right-hand sides, and for the shifted cycle Laplacian the whole algorithm
runs on polynomially many elementary gates with an explicit count. Two extra sessions run the
circuit on a $2\times2$ example with exact arithmetic in $\mathbb{Q}(\sqrt2)$ and import the
quantum search lower bound behind the optimality theorem from Compressed_Oracles.

## Comment for the editors

- Builds with Isabelle2026 and the AFP of 2026-10-29; no `sorry`. The only oracle is
  Types_To_Sets' `cancel_type_definition`, inherited in session Quantum_Search_Bound from
  Compressed_Oracles' search bound.
- Depends on two entries not yet in the AFP: Hermitian_Functional_Calculus (submitted on
  2026-10-24, under review; it builds unchanged with Isabelle2026) and Quantum_Computing_CP_Maps
  (submitted at the same time as this entry).  Please review those first.
- Sessions: HHL_Algorithm (main, with document; the subdirectories `Channels/` and `Gates/` hold
  the channel theory and the black boxes in elementary gates), HHL_Explicit_Demo (needs
  Real_Impl, which replaces the code setup of the reals), Quantum_Search_Bound (needs
  Compressed_Oracles, built on Complex_Bounded_Operators).
- Names: the entry uses QHLProver's `hermitian` (as Hermitian_Functional_Calculus does) and the
  notes'/IMD's `unitary`, inner and outer products; the first theory hides QHLProver's clashing
  names and bridges the notes' `hermitian` (`hermitian_notes`).
