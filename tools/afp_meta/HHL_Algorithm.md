# AFP submission: HHL_Algorithm

Fields of the submission form at https://isa-afp.org/submission/

- **Title:** Quantum Phase Estimation and the HHL Algorithm
- **Short name:** HHL_Algorithm
- **Author:** Dustin Bryant (brydustin@gmail.com)
- **Topics (suggested):** Computer science/Algorithms/Quantum computing; Computer science/Programming languages/Logics; Mathematics/Physics/Quantum information
- **License:** BSD
- **Archive:** `HHL_Algorithm.tar.gz` (the folder `HHL_Algorithm/`)
- **Depends on (AFP):** Hermitian_Functional_Calculus and Quantum_Computing_CP_Maps (submitted at the
  same time), QHLProver, Isabelle_Marries_Dirac, Jordan_Normal_Form, Quantum_Fourier_Transform;
  for the extra sessions Real_Impl (HHL_Algorithm_Demo) and Compressed_Oracles (HHL_Algorithm_Search)

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
and compiled to elementary gates. Extra sessions run the circuit on a $2\times2$ example with
exact arithmetic in $\mathbb{Q}(\sqrt2)$, show that loop-free programs denote completely positive
trace-preserving maps, import the quantum search lower bound behind the optimality theorem
from Compressed_Oracles, and compile the black boxes to elementary gates: a reversible comparator
gives the sparse simulation from oracles, state preparation is built from an angle oracle and,
without oracles, for sparse right-hand sides, and for the shifted cycle Laplacian the whole
algorithm runs on polynomially many elementary gates with an explicit count.

## Comment for the editors

- Builds with Isabelle2025-2 and the AFP of 2026-04-09; no `sorry`. The only oracle is
  Types_To_Sets' `cancel_type_definition`, inherited in session HHL_Algorithm_Search from
  Compressed_Oracles' search bound.
- Depends on the entries Hermitian_Functional_Calculus and Quantum_Computing_CP_Maps, submitted at the
  same time; please review those first.
- Sessions: HHL_Algorithm (main, with document), HHL_Algorithm_Demo (needs Real_Impl, which
  replaces the code setup of the reals), HHL_Algorithm_Channels (loads the notes' channel
  theory), HHL_Algorithm_Search (needs Compressed_Oracles, built on Complex_Bounded_Operators),
  HHL_Algorithm_Gates (the black boxes in elementary gates; about 5 minutes).
- Names: the entry uses QHLProver's `hermitian` (as Hermitian_Functional_Calculus does) and the
  notes'/IMD's `unitary`, inner and outer products; the first theory hides QHLProver's clashing
  names and bridges the notes' `hermitian` (`hermitian_notes`).
