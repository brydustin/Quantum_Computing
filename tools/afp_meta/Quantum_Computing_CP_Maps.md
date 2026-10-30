# AFP submission: Quantum_Computing_CP_Maps

Fields of the submission form at https://isa-afp.org/submission/

- **Title:** Lectures on Quantum Computing and Completely Positive Maps
- **Short name:** Quantum_Computing_CP_Maps
- **Author:** Dustin Bryant (brydustin@gmail.com)
- **Topics (suggested):** Mathematics/Physics/Quantum information; Computer science/Algorithms/Quantum computing; Mathematics/Algebra
- **License:** BSD
- **Archive:** `Quantum_Computing_CP_Maps.tar.gz` (the folder `Quantum_Computing_CP_Maps/`)
- **Depends on (AFP):** Two_Hermitian_Results (parent of the first session), Isabelle_Marries_Dirac,
  Jordan_Normal_Form, Quantum_Fourier_Transform, QHLProver, Kraus_Maps (parent of the third session); Isabelle: HOL-Analysis, HOL-Hahn_Banach

## Abstract

We formalise Vern Paulsen's lecture notes *Lectures on Quantum Computing and Completely Positive
Maps* (University of Houston, Fall 2011), lecture by lecture. The development covers the
mathematics of quantum computing (inner products, unitaries and Householder reflections, Schur's
theorem, the spectral theorem, positive matrices, tensor products, the postulates of quantum
mechanics, measurements and gates), density matrices and partial traces, completely positive
maps (Choi's theorem, Kraus representations and their unitary freedom, the Choi rank, extreme
points of the unital and trace-preserving maps), operator systems and Arveson's extension
theorem (via Hahn–Banach on matrix spaces), separability and entanglement witnesses (the
positive-map criterion, the Horodecki–Peres criterion for two qubits), and quantum error
correction (classical codes, the bit-flip, phase-flip and Shor codes, the Knill–Laflamme
conditions). The document restates the notes' definitions and results before their formal
statements; the leading principal minors test of Day 5 is imported from Two_Hermitian_Results,
and a bridge theory shows that the lectures' basic definitions agree with those of QHLProver and
Isabelle Marries Dirac. A prerequisite session, Matrix Analysis Prerequisites, collects reusable
matrix analysis: unitary and Kronecker-product algebra, and matrices of fixed dimension as a
Euclidean space. A third session, Kraus Maps Bridge, identifies the lectures' Kraus maps with
those of the AFP entry Kraus_Maps: with Choi's theorem, every completely positive map of the
lectures is a Kraus map there, and every completely positive trace-preserving map a
trace-preserving one.

## Comment for the editors

- Builds with Isabelle2026 and the AFP of 2026-10-29; no `sorry`.  No oracles in the first two
  sessions; Kraus_Maps_Bridge inherits Types_To_Sets' `cancel_type_definition` from
  Complex_Bounded_Operators / Kraus_Maps (every theorem there depends on it through the
  trace-class type).
- Three sessions.  Matrix_Analysis_Prerequisites (directory `Matrix_Analysis_Prerequisites/`, own
  document): general matrix lemmas, unitary and Kronecker-product algebra, and matrices of fixed
  dimension with the Hilbert-Schmidt norm as a normed and a Euclidean space, independent of the
  lectures; its parent is Two_Hermitian_Results.  Quantum_Computing_CP_Maps, built on it: every
  lecture, one theory per lecture, and the document; Day 5 imports the leading principal minors
  test of Two_Hermitian_Results.
- Theory Notes_Library_Bridge (after Day 13) proves that the lectures' definitions agree with the
  AFP's: Hermitian, positive semidefinite (QHLProver's `positive`), density matrices
  (`density_operator`), trace, projections, unitaries and the Pauli matrices (IMD).  It is the
  only theory that loads QHLProver, so its names stay out of the lectures.
- Kraus_Maps_Bridge (directory `Kraus_Maps_Bridge/`, own document; parent Kraus_Maps, about 2
  minutes): a list of Kraus matrices as a Kraus family of Unruh's entry; its Kraus map is the
  lectures' (`kf_of_mats_apply`), trace preserving iff the matrices are Kraus operators; every
  CP map of the lectures is a `kraus_map` (`cp_kraus_map`), every CPTP map `km_trace_preserving`.
  A separate session so that the lectures do not load Complex_Bounded_Operators.
- The notes are by Vern Paulsen (notes taken by Brandon Lee); they are cited, not reproduced:
  the document paraphrases each definition and theorem before its formal statement.
- The entry HHL_Algorithm (submitted at the same time) builds on it.
