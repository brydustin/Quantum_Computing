# AFP submission: Quantum_Computing_by_VP

Fields of the submission form at https://isa-afp.org/submission/

- **Title:** Lectures on Quantum Computing and Completely Positive Maps
- **Short name:** Quantum_Computing_by_VP
- **Author:** Dustin Bryant (brydustin@gmail.com)
- **Topics (suggested):** Mathematics/Physics/Quantum information; Computer science/Algorithms/Quantum computing; Mathematics/Algebra
- **License:** BSD
- **Archive:** `Quantum_Computing_by_VP.tar.gz` (the folder `Quantum_Computing_by_VP/`)
- **Depends on (AFP):** Isabelle_Marries_Dirac, Jordan_Normal_Form, Quantum_Fourier_Transform,
  Two_Hermitian_Results (session Quantum_Computing_by_VP_Day05 only); Isabelle: HOL-Analysis, HOL-Hahn_Banach

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
statements; a separate session (Day 5) imports the leading principal minors test from Two_Hermitian_Results.

## Comment for the editors

- Builds with Isabelle2025-2 and the AFP of 2026-04-09; no `sorry`, no oracles.
- Sessions: Quantum_Computing_by_VP (every lecture, one theory per lecture, and the document),
  Quantum_Computing_by_VP_Day05 (directory `Leading_Minors/`; Day 5: the leading principal minors test from Two_Hermitian_Results, kept
  apart because that entry loads HOL-Probability).
- The notes are by Vern Paulsen (notes taken by Brandon Lee); they are cited, not reproduced:
  the document paraphrases each definition and theorem before its formal statement.
  **Please confirm with Vern Paulsen before submitting** that he is happy with an entry named
  after him and his notes.
- The entry HHL_Algorithm (submitted at the same time) builds on it.
