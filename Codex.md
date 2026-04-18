# Codex Instructions

## Isabelle Command For This Workspace

For this session, run Isabelle exactly this way:

```bash
~/Desktop/Isabelle/Isabelle2025-2/bin/isabelle jedit -l Quantum_Fourier_Transform
```

This is the command the user uses from the terminal, and it is the command that
works for this workspace. Do not change the session layout, rename sessions,
rewrite `ROOT` files, or substitute a different build command unless the user
explicitly asks for that.

## Current Goal

Build the Vern Paulsen quantum computing formalization on top of
`Quantum_Computing.thy`.

The existing material is a work in progress. Some definitions and proof
statements may be rough, and some facts may still be deferred with `sorry`.
The priority is to make the existing formalization polished, coherent, and
accepted by Isabelle in the `Quantum_Fourier_Transform` session opened by the
jEdit command above.

## Main Theory Stack

Use the existing local theory stack instead of starting a separate development.

- Primary working theory: `Quantum_Computing.thy`
- Supporting local theory: `Basic_Math.thy` / `Basic_Math_session/Basic_Math.thy`
- QFT base session opened in Isabelle: `Quantum_Fourier_Transform`
- Imported quantum infrastructure: the existing `Quantum_Fourier_Transform`,
  `Isabelle_Marries_Dirac`, matrix, vector, tensor, and Jordan normal form
  material already wired into the workspace

When extending the formalization, prefer the definitions and lemmas already
available from this stack. Do not introduce a parallel quantum-computing API
unless the current one is genuinely unusable.

## Formalization Style

The development should remain close to Vern Paulsen's notes while being clean
Isabelle.

- Keep theorem and definition names descriptive and stable.
- Prefer small, reusable definitions over large ad hoc theorem statements.
- Use `sorry` for difficult proofs when the statement and definitions are
  mathematically clear.
- Do not leave syntactically broken placeholders such as malformed
  `definition` commands.
- Avoid adding imports just to bypass a small local proof obligation.
- Add short comments only when they clarify the mathematical intent or explain
  a deferred proof dependency.

## Lists, Vectors, and Matrices

Be consistent about representation choices.

- Use `complex Matrix.vec` for finite-dimensional vectors in the matrix library.
- Use `complex Matrix.mat` for matrices and operators.
- Use lists only for finite enumerations, theorem packaging, or constructors
  that explicitly require lists.
- Convert lists to vectors or matrices at clear boundaries, not throughout a
  proof.
- Avoid mixing list indexing and vector indexing in the same definition unless
  the conversion is part of the definition being formalized.

When a mathematical object is an element of `C^n`, represent it as a
`complex Matrix.vec`. When it is a matrix in `M_n`, represent it as a
`complex Matrix.mat`. This convention should guide new definitions and repairs
to old ones.

## Compilation Standard

Before considering a change complete, make sure the affected theory is accepted
by Isabelle in the session opened with:

```bash
~/Desktop/Isabelle/Isabelle2025-2/bin/isabelle jedit -l Quantum_Fourier_Transform
```

The intended standard is:

- no parse errors
- no type errors
- no malformed definitions
- no accidental shadow API for vectors, matrices, gates, or tensor products
- `sorry` is acceptable only for mathematically sensible, well-typed statements

If batch verification is needed, first ask the user which command they want run.
Do not infer or change the build command independently.

## Source Material

Use the local notes as the mathematical source.

- Primary source: `QC_Notes_overleaf.tex`
- Ground truth for ambiguity: `QC_Notes.pdf`
- Existing formalization: `Quantum_Computing.thy`
- Earlier foundational material: `Basic_Math.thy`

The goal is not just to transcribe statements. Existing definitions should be
made sensible enough that later proofs can be written naturally.

## Working Rules

1. Start by inspecting the relevant existing definitions and lemmas.
2. Build on `Quantum_Computing.thy`; do not fork the development.
3. Keep representations consistent: vectors as `complex vec`, matrices as
   `complex mat`, lists only at explicit constructor boundaries.
4. Repair bad definitions before adding theorems that depend on them.
5. Prefer local lemmas that clarify dimensions and carriers.
6. Keep the theory accepted by Isabelle under the user's jEdit session.
7. Do not alter `ROOT` files, session names, or the Isabelle invocation unless
   explicitly requested.
