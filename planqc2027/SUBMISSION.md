# PLanQC 2027 submission

- Site: https://planqc27.hotcrp.com
- Deadline: Fri 30 Oct 2026, end of day AoE (Sat 31 Oct, 7:00 am CDT)
- Format: 2–5 page abstract, single-column 11pt acmsmall, references not counted. No proceedings.
- File: `planqc.pdf` (body 5 pages, references on page 6)
- Build: `TEXINPUTS=.:../paper_hhl: pdflatex planqc && bibtex planqc && pdflatex planqc && pdflatex planqc`

## Title

Gate-Level Verification of HHL with Quantum Hoare Logic in Isabelle/HOL

## Author

Dustin Bryant, Independent researcher, USA

## Abstract (plain text for the form)

The HHL algorithm of Harrow, Hassidim and Lloyd solves a linear system Ax = b on a quantum computer,
in the sense that it prepares a quantum state whose amplitudes are proportional to x. Earlier
machine-checked proofs cover only the idealised case, in which every eigenvalue of A is exactly
representable in the algorithm's finite precision, and they treat its subroutines as black boxes. We
verify HHL in Isabelle/HOL, from the spectral theorem through quantum Hoare logic down to circuits of
elementary one- and two-qubit gates. Four small proof rules make the logic practical for a whole
algorithm. In the idealised case, the program that repeats the circuit until a measurement signals
success is totally correct, and its number of rounds is geometric with mean 1/p, where p is the
probability that a round succeeds. Beyond that case, the original paper's error analysis holds with
explicit constants, and for a concrete family of sparse matrices the whole algorithm, including the
subroutines that access the matrix, becomes a verified list of gates whose number is bounded by an
explicit formula. Along the way we found seven false statements in the original paper. An AI agent
wrote almost all of the 64,000 lines of Isabelle, directed by the author.

## Notes

- Isabelle sources on Zenodo: https://doi.org/10.5281/zenodo.23812498 (cited in the title note).
  The record must be published before submitting, or the link will not resolve.
