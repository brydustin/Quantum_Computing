# PLanQC 2027 submission

- Site: https://planqc27.hotcrp.com
- Deadline: Fri 30 Oct 2026, end of day AoE (Sat 31 Oct, 7:00 am CDT)
- Format: 2–5 page abstract, single-column 11pt acmsmall, references not counted. No proceedings.
- File: `planqc.pdf` (body 5 pages, references on page 6)
- Build: `TEXINPUTS=.:../paper_hhl: pdflatex planqc && bibtex planqc && pdflatex planqc && pdflatex planqc`

## Title

HHL, Verified to the Gate: Quantum Hoare Logic at Algorithm Scale in Isabelle/HOL, Written with an AI Agent

## Author

Dustin Bryant, Independent researcher, USA

## Abstract (plain text for the form)

HHL prepares a quantum state proportional to the solution of a linear system. Earlier mechanised
proofs cover its exact case and treat its subroutines as black boxes. We verify HHL in Isabelle/HOL,
from the spectral theorem through quantum Hoare logic down to circuits of one- and two-qubit gates.
Four small rules make the logic work at algorithm scale. In the exact case the repeat-until-success
program is totally correct, and its number of rounds is geometric with mean 1/p. Beyond the exact
case, the paper's error analysis holds with explicit constants, and for the shifted cycle Laplacian the whole algorithm, oracles included, is a
verified gate list with a closed-form count. Seven statements of the original paper are false. An AI
agent wrote almost all of the 64,000 lines, directed by one mathematician.

## Notes

- Isabelle sources on Zenodo: https://doi.org/10.5281/zenodo.23812498 (cited in the title note).
  The record must be published before submitting, or the link will not resolve.
