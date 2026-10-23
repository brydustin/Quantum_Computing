# Three AFP submissions

Prepared from the repository https://github.com/brydustin/Quantum_Computing by
`tools/afp_package.sh`: each entry was exported from the tracked sources and built from the
export alone (fresh build, Isabelle2025-2, AFP 2026-04-09, `-o document=pdf`), with no `sorry`
and no oracles except the one noted for HHL_Algorithm_Search.

| Folder | Entry | Depends on (new) | Contents |
|---|---|---|---|
| `1_Hermitian_Functional_Calculus` | Hermitian_Functional_Calculus | – | functional calculus of Hermitian matrices, Lie–Trotter and Suzuki product formulas |
| `2_Quantum_Computing_by_VP` | Quantum_Computing_by_VP | – | Vern Paulsen's 2011 lecture notes on quantum computing and completely positive maps |
| `3_HHL_Algorithm` | HHL_Algorithm | entries 1 and 2 | quantum phase estimation and the HHL algorithm |

Each folder holds the archive to upload (`<Entry>.tar.gz`), the same entry unpacked, the PDF of
every session with a document (the AFP's full variant, with proofs: 70, 603 and 390 pages for the
three main sessions), and `SUBMISSION.md` with the fields of the submission form
(title, short name, topics, license, abstract) and a comment for the editors.

Submitting: https://isa-afp.org/submission/ — entries 1 and 2 are independent and can go first
(or together with 3); entry 3 needs both, so mention in its comment that they were submitted at
the same time.  Before submitting, decide the open points:

- entry 2 is fixed: short name `Quantum_Computing_by_VP`, title "Lectures on Quantum Computing and
  Completely Positive Maps"; the names and titles of entries 1 and 3 are suggestions;
- ask Vern Paulsen whether he agrees with an entry built on, and named after, his notes;
- the topics are suggestions from the AFP's topic list;
- the license is BSD in all three (the AFP's default; LGPL is the other option).
