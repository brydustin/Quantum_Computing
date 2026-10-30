# AFP submissions

Prepared from the repository https://github.com/brydustin/Quantum_Computing by
`tools/afp_package.sh`: each entry was exported from the tracked sources and built from the
export alone (Isabelle2026, AFP 2026-10-29, `-o document=pdf`), with no `sorry` and no oracles
except the one noted for Quantum_Search_Bound.

| Folder | Entry | Status | Sessions |
|---|---|---|---|
| `1_Hermitian_Functional_Calculus` | Hermitian_Functional_Calculus | submitted 2026-10-24, under review; builds unchanged with Isabelle2026 | 1 |
| `2_Quantum_Computing_CP_Maps` | Quantum_Computing_CP_Maps | to submit | Matrix_Analysis_Prerequisites, Quantum_Computing_CP_Maps, Kraus_Maps_Bridge |
| `3_HHL_Algorithm` | HHL_Algorithm | to submit (needs entries 1 and 2) | HHL_Algorithm, HHL_Explicit_Demo, Quantum_Search_Bound |

Each folder holds the archive to upload (`<Entry>.tar.gz`), the same entry unpacked, the PDF of
every session (the AFP's full variant, with proofs), and `SUBMISSION.md` with the fields of the
submission form (title, short name, topics, license, abstract) and the comment for the editors.

Submitting entries 2 and 3 at https://isa-afp.org/submission/ — one form per entry, entry 2
first; copy each field from its `SUBMISSION.md` and upload its `.tar.gz`.  The license is BSD
(the AFP's default); the topics are suggestions from the AFP's topic list.
