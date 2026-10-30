# Review of "The HHL Algorithm, Verified: From Lecture Notes to Elementary Gates in Isabelle/HOL, and How It Was Built"

*Round 1. Written in the role of an experienced CADE programme-committee member. Length is ignored, as requested.*

## Summary

The paper reports a machine-checked verification of the HHL quantum linear-systems algorithm in
Isabelle/HOL. It covers the mathematics: a functional calculus, Trotter/Suzuki product formulas and
phase estimation. It covers the exact algorithm as a matrix identity and the inexact error analysis of
the original paper, with explicit constants. It covers programs in the quantum while-language of
QHLProver, including total correctness of the repeat-until-success loop, and a refinement to
elementary gates; for the shifted cycle Laplacian the gate count is explicit. Seven statements of the
original paper are refuted with formal witnesses. The second half is an experience report: the
development (64k lines, 130 theories) was written by an AI agent directed by one person, with a 147-day
pause, and the paper gives a timeline, statistics from git and agent logs, a hand coding of the human's
258 directions, failure modes, and lessons.

## Overall assessment

This is a substantial and, as far as I can judge, careful piece of work. The listings are generated
from the sources and checked mechanically, which I appreciate. The errata are concrete and witnessed,
and the end-to-end gate-level result for one matrix family is genuinely new. My main concerns:

- The paper overstates what is new about the logic.
- The headline result depends on assumptions that are stronger than the text admits.
- The reader cannot check the specification.
- The process half reads as an engaging anecdote rather than an empirical study, and lacks a threats
  to validity discussion.

All of this is fixable.

**Recommendation:** major revision. I would argue for acceptance once M1–M5 are addressed.

## Major concerns

**M1. The novelty of the logic contributions is overstated, and one claim is wrong.**
- The paper says repeatedly that "the logic has no rule for total correctness of loops" and that
  termination is a statement "no rule of the system can prove". Ying's TOPLAS 2011 paper, which the
  authors cite, presents *both* a partial and a total correctness proof system, including a
  total-correctness rule for `while`. What is true is that *QHLProver* formalises only the
  partial-correctness system. Please correct this everywhere (introduction, Section 4, Lessons).
- Lemma 1 (resetting loops) should be positioned honestly. It is a semantic special case for loops
  whose body ignores its input, not a new proof rule of the logic, and its proof is a geometric series.
- The "closed-form weakest precondition of initialise; gates; measure" is a direct consequence of the
  standard wp calculus. That is useful, but it should not be presented as an insight on a par with the
  results.
- The "three ideas" in the introduction are all standard facts. They are worth stating as the reason
  the proofs are short, but please say that none is new in isolation.

**M2. The headline theorem rests on strong assumptions that are not discussed.**
- Theorem 9 (total correctness) needs every eigenvalue of A on the phase-estimation grid. It also needs
  the hypothesis `Cb`, |C/λ_j| ≤ 1 for *every* clock value j < N, not only for eigenvalues.
- Since λ_1 = 2π/(N t_0) is the smallest positive grid value, `Cb` forces C ≤ 2π/(N t_0). The success
  probability p = C²‖A⁻¹b‖² is then at most (2π/(N t_0))²‖A⁻¹b‖², which can be far below the 1/κ² the
  introduction suggests. The expected number of rounds 1/p grows with N².
- This is presumably because the controlled rotation must be unitary on every clock value. The inexact
  theorems clamp the rotation instead. The paper must state this restriction where the headline is
  stated, explain where it comes from, and point to the theorems that avoid it.

**M3. The reader cannot check the specification.**
- The headline listing refers to `hhl_rus`, `hhl_target`, `reg_eig`, `herm_spectrum` and the register
  layout `[2^k, n, 2]`, none of which is shown. For a CADE audience the specification *is* the result.
- Please show the definitions of the target state, the gate list and the grid eigenvalues, and say
  which definitions a reader must trust.
- The same applies to `elementary` and `hhl_lap_gates` for the gate-level theorem. There, the abridged
  listing hides all hypotheses, which makes it impossible to check what "for L + μI" quantifies over.

**M4. The gate-level claim needs an honest complexity reading.**
- Theorem 11 gives a closed-form count but no asymptotic interpretation, and no comparison with HHL's
  claimed complexity. The count is linear in the clock size 2^k (≈ κ/ε) and uses first-order Trotter,
  so r grows like t²/η.
- Please give the leading term in O-notation, say how it compares with the complexity HHL promises,
  and state clearly that the oracle-free result is for one family. For general sparse A the oracles
  remain.
- The phrase "the whole algorithm runs on polynomially many elementary gates" needs its parameters.

**M5. The process study needs a threats-to-validity section and some missing data.**
- It is a single case (n = 1).
- The prompt coding was done by the agent itself, as the method section only hints ("the coding is
  ours"). There is a single coder, no codebook validation and no second rater.
- Spring logs are missing, so October numbers stand in for the whole project.
- Model versions are proprietary and will change.
- "Results" counts lemmas of any size.
- No measure of human time is given. Ilin's report, which this paper follows, gives hours; even a
  proxy (hours in which the human sent a direction) would help.
- No cost is given, only tokens.
- Please add a limitations section that discusses each of these, and disclose explicitly who coded
  the prompts.

## Minor concerns

1. **Errata.** Say which version is meant in every row: the appendix exists only in arXiv v3. Say
   whether the errors are typos or substantive, and whether the authors have been informed. Row 9
   (κ ≤ 2T) is not formally refuted and should be marked as such in the table itself, not only in the
   text.
2. **Organisation.** Sections 2.2 and 4.1 overlap: the language and the triples are introduced twice.
   The introduction lacks a roadmap of the sections.
3. **Figure 5** is computed numerically, not proved; the caption says so, but the text should not
   suggest otherwise.
4. **Table 5 (statistics)** mixes spring and October columns whose rows are mostly empty for spring.
   Consider a note on what each missing value would need.
5. **Responsibility for the text.** The "Use of AI" paragraph should state who takes responsibility
   for the text and the claims, and how the author reviewed the agent's statements.
6. **Related work** misses the survey by Lewis, Soudjani and Zuliani (ACM TQC 2023) and a discussion of
   total correctness for quantum while-loops beyond QHLProver.
7. **The title** "Verified" is strong given M2 and M4. Consider qualifying it in the abstract.
8. **The abridged listing** of Theorem 11 is hard to read: the count is one long expression.

## Questions to the authors

1. How many hours did the human spend, even approximately?
2. Did the human's review ever change a *statement*, as opposed to names and presentation? Examples
   would strengthen the "specification review is not delegable" claim.
3. Did the agent ever weaken a statement or add a hypothesis to make a proof go through
   ("hypothesis creep", in Ilin's terms)? If `Cb` is an instance, say so.
4. Could the derived rules (initialisation, gate lists, resetting loops) be contributed to QHLProver?

---

# Response and revision (round 1)

*Written as the authors, after revising the paper. Each item names the change.*

## Major concerns

- **M1.** Corrected everywhere (introduction, Section 4, Lessons, Related work). Ying's 2011 paper has
  a total-correctness system whose loop rule needs a bound function; QHLProver formalises only the
  partial one. Lemma 1 (resetting loops) is now presented as a semantic special case proved from the
  denotation, not as a rule of the logic. The closed-form weakest precondition is described as a
  consequence of the wp calculus, and the "three ideas" are introduced as standard facts that keep
  the proofs short ("None of them is new in isolation").
- **M2.** A new paragraph, *A restriction*, follows Theorem 8. It states that `Cb` ranges over every
  clock value, so C ≤ 2π/(N t₀), and that 1/p then grows like N². It explains why: the exact circuit
  applies the rotation on every clock value. It notes that the matrix-level theorem holds for every C
  and that the circuits of the paper's regime clamp the rotation instead. The introduction states the
  exact-case caveat, and the restriction is listed among the limitations.
- **M3.** A new paragraph, *What is specified*, with Listing `lst:spec`, shows the grid eigenvalues
  `reg_eig`, the target state `hhl_target` and the gate list `hhl_gates`, and says which definitions a
  reader must trust. The gate-level listing for the Laplacian now shows all its hypotheses and the
  elementary-gate and length conclusions; its caption says exactly what is elided.
- **M4.** After Theorem 11, the count is read asymptotically: O(4^k (2+μ)² t₀ m² K / C) gates, with
  the factor 2^k from the clock and a second from first-order Trotter. The paragraph compares this
  with the cost HHL claims for higher-order simulation, and says that the oracle-free result is for one
  family; for general sparse A the oracles remain.
- **M5.** A new subsection, *Limitations and Threats to Validity* (Section 8.3), covers each point:
  a single case, coding by the agent with one coder and no second rater, missing spring logs,
  proprietary model versions, results of unequal size, the human-time proxy, no monetary cost. The
  method appendix now says that the agent coded the directions. The statistics table gives the proxy:
  84 distinct local hours with a direction in October (on 11 days).

## Minor concerns

1. **Errata.** The caption names arXiv:0811.3171v3 and notes that the appendix exists only there. The
   last row says in the table that the failure of κ ≤ 2T is argued informally and that only the
   correction κ ≤ 2T + 1 is formal. The text says that we cannot always tell a misprint from a
   miscalculation. The paper makes no claim about contacting the HHL authors; that is the author's
   decision.
2. **Organisation.** The semantics of the while-language moved from Section 4.1 to Section 2.2, so the
   language, its semantics and the triples are introduced once; Section 4.1 now gives only the proof
   system. A roadmap closes the introduction.
3. **Figure 5.** The text claims only the proved bounds (`pe_amp_tail`, `win_amp_tail`); the figure
   illustrates them with computed values, as its caption says. No change needed.
4. **Table 5.** The caption now says what the blank spring cells would need.
5. **Responsibility.** The Use-of-AI paragraph now ends "The author takes full responsibility for the
   content of this paper."
6. **Related work.** New paragraph on total correctness of quantum loops (Ying's total-correctness
   system; our Lemma 1 as a semantic special case) and a pointer to the survey by Lewis, Soudjani and
   Zuliani (ACM TQC 5(1), 2023).
7. **Title and abstract.** We kept the title. The abstract now says that the exact case has the
   eigenvalues on the grid, that the gate-level result is for one family, and that the simulation is
   first-order.
8. **Abridged listing.** Rebuilt; the count is now stated as its own conclusion and the hypotheses are
   shown.

## Answers to the questions

1. **Hours.** We have no time log. The proxy is 84 distinct local hours in which a direction was given
   (October, 11 days). It counts neither reading nor thinking between directions.
2. **Did review change statements?** Yes, in scope rather than in wording. The human's question about
   the "black boxes" (28 October) turned the circuit-level theorems with oracles into a gate-level
   pipeline; the request to remove the oracle queries led to the oracle-free Laplacian instance; and
   the request for the sparse case added the sparse-simulation theorem. Section 7 quotes the first and
   the last.
3. **Hypothesis creep.** `Cb` was not added to rescue a proof: without it the controlled rotation of
   the exact circuit is not unitary. It is a modelling restriction, and the paper now says what it
   costs. We did not audit the history systematically for creep, and the spring logs that would allow
   it were not retained.
4. **Contributing the rules to QHLProver.** The derived rules depend only on QHLProver and on matrix
   lemmas of our entries, so they could move there. That is for QHLProver's maintainers to decide.
