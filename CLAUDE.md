# QC Notes LaTeX Reconstruction

## Project Overview

This project reconstructs a LaTeX source file to faithfully match an original PDF of lecture notes on Quantum Computing by Vern Paulsen.

- **Target (ground truth):** `QC_Notes.pdf` — the original PDF; this is what the final output must match exactly.
- **Working file:** `QC_Notes_overleaf.tex` — a hand-reconstructed `.tex` file that approximates the original but likely contains errors, omissions, or formatting discrepancies.

**Your job:** Edit `QC_Notes_overleaf.tex` until it compiles to a document that is faithful to `QC_Notes.pdf` in content, structure, mathematical notation, and formatting. The PDF is always right. The `.tex` file may be wrong.

---

## Workflow

### 1. Reading the PDF

Use `pdftoppm` to rasterize pages for visual inspection — this is essential for math-heavy documents where text extraction alone is unreliable:

```bash
# Rasterize a single page (e.g., page 5) at 150 DPI
pdftoppm -jpeg -r 150 -f 5 -l 5 QC_Notes.pdf /tmp/page
ls /tmp/page-*.jpg   # find the output filename, then Read it
```

Rasterize individual pages as needed rather than all at once — each page at 150 DPI costs roughly 1,600 tokens.

Also try text extraction for bulk content checking:

```bash
pdftotext -layout QC_Notes.pdf /tmp/qc_text.txt
```

But prefer visual inspection (rasterization) for verifying mathematical expressions, alignment, spacing, and notation.

### 2. Compiling the `.tex` File

Compile with `pdflatex` (or `xelatex`/`lualatex` if the document requires it) and check for errors:

```bash
pdflatex QC_Notes_overleaf.tex
```

If the document uses bibliographies or cross-references, run the full sequence:

```bash
pdflatex QC_Notes_overleaf.tex
bibtex QC_Notes_overleaf   # only if needed
pdflatex QC_Notes_overleaf.tex
pdflatex QC_Notes_overleaf.tex
```

### 3. Comparing Output to PDF

After compiling, rasterize corresponding pages from both the original PDF and the compiled output, then compare them visually:

```bash
# Original PDF, page N
pdftoppm -jpeg -r 150 -f N -l N QC_Notes.pdf /tmp/orig
ls /tmp/orig-*.jpg

# Compiled output, page N
pdftoppm -jpeg -r 150 -f N -l N QC_Notes_overleaf.pdf /tmp/new
ls /tmp/new-*.jpg
```

Read both images and identify discrepancies.

---

## What to Fix

Work through the document page by page. For each page, compare the compiled `.tex` output to the original PDF and fix any of the following:

### Content Errors
- Missing text, sentences, or paragraphs
- Wrong words or garbled phrasing
- Missing or incorrect section/subsection titles
- Missing theorems, lemmas, definitions, proofs, or examples
- Incorrect theorem/lemma/definition numbering

### Mathematical Notation
- Incorrect or missing mathematical symbols
- Wrong use of `\mathbb`, `\mathcal`, `\mathbf`, `\mathrm`, etc.
- Incorrect subscripts, superscripts, or limits
- Missing or wrong indices in sums, products, or integrals
- Incorrectly rendered bras/kets (Dirac notation) — check for `\langle`, `\rangle`, `|`, or a custom bra-ket package
- Incorrect matrix or operator notation
- Wrong equation alignment or grouping (`align`, `equation`, `gather`, etc.)
- Missing or misplaced equation numbers

### Formatting and Structure
- Wrong heading levels (e.g., `\section` vs `\subsection`)
- Missing or extra blank lines that affect paragraph spacing
- Incorrect list environments (`itemize`, `enumerate`)
- Wrong theorem/definition environment names or styles
- Page layout discrepancies (margins, line spacing, font size)
- Missing or incorrect labels and cross-references

### Figures and Diagrams
- Missing figures or diagrams
- Incorrect captions or labels
- Wrong positioning or sizing

---

## Priorities

1. **Correctness of mathematical content** — every formula, equation, and symbol must exactly match the PDF.
2. **Completeness** — no text, theorem, proof, or section should be missing.
3. **Structural fidelity** — section hierarchy, theorem numbering, and cross-references should match.
4. **Visual similarity** — spacing, alignment, and layout should be close to the original (exact pixel-perfect match is not required, but the document should look like the same notes).

---

## Notes and Cautions

- **Do not rewrite or paraphrase.** The goal is reconstruction, not improvement. Preserve the original author's wording exactly.
- **Do not add content** that is not in the PDF.
- **Do not remove content** that is in the PDF, even if it seems redundant or unusual.
- If a section of the `.tex` file looks plausible but you cannot verify it against the PDF, rasterize that page of the PDF and check.
- If the `.tex` file uses a package or macro that produces errors, investigate whether the original document used a different package — check the PDF's visual output to infer the intent.
- Quantum computing notes commonly use Dirac bra-ket notation, tensor products (`\otimes`), and linear algebra over `\mathbb{C}`. Pay extra attention to these.

---

## File Reference

| File | Role |
|------|------|
| `QC_Notes.pdf` | **Ground truth.** Do not modify. |
| `QC_Notes_overleaf.tex` | **Working file.** Edit this to match the PDF. |
| `QC_Notes_overleaf.pdf` | Compiled output for comparison. Regenerated on each compile. |

---

## Git Workflow (auto-commit / auto-push)

This repo is mirrored to https://github.com/brydustin/Quantum_Computing on branch `main` via SSH (`git@github.com:brydustin/Quantum_Computing.git`). The user has authorized Claude to **commit and push automatically** without asking — follow these rules strictly.

### When to commit
- After each **logical unit of work** (e.g., "resolve sorrys of lemma X", "fix LaTeX page N", "add proof Y"). One commit per coherent task — not mega-commits spanning unrelated changes, not micro-commits per file.
- **Only commit verified state.** For Isabelle theories, that means `isabelle build -d . Quantum_Computing_by_VP` passes. For LaTeX, that means `pdflatex QC_Notes_overleaf.tex` compiles without errors. **Never commit broken state.** If you introduced new sorrys intentionally (as scaffolding), that's fine, but the theory must still build.
- Before committing, run `git status` to confirm you're only committing intended files; use `git add <specific-files>` rather than `git add -A` or `git add .` to avoid sweeping in noise.

### When to push
- Push after each commit that completes a task the user asked for, or at the end of a session. Don't batch a dozen unrelated commits before pushing — the user's remote should reflect verified progress as it happens.
- Push with `git push` (upstream is already set to `origin/main`). **Never** `--force` / `--force-with-lease` without explicit user request.

### Commit message style
- Short imperative first line (≤70 chars). Focus on *what* changed and *why* if non-obvious.
- Examples that fit this repo:
  - `Resolve sorrys in four_block_mat_mult_left_block_diag`
  - `Prove schur_induct via ONB extension + block structure`
  - `Fix LaTeX page 12: missing tensor product notation`
  - `Add helper lemma cscalar_prod_is_inner_prod_swap`
- Include the Claude co-author trailer (per global instructions).

### What NOT to commit
The `.gitignore` already excludes:
- Vendored AFP/Isabelle directories (`Jordan_Normal_Form/`, `Matrix/`, `Isabelle_Marries_Dirac/`, `Isabelle2025-2/`, etc.) — these come from AFP, not from this repo.
- Build artifacts: `Basic_Math_session/`, LaTeX `.aux`/`.log`/`.out`/`.toc`, `QC_Notes_overleaf.pdf`, editor backups (`*~`, `.Rhistory`, `.codex`).

Never commit:
- Credentials, `.env` files, SSH keys.
- Large binaries beyond what's already tracked (the ground-truth `QC_Notes.pdf` is fine; compiled `QC_Notes_overleaf.pdf` is ignored).

### Recovery
If a push is rejected (e.g., upstream moved), `git pull --rebase origin main`, resolve any conflicts, re-verify the build, then push. **Never** `git push --force` to recover — the user can do that manually if they actually want it.
