paper.pdf: paper.tex refs.bib
	pdflatex -interaction=nonstopmode paper.tex >/dev/null || true
	bibtex paper >/dev/null || true
	pdflatex -interaction=nonstopmode paper.tex >/dev/null || true
	pdflatex -interaction=nonstopmode paper.tex | grep -E 'Output written|Error|Warning: Citation' || true
clean:
	rm -f paper.aux paper.bbl paper.blg paper.log paper.out paper.toc
