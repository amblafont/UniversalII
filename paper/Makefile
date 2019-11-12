all: paper.pdf

paper.pdf : paper.tex abbrevs.tex universaliit.tex b.bib
	latexmk -pdf $<

clean:
	rm -f *.aux *.bbl *.blg *.fdb_latexmk *.fls *.log *.out *.nav *.snm *.toc *.vtc *.ptb *~ paper.pdf
