all: hasochism.pdf

hasochism.tex: hasochism.lhs
	if [ -f "hasochism.tex" ]; then chmod +w hasochism.tex; fi
	lhs2TeX -o hasochism.tex hasochism.lhs
	chmod -w hasochism.tex

hasochism.aux: hasochism.tex
	pdflatex hasochism

#hasochism.bbl: hasochism.aux hasochism.bib
#	bibtex hasochism

hasochism.pdf: hasochism.aux # hasochism.bbl
	pdflatex hasochism
	pdflatex hasochism

clean:
	rm -f *.aux *.log *.bbl *.blg *.ptb *.nav *.out *.snm *.toc *.vrb *~ \
	hasochism.tex

clean-all: clean
	rm hasochism.pdf
