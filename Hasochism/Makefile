all: hasochism.pdf

hasochism.tex: hasochism.lhs \
        NatVec.lhs Existentials.lhs Pies.lhs NATTYInNatty.lhs \
        MergeSort.lhs \
        Evidence.lhs BoxPain.lhs BoxPleasure.lhs Editor.lhs
	if [ -f "hasochism.tex" ]; then chmod +w hasochism.tex; fi
	lhs2TeX -o hasochism.tex hasochism.lhs
	chmod -w hasochism.tex

hasochism.aux: hasochism.tex
	pdflatex hasochism

hasochism.bbl: hasochism.aux hasochism.bib
	bibtex hasochism

hasochism.pdf: hasochism.aux hasochism.bbl
	pdflatex hasochism
	pdflatex hasochism

edit: NatVec.lhs Pies.lhs BoxPleasure.lhs Editor.lhs ANSIEscapes.hs
	ghc -lncurses --make Editor -o edit

clean:
	rm -f *.aux *.log *.bbl *.blg *.ptb *~ \
	*.o *.hi \
	hasochism.tex

clean-all: clean
	rm -f edit hasochism.pdf
