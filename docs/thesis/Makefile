lhsfiles = thesis.lhs erasure.lhs bibliography.lhs commands.lhs thesis.fmt

default : thesis.pdf

preview : thesis.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app thesis.pdf; fi

thesis.pdf : thesis.tex $(lhsfiles) thesis.bib
	pdflatex thesis.tex && pdflatex thesis.tex
	bibtex thesis
	pdflatex thesis.tex && pdflatex thesis.tex && pdflatex -synctex=1 thesis.tex

thesis.tex : $(lhsfiles)
	lhs2TeX -o thesis.tex thesis.lhs

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm thesis.pdf thesis.tex *.synctex.gz *.bbl *.blg

