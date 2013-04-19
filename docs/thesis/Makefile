default : thesis.pdf

preview : thesis.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app thesis.pdf; fi

thesis.pdf : thesis.tex erasure.lhs
	pdflatex thesis.tex && pdflatex thesis.tex && pdflatex -synctex=1 thesis.tex

thesis.tex : thesis.lhs erasure.lhs
	lhs2TeX -o thesis.tex thesis.lhs

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm thesis.pdf erasure.tex thesis.tex *.synctex.gz *.bbl *.blg

