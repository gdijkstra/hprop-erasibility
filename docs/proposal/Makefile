default : proposal.pdf

preview : proposal.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app proposal.pdf; fi

proposal.pdf : proposal.tex outline.lhs proposal.bib
	pdflatex proposal.tex && pdflatex proposal.tex
	bibtex proposal
	pdflatex proposal.tex && pdflatex proposal.tex && pdflatex -synctex=1 proposal.tex

proposal.tex : proposal.lhs outline.lhs proposal.bib proposal.fmt
	lhs2TeX -o proposal.tex proposal.lhs

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm proposal.pdf outline.tex proposal.tex *.synctex.gz *.bbl *.blg

