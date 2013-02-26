default : proposal.pdf

preview : proposal.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app proposal.pdf; fi

proposal.pdf : proposal.tex outline.tex
	pdflatex proposal.tex && pdflatex proposal.tex && pdflatex -synctex=1 proposal.tex

proposal.tex : proposal.lhs
	lhs2TeX -o proposal.tex proposal.lhs

outline.tex : outline.org
	emacs -batch --visit=outline.org -eval "(org-export-as-latex nil nil nil nil t)"

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm proposal.pdf outline.tex *.synctex.gz *.bbl *.blg

