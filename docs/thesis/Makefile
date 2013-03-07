default : thesis.pdf

preview : thesis.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app thesis.pdf; fi

thesis.pdf : thesis.tex outline.tex
	pdflatex thesis.tex && pdflatex thesis.tex && pdflatex -synctex=1 thesis.tex

thesis.tex : thesis.lhs outline.tex
	lhs2TeX -o thesis.tex thesis.lhs

outline.tex : outline.org
	rm -f outline.tex
	emacs -batch --visit=outline.org -eval "(org-export-as-latex nil nil nil nil t)"

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm thesis.pdf outline.tex thesis.tex *.synctex.gz *.bbl *.blg

