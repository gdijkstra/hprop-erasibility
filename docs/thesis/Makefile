lhsfiles = abstract.lhs acknowledgements.lhs applications.lhs	\
bibliography.lhs commands.lhs discussion.lhs erasure.lhs	\
hottintro.lhs intro.lhs thesis.lhs titlepage.lhs

default : thesis.pdf

preview : thesis.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app thesis.pdf; fi

thesis.pdf : thesis.tex $(lhsfiles) thesis.bib
	rubber -d thesis.tex

thesis.tex : $(lhsfiles) thesis.fmt
	lhs2TeX -o thesis.tex thesis.lhs

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm thesis.pdf thesis.tex *.synctex.gz *.bbl *.blg *.idx *.ilg *.ind

