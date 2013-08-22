agdafiles = $(wildcard *.agda)

default : html

html : $(agdafiles)
	agda --html --html-dir=/home/gdijkstra/thesispages/hprop-erasibility README.agda
