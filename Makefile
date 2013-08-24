agdafiles = $(wildcard *.agda)
htmlDirMac = /Users/gdijkstra/Documents/Studie/Master/Afstuderen/thesispages/hprop-erasibility
htmlDirLinux = /home/gdijkstra/thesispages/hprop-erasibility
default : html

html : $(agdafiles)
	if [ `uname` = 'Darwin' ]; then					\
		agda --html --html-dir=$(htmlDirMac) index.agda;        \
	else								\
		agda --html --html-dir=$(htmlDirLinux) index.agda;	\
	fi

