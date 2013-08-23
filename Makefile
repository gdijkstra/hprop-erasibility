agdafiles = $(wildcard *.agda)
htmlDirMac = 
htmlDirLinux = /home/gdijkstra/thesispages/hprop-erasibility
default : html

html : $(agdafiles)
	if [ `uname` = 'Darwin' ]; then									\
		agda --html --html-dir=$(htmlDirMac) index.agda;
	else												\
		agda --html --html-dir= index.agda;	\
	fi

