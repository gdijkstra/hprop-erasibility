\documentclass[a4paper,10pt]{article}

%include proposal.fmt

\newcommand{\MLTT}{Martin-L\"of's type theory }
\newcommand{\todoi}[1]{\todo[inline]{#1}}
\newcommand{\contribution}[1]{\begin{quote}
{\bf Contribution: } #1
\end{quote}}

\newcommand{\contrtype}{$(-2)$-type }
\newcommand{\contrtypes}{$(-2)$-types }
\newcommand{\proptype}{$(-1)$-type }
\newcommand{\proptypes}{$(-1)$-types }
\newcommand{\ntype}[1]{$#1$-type}
\newcommand{\ntypes}[1]{$#1$-types}
\newcommand{\inftygrpd}{$\infty$-groupoid }
\newcommand{\inftygrpds}{$\infty$-groupoids }

\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage[text width=10cm]{todonotes}
\usepackage{tgpagella}
\usepackage[authoryear,round]{natbib}
\usepackage{url}

\title{Master thesis proposal: \\
Erasing propositions \\ in homotopy type theory}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

%include outline.tex

\bibliographystyle{plainnat}
\bibliography{proposal}

\end{document}
