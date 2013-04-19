\documentclass[a4paper,10pt]{book}

%include thesis.fmt

\usepackage{xspace}
\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage[text width=10cm]{todonotes}
\usepackage{tgpagella}
\usepackage[authoryear,round]{natbib}
\usepackage{url}

\newcommand{\MLTT}{Martin-L\"of's type theory\xspace}
\newcommand{\todoi}[1]{\todo[inline]{#1}}
\newcommand{\contribution}[1]{\begin{quote}
{\bf Contribution: } #1
\end{quote}}

\newcommand{\pitype}{$\Pi$-type\xspace}
\newcommand{\pitypes}{$\Pi$-types\xspace}
\newcommand{\sigmatype}{$\Sigma$-type\xspace}
\newcommand{\sigmatypes}{$\Sigma$-types\xspace}
\newcommand{\contrtype}{$(-2)$-type\xspace}
\newcommand{\contrtypes}{$(-2)$-types\xspace}
\newcommand{\hprop}{$h$-proposition\xspace}
\newcommand{\hprops}{$h$-propositions\xspace}
\newcommand{\proptype}{$(-1)$-type\xspace}
\newcommand{\proptypes}{$(-1)$-types\xspace}
\newcommand{\ntype}[1]{$#1$-type}
\newcommand{\ntypes}[1]{$#1$-types}
\newcommand{\inftygrpd}{$\infty$-groupoid\xspace}
\newcommand{\inftygrpds}{$\infty$-groupoids\xspace}

\title{Erasing propositions \\ in homotopy type theory}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

%include erasure.lhs

\newpage

\bibliographystyle{plainnat}
\bibliography{thesis}

\end{document}
