\documentclass[a4paper,10pt]{article}

%include thesis.fmt

\newcommand{\MLTT}{Martin-L\"of's type theory }
\newcommand{\todoi}[1]{\todo[inline]{#1}}
\newcommand{\contribution}[1]{\begin{quote}
{\bf Contribution: } #1
\end{quote}}

\newcommand{\pitype}{$\Pi$-type }
\newcommand{\pitypes}{$\Pi$-types }
\newcommand{\sigmatype}{$\Sigma$-type }
\newcommand{\sigmatypes}{$\Sigma$-types }
\newcommand{\contrtype}{$(-2)$-type }
\newcommand{\contrtypes}{$(-2)$-types }
\newcommand{\hprop}{$h$-proposition}
\newcommand{\hprops}{$h$-propositions }
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

\title{Erasing propositions \\ in homotopy type theory}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

%include erasure.lhs

\newpage

\bibliographystyle{plainnat}
\bibliography{proposal}

\end{document}
