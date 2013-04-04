\documentclass[a4paper,10pt]{article}

%include proposal.fmt

\newcommand{\todoi}[1]{\todo[inline]{#1}}
\newcommand{\contribution}[1]{\begin{quote}
{\bf Contribution: } #1
\end{quote}}

\usepackage[utf8x]{inputenc}
\usepackage[parfill]{parskip}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{todonotes}
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
