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

%include commands.lhs

\title{Erasing propositions \\ in homotopy type theory}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

\tableofcontents

%include intro.lhs
%include hottintro.lhs
%include erasure.lhs
%include applications.lhs

\todoi{Remove this: a citation to keep stuff from complaining~\citep{mltt}}

%include bibliography.lhs


\end{document}
