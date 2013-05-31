\documentclass[a4paper,10pt]{book}

%include thesis.fmt

\usepackage[authoryear,round]{natbib}
\usepackage[parfill]{parskip}
\usepackage[text width=10cm]{todonotes}
\usepackage[utf8x]{inputenc}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{tgpagella}
\usepackage{url}
\usepackage{verbatim}
\usepackage{xspace}
\usepackage{setspace} 
\onehalfspacing

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
