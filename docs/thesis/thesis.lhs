\documentclass[a4paper,10pt]{book}

%include thesis.fmt

\usepackage[authoryear,round]{natbib}
\usepackage[text width=10cm]{todonotes}
\usepackage[utf8x]{inputenc}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{tgpagella}
\usepackage{url}
\usepackage{verbatim}
\usepackage{xspace}
\usepackage[parfill]{parskip}
\usepackage{setspace} 
%\onehalfspacing

%include commands.lhs

\title{Erasing propositions \\ and homotopy type theory}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

\tableofcontents

%include intro.lhs
%include hottintro.lhs
%include erasure.lhs
%include applications.lhs

%include bibliography.lhs


\end{document}
