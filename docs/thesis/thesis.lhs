\documentclass[a4paper,10pt]{report}

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
\usepackage{makeidx}
\makeindex

%\onehalfspacing

%include commands.lhs

\title{Erasing propositions \\ and homotopy type theory}

\author{Gabe Dijkstra}

\date{\today}

\begin{document}

\maketitle

%include abstract.lhs

\tableofcontents

%include intro.lhs
%include hottintro.lhs
%include applications.lhs
%include erasure.lhs
%include discussion.lhs

%include acknowledgements.lhs

\appendix

%include code.lhs
%include bibliography.lhs
%include symbols.lhs
%include index.lhs

\end{document}
