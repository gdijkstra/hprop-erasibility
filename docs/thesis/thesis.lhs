\documentclass[a4paper,10pt]{report}

%include thesis.fmt

\usepackage[paper=a4paper, margin=4.3cm]{geometry}

\usepackage{color}
\usepackage[usenames,dvipsnames,svgnames,table]{xcolor}

\usepackage[authoryear,numbers]{natbib}

\usepackage[text width=10cm]{todonotes}
\usepackage[utf8x]{inputenc}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{tgpagella}
\usepackage{url}
\usepackage{hyperref}

\hypersetup{
  colorlinks,
  citecolor=DarkBlue,
  linkcolor=black,
  urlcolor=DarkBlue}

\usepackage{verbatim}
\usepackage{xspace}
\usepackage[parfill]{parskip}
\usepackage{setspace} 
\usepackage{makeidx}
\makeindex

\setcounter{tocdepth}{1}

\usepackage{tikz}
\usetikzlibrary{decorations.pathmorphing} % for snake lines
\usetikzlibrary{matrix}
% TikZ styles for drawing

\tikzstyle{snakeline} = [->, decorate, decoration={zigzag, pre length=0.1cm, post length=0.1cm, segment length=1.5mm, amplitude=.25mm}]
\tikzstyle{snakelin} = [->, decoration={zigzag, pre length=0.1cm, post length=0.1cm, segment length=1.5mm, amplitude=.25mm}]
\tikzset{node distance=2cm, auto}

%\onehalfspacing

%include commands.lhs

\newcommand{\HRule}{\noindent\rule{\linewidth}{1.5pt}}

\begin{document}

%include titlepage.lhs
%include abstract.lhs

\tableofcontents

%include intro.lhs
%include hottintro.lhs
%include applications.lhs
%include erasure.lhs
%include discussion.lhs

%include acknowledgements.lhs

\appendix

%include bibliography.lhs
%include symbols.lhs
%include index.lhs

\end{document}
