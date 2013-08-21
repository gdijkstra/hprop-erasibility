\newcommand{\ie}{i.e.\ }
\newcommand{\st}{such that\xspace}
\newcommand{\eg}{e.g.\ }
\newcommand{\UIP}{uniqueness of identity proofs\xspace}
\newcommand{\uip}{uniqueness of identity proofs\xspace}
\newcommand{\MLTT}{Martin-L\"of's type theory\xspace}
\newcommand{\pitype}{$\Pi$-type\xspace}
\newcommand{\pitypes}{$\Pi$-types\xspace}
\newcommand{\sigmatype}{$\Sigma$-type\xspace}
\newcommand{\sigmatypes}{$\Sigma$-types\xspace}
\newcommand{\contrtype}{$(-2)$-type\xspace}
\newcommand{\contrtypes}{$(-2)$-types\xspace}
\newcommand{\hprop}{$h$-proposition\xspace}
\newcommand{\hprops}{$h$-propositions\xspace}
\newcommand{\hset}{$h$-set\xspace}
\newcommand{\hsets}{$h$-sets\xspace}
\newcommand{\proptype}{$(-1)$-type\xspace}
\newcommand{\proptypes}{$(-1)$-types\xspace}
\newcommand{\ntype}[1]{$#1$-type\xspace}
\newcommand{\ntypes}[1]{$#1$-types\xspace}
\newcommand{\ntruncation}[1]{$#1$-truncation\xspace}
\newcommand{\ntruncated}[1]{$#1$-truncated\xspace}
\newcommand{\inftygrpd}{$\infty$-groupoid\xspace}
\newcommand{\inftygrpds}{$\infty$-groupoids\xspace}
\newcommand{\Hit}{Higher inductive type\xspace}
\newcommand{\Hits}{Higher inductive types\xspace}
\newcommand{\onehit}{$1$-{\textsc HIT}\xspace}
\newcommand{\onehits}{$1$-{\textsc HITs}\xspace}
\newcommand{\hit}{higher inductive type\xspace}
\newcommand{\hits}{higher inductive types\xspace}
\newcommand{\propeq}{\equiv}
\newcommand{\defeq}{\overset{\Delta}{=}}
\newcommand{\hott}{homotopy type theory\xspace}
\newcommand{\Hott}{Homotopy type theory\xspace}
\newcommand{\coqprop}{|Prop|\xspace}
\newcommand{\coqtype}{|Type|\xspace}
\newcommand{\coqset}{|Set|\xspace}
\newcommand{\coqprops}{|Prop|s\xspace}
\newcommand{\coqtypes}{|Type|s\xspace}
\newcommand{\coqsets}{|Set|s\xspace}
\newcommand{\withoutk}{\verb+--without-K+}
\newcommand{\ghcrewriterules}{\textsc{GHC} rewrite rules\xspace}
\newcommand{\todoi}[1]{\todo[inline]{#1}}
\newcommand{\contribution}[1]{\begin{quote}%
{\bf Contribution: } #1%
\end{quote}}

\newenvironment{coq}{%
\verbatim%
}{%
\endverbatim%
}

\newcommand{\homotopyinterpretation}{
\begin{center}%
\begin{tabular}{||l||l||}%
\hline%
 \textbf{type theory}  &  \textbf{homotopy theory}  \\%
\hline%
 |A| is a type          &  |A| is a space                              \\%
 |x, y : A|             &  |x| and |y| are points in |A|               \\%
 |p, q : x == y|        &  |p| and |q| are paths from |x| to |y|       \\%
 |w : p == q|           &  |w| is a homotopy between paths |p| and |q| \\%
 \hfill $\vdots$ \hfill & \hfill $\vdots$ \hfill                       \\%
\hline%
\end{tabular}%
\end{center}%
}

\newcommand{\researchquestionA}{%
\begin{quote}%
  What is \hott and why is it interesting to do programming in?%
\end{quote}%
}

\newcommand*\widebar[1]{\overline{#1}}