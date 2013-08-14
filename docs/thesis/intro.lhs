\chapter{Introduction}
\label{chap:intro}

\todoi{We want to talk about equality from within the type theory:
  propositional equality. For type checking we sometimes need to check
  whether two terms are equal, so we also have an external notion of
  equality: definitional equality. If we want these to coincide:
  extensional (which brings about UIP (assuming we have J) and
  function extensionality). If we do not force this, we get
  intensional type theory, in which we cannot prove UIP and fun
  ext. The lack of the latter is particularly annoying.}

\todoi{How this propositional equality should be interpreted was
  vague, seemed to lack UIP, but the usual models did not reflect
  this.}

\todoi{Eventually, things led to homotopy type theory: a new
  interpretation of propositional equality in \MLTT.}

\homotopyinterpretation

\todoi{Refer to current material on homotopy type theory. It's all
  geared toward mathematicians and stuff. Applications are
  formalisation of mathematics.}

\begin{quote}
  \todoi{Research question (roughly): what is homotopy type theory and
    (why) is it interesting for programming?}
\end{quote}

 \begin{itemize}
 \item \todoi{Contribution chapter~\autoref{chap:hottintro} introduction homotopy type theory}
 \item \todoi{Contribution chapter~\autoref{chap:applications} applications homotopy type theory}
 \item \todoi{Contribution chapter~\autoref{chap:erasure} on erasing propositions}
 \end{itemize}

\todoi{Discussion chapter~\autoref{chap:discussion}}

\todoi{Since the focus is on programming aspects of \hott, as opposed
  to doing homotopy theory, we won't do any diagram chasing and
  instead will use Agda syntax throughout the thesis. As such, we will
  expect the reader to be familiar with this.}

\todoi{Mention |A : Universe| versus |A : Set| thing and that we will
  omit levels.}

\todoi{Mention that there is no pattern matching in \MLTT and that we
  will abuse the \verb+--without-k+ flag.}

\todoi{Guide to source code appendix~\autoref{chap:code}}

