\chapter{Applications of homotopy type theory}

\todoi{Introductory paragraph explaining what applications we will
  look at, apart from that we have already seen function
  extensionality.}

\section{Quotient types}
\label{sec:quots}

\begin{itemize}
\item Ubiquity of quotients in mathematics and programming
\item Difficulties of quotients in intensional type theory
\item Agda's approach: setoids
\item Definable quotients
\item Contributions: investigate how \hits can be used to construct
  quotients and how this compares to other approaches (setoids,
  definable quotients).
\end{itemize}

\subsection{Quotients as a \hit}

\begin{itemize}
\item Downside of setoid: one has to be careful to use the equivalence
  relation instead of propositional equality. Equivalence relation has
  to be preserved when writing functions on setoids, but this is not
  immediately enforced by the type system.
\item With \hits, we can use the equivalence relation to generate the
  propositional equality of our type from, which means:
  \begin{itemize}
  \item No more confusion possible whether we have to use
    propositional equality or the equivalence relation: they coincide.
  \item Elimination principle forces us to preserve the equivalence relation.
  \end{itemize}
\item First naive attempt: add path constructor: |(x y : A) -> x ~ y -> x == y|
\item Looking at eliminator: seems to satisfy our needs.
\item However: not a \hset: consider the Maclane pentagon.
\item We need the \ntruncation{0}.
\item Look at eliminator
\item Define $\mathbb{Q}$ as a quotient along with the operations.
\end{itemize}

\subsection{Definable quotients}

\section{Views on abstract types}
\label{sec:views}

