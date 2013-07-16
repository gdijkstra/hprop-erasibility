\chapter{Applications of homotopy type theory}

\todoi{Introductory paragraph explaining what applications we will
  look at, apart from that we have already seen function
  extensionality.}

Contributions:

\begin{itemize}
\item Investigate how \hits can be used to construct
  quotients and how this compares to other approaches (setoids,
  definable quotients).
\item Elaborate on Licata's use of univalence for views on abstract
  types and extend it to non-isomorphic views.
\end{itemize}

\section{Quotient types}
\label{sec:quots}

\begin{itemize}
\item Ubiquity of quotients in mathematics and programming
\item Difficulties of quotients in intensional type theory
\item Agda's approach: setoids
\item Note that using setoids has its downsides:
  \begin{itemize}
  \item User has access to the underlying set.
  \item Functions acting on setoids need not respect setoid structure.
  \item User has to be careful to use the right notion of equality
    (equivalence relation vs propositional equality).
  \end{itemize}
\item Do we need quotients?
\item Definition of from ``Definable quotients''
  paper~\citep{definablequotients}.
\item ``Definable quotients'' paper: give conditions when we do not
  quotients.
\item There are quotients (real numbers being an example) that we
  cannot define in ordinary \MLTT.
\end{itemize}

\subsection{Quotients as a \hit}

\begin{itemize}
\item With \hits, we can use the equivalence relation to generate the
  propositional equality of our type from, which means:
  \begin{itemize}
  \item No more confusion possible whether we have to use
    propositional equality or the equivalence relation: they
    coincide. (Sort of.)
  \item Elimination principle forces us to preserve the equivalence relation.
  \end{itemize}
\item First naive attempt: add path constructor: |(x y : A) -> x ~ y -> x == y|
\item Looking at eliminator: seems to satisfy our needs.
\item Define $\mathbb{Z}$ and $\mathbb{Q}$ as a quotient along with
  the usual operations.
\end{itemize}

\subsection{Coherence issues}

Suppose we have the a binary tree data type:

\begin{code}
  data Tree : Universe where
    Leaf : Tree
    Bin : Tree -> Tree -> Tree
\end{code}

Now suppose we are not interested in how this tree is balanced, so we
want to take the quotient of |Tree| by the following relation:

\begin{code}
  relation
\end{code}

\begin{itemize}
\item However: not a \hset: consider the MacLane pentagon.
\item We usually need the \ntruncation{0}.
\item Sometimes we do want proof relevant relations: modding out by isos.
\item Quotient construction can be generalised: generalise the
  \ntruncation{0} to arbitrary $n$ and generalise the |~|-valued
  relation |R| to any \ntype{m}.
\end{itemize}

\section{Views on abstract types}
\label{sec:views}

