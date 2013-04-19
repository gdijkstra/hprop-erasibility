\chapter{Erasing propositions}

Recall that we defined \emph{\hprops} as \proptypes \todo{Refer to
  appropriate section\\ when its there.}, i.e. types of which its
identity types are contractible. Equivalently, we can also define
\hprops as follows:

\begin{code}
  isprop : (A : Set) -> Set
  isprop A = (x y : A) -> x == y
\end{code}

From this definition, it is immediate that \hprops are those types
that satisfy \emph{proof irrelevance}. 

\todoi{Explain that this is proof irrelevance}

\todoi{Show some closure properties}

\todoi{Impredicativity}

\todoi{Relate it to collapsibility~\citep{collapsibility}}



\begin{itemize}
\item Can we formulate erasure ``things'' on \sigmatypes and \pitypes,
  considering their elimination properties and all that. From this
  move on to general inductive data types, or maybe the other way
  around?
\item We can establish, as seen above, that a lot of operations are in
  a sense independent of the inhabitant of the \hprop at hand. Does
  this mean we can also use these results as a base for optimisations?
\item We want optimisations to be some sort of transformation that
  preserves \emph{definitional} equality. But why exactly do we want
  this? Interfacing with other languages is one: representations have
  to match exactly, there are no implicit conversions anymore. Another
  reason is that we do not want to mess up metatheoretical properties,
  or have to formulate new ones to argue that what we are doing makes
  sense.
\end{itemize}
