\section{Erasing propositions}

\begin{itemize}
\item What are \hprops?
\item What properties do they have?
  \begin{itemize}
  \item Proof irrelevance
  \item Given |A B : Set| and |hProp A|, every function |f : A -> B|
    is constant.
  \item Closed under sum, product, dependent sum, dependent product in some way.
  \item Impredicative in some way.
  \end{itemize}
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
