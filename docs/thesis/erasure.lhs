\chapter{Erasing propositions}

When writing certified programs in a dependently typed setting, the
definition of computation is often intertwined with the the proof of
its correctness. Consider for example the sorting of list of naturals:
given some predicate |isSorted : List Nat -> List Nat -> Universe|
that tells us whether the second list is a sorted permutation of the
first one, we can write a term of the following type:

\begin{code}
  sort : (xs : List Nat) -> Sigma (ys : List Nat) (isSorted xs ys)
\end{code}

To implement such a function, we need to provide for every list a
sorted list and a proof that this is indeed a sorted version of the
input list. To calculate the sorted list however, we do not care what
kind of proof of |isSorted xs ys| is generated: we only care about the
fact that such a proof can be generated. At run-time we tend to be
more interested in a function without the correctness proofs,
e.g. |sort' : List Nat -> List Nat|.

\todoi{Maybe start mentioning \emph{propositions} and \emph{erasure}
  here already, along with some description of the flow of this
  chapter.}

\todoi{Call the rest of this ``introduction'' just the first section,
  called ``Propositions'' or something}

\section{Propositions}

In the |sort| example we can still separate the correctness proof from
the sorting, i.e. write the |sort' : List Nat -> List Nat| and a proof
of the following:

\begin{code}
  sortCorrect : (xs : List Nat) -> isSorted xs (sort' xs)
\end{code}

In the case of |sort|, the ``computationally irrelevant'' part asserts
properties of the result of the computation. If we instead have
assertions on our input, we usually cannot decouple this from the rest
of the function. For example, suppose we have the following function,
(safely) selecting the $n$-th element of a list:

\begin{code}
 elem : (A : Universe) (xs : List A) (i : Nat) -> i < length xs -> A
\end{code}

Since we can only define total functions inside our type theory, we
cannot write a function |elem'| that leaves out the |i < length xs|
argument. However, at run-time, carrying these proofs around makes no
sense: type checking has already showed that all calls to |elem| are
safe and the proofs do not influence the outcome of
|elem|.\footnote{Of course, we could have written |elem| in such a way
  that the proof of |i < length xs| \emph{does} influence the output.}
We want to \emph{erase} terms of types such as |i < length xs| and
|isSorted xs ys|, if we have established that they do not influence
the run-time computational behaviour of our functions.

\subsection{Bove-Capretta method}

Another source of (more involved) examples is the Bove-Capretta
method~\citep{bcmethod}. If we try to implement quicksort in type
theory, we notice that the recursion pattern does not fit the
structural recursion one we are allowed to work with:

\begin{code}
  qs : List Nat -> List Nat
  qs []         = []
  qs (x :: xs)  = qs (filter (gt x) xs) ++ x :: qs (filter (le x) xs)
\end{code}

The recursive calls are done on |filter (gt x) xs)| and |filter (le x)
xs)| instead of just |xs|, hence it is not structurally recursive. One
way to solve this is by creating an inductive family from the original
function definition, describing the call graph of each input. Since we
can only construct finite values, being able to produce such a call
graph means that the function terminates for that input. We can then
write a new function that structurally recurses on the call graph. In
our quicksort case we get the following inductive family:

\begin{code}
  data qsAcc : List Nat -> Set where
    qsAccNil   : qsAcc []
    qsAccCons  : (x : Nat) (xs : List Nat) 
                 (h1 : qsAcc (filter (gt x) xs))
                 (h2 : qsAcc (filter (le x) xs))
                 -> qsAcc (x :: xs)
\end{code}

with the following function definition\footnote{This definition uses
  dependent pattern matching, but can be rewritten directly using the
  elimination operators instead. The important thing here is to notice
  that we are eliminating the |qsAcc xs| argument.}

\begin{code}
  qs : (xs : List Nat) → qsAcc xs → List Nat
  qs dotnil         qsAccNil                =  []
  qs dotcons        (qsAccCons x xs h1 h2)  =  qs (filter (gt x) xs) h1 ++
                                               x :: qs (filter (le x) xs) h2
\end{code}

Pattern matching on the |qsAcc xs| argument gives us a structurally
recursive version of |qs|. Just as with the |elem| example, we need
information from the proof to be able to write this definition. In the
case of |elem|, we need the proof of |i < length xs| to deal with the
(impossible) case where |xs| is empty. In the |qs| case, we need
|qsAcc xs| to guide the recursion. However, at run-time, when the type
checker has seen that our definitions are total and our recursion is
structural, their work is done and hence should be erased.

As we have mentioned, we are interested in the fact that we have
proofs of |isSorted xs ys| and |i < length xs| and do not care what
proof we have exactly. In fact, if we have two inhabitants of
|isSorted xs ys|, we may even deem them to be equal, since they do not
influence the run-time behaviour of our sort function. If a type has
the property that all its inhabitants are equal to eachother, then the
type admits \emph{proof irrelevance} and the type is called a
\emph{proposition}.

\subsection{Propositions and \hprops}

Note that in the definitions above we have been a bit vague about what
kind of equality we are talking about exactly. The equality may refer
to definitional equality or propositional equality, depending on the
context. In order to avoid confusion, we will refer to the
propositional version as \emph{\hprops}, in accord with previous
definitions. In more informal passages where we do not specifically
chose one or another, we will use \emph{propositions} instead.

\section{The sort \coqprop in Coq}

\todoi{Motivating example in Coq}

\todoi{Show how the extracted version looks like}

\todoi{Note the limitations of what we can eliminate into}

\todoi{Impredicativity}

\todoi{Proof irrelevance can be assumed?}

\todoi{Proof irrelevance not enforced}

\todoi{Example of how things can go wrong}

\todoi{Singleton elimination}

\todoi{We can get the Bove-Capretta thing to work in such a way that
  the extracted version is like the original.}

\section{Irrelevance in Agda}

\todoi{TODO}

\section{Collapsible families}

Instead of letting the user annotate the programs to indicate what
parts are irrelevant to the computation at hand, \cite{collapsibility}
propose a series of optimisations, for the language Epigram, based on
the observation there is a lot of redundancy in well-typed programs,
hence some parts can be erased as they can recovered from other parts.

\todoi{Note that we are working in Epigram, even though we can write
  things in a dependent pattern matching style, everything gets
  \emph{elaborated} to a smaller language, which is very close to
  conventional \MLTT along with inductive families (Dybjer?).}

\todoi{Vec example: show that we indeed have a lot of duplication,
  even though there's a lot of arguments that can be recovered from
  others, so we can leave stuff out.}

\todoi{Not a language construct: instead of marking things as being a
  \coqprop or as irrelevant, the compiler itself figures out whether
  it is irrelevant or not.}

\todoi{Recover values of inductive families via their indices.}

\todoi{Needs the \emph{adequacy} property to hold, which breaks if we
  do \hott.}

\todoi{Bove-Capretta works nicely, really the way we want it to, as
  opposed to the Coq thing.}

\todoi{How about \sigmatypes? It does not apply to that. (Neither do
  any of the other optimisations in that paper?)}

\section{\hprops}

\todoi{As we have seen, \hprops admit all kinds of interesting
  properties: impredicativity and all that.}

\todoi{Can \emph{almost} be seen as an internalised version of
  collapible families.}

\todoi{Internal to the type theory: the user can show that things as
  \hprops.}

\todoi{Can we do some sort of singleton elimination?}

\todoi{Does the \sigmatypes example work?}

\todoi{How does it relate to Agda's irrelevance?}
