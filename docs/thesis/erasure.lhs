\chapter{Erasing propositions}

When writing certified programs in a dependently typed setting, we can
conceptually distinguish between the \emph{program} parts and the
(correctness) \emph{proof} parts. (Also called the informative and
logical parts, respectively.) In practice, these two seemingly
separate concerns are often intertwined. Consider for example the
sorting of lists of naturals: given some predicate |isSorted : List
Nat -> List Nat -> Universe| that tells us whether the second list is
a sorted permutation of the first one, we want to write a term of the
following type:

\begin{code}
  sort : (xs : List Nat) -> Sigma (ys : List Nat) (isSorted xs ys)
\end{code}

To implement such a function, we need to provide for every list a
sorted list and a proof that this is indeed a sorted version of the
input list. At run-time we tend to be more interested in a function
without the correctness proofs, e.g. |sort' : List Nat -> List Nat|:
we want to \emph{erase} the logical parts.

Types such as |isSorted xs ys| are purely logical: we care more about
the presence of an inhabitant than what kind of inhabitant we exactly
have at our disposal. In section~\ref{sec:props} we give more examples
of such types, called \emph{propositions}, and places where they can
occur. In sections~\ref{sec:coqprop} and~\ref{sec:irragda} we review
the methods Coq and Agda provide us to annotate
types. Section~\ref{sec:colfam} reviews the concept of
\emph{collapsible families} and how we can detect whether a type is a
proposition. In section~\ref{sec:hprops} we relate all these methods
to the concept of \hprops.

\section{Propositions}
\label{sec:props}

In the |sort| example, the logical part, |isSorted xs ys|, occurs in
the result as part of a \sigmatype. This means we can separate the
proof of correctness from the sorting itself, i.e. we can write a
function |sort' : List Nat -> List Nat| and a proof of the following:

\begin{code}
  sortCorrect : (xs : List Nat) -> isSorted xs (sort' xs)
\end{code}

The logical part here asserts properties of the \emph{result} of the
computation. If we instead have assertions on our \emph{input}, we
cannot decouple this from the rest of the function as easily as, if it
is at all possible. For example, suppose we have the following
function, (safely) selecting the $n$-th element of a list:

\begin{code}
 elem : (A : Universe) (xs : List A) (i : Nat) -> i < length xs -> A
\end{code}

If we were to write |elem| without the bounds check |i < length xs|,
we would get a partial function. Since we can only define total
functions in our type theory, we cannot write such a
function. However, at run-time, carrying these proofs around makes no
sense: type checking has already showed that all calls to |elem| are
safe and the proofs do not influence the outcome of |elem|. We want to
erase terms of types such as |i < length xs|, if we have established
that they do not influence the run-time computational behaviour of our
functions.

\subsection{Bove-Capretta method}

The |elem| example showed us how we can use propositions to write
functions that would otherwise be partial, by asserting properties of
the input. The Bove-Capretta method~\citep{bcmethod} somewhat
generalises this: it provides us with a way to transform any (possibly
partial) function defined by general recursion into a total,
structurally recursive one. The quintessential example of a definition
that is not structurally recursive is \emph{quicksort}:

\begin{code}
  qs : List Nat -> List Nat
  qs []         = []
  qs (x :: xs)  = qs (filter (gt x) xs) ++ x :: qs (filter (le x) xs)
\end{code}

The recursive calls are done on |filter (gt x) xs)| and |filter (le x)
xs)| instead of just |xs|, hence it is not structurally recursive. To
solve this problem, we create an inductive family from the original
function definition, describing the call graphs for every input. Since
we can only construct finite values, being able to produce such a call
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
|qsAcc xs| to guide the recursion. Even though we actually pattern
match on |qsAcc xs| and seemingly influences the computational
behaviour of the function, erasing this argument yields the original
|qs| definition.

\section{The sort \coqprop in Coq}
\label{sec:coqprop}

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
\label{sec:irragda}

\todoi{TODO}

\section{Collapsible families}
\label{sec:colfam}

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
\label{sec:hprops}

\todoi{As we have seen, \hprops admit all kinds of interesting
  properties: impredicativity and all that.}

\todoi{Can \emph{almost} be seen as an internalised version of
  collapible families.}

\todoi{Internal to the type theory: the user can show that things as
  \hprops.}

\todoi{Can we do some sort of singleton elimination?}

\todoi{Does the \sigmatypes example work?}

\todoi{How does it relate to Agda's irrelevance?}
