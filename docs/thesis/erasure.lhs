\chapter{Erasing propositions}

When writing certified programs in a dependently typed setting, we can
conceptually distinguish between the \emph{program} parts and the
\emph{proof} (of correctness) parts. (Also called the informative and
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
sorted list along with a proof that this is indeed a sorted version of the
input list. At run-time we tend to be more interested in a function
without the correctness proofs, e.g. |sort' : List Nat -> List Nat|:
we want to \emph{erase} the logical parts.

Types such as |isSorted xs ys| are purely logical: we care more about
the presence of an inhabitant than what kind of inhabitant we exactly
have at our disposal. In section~\ref{sec:props} we give more examples
of such types, called \emph{propositions}, and how they can occur. In
sections~\ref{sec:coqprop} and~\ref{sec:irragda} we review the methods
Coq and Agda provide us to annotate parts of our program as being
propositions. Section~\ref{sec:colfam} reviews the concept of
\emph{collapsible families} and how we, can automatically detect
whether a type is a proposition, instead of annotating them
ourselves. In section~\ref{sec:hprops} we relate all these methods to
the concept of \hprops and propose optimisations based on this.

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

The recursive calls are done on |filter (gt x) xs| and |filter (le x)
xs| instead of just |xs|, hence |qs| is not structurally recursive. To
solve this problem, we create an inductive family describing the call
graphs of the original function for every input. Since we can only
construct finite values, being able to produce such a call graph
essentially means that the function terminates for that input. We can
then write a new function that structurally recurses on the call
graph. In our quicksort case we get the following inductive family:

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
match on |qsAcc xs| and it therefore seemingly influences the
computational behaviour of the function, erasing this argument yields
the original |qs| definition.

\section{The \coqprop universe in Coq}
\label{sec:coqprop}

\todoi{Replace \coqtype with \coqset in the appropriate places.}

Apart from the \coqtype universe (or to be more precise: hierarchy of
universes), we have the \coqprop universe. As the name suggests, by
defining a type to be of sort \coqprop, we ``annotate'' it to be a
logical type, a proposition. Explicitly marking the logical parts like
this, makes the development easier to read and understand. More
importantly, the extraction mechanism now knows what parts are
supposed to be logical, hence what parts are to be erased.

In the |sort| example, we would define |isSorted| to be a family of
\coqprops indexed by |List Nat|. For the \sigmatype, Coq provides two
options: \verb+sig+ and \verb+ex+, defined as follows:

\begin{verbatim}
  Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P

  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P
\end{verbatim}

Since we have have an informative part in the \sigmatype that is the
result type of |sort|, we choose the \verb+sig+ version.

The extracted version of \verb+sig+ consists of a single constructor
\verb+exist+, with a single field of type \verb+A+. Since this is
isomorphic the type \verb+A+ itself, Coq optimises this away during
extraction. This means |sort : (xs : List Nat) -> Sigma (ys : List
Nat) (isSorted xs ys)| gets extracted to a function |sort' : List Nat
-> List Nat|.

When erasing all the \coqprop parts from our program, we do want to
retain the computational behaviour of the remaining parts. Every
function that takes an argument of sort \coqprop, but whose result
type is not in \coqprop, needs to be invariant under choice of
inhabitant for the \coqprop argument. To force this property, Coq
restricts the things we can eliminate a \coqprop into. The general
rule is that pattern matching on something of sort \coqprop is allowed
if the result type of the function happens to be in \coqprop.

There are exceptions to this rule: if the argument we are pattern
matching on happens to be an \emph{empty} or \emph{singleton
  definition} we may also eliminate into \coqtype. An empty definition
is an inductive definition without any constructors. A singleton
definition is an inductive definition with precisely one constructor,
whose fields are all in \coqprop. Examples of such singleton
definitions are conjunction on \coqprop (\verb+/\+) and the
accessibility predicate \verb+Acc+ used to define functions using
well-founded recursion.

Another important example of singleton elimination is elimination on
Coq's equality \verb+=+. In the standard library we have the following
function:

\begin{verbatim}
eq_rec : forall (A : Type) (x : A) (P : A -> Set), 
           P x -> forall y : A, x = y -> P y
\end{verbatim}

\verb+eq_rec+ is just the function |transport| with a slightly
different order of arguments. The inductive family \verb+=+ is defined
in the same way as we have defined it \todo{reference to appropriate
  section here?}, hence it is a singleton definition, amenable to
singleton elimination. However useful it is when programming in Coq,
it is not a desirable feature to have when working with homotopy type
theory. By allowing singleton elimination for identity types, we
essentially assume some form of \UIP. 

\todoi{Elaborate on how we cannot prove things about \coqprop in Coq
  itself and how this form of \UIP leads to an ``inconsistency'' as
  uncovered by Michael Shulman.}

\subsection{Quicksort example}

\begin{itemize}
\item We cannot pattern match on |qsAcc xs|, but we need to, in order to have a decreasing argument.
\item No singleton elimination, even though it is effectively a
  (sub)singleton type for every index.
\item We can do the pattern matching ``manually'': inversion and impossibility theorems.
\item Extracted version is ``exactly'' the original Haskell definition |qs|.
\end{itemize}

\subsection{Impredicativity}

\todoi{Impredicativity}



\section{Irrelevance in Agda}
\label{sec:irragda}

\todoi{TODO}

\section{Collapsible families}
\label{sec:colfam}

Instead of letting the user annotate the programs to indicate what
parts are irrelevant to the computation at hand, \cite{collapsibility}
propose a series of optimisations, for the language Epigram, based on
the observation there is a lot of redundancy in well-typed programs,
hence some parts can be erased as they can recovered from other parts
relatively cheaply.

Since we can write our definitions using (dependent) pattern matching
in Epigram, everything gets elaborated to a smaller core language
without pattern matching and calls to the elimination principle
instead. In order to optimise an inductive family, we need only look
at the constructors and the elimination principles. 

\todoi{Vec example: show that we indeed have a lot of duplication,
  even though there's a lot of arguments that can be recovered from
  others, so we can leave stuff out.}

\todoi{Not a language construct: instead of marking things as being a
  \coqprop or as irrelevant, the compiler itself figures out whether
  it is irrelevant or not.}

\todoi{Recover values of inductive families via their indices.}

\todoi{Needs the \emph{adequacy} property to hold, which breaks if we
  do \hott.}

\todoi{We want singleton elimination on Bove-Capretta stuff: there's
  at most one option for every index.}

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
