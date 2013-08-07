\chapter{Homotopy type theory}
\label{chap:hottintro}

As was briefly mentioned in~\autoref{chap:intro}, homotopy type theory
studies the correspondence between homotopy theory and type theory. As
such, we will start out with a very brief sketch of the basic notions
of homotopy theory. \todoi{Introduce the rest of the chapter.}

In \emph{homotopy theory} we are interested in studying
\emph{continuous deformations} \index{continuous deformation}. The
simplest case of this is continuously deforming one point into another
point, which is called a \emph{path}. A path in a space |X| from point
|x| to |y| is a continuous function |p : [0,1] -> X|, \st |p 0 = x|
and |p y = y|, also notated as |p : x ~~> y|.  The set of all paths in
|X| can be also considered as a space. In this space, called the
\emph{path space} \index{path space} of |X|, we again can look at
the paths. Suppose we have two paths |p, q : [0,1] -> X| with the same
begin and end points, then a path between |p| and |q|, called a
\emph{homotopy}, is a continuous function |gamma : [0,1] -> [0,1] ->
X| where |gamma 0 = p| and |gamma 1 = q| (see figure
\todo{figure}). Of course, we can also look at homotopies in these
path spaces, and homotopies between these higher homotopies, ad
infinitum.

If we have a path |p : a ~~> b| and a path |q : b ~~> c|, we can
compose these to form a path |p circ q : a ~~> c|.  For every path |p : a
~~> b|, there is a reversed path |p inv : b ~~> a|. For every point
|a|, there is the constant path |ra : a ~~> a|. One might wonder
whether reversing a path acts as an inverse operation with |ra| being
the unit of path composition, \ie whether we the following
equations are satisfied: 

\begin{itemize}
\item |p circ p inv = ra|
\item |p inv circ p = rb|
\item |p circ rb = p|
\item |ra circ p = p|
\end{itemize}

This happens to not be the case: the equations do not hold in the
strict sense. However, both sides of the equations are homotopic to
eachother. The same holds for the associativity of composition: it is
only associative up to homotopy.

\todoi{Note that this gives us a (weak) groupoid structure. This is
  the way to do homotopy theory according to Grothendieck?}

\section{Identity types of \MLTT}
\label{sec:identitytypes}

\cite{mltt} introduced a notion of equality in his type theory:
\emph{propositional} equality \index{propositional equality}, defined
using so called identity types. These types can be formulated in Agda
syntax as follows:

\begin{code}
  data Id (A : Universe) : A → A → Universe where
    refl : (x : A) → Id A x x
\end{code}

In order to type check |refl x : Id A x y|, the type checker needs to
verify that |x| and |y| are definitionally equal. The |refl|
constructor gives us that definitional equality implies propositional
equality. The converse does not hold: we are working with an
\emph{intensional} type theory \index{intensional type
  theory}. \emph{Extensional} type theories \index{extensional type
  theory} add a so called equality reflection rule that propositional
equality implies definitional equality.

If we want to do something with the inhabitants of an inductive type,
other than passing them around, we must use the induction principle
(or elimination operator) of the inductive type. The induction
principle of the |Id| type is usually called |J| and has the following
type:

\begin{code}
  J :   (A : Universe)
    ->  (P : (x y : A) -> (p : Id A x y) -> Universe)
    -> (c : (x : A) -> P x x (refl x))
    -> (x y : A) -> (p : Id A x y)
    -> P x y p
\end{code}

Along with this type, we have the following computation rule:

\begin{code}
  J A P c x x (refl x) === c x
\end{code}

We will make use of a slightly different, but equivalent formulation
of these types, due to Paulin-Mohring \todo{citation needed}:

\begin{code}
  data Id' (A : Universe) (x : A) : A → Universe where
    refl : Id' A x x
\end{code}

with induction principle:

\begin{code}
  J' :  (A : Universe)
    ->  (P : (x y : A) -> (p : Id' A x y) -> Universe)
    ->  (c : P x x refl)
    ->  (x y : A) -> (p : Id' A x y)
    ->  P x y p
\end{code}

and computation rule:

\begin{code}
  J' A P c x refl === c
\end{code}

To make things look more like the equations we are used to, we will
for the most part use infix notation, leaving the type parameter
implicit: |Id A x y| becomes |x == y|. In some cases we will fall back
to the |Id A x y| notation, when it is a bit harder to infer the type
parameter.

Using the identity types and their induction principles, we can show
that it is an equivalence relation, \ie given |A : Universe| and |x y z :
A|, we can find inhabitants of the following types:

\begin{itemize}
\item |refl   : Id A x x|
\item |symm   : Id A x y -> Id A y x|
\item |trans  : Id A x y -> Id A y z -> Id A x z|
\end{itemize}

\subsection{Function extensionality}
\label{sec:funext}

To prove properties about functions, it is often useful to have the
principle of function extensionality:

\begin{code}
  functionExtensionality  :   (A B : Universe) -> (f g : A -> B)
                          ->  ((x : A) -> f x == g x)
                          ->  f == g

\end{code}

However, in \MLTT there is no term of that type. Since this theory has
the canonicity property, having a propositional equality in the empty
context, \ie | /- p : x == y |, we know that |p| must be canonical: it is
definitionally equal to |refl|. In order for it to type check, we then
know that |x| and |y| must be definitionally equal. Now consider the
functions |f = \n -> n + 0| and |g = \n -> 0 + n|, with the usual
definition of |+ : Nat -> Nat -> Nat|, we can prove that |(n : Nat)
-> f n == g n|, but not that |f == g|, since that would imply they are
definitionally equal, which they are not.

\subsection{Uniqueness of identity proofs}
\label{sec:uip}

The canonicity property implies that if, in the empty context, we have
two identity proofs |p q : Id A x y|, these proofs are both |refl|,
hence they are equal to one another. Using dependent pattern matching,
we can prove this property in Agda, called \emph{uniqueness of identity
  proofs}:

\begin{code}
UIP : (A : Universe) (x y : A) (p q : Id A x y) -> Id (Id A x y) p q
UIP A x dotx refl refl = refl
\end{code}

Proving this using~|J| instead of dependent pattern matching has
remained an open problem for a long time and has eventually been shown
to be impossible \citep{groupoidinterpretation}. As a complement
to~|J|, Streicher introduced the induction principle~|K|:

\begin{code}
  K  :   (A : Universe) (x : A) (P : Id A x x -> Universe)
     ->  P refl
     ->  (p : Id A x x)
     ->  P c
\end{code}

Using |K| we can prove |UIP|, and the other way around. It has been
shown that in type theory along with axiom |K|, we can rewrite
definitions written with dependent pattern matching to ones that use
the induction principles and axiom~|K|
\citep{eliminatingdependentpatternmatching}.

\section{Groupoid interpretation of types}
\label{sec:groupoid}

One way to show that we cannot prove |UIP| and |K| from |J|, is to
construct models of type theory with identity types in which there are
types that do not exhibit the |UIP| property. In
\cite{groupoidinterpretation}, the authors note that types have a
groupoid structure. This means that if we can find a groupoid that
violates |UIP|, translated to the language of groupoids, then |UIP| is
not provable within \MLTT with identity types.

We have a notion of composition of proofs of propositional equality:
the term |trans : Id A x y -> Id A y z -> Id A x z|, as such we will
use the notation |_ circ _| instead of |trans|. The same goes for |symm :
Id A x y -> Id A y x|, which we will denote as |_inv|. We can prove
that this gives us a groupoid, \ie we can prove the following laws
hold:

Given |a, b, c, d: A| and |p : a == b|, |p : b == c| and |q : c == d|
we have:

\begin{itemize}
\item Associativity: |p circ (q circ r) == (p circ q) circ r|
\item Left inverses: |p inv circ p == refl|
\item Right inverses: |p circ p inv == refl|
\item Left identity: |refl circ p == p|
\item Right identity: |p circ refl == p|
\end{itemize}

Groupoids can be seen as categories in which every arrow is
invertible. Using this correspondence, |p : x == y| can be seen as an
arrow |p : x -> y|. In this language, |UIP| means that if we have two
arrows |p, q : x -> y|, then |p| and |q| are the same. The category
consisting of two objects |x| and |y| with distinct arrows |p, q : x
-> y| along with their inverses is then a counterexample of |UIP|.

One thing we glossed over is what kind of equalities we were talking
about: associativity, etc. all hold up to propositional equality one
level higher. The identity type |Id A x y| is of course a type and
therefore has a groupoid structure of its own. Every type gives rise
to a tower of groupoids that can interact with eachother. These
structures, called \inftygrpds, also show up in homotopy theory, hence
we have the correspondence between types and spaces as mentioned
earlier.

\section{Truncations}
\label{sec:truncations}

The tower of iterated identity types of a type can tell us all sorts
of things about the type. For example, we can have a tower in which
the identity types in a sense become simpler every iteration, until
they reach a fixpoint, in which the identity types are isomorphic to
the unit type, |top|. In homotopy theory, spaces isomorphic (or
rather, homotopic) to the ``unit space'', \ie the space consisting of
one point, are called contractible. One way to formulate this in type
theory is with the following definition:

\begin{code}
isContractible : Universe -> Universe
isContractible A = Sigma A (\ center -> (x : A) -> (Id A center x))
\end{code}

If the structure of the identity types peters out after $n$
iterations, we call such a type $(n-2)$-truncated, or a
\ntype{(n-2)}\footnote{The somewhat strange numbering, starting at
  $-2$ comes from homotopy theory, where they first considered
  groupoids without any higher structure to be $0$-truncated and then
  generalised backwards.}:

\begin{code}
ntruncated : NatMinusTwo -> Universe -> Universe
ntruncated minustwo  A = isContractible A
ntruncated (S n)     A = (x : A) -> (y : A) -> ntruncated n (Id A x y)
\end{code}

These truncation levels have the property that every \ntype{n} is also
an \ntype{(n+1)}, \ie |ntruncated| defines a filtration on the
universe of types.

The \emph{contractible} types are the types that are isomorphic to
|top| in the sense that every inhabitant of a contractible type is
unique up to propositional equality. In section~\autoref{sec:hit} we will
see examples of contractible types that have more than one canonical
element.

Types of truncation level $-1$ are called
\emph{h-propositions}. \ntypes{(-1)} are either empty (|bottom|) or,
if they are inhabited, contractible, hence isomorphic to
|top|. h-propositions satisfy the principle of proof irrelevance:

\begin{code}
  proofIrrelevance : Universe -> Universe
  proofIrrelevance A = (x y : A) -> Id A x y
\end{code}

This fits the classical view of propositions and their proofs: we only
care about whether or not we have a proof of a proposition and do not
distinguish between two proofs of the same proposition.

\emph{h-Sets} are the \ntypes{0}. Every type that satisfies |K| and
|UIP| is an h-set. This is the highest truncation level we can get to
in Agda, without adding extra axioms.

\section{Higher inductive types}
\label{sec:hit}

In order to do some homotopy theory in type theory, we need to be able
to construct interesting spaces in our type theory. One way to define
spaces inductively, is by giving the constructors of the points in the
space along with (higher) paths between them. For example, the
interval can be seen as two points and a path connecting these two
points, which in pseudo-Agda would look like:

\begin{code}
  data Interval : Universe where
    zero  : Interval
    one   : Interval

    segment : zero == one
\end{code}

Inductive types with added equalities/paths are called \emph{higher
  inductive types}. As of yet, these have not been implemented in
Agda, but there are ways to simulate
them.\footnote{\verb+http://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/+}

Apart from defining the constructors and its paths, we also need an
induction principle. Intuitively, to write a function from a higher
inductive type into something else, we need to specify what to do with
the constructors, just as with normal inductive types, but we need to
do this in such a way that we preserve the added equalities. 

As one would expect from homotopy theory, we can prove that the type
|Interval| is contractible, even though it has more than one canonical
element. It is indeed isomorphic to the unit type, since isomorphism
is defined with propositional equality and we have a proof of |zero ==
one|.

\section{Univalence}
\label{sec:univalence}

A property satisfied by a popular model of homotopy theory, the
category of simplicial sets, is the \emph{univalence} property. In
type theory terms this roughly means we have the following axiom:

\begin{code}
  univalence : (A B : Universe) -> Iso A B -> Id Universe A B
\end{code}

where |Iso A B| is a record containing functions between |A| and |B|
and proofs that these functions are eachother's inverses.

Unfortunately, the full axiom is a bit more involved, since we have
additional coherence properties that need to hold: the proofs in the
|Iso A B| record need to interact in a certain way. However, the axiom
as stated above does hold for all h-sets, where there higher structure
is simple enough to not have to worry about coherence.
