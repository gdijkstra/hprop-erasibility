
When writing programs in a dependently typed language, we often find
ourselves writing terms whose sole purpose is to convince the type
checker that we are doing the right thing, instead of being relevant
to the actual computation at hand. The concept of h-propositions from
homotopy type theory helps us describes a class of such terms. We
propose an optimisation based on h-propositions and compare this to
other approaches, such as Coq's program extraction. Apart from this,
we provide an introduction to homotopy theory and discuss several
applications to dependently typed programming.

\section{Homotopy type theory}
\label{sec:hott}

In \emph{homotopy theory} we are interested in studying paths between
points of some topological space. All the paths of a space form again
a space, called the path space. In such a path space, we have the
following notion of (higher) paths: if we can continuously deform one
path, i.e. a point in the path space, into another, we have a higher
path in the path space. These higher paths are called
\emph{homotopies}. Since the path space is a space, we can repeat this
construction indefinitely and talk about higher homotopies.

In \MLTT we have a notion of equality interal to the type theory,
namely the \emph{identity types}
(section~\ref{sec:identitytypes}). These happen to behave in ways
similar to the aforementioned homotopies. \emph{Homotopy type theory}
studies these similarities, which roughly boils down to the following
correspondence:

\begin{center}
\begin{tabular}{||l||l||}
\hline
 \textbf{type theory}  &  \textbf{homotopy theory}  \\
\hline
 |A| is a type      &  |A| is a space                              \\
 |x, y : A|         &  |x| and |y| are points in |A|               \\
 |p, q : == y|      &  |p| and |q| are paths from |x| to |y|       \\
 |w : p == q|       &  |w| is a homotopy between paths |p| and |q| \\
\hline
\end{tabular}
\end{center}

This table can be expanded indefinitely: there is no need to stop at
homotopies between paths: we also have identity types analogous to
homotopies between homotopies, ad infinitum.

In homotopy theory, one classifies spaces along the structure of their
(higher) homotopies. Using the correspondence, this way of thinking
can be translated to type theory, where we arrive at the notion of
\ntypes{n} (section~\ref{sec:truncations}). The \ntypes{(-1)} (or
h-propositions) are of particular interest in this thesis, as they
help us provide a way to classify types of which its inhabitants only
serve to convince the type checker as opposed to having any
computational relevance. In section~\ref{sec:contrib-optimisation} we
discuss how these can be used to optimise dependently typed programs.

The homotopic way of thinking has also inspired additions to the type
theory, such as \emph{higher inductive types} (section~\ref{sec:hit})
and the \emph{univalence axiom} (section~\ref{sec:univalence}). These
additions have been successfully used to formalise proofs from
topology, such as the calculation of the fundamental group of the
circle \citep{fundamentalgroup}. Apart from their use in formal
mathematics, these additions might also prove useful for programming
purposes, which is the subject of
section~\ref{sec:contrib-hott-applications}.

\subsection{Identity types of \MLTT}
\label{sec:identitytypes}

\cite{mltt} introduced a notion of equality in his type theory:
\emph{propositional} equality, defined using so called identity
types. These types can be formulated in Agda syntax as follows:

\begin{code}
  data Id (A : Set) : A → A → Set where
    refl : (x : A) → Id A x x
\end{code}

In \MLTT we do not have pattern matching to work with inhabitants of
an inductive type, but use the induction principles (or elimination
operators) instead. The induction principle of the |Id| type is
usually called |J| and has the following type:

\begin{code}
  J :   (A : Set)
    ->  (P : (x y : A) -> (p : Id A x y) -> Set)
    -> (c : (x : A) -> P x x (refl x))
    -> (x y : A) -> (p : Id A x y)
    -> P x y p
\end{code}

Along with this type, we have the following computation rule:

\begin{code}
  J A P c x x (refl x) === c x
\end{code}

\newpage

We will make use of a slightly different, but equivalent formulation
of these types, due to Paulin-Mohring:

\begin{code}
  data Id' (A : Set) (x : A) : A → Set where
    refl : Id' A x x
\end{code}

with induction principle:

\begin{code}
  J' :  (A : Set)
    ->  (P : (x y : A) -> (p : Id' A x y) -> Set)
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
that it is an equivalence relation, i.e. given |A : Set| and |x y z :
A|, we can find inhabitants of the following types:

\begin{itemize}
\item |refl   : Id A x x|
\item |symm   : Id A x y -> Id A y x|
\item |trans  : Id A x y -> Id A y z -> Id A x z|
\end{itemize}

\subsubsection{Function extensionality}
\label{sec:funext}

To prove properties about functions, it is often useful to have the
principle of function extensionality:

\begin{code}
  functionExtensionality  :   (A B : Set) -> (f g : A -> B)
                          ->  ((x : A) -> f x == g x)
                          ->  f == g

\end{code}

However, in \MLTT there is no term of that type. Since this theory has
the canonicity property, having a propositional equality in the empty
context, i.e. | /- p : x == y |, we know that |p| must be canonical: it is
definitionally equal to |refl|. In order for it to type check, we then
know that |x| and |y| must be definitionally equal. Now consider the
functions |f = \n -> n + 0| and |g = \n -> 0 + n|, with the usual
definition of |+ : Nat -> Nat -> Nat|, we can prove that |(n : Nat)
-> f n == g n|, but not that |f == g|, since that would imply they are
definitionally equal, which they are not.

\subsubsection{Uniqueness of identity proofs}
\label{sec:uip}

The canonicity property implies that if, in the empty context, we have
two identity proofs |p q : Id A x y|, these proofs are both |refl|,
hence they are equal to one another. Using dependent pattern matching,
we can prove this property in Agda, called \emph{uniqueness of identity
  proofs}:

\begin{code}
UIP : (A : Set) (x y : A) (p q : Id A x y) -> Id (Id A x y) p q
UIP A x dotx refl refl = refl
\end{code}

Proving this using~|J| instead of dependent pattern matching has
remained an open problem for a long time and has eventually been shown
to be impossible \citep{groupoidinterpretation}. As a complement
to~|J|, Streicher introduced the induction principle~|K|:

\begin{code}
  K  :   (A : Set) (x : A) (P : Id A x x -> Set)
     ->  P refl
     ->  (p : Id A x x)
     ->  P c
\end{code}

Using |K| we can prove |UIP|, and the other way around. It has been
shown that in type theory along with axiom |K|, we can rewrite
definitions written with dependent pattern matching to ones that use
the induction principles and axiom~|K|
\citep{eliminatingdependentpatternmatching}.

\subsection{Groupoid interpretation of types}
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
use the notation |_ . _| instead of |trans|. The same goes for |symm :
Id A x y -> Id A y x|, which we will denote as |_inv|. We can prove
that this gives us a groupoid, i.e. we can prove the following laws
hold:

Given |a, b, c, d: A| and |p : a == b|, |p : b == c| and |q : c == d|
we have:

\begin{itemize}
\item Associativity: |p . (q . r) == (p . q) . r|
\item Left inverses: |p inv . p == refl|
\item Right inverses: |p . p inv == refl|
\item Left identity: |refl . p == p|
\item Right identity: |p . refl == p|
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

\subsection{Truncations}
\label{sec:truncations}

The tower of (iterated) identity types of a type can tell us all sorts
of things about the type. For example, we can have a tower in which
the identity types in a sense become simpler every iteration, until
they reach a fixpoint, in which the identity types are isomorphic to
the unit type, |top|. In homotopy theory, spaces isomorphic (or
rather, homotopic) to the ``unit space'', i.e. the space consisting of
one point, are called contractible. One way to formulate this in type
theory is with the following definition:

\begin{code}
isContractible : Set -> Set
isContractible A = Sigma A (\ center -> (x : A) -> (Id A center x))
\end{code}

If the structure of the identity types peters out after $n$
iterations, we call such a type $(n-2)$-truncated, or a
\ntype{(n-2)}\footnote{The somewhat strange numbering, starting at
  $-2$ comes from homotopy theory, where they first considered
  groupoids without any higher structure to be $0$-truncated and then
  generalised backwards.}:

\begin{code}
ntruncated : NatMinusTwo -> Set -> Set
ntruncated minustwo  A = isContractible A
ntruncated (S n)     A = (x : A) -> (y : A) -> ntruncated n (Id A x y)
\end{code}

These truncation levels have the property that every \ntype{n} is also
an \ntype{(n+1)}, i.e. |ntruncated| defines a filtration on the
universe of types.

The \emph{contractible} types are the types that are isomorphic to
|top| in the sense that every inhabitant of a contractible type is
unique up to propositional equality. In section~\ref{sec:hit} we will
see examples of contractible types that have more than one canonical
element.

Types of truncation level $-1$ are called
\emph{h-propositions}. \ntypes{(-1)} are either empty (|bottom|) or,
if they are inhabited, contractible, hence isomorphic to
|top|. h-propositions satisfy the principle of proof irrelevance:

\begin{code}
  proofIrrelevance : Set -> Set
  proofIrrelevance A = (x y : A) -> Id A x y
\end{code}

This fits the classical view of propositions and their proofs: we only
care about whether or not we have a proof of a proposition and do not
distinguish between two proofs of the same proposition.

\emph{h-Sets} are the \ntypes{0}. Every type that satisfies |K| and
|UIP| is an h-set. This is the highest truncation level we can get to
in Agda, without adding extra axioms.

\subsection{Higher inductive types}
\label{sec:hit}

In order to do some homotopy theory in type theory, we need to be able
to construct interesting spaces in our type theory. One way to define
spaces inductively, is by giving the constructors of the points in the
space along with (higher) paths between them. For example, the
interval can be seen as two points and a path connecting these two
points, which in pseudo-Agda would look like:

\begin{code}
  data Interval : Set where
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

\subsection{Univalence}
\label{sec:univalence}

A property satisfied by a popular model of homotopy theory, the
category of simplicial sets, is the \emph{univalence} property. In
type theory terms this roughly means we have the following axiom:

\begin{code}
  univalence : (A B : Set) -> Iso A B -> Id Set A B
\end{code}

where |Iso A B| is a record containing functions between |A| and |B|
and proofs that these functions are eachother's inverses.

Unfortunately, the full axiom is a bit more involved, since we have
additional coherence properties that need to hold: the proofs in the
|Iso A B| record need to interact in a certain way. However, the axiom
as stated above does hold for all h-sets, where there higher structure
is simple enough to not have to worry about coherence.

\section{Contributions}
\label{sec:contribs}


\subsection{Introduction to homotopy type theory}
\label{sec:contrib-hott-intro}


There are several introductions to homotopy type theory
(e.g. \cite{awodeysurvey}, \cite{pelayosurvey} and \cite{rijkehott}),
but these are geared towards mathematicians who know about homotopy
theory, but do not know about type theory. For the computer scientist
who knows some type theory, but has never seen any homotopy theory,
there is virtually no material.

\contribution{We provide an introduction to homotopy type theory for
the computer scientist who has some familiarity with type theory, but
does not have the background in homotopy theory.}

\subsection{Optimisations based on h-propositions}
\label{sec:contrib-optimisation}


In homotopy type theory we have a class of types called h-propositions
or \ntypes{(-1)}, satisfying the proof irrelevance principle:

\begin{code}
  proofIrrelevance : Set -> Set
  proofIrrelevance A = (x y : A) -> Id A x y
\end{code}

i.e., we can find a term of type |(A : Set) -> ntruncated (-1) A ->
proofIrrelevance A|. The other way around also holds: if a type
exhibits proof irrelevance, it is an h-proposition. Examples of
h-propositions are the empty type |bottom| and the unit type |top|. In
fact, we can prove that if a type is inhabitated and it is a
proposition, it is isomorphic to the unit type.

\subsubsection{Comparison with collapsibility}


The definition of h-propositions looks a lot like
\emph{collapsibility} \citep{collapsibility}. Given some indexing type
|I|, a family |D : I -> Set| is called \emph{collapsible} if for all
indices |i| and inhabitants |x, y : D i|, |x| and |y| are
definitionally equal. In other words: every |D i| is either empty or
has one element (up to definitional equality).

If we know that a family is collapsible, we can optimise its
constructors and induction principles by erasing certain parts, since
we know that the relevant parts (if there are any) can be recovered
from the indices.

Comparing the definition of collapsible families to that of
h-propositions, we notice that they are largely the same. The latter
is a can be seen as an internalised version of collapsibility: we have
replaced definitional equality with propositional equality.

A question one might ask is whether the optimisations based on
collapsibility also hold for h-propositions. If our type theory
satisfies canonicity, propositional equality implies definitional
equality in the empty context. This means, that we can indeed use the
concept of propositions for the same optimisations as those for
collapsible families.

In homotopy type theory, one usually adds axioms such as the
univalence axiom, or assume extra equalities to hold in order to
implement higher inductive types. This means we lose canonicity hence
we no longer have that propositional equality always implies
definitional equality.

Not all is lost: let |B| be a type for which all proofs |p : Id B x y|
are definitionally equal to |refl| and let |A| be an h-proposition,
then the only functions we |f : A -> B| we can write are
(definitionally) constant functions, hence we can at run-time ignore
what value of |A| we get exactly.

\contribution{We identify cases where h-propositions can be safely
  erased: we provide an optimisation in the spirit of
  \cite{collapsibility}}

\subsubsection{Comparison with Prop in Coq}


In Coq we can make the distinction between informative or
computational parts of our program (everything that lives in |Set|)
and logical parts (everything that lives in |Prop|). This distinction
is also used when extracting a Coq development to another language: we
can safely erase terms of sort |Prop|.

Another property of the |Prop| universe is that it is impredicative:
propositions can quantify over propositions. h-Propositions also have
this property in a certain sense.

\contribution{We provide a comparison between Coq's |Prop| universe to
the h-propositions of homotopy type theory and our run-time optimisation.}

\subsection{Applications of homotopy type theory to programming}
\label{sec:contrib-hott-applications}


\subsubsection{Quotients}


Higher inductive types provide for a natural construction of
quotients. In pseudo-Agda this would look as follows:

\begin{code}
data Quotient (A : Set) (R : A -> A -> Proposition) : Set where
  project  : A -> Quotient A R

  relate   : (x y : A) -> R x y -> Id (Quotient A R) (project x) (project y)
  contr    : (x y : Quotient A R)  -> (p q : Id (Quotient A R) x y) 
                                   -> Id (Id (Quotient A R) x y) p q
\end{code}

Quotienting out by the given relation means that we need to regard two
terms |x| and |y| related to eachother with |R| as propositionally
equal, which is witnessed by the |relate| constructor. In order for
the result to be a set (in the sense of being a discrete groupoid), we
also need to ensure that it satisfies UIP, which in turn is witnessed
by the |contr| constructor.

\contribution{We compare this approach to quotients to other
approaches, such as definable quotients \citep{definablequotients}.}

\subsubsection{Views on abstract types}


The univalence axiom should make it more easy to work with views in a
dependently typed
setting.\footnote{\verb+http://homotopytypetheory.org/2012/11/12/abstract-types-with-isomorphic-types/+}

There are cases where it makes sense to have an implementation that
has more structure than we want to expose to the user using the
view. Instead of having an isomorphism, we then have a
section/retraction pair. Since we have quotients to our disposal, we
can transform any such pair into an isomorphism.

\contribution{Identify examples of non-isomorphic views and determine
whether quotients are easy to work with for this use case.}

