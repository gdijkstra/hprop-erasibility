\chapter{Homotopy type theory}
\label{chap:hottintro}

As was briefly mentioned in~\cref{chap:intro}, homotopy type theory
studies the correspondence between homotopy theory and type theory. As
such, we will start out with a very brief sketch of the basic notions
of topology and homotopy theory (\cref{sec:homotopytheory}). After
that, we will describe the notion of propositional equality in \MLTT
using identity types (\cref{sec:identitytypes}). Having defined the
identity types, we can explain the interpretation of \MLTT in homotopy
theoretic terms, relating propositional equality to paths
(\cref{sec:homotopyinterpretation}). In \cref{sec:truncations}
we describe how the idea of classifying spaces along their homotopic
structure can be used in type theory to classify
types. \Cref{sec:hit} and \cref{sec:univalence} describe two
extensions to \MLTT inspired by homotopy theory. This chapter is
concluded by a discussion on the implementation issues of \hott
(\cref{sec:implementation}).

\section{Topology and homotopy theory}
\label{sec:homotopytheory}

Topology is the study of shapes (called spaces) and continuous
functions between spaces. It generalises the familiar notion of
continuity from calculus. In \emph{homotopy theory} we are interested
in studying continuous {deformations} \index{continuous
  deformation}. The simplest case of this is continuously deforming
one point into another point, which is called a \emph{path}. A path in
a space |X| from point |x| to |y| is a continuous function |p : [0,1]
-> X|, \st |p 0 = x| and |p y = y|, also notated as |p : x ~~> y|.
The set of all paths in |X| can be also considered as a space. In this
space, called the \emph{path space} \index{path space} of |X|, we
again can look at the paths. Suppose we have two paths |p, q : [0,1]
-> X| with the same begin and end points, then a path between |p| and
|q|, called a \emph{homotopy}, is a continuous function |gamma : [0,1]
-> [0,1] -> X| where |gamma 0 = p| and |gamma 1 = q|
(see~\cref{fig:homotopy}). Of course, we can also look at
homotopies in these path spaces, and homotopies between these higher
homotopies, ad infinitum.

\begin{figure}[!htb]
\minipage{0.24\textwidth}
\includegraphics[width=\textwidth]{img/homotopy0.pdf}
\endminipage\hfill
\minipage{0.24\textwidth}
\includegraphics[width=\textwidth]{img/homotopy1.pdf}
\endminipage\hfill
\minipage{0.24\textwidth}%
\includegraphics[width=\textwidth]{img/homotopy2.pdf}
\endminipage
\minipage{0.24\textwidth}%
\includegraphics[width=\textwidth]{img/homotopy3.pdf}
\endminipage
\label{fig:homotopy}
\caption{A homotopy between paths |p| and |q|}
\end{figure}

These paths have an interesting structure: we can define operations
acting on paths that satisfy certain laws: paths form a groupoid-like
structure. If we have a path |p : a ~~> b| and a path |q : b ~~> c|,
we can compose these to form a path |p circ q : a ~~> c|.  For every
path |p : a ~~> b|, there is a reversed path |p inv : b ~~> a|. For
every point |a|, there is the constant path |ra : a ~~> a|. One might
wonder whether reversing a path acts as an inverse operation with |ra|
being the unit of path composition, \ie whether we the following
equations are satisfied:

\begin{itemize}
\item |p circ (q circ s) = (p circ q) circ s|
\item |p circ p inv = ra|
\item |p inv circ p = rb|
\item |p circ rb = p|
\item |ra circ p = p|
\end{itemize}

This happens to not be the case: the equations do not hold in the
strict sense. However, both sides of the equations are homotopic to
eachother. These operations can also be defined on homotopies between
paths, for which the same equations can be shown to hold up to higher
homotopy. What we get is a tower of homotopies for which we have these
groupoid-like structure at every level, in which the equations hold up
to homotopy one level higher. This structure is called a \inftygrpd
structure. It was proposed in \citet{pursuing} that this notion
homotopy theory should be the study of these \inftygrpds, as these
should capture all the interesting homotopy properties of a space.

\section{Identity types of \MLTT}
\label{sec:identitytypes}

\cite{mltt} introduced a notion of equality internal to his type
theory, defined using \emph{identity types}. These types can be
formulated in Agda syntax as follows:

\begin{code}
  data Id (A : Universe) : A → A → Universe where
    refl : (x : A) → Id A x x
\end{code}

In order to type check |refl x : Id A x y|, the type checker needs to
verify that |x| and |y| are definitionally equal. The |refl|
constructor can be seen as a rule that definitional equality implies
propositional equality. The converse does not need to hold: type
theories (such as \MLTT) in which we do not have the \emph{equality
  reflection rule}, that states that propositional equality implies
definitional equality, are called \emph{intensional} type
theories. \emph{Extensional} type theories \index{extensional type
  theory} are theories in which the equality reflection rule does
hold.

If we want to do something with the inhabitants of an inductive type,
other than passing them around or ignoring them, we must use the
induction principle (or elimination operator) of the inductive
type. The induction principle of the |Id| type is usually called |J|
and has the following type:

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
of these types, due to \citet{mohring}, where the |x| is a parameter
as opposed to an index, yielding a more convenient elimination
principle:

\begin{code}
  data Id' (A : Universe) (x : A) : A → Universe where
    refl : Id' A x x
\end{code}

with induction principle:

\begin{code}
  J' :  (A : Universe)
    ->  (x : A)
    ->  (P : (y : A) -> (p : Id' A x y) -> Universe)
    ->  (c : P x x refl)
    ->  (y : A) -> (p : Id' A x y)
    ->  P x y p
\end{code}

and computation rule:

\begin{code}
  J' A P c x refl === c
\end{code}

Since the |x| is a fixed base point, this elimination principle is
also called \emph{based path induction} \citep{hottbook}.

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

Another important property of propositional equality is that it is a
congruence relation, \ie we have a term with the following type:

\begin{code}
  ap : {A B : Universe} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y
\end{code}

|ap f| can be read as the (functorial) \emph{action} on \emph{paths}
induced by |f| or the \emph{application} of |f| on \emph{paths}. If we
want to generalise |ap| to also work on dependent functions |f : (a :
A) -> B a|, we notice that we get something that does not type check:
|f x == f y| does not type check because |f x : B x| and |f y : B
y|. However, if we have an equality between |x| and |y|, then |B x ==
B y|, so we should be able to somehow transform something of type |B
x| to something of type |B y|. This process is called
\emph{transporting}:

\begin{code}
  transport : {A : Universe} {B : A -> Universe} {x y : A} -> x == y -> B x -> B y
\end{code}

|transport| is sometimes also called |subst|, as |transport| witnesses
the fact that if we have |x == y|, we can substitute any occurrence of
|x| in context |B| with |y|.

Using |transport| we can now formulate the dependent version of |ap|:

\begin{code}
  apd : {A : Universe} {B : A → Universe} {x y : A} → (f : (a : A) → B a) → (beta : x == y)
  → transport beta (f x) == f y
\end{code}

The resulting equality is an equality of between points in |B y|. Of
course it does not matter if we |transport| to |B x| or |B y|, as
propositional equalities are symmetric.

\subsection{Difficulties of identity types}

Even though at first glance the identity types have the right
structure: they form equivalence relations on types, there are still
some properties that cannot be proven, things that can be useful or
seem to be natural properties of a notion of equality.

\paragraph{Function extensionality}
\label{sec:funext}

When doing certified programming, we sometimes want to show one (more
optimised) function to be equal to another (naively implemented)
function. In these cases is often useful to have the principle of
function extensionality:

\begin{code}
  functionExtensionality  :   (A B : Universe) -> (f g : A -> B)
                          ->  ((x : A) -> f x == g x)
                          ->  f == g

\end{code}

However, in \MLTT there is no term of that type. Since this theory has
the canonicity property, having a propositional equality in the empty
context, \ie | /- p : x == y |, we know that |p| must be canonical: it
is definitionally equal to |refl|. In order for |/- refl : x == y| to
type check, we then know that |x| and |y| must be definitionally
equal. Now consider the functions |f = \n -> n + 0| and |g = \n -> 0 +
n|, with the usual definition of |+ : Nat -> Nat -> Nat| by recursion
on the first argument, we can prove that |(n : Nat) -> f n == g n|,
but not that |f == g|, since that would imply they are definitionally
equal, which they are not: one reduces to |\ n -> 0|, whereas the
other reduces to |\ n -> n + 0|.

\paragraph{Uniqueness of identity proofs}
\label{sec:uip}

The canonicity property implies that if we have |/- p : Id A x y| and
|/- q : Id A x y|, these proofs are both |refl|, hence they are equal
to one another: |p == q|. One would expect that it is possible to
prove this inside \MLTT. Using dependent pattern matching
\citep{depmatch}, we can easily prove this property in Agda, called
\UIP:

\begin{code}
UIP : (A : Universe) (x y : A) (p q : Id A x y) -> Id (Id A x y) p q
UIP A x dotx refl refl = refl
\end{code}

Proving this using~|J| instead of dependent pattern matching has
remained an open problem for a long time and has eventually been shown
to be impossible \citep{groupoidinterpretation} by constructing a
model of \MLTT in which there is a type that violates \UIP. This tells
us that dependent pattern matching is a non-conservative extension
over \MLTT\footnote{This actually means that all the code we write,
  should be written using the elimination principles. Agda provides a
  \withoutk flag that limits pattern matches to those cases that
  should be safe. The assumption is that every definition given by
  pattern matching that passes the \withoutk check, can be rewritten
  using the elimination principles. As such, we will sometimes use
  pattern matching for our definition.}

As a complement to~|J|, Streicher introduced the induction
principle~|K|:

\begin{code}
  K  :   (A : Universe) (x : A) (P : Id A x x -> Universe)
     ->  P refl
     ->  (c : Id A x x)
     ->  P c
\end{code}

Using |K| we can prove the |UIP| property, and the other way
around. We have also seen that dependent pattern matching implies
|K|. The converse of this has also been established: we can rewrite
definitions written with dependent pattern matching to ones that use
only the induction principles and axiom~|K|
\citep{eliminatingdependentpatternmatching}.

In \hott, we give up |K| (and essentially dependent pattern matching),
to allow for a more interesting structure of propositional equalities.

\section{Homotopy interpretation}
\label{sec:homotopyinterpretation}

In the introduction (\cref{chap:intro}), it was mentioned that
homotopy type theory concerns itself with the following
correspondence:


\homotopyinterpretation


In \cref{sec:homotopytheory} we noted that homotopies have a
\inftygrpd structure. It is this structure that leads us to the
correspondence between the identity types from \MLTT and homotopy
theory. In \cite{groupoidinterpretation}, the authors note that types
have a groupoid structure. We have a notion of composition of proofs
of propositional equality: the term |trans : Id A x y -> Id A y z ->
Id A x z|, as such we will use the notation |_ circ _| instead of
|trans|. The same goes for |symm : Id A x y -> Id A y x|, which we
will denote as |_inv|. We can prove that this gives us a groupoid, \ie
we can prove the following laws hold:

Given |a, b, c, d: A| and |p : a == b|, |p : b == c| and |q : c == d|
we have:

\begin{itemize}
\item Associativity: |p circ (q circ r) == (p circ q) circ r|
\item Left inverses: |p inv circ p == refl|
\item Right inverses: |p circ p inv == refl|
\item Left identity: |refl circ p == p|
\item Right identity: |p circ refl == p|
\end{itemize}

The important thing to note is what kind of equalities we are talking
about: the equations given above all hold up to propositional equality
one level higher. The identity type |Id A x y| is of course a type and
therefore has a groupoid structure of its own. Every type gives rise
to a tower of groupoids that can interact with eachother: the presence
of equations at one level can imply the presence of equations at a
higher level. This is exactly the same as the way homotopies form an
\inftygrpd, hence we have the correspondence between types and spaces
as mentioned earlier.

Having such an interpretation of type theory brings us several
things. Since every proof we write in type theory corresponds to a
proof of a statement in homotopy theory, we can use it to proof
theorems of homotopy theory.

It also means that the intuition about homotopy theory can be applied
to type theory. As such, we can use it to explain why one cannot prove
|K| using |J| (\cref{sec:interpret}), using a couple of
illustrations.

\subsection{Interpreting \UIP and |K|}
\label{sec:interpret}

Recall the elimination principle of identity types, |J|:

\begin{code}
  J :  (A : Universe)
    ->  (x : A)
    ->  (P : (y : A) -> (p : Id A x y) -> Universe)
    ->  (c : P x x refl)
    ->  (y : A) -> (p : Id A x y)
    ->  P x y p
\end{code}

Interpreting propositional equalities as paths, we see that it tells
us that if we want to prove that a predicate |P| on paths holds, we
only have to show that it is satisfied for the constant path
|refl|. Homotopically this can be motivated by the fact that |P| is a
predicate on paths with a fixed starting point |x| and a |y| that can
be chosen freely (see~\cref{fig:j}). Any path |p : x == y| can be
contracted along this path to the constant path |refl : x == x|, so
there is a homotopy between these two paths.

\begin{figure}[!htb]
\minipage{0.32\textwidth}
\includegraphics[width=\textwidth]{img/J0.pdf}
\endminipage\hfill
\minipage{0.32\textwidth}
\includegraphics[width=\textwidth]{img/J1.pdf}
\endminipage\hfill
\minipage{0.32\textwidth}%
\includegraphics[width=\textwidth]{img/J2.pdf}
\endminipage
\label{fig:j}
\caption{With |J| we have the freedom to move the end point around.}
\end{figure}

In the case of axiom |K|, both the beginning and the end point are
fixed:

\begin{code}
  K  :   (A : Universe) (x : A) (P : Id A x x -> Universe)
     ->  P refl
     ->  (p : Id A x x)
     ->  P c
\end{code}

Homotopically this means that we are restricted to loops. If we want
to contract a given path |p : x == x| to |refl : x == x|, we cannot
use the same trick as with |J|, as the end point is fixed. Contracting
a loop to |refl| does not always work, as can be seen
in~\cref{fig:k}. If we have a hole in our space, then we can
distinguish between loops that go around the hole and those that do
not.

\begin{figure}[!htb]
\minipage{0.32\textwidth}
\includegraphics[width=\textwidth]{img/K0.pdf}
\endminipage\hfill
\minipage{0.32\textwidth}
\includegraphics[width=\textwidth]{img/K1.pdf}
\endminipage\hfill
\minipage{0.32\textwidth}%
\includegraphics[width=\textwidth]{img/K2.pdf}
\endminipage
\label{fig:k}
\caption{With |K|, we are restricted to loops}
\end{figure}

\section{\ntypes{n}}
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

This can be interpreted as having a point |center| \st there is a path
from |center| to any point |x|. Such an interpretation sounds more
like the definition of \emph{path connectedness}. In homotopy theory
these two definitions do not coincide: contractibility implies path
connectedness, but not the other way around. An example of this is the
circle, which is path connected, but not contractible: going around
the circle once is not homotopic to the constant loop. The key here is
that the only functions that we can define in type theory are
\emph{continuous} functions, so |isContractible| should really be
interpreted as there being a point |center| \st we can construct paths
from |center| to any point |x| \emph{in a continuous manner}.

If the structure of the identity types peters out after $n$
iterations, we call such a type an \ntype{(n-2)}, or
\ntruncated{(n-2)}\footnote{The somewhat strange numbering, starting
  at $-2$ comes from homotopy theory, where they first considered
  groupoids without any higher structure to be $0$-truncated and then
  generalised backwards.}:

\begin{code}
ntruncated : NatMinusTwo -> Universe -> Universe
ntruncated minustwo  A = isContractible A
ntruncated (S n)     A = (x y : A) -> ntruncated n (Id A x y)
\end{code}

These truncation levels have the property that every \ntype{n} is also
an \ntype{(n+1)}, \ie |ntruncated| defines a filtration on the
universe of types.

The \emph{contractible} types are the types that are isomorphic to
|top| in the sense that a contractible type has an inhabitant that is
unique up to propositional equality. In section~\cref{sec:hit} we
will see examples of contractible types that have more than one
constructor.

Types of truncation level $-1$ are called \hprops. \ntypes{(-1)} are
either empty (|bottom|) or, if they are inhabited, contractible, hence
isomorphic to |top|. They can be interpreted as false and true
propositions. One can easily prove that \hprops satisfy the principle
of proof irrelevance:

\begin{code}
  proofIrrelevance : Universe -> Universe
  proofIrrelevance A = (x y : A) -> Id A x y
\end{code}

The converse also holds: if a type satisfies proof irrelevance, it is
an \hprop. Showing this is a bit more involved, but it is a nice
example of how one can proof things about equalities between
equalities.

\begin{code}
  piimplieshprop : (A : Universe) -> (p : proofIrrelevance A) -> isprop A
\end{code}

We need to show that for every |x y : A|, |x == y| is contractible: we
need to find a proof |c : x == y| and show that any other proof of |x
== y| is equal to |c|. An obvious candidate for |c| is |p x y|. To
show that |c == p x y|, we use based path induction on |c|, fixing the
|y|, so we need to prove that |refl == p y y|. Instead of doing this
directly, we first prove something more general:

\begin{code}
  lemma : (x y : A) (q : x == y) -> p x y == q circ p y y  
\end{code}

This can be done by based path induction on |q|, fixing |y|. The goal
then reduces to showing that |p y y == p y y|. Using the lemma we can
show that |p y y == p y y circ p y y|. Combining this with |p y y circ
refl| and the fact that |\ q -> p circ q| is injective for any |p|, we
get that |p y y == refl|.

The definition of \hprop via proof irrelevance fits the classical view
of propositions and their proofs: we only care about whether or not we
have a proof of a proposition and do not distinguish between two
proofs of the same proposition.

Another important case are the \ntypes{0}, also called \emph{\hsets},
which are perhaps the most familiar to programmers. These are the
types of which we have that any two inhabitants |x| and |y| are either
equal to eachother in a unique way, or are not equal, \ie \hsets are
precisely those types that satisfy \UIP. The simplest example of a
type that is a \hset, but not a \hprop is the type |Bool|:

\begin{code}
  data Bool : Universe where
    True : Bool
    False : Bool
\end{code}

In fact, most types one defines in Agda are \hsets. One characteristic
of \hsets is given by Hedberg's theorem \citep{hedberg}, which states
that every type that has decidable equality (\ie |(x y : A) -> x == y
+ (x == y -> bottom)|) also is an \hset. The only way to define a type
that is not an \hset in Agda, is to add extra propositional equalities
to the type by adding axioms. This is the subject of
\cref{sec:hit}.

\paragraph{Notation} Sometimes we will use the notation |A : hProp| to
indicate that |A| is a type that is an \hprop. In an actual
implementation |hProp| would be defined as |Sigma (A : Universe)
(istruncated minusone A)|. When we refer to |A|, we are usually not
interested in an inhabitant of the \sigmatype, but in the first field
of that inhabitant, \ie the |A : Universe|. The same holds for the
notation |A : hSet|.

\subsection{Truncations}
\label{sec:trunc}

It may happen that we sometimes construct a type of which the identity
types have too much structure, \eg it is a \ntype{2} but we want it to
be a \ntype{0}. In homotopy type theory, we have a way to consider a
type as though it were an \ntype{n}, for some |n| we have chosen
ourselves, the so called \ntruncation{n} of a type. Special cases that
are particularly interesting are the \ntruncation{(-1)}, \ie we force
something to be a \hprop, which is particularly useful when we want to
do logic, and \ntruncation{0}, \ie we force something to be a
\hset. The idea is that we add enough extra equalities to the type
such that the higher structure collapses. This can be done using
\hits~(\cref{sec:hit}). The general construction is rather involved
and not of much interest for the purposes of this thesis: we will only
encounter the \ntruncation{(-1)} and \ntruncation{0}.

\section{Higher inductive types}
\label{sec:hit}

We have seen a counterexample of a space in which the interpretation
of |K| and \UIP fails: a space with a hole in it. The question is then
if we can construct such counterexamples in the type theory
itself. Since we are asking for a type |A : Universe| for which there
is an inhabitant |x : A| with a term |p : Id A x x| \st |p == refl ->
bottom|, we know that we cannot do this is normal \MLTT without adding
axioms as this would violate the canonicity property.

\emph{\Hits} extend inductive types with the possibility add
\emph{path constructors} to the definition of a type: instead of
giving constructors for the points of a space, we may also give
constructors for paths between points, and paths between paths, and so
on. Using \hits we can now describe\footnote{This is not valid
  Agda. We can simulate \hits by adding (in this case) |loop| as a postulate
  and only exposing the elimination principles.} familiar spaces, such
as the circle (see also~\cref{fig:circle}):

\begin{code}
  data Circle : Universe where
    base : Circle
    
    loop : base == base
\end{code}

Apart from defining how we can construct equalities between
inhabitants of the type, we also need to specify how we can eliminate
inhabitants. Roughly speaking we need to ensure that all the points
get mapped in such a way that all the (extra) equalities are
respected. In the case of the circle this looks as follows (see
also~\cref{fig:hit_interval}):

\begin{code}
  Circlerec : {B : Set} 
       -> (b : B)
       -> (p : b == b)
       -> Circle -> B
\end{code}

with computation rule:

\begin{code}
  Circlerec b p base === b
\end{code}

We also need a computation rule for the paths, to witness that the
|loop| indeed gets mapped onto the specified path |p : b == b| by
|ap|:

\begin{code}
  ap (Circlerec b p) loop === p
\end{code}

It might seem a bit silly that we need to provide a path |b == b|, as
this type is always inhabited by |refl|. However, we sometimes do want
|p| to be different from |refl|: in order to write the identity
function on |Circle|, we also want |loop| to be preserved by this map.

Apart from a non-dependent elimination principle, we also need a
dependent version:

\begin{code}
  Circleind : {B : Circle -> Set}
          -> (b : B base)
          -> (p : transport B loop b == b)
          -> (x : Circle) -> B x
\end{code}

Using the dependent elimination principle, we can show that this type
violates \UIP, \ie we can prove that |loop == refl| does not hold. In
fact, the type |Id Circle base base| is isomorphic to the integers
|Int|, where transitivity maps to addition on integers
\citep{fundamentalgroup}. This might seem a bit strange, because at
first glance |Circle| seems to be a contractible type: we have only
have one constructor |base| and an equality |base == base|, so it
seems to fit the definition. However, trying to prove |(x : Circle) ->
x == base| will not work, as the only functions we can define in type
theory are \emph{continuous} functions. While it is true in homotopy
theory that for every point on the circle, we can find a path to the
base point, we cannot do so in a continuous way.

\begin{figure}
  \centering
  \begin{tikzpicture}[descr/.style={fill=white,inner sep=2pt}]
    \node[descr] (A) {|base|};

    \draw[snakeline] (A) arc[radius = 1.5cm, start angle=0, end angle=190] node[descr,above] {|loop|} arc[radius = 1.5, start angle=190, delta angle=160];
  \end{tikzpicture}
  \caption{The circle as a \hit}
  \label{fig:circle}
\end{figure}

If we add a path constructor connecting two points |x| and |y|, we do
not only get that specific path, but all the paths that can be
constructed from that path using transitivity and symmetry. If we
start out with a type with only two constructors |x| and |y|, we get a
type isomorphic to the booleans (see~\cref{fig:hit_bool}), a
\ntype{0}. Adding one path constructor |p : x == y| gives us the
interval (see~\cref{fig:hit_interval} and \cref{sec:interval}),
which is a contractible type (it is a \ntype{(-2)}) and hence
isomorphic to the unit type |top|. If we add yet another path
constructor |q : x == y|, we get a type isomorphic to |Circle|, which
is a \ntype{1}.

\begin{figure}[!htb]
\minipage{0.32\textwidth}
\begin{tikzpicture}
  \path[use as bounding box] (-1,-0.5) rectangle (10,0.5);
  \node (A) {|x|};
  \node (B) [right of=A] {|y|};
\end{tikzpicture}
\caption{Booleans}\label{fig:hit_bool}
\endminipage\hfill
\minipage{0.32\textwidth}
\begin{tikzpicture}
  \path[use as bounding box] (-1,-0.5) rectangle (10,0.5);
  \node (A) {|x|};
  \node (B) [right of=A] {|y|};
  \draw[snakeline, bend left=45] (A.20) to node {|p|} (B.160);
\end{tikzpicture}
\caption{Interval}\label{fig:hit_interval}
\endminipage\hfill
\minipage{0.32\textwidth}%
\begin{tikzpicture}
  \path[use as bounding box] (-1,-0.5) rectangle (10,0.5);
  \node (A) {|x|};
  \node (B) [right of=A] {|y|};
  \draw[snakeline, bend left=45] (A.20) to node {|p|} (B.160);
  \draw[snakeline, bend right=45] (A.340) to node [swap] {|q|} (B.200);
\end{tikzpicture}
\caption{Circle}\label{fig:hit_circle}
\endminipage
\end{figure}

\subsection{Coherence issues}

Equalities at different levels interact with eachother: if we add
equalities at one level, \eg paths between points, it may also
generate new paths at other levels, \eg new homotopies between paths
that previously did not exist. One example of this is
\ntruncation{(-1)}, or propositional truncation, via the following
\hit:

\begin{code}
  data proptruncate : (A : Universe) : Universe where
    inhabitant : A -> proptruncate A
    
    allpaths : (x y : proptruncate A) -> x == y
\end{code}

We have seen in~\cref{sec:truncations} that this type indeed yields
a proposition, as it satisfies proof irrelevance, since we have added
paths between all points |x| and |y|. This collapses all higher
structure of the original type |A : Universe|.

The converse can also happen: instead of collapsing the structure at
higher levels, we might gain new structure at those levels, which
sometimes may be undesirable. If this is the case, the resulting type
is not coherent enough. \emph{Coherence properties} are properties
that state that certain equalities between equalities must
hold. Suppose we want to consider words generated by some alphabet |A
: Set|. This can be done with the following type:

\begin{code}
  data FreeSemigroup (A : Set) : Universe where
    elem : A -> FreeSemigroup A
    binopname : FreeSemigroup A -> FreeSemigroup A -> FreeSemigroup A
\end{code}

Clearly, |FreeSemigroup A| is a set. Suppose we want |binopname| to be
associative, so we add the following path constructor:

\begin{code}
  assoc : {a b c : FreeSemigroup A} -> (a binop b) binop c == a binop (b binop c)
\end{code}

Adding these equalities breaks the \hset property. The coherence
property that we want to hold here is \uip. One example for which this
fails, is that the following diagram (the so called \emph{Mac Lane
  pentagon}) does not commute:

\begin{center}
  \begin{tikzpicture}[description/.style={fill=white,inner sep=2pt}]
    \matrix (m) [matrix of math nodes, 
                row sep=4.5em,
                column sep=3.5em,
                text height=1.5ex,
                text depth=0.25ex]
 { |((a binop b) binop c) binop d| & & & |(a binop (b binop c)) binop d| & |a binop ((b binop c) binop d)| \\
   |(a binop b) binop (c binop d)| & & &                                 & |a binop (b binop (c binop d))| \\ };

  \path[snakelin] (m-1-1) edge[decorate] node[auto]       {|ap (\ x -> x binop d) assoc|} (m-1-4);
  \path[snakelin] (m-1-4) edge[decorate] node[auto]       {|assoc|} (m-1-5);
  \path[snakelin] (m-1-1) edge[decorate] node[auto, swap] {|assoc|} (m-2-1);
  \path[snakelin] (m-2-1) edge[decorate] node[auto, swap] {|assoc|} (m-2-5);
  \path[snakelin] (m-1-5) edge[decorate] node[auto]       {|ap (\ x -> a binop x) assoc|} (m-2-5);

  \end{tikzpicture}
\end{center}

This shows us that the interaction of propositional equalities at the
different levels can be quite subtle. For this reason one often
truncates a \hit, to be sure that it is coherent enough, \eg that it
is really a \hset.

\subsection{Interval}
\label{sec:interval}
Another example of a space from homotopy theory is the interval. At
first glance this might seem like a rather uninteresting space to
study, as it is homotopy equivalent to the space that consists of one
point. The following presentation of the interval as a \hit has some
interesting consequences.

The interval $[0,1]$ can be seen, from a homotopy theory perspective,
as a space with two points, $0$ and $1$, and a path between them. As a
\hit, this can be presented as follows:

\begin{code}
  data Interval : Universe where
    zero  : Interval
    one   : Interval

    segment : zero == one
\end{code}

A map from |Interval| to some type |B : Universe| must map |zero| and
|one| to points in |a b : B| such that |a == b|:

\begin{code}
  Intervalrec : {B : Universe} 
       -> (b0 b1 : B)
       -> (p : b0 == b1)
       -> Interval -> B
\end{code}

with computation rules:

\begin{code}
    Intervalrec b0 b1 p zero  === b0
    Intervalrec b0 b1 p one   === b1

    ap (Intervalrec b0 b1 p) seg === p
\end{code}

Having an interval type means that we have a different way to talk
about equalities: any path |p : Id A x y| can be seen as a map |Interval ->
A|:

\begin{code}
  eqtointerval : {A : Universe} {x y : A} -> x == y -> Interval -> A
  eqtointerval {A} {x} {y} p i = Intervalrec {A} x y p i
\end{code}

The other way around can also be done:

\begin{code}
  intervaltoeq : {A : Set} -> (p : Interval -> A) -> (p zer) ≡ (p one)
  intervaltoeq p = ap p seg
\end{code}

Using this we can now manipulate propositional equalities in such a
way that we can prove function extensionality. Suppose two functions
|f g : A -> B| and a term |alpha : (x : A) -> f x == g x|. To remove
the dependency in the type, we can use |eqtointerval|: 

\begin{code}
  \ a -> eqtointerval (alpha a) : A -> Interval -> A
\end{code}

If we flip the arguments of that term, we get a function |Interval ->
A -> A|, which then can be turned into the desired |f == g|. The whole
term looks as follows:

\begin{code}
  ext : (A B : Universe) (f g : A -> B) (alpha : (x : A) -> f x == g x) -> f == g
  ext A B f g alpha = intervaltoeq (flip (\ a -> eqtointerval (alpha a)))
\end{code}

\section{Equivalence and univalence}
\label{sec:univalence}

\MLTT satisfies the property that everything you construct in the
theory is invariant under isomorphism. Consider for example the
definition of a monoid:

\begin{code}
  Monoid : Universe
  Monoid =  Sigma  (carrier    : Set) .
            Sigma  (unit       : carrier) .
            Sigma  (binopname  : carrier -> carrier -> carrier) .
            Sigma  (assoc      : (x y z : carrier) -> x binop (y binop z) == (x binop y) binop z) .
            Sigma  (unitleft   : (x : carrier) -> unit binop x == x) .
            Sigma  (unitright  : (x : carrier) -> x binop unit == x) . top
\end{code}

If we have two types |A B : Universe| with an isomorphism |f : A -> B|
and a proof |ma : Monoid A|, then it is straightforward to produce a
|Monoid B| using only |Monoid A| and the isomorphism |f|, by applying
|f| and |f inv| to the fields of |ma : Monoid A|. The resulting
instance of |Monoid B| can then also be shown to be isomorphic to
|ma|. This is similar to the situation with |transport| and |apd|: if
we have a proof |p : A == B|, then we can use |transport| to create an
inhabitant of |Monoid B| using |ma| and |p|. We can then prove that
the resulting instance of |Monoid B| is propositionally equal to |ma|
using |apd|. However, writing |transport| and |apd| functions that
works with isomorphisms instead of propositional equalities will not
work in \MLTT, as we cannot access the information about how the types
are constructed, to figure out where the isomorphisms have to be
applied.

\emph{Univalence} gives us an internal account of this principle. It
roughly says that isomorphic types are propositionally equal, so all
the tools to manipulate propositional equalities now also can be
applied to isomorphisms. But before we can formulate the univalence
axiom, we need to introduce some new terminology. We can define the
notion of a function |f : A -> B| being an isomorphism as follows:

\begin{code}
  isIsomorphism : {A B : Universe} (f : A -> B) -> Universe
  isIsomorphism f = Sigma (B -> A) (\ g ->  (x : B) -> f (g x) == x times 
                                            (x : A) -> g (f x) == x)
\end{code}

We want the type |isIsomorphism f| to be an \hprop, which it is when
|A| and |B| are \hsets, but it can fail to be an \hprop when |A| and
|B| are \ntypes{n} with $n > 0$. Instead we introduce the notion of
\emph{equivalence} \index{equivalence}:

\begin{code}
  isEquivalence : {A B : Universe} (f : A -> B) -> Universe
  isEquivalence f =  Sigma (B -> A) (\g -> (x : B) -> f (g x) == x)
              times  Sigma (B -> A) (\h -> (x : a) -> h (f x) == x)
\end{code}

This definition does satisfy the property that |isEquivalence f| can
hold in at most one way (up to propositional equality). We can also
show that |isIsomorphism f -> isEquivalence f| and |isEquivalence f ->
isIsomorphism f|, \ie the two types are \emph{coinhabited}.

Using this definition of what it means to be an equivalence, we can
define the following relation on types:

\begin{code}
  equivrel : {A B : Universe} -> Universe
  A equivrel B = Sigma (A -> B) (\f -> isEquivalence f)
\end{code}

It is easy to show that if two types are propositional equal, then
they are also equivalent, by transporting along |\ X -> X|:

\begin{code}
  equalimpliesequiv : (A B : Universe) -> A == B -> A equiv B
\end{code}

A universe of types is called a \emph{univalent} universe if
equivalences and propositional equalities are equivalent, \eg in the
case of the universe |Universe|, this would look as follows:

\begin{code}
  (A B : Universe) -> isEquivalence (equalimpliesequiv A B)
\end{code}

It has been shown that in a popular model of homotopy theory, the
category of simplicial sets, the universe of spaces is indeed
univalent \citep{univalence}. One important consequence of this
property is that we have the following:

\begin{code}
  ua : (A B : Universe) -> A equiv B -> A == B
\end{code}

which should satisfy the following computation rule:

\begin{code}
  uacomp : {A B : Universe} 
           {f : A -> B}
           {eq : isEquivalence f}
           {x : A} 
      ->   transport (\X -> X) (ua A B) x == f x
\end{code}

Univalence means that we can now generalise the |Monoid| example
mentioned to any |B : Universe -> Universe|, since |transport| and
|apd| can now be used for isomorphisms as well.

If we have univalence, the universe of \hsets is not a \hset, as is
exhibited by the isomorphisms |Bool -> Bool|. There are two different
such isomorphisms: |id| and |not|. Using |ua|, these isomorphisms map
to different proofs of |Bool == Bool|. |id| maps to |refl| and |not|
to something that is not equal to |refl|. This means that the universe
of \hsets violates \UIP. It can be shown to be a \ntype{1} instead. In
fact, the universe of \ntype{n} is not an \ntype{n} but an
\ntype{(n+1)}~\citep{ntypes}.

\section{Implementation}
\label{sec:implementation}

Currently, the way to ``implement'' \hott, \ie \MLTT with univalence
and \hits, is to take an existing implementation of \MLTT such as Agda
or Coq and add univalence and the computation rules for univalence as
axioms. This approach is sufficient when we want to do formal
mathematics, since in that case we only are interested in type
checking our developments. If we want to run the program, terms that
make use of univalence then get stuck as soon as it hits an axiom.

The computational interpretation of univalence is one the biggest open
problems of \hott. Several attempts have been made at a computation
interpretation for truncated versions of \hott: \citet{canonicity}
show that if we restrict ourselves to a univalent universe of \hsets,
we can achieve canonicity. The article however does not present a
decidability result for type checking. \citet{univalencefree}
internalise \hott in Coq and also restrict themselves to the
two-dimensional case, \ie \UIP need not hold, but equalities between
equalities are unique.

A question one might ask is why we cannot add an extra constructor to
the definition of |Id| for univalence. Doing this means that we end up
with a different elimination principle: if we want to prove something
about propositional equalities, we also need to account for the case
when it was proven using univalence. Apart from making it more
difficult to prove things about propositional equalities, it is also
has some undesirable properties. We can prove that a proof of equality
constructed using the univalence constructor is never equal to
|refl|. There are cases in which we want this to be the case, \eg when
we apply univalence to the identity isomorphism.

The conjecture is that full canonicity will probably not hold, but
only canonicity ``up to propositional equality'': it is conjectured
\citep{canonicityconj} that there is a terminating algorithm that
takes an expression |t : Nat| and produces a canonical term |t' : Nat|
along with a proof that |t == t'|. The proof of equality may use the
univalence axiom.

\hits can also be implemented by adding axioms for the extra
paths. The elimination principles also can be implemented by adding
the computation rules for paths as axioms. One then has to be careful
to not do pattern matching on \hits. In Agda one can hide things in
such a way that one can export an elimination principle in which the
computation rules for the points hold definitionally and the other
rules propositionally, while also making direct pattern matching
impossible from any other module that imports the module containing
the \hit \citep{hit-agda}. However, one still has to be careful not to
use the absurdity pattern, |()|, when dealing with \hits, as that can
be used to prove |bottom| \citep{unsound}.
