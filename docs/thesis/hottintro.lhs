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
\emph{path space} \index{path space} of |X|, we again can look at the
paths. Suppose we have two paths |p, q : [0,1] -> X| with the same
begin and end points, then a path between |p| and |q|, called a
\emph{homotopy}, is a continuous function |gamma : [0,1] -> [0,1] ->
X| where |gamma 0 = p| and |gamma 1 = q|
(see~\autoref{fig:homotopy}). Of course, we can also look at
homotopies in these path spaces, and homotopies between these higher
homotopies, ad infinitum.

\begin{figure}
  \centering
  \begin{tikzpicture}
    \node[draw,shape=circle,minimum size=0.02cm,fill=black,label=below:|x|] (A) {};
    \node[draw,shape=circle,minimum size=0.02cm,fill=black,label=below:|y|] (B) [right of=A] {};
    \draw[snakeline, bend left=45] (A.20) to node {|p|} (B.160);
    \draw[snakeline, bend right=45] (A.340) to node [swap] {|q|} (B.200);

  \end{tikzpicture}
  \caption{Homotopy between paths |p| and |q|}
  \label{fig:homotopy}
\end{figure}

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
  the way to do homotopy theory according to Grothendieck and Quillen?}

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

Another important property of propositional equality is that it is a
congruence relation, \ie we have a term with the following type:
\todoi{Is this congruence? What about |f == g -> f x == g x|?}

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

The resulting equality is an equality of between points in |B y|.

\subsection{Difficulties of identity types}

Even though at first glance the identity types have the right
structure: they form equivalence relations on types, there are still
some things lacking and some things that are rather strange.

\paragraph{Function extensionality}
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

\paragraph{Uniqueness of identity proofs}
\label{sec:uip}

The canonicity property implies that if, in the empty context, we have
two identity proofs |p q : Id A x y|, these proofs are both |refl|,
hence they are equal to one another. One would expect that it is
possible to prove this inside \MLTT. Using dependent pattern matching,
we can easily prove this property in Agda, called \UIP
\index{uniqueness of identity proofs}:

\begin{code}
UIP : (A : Universe) (x y : A) (p q : Id A x y) -> Id (Id A x y) p q
UIP A x dotx refl refl = refl
\end{code}

Proving this using~|J| instead of dependent pattern matching to prove
\UIP has remained an open problem for a long time and has eventually
been shown to be impossible \citep{groupoidinterpretation}.

\todoi{Note that this is different from proving that function
  extensionality cannot be proven: that one uses the operational
  semantics whereas for the non-provability of \UIP we need other
  semantics, namely the groupoid interpretation, which eventually led
  to the homotopy interpretation.}

\todoi{Note that this means that dependent pattern matching is a
  non-conservative extension over \MLTT.}

As a complement to~|J|, Streicher introduced the induction
principle~|K|:

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

\todoi{Note that we will show examples of types violating \UIP and |K|
  later on and how |K| compares to |J|.}

\section{Homotopy interpretation}
\label{sec:homotopyinterpretation}

\todoi{Recall the table}

\homotopyinterpretation

\todoi{Recall that homotopy had this \inftygrpd structure}

In \cite{groupoidinterpretation}, the authors note that types have a
groupoid structure. We have a notion of composition of proofs of
propositional equality: the term |trans : Id A x y -> Id A y z -> Id A
x z|, as such we will use the notation |_ circ _| instead of
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

The important thing to note is what kind of equalities we were talking
about: associativity, etc. all hold up to propositional equality one
level higher. The identity type |Id A x y| is of course a type and
therefore has a groupoid structure of its own. Every type gives rise
to a tower of groupoids that can interact with eachother. These
structures, called \inftygrpds, also show up in homotopy theory, hence
we have the correspondence between types and spaces as mentioned
earlier.

\todoi{Explain what this interpretation brings us}

\todoi{Gives more explanation, reasons to see why it is the right
  definition.}

\todoi{Gives us a way to do homotopy theory. citations?}

\todoi{Gives us a way to explain things such as the \UIP and the |K|
  versus |J| thing, in pictures.}

\todoi{Note that function extensionality does hold in the homotopy
  interpretation.}

\todoi{Inspires new additions to the type theory: \hits and
  univalence.}

\subsection{Interpreting \UIP and |K|}

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
\caption{With |J| we have the freedom to move the end point around.}
\end{figure}

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
\caption{With |K|, we are restricted to loops}
\end{figure}

\todoi{Explain things, using pictures and whatever}

\todoi{Give counterexamples}

\section{\ntypes{n} and truncations}
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
unique up to propositional equality. In section~\autoref{sec:hit} we
will see examples of contractible types that have more than one
canonical element.

Types of truncation level $-1$ are called \hprops. \ntypes{(-1)} are
either empty (|bottom|) or, if they are inhabited, contractible, hence
isomorphic to |top|. One can easily prove that \hprops satisfy the
principle of proof irrelevance:

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
show that |c == p x y|, we use (one-sided) induction on |c|, fixing
the |y|, so we need to prove that |refl == p y y|. Instead of doing
this directly, we first prove something more general:

\begin{code}
  lemma : (x y : A) (q : x == y) -> p x y == q circ p y y  
\end{code}

This can be done by one-sided induction on |q|, fixing |y|. The goal
then reduces to showing that |p y y == p y y|. Using the lemma we can
show that |p y y == p y y circ p y y|. Combining this with |p y y circ
refl| and the fact that |\ q -> p circ q| is injective for any |p|, we
get that |p y y == refl|.

The definition of \hprop fits the classical view of propositions and
their proofs: we only care about whether or not we have a proof of a
proposition and do not distinguish between two proofs of the same
proposition.

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
of \hsets is given by Hedberg's theorem \todo{Cite Nicolai Kraus
  paper}, which states that every type that has decidable equality
(\ie |(x y : A) -> x == y + (x == y -> bottom)|) also is an \hset. The
only way to define a type that is not an \hset in Agda, is to add
extra propositional equalities to the type by adding axioms. This is
the subject of \autoref{sec:hit}.

\paragraph{Notation} Sometimes we will use the notation |A : Prop| to
indicate that |A| is a type that is an \hprop. In an actual
implementation |Prop| would be defined as |Sigma (A : Universe)
(is-truncated minusone A)|. When we refer to |A|, we are usually not
interested in an inhabitant of the \sigmatype, but in the first field
of that inhabitant, \ie the |A : Universe|. The same holds for the
notation |A : Set|.

\subsection{Truncations}
\label{sec:trunc}

It may happen that we sometimes construct a type of which the identity
types have too much structure, \eg it is a \ntype{2} but we want it to
be a \ntype{0}. In homotopy type theory, we have a way to consider a
type as though it were an \ntype{n}, for some |n| we have chosen
ourselves, the so called \ntruncation{n} of a type. Special cases that
are particularly interesting are the \ntruncation{(-1)}, \ie we force
something to be a \hprop, which is particularly useful when we
want to do logic, and \ntruncation{0}, \ie we force something to be a
\hset. The idea is that we add enough extra equalities to the type
such that the higher structure collapses. This can be done using
\hits~(\autoref{sec:hit}). The general construction is rather involved
and not of much interest for the purposes of this thesis.


\section{Higher inductive types}
\label{sec:hit}

\todoi{We've seen counterexamples of \UIP, but how do we define such
  examples in the type theory itself?}

\todoi{Example: circle. Definition plus eliminator.}

\begin{figure}
  \centering
  \begin{tikzpicture}
    \node (A) {|base|};
    \draw[snakeline] (A) arc (0:350:1.5cm) node[above] {|loop|};
  \end{tikzpicture}
  \caption{The circle as a \hit}
  \label{fig:homotopy}
\end{figure}


\todoi{Why does this violate \UIP: is |loop| really different from
  |refl|? Why is it not contractible?}

\todoi{Things are not entirely trivial with respect to their identity
  types: Bool -> Interval -> Circle figure. (Set -> Contractible -> 1-type)}
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

We have seen in~\autoref{sec:truncations} that this type indeed yields
a proposition, as it satisfies proof irrelevance. It collapses all
higher structure of the original type |A : Universe|.

The converse can also happen: instead of collapsing the structure at
higher levels, we might gain new structure at those levels, which
sometimes may be undesirable. Suppose we want to consider words
generated by some alphabet |A : Set|. This can be done with the
following type:

\begin{code}
  data FreeSemigroup : (A : Set) : Universe where
    elem : A -> FreeSemigroup A
    binopname : FreeSemigroup A -> FreeSemigroup A -> FreeSemigroup A
\end{code}

Clearly, |FreeSemigroup A| is a set. Suppose we want |binopname| to be
associative, so we add the following path constructor:

\begin{code}
  assoc : {a b c : FreeSemigroup A} -> (a binop b) binop c == a binop (b binop c)
\end{code}

Adding these equalities breaks the set property: the following diagram
(the so called \emph{Mac Lane pentagon} \todo{cite}) does not commute:

\begin{center}
  \begin{tikzpicture}
    \node (A)              {|((a binop b) binop c) binop d|};
    \node (B) [right of=A] {|(a binop (b binop c)) binop d|};
    \node (C) [right of=B] {|a binop ((b binop c) binop d)|};
    \node (D) [below of=A] {|(a binop b) binop (c binop d)|};
    \node (E) [below of=C] {|a binop (b binop (c binop d))|};
    \draw[snakeline] (A) to node {|ap (\ x -> x binop d) assoc|} (B);
    \draw[snakeline] (B) to node {|assoc|} (C);
    \draw[snakeline] (A) to node {|assoc|} (D);
    \draw[snakeline] (C) to node {|ap (\ x -> a binop x) assoc|} (E);
    \draw[snakeline] (D) to node {|assoc|} (E);
  \end{tikzpicture}
\end{center}

\todoi{Something about \hits not being trivial, there's a lot of
  interaction between things that is quite subtle. In fact, you want
  it to be subtle.}

\subsection{Interval}
For example, the interval can be seen as two points and a path
connecting these two points, which in pseudo-Agda would look like:

\begin{code}
  data Interval : Universe where
    zero  : Interval
    one   : Interval

    segment : zero == one
\end{code}

\todoi{Elimination principle}

\todoi{Interval implies fun ext}

\todoi{Mention implementation hack for Agda}

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
            Sigma  (assoc      : (x y z : carrier) -> x binop (y binop z) == (x bin op y) binop z) .
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
using |apd|. However, writing |transport| and |apd| function that
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

The \emph{univalence axiom} then tells us that equivalences and
propositional equalities are equivalent:

\begin{code}
  Univalence : (A B : Universe) -> isEquivalence (equalimpliesequiv A B)
\end{code}

One important consequence of this axiom is that we have the following:

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
mentioned, since |transport| and |apd| can now be used for
isomorphisms as well.

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
or Coq and adding univalence and the computation rules for univalence
as axioms. This approach is sufficient when we want to do formal
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
the \hit \citep{hit-agda}. \todoi{Mention inconsistency result.}

Since dependent pattern matching is not a conservative extension of
\MLTT and in general incompatible with \hott, we have to use the
\verb+--without-K+ flag for our Agda code, to ensure that we aren't
pattern matching too liberally. The assumption is that all code
written using pattern matching that passes the \verb+--without-K+
check can be rewritten using only elimination principles.

A question one might ask is whether we cannot add an extra constructor
to the definition of |Id| for univalence. Doing this means that we end
up with a different elimination principle: if we want to prove
something about propositional equalities, we also need to account for
the case when it was proven using univalence. Apart from making it
more difficult to prove things about propositional equalities, it is
also not clear if the resulting type has the right properties to be
called an equality, if we look at its interpretation in some model.