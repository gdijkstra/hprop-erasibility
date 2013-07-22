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

\newpage

\section{Quotient types}
\label{sec:quots}

In mathematics, one way to construct new sets is to take the
\emph{quotient} of a set $X$ by an equivalence relation $R$ on that
particular set. The new set is formed by regarding all elements $x, y
\in X$ \st $xRy$ as equal. An example of a quotient set is the set of
rationals $\mathbb{Q}$ constructed from the integers as follows: we
quotient out $\mathbb{Z} \times \mathbb{Z}$ by the relation $(a, b) \sim
(c, d)$ if and only if $ad = bc$.

In ordinary \MLTT, such a construction is not present.

\todoi{Bruggetje hier dat we het nog steeds over quotients hebben.}

In programming, it often happens that we have defined a data type that
has more structure than we want to expose. This situation typically
occurs when we want to encode our data in such a way that certain
operations on the data can be implemented more efficiently. An example
of this is implementing a dictionary with a binary search tree: there
are multiple binary search trees that represent the same dictionary,
\ie contain the same key-value pairs. If we pass two different trees
representing the same dictionary to an operation, we want the
operation to yield the same results.

To make the above more precise, suppose we have defined a data type of
binary search trees, |BST : Universe|, along with a relation |_~_ :
BST -> BST -> Universe| \st |x ~ y == top| if and only if |x|
and |y| are comprised of the same key-value pairs, and |x ~ y ==
bottom| otherwise. Suppose we have an insertion operation |insert :
KeyValuePair -> BST -> BST| and a lookup function |lookup : Key -> BST
-> Maybe Value|. We can formulate the properties that should hold:

\begin{itemize}
\item |(a : KeyValPair) (x y : BST) -> x ~ y -> insert a x ~ insert a y|
\item |(a : Key) (x y : BST) -> x ~ y -> lookup a x == lookup a y|
\end{itemize}

Note that for insertion, returning the same results means that we want
them to represent the same dictionary: it is perfectly allowed to
return differently balanced binary search trees. For |lookup|, we want
the results to be propositionally equal, as we do not have any other
relation available that holds on the result type, |Maybe Value|.

A type that comes equipped with an equivalence relation, such as |BST|
along with |_~_|, is called a \emph{setoid}. Its disadvantages are
that we have to formulate and check the properties ourselves: there is
no guarantee that a function out of a setoid respects the relation
from the setoid. As can be seen in the binary search tree example, we
have to be careful to use the right relation (propositional equality
or the setoid's equivalence relation) when we want to talk about two
inhabitants being the same. \Hott provides us with the machinery,
namely \hits, to enrich the propositional equality of a type, so we
can actually construct a new type in which propositional equality and
the provided equivalence relation coincide.

\subsection{Do we need quotients?}
\label{sec:defquotient}

Before we look at the quotient type construction with \hits, we will
determine whether we actually need such a thing. In the case of the
dictionary example, we might consider making the |BST| data type more
precise \st the only inhabitants are trees that are balanced in a
certain way, so we do have a unique representation for every
dictionary. One way to do this is to use nested data
types. \todo{citation needed}

The question then is whether such a construction always exist: can we
define a type that is in some sense equal to the quotient. To be able
to answer this question, we need to define what it means to be a
quotient and what notion of equality we want.

\cite{definablequotients} define a quotient, given a setoid |(A,_~_)| as
a type |Q : Universe| with the following:

\begin{itemize}
\item a projection function |[_] : A -> Q|
\item a function |sound : (x y : A) -> x ~ y -> [ x ] == [ y ]|
\item an elimination principle: 
  \begin{code}
    Q-elim :  (B : Q -> Universe)
              (f : (x : A) -> B [ x ])
              ((x y : A) (p : x ~ y) -> (transport (sound x y p) (f x)) ≡ f y)
              (q : Q) -> B q
  \end{code}
\end{itemize}

A quotient is called definable if we have a quotient |Q| along with
the following:

\begin{itemize}
\item |emb : Q -> A|
\item |complete : (a : A) -> emb [ a ] ~ a|
\item |stable : (q : Q) -> [ emb q ] == q|
\end{itemize}

We can view these requirements as having a proof of |[_]| being an
isomorphism, with respect to the relation |_~_| on |A| instead of
propositional equality.

The result of \cite{definablequotients} is that there exist quotients
that are not definable with one example being the real numbers
constructed using the usual Cauchy sequence method.

\todoi{Mention that we can conclude that adding quotients via HITs
  does not make things definable, but we no longer have to choose
  between the different equality relations as we have with the setoid
  approach.}

\subsection{Quotients as a \hit}

Using \hits, we can define the quotient of a type by a relation as
follows:

\begin{code}
  data Quotient (A : Universe) (_~_ : A -> A -> Universe) : Universe where
    [_] : A -> Quotient A _~_

    sound : (x y : A) -> x ~ y -> [ x ] == [ y ]
\end{code}

To write a function |Quotient A _~_ -> B| for some |B : Universe|, we
need to specify what this function should do with values |[ x ]| with
|x : A|. This needs to be done in such a way that the paths added by
|sound| are preserved. Hence the recursion principle lifts a function
|f : A -> B| to |fsnake : Quotient A _~_ -> B| given a proof that it
preserves the added paths:

\begin{code}
  Quotient-rec :  (A : Universe) (_~_ : A -> A -> Universe)
                  (B : Universe)
                  (f : A -> B)
                  ((x y : A) -> x ~ y -> f x == f y)
                  Quotient A _~_ -> B
\end{code}

with elimination principle:

\begin{code}
    Quotient-elim :  (A : Universe) (_~_ : A -> A -> Universe)
                     (B : Quotient A _~_ -> Universe)
                     (f : (x : A) -> B [ x ])
                     ((x y : A) (p : x ~ y) -> (transport (sound x y p) (f x)) ≡ f y)
                     (q : Quotient A _~_) -> B q
\end{code}

which means that for any type |A| with |_~_ : A -> A -> Universe|, the
type |Quotient A _~_| is a quotient by the definition given in~\ref{sec:defquotient}.

\todoi{Note that the relation need not be an equivalence relation,
  since we effectively mod out by the smallest equivalence relation
  generated by this relation.}

\newpage

\subsection{Binary operations on quotients}

We have seen how to lift a function |f : A -> B| to |fsnake : Quotient
A _~_ B| given a proof of |(x y : A) -> x ~ y -> f x == f y|, using
|Quotient-rec|. Suppose we want to write a binary operation on
quotients, then we want to have a way to lift a function |f : A -> A
-> B| satisfying |(x y x' y' : A) -> x ~ x' -> y ~ y' -> f x y == f x'
y'| to |fsnake : Quotient A _~_ -> Quotient A _~_ -> B|. 

Let us fix |A|, |_~_| and |B|, so that we do not have to pass them
around explicitly. Our goal is to write a term of the following type:

\begin{code}
  Quotient-rec-2 :  (f : A -> A -> B)
                    (resp : (x y x' y' : A) -> x ~ x' -> y ~ y' -> f x y == f x' y')
                    Quotient A _~_ -> Quotient A _~_ -> B
\end{code}

We will first use |Quotient-rec| to lift the left argument, \ie we
want to produce a function of type |Quotient A _~_ -> A -> B| and then
use |Quotient-rec| on this function to achieve our goal. So let us try
writing the function that lifts the left argument:

\begin{code}
  lift-left : (f : A -> A -> B) 
              (resp : (x y x' y' : A) -> x ~ x' -> y ~ y' -> f x y == f x' y')
              Quotient A _~_ -> A -> B
  lift-left f resp q = Quotient-rec f goal0 q
\end{code}

where |goal0 : (x x' : A) -> x ~ x' -> f x == f x'|. Since we have
quotient types, we also have function extensionality\footnote{We can
  quotient |Bool| by the trivial relation. Using this, we can perform
  essentially the same proof of function extensionality as the one
  that uses the interval type.}, hence we can solve this by proving
|(x x' y : A) -> x ~ x' -> f x y == f x' y|. However, to be able to
use |resp|, we also need a proof of |y ~ y|, so if we assume that
|_~_| is an equivalence relation, we can solve this goal.

We can now fill in |lift-left| in the definition of |Quotient-rec-2|:

\begin{code}
  Quotient-rec-2 f resp q q' = Quotient-rec (lift-left f resp q) goal1 q'
\end{code}

where |goal1 : (y y' : A) → y ~ y' → lift-left f resp q y ≡ lift-left
f resp q y'|, which can be proven using |Quotient-ind|. We then only
have to consider the case where |q| is of the form |[ a ]| for some |a
: A|. In that case, |lift-left f resp q y| reduces to |f a y| and
|lift-left f resp q y'| to |f a y'|. Since we have |y ~ y'|, we again
need |_~_| to be reflexive to get |a ~ a| so we can use |resp|. We now
have the following:

\begin{code}
  goal1 : (y y' : A) → y ~ y' → lift-left f resp q y ≡ lift-left f resp q y'
  goal1 = \ y y' r -> Quotient-ind  (\ w -> lift-left f resp w y ≡ lift-left f resp w y')
                                    (\ a -> resp a y a y' (~-refl a) r)
                                    goal2
                                    q
\end{code}

Of course, we have still to prove that this respects the quotient
structure on |q|:

\begin{code}
  goal2 : (p : x ~ x')
          transport (sound x x' p) (resp x y x y' (~-refl x) r) ==
          resp x' y x' y' (~-refl x') r
\end{code}

Note that this equality is of type |Id (Id B (f x y) (f x y'))|, which
means that if |B| happens to be a \hset, we can appeal to \UIP and we
are done.

\todoi{Note that it's interesting to see that we need to assume these
  extra properties of our relation |_~_|, even though we don't really
  work with that relation, but the smallest equivalence relation
  generated by |_~_|.}

\subsection{Coherence issues}

\todoi{In the HoTT book, they specifically mention the quotient should
  be the \ntruncation{0}. Why do we need this? Can we find a \hset |A|
  with a relation |_~_ : A -> A -> Prop| \st |Quotient A _~_| is not a
  \hset.}

\todoi{If we use the \ntruncation{0}, then we can also easily prove
  that |[_]| preserves all the equivalence relation structure:
  reflexivity of the one structure gets mapped to the other
  reflexivity, same for symmetry. Transitivity also gets mapped in the
  right way, \ie things commute.}


\section{Views on abstract types}
\label{sec:views}

