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
rationals |Rat| constructed from the integers as follows: we quotient
out |Int times Int| by the relation |(a,b) ~ (c, d)| if and only if
|ad = bc|.

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
binary search trees, |BST : Universe|, along with a relation |rel :
BST -> BST -> hProp| \st |x ~ y == top| if and only if |x| and |y| are
comprised of the same key-value pairs, and |x ~ y == bottom|
otherwise. Suppose we have an insertion operation |insert :
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
along with |rel|, is called a \emph{setoid}. Its disadvantages are
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
dictionary. 

The question then is whether such a construction always exists: can we
define a type that is in some sense equal to the quotient?  To be able
to answer this question, we need to define what it means to be a
quotient and what notion of equality we want.

\cite{definablequotients} define a quotient, given a setoid |(A,rel)| as
a type |Q : Universe| with the following:

\begin{itemize}
\item a projection function |[_] : A -> Q|
\item a function |sound : (x y : A) -> x ~ y -> [ x ] == [ y ]|
\item an elimination principle: 
  \begin{code}
    Qelim :  (B : Q -> Universe)
             (f : (x : A) -> B [ x ])
             ((x y : A) (p : x ~ y) -> (transport (sound x y p) (f x)) == f y)
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
isomorphism, with respect to the relation |rel| on |A| instead of
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
  data Quotient (A : Universe) (rel : A -> A -> hProp) : Universe where
    [_] : A -> Quotient A rel

    sound : (x y : A) -> x ~ y -> [ x ] == [ y ]
\end{code}

To write a function |Quotient A rel -> B| for some |B : Universe|, we
need to specify what this function should do with values |[ x ]| with
|x : A|. This needs to be done in such a way that the paths added by
|sound| are preserved. Hence the recursion principle lifts a function
|f : A -> B| to |fsnake : Quotient A rel -> B| given a proof that it
preserves the added paths:

\begin{code}
  quotientrec :   (A : Universe) (rel : A -> A -> hProp)
                  (B : Universe)
                  (f : A -> B)
                  ((x y : A) -> x ~ y -> f x == f y)
                  Quotient A rel -> B
\end{code}

If we generalise this to the dependent case, we get something that
fits perfectly in the requirement of a type being a quotient given
earlier:

\begin{code}
    quotientind :  (A : Universe) (rel : A -> A -> hProp)
                   (B : Quotient A rel -> Universe)
                   (f : (x : A) -> B [ x ])
                   ((x y : A) (p : x ~ y) -> (transport (sound x y p) (f x)) == f y)
                   (q : Quotient A rel) -> B q
\end{code}

Note that we do not require a proof of |rel| being an equivalence
relation. Instead, the quotient should be read as identifying
inhabitants by the smallest equivalence relation generated by |rel|.

\subsection{Binary operations on quotients}

We have seen how to lift a function |f : A -> B| to |fsnake : Quotient
A rel B| given a proof of |(x y : A) -> x ~ y -> f x == f y|, using
|quotientrec|. Suppose we want to write a binary operation on
quotients, then we want to have a way to lift a function |f : A -> A
-> B| satisfying |(x y x' y' : A) -> x ~ x' -> y ~ y' -> f x y == f x'
y'| to |fsnake : Quotient A rel -> Quotient A rel -> B|. 

Let us fix |A|, |rel| and |B|, so that we do not have to pass them
around explicitly. Our goal is to write a term of the following type:

\begin{code}
  quotientrec2 :  (f : A -> A -> B)
                  (resp : (x y x' y' : A) -> x ~ x' -> y ~ y' -> f x y == f x' y')
                  Quotient A rel -> Quotient A rel -> B
\end{code}

We will first use |quotientrec| to lift the left argument, \ie we
want to produce a function of type |Quotient A rel -> A -> B| and then
use |quotientrec| on this function to achieve our goal. So let us try
writing the function that lifts the left argument:

\begin{code}
  liftleft : (f : A -> A -> B) 
              (resp : (x y x' y' : A) -> x ~ x' -> y ~ y' -> f x y == f x' y')
              Quotient A rel -> A -> B
  liftleft f resp q = quotientrec f goal0 q
\end{code}

where |goal0 : (x x' : A) -> x ~ x' -> f x == f x'|. Since we have
quotient types, we also have function extensionality\footnote{We can
  quotient |Bool| by the trivial relation. Using this, we can perform
  essentially the same proof of function extensionality as the one
  that uses the interval type.}, hence we can solve this by proving
|(x x' y : A) -> x ~ x' -> f x y == f x' y|. However, to be able to
use |resp|, we also need a proof of |y ~ y|, so if we assume that
|rel| is an equivalence relation, we can solve this goal.

We can now fill in |liftleft| in the definition of |quotientrec2|:

\begin{code}
  quotientrec2 f resp q q' = quotientrec (liftleft f resp q) goal1 q'
\end{code}

where |goal1 : (y y' : A) → y ~ y' → liftleft f resp q y == liftleft
f resp q y'|, which can be proven using |quotientind|. We then only
have to consider the case where |q| is of the form |[ a ]| for some |a
: A|. In that case, |liftleft f resp q y| reduces to |f a y| and
|liftleft f resp q y'| to |f a y'|. Since we have |y ~ y'|, we again
need |rel| to be reflexive to get |a ~ a| so we can use |resp|. We now
have the following:

\begin{code}
  goal1 : (y y' : A) → y ~ y' → liftleft f resp q y == liftleft f resp q y'
  goal1 = \ y y' r -> 
             quotientind  (\ w -> liftleft f resp w y == liftleft f resp w y')
                          (\ a -> resp a y a y' (relrefl a) r)
                          goal2
                          q
\end{code}

Of course, we have still to prove that this respects the quotient
structure on |q|:

\begin{code}
  goal2 : (p : x ~ x')
          transport (sound x x' p) (resp x y x y' (relrefl x) r) ==
          resp x' y x' y' (relrefl x') r
\end{code}

Note that this equality is of type |Id (Id B (f x y) (f x y'))|, which
means that if |B| happens to be a \hset, we can appeal to \UIP and we
are done.

\todoi{Note that it's interesting to see that we need to assume these
  extra properties of our relation |rel|, even though we don't really
  work with that relation, but the smallest equivalence relation
  generated by |rel|.}

\subsection{Coherence issues}

\todoi{In the HoTT book, they specifically mention the quotient should
  be the \ntruncation{0}. Why do we need this? Can we find a \hset |A|
  with a relation |rel : A -> A -> Prop| \st |Quotient A rel| is not a
  \hset.}

\todoi{If we use the \ntruncation{0}, then we can also easily prove
  that |[_]| preserves all the equivalence relation structure:
  reflexivity of the one structure gets mapped to the other
  reflexivity, same for symmetry. Transitivity also gets mapped in the
  right way, \ie things commute.}


\section{Views on abstract types}

\begin{itemize}
\item Why do we need abstract types/views?
\item Define how we can describe an abstract type: nested sigma types.
\item Example: sequence.
\item We need more than just the types of the operations: we want some
  behavioural specs as well.
\item We can give this in the form of a reference implementation, in
  this case ListSeq.
\item If we have another implementation, we want the other type to be
  isomorphic and implement the same operations.
\item We also want these operations to respect the isomorphism.
\item Example of isomorphic views on sequences: ListSeq versus some OtherSeq.
\item Show what the equality OtherSeq == ListSeq entails: how can we
  reason with nested sigma types? What does this equality mean?
\item Show how things like map-fusion carry over from ListSeq to
  OtherSeq.
\item Example of non-isomorphic views: ListSeq vs. JoinListSeq.
\item For the specification (the equality), we can work with quotient
  types.
\item Mention that if we have a section-retraction, we do not need the
  quotient type structure directly, but have an alternative
  (equivalent) formulation that works more nicely.
\item Show how we can carry over the results, such as proving that it
  respects the section-retraction, from working with the JoinListSeq
  to the JoinListSeq/~ stuff.
\end{itemize}

\section{Conclusion}

\label{sec:views}

