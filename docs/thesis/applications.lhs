\chapter{Applications of homotopy type theory}
\label{chap:applications}

In \cref{chap:hottintro} we introduced \hott and the two extensions
to \MLTT it brings us: univalence and \hits. We have seen how \hits
can be used to prove function extensionality and how univalence makes
it a lot easier to deal with isomorphic types in programs. This
chapter is devoted to other applications of \hott to programming. In
\cref{sec:quots} we show how \hits can be used to define quotient
types and argue whether we need such a construction and contrast this
approach to the setoid approach. We consider some of the difficulties
that \hits usually bring with them (so called coherence issues) and
show how to write binary operations on quotients as an example of how
one uses the elimination principles of quotients.

We also consider the application of univalence to views on abstract
types (\cref{sec:views}), as proposed by \cite{licataview}. We work
out the computations in detail to show how this works out and extend
the approach to also work with non-isomorphic views. The resulting
construction is a nice application of quotient types.

\section{Quotient types}
\label{sec:quots}

In mathematics, one way to construct new sets is to take the
\emph{quotient} \index{quotient} of a set $X$ by an equivalence
relation $R$ on that particular set. The new set is formed by
regarding all elements $x, y \in X$ \st $xRy$ as equal. An example of
a quotient set is the set of rationals |Rat| constructed from the
integers as follows: we quotient out |Int times Int| by the relation
|(a,b) ~ (c, d)| if and only if |ad = bc|.

In programming, such a construction can also be very useful, as it
often happens that we have defined a data type that has more structure
than we want to expose via the interface. An example of this is
encoding sets as lists: we want to regard two lists as encoding the
same set if they contain the same elements, no matter what the
multiplicity of every elements is or how the list is ordered. Other
examples where quotient types can be useful are the situations in
which we want to encode our data in such a way that certain operations
on the data can be implemented more efficiently. An example of this is
implementing a dictionary with a binary search tree: there are
multiple binary search trees that represent the same dictionary, \ie
contain the same key-value pairs. If we pass two different trees
representing the same dictionary \index{dictionary} to an operation,
we want the operation to yield the same results.

To make the above more precise, suppose we have defined a data type of
binary search trees, |BST : Universe|, along with a relation |rel :
BST -> BST -> hProp| \st |x ~ y == top| if and only if |x| and |y| are
comprised of the same key-value pairs, and |x ~ y == bottom|
otherwise. Suppose we have an insertion operation |insert| of type |
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
certain way, \eg by using a cleverly indexed type, so we do have a
unique representation for every dictionary.

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

The result of \cite{definablequotients} \index{definable quotient} is
that there exist quotients that are not definable with one example
being the real numbers constructed using the usual Cauchy sequence
method. Adding quotients as \hits to our type theory, does not make
the real numbers definable. Adding quotients is still useful in that
we only have to work with propositional equality, as opposed to the
confusion as to what relation one should use that arises from the use
of setoids.

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
inhabitants by the smallest equivalence relation generated by |rel|:
we do not only add |x == y| for every |x ~ y|, but can also construct
new equalities using |trans| and |sym|.

\subsection{Coherence issues}

One thing we glossed over is the question whether |Quotient A rel| is
actually a \hset, given the fact that |A| is a \hset. This need not be
the case, as is exhibited by the case where |A| is taken to be |top|
and |rel| is the trivial relation. The resulting quotient is
equivalent to the circle, which is not a \hset: the loop |sound tt tt
tt : [ tt ] == [ tt ]| is not equal to |refl : [ tt ] == [ tt ]|.

In order to get a \hset, we therefore need to take the \ntruncation{0}
of the quotient, which can be done with the following \hit:

\begin{code}
  settruncate (A : Universe) : Universe where
    inhabitant : A -> settruncate A
    
    uip : {x y : settruncate A} -> (p q : x == y) -> p == q
\end{code}

The elimination principle tells us that any function |A -> B|, with |A
B : Universe| can be lifted to |settruncate A -> B| if it respects the
additional paths of |settruncate A|. If |B| happens to be a \hset,
then these conditions are automatically satisfied. In the dependent
case, we have to supply a family of types |B : settruncate A ->
Universe| and a function |f : (x : A) -> B (inhabitant x)| such that,
again, the additional paths of |settruncate A| are respected. If we
have that for every |x : settruncate A|, |B x| is a \hset, then we are
done. The precise formulations of the elimination principles, both
dependent and non-dependent, are rather technical and involved and not
of interest for our purposes. In the examples we consider, we
eliminate into \hsets, so we do not need to explicitly check the
additional conditions.

If the relation |rel| happens to be an equivalence relation, using the
truncated quotient also gives us that we have (using univalence) |a ~
b == ([ a ] == [ b ])|, for every |a b : A|, supporting our previous
statement that the propositional equality of |Quotient A rel| is the
smallest equivalence relation generated by |rel|.

\newpage

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

\newpage

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

It is interesting to see that even though we do not need |rel| to be
an equivalence relation for the definition of quotient to work, we do
find ourselves in need of properties such as reflexivity for |rel|, in
order to define operations on quotients.

\section{Views on abstract types}
\label{sec:views}

Consider the dictionary example of the previous section. Most
languages provide such a structure as an \emph{abstract type}, \eg in
the Haskell Platform, a dictionary structure is provided by the
\verb+Data.Map+ module. To the users importing this module, the type
|Map| is opaque: its constructors are hidden. The user may only use
the operations such as |insert| and |lookup|. The advantage of this
approach is that we can easily interchange an obvious but slow
implementation (\eg implementing a dictionary as a list of tuples)
with a more efficient but more complex solution (\eg using binary
search trees instead of lists), without having to change a single line
of code in the modules using the abstract type.

In dependently typed programming, such an approach often means that we
have hidden too much: as soon as we try to prove properties about our
program that uses some abstract type, we find ourselves having to add
properties to the abstract type specification, or even worse: we end
up exporting everything so we can use induction on the concrete type
used in the actual implementation.

A solution to this problem is to supply the abstract type along with a
concrete implementation of the abstract type, called a
\emph{view}. This approach was introduced by \cite{wadlerview} as a
way to do pattern matching on abstract types.

\newpage

\subsection{Specifying views} 

An implementation of an abstract type is a type along with a
collection of operations on that type. An abstract type can then be
described in type theory as a nested \sigmatype \citep{abstractsigma},
\eg a sequence abstract type can be described as follows:

\begin{code}
Sequence =  Sigma  (seq     : Set -> Set)                                 dot
            Sigma  (empty   : (A : Set) -> (seq A))                       dot
            Sigma  (single  : (A : Set) -> A -> seq A)                    dot 
            Sigma  (append  : (A : Set) -> seq A -> seq A -> seq A)       dot
                   (map     : (A B : Set) -> (A -> B) -> seq A -> seq B) 
\end{code}

An implementation of such an abstract type then is just an inhabitant
of this nested \sigmatype.

If we want to do more than just use the operations and prove
properties about our programs that make use of abstract types, we
often find that we do not have enough information in the abstract type
specification available to prove the property at hand. One way to
address this problem is to add properties to the specification, but it
might not at all be clear a priori what properties are interesting and
expressive enough to add to the specification.

Another solution, proposed by \citet{licataview}, is to use views:
along with nested \sigmatype, we also provide a concrete
implementation, \ie an inhabitant of said \sigmatype, called a
\emph{view} on the abstract type. The idea is that the concrete view
can be used to prove theorems about the abstract type. However, for
this to work, we need to make sure that any implementation of the
abstract type is also in some sense compatible with the view: the
types of both implementations need to be isomorphic and the operations
need to respect the isomorphism. To illustrate this, consider we have
two sequence implementations:

\begin{code}
  ListImpl : Sequence
  ListImpl = (List, ([], (\x -> [x], (listapp, map))))

  OtherImpl : Sequence
  OtherImpl = (Other, (otherEmpty, (otherSingle, (otherAppend, otherMap))))
\end{code}

We want |List| and |Other| to be ``isomorphic''\footnote{|List| and
  |Other| cannot be isomorphic, as they are not types but type
  \emph{constructors}.}, \ie we need to write the following terms:

\begin{itemize}
\item |to : (A : Universe) -> Other A -> List A|
\item |from : (A : Universe) -> List A -> Other A|
\item |fromIsRightInverse : (A : Universe) (xs : List A) -> to (from xs) == xs|
\item |fromIsLeftInverse : (A : Universe) (xs : Other A) -> from (to xs) == xs|
\end{itemize}

\newpage

We also want the operations on |Other| to behave in the same way as
the operations on |List|s, \ie the following properties should be
satisfied:

\begin{itemize}
\item |to otherEmpty == []|
\item |(x : A) -> to (otherSingle x) == [x]|
\item |(xs ys : Other A) -> to (otherAppend xs ys) == to xs ++ to ys|
\item |(f : A -> B) (xs : Other A) -> to (otherMap f xs) == map f (to xs)|
\end{itemize}

These properties can be added to the original |Sequence|
type. However, it is rather tedious having to formulate these
properties for every operation of the abstract type. Since we have
specified the abstract type as a \sigmatype, we can use propositional
equality and univalence between these to guide us to the desired
properties. The full specification predicate now becomes the
following:

\begin{code}
  SequenceSpecification : Sequence -> Universe
  SequenceSpecification seqImpl = seqImpl == ListImpl
\end{code}

We know that in order to prove that two values |a| and |b| of type
|Sigma (x : A) . B x| are propositionally equal, we need to show its
fields are propositionally equal as well:

\begin{code}
  SigmaEq :  {A : Universe} {B : A -> Universe}
             {s s' : Sigma (x : A) dot B x}
             (p : fst s ≡ fst s')
             (q : transport B p (snd s) ≡ snd s')
        ->   s == s'
\end{code}

If we want to prove that |ListImpl == OtherImpl|, using |SigmaEq|, we
first need to show that |List == Other|. This can be done by showing
that for every |(A : Universe)|, we have an isomorphism |to : Other A
-> List A|. Using the univalence axiom and function extensionality, we
can then prove our goal, |List == Other|. For the second part of the
outermost \sigmatype, we need to transport the |snd| of |ListImpl|
along the proof of |List == Other| we just gave and prove it to be
propositionally equal to the |snd| of |OtherImpl|. Rather than deal
with the fully general |Sequence| where will show how the transporting
looks like for the case when we fix the type parameter. This is done
so we do not have to deal with function extensionality and only have
to use univalence directly once. We consider the following definitions
where we fix the type parameter |A : Universe|:

\begin{code}
  SequenceA =  Sigma  (seqA     : Set) dot
               Sigma  (emptyA   : seqA) dot
               Sigma  (singleA  : A -> seqA) dot 
               Sigma  (appendA  : seqA -> seqA -> seqA) dot
                      (mapA     : (A -> A) -> seqA -> seqA) 

\end{code}

with |ListImplA| and |OtherImplA| defined from the previous
definitions. 

\newpage

To show that |ListImplA| and |OtherImplA|, we need to show using
univalence that |List A == Other A|, so the beginning of the proof
looks like this:

\begin{code}
  spec : 
    (from : List A -> Other A)
    (to : Other A -> List A)
    -> Iso (List A) (Other A) from to
    -> ListImplA == OtherImplA
  spec from to iso =  SigmaEq (ua (List A) (Other A) iso) 
                      (SigmaEq  goal0
                      (SigmaEq  goal1
                      (SigmaEq  goal2
                                goal3)))
\end{code}

The first goal, |goal0|, has type |fst (transport (ua (List A)
(JoinList A) iso)| \\ |([], (\x -> [x], (listapp, map)))) ==
otherEmpty|. The left hand side of the equation is stuck, as we made
use of the univalence axiom. However, we can prove that the first
field of |transport| applied to the dependent pair, is |transport|
applied to the first field of the dependent pair:

\begin{code}
SigmaTransport : 
  {Ctx : Universe}
  {A : Ctx -> Universe} {B : (ctx : Ctx) -> A ctx -> Universe}
  {ctx ctx' : Ctx}
  {x : A ctx} {y : B ctx x}
  (pf : ctx == ctx') ->
  fst (transport (\ c -> Sigma (x : A c) dot B c x)) pf (x , y)) == transport (\ c -> A c) pf x
\end{code}

If we apply this to |goal0|, we now need to show that \\ |transport (\
c -> c) (ua (List A) (JoinList A) iso) [] == otherEmpty|, which we can
further reduce using the ``computation'' rule for univalence:

\begin{code}
  univalencecomp : 
       {A B : Universe}
       {from : A -> B}
       {to : B -> A}
       {iso : Iso A B from to}
       {x : A}
   ->  transport (\X -> X) (ua A B iso) x == from x
\end{code}

We have reduced |goal0| to the proof obligation |from [] ==
otherEmpty|. We can apply the same steps to the other goals and
recover the properties we formulated earlier. As we have now seen,
using this method, giving a specification of an abstract type amounts
to giving a nested \sigmatype specifying the interface and a concrete
view specifying the behaviour. We now get to prove properties of the
abstract type without having to add numerous properties to the
interface.

With the current ``implementation'' of \hott done by adding things
such as univalence as axioms, we have to do all this rewriting by
hand, but if we have a version of univalence available that computes, we
automatically arrive at the desired properties. 

\subsection{Reasoning with views}

If we want to prove a property about our abstract type, we now only
have to prove that it holds for the concrete view. The resulting proof
can then be used to show that it also holds for any other
implementation of the abstract type.

As an example of this, we will show that the |empty| operation of our
sequence type is the (left) unit of |append|. The case for lists is
easy, assuming that |listappend| only does induction on its left
argument:

\begin{code}
leftunitapp : (xs : List A) -> [] listappend xs == xs
leftunitapp xs = refl  
\end{code}

The general case of this statement is:

\begin{code}
  (xs : Other A) -> otherAppend otherEmpty xs == xs 
\end{code}

which can be established by the following equational reasoning:

\begin{code}
      xs
  == { isomm }
      from (to xs)
  == { [] isleftunitof listappend }
      from ([] listappend to xs)
  == { specof otherImpl }
      from (to otherEmpty ++ to xs)
  == { specof otherAppend }
      from (to (otherAppend otherEmpty xs))
  == { isomm }
      otherAppend otherEmpty xs
\end{code}

\subsection{Non-isomorphic views}

An implementation of an abstract type sometimes does not turn out to
be isomorphic to the concrete view. An example of this is an
implementation of sequences via join lists:

\begin{code}
  data JoinList (A : Universe) : Universe where
    nil   : JoinList A
    unit  : A -> JoinList A
    join  : JoinList A -> JoinList A -> JoinList A
\end{code}

Note that in this section we will fix an |A : Universe| and use
subscripts to emphasise this and avoid the confusion between
|JoinListWrong| and |JoinListRight|.

We have a function |to : JoinListA -> ListA| that maps |nil| to |nil|,
|unit a| to |[a]| and interprets |join| as concatenation of lists. The
other way around, |from : ListA -> JoinListA| can be constructed by
mapping every element |a| of the input list to |unit a| and then using
|join| to concatenate the resulting list of |JoinList|s.

While we do have that |(ls : ListA) -> to (from ls) == ls|, it is not
the case that |(js : JoinListA) -> from (to js) == js|, as |to| is not
injective: |JoinList| has a finer structure than |List|. This means
that|to| and |from| do not form an isomorphism. If only the first
equality holds (|to (from ls) == ls)|), but the second does not, |to|
is called a \emph{retraction} with |from| as its \emph{section}. It
still makes sense to use |JoinList| as an implementation of
sequences. The properties that the operations on |JoinList|s should
respect, do not make use of the fact that |from| and |to| are
isomorphisms; they can still be used for non-isomorphic views.

Since we are only interested in using the |JoinList| as a sequence and
do not care how the inhabitants are balanced, we can take the quotient
by the following relation:

\begin{code}
  rel : JoinListA -> JoinListA -> Universe
  x ~ y = to x == to y
\end{code}

The type |Quotient (JoinListA) rel| is then isomorphic to
|ListA|. This result can be generalised to arbitrary
section-retraction pairs between \hsets |A| and |B|: given |r : A ->
B| and |s : B -> A| such that |(a : A) -> s (r a) == a|, then |B| is
isomorphic to |Aquote| where |x ~ y| is defined as |r x == r y|. We
have a function |A -> Aquote|, namely the constructor |box| and can
write a function |Aquote -> A|. If we use |Quotientrec| for this, we
need to supply a function |f : A -> A| such that if |r x == r y|, then
also |f x == f y|. Choosing |f| to be |\ x -> s (r x)| works. The
identity function need not work: if it did, |r| would be injective and
would be an isomorphism. Let us name the functions between |A| and
|Aquote| |toAquote| and |fromAquote|. Composing these functions with
|r| or |s|, we get functions between |Aquote| and |B| that give us the
desired isomorphism. Proving that this is an isomorphism mostly
involves applying the proof that |r (s x) == x| in various ways. We
also have to invoke the \UIP property that |Aquote| admits (thanks to
the \ntruncation{0}) for the induction step on |Aquote|. The fact that
|toAquote| is a retraction with |fromAquote| as its section can be
proved using the same techniques.

To lift the operations on |A| to operations on |Aquote| we simply
apply |toAquote| and |fromAquote| in the right places. Showing that
these lifted operations satisfy the conditions that follow from the
specification then boils down to conditions that only refer to the
operations on |A| in relation to those on |B|, as we will demonstrate
with the |JoinList| example. Let us define |JoinList'| as |Quotient A
rel| with |x ~ y| defined as |to x == to y|. We have the following
functions:

\begin{itemize}
\item |to : JoinListA -> ListA|
\item |from : ListA -> JoinListA|
\item |to' : JoinListA -> JoinList'|
\item |from' : JoinList' -> JoinListA|
\end{itemize}

\newpage

The isomorphism between |JoinList'| and |ListA| is witnessed by \\ |to
circ from' : JoinList' -> ListA| and |to' circ from : ListA ->
JoinListA|. The |empty| of |JoinList'| is |to' nil|, which means
that we need to establish |to (from' (to' nil)) == []|. We can reduce
this goal to |to nil == []| via equational reasoning:

\begin{code}
      to (from' (to' nil))
  == { definition to' }
      to (from' (box nil))
  == { beta reduction }
      to (from (to nil))
  == { to/from is a retraction/section }
      to nil
\end{code}

In general we have that |from' (to' x) == from (to x)| holds for any
|x : JoinListA|. Deriving the property for |single| goes analogously
to the derivation above. The rule for |append| is more interesting as
we there also need |from'| in other positions:

\begin{code}
      to (from' (to' (join (from' xs) (from' ys))))
  == { beta reduction }
      to (from (to (join (from' xs) (from' ys))))
  == { to/from is a retraction/section }
      to (join (from' xs) (from' ys))
\end{code}

We end up with having to prove the following:

\begin{code}
  (xs ys : JoinList') -> 
    to (join (from' xs) (from' ys)) == to (from' xs) listappend to (from' ys)
\end{code}
which follows from |(xs ys : JoinListA) -> to (join xs ys) == to xs
listappend to ys|.

The above derivation shows us that we might arrive at equations that
are a bit less general than the equations we get from if we were to
pretend our retraction-section pair is actually an isomorphism.

\subsubsection{Non-isomorphic views via definable quotients}

It so happens that the quotient |Aquote| is definable: it can be
defined as the type |Sigma (x : A) dot s (r x) == x|, \ie restrict |A|
to those inhabitants \st (the lifted versions of) |s| and |r| become
isomorphisms. The function |box| is then defined by:

\begin{code}
 box : A -> Sigma (x : A) dot s (r x) == x
 box x = (s (r x)) , ap s (isretract (r x))
\end{code}

where |isretract : (x : B) -> r (s x) == x| witnesses the fact that
|r| and |s| form a retraction-section pair.

Notice that for the quotient type we have the |\ x -> s (r x)| in the
``deconstructor'' (\ie in the function |from' : JoinList' -> JoinList
A|) and here we have it in the constructor (\ie the function
|box|). This stems from the fact that the soundness of quotient types
is enforced by the way they are eliminated. It is only there that we
have the obligation to show that we respect the relation on the
type. With the \sigmatype it is more correctness by construction.

From a computational perspective, the first approach with the quotient
types is more desirable, as the values of the type do not carry
around any correctness proof.

\section{Conclusion}

\Hits allow us to straightforwardly define quotient types. This
definition works better than the setoid method in that we no longer
have to be careful whether we use the custom equivalence relation or
propositional equality: we only have to consider propositional
equality. However, as is common with \hits, we have to take the
\ntruncation{0} in the definition of a quotient type. This makes the
elimination principle more complex to work with, but since virtually
any of the types we encounter in programming are \hsets, the extra
conditions that the \ntruncation{0} adds to the elimination principle
are usually trivially satisfied.

Univalence gives us a very clean way to define specifications of
abstract types using concrete views. Working with this specification,
\eg trying to prove that a given implementation satisfies the
specification, involves a lot of manual fiddling with the computation
rules of \sigmatypes and univalence. Having a computational
interpretation of univalence would obviously be of great importance
for this method to be useful.

Using quotient types, we can also define a view on an abstract type
that is not isomorphic to the concrete type of the reference
implementation, but only instead we have a retraction-section pair
between the two types. Any retraction-section pair can be turned into
an isomorphism, by quotienting out by the retraction. Such a quotient
happens to be definable, which means that we do not need the quotient
type construction using \hits to do this. However, the \hit
construction does yield a definition that is more amenable to the
optimisations that will be discussed in~\cref{chap:erasure}, as
the proofs that the quotient structure is respected only occur in the
calls to the elimination principle, instead of occurring in all the
terms of type, which is the case with the definable quotient
implementation.
