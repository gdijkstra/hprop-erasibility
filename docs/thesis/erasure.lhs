\chapter{Erasing propositions}
\label{chap:erasure}

When writing certified programs in a dependently typed setting, we can
conceptually distinguish between the program parts and the proof (of
correctness) parts. These are sometimes also referred to as the
informative\footnote{Instead of ``informative'', it is sometimes also
  called ``computation'', but this is a bit of a misnomer as the proof
  parts can be computational as well, but then only at compile time
  (\ie during type checking).}  and logical parts, respectively. In
practice, these two seemingly separate concerns are often
intertwined. Consider for example the sorting of lists of naturals:
given some predicate |isSorted : List Nat -> List Nat -> Universe|
that tells us whether the second list is a sorted permutation of the
first one, we can to write a term of the following type:

\begin{code}
  sort : (xs : List Nat) -> Sigma (ys : List Nat) dot (isSorted xs ys)
\end{code}

To implement such a function, we need to provide for every list a
sorted list along with a proof that this is indeed a sorted version of
the input list. At run-time the type checking has been done, hence the
proof of correctness has already been verified: we want to
\emph{erase} these logical parts.

Types such as |isSorted xs ys| are purely logical: we care more about
the presence of an inhabitant than what kind of inhabitant we exactly
have at our disposal. In~\cref{sec:props} we will give more
examples of such types, called \emph{propositions} (compare this with
the definition of \hprops via proof irrelevance
(\cref{sec:truncations}), and how they can occur in various places
in certified programs. In~\cref{sec:coqprop}
and~\cref{sec:irragda} we review the methods Coq and Agda provide
us to annotate parts of our program as being propositions in such a
way that those parts can be erased after type checking and are absent
at run-time. \Cref{sec:colfam} reviews the concept of
\emph{collapsible families} and how we can automatically detect
whether a type is a proposition, instead of annotating them
ourselves. In~\cref{sec:intcol} we internalise the concept of
collapsible families and try to do the same with the optimisation
in~\cref{sec:intcolopt}. The internalised version of collapsibility
looks like an indexed version of the concept of
\hprops. In~\cref{sec:indhprops} we investigate if we can use this
to devise an optimisation akin to the optimisation based on
collapsibility.

\section{Propositions}
\label{sec:props}

In the |sort| example, the logical part |isSorted xs ys| occurs in
the result as part of a \sigmatype. This means we can separate the
proof of correctness from the sorting itself, \ie we can write a
function |sort' : List Nat -> List Nat| and a proof of the following:

\begin{code}
  sortCorrect : (xs : List Nat) -> isSorted xs (sort' xs)
\end{code}

The logical part here asserts properties of the \emph{result} of the
computation. If we instead have assertions on our \emph{input}, we
cannot decouple this from the rest of the function as easily as, if it
is at all possible. For example, suppose we have a function, safely
selecting the $n$-th element of a list:

\begin{code}
 elem : (A : Universe) (xs : List A) (i : Nat) -> i < length xs -> A
\end{code}

If we were to write |elem| without the bounds check |i < length xs|,
we would get a partial function. Since we can only define total
functions in our type theory, we cannot write such a
function. However, at run-time, carrying these proofs around makes no
sense: type checking has already shown that all calls to |elem| are
safe and the proofs do not influence the outcome of |elem|. We want to
erase terms of types such as |i < length xs|, if we have established
that they do not influence the run-time computational behaviour of our
functions.

\subsection{Bove-Capretta method}

The |elem| example showed us how we can use propositions to write
functions that would otherwise be partial, by asserting properties of
the input. The Bove-Capretta method~\citep{bcmethod} generalises this
and more: it provides us with a way to transform any (possibly
partial) function defined by general recursion into a total,
structurally recursive one. The quintessential example of a definition
that is not structurally recursive is \emph{quicksort}\footnote{In
  most implementations of functional languages, this definition will
  not have the same space complexity as the usual in-place version. We
  are more interested in this function as an example of non-structural
  recursion and are not too concerned with its complexity.} :

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
graph. 

\newpage

In our quicksort case we get the following inductive family:

\begin{code}
  data qsAcc : List Nat -> Universe where
    qsAccNil   : qsAcc []
    qsAccCons  : (x : Nat) (xs : List Nat) 
                 (h1 : qsAcc (filter (gt x) xs))
                 (h2 : qsAcc (filter (le x) xs))
                 -> qsAcc (x :: xs)
\end{code}

with the following function definition\footnote{This definition uses
  dependent pattern matching~\citep{depmatch}, but can be rewritten directly using the
  elimination operators instead. The important thing here is to notice
  that we are eliminating the |qsAcc xs| argument.}

\begin{code}
  qs : (xs : List Nat) → qsAcc xs → List Nat
  qs .nil         qsAccNil                =  []
  qs .cons        (qsAccCons x xs h1 h2)  =  qs (filter (gt x) xs) h1 ++
                                             x :: qs (filter (le x) xs) h2
\end{code}

Pattern matching on the |qsAcc xs| argument gives us a structurally
recursive version of |qs|. Just as with the |elem| example, we need
information from the proof to be able to write this definition in our
type theory. In the case of |elem|, we need the proof of |i < length
xs| to deal with the (impossible) case where |xs| is empty. In the
|qs| case, we need |qsAcc xs| to guide the recursion. Even though we
actually pattern match on |qsAcc xs| and it therefore seemingly
influences the computational behaviour of the function, erasing this
argument yields the original |qs| definition.

\section{The \coqprop universe in Coq}
\label{sec:coqprop}

In Coq we have have the \coqprop universe, apart from the \coqset
universe. Both universes act as base sorts of the hierarchy of sorts,
\coqtype, \ie |Prop : Type(1)|, |Set : Type(1)| and for every |i|,
|Type(i) : Type(i+1)|.  As the name suggests, by defining a type to be
of sort \coqprop, we ``annotate'' it to be a logical type, a
proposition. Explicitly marking the logical parts like this, makes the
development easier to read and understand: we can more easily
distinguish between the proof of correctness parts and the actual
program parts. More importantly, Coq's extraction
mechanism~\citep{letouzeyextraction} now knows what parts are supposed
to be logical, hence what parts are to be erased.

In the |sort| example, we would define |isSorted| to be a family of
\coqprops indexed by |List Nat|. For the \sigmatype, Coq provides two
options: |sig| and |ex|, defined as follows:

\begin{code}
  Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P

  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P
\end{code}

As can be seen above, |sig| differs from |ex| in that the
latter is completely logical, whereas |sig| has one informative
and one logical field and in its entirety is informative. Since we are
interested in the |list Nat| part of the \sigmatype that is the result
type of |sort|, but not the |isSorted| part, we choose the |sig|
version.

The extracted version of |sig| consists of a single constructor
|exist|, with a single field of type |A|. Since this is
isomorphic the type |A| itself, Coq optimises this away during
extraction. This means |sort : (xs : List Nat) -> Sigma (ys : List
Nat) dot (isSorted xs ys)| gets extracted to a function |sort' : List Nat
-> List Nat|.

When erasing all the \coqprop parts from our program, we do want to
retain the computational behaviour of the remaining parts. Every
function that takes an argument of sort \coqprop, but whose result
type is not in \coqprop, needs to be invariant under choice of
inhabitant for the \coqprop argument. To force this property, Coq
restricts the things we can eliminate a \coqprop into. The general
rule is that pattern matching on something of sort \coqprop is allowed
if the result type of the function happens to be in \coqprop.

\subsection{Singleton elimination and \hott}
There are exceptions to this rule: if the argument we are pattern
matching on happens to be an \emph{empty} or \emph{singleton
  definition} of sort \coqprop, we may also eliminate into
\coqtype. An empty definition is an inductive definition without any
constructors. A singleton definition is an inductive definition with
precisely one constructor, whose fields are all in \coqprop. Examples
of such singleton definitions are conjunction on \coqprop (|/\|)
and the accessibility predicate |Acc| used to define functions
using well-founded recursion.

Another important example of singleton elimination is elimination on
Coq's equality |eq| (where |a = b| is special notation for
|eq a b|), which is defined to be in \coqprop. The inductive
family |eq| is defined in the same way as we have defined
identity types, hence it is a singleton definition, amenable to
singleton elimination. Consider for example the |transport| function:

\begin{code}
Definition transport : forall A, forall (P : A -> Type), 
  forall (x y : A),
  forall (path : x = y),
  P x -> P y.
\end{code}

Singleton elimination allows us to pattern match on |path| and and
eliminate into something of sort |Type|. In the extracted version, the
|path| argument gets erased and the |P x| argument is returned. In
\hott, we know that the identity types need not be singletons and can
have other inhabitants than just the canonical |refl|, so throwing
away the identity proof is not correct. As has been discovered by
\citet{univalencevsextraction}, singleton elimination leads to some
sort of inconsistency, if we assume the univalence axiom: we can
construct a value |x : bool| such that we can prove |x = false|, even
though in the extracted version |x| normalises to |true|. Assuming
univalence, we have two distinct proofs of |bool = bool|, namely
|refl| and the proof we get from applying univalence to the
isomorphism |not : bool -> bool|. Transporting a value along a path we
have obtained from using univalence, is the same as applying the
isomorphism. Defining |x| to be |true| transported along the path
obtained from applying univalence to the isomorphism |not|, yields
something that is propositionally equal to |false|. If we extract the
development, we get a definition of |x| that ignores the proof of
|bool = bool| and just returns |true|.

In other words, Coq does not enforce or check proof irrelevance of the
types we define to be of sort \coqprop, which internally is fine: it
does not allow us to derive falsity using this fact. The extraction
mechanism however, does assume that everything admits proof
irrelevance. The combination of this along with singleton elimination
means that we can prove properties about our programs that no longer
hold in the extracted version. It also goes to show that the design
decision to define the identity types to be in \coqprop is not
compatible with \hott.

\subsection{Quicksort example}

In the case of |qs| defined using the Bove-Capretta method, we
actually want to pattern match on the logical part: |qsAcc xs|. Coq
does not allow this if we define the family |qsAcc| to be in
\coqprop. However, we can do the pattern matching ``manually'', as
described in~\cite{coqart}. We know that we have exactly one
inhabitant of |qsAcc xs| for each |xs|, as they represent the call
graph of |qs| for the input |xs|, and the pattern matches of the
original definition do not overlap, hence each |xs| has a unique call
graph. We can therefore easily define and prove the following
inversion theorems, that roughly look as follows:

\begin{code}
  qsAccInv0 : (x : Nat) (xs : List Nat) (qsAcc (x :: xs)) -> qsAcc (filter (le x) xs)

  qsAccInv1 : (x : Nat) (xs : List Nat) (qsAcc (x :: xs)) -> qsAcc (filter (gt x) xs)
\end{code}

We define the function |qs| just as we originally intended to and add
the |qsAcc xs| argument to every pattern match. We then call the
inversion theorems for the appropriate recursive calls. Coq still
notices that there is a decreasing argument, namely |qsAcc xs|. If we
follow this approach, we can define |qsAcc| to be a family in \coqprop
and recover the original |qs| definition without the |qsAcc xs|
argument using extraction.

In the case of partial functions, we still have to add the missing
pattern matches and define impossibility theorems: if we reach that
pattern match and we have a proof of our Bove-Capretta predicate for
that particular pattern match, we can prove falsity, hence we can use
|False_rect| do deal with the missing pattern match.

\newpage

\subsection{Impredicativity}

So far we have seen how \coqprop differs from \coqset with respect to
its restricted elimination rules and its erasure during extraction,
but \coqprop has another property that sets it apart from \coqset:
\emph{impredicativity}. Impredicativity means that we are able to
quantify over something which contains the thing currently being
defined. In set theory unrestricted use of this principle leads us to
being able to construct Russell's paradox: the set $R = \{x || x \in x
\}$ is an impredicative definition, we quantify over $x$, while we are
also defining $x$. Using this definition we can prove that $R \in R$
if and only if $R \not\in R$. Impredicativity is also a necessary
ingredient for the Burali-Forti paradox: constructing the set of all
ordinal numbers yields an inconsistency. It is this paradox that can
be expressed in impredicative \MLTT (\ie |Universe : Universe| holds),
where it is called Girard's paradox. However, impredicative
definitions are sometimes very useful and benign, in particularly when
dealing with propositions: we want to be able to write propositions
that quantify over propositions, for example:

\begin{code}
  Definition demorgan : Prop := forall P Q : Prop, 
    ~(P /\ Q) -> ~P \/ ~Q.
\end{code}

Coq allows for such definitions as the restrictions on \coqprop
prevent us from constructing paradoxes such as Girard's. For details
on these limitations, the reader is referred to the Coq
FAQ\footnote{\url{http://coq.inria.fr/V8.1/faq.html\#htoc49}}.

\section{Irrelevance in Agda}
\label{sec:irragda}

In Coq, we put the annotations of something being a proposition in the
definition of our inductive type, by defining it to be of sort
\coqprop. With Agda's irrelevance mechanism, we instead put the
annotations at the places we \emph{use} the proposition, by placing a
dot in front of the corresponding type. For example, the type of the
|elem| becomes:

\begin{code}
  elem : (A : Universe) (xs : List A) (i : ℕ) → .(i < length xs) → A
\end{code}

We can also mark fields of a record to be irrelevant. In the case of
|sort|, we want something similar to the |sig| type from Coq,
where second field of the \sigmatype is deemed irrelevant. In Agda
this can be done as follows:

\begin{code}
  record Sigmairr (A : Universe) (B : A → Universe) : Universe  where
    constructor _,_ 
    field
      fst   : A
      .snd  : B fst
\end{code}

\newpage

To ensure that irrelevant arguments are indeed irrelevant to the
computation at hand, Agda has several criteria that it checks. First
of all, no pattern matching may be performed on irrelevant arguments,
just as is the case with \coqprop. (However, the absurd pattern may be
used, if applicable.)  Contrary to Coq, singleton elimination is not
allowed. Secondly, we need to ascertain that the annotations are
preserved: irrelevant arguments may only be passed on to irrelevant
contexts. This prevents us from writing a function of type |(A :
Universe) -> .A -> A|.

Another, more important, difference with \coqprop is that irrelevant
arguments are ignored by the type checker when checking equality of
terms. This can be done safely, even though the terms at hand may in
fact be definitionally different, as we never need to appeal to the
structure of the value: we cannot pattern match on it. The only thing
that we can do with irrelevant arguments is either ignore them or pass
them around to other irrelevant contexts.

The reason why the type checker ignoring irrelevant arguments is
important, is that it allows us to` prove properties about irrelevant
arguments in Agda, internally. For example: any function out of an
irrelevant type is constant:

\begin{code}
  irrelevantConstantFunction  :  {A : Universe} {B : Universe} 
                              →  (f : .A → B) → (x y : A) → f x == f y
  irrelevantConstantFunction f x y = refl
\end{code}

There is no need to use the congruence rule for |==|, since the |x| and
|y| are ignored when the type checker compares |f x| to |f y|, when
type checking the |refl|. The result can be easily generalised to
dependent functions:

\begin{code}
  irrelevantConstantDepFunction  :  {A : Universe} {B : .A → Universe} 
                                 →  (f : .(x : A) → B x) → (x y : A) → f x == f y
  irrelevantConstantDepFunction f x y = refl
\end{code}

Note that we do not only annotate |(x : A)| with a dot, but also
occurrence of |A| in the type |B : A -> Universe|, otherwise we are
not allowed to write |B x| as we would use an irrelevant argument in a
relevant context. When checking the term
|irrelevantConstantDepFunction|, the term |f x == f y| type checks,
without having to transport one value along some path, because the
types |B x| and |B y| are regarded as definitionally equal by the type
checker, ignoring the |x| and |y|. Just as before, there is no need
to use the (dependent) congruence rule; a |refl| suffices.

We would also like to show that we have proof irrelevance for
irrelevant arguments, \ie we want to prove the following:

\begin{code}
  irrelevantProofIrrelevance : {A : Universe} .(x y : A) → x == y
\end{code}

Agda does not accept this, because the term |x == y| uses irrelevant
arguments in a relevant context: |x == y|. If we instead package the
irrelevant arguments in an inductive type, we can prove that the two
values of the packaged type are propositionally equal.

\newpage 

Consider the following record type with only one irrelevant field:

\begin{code}
  record Squash (A : Universe) : Universe where
    constructor squash
    field
      .proof : A
\end{code}

Using this type, we can now formulate the proof irrelevance principle
for irrelevant arguments and prove it:

\begin{code}
  squashProofIrrelevance : {A : Universe} (x y : Squash A) → x == y
  squashProofIrrelevance x y = refl
\end{code}

The name ``squash type'' comes from Nuprl~\citep{nuprl}: one takes a
type and identifies (or ``squashes'') all its inhabitants into one
unique (up to propositional equality) inhabitant. In \hott the process
of squashing a type is called \ntruncation{(-1)} (\cref{sec:trunc})
and can also be achieved by defining the following \hit:

\begin{code}
  data proptruncate : (A : Universe) : Universe where
    inhabitant : A -> proptruncate A
    
    allpaths : (x y : proptruncate A) -> x == y
\end{code}

\subsection{Quicksort example}

If we want to mark the |qsAcc xs| argument of the |qs| function as
irrelevant, we run into the same problems as we did when we tried to
define |qsAcc| as a family in \coqprop: we can no longer pattern match
on it. In Coq, we did have a way around this, by using inversion and
impossibility theorems to do the pattern matching
``manually''. However, if we try such an approach in Agda, its
termination checker cannot see that |qsAcc xs| is indeed a decreasing
argument and refuses the definition.

\section{Collapsible families}
\label{sec:colfam}

The approaches we have seen so far let the user indicate what parts of
the program are the logical parts and are amenable for
erasure. \cite{collapsibility} show that we can let the compiler
figure that out by itself instead. The authors propose a series of
optimisations for the Epigram system, based on the observation that
one often has a lot of redundancy in well-typed terms. If it is the
case that one part of a term has to be definitionally equal to another
part in order to be well-typed, we can leave out (presuppose) the
latter part if we have already established that the term is
well-typed.

\newpage

The authors describe their optimisations in the context of Epigram. In
this system, the user writes programs in a high-level language that
gets elaborated to programs in a small type theory language. This has
the advantage that if we can describe a translation for high-level
features, such as dependent pattern matching, to a simple core type
theory, the metatheory becomes a lot simpler. The smaller type theory
also allows us to specify optimisations more easily, because we do not
have to deal with the more intricate, high-level features.

As such, the only things we need to look at, if our goal is to
optimise a certain inductive family, are its constructors and its
elimination principle. Going back to the |elem| example, we had the |i
< length xs| argument. The smaller-than relation can be defined as the
following inductive family (in Agda syntax):

\begin{code}
data ltfam : ℕ → ℕ → Universe where
  ltZ : (y : ℕ)            → Z    < S y
  ltS : (x y : ℕ) → x < y  → S x  < S y
\end{code}

with elimination operator

\begin{code}
  ltelim  :  (P : (x y : ℕ) → x < y → Universe)
             (mZ : (y : ℕ) → P 0 (S y) (ltZ y))
             (mS : (x y : ℕ) → (pf : x < y) → P x y pf → P (S x) (S y) (ltS x y pf))
             (x y : ℕ)
             (pf : x < y)
          →  P x y pf
\end{code}

and computation rules

\begin{code}
  ltelim P mZ mS 0      (S y)  (ltZ y)        ===  mZ y
  ltelim P mZ mS (S x)  (S y)  (ltS x y pf)   ===  mS x y pf (ltelim P mZ mS x y pf)
\end{code}

If we look at the computation rules, we see that we can presuppose
several things. The first rule has a repeated occurrence of |y|, so we
can presuppose the latter occurrence, the argument of the
constructor. In the second rule, the same can be done for |x| and
|y|. The |pf| argument can also be erased, as it is never inspected:
the only way to inspect |pf| is via another call the |ltelim|, so by
induction it is never inspected. Another thing we observe is that the
pattern matches on the indices are disjoint, so we can presuppose the
entire target: everything can be recovered from the indices given to
the call of |ltelim|.

We have to be careful when making assumptions about values, given
their indices. Suppose we have written a function that takes |p : 1 <
1| as an argument and contains a call to |ltelim| on |p|. If we look
at the pattern matches on the indices, we may be led to believe that
|p| is of form |ltS 0 0 p'| for some |p' : 0 < 0| and reduce
accordingly. The presupposing only works for \emph{canonical} values,
hence we restrict our optimisations to the run-time (evaluation in the
empty context), as we know we do not perform reductions under binders
in that case and every value is canonical after reduction. The
property that every term that is well-typed in the empty context,
reduces to a canonical form is called \emph{adequacy} and is a
property that is satisfied by \MLTT.

The family |ltelim| has the property that for indices |x y : Nat|, its
inhabitants |p : x < y| are uniquely determined by these indices. To
be more precise, the following is satisfied: for all |x y : Nat|, |/-
p q : x < y| implies |/- p === q|. Families |D : I0 -> dots -> In ->
Universe| such as |ltelim| are called \emph{collapsible} if they
satisfy that for every |i0 : I0, dots, in : In|, if |/- p q : D i0
dots in|, then |/- p === q|.

Checking collapsibility of an inductive family is undecidable in
general. This can be seen by reducing it to the type inhabitation
problem: consider the type |top + A|. This type is collapsible if and
only if |A| is uninhabited, hence determining with being able to
decide collapsibility means we can decide type inhabitation as
well. As such, we limit ourselves to a subset that we can recognise,
called \emph{concretely} collapsible families. A family |D : I0 ->
dots -> In -> Universe| is concretely collapsible if satisfies the
following two properties:

\begin{itemize}
\item If we have |/- x : D i0 dots in|, for some |i0 : I0|, |dots|, |in
  : In|, then we can recover its constructor tag by pattern matching
  on the indices.
\item All the non-recursive arguments to the constructors of |D| can
  be recovered by pattern matching on the indices.
\end{itemize}

Note that the first property makes sense because we only have to deal
with canonical terms, due to the adequacy property. Checking whether
this first property holds can be done by checking whether the indices
of the constructors, viewed as patterns, are disjoint. The second
property can be checked by pattern matching on the indices of every
constructor and checking whether the non-recursive arguments occur as
pattern variables.

\subsection{Erasing concretely collapsible families}
\label{sec:erasecolfam}

If |D| is a collapsible family, then its elimination operator |Delim|
is constant in its target, if we fix the indices. This seems to
indicate that there might be a possibility to erase the target
altogether. Nevertheless, |D| might have constructors with
non-recursive arguments giving us information. Concretely collapsible
families satisfy the property that this kind of information can be
recovered from the indices, so we can get away with erasing the entire
target. Being concretely collapsible means that we have a function at
the meta-level (or implementation level) from the indices to the
non-recursive, relevant parts of the target. Since this is done by
pattern matching on the fully evaluated indices, recovering these
parts takes an amount of time that is constant in the size of the
given indices. Even though this sounds promising, the complexity of
patterns does influence this constant, \eg the more deeply nested the
patterns are, the higher the constant. We now also need the indices to
be fully evaluated when eliminating a particular inductive family,
whereas that previously might not have been needed. The optimisation
is therefore one that gives our dependently typed programs a better
space complexity, but not necessarily a better time complexity.

\subsection{Quicksort example}

The accessibility predicates |qsAcc| form a collapsible family. The
pattern matches on the indices in the computation rules for |qsAcc|
are the same pattern matches as those of the original |qs|
definition. There are no overlapping patterns in the original
definition, so we can indeed recover the constructor tags from the
indices. Also, the non-recursive arguments of |qsAcc| are precisely
those given as indices, hence |qsAcc| is indeed a (concretely)
collapsible family. By the same reasoning, any Bove-Capretta predicate
is concretely collapsible, given that the original definition we
derived the predicate from, has disjoint pattern matches.

The most important aspect of the collapsibility optimisation is that
we have established that everything we need from the value that is to
be erased, can be (cheaply) \emph{recovered} from its indices passed
to the call to its elimination operator. This means that we have no
restrictions on the elimination of collapsible families: we can just
write our definition of |qs| by pattern matching on the |qsAcc xs|
argument. At run-time, the |qsAcc xs| argument has been erased and the
relevant parts are recovered from the indices.

\section{Internalising collapsibility}
\label{sec:intcol}

Checking whether an inductive family is concretely collapsible is
something that can be easily done automatically, as opposed to
determining collapsibility in general, which is undecidable. Since
collapsibility is also a meta-theoretical concept (it makes use of
definitional equality and talks about provability), it is only the
compiler that can find out whether an inductive family is collapsible
or not. If we want to provide the user with the means to give a proof
of collapsibility for a certain family itself, if the compiler fails
to notice this, then we would need to specify a new language for such
evidence. Instead of create such a language, we will create an
internal version of the meta-theoretical notion of collapsibility, so
that user can provide the evidence in the type theory itself.

Recall the definition of a collapsible family\footnote{The definition
  we originally gave allowed for an arbitrary number of indices. In
  the following sections we will limit ourselves to the case where we
  have only one index for presentation purposes. All the results given
  can be easily generalised to allow more indices.} : given an
inductive family |D| indexed by the type |I|, we say that |D| is
collapsible if for every index |i : I| and terms |x|, |y|, the
following holds:

\begin{code}
  /- x, y : D i implies /- x === y
\end{code}

This definition makes use of definitional equality. Since we are
working with an intensional type theory, we do not have the
\emph{equality reflection rule} at our disposal: there is no rule that
tells us that propositional equality implies definitional
equality. This might lead us to think that internalising the above
definition will not work, as we seemingly cannot say anything about
definitional equality from within \MLTT. 

\newpage

Let us consider the following variation: for all terms |x|, |y| there
exists a term |p| such that

\begin{code}
  /- x, y : D i implies /- p : x == y
\end{code}

Since \MLTT satisfies the canonicity property, any term |p| such that
|/- p : x == y| reduces to |refl|. The only way for the term to type
check, is if |x === y|, hence in the empty context the equality
reflection rule does hold. The converse is also true: definitional
equality implies of |x| and |y| that |/- refl : x == y| type checks,
hence the latter definition is equal to the original definition of
collapsibility.

The variation given above is still not a statement that we can
directly prove internally: we need to internalise the implication and
replace it by the function space. Doing so yields the following
following definition: there exists a term |p| such that:

\begin{code}
  /- p : (i : I) -> (x y : D i) -> x == y
\end{code}

Or, written as a function in Agda:

\begin{code}
  isInternallyCollapsible : (I : Universe) (A : I -> Universe) -> Universe
  isInternallyCollapsible I A = (i : I) -> (x y : A i) -> x == y
\end{code}


We will refer to this definition as \emph{internal collapsibility}. It
is easy to see that every internally collapsible family is also
collapsible, by canonicity and the fact that |refl| implies
definitional equality. However, internally collapsible families do
differ from collapsible families as can be seen by considering |D| to
be the family |Id|. By canonicity we have that for any |A : Universe|,
|x, y : A|, a term |p| satisfying |/- p : Id A x y| necessarily
reduces to |refl|. This means that |Id| is a collapsible family. In
contrast, |Id| does not satisfy the internalised condition given
above, since this then boils down to the \UIP principle, which does
not hold, as we have discussed.

\section{Internalising the collapsibility optimisation}
\label{sec:intcolopt}

In~\cref{sec:erasecolfam} we saw how concretely collapsible
families can be erased, since all we want to know about the
inhabitants can be recovered from its indices. In this section we will
try to uncover a similar optimisation for internally collapsible
families.

We cannot simply erase the internally collapsible arguments from the
function we want to optimise, \eg given a function |f : (i : I) -> (x
: D i) -> tau|, we generally cannot produce a function
|fsnake : (i : I) -> tau|, since we sometimes need
the |x : D i| in order for the function to
type check. However, we can use Agda's irrelevance mechanism to instead
generate a function in which the collapsible argument is marked as
irrelevant.

\newpage

The goal is now to write the following function (for the non-dependent
case):

\begin{code}
  optimiseFunction : 
    (I : Universe) (A : I → Universe) (B : Universe)
    (isInternallyCollapsible I A)
    (f : (i : I) → A i →  B) 
    -> ((i : I) → .(A i) → B)
\end{code}

Along with such a function, we should also give a proof that the
generated function is equal to the original one in the following
sense:

\begin{code}
  optimiseFunctionCorrect :
    (I : Universe) (D : I → Universe) (B : Universe)
    (pf : isInternallyCollapsible I D)
    (f : (i : I) → D i →  B)
    (i : I) (x : D i)
    -> optimiseFunction I D B pf f i x == f i x
\end{code}
If we set out to write the function |optimiseFunction|, after having
introduced all the variables, our goal is to produce something of type
|B|. This can be done by using the function |f|, but then we need a |i
: I| and something of type |D i|. We have both, however the |D i| we
have is marked as irrelevant, so it may only be passed along to
irrelevant contexts, which the function |f| does not provide, so we
cannot use that one. We need to find another way to produce an |D
i|. We might try to extract it from the proof of
|isInternallyCollapsible I D|, but this proof only tells us how the
inhabitants of every |D i| are related to each other with propositional
equality. From this proof we cannot tell whether some |D i| is
inhabited or empty.

The optimisation given for concretely collapsible families need not
worry about this. In that case we have a lot more information to work
with. We only have to worry about well-typed calls to the elimination
operator, so we do not have to deal with deciding whether |D i| is
empty or not. Apart from this we only need to recover the
non-recursive parts of the erased, canonical term.

If we extend the definition of internal collapsibility with something
that decides whether |A i| is empty or not, we get the following
definition:

\begin{code}
  isInternallyCollapsibleDecidable : (I : Universe) (A : I -> Universe) -> Universe
  isInternallyCollapsibleDecidable I A = (i : I) 
    -> (((x y : A i) -> x == y) otimes (A i oplus A i -> bottom))
\end{code}

If we then replace the occurrence of |isInternallyCollapsible| in the
type signature of |optimiseFunction| with
|isInternallyCollapsibleDecidable|

\newpage

\subsection{Time complexity issues}

Using this definition we do get enough information to write
|optimiseFunction|. However, the success of the optimistically named
function |optimiseFunction| relies on time complexity the proof given
of |isInternallyCollapsibleDecidable D I| that is used to recover the
erased |A i| value from the index |i|. In the case of concrete
collapsibility this was not that much of an issue, since the way we
retrieve the erased values from the indices was constant in the size
of the given indices.

Apart from requiring a decision procedure that gives us, for every
index |i : I|, an inhabitant of |A i| or a proof that |A i| is empty,
we need a bound on the time complexity of this procedure. If we want
to analyse the complexity of the functions, we need an embedding of
the language they are written in. Examples of this approach can be
found in \cite{sorted} and \cite{timecomplexity}. In
\cite{timecomplexity} the functions are written using a monad that
keeps track of how many ``ticks'' are needed to evaluate the function
for the given input, called the |Thunk| monad. |Thunk : Nat ->
Universe -> Universe| is implemented as an abstract type that comes
with the following primitives:

\begin{itemize}
\item |step : (a : Universe) -> (n : Nat) -> Thunk n a -> Thunk (n+1) a|
\item |return : (a : Universe) -> (n : Nat) -> a -> Thunk n a|
\item |(>>=) : (a b : Universe) -> (n m : Nat) -> Thunk m a -> (a -> Thunk n b) -> Thunk (m + n) b|
\item |force : (a : Universe) -> (n : Nat) -> Thunk n a|
\end{itemize}

The user has to write its programs using these primitives. A similar
approach has also been used in \citet{twansorting} to count the number
of comparisons needed for various comparison-based sorting algorithms.

Using this to enforce a time bound on the decision procedure is not
entirely trivial. We first need to establish what kind of time limit
we want: do we want a constant time complexity, as we have with the
concrete collapsibility optimisation? If we want it to be
non-constant, on what variable do we want it to depend?

Apart from these questions, approaches such as the |Thunk| monad, are
prone to ``cheating'': we can just write our decision procedure the
normal way and then write |return 1 decisionProcedure| to make sure it
has the right type. To prevent this, we can deepen our embedding of
the programming language in such a way, that the users can write the
program completely in this language. Such a language, if it is
complete enough, will most likely make writing programs unnecessarily
complex for the user.

Even though we can internalise certain conditions under which certain
transformations are safe (preserve definitional equality), along with
the transformations, guaranteeing that this transformation actually
improves complexity proves to be a lot more difficult.

\section{Indexed \hprops and \hott}
\label{sec:indhprops}

In~\cref{sec:truncations} we have seen that \hprops are exactly those
types that obey proof irrelevance. If we generalise this internal
notion to the indexed case we arrive at something we previously have
called internal collapsibility. We have also seen that if we restrict
ourselves to the empty context, internal collapsibility implies
collapsibility. The purpose of the collapsibility optimisations is to
optimise the evaluation of terms in the empty context. In \hott
however, we postulate extra equalities in order to implement
univalence or \hits. ``Run-time'' for these programs does therefore
not mean evaluation in the empty context, but evaluation in a context
that can possibly contain the aforementioned postulates. To stress
this difference in what contexts we are considering to do the
evaluation in, we will talk about internal collapsible for the empty
context case and indexed \hprops in for the \hott case. In this
section we will investigate what these differences mean when trying to
optimise our programs.

When postulating extra propositional equalities, we obviously lose the
canonicity property, hence we can no longer say that propositional
equality implies definitional equality at run-time. The essence of the
concrete collapsibility optimisation is that we need not store certain
parts of our programs, because we know that they are unique, canonical
and can be recovered from other parts of our program. In \hott we no
longer have this canonicity property and may have to make choice in
what inhabitant we recover from the indices. As an example of this we
will compare two non-indexed types: the unit type and the
interval. Both types are \hprops, so they admit proof irrelevance, but
the interval does have two canonical inhabitants that can be
distinguished by definitional equality.

\begin{code}
  data I : Set where
    zero  : Interval
    one   : Interval

    segment : zero == one
\end{code}

The elimination operator for this type is defined in this way:

\begin{code}
  Ielim :  (B : I -> Universe)
          -> (b0 : B zero)
          -> (b1 : B one)
          -> (p : (transport B segment b0) == b1)
          -> (i : I) -> B i
\end{code}

with computation rules\footnote{Apart from giving computation rules
  for the points, we also need to give a computation rule for the path
  constructor, |segment|, but as we do not need this rule for the
  discussion here, we have left it out.}:

\begin{code}
  Ielim B b0 b1 p zero  === b0
  Ielim B b0 b1 p one   === b1
\end{code}

In other words, in order to eliminate a value in the interval, we need
to tell what has to be done with the endpoints interval and then
have to show that this is done in such a way that the path between the
endpoints is preserved.

Let us compare the above to the elimination operator for the unit
type, |top|:

\begin{code}
  topelim :  (B : top -> Universe)
          -> (b : B tt)
          -> (t : top) -> B t
\end{code}

with computation rule:

\begin{code}
  topelim B b tt === b
\end{code}

If we have canonicity, we can clearly assume every inhabitant of |top|
to be |tt| at run-time and erase the |t| argument from |topelim|. In
the case of |I|, we cannot do this: we have two canonical inhabitants
that are propositionally equal, but not definitionally.

Not all is lost, if we consider the non-dependent elimination operator
for the interval:

\begin{code}
  Ielimnondep :  (B : Universe)
          -> (b0 : B)
          -> (b1 : B)
          -> (p : b0 == b1)
          -> I -> B
\end{code}

then it is easy to see that all such functions are constant functions,
with respect to propositional equality. If we erase the |I| argument
and presuppose it to be |zero|, we will get a new function that is
propositionally equal to the original one. However, it is definitional
equality that we are after. We can define the following two functions:

\begin{code}
  Iid : I -> I
  Iid = Ielimnondep I zero one segment

  Iconstzero : I -> I
  Iconstzero = Ielimnondep I zero zero refl
\end{code}

If we presuppose and erase the |I| argument to be |zero| in the |Iid|
case, we would get definitionally different behaviour. In the case of
|Iconstzero|, it does not matter if we presuppose the argument to be
|zero| or |one|, since this function is also definitionally
constant. This is because for the |refl| to type check, |b0| and |b1|
have to definitionally equal. So if we want to optimise the
elimination operators of \hits that are \hprops, such as the interval,
we need to look at what paths the non-trivial paths are mapped to. If
these are all mapped to |refl|, then the points all get mapped to
definitionally equal points. 

\newpage

Suppose that |f| is the function that we are constructing using the
elimination principle of some \hit |H|, which happens to be a
\hprop. We want to verify that |ap f| maps every path to
|refl|. Checking this property can become difficult, as we can tell
from this rather silly example:

\begin{code}
  data nattruncated : Universe where
    0 : nattruncated
    S : (n : nattruncated) -> nattruncated

    equalTo0 : (n : nattruncated) -> 0 == n
\end{code}

with non-dependent eliminator:

\begin{code}
  nattruncatedelimnondep : (B : Universe)
              -> (b0 : B)
              -> (bS : B -> B)
              -> (p : (b : B) -> b0 == b)
              -> nattruncated -> B
\end{code}

If we were to check that all paths between |0| and |n| are mapped to
|refl|, we have to check that |p| satisfies this property, which we
cannot do.

\subsection{Internally optimising \hprops}

The optimisation given in~\cref{sec:intcolopt} of course still is a
valid transformation for the \hott case. The proof of a family |D : I
-> Universe| being an indexed \hprop is again not enough for us to be
able to write the term |optimiseFunction|. What we called
|isInternallyCollapsibleDecidable| is that we internally need a
witness of the fact that every \hprop in the family is either
contractible or empty, so we could have written the property as
follows:

\begin{code}
  isIndexedhPropDecidable : (I : Universe) (A : I -> Universe) -> Universe
  isIndexedhPropDecidable I A = (i : I) 
    -> (isContractible (A i)) oplus (A i -> bottom)
\end{code}

\newpage

\section{Conclusions}

In this chapter we have looked at various ways of dealing with types
that are purely logical, called propositions. Coq and Agda both
provide mechanisms to in a way ``truncate'' a type into a
proposition. The first takes this approach by allowing the user to
annotate a type as being a proposition when defining the type. Making
sure it is a proposition and has no computational effect on
non-propositions is handled by limiting the elimination of these
propositions: we may only eliminate into other propositions. Singleton
elimination is an exception to this rule, which does not play well
with \hott and the univalence axiom, as it means that the equality
used by Coq gets falsely recognised as a singleton type, even though
it is provably not one. Using univalence we can construct a term that
behaves differently in Coq as it does in the extracted version.

Agda allows the user to indicate that a type is a proposition when
referring to that type, instead of having to annotate it when defining
it. Agda enforces the proof irrelevance by ensuring that inhabitants
of an annotated type are never scrutinised in a pattern match and may
only be passed onto other irrelevant contexts. It contrast to Coq's
mechanism, it does not allow for singleton elimination, but unlike
Coq, it does enable the user to prove properties of the annotated
types in Agda itself. As such, we can construct a squash type that is
isomorphic to the \ntruncation{(-1)} from \hott, defined as a \hit.

Instead of truncating a type such that it becomes a proposition, we
can also let the compiler recognise whether a type is a proposition or
not. This is the approach that the collapsible families optimisation
takes in Epigram. The definition of collapsibility is reminiscent of
the definition of \hprop, albeit it an indexed version that uses
definitional equality instead of propositional equality. The
optimisation specifically focuses on families of
propositions. 

Recognising whether an inductive family is a collapsible family is
undecidable, so the actual optimisation restricts itself to a subset
called concretely collapsible families. To improve on this, we
internalise the notion of collapsibility, allowing the user to provide
a proof if the compiler fails to notice this property. We show that
this notion of internal collapsibility is a subset of
collapsibility. We also try to internalise the optimisation, but since
the time complexity of the optimised function heavily depends on the
user-provided proof, we cannot be sure whether it the ``optimised''
version actually improves on the complexity. We have looked at ways to
enforce time complexities in the user-provided proofs. Our conclusion
is that this is not viable.

Collapsible families look a lot like families of \hprops. When
internalising the collapsibility concept and the optimisation, we only
considered the non-\hott case, \ie no univalence and no \hits. We have
looked at extending the optimisations to the \hott case, but as we
lose canonicity the optimised versions may no longer yield the same
results as the original function, with respect to definitional
equality. We have identified cases in which this is the case and cases
in which definitional equality actually is preserved. We also argue
that detecting such cases is undecidable.
