\chapter{Erasing propositions}

When writing certified programs in a dependently typed setting, we can
conceptually distinguish between the \emph{program} parts and the
\emph{proof} (of correctness) parts. These are sometimes also referred
to as the informative and logical parts, respectively. In practice,
these two seemingly separate concerns are often intertwined. Consider
for example the sorting of lists of naturals: given some predicate
|isSorted : List Nat -> List Nat -> Universe| that tells us whether
the second list is a sorted permutation of the first one, we can to
write a term of the following type:

\begin{code}
  sort : (xs : List Nat) -> Sigma (ys : List Nat) (isSorted xs ys)
\end{code}

To implement such a function, we need to provide for every list a
sorted list along with a proof that this is indeed a sorted version of
the input list. At run-time the type checking has been done, hence the
proof of correctness has already been verified: we want to
\emph{erase} the logical parts.

Types such as |isSorted xs ys| are purely logical: we care more about
the presence of an inhabitant than what kind of inhabitant we exactly
have at our disposal. In section~\ref{sec:props} we will give more
examples of such types, called \emph{propositions}, and how they can
occur in various places in certified programs. In
sections~\ref{sec:coqprop} and~\ref{sec:irragda} we review the methods
Coq and Agda provide us to annotate parts of our program as being
propositions. Section~\ref{sec:colfam} reviews the concept of
\emph{collapsible families} and how we can automatically detect
whether a type is a proposition, instead of annotating them
ourselves. In section~\ref{sec:intcol} we internalise the concept of
collapsible families and try to do the same with the optimisation in
section~\ref{sec:intcolopt}. The internalised version of
collapsibility looks like an indexed version of the concept of
\hprops. In section~\ref{sec:indhprops} we investigate if we can use
this to devise an optimisation akin to the optimisation based on
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
universe. Both universes are base sorts of the hierarchy of sorts,
\coqtype, \ie |Prop : Type(1)|, |Set : Type(1)| and for
every |i|, |Type(i) : Type(i+1)|.  As the name suggests, by
defining a type to be of sort \coqprop, we ``annotate'' it to be a
logical type, a proposition. Explicitly marking the logical parts like
this, makes the development easier to read and understand. More
importantly, the extraction mechanism~\citep{letouzeyextraction} now
knows what parts are supposed to be logical, hence what parts are to
be erased.

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

Singleton elimination allows us to pattern match on |path| and
and eliminate into something of sort |Type|. In the extracted
version, the |path| argument gets erased and the |P x|
argument is returned. In \hott, we know that the identity types need
not be singletons and can have other inhabitants than just the
canonical |refl|, so throwing away the identity proof is not
correct. As has been discovered by Michael
Shulman\footnote{\url{http://homotopytypetheory.org/2012/01/22/univalence-versus-extraction/}},
singleton elimination leads to some sort of inconsistency, if we
assume the univalence axiom: we can construct a value |x : bool|
such that we can prove |x = false|, even though in the extracted
version |x| normalises to |true|. Assuming univalence, we
have two distinct proofs of |bool = bool|, namely |refl| and
the proof we get from applying univalence to the isomorphism
|not : bool -> bool|. Transporting a value along a path we have
obtained from using univalence, is the same as applying the
isomorphism. Defining |x| to be |true| transported along the
path obtained from applying univalence to the isomorphism |not|,
yields something that is propositionally equal to |false|. If we
extract the development, we get a definition of |x| that ignores
the proof of |bool = bool| and just returns |true|.

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
if and only if $R \not\in R$. In type theory, an analogous paradox,
Girard's paradox, arises if we allow for impredicativity via the
|Universe : Universe| rule. However, impredicative definitions are
sometimes very useful and benign, in particularly when dealing with
propositions: we want to be able to write propositions that quantify
over propositions, for example:

\begin{code}
  Definition demorgan : Prop := forall P Q : Prop, 
    ~(P /\ Q) -> ~P \/ ~Q.
\end{code}

Coq allows for such definitions as the restrictions on \coqprop
prevent us from constructing paradoxes such as Girard's.

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

To ensure that irrelevant arguments are indeed irrelevant to the
computation at hand, Agda has several criteria that it checks. First
of all, no pattern matching may be performed on irrelevant arguments,
just as is the case with \coqprop. (However, the absurd pattern may
be used, if applicable.)  Contrary to Coq, singleton elimination is
not allowed.  Secondly, we need to ascertain that the annotations are
preserved: irrelevant arguments may only be passed on to irrelevant
contexts. This prevents us from writing a function of type |.A ->
A|.

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
                              →  (f : .A → B) → (x y : A) → f x ≡ f y
  irrelevantConstantFunction f x y = refl
\end{code}

There is no need to use the congruence rule for |≡|, since the |x| and
|y| are ignored when the type checker compares |f x| to |f y|, when
type checking the |refl|. The result can be easily generalised to
dependent functions:

\begin{code}
  irrelevantConstantDepFunction  :  {A : Universe} {B : .A → Universe} 
                                 →  (f : .(x : A) → B x) → (x y : A) → f x ≡ f y
  irrelevantConstantDepFunction f x y = refl
\end{code}

Note that we do not only annotate |(x : A)| with a dot, but also
occurrence of |A| in the type |B : A -> Universe|, otherwise we are
not allowed to write |B x| as we would use an irrelevant argument in a
relevant context. When checking |irrelevantConstantDepFunction|, the
term |f x ≡ f y| type checks, without having to transport one value
along some path, because the types |B x| and |B y| are regarded as
definitionally equal by the type checking, ignoring the |x| and
|y|. Just as before, there is no need to use the (dependent)
congruence rule; a |refl| suffices.

We would also like to show that we have proof irrelevance for
irrelevant arguments, \ie we want to prove the following:

\begin{code}
  irrelevantProofIrrelevance : {A : Universe} .(x y : A) → x ≡ y
\end{code}

Agda does not accept this, because the term |x == y| uses irrelevant
arguments in a relevant context: |x == y|. If we instead package the
irrelevant arguments in an inductive type, we can prove that the two
values of the packaged type are propositionally equal. Consider the
following record type with only one irrelevant field:

\begin{code}
  record Squash (A : Universe) : Universe where
    constructor squash
    field
      .proof : A
\end{code}

Using this type, we can now formulate the proof irrelevance principle
for irrelevant arguments and prove it:

\begin{code}
  squashProofIrrelevance : {A : Universe} (x y : Squash A) → x ≡ y
  squashProofIrrelevance x y = refl
\end{code}

The name ``squash type'' comes from Nuprl~\citep{nuprl}: one takes a
type and identifies (or ``squashes'') all its inhabitants into one
unique (up to propositional equality) inhabitant. In \hott the process
of squashing a type is called \ntruncation{(-1)} and can also be
achieved by defining the following \hit:

\begin{code}
  data minusonetruncation (A : Universe) : Universe where
    inhab : A

    allpaths : (x y : A) → x ≡ y
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
  ltelim P mZ mS 0      (S y)  (ltZ y)        ~>  mZ y
  ltelim P mZ mS (S x)  (S y)  (ltS x y pf)   ~>  mS x y pf (ltelim P mZ mS x y pf)
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

If |D| is a collapsible family, then its elimination operator |D-elim|
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
determining collapsibility in general, which is undecidable. In this
section we investigate if we can formulate an internal version of
collapsibility, enabling the user to give a proof that a certain
family is collapsible, if the compiler fails to notice so itself.

Recall the definition of a collapsible family\footnote{The definition
  we originally gave allowed for an arbitrary number of indices. In
  the following sections we will limit ourselves to the case where we
  have only one index for presentation purposes. All the results given
  can be easily generalised to allow more indices.} : given an
inductive family |D| indexed by the type |I|, |D| is collapsible if
for every index |i : I| and terms |x|, |y|, the following holds:

\begin{code}
  /- x, y : D i implies /- x === y
\end{code}

This definition makes use of definitional equality. Since we are
working with an intensional type theory, we do not have the
\emph{equality reflection rule} at our disposal: there is no rule that
tells us that propositional equality implies definitional
equality. This might lead us to think that internalising the above
definition will not work, as we seemingly cannot say anything about
definitional equality from within \MLTT. Let us consider the following
variation: for all terms |x|, |y| there exists a term |p| such that

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

\newpage

\section{Internalising the collapsibility optimisation}
\label{sec:intcolopt}

In section~\ref{sec:erasecolfam} we saw how concretely collapsible
families can be erased, since all we want to know about the
inhabitants can be recovered from its indices. In this section we will
try to uncover a similar optimisation for internally collapsible
families.

We cannot simply erase the internally collapsible arguments from the
function we want to optimise, \eg given a function |f : (i : I) -> (x
: D i) -> tau|, we generally cannot produce a function
|fsnake : (i : I) -> tau|, since we sometimes need
the |x : D i| in order for the function to
typecheck. However, we can use Agda's irrelevance mechanism to instead
generate a function in which the collapsible argument is marked as
irrelevant, \ie we want to write the following function (for the
non-dependent case):

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
inhabitants of every |D i| are related to eachother with propositional
equality. From this proof we cannot tell whether some |D i| is
inhabited or empty.

\todoi{something about situation with concretely collapsible families}

If we extend the definition of internal collapsibility with something
that decides whether |A i| is empty or not, we get the following
definition:

\begin{code}
  isInternallyCollapsibleDecidable : (I : Universe) (A : I -> Universe) -> Universe
  isInternallyCollapsibleDecidable I A = (i : I) 
    -> (((x y : A i) -> x == y) otimes (A i oplus A i -> bottom))
\end{code}

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
we need a bound on the time complexity of this procedure. One
approach, taken in \cite{timecomplexity} to prove time complexities of
functions, is to write the functions with a monad that keeps track of
how many ``ticks'' are needed to evaluate the function for the given
input, called the |Thunk| monad. |Thunk : Nat -> Universe -> Universe|
is implemented as an abstract type that comes with the following
primitives:

\begin{itemize}
\item |step : (a : Universe) -> (n : Nat) -> Thunk n a -> Thunk (n+1) a|
\item |return : (a : Universe) -> (n : Nat) -> a -> Thunk n a|
\item |>>= : (a b : Universe) -> (n m : Nat) -> Thunk m a -> (a -> Thunk n b) -> Thunk (m + n) b|
\item |force : (a : Universe) -> (n : Nat) -> Thunk n a|
\end{itemize}

The user has to write its programs using these primitives. A similar
approach has also been used by van
Laarhoven\footnote{http://twanvl.nl/blog/agda/sorting} to count the
number of comparisons needed for various comparison-based sorting
algorithms.

Using this to enforce a time bound on the decision procedure is not
too trivial. We first need to establish what kind of time limit we
want: do we want a constant time complexity, as we have with the
concrete collapsibility optimisation? If we want it to be
non-constant, on what variable do we want it to depend?

Apart from these questions, approaches such as the |Thunk| monad, are
prone to cheating: we can just write our decision procedure the normal
way and then write |return 1 decisionProcedure| to make sure it has
the right type. To prevent cheating, we can extend the list of
primitives in such a way, that the users can write the program
completely in this language. Such a language, if it is complete
enough, will most likely make writing programs unnecessarily complex
for the user.

Even though we can internalise certain conditions under which certain
transformations are safe (preserve definitional equality), along with
the transformations, guaranteeing that this transformation actually
improves complexity proves to be a lot more difficult.

\section{Indexed \hprops and \hott}
\label{sec:indhprops}

In section~\ref{sec:hprop} we have seen that \hprops are those types
that obey proof irrelevance. We can generalise this to the indexed
case as follows: a family |D : I -> Universe| is an indexed \hprop if
for every index |i : I|, |D i| is an \hprop. This definition is
exactly the definition internal collapsibility. For internal
collapsibility, however, we only considered optimising evaluation in
the empty context. In \hott, we are also interested in evaluation in
non-empty context, since we have to deal with all these postulated
equalities arising from univalence and higher inductive types. This
means we can no longer exploit canonicity to say something about the
relationship between propositional and definitional equality. We can
also no longer use it to make assumptions about our terms

To see how propositional and definitional equality can diverge, we
will first consider the non-indexed case.


\section{Conclusion and future work}

