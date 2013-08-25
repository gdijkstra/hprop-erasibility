\chapter{Introduction}
\label{chap:intro}

One of the tricky things that comes up sooner or later when one
designs a type system or a logic, is the defining a right notion of
equality. When type checking a term, one needs a suitable concept of
equality, \eg when one type checks an application |f a| and we know
that |f : A -> B| and we know that |a : X|, we have to check that |A|
and |X| are equal in some way. In \MLTT \citep{mltt}, |A| and |X| need
to be \emph{definitionally equal} (denoted in this thesis by |A ===
X|): if we reduce both |A| and |X| to their normal forms, they need to
be syntactically equal.

We also want to be able to reason about equality in the type theory
itself: we want to use it in our programs (or proofs) written in the
type theory language, \eg to show that two programs behave in the same
way, when given the same input. If we have a version of a
meta-theoretical concept, such as definitional equality, that can be
expressed in the language of type theory itself, we call such a
version of the concept \emph{internal}. The notion of equality
internal to a type theory is called a \emph{propositional equality}
(in this thesis denoted by |==|). In \MLTT, propositional equality is
defined using the so called \emph{identity types}: an inductive family
with |refl| as its only constructor. This construction essentially
imports definitional equality into the type theory. However, the
resulting structure is not exactly definitional equality: as we will
see at various points in this thesis, it is valid to add as axioms
extra propositional equalities between terms that are not
definitionally equal.

We can force the two notions to coincide by adding an \emph{equality
  reflection} rule, \ie a rule that states that if we have a proof |p
: x == y| are propositionally equal, then |x === y| also holds. Since
type checking makes use of definitional equality, to show that two
terms are definitionally equal, we may need to produce a proof of
propositional equality first. This proof search means that type
checking becomes undecidable. Even though it is undecidable in
general, it still works out for enough cases to be useful, as is
exemplified by Nuprl \citep{nuprl}. One advantage of adding equality
reflection is that we can prove useful things such as function
extensionality (|((x : A) -> f x == g x) -> f == g|), something that
we cannot prove if we leave the equality reflection rule out.

The study of \emph{intensional type theory}, \ie type theory without
the equality reflection rule, involves finding out why we cannot prove
certain properties about propositional equality that are deemed to be
natural properties for a notion of equality, such as function
extensionality and \UIP. This eventually led to the discovery of
\hott, an interpretation of types and their identity types in the
language of homotopy theory:

\homotopyinterpretation

The discovery was that propositional equality behaves just like the
homotopy we know from topology. This discovery spawned a lot of
interest, as it meant that the language of type theory can be used to
prove theorems about homotopy theory. It is also regarded as an
interesting foundation of mathematics, as it makes working with
isomorphic structures a lot more convenient than foundations based on
set theory. There are already several introductions on the subject
(\eg \citet{awodeysurvey}, \citet{pelayosurvey} and
\citet{rijkehott}). There has been a special year in 2012--2013 on the
subject at the Institute of Advance Study in Princeton, which has
culminated in a book \citep{hottbook}, giving a very complete overview
of the results. The focus of these materials is on \hott as a
foundation of mathematics and its use in formalising mathematics.

The materials mentioned above assume the reader to have experience
with homotopy theory and none with type theory. In this thesis instead
assumes the reader to have experience with using a dependently typed
language such as Agda as a programming language for certified
programs, but have no background in homotopy theory. This leads us to
the main research question of this thesis:

\researchquestionA

In~\cref{chap:hottintro} we give an introduction and overview of
some of the main concepts of \hott. In this chapter we will also
provide a very short introduction into topology and homotopy theory,
to give a bit of intuition behind the terminology and where the
concepts come from. In~\cref{chap:applications} we discuss several
applications of \hott to programming. In particular we look at how we
can implement quotient types in \hott and contrast this to other ways
to work with quotient types. Another application we consider is the
use of univalence to deal with views on abstract types. We work out
the examples given by~\citet{licataview} and extend the result to
non-isomorphic views, using quotient types.

\Hott provides us with a notion of propositions, the so called
\hprops. In~\cref{chap:erasure} we compare this to similar notions
found in Coq, Agda and Epigram. We investigate whether we can
formulate an optimisation based on \hprops in the spirit of the
collapsibility optimisation proposed in~\citet{collapsibility}.

In the final chapter, \cref{chap:discussion}, we will discuss our
answers to our research questions and propose directions of future
research.

Since the focus of this thesis is on the programming aspects of \hott,
as opposed to doing homotopy theory, we will not do any diagram
chasing and instead will use Agda syntax throughout the thesis. As
such, we will expect the reader to be familiar with this language.

\paragraph{Notation} 

We will use Agda syntax for most of the code in this thesis, except
for some parts in~\cref{chap:erasure}. The code will not always
be valid Agda syntax. We will use the notation |A : Universe| instead
of |A : Set|, in order to avoid confusion between types and the \hott
notion of \hsets. We will also refrain from mentioning levels and
essentially assume that these are automatically inferred. For
\sigmatypes, we will sometimes use the notation |Sigma (x : A) dot B x|
instead of |Sigma A (\ x -> B x)|, for brevity.

\paragraph{Code} 

The accompanying code can be found in the appropriate {\textsc GitHub}
repository\footnote{\url{https://github.com/gdijkstra/hprop-erasibility}
  and for a browsable variant with syntax colouring:
  \url{http://gdijkstra.github.io/hprop-erasibility/}}. The file
\verb+index.agda+ lists for each chapter the modules that contain code
relevant to the chapter.
