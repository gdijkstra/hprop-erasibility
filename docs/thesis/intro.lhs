\chapter{Introduction}
\label{chap:intro}

One of the tricky things that comes up when designing a type system or
a logic, is the defining a right notion of equality. When type
checking a term, one needs a notion of equality, called
\emph{definitional equality}, in this thesis denoted by |===|. For
example when one type checks an application |f a| and we know that |f
: A -> B| and we know that |a : X|, we have to check that |A| and |X|
are equal in some way. In \MLTT, |A| and |X| need to be definitionally
equal: if we reduce both |A| and |X| to their normal forms, they need
to be syntactically equal.

We also want to be able to reason about equality in the type theory
itself, \eg use it to show that two programs behave in the same way,
when given the same input. The notion of equality internal to the type
theory is called \emph{propositional equality} (in this thesis denoted
by |==|). In \MLTT, propositional equality is defined using the so
called \emph{identity types}: an inductive family with |refl| as its
only constructor. This construction essentially imports definitional
equality into the type theory.

However, the resulting structure is not exactly definitional
equality. We can force the two notions to coincide by adding an
\emph{equality reflection} rule, \ie a rule that states that if we
have a proof that |x| and |y| are propositionally equal, they are also
definitionally equal. Since type checking makes use of definitional
equality, to show that two terms are definitionally equal, we may need
to produce a proof of propositional equality first. This proof search
means that type checking becomes undecidable. However, adding equality
reflection does mean that we can prove useful things such as function
extensionality (|((x : A) -> f x == g x) -> f == g|), something that
we cannot prove if we leave the equality reflection rule out.

The study of intensional type theory, \ie type theory without the
equality reflection rule, involved finding out why we cannot prove
certain properties about propositional equality that were deemed to be
natural properties for a notion of equality. This eventually led to
the discovery of \hott, an interpretation of types and their identity
types in the language of homotopy theory:

\homotopyinterpretation

The discovery was that propositional equality behaves just like the
homotopy we know from topology. This discovery spawned a lot of
interest, as it meant that the language of type theory can be used to
prove theorems about homotopy theory. It also means that we can use
our intuition about homotopy theory to make statements about type
theory. For example, one question that has remained unanswered for
nearly two decades, the question why \UIP cannot be proven using |J|,
can now be answered by drawing a couple of pictures
(see~\autoref{sec:interpret}).

This leads us to the main research question:

\researchquestionA

In~\autoref{chap:hottintro} we give an introduction and overview of
some of the main concepts of \hott. In~\autoref{chap:applications} we
discuss several applications of \hott to programming. In particular we
look at how we can implement quotient types in \hott and contrast this
to popular ways to work with quotient types. Another application we
consider is the use of univalence to deal with views on abstract
types. We work out the example given by~\citet{licataview} and extend
the result to non-isomorphic views, using quotient types.

\Hott provides us with a notion of propositions, the so called
\hprops. In~\autoref{chap:erasure} we compare this to similar notions
found in Coq, Agda and Epigram. 

We investigate whether we can formulate an optimisation based on
\hprops in the spirit of the collapsibility optimisation proposed
in~\citet{collapsibility}.

In the final chapter, \autoref{chap:discussion}, we will discuss our
answers to our research questions and propose directions of future
research.

Since the focus of this thesis is on the programming aspects of \hott,
as opposed to doing homotopy theory, we will not do any diagram
chasing and instead will use Agda syntax throughout the thesis. As
such, we will expect the reader to be familiar with this language.

\paragraph{Notation} The code in the thesis will not always be valid
Agda code. We will use the notation |A : Universe| instead of |A :
Set|, in order to avoid confusion between types and the \hott notion
of \hsets. We will also refrain from mentioning levels and essentially
assume |Universe : Universe|. The accompanying will explicitly mention
the levels.

\paragraph{Code} Look at \verb+README.agda+.
