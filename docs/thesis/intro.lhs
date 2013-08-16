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

The discovery was that propositional equality behaves just like
the homotopy we know from topology. This discovery spawned a lot of
interest, as it meant that type theory can be used to prove theorems
about homotopy theory.

\begin{quote}
  \todoi{Research question (roughly): what is homotopy type theory and
    (why) is it interesting for programming?}
\end{quote}

 \begin{itemize}
 \item \todoi{Contribution chapter~\autoref{chap:hottintro} introduction homotopy type theory}
 \item \todoi{Contribution chapter~\autoref{chap:applications} applications homotopy type theory}
 \item \todoi{Contribution chapter~\autoref{chap:erasure} on erasing propositions}
 \end{itemize}

\todoi{Discussion chapter~\autoref{chap:discussion}}

\todoi{Since the focus is on programming aspects of \hott, as opposed
  to doing homotopy theory, we won't do any diagram chasing and
  instead will use Agda syntax throughout the thesis. As such, we will
  expect the reader to be familiar with this.}

\todoi{Mention |A : Universe| versus |A : Set| thing and that we will
  omit levels.}

\todoi{Mention that there is no pattern matching in \MLTT and that we
  will abuse the \verb+--without-k+ flag.}

\todoi{Guide to source code appendix~\autoref{chap:code}}

