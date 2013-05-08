\chapter{Erasing propositions}

When writing programs in a dependently typed setting, it can easily
happen that there is no clear separation between the parts that
describe the computation and the parts that show that our computation
satisfies certain properties. Mixing these two concerns even has its
advantages. \todoi{What advantages exactly? Externalist versus
  internalist?} Or we have to provide extra computations to be able to
model functions that are not structurally recursive in our type
theory. \todoi{Add citation} At run-time, these parts that have helped
us pass the type checking phase, have already served their purpose and
are now dead weight. We want some way to be able to tell these parts
of our program apart so that we can ignore or \emph{erase} them at
run-time, without affecting the outcome of the
computation. \todoi{Note that we will not formally define erasure
  here, because the (meta)theories are too far apart and stuff.}

\todoi{Introduce propositions}

\todoi{Motivating examples: Bove-Capretta, \sigmatypes (also called
  subset types?), types that admit proof irrelevance.}

\section{The sort \coqprop in Coq}

\todoi{Motivating example in Coq}

\todoi{Show how the extracted version looks like}

\todoi{Note the limitations of what we can eliminate into}

\todoi{Impredicativity}

\todoi{Proof irrelevance can be assumed?}

\todoi{Proof irrelevance not enforced}

\todoi{Example of how things can go wrong}

\todoi{Singleton elimination}

\todoi{We can get the Bove-Capretta thing to work in such a way that
  the extracted version is like the original.}

\section{Irrelevance in Agda}

\todoi{Motivating example in Agda}

\todoi{Allows for run-time behaviour optimisations? e.g. it is
  actually used in the compilation pipeline or something?}

\todoi{Has some form of singleton elimination?}

\todoi{Can we it to have some form of proof irrelevance? Or that they
  are somewhat like \hprops?}

\todoi{Squash type: \ntruncation{(-1)}}

\section{Collapsible families}

Instead of letting the user annotate the programs to indicate what
parts are irrelevant to the computation at hand, \cite{collapsibility}
propose a series of optimisations, for the language Epigram, based on
the observation there is a lot of redundancy in well-typed programs,
hence some parts can be erased as they can recovered from other parts.

\todoi{Note that we are working in Epigram, even though we can write
  things in a dependent pattern matching style, everything gets
  \emph{elaborated} to a smaller language, which is very close to
  conventional \MLTT along with inductive families (Dybjer?).}

\todoi{Vec example: show that we indeed have a lot of duplication,
  even though there's a lot of arguments that can be recovered from
  others, so we can leave stuff out.}

\todoi{Not a language construct: instead of marking things as being a
  \coqprop or as irrelevant, the compiler itself figures out whether
  it is irrelevant or not.}

\todoi{Recover values of inductive families via their indices.}

\todoi{Needs the \emph{adequacy} property to hold, which breaks if we
  do \hott.}

\todoi{Bove-Capretta works nicely, really the way we want it to, as
  opposed to the Coq thing.}

\todoi{How about \sigmatypes? It does not apply to that. (Neither do
  any of the other optimisations in that paper?)}

\section{\hprops}

\todoi{As we have seen, \hprops admit all kinds of interesting
  properties: impredicativity and all that.}

\todoi{Can \emph{almost} be seen as an internalised version of
  collapible families.}

\todoi{Internal to the type theory: the user can show that things as
  \hprops.}

\todoi{Can we do some sort of singleton elimination?}

\todoi{Does the \sigmatypes example work?}

\todoi{How does it relate to Agda's irrelevance?}
