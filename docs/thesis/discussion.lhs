\chapter{Discussion}
\label{chap:discussion}

One of the main goals of this project was to establish whether \hott
is an interesting language to do dependently typed programming in. As
it is incompatible with dependent pattern matching in general, it
seems like we are taking a step backwards. However, univalence and
\hits can become the two steps forward. Univalence means that we can
transport definitions along isomorphisms, which saves us a great deal
of writing boring code applying the |to| and |from| parts of the
isomorphisms in the right places. It also implies function
extensionality, which is indispensable when proving properties about
programs.

We have also seen the usefulness of \hits. They allow us to define
quotient types. It is all too easy to come up with a \hit that has
more structure than is desired: one quickly runs into \emph{coherence
  issues}: the resulting type has too many different equalities at
higher levels than is needed. The original definition of quotient
types also suffered from this issue: we want it to be a \hset, but as
could be seen from a simple example, one could easily define the
circle: the simplest type that is not a \hset. Therefore one usually
needs to truncate the \hit to a certain level, \eg take the
\ntruncation{0} in the case of quotients. Truncating a type does mean
that we have extra conditions that we need to satisfy when eliminating
something of that particular type. In a programming setting, one
typically only encounters \hsets, except for univalent universes of
\hsets. Eliminating into a \hset means that the extra conditions
stemming from \ntruncation{0} are automatically satisfied, so in
programming this need not be too much of a problem.

For these two steps to be actual steps forward, there is still a lot
of work that needs to be done. The most obvious and possibly most
difficult problem is determining the computational content of the
univalence axiom. Seeing as most types in programming applications are
\hsets, it is already a big improvement if we get this to work for a
type theory in which everything is \ntruncated{1} and the only
\ntype{1} which is not a \hset is a univalent universe of all \hsets.

Giving up pattern matching altogether is quite drastic. There are
still a lot of cases in which (dependent) pattern matching is still
valid and can be transformed to an expression using only elimination
principles. An interesting future research direction is to take the
elaboration process described in
\citet{eliminatingdependentpatternmatching}, which critically depends
on axiom |K| \todo{that computes}, and see how one can uncover
conditions in which |K| is not necessary for the elaboration to work.

There is also a lot of work to be done on \hits. As of yet, a
well-defined syntax for \hits and a generic way to derive the
induction principles is lacking. It has also been
noted~\citep{reducinghits} that every \hit that has higher path
constructors in its definition, can be rewritten to an equivalent form
that only has path constructors that construct paths between points (a
so called \onehit). Having a mechanism that automatically translates
the definition of a \hit to a \onehit, also means that we only have to
care about these cases when devising induction principles. Having a
form of pattern matching for \hits is also a research direction that
can help make \hits significantly more easy to work with.

In~\cref{chap:erasure}, we have seen that in traditional \MLTT,
propositional equality coincides with definitional equality at
``run-time'' (\ie in the empty context). This property makes it
possible to internalise optimisations: one could create a system in
which we provide rules to the compiler akin to the \ghcrewriterules
\citep{ghcrewrite}, but along with a proof of correctness. In \hott,
we also want to have non-canonical proofs of propositional equality at
run-time, so we lose this property. A further investigation of when
propositional equality still does imply definitional equality might be
an interesting research direction. Another interesting thing to look
at is the question whether we really need definitional equality, \ie
identify cases in which we can safely replace something by something
else that is propositionally but not necessarily definitionally equal.

Coming back to the main research question:

\researchquestionA

In this thesis, we have given evidence that \hott is an interesting
language to program in, but as of yet we have to sacrifice too much
(\ie dependent pattern matching and canonicity in its entirety) for it
to be useful for programming right now, but the future looks
promising, even if we only get to implement restricted versions of
\hott.
