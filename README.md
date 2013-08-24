Programming in homotopy type theory and erasing propositions
============================================================

This project's goal is to find out whether we can devise useful
conditions under which hProp can be erased, as a run-time
optimisation. Since the definition of hProp looks a lot like Edwin
Brady's concept of collapsibility, we will study his work and check if
his results are still sensible and correct when applied to hProp.

This turns out to not be the case: since we no longer can easily tell
when propositional and definitional equality coincide at run-time, the
optimisations will not work.

Apart from this, we will provide an introduction to homotopy type
theory aimed specifically towards computer scientists, as opposed to
mathematicians. As such, the focus will be on programming applications
of new concepts such as higher inductive types and univalence, instead
of studying models of the type theory.

A syntax-highlighted and browsable version of the code can be found [here](http://gdijkstra.github.io/hprop-erasibility).
