\chapter{Applications of homotopy type theory}

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
\emph{view}. This approach was introduced by \citep{wadlerview} as a
way to do pattern matching on abstract types. 

