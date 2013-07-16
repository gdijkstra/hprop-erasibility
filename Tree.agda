module Tree where

open import Empty
open import UnitVersusInterval

data Tree : Set where
  Leaf : Tree
  Bin : Tree -> Tree -> Tree

R : Tree -> Tree -> Set
R Leaf Leaf = ⊤
R Leaf (Bin _ _) = ⊥
R (Bin _ _) Leaf = ⊥
R (Bin l l₁) r = {!!}
