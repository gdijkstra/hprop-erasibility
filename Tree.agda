module Tree where

open import Empty
open import UnitVersusInterval
open import Identity
open import Naturals

data Tree : Set where
  Leaf : Tree
  Bin : Tree → Tree → Tree

countLeaves : Tree → ℕ
countLeaves Leaf = 1
countLeaves (Bin l r) = S (countLeaves l + countLeaves r)

R : Tree → Tree → Set
R l r = countLeaves l ≡ countLeaves r

assocTree : (a b c : Tree) → R (Bin a (Bin b c)) (Bin (Bin a b) c)
assocTree a b c = {!!} -- use the omega tactic...
