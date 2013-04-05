module UIP where

data Id (A : Set) (x : A) : A → Set where
  refl : Id A x x

-- We can easily prove uniqueness of identity proofs using dependent
-- pattern matching.
uip : (A : Set) (x y : A) (p q : Id A x y) -> Id (Id A x y) p q
uip A x .x refl refl = refl
