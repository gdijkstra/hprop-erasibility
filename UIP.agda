module UIP where

open import Identity

-- We can easily prove uniqueness of identity proofs using dependent
-- pattern matching. Obviously, this does not type check with the
-- --without-K flag.
uip : (A : Set) (x y : A) (p q : Id A x y) -> Id (Id A x y) p q
uip A x .x refl refl = refl
