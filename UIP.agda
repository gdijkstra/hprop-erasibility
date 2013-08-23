module UIP where

open import Identity

-- We can easily prove uniqueness of identity proofs using dependent
-- pattern matching. Obviously, this does not type check with the
-- --without-K flag.
uip : (A : Set) (x y : A) (p q : Id A x y) → Id (Id A x y) p q
uip A x .x refl refl = refl

K  :   (A : Set) (x : A) (P : Id A x x → Set)
   →  P refl
   →  (c : Id A x x)
   →  P c
K A x P p-refl refl = p-refl

uip⇒K : (A : Set) (x : A) (P : Id A x x → Set)
   →  P refl
   →  (c : Id A x x)
   →  P c
uip⇒K A x P p-refl c = transport {B = P} refl≡c p-refl
  where 
    refl≡c : refl ≡ c
    refl≡c = uip A x x refl c

-- Since we can prove UIP with dependent pattern matching, this
-- amounts to a proof of UIP using K, using the McBride elaboration of
-- pattern matching.
