{-# OPTIONS --without-K #-}

open import Identity
open import Sigma
open import Levels

module RetractIso (A B : Set) (r : A -> B) (s : B -> A) (is-retract : (x : B) -> r (s x) ≡ x) where

-- Sigma part
A' : Set
A' = Σ A (λ x → s (r x) ≡ x)

to-A' : A -> A'
to-A' x = (s (r x)) , ap s (is-retract (r x))

from-A' : A' -> A
from-A' x = Σ.fst x

r' : A' -> B
r' x = r (from-A' x)

s' : B -> A'
s' x = to-A' (s x)

s'-right-inverse : (x : B) -> r' (s' x) ≡ x
s'-right-inverse x = trans (is-retract (r (s x))) (is-retract x)

postulate
  uip-A : {x y : A} (p q : x ≡ y) -> p ≡ q

s'-left-inverse : (x : A') -> s' (r' x) ≡ x
s'-left-inverse (fst , snd) = Σ-≡ (trans (ap (λ x → s (r x)) snd) snd) (uip-A (transport {B = (λ x → s (r x) ≡ x)} (trans (ap (λ z → s (r z)) snd) snd)
                                                                                 (ap s (is-retract (r (s (r fst)))))) snd)

-- Quotient part
retract-rel : A -> A -> Set
retract-rel x y = r x ≡ r y

retract-rel-refl : (x : A) -> retract-rel x x
retract-rel-refl x = refl

open import QuotientUntruncated A retract-rel retract-rel-refl

A/~ : Set
A/~ = Quotient 

to-A/~ : A -> A/~
to-A/~ x = box x

-- Identity won't work. If it did, we'd be done already.
from-A/~ : A/~ -> A
from-A/~ = Quotient-rec (λ x → s (r x)) (λ x y p → ap s p)

r~ : A/~ -> B
r~ x = r (from-A/~ x)

s~ : B -> A/~
s~ x = to-A/~ (s x)

s~-right-inverse : (x : B) -> r~ (s~ x) ≡ x
s~-right-inverse x = trans (is-retract (r (s x))) (is-retract x)

s~-left-inverse : (x : A/~) -> s~ (r~ x) ≡ x
s~-left-inverse x = Quotient-ind {B = λ x~ → s~ (r~ x~) ≡ x~} (λ x~ → quot (s (r (s (r x~)))) x~ (trans (is-retract (r (s (r x~)))) (is-retract (r x~)))) (λ x₁ y p → {!!}) x 
-- the hole can be solved with UIP that A/~ satisfies. (retract-rel is
-- an equivalence relation.)
