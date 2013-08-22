{-# OPTIONS --without-K #-}

open import Identity
open import Sigma
open import Levels

module RetractIso (A B : Set) (r : A -> B) (s : B -> A) (is-retract : (x : B) -> r (s x) ≡ x) where

module QuotientConstruction where
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

  postulate
    uip-A/~ : {x y : A/~} (p q : x ≡ y) → p ≡ q

  s~-left-inverse : (x : A/~) -> s~ (r~ x) ≡ x
  s~-left-inverse x = Quotient-ind {B = λ x~ → s~ (r~ x~) ≡ x~} (λ x~ → quot (s (r (s (r x~)))) x~ (trans (is-retract (r (s (r x~)))) (is-retract (r x~)))) (λ x₁ y p → uip-A/~
                                                                                                                                                                          (transport {B = λ x~ → s~ (r~ x~) ≡ x~} (quot x₁ y p)
                                                                                                                                                                           (quot (s (r (s (r x₁)))) x₁
                                                                                                                                                                            (trans (is-retract (r (s (r x₁)))) (is-retract (r x₁)))))
                                                                                                                                                                          (quot (s (r (s (r y)))) y
                                                                                                                                                                             (trans (is-retract (r (s (r y)))) (is-retract (r y))))) x 
  
  fromTo≡sr : (x : A) -> from-A/~ (to-A/~ x) ≡ s (r x)
  fromTo≡sr x = refl

module SigmaConstruction where
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
  
