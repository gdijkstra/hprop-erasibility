{-# OPTIONS --without-K #-}

module Retraction where

open import Identity
open import Sigma
open import Levels

Iso : (A B : Set) (f : A -> B) (g : B -> A) -> Set
Iso A B f g = ((x : A) -> g (f x) ≡ x) × ((x : B) -> f (g x) ≡ x)

is-retraction : {A B : Set} (r : A -> B) -> Set
is-retraction {A} {B} r = Σ (B → A) (λ s → (x : B) → r (s x) ≡ x)

-- B is isomorphic to A/~ where x ~ y iff s (r x) ≡ s (r y)
-- A/~ is isomorphic to Σ A (λ x -> s (r x) ≡ x
retraction-iso : {A B : Set} (r : A -> B) -> (s : is-retraction r) 
  -> Iso (Σ A (λ x -> (Σ.fst s) (r x) ≡ x)) B (λ a → r (Σ.fst a)) (λ b → (Σ.fst s b) , ap (Σ.fst s) (Σ.snd s b))
retraction-iso r (s , s-is-retraction) = {!!} -- This is tedious but rather trivial rewriting.
