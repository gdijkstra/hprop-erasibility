{-# OPTIONS --without-K #-}

module UnitVersusInterval where

open import Naturals
open import Levels
open import Identity
open import Interval

data ⊤ : Set where
  tt : ⊤

⊤⇒Interval : ⊤ → I
⊤⇒Interval tt = zer

Interval⇒⊤ : I → ⊤
Interval⇒⊤ = I-rec tt tt refl

-- This should be an isomorphism.
left : (t : ⊤) → (Interval⇒⊤ (⊤⇒Interval t)) ≡ t
left tt = refl

-- TODO: Finish this proof.
right : (i : I) → (⊤⇒Interval (Interval⇒⊤ i)) ≡ i
right i = {!!}
