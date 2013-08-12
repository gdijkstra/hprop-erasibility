{-# OPTIONS --without-K #-}

module Irrelevance where

open import Naturals
open import Levels
open import Identity

record Squash (A : Set) : Set where
  constructor squash
  field
    .proof : A

squashProp : {A : Set} (x y : Squash A) → x ≡ y
squashProp x y = refl

elim-Squash : {A : Set} (P : Squash A → Set)
            (ih : .(a : A) → P (squash a)) →
            (a⁻ : Squash A) → P a⁻
elim-Squash P ih (squash a) = ih a

record Σ-irr {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    .snd : B fst

Σ-irr-irrelevant : {a b : Level} {A : Set a} {B : A → Set b}
  (x : A) (y₁ y₂ : B x) → Id (Σ-irr A B) (x , y₁) (x , y₂)
Σ-irr-irrelevant _ _ _ = refl 
