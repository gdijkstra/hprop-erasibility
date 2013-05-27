{-# OPTIONS --without-K #-}

module Irrelevance where

open import Naturals
open import Levels
open import Identity

record Irrelevant {a} {A : Set a} : Set a where
  constructor irr
  field
    .val : A

∣_∣ₜ : {a : Level} (A : Set a) → Set a
∣_∣ₜ {a} A = Irrelevant {a} {A}

∣_∣ : {a : Level} {A : Set a} → A → Irrelevant
∣ x ∣ = irr x

test : ∣ ℕ ∣ₜ → ℕ
test (irr name) = 0

-- qsAccRec : 
--   (P : (xs : List ℕ) → ∣ qsAcc xs ∣ → Set)
--   (m1 : P [] ∣ qsAccNil ∣)
--   (m2 : (x : ℕ) (xs : List ℕ) (h₁ : qsAcc (filter (gt x) xs)) (h₂ : qsAcc (filter (le x) xs))
--         → P (filter (gt x) xs) h₁
--         → P (filter (le x) xs) h₂
--         → P (x :: xs) (qsAccCons x xs h₁ h₂))
--   (xs : List ℕ)
--   (p : qsAcc xs)
--   → P xs p
-- qsAccRec P m1 m2 .[]        qsAccNil               = m1
-- qsAccRec P m1 m2 .(x :: xs) (qsAccCons x xs p₁ p₂) = m2 x xs p₁ p₂ (qsAccRec P m1 m2 (filter (gt x) xs) p₁) 

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
