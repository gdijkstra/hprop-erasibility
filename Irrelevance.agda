module Irrelevance where

open import Naturals
open import Levels

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

