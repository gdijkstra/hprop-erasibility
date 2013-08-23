{-# OPTIONS --without-K #-}

module PredicatesOnNaturals where

open import Naturals
open import Identity
open import Sigma
open import Proposition

-- "Less than or equal" relation on naturals
data _≤_ : ℕ → ℕ → Set where
  leZ : (y : ℕ)   → Z ≤ y
  leS : (x y : ℕ) → x ≤ y → S x ≤ S y

≤-elim : 
  (P : (x y : ℕ) → x ≤ y → Set)
  (mZ : (y : ℕ) → P 0 y (leZ y))
  (mS : (x y : ℕ) → (x≤y : x ≤ y) → P x y x≤y → P (S x) (S y) (leS x y x≤y))
  (x y : ℕ)
  (x≤y : (x ≤ y))
  → P x y x≤y
≤-elim P mZ mS .0 y (leZ .y) = mZ y
≤-elim P mZ mS .(S x) .(S y) (leS x y x≤y) = mS x y x≤y (≤-elim P mZ mS x y x≤y)

-- "Less than" relation on naturals
data _<_ : ℕ → ℕ → Set where
  leZ : (y : ℕ)   → Z < S y
  leS : (x y : ℕ) → x < y → S x < S y

<-inv : {x y : ℕ} → S x < S y → x < y
<-inv {x} {y} (leS .x .y pf) = pf

<-elim : 
  (P : (x y : ℕ) → x < y → Set)
  (mZ : (y : ℕ) → P 0 (S y) (leZ y))
  (mS : (x y : ℕ) → (x<y : x < y) → P x y x<y → P (S x) (S y) (leS x y x<y))
  (x y : ℕ)
  (x<y : (x < y))
  → P x y x<y
<-elim P mZ mS .0 .(S y) (leZ y) = mZ y
<-elim P mZ mS .(S x) .(S y) (leS x y x<y) = mS x y x<y (<-elim P mZ mS x y x<y)

-- Parity predicate on naturals
data isEven : ℕ → Set where
  isEvenZ  : isEven 0
  isEvenSS : (n : ℕ) → isEven n → isEven (S (S n))

-- _≤_ is in hProp for every x, y in ℕ, making use of dependent
-- pattern matching.
x≤y-in-hprop : (x y : ℕ) → proofIrrelevance (x ≤ y)
x≤y-in-hprop .0 y (leZ .y) (leZ .y) = refl
x≤y-in-hprop .(S x) .(S y) (leS x y x≤y₁) (leS .x .y x≤y₂) = ap (leS x y) (x≤y-in-hprop x y x≤y₁ x≤y₂)

-- Similarly, for every x in ℕ, isEven x is in hProp.
isEven-x-in-hProp : (x : ℕ) → proofIrrelevance (isEven x)
isEven-x-in-hProp .0 isEvenZ isEvenZ = refl
isEven-x-in-hProp .(S (S n)) (isEvenSS .n p₁) (isEvenSS n p₂) = ap (isEvenSS n) (isEven-x-in-hProp n p₁ p₂)
