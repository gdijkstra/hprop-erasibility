{-# OPTIONS --without-K #-}

module Naturals where

-- Nats
data ℕ : Set where
  Z : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO    Z #-}
{-# BUILTIN SUC     S #-}

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

-- Parity predicate on naturals
data isEven : ℕ → Set where
  isEvenZ  : isEven 0
  isEvenSS : (n : ℕ) → isEven n → isEven (S (S n))

