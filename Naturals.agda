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

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
Z  + n = n
S m + n = S (m + n)

_*_ : ℕ → ℕ → ℕ
Z   * n = Z
S m * n = n + m * n



{-# BUILTIN NATPLUS _+_ #-}
