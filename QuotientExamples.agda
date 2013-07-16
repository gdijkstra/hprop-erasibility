module QuotientExamples where

open import Identity
open import QuotientUntruncated
open import Naturals
open import UnitVersusInterval
open import Sigma

[_] : {A : Set} {R : A -> A -> Set} → A → Quotient A R
[_] {A} {R} a = box A R a

-- Integers: (m,n) represents m - n
ℤ : Set
ℤ = Quotient (ℕ × ℕ) R
  where
    R : (ℕ × ℕ) → (ℕ × ℕ) → Set
    R (a , b) (c , d) = (a + d) ≡ (c + b)

ℕ-to-ℤ : ℕ → ℤ
ℕ-to-ℤ n = [ n , 0 ]

_*'_ : ℤ → ℤ → ℤ
x *' y = {!!}

-- Rationals: (m,n) represents m/(n+1)
ℚ : Set
ℚ = Quotient (ℤ × ℕ) R
  where
    R : (ℤ × ℕ) → (ℤ × ℕ) → Set
    R (a , b) (c , d) = (a *' (ℕ-to-ℤ (S d))) ≡ (c *' (ℕ-to-ℤ (S b)))

-- Coherence problem

