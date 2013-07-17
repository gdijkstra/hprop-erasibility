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

record EqRel {A : Set} (_~_ : A → A → Set) : Set where
  field
    trans~ : {x y z : A} → x ~ y → y ~ z → x ~ z
    sym~   : {x y : A} → x ~ y → y ~ x
    refl~  : {x : A} → x ~ x

-- One can formulate conditions expressing whether the equivalence
-- relation is being mapped onto the right constructions in the
-- quotient, i.e. the mapping "quot" translates trans~ to trans≡, etc.
QuotientPreservesTrans : 
  (A : Set) (_~_ : A → A → Set) (pf : EqRel _~_)
  (x y z : A) (p : x ~ y) (q : y ~ z) →
  (quot A _~_ x z (EqRel.trans~ pf p q)) ≡ (trans (quot A _~_ x y p) (quot A _~_ y z q))
QuotientPreservesTrans A _~_ pf x y z p q = {!!}
