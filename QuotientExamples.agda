module QuotientExamples where

open import Identity
open import QuotientUntruncated
open import Naturals
open import UnitVersusInterval
open import Sigma
open import Proposition

[_] : {A : Set} {R : A -> A -> Set} → A → Quotient A R
[_] {A} {R} a = box A R a

-- Integers: (m,n) represents m - n
Rℤ : (ℕ × ℕ) → (ℕ × ℕ) → Set
Rℤ (a , b) (c , d) = (a + d) ≡ (c + b)

ℤ : Set
ℤ = Quotient (ℕ × ℕ) Rℤ

ℕ-to-ℤ : ℕ → ℤ
ℕ-to-ℤ n = [ n , 0 ] -- n - 0

_+ℤ_ : ℤ → ℤ → ℤ
x +ℤ y = Quotient-rec-2 (ℕ × ℕ) Rℤ f {!!} {!!} {!!}
  where 
    f : (ℕ × ℕ) → (ℕ × ℕ) → ℤ
    f (a , b) (c , d) = [ (a + c) , (b + d) ]

_*ℤ_ : ℤ → ℤ → ℤ
x *ℤ y = Quotient-rec-2 {!!} {!!} {!!} {!!} {!!} {!!}

-- Rationals: (m,n) represents m/(n+1)
ℚ : Set
ℚ = Quotient (ℤ × ℕ) R
  where
    R : (ℤ × ℕ) → (ℤ × ℕ) → Set
    R (a , b) (c , d) = (a *ℤ (ℕ-to-ℤ (S d))) ≡ (c *ℤ (ℕ-to-ℤ (S b)))

ℤ-to-ℚ : ℤ → ℚ
ℤ-to-ℚ z = [ z , 0 ] -- z / 1

-- Quotient of an hSet by an hProp-valued relation yielding a 1-type.

TrivialRelation : {A : Set} → A → A → Set
TrivialRelation _ _ = ⊤

UnitQuotient : Set
UnitQuotient = Quotient ⊤ TrivialRelation

lemma : (x y : ⊤) → box ⊤ TrivialRelation x ≡ box ⊤ TrivialRelation y
lemma tt tt = ap (box ⊤ TrivialRelation) refl

-- test : Id
--       (Id (Quotient ⊤ (λ _ _ → ⊤))
--        (box ⊤ TrivialRelation tt)
--        (box ⊤ TrivialRelation tt))
--       (transport (quot ⊤ (λ _ _ → ⊤) tt tt tt) (lemma tt tt)) (lemma tt tt)
-- test = refl

goal0 : (y : UnitQuotient) (x₁ : ⊤) → (box ⊤ TrivialRelation x₁) ≡ y
goal0 y x₁ = Quotient-ind ⊤ TrivialRelation {B = λ x → box ⊤ TrivialRelation x₁ ≡ x} (λ x → lemma x₁ x) {!!} y

UnitQuotient-is-prop : proofIrrelevance UnitQuotient
UnitQuotient-is-prop x y = Quotient-ind ⊤ TrivialRelation {B = λ x₁ → x₁ ≡ y} (goal0 y) {!!} x

-- This probably works out, seeing as the test thing type checks.

-- Coherence problems
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

