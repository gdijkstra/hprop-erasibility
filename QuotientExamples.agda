{-# OPTIONS --without-K #-}

module QuotientExamples where

open import Identity

open import Naturals
open import UnitVersusInterval
open import Sigma
open import Proposition

-- Quotient of an hSet by an hProp-valued relation yielding a 1-type?
TrivialRelation : {A : Set} → A → A → Set
TrivialRelation _ _ = ⊤

TrivialRelation-refl : {A : Set} → (x : A) -> TrivialRelation x x
TrivialRelation-refl _ = tt

open import QuotientUntruncated ⊤ TrivialRelation TrivialRelation-refl

UnitQuotient : Set
UnitQuotient = Quotient

f : (x : ⊤) → box x ≡ box tt
f tt = refl

goal : (x y : ⊤) (p : TrivialRelation x y) → transport {B = λ x₁ → x₁ ≡ box tt} (quot x y p) (f x) ≡ f y
goal tt tt tt = -- The goal here is basically to show that transport (quot tt tt tt) refl ≡ refl.

Quotient-is-contractible : (x : Quotient) -> x ≡ box tt
Quotient-is-contractible x = Quotient-ind {B = λ x₁ → x₁ ≡ box tt} f {!!} x
