{-# OPTIONS --without-K #-}

module Proposition where

open import Naturals
open import Levels
open import Identity
open import Sigma
open import Truncation

proofIrrelevance : {a : Level} → Set a → Set a
proofIrrelevance A = (x y : A) → x ≡ y

hProp⇒proofIrrelevance : {a : Level} → (A : Set a) → hProp A → proofIrrelevance A
hProp⇒proofIrrelevance A p x y with p x y
hProp⇒proofIrrelevance A p x y | x≡y , _ = x≡y

foo : (A : Set) → proofIrrelevance A → (x y : A) → (p : x ≡ y) → transport {zero} {zero} {A} {\y -> Id A x y} {x} {y} p refl ≡ p
foo = {!!}
--foo A pi x y p = apd {zero} {zero} {A} {\ y -> Id A x y} {x} {y} (λ x₁ → pi x x₁) ?

proofIrrelevance⇒hProp : {a : Level} → (A : Set a) → proofIrrelevance A → hProp A
proofIrrelevance⇒hProp A p = λ x y → p x y , (λ q → {!!})
