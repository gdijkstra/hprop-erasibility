{-# OPTIONS --without-K #-}

module Monoid where

open import Identity
open import Univalence
open import Unit
open import Sigma

Monoid : Set → Set
Monoid A =
          Σ A                                                  (λ unit →
          Σ (A → A → A)                                      (λ _op_ →
          Σ ((x y z : A) → (x op (y op z)) ≡ ((x op y) op z)) (λ assoc →
          Σ ((x : A) → (unit op x) ≡ x)                       (λ unitleft → 
          Σ ((x : A) → (x op unit) ≡ x)                       (λ unitright →
            ⊤)))))

Monoid-transport : (A B : Set) → A ≃ B → Monoid A → Monoid B
Monoid-transport A B iso ma = transport {B = Monoid} (univalence A B iso) ma

Monoid-iso : (A B : Set) → A ≃ B → Monoid A ≃ Monoid B
Monoid-iso A B iso = ≡⇒≃ (Monoid A) (Monoid B) (ap {B = Set} Monoid (univalence A B iso))
