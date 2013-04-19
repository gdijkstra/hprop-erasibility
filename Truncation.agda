{-# OPTIONS --without-K #-}

module Truncation where

open import Sigma
open import Levels
open import Identity

data ℕ₋₂ : Set where
  ⟨-2⟩ : ℕ₋₂
  S : (n : ℕ₋₂) → ℕ₋₂

⟨-1⟩ : ℕ₋₂
⟨-1⟩ = S ⟨-2⟩

⟨0⟩ : ℕ₋₂
⟨0⟩ = S ⟨-1⟩

⟨1⟩ : ℕ₋₂
⟨1⟩ = S ⟨0⟩

⟨2⟩ : ℕ₋₂
⟨2⟩ = S ⟨1⟩

isContractible : {a : Level} → Set a → Set a
isContractible A = Σ A (λ center → (x : A) → (Id A center x))

isTruncated : {a : Level} → ℕ₋₂ → Set a → Set a
isTruncated ⟨-2⟩  A = isContractible A
isTruncated (S n) A = (x : A) → (y : A) → isTruncated n (Id A x y)

hProp : {a : Level} → Set a → Set a
hProp A = isTruncated ⟨-1⟩ A

hSet : {a : Level} → Set a → Set a
hSet A = isTruncated ⟨0⟩ A

-- Filtration property
-- truncatedFiltration : {a : Level} → (A : Set a) → (n : ℕ₋₂) → isTruncated n A → isTruncated (S n) A
-- truncatedFiltration A ⟨-2⟩ (center , xToCenter) = {!!} -- TODO: Finish this.
-- truncatedFiltration A (S n) proof = λ x y → truncatedFiltration (Id A x y) n (proof x y)

