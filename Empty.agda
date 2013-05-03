{-# OPTIONS --without-K #-}

module Empty where

open import Levels

data ⊥ : Set where

efsq : {a : Level} {A : Set a} → ⊥ → A
efsq ()

isEmpty : {a : Level} → Set a → Set a
isEmpty A = A → ⊥
