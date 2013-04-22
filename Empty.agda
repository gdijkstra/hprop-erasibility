{-# OPTIONS --without-K #-}

module Empty where

open import Levels

data ⊥ {a} : Set a where

efsq : {a b : Level} {A : Set a} → ⊥ {b} → A
efsq ()
