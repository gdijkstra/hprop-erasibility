module Sigma where

open import Levels

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    snd : B fst

