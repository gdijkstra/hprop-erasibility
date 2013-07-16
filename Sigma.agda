module Sigma where

open import Levels

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    snd : B fst

-- fst : {a b : Level} {A : Set a} {B : A → Set b} → Σ A B → A
-- fst (x , _) = x

-- snd : {a b : Level} {A : Set a} {B : A → Set b} → (p : Σ A B) → B (fst p)
-- snd (_ , y) = y

-- Non-dependent version

record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    snd : B
