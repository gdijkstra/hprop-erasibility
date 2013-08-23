{-# OPTIONS --without-K #-}

module Irrelevance where

open import Naturals
open import Levels
open import Identity
open import Proposition

-- Irrelevant functions are constant.
irrelevantConstantFunction : {a b : Level} {A : Set a} {B : Set b} → (f : .A → B) 
                           → isConstant f
irrelevantConstantFunction {a} {b} {A} {B} f x _ = refl

irrelevantConstantFunctionDep : {a b : Level} {A : Set a} {B : .A → Set b}
                         → (f : .(x : A) → B x) 
                         → .(x y : A) 
                         → f x ≡ f y
irrelevantConstantFunctionDep _ _ _ = refl


-- We cannot do the following, because Id A _ _ is not an irrelevant
-- context.
-- irrelevantAllPaths : {a : Level} {A : Set a} .(x y : A) → x ≡ y

-- However, if we package the irrelevantness in a record, then we can
-- prove proof irrelevance.
record Squash (A : Set) : Set where
  constructor squash
  field
    .proof : A

squashProofIrrelevance : {A : Set} (x y : Squash A) → x ≡ y
squashProofIrrelevance x y = refl

record Σ-irr {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    .snd : B fst

Σ-irr-irrelevant : {a b : Level} {A : Set a} {B : A → Set b}
  (x : A) (y₁ y₂ : B x) → Id (Σ-irr A B) (x , y₁) (x , y₂)
Σ-irr-irrelevant _ _ _ = refl 

