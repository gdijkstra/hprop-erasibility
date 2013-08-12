{-# OPTIONS --without-K #-}

module Sigma where

open import Levels
open import Identity

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    snd : B fst

-- Non-dependent version
record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    snd : B

Σ-≡ : {a b : Level} {A : Set a} {B : A -> Set b}
  {s s' : Σ A B}
  (p : Σ.fst s ≡ Σ.fst s')
  (q : transport {B = B} p (Σ.snd s) ≡ Σ.snd s')
  → s ≡ s'
Σ-≡ {a} {b} {A} {B} {.fst , .snd₁} {fst , snd₁} refl refl = refl

Σ-transport : {a b c : Level} {Ctx : Set c} {A : Ctx -> Set a} {B : (ctx : Ctx) -> A ctx -> Set b}
  {ctx ctx' : Ctx}
  {x : A ctx} {y : B ctx x}
  (pf : ctx ≡ ctx') ->
  Σ.fst (transport {B = λ ctx -> Σ (A ctx) (B ctx)} pf (x , y)) ≡ transport {B = λ ctx₁ → A ctx₁} pf x
Σ-transport refl = refl
