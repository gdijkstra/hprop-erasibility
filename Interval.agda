{-# OPTIONS --without-K #-}

module Interval where

open import Naturals
open import Identity

private
  data #I : Set where
    #zero : #I
    #one  : #I

I : Set
I = #I

zer : I
zer = #zero

one : I
one = #one

postulate 
  seg : zer ≡ one

I-ind : {B : I → Set}
          → (b₀ : B zer)
          → (b₁ : B one)
          → (p : (transport {B = B} seg b₀) ≡ b₁)
          → (i : I) → B i
I-ind b₀ b₁ _ #zero = b₀
I-ind b₀ b₁ _ #one  = b₁


I-rec : {B : Set} 
       → (b₀ b₁ : B)
       → (p : b₀ ≡ b₁)
       → I → B
I-rec a b _ #zero = a
I-rec a b _ #one  = b

-- Computation rules
postulate
  βseg : {A : Set} 
       → (b₀ b₁ : A)
       → (p : b₀ ≡ b₁)
       → ap (I-rec b₀ b₁ p) seg ≡ p
  βseg' : {B : I → Set} 
       → (b₀ : B zer)
       → (b₁ : B one)
       → (p : transport {B = B} seg b₀ ≡ b₁)
       → apd {B = B} (I-ind b₀ b₁ p) seg ≡ p
