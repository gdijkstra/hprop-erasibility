{-# OPTIONS --without-K #-}

module Circle where

open import Naturals
open import Levels
open import Identity

private
  data #Circle : Set where
    #base : #Circle

Circle : Set
Circle = #Circle

base : Circle
base = #base

postulate 
  loop : base ≡ base

Circle-ind : {B : Circle → Set}
          → (b : B base)
          → (p : (transport {B = B} loop b) ≡ b)
          → (x : Circle) → B x
Circle-ind b _ #base = b

Circle-rec : {B : Set} 
       -> (b : B)
       -> (p : b ≡ b)
       -> Circle -> B
Circle-rec a _ #base = a

-- -- Computation rules
postulate
  βloop-rec : {B : Set} 
           -> (b : B)
           -> (p : b ≡ b)
           -> ap (Circle-rec b p) loop ≡ p

  βloop-ind : {B : Circle → Set} 
           -> (b : B base)
           -> (p : (transport {B = B} loop b) ≡ b)
           -> apd {B = B} (Circle-ind b p) loop ≡ p
