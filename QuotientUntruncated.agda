module QuotientUntruncated (A : Set) (R : A -> A -> Set) where

open import Identity

private
  data #Quotient : Set where
    #box : A -> #Quotient

Quotient : Set
Quotient = #Quotient

box : A -> Quotient
box a = #box a


postulate 
  quot : (x y : A) -> R x y -> box x ≡ box y

Quotient-ind : {B : Quotient -> Set} 
       -> (f : (x : A) -> B (box x))
       -> (resp : (x y : A) -> (p : R x y) -> transport {B = B} (quot x y p) (f x) ≡ f y)
       -> (x : Quotient) -> B x
Quotient-ind f _ (#box x) = f x

Quotient-rec : {B : Set} 
       -> (f : A -> B)
       -> (resp : (x y : A) -> R x y -> f x ≡ f y)
       -> Quotient -> B
Quotient-rec f _ (#box x) = f x

-- TODO: Computation rules
