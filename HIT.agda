{-# OPTIONS --without-K #-}

module HIT where

open import Naturals
open import Levels
open import Identity

module Interval where
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
    
    -- TODO: dependent recursor
    -- TODO: levels

    I-rec : {A : Set} 
           -> (a b : A)
           -> (p : a ≡ b)
           -> I -> A
    I-rec a b _ #zero = a
    I-rec a b _ #one  = b
    
    postulate 
      seg : zer ≡ one
      βseg : {A : Set} 
           -> (a b : A)
           -> (p : a ≡ b)
           -> ap (I-rec a b p) seg ≡ p


open Interval -- tee hee!

≡⇒Interval : {A : Set} {x y : A} -> x ≡ y -> I -> A
≡⇒Interval {A} {x} {y} p i = I-rec {A} x y p i

Interval⇒≡ : {A : Set} -> (p : I -> A) -> (p zer) ≡ (p one)
Interval⇒≡ p = ap p seg

flip : {A B C : Set} -> (A -> B -> C) -> (B -> A -> C)
flip f b a = f a b

ext : (A B : Set) (f g : A -> B) (α : (x : A) -> f x ≡ g x) -> f ≡ g
ext A B f g α = Interval⇒≡ (flip (λ a → ≡⇒Interval (α a)))

left : {A : Set} {x y : A} -> (p : x ≡ y) -> (Interval⇒≡ (≡⇒Interval p)) ≡ p
left {A} {x} {.x} refl = βseg x x refl

--right : {A : Set} (p : I -> A) -> (≡⇒Interval (Interval⇒≡ p)) ≡ p
--right {A} p = ? -- needs function extensionality?

_+_ : ℕ -> ℕ -> ℕ
Z   + y = y
S x + y = S (x + y)


foo : ℕ → ℕ
foo x = x + 0

bar : ℕ → ℕ
bar x = 0 + x

0+x≡x+0 : (x : ℕ) → foo x ≡ bar x
0+x≡x+0 Z     = refl
0+x≡x+0 (S x) = ap S (0+x≡x+0 x)

foo≡bar : foo ≡ bar
foo≡bar = ext ℕ ℕ foo bar 0+x≡x+0


ext' : (A B : Set) (f g : A -> B) (α : (x : A) -> f x ≡ g x) -> f ≡ g
ext' A B f g α = ap h seg where
    h : (I -> A -> B)
    h = (λ i x → I-rec (f x) (g x) (α x) i)

foo≡bar' : foo ≡ bar
foo≡bar' = ext' ℕ ℕ foo bar 0+x≡x+0

--ap (λ b a → I-rec (a + 0) a (0+x≡x+0 a) b) seg
--ap (λ i x → I-rec (x + 0) x (0+x≡x+0 x) i) seg
