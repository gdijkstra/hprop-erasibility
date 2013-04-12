{-# OPTIONS --without-K #-}

module HIT where

-- Nats
data ℕ : Set where
  Z : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO    Z #-}
{-# BUILTIN SUC     S #-}

-- Level stuff
infixl 6 _⊔_

postulate
  Level : Set
  lzero  : Level
  lsuc   : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

data Id {a} (A : Set a) (x : A) : A → Set a where
  refl : Id A x x

_≡_ : {a : Level} {A : Set a} (x y : A) → Set a
x ≡ y = Id _ x y

trans : {a : Level} {A : Set a} {x y z : A} -> Id A x y -> Id A y z -> Id A x z
trans refl refl = refl

infix 8 _∘_

_∘_ : {a : Level} {A : Set a} {x y z : A} -> Id A x y -> Id A y z -> Id A x z
p ∘ q = trans p q

sym : {a : Level} {A : Set a} {x y : A} -> Id A x y -> Id A y x
sym refl = refl 

transport : {a b : Level} {A : Set a} {B : A -> Set b} {x y : A} -> x ≡ y -> B x -> B y
transport refl bx = bx

map : {a b : Level} {A : Set a} {B : Set b} {x y : A} (f : A -> B) -> x ≡ y -> f x ≡ f y
map f refl = refl

map-dep : {a b : Level} {A : Set a} {B : A -> Set b} {x y : A} (f : A -> B x) -> (p : x ≡ y) -> transport p (f x) ≡ f y
map-dep f refl = refl

module Interval where
    private
      data #I : Set where
        #zero : #I
        #one  : #I
    
    I : Set
    I = #I
    
    zero : I
    zero = #zero
    
    one : I
    one = #one
    
    -- TODO: dependent recursor
    -- TODO: levels

    I-rec : {A : Set} 
           -> (a b : A)
           -> (p : a ≡ b)
           -> I -> A
    I-rec a b _ #zero = a
    I-rec a b _ #one = b
    
    postulate 
      seg : zero ≡ one
      βseg : {A : Set} 
           -> (a b : A)
           -> (p : a ≡ b)
           -> map (I-rec a b p) seg ≡ p


open Interval -- tee hee!

≡⇒Interval : {A : Set} {x y : A} -> x ≡ y -> I -> A
≡⇒Interval {A} {x} {y} p i = I-rec {A} x y p i

Interval⇒≡ : {A : Set} -> (p : I -> A) -> (p zero) ≡ (p one)
Interval⇒≡ p = map p seg

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
0+x≡x+0 (S x) = map S (0+x≡x+0 x)

foo≡bar : foo ≡ bar
foo≡bar = ext ℕ ℕ foo bar 0+x≡x+0


ext' : (A B : Set) (f g : A -> B) (α : (x : A) -> f x ≡ g x) -> f ≡ g
ext' A B f g α = map h seg where
    h : (I -> A -> B)
    h = (λ i x → I-rec (f x) (g x) (α x) i)

foo≡bar' : foo ≡ bar
foo≡bar' = ext' ℕ ℕ foo bar 0+x≡x+0

--map (λ b a → I-rec (a + 0) a (0+x≡x+0 a) b) seg
--map (λ i x → I-rec (x + 0) x (0+x≡x+0 x) i) seg
