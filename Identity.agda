{-# OPTIONS --without-K #-}

module Identity where

open import Levels

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

ap : {a b : Level} {A : Set a} {B : Set b} {x y : A} (f : A -> B) -> x ≡ y -> f x ≡ f y
ap f refl = refl

cong : {a b : Level} {A : Set a} {B : Set b} {x y : A} (f : A -> B) -> x ≡ y -> f x ≡ f y
cong = ap

apd : {a b : Level} {A : Set a} {B : A → Set b} {a₁ a₂ : A} → (f : (x : A) → B x) → (β : Id A a₁ a₂)
  → Id (B a₂) (transport β (f a₁)) (f a₂)
apd f refl = refl

cong-dep : {a b : Level} {A : Set a} {B : A → Set b} {a₁ a₂ : A} → (f : (x : A) → B x) → (β : Id A a₁ a₂)
  → Id (B a₂) (transport β (f a₁)) (f a₂)
cong-dep = apd
