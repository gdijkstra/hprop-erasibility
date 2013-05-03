{-# OPTIONS --without-K #-}

module Identity where

open import Levels

data Id {a} (A : Set a) (x : A) : A → Set a where
  refl : Id A x x


_≡_ : {a : Level} {A : Set a} (x y : A) → Set a
x ≡ y = Id _ x y

trans : {a : Level} {A : Set a} {x y z : A} -> Id A x y -> Id A y z -> Id A x z
trans refl refl = refl


sym : {a : Level} {A : Set a} {x y : A} -> Id A x y -> Id A y x
sym refl = refl 

-- Identity types give us a groupoid.
infix 8 _∘_

_∘_ : {a : Level} {A : Set a} {x y z : A} -> Id A x y -> Id A y z -> Id A x z
p ∘ q = trans p q

_⁻¹ : {a : Level} {A : Set a} {x y : A} → Id A x y → Id A y x
p ⁻¹ = sym p 

assoc : {a : Level} {A : Set a} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
      → (p ∘ (q ∘ r)) ≡ ((p ∘ q) ∘ r)
assoc refl refl refl = refl

refl-left-identity : {a : Level} {A : Set a} {x y : A} (p : x ≡ y) → (refl ∘ p) ≡ p
refl-left-identity refl = refl

refl-right-identity : {a : Level} {A : Set a} {x y : A} (p : x ≡ y) → (p ∘ refl) ≡ p
refl-right-identity refl = refl

left-inverse-refl : {a : Level} {A : Set a} {x y : A} (p : x ≡ y) → (p ⁻¹ ∘ p) ≡ refl
left-inverse-refl refl = refl

right-inverse-refl : {a : Level} {A : Set a} {x y : A} (p : x ≡ y) → (p ∘ p ⁻¹) ≡ refl
right-inverse-refl refl = refl

-- We can transport values across fibers along paths in the base
-- space.
transport : {a b : Level} {A : Set a} {B : A -> Set b} {x y : A} -> x ≡ y -> B x -> B y
transport refl bx = bx

-- Functorial action on points.
ap : {a b : Level} {A : Set a} {B : Set b} {x y : A} (f : A -> B) -> x ≡ y -> f x ≡ f y
ap f refl = refl

cong : {a b : Level} {A : Set a} {B : Set b} {x y : A} (f : A -> B) -> x ≡ y -> f x ≡ f y
cong = ap

-- Dependent action on points.
apd : {a b : Level} {A : Set a} {B : A → Set b} {a₁ a₂ : A} → (f : (x : A) → B x) → (β : Id A a₁ a₂)
  → Id (B a₂) (transport β (f a₁)) (f a₂)
apd f refl = refl

cong-dep : {a b : Level} {A : Set a} {B : A → Set b} {a₁ a₂ : A} → (f : (x : A) → B x) → (β : Id A a₁ a₂)
  → Id (B a₂) (transport β (f a₁)) (f a₂)
cong-dep = apd

