{-# OPTIONS --without-K #-}

module Identity where

open import Levels

data Id {a} (A : Set a) (x : A) : A → Set a where
  refl : Id A x x

module IdentityTypesEquivalenceRelation {a : Level} {A : Set a} where
  _≡_ : (x y : A) → Set a
  x ≡ y = Id _ x y
  
  -- reflexivitiy is witnessed by refl.

  trans : {x y z : A} → Id A x y → Id A y z → Id A x z
  trans refl q = q
  
  sym : {x y : A} → Id A x y → Id A y x
  sym refl = refl 
  
open IdentityTypesEquivalenceRelation public

-- Identity types give us a groupoid.
module IdentityTypesGroupoid {a : Level} {A : Set a} where
  infix 8 _∘_
  
  _∘_ : {x y z : A} → Id A x y → Id A y z → Id A x z
  p ∘ q = trans p q
  
  _⁻¹ : {x y : A} → Id A x y → Id A y x
  p ⁻¹ = sym p 
  
  assoc : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
        → (p ∘ (q ∘ r)) ≡ ((p ∘ q) ∘ r)
  assoc refl refl refl = refl
  
  refl-left-identity : {x y : A} (p : x ≡ y) → (refl ∘ p) ≡ p
  refl-left-identity refl = refl
  
  refl-right-identity : {x y : A} (p : x ≡ y) → (p ∘ refl) ≡ p
  refl-right-identity refl = refl
  
  left-inverse-refl : {x y : A} (p : x ≡ y) → (p ⁻¹ ∘ p) ≡ refl
  left-inverse-refl refl = refl
  
  right-inverse-refl : {x y : A} (p : x ≡ y) → (p ∘ p ⁻¹) ≡ refl
  right-inverse-refl refl = refl
  
open IdentityTypesGroupoid public

-- Injectivity or "whisker" properties of "trans".
∘-injective-left : {a : Level} {A : Set a} {x y z : A} (p : y ≡ z) {q r : x ≡ y}
    → (q ∘ p) ≡ (r ∘ p) → q ≡ r
∘-injective-left refl {q} {r} h = trans (sym (refl-right-identity q)) (trans h (refl-right-identity r))

∘-injective-right : {a : Level} {A : Set a} {x y z : A} (p : x ≡ y) {q r : y ≡ z}
    → (p ∘ q) ≡ (p ∘ r) → q ≡ r
∘-injective-right refl h = h


-- We can transport values across fibers along paths in the base
-- space.
transport : {a b : Level} {A : Set a} {B : A → Set b} {x y : A} → x ≡ y → B x → B y
transport refl bx = bx

-- Functorial action on paths.
ap : {a b : Level} {A : Set a} {B : Set b} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

ap-2 : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} {x x' : A} {y y' : B} (f : A → B → C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap-2 f refl refl = refl

cong : {a b : Level} {A : Set a} {B : Set b} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong = ap

-- Dependent action on paths.
apd : {a b : Level} {A : Set a} {B : A → Set b} {a₁ a₂ : A} → (f : (x : A) → B x) → (β : Id A a₁ a₂)
  → Id (B a₂) (transport β (f a₁)) (f a₂)
apd f refl = refl

cong-dep : {a b : Level} {A : Set a} {B : A → Set b} {a₁ a₂ : A} → (f : (x : A) → B x) → (β : Id A a₁ a₂)
  → Id (B a₂) (transport β (f a₁)) (f a₂)
cong-dep = apd

