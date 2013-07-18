module QuotientUntruncated (A : Set) (R : A -> A -> Set) (R-refl : (x : A) -> R x x) where

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

-- This should be expressed using Quotient-ind or Quotient-rec...
Quotient-rec-2 : {B : Set}
       -> (f : A -> A -> B)
       -> (resp : (a b c d : A) -> R a c -> R b d -> f a b ≡ f c d)
       -> Quotient -> Quotient -> B
Quotient-rec-2 f _ (#box x) (#box y) = f x y

postulate
  fun-ext : {X Y : Set} (f g : X -> Y) -> ((x : X) -> f x ≡ g x) -> f ≡ g

Quotient-rec-2'' : {B : Set}
       -> (f : A -> A -> B)
       -> (resp : (a b c d : A) -> R a c -> R b d -> f a b ≡ f c d)
       -> Quotient -> A -> B
Quotient-rec-2'' f resp x = 
    (Quotient-rec 
       f 
       (λ x₁ y₁ r → fun-ext (f x₁) (f y₁) (λ x₂ → resp x₁ x₂ y₁ x₂ r (R-refl x₂)))
       x
    )

lemma : {B : Set}
       -> (f : A -> A -> B)
       -> (resp : (a b c d : A) -> R a c -> R b d -> f a b ≡ f c d)
       -> (q : Quotient)
       -> (x y : A)
       -> (r : R x y)
       -> Quotient-rec-2'' f resp q x ≡ Quotient-rec-2'' f resp q y
lemma f resp q x y r = Quotient-ind {B = (λ q₁ → Quotient-rec-2'' f resp q₁ x ≡ Quotient-rec-2'' f resp q₁ y)} 
  (λ x₁ → resp x₁ x x₁ y (R-refl x₁) r) {!!} q -- If B is a set, then we can use this to prove the goal.

Quotient-rec-2' : {B : Set}
       -> (f : A -> A -> B)
       -> (resp : (a b c d : A) -> R a c -> R b d -> f a b ≡ f c d)
       -> Quotient -> Quotient -> B
Quotient-rec-2' f resp x y = 
  Quotient-rec 
    (Quotient-rec-2'' f resp x)
    (λ x₁ y₁ r → lemma f resp x x₁ y₁ r)
    y
