module QuotientBinaryRec (A : Set) (R : A -> A -> Set) (R-refl : (x : A) -> R x x) (B : Set) where

open import Identity
open import QuotientUntruncated A R R-refl

postulate
  fun-ext : {X Y : Set} (f g : X -> Y) -> ((x : X) -> f x ≡ g x) -> f ≡ g

Quotient-rec-2' : (f : A -> A -> B)
       -> (resp : (a b c d : A) -> R a c -> R b d -> f a b ≡ f c d)
       -> Quotient -> A -> B
Quotient-rec-2' f resp x = 
    (Quotient-rec 
       f 
       (λ x₁ y₁ r → fun-ext (f x₁) (f y₁) (λ x₂ → resp x₁ x₂ y₁ x₂ r (R-refl x₂)))
       x
    )

postulate
  uip-B : (x y : B) (p q : x ≡ y) -> Id (Id B x y) p q

lemma : (f : A -> A -> B)
       -> (resp : (a b c d : A) -> R a c -> R b d -> f a b ≡ f c d)
       -> (q : Quotient)
       -> (x y : A)
       -> (r : R x y)
       -> Quotient-rec-2' f resp q x ≡ Quotient-rec-2' f resp q y
lemma f resp q x y r = Quotient-ind {B = (λ q₁ → Quotient-rec-2' f resp q₁ x ≡ Quotient-rec-2' f resp q₁ y)} 
  (λ x₁ → resp x₁ x x₁ y (R-refl x₁) r) (λ x₁ y₁ p → uip-B (f y₁ x) (f y₁ y) (transport {B = (λ q₁ → Quotient-rec-2' f resp q₁ x ≡ Quotient-rec-2' f resp q₁ y)}(quot x₁ y₁ p) (resp x₁ x x₁ y (R-refl x₁) r))(resp y₁ x y₁ y (R-refl y₁) r)) q 

Quotient-rec-2 :(f : A -> A -> B)
       -> (resp : (a b c d : A) -> R a c -> R b d -> f a b ≡ f c d)
       -> Quotient -> Quotient -> B
Quotient-rec-2 f resp x y = 
  Quotient-rec 
    (Quotient-rec-2' f resp x)
    (lemma f resp x)
    y
