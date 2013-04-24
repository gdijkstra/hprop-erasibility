{-# OPTIONS --without-K #-}

module IntervalExtensionality where

open import Naturals
open import Levels
open import Identity
open import Interval

≡⇒Interval : {A : Set} {x y : A} -> x ≡ y -> I -> A
≡⇒Interval {A} {x} {y} p i = I-rec {A} x y p i

Interval⇒≡ : {A : Set} -> (p : I -> A) -> (p zer) ≡ (p one)
Interval⇒≡ p = ap p seg

flip : {A B C : Set} -> (A -> B -> C) -> (B -> A -> C)
flip f b a = f a b

ext : (A B : Set) (f g : A -> B) (α : (x : A) -> f x ≡ g x) -> f ≡ g
ext A B f g α = Interval⇒≡ (flip (λ a → ≡⇒Interval (α a)))

-- Are Interval and _≡_ isomorphic?
left : {A : Set} {x y : A} -> (p : x ≡ y) -> (Interval⇒≡ (≡⇒Interval p)) ≡ p
left {A} {x} {.x} refl = βseg x x refl

--right : {A : Set} (p : I -> A) -> (≡⇒Interval (Interval⇒≡ p)) ≡ p
--right {A} p = ? -- needs function extensionality?

-- Example of using function extensionality
_+_ : ℕ -> ℕ -> ℕ
Z   + y = y
S x + y = S (x + y)

+0 : ℕ → ℕ
+0 x = x + 0

0+ : ℕ → ℕ
0+ x = 0 + x

0+x≡x+0 : (x : ℕ) → 0+ x ≡ +0 x
0+x≡x+0 Z     = refl
0+x≡x+0 (S x) = ap S (0+x≡x+0 x)

-- The following does not reduce to a canonical form, but instead
-- reduces to:
-- ap (λ b a → I-rec a (a + 0) (0+x≡x+0 a) b) seg
-- to which we cannot apply βseg directly.
0+≡+0 : 0+ ≡ +0
0+≡+0 = ext ℕ ℕ 0+ +0 0+x≡x+0
