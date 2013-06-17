{-# OPTIONS --without-K #-}

module Compare where

open import Naturals
open import Identity
open import Proposition

-- Compare is in hProp for every x, y in ℕ
data Compare : ℕ → ℕ → Set where
  lt : (x y : ℕ) → Compare x           (x + (S y))
  eq : (x : ℕ)   → Compare x           x
  gt : (x y : ℕ) → Compare (y + (S x)) y

Compare-elim :
  (P : (x y : ℕ) → Compare x y → Set)
  (mlt : (x y : ℕ) → P x (x + (S y)) (lt x y))
  (meq : (x : ℕ) → P x x (eq x))
  (mgt : (x y : ℕ) → P (y + (S x)) y (gt x y))
  (x y : ℕ)
  (Compare-x-y : Compare x y)
  → P x y Compare-x-y
Compare-elim P mlt meq mgt x .(x + S y) (lt .x y) = mlt x y
Compare-elim P mlt meq mgt .y y (eq .y) = meq y
Compare-elim P mlt meq mgt .(y + S x) y (gt x .y) = mgt x y

cmp : (n m : ℕ) → Compare n m
cmp Z Z = eq Z
cmp Z (S y) = lt Z y
cmp (S x) Z = gt x Z
cmp (S x) (S y) with cmp x y
cmp (S x) (S .(x + S y)) | lt .x y = lt (S x) y
cmp (S .y) (S y) | eq .y = eq (S y)
cmp (S .(y + S x)) (S y) | gt x .y = gt x (S y)

compare-x-y-in-hProp : (x y : ℕ) → proofIrrelevance (Compare x y)
compare-x-y-in-hProp x .(x + S y) p (lt .x y) = Compare-elim (λ xprime₁ yprime₁ pprime₂ → {!x ≡ xprime → y ≡ yprime → pprime ≡ lt x y!}) {!!} {!!} {!!} {!!} {!!} {!!} refl refl
compare-x-y-in-hProp .y y         p (eq .y)   = {!!}
compare-x-y-in-hProp .(y + S x) y p (gt x .y) = {!!}
