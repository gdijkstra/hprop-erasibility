{-# OPTIONS --without-K #-}

module Quicksort where

open import Naturals
open import Identity

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A → List A

append : {A : Set} → List A → List A → List A
append [] ys       = ys
append (x :: xs) ys = x :: (append xs ys)

data Bool : Set where
  True : Bool
  False : Bool

¬_ : Bool → Bool
¬ True = False
¬ False = True



gt : ℕ -> ℕ -> Bool
gt Z     Z     = False
gt Z     (S n) = False
gt (S n) Z     = True
gt (S n) (S m) = gt n m

-- x <= y
le : ℕ -> ℕ -> Bool
le a b = ¬ (gt a b)

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x :: xs) with f x
filter f (x :: xs) | True = x :: filter f xs
filter f (x :: xs) | False = filter f xs

data qsAcc : List ℕ → Set where
  qsAccNil : qsAcc []
  qsAccCons : (x : ℕ) → (xs : List ℕ) → (h₁ : qsAcc (filter (gt x) xs))
                                      → (h₂ : qsAcc (filter (le x) xs))
                                      → qsAcc (x :: xs)

quicksort : (xs : List ℕ) → qsAcc xs → List ℕ
quicksort .[] qsAccNil = []
quicksort .(x :: xs) (qsAccCons x xs h₁ h₂) = append (quicksort (filter (gt x) xs) h₁)
                                                (x :: quicksort (filter (le x) xs) h₂)

qsAccRec : 
  (P : (xs : List ℕ) → qsAcc xs → Set)
  (m1 : P [] qsAccNil)
  (m2 : (x : ℕ) (xs : List ℕ) (h₁ : qsAcc (filter (gt x) xs)) (h₂ : qsAcc (filter (le x) xs))
        → P (filter (gt x) xs) h₁
        → P (filter (le x) xs) h₂
        → P (x :: xs) (qsAccCons x xs h₁ h₂))
  (xs : List ℕ)
  (p : qsAcc xs)
  → P xs p
qsAccRec P m1 m2 .[]        qsAccNil               = m1
qsAccRec P m1 m2 .(x :: xs) (qsAccCons x xs p₁ p₂) = m2 x xs p₁ p₂ (qsAccRec P m1 m2 (filter (gt x) xs) p₁) 
                                                                   (qsAccRec P m1 m2 (filter (λ z → ¬ gt x z) xs) p₂)

quicksortRec : (xs : List ℕ) → qsAcc xs → List ℕ
quicksortRec = qsAccRec (λ _ _ → List ℕ) [] (λ x _ _ _ rec₁ rec₂ → append rec₁ (x :: rec₂))

-- TODO: write proof of (xs : List ℕ) → qsAcc xs


