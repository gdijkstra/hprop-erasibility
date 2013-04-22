{-# OPTIONS --without-K #-}

module Quicksort where

open import Naturals

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

-- TODO: write recursor and inductor
