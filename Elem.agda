{-# OPTIONS --without-K #-}

module Elem where

open import Naturals
open import PredicatesOnNaturals

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

length : {A : Set} → List A → ℕ
length [] = Z
length (_ :: xs) = S (length xs)

elem : {A : Set} (xs : List A) (i : ℕ) → i < length xs → A
elem []        i     ()
elem (x :: xs) Z     pf = x
elem (x :: xs) (S i) pf = elem xs i (<-inv pf)

elem-irr : {A : Set} (xs : List A) (i : ℕ) → .(i < length xs) → A
elem-irr []        i     ()
elem-irr (x :: xs) Z     pf = x
elem-irr (x :: xs) (S i) pf = elem-irr xs i (<-inv pf)
