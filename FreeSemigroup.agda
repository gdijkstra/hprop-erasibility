{-# OPTIONS --without-K #-}

module FreeSemigroup where

open import Identity

private
  data #FreeSemigroup (A : Set) : Set where
    #elem : A → #FreeSemigroup A
    #· : #FreeSemigroup A → #FreeSemigroup A → #FreeSemigroup A
       
FreeSemigroup : Set → Set
FreeSemigroup A = #FreeSemigroup A

elem : {A : Set} → A → FreeSemigroup A
elem = #elem

_·_ : {A : Set} → FreeSemigroup A → FreeSemigroup A → FreeSemigroup A
x · y = #· x y

postulate
  fg-assoc : {A : Set} {a b c : FreeSemigroup A} → ((a · b) · c) ≡ (a · (b · c))

FreeSemigroup-rec : {A B : Set}
                → (el : A → B)
                → (binop : B → B → B)
                → (p : (a b c : B) → (binop a (binop b c)) ≡ (binop (binop a b) c))
                → FreeSemigroup A
                → B
FreeSemigroup-rec el binop p (#elem x) = el x
FreeSemigroup-rec el binop p (#· a b) = binop (FreeSemigroup-rec el binop p a) (FreeSemigroup-rec el binop p b)
