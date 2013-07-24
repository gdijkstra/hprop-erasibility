{-# OPTIONS --without-K #-}

module Views where

open import Identity
open import Sigma
  
data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

list-append : {A : Set} -> List A -> List A -> List A
list-append nil r = r
list-append (cons x l) r = cons x (list-append l r)

list-map : {A B : Set} -> (A -> B) -> List A -> List B
list-map f nil = nil
list-map f (cons x xs) = cons (f x) (list-map f xs)

data BinTree (A : Set) : Set where
  null : BinTree A
  leaf : A -> BinTree A
  node : BinTree A -> BinTree A -> BinTree A

bin-tree-append : {A : Set} -> BinTree A -> BinTree A -> BinTree A
bin-tree-append l r = node l r

bin-tree-map : {A B : Set} -> (A -> B) -> BinTree A -> BinTree B
bin-tree-map f null = null
bin-tree-map f (leaf x) = leaf (f x)
bin-tree-map f (node l r) = node (bin-tree-map f l) (bin-tree-map f r)

retract : {A : Set} -> BinTree A -> List A
retract null = nil
retract (leaf x) = cons x nil
retract (node l r) = list-append (retract l) (retract r)

section : {A : Set} -> List A -> BinTree A
section nil = null
section (cons x xs) = node (leaf x) (section xs)

is-retract : {A : Set} -> (xs : List A) -> (retract (section xs)) ≡ xs
is-retract nil = refl
is-retract (cons x xs) = ap (cons x) (is-retract xs)

-- Sequence signature

-- signature SEQ =
-- sig
--    type α seq

--    val empty  : α seq
--    val single : α → α seq 
--    val append : α seq → α seq → α seq 

--    (* Behavior: map f < x1, ..., xn >  =  < f x1, ..., f xn > *)
--    val map    : (α → β) → (α seq → β seq)

--    val reduce : (α → α → α) → α → α seq → α 
-- end 

SequenceSignature : Set₁
SequenceSignature = Σ (Set -> Set)                              (λ seq ->
                    Σ Set                                       (λ A ->
                    Σ (seq A)                                   (λ empty ->
                    Σ (A -> seq A)                              (λ single -> 
                    Σ (seq A -> seq A -> seq A)                 (λ append ->
                      ((B : Set) -> (A -> B) -> seq A -> seq B) -- map
                  )))))

ListSeq : (A : Set) -> SequenceSignature
ListSeq A = List , (A , (nil , ((λ x → cons x nil) , (list-append , (λ B f xs → list-map f xs)))))

BinTreeSeq : (A : Set) -> SequenceSignature
BinTreeSeq A = BinTree , (A , (null , ((λ x → leaf x) , (bin-tree-append , (λ B f xs → bin-tree-map f xs)))))

-- Unfolding this and applying some rule that ≡ for Σ-types can be
-- done via ≡ on first field and transport rules for the second will
-- lead us to the desired properties on the methods, if we also use
-- the rules for transport on equalities obtained from applying
-- univalence.
spec : {A : Set} -> ListSeq A ≡ BinTreeSeq A
spec {A} = {!!}

