{-# OPTIONS --without-K #-}

module Views where

open import Identity
open import Sigma
open import Levels
  
data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

list-append : {A : Set} -> List A -> List A -> List A
list-append nil r = r
list-append (cons x l) r = cons x (list-append l r)

list-map : {A B : Set} -> (A -> B) -> List A -> List B
list-map f nil = nil
list-map f (cons x xs) = cons (f x) (list-map f xs)

data JoinList (A : Set) : Set where
  nil : JoinList A
  unit : A -> JoinList A
  join : JoinList A -> JoinList A -> JoinList A

join-list-append : {A : Set} -> JoinList A -> JoinList A -> JoinList A
join-list-append l r = join l r

join-list-map : {A B : Set} -> (A -> B) -> JoinList A -> JoinList B
join-list-map f nil = nil
join-list-map f (unit x) = unit (f x)
join-list-map f (join l r) = join (join-list-map f l) (join-list-map f r)

retract : {A : Set} -> JoinList A -> List A
retract nil = nil
retract (unit x) = cons x nil
retract (join l r) = list-append (retract l) (retract r)

section : {A : Set} -> List A -> JoinList A
section nil = nil
section (cons x xs) = join (unit x) (section xs)

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

JoinListSeq : (A : Set) -> SequenceSignature
JoinListSeq A = JoinList , (A , (nil , ((λ x → unit x) , (join-list-append , (λ B f xs → join-list-map f xs)))))

-- Unfolding this and applying some rule that ≡ for Σ-types can be
-- done via ≡ on first field and transport rules for the second will
-- lead us to the desired properties on the methods, if we also use
-- the rules for transport on equalities obtained from applying
-- univalence.
spec : {A : Set} (OtherSeq : Set -> SequenceSignature) -> ListSeq A ≡ OtherSeq A
spec {A} OtherSeq with OtherSeq A
spec OtherSeq | rep , (a , (empty , (single , (append , map)))) = 
  Σ-≡ {!!} 
  (Σ-≡ {!!} (Σ-≡ {!!} (Σ-≡ {!!} (Σ-≡ {!!} {!!}))))

