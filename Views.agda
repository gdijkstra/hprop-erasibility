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

join-list-empty : {A : Set} -> JoinList A
join-list-empty = nil

join-list-single : {A : Set} -> A -> JoinList A
join-list-single = unit

join-list-append : {A : Set} -> JoinList A -> JoinList A -> JoinList A
join-list-append l r = join l r

join-list-map : {A B : Set} -> (A -> B) -> JoinList A -> JoinList B
join-list-map f nil = nil
join-list-map f (unit x) = unit (f x)
join-list-map f (join l r) = join (join-list-map f l) (join-list-map f r)

to : {A : Set} -> JoinList A -> List A
to nil = nil
to (unit x) = cons x nil
to (join l r) = list-append (to l) (to r)

from : {A : Set} -> List A -> JoinList A
from nil = nil
from (cons x xs) = join (unit x) (from xs)

is-retraction : {A : Set} -> (xs : List A) -> (to (from xs)) ≡ xs
is-retraction nil = refl
is-retraction (cons x xs) = ap (cons x) (is-retraction xs)

-- Join lists satisfy the properties
empty-resp : {A : Set} -> to (join-list-empty {A}) ≡ nil
empty-resp = refl

single-resp : {A : Set} -> (a : A) -> to (join-list-single a) ≡ cons a nil
single-resp _ = refl

append-resp : {A : Set} -> (xs ys : JoinList A) -> to (join-list-append xs ys) ≡ list-append (to xs) (to ys)
append-resp _ _ = refl

map-resp : {A B : Set} -> (f : A -> B) -> (xs : JoinList A) -> to (join-list-map f xs) ≡ list-map f (to xs)
map-resp f nil = refl
map-resp f (unit x) = refl
map-resp f (join l r) = {!!} -- use recursive call to reduce goal to
                             -- showing that "map f (to l) ++ map f
                             -- (to r) ≡ map f (to l ++ to r)"

-- Quotient method

rel : {X : Set} -> JoinList X -> JoinList X -> Set
rel x y = to x ≡ to y

rel-refl : {X : Set} -> (x : JoinList X) -> rel x x
rel-refl x = refl

open import QuotientUntruncated -- Quotient is now the type we're interested in.

JoinListQuotient : (A : Set) -> Set
JoinListQuotient A = Quotient (JoinList A) rel rel-refl

toQuotient : {A : Set} -> JoinList A -> JoinListQuotient A
toQuotient {A} x = box (JoinList A) rel rel-refl x

from' : {A : Set} -> List A -> JoinListQuotient A
from' x = toQuotient (from x)

to' : {A : Set} -> JoinListQuotient A -> List A
to' {A} q = Quotient-rec (JoinList A) rel rel-refl to (λ x y z → z) q

join-list-empty' : {A : Set} -> JoinListQuotient A
join-list-empty' = toQuotient join-list-empty

join-list-single' : {A : Set} -> A -> JoinListQuotient A
join-list-single' x = toQuotient (join-list-single x)

join-list-append' : {A : Set} -> JoinListQuotient A -> JoinListQuotient A -> JoinListQuotient A
join-list-append' {A} l r = Quotient-rec-2 (JoinList A) rel rel-refl (λ l₁ r₁ → toQuotient (join-list-append l₁ r₁)) (λ a b c d x x₁ → quot (JoinList A) rel rel-refl (join a b) (join c d) (ap-2 list-append x x₁)) l r

join-list-map' : {A B : Set} -> (f : A -> B) -> JoinListQuotient A -> JoinListQuotient B
join-list-map' {A} {B} f xs = Quotient-rec (JoinList A) rel rel-refl (λ x → toQuotient (join-list-map f x)) (λ x y x₁ → quot (JoinList B) rel rel-refl (join-list-map f x) (join-list-map f y) (trans (map-resp f x) (trans (ap (list-map f) x₁) (sym (map-resp f y))))) xs

-- Join lists satisfy the properties
empty-resp' : {A : Set} -> to' (join-list-empty' {A}) ≡ nil
empty-resp' = refl

single-resp' : {A : Set} -> (a : A) -> to' (join-list-single' a) ≡ cons a nil
single-resp' _ = refl

append-resp' : {A : Set} -> (xs ys : JoinListQuotient A) -> to' (join-list-append' xs ys) ≡ list-append (to' xs) (to' ys)
append-resp' xs ys = {!!}

map-resp' : {A B : Set} -> (f : A -> B) -> (xs : JoinListQuotient A) -> to' (join-list-map' f xs) ≡ list-map f (to' xs)
map-resp' f x = {!!}

-- Sigma type method
JoinListSigma : Set -> Set
JoinListSigma A = Σ (JoinList A) (λ xs → from (to xs) ≡ xs)

toSigma : {A : Set} -> JoinList A -> JoinListSigma A
toSigma x = from (to x) , ap from (is-retraction (to x))

fromSigma : {A : Set} -> JoinListSigma A -> JoinList A
fromSigma = Σ.fst

to'' : {A : Set} -> JoinListSigma A -> List A
to'' xs = to (fromSigma xs)

from'' : {A : Set} -> List A -> JoinListSigma A
from'' xs = toSigma (from xs)

join-list-empty'' : {A : Set} -> JoinListSigma A
join-list-empty'' = toSigma join-list-empty

join-list-single'' : {A : Set} -> A -> JoinListSigma A
join-list-single'' a = toSigma (join-list-single a)

join-list-append'' : {A : Set} -> JoinListSigma A -> JoinListSigma A -> JoinListSigma A
join-list-append'' l r = toSigma (join-list-append (fromSigma l) (fromSigma r))

join-list-map'' : {A B : Set} -> (f : A -> B) -> JoinListSigma A -> JoinListSigma B
join-list-map'' f xs = toSigma (join-list-map f (fromSigma xs))

-- Join lists satisfy the properties
empty-resp'' : {A : Set} -> to'' (join-list-empty'' {A}) ≡ nil
empty-resp'' = refl

single-resp'' : {A : Set} -> (a : A) -> to'' (join-list-single'' a) ≡ cons a nil
single-resp'' _ = refl

append-resp'' : {A : Set} -> (xs ys : JoinListSigma A) -> to'' (join-list-append'' xs ys) ≡ list-append (to'' xs) (to'' ys)
append-resp'' xs ys = is-retraction (list-append (to (Σ.fst xs)) (to (Σ.fst ys)))

map-resp'' : {A B : Set} -> (f : A -> B) -> (xs : JoinListSigma A) -> to'' (join-list-map'' f xs) ≡ list-map f (to'' xs)
map-resp'' f x = trans (is-retraction (to (join-list-map f (Σ.fst x)))) (map-resp f (fromSigma x))

-- Spec stuff
Iso : {a : Level} -> Set a → Set a → Set a
Iso A B = Σ (A → B) (\f → 
          Σ (B → A) (\g → 
          Σ ((x : A) → Id A (g (f x)) x) (\_ → 
             (x : B) → Id B (f (g x)) x)))

postulate
  ua : (A B : Set) -> Iso A B -> A ≡ B

Sequence : Set₁
Sequence = 
         Σ Set (λ A ->
         Σ Set (λ seq ->
         Σ (seq)                               (λ empty ->
         Σ (A -> seq)                          (λ single -> 
         Σ (seq -> seq -> seq)                 (λ append ->
           ((A -> A) -> seq -> seq) -- map
         )))))

ListSeq : (A : Set) -> Sequence
ListSeq A = A , (List A , (nil , ((λ x → cons x nil) , (list-append , list-map))))

-- This does not satisfy the specifcation: "JoinList A" is not
-- isomorphic to "ListSeq A".
JoinListSeq : (A : Set) -> Sequence
JoinListSeq A = A , (JoinList A , (nil , (unit , (join-list-append , join-list-map))))

-- Unfolding this and applying some rule that ≡ for Σ-types can be
-- done via ≡ on first field and transport rules for the second will
-- lead us to the desired properties on the methods, if we also use
-- the rules for transport on equalities obtained from applying
-- univalence.
spec : (A : Set) -> Iso (List A) (JoinList A) -> ListSeq A ≡ JoinListSeq A
spec A iso = Σ-≡ refl 
  (Σ-≡ (ua (List A) (JoinList A) iso) 
  (Σ-≡ {!!}
  (Σ-≡ {!!} 
  (Σ-≡ {!!} 
  {!!}))))
