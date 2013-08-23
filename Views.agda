{-# OPTIONS --without-K #-}

module Views where

open import Identity
open import Sigma
open import Levels

-- We define the abstract type Sequence as a nested Σ-type:
Sequence : Set₁
Sequence = 
         Σ Set               (λ A →
         Σ Set               (λ seq →
         Σ (seq)             (λ empty →
         Σ (A → seq)         (λ single → 
         Σ (seq → seq → seq) (λ append →
           ((A → A) → seq → seq) -- map
         )))))

module ListImplementsSequence where
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
  
  list-append : {A : Set} → List A → List A → List A
  list-append nil r = r
  list-append (cons x l) r = cons x (list-append l r)
  
  list-map : {A B : Set} → (A → B) → List A → List B
  list-map f nil = nil
  list-map f (cons x xs) = cons (f x) (list-map f xs)
  
  -- This can be proved, but we will postulate it for now.
  postulate
    list-map-append-commutes : {A B : Set} {xs ys : List A} {f : A → B}
      → list-append (list-map f xs) (list-map f ys) ≡ list-map f (list-append xs ys)

  ListSeq : (A : Set) → Sequence
  ListSeq A = A , (List A , (nil , ((λ x → cons x nil) , (list-append , list-map))))

open ListImplementsSequence
  
module JoinListImplementsSequence where
  data JoinList (A : Set) : Set where
    nil : JoinList A
    unit : A → JoinList A
    join : JoinList A → JoinList A → JoinList A
  
  join-list-empty : {A : Set} → JoinList A
  join-list-empty = nil
  
  join-list-single : {A : Set} → A → JoinList A
  join-list-single = unit
  
  join-list-append : {A : Set} → JoinList A → JoinList A → JoinList A
  join-list-append l r = join l r
  
  join-list-map : {A B : Set} → (A → B) → JoinList A → JoinList B
  join-list-map f nil = nil
  join-list-map f (unit x) = unit (f x)
  join-list-map f (join l r) = join (join-list-map f l) (join-list-map f r)

  JoinListSeq : (A : Set) → Sequence
  JoinListSeq A = A , (JoinList A , (nil , (unit , (join-list-append , join-list-map))))

open JoinListImplementsSequence

-- We have a retraction JoinList A → List A.
module JoinListRetraction where
  to : {A : Set} → JoinList A → List A
  to nil = nil
  to (unit x) = cons x nil
  to (join l r) = list-append (to l) (to r)
  
  from : {A : Set} → List A → JoinList A
  from nil = nil
  from (cons x xs) = join (unit x) (from xs)
  
  is-retraction : {A : Set} → (xs : List A) → (to (from xs)) ≡ xs
  is-retraction nil = refl
  is-retraction (cons x xs) = ap (cons x) (is-retraction xs)

open JoinListRetraction

-- We can show that the JoinList implementation of Sequence respects
-- the List implementation via the retraction.
module JoinListRetractionRespectsListImplementation where
  empty-resp : {A : Set} → to (join-list-empty {A}) ≡ nil
  empty-resp = refl
  
  single-resp : {A : Set} → (a : A) → to (join-list-single a) ≡ cons a nil
  single-resp _ = refl
  
  append-resp : {A : Set} → (xs ys : JoinList A) → to (join-list-append xs ys) ≡ list-append (to xs) (to ys)
  append-resp _ _ = refl
  
  map-resp : {A B : Set} → (f : A → B) → (xs : JoinList A) → to (join-list-map f xs) ≡ list-map f (to xs)
  map-resp f nil = refl
  map-resp f (unit x) = refl
  map-resp f (join l r) with map-resp f l
  ... | pₗ with map-resp f r
  ... | pᵣ = trans (ap (λ xs → list-append xs (to (join-list-map f r))) pₗ) 
             (trans (ap (λ ys → list-append (list-map f (to l)) ys) pᵣ) 
             (list-map-append-commutes {xs = to l} {ys = to r} {f = f}))
  
open JoinListRetractionRespectsListImplementation

-- However, where do these properties come from? Do we have to add
-- these to the abstract type definition? As noted in the thesis, we
-- can use univalence to automatically derive these, by using as a
-- specification:
SequenceSpec : (Set → Sequence) → Set (suc zero)
SequenceSpec OtherSeq = (A : Set) → (ListSeq A ≡ OtherSeq A)

-- We first have to show that the first field of ListSeq and OtherSeq
-- are propositionally equal, which can be done by showing they are
-- isomorphic and then use univalence. We then have to transport the
-- other fields along this proof, which, by the univalence computation
-- rules, yields the properties shown above.

-- However, JoinList A and List A are not isomorphic. Luckily we can
-- turn the retraction into an isomorphism, by quotienting JoinList
-- out by this retraction.
module JoinListQuotient (A : Set) where
  open import RetractIso (JoinList A) (List A) to from is-retraction

  JoinListQuotient : Set
  JoinListQuotient = A/~

  -- Lifting the operations to the quotient is simply done by applying
  -- the functions from JoinList A to the quotient and back in the
  -- right places.
  join-list-empty~ : JoinListQuotient
  join-list-empty~ = to-A/~ join-list-empty

  join-list-single~ : A → JoinListQuotient
  join-list-single~ x = to-A/~ (join-list-single x)

  join-list-append~ : JoinListQuotient → JoinListQuotient → JoinListQuotient
  join-list-append~ l r = to-A/~ (join-list-append (from-A/~ l) (from-A/~ r))

  join-list-map~ : (f : A → A) → JoinListQuotient → JoinListQuotient
  join-list-map~ f xs = to-A/~ (join-list-map f (from-A/~ xs))

  -- The properties can be proven in terms of the proofs of JoinList
  -- satisfying the properties, which are a bit more general than
  -- needed, as we can see in append-resp~ and map-resp~.
  empty-resp~ : r~ (join-list-empty~) ≡ nil
  empty-resp~ = empty-resp

  single-resp~ : (a : A) → r~ (join-list-single~ a) ≡ cons a nil
  single-resp~ a = single-resp a

  -- For append-resp~ and map-resp~, we need to do a bit more work: we
  -- need to use the fact that to/from is a retraction-section
  -- pair. Making use of this, we can simply reuse the proof of
  -- append-resp/map-resp.
  append-resp~ : (xs ys : JoinListQuotient) → r~ (join-list-append~ xs ys) ≡ list-append (r~ xs) (r~ ys)
  append-resp~ xs ys = trans (is-retraction (list-append (to (from-A/~ xs)) (to (from-A/~ ys))))
                             (append-resp (from-A/~ xs) (from-A/~ ys))

  map-resp~ : (f : A → A) → (xs : JoinListQuotient) → r~ (join-list-map~ f xs) ≡ list-map f (r~ xs)
  map-resp~ f xs = trans (is-retraction (to (join-list-map f (from-A/~ xs)))) 
                         (map-resp f (from-A/~ xs))


  -- In this case we used the quotient type construction. It can also
  -- be done using the Σ-type construction, mutatatis mutandis.
