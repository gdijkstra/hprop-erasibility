{-# OPTIONS --without-K #-}

module Proposition where

open import Naturals
open import Levels
open import Identity
open import Sigma
open import Truncation

proofIrrelevance : {a : Level} → Set a → Set a
proofIrrelevance A = (x y : A) → x ≡ y

hProp⇒proofIrrelevance : {a : Level} → {A : Set a} → hProp A → proofIrrelevance A
hProp⇒proofIrrelevance p x y with p x y
hProp⇒proofIrrelevance p x y | x≡y , _ = x≡y

-- Proof from Brunerie's github.
proofIrrelevance⇒hProp : {a : Level} → {A : Set a} → proofIrrelevance A → hProp A
proofIrrelevance⇒hProp {A = A} p x y = p x y , (λ q → sym (canon-path q))
  where
    lemma : {x y : A} (q : x ≡ y) → p x y ≡ (q ∘ p y y)
    lemma refl = refl

    canon-path : {x y : A} (q : x ≡ y) →  q ≡ p x y
    canon-path {.y} {y} refl = anti-whisker-right (p y y) (lemma (p y y))

proofIrrelevance⇒inhabitedContractible : {a : Level} → (A : Set a) → proofIrrelevance A → (A → isContractible A)
proofIrrelevance⇒inhabitedContractible A proofIrr a = a , proofIrr a

inhabitedContractible⇒proofIrrelevance : {a : Level} → (A : Set a) → (A → isContractible A) → proofIrrelevance A
inhabitedContractible⇒proofIrrelevance A contr x y with contr x
inhabitedContractible⇒proofIrrelevance A contr x y | center , center≡ = trans (sym (center≡ x)) (center≡ y)

isConstant : {a b : Level} {A : Set a} {B : Set b} → (f : A → B) → Set (a ⊔ b)
isConstant {A = A} f = (x y : A) → (f x ≡ f y)

-- One thing that follows from the above is that every function out of
-- an h-proposition is constant, up to propositional equality.
hPropConstantFunction : {a b : Level} {A : Set a} {B : Set b} → hProp A → (f : A → B) → isConstant f
hPropConstantFunction p f x y = ap f (hProp⇒proofIrrelevance p x y)

-- This also holds for dependent functions f : (x : A) → B x, but we
-- have to transport things along the x ≡ y equality for the exact
-- statement to type check.
hPropConstantFunctionDep : {a b : Level} {A : Set a} {B : A → Set b}
                         → (p : hProp A) 
                         → (f : (x : A) → B x) 
                         → (x y : A) 
                         → (transport (hProp⇒proofIrrelevance p x y) (f x) ≡ f y)
hPropConstantFunctionDep {A = A} p f x y = apd f (hProp⇒proofIrrelevance p x y)

-- Given that A is contractible, we can transform a function f : A → B
-- into an irrelevant version.
makeIrrelevant : {a b : Level} {A : Set a} {B : Set b} → isContractible A → (f : A → B) → (.A → B)
makeIrrelevant (center , _) f x = f center

-- This transformed function is in fact equivalent to the original
-- function, in the following sense:
makeIrrelevantWorks : {a b : Level} {A : Set a} {B : Set b} → (pf : isContractible A) → (f : A → B) → (x : A) → (makeIrrelevant pf f x) ≡ f x
makeIrrelevantWorks (center , center≡) f x = ap f (center≡ x)

-- Generalising `makeIrrelevant` to dependent functions f : (x : A) →
-- B x is a bit more involved. We cannot simply make the x : A
-- irrelevant, because can still be relevant to the function B. So we
-- also have to make B irrelevant.
makeIrrelevantDep : {a b : Level} {A : Set a} {B : A -> Set b} 
                  → (pf : isContractible A) 
                  → (f : (x : A) → B x) 
                  → (.(x : A) → (makeIrrelevant {a} {suc b} {A} {Set b} pf B x))
makeIrrelevantDep (center , _) f x = f center

-- In order to do the same comparison as with `makeIrrelevantWorks`,
-- we have to transform the type first.
fromIrrelevantType : {a b : Level} {A : Set a} {B : A → Set b} 
                       → (pf : isContractible A) 
                       → (x : A) 
                       → makeIrrelevant {a} {suc b} {A} {Set b} pf B x
                       → B x
fromIrrelevantType (center , center≡) x bix = transport (center≡ x) bix

-- Now we can prove the dependent version of `makeIrrelevantWorks`.
makeIrrelevantDepWorks : {a b : Level} {A : Set a} {B : A → Set b} 
                       → (pf : isContractible A) 
                       → (f : (x : A) → B x) 
                       → (x : A) 
                       → fromIrrelevantType pf x (makeIrrelevantDep pf f x) ≡ f x
makeIrrelevantDepWorks (center , center≡) f x = apd f (center≡ x)

-- Indexed versions of the above.
makeIrrelevantIndexed : {a b c : Level} {I : Set a} {A : I → Set b} {B : Set c} → ((i : I) → isContractible (A i)) → (f : (i : I) → A i → B) → ((i : I) → .(A i) → B)
makeIrrelevantIndexed pf f i ai with pf i
makeIrrelevantIndexed pf f i ai | center , center≡ = f i center

makeIrrelevantWorksIndexed : {a b c : Level} {I : Set a} {A : I → Set b} {B : Set c} → (pf : (i : I) → isContractible (A i)) → (f : (i : I) → A i → B) → (i : I) → (x : A i) → (makeIrrelevantIndexed pf f i x) ≡ f i x
makeIrrelevantWorksIndexed pf f i ai with pf i
makeIrrelevantWorksIndexed pf f i ai | center , center≡ = ap (f i) (center≡ ai)

makeIrrelevantIndexedDep : {a b c : Level} {I : Set a} {A : I → Set b} {B : (i : I) → A i → Set c}
                  → (pf : (i : I) → isContractible (A i)) 
                  → (f : (i : I) → (x : A i) → B i x) 
                  → ((i : I) → .(x : A i) → (makeIrrelevantIndexed pf B i x))
makeIrrelevantIndexedDep pf f i x with pf i
makeIrrelevantIndexedDep pf f i x | center , center≡ = f i center

fromIrrelevantIndexedType : {a b c : Level} {I : Set a} {A : I → Set b} {B : (i : I) → A i → Set c}
                       → (pf : (i : I) → isContractible (A i))
                       → (i : I)
                       → (x : A i)
                       → makeIrrelevantIndexed pf B i x
                       → B i x
fromIrrelevantIndexedType pf i x bix with pf i
fromIrrelevantIndexedType pf i x bix | center , center≡ = transport (center≡ x) bix

makeIrrelevantIndexedDepWorks : {a b c : Level} {I : Set a} {A : I → Set b} {B : (i : I) → A i → Set c}
                       → (pf : (i : I) → isContractible (A i)) 
                       → (f : (i : I) → (x : A i) → B i x) 
                       → (i : I)
                       → (x : A i) 
                       → fromIrrelevantIndexedType {a} {b} {c} {I} {A} {B} pf i x (makeIrrelevantIndexedDep pf f i x) ≡ f i x
makeIrrelevantIndexedDepWorks pf f i x with pf i
makeIrrelevantIndexedDepWorks pf f i x | center , center≡ = apd (f i) (center≡ x)

-- TODO: Write all the work in terms of the indexed results.

-- Trying to make it work for hProp. In this case we still need to
-- prove that hProp implies .A → isContractible A.
makeIrrelevant' : {a b : Level} {A : Set a} {B : Set b} → (.A → isContractible A) → (f : A → B) → (.A → B)
makeIrrelevant' pf f x with pf x
makeIrrelevant' pf f x | center , _ = f center

makeIrrelevantWorks' : {a b : Level} {A : Set a} {B : Set b} → (pf : .A → isContractible A) → (f : A → B) → (x : A) → (makeIrrelevant' pf f x) ≡ f x
makeIrrelevantWorks' pf f x with pf x
makeIrrelevantWorks' pf f x | center , center≡ = ap f (center≡ x)

-- _≤_ is in hProp for every x, y in ℕ, making use of dependent
-- pattern matching.
x≤y-in-hprop : (x y : ℕ) → proofIrrelevance (x ≤ y)
x≤y-in-hprop .0 y (leZ .y) (leZ .y) = refl
x≤y-in-hprop .(S x) .(S y) (leS x y x≤y₁) (leS .x .y x≤y₂) = ap (leS x y) (x≤y-in-hprop x y x≤y₁ x≤y₂)
