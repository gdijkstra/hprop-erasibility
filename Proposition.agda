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

--foo : (A : Set) → proofIrrelevance A → (x y : A) → (p : x ≡ y) → transport {zero} {zero} {A} {\y -> Id A x y} {x} {y} p refl ≡ p
--foo = {!!}
--foo A pi x y p = apd {zero} {zero} {A} {\ y -> Id A x y} {x} {y} (λ x₁ → pi x x₁) ?

--proofIrrelevance⇒hProp : {a : Level} → (A : Set a) → proofIrrelevance A → hProp A
--proofIrrelevance⇒hProp A p = λ x y → p x y , (λ q → {!!})

proofIrrelevance⇒inhabitedContractible : {a : Level} → (A : Set a) → proofIrrelevance A → (A → isContractible A)
proofIrrelevance⇒inhabitedContractible A proofIrr a = a , proofIrr a

inhabitedContractible⇒proofIrrelevance : {a : Level} → (A : Set a) → (A → isContractible A) → proofIrrelevance A
inhabitedContractible⇒proofIrrelevance A contr x y with contr x
inhabitedContractible⇒proofIrrelevance A contr x y | center , center≡ = trans (sym (center≡ x)) (center≡ y)

-- One thing that follows from the above is that every function out of
-- an h-proposition is constant, up to propositional equality.
hPropConstantFunction : {a b : Level} {A : Set a} {B : Set b} → hProp A → (f : A → B) → (x y : A) → (f x ≡ f y)
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
                  → (.(x : A) → (makeIrrelevant pf B x))
makeIrrelevantDep (center , _) f x = f center

-- TODO: Prove the following...
-- We again want to prove that the irrelevant version yields the same
-- results for the same inputs. The proof currently does not
-- work. Maybe because the type isn't completely correct yet.

-- makeIrrelevantDepWorks : {a b : Level} {A : Set a} {B : A → Set b} 
--                        → (pf : isContractible A) 
--                        → (f : (x : A) → B x) 
--                        → (x : A) 
--                        → f x ≡ transport {B = λ x₁ → x₁} (makeIrrelevantWorks pf B x) (makeIrrelevantDep pf f x)
-- makeIrrelevantDepWorks {A = A} {B = B} (center , center≡) f x = sym (apd {A = A} {B = B} {a₁ = center} {a₂ = x} f (center≡ x))
