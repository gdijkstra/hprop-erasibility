{-# OPTIONS --without-K #-}

module Univalence where

open import Levels
open import Sigma
open import Identity

-- Definition of what it means for a function f : A → B to be an
-- isomorphism.
isIsomorphism : {a b : Level} {A : Set a} {B : Set b} → (f : A → B) → Set (a ⊔ b)
isIsomorphism {A = A} {B = B} f = Σ (B → A) (\ g → ((x : B) → (f (g x)) ≡ x) 
                                                   × ((x : A) → (g (f x)) ≡ x))

_≃_ : {a b : Level} → (A : Set a) → (B : Set b) → Set (a ⊔ b)
A ≃ B = Σ (A → B) (\f → isIsomorphism f)

-- Propositional equality implies isomorphism.
≡⇒≃ : {a : Level} → (A B : Set a) → A ≡ B → A ≃ B
≡⇒≃ .B B refl = (λ x → x) , ((λ x → x) , ((λ x → refl) , (λ x → refl))) 

-- Unfortunately, isIsomorphism f need not be in hProp. This
-- complicates further matters (the details of which are not too
-- relevant for this thesis), so we need an alternative notion:
-- equivalence.
isEquivalence : {a b : Level} {A : Set a} {B : Set b} → (f : A → B) → Set (a ⊔ b)
isEquivalence {A = A} {B = B} f = Σ (B → A) (\g → (x : B) → (f (g x)) ≡ x)
                               ×  Σ (B → A) (\h → (x : A) → (h (f x)) ≡ x)

_≅_ : {a b : Level} → (A : Set a) → (B : Set b) → Set (a ⊔ b)
A ≅ B = Σ (A → B) (\f → isEquivalence f)

toEquiv : {a b : Level} {A : Set a} {B : Set b} → A ≃ B → A ≅ B
toEquiv (fst , (fst' , (fst'' , snd))) = fst , ((fst' , fst'') , (fst' , snd))

-- Propositional equality implies equivalence.
≡⇒≅ : {a : Level} → (A B : Set a) → A ≡ B → A ≅ B
≡⇒≅ .B B refl = (λ x → x) ,
                  (((λ x → x) , (λ x → refl)) , ((λ x → x) , (λ x → refl)))

-- The univalence axiom in all its glory.
postulate
  Univalence : {a : Level} (A B : Set a) → isEquivalence (≡⇒≅ A B)

-- Corollary that is the most useful for us, assuming A and B are
-- hSets.
univalence : {a : Level} → (A B : Set a) → A ≃ B → A ≡ B
univalence A B pf with Univalence A B
univalence A B pf | ((≅⇒≡ , _) , _) = ≅⇒≡ (toEquiv pf)

-- Computation rules.
postulate
  uacomp : {a : Level}
           {A B : Set a}
           {f : A → B}
           {eq : isIsomorphism f}
           {x : A}
        → (transport {B = λ X → X} (univalence A B (f , eq)) x) ≡ f x
