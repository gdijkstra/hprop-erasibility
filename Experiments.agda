{-# OPTIONS --without-K #-}

module Experiments where

open import Naturals
open import Levels
open import Identity

Iso : {a : Level} → Set a → Set a → Set a
Iso A B = Σ (A → B) (\f → 
          Σ (B → A) (\g → 
          Σ ((x : A) → Id A (g (f x)) x) (\_ → 
             (x : B) → Id B (f (g x)) x)))

TrivialIso : (A : Set) → Iso A A
TrivialIso A = (λ x → x) , ((λ x → x) , ((λ x → refl) , (λ x → refl)))

isContractible : {a : Level} → Set a → Set a
isContractible A = Σ A (λ center → (x : A) → (Id A center x))

-- Truncation index (isomorphic to the type of integers ≥ -2)
-- stolen from: https://github.com/HoTT/HoTT-Agda/blob/master/Types.agda


-- unit is contractible
data ⊤ : Set where
  tt : ⊤

⊤-contractible : isContractible ⊤
⊤-contractible = tt , match-⊤
  where
    match-⊤ : (x : ⊤) → Id ⊤ tt x
    match-⊤ tt = refl

ContractibleUniv : isContractible (Σ Set isContractible)
ContractibleUniv = (⊤ , ⊤-contractible) , pf
  where
    pf : (x : Σ Set isContractible) → Id (Σ Set isContractible) (⊤ , ⊤-contractible) x
    pf (A , A-contractible) = {!!}


