{-# OPTIONS --without-K #-}

module UnitVersusInterval where

open import Naturals
open import Levels
open import Identity
open import Interval
open import Truncation
open import Sigma
open import Proposition

data ⊤ : Set where
  tt : ⊤

⊤-ind : {B : ⊤ → Set}
           → (b : B tt)
           → (t : ⊤) → B t
⊤-ind b tt = b

⊤-rec : {B : Set}
           → (b : B)
           → ⊤ → B
⊤-rec {B} = ⊤-ind {B = λ _ → B}

⊤⇒Interval : ⊤ → I
⊤⇒Interval = ⊤-rec zer

Interval⇒⊤ : I → ⊤
Interval⇒⊤ = I-rec tt tt refl

-- This should be an isomorphism.
left : (t : ⊤) → (Interval⇒⊤ (⊤⇒Interval t)) ≡ t
left tt = refl

-- TODO: Finish this proof.
-- right : (i : I) → (⊤⇒Interval (Interval⇒⊤ i)) ≡ i
-- right i = I-ind {B = λ i₁ → ⊤-ind {B = \ _ → I} zer (I-rec {B = ⊤} tt tt refl i₁) ≡ i₁} refl seg {!!} i


-- ⊤ is contractible, hence an h-proposition
⊤-is-contractible : isContractible ⊤
⊤-is-contractible = tt , (λ x → ⊤-ind {B = λ t → Id ⊤ tt t} refl x)

-- I is proof irrelevant and inhabited, hence contractible, hence an h-proposition
--I-is-proof-irrelevant : proofIrrelevance I
--I-is-proof-irrelevant = λ x y → I-ind {B = λ i → x ≡ i} {!!} {!!} {!!} y



-- I-is-contr : is-contr I
-- I-is-contr =
--   (zer , I-rec (λ (t : I) → t ≡ zer) refl (sym seg)
--                 (trans (trans-id≡cst seg refl) (refl-right-unit (sym seg)))

trans-id≡cst : {a : Level} {A : Set a} {a b c : A} (p : b ≡ c) (q : b ≡ a)
    → transport {B = λ x → x ≡ a} p q ≡ (trans (sym p) q)
trans-id≡cst refl refl = refl

refl-right-unit : {a : Level} {A : Set a} {x y : A} (q : x ≡ y) → trans q refl ≡ q
refl-right-unit refl = refl
