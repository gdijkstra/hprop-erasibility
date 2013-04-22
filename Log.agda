{-# OPTIONS --without-K #-}

module Log where

open import Naturals
open import Levels
open import Identity
open import Truncation
open import Proposition
open import Empty

div2 : ℕ -> ℕ
div2 Z = Z
div2 (S Z) = Z
div2 (S (S n)) = S (div2 n)

data logAcc : ℕ → Set where
 logAcc0 : logAcc (S Z)
 logAcc1 : (k : ℕ) → logAcc (S (div2 k)) → logAcc (S (S k))

logAcc0IsEmpty : logAcc 0 → ⊥ {zero}
logAcc0IsEmpty ()

logAccIsProp : (x : ℕ) → proofIrrelevance (logAcc x)
logAccIsProp Z () ()
logAccIsProp (S .0) logAcc0 logAcc0 = refl
logAccIsProp (S .(S k)) (logAcc1 k x) (logAcc1 .k y) = ap (logAcc1 k) (logAccIsProp (S (div2 k)) x y)


logAccInd : 
  (P : ℕ → Set)  -- motive
  (m1 : P 1)  -- method one
  (m2 : (k : ℕ) → logAcc (S (div2 k)) → P (S (div2 k)) → P (S (S k))) -- method two
  (i : ℕ) -- index
  (p : logAcc i) -- target
   → P i
logAccInd P m1 m2 .1 logAcc0 = m1
logAccInd P m1 m2 .(S (S k)) (logAcc1 k p) = m2 k p (logAccInd P m1 m2 (S (div2 k)) p)

logAccRec : 
  (P : (n : ℕ) → logAcc n → Set)  -- motive
  (m1 : P 1 logAcc0)  -- method one
  (m2 : (k : ℕ) (l : logAcc (S (div2 k))) → P (S (div2 k)) l → P (S (S k)) (logAcc1 k l)) -- method two
  (i : ℕ) -- index
  (x : logAcc i) -- target
   → P i x
logAccRec P m1 m2 .1 logAcc0 = m1
logAccRec P m1 m2 .(S (S k)) (logAcc1 k x) = m2 k x (logAccRec P m1 m2 (S (div2 k)) x)

-- TODO: Write the proof that it is in prop using logAccRec.

log : (x : ℕ) → logAcc x → ℕ
log .1 logAcc0 = 0
log .(S (S k)) (logAcc1 k pf) = S (log (S (div2 k)) pf)

logInd : (x : ℕ) → logAcc x → ℕ
logInd = logAccInd (λ _ → ℕ) 0 (λ _ _ recVal → S recVal)

logRec : (x : ℕ) → logAcc x → ℕ
logRec = logAccRec (λ _ _ → ℕ) 0 (λ _ _ recVal → S recVal)

-- TODO: Make this into a structural recursive function.
-- logAccProof : (x : ℕ) → logAcc (S x)
-- logAccProof Z = logAcc0
-- logAccProof (S x) = logAcc1 x (logAccProof (div2 x))

--proofEqual : (x : ℕ) (acc : logAcc x) → log x acc ≡ logInd x acc
--proofEqual .1 logAcc0 = refl
--proofEqual .(S (S k)) (logAcc1 k acc) = proofEqual {!!} {!!}

-- Theorem logAcc_non_0 : forall (x0 : ℕ) , logAcc x0 -> (x0 = Z) -> Logic.False .
-- intros x0 H; case H; intros; discriminate.
-- Defined.

-- Theorem logAcc_inv_1_0 : forall (x0 : ℕ) (p : ℕ) , logAcc x0 -> (x0 = S (S p)) -> logAcc (S (div2 p)) .
-- intros x0 p H; case H; try (intros; discriminate). intros p' Hcall0 . intros Heq0; injection Heq0. intros Heq0_ctx_0. try (rewrite <- Heq0_ctx_0). assumption.
-- Defined.

-- Unset Implicit Arguments.

-- Fixpoint log (x0 : ℕ) (x1 : logAcc x0) : ℕ :=
--            match x0 as _y0 return (x0 = _y0) -> ℕ with
--              | S Z => fun _h0 => Z
--              | S (S p) => fun _h0 => S (log (S (div2 p)) (logAcc_inv_1_0 x1 _h0))
--              | Z => fun _h0 => False_rec ℕ (logAcc_non_0 x1 _h0)
--            end (refl_equal x0).

-- End Log.


-- --log : ℕ -> ℕ
-- --log (S Z) = Z
-- --log (S (S p)) = S (log (S (div2 p)))
