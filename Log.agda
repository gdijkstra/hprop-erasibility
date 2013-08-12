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

logAcc0IsEmpty : logAcc 0 → ⊥
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

log : (x : ℕ) → logAcc x → ℕ
log .1 logAcc0 = 0
log .(S (S k)) (logAcc1 k pf) = S (log (S (div2 k)) pf)

logInd : (x : ℕ) → logAcc x → ℕ
logInd = logAccInd (λ _ → ℕ) 0 (λ _ _ recVal → S recVal)

-- TODO: Write proof of (x : ℕ) → logAcc (S x)
