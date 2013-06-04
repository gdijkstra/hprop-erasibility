-- Van Laarhoven's counting monad.
-- https://gist.github.com/twanvl/5635740
-- and http://twanvl.nl/blog/agda/sorting
module CountingMonad where
  open import Naturals
  open import Identity

  private
    module Dummy where
      infix 1 _in-time_
      data _in-time_ {a} (A : Set a) (n : ℕ) : Set a where
        box : A → A in-time n
    
    open Dummy public using (_in-time_)
    open Dummy
    
    unbox : ∀ {a} {A : Set a} {n} → A in-time n → A
    unbox (box x) = x
    
  infixl 1 _>>=_
  _>>=_ : ∀ {a b} {A : Set a} {B : Set b} → {n m : ℕ} → A in-time n → (A → B in-time m) → B in-time (n + m)
  box x >>= f = box (unbox (f x))
  
  -- _=<<_ : ∀ {a b} {A : Set a} {B : Set b} → {n m : ℕ} → (A → B in-time m) → A in-time n → B in-time (n + m)
  -- _=<<_ = flip _>>=_
    
  infixr 2 _<$>_
  _<$>_ : ∀ {a b} {A : Set a} {B : Set b} → {n : ℕ} → (A → B) → A in-time n → B in-time n
  f <$> box x = box (f x)
  
  -- _<$$>_ : ∀ {a b} {A : Set a} {B : Set b} → {n : ℕ} → A in-time n → (A → B) → B in-time n
  -- _<$$>_ = flip _<$>_
  
  return : ∀ {a} {A : Set a} → {n : ℕ} → A → A in-time n
  return = box

    -- bound-≡ : ∀ {a} {A : Set a} {m n} → (m ≡ n) → A in-time m → A in-time n
  -- bound-≡ = PE.subst (_in-time_ _)
  
  -- bound-+ : ∀ {a} {A : Set a} {m n k} → (m + k ≡ n) → A in-time m → A in-time n
  -- bound-+ eq x = bound-≡ eq (x >>= return)
  
  -- bound-≤ : ∀ {a} {A : Set a} {m n} → (m ≤ n) → A in-time m → A in-time n
  -- bound-≤ m≤n = bound-+ (lem m≤n)
  --   where
  --   lem : ∀ {m n} → (m ≤ n) → m + (n ∸ m) ≡ n
  --   lem z≤n        = PE.refl
  --   lem (s≤s m≤n') = PE.cong suc (lem m≤n')
  
  -- bound-≤′ : ∀ {a} {A : Set a} {m n} → (m ≤′ n) → A in-time m → A in-time n
  -- bound-≤′ ≤′-refl     x = x
  -- bound-≤′ (≤′-step l) x = return {n = 1} x >>= bound-≤′ l
