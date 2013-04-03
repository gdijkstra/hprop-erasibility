{-# OPTIONS --without-K #-}

module Experiments where

-- Nats
data ℕ : Set where
  Z : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO    Z #-}
{-# BUILTIN SUC     S #-}

-- Level stuff
infixl 6 _⊔_

postulate
  Level : Set
  zero  : Level
  suc   : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

data Id {a} (A : Set a) (x : A) : A → Set a where
  refl : Id A x x

transport : {a : Level} {B : Set a} (E : B → Set a) {b₁ b₂ : B} → Id B b₁ b₂ → E b₁ → E b₂
transport E refl = λ x → x

-- I'm not really happy with this, as it relies on
-- dot-patterns. Conceptually, the actual resulting path lives in the
-- total space.
apd : {a : Level} {B : Set a} {E : B → Set a} {b₁ b₂ : B} → (f : (x : B) → E x) → (β : Id B b₁ b₂)
  → Id (E b₂) (transport E β (f b₁)) (f b₂)
apd f refl = refl

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    snd : B fst

Iso : {a : Level} → Set a → Set a → Set a
Iso A B = Σ (A → B) (\f → 
          Σ (B → A) (\g → 
          Σ ((x : A) → Id A (g (f x)) x) (\_ → 
             (x : B) → Id B (f (g x)) x)))

TrivialIso : (A : Set) → Iso A A
TrivialIso A = (λ x → x) , ((λ x → x) , ((λ x → refl) , (λ x → refl)))

isContractible : {a : Level} → Set a → Set a
isContractible A = Σ A (λ center → (x : A) → (Id A center x))

h-level : {a : Level} → ℕ → Set a → Set a
h-level Z     A = isContractible A
h-level (S n) A = (x : A) → (y : A) → h-level n (Id A x y)

h-prop : {a : Level} → Set a → Set a
h-prop A = h-level 1 A

h-set : {a : Level} → Set a → Set a
h-set A = h-level 2 A

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

-- filtration property
-- Proofs left open are conceptually easy, but involves some equational reasoning.
h-levelFiltration : {a : Level} → (A : Set a) → (n : ℕ) → h-level n A → h-level (S n) A
h-levelFiltration A Z (center , xToCenter) = {!!}
h-levelFiltration A (S n) proof = λ x y → h-levelFiltration (Id A x y) n (proof x y)

-- Univalence in the case of h-sets.
UnivalenceLight : {a : Level} → Set (suc a)
UnivalenceLight {a} = (A B : Set a) → h-set A → h-set B → Iso A B → Id (Set a) A B

sym : {A : Set} {a b : A} → (Id A a b) → (Id A b a)
sym refl = refl

