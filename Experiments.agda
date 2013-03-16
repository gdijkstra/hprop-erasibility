module Experiments where

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

data Id {a} (A : Set a) (x : A) : A -> Set a where
  refl : Id A x x

record Σ {a b} (A : Set a) (B : A -> Set b) : Set (a ⊔ b)  where
  constructor _,_ 
  field
    fst : A
    snd : B fst

Iso : {a : Level} -> Set a -> Set a -> Set a
Iso A B = Σ (A -> B) (\f -> 
          Σ (B -> A) (\g -> 
          Σ ((x : A) -> Id A (g (f x)) x) (\_ -> 
             (x : B) -> Id B (f (g x)) x)))

TrivialIso : (A : Set) -> Iso A A
TrivialIso A = (λ x → x) , ((λ x → x) , ((λ x → refl) , (λ x → refl)))

Contractible : {a : Level} -> Set a -> Set a
Contractible A = Σ A (\center -> (x : A) -> (Id A center x))

-- add naturals and h-level

UnivalenceLight : Set (suc zero)
UnivalenceLight = (A B : Set) -> Iso A B -> Id Set A B
