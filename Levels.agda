module Levels where

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
