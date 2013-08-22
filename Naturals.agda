{-# OPTIONS --without-K #-}

module Naturals where

-- Nats
data ℕ : Set where
  Z : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO    Z #-}
{-# BUILTIN SUC     S #-}

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
Z  + n = n
S m + n = S (m + n)

_*_ : ℕ → ℕ → ℕ
Z   * n = Z
S m * n = n + m * n

{-# BUILTIN NATPLUS _+_ #-}
