{-# OPTIONS --without-K #-}

module IntervalFunctions where

open import Interval
open import Identity

const-I : I → I
const-I = I-rec zer one seg

-- const-I zer evaluates to zer
-- const-I one evaluates to one

flip-I : I → I
flip-I = I-rec one zer (sym seg)

-- flip-I zer evaluates to one
-- flip-I one evaluates to zer

-- We cannot distinguish these functions in Agda.
