{-# OPTIONS --without-K #-}

module IntervalFunctions where

open import Interval
open import Identity

-- All four functions I → I, that are all definitionally different,
-- but all propositionally equal to eachother.

const-I : I → I
const-I = I-rec zer zer refl

const-I' : I → I
const-I' = I-rec one one refl

id-I : I → I
id-I = I-rec zer one seg

flip-I : I → I
flip-I = I-rec one zer (sym seg)

-- flip-I zer evaluates to one
-- flip-I one evaluates to zer
