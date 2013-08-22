{-# OPTIONS --without-K #-}

module Unit where

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
