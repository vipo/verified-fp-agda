module bool where

data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹
-- {-# BUILTIN BOOL 𝔹 #-}
-- {-# BUILTIN TRUE tt #-}
-- {-# BUILTIN FALSE ff #-}

~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

infix  7 ~_
-- infixl 6 _xor_ _nand_
infixr 6 _&&_
-- infixr 5 _||_

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && b = ff
 
_||_ : 𝔹 → 𝔹 → 𝔹
tt || b = tt
ff || b = b

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then t else f = t
if ff then t else f = f
