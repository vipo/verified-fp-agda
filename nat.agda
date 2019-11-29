module nat where

open import bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

pred : ℕ → ℕ
pred zero = 0
pred (suc n) = n

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + (x * y)

_<_ : ℕ → ℕ → 𝔹
zero < 0 = ff
zero < suc y = tt
(suc x) < (suc y) = x < y
(suc x) < 0 = ff

_=ℕ_ : ℕ → ℕ → 𝔹
zero =ℕ zero = tt
suc n =ℕ suc m = n =ℕ m
_ =ℕ _ = ff

_≤_ : ℕ → ℕ → 𝔹
x ≤ y = (x < y) || (x =ℕ y)

is-even : ℕ → 𝔹
is-odd : ℕ → 𝔹
is-even zero = tt
is-even (suc n) = is-odd n
is-odd zero = ff
is-odd (suc n) = is-even n
