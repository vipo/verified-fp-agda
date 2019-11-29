module vector where

open import bool
open import nat

open import Relation.Binary.PropositionalEquality

data 𝕍 {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  [] : 𝕍 A 0
  _∷_ : {n : ℕ} (x : A) (xs : 𝕍 A n) → 𝕍 A (suc n)

infixr 6 _∷_

_++𝕍_ : ∀ {ℓ}{A : Set ℓ} {n m : ℕ} → 𝕍 A n → 𝕍 A m → 𝕍 A (n + m)
[] ++𝕍 m = m
(x ∷ n) ++𝕍 m = x ∷ (n ++𝕍 m)

head𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕍 A (suc n) → A
head𝕍 (x ∷ _) = x

tail𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕍 A (pred n)
tail𝕍 [] = []
tail𝕍 (x ∷ n) = n

map𝕍 : ∀{ℓ ℓ′}{A : Set ℓ}{B : Set ℓ′}{n : ℕ} → (A → B) → 𝕍 A n → 𝕍 B n
map𝕍 f [] = []
map𝕍 f (x ∷ n) = f x ∷ map𝕍 f n

concat𝕍 : ∀{ℓ}{A : Set ℓ}{n m : ℕ} → 𝕍 (𝕍 A n) m → 𝕍 A (m * n)
concat𝕍 [] = []
concat𝕍 (v ∷ v₁) = v ++𝕍 (concat𝕍 v₁)

nth𝕍 : ∀{ℓ}{A : Set ℓ}{m : ℕ} → (n : ℕ) → n < m ≡ tt → 𝕍 A m → A
nth𝕍 zero _ (x ∷ _) = x
nth𝕍 (suc n) p (_ ∷ xs) = nth𝕍 n p xs
nth𝕍 zero () []
nth𝕍 (suc n) () []

repeat𝕍 : ∀{ℓ} {A : Set ℓ} → (a : A) (n : ℕ) → 𝕍 A n
repeat𝕍 a zero = []
repeat𝕍 a (suc n) = a ∷ repeat𝕍 a n
