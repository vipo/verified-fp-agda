module list where

open import bool
open import nat

data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _∷_ : (x : A) (xs : 𝕃 A) → 𝕃 A

length : ∀{ℓ}{A : Set ℓ} → 𝕃 A → ℕ
length [] = 0
length (_ ∷ l) = suc (length l)

_++_ : ∀{ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[] ++ m = m
(x ∷ l) ++ m = x ∷ (l ++ m)

map : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A → B) → 𝕃 A → 𝕃 B 
map f [] = []
map f (x ∷ l) = f x ∷ map f l

filter : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x ∷ l) =
  let r = filter p l
  in if p x then x ∷ r else r

remove : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l : 𝕃 A) → 𝕃 A
remove eq a l = filter (λ x → ~ (eq a x)) l

data maybe {ℓ}(A : Set ℓ) : Set ℓ where
  just : A → maybe A
  nothing : maybe A

nth : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → maybe A
nth n [] = nothing
nth zero (x ∷ l) =  just x
nth (suc n) (x ∷ l) = nth n l

sreverse : ∀{ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A
sreverse [] = []
sreverse (h ∷ t) = (sreverse t) ++ (h ∷ [])

reverse-helper : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
reverse-helper acc [] = acc
reverse-helper acc (x ∷ l) = reverse-helper (x ∷ acc) l 

reverse : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A
reverse l = reverse-helper [] l
