module vector-test where

open import vector
open import nat
open import bool
open import list

test-vector : 𝕍 𝔹 4
test-vector = ff ∷ ff ∷ tt ∷ ff ∷ []

test-vector2 : 𝕃 (𝕍 𝔹 2)
test-vector2 = (ff ∷ ff ∷ []) ∷
               (tt ∷ ff ∷ []) ∷
               []

test-vector3 : 𝕍 (𝕍 𝔹 3) 2
test-vector3 = (tt ∷ tt ∷ ff ∷ []) ∷
               (ff ∷ ff ∷ tt ∷ []) ∷
               []

test-vector-append : 𝕍 𝔹 8
test-vector-append = test-vector ++𝕍 test-vector

concat𝕍-test : 𝕍 𝔹 8
concat𝕍-test = concat𝕍 (test-vector ∷ test-vector ∷ [])

