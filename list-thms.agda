module list-thms where

open import bool
open import nat
open import nat-thms
open import list

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; inspect; [_])
open import Relation.Binary.PropositionalEquality

length-++ : ∀{ℓ}{A : Set ℓ} (l1 l2 : 𝕃 A) → length (l1 ++ l2) ≡ length l1 + length l2
length-++ [] l2 = refl
length-++ (h ∷ t) l2 rewrite length-++ t l2 = refl

++-assoc : ∀{ℓ}{A : Set ℓ} (l1 l2 l3 : 𝕃 A) → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x ∷ l1) l2 l3 rewrite ++-assoc l1 l2 l3 = refl

length-filter : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) → length (filter p l) ≤ length l ≡ tt
length-filter p [] = refl
length-filter p (x ∷ l) with p x
length-filter p (x ∷ l) | tt = length-filter p l
length-filter p (x ∷ l) | ff = ≤-trans{length (filter p l)} (length-filter p l) (≤-suc (length l))

filter-idem : ∀ {ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) → (filter p (filter p l)) ≡ (filter p l)
filter-idem p [] = refl
filter-idem p (x ∷ l) with p x | inspect p x 
filter-idem p (x ∷ l) | tt | [ p′ ] rewrite p′ | filter-idem p l = refl
filter-idem p (x ∷ l) | ff | [ p′ ] rewrite filter-idem p l = refl

length-reverse-helper : ∀{ℓ}{A : Set ℓ}(a l : 𝕃 A) → length (reverse-helper a l) ≡ length a + length l
length-reverse-helper a [] rewrite +0 (length a) = refl
length-reverse-helper a (x ∷ l) rewrite length-reverse-helper (x ∷ a) l =
  sym (+suc (length a) (length l))

length-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → length (reverse l) ≡ length l
length-reverse = length-reverse-helper []
