module nat-thms where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Data.Sum using (inj₁; inj₂)

open import nat
open import bool
open import bool-thms

0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 zero = refl
+0 (suc k) rewrite +0 k = refl  

+-assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc zero y z = refl
+-assoc (suc x) y z rewrite +-assoc x y z = refl

+suc : ∀ (x y : ℕ) → x + (suc y) ≡ suc (x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+-comm : ∀ (x y : ℕ) → x + y ≡ y + x
+-comm zero y rewrite +0 y = refl
+-comm (suc x) y rewrite +suc y x | +-comm x y = refl

*-distrib : ∀ (x y z : ℕ) → (x + y) * z ≡ (x * z) + (y * z)
*-distrib zero y z = refl
*-distrib (suc x) y z rewrite *-distrib x y z = +-assoc z (x * z) (y * z)

*0 : ∀ (x : ℕ) → x * 0 ≡ 0
*0 zero = refl
*0 (suc x) rewrite *0 x = refl

*suc : ∀ (x y : ℕ) → x * (suc y) ≡ x + (x * y)
*suc zero y = refl
*suc (suc x) y rewrite *suc x y | +-assoc y x (x * y) | +-assoc x y (x * y) | +-comm y x = refl

*-comm : ∀ (x y : ℕ) → x * y ≡ y * x
*-comm zero y rewrite *0 y = refl
*-comm (suc x) y rewrite *suc y x | *-comm x y = refl

*-assoc : ∀ (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
*-assoc zero y z = refl
*-assoc (suc x) y z rewrite *-assoc x y z | *-distrib y (x * y) z = refl

<-0 : ∀ (x : ℕ) → x < 0 ≡ ff
<-0 zero = refl
<-0 (suc x) = refl

<-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
<-trans {x} {0} p1 p2 rewrite <-0 x = 𝔹-contra p1
<-trans {0} {suc y} {0} p1 ()
<-trans {0} {suc y} {suc z} p1 p2 = refl  
<-trans {suc x} {suc y} {0} p1 ()
<-trans {suc x} {suc y} {suc z} p1 p2 = <-trans {x} {y} {z} p1 p2

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ tt → x ≡ y
=ℕ-to-≡ {zero} {zero} e = refl 
=ℕ-to-≡ {zero} {suc y} () 
=ℕ-to-≡ {suc x} {zero} ()
=ℕ-to-≡ {suc x} {suc y} e rewrite =ℕ-to-≡ {x} {y} e = refl

=ℕ-refl : ∀ (x : ℕ) → (x =ℕ x) ≡ tt
=ℕ-refl zero = refl
=ℕ-refl (suc k) = =ℕ-refl k

≤-trans : ∀ {x y z : ℕ} → x ≤ y ≡ tt → y ≤ z ≡ tt → x ≤ z ≡ tt
≤-trans {x} {y} {z} p1 p2 with ||-split p1 | ||-split p2
... | inj₁ p' | inj₁ p'' rewrite <-trans {x} p' p'' = refl
... | inj₂ p' | inj₁ p'' rewrite =ℕ-to-≡ {x} p'  | p'' = refl
... | inj₁ p' | inj₂ p'' rewrite =ℕ-to-≡ {y} p'' | p' = refl
... | inj₂ p' | inj₂ p'' rewrite =ℕ-to-≡ {x} p'  | =ℕ-to-≡ {y} p'' | =ℕ-refl z | ||-tt (z < z) = refl

=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ tt
=ℕ-from-≡ {x} refl = =ℕ-refl x  

<-suc : ∀ (n : ℕ) → n < suc n ≡ tt
<-suc zero = refl
<-suc (suc n) rewrite <-suc n = refl

≤-suc : ∀ (n : ℕ) → n ≤ suc n ≡ tt
≤-suc zero = refl
≤-suc (suc n) rewrite <-suc n = refl

even~odd : ∀ (x : ℕ) → is-even x ≡ ~ is-odd x
odd~even : ∀ (x : ℕ) → is-odd x ≡ ~ is-even x
even~odd zero = refl
even~odd (suc x) = odd~even x
odd~even zero = refl
odd~even (suc x) = even~odd x


