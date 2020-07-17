module bv where

open import Agda.Builtin.Nat using () renaming (div-helper to divₕ; mod-helper to modₕ)

open import Data.Bool using (Bool; true; false; not; if_then_else_)

import Relation.Binary.PropositionalEquality as P
import Relation.Binary.HeterogeneousEquality as H

open P using (_≡_; _≢_; refl; cong; cong₂; subst; sym; ≢-sym; inspect)
open H using (_≅_)

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Core
open import Data.Nat.Properties

open import Function
open import Relation.Nullary.Negation

divₕ′ : ℕ → ℕ → ℕ
divₕ′ a m = divₕ 0 m a m

modₕ′ : ℕ → ℕ → ℕ
modₕ′ a m = modₕ 0 m a m

1+n<m≡n≤m : ∀ (n m : ℕ) → (n < m) ≡ (suc n ≤ m)
1+n<m≡n≤m n m = refl

a<n⇒a[divₕ]n≡0 : ∀ (a n n′ : ℕ) → a ≤ n → divₕ 0 n′ a n ≡ 0
a<n⇒a[divₕ]n≡0 zero _ _ _ = refl
a<n⇒a[divₕ]n≡0 (suc a) (suc n) n′ (s≤s a≤n) = a<n⇒a[divₕ]n≡0 a n n′ a≤n

a*n[modₕ]n≡0 : ∀ (a n : ℕ) → modₕ 0 n (a * suc n) n ≡ 0
a*n[modₕ]n≡0 zero n = refl
a*n[modₕ]n≡0 (suc a) n rewrite +-comm (suc n) (a * suc n) | a+n[modₕ]n≡a[modₕ]n 0 (a * suc n) n = a*n[modₕ]n≡0 a n

a<n⇒a+b*n[divₕ]n≡b : ∀ (a b n : ℕ) → a ≤ n → divₕ 0 n (a + b * suc n) n ≡ b
a<n⇒a+b*n[divₕ]n≡b a b n a≤n =
  begin
    divₕ′ (a + b * suc n) n
  ≡⟨ +-distrib-divₕ 0 0 a (b * suc n) n lem₁ ⟩
    divₕ′ a n + divₕ′ (b * suc n) n
  ≡⟨ cong (_+ divₕ′ (b * suc n) n) (a<n⇒a[divₕ]n≡0 a n n a≤n) ⟩
    0 + divₕ′ (b * suc n) n
  ≡⟨ +-identityˡ (divₕ 0 n (b * suc n) n) ⟩
    divₕ′ (b * suc n) n
  ≡⟨ m*n/n≡m b (suc n) ⟩
    b
  ∎

  where

  open P.≡-Reasoning

  ≤₁ = a[modₕ]n<n 0 a n
  ≤₂ = ≤-reflexive (a*n[modₕ]n≡0 b n)

  <₃ : n + 0 < suc n
  <₃ = s≤s (≤-reflexive (+-identityʳ n))

  lem₁ : modₕ′ a n + modₕ′ (b * suc n) n < suc n
  lem₁ = <-transʳ (+-mono-≤ ≤₁ ≤₂) <₃ 

a<n⇒a+b*n[modₕ]n≡a : ∀ (a b n : ℕ) → a ≤ n → modₕ 0 n (a + b * suc n) n ≡ a
a<n⇒a+b*n[modₕ]n≡a a zero n a≤n =
  begin
    modₕ 0 n (a + zero * suc n) n
  ≡⟨ cong (λ # → modₕ 0 n # n) (+-identityʳ a) ⟩
    modₕ 0 n a n
  ≡⟨ cong (λ # → modₕ 0 n a #) (sym (m+[n∸m]≡n a≤n)) ⟩
    modₕ 0 n a (a + (n ∸ a))
  ≡⟨ a≤n⇒a[modₕ]n≡a 0 n a (n ∸ a) ⟩
    a
  ∎

  where open P.≡-Reasoning

a<n⇒a+b*n[modₕ]n≡a a (suc b) n a≤n =
  begin
    modₕ′ (a + suc (n + b * suc n)) n
  ≡⟨⟩
    modₕ′ (a + (suc n + b * suc n)) n
  ≡⟨ cong (λ # → modₕ′ (a + #) n) (+-comm (suc n) (b * suc n)) ⟩
    modₕ′ (a + (b * suc n + suc n)) n
  ≡⟨ cong (λ # → modₕ′ # n) (sym (+-assoc a (b * suc n) (suc n))) ⟩
    modₕ′ (a + b * suc n + suc n) n
  ≡⟨ a+n[modₕ]n≡a[modₕ]n 0 (a + b * suc n) n ⟩
    modₕ′ (a + b * suc n) n
  ≡⟨ a<n⇒a+b*n[modₕ]n≡a a b n a≤n ⟩
    a
  ∎

  where open P.≡-Reasoning

a[divₕ]m*n≡a[divₕ]m[divₕ]n : ∀ (a m n : ℕ) → divₕ 0 (m + n + m * n) a (m + n + m * n) ≡ divₕ 0 n (divₕ 0 m a m) n
a[divₕ]m*n≡a[divₕ]m[divₕ]n a m n =
  begin
    divₕ′ a mn
  ≡⟨ cong (λ # → divₕ′ # mn) (div-mod-lemma 0 0 a m) ⟩
    divₕ′ (modₕ′ a m + divₕ′ a m * suc m) mn
  ≡⟨ cong (λ # → divₕ′ (modₕ′ a m + # * suc m) mn) (div-mod-lemma 0 0 (divₕ′ a m) n) ⟩
    divₕ′ (modₕ′ a m + (modₕ′ (divₕ′ a m) n + divₕ′ (divₕ′ a m) n * suc n) * suc m) mn
  ≡⟨ cong (λ # → divₕ′ (modₕ′ a m + #) mn) (*-distribʳ-+ (suc m) (modₕ′ (divₕ′ a m) n) (divₕ′ (divₕ′ a m) n * suc n)) ⟩
    divₕ′ (modₕ′ a m + (modₕ′ (divₕ′ a m) n * suc m + divₕ′ (divₕ′ a m) n * suc n * suc m)) mn
  ≡⟨ cong (λ # → divₕ′ # mn) (sym (+-assoc (modₕ′ a m) (modₕ′ (divₕ′ a m) n * suc m) (divₕ′ (divₕ′ a m) n * suc n * suc m))) ⟩
    divₕ′ (modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m + divₕ′ (divₕ′ a m) n * suc n * suc m) mn
  ≡⟨ cong (λ # → divₕ′ (modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m + #) mn) (*-assoc (divₕ′ (divₕ′ a m) n) (suc n) (suc m))⟩
    divₕ′ (modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m + divₕ′ (divₕ′ a m) n * (suc n * suc m)) mn
  ≡⟨ cong (λ # → divₕ′ (modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m + divₕ′ (divₕ′ a m) n * #) mn) (*-comm (suc n) (suc m)) ⟩
    divₕ′ (modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m + divₕ′ (divₕ′ a m) n * (suc m * suc n)) mn
  ≡⟨ cong (λ # → divₕ′ (modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m + divₕ′ (divₕ′ a m) n * #) mn) lem₁ ⟩
    divₕ′ (modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m + divₕ′ (divₕ′ a m) n * suc mn) mn
  ≡⟨ a<n⇒a+b*n[divₕ]n≡b (modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m) (divₕ′ (divₕ′ a m) n) mn lem₄ ⟩
    divₕ 0 n (divₕ′ a m) n
  ∎

  where

  open P.≡-Reasoning

  mn = m + n + m * n

  lem₁ : suc m * suc n ≡ suc mn
  lem₁ rewrite +-comm m n | *-comm m (suc n) | *-comm m n | +-assoc n m (n * m) = refl

  lem₂ : m + n * suc m ≡ mn
  lem₂ rewrite *-comm n (suc m) | +-assoc m n (m * n) = refl

  ≤₁ = a[modₕ]n<n 0 a m
  ≤₂ = a[modₕ]n<n 0 (divₕ 0 m a m) n
  ≤₃ = ≤-refl {suc m}

  lem₃ = +-mono-≤ ≤₁ (*-mono-≤ ≤₂ ≤₃)

  lem₄ : modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m ≤ mn
  lem₄ = subst (λ # → modₕ′ a m + modₕ′ (divₕ′ a m) n * suc m ≤ #) lem₂ lem₃

a*n[divₕ]b*n≡a[divₕ]b : ∀ (a b n : ℕ) → divₕ 0 (b + n + b * n) (a + n * a) (b + n + b * n) ≡ divₕ 0 b a b
a*n[divₕ]b*n≡a[divₕ]b a b n =
  begin
    divₕ′ na nb
  ≡⟨ cong (λ # → divₕ′ na #) nb≡bn ⟩
    divₕ′ na bn
  ≡⟨ a[divₕ]m*n≡a[divₕ]m[divₕ]n na n b ⟩
    divₕ′ (divₕ′ na n) b
  ≡⟨ cong (λ # → divₕ′ (divₕ′ # n) b) lem₁ ⟩
    divₕ′ (divₕ′ (a * suc n) n) b
  ≡⟨ cong (λ # → divₕ′ # b) (a*n[divₕ]n≡a 0 a n) ⟩
    divₕ 0 b a b
  ∎

  where

  open P.≡-Reasoning

  na = a + n * a

  nb = b + n + b * n
  bn = n + b + n * b

  nb≡bn : nb ≡ bn
  nb≡bn rewrite +-comm n b | *-comm n b = refl

  lem₁ : na ≡ a * suc n
  lem₁ rewrite *-comm a (suc n) = refl

a[modₕ]n≡a∸a[divₕ]n*n : ∀ (a n : ℕ) → modₕ 0 n a n ≡ a ∸ divₕ 0 n a n * suc n
a[modₕ]n≡a∸a[divₕ]n*n a n = sym lem₁

  where

  open P.≡-Reasoning

  lem₁ : a ∸ divₕ′ a n * suc n ≡ modₕ′ a n
  lem₁ =
    begin
      a ∸ divₕ′ a n * suc n
    ≡⟨ cong (_∸ divₕ′ a n * suc n) (div-mod-lemma 0 0 a n) ⟩
      modₕ′ a n + divₕ′ a n * suc n ∸ divₕ′ a n * suc n
    ≡⟨ m+n∸n≡m (modₕ′ a n) (divₕ′ a n * suc n) ⟩
      modₕ 0 n a n
    ∎

a[divₕ]n*n≡a∸a[modₕ]n : ∀ (a n : ℕ) → divₕ 0 n a n * suc n ≡ a ∸ modₕ 0 n a n
a[divₕ]n*n≡a∸a[modₕ]n a n = sym lem₁

  where

  open P.≡-Reasoning

  lem₁ : a ∸ modₕ 0 n a n ≡ divₕ 0 n a n * suc n
  lem₁ =
    begin
      a ∸ modₕ′ a n
    ≡⟨ cong (_∸ modₕ′ a n) (div-mod-lemma 0 0 a n) ⟩
      modₕ′ a n + divₕ′ a n * suc n ∸ modₕ′ a n
    ≡⟨ cong (λ # → #  ∸ modₕ′ a n) (+-comm (modₕ′ a n) (divₕ′ a n * suc n)) ⟩
      divₕ′ a n * suc n + modₕ′ a n ∸ modₕ′ a n
    ≡⟨ m+n∸n≡m ((divₕ′ a n) * suc n) (modₕ′ a n) ⟩
      divₕ 0 n a n * suc n
    ∎

a*n[modₕ]m*n≡[a[modₕ]m]*n : ∀ (a n m : ℕ) → modₕ 0 (m + n + m * n) (a + n * a) (m + n + m * n) ≡ modₕ 0 m a m * suc n
a*n[modₕ]m*n≡[a[modₕ]m]*n a n m =
  begin
    modₕ′ an mn
  ≡⟨ a[modₕ]n≡a∸a[divₕ]n*n an mn ⟩
    an ∸ divₕ′ an mn * suc mn
  ≡⟨ cong (λ # → an ∸ # * suc mn) (a*n[divₕ]b*n≡a[divₕ]b a m n) ⟩
    an ∸ divₕ′ a m * suc mn
  ≡⟨ cong (λ # → an ∸ divₕ′ a m * #) lem₁ ⟩
    an ∸ divₕ′ a m * (suc m * suc n)
  ≡⟨ cong (λ # → an ∸ #) (sym (*-assoc (divₕ′ a m) (suc m) (suc n))) ⟩
    an ∸ divₕ′ a m * suc m * suc n
  ≡⟨ cong (λ # → an ∸ # * suc n) (a[divₕ]n*n≡a∸a[modₕ]n a m) ⟩
    an ∸ (a ∸ modₕ′ a m) * suc n
  ≡⟨ cong (λ # → # ∸ (a ∸ modₕ′ a m) * suc n) lem₂ ⟩
    a * suc n ∸ (a ∸ modₕ′ a m) * suc n
  ≡⟨ sym (*-distribʳ-∸ (suc n) a (a ∸ modₕ′ a m)) ⟩
    (a ∸ (a ∸ modₕ′ a m)) * suc n
  ≡⟨ cong (λ # → # * suc n) (m∸[m∸n]≡n (a[modₕ]n≤a 0 a m)) ⟩
    modₕ 0 m a m * suc n
  ∎
  
  where

  open P.≡-Reasoning

  an = a + n * a
  mn = m + n + m * n

  lem₁ : suc mn ≡ suc m * suc n
  lem₁ rewrite *-comm m (suc n) | *-comm m n | +-comm m n | +-assoc n m (n * m) = refl

  lem₂ : an ≡ a * (suc n)
  lem₂ rewrite *-comm a (suc n) = refl

a<n⇒a+b*n[modₕ]c*n : ∀ (a b c n : ℕ) → a ≤ n → modₕ 0 (c + n + c * n) (a + b * suc n) (c + n + c * n) ≡ a + modₕ 0 (c + n + c * n) (b * suc n) (c + n + c * n)
a<n⇒a+b*n[modₕ]c*n a b c n a≤n =
  begin
    modₕ′ (a + b * suc n) cn
  ≡⟨ a[modₕ]n≡a∸a[divₕ]n*n (a + b * suc n) cn ⟩
    a + b * suc n ∸ divₕ′ (a + b * suc n) cn * suc cn
  ≡⟨ cong (λ # → a + b * suc n ∸ divₕ′ (a + b * suc n) # * suc #) cn≡nc ⟩
    a + b * suc n ∸ divₕ′ (a + b * suc n) nc * suc nc
  ≡⟨ cong (λ # → a + b * suc n ∸ # * suc nc) (a[divₕ]m*n≡a[divₕ]m[divₕ]n (a + b * suc n) n c) ⟩
    a + b * suc n ∸ divₕ′ (divₕ′ (a + b * suc n) n) c * suc nc
  ≡⟨ cong (λ # → a + b * suc n ∸ divₕ′ # c * suc nc) (a<n⇒a+b*n[divₕ]n≡b a b n a≤n) ⟩
    a + b * suc n ∸ divₕ′ b c * suc nc
  ≡⟨ cong (λ # → a + b * suc n ∸ divₕ′ b c * #) lem₁ ⟩
    a + b * suc n ∸ divₕ′ b c * (suc c * suc n)
  ≡⟨ cong (λ # → a + b * suc n ∸ #) (sym (*-assoc (divₕ′ b c) (suc c) (suc n))) ⟩
    a + b * suc n ∸ divₕ′ b c * suc c * suc n
  ≡⟨ cong (λ # → a + b * suc n ∸ # * suc n) (a[divₕ]n*n≡a∸a[modₕ]n b c) ⟩
    a + b * suc n ∸ (b ∸ modₕ′ b c) * suc n
  ≡⟨ cong (λ # → a + b * suc n ∸ #) (*-distribʳ-∸ (suc n) b (modₕ′ b c)) ⟩
    a + b * suc n ∸ (b * suc n ∸ modₕ′ b c * suc n)
  ≡⟨ +-∸-assoc a (m∸n≤m (b * suc n) (modₕ′ b c * suc n)) ⟩
    a + (b * suc n ∸ (b * suc n ∸ modₕ′ b c * suc n))
  ≡⟨ cong (a +_) (m∸[m∸n]≡n (*-monoˡ-≤ (suc n) (a[modₕ]n≤a 0 b c))) ⟩
    a + modₕ′ b c * suc n
  ≡⟨ cong (a +_) (sym (a*n[modₕ]m*n≡[a[modₕ]m]*n b n c)) ⟩
    a + modₕ′ (b + n * b) (c + n + c * n)
  ≡⟨ cong (λ # → a + modₕ′ # (c + n + c * n)) lem₂ ⟩
    a + modₕ′ (b * suc n) (c + n + c * n)
  ∎

  where
  
  open P.≡-Reasoning

  cn = c + n + c * n
  nc = n + c + n * c
  
  cn≡nc : cn ≡ nc
  cn≡nc rewrite +-comm c n | *-comm c n = refl

  lem₁ : suc nc ≡ suc c * suc n
  lem₁ rewrite *-comm c (suc n) | +-assoc n c (n * c) = refl

  lem₂ : b + n * b ≡ b * suc n
  lem₂ rewrite *-comm b (suc n) = refl

data BitVec : (len : ℕ) → Set where
  Nil : BitVec zero
  Bit : {len : ℕ} → Bool -> BitVec len → BitVec (suc len)

bv-not : {len : ℕ} → BitVec len -> BitVec len
bv-not Nil = Nil
bv-not (Bit b bs) = Bit (not b) (bv-not bs)

bv-to-nat : {len : ℕ} → BitVec len → ℕ
bv-to-nat Nil = zero
bv-to-nat (Bit b bs) = (if b then 1 else 0) + 2 * bv-to-nat bs

nat-to-bv : {len : ℕ} → (x : ℕ) → BitVec len
nat-to-bv {zero} _ = Nil
nat-to-bv {suc len} x = Bit (not ((x % 2) ≡ᵇ 0)) (nat-to-bv (x / 2))

bv-nat-bv : ∀ {len : ℕ} → ∀ (bv : BitVec len) → nat-to-bv (bv-to-nat bv) ≡ bv
bv-nat-bv {zero} Nil = refl

bv-nat-bv {suc len} (Bit false bs) =
  begin
    nat-to-bv (bv-to-nat (Bit false bs))
  ≡⟨⟩
    nat-to-bv (2 * bv-to-nat bs)
  ≡⟨⟩
    Bit (not (((2 * bv-to-nat bs) % 2) ≡ᵇ 0)) (nat-to-bv ((2 * bv-to-nat bs) / 2))
  ≡⟨ cong (λ x → Bit (not (x ≡ᵇ 0)) (nat-to-bv ((2 * bv-to-nat bs) / 2))) (lem₁ (bv-to-nat bs)) ⟩
    Bit (not (0 ≡ᵇ 0)) (nat-to-bv (2 * bv-to-nat bs / 2))
  ≡⟨ cong (λ x → Bit false (nat-to-bv x)) (lem₂ (bv-to-nat bs)) ⟩
    Bit false (nat-to-bv (bv-to-nat bs))
  ≡⟨ cong (Bit false) (bv-nat-bv bs) ⟩
    Bit false bs
  ∎ 

  where

  open P.≡-Reasoning

  lem₁ : ∀ (x : ℕ) → 2 * x % 2 ≡ 0
  lem₁ x rewrite *-comm 2 x = a<n⇒a+b*n[modₕ]n≡a 0 x 1 z≤n
  
  lem₂ : ∀ (x : ℕ) → 2 * x / 2 ≡ x
  lem₂ x rewrite *-comm 2 x = a<n⇒a+b*n[divₕ]n≡b 0 x 1 z≤n

bv-nat-bv {suc len} (Bit true bs) =
  begin
    nat-to-bv (bv-to-nat (Bit true bs))
  ≡⟨⟩
    nat-to-bv (1 + 2 * bv-to-nat bs)
  ≡⟨⟩
    Bit (not (((1 + 2 * bv-to-nat bs) % 2) ≡ᵇ 0)) (nat-to-bv ((1 + 2 * bv-to-nat bs) / 2))
  ≡⟨ cong (λ x → Bit (not (x ≡ᵇ 0)) (nat-to-bv ((1 + 2 * bv-to-nat bs) / 2))) (lem₁ (bv-to-nat bs)) ⟩
    Bit (not (1 ≡ᵇ 0)) (nat-to-bv ((1 + 2 * bv-to-nat bs) / 2))
  ≡⟨ cong (λ x → Bit true (nat-to-bv x)) (lem₂ (bv-to-nat bs)) ⟩
    Bit true (nat-to-bv (bv-to-nat bs))
  ≡⟨ cong (Bit true) (bv-nat-bv bs) ⟩
    Bit true bs
  ∎

  where

  open P.≡-Reasoning

  lem₁ : ∀ (x : ℕ) → (1 + 2 * x) % 2 ≡ 1
  lem₁ x rewrite *-comm 2 x = a<n⇒a+b*n[modₕ]n≡a 1 x 1 (≤-refl {1}) 

  lem₂ : ∀ (x : ℕ) → (1 + 2 * x) / 2 ≡ x
  lem₂ x rewrite *-comm 2 x = a<n⇒a+b*n[divₕ]n≡b 1 x 1 (≤-refl {1})

nat-bv-nat : ∀ {len : ℕ} → ∀ (a : ℕ) → bv-to-nat (nat-to-bv {len} a) ≡ modₕ 0 (2 ^ len ∸ 1) a (2 ^ len ∸ 1)
nat-bv-nat {zero} a = sym (a[modₕ]1≡0 a)
nat-bv-nat {suc len} a =
  begin
    bv-to-nat (nat-to-bv {suc len} a)
  ≡⟨⟩
    (if not (modₕ′ a 1 ≡ᵇ 0) then 1 else 0) + 2 * (bv-to-nat (nat-to-bv {len} (divₕ′ a 1))) 
  ≡⟨ cong (λ # → (if not (a % 2 ≡ᵇ 0) then 1 else 0) + 2 * #) (nat-bv-nat {len} (divₕ′ a 1)) ⟩
    (if not (modₕ′ a 1 ≡ᵇ 0) then 1 else 0) + 2 * (modₕ′ (divₕ′ a 1) (2 ^ len ∸ 1))
  ≡⟨ cong (λ # → (if not (a % 2 ≡ᵇ 0) then 1 else 0) + #) (*-comm 2 (modₕ′ (divₕ′ a 1) (2 ^ len ∸ 1))) ⟩
    (if not (modₕ′ a 1 ≡ᵇ 0) then 1 else 0) + (modₕ′ (divₕ′ a 1) (2 ^ len ∸ 1)) * 2
  ≡⟨ cong (λ # → (if not (a % 2 ≡ᵇ 0) then 1 else 0) + #) (sym (a*n[modₕ]m*n≡[a[modₕ]m]*n (divₕ′ a 1) 1 ((2 ^ len) ∸ 1))) ⟩
    (if not (modₕ′ a 1 ≡ᵇ 0) then 1 else 0) + (modₕ′ (2 * divₕ′ a 1) (2 ^ len ∸ 1 + 1 + ((2 ^ len) ∸ 1) * 1))
  ≡⟨ cong (λ # → (if not (a % 2 ≡ᵇ 0) then 1 else 0) + (modₕ′ # (2 ^ len ∸ 1 + 1 + ((2 ^ len) ∸ 1) * 1))) (*-comm 2 (divₕ′ a 1)) ⟩
    (if not (modₕ′ a 1 ≡ᵇ 0) then 1 else 0) + (modₕ′ (divₕ′ a 1 * 2) (2 ^ len ∸ 1 + 1 + ((2 ^ len) ∸ 1) * 1))
  ≡⟨ sym (a<n⇒a+b*n[modₕ]c*n (if not (a % 2 ≡ᵇ 0) then 1 else 0) (divₕ′ a 1) ((2 ^ len) ∸ 1) 1 lem₁) ⟩
    modₕ′ ((if not (modₕ′ a 1 ≡ᵇ 0) then 1 else 0) + divₕ′ a 1 * 2) ((2 ^ len) ∸ 1 + 1 + ((2 ^ len) ∸ 1) * 1)
  ≡⟨ cong (λ # → modₕ′ (# + divₕ′ a 1 * 2) ((2 ^ len) ∸ 1 + 1 + ((2 ^ len) ∸ 1) * 1)) (lem₂ a) ⟩
    modₕ′ (modₕ′ a 1 + divₕ′ a 1 * 2) ((2 ^ len) ∸ 1 + 1 + ((2 ^ len) ∸ 1) * 1)
  ≡⟨ cong (λ # → modₕ′ # ((2 ^ len) ∸ 1 + 1 + ((2 ^ len) ∸ 1) * 1)) (sym (div-mod-lemma 0 0 a 1)) ⟩
    modₕ′ a ((2 ^ len) ∸ 1 + 1 + ((2 ^ len) ∸ 1) * 1)
  ≡⟨ cong (λ # → modₕ′ a (# + ((2 ^ len) ∸ 1) * 1)) (m∸n+n≡m (lem₃ len)) ⟩
    modₕ′ a ((2 ^ len) + ((2 ^ len) ∸ 1) * 1)
  ≡⟨ cong (λ # → modₕ′ a ((2 ^ len) + #)) (*-identityʳ ((2 ^ len) ∸ 1)) ⟩
    modₕ′ a ((2 ^ len) + ((2 ^ len) ∸ 1))
  ≡⟨ cong (λ # → modₕ′ a #) (sym (+-∸-assoc (2 ^ len) (lem₃ len))) ⟩
    modₕ′ a ((2 ^ len) + (2 ^ len) ∸ 1)
  ≡⟨ cong (λ # → modₕ′ a ((2 ^ len) + # ∸ 1)) (sym (+-identityʳ (2 ^ len))) ⟩
    modₕ′ a ((2 ^ len) + ((2 ^ len) + 0) ∸ 1)
  ∎
  
  where

  open P.≡-Reasoning

  lem₁ : (if not (modₕ′ a 1 ≡ᵇ 0) then 1 else 0) ≤ 1
  lem₁ with modₕ′ a 1 ≡ᵇ 0
  ... | true = z≤n
  ... | false = s≤s z≤n

  lem₂ : ∀ (a : ℕ) → (if not (modₕ′ a 1 ≡ᵇ 0) then 1 else 0) ≡ modₕ′ a 1
  lem₂ zero = refl
  lem₂ (suc zero) = refl
  lem₂ (suc (suc a)) rewrite a+n[modₕ]n≡a[modₕ]n 0 a 1 = lem₂ a 

  lem₃ : ∀ (a : ℕ) → 1 ≤ 2 ^ a
  lem₃ zero = s≤s z≤n
  lem₃ (suc a) rewrite +-identityʳ (2 ^ a) = ≤-trans (s≤s (z≤n {1})) (+-mono-≤ (lem₃ a) (lem₃ a))

data Big (max : ℕ) : (len : ℕ) → Set where
  nil : Big max zero
  limb : {len : ℕ} → (l : ℕ) → l ≤ max → Big max len → Big max (suc len)

big-to-nat : {max len : ℕ} → Big max len → ℕ
big-to-nat nil = zero
big-to-nat {max} (limb l _ ls) = l + suc max * big-to-nat ls

nat-to-big : {max len : ℕ} → (x : ℕ) → Big max len
nat-to-big {_} {zero} _ = nil
nat-to-big {max} {suc len} x = limb (modₕ′ x max) (a[modₕ]n<n 0 x max) (nat-to-big (divₕ′ x max))

big-nat-big : ∀ {max len : ℕ} → ∀ (big : Big max len) → nat-to-big (big-to-nat big) ≡ big
big-nat-big {max} {zero} nil = refl
big-nat-big {max} {suc len} (limb l l≤max ls) =
  begin
    nat-to-big (big-to-nat (limb l l≤max ls))
  ≡⟨⟩
    nat-to-big (l + suc max * big-to-nat ls)
  ≡⟨ cong (λ # → nat-to-big (l + #)) (*-comm (suc max) (big-to-nat ls)) ⟩
    nat-to-big (l + big-to-nat ls * suc max)
  ≡⟨⟩
    limb (modₕ′ (l + big-to-nat ls * suc max) max) (a[modₕ]n<n 0 (l + big-to-nat ls * suc max) max) (nat-to-big (divₕ′ (l + big-to-nat ls * suc max) max))
  ≡⟨ cong (λ # → limb (modₕ′ (l + big-to-nat ls * suc max) max) # (nat-to-big (divₕ′ (l + big-to-nat ls * suc max) max))) lem₃ ⟩
    limb (modₕ′ (l + big-to-nat ls * suc max) max) lem₂ (nat-to-big (divₕ′ (l + big-to-nat ls * suc max) max))
  ≡⟨ lem₄ len (nat-to-big (divₕ′ (l + big-to-nat ls * suc max) max)) ⟩
    limb l l≤max (nat-to-big (divₕ′ (l + big-to-nat ls * suc max) max))
  ≡⟨ cong (λ # → limb l l≤max (nat-to-big #)) (a<n⇒a+b*n[divₕ]n≡b l (big-to-nat ls) max l≤max) ⟩
    limb l l≤max (nat-to-big (big-to-nat ls))
  ≡⟨ cong (λ # → limb l l≤max #) (big-nat-big ls) ⟩
    limb l l≤max ls
  ∎

  where

  open P.≡-Reasoning

  lem₁ = a<n⇒a+b*n[modₕ]n≡a l (big-to-nat ls) max l≤max
  lem₂ = subst (_≤ max) (sym lem₁) l≤max
  lem₃ = ≤-irrelevant (a[modₕ]n<n 0 (l + big-to-nat ls * suc max) max) lem₂

  lem₄ : ∀ (len : ℕ) → ∀ (x : Big max len) → limb (modₕ′ (l + big-to-nat ls * suc max) max) lem₂ x ≡ limb l l≤max x
  lem₄ len x rewrite lem₁ = refl

{-
nat-big-nat : ∀ {max len : ℕ} → ∀ (n : ℕ) → big-to-nat (nat-to-big {len} n) ≡ modₕ 0 (2 ^ len ∸ 1) n (2 ^ len ∸ 1)
nat-big-nat {_} {zero} n = sym (a[modₕ]1≡0 n)
nat-big-nat {max} {suc len} n = {!!}
-}
