module Env where

open import Agda.Primitive using () renaming (lzero to 0ℓ)

open import Data.Bool using (Bool ; true ; false)
open import Data.Maybe using (just ; nothing)
open import Data.Nat using (ℕ ; _<_)
open import Data.Nat.Properties using (<-trans) renaming (<-strictTotalOrder to <-STO)

open import Function using (_∘_ ; id)

open import Relation.Binary
  using (Transitive ; Trichotomous ; tri< ; tri≈ ; tri>)
  renaming (StrictTotalOrder to STO; IsStrictTotalOrder to ISTO)

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; cong)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)

-- LFSC: var
data Var : Set where
  var : ℕ → Bool → Var

ℕ-comp = ISTO.compare (STO.isStrictTotalOrder <-STO)

data Var-< : Var → Var → Set where
  f<t : ∀ {m n}         → Var-< (var m false) (var n true)
  f<f : ∀ {m n} → m < n → Var-< (var m false) (var n false)
  t<t : ∀ {m n} → m < n → Var-< (var m true)  (var n true)

var-<-trans : Transitive Var-<
var-<-trans {var _ false} {var _ true}  {var _ true}  f<t      _        = f<t
var-<-trans {var _ false} {var _ false} {var _ true}  (f<f _)  f<t      = f<t
var-<-trans {var _ false} {var _ false} {var _ false} (f<f p₁) (f<f p₂) = f<f (<-trans p₁ p₂)
var-<-trans {var _ true}  {var _ true}  {var _ true}  (t<t p₁) (t<t p₂) = t<t (<-trans p₁ p₂)

var-≡ : ∀ {m n a b} → var m a ≡ var n b → m ≡ n
var-≡ refl = refl

var-< : ∀ {m n b} → Var-< (var m b) (var n b) → m < n
var-< (t<t p) = p
var-< (f<f p) = p

var-comp : Trichotomous _≡_ Var-<
var-comp (var m true) (var n true) with ℕ-comp m n
... | tri< p₁ p₂ p₃ = tri< (t<t p₁)     (p₂ ∘ var-≡)                 (p₃ ∘ var-<)
... | tri≈ p₁ p₂ p₃ = tri≈ (p₁ ∘ var-<) (cong (λ # → var # true) p₂) (p₃ ∘ var-<)
... | tri> p₁ p₂ p₃ = tri> (p₁ ∘ var-<) (p₂ ∘ var-≡)                 (t<t p₃)

var-comp (var m true)  (var n false) = tri> (λ ()) (λ ()) f<t
var-comp (var m false) (var n true)  = tri< f<t    (λ ()) (λ ())

var-comp (var m false) (var n false) with ℕ-comp m n
... | tri< p₁ p₂ p₃ = tri< (f<f p₁)     (p₂ ∘ var-≡)                  (p₃ ∘ var-<)
... | tri≈ p₁ p₂ p₃ = tri≈ (p₁ ∘ var-<) (cong (λ # → var # false) p₂) (p₃ ∘ var-<)
... | tri> p₁ p₂ p₃ = tri> (p₁ ∘ var-<) (p₂ ∘ var-≡)                  (f<f p₃)

var-<-ISTO : ISTO _≡_ Var-<
var-<-ISTO = record { isEquivalence = isEquivalence ; trans = var-<-trans ; compare = var-comp }

var-<-STO : STO 0ℓ 0ℓ 0ℓ
var-<-STO = record { Carrier = Var ; _≈_ = _≡_ ; _<_ = Var-< ; isStrictTotalOrder = var-<-ISTO }

evalᵛ : Var → Bool
evalᵛ (var _ b) = b
