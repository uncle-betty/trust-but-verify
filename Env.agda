module Env where

open import Agda.Primitive using () renaming (lzero to 0ℓ)

open import Data.Bool using (Bool ; false)
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
  var : ℕ → Var

ℕ-comp = ISTO.compare (STO.isStrictTotalOrder <-STO)

data Var-< : Var → Var → Set where
  v<v : ∀ {m n} → m < n → Var-< (var m) (var n)

var-<-trans : Transitive Var-<
var-<-trans {var m} {var n} {var o} (v<v m<n) (v<v n<o) = v<v (<-trans m<n n<o)

var-≡ : ∀ {m n} → var m ≡ var n → m ≡ n
var-≡ refl = refl

var-< : ∀ {m n} → Var-< (var m) (var n) → m < n
var-< (v<v p) = p

var-comp : Trichotomous _≡_ Var-<
var-comp (var m) (var n) with ℕ-comp m n
... | tri< p₁ p₂ p₃ = tri< (v<v p₁)     (p₂ ∘ var-≡)  (p₃ ∘ var-<)
... | tri≈ p₁ p₂ p₃ = tri≈ (p₁ ∘ var-<) (cong var p₂) (p₃ ∘ var-<)
... | tri> p₁ p₂ p₃ = tri> (p₁ ∘ var-<) (p₂ ∘ var-≡)  (v<v p₃)

var-<-ISTO : ISTO _≡_ Var-<
var-<-ISTO = record { isEquivalence = isEquivalence ; trans = var-<-trans ; compare = var-comp }

var-<-STO : STO 0ℓ 0ℓ 0ℓ
var-<-STO = record { Carrier = Var ; _≈_ = _≡_ ; _<_ = Var-< ; isStrictTotalOrder = var-<-ISTO }

import Data.Tree.AVL.Map var-<-STO as M using (Map ; empty ; insert ; lookup)
import Data.Tree.AVL.Indexed var-<-STO as IM using (const)
import AVL var-<-STO (IM.const Bool) id (λ _ _ → refl) as AM using (avl-insed ; avl-other)

map-insed : ∀ v (b : Bool) m → (M.lookup v (M.insert v b m)) ≡ just b
map-insed v b m = AM.avl-insed v b m

map-other : ∀ v′ v (b : Bool) m → v′ ≢ v → (M.lookup v′ (M.insert v b m)) ≡ M.lookup v′ m
map-other v′ v b m = AM.avl-other v′ v b m

Env = M.Map Bool

ε = M.empty

evalᵛ : Env → Var → Bool
evalᵛ env v with M.lookup v env
... | just b  = b
... | nothing = false

assignᵛ : Var → Bool → Env → Env
assignᵛ v b env = M.insert v b env
