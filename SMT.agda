module SMT where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)

open import Function using (id ; _∘_ ; _$_ ; _∋_)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; inspect ; [_])

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Env using (Var ; var ; Env ; evalᵛ)

data Formula : Set

-- LFSC: formula_op1
formula-op₁ = Formula → Formula
-- LFSC: formula_op2
formula-op₂ = Formula → Formula → Formula
-- LFSC: formula_op3
formula-op₃ = Formula → Formula → Formula → Formula

-- LFSC: formula
data Formula where
  -- LFSC: true
  trueᶠ  : Formula
  -- LFSC: false
  falseᶠ : Formula

  -- LFSC: not
  notᶠ   : formula-op₁
  -- LFSC: and
  andᶠ   : formula-op₂
  -- LFSC: or
  orᶠ    : formula-op₂

evalᶠ : Formula → Bool
evalᶠ trueᶠ = true
evalᶠ falseᶠ = false

evalᶠ (notᶠ f) = not (evalᶠ f)
evalᶠ (andᶠ f₁ f₂) = evalᶠ f₁ ∧ evalᶠ f₂
evalᶠ (orᶠ f₁ f₂) = evalᶠ f₁ ∨ evalᶠ f₂

propᶠ : Formula → Set
propᶠ trueᶠ  = ⊤
propᶠ falseᶠ = ⊥

propᶠ (notᶠ f) = ¬ propᶠ f
propᶠ (andᶠ f₁ f₂) = propᶠ f₁ × propᶠ f₂
propᶠ (orᶠ f₁ f₂) = propᶠ f₁ ⊎ propᶠ f₂

proveᶠ : ∀ {f} → evalᶠ f ≡ true → propᶠ f
proveᶠ-¬ : ∀ {f} → evalᶠ f ≡ false → ¬ propᶠ f

proveᶠ {trueᶠ} p = tt

proveᶠ {notᶠ f} p with evalᶠ f | inspect evalᶠ f
proveᶠ {notᶠ f} () | true  | _
proveᶠ {notᶠ f} _  | false | [ eq ] = proveᶠ-¬ eq

proveᶠ {andᶠ f₁ f₂} p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᶠ {andᶠ f₁ f₂} _  | true  | [ eq₁ ] | true  | [ eq₂ ] = proveᶠ eq₁ , proveᶠ eq₂
proveᶠ {andᶠ f₁ f₂} () | true  | _       | false | _
proveᶠ {andᶠ f₁ f₂} () | false | _       | true  | _
proveᶠ {andᶠ f₁ f₂} () | false | _       | false | _

proveᶠ {orᶠ f₁ f₂} p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᶠ {orᶠ f₁ f₂} _  | true  | [ eq₁ ] | _     | _       = inj₁ (proveᶠ eq₁)
proveᶠ {orᶠ f₁ f₂} _  | false | _       | true  | [ eq₂ ] = inj₂ (proveᶠ eq₂)
proveᶠ {orᶠ f₁ f₂} () | false | _       | false | _

proveᶠ-¬ {falseᶠ} p = id

proveᶠ-¬ {notᶠ f} p with evalᶠ f | inspect evalᶠ f
proveᶠ-¬ {notᶠ f} _  | true  | [ eq ] = λ x → x (proveᶠ eq)
proveᶠ-¬ {notᶠ f} () | false | _

proveᶠ-¬ {andᶠ f₁ f₂} p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᶠ-¬ {andᶠ f₁ f₂} () | true  | [ eq₁ ] | true  | [ eq₂ ]

proveᶠ-¬ {andᶠ f₁ f₂} _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ { (_ , p₂) → contradiction p₂ (proveᶠ-¬ eq₂) }

proveᶠ-¬ {andᶠ f₁ f₂} _  | false | [ eq₁ ] | true  | [ eq₂ ] =
  λ { (p₁ , _) → contradiction p₁ (proveᶠ-¬ eq₁) }

proveᶠ-¬ {andᶠ f₁ f₂} _  | false | [ eq₁ ] | false | [ eq₂ ] =
  λ { (p₁ , _) → contradiction p₁ (proveᶠ-¬ eq₁) }

proveᶠ-¬ {orᶠ f₁ f₂} p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᶠ-¬ {orᶠ f₁ f₂} () | true  | _       | _     | _
proveᶠ-¬ {orᶠ f₁ f₂} () | false | _       | true  | _

proveᶠ-¬ {orᶠ f₁ f₂} _  | false | [ eq₁ ] | false | [ eq₂ ] =
  λ {
    (inj₁ p₁) → contradiction p₁ (proveᶠ-¬ eq₁) ;
    (inj₂ p₂) → contradiction p₂ (proveᶠ-¬ eq₂)
  }

-- LFSC: th_holds
data Holdsᶠ : Formula → Set where
  holdsᶠ : (f : Formula) → evalᶠ f ≡ true → Holdsᶠ f

module Rules (env : Env) where

  open import SAT env using (Holdsᶜ)

  -- LFSC: atom
  data Atom : Var → Formula → Set where
    atom : (v : Var) → (f : Formula) → evalᵛ env v ≡ evalᶠ f → Atom v f

  -- LFSC: decl_atom - but note the additional Atom parameter
  decl-atom : ∀ {v} f → {{Atom v f}} → ((v : Var) → Atom v f → Holdsᶜ []) → Holdsᶜ []
  decl-atom {v} _ {{a}} fn = fn v a

{-
claus-t : ∀ {v f} → atom v f → holdsᶠ f → holds (pos v ∷ [])
claus-t {v} {f} a h with evalᶠ f | inspect evalᶠ f
... | true  | _      rewrite a = inj₁ tt
... | false | [ eq ] = contradiction h (evalᶠ-f eq)

claus-f : ∀ {v f} → atom v f → holdsᶠ (notᶠ f) → holds (neg v ∷ [])
claus-f {v} {f} a h with evalᶠ f | inspect evalᶠ f
... | true  | [ eq ] = contradiction (evalᶠ-t eq) h
... | false | [ eq ] rewrite a = inj₁ id

assum-t : ∀ {v f c} → atom v f → (holdsᶠ f → holds c) → holds (neg v ∷ c)
assum-t {v} {f} {c} a fn with evalᶠ f | inspect evalᶠ f
... | true  | [ eq ] = inj₂ (fn (evalᶠ-t eq))
... | false | _      rewrite a = inj₁ id

assum-f : ∀ {v f c} → atom v f → (holdsᶠ (notᶠ f) → holds c) → holds (pos v ∷ c)
assum-f {v} {f} {c} a fn with evalᶠ f | inspect evalᶠ f
... | true  | _      rewrite a = inj₁ tt
... | false | [ eq ] = inj₂ (fn (evalᶠ-f eq))
-}
