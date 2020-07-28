module SMT where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ ; not-¬)
open import Data.Empty using (⊥)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)

open import Function using (id ; _∘_ ; _$_ ; _∋_)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst ; sym ; inspect ; [_])

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Env using (Var ; var ; Env ; evalᵛ)

--- SMT ---

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

  open import SAT env using (pos ; neg ; Holdsᶜ ; holdsᶜ ; evalᶜ ; not-t⇒f ; f⇒not-t)

  -- LFSC: atom
  data Atom : Var → Formula → Set where
    atom : (v : Var) → (f : Formula) → evalᵛ env v ≡ evalᶠ f → Atom v f

  -- LFSC: decl_atom - adapted: additional Atom, missing Var
  decl-atom : ∀ {v} f → {{Atom v f}} → (Atom v f → Holdsᶜ []) → Holdsᶜ []
  decl-atom _ {{a}} fn = fn a

  -- LFSC: clausify_form
  clausi : ∀ {f v} → Atom v f → Holdsᶠ f → Holdsᶜ (pos v ∷ [])

  clausi {f} {v} (atom .v .f a) (holdsᶠ .f h)
    rewrite h
    = holdsᶜ (pos v ∷ []) (subst (λ # → # ∨ false ≡ true) (sym a) refl)

  -- LFSC: clausify_form_not
  clausi-¬ : ∀ {f v} → Atom v f → Holdsᶠ (notᶠ f) → Holdsᶜ (neg v ∷ [])

  clausi-¬ {f} {v} (atom .v .f a) (holdsᶠ .(notᶠ f) h)
    rewrite not-t⇒f h
    = holdsᶜ (neg v ∷ []) (subst (λ # → not # ∨ false ≡ true) (sym a) refl)

  -- LFSC: clausify_false
  clausi-f : Holdsᶠ falseᶠ → Holdsᶜ []
  clausi-f (holdsᶠ .falseᶠ ())

  -- LFSC: th_let_pf
  mpᶠ : ∀ {f} → Holdsᶠ f → (Holdsᶠ f → Holdsᶜ []) → Holdsᶜ []
  mpᶠ {f} h fn = fn h

  -- LFSC: contra
  contra : ∀ {f} → Holdsᶠ f → Holdsᶠ (notᶠ f) → Holdsᶠ falseᶠ
  contra {f} (holdsᶠ .f h₁) (holdsᶠ .(notᶠ f) h₂) = contradiction (not-t⇒f h₂) (not-¬ h₁)

  holds⇒eval : ∀ {f c} → (Holdsᶠ f → Holdsᶜ c) → evalᶠ f ≡ true → evalᶜ c ≡ true
  holds⇒eval {f} {c} fn e with fn (holdsᶠ f e)
  ... | holdsᶜ .c h = h

  holds⇒eval-¬ : ∀ {f c} → (Holdsᶠ (notᶠ f) → Holdsᶜ c) → evalᶠ f ≡ false → evalᶜ c ≡ true
  holds⇒eval-¬ {f} {c} fn e with fn (holdsᶠ (notᶠ f) (f⇒not-t e))
  ... | holdsᶜ .c h = h

  -- LFSC: ast
  assum : ∀ {v f c} → Atom v f → (Holdsᶠ f → Holdsᶜ c) → Holdsᶜ (neg v ∷ c)
  assum {v} {f} {c} (atom .v .f a) fn = holdsᶜ (neg v ∷ c) lem

    where

    lem : not (evalᵛ env v) ∨ evalᶜ c ≡ true
    lem with evalᶠ f | inspect evalᶠ f
    lem | true  | [ eq ] rewrite a = holds⇒eval fn eq
    lem | false | [ eq ] rewrite a = refl

  -- LFSC: asf
  assum-¬ : ∀ {v f c} → Atom v f → (Holdsᶠ (notᶠ f) → Holdsᶜ c) → Holdsᶜ (pos v ∷ c)
  assum-¬ {v} {f} {c} (atom .v .f a) fn = holdsᶜ (pos v ∷ c) lem

    where

    lem : evalᵛ env v ∨ evalᶜ c ≡ true
    lem with evalᶠ f | inspect evalᶠ f
    lem | true  | [ eq ] rewrite a = refl
    lem | false | [ eq ] rewrite a = holds⇒eval-¬ fn eq

--- Base theory ---

-- XXX - remove some day, CVC4 says that these are temporary
postulate
  -- LFSC: trust
  trust-f : Holdsᶠ falseᶠ
  -- LFSC: trust_f
  trustᶠ : (f : Formula) → Holdsᶠ f
