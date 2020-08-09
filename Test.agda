module Test where

open import Data.Bool using (Bool ; false ; T)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_×_)
open import Function using (id ; _$_)
open import Function.Equivalence using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Base using (trust)
open import Env using (var ; ε ; assignᵛ)

open import SMT as S
  using (
    trueᶠ ; falseᶠ ; notᶠ ; iffᶠ ; appᵇ ; boolˣ ; equˣ ;
    eval ; Holds ; holds ; _≡ᵇ_
  )

env =
  assignᵛ (var 1) (eval falseᶠ) $
  ε

open import SAT env
  using (
    pos ; neg ; Holdsᶜ ; expand ; from⁺ ; fromᶜ ;
    resolve-r ; resolve-r⁺ ; resolve-q ; resolve-q⁺ ; mpᶜ ; mp⁺
  )

open S.Rules env using (Atom ; atom ; mp ; assum ; assum-¬ ; clausi-f ; contra ; final)

-- SAT test #1

sat₁ : Holdsᶜ (pos (var 0) ∷ []) → Holdsᶜ (neg (var 1) ∷ []) →
  Holdsᶜ (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ []

sat₁ a b r =
  let a⁺ = expand a in
  let b⁺ = expand b in
  let r⁺ = expand r in
  let x₁ = resolve-r a⁺ r⁺ (var 0) in
  let x₂ = resolve-q b⁺ x₁ (var 1) in
  mp⁺ x₂ id

-- SAT test #2

instance
  _ = from⁺
  _ = fromᶜ

sat₂ : Holdsᶜ (pos (var 0) ∷ []) → Holdsᶜ (neg (var 1) ∷ []) →
  Holdsᶜ (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ []

sat₂ a b r =
  let x₁ = resolve-r⁺ a r  (var 0) in
  let x₂ = resolve-q⁺ b x₁ (var 1) in
  mp⁺ x₂ id

-- SMT test #1

smt₁ =
  λ (x : Bool) →
  λ (as₁ : Holds trueᶠ) →
  λ (as₂ : Holds (notᶠ (iffᶠ (appᵇ x) (appᵇ x)))) →
  let let₁ = falseᶠ in
  mp (trust falseᶠ) λ pa₁ →
  mp (trust (notᶠ let₁)) λ pa₂ →
  -- instead of decl_atom
  let v₁ = var 1 in
  let a₁ = atom v₁ let₁ refl in
  mpᶜ (assum a₁ λ l₃ → clausi-f (contra l₃ pa₂)) λ pb₁ →
  mpᶜ (assum-¬ a₁ λ l₂ → clausi-f (contra pa₁ l₂)) λ pb₄ →
  mp⁺ (resolve-r⁺ pb₄ pb₁ v₁) id

prop₁ : (x : Bool) → T x ⇔ T x
prop₁ x = final (iffᶠ (appᵇ x) (appᵇ x)) (smt₁ x (holds trueᶠ refl))

bool₁ : (x : Bool) → T (x ≡ᵇ x)
bool₁ x = final (boolˣ (iffᶠ (appᵇ x) (appᵇ x))) (smt₁ x (holds trueᶠ refl))

equ₁ : (x : Bool) → x ≡ x
equ₁ x = final (equˣ (appᵇ x) (appᵇ x)) (smt₁ x (holds trueᶠ refl))
