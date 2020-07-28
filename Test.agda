module Test where

open import Data.List using ([] ; _∷_)
open import Function using (id ; _$_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Env using (var ; ε ; assignᵛ)
open import SMT as S using (trueᶠ ; falseᶠ ; notᶠ ; evalᶠ ; trustᶠ)

env =
  assignᵛ (var 1) (evalᶠ falseᶠ) $
  ε

open import SAT env
  using (
    pos ; neg ; Holdsᶜ ; expand ; from⁺ ; fromᶜ ;
    resolve-r ; resolve-r⁺ ; resolve-q ; resolve-q⁺ ; mp ; simpl-mp
  )

open S.Rules env using (Atom ; atom ; mpᶠ ; assum ; assum-¬ ; clausi-f ; contra)

-- SAT test #1

sat₁ : Holdsᶜ (pos (var 0) ∷ []) → Holdsᶜ (neg (var 1) ∷ []) →
  Holdsᶜ (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ []

sat₁ a b r =
  let a⁺ = expand a in
  let b⁺ = expand b in
  let r⁺ = expand r in
  let x₁ = resolve-r a⁺ r⁺ (var 0) in
  let x₂ = resolve-q b⁺ x₁ (var 1) in
  simpl-mp x₂ id

-- SAT test #2

instance
  _ = from⁺
  _ = fromᶜ

sat₂ : Holdsᶜ (pos (var 0) ∷ []) → Holdsᶜ (neg (var 1) ∷ []) →
  Holdsᶜ (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ []

sat₂ a b r =
  let x₁ = resolve-r⁺ a r  (var 0) in
  let x₂ = resolve-q⁺ b x₁ (var 1) in
  simpl-mp x₂ id

-- SMT test #1

smt₁ : Holdsᶜ []
smt₁ =
  let let₁ = falseᶠ in
  let v₁ = var 1 in
  let a₁ = atom v₁ let₁ refl in
  mpᶠ (trustᶠ falseᶠ) λ pa₁ →
  mpᶠ (trustᶠ (notᶠ let₁)) λ pa₂ →
  mp (assum a₁ λ l₃ → clausi-f (contra l₃ pa₂)) λ pb₁ →
  mp (assum-¬ a₁ λ l₂ → clausi-f (contra pa₁ l₂)) λ pb₄ →
  simpl-mp (resolve-r⁺ pb₄ pb₁ v₁) id
