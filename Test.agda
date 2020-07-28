module Test where

open import Data.List using ([] ; _∷_)
open import Function using (id ; _$_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Env using (var ; ε ; assignᵛ)
open import SMT as S using (trueᶠ ; falseᶠ ; evalᶠ)

env =
  assignᵛ (var 0) (evalᶠ falseᶠ) $
  assignᵛ (var 1) (evalᶠ trueᶠ) $
  ε

open import SAT env
  using (
    pos ; neg ; Holdsᶜ ; expand ; from⁺ ; fromᶜ ;
    resolve-r ; resolve-r⁺ ; resolve-q ; resolve-q⁺ ; simpl-mp
  )

open S.Rules env using (atom ; decl-atom)

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

a₀ = atom (var 0) falseᶠ refl
a₁ = atom (var 1) trueᶠ refl
