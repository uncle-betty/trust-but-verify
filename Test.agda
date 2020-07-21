open import SAT using (var ; pos ; neg ; Holdsᶜ ; expand ; resolve-r ; resolve-r⁺ ; resolve-q ; resolve-q⁺ ; simpl-mp ; from⁺ ; fromᶜ)

module Test where

open import Data.List using ([] ; _∷_)
open import Function using (id)

sat₁ : Holdsᶜ (pos (var 0) ∷ []) → Holdsᶜ (neg (var 1) ∷ []) →
  Holdsᶜ (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ []

sat₁ a b r =
  let a⁺ = expand a in
  let b⁺ = expand b in
  let r⁺ = expand r in
  let x₁ = resolve-r a⁺ r⁺ (var 0) in
  let x₂ = resolve-q b⁺ x₁ (var 1) in
  simpl-mp x₂ id

instance
  _ = from⁺
  _ = fromᶜ

sat₂ : Holdsᶜ (pos (var 0) ∷ []) → Holdsᶜ (neg (var 1) ∷ []) →
  Holdsᶜ (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ []

sat₂ a b r =
  let x₁ = resolve-r⁺ a r  (var 0) in
  let x₂ = resolve-q⁺ b x₁ (var 1) in
  simpl-mp x₂ id
