open import SAT using (Var ; var ; Lit ; pos ; neg ; Oper ; join ; skip ; Clause ; Clause⁺ ; lit-<-STO ; Holdsᶜ ; holdsᶜ-holds⁺ ; resolve⁺-r ; resolve⁺-q ; mp⁺)

module Test where

open import Data.Empty using (⊥)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Tree.AVL.Sets lit-<-STO using (⟨Set⟩ ; empty)
open import Function using (id ; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; subst)
open import Relation.Nullary using (¬_)

sat₁ : Holdsᶜ (pos (var 0) ∷ []) → Holdsᶜ (neg (var 1) ∷ []) →
  Holdsᶜ (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ []

sat₁ hᵃ hᵇ hʳ =
  let a⁺ = holdsᶜ-holds⁺ hᵃ in
  let b⁺ = holdsᶜ-holds⁺ hᵇ in
  let r⁺ = holdsᶜ-holds⁺ hʳ in
  let x₁ = resolve⁺-r a⁺ r⁺ (var 0) in
  let x₂ = resolve⁺-q b⁺ x₁ (var 1) in
  mp⁺ x₂ id
