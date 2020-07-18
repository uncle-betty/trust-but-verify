module Test where

open import CVC4 using (Var ; var ; Lit ; pos ; neg ; Oper ; join ; skip ; Clause ; Clause⁺ ; compl ; simpl ; lit-<-STO)

open import Data.Empty using (⊥)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Tree.AVL.Sets lit-<-STO using (⟨Set⟩ ; empty)
open import Function using (id ; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; subst)
open import Relation.Nullary using (¬_)

postulate
  holds : Clause → Set
  holds-[] : holds [] ≡ ⊥
  holds⁺ : Clause⁺ → ⟨Set⟩ → Set
  holds-holds⁺ : ∀ {c} → holds c → holds⁺ (compl c) empty

  resolve⁺-r : ∀ {c₁ c₂} → holds⁺ c₁ empty → holds⁺ c₂ empty → (v : Var) →
    holds⁺ (inj₂ (join (inj₂ (skip (pos v)) ∷ c₁)) ∷ inj₂ (skip (neg v)) ∷ c₂) empty

  resolve⁺-q : ∀ {c₁ c₂} → holds⁺ c₁ empty → holds⁺ c₂ empty → (v : Var) →
    holds⁺ (inj₂ (join (inj₂ (skip (neg v)) ∷ c₁)) ∷ inj₂ (skip (pos v)) ∷ c₂) empty

  mp⁺ : ∀ {c₁ c₂} → holds⁺ c₁ empty → (holds (simpl c₁ empty) → holds c₂) → holds c₂

sat₁ : holds (pos (var 0) ∷ []) → holds (neg (var 1) ∷ []) → ¬ holds (neg (var 0) ∷ pos (var 1) ∷ [])
sat₁ cᵃ cᵇ cʳ = subst id holds-[] $
  let a⁺ = holds-holds⁺ cᵃ in
  let b⁺ = holds-holds⁺ cᵇ in
  let r⁺ = holds-holds⁺ cʳ in
  let x₁ = resolve⁺-r a⁺ r⁺ (var 0) in
  let x₂ = resolve⁺-q b⁺ x₁ (var 1) in mp⁺ x₂ id
