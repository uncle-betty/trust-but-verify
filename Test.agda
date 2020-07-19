open import CVC4 using (Var ; var ; Lit ; pos ; neg ; Oper ; join ; skip ; Clause ; Clause⁺ ; compl ; simpl ; lit-<-STO ; Rules)

-- XXX - Don't use the "rules" record from CVC4 directly. Knowing the definition of "⟨holds⟩"
-- makes the type checker partially evaluate clauses, which leads to unification failures for
-- "neg" literals.
module Test (rules : Rules) where

open import Data.Empty using (⊥)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Tree.AVL.Sets lit-<-STO using (⟨Set⟩ ; empty)
open import Function using (id ; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; subst)
open import Relation.Nullary using (¬_)

open Rules rules
  renaming (
    ⟨holds-holds⁺⟩ to r₁ ;
    ⟨resolve⁺-r⟩   to r₂ ;
    ⟨resolve⁺-q⟩   to r₃ ;
    ⟨mp⁺⟩          to r₄
  )

⟨holds-holds⁺⟩ = λ {c}       → r₁ c
⟨resolve⁺-r⟩   = λ {c₁} {c₂} → r₂ c₁ c₂
⟨resolve⁺-q⟩   = λ {c₁} {c₂} → r₃ c₁ c₂
⟨mp⁺⟩          = λ {c₁} {c₂} → r₄ c₁ c₂

sat₁ : ⟨holds⟩ (pos (var 0) ∷ []) → ⟨holds⟩ (neg (var 1) ∷ []) →
  ¬ ⟨holds⟩ (neg (var 0) ∷ pos (var 1) ∷ [])

sat₁ hᵃ hᵇ hʳ = subst id ⟨holds-[]⟩ $
  let a⁺ = ⟨holds-holds⁺⟩ hᵃ in
  let b⁺ = ⟨holds-holds⁺⟩ hᵇ in
  let r⁺ = ⟨holds-holds⁺⟩ hʳ in
  let x₁ = ⟨resolve⁺-r⟩ a⁺ r⁺ (var 0) in
  let x₂ = ⟨resolve⁺-q⟩ b⁺ x₁ (var 1) in ⟨mp⁺⟩ x₂ id
