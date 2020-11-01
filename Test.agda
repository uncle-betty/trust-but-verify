module Test where

open import Data.Bool using (Bool ; true ; false ; T)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Function using (id ; _$_ ; _∘_)
open import Function.Equivalence using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to reflₚ)

open import SAT
open import SMT
open import Base
open import Transliterate

instance
  _ = from⁺
  _ = fromᶜ

module SAT₁ where
  proof : Holdsᶜ ε (pos (var 0) ∷ []) → Holdsᶜ ε (neg (var 1) ∷ []) →
    Holdsᶜ ε (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ ε []

  proof a b r =
    let a⁺ = expand ε a in
    let b⁺ = expand ε b in
    let r⁺ = expand ε r in
    let x₁ = resolve-r ε a⁺ r⁺ (var 0) in
    let x₂ = resolve-q ε b⁺ x₁ (var 1) in
    mp⁺ ε x₂ id

module SAT₂ where
  proof : Holdsᶜ ε (pos (var 0) ∷ []) → Holdsᶜ ε (neg (var 1) ∷ []) →
    Holdsᶜ ε (neg (var 0) ∷ pos (var 1) ∷ []) → Holdsᶜ ε []

  proof a b r =
    let x₁ = resolve-r⁺ ε a r  (var 0) in
    let x₂ = resolve-q⁺ ε b x₁ (var 1) in
    mp⁺ ε x₂ id

module SMT₁ where
  proof =
    λ (x : Bool) →
    λ (as₁ : Holds trueᶠ) →
    λ (as₂ : Holds (notᶠ (iffᶠ (appᵇ x) (appᵇ x)))) →
    bind-let falseᶠ λ {
      let₁ reflₚ →
        mp (trust falseᶠ) λ pa₁ →
        mp (trust (notᶠ let₁)) λ pa₂ →
        bind-atom 1 let₁ ε λ {
          v₁ reflₚ env reflₚ a₁ →
            mpᶜ env (assum (a₁ env reflₚ) λ l₃ → clausi-f (contra l₃ pa₂)) λ pb₁ →
            mpᶜ env (assum-¬ (a₁ env reflₚ) λ l₂ → clausi-f (contra pa₁ l₂)) λ pb₄ →
            mp⁺ env (resolve-r⁺ env pb₄ pb₁ v₁) id
          }
      }

  proof-prop : (x : Bool) → T x ⇔ T x
  proof-prop x = final (iffᶠ (appᵇ x) (appᵇ x)) (proof x (holds trueᶠ reflₚ))

module SMT₂ where
  -- the LFSC proof output by CVC4; comments supported, but removed for brevity
  input : String
  input = "
    (check
    (% x (term Bool)
    (% A1 (th_holds true)
    (% A0 (th_holds (not (iff (p_app x) (p_app x) )))
    (: (holds cln)
    (@ let1 false
    (th_let_pf _ (trust_f false) (\\ .PA248
    (th_let_pf _ (trust_f (not let1)) (\\ .PA267
    (decl_atom let1 (\\ .v1 (\\ .a1
    (satlem _ _ (ast _ _ _ .a1 (\\ .l3 (clausify_false (contra _ .l3 .PA267)))) (\\ .pb1
    (satlem _ _ (asf _ _ _ .a1 (\\ .l2 (clausify_false (contra _ .PA248 .l2)))) (\\ .pb4
    (satlem_simplify _ _ _ (R _ _ .pb4 .pb1 .v1) (\\ empty empty)))))))))))))))))))"

  -- convert the LFSC proof into a type and a term of this type.
  typeTerm = convertProof input

  -- unquote the type
  proof : proofType typeTerm
  -- unquote the term
  proof = proofTerm typeTerm

  -- now we can do the same things we did in SMT₁
  proof-prop : (x : Bool) → T x ⇔ T x
  proof-prop x = final (iffᶠ (appᵇ x) (appᵇ x)) (proof x (holds trueᶠ reflₚ))
