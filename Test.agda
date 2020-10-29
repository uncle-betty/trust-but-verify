module Test where

open import Data.Bool using (Bool ; true ; false ; T)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Function using (id ; _$_)
open import Function.Equivalence using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to reflₚ)

open import SAT
open import SMT
open import Base
open import Convert

instance
  _ = from⁺
  _ = fromᶜ

module SAT₁ where
  proof : Holdsᶜ (pos (var 0 false) ∷ []) → Holdsᶜ (neg (var 1 true) ∷ []) →
    Holdsᶜ (neg (var 0 false) ∷ pos (var 1 true) ∷ []) → Holdsᶜ []

  proof a b r =
    let a⁺ = expand a in
    let b⁺ = expand b in
    let r⁺ = expand r in
    let x₁ = resolve-r a⁺ r⁺ (var 0 false) in
    let x₂ = resolve-q b⁺ x₁ (var 1 true) in
    mp⁺ x₂ id

module SAT₂ where
  proof : Holdsᶜ (pos (var 0 false) ∷ []) → Holdsᶜ (neg (var 1 true) ∷ []) →
    Holdsᶜ (neg (var 0 false) ∷ pos (var 1 true) ∷ []) → Holdsᶜ []

  proof a b r =
    let x₁ = resolve-r⁺ a r  (var 0 false) in
    let x₂ = resolve-q⁺ b x₁ (var 1 true) in
    mp⁺ x₂ id

module SMT₁ where
  proof =
    λ (x : Bool) →
    λ (as₁ : Holds trueᶠ) →
    λ (as₂ : Holds (notᶠ (iffᶠ (appᵇ x) (appᵇ x)))) →
    let let₁ = falseᶠ in
    mp (trust falseᶠ) λ pa₁ →
    mp (trust (notᶠ let₁)) λ pa₂ →
    -- instead of decl_atom
    let tbv-tmp = let₁ in
    let v₁ = var 1 (eval tbv-tmp) in
    let a₁ = atom v₁ tbv-tmp reflₚ in
    mpᶜ (assum a₁ λ l₃ → clausi-f (contra l₃ pa₂)) λ pb₁ →
    mpᶜ (assum-¬ a₁ λ l₂ → clausi-f (contra pa₁ l₂)) λ pb₄ →
    mp⁺ (resolve-r⁺ pb₄ pb₁ v₁) id

  proof-prop : (x : Bool) → T x ⇔ T x
  proof-prop x = final (iffᶠ (appᵇ x) (appᵇ x)) (proof x (holds trueᶠ reflₚ))

  proof-bool : (x : Bool) → T (x ≡ᵇ x)
  proof-bool x = final (boolˣ (iffᶠ (appᵇ x) (appᵇ x))) (proof x (holds trueᶠ reflₚ))

  proof-equ : (x : Bool) → x ≡ x
  proof-equ x = final (equˣ (appᵇ x) (appᵇ x)) (proof x (holds trueᶠ reflₚ))

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
  typeTerm = convertProof "(check (decl_atom true (\\ .foo1 (\\ .foo2 true))))" -- input

  open import Agda.Builtin.Reflection

  test₁ =
    let f = trueᶠ in
    let v = var 1 (eval f) in
    let a = atom v f reflₚ in
    trueᶠ

  data Wrap : Set where
    wrap : (v : Var) → evalᵛ v ≡

  test₂ =
    (λ (f : Formula) →
      (λ (v : Var) →
        (λ (a : Atom v f) → trueᶠ) $
          atom v f {!!}) $
      var 1 (eval f)) $
    trueᶠ

  -- unquote the type
  -- proof : proofType typeTerm
  -- unquote the term
  -- proof = proofTerm typeTerm

{-
  -- now we can do the same things we did in SMT₁
  proof-prop : (x : Bool) → T x ⇔ T x
  proof-prop x = final (iffᶠ (appᵇ x) (appᵇ x)) (proof x (holds trueᶠ reflₚ))
-}
