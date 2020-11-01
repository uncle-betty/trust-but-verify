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
  proof : (x : Bool) → Holds trueᶠ → Holds (notᶠ (iffᶠ (appᵇ x) (appᵇ x))) → Holdsᶜ ε []
  proof =
    λ (x : Bool) →
    λ (as₁ : Holds trueᶠ) →
    λ (as₂ : Holds (notᶠ (iffᶠ (appᵇ x) (appᵇ x)))) →
    holdsᶜ-[]-ε $
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
  proof-prop x = invert $ proof x (holds trueᶠ reflₚ)

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
  proof-prop x = invert $ proof x (holds trueᶠ reflₚ)

module SMT₃ where
  -- this one's a little longer and reasons about variables (see let1, let2, let3)
  input : String
  input = "
    (check
    (% z (term Bool)
    (% x (term Bool)
    (% y (term Bool)
    (% A1 (th_holds true)
    (% A0 (th_holds (not (impl (and (and (p_app x) (p_app y)) (p_app z)) (and (p_app z) (p_app x)))))
    (: (holds cln)
    (@ let1 x
    (@ let2 y
    (@ let3 z
    (th_let_pf _ (trust_f (not (impl (and (p_app let3) (and (p_app let1) (p_app let2) )) (and (p_app let3) (p_app let1))))) (\\ .PA278
    (decl_atom (p_app let1) (\\ .v3 (\\ .a3
    (decl_atom (p_app let2) (\\ .v4 (\\ .a4
    (decl_atom (p_app let3) (\\ .v2 (\\ .a2
    (satlem _ _ (asf _ _ _ .a2 (\\ .l4 (clausify_false (contra _ (and_elim_1 _ _ (and_elim_1 _ _ (not_impl_elim _ _ .PA278))) .l4)))) (\\ .pb4
    (satlem _ _ (ast _ _ _ .a3 (\\ .l7 (ast _ _ _ .a2 (\\ .l5 (clausify_false (contra _ .l7 (or_elim_1 _ _ (not_not_intro _ .l5) (not_and_elim _ _ (and_elim_2 _ _ (not_impl_elim _ _ .PA278)))))))))) (\\ .pb7
    (satlem _ _ (asf _ _ _ .a3 (\\ .l6 (clausify_false (contra _ (and_elim_1 _ _ (and_elim_2 _ _ (and_elim_1 _ _ (not_impl_elim _ _ .PA278)))) .l6)))) (\\ .pb5
    (satlem_simplify _ _ _ (Q _ _ (Q _ _ .pb7 .pb5 .v3) .pb4 .v2) (\\ empty empty)))))))))))))))))))))))))))))"

  typeTerm = convertProof input

  proof : proofType typeTerm
  proof = proofTerm typeTerm

  proof-prop : (z x y : Bool) → (T x × T y) × T z → T z × T x
  proof-prop z x y = invert $ proof z x y (holds trueᶠ reflₚ)
