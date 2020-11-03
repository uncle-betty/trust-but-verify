module Test where

open import Data.Bool using (Bool ; true ; false ; T)
open import Data.Bool.Properties using () renaming (≡-decSetoid to bool-decSetoid)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Function using (id ; _$_ ; _∘_)
open import Function.Equivalence using (_⇔_)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to reflₚ)

open import SAT
open import SMT
open import Base
open import Transliterate

instance
  i₁ = from⁺
  i₂ = fromᶜ
  i₃ = bool-decSetoid
  i₄ = bool-wrapper
  i₅ : {{dsdᵗ : DecSetoid 0ℓ 0ℓ}} → DecSetoid 0ℓ 0ℓ
  i₅ {{dsdᵗ}} = build-dsd bool-decSetoid dsdᵗ bool-wrapper

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

module SMT₄ where
  -- this one's even longer and uses the base theory - functions, reflexivity, congruence, etc.
  input : String
  input = "
    (check
    (% y (term Bool)
    (% x (term Bool)
    (% v (term Bool)
    (% w (term Bool)
    (% BOOLEAN_TERM_VARIABLE_287 (term Bool)
    (% BOOLEAN_TERM_VARIABLE_289 (term Bool)
    (% f (term (arrow Bool (arrow Bool Bool)))
    (% BOOLEAN_TERM_VARIABLE_282 (term Bool)
    (% BOOLEAN_TERM_VARIABLE_284 (term Bool)
    (% A1 (th_holds true)
    (% A0 (th_holds (not (impl (and (iff (p_app x) (p_app y) ) (iff (p_app v) (p_app w) )) (iff (p_app (apply _ _ (apply _ _ f w)y)) (p_app (apply _ _ (apply _ _ f v)x))))))
    (: (holds cln)
    (@ let1 v
    (@ let2 w
    (@ let3 x
    (@ let4 y
    (@ let5 BOOLEAN_TERM_VARIABLE_282
    (@ let6 BOOLEAN_TERM_VARIABLE_284
    (@ let7 (p_app (apply _ _ (apply _ _ f let5)let6))
    (@ let8 BOOLEAN_TERM_VARIABLE_287
    (@ let9 BOOLEAN_TERM_VARIABLE_289
    (@ let10 (p_app (apply _ _ (apply _ _ f let8)let9))
    (th_let_pf _ (trust_f (not (impl (and (iff (p_app let3) (p_app let4) ) (iff (p_app let1) (p_app let2) )) (iff let7 let10)))) (\\ .PA294
    (th_let_pf _ (trust_f (and (iff (p_app let8) (p_app let1) ) (and (iff (p_app let9) (p_app let3) ) (and (iff (p_app let5) (p_app let2) ) (iff (p_app let6) (p_app let4) ) )))) (\\ .PA296
    (decl_atom (p_app let1) (\\ .v4 (\\ .a4
    (decl_atom (p_app let2) (\\ .v5 (\\ .a5
    (decl_atom (p_app let3) (\\ .v2 (\\ .a2
    (decl_atom (p_app let4) (\\ .v3 (\\ .a3
    (decl_atom (p_app let5) (\\ .v10 (\\ .a10
    (decl_atom (p_app let6) (\\ .v11 (\\ .a11
    (decl_atom let7 (\\ .v6 (\\ .a6
    (decl_atom (p_app let8) (\\ .v8 (\\ .a8
    (decl_atom (p_app let9) (\\ .v9 (\\ .a9
    (decl_atom let10 (\\ .v7 (\\ .a7
    (satlem _ _ (asf _ _ _ .a9 (\\ .l18 (ast _ _ _ .a2 (\\ .l5 (clausify_false (contra _ (or_elim_1 _ _ .l18 (iff_elim_2 _ _ (and_elim_1 _ _ (and_elim_2 _ _ .PA296)))) (not_not_intro _ .l5))))))) (\\ .pb13
    (satlem _ _ (ast _ _ _ .a3 (\\ .l7 (asf _ _ _ .a2 (\\ .l4 (clausify_false (contra _ (or_elim_1 _ _ .l4 (iff_elim_2 _ _ (and_elim_1 _ _ (and_elim_1 _ _ (not_impl_elim _ _ .PA294))))) (not_not_intro _ .l7))))))) (\\ .pb5
    (satlem _ _ (ast _ _ _ .a9 (\\ .l19 (asf _ _ _ .a2 (\\ .l4 (clausify_false (contra _ (or_elim_1 _ _ (not_not_intro _ .l19) (iff_elim_1 _ _ (and_elim_1 _ _ (and_elim_2 _ _ .PA296)))) .l4)))))) (\\ .pb12
    (satlem _ _ (ast _ _ _ .a11 (\\ .l23 (asf _ _ _ .a3 (\\ .l6 (clausify_false (contra _ (or_elim_1 _ _ (not_not_intro _ .l23) (iff_elim_1 _ _ (and_elim_2 _ _ (and_elim_2 _ _ (and_elim_2 _ _ .PA296))))) .l6)))))) (\\ .pb16
    (satlem _ _ (ast _ _ _ .a5 (\\ .l11 (asf _ _ _ .a4 (\\ .l8 (clausify_false (contra _ (or_elim_1 _ _ .l8 (iff_elim_2 _ _ (and_elim_2 _ _ (and_elim_1 _ _ (not_impl_elim _ _ .PA294))))) (not_not_intro _ .l11))))))) (\\ .pb7
    (satlem _ _ (ast _ _ _ .a8 (\\ .l17 (asf _ _ _ .a4 (\\ .l8 (clausify_false (contra _ (or_elim_1 _ _ (not_not_intro _ .l17) (iff_elim_1 _ _ (and_elim_1 _ _ .PA296))) .l8)))))) (\\ .pb10
    (satlem _ _ (ast _ _ _ .a10 (\\ .l21 (asf _ _ _ .a5 (\\ .l10 (clausify_false (contra _ (or_elim_1 _ _ (not_not_intro _ .l21) (iff_elim_1 _ _ (and_elim_1 _ _ (and_elim_2 _ _ (and_elim_2 _ _ .PA296))))) .l10)))))) (\\ .pb14
    (satlem _ _ (asf _ _ _ .a8 (\\ .l16 (ast _ _ _ .a4 (\\ .l9 (clausify_false (contra _ (or_elim_1 _ _ .l16 (iff_elim_2 _ _ (and_elim_1 _ _ .PA296))) (not_not_intro _ .l9))))))) (\\ .pb11
    (satlem _ _ (asf _ _ _ .a10 (\\ .l20 (ast _ _ _ .a5 (\\ .l11 (clausify_false (contra _ (or_elim_1 _ _ .l20 (iff_elim_2 _ _ (and_elim_1 _ _ (and_elim_2 _ _ (and_elim_2 _ _ .PA296))))) (not_not_intro _ .l11))))))) (\\ .pb15
    (satlem _ _ (ast _ _ _ .a7 (\\ .l15 (ast _ _ _ .a6 (\\ .l13 (clausify_false (contra _ (or_elim_1 _ _ (not_not_intro _ .l13) (iff_elim_1 _ _ (not_iff_elim _ _ (and_elim_2 _ _ (not_impl_elim _ _ .PA294))))) (not_not_intro _ .l15))))))) (\\ .pb8
    (satlem _ _ (asf _ _ _ .a5 (\\ .l10 (ast _ _ _ .a4 (\\ .l9 (clausify_false (contra _ (or_elim_1 _ _ (not_not_intro _ .l9) (iff_elim_1 _ _ (and_elim_2 _ _ (and_elim_1 _ _ (not_impl_elim _ _ .PA294))))) .l10)))))) (\\ .pb6
    (satlem _ _ (asf _ _ _ .a11 (\\ .l22 (ast _ _ _ .a3 (\\ .l7 (clausify_false (contra _ (or_elim_1 _ _ .l22 (iff_elim_2 _ _ (and_elim_2 _ _ (and_elim_2 _ _ (and_elim_2 _ _ .PA296))))) (not_not_intro _ .l7))))))) (\\ .pb17
    (satlem _ _ (asf _ _ _ .a3 (\\ .l6 (ast _ _ _ .a2 (\\ .l5 (clausify_false (contra _ (or_elim_1 _ _ (not_not_intro _ .l5) (iff_elim_1 _ _ (and_elim_1 _ _ (and_elim_1 _ _ (not_impl_elim _ _ .PA294))))) .l6)))))) (\\ .pb4
    (satlem _ _ (asf _ _ _ .a7 (\\ .l14 (asf _ _ _ .a6 (\\ .l12 (clausify_false (contra _ (not_not_elim _ (or_elim_1 _ _ .l12 (iff_elim_2 _ _ (not_iff_elim _ _ (and_elim_2 _ _ (not_impl_elim _ _ .PA294)))))) .l14)))))) (\\ .pb9
    (satlem _ _ (ast _ _ _ .a7 (\\ .l15 (asf _ _ _ .a6 (\\ .l12 (asf _ _ _ .a10 (\\ .l20 (asf _ _ _ .a8 (\\ .l16 (ast _ _ _ .a11 (\\ .l23 (ast _ _ _ .a9 (\\ .l19
    (clausify_false (contra _ (trans _ _ _ _ (symm _ _ _ (trans _ _ _ _ (symm _ _ _ (cong _ _ _ _ _ _ (cong _ _ _ _ _ _ (refl _ f) (symm _ _ _ (trans _ _ _ _ (pred_eq_f _ .l20) (symm _ _ _ (pred_eq_f _ .l16))))) (symm _ _ _ (trans _ _ _ _ (pred_eq_t _ .l23) (symm _ _ _ (pred_eq_t _ .l19)))))) (pred_eq_t _ .l15))) (pred_eq_f _ .l12)) t_t_neq_f))
    ))))))))))))( \\ .lemc26
    (satlem _ _ (asf _ _ _ .a11 (\\ .l22 (ast _ _ _ .a7 (\\ .l15 (asf _ _ _ .a10 (\\ .l20 (asf _ _ _ .a8 (\\ .l16 (asf _ _ _ .a6 (\\ .l12 (asf _ _ _ .a9 (\\ .l18
    (clausify_false (contra _ (trans _ _ _ _ (symm _ _ _ (trans _ _ _ _ (symm _ _ _ (cong _ _ _ _ _ _ (cong _ _ _ _ _ _ (refl _ f) (symm _ _ _ (trans _ _ _ _ (pred_eq_f _ .l20) (symm _ _ _ (pred_eq_f _ .l16))))) (symm _ _ _ (trans _ _ _ _ (pred_eq_f _ .l22) (symm _ _ _ (pred_eq_f _ .l18)))))) (pred_eq_t _ .l15))) (pred_eq_f _ .l12)) t_t_neq_f))
    ))))))))))))( \\ .lemc18
    (satlem _ _ (ast _ _ _ .a7 (\\ .l15 (asf _ _ _ .a6 (\\ .l12 (ast _ _ _ .a10 (\\ .l21 (ast _ _ _ .a8 (\\ .l17 (ast _ _ _ .a11 (\\ .l23 (ast _ _ _ .a9 (\\ .l19
    (clausify_false (contra _ (trans _ _ _ _ (symm _ _ _ (trans _ _ _ _ (symm _ _ _ (cong _ _ _ _ _ _ (cong _ _ _ _ _ _ (refl _ f) (symm _ _ _ (trans _ _ _ _ (pred_eq_t _ .l21) (symm _ _ _ (pred_eq_t _ .l17))))) (symm _ _ _ (trans _ _ _ _ (pred_eq_t _ .l23) (symm _ _ _ (pred_eq_t _ .l19)))))) (pred_eq_t _ .l15))) (pred_eq_f _ .l12)) t_t_neq_f))
    ))))))))))))( \\ .lemc33
    (satlem _ _ (asf _ _ _ .a7 (\\ .l14 (ast _ _ _ .a6 (\\ .l13 (ast _ _ _ .a10 (\\ .l21 (ast _ _ _ .a8 (\\ .l17 (ast _ _ _ .a11 (\\ .l23 (ast _ _ _ .a9 (\\ .l19
    (clausify_false (contra _ (trans _ _ _ _ (symm _ _ _ (trans _ _ _ _ (cong _ _ _ _ _ _ (cong _ _ _ _ _ _ (refl _ f) (symm _ _ _ (trans _ _ _ _ (pred_eq_t _ .l21) (symm _ _ _ (pred_eq_t _ .l17))))) (symm _ _ _ (trans _ _ _ _ (pred_eq_t _ .l23) (symm _ _ _ (pred_eq_t _ .l19))))) (pred_eq_t _ .l13))) (pred_eq_f _ .l14)) t_t_neq_f))
    ))))))))))))( \\ .lemc38
    (satlem _ _ (asf _ _ _ .a7 (\\ .l14 (ast _ _ _ .a6 (\\ .l13 (asf _ _ _ .a10 (\\ .l20 (asf _ _ _ .a8 (\\ .l16 (ast _ _ _ .a11 (\\ .l23 (ast _ _ _ .a9 (\\ .l19
    (clausify_false (contra _ (trans _ _ _ _ (symm _ _ _ (trans _ _ _ _ (cong _ _ _ _ _ _ (cong _ _ _ _ _ _ (refl _ f) (symm _ _ _ (trans _ _ _ _ (pred_eq_f _ .l20) (symm _ _ _ (pred_eq_f _ .l16))))) (symm _ _ _ (trans _ _ _ _ (pred_eq_t _ .l23) (symm _ _ _ (pred_eq_t _ .l19))))) (pred_eq_t _ .l13))) (pred_eq_f _ .l14)) t_t_neq_f))
    ))))))))))))( \\ .lemc31
    (satlem _ _ (asf _ _ _ .a7 (\\ .l14 (ast _ _ _ .a6 (\\ .l13 (ast _ _ _ .a10 (\\ .l21 (ast _ _ _ .a8 (\\ .l17 (asf _ _ _ .a11 (\\ .l22 (asf _ _ _ .a9 (\\ .l18
    (clausify_false (contra _ (trans _ _ _ _ (symm _ _ _ (trans _ _ _ _ (cong _ _ _ _ _ _ (cong _ _ _ _ _ _ (refl _ f) (symm _ _ _ (trans _ _ _ _ (pred_eq_t _ .l21) (symm _ _ _ (pred_eq_t _ .l17))))) (symm _ _ _ (trans _ _ _ _ (pred_eq_f _ .l22) (symm _ _ _ (pred_eq_f _ .l18))))) (pred_eq_t _ .l13))) (pred_eq_f _ .l14)) t_t_neq_f))
    ))))))))))))( \\ .lemc24
    (satlem _ _ (ast _ _ _ .a7 (\\ .l15 (asf _ _ _ .a6 (\\ .l12 (ast _ _ _ .a10 (\\ .l21 (ast _ _ _ .a8 (\\ .l17 (asf _ _ _ .a11 (\\ .l22 (asf _ _ _ .a9 (\\ .l18
    (clausify_false (contra _ (trans _ _ _ _ (symm _ _ _ (trans _ _ _ _ (symm _ _ _ (cong _ _ _ _ _ _ (cong _ _ _ _ _ _ (refl _ f) (symm _ _ _ (trans _ _ _ _ (pred_eq_t _ .l21) (symm _ _ _ (pred_eq_t _ .l17))))) (symm _ _ _ (trans _ _ _ _ (pred_eq_f _ .l22) (symm _ _ _ (pred_eq_f _ .l18)))))) (pred_eq_t _ .l15))) (pred_eq_f _ .l12)) t_t_neq_f))
    ))))))))))))( \\ .lemc22
    (satlem _ _ (asf _ _ _ .a11 (\\ .l22 (asf _ _ _ .a7 (\\ .l14 (asf _ _ _ .a10 (\\ .l20 (asf _ _ _ .a8 (\\ .l16 (ast _ _ _ .a6 (\\ .l13 (asf _ _ _ .a9 (\\ .l18
    (clausify_false (contra _ (trans _ _ _ _ (symm _ _ _ (trans _ _ _ _ (cong _ _ _ _ _ _ (cong _ _ _ _ _ _ (refl _ f) (symm _ _ _ (trans _ _ _ _ (pred_eq_f _ .l20) (symm _ _ _ (pred_eq_f _ .l16))))) (symm _ _ _ (trans _ _ _ _ (pred_eq_f _ .l22) (symm _ _ _ (pred_eq_f _ .l18))))) (pred_eq_t _ .l13))) (pred_eq_f _ .l14)) t_t_neq_f))
    ))))))))))))( \\ .lemc20
    (satlem_simplify _ _ _ (Q _ _ .lemc18 .pb9 .v7) (\\ .cl19
    (satlem_simplify _ _ _ (R _ _ (R _ _ (R _ _ (Q _ _ (R _ _ .lemc20 .pb8 .v7) .cl19 .v6) .pb14 .v10) .pb10 .v8) .pb7 .v5) (\\ .cl21
    (satlem_simplify _ _ _ (Q _ _ (Q _ _ (Q _ _ (Q _ _ (Q _ _ .lemc22 .pb9 .v7) .pb15 .v10) .pb6 .v5) .pb11 .v8) .cl21 .v4) (\\ .cl23
    (satlem_simplify _ _ _ (R _ _ (R _ _ (R _ _ (Q _ _ (Q _ _ (Q _ _ (Q _ _ (Q _ _ (R _ _ .lemc24 .pb8 .v7) .cl23 .v6) .pb15 .v10) .pb11 .v8) .pb6 .v5) .cl21 .v4) .pb16 .v11) .pb12 .v9) .pb5 .v3) (\\ .cl25
    (satlem_simplify _ _ _ (Q _ _ .pb4 .cl25 .v2) (\\ .cl27
    (satlem_simplify _ _ _ (Q _ _ .pb17 .cl27 .v3) (\\ .cl28
    (satlem_simplify _ _ _ (Q _ _ .pb13 .cl25 .v2) (\\ .cl29
    (satlem_simplify _ _ _ (Q _ _ (Q _ _ (Q _ _ .lemc26 .cl28 .v11) .cl29 .v9) .pb9 .v7) (\\ .cl30
    (satlem_simplify _ _ _ (R _ _ (R _ _ (R _ _ (Q _ _ (R _ _ (Q _ _ (Q _ _ .lemc31 .cl28 .v11) .cl29 .v9) .pb8 .v7) .cl30 .v6) .pb14 .v10) .pb10 .v8) .pb7 .v5) (\\ .cl32
    (satlem_simplify _ _ _ (Q _ _ .pb6 .cl32 .v4) (\\ .cl34
    (satlem_simplify _ _ _ (Q _ _ .pb15 .cl34 .v5) (\\ .cl35
    (satlem_simplify _ _ _ (Q _ _ .pb11 .cl32 .v4) (\\ .cl36
    (satlem_simplify _ _ _ (Q _ _ (Q _ _ (Q _ _ (Q _ _ (Q _ _ .lemc33 .cl35 .v10) .cl36 .v8) .cl28 .v11) .cl29 .v9) .pb9 .v7) (\\ .cl37
    (satlem_simplify _ _ _ (Q _ _ .pb8 .cl37 .v6) (\\ .cl39
    (satlem_simplify _ _ _ (Q _ _ (Q _ _ (Q _ _ (Q _ _ (Q _ _ (R _ _ .lemc38 .cl39 .v7) .cl37 .v6) .cl35 .v10) .cl36 .v8) .cl28 .v11) .cl29 .v9) (\\ empty empty)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"

  typeTerm = convertProof input

  proof : proofType typeTerm
  proof = proofTerm typeTerm

  proof-prop : (y x v w : Bool) → (f : Bool → Bool → Bool) →
    (T x ⇔ T y) × (T v ⇔ T w) → T (f w y) ⇔ T (f v x)
  proof-prop y x v w f = invert $ proof y x v w false false f false false (holds trueᶠ reflₚ)
