module SMT where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_ ; T)
open import Data.Bool.Properties using (∨-identityʳ ; not-¬)
open import Data.Empty using (⊥)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)

open import Function using (id ; _∘_ ; _$_ ; const)
open import Function.Equality using (Π)
open import Function.Equivalence using (_⇔_ ; equivalence)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; subst ; sym ; inspect ; [_])

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Env using (Var ; var ; Env ; evalᵛ)

--- SMT ---

data Formula : Bool → Set₁

formula-op₀ = {ex : Bool} → Formula ex
-- LFSC: formula_op1 (extended)
formula-op₁ = {ex : Bool} → Formula ex → Formula ex
-- LFSC: formula_op2 (extended)
formula-op₂ = {ex : Bool} → Formula ex → Formula ex → Formula ex
-- LFSC: formula_op3 (extended)
formula-op₃ = {ex : Bool} → Formula ex → Formula ex → Formula ex → Formula ex

-- LFSC: formula (extended)
data Formula where
  -- LFSC: true
  trueᶠ  : formula-op₀
  -- LFSC: false
  falseᶠ : formula-op₀

  -- LFSC: not
  notᶠ   : formula-op₁
  -- LFSC: and
  andᶠ   : formula-op₂
  -- LFSC: or
  orᶠ    : formula-op₂
  -- LFSC: impl
  implᶠ  : formula-op₂
  -- LFSC: iff
  iffᶠ   : formula-op₂

  -- LFSC: = (Bool sort)
  ≡ᵇ     : {ex : Bool} → Bool → Bool → Formula ex
  -- LFSC: p_app
  appᵇ   : {ex : Bool} → Bool → Formula ex

  -- extension - boolean subformulas
  boolᶠ  : Formula true → Formula true
  -- extension - boolean equalities
  equᶠ   : Formula true → Formula true → Formula true

infix 3 _→ᵇ_

_→ᵇ_ : Bool → Bool → Bool
true  →ᵇ b = b
false →ᵇ _ = true

infix 3 _⇔ᵇ_

_⇔ᵇ_ : Bool → Bool → Bool
true  ⇔ᵇ true  = true
false ⇔ᵇ false = true
_     ⇔ᵇ _     = false

⇔ᵇ≡t⇒≡ : ∀ b₁ b₂ → (b₁ ⇔ᵇ b₂) ≡ true → b₁ ≡ b₂
⇔ᵇ≡t⇒≡ true true refl = refl
⇔ᵇ≡t⇒≡ false false refl = refl

⇔ᵇ≡f⇒≢ : ∀ b₁ b₂ → (b₁ ⇔ᵇ b₂) ≡ false → b₁ ≢ b₂
⇔ᵇ≡f⇒≢ true false p = λ ()
⇔ᵇ≡f⇒≢ false true p = λ ()

x⇔ᵇx : ∀ b → (b ⇔ᵇ b) ≡ true
x⇔ᵇx true  = refl
x⇔ᵇx false = refl

evalᶠ : {ex : Bool} → Formula ex → Bool
evalᶠ trueᶠ = true
evalᶠ falseᶠ = false

evalᶠ (notᶠ f) = not (evalᶠ f)
evalᶠ (andᶠ f₁ f₂) = evalᶠ f₁ ∧ evalᶠ f₂
evalᶠ (orᶠ f₁ f₂) = evalᶠ f₁ ∨ evalᶠ f₂
evalᶠ (implᶠ f₁ f₂) = evalᶠ f₁ →ᵇ evalᶠ f₂
evalᶠ (iffᶠ f₁ f₂) = evalᶠ f₁ ⇔ᵇ evalᶠ f₂

evalᶠ (≡ᵇ b₁ b₂) = b₁ ⇔ᵇ b₂
evalᶠ (appᵇ b) = b

evalᶠ (boolᶠ f) = evalᶠ f
evalᶠ (equᶠ f₁ f₂) = evalᶠ f₁ ⇔ᵇ evalᶠ f₂

propᶠ : {ex : Bool} → Formula ex → Set
propᶠ trueᶠ  = ⊤
propᶠ falseᶠ = ⊥

propᶠ (notᶠ f) = ¬ propᶠ f
propᶠ (andᶠ f₁ f₂) = propᶠ f₁ × propᶠ f₂
propᶠ (orᶠ f₁ f₂) = propᶠ f₁ ⊎ propᶠ f₂
propᶠ (implᶠ f₁ f₂) = propᶠ f₁ → propᶠ f₂
propᶠ (iffᶠ f₁ f₂) = propᶠ f₁ ⇔ propᶠ f₂

propᶠ (≡ᵇ b₁ b₂) = b₁ ≡ b₂
propᶠ (appᵇ b) = T b

propᶠ (boolᶠ f) = T (evalᶠ f)
propᶠ (equᶠ f₁ f₂) = evalᶠ f₁ ≡ evalᶠ f₂

proveᵗ : ∀ {ex} → (f : Formula ex) → evalᶠ f ≡ true → propᶠ f
proveᵗ-¬ : ∀ {ex} → (f : Formula ex) → evalᶠ f ≡ false → ¬ propᶠ f

proveᵗ trueᶠ p = tt

proveᵗ (notᶠ f) p with evalᶠ f | inspect evalᶠ f
proveᵗ (notᶠ f) () | true  | _
proveᵗ (notᶠ f) _  | false | [ eq ] = proveᵗ-¬ f eq

proveᵗ (andᶠ f₁ f₂) p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ (andᶠ f₁ f₂) _  | true  | [ eq₁ ] | true  | [ eq₂ ] = proveᵗ f₁ eq₁ , proveᵗ f₂ eq₂
proveᵗ (andᶠ f₁ f₂) () | true  | _       | false | _
proveᵗ (andᶠ f₁ f₂) () | false | _       | true  | _
proveᵗ (andᶠ f₁ f₂) () | false | _       | false | _

proveᵗ (orᶠ f₁ f₂) p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ (orᶠ f₁ f₂) _  | true  | [ eq₁ ] | _     | _       = inj₁ (proveᵗ f₁ eq₁)
proveᵗ (orᶠ f₁ f₂) _  | false | _       | true  | [ eq₂ ] = inj₂ (proveᵗ f₂ eq₂)
proveᵗ (orᶠ f₁ f₂) () | false | _       | false | _

proveᵗ (implᶠ f₁ f₂) p with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ (implᶠ f₁ f₂) _  | true  | [ eq₁ ] | true  | [ eq₂ ] = const $ proveᵗ f₂ eq₂
proveᵗ (implᶠ f₁ f₂) () | true  | _       | false | _

proveᵗ (implᶠ f₁ f₂) _  | false | [ eq₁ ] | _     | _       =
  λ x → contradiction x (proveᵗ-¬ f₁ eq₁)

proveᵗ (iffᶠ f₁ f₂) p with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ (iffᶠ f₁ f₂) _  | true  | [ eq₁ ] | true  | [ eq₂ ] =
  equivalence (const $ proveᵗ f₂ eq₂) (const $ proveᵗ f₁ eq₁)

proveᵗ (iffᶠ f₁ f₂) () | true  | _       | false | _
proveᵗ (iffᶠ f₁ f₂) () | false | _       | true  | _

proveᵗ (iffᶠ f₁ f₂) _  | false | [ eq₁ ] | false | [ eq₂ ] =
  equivalence
    (λ x → contradiction x (proveᵗ-¬ f₁ eq₁))
    λ x → contradiction x (proveᵗ-¬ f₂ eq₂)

proveᵗ (≡ᵇ b₁ b₂) p = ⇔ᵇ≡t⇒≡ b₁ b₂ p
proveᵗ (appᵇ b) refl = tt

proveᵗ (boolᶠ f) p = subst T (sym p) tt
proveᵗ (equᶠ f₁ f₂) p = ⇔ᵇ≡t⇒≡ (evalᶠ f₁) (evalᶠ f₂) p

proveᵗ-¬ falseᶠ p = id

proveᵗ-¬ (notᶠ f) p with evalᶠ f | inspect evalᶠ f
proveᵗ-¬ (notᶠ f) _  | true  | [ eq ] = λ x → x (proveᵗ f eq)
proveᵗ-¬ (notᶠ f) () | false | _

proveᵗ-¬ (andᶠ f₁ f₂) p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ-¬ (andᶠ f₁ f₂) () | true  | [ eq₁ ] | true  | [ eq₂ ]

proveᵗ-¬ (andᶠ f₁ f₂) _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ { (_ , p₂) → contradiction p₂ (proveᵗ-¬ f₂ eq₂) }

proveᵗ-¬ (andᶠ f₁ f₂) _  | false | [ eq₁ ] | true  | [ eq₂ ] =
  λ { (p₁ , _) → contradiction p₁ (proveᵗ-¬ f₁ eq₁) }

proveᵗ-¬ (andᶠ f₁ f₂) _  | false | [ eq₁ ] | false | [ eq₂ ] =
  λ { (p₁ , _) → contradiction p₁ (proveᵗ-¬ f₁ eq₁) }

proveᵗ-¬ (orᶠ f₁ f₂) p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ-¬ (orᶠ f₁ f₂) () | true  | _       | _     | _
proveᵗ-¬ (orᶠ f₁ f₂) () | false | _       | true  | _

proveᵗ-¬ (orᶠ f₁ f₂) _  | false | [ eq₁ ] | false | [ eq₂ ] =
  λ {
    (inj₁ p₁) → contradiction p₁ (proveᵗ-¬ f₁ eq₁) ;
    (inj₂ p₂) → contradiction p₂ (proveᵗ-¬ f₂ eq₂)
  }

proveᵗ-¬ (implᶠ f₁ f₂) p with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ-¬ (implᶠ f₁ f₂) () | true  | _       | true  | _

proveᵗ-¬ (implᶠ f₁ f₂) _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ fn → proveᵗ-¬ f₂ eq₂ $ fn (proveᵗ f₁ eq₁)

proveᵗ-¬ (implᶠ f₁ f₂) () | false | _       | _     | _

proveᵗ-¬ (iffᶠ f₁ f₂) p with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ-¬ (iffᶠ f₁ f₂) () | true  | _       | true  | _

proveᵗ-¬ (iffᶠ f₁ f₂) _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ { (record {to = lr}) → proveᵗ-¬ f₂ eq₂ $ lr ⟨$⟩ proveᵗ f₁ eq₁ }
  where open Π

proveᵗ-¬ (iffᶠ f₁ f₂) _  | false | [ eq₁ ] | true  | [ eq₂ ] =
  λ { (record {from = rl}) → proveᵗ-¬ f₁ eq₁ $ rl ⟨$⟩ proveᵗ f₂ eq₂ }
  where open Π

proveᵗ-¬ (iffᶠ f₁ f₂) () | false | _       | false | _

proveᵗ-¬ (≡ᵇ b₁ b₂) p = ⇔ᵇ≡f⇒≢ b₁ b₂ p
proveᵗ-¬ (appᵇ b) refl = id

proveᵗ-¬ (boolᶠ f) p r = subst T p r
proveᵗ-¬ (equᶠ f₁ f₂) p = ⇔ᵇ≡f⇒≢ (evalᶠ f₁) (evalᶠ f₂) p

strip : {ex : Bool} → Formula ex → Formula false
strip trueᶠ = trueᶠ
strip falseᶠ = falseᶠ

strip (notᶠ f) = notᶠ (strip f)
strip (andᶠ f₁ f₂) = andᶠ (strip f₁) (strip f₂)
strip (orᶠ f₁ f₂) = orᶠ (strip f₁) (strip f₂)
strip (implᶠ f₁ f₂) = implᶠ (strip f₁) (strip f₂)
strip (iffᶠ f₁ f₂) = iffᶠ (strip f₁) (strip f₂)

strip (≡ᵇ b₁ b₂) = ≡ᵇ b₁ b₂
strip (appᵇ b) = appᵇ b

strip (boolᶠ f) = strip f
strip (equᶠ f₁ f₂) = iffᶠ (strip f₁) (strip f₂)

strip-sound : ∀ {ex} → (f : Formula ex) → evalᶠ (strip f) ≡ evalᶠ f

strip-sound trueᶠ = refl
strip-sound falseᶠ = refl

strip-sound (notᶠ f) rewrite strip-sound f = refl
strip-sound (andᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl
strip-sound (orᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl
strip-sound (implᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl
strip-sound (iffᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl

strip-sound (≡ᵇ b₁ b₂) = refl
strip-sound (appᵇ b) = refl

strip-sound (boolᶠ f) = strip-sound f
strip-sound (equᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl

-- LFSC: th_holds
data Holdsᶠ : Formula false → Set where
  holdsᶠ : (f : Formula false) → evalᶠ f ≡ true → Holdsᶠ f

module Rules (env : Env) where

  open import SAT env
    using (pos ; neg ; Holdsᶜ ; holdsᶜ ; holdsᶜ-[] ; evalᶜ ; not-t⇒f ; f⇒not-t)

  final : (f : Formula true) → (Holdsᶠ (notᶠ (strip f)) → Holdsᶜ []) → propᶠ f
  final f h =
    let
      f′ = strip f
      p′ = lem f′ h
      p  = subst (_≡ true) (strip-sound f) p′
    in
      proveᵗ f p
    where
      lem : (f : Formula false) → (Holdsᶠ (notᶠ f) → Holdsᶜ []) → evalᶠ f ≡ true
      lem f h with evalᶠ f | inspect evalᶠ f
      ... | true  | [ eq ] = refl
      ... | false | [ eq ] = contradiction (holdsᶠ (notᶠ f) (f⇒not-t eq)) (holdsᶜ-[] ∘ h)

  -- LFSC: t_t_neq_f
  t≢fᵇ : Holdsᶠ (notᶠ (≡ᵇ true false))
  t≢fᵇ = holdsᶠ _ refl

  -- LFSC: pred_eq_t
  t⇒x≡tᵇ : ∀ {b} → Holdsᶠ (appᵇ b) → Holdsᶠ (≡ᵇ b true)
  t⇒x≡tᵇ {true} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_eq_f
  f⇒x≡fᵇ : ∀ {b} → Holdsᶠ (notᶠ (appᵇ b)) → Holdsᶠ (≡ᵇ b false)
  f⇒x≡fᵇ {false} (holdsᶠ _ _) = holdsᶠ _ refl

  -- XXX - what does f_to_b do?

  -- LFSC: true_preds_equal
  tt⇒x≡yᵇ : ∀ {b₁ b₂} → Holdsᶠ (appᵇ b₁) → Holdsᶠ (appᵇ b₂) → Holdsᶠ (≡ᵇ b₁ b₂)
  tt⇒x≡yᵇ {true} {true} (holdsᶠ _ _) (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: false_preds_equal
  ff⇒x≡yᵇ : ∀ {b₁ b₂} → Holdsᶠ (notᶠ (appᵇ b₁)) → Holdsᶠ (notᶠ (appᵇ b₂)) → Holdsᶠ (≡ᵇ b₁ b₂)
  ff⇒x≡yᵇ {false} {false} (holdsᶠ _ _) (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_refl_pos
  t⇒x≡xᵇ : ∀ {b} → Holdsᶠ (appᵇ b) → Holdsᶠ (≡ᵇ b b)
  t⇒x≡xᵇ (holdsᶠ _ refl) = holdsᶠ _ refl

  -- LFSC: pred_refl_neg
  f⇒x≡xᵇ : ∀ {b} → Holdsᶠ (notᶠ (appᵇ b)) → Holdsᶠ (≡ᵇ b b)
  f⇒x≡xᵇ (holdsᶠ _ p) rewrite not-t⇒f p = holdsᶠ _ refl

  -- LFSC: pred_not_iff_f
  ¬f≡x⇒t≡xᵇ : ∀ {b} → Holdsᶠ (notᶠ (iffᶠ falseᶠ (appᵇ b))) → Holdsᶠ (≡ᵇ true b)
  ¬f≡x⇒t≡xᵇ {true} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_not_iff_f_2
  ¬x≡f⇒x≡tᵇ : ∀ {b} → Holdsᶠ (notᶠ (iffᶠ (appᵇ b) falseᶠ)) → Holdsᶠ (≡ᵇ b true)
  ¬x≡f⇒x≡tᵇ {true} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_not_iff_t
  ¬t≡x⇒f≡xᵇ : ∀ {b} → Holdsᶠ (notᶠ (iffᶠ trueᶠ (appᵇ b))) → Holdsᶠ (≡ᵇ false b)
  ¬t≡x⇒f≡xᵇ {false} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_not_iff_t_2
  ¬x≡t⇒xfxᵇ : ∀ {b} → Holdsᶠ (notᶠ (iffᶠ (appᵇ b) trueᶠ)) → Holdsᶠ (≡ᵇ b false)
  ¬x≡t⇒xfxᵇ {false} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_iff_f
  f≡x⇒f≡xᵇ : ∀ {b} → Holdsᶠ (iffᶠ falseᶠ (appᵇ b)) → Holdsᶠ (≡ᵇ false b)
  f≡x⇒f≡xᵇ {false} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_iff_f_2
  x≡f⇒x≡fᵇ : ∀ {b} → Holdsᶠ (iffᶠ (appᵇ b) falseᶠ) → Holdsᶠ (≡ᵇ b false)
  x≡f⇒x≡fᵇ {false} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_iff_t
  t≡x⇒t≡xᵇ : ∀ {b} → Holdsᶠ (iffᶠ trueᶠ (appᵇ b)) → Holdsᶠ (≡ᵇ true b)
  t≡x⇒t≡xᵇ {true} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_iff_t_2
  x≡t⇒x≡tᵇ : ∀ {b} → Holdsᶠ (iffᶠ (appᵇ b) trueᶠ) → Holdsᶠ (≡ᵇ b true)
  x≡t⇒x≡tᵇ {true} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: atom
  data Atom : Var → Formula false → Set where
    atom : (v : Var) → (f : Formula false) → evalᵛ env v ≡ evalᶠ f → Atom v f

  -- XXX - cover bvatom

  -- LFSC: decl_atom - replaced with concrete assignments to vᵢ and aᵢ

  -- XXX - cover decl_bvatom

  -- LFSC: clausify_form
  clausi : ∀ {f v} → Atom v f → Holdsᶠ f → Holdsᶜ (pos v ∷ [])

  clausi {f} {v} (atom .v .f a) (holdsᶠ .f h)
    rewrite h = holdsᶜ (pos v ∷ []) (subst (λ # → # ∨ false ≡ true) (sym a) refl)

  -- LFSC: clausify_form_not
  clausi-¬ : ∀ {f v} → Atom v f → Holdsᶠ (notᶠ f) → Holdsᶜ (neg v ∷ [])

  clausi-¬ {f} {v} (atom .v .f a) (holdsᶠ .(notᶠ f) h)
    rewrite not-t⇒f h = holdsᶜ (neg v ∷ []) (subst (λ # → not # ∨ false ≡ true) (sym a) refl)

  -- LFSC: clausify_false
  clausi-f : Holdsᶠ falseᶠ → Holdsᶜ []
  clausi-f (holdsᶠ .falseᶠ ())

  -- LFSC: th_let_pf
  mpᶠ : ∀ {f} → Holdsᶠ f → (Holdsᶠ f → Holdsᶜ []) → Holdsᶜ []
  mpᶠ {f} h fn = fn h

  -- LFSC: iff_symm
  x≡ᵇx : ∀ {f} → Holdsᶠ (iffᶠ f f)
  x≡ᵇx {f} = holdsᶠ (iffᶠ f f) (x⇔ᵇx (evalᶠ f))

  -- LFSC: contra
  contra : ∀ {f} → Holdsᶠ f → Holdsᶠ (notᶠ f) → Holdsᶠ falseᶠ
  contra {f} (holdsᶠ .f h₁) (holdsᶠ .(notᶠ f) h₂) = contradiction (not-t⇒f h₂) (not-¬ h₁)

  -- LFSC: truth
  truth : Holdsᶠ trueᶠ
  truth = holdsᶠ trueᶠ refl

  -- LFSC: not_not_intro
  ¬-¬-intro : ∀ {f} → Holdsᶠ f → Holdsᶠ (notᶠ (notᶠ f))
  ¬-¬-intro {f} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : not (not (evalᶠ f)) ≡ true
    lem rewrite p = refl

  -- LFSC: not_not_elim
  ¬-¬-elim : ∀ {f} → Holdsᶠ (notᶠ (notᶠ f)) → Holdsᶠ f
  ¬-¬-elim {f} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : evalᶠ f ≡ true
    lem with evalᶠ f
    lem | true  = refl
    lem | false = contradiction p (not-¬ refl)

  -- LFSC: or_elim_1
  ∨-elimˡ : ∀ {f₁ f₂} → Holdsᶠ (notᶠ f₁) → Holdsᶠ (orᶠ f₁ f₂) → Holdsᶠ f₂
  ∨-elimˡ (holdsᶠ _ p₁) (holdsᶠ _ p₂) rewrite not-t⇒f p₁ = holdsᶠ _ p₂

  -- LFSC: or_elim_2
  ∨-elimʳ : ∀ {f₁ f₂} → Holdsᶠ (notᶠ f₂) → Holdsᶠ (orᶠ f₁ f₂) → Holdsᶠ f₁
  ∨-elimʳ {f₁} (holdsᶠ _ p₁) (holdsᶠ _ p₂) rewrite not-t⇒f p₁ | ∨-identityʳ (evalᶠ f₁) = holdsᶠ _ p₂

  -- LFSC: not_or_elim
  de-morgan₁ : ∀ {f₁ f₂} → Holdsᶠ (notᶠ (orᶠ f₁ f₂)) → Holdsᶠ (andᶠ (notᶠ f₁) (notᶠ f₂))
  de-morgan₁ {f₁} {f₂} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : not (evalᶠ f₁) ∧ not (evalᶠ f₂) ≡ true
    lem with evalᶠ f₁ | evalᶠ f₂
    lem | true  | _     = contradiction p (not-¬ refl)
    lem | false | true  = contradiction p (not-¬ refl)
    lem | false | false = refl

  -- LFSC: and_elim_1
  ∧-elimʳ : ∀ {f₁ f₂} → Holdsᶠ (andᶠ f₁ f₂) → Holdsᶠ f₁
  ∧-elimʳ {f₁} (holdsᶠ _ p) with evalᶠ f₁ | inspect evalᶠ f₁
  ∧-elimʳ {f₁} (holdsᶠ _ p) | true | [ eq ] = holdsᶠ _ eq

  -- LFSC: and_elim_2
  ∧-elimˡ : ∀ {f₁ f₂} → Holdsᶠ (andᶠ f₁ f₂) → Holdsᶠ f₂
  ∧-elimˡ {f₁} {f₂} (holdsᶠ _ p) with evalᶠ f₁
  ∧-elimˡ {f₁} {f₂} (holdsᶠ _ p) | true = holdsᶠ _ p

  -- LFSC: not_and_elim
  de-morgan₂ : ∀ {f₁ f₂} → Holdsᶠ (notᶠ (andᶠ f₁ f₂)) → Holdsᶠ (orᶠ (notᶠ f₁) (notᶠ f₂))
  de-morgan₂ {f₁} {f₂} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : not (evalᶠ f₁) ∨ not (evalᶠ f₂) ≡ true
    lem with evalᶠ f₁ | evalᶠ f₂
    lem | true  | true  = contradiction p (not-¬ refl)
    lem | true  | false = refl
    lem | false | _     = refl

  -- LFSC: impl_intro
  ⇒-intro : ∀ {f₁ f₂} → Holdsᶠ f₁ → Holdsᶠ f₂ → Holdsᶠ (implᶠ f₁ f₂)
  ⇒-intro {f₁} {f₂} (holdsᶠ _ p₁) (holdsᶠ _ p₂) = holdsᶠ _ lem
    where
    lem : (evalᶠ f₁ →ᵇ evalᶠ f₂) ≡ true
    lem rewrite p₁ | p₂ = refl

  -- LFSC: impl_elim
  ⇒-elim : ∀ {f₁ f₂} → Holdsᶠ (implᶠ f₁ f₂) → Holdsᶠ (orᶠ (notᶠ f₁) f₂)
  ⇒-elim {f₁} {f₂} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : not (evalᶠ f₁) ∨ evalᶠ f₂ ≡ true
    lem with evalᶠ f₁ | evalᶠ f₂
    lem | true  | true  = refl
    lem | true  | false = contradiction p (not-¬ refl)
    lem | false | _     = refl

  -- LFSC: not_impl_elim
  ¬-⇒-elim : ∀ {f₁ f₂} → Holdsᶠ (notᶠ (implᶠ f₁ f₂)) → Holdsᶠ (andᶠ f₁ (notᶠ f₂))
  ¬-⇒-elim {f₁} {f₂} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : evalᶠ f₁ ∧ not (evalᶠ f₂) ≡ true
    lem with evalᶠ f₁ | evalᶠ f₂
    lem | true  | true  = contradiction p (not-¬ refl)
    lem | true  | false = refl
    lem | false | _     = contradiction p (not-¬ refl)

  -- LFSC: iff_elim_1
  ⇔-elim-⇒ : ∀ {f₁ f₂} → Holdsᶠ (iffᶠ f₁ f₂) → Holdsᶠ (orᶠ (notᶠ f₁) f₂)
  ⇔-elim-⇒ {f₁} {f₂} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : not (evalᶠ f₁) ∨ evalᶠ f₂ ≡ true
    lem with evalᶠ f₁ | evalᶠ f₂
    lem | true  | true  = refl
    lem | true  | false = contradiction p (not-¬ refl)
    lem | false | true  = contradiction p (not-¬ refl)
    lem | false | false = refl

  -- LFSC: iff_elim_2
  ⇔-elim-⇐ : ∀ {f₁ f₂} → Holdsᶠ (iffᶠ f₁ f₂) → Holdsᶠ (orᶠ f₁ (notᶠ f₂))
  ⇔-elim-⇐ {f₁} {f₂} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : evalᶠ f₁ ∨ not (evalᶠ f₂) ≡ true
    lem with evalᶠ f₁ | evalᶠ f₂
    lem | true  | true  = refl
    lem | true  | false = contradiction p (not-¬ refl)
    lem | false | true  = contradiction p (not-¬ refl)
    lem | false | false = refl

  -- LFSC: not_iff_elim
  ¬-⇔-elim : ∀ {f₁ f₂} → Holdsᶠ (notᶠ (iffᶠ f₁ f₂)) → Holdsᶠ (iffᶠ f₁ (notᶠ f₂))
  ¬-⇔-elim {f₁} {f₂} (holdsᶠ _ p) = holdsᶠ _ lem
    where
    lem : (evalᶠ f₁ ⇔ᵇ not (evalᶠ f₂)) ≡ true
    lem with evalᶠ f₁ | evalᶠ f₂
    lem | true  | true  = contradiction p (not-¬ refl)
    lem | true  | false = refl
    lem | false | true  = refl
    lem | false | false = contradiction p (not-¬ refl)

  -- LFSC: ast
  assum : ∀ {v f c} → Atom v f → (Holdsᶠ f → Holdsᶜ c) → Holdsᶜ (neg v ∷ c)
  assum {v} {f} {c} (atom .v .f a) fn = holdsᶜ (neg v ∷ c) lem₂

    where

    lem₁ : ∀ {f c} → (Holdsᶠ f → Holdsᶜ c) → evalᶠ f ≡ true → evalᶜ c ≡ true
    lem₁ {f} {c} fn e with fn (holdsᶠ f e)
    ... | holdsᶜ _ h = h

    lem₂ : not (evalᵛ env v) ∨ evalᶜ c ≡ true
    lem₂ with evalᶠ f | inspect evalᶠ f
    lem₂ | true  | [ eq ] rewrite a = lem₁ fn eq
    lem₂ | false | _      rewrite a = refl

  -- LFSC: asf
  assum-¬ : ∀ {v f c} → Atom v f → (Holdsᶠ (notᶠ f) → Holdsᶜ c) → Holdsᶜ (pos v ∷ c)
  assum-¬ {v} {f} {c} (atom .v .f a) fn = holdsᶜ (pos v ∷ c) lem₂

    where

    lem₁ : ∀ {f c} → (Holdsᶠ (notᶠ f) → Holdsᶜ c) → evalᶠ f ≡ false → evalᶜ c ≡ true
    lem₁ {f} {c} fn e with fn (holdsᶠ (notᶠ f) (f⇒not-t e))
    ... | holdsᶜ _ h = h

    lem₂ : evalᵛ env v ∨ evalᶜ c ≡ true
    lem₂ with evalᶠ f | inspect evalᶠ f
    lem₂ | true  | _      rewrite a = refl
    lem₂ | false | [ eq ] rewrite a = lem₁ fn eq

--- Base theory ---

-- XXX - remove one day, CVC4 promises that these are only temporary
postulate
  -- LFSC: trust
  trust-f : Holdsᶠ falseᶠ
  -- LFSC: trust_f
  trustᶠ : (f : Formula false) → Holdsᶠ f
