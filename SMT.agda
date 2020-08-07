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
  boolˣ  : Formula true → Formula true
  -- extension - boolean equalities
  equˣ   : Formula true → Formula true → Formula true

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

eval : {ex : Bool} → Formula ex → Bool
eval trueᶠ = true
eval falseᶠ = false

eval (notᶠ f) = not (eval f)
eval (andᶠ f₁ f₂) = eval f₁ ∧ eval f₂
eval (orᶠ f₁ f₂) = eval f₁ ∨ eval f₂
eval (implᶠ f₁ f₂) = eval f₁ →ᵇ eval f₂
eval (iffᶠ f₁ f₂) = eval f₁ ⇔ᵇ eval f₂

eval (≡ᵇ b₁ b₂) = b₁ ⇔ᵇ b₂
eval (appᵇ b) = b

eval (boolˣ f) = eval f
eval (equˣ f₁ f₂) = eval f₁ ⇔ᵇ eval f₂

prop : {ex : Bool} → Formula ex → Set
prop trueᶠ  = ⊤
prop falseᶠ = ⊥

prop (notᶠ f) = ¬ prop f
prop (andᶠ f₁ f₂) = prop f₁ × prop f₂
prop (orᶠ f₁ f₂) = prop f₁ ⊎ prop f₂
prop (implᶠ f₁ f₂) = prop f₁ → prop f₂
prop (iffᶠ f₁ f₂) = prop f₁ ⇔ prop f₂

prop (≡ᵇ b₁ b₂) = b₁ ≡ b₂
prop (appᵇ b) = T b

prop (boolˣ f) = T (eval f)
prop (equˣ f₁ f₂) = eval f₁ ≡ eval f₂

prove : ∀ {ex} → (f : Formula ex) → eval f ≡ true → prop f
prove-¬ : ∀ {ex} → (f : Formula ex) → eval f ≡ false → ¬ prop f

prove trueᶠ p = tt

prove (notᶠ f) p with eval f | inspect eval f
prove (notᶠ f) () | true  | _
prove (notᶠ f) _  | false | [ eq ] = prove-¬ f eq

prove (andᶠ f₁ f₂) p  with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove (andᶠ f₁ f₂) _  | true  | [ eq₁ ] | true  | [ eq₂ ] = prove f₁ eq₁ , prove f₂ eq₂
prove (andᶠ f₁ f₂) () | true  | _       | false | _
prove (andᶠ f₁ f₂) () | false | _       | true  | _
prove (andᶠ f₁ f₂) () | false | _       | false | _

prove (orᶠ f₁ f₂) p  with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove (orᶠ f₁ f₂) _  | true  | [ eq₁ ] | _     | _       = inj₁ (prove f₁ eq₁)
prove (orᶠ f₁ f₂) _  | false | _       | true  | [ eq₂ ] = inj₂ (prove f₂ eq₂)
prove (orᶠ f₁ f₂) () | false | _       | false | _

prove (implᶠ f₁ f₂) p with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove (implᶠ f₁ f₂) _  | true  | [ eq₁ ] | true  | [ eq₂ ] = const $ prove f₂ eq₂
prove (implᶠ f₁ f₂) () | true  | _       | false | _

prove (implᶠ f₁ f₂) _  | false | [ eq₁ ] | _     | _       =
  λ x → contradiction x (prove-¬ f₁ eq₁)

prove (iffᶠ f₁ f₂) p with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove (iffᶠ f₁ f₂) _  | true  | [ eq₁ ] | true  | [ eq₂ ] =
  equivalence (const $ prove f₂ eq₂) (const $ prove f₁ eq₁)

prove (iffᶠ f₁ f₂) () | true  | _       | false | _
prove (iffᶠ f₁ f₂) () | false | _       | true  | _

prove (iffᶠ f₁ f₂) _  | false | [ eq₁ ] | false | [ eq₂ ] =
  equivalence
    (λ x → contradiction x (prove-¬ f₁ eq₁))
    λ x → contradiction x (prove-¬ f₂ eq₂)

prove (≡ᵇ b₁ b₂) p = ⇔ᵇ≡t⇒≡ b₁ b₂ p
prove (appᵇ b) refl = tt

prove (boolˣ f) p = subst T (sym p) tt
prove (equˣ f₁ f₂) p = ⇔ᵇ≡t⇒≡ (eval f₁) (eval f₂) p

prove-¬ falseᶠ p = id

prove-¬ (notᶠ f) p with eval f | inspect eval f
prove-¬ (notᶠ f) _  | true  | [ eq ] = λ x → x (prove f eq)
prove-¬ (notᶠ f) () | false | _

prove-¬ (andᶠ f₁ f₂) p  with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove-¬ (andᶠ f₁ f₂) () | true  | [ eq₁ ] | true  | [ eq₂ ]

prove-¬ (andᶠ f₁ f₂) _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ { (_ , p₂) → contradiction p₂ (prove-¬ f₂ eq₂) }

prove-¬ (andᶠ f₁ f₂) _  | false | [ eq₁ ] | true  | [ eq₂ ] =
  λ { (p₁ , _) → contradiction p₁ (prove-¬ f₁ eq₁) }

prove-¬ (andᶠ f₁ f₂) _  | false | [ eq₁ ] | false | [ eq₂ ] =
  λ { (p₁ , _) → contradiction p₁ (prove-¬ f₁ eq₁) }

prove-¬ (orᶠ f₁ f₂) p  with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove-¬ (orᶠ f₁ f₂) () | true  | _       | _     | _
prove-¬ (orᶠ f₁ f₂) () | false | _       | true  | _

prove-¬ (orᶠ f₁ f₂) _  | false | [ eq₁ ] | false | [ eq₂ ] =
  λ {
    (inj₁ p₁) → contradiction p₁ (prove-¬ f₁ eq₁) ;
    (inj₂ p₂) → contradiction p₂ (prove-¬ f₂ eq₂)
  }

prove-¬ (implᶠ f₁ f₂) p with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove-¬ (implᶠ f₁ f₂) () | true  | _       | true  | _

prove-¬ (implᶠ f₁ f₂) _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ fn → prove-¬ f₂ eq₂ $ fn (prove f₁ eq₁)

prove-¬ (implᶠ f₁ f₂) () | false | _       | _     | _

prove-¬ (iffᶠ f₁ f₂) p with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove-¬ (iffᶠ f₁ f₂) () | true  | _       | true  | _

prove-¬ (iffᶠ f₁ f₂) _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ { (record {to = lr}) → prove-¬ f₂ eq₂ $ lr ⟨$⟩ prove f₁ eq₁ }
  where open Π

prove-¬ (iffᶠ f₁ f₂) _  | false | [ eq₁ ] | true  | [ eq₂ ] =
  λ { (record {from = rl}) → prove-¬ f₁ eq₁ $ rl ⟨$⟩ prove f₂ eq₂ }
  where open Π

prove-¬ (iffᶠ f₁ f₂) () | false | _       | false | _

prove-¬ (≡ᵇ b₁ b₂) p = ⇔ᵇ≡f⇒≢ b₁ b₂ p
prove-¬ (appᵇ b) refl = id

prove-¬ (boolˣ f) p r = subst T p r
prove-¬ (equˣ f₁ f₂) p = ⇔ᵇ≡f⇒≢ (eval f₁) (eval f₂) p

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

strip (boolˣ f) = strip f
strip (equˣ f₁ f₂) = iffᶠ (strip f₁) (strip f₂)

strip-sound : ∀ {ex} → (f : Formula ex) → eval (strip f) ≡ eval f

strip-sound trueᶠ = refl
strip-sound falseᶠ = refl

strip-sound (notᶠ f) rewrite strip-sound f = refl
strip-sound (andᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl
strip-sound (orᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl
strip-sound (implᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl
strip-sound (iffᶠ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl

strip-sound (≡ᵇ b₁ b₂) = refl
strip-sound (appᵇ b) = refl

strip-sound (boolˣ f) = strip-sound f
strip-sound (equˣ f₁ f₂) rewrite strip-sound f₁ | strip-sound f₂ = refl

-- LFSC: th_holds
data Holds : Formula false → Set where
  holds : (f : Formula false) → eval f ≡ true → Holds f

module Rules (env : Env) where

  open import SAT env
    using (pos ; neg ; Holdsᶜ ; holdsᶜ ; holdsᶜ-[] ; evalᶜ ; not-t⇒f ; f⇒not-t)

  final : (f : Formula true) → (Holds (notᶠ (strip f)) → Holdsᶜ []) → prop f
  final f h = prove f $ subst (_≡ true) (strip-sound f) (lem (strip f) h)
    where
    lem : (f : Formula false) → (Holds (notᶠ f) → Holdsᶜ []) → eval f ≡ true
    lem f h with eval f | inspect eval f
    ... | true  | [ eq ] = refl
    ... | false | [ eq ] = contradiction (holds (notᶠ f) (f⇒not-t eq)) (holdsᶜ-[] ∘ h)

  -- LFSC: t_t_neq_f
  t≢fᵇ : Holds (notᶠ (≡ᵇ true false))
  t≢fᵇ = holds _ refl

  -- LFSC: pred_eq_t
  t⇒x≡tᵇ : ∀ {b} → Holds (appᵇ b) → Holds (≡ᵇ b true)
  t⇒x≡tᵇ {true} (holds _ _) = holds _ refl

  -- LFSC: pred_eq_f
  f⇒x≡fᵇ : ∀ {b} → Holds (notᶠ (appᵇ b)) → Holds (≡ᵇ b false)
  f⇒x≡fᵇ {false} (holds _ _) = holds _ refl

  -- XXX - what does f_to_b do?

  -- LFSC: true_preds_equal
  tt⇒x≡yᵇ : ∀ {b₁ b₂} → Holds (appᵇ b₁) → Holds (appᵇ b₂) → Holds (≡ᵇ b₁ b₂)
  tt⇒x≡yᵇ {true} {true} (holds _ _) (holds _ _) = holds _ refl

  -- LFSC: false_preds_equal
  ff⇒x≡yᵇ : ∀ {b₁ b₂} → Holds (notᶠ (appᵇ b₁)) → Holds (notᶠ (appᵇ b₂)) → Holds (≡ᵇ b₁ b₂)
  ff⇒x≡yᵇ {false} {false} (holds _ _) (holds _ _) = holds _ refl

  -- LFSC: pred_refl_pos
  t⇒x≡xᵇ : ∀ {b} → Holds (appᵇ b) → Holds (≡ᵇ b b)
  t⇒x≡xᵇ (holds _ refl) = holds _ refl

  -- LFSC: pred_refl_neg
  f⇒x≡xᵇ : ∀ {b} → Holds (notᶠ (appᵇ b)) → Holds (≡ᵇ b b)
  f⇒x≡xᵇ (holds _ p) rewrite not-t⇒f p = holds _ refl

  -- LFSC: pred_not_iff_f
  ¬f≡x⇒t≡xᵇ : ∀ {b} → Holds (notᶠ (iffᶠ falseᶠ (appᵇ b))) → Holds (≡ᵇ true b)
  ¬f≡x⇒t≡xᵇ {true} (holds _ _) = holds _ refl

  -- LFSC: pred_not_iff_f_2
  ¬x≡f⇒x≡tᵇ : ∀ {b} → Holds (notᶠ (iffᶠ (appᵇ b) falseᶠ)) → Holds (≡ᵇ b true)
  ¬x≡f⇒x≡tᵇ {true} (holds _ _) = holds _ refl

  -- LFSC: pred_not_iff_t
  ¬t≡x⇒f≡xᵇ : ∀ {b} → Holds (notᶠ (iffᶠ trueᶠ (appᵇ b))) → Holds (≡ᵇ false b)
  ¬t≡x⇒f≡xᵇ {false} (holds _ _) = holds _ refl

  -- LFSC: pred_not_iff_t_2
  ¬x≡t⇒xfxᵇ : ∀ {b} → Holds (notᶠ (iffᶠ (appᵇ b) trueᶠ)) → Holds (≡ᵇ b false)
  ¬x≡t⇒xfxᵇ {false} (holds _ _) = holds _ refl

  -- LFSC: pred_iff_f
  f≡x⇒f≡xᵇ : ∀ {b} → Holds (iffᶠ falseᶠ (appᵇ b)) → Holds (≡ᵇ false b)
  f≡x⇒f≡xᵇ {false} (holds _ _) = holds _ refl

  -- LFSC: pred_iff_f_2
  x≡f⇒x≡fᵇ : ∀ {b} → Holds (iffᶠ (appᵇ b) falseᶠ) → Holds (≡ᵇ b false)
  x≡f⇒x≡fᵇ {false} (holds _ _) = holds _ refl

  -- LFSC: pred_iff_t
  t≡x⇒t≡xᵇ : ∀ {b} → Holds (iffᶠ trueᶠ (appᵇ b)) → Holds (≡ᵇ true b)
  t≡x⇒t≡xᵇ {true} (holds _ _) = holds _ refl

  -- LFSC: pred_iff_t_2
  x≡t⇒x≡tᵇ : ∀ {b} → Holds (iffᶠ (appᵇ b) trueᶠ) → Holds (≡ᵇ b true)
  x≡t⇒x≡tᵇ {true} (holds _ _) = holds _ refl

  -- LFSC: atom
  data Atom : Var → Formula false → Set where
    atom : (v : Var) → (f : Formula false) → evalᵛ env v ≡ eval f → Atom v f

  -- XXX - cover bvatom

  -- LFSC: decl_atom - replaced with concrete assignments to vᵢ and aᵢ

  -- XXX - cover decl_bvatom

  -- LFSC: clausify_form
  clausi : ∀ {f v} → Atom v f → Holds f → Holdsᶜ (pos v ∷ [])

  clausi {f} {v} (atom .v .f a) (holds .f h)
    rewrite h = holdsᶜ (pos v ∷ []) (subst (λ # → # ∨ false ≡ true) (sym a) refl)

  -- LFSC: clausify_form_not
  clausi-¬ : ∀ {f v} → Atom v f → Holds (notᶠ f) → Holdsᶜ (neg v ∷ [])

  clausi-¬ {f} {v} (atom .v .f a) (holds .(notᶠ f) h)
    rewrite not-t⇒f h = holdsᶜ (neg v ∷ []) (subst (λ # → not # ∨ false ≡ true) (sym a) refl)

  -- LFSC: clausify_false
  clausi-f : Holds falseᶠ → Holdsᶜ []
  clausi-f (holds .falseᶠ ())

  -- LFSC: th_let_pf
  mpᶠ : ∀ {f} → Holds f → (Holds f → Holdsᶜ []) → Holdsᶜ []
  mpᶠ {f} h fn = fn h

  -- LFSC: iff_symm
  x≡ᵇx : ∀ {f} → Holds (iffᶠ f f)
  x≡ᵇx {f} = holds (iffᶠ f f) (x⇔ᵇx (eval f))

  -- LFSC: contra
  contra : ∀ {f} → Holds f → Holds (notᶠ f) → Holds falseᶠ
  contra {f} (holds .f h₁) (holds .(notᶠ f) h₂) = contradiction (not-t⇒f h₂) (not-¬ h₁)

  -- LFSC: truth
  truth : Holds trueᶠ
  truth = holds trueᶠ refl

  -- LFSC: not_not_intro
  ¬-¬-intro : ∀ {f} → Holds f → Holds (notᶠ (notᶠ f))
  ¬-¬-intro {f} (holds _ p) = holds _ lem
    where
    lem : not (not (eval f)) ≡ true
    lem rewrite p = refl

  -- LFSC: not_not_elim
  ¬-¬-elim : ∀ {f} → Holds (notᶠ (notᶠ f)) → Holds f
  ¬-¬-elim {f} (holds _ p) = holds _ lem
    where
    lem : eval f ≡ true
    lem with eval f
    lem | true  = refl
    lem | false = contradiction p (not-¬ refl)

  -- LFSC: or_elim_1
  ∨-elimˡ : ∀ {f₁ f₂} → Holds (notᶠ f₁) → Holds (orᶠ f₁ f₂) → Holds f₂
  ∨-elimˡ (holds _ p₁) (holds _ p₂) rewrite not-t⇒f p₁ = holds _ p₂

  -- LFSC: or_elim_2
  ∨-elimʳ : ∀ {f₁ f₂} → Holds (notᶠ f₂) → Holds (orᶠ f₁ f₂) → Holds f₁
  ∨-elimʳ {f₁} (holds _ p₁) (holds _ p₂) rewrite not-t⇒f p₁ | ∨-identityʳ (eval f₁) = holds _ p₂

  -- LFSC: not_or_elim
  de-morgan₁ : ∀ {f₁ f₂} → Holds (notᶠ (orᶠ f₁ f₂)) → Holds (andᶠ (notᶠ f₁) (notᶠ f₂))
  de-morgan₁ {f₁} {f₂} (holds _ p) = holds _ lem
    where
    lem : not (eval f₁) ∧ not (eval f₂) ≡ true
    lem with eval f₁ | eval f₂
    lem | true  | _     = contradiction p (not-¬ refl)
    lem | false | true  = contradiction p (not-¬ refl)
    lem | false | false = refl

  -- LFSC: and_elim_1
  ∧-elimʳ : ∀ {f₁ f₂} → Holds (andᶠ f₁ f₂) → Holds f₁
  ∧-elimʳ {f₁} (holds _ p) with eval f₁ | inspect eval f₁
  ∧-elimʳ {f₁} (holds _ p) | true | [ eq ] = holds _ eq

  -- LFSC: and_elim_2
  ∧-elimˡ : ∀ {f₁ f₂} → Holds (andᶠ f₁ f₂) → Holds f₂
  ∧-elimˡ {f₁} {f₂} (holds _ p) with eval f₁
  ∧-elimˡ {f₁} {f₂} (holds _ p) | true = holds _ p

  -- LFSC: not_and_elim
  de-morgan₂ : ∀ {f₁ f₂} → Holds (notᶠ (andᶠ f₁ f₂)) → Holds (orᶠ (notᶠ f₁) (notᶠ f₂))
  de-morgan₂ {f₁} {f₂} (holds _ p) = holds _ lem
    where
    lem : not (eval f₁) ∨ not (eval f₂) ≡ true
    lem with eval f₁ | eval f₂
    lem | true  | true  = contradiction p (not-¬ refl)
    lem | true  | false = refl
    lem | false | _     = refl

  -- LFSC: impl_intro
  ⇒-intro : ∀ {f₁ f₂} → Holds f₁ → Holds f₂ → Holds (implᶠ f₁ f₂)
  ⇒-intro {f₁} {f₂} (holds _ p₁) (holds _ p₂) = holds _ lem
    where
    lem : (eval f₁ →ᵇ eval f₂) ≡ true
    lem rewrite p₁ | p₂ = refl

  -- LFSC: impl_elim
  ⇒-elim : ∀ {f₁ f₂} → Holds (implᶠ f₁ f₂) → Holds (orᶠ (notᶠ f₁) f₂)
  ⇒-elim {f₁} {f₂} (holds _ p) = holds _ lem
    where
    lem : not (eval f₁) ∨ eval f₂ ≡ true
    lem with eval f₁ | eval f₂
    lem | true  | true  = refl
    lem | true  | false = contradiction p (not-¬ refl)
    lem | false | _     = refl

  -- LFSC: not_impl_elim
  ¬-⇒-elim : ∀ {f₁ f₂} → Holds (notᶠ (implᶠ f₁ f₂)) → Holds (andᶠ f₁ (notᶠ f₂))
  ¬-⇒-elim {f₁} {f₂} (holds _ p) = holds _ lem
    where
    lem : eval f₁ ∧ not (eval f₂) ≡ true
    lem with eval f₁ | eval f₂
    lem | true  | true  = contradiction p (not-¬ refl)
    lem | true  | false = refl
    lem | false | _     = contradiction p (not-¬ refl)

  -- LFSC: iff_elim_1
  ⇔-elim-⇒ : ∀ {f₁ f₂} → Holds (iffᶠ f₁ f₂) → Holds (orᶠ (notᶠ f₁) f₂)
  ⇔-elim-⇒ {f₁} {f₂} (holds _ p) = holds _ lem
    where
    lem : not (eval f₁) ∨ eval f₂ ≡ true
    lem with eval f₁ | eval f₂
    lem | true  | true  = refl
    lem | true  | false = contradiction p (not-¬ refl)
    lem | false | true  = contradiction p (not-¬ refl)
    lem | false | false = refl

  -- LFSC: iff_elim_2
  ⇔-elim-⇐ : ∀ {f₁ f₂} → Holds (iffᶠ f₁ f₂) → Holds (orᶠ f₁ (notᶠ f₂))
  ⇔-elim-⇐ {f₁} {f₂} (holds _ p) = holds _ lem
    where
    lem : eval f₁ ∨ not (eval f₂) ≡ true
    lem with eval f₁ | eval f₂
    lem | true  | true  = refl
    lem | true  | false = contradiction p (not-¬ refl)
    lem | false | true  = contradiction p (not-¬ refl)
    lem | false | false = refl

  -- LFSC: not_iff_elim
  ¬-⇔-elim : ∀ {f₁ f₂} → Holds (notᶠ (iffᶠ f₁ f₂)) → Holds (iffᶠ f₁ (notᶠ f₂))
  ¬-⇔-elim {f₁} {f₂} (holds _ p) = holds _ lem
    where
    lem : (eval f₁ ⇔ᵇ not (eval f₂)) ≡ true
    lem with eval f₁ | eval f₂
    lem | true  | true  = contradiction p (not-¬ refl)
    lem | true  | false = refl
    lem | false | true  = refl
    lem | false | false = contradiction p (not-¬ refl)

  -- LFSC: ast
  assum : ∀ {v f c} → Atom v f → (Holds f → Holdsᶜ c) → Holdsᶜ (neg v ∷ c)
  assum {v} {f} {c} (atom .v .f a) fn = holdsᶜ (neg v ∷ c) lem₂

    where

    lem₁ : ∀ {f c} → (Holds f → Holdsᶜ c) → eval f ≡ true → evalᶜ c ≡ true
    lem₁ {f} {c} fn e with fn (holds f e)
    ... | holdsᶜ _ h = h

    lem₂ : not (evalᵛ env v) ∨ evalᶜ c ≡ true
    lem₂ with eval f | inspect eval f
    lem₂ | true  | [ eq ] rewrite a = lem₁ fn eq
    lem₂ | false | _      rewrite a = refl

  -- LFSC: asf
  assum-¬ : ∀ {v f c} → Atom v f → (Holds (notᶠ f) → Holdsᶜ c) → Holdsᶜ (pos v ∷ c)
  assum-¬ {v} {f} {c} (atom .v .f a) fn = holdsᶜ (pos v ∷ c) lem₂

    where

    lem₁ : ∀ {f c} → (Holds (notᶠ f) → Holdsᶜ c) → eval f ≡ false → evalᶜ c ≡ true
    lem₁ {f} {c} fn e with fn (holds (notᶠ f) (f⇒not-t e))
    ... | holdsᶜ _ h = h

    lem₂ : evalᵛ env v ∨ evalᶜ c ≡ true
    lem₂ with eval f | inspect eval f
    lem₂ | true  | _      rewrite a = refl
    lem₂ | false | [ eq ] rewrite a = lem₁ fn eq

--- Base theory ---

-- XXX - remove one day, CVC4 promises that these are only temporary
postulate
  -- LFSC: trust
  trust-f : Holds falseᶠ
  -- LFSC: trust_f
  trust : (f : Formula false) → Holds f
