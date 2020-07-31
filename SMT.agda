module SMT where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_ ; T)
open import Data.Bool.Properties using (∨-identityʳ ; not-¬)
open import Data.Empty using (⊥)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)

open import Function using (id ; _∘_ ; _$_ ; _∋_)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; subst ; sym ; inspect ; [_])

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Env using (Var ; var ; Env ; evalᵛ)

--- SMT ---

data Formula : Set₁

-- LFSC: formula_op1
formula-op₁ = Formula → Formula
-- LFSC: formula_op2
formula-op₂ = Formula → Formula → Formula
-- LFSC: formula_op3
formula-op₃ = Formula → Formula → Formula → Formula

-- LFSC: formula
data Formula where
  -- LFSC: true
  trueᶠ  : Formula
  -- LFSC: false
  falseᶠ : Formula

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
  ≡ᵇ     : Bool → Bool → Formula

  -- LFSC: p_app
  appᵇ   : Bool → Formula

  -- extension to opaquely wrap an existing witness for an arbitrary proposition
  witᶠ   : {P : Set} → P → Formula

infix 0 _⇔_

record _⇔_ (P Q : Set) : Set where
  constructor iffʳ
  field
    lr : P → Q
    rl : Q → P

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

evalᶠ : Formula → Bool
evalᶠ trueᶠ = true
evalᶠ falseᶠ = false

evalᶠ (notᶠ f) = not (evalᶠ f)
evalᶠ (andᶠ f₁ f₂) = evalᶠ f₁ ∧ evalᶠ f₂
evalᶠ (orᶠ f₁ f₂) = evalᶠ f₁ ∨ evalᶠ f₂
evalᶠ (implᶠ f₁ f₂) = evalᶠ f₁ →ᵇ evalᶠ f₂
evalᶠ (iffᶠ f₁ f₂) = evalᶠ f₁ ⇔ᵇ evalᶠ f₂

evalᶠ (≡ᵇ b₁ b₂) = b₁ ⇔ᵇ b₂
evalᶠ (appᵇ b) = b

evalᶠ (witᶠ _) = true

propᵇ : Formula → Set
propᵇ = T ∘ evalᶠ

propᵉ : Formula → Formula → Set
propᵉ f₁ f₂ = evalᶠ f₁ ≡ evalᶠ f₂

propᶠ : Formula → Set
propᶠ trueᶠ  = ⊤
propᶠ falseᶠ = ⊥

propᶠ (notᶠ f) = ¬ propᶠ f
propᶠ (andᶠ f₁ f₂) = propᶠ f₁ × propᶠ f₂
propᶠ (orᶠ f₁ f₂) = propᶠ f₁ ⊎ propᶠ f₂
propᶠ (implᶠ f₁ f₂) = propᶠ f₁ → propᶠ f₂
propᶠ (iffᶠ f₁ f₂) = propᶠ f₁ ⇔ propᶠ f₂

propᶠ (≡ᵇ b₁ b₂) = b₁ ≡ b₂
propᶠ (appᵇ b) = T b

propᶠ (witᶠ {P} _) = P

proveᵇ : ∀ f → evalᶠ f ≡ true → propᵇ f
proveᵇ _ p = subst T (sym p) tt

proveᵉ : ∀ f₁ f₂ → evalᶠ (iffᶠ f₁ f₂) ≡ true → propᵉ f₁ f₂
proveᵉ f₁ f₂ p = ⇔ᵇ≡t⇒≡ (evalᶠ f₁) (evalᶠ f₂) p

proveᵗ : ∀ f → evalᶠ f ≡ true → propᶠ f
proveᵗ-¬ : ∀ f → evalᶠ f ≡ false → ¬ propᶠ f

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
proveᵗ (implᶠ f₁ f₂) _  | true  | [ eq₁ ] | true  | [ eq₂ ] = λ _ → proveᵗ f₂ eq₂
proveᵗ (implᶠ f₁ f₂) () | true  | _       | false | _

proveᵗ (implᶠ f₁ f₂) _  | false | [ eq₁ ] | _     | _       =
  λ x → contradiction x (proveᵗ-¬ f₁ eq₁)

proveᵗ (iffᶠ f₁ f₂) p with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ (iffᶠ f₁ f₂) _  | true  | [ eq₁ ] | true  | [ eq₂ ] =
  record {
    lr = λ _ → proveᵗ f₂ eq₂ ;
    rl = λ _ → proveᵗ f₁ eq₁
  }

proveᵗ (iffᶠ f₁ f₂) () | true  | _       | false | _
proveᵗ (iffᶠ f₁ f₂) () | false | _       | true  | _

proveᵗ (iffᶠ f₁ f₂) _  | false | [ eq₁ ] | false | [ eq₂ ] =
  record {
    lr = λ x → contradiction x (proveᵗ-¬ f₁ eq₁) ;
    rl = λ x → contradiction x (proveᵗ-¬ f₂ eq₂)
  }

proveᵗ (≡ᵇ b₁ b₂) p = ⇔ᵇ≡t⇒≡ b₁ b₂ p
proveᵗ (appᵇ b) refl = tt

proveᵗ (witᶠ w) refl = w

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
  λ fn → (proveᵗ-¬ f₂ eq₂ ∘ fn) (proveᵗ f₁ eq₁)

proveᵗ-¬ (implᶠ f₁ f₂) () | false | _       | _     | _

proveᵗ-¬ (iffᶠ f₁ f₂) p with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
proveᵗ-¬ (iffᶠ f₁ f₂) () | true  | _       | true  | _

proveᵗ-¬ (iffᶠ f₁ f₂) _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ { (iffʳ lr _) → (proveᵗ-¬ f₂ eq₂ ∘ lr) (proveᵗ f₁ eq₁) }

proveᵗ-¬ (iffᶠ f₁ f₂) _  | false | [ eq₁ ] | true  | [ eq₂ ] =
  λ { (iffʳ _ rl) → (proveᵗ-¬ f₁ eq₁ ∘ rl) (proveᵗ f₂ eq₂) }

proveᵗ-¬ (iffᶠ f₁ f₂) () | false | _       | false | _

proveᵗ-¬ (≡ᵇ b₁ b₂) p = ⇔ᵇ≡f⇒≢ b₁ b₂ p
proveᵗ-¬ (appᵇ b) refl = id

-- LFSC: th_holds
data Holdsᶠ : Formula → Set where
  holdsᶠ : (f : Formula) → evalᶠ f ≡ true → Holdsᶠ f

module Rules (env : Env) where

  open import SAT env
    using (pos ; neg ; Holdsᶜ ; holdsᶜ ; holdsᶜ-[] ; evalᶜ ; not-t⇒f ; f⇒not-t)

  final : (f : Formula) → (Holdsᶠ (notᶠ f) → Holdsᶜ []) → evalᶠ f ≡ true
  final f h with evalᶠ f | inspect evalᶠ f
  ... | true  | [ eq ] = refl
  ... | false | [ eq ] = contradiction (holdsᶠ (notᶠ f) (f⇒not-t eq)) (holdsᶜ-[] ∘ h)

  -- XXX - unify the following three? for mixed formulas like (a ≡ b) ⊎ T (c ⇔ᵇ d)

  finalᶠ : (f : Formula) → (Holdsᶠ (notᶠ f) → Holdsᶜ []) → propᶠ f
  finalᶠ f h = proveᵗ f (final f h)

  finalᵇ : (f : Formula) → (Holdsᶠ (notᶠ f) → Holdsᶜ []) → propᵇ f
  finalᵇ f h = proveᵇ f (final f h)

  finalᵉ : (f₁ f₂ : Formula) → (Holdsᶠ (notᶠ (iffᶠ f₁ f₂)) → Holdsᶜ []) → evalᶠ f₁ ≡ evalᶠ f₂
  finalᵉ f₁ f₂ h = proveᵉ f₁ f₂ (final (iffᶠ f₁ f₂) h)

  -- LFSC: t_t_neq_f
  t≢fᵇ : Holdsᶠ (notᶠ (≡ᵇ true false))
  t≢fᵇ = holdsᶠ _ refl

  -- LFSC: pred_eq_t
  x≡tᵇ : ∀ {b} → Holdsᶠ (appᵇ b) → Holdsᶠ (≡ᵇ b true)
  x≡tᵇ {true} (holdsᶠ _ _) = holdsᶠ _ refl

  -- LFSC: pred_eq_f
  x≡fᵇ : ∀ {b} → Holdsᶠ (notᶠ (appᵇ b)) → Holdsᶠ (≡ᵇ b false)
  x≡fᵇ {false} (holdsᶠ _ _) = holdsᶠ _ refl

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
  data Atom : Var → Formula → Set where
    atom : (v : Var) → (f : Formula) → evalᵛ env v ≡ evalᶠ f → Atom v f

  -- XXX - cover bvatom

  -- LFSC: decl_atom - replaced with concrete assignments to vᵢ and aᵢ

  -- XXX - cover decl_bvatom

  -- LFSC: clausify_form
  clausi : ∀ {f v} → Atom v f → Holdsᶠ f → Holdsᶜ (pos v ∷ [])

  clausi {f} {v} (atom .v .f a) (holdsᶠ .f h)
    rewrite h
    = holdsᶜ (pos v ∷ []) (subst (λ # → # ∨ false ≡ true) (sym a) refl)

  -- LFSC: clausify_form_not
  clausi-¬ : ∀ {f v} → Atom v f → Holdsᶠ (notᶠ f) → Holdsᶜ (neg v ∷ [])

  clausi-¬ {f} {v} (atom .v .f a) (holdsᶠ .(notᶠ f) h)
    rewrite not-t⇒f h
    = holdsᶜ (neg v ∷ []) (subst (λ # → not # ∨ false ≡ true) (sym a) refl)

  -- LFSC: clausify_false
  clausi-f : Holdsᶠ falseᶠ → Holdsᶜ []
  clausi-f (holdsᶠ .falseᶠ ())

  -- LFSC: th_let_pf
  mpᶠ : ∀ {f} → Holdsᶠ f → (Holdsᶠ f → Holdsᶜ []) → Holdsᶜ []
  mpᶠ {f} h fn = fn h

  -- LFSC: iff_symm
  x-iff-x : ∀ {f} → Holdsᶠ (iffᶠ f f)
  x-iff-x {f} = holdsᶠ (iffᶠ f f) (x⇔ᵇx (evalᶠ f))

  -- LFSC: contra
  contra : ∀ {f} → Holdsᶠ f → Holdsᶠ (notᶠ f) → Holdsᶠ falseᶠ
  contra {f} (holdsᶠ .f h₁) (holdsᶠ .(notᶠ f) h₂) = contradiction (not-t⇒f h₂) (not-¬ h₁)

  -- LFSC: truth
  truth : Holdsᶠ trueᶠ
  truth = holdsᶠ trueᶠ refl

  holds⇒eval : ∀ {f c} → (Holdsᶠ f → Holdsᶜ c) → evalᶠ f ≡ true → evalᶜ c ≡ true
  holds⇒eval {f} {c} fn e with fn (holdsᶠ f e)
  ... | holdsᶜ .c h = h

  holds⇒eval-¬ : ∀ {f c} → (Holdsᶠ (notᶠ f) → Holdsᶜ c) → evalᶠ f ≡ false → evalᶜ c ≡ true
  holds⇒eval-¬ {f} {c} fn e with fn (holdsᶠ (notᶠ f) (f⇒not-t e))
  ... | holdsᶜ .c h = h

  -- LFSC: ast
  assum : ∀ {v f c} → Atom v f → (Holdsᶠ f → Holdsᶜ c) → Holdsᶜ (neg v ∷ c)
  assum {v} {f} {c} (atom .v .f a) fn = holdsᶜ (neg v ∷ c) lem

    where

    lem : not (evalᵛ env v) ∨ evalᶜ c ≡ true
    lem with evalᶠ f | inspect evalᶠ f
    lem | true  | [ eq ] rewrite a = holds⇒eval fn eq
    lem | false | [ eq ] rewrite a = refl

  -- LFSC: asf
  assum-¬ : ∀ {v f c} → Atom v f → (Holdsᶠ (notᶠ f) → Holdsᶜ c) → Holdsᶜ (pos v ∷ c)
  assum-¬ {v} {f} {c} (atom .v .f a) fn = holdsᶜ (pos v ∷ c) lem

    where

    lem : evalᵛ env v ∨ evalᶜ c ≡ true
    lem with evalᶠ f | inspect evalᶠ f
    lem | true  | [ eq ] rewrite a = refl
    lem | false | [ eq ] rewrite a = holds⇒eval-¬ fn eq

--- Base theory ---

-- XXX - remove some day, CVC4 says that these are temporary
postulate
  -- LFSC: trust
  trust-f : Holdsᶠ falseᶠ
  -- LFSC: trust_f
  trustᶠ : (f : Formula) → Holdsᶠ f
