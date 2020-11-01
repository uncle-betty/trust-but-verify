module SMT where

open import Agda.Primitive using (Level) renaming (lzero to 0ℓ)

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_ ; T)

open import Data.Bool.Properties
  using (∨-identityʳ ; ∨-zeroʳ ; not-¬) renaming (≡-decSetoid to bool-setoid)

open import Data.Empty using (⊥)
open import Data.List using ([] ; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)

open import Function using (id ; _∘_ ; _$_ ; const)
open import Function.Equality using (Π)
open import Function.Equivalence using (_⇔_ ; equivalence)

open import Relation.Binary.Bundles using (DecSetoid)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; subst ; sym ; inspect ; [_])

open import Relation.Nullary using (¬_ ; Dec ; does ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Negation using (contradiction)

open import SAT
  using (
    Var ; var ; pos ; neg ; not-t⇒f ; f⇒not-t ;
    Env ; ε ; assignᵛ ; evalᵛ ; evalᶜ ; Holdsᶜ ; holdsᶜ
  )

instance
  _ = bool-setoid

data Formula : Set₁

formula-op₀ = Formula
-- LFSC: formula_op1
formula-op₁ = Formula → Formula
-- LFSC: formula_op2
formula-op₂ =  Formula → Formula → Formula
-- LFSC: formula_op3
formula-op₃ = Formula → Formula → Formula → Formula

-- LFSC: formula
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
  -- LFSC: xor
  xorᶠ   : formula-op₂
  -- LFSC: ifte
  iteᶠ   : formula-op₃
  -- LFSC: =
  equᶠ   : {{s : DecSetoid 0ℓ 0ℓ}} → DecSetoid.Carrier s → DecSetoid.Carrier s → Formula

  -- LFSC: p_app
  appᵇ   : Bool → Formula

  -- XXX - cover ite, let, flet?

  -- LFSC: bvult, ... (binary relations over terms)
  decˣ   : {S : Set} → Dec S → Formula

-- LFSC: sort, term replaced by Bool and BitVec

infix 3 _→ᵇ_

_→ᵇ_ : Bool → Bool → Bool
true  →ᵇ b = b
false →ᵇ _ = true

infix 3 _≡ᵇ_

_≡ᵇ_ : Bool → Bool → Bool
true  ≡ᵇ true  = true
false ≡ᵇ false = true
_     ≡ᵇ _     = false

≡ᵇ≡t⇒≡ : ∀ b₁ b₂ → (b₁ ≡ᵇ b₂) ≡ true → b₁ ≡ b₂
≡ᵇ≡t⇒≡ true true refl = refl
≡ᵇ≡t⇒≡ false false refl = refl

≡ᵇ≡f⇒≢ : ∀ b₁ b₂ → (b₁ ≡ᵇ b₂) ≡ false → b₁ ≢ b₂
≡ᵇ≡f⇒≢ true false p = λ ()
≡ᵇ≡f⇒≢ false true p = λ ()

x≡ᵇx : ∀ b → (b ≡ᵇ b) ≡ true
x≡ᵇx true  = refl
x≡ᵇx false = refl

eval : Formula → Bool
eval trueᶠ = true
eval falseᶠ = false

eval (notᶠ f) = not (eval f)
eval (andᶠ f₁ f₂) = eval f₁ ∧ eval f₂
eval (orᶠ f₁ f₂) = eval f₁ ∨ eval f₂
eval (implᶠ f₁ f₂) = eval f₁ →ᵇ eval f₂
eval (iffᶠ f₁ f₂) = eval f₁ ≡ᵇ eval f₂
eval (xorᶠ f₁ f₂) = eval f₁ xor eval f₂
eval (iteᶠ f₁ f₂ f₃) = if eval f₁ then eval f₂ else eval f₃
eval (equᶠ {{s}} x₁ x₂) = does (DecSetoid._≟_ s x₁ x₂)

eval (appᵇ b) = b
eval (decˣ d) = does d

prop : Formula → Set
prop trueᶠ  = ⊤
prop falseᶠ = ⊥

prop (notᶠ f) = ¬ prop f
prop (andᶠ f₁ f₂) = prop f₁ × prop f₂
prop (orᶠ f₁ f₂) = prop f₁ ⊎ prop f₂
prop (implᶠ f₁ f₂) = prop f₁ → prop f₂
prop (iffᶠ f₁ f₂) = prop f₁ ⇔ prop f₂
prop (xorᶠ f₁ f₂) = (prop f₁ × ¬ prop f₂) ⊎ (¬ prop f₁ × prop f₂)
prop (iteᶠ f₁ f₂ f₃) = (prop f₁ × prop f₂) ⊎ (¬ prop f₁ × prop f₃)
prop (equᶠ {{s}} x₁ x₂) = DecSetoid._≈_ s x₁ x₂

prop (appᵇ b) = T b
prop (decˣ {S} _) = S

-- XXX - wait... did I reinvent Dec here, with "eval f" reflecting "prop f"?
prove : ∀ f → eval f ≡ true → prop f
prove-¬ : ∀ f → eval f ≡ false → ¬ prop f

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

prove (xorᶠ f₁ f₂) p  with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
prove (xorᶠ f₁ f₂) () | true  | _       | true  | _
prove (xorᶠ f₁ f₂) _  | true  | [ eq₁ ] | false | [ eq₂ ] = inj₁ (prove f₁ eq₁ , prove-¬ f₂ eq₂)
prove (xorᶠ f₁ f₂) _  | false | [ eq₁ ] | true  | [ eq₂ ] = inj₂ (prove-¬ f₁ eq₁ , prove f₂ eq₂)
prove (xorᶠ f₁ f₂) () | false | _       | false | _

prove (iteᶠ f₁ f₂ f₃) p
  with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂ | eval f₃ | inspect eval f₃

prove (iteᶠ f₁ f₂ f₃) _  | true  | [ eq₁ ] | true  | [ eq₂ ] | _     | _       =
  inj₁ (prove f₁ eq₁ , prove f₂ eq₂)

prove (iteᶠ f₁ f₂ f₃) () | true  | _       | false | _       | _     | _

prove (iteᶠ f₁ f₂ f₃) _  | false | [ eq₁ ] | _     | _       | true  | [ eq₃ ] =
  inj₂ (prove-¬ f₁ eq₁ , prove f₃ eq₃)

prove (iteᶠ f₁ f₂ f₃) () | false | _       | _     | _       | false | _

prove (equᶠ {{s}} x₁ x₂) with DecSetoid._≟_ s x₁ x₂
... | true  because ofʸ p = λ { refl → p }
... | false because ofⁿ _ = λ ()

prove (appᵇ b) refl = tt
prove (decˣ (true because ofʸ p)) refl = p

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

prove-¬ (xorᶠ f₁ f₂) p  r with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂

prove-¬ (xorᶠ f₁ f₂) _  (inj₁ r) | true  | _       | true  | [ eq₂ ] =
  contradiction (prove f₂ eq₂) (proj₂ r)

prove-¬ (xorᶠ f₁ f₂) _  (inj₂ r) | true  | [ eq₁ ] | true  | _       =
  contradiction (prove f₁ eq₁) (proj₁ r)

prove-¬ (xorᶠ f₁ f₂) () _        | true  | _       | false | _
prove-¬ (xorᶠ f₁ f₂) () _        | false | _       | true  | _

prove-¬ (xorᶠ f₁ f₂) _  (inj₁ r) | false | [ eq₁ ] | false | _       =
  contradiction (proj₁ r) (prove-¬ f₁ eq₁)

prove-¬ (xorᶠ f₁ f₂) _  (inj₂ r) | false | _       | false | [ eq₂ ] =
  contradiction (proj₂ r) (prove-¬ f₂ eq₂)

prove-¬ (iteᶠ f₁ f₂ f₃) p r
  with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂ | eval f₃ | inspect eval f₃

prove-¬ (iteᶠ f₁ f₂ f₃) () _        | true  | _       | true  | _       | _     | _

prove-¬ (iteᶠ f₁ f₂ f₃) _  (inj₁ r) | true  | _       | false | [ eq₂ ] | _     | _       =
  contradiction (proj₂ r) (prove-¬ f₂ eq₂)

prove-¬ (iteᶠ f₁ f₂ f₃) _  (inj₂ r) | true  | [ eq₁ ] | false | _       | _     | _       =
  contradiction (prove f₁ eq₁) (proj₁ r)

prove-¬ (iteᶠ f₁ f₂ f₃) () _        | false | _       | _     | _       | true  | _

prove-¬ (iteᶠ f₁ f₂ f₃) _  (inj₁ r) | false | [ eq₁ ] | _     | _       | false | _       =
  contradiction (proj₁ r) (prove-¬ f₁ eq₁)

prove-¬ (iteᶠ f₁ f₂ f₃) _  (inj₂ r) | false | _       | _     | _       | false | [ eq₃ ] =
  contradiction (proj₂ r) (prove-¬ f₃ eq₃)

prove-¬ (equᶠ {{s}} x₁ x₂) with DecSetoid._≟_ s x₁ x₂
... | true  because ofʸ _ = λ ()
... | false because ofⁿ p = λ { refl → p }

prove-¬ (appᵇ b) refl = id
prove-¬ (decˣ (false because ofⁿ p)) refl = p

-- LFSC: th_holds
data Holds : Formula → Set where
  holds : ∀ f → eval f ≡ true → Holds f

holdsᶜ-[] : ∀ {env} → Holdsᶜ env [] → ⊥
holdsᶜ-[] (holdsᶜ .[] ())

holdsᶜ-[]-ε : ∀ {env} → Holdsᶜ env [] → Holdsᶜ ε []
holdsᶜ-[]-ε (holdsᶜ .[] ())

invert : ∀ {f} → (Holds (notᶠ f) → Holdsᶜ ε []) → prop f
invert {f} h with eval f | inspect eval f
... | true  | [ eq ] = prove f eq
... | false | [ eq ] = contradiction (holds (notᶠ f) (f⇒not-t eq)) (holdsᶜ-[] ∘ h)

-- LFSC: t_t_neq_f
t≢fᵇ : Holds (notᶠ (equᶠ true false))
t≢fᵇ = holds _ refl

-- LFSC: pred_eq_t
x⇒x≡tᵇ : ∀ {b} → Holds (appᵇ b) → Holds (equᶠ b true)
x⇒x≡tᵇ {true} (holds _ _) = holds _ refl

-- LFSC: pred_eq_f
¬x⇒x≡fᵇ : ∀ {b} → Holds (notᶠ (appᵇ b)) → Holds (equᶠ b false)
¬x⇒x≡fᵇ {false} (holds _ _) = holds _ refl

-- XXX - need f_to_b?

-- LFSC: true_preds_equal
x⇒y⇒x≡yᵇ : ∀ {b₁ b₂} → Holds (appᵇ b₁) → Holds (appᵇ b₂) → Holds (equᶠ b₁ b₂)
x⇒y⇒x≡yᵇ {true} {true} (holds _ _) (holds _ _) = holds _ refl

-- LFSC: false_preds_equal
¬x⇒¬y⇒x≡yᵇ : ∀ {b₁ b₂} → Holds (notᶠ (appᵇ b₁)) → Holds (notᶠ (appᵇ b₂)) → Holds (equᶠ b₁ b₂)
¬x⇒¬y⇒x≡yᵇ {false} {false} (holds _ _) (holds _ _) = holds _ refl

-- LFSC: pred_refl_pos
x⇒x≡xᵇ : ∀ {b} → Holds (appᵇ b) → Holds (equᶠ b b)
x⇒x≡xᵇ (holds _ refl) = holds _ refl

-- LFSC: pred_refl_neg
¬x⇒x≡xᵇ : ∀ {b} → Holds (notᶠ (appᵇ b)) → Holds (equᶠ b b)
¬x⇒x≡xᵇ (holds _ p) rewrite not-t⇒f p = holds _ refl

-- LFSC: pred_not_iff_f
¬f⇔x⇒t≡xᵇ : ∀ {b} → Holds (notᶠ (iffᶠ falseᶠ (appᵇ b))) → Holds (equᶠ true b)
¬f⇔x⇒t≡xᵇ {true} (holds _ _) = holds _ refl

-- LFSC: pred_not_iff_f_2
¬x⇔f⇒x≡tᵇ : ∀ {b} → Holds (notᶠ (iffᶠ (appᵇ b) falseᶠ)) → Holds (equᶠ b true)
¬x⇔f⇒x≡tᵇ {true} (holds _ _) = holds _ refl

-- LFSC: pred_not_iff_t
¬t⇔x⇒f≡xᵇ : ∀ {b} → Holds (notᶠ (iffᶠ trueᶠ (appᵇ b))) → Holds (equᶠ false b)
¬t⇔x⇒f≡xᵇ {false} (holds _ _) = holds _ refl

-- LFSC: pred_not_iff_t_2
¬x⇔t⇒x≡fᵇ : ∀ {b} → Holds (notᶠ (iffᶠ (appᵇ b) trueᶠ)) → Holds (equᶠ b false)
¬x⇔t⇒x≡fᵇ {false} (holds _ _) = holds _ refl

-- LFSC: pred_iff_f
f⇔x⇒f≡xᵇ : ∀ {b} → Holds (iffᶠ falseᶠ (appᵇ b)) → Holds (equᶠ false b)
f⇔x⇒f≡xᵇ {false} (holds _ _) = holds _ refl

-- LFSC: pred_iff_f_2
x⇔f⇒x≡fᵇ : ∀ {b} → Holds (iffᶠ (appᵇ b) falseᶠ) → Holds (equᶠ b false)
x⇔f⇒x≡fᵇ {false} (holds _ _) = holds _ refl

-- LFSC: pred_iff_t
t⇔x⇒t≡xᵇ : ∀ {b} → Holds (iffᶠ trueᶠ (appᵇ b)) → Holds (equᶠ true b)
t⇔x⇒t≡xᵇ {true} (holds _ _) = holds _ refl

-- LFSC: pred_iff_t_2
x⇔t⇒x≡tᵇ : ∀ {b} → Holds (iffᶠ (appᵇ b) trueᶠ) → Holds (equᶠ b true)
x⇔t⇒x≡tᵇ {true} (holds _ _) = holds _ refl

-- LFSC: atom
data Atom : Var → Formula → Env → Set where
  atom : ∀ v f env → evalᵛ env v ≡ eval f → Atom v f env

-- XXX - need bvatom?

-- LFSC: decl_atom
bind-atom : {env-[] : Env} → (n : ℕ) → (f : Formula) → (env-in : Env) →
  (fn :
    (v : Var) → v ≡ var n →
    (env-out : Env) → env-out ≡ assignᵛ env-in v (eval f) →
    ((env : Env) → evalᵛ env v ≡ eval f → Atom v f env) →
    Holdsᶜ env-[] []) →
  Holdsᶜ env-[] []

bind-atom n f env-in fn =
  let v = var n in
  let a⁻ = atom v f in
  let env-out = assignᵛ env-in v (eval f) in
  fn v refl env-out refl a⁻

bind-let : ∀ {ℓ₁ ℓ₂} → {S₁ : Set ℓ₁} → {S₂ : Set ℓ₂} → (y : S₁) → (fn : (x : S₁) → x ≡ y → S₂) → S₂
bind-let y fn = fn y refl

-- XXX - need decl_bvatom?

-- LFSC: clausify_form
clausi : ∀ {f v env} → Atom v f env → Holds f → Holdsᶜ env (pos v ∷ [])

clausi {f} {v} {env} (atom .v .f .env a) (holds .f h)
  rewrite h = holdsᶜ (pos v ∷ []) (subst (λ # → # ∨ false ≡ true) (sym a) refl)

-- LFSC: clausify_form_not
clausi-¬ : ∀ {f v env} → Atom v f env → Holds (notᶠ f) → Holdsᶜ env (neg v ∷ [])

clausi-¬ {f} {v} {env} (atom .v .f .env a) (holds .(notᶠ f) h)
  rewrite not-t⇒f h = holdsᶜ (neg v ∷ []) (subst (λ # → not # ∨ false ≡ true) (sym a) refl)

-- LFSC: clausify_false
clausi-f : ∀ {env} → Holds falseᶠ → Holdsᶜ env []
clausi-f (holds .falseᶠ ())

-- LFSC: th_let_pf
mp : ∀ {env f} → Holds f → (Holds f → Holdsᶜ env []) → Holdsᶜ env []
mp {f} h fn = fn h

-- LFSC: iff_symm
x⇔x : (f : Formula) → Holds (iffᶠ f f)
x⇔x f = holds (iffᶠ f f) (x≡ᵇx (eval f))

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
⇒-intro : ∀ {f₁ f₂} → (Holds f₁ → Holds f₂) → Holds (implᶠ f₁ f₂)
⇒-intro {f₁} {f₂} fn = holds _ lem
  where
  lem : (eval f₁ →ᵇ eval f₂) ≡ true
  lem with eval f₁ | inspect eval f₁ | eval f₂ | inspect eval f₂
  lem | true  | _      | true  | _      = refl
  lem | true  | [ p₁ ] | false | [ p₂ ] with holds _ p₃ ← fn (holds _ p₁) rewrite p₂ = p₃
  lem | false | _      | _     | _      = refl

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
  lem : (eval f₁ ≡ᵇ not (eval f₂)) ≡ true
  lem with eval f₁ | eval f₂
  lem | true  | true  = contradiction p (not-¬ refl)
  lem | true  | false = refl
  lem | false | true  = refl
  lem | false | false = contradiction p (not-¬ refl)

-- LFSC: xor_elim_1
xor-elim-¬ : ∀ {f₁ f₂} → Holds (xorᶠ f₁ f₂) → Holds (orᶠ (notᶠ f₁) (notᶠ f₂))
xor-elim-¬ {f₁} {f₂} (holds _ p) = holds _ lem
  where
  lem : not (eval f₁) ∨ not (eval f₂) ≡ true
  lem with eval f₁ | eval f₂
  lem | true  | true  = contradiction p (not-¬ refl)
  lem | true  | false = refl
  lem | false | true  = refl
  lem | false | false = contradiction p (not-¬ refl)

-- LFSC: xor_elim_2
xor-elim : ∀ {f₁ f₂} → Holds (xorᶠ f₁ f₂) → Holds (orᶠ f₁ f₂)
xor-elim {f₁} {f₂} (holds _ p) = holds _ lem
  where
  lem : eval f₁ ∨ eval f₂ ≡ true
  lem with eval f₁ | eval f₂
  lem | true  | true  = contradiction p (not-¬ refl)
  lem | true  | false = refl
  lem | false | true  = refl
  lem | false | false = contradiction p (not-¬ refl)

-- LFSC: not_xor_elim
¬-xor-elim : ∀ {f₁ f₂} → Holds (notᶠ (xorᶠ f₁ f₂)) → Holds (iffᶠ f₁ f₂)
¬-xor-elim {f₁} {f₂} (holds _ p) = holds _ lem
  where
  lem : (eval f₁ ≡ᵇ eval f₂) ≡ true
  lem with eval f₁ | eval f₂
  lem | true  | true  = refl
  lem | true  | false = contradiction p (not-¬ refl)
  lem | false | true  = contradiction p (not-¬ refl)
  lem | false | false = refl

-- LFSC: ite_elim_1
ite-elim-then : ∀ {f₁ f₂ f₃} → Holds (iteᶠ f₁ f₂ f₃) → Holds (orᶠ (notᶠ f₁) f₂)
ite-elim-then {f₁} {f₂} {f₃} (holds _ p) = holds _ lem
  where
  lem : not (eval f₁) ∨ eval f₂ ≡ true
  lem with eval f₁
  ... | true  = p
  ... | false = refl

-- LFSC: ite_elim_2
ite-elim-else : ∀ {f₁ f₂ f₃} → Holds (iteᶠ f₁ f₂ f₃) → Holds (orᶠ f₁ f₃)
ite-elim-else {f₁} {f₂} {f₃} (holds _ p) = holds _ lem
  where
  lem : eval f₁ ∨ eval f₃ ≡ true
  lem with eval f₁
  ... | true  = refl
  ... | false = p

-- LFSC: ite_elim_3
ite-elim-both : ∀ {f₁ f₂ f₃} → Holds (iteᶠ f₁ f₂ f₃) → Holds (orᶠ f₂ f₃)
ite-elim-both {f₁} {f₂} {f₃} (holds _ p) = holds _ lem
  where
  lem : eval f₂ ∨ eval f₃ ≡ true
  lem with eval f₁
  ... | true  rewrite p = refl
  ... | false rewrite p = ∨-zeroʳ (eval f₂)

-- LFSC: not_ite_elim_1
¬-ite-elim-then : ∀ {f₁ f₂ f₃} → Holds (notᶠ (iteᶠ f₁ f₂ f₃)) → Holds (orᶠ (notᶠ f₁) (notᶠ f₂))
¬-ite-elim-then {f₁} {f₂} {f₃} (holds _ p) = holds _ lem
  where
  lem : not (eval f₁) ∨ not (eval f₂) ≡ true
  lem with eval f₁
  ... | true  = p
  ... | false = refl

-- LFSC: not_ite_elim_2
¬-ite-elim-else : ∀ {f₁ f₂ f₃} → Holds (notᶠ (iteᶠ f₁ f₂ f₃)) → Holds (orᶠ f₁ (notᶠ f₃))
¬-ite-elim-else {f₁} {f₂} {f₃} (holds _ p) = holds _ lem
  where
  lem : eval f₁ ∨ not (eval f₃) ≡ true
  lem with eval f₁
  ... | true  = refl
  ... | false = p

-- LFSC: not_ite_elim_3
¬-ite-elim-both : ∀ {f₁ f₂ f₃} → Holds (notᶠ (iteᶠ f₁ f₂ f₃)) → Holds (orᶠ (notᶠ f₂) (notᶠ f₃))
¬-ite-elim-both {f₁} {f₂} {f₃} (holds _ p) = holds _ lem
  where
  lem : not (eval f₂) ∨ not (eval f₃) ≡ true
  lem with eval f₁
  ... | true  rewrite p = refl
  ... | false rewrite p = ∨-zeroʳ (not (eval f₂))

-- LFSC: ast
assum : ∀ {v f env c} → Atom v f env → (Holds f → Holdsᶜ env c) → Holdsᶜ env (neg v ∷ c)
assum {v} {f} {env} {c} (atom .v .f .env a) fn = holdsᶜ (neg v ∷ c) lem₂
  where
  lem₁ : ∀ {f c} → (Holds f → Holdsᶜ env c) → eval f ≡ true → evalᶜ env c ≡ true
  lem₁ {f} {c} fn e with holdsᶜ _ h ← fn (holds f e) = h

  lem₂ : not (evalᵛ env v) ∨ evalᶜ env c ≡ true
  lem₂ with eval f | inspect eval f
  lem₂ | true  | [ eq ] rewrite a = lem₁ fn eq
  lem₂ | false | _      rewrite a = refl

-- LFSC: asf
assum-¬ : ∀ {v f env c} → Atom v f env → (Holds (notᶠ f) → Holdsᶜ env c) → Holdsᶜ env (pos v ∷ c)
assum-¬ {v} {f} {env} {c} (atom .v .f .env a) fn = holdsᶜ (pos v ∷ c) lem₂
  where
  lem₁ : ∀ {f c} → (Holds (notᶠ f) → Holdsᶜ env c) → eval f ≡ false → evalᶜ env c ≡ true
  lem₁ {f} {c} fn e with holdsᶜ _ h ← fn (holds (notᶠ f) (f⇒not-t e)) = h

  lem₂ : evalᵛ env v ∨ evalᶜ env c ≡ true
  lem₂ with eval f | inspect eval f
  lem₂ | true  | _      rewrite a = refl
  lem₂ | false | [ eq ] rewrite a = lem₁ fn eq

-- XXX - need bv_asf, bv_ast?
-- XXX - need mpz_sub, mp_ispos, mpz_eq, mpz_lt, mpz_lte?
