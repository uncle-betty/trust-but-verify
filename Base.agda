module Base where

open import Data.Bool using (Bool ; true ; false ; not)

open import Data.Bool.Properties
  using (not-¬) renaming (≡-setoid to bool-sd ; ≡-decSetoid to bool-dsd)

open import Function using (_$_ ; _∘_ ; it)

open import Level using (0ℓ)

open import Relation.Binary using (Decidable)
open import Relation.Binary.Bundles using () renaming (DecSetoid to DSD ; Setoid to SD)
open import Relation.Binary.Properties.Setoid using (≉-sym ; ≉-respʳ ; ≉-respˡ)

open import Relation.Binary.PropositionalEquality
  using (inspect ; [_] ; _≡_) renaming (cong to cong′ ; refl to refl′)

open import Relation.Nullary using (Dec ; _because_ ; does ; ofʸ ; ofⁿ ; yes ; no ; ¬_)
open import Relation.Nullary.Decidable using (dec-true ; dec-false)
open import Relation.Nullary.Negation using (contradiction)

open import SMT using (Holds ; holds ; falseᶠ ; equᶠ ; notᶠ ; prove)

open DSD using (_≈_ ; _≟_ ; setoid) renaming (Carrier to Car)

-- LFSC: arrow, apply - replaced by Agda function types and application

postulate
  -- LFSC: trust
  trust-f : Holds falseᶠ
  -- LFSC: trust_f
  trust : ∀ f → Holds f

-- LFSC: refl
refl : {{dsd : DSD 0ℓ 0ℓ}} → (x : Car dsd) → Holds (equᶠ x x)
refl x with _≟_ it x x | inspect (_≟_ it x) x
... | true  because ofʸ _ | [ eq ] = holds _ (cong′ does eq)
... | false because ofⁿ p | _      = contradiction (DSD.refl it {x}) p

-- LFSC: symm
sym : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ : Car dsd} → Holds (equᶠ x₁ x₂) → Holds (equᶠ x₂ x₁)
sym (holds (equᶠ x₁ x₂) _) with _≟_ it x₁ x₂
... | true because ofʸ p = holds _ $ dec-true (_≟_ it x₂ x₁) (DSD.sym it p)

-- LFSC: trans
trans : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ x₃ : Car dsd} →
  Holds (equᶠ x₁ x₂) → Holds (equᶠ x₂ x₃) → Holds (equᶠ x₁ x₃)

trans (holds (equᶠ x₁ x₂) _) (holds (equᶠ x₂ x₃) _) with _≟_ it x₁ x₂ | _≟_ it x₂ x₃
... | true because ofʸ p₁ | true because ofʸ p₂ =
  holds _ $ dec-true (_≟_ it x₁ x₃) (DSD.trans it p₁ p₂)

-- LFSC: negsymm
¬-sym : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ : Car dsd} →
  Holds (notᶠ (equᶠ x₁ x₂)) → Holds (notᶠ (equᶠ x₂ x₁))

¬-sym (holds (notᶠ (equᶠ x₁ x₂)) h) with _≟_ it x₁ x₂
... | false because ofⁿ p =
  holds _ $ cong′ not $ dec-false (_≟_ it x₂ x₁) (≉-sym (setoid it) p)

-- LFSC: negtrans1
¬-trans₁ : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ x₃ : Car dsd} →
  Holds (notᶠ (equᶠ x₁ x₂)) → Holds (equᶠ x₂ x₃) → Holds (notᶠ (equᶠ x₁ x₃))

¬-trans₁ (holds (notᶠ (equᶠ x₁ x₂)) _) (holds (equᶠ x₂ x₃) _)
  with _≟_ it x₁ x₂ | _≟_ it x₂ x₃

... | false because ofⁿ p₁ | true because ofʸ p₂ =
  holds _ $ cong′ not $ dec-false (_≟_ it x₁ x₃) (≉-respʳ (setoid it) p₂ p₁)

-- LFSC: negtrans2
¬-trans₂ : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ x₃ : Car dsd} →
  Holds (equᶠ x₁ x₂) → Holds (notᶠ (equᶠ x₂ x₃)) → Holds (notᶠ (equᶠ x₁ x₃))

¬-trans₂ (holds (equᶠ x₁ x₂) _) (holds (notᶠ (equᶠ x₂ x₃)) _)
  with _≟_ it x₁ x₂ | _≟_ it x₂ x₃

... | true because ofʸ p₁ | false because ofⁿ p₂ =
  holds _ $ cong′ not $ dec-false (_≟_ it x₁ x₃) (≉-respˡ (setoid it) (DSD.sym it p₁) p₂)

-- instance resolution doesn't like function types, so wrap functions in records
record Wrapper (dsdᶠ : DSD 0ℓ 0ℓ) (dsdᵗ : DSD 0ℓ 0ℓ) : Set where
  open DSD dsdᶠ using () renaming (_≈_ to _≈ᶠ_ ; Carrier to Carᶠ)
  open DSD dsdᵗ using () renaming (_≈_ to _≈ᵗ_ ; Carrier to Carᵗ)

  field
    decide-eq : Decidable (λ (f₁ : Carᶠ → Carᵗ) (f₂ : Carᶠ → Carᵗ) →
      {x₁ x₂ : Carᶠ} → x₁ ≈ᶠ x₂ → f₁ x₁ ≈ᵗ f₂ x₂)
    congruence : {f : Carᶠ → Carᵗ} → {x₁ x₂ : Carᶠ} → x₁ ≈ᶠ x₂ → f x₁ ≈ᵗ f x₂

build-dsd : (dsdᶠ : DSD 0ℓ 0ℓ) → (dsdᵗ : DSD 0ℓ 0ℓ) → Wrapper dsdᶠ dsdᵗ → DSD 0ℓ 0ℓ
build-dsd dsdᶠ dsdᵗ wrap = record {
    Carrier = Car dsdᶠ → Car dsdᵗ ;
    _≈_ = λ f₁ f₂ → ∀ {x₁ x₂} → x₁ ≈ᶠ x₂ → f₁ x₁ ≈ᵗ f₂ x₂ ;
    isDecEquivalence = record {
        isEquivalence = record {
            refl  = congruence ;
            sym   = λ p₁ p₂ → symᵗ (p₁ (symᶠ p₂)) ;
            trans = λ p₁ p₂ p₃ → transᵗ (p₁ reflᶠ) (p₂ p₃)
          } ;
        _≟_ = decide-eq
      }
  }

  where
  open DSD dsdᶠ using () renaming (_≈_ to _≈ᶠ_ ; sym to symᶠ ; refl to reflᶠ)
  open DSD dsdᵗ using () renaming (_≈_ to _≈ᵗ_ ; sym to symᵗ ; trans to transᵗ)
  open Wrapper wrap using (decide-eq ; congruence)

equᶠ-≈ : {dsd : DSD 0ℓ 0ℓ} → {x y : Car dsd} → Holds (equᶠ {{dsd}} x y) → _≈_ dsd x y
equᶠ-≈ {dsd} {x} {y} (holds _ h) = prove (equᶠ {{dsd}} x y) h

≈-does : {dsd : DSD 0ℓ 0ℓ} → {x y : Car dsd} → _≈_ dsd x y → does (_≟_ dsd x y) ≡ true
≈-does {dsd} {x} {y} p with _≟_ dsd x y
... | true  because ofʸ _  = refl′
... | false because ofⁿ p′ = contradiction p p′

-- LFSC: cong
cong :
  {{dsdᶠ dsdᵗ : DSD 0ℓ 0ℓ}} →
  {{wrap : Wrapper dsdᶠ dsdᵗ}} →
  {f₁ f₂ : Car dsdᶠ → Car dsdᵗ} →
  {x₁ x₂ : Car dsdᶠ} →
  Holds (equᶠ {{build-dsd dsdᶠ dsdᵗ wrap}} f₁ f₂) →
  Holds (equᶠ {{dsdᶠ}} x₁ x₂) →
  Holds (equᶠ {{dsdᵗ}} (f₁ x₁) (f₂ x₂))

cong h₁ h₂ = holds _ $ ≈-does {it} $ equᶠ-≈ h₁ (equᶠ-≈ h₂)

gen-bool₁ : {sdᵗ : SD 0ℓ 0ℓ} → {f₁ f₂ : Bool → SD.Carrier sdᵗ} →
  SD._≈_ sdᵗ (f₁ true)  (f₂ true)  →
  SD._≈_ sdᵗ (f₁ false) (f₂ false) →
  (({x₁ x₂} : Bool) → x₁ ≡ x₂ → SD._≈_ sdᵗ (f₁ x₁) (f₂ x₂))

gen-bool₁ p₁ _  {true}  refl′ = p₁
gen-bool₁ _  p₂ {false} refl′ = p₂

gen-bool₂ : {sdᵗ : SD 0ℓ 0ℓ} → {f₁ f₂ : Bool → SD.Carrier sdᵗ} →
  ¬ (SD._≈_ sdᵗ (f₁ true) (f₂ true)) →
  ¬ (({x₁ x₂} : Bool) → x₁ ≡ x₂ → SD._≈_ sdᵗ (f₁ x₁) (f₂ x₂))

gen-bool₂ p n = p (n {true} refl′)

gen-bool₃ : {sdᵗ : SD 0ℓ 0ℓ} → {f₁ f₂ : Bool → SD.Carrier sdᵗ} →
  ¬ (SD._≈_ sdᵗ (f₁ false) (f₂ false)) →
  ¬ (({x₁ x₂} : Bool) → x₁ ≡ x₂ → SD._≈_ sdᵗ (f₁ x₁) (f₂ x₂))

gen-bool₃ p n = p (n {false} refl′)

≟-bool : (dsdᵗ : DSD 0ℓ 0ℓ) → (f₁ f₂ : Bool → Car dsdᵗ) →
  Dec ({x₁ x₂ : Bool} → x₁ ≡ x₂ → _≈_ dsdᵗ (f₁ x₁) (f₂ x₂))

≟-bool dsdᵗ f₁ f₂
  with _≟_ dsdᵗ (f₁ true) (f₂ true) | _≟_ dsdᵗ (f₁ false) (f₂ false)

... | yes p₁ | yes p₂ = yes (gen-bool₁ {setoid dsdᵗ} {f₁} {f₂} p₁ p₂)
... | yes p₁ | no  p₂ = no  (gen-bool₃ {setoid dsdᵗ} {f₁} {f₂} p₂)
... | no  p₁ | yes p₂ = no  (gen-bool₂ {setoid dsdᵗ} {f₁} {f₂} p₁)
... | no  p₁ | no  p₂ = no  (gen-bool₂ {setoid dsdᵗ} {f₁} {f₂} p₁)

bool-wrapper : {dsdᵗ : DSD 0ℓ 0ℓ} → Wrapper bool-dsd dsdᵗ
bool-wrapper {dsdᵗ} = record {
    decide-eq = ≟-bool dsdᵗ ;
    congruence = λ { {f} {x₁} {x₂} refl′ → DSD.refl dsdᵗ }
  }
