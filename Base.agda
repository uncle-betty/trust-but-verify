module Base where

open import Agda.Primitive using (Level) renaming (lzero to 0ℓ)

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Bool.Properties using (not-¬) renaming (≡-setoid to bool-sd)

open import Function using (_$_ ; _∘_ ; it)
open import Function.Equality using (_⟨$⟩_ ; _⟶_ ; _⇨_) renaming (cong to Π-cong)

open import Relation.Binary using (Decidable)
open import Relation.Binary.Bundles using () renaming (DecSetoid to DSD ; Setoid to SD)
open import Relation.Binary.Properties.Setoid using (≉-sym ; ≉-respʳ ; ≉-respˡ)

open import Relation.Binary.PropositionalEquality
  using (inspect ; [_] ; _≡_) renaming (cong to cong′ ; refl to refl′)

open import Relation.Nullary using (Dec ; _because_ ; does ; ofʸ ; ofⁿ ; yes ; no ; ¬_)
open import Relation.Nullary.Decidable using (dec-true ; dec-false)
open import Relation.Nullary.Negation using (contradiction)

open import SMT using (Holds ; holds ; falseᶠ ; equᶠ ; notᶠ ; prove)

-- LFSC: arrow, apply - replaced by Agda function types and application

postulate
  -- LFSC: trust
  trust-f : Holds falseᶠ
  -- LFSC: trust_f
  trust : ∀ f → Holds f

-- LFSC: refl
refl : {{dsd : DSD 0ℓ 0ℓ}} → (x : DSD.Carrier dsd) → Holds (equᶠ x x)
refl x with DSD._≟_ it x x | inspect (DSD._≟_ it x) x
... | true  because ofʸ _ | [ eq ] = holds _ (cong′ does eq)
... | false because ofⁿ p | _      = contradiction (DSD.refl it {x}) p

-- LFSC: symm
sym : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ : DSD.Carrier dsd} → Holds (equᶠ x₁ x₂) → Holds (equᶠ x₂ x₁)
sym (holds (equᶠ x₁ x₂) _) with DSD._≟_ it x₁ x₂
... | true because ofʸ p = holds _ $ dec-true (DSD._≟_ it x₂ x₁) (DSD.sym it p)

-- LFSC: trans
trans : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DSD.Carrier dsd} →
  Holds (equᶠ x₁ x₂) → Holds (equᶠ x₂ x₃) → Holds (equᶠ x₁ x₃)

trans (holds (equᶠ x₁ x₂) _) (holds (equᶠ x₂ x₃) _) with DSD._≟_ it x₁ x₂ | DSD._≟_ it x₂ x₃
... | true because ofʸ p₁ | true because ofʸ p₂ =
  holds _ $ dec-true (DSD._≟_ it x₁ x₃) (DSD.trans it p₁ p₂)

-- LFSC: negsymm
¬-sym : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ : DSD.Carrier dsd} →
  Holds (notᶠ (equᶠ x₁ x₂)) → Holds (notᶠ (equᶠ x₂ x₁))

¬-sym (holds (notᶠ (equᶠ x₁ x₂)) h) with DSD._≟_ it x₁ x₂
... | false because ofⁿ p =
  holds _ $ cong′ not $ dec-false (DSD._≟_ it x₂ x₁) (≉-sym (DSD.setoid it) p)

-- LFSC: negtrans1
¬-trans₁ : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DSD.Carrier dsd} →
  Holds (notᶠ (equᶠ x₁ x₂)) → Holds (equᶠ x₂ x₃) → Holds (notᶠ (equᶠ x₁ x₃))

¬-trans₁ (holds (notᶠ (equᶠ x₁ x₂)) _) (holds (equᶠ x₂ x₃) _)
  with DSD._≟_ it x₁ x₂ | DSD._≟_ it x₂ x₃

... | false because ofⁿ p₁ | true because ofʸ p₂ =
  holds _ $ cong′ not $ dec-false (DSD._≟_ it x₁ x₃) (≉-respʳ (DSD.setoid it) p₂ p₁)

-- LFSC: negtrans2
¬-trans₂ : {{dsd : DSD 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DSD.Carrier dsd} →
  Holds (equᶠ x₁ x₂) → Holds (notᶠ (equᶠ x₂ x₃)) → Holds (notᶠ (equᶠ x₁ x₃))

¬-trans₂ (holds (equᶠ x₁ x₂) _) (holds (notᶠ (equᶠ x₂ x₃)) _)
  with DSD._≟_ it x₁ x₂ | DSD._≟_ it x₂ x₃

... | true because ofʸ p₁ | false because ofⁿ p₂ =
  holds _ $ cong′ not $ dec-false (DSD._≟_ it x₁ x₃) (≉-respˡ (DSD.setoid it) (DSD.sym it p₁) p₂)

build-func-dsd : (dsdᶠ : DSD 0ℓ 0ℓ) → (dsdᵗ : DSD 0ℓ 0ℓ) →
  (dec : Decidable (SD._≈_ (DSD.setoid dsdᶠ ⇨ (DSD.setoid dsdᵗ)))) → DSD 0ℓ 0ℓ
build-func-dsd dsdᶠ dsdᵗ dec =
  let func-sd = DSD.setoid dsdᶠ ⇨ (DSD.setoid dsdᵗ) in
  record {
      Carrier          = SD.Carrier func-sd ;
      _≈_              = SD._≈_     func-sd ;
      isDecEquivalence = record {
          isEquivalence = SD.isEquivalence func-sd ;
          _≟_           = dec
        }
    }

equᶠ-≈ : {dsd : DSD 0ℓ 0ℓ} → {x y : DSD.Carrier dsd} → Holds (equᶠ {{dsd}} x y) → DSD._≈_ dsd x y
equᶠ-≈ {dsd} {x} {y} (holds _ h) = prove (equᶠ {{dsd}} x y) h

≈-does : {dsd : DSD 0ℓ 0ℓ} → {x y : DSD.Carrier dsd} → DSD._≈_ dsd x y →
  does (DSD._≟_ dsd x y) ≡ true

≈-does {dsd} {x} {y} p with DSD._≟_ dsd x y
... | true  because ofʸ _  = refl′
... | false because ofⁿ p′ = contradiction p p′

-- LFSC: cong
cong :
  {{dsdᶠ dsdᵗ : DSD 0ℓ 0ℓ}} →
  {{Π₁ Π₂ : DSD.setoid dsdᶠ ⟶ DSD.setoid dsdᵗ}} →
  {x₁ x₂ : DSD.Carrier dsdᶠ} →
  {{dec : _}} → -- Decidable (SD._≈_ (DSD.setoid dsdᶠ ⇨ DSD.setoid dsdᵗ))
  Holds (equᶠ {{build-func-dsd dsdᶠ dsdᵗ dec}} Π₁ Π₂) →
  Holds (equᶠ {{dsdᶠ}} x₁ x₂) →
  Holds (equᶠ {{dsdᵗ}} (Π₁ ⟨$⟩ x₁) (Π₂ ⟨$⟩ x₂))

cong h₁ h₂ = holds _ $ ≈-does {it} $ equᶠ-≈ h₁ (equᶠ-≈ h₂)

gen-bool-func₁ : {dsdᵗ : SD 0ℓ 0ℓ} → {Π₁ Π₂ : bool-sd ⟶ dsdᵗ} →
  SD._≈_ dsdᵗ (Π₁ ⟨$⟩ true)  (Π₂ ⟨$⟩ true)  →
  SD._≈_ dsdᵗ (Π₁ ⟨$⟩ false) (Π₂ ⟨$⟩ false) →
  (({x₁ x₂} : Bool) → x₁ ≡ x₂ → SD._≈_ dsdᵗ (Π₁ ⟨$⟩ x₁) (Π₂ ⟨$⟩ x₂))

gen-bool-func₁ p₁ _  {true}  refl′ = p₁
gen-bool-func₁ _  p₂ {false} refl′ = p₂

gen-bool-func₂ : {dsdᵗ : SD 0ℓ 0ℓ} → {Π₁ Π₂ : bool-sd ⟶ dsdᵗ} →
  ¬ (SD._≈_ dsdᵗ (Π₁ ⟨$⟩ true)  (Π₂ ⟨$⟩ true))  →
  ¬ (({x₁ x₂} : Bool) → x₁ ≡ x₂ → SD._≈_ dsdᵗ (Π₁ ⟨$⟩ x₁) (Π₂ ⟨$⟩ x₂))

gen-bool-func₂ {dsdᵗ} {Π₁} {Π₂} p n = p (n {true} refl′)

gen-bool-func₃ : {dsdᵗ : SD 0ℓ 0ℓ} → {Π₁ Π₂ : bool-sd ⟶ dsdᵗ} →
  ¬ (SD._≈_ dsdᵗ (Π₁ ⟨$⟩ false)  (Π₂ ⟨$⟩ false))  →
  ¬ (({x₁ x₂} : Bool) → x₁ ≡ x₂ → SD._≈_ dsdᵗ (Π₁ ⟨$⟩ x₁) (Π₂ ⟨$⟩ x₂))

gen-bool-func₃ {dsdᵗ} {Π₁} {Π₂} p n = p (n {false} refl′)

≟-bool-func : (dsdᵗ : DSD 0ℓ 0ℓ) → (Π₁ Π₂ : bool-sd ⟶ DSD.setoid dsdᵗ) →
  Dec (SD._≈_ (bool-sd ⇨ (DSD.setoid dsdᵗ)) Π₁ Π₂)

≟-bool-func dsdᵗ Π₁ Π₂
  with DSD._≟_ dsdᵗ (Π₁ ⟨$⟩ true) (Π₂ ⟨$⟩ true) | DSD._≟_ dsdᵗ (Π₁ ⟨$⟩ false) (Π₂ ⟨$⟩ false)

... | yes p₁ | yes p₂ = yes (gen-bool-func₁ {DSD.setoid dsdᵗ} {Π₁} {Π₂} p₁ p₂)
... | yes p₁ | no  p₂ = no  (gen-bool-func₃ {DSD.setoid dsdᵗ} {Π₁} {Π₂} p₂)
... | no  p₁ | yes p₂ = no  (gen-bool-func₂ {DSD.setoid dsdᵗ} {Π₁} {Π₂} p₁)
... | no  p₁ | no  p₂ = no  (gen-bool-func₂ {DSD.setoid dsdᵗ} {Π₁} {Π₂} p₁)
