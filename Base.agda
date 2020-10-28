module Base where

open import Agda.Primitive using (Level) renaming (lzero to 0ℓ)

open import Data.Bool using (true ; false ; not)
open import Data.Bool.Properties using (not-¬)

open import Function using (_$_ ; _∘_ ; it)
open import Function.Equality using (_⟨$⟩_ ; _⟶_) renaming (cong to Π-cong)

open import Relation.Binary.Bundles using () renaming (DecSetoid to DS)
open import Relation.Binary.Properties.Setoid using (≉-sym ; ≉-respʳ ; ≉-respˡ)

open import Relation.Binary.PropositionalEquality
  using (inspect ; [_]) renaming (cong to cong′ ; refl to refl′)

open import Relation.Nullary using (_because_ ; does ; ofʸ ; ofⁿ)
open import Relation.Nullary.Decidable using (dec-true ; dec-false)
open import Relation.Nullary.Negation using (contradiction)

open import SMT using (Holds ; holds ; falseᶠ ; equᶠ ; notᶠ)

-- LFSC: arrow, apply - replaced by Agda function types and application

postulate
  -- LFSC: trust
  trust-f : Holds falseᶠ
  -- LFSC: trust_f
  trust : ∀ f → Holds f

-- LFSC: refl
refl : {{s : DS 0ℓ 0ℓ}} → (x : DS.Carrier s) → Holds (equᶠ x x)
refl x with DS._≟_ it x x | inspect (DS._≟_ it x) x
... | true  because ofʸ _ | [ eq ] = holds _ (cong′ does eq)
... | false because ofⁿ p | _      = contradiction (DS.refl it {x}) p

-- LFSC: symm
sym : {{s : DS 0ℓ 0ℓ}} → {x₁ x₂ : DS.Carrier s} → Holds (equᶠ x₁ x₂) → Holds (equᶠ x₂ x₁)
sym (holds (equᶠ x₁ x₂) _) with DS._≟_ it x₁ x₂
... | true because ofʸ p = holds _ $ dec-true (DS._≟_ it x₂ x₁) (DS.sym it p)

-- LFSC: trans
trans : {{s : DS 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DS.Carrier s} →
  Holds (equᶠ x₁ x₂) → Holds (equᶠ x₂ x₃) → Holds (equᶠ x₁ x₃)

trans (holds (equᶠ x₁ x₂) _) (holds (equᶠ x₂ x₃) _) with DS._≟_ it x₁ x₂ | DS._≟_ it x₂ x₃

... | true because ofʸ p₁ | true because ofʸ p₂ =
  holds _ $ dec-true (DS._≟_ it x₁ x₃) (DS.trans it p₁ p₂)

-- LFSC: negsymm
¬-sym : {{s : DS 0ℓ 0ℓ}} → {x₁ x₂ : DS.Carrier s} →
  Holds (notᶠ (equᶠ x₁ x₂)) → Holds (notᶠ (equᶠ x₂ x₁))

¬-sym (holds (notᶠ (equᶠ x₁ x₂)) h) with DS._≟_ it x₁ x₂

... | false because ofⁿ p =
  let s′ = DS.setoid it in
  holds _ $ cong′ not $ dec-false (DS._≟_ it x₂ x₁) (≉-sym s′ p)

-- LFSC: negtrans1
¬-trans₁ : {{s : DS 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DS.Carrier s} →
  Holds (notᶠ (equᶠ x₁ x₂)) → Holds (equᶠ x₂ x₃) → Holds (notᶠ (equᶠ x₁ x₃))

¬-trans₁ (holds (notᶠ (equᶠ x₁ x₂)) _) (holds (equᶠ x₂ x₃) _) with DS._≟_ it x₁ x₂ | DS._≟_ it x₂ x₃

... | false because ofⁿ p₁ | true because ofʸ p₂ =
  let s′ = DS.setoid it in
  holds _ $ cong′ not $ dec-false (DS._≟_ it x₁ x₃) (≉-respʳ s′ p₂ p₁)

-- LFSC: negtrans2
¬-trans₂ : {{s : DS 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DS.Carrier s} →
  Holds (equᶠ x₁ x₂) → Holds (notᶠ (equᶠ x₂ x₃)) → Holds (notᶠ (equᶠ x₁ x₃))

¬-trans₂ (holds (equᶠ x₁ x₂) _) (holds (notᶠ (equᶠ x₂ x₃)) _) with DS._≟_ it x₁ x₂ | DS._≟_ it x₂ x₃

... | true because ofʸ p₁ | false because ofⁿ p₂ =
  let s′ = DS.setoid it in
  holds _ $ cong′ not $ dec-false (DS._≟_ it x₁ x₃) (≉-respˡ s′ (DS.sym it p₁) p₂)

-- LFSC: cong
-- XXX - simplified for now, no function equality
cong : {{s₁ s₂ : DS 0ℓ 0ℓ}} → {{Π : DS.setoid s₁ ⟶ DS.setoid s₂}} → {x₁ x₂ : DS.Carrier s₁} →
  Holds (equᶠ x₁ x₂) → Holds (equᶠ (Π ⟨$⟩ x₁) (Π ⟨$⟩ x₂))

cong (holds (equᶠ x₁ x₂) _) with DS._≟_ it x₁ x₂
... | true because ofʸ p = holds _ $ dec-true (DS._≟_ it (it ⟨$⟩ x₁) (it ⟨$⟩ x₂)) (Π-cong it p)
