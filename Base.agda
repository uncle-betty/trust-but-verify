module Base where

open import Agda.Primitive using (Level) renaming (lzero to 0ℓ)

open import Data.Bool using (true ; false ; not)
open import Data.Bool.Properties using (not-¬)

open import Function using (_$_ ; _∘_ ; it)

open import Relation.Binary.Bundles using (DecSetoid)
open import Relation.Binary.Properties.Setoid using (≉-sym ; ≉-respʳ ; ≉-respˡ)

open import Relation.Binary.PropositionalEquality
  using (inspect ; [_]) renaming (cong to cong′ ; refl to refl′)

open import Relation.Nullary using (_because_ ; does ; ofʸ ; ofⁿ)
open import Relation.Nullary.Decidable using (dec-true ; dec-false)
open import Relation.Nullary.Negation using (contradiction)

open import SMT using (Holds ; holds ; falseᶠ ; equᶠ ; notᶠ)

postulate
  -- LFSC: trust
  trust-f : Holds falseᶠ
  -- LFSC: trust_f
  trust : ∀ f → Holds f

-- LFSC: refl
refl : {{s : DecSetoid 0ℓ 0ℓ}} → {x : DecSetoid.Carrier s} → Holds (equᶠ x x)
refl {x} with DecSetoid._≟_ it x x | inspect (DecSetoid._≟_ it x) x
... | true  because ofʸ _ | [ eq ] = holds _ (cong′ does eq)
... | false because ofⁿ p | _      = contradiction (DecSetoid.refl it {x}) p

-- LFSC: symm
sym : {{s : DecSetoid 0ℓ 0ℓ}} → {x₁ x₂ : DecSetoid.Carrier s} →
  Holds (equᶠ x₁ x₂) → Holds (equᶠ x₂ x₁)

sym (holds (equᶠ x₁ x₂) _) with DecSetoid._≟_ it x₁ x₂
... | true because ofʸ p = holds _ $ dec-true (DecSetoid._≟_ it x₂ x₁) (DecSetoid.sym it p)

-- LFSC: trans
trans : {{s : DecSetoid 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DecSetoid.Carrier s} →
  Holds (equᶠ x₁ x₂) → Holds (equᶠ x₂ x₃) → Holds (equᶠ x₁ x₃)

trans (holds (equᶠ x₁ x₂) _) (holds (equᶠ x₂ x₃) _)
  with DecSetoid._≟_ it x₁ x₂ | DecSetoid._≟_ it x₂ x₃

... | true because ofʸ p₁ | true because ofʸ p₂ =
  holds _ $ dec-true (DecSetoid._≟_ it x₁ x₃) (DecSetoid.trans it p₁ p₂)

-- LFSC: negsymm
¬-sym : {{s : DecSetoid 0ℓ 0ℓ}} → {x₁ x₂ : DecSetoid.Carrier s} →
  Holds (notᶠ (equᶠ x₁ x₂)) → Holds (notᶠ (equᶠ x₂ x₁))

¬-sym (holds (notᶠ (equᶠ x₁ x₂)) h) with DecSetoid._≟_ it x₁ x₂

... | false because ofⁿ p =
  let s′ = DecSetoid.setoid it in
  holds _ $ cong′ not $ dec-false (DecSetoid._≟_ it x₂ x₁) (≉-sym s′ p)

-- LFSC: negtrans1
¬-trans₁ : {{s : DecSetoid 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DecSetoid.Carrier s} →
  Holds (notᶠ (equᶠ x₁ x₂)) → Holds (equᶠ x₂ x₃) → Holds (notᶠ (equᶠ x₁ x₃))

¬-trans₁ (holds (notᶠ (equᶠ x₁ x₂)) _) (holds (equᶠ x₂ x₃) _)
  with DecSetoid._≟_ it x₁ x₂ | DecSetoid._≟_ it x₂ x₃

... | false because ofⁿ p₁ | true because ofʸ p₂ =
  let s′ = DecSetoid.setoid it in
  holds _ $ cong′ not $ dec-false (DecSetoid._≟_ it x₁ x₃) (≉-respʳ s′ p₂ p₁)

-- LFSC: negtrans2
¬-trans₂ : {{s : DecSetoid 0ℓ 0ℓ}} → {x₁ x₂ x₃ : DecSetoid.Carrier s} →
  Holds (equᶠ x₁ x₂) → Holds (notᶠ (equᶠ x₂ x₃)) → Holds (notᶠ (equᶠ x₁ x₃))

¬-trans₂ (holds (equᶠ x₁ x₂) _) (holds (notᶠ (equᶠ x₂ x₃)) _)
  with DecSetoid._≟_ it x₁ x₂ | DecSetoid._≟_ it x₂ x₃

... | true because ofʸ p₁ | false because ofⁿ p₂ =
  let s′ = DecSetoid.setoid it in
  holds _ $ cong′ not $ dec-false (DecSetoid._≟_ it x₁ x₃) (≉-respˡ s′ (DecSetoid.sym it p₁) p₂)
