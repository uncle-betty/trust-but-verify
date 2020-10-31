module Congruence where

open import Function.Equality using (_⟶_)

open import Relation.Binary.PropositionalEquality using () renaming (cong to cong-pe)

module _ where
  open import Data.Bool using (Bool)
  open import Data.Bool.Properties using () renaming (≡-setoid to ≡-setoid-bool)

  Π-≡-bool-bool : {f : Bool → Bool} → ≡-setoid-bool ⟶ ≡-setoid-bool
  Π-≡-bool-bool {f} = record
    {
      _⟨$⟩_ = f ;
      cong = cong-pe f
    }
