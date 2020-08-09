module Base where

open import SMT using (Holds ; falseᶠ)

postulate
  -- LFSC: trust
  trust-f : Holds falseᶠ
  -- LFSC: trust_f
  trust : ∀ f → Holds f
