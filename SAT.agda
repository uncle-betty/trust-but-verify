module SAT where

open import Agda.Primitive using (Level) renaming (lzero to 0ℓ ; lsuc to +ℓ)

open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; T ; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Maybe using (just ; nothing ; is-just)
open import Data.Nat using (ℕ ; _<_)
open import Data.Nat.Properties using (<-trans) renaming (<-strictTotalOrder to <-STO)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)

open import Function using (_∘_ ; id)

open import Relation.Binary
  using (Transitive ; Trichotomous ; tri< ; tri≈ ; tri>)
  renaming (StrictTotalOrder to STO; IsStrictTotalOrder to ISTO)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; cong ; subst ; inspect ; [_])

open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Relation.Nullary using (Dec ; yes ; no ; _because_ ; does ; proof ; ofʸ ; ofⁿ ; ¬_)
open import Relation.Nullary.Negation using (contradiction)

data Oper : Set

-- LFSC: var
data Var : Set where
  var : ℕ → Var

-- LFSC: lit, pos, neg
data Lit : Set where
  pos : Var → Lit
  neg : Var → Lit

-- LFSC: clause, cln, clc
Clause = List Lit
Clause⁺ = List (Lit ⊎ Oper)

-- LFSC: concat_cl, clr
data Oper where
  join : Clause⁺ → Oper
  skip : Lit → Oper

-- LFSC: cnf, cnfn, cnfc
CNF = List Clause

not-t⇒f : ∀ {x} → not x ≡ true → x ≡ false
not-t⇒f {true}  ()
not-t⇒f {false} _  = refl

f⇒not-t : ∀ {x} → x ≡ false → not x ≡ true
f⇒not-t {true}  ()
f⇒not-t {false} _  = refl

not-f⇒t : ∀ {x} → not x ≡ false → x ≡ true
not-f⇒t {true}  _  = refl
not-f⇒t {false} ()

t⇒not-f : ∀ {x} → x ≡ true → not x ≡ false
t⇒not-f {true}  _  = refl
t⇒not-f {false} ()

ℕ-comp = ISTO.compare (STO.isStrictTotalOrder <-STO)

data Var-< : Var → Var → Set where
  v<v : ∀ {m n} → m < n → Var-< (var m) (var n)

var-<-trans : Transitive Var-<
var-<-trans {var m} {var n} {var o} (v<v m<n) (v<v n<o) = v<v (<-trans m<n n<o)

var-≡ : ∀ {m n} → var m ≡ var n → m ≡ n
var-≡ refl = refl

var-< : ∀ {m n} → Var-< (var m) (var n) → m < n
var-< (v<v p) = p

var-comp : Trichotomous _≡_ Var-<
var-comp (var m) (var n) with ℕ-comp m n
... | tri< p₁ p₂ p₃ = tri< (v<v p₁)     (p₂ ∘ var-≡)  (p₃ ∘ var-<)
... | tri≈ p₁ p₂ p₃ = tri≈ (p₁ ∘ var-<) (cong var p₂) (p₃ ∘ var-<)
... | tri> p₁ p₂ p₃ = tri> (p₁ ∘ var-<) (p₂ ∘ var-≡)  (v<v p₃)

var-<-ISTO : ISTO _≡_ Var-<
var-<-ISTO = record { isEquivalence = isEquivalence ; trans = var-<-trans ; compare = var-comp }

var-<-STO : STO 0ℓ 0ℓ 0ℓ
var-<-STO = record { Carrier = Var ; _≈_ = _≡_ ; _<_ = Var-< ; isStrictTotalOrder = var-<-ISTO }

import Data.Tree.AVL.Map var-<-STO as M using (Map ; empty ; insert ; lookup)
import AVL var-<-STO Bool as AM using (avl-insed ; avl-other)

map-insed : ∀ v (b : Bool) m → (M.lookup v (M.insert v b m)) ≡ just b
map-insed v b m = AM.avl-insed v b m

map-other : ∀ v′ v (b : Bool) m → v′ ≢ v → (M.lookup v′ (M.insert v b m)) ≡ M.lookup v′ m
map-other v′ v b m = AM.avl-other v′ v b m

Env = M.Map Bool
ε = M.empty

module _ (env : Env) where
  data Lit-< : Lit → Lit → Set where
    n<p : ∀ {x y} →             Lit-< (neg x) (pos y)
    n<n : ∀ {x y} → Var-< x y → Lit-< (neg x) (neg y)
    p<p : ∀ {x y} → Var-< x y → Lit-< (pos x) (pos y)

  lit-<-trans : Transitive Lit-<
  lit-<-trans {pos x} {pos y} {pos z} (p<p x<y) (p<p y<z) = p<p (var-<-trans x<y y<z)
  lit-<-trans {neg x} {_}     {pos z} _         _         = n<p
  lit-<-trans {neg x} {neg y} {neg z} (n<n x<y) (n<n y<z) = n<n (var-<-trans x<y y<z)

  pos-≡ : ∀ {x y} → pos x ≡ pos y → x ≡ y
  pos-≡ refl = refl

  pos-< : ∀ {x y} → Lit-< (pos x) (pos y) → Var-< x y
  pos-< (p<p p) = p

  neg-≡ : ∀ {x y} → neg x ≡ neg y → x ≡ y
  neg-≡ refl = refl

  neg-< : ∀ {x y} → Lit-< (neg x) (neg y) → Var-< x y
  neg-< (n<n p) = p

  lit-comp : Trichotomous _≡_ Lit-<
  lit-comp (pos x) (pos y) with var-comp x y
  ... | tri< p₁ p₂   p₃ = tri< (p<p p₁)     (p₂ ∘ pos-≡) (p₃ ∘ pos-<)
  ... | tri≈ p₁ refl p₃ = tri≈ (p₁ ∘ pos-<) refl         (p₃ ∘ pos-<)
  ... | tri> p₁ p₂   p₃ = tri> (p₁ ∘ pos-<) (p₂ ∘ pos-≡) (p<p p₃)

  lit-comp (pos x) (neg y) = tri> (λ ()) (λ ()) n<p
  lit-comp (neg x) (pos y) = tri< n<p    (λ ()) (λ ())

  lit-comp (neg x) (neg y) with var-comp x y
  ... | tri< p₁ p₂   p₃ = tri< (n<n p₁)     (p₂ ∘ neg-≡) (p₃ ∘ neg-<)
  ... | tri≈ p₁ refl p₃ = tri≈ (p₁ ∘ neg-<) refl         (p₃ ∘ neg-<)
  ... | tri> p₁ p₂   p₃ = tri> (p₁ ∘ neg-<) (p₂ ∘ neg-≡) (n<n p₃)

  lit-<-ISTO : ISTO _≡_ Lit-<
  lit-<-ISTO = record { isEquivalence = isEquivalence ; trans = lit-<-trans ; compare = lit-comp }

  lit-<-STO : STO 0ℓ 0ℓ 0ℓ
  lit-<-STO = record { Carrier = Lit ; _≈_ = _≡_ ; _<_ = Lit-< ; isStrictTotalOrder = lit-<-ISTO }

  dec-≡ˡ : (l₁ l₂ : Lit) → Dec (l₁ ≡ l₂)
  dec-≡ˡ l₁ l₂ with lit-comp l₁ l₂
  ... | tri< _ p _ = false because ofⁿ p
  ... | tri≈ _ p _ = true  because ofʸ p
  ... | tri> _ p _ = false because ofⁿ p

  open import Data.Tree.AVL.Sets lit-<-STO using (⟨Set⟩ ; empty ; insert ; _∈?_)
  import AVL lit-<-STO ⊤ as AS using (avl-insed ; avl-other)

  set-insed : ∀ l s → (l ∈? (insert l s)) ≡ true
  set-insed l s = cong is-just (AS.avl-insed l tt s)

  set-other : ∀ l′ l s → l′ ≢ l → (l′ ∈? (insert l s)) ≡ (l′ ∈? s)
  set-other l′ l s l′≢l = cong is-just (AS.avl-other l′ l tt s l′≢l)

  set-≡ : ∀ s₁ s₂ → Set
  set-≡ s₁ s₂ = ∀ l′ → (l′ ∈? s₁) ≡ (l′ ∈? s₂)

  set-add-≡ : ∀ {s₁ s₂} l → set-≡ s₁ s₂ → (∀ l′ → (l′ ∈? (insert l s₁)) ≡ (l′ ∈? (insert l s₂)))

  set-add-≡ {s₁} {s₂} l p l′ with dec-≡ˡ l′ l
  ... | yes p′ rewrite p′ | set-insed l s₁ | set-insed l s₂ = refl
  ... | no  p′ rewrite set-other l′ l s₁ p′ | set-other l′ l s₂ p′ = p l′

  set-add-com : ∀ l₁ l₂ s l′ → (l′ ∈? (insert l₁ (insert l₂ s))) ≡ (l′ ∈? (insert l₂ (insert l₁ s)))
  set-add-com l₁ l₂ s l′ with dec-≡ˡ l₁ l₂
  ... | yes p₁ rewrite p₁ = refl
  ... | no  p₁ with dec-≡ˡ l′ l₁

  ... | yes p₂
    rewrite p₂
          | set-insed l₁ (insert l₂ s)
          | set-other l₁ l₂ (insert l₁ s) p₁
          | set-insed l₁ s
    = refl

  ... | no  p₂ with dec-≡ˡ l′ l₂

  ... | yes p₃
    rewrite p₃
          | set-insed l₂ (insert l₁ s)
          | set-other l₂ l₁ (insert l₂ s) (≢-sym p₁)
          | set-insed l₂ s
    = refl

  ... | no  p₃
    rewrite set-other l′ l₁ (insert l₂ s) p₂
          | set-other l′ l₂ (insert l₁ s) p₃
          | set-other l′ l₂ s p₃
          | set-other l′ l₁ s p₂
    = refl

  assignᵛ : Var → Bool → Env
  assignᵛ v b = M.insert v b env

  evalᵛ : Var → Bool
  evalᵛ v with M.lookup v env
  ... | just b  = b
  ... | nothing = false

  propᵛ : Var → Set
  propᵛ = T ∘ evalᵛ

  proveᵛ : ∀ {v} → evalᵛ v ≡ true → propᵛ v
  proveᵛ p = subst id (sym (cong T p)) tt

  proveᵛ-¬ : ∀ {v} → evalᵛ v ≡ false → ¬ propᵛ v
  proveᵛ-¬ p r = subst id (cong T p) r

  evalˡ : Lit → Bool
  evalˡ (pos v′) = evalᵛ v′
  evalˡ (neg v′) = not (evalᵛ v′)

  propˡ : Lit → Set
  propˡ (pos v′) = propᵛ v′
  propˡ (neg v′) = ¬ (propᵛ v′)

  -- XXX - without {v′} the constraint solver fails
  proveˡ : ∀ {l} → evalˡ l ≡ true → propˡ l
  proveˡ {pos v′} p = proveᵛ {v′} p
  proveˡ {neg v′} p = proveᵛ-¬ {v′} (not-t⇒f p)

  -- XXX - without {v′} the constraint solver fails
  proveˡ-¬ : ∀ {l} → evalˡ l ≡ false → ¬ propˡ l
  proveˡ-¬ {pos v′} p r = contradiction r (proveᵛ-¬ {v′} p)
  proveˡ-¬ {neg v′} p r = contradiction (proveᵛ {v′} (not-f⇒t p)) r

  evalᶜ : Clause → Bool
  evalᶜ []        = false
  evalᶜ (l′ ∷ ls) = evalˡ l′ ∨ evalᶜ ls

  propᶜ : Clause → Set
  propᶜ []        = ⊥
  propᶜ (l′ ∷ ls) = propˡ l′ ⊎ propᶜ ls

  proveᶜ : ∀ {c} → evalᶜ c ≡ true → propᶜ c
  proveᶜ {l′ ∷ ls} p with evalˡ l′ | inspect evalˡ l′
  ... | true  | [ eq ] = inj₁ (proveˡ {l′} eq)
  ... | false | [ eq ] = inj₂ (proveᶜ p)

  proveᶜ-¬ : ∀ {c} → evalᶜ c ≡ false → ¬ propᶜ c
  proveᶜ-¬ {[]}      _  r = ⊥-elim r

  proveᶜ-¬ {l′ ∷ ls} p  r with evalˡ l′ | inspect evalˡ l′
  proveᶜ-¬ {l′ ∷ ls} () _         | true  | _
  proveᶜ-¬ {l′ ∷ ls} _  (inj₁ r′) | false | [ eq ] = contradiction r′ (proveˡ-¬ {l′} eq)
  proveᶜ-¬ {l′ ∷ ls} p  (inj₂ r′) | false | _      = contradiction r′ (proveᶜ-¬ p)

  eval⁺ : Clause⁺ → ⟨Set⟩ → Bool
  eval⁺ []                    s = false
  eval⁺ (inj₁ l′        ∷ xs) s = if l′ ∈? s then eval⁺ xs s else evalˡ l′ ∨ eval⁺ xs s
  eval⁺ (inj₂ (join c′) ∷ xs) s = eval⁺ c′ s ∨ eval⁺ xs s
  eval⁺ (inj₂ (skip l′) ∷ xs) s = eval⁺ xs (insert l′ s)

  prop⁺ : Clause⁺ → ⟨Set⟩ → Set
  prop⁺ []                    s = ⊥
  prop⁺ (inj₁ l′        ∷ xs) s = if l′ ∈? s then prop⁺ xs s else propˡ l′ ⊎ prop⁺ xs s
  prop⁺ (inj₂ (join c′) ∷ xs) s = prop⁺ c′ s ⊎ prop⁺ xs s
  prop⁺ (inj₂ (skip l′) ∷ xs) s = prop⁺ xs (insert l′ s)

  prove⁺ : ∀ {c s} → eval⁺ c s ≡ true → prop⁺ c s
  prove⁺ {inj₁ l′ ∷ xs} {s} p with l′ ∈? s | evalˡ l′ | inspect evalˡ l′
  ... | true  | _     | _       = prove⁺ {xs} {s} p
  ... | false | true  | [ eq ]  = inj₁ (proveˡ {l′} eq)
  ... | false | false | _       = inj₂ (prove⁺ {xs} {s} p)

  prove⁺ {inj₂ (join c′) ∷ xs} {s} p with eval⁺ c′ s | inspect (eval⁺ c′) s
  ... | true  | [ eq ] = inj₁ (prove⁺ {c′} {s} eq)
  ... | false | _      = inj₂ (prove⁺ {xs} {s} p)

  prove⁺ {inj₂ (skip l′) ∷ xs} {s} p = prove⁺ {xs} {insert l′ s} p

  prove⁺-¬ : ∀ {c s} → eval⁺ c s ≡ false → ¬ prop⁺ c s
  prove⁺-¬ {[]} {s} p r = ⊥-elim r

  prove⁺-¬ {inj₁ l′ ∷ xs} {s} p  r with l′ ∈? s | evalˡ l′ | inspect evalˡ l′

  prove⁺-¬ {inj₁ l′ ∷ xs} {s} p  r         | true  | _     | _      =
    contradiction r (prove⁺-¬ {xs} {s} p)

  prove⁺-¬ {inj₁ l′ ∷ xs} {_} () _         | false | true  | _

  prove⁺-¬ {inj₁ l′ ∷ xs} {_} _  (inj₁ r′) | false | false | [ eq ] =
    contradiction r′ (proveˡ-¬ {l′} eq)

  prove⁺-¬ {inj₁ l′ ∷ xs} {s} p  (inj₂ r′) | false | false | _      =
    contradiction r′ (prove⁺-¬ {xs} {s} p)

  prove⁺-¬ {inj₂ (join c′) ∷ xs} {s} p  r with eval⁺ c′ s | inspect (eval⁺ c′) s
  prove⁺-¬ {inj₂ (join c′) ∷ xs} {_} () _         | true  | _

  prove⁺-¬ {inj₂ (join c′) ∷ xs} {s} _  (inj₁ r′) | false | [ eq ] =
    contradiction r′ (prove⁺-¬ {c′} {s} eq)

  prove⁺-¬ {inj₂ (join c′) ∷ xs} {s} p  (inj₂ r′) | false | _      =
    contradiction r′ (prove⁺-¬ {xs} {s} p)

  prove⁺-¬ {inj₂ (skip l′) ∷ xs} {s} p r = contradiction r (prove⁺-¬ {xs} {insert l′ s} p)

  eval⁺-add-≡ : ∀ {s₁ s₂} c → set-≡ s₁ s₂ → eval⁺ c s₁ ≡ eval⁺ c s₂
  eval⁺-add-≡ [] p = refl

  eval⁺-add-≡ {s₁} {s₂} (inj₁ l′ ∷ xs) p rewrite p l′ with l′ ∈? s₂
  ... | true  = eval⁺-add-≡ {s₁} {s₂} xs p
  ... | false rewrite eval⁺-add-≡ {s₁} {s₂} xs p = refl

  eval⁺-add-≡ {s₁} {s₂} (inj₂ (join c′) ∷ xs) p
    rewrite eval⁺-add-≡ {s₁} {s₂} c′ p | eval⁺-add-≡ {s₁} {s₂} xs p = refl

  eval⁺-add-≡ {s₁} {s₂} (inj₂ (skip l′) ∷ xs) p =
    eval⁺-add-≡ {insert l′ s₁} {insert l′ s₂} xs (set-add-≡ {s₁} {s₂} l′ p)

  eval⁺-add-com : ∀ c l₁ l₂ s →
    eval⁺ c (insert l₁ (insert l₂ s)) ≡ eval⁺ c (insert l₂ (insert l₁ s))

  eval⁺-add-com c l₁ l₂ s =
    eval⁺-add-≡ {insert l₁ (insert l₂ s)} {insert l₂ (insert l₁ s)} c (set-add-com l₁ l₂ s)

  -- LFSC: lit_flip
  flip : Lit → Lit
  flip (pos v) = neg v
  flip (neg v) = pos v

  t≡flip-f : ∀ {l} → evalˡ l ≡ true → evalˡ (flip l) ≡ false
  t≡flip-f {pos v′} p = t⇒not-f p
  t≡flip-f {neg v′} p = not-t⇒f p

  f≡flip-t : ∀ {l} → evalˡ l ≡ false → evalˡ (flip l) ≡ true
  f≡flip-t {pos v′} p = f⇒not-t p
  f≡flip-t {neg v′} p = not-f⇒t p

  ite-same : ∀ {A : Set} b (a : A) → (if b then a else a) ≡ a
  ite-same true  x = refl
  ite-same false x = refl

  resolve : ∀ {l c s} → evalˡ l ≡ true → eval⁺ c s ≡ true → eval⁺ c (insert (flip l) s) ≡ true
  resolve {l} {inj₁ l′ ∷ xs} {s} h₁ h₂ with dec-≡ˡ l′ (flip l)

  resolve {l} {inj₁ l′ ∷ xs} {s} h₁ h₂ | yes p
    rewrite p
          | set-insed (flip l) s
          | t≡flip-f {l} h₁
          | ite-same (flip l ∈? s) (eval⁺ xs s)
    = resolve {l} {xs} {s} h₁ h₂

  resolve {l} {inj₁ l′ ∷ xs} {s} h₁ h₂ | no p rewrite set-other l′ (flip l) s p with l′ ∈? s
  ... | true  = resolve {l} {xs} {s} h₁ h₂
  ... | false with evalˡ l′
  ... | true  = refl
  ... | false = resolve {l} {xs} {s} h₁ h₂

  resolve {l} {inj₂ (join c′) ∷ xs} {s} h₁ h₂ with eval⁺ c′ s | inspect (eval⁺ c′) s
  ... | true  | [ eq ] rewrite resolve {l} {c′} {s} h₁ eq = refl
  ... | false | _      rewrite resolve {l} {xs} {s} h₁ h₂ = ∨-zeroʳ (eval⁺ c′ (insert (flip l) s))

  resolve {l} {inj₂ (skip l′) ∷ xs} {s} h₁ h₂
    rewrite eval⁺-add-com xs l′ (flip l) s = resolve {l} {xs} {insert l′ s} h₁ h₂

  -- LFSC: holds
  data Holdsᶜ : Clause → Set where
    holdsᶜ : (c : Clause) → evalᶜ c ≡ true → Holdsᶜ c

  data Holds⁺ : Clause⁺ → Set where
    holds⁺ : (c : Clause⁺) → eval⁺ c empty ≡ true → Holds⁺ c

  -- LFSC: R
  resolve-r : ∀ {c₁ c₂} → Holds⁺ c₁ → Holds⁺ c₂ → (v : Var) →
    Holds⁺ (inj₂ (join (inj₂ (skip (pos v)) ∷ c₁)) ∷ inj₂ (skip (neg v)) ∷ c₂)

  resolve-r (holds⁺ c₁ p₁) (holds⁺ c₂ p₂) v = holds⁺ _ (help {c₁} {c₂} p₁ p₂ v)

    where
    help : ∀ {c₁ c₂} → eval⁺ c₁ empty ≡ true → eval⁺ c₂ empty ≡ true → (v : Var) →
      eval⁺ (inj₂ (join (inj₂ (skip (pos v)) ∷ c₁)) ∷ inj₂ (skip (neg v)) ∷ c₂) empty ≡ true

    help {c₁} {c₂} h₁ h₂ v with evalᵛ v | inspect evalᵛ v
    ... | true | [ eq ]
      rewrite resolve {pos v} {c₂} {empty} eq h₂
      = ∨-zeroʳ (eval⁺ c₁ (insert (pos v) empty))

    ... | false | [ eq ] rewrite resolve {neg v} {c₁} {empty} (f⇒not-t eq) h₁ = refl

  -- LFSC: Q
  resolve-q : ∀ {c₁ c₂} → Holds⁺ c₁ → Holds⁺ c₂ → (v : Var) →
    Holds⁺ (inj₂ (join (inj₂ (skip (neg v)) ∷ c₁)) ∷ inj₂ (skip (pos v)) ∷ c₂)

  resolve-q (holds⁺ c₁ p₁) (holds⁺ c₂ p₂) v = holds⁺ _ (help {c₁} {c₂} p₁ p₂ v)

    where
    help : ∀ {c₁ c₂} → eval⁺ c₁ empty ≡ true → eval⁺ c₂ empty ≡ true → (v : Var) →
      eval⁺ (inj₂ (join (inj₂ (skip (neg v)) ∷ c₁)) ∷ inj₂ (skip (pos v)) ∷ c₂) empty ≡ true

    help {c₁} {c₂} h₁ h₂ v with evalᵛ v | inspect evalᵛ v
    ... | true  | [ eq ] rewrite resolve {pos v} {c₁} {empty} eq h₁ = refl

    ... | false | [ eq ]
      rewrite resolve {neg v} {c₂} {empty} (f⇒not-t eq) h₂
      = ∨-zeroʳ (eval⁺ c₁ (insert (neg v) empty))

  compl : Clause → Clause⁺
  compl = map inj₁

  -- LFSC: simplify_clause (++ is clause_append)
  simpl : Clause⁺ → ⟨Set⟩ → Clause
  simpl []                   _ = []
  simpl (inj₁ l        ∷ xs) s = if l ∈? s then simpl xs s else l ∷ simpl xs s
  simpl (inj₂ (join c) ∷ xs) s = simpl c s ++ simpl xs s
  simpl (inj₂ (skip l) ∷ xs) s = simpl xs (insert l s)

  expand : ∀ {c} → Holdsᶜ c → Holds⁺ (compl c)
  expand (holdsᶜ c p) = holds⁺ _ (help {c} p)

    where
    help : ∀ {c} → evalᶜ c ≡ true → eval⁺ (compl c) empty ≡ true
    help {l′ ∷ ls} h with evalˡ l′
    ... | true  = refl
    ... | false = help {ls} h

  evalᶜ-++ʳ : ∀ {c₁ c₂} → evalᶜ c₁ ≡ true → evalᶜ (c₁ ++ c₂) ≡ true
  evalᶜ-++ʳ {l′ ∷ ls} {c₂} h with evalˡ l′
  ... | true  = refl
  ... | false = evalᶜ-++ʳ {ls} {c₂} h

  evalᶜ-++ˡ : ∀ {c₁ c₂} → evalᶜ c₂ ≡ true → evalᶜ (c₁ ++ c₂) ≡ true
  evalᶜ-++ˡ {[]}      {c₂} h = h
  evalᶜ-++ˡ {l′ ∷ ls} {c₂} h rewrite evalᶜ-++ˡ {ls} {c₂} h = ∨-zeroʳ (evalˡ l′)

  simpl-sound : ∀ {c s} → eval⁺ c s ≡ true → evalᶜ (simpl c s) ≡ true

  simpl-sound {inj₁ l′ ∷ xs} {s} h with l′ ∈? s
  ... | true  = simpl-sound {xs} {s} h
  ... | false with evalˡ l′
  ... | true  = refl
  ... | false = simpl-sound {xs} {s} h

  simpl-sound {inj₂ (join c′) ∷ xs} {s} h with eval⁺ c′ s | inspect (eval⁺ c′) s
  ... | true  | [ eq ] = evalᶜ-++ʳ {simpl c′ s} {simpl xs s} (simpl-sound {c′} {s} eq)
  ... | false | [ eq ] = evalᶜ-++ˡ {simpl c′ s} {simpl xs s} (simpl-sound {xs} {s} h)

  simpl-sound {inj₂ (skip l′) ∷ xs} {s} h = simpl-sound {xs} {insert l′ s} h

  -- LFSC: satlem_simplify
  mp⁺ : ∀ {c₁ c₂} → Holds⁺ c₁ → (Holdsᶜ (simpl c₁ empty) → Holdsᶜ c₂) → Holdsᶜ c₂
  mp⁺ (holds⁺ c₁ p₁) fn = fn (holdsᶜ (simpl c₁ empty) (simpl-sound {c₁} {empty} p₁))

  -- LFSC: satlem
  mpᶜ : ∀ {c₁ c₂} → Holdsᶜ c₁ → (Holdsᶜ c₁ → Holdsᶜ c₂) → Holdsᶜ c₂
  mpᶜ h₁ fn = fn h₁

  data From (A : Set) (c : Clause⁺) : Set where
    from : (A → Holds⁺ c) → From A c

  resolve-r⁺ : ∀ {c₁ c₂} → {X₁ X₂ : Set} → {{From X₁ c₁}} → {{From X₂ c₂ }} → X₁ → X₂ →
    (v : Var) → Holds⁺ (inj₂ (join (inj₂ (skip (pos v)) ∷ c₁)) ∷ inj₂ (skip (neg v)) ∷ c₂)

  resolve-r⁺ {{from f₁}} {{from f₂}} x₁ x₂ v = resolve-r (f₁ x₁) (f₂ x₂) v

  resolve-q⁺ : ∀ {c₁ c₂} → {X₁ X₂ : Set} → {{From X₁ c₁}} → {{From X₂ c₂ }} → X₁ → X₂ →
    (v : Var) → Holds⁺ (inj₂ (join (inj₂ (skip (neg v)) ∷ c₁)) ∷ inj₂ (skip (pos v)) ∷ c₂)

  resolve-q⁺ {{from f₁}} {{from f₂}} x₁ x₂ v = resolve-q (f₁ x₁) (f₂ x₂) v

  -- LFSC: clause_dedup
  dedup : Clause → ⟨Set⟩ → Clause
  dedup []       _ = []
  dedup (l ∷ ls) s = if l ∈? s then dedup ls s else l ∷ dedup ls (insert l s)

  dedup-≡ : ∀ {s₁ s₂} c → set-≡ s₁ s₂ → dedup c s₁ ≡ dedup c s₂
  dedup-≡ {s₁} {s₂} [] p = refl

  dedup-≡ {s₁} {s₂} (l′ ∷ ls) p
    rewrite p l′
          | dedup-≡ {s₁} {s₂} ls p
          | dedup-≡ {insert l′ s₁} {insert l′ s₂} ls (set-add-≡ {s₁} {s₂} l′ p)
    = refl

  dedup-add-com : ∀ c l₁ l₂ s →
    dedup c (insert l₁ (insert l₂ s)) ≡ dedup c (insert l₂ (insert l₁ s))

  dedup-add-com c l₁ l₂ s =
    dedup-≡ {insert l₁ (insert l₂ s)} {insert l₂ (insert l₁ s)} c (set-add-com l₁ l₂ s)

  dedup-add-f-≡ : ∀ {l c s} → evalˡ l ≡ false → evalᶜ (dedup c s) ≡ true →
    evalᶜ (dedup c (insert l s)) ≡ true

  dedup-add-f-≡ {l} {l′ ∷ ls} {s} h₁ h₂ with dec-≡ˡ l′ l
  dedup-add-f-≡ {l} {l′ ∷ ls} {s} h₁ h₂ | yes p rewrite p | set-insed l s with l ∈? s
  ... | true  = dedup-add-f-≡ {l} {ls} {s} h₁ h₂
  ... | false rewrite h₁ = h₂

  dedup-add-f-≡ {l} {l′ ∷ ls} {s} h₁ h₂ | no p rewrite set-other l′ l s p with l′ ∈? s
  ... | true  = dedup-add-f-≡ {l} {ls} {s} h₁ h₂
  ... | false with evalˡ l′
  ... | true  = refl
  ... | false rewrite dedup-add-com ls l′ l s = dedup-add-f-≡ {l} {ls} {insert l′ s} h₁ h₂

  dedup-sound : ∀ {c} → evalᶜ c ≡ true → evalᶜ (dedup c empty) ≡ true

  dedup-sound {pos v′ ∷ ls} h with evalᵛ v′ | inspect evalᵛ v′
  ... | true  | _      = refl
  ... | false | [ eq ] = dedup-add-f-≡ {pos v′} {ls} {empty} eq (dedup-sound {ls} h)

  dedup-sound {neg v′ ∷ ls} h with evalᵛ v′ | inspect evalᵛ v′
  ... | true  | [ eq ] = dedup-add-f-≡ {neg v′} {ls} {empty} (t⇒not-f eq) (dedup-sound {ls} h)
  ... | false | _      = refl

  -- XXX - cover cnf_holds, cnfn_proof, cnfc_proof

from⁺ : ∀ {env c} → From env (Holds⁺ env c) c
from⁺ = from id

fromᶜ : ∀ {env c} → From env (Holdsᶜ env c) (compl env c)
fromᶜ {env} = from (expand env)
