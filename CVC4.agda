module CVC4 where

open import Agda.Primitive using (Level ; lzero ; lsuc)
open import Data.Bool using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; T ; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map ; filter)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; _≟_ ; _<_)
open import Data.Nat.Properties using (<-trans) renaming (<-strictTotalOrder to <-STO)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; id ; _∋_)
open import Relation.Binary using (Transitive ; Trichotomous ; tri< ; tri≈ ; tri>) renaming (StrictTotalOrder to STO; IsStrictTotalOrder to ISTO)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; cong ; cong₂ ; subst ; trans ; inspect ; [_])
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Relation.Nullary using (Dec ; yes ; no ; _because_ ; does ; proof ; ofʸ ; ofⁿ ; ¬_)
open import Relation.Nullary.Negation using (contradiction ; contraposition ; ¬?)

--- Forward declarations ---

data Oper : Set
data Formula : Set

--- SAT ---

data Var : Set where
  var : ℕ → Var

data Lit : Set where
  pos : Var → Lit
  neg : Var → Lit

Clause = List Lit
Clause⁺ = List (Lit ⊎ Oper)

data Oper where
  join : Clause⁺ → Oper
  skip : Lit → Oper

CNF = List Clause

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

var-<-STO : STO lzero lzero  lzero
var-<-STO = record { Carrier = Var ; _≈_ = _≡_ ; _<_ = Var-< ; isStrictTotalOrder = var-<-ISTO }

import Data.Tree.AVL.Map var-<-STO as M using (Map ; empty ; insert ; lookup)

postulate
  map-insed : ∀ v    (b : Bool) m →          (M.lookup v  (M.insert v b m)) ≡ just b
  map-other : ∀ v′ v (b : Bool) m → v′ ≢ v → (M.lookup v′ (M.insert v b m)) ≡ M.lookup v′ m

data Lit-< : Lit → Lit → Set where
  n<p : ∀ {x y} → Lit-< (neg x) (pos y)
  n<n : ∀ {m n} → m < n → Lit-< (neg (var m)) (neg (var n))
  p<p : ∀ {m n} → m < n → Lit-< (pos (var m)) (pos (var n))

lit-<-trans : Transitive Lit-<
lit-<-trans {pos (var i)} {pos (var j)} {pos (var k)} (p<p i<j) (p<p j<k) = p<p (<-trans i<j j<k)
lit-<-trans {neg i}       {_}           {pos k}       _         _         = n<p
lit-<-trans {neg (var i)} {neg (var j)} {neg (var k)} (n<n i<j) (n<n j<k) = n<n (<-trans i<j j<k)

pos-≡ : ∀ {m n} → pos (var m) ≡ pos (var n) → m ≡ n
pos-≡ refl = refl

pos-< : ∀ {m n} → Lit-< (pos (var m)) (pos (var n)) → m < n
pos-< (p<p p) = p

neg-≡ : ∀ {m n} → neg (var m) ≡ neg (var n) → m ≡ n
neg-≡ refl = refl

neg-< : ∀ {m n} → Lit-< (neg (var m)) (neg (var n)) → m < n
neg-< (n<n p) = p

lit-comp : Trichotomous _≡_ Lit-<

lit-comp (pos (var m)) (pos (var n)) with ℕ-comp m n
... | tri< p₁ p₂   p₃ = tri< (p<p p₁)     (p₂ ∘ pos-≡) (p₃ ∘ pos-<)
... | tri≈ p₁ refl p₃ = tri≈ (p₁ ∘ pos-<) refl         (p₃ ∘ pos-<)
... | tri> p₁ p₂   p₃ = tri> (p₁ ∘ pos-<) (p₂ ∘ pos-≡) (p<p p₃)

lit-comp (pos x) (neg y) = tri> (λ ()) (λ ()) n<p
lit-comp (neg x) (pos y) = tri< n<p    (λ ()) (λ ())

lit-comp (neg (var m)) (neg (var n)) with ℕ-comp m n
... | tri< p₁ p₂   p₃ = tri< (n<n p₁)     (p₂ ∘ neg-≡) (p₃ ∘ neg-<)
... | tri≈ p₁ refl p₃ = tri≈ (p₁ ∘ neg-<) refl         (p₃ ∘ neg-<)
... | tri> p₁ p₂   p₃ = tri> (p₁ ∘ neg-<) (p₂ ∘ neg-≡) (n<n p₃)

lit-<-ISTO : ISTO _≡_ Lit-<
lit-<-ISTO = record { isEquivalence = isEquivalence ; trans = lit-<-trans ; compare = lit-comp }

lit-<-STO : STO lzero lzero  lzero
lit-<-STO = record { Carrier = Lit ; _≈_ = _≡_ ; _<_ = Lit-< ; isStrictTotalOrder = lit-<-ISTO }

dec-≡ˡ : (l₁ l₂ : Lit) → Dec (l₁ ≡ l₂)
dec-≡ˡ l₁ l₂ with lit-comp l₁ l₂
... | tri< _ p _ = false because ofⁿ p
... | tri≈ _ p _ = true  because ofʸ p
... | tri> _ p _ = false because ofⁿ p

open import Data.Tree.AVL.Sets lit-<-STO using (⟨Set⟩ ; empty ; insert ; _∈?_)

postulate
  envir : M.Map Bool

  set-insed : ∀ l    s →          (l  ∈? (insert l s)) ≡ true
  set-other : ∀ l′ l s → l′ ≢ l → (l′ ∈? (insert l s)) ≡ (l′ ∈? s)

set-≡ : ∀ s₁ s₂ → Set
set-≡ s₁ s₂ = ∀ l′ → (l′ ∈? s₁) ≡ (l′ ∈? s₂)

set-add-mono : ∀ l s₁ s₂ → set-≡ s₁ s₂ → (∀ l′ → (l′ ∈? (insert l s₁)) ≡ (l′ ∈? (insert l s₂)))

set-add-mono l s₁ s₂ p l′ with dec-≡ˡ l′ l
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

evalᵛ : Var → Bool
evalᵛ v with M.lookup v envir
... | just b  = b
... | nothing = false

holdsᵛ : Var → Set
holdsᵛ = T ∘ evalᵛ

holdsˡ : Lit → Set
holdsˡ (pos v′) = holdsᵛ v′
holdsˡ (neg v′) = ¬ (holdsᵛ v′)

holds : Clause → Set
holds []       = ⊥
holds (l′ ∷ xs) = holdsˡ l′ ⊎ holds xs

holds⁺ : Clause⁺ → ⟨Set⟩ → Set
holds⁺ []                    s = ⊥
holds⁺ (inj₁ l′        ∷ xs) s = if l′ ∈? s then holds⁺ xs s else holdsˡ l′ ⊎ holds⁺ xs s
holds⁺ (inj₂ (join c′) ∷ xs) s = holds⁺ c′ s ⊎ holds⁺ xs s
holds⁺ (inj₂ (skip l′) ∷ xs) s = holds⁺ xs (insert l′ s)

holds⁺-≡ : ∀ s₁ s₂ c → set-≡ s₁ s₂ → holds⁺ c s₁ ≡ holds⁺ c s₂
holds⁺-≡ s₁ s₂ [] p = refl

holds⁺-≡ s₁ s₂ (inj₁ l′ ∷ xs) p rewrite p l′ with l′ ∈? s₂
... | true  = holds⁺-≡ s₁ s₂ xs p
... | false rewrite holds⁺-≡ s₁ s₂ xs p = refl

holds⁺-≡ s₁ s₂ (inj₂ (join c′) ∷ xs) p
  rewrite holds⁺-≡ s₁ s₂ c′ p | holds⁺-≡ s₁ s₂ xs p = refl

holds⁺-≡ s₁ s₂ (inj₂ (skip l′) ∷ xs) p =
  holds⁺-≡ (insert l′ s₁) (insert l′ s₂) xs (set-add-mono l′ s₁ s₂ p)

holds⁺-com : ∀ l₁ l₂ s c → holds⁺ c (insert l₁ (insert l₂ s)) ≡ holds⁺ c (insert l₂ (insert l₁ s))
holds⁺-com l₁ l₂ s c =
  holds⁺-≡ (insert l₁ (insert l₂ s)) (insert l₂ (insert l₁ s)) c (set-add-com l₁ l₂ s)

flipˡ : Lit → Lit
flipˡ (pos v) = neg v
flipˡ (neg v) = pos v

flipˡ-≢ : ∀ l → l ≢ flipˡ l
flipˡ-≢ (pos v) = λ ()
flipˡ-≢ (neg v) = λ ()

flipˡ-¬ : ∀ {l} → holdsˡ l → ¬ (holdsˡ (flipˡ l))
flipˡ-¬ {pos v′} p f = f p
flipˡ-¬ {neg v′} p = p

evalᵛ-t : ∀ {v} → evalᵛ v ≡ true → holdsˡ (pos v)
evalᵛ-t p rewrite p = tt

evalᵛ-f : ∀ {v} → evalᵛ v ≡ false → holdsˡ (neg v)
evalᵛ-f p rewrite p = id

⊥-⊎ : ∀ {ℓ} {A B : Set ℓ} → ¬ A → A ⊎ B → B
⊥-⊎ p₁ (inj₁ p′) = contradiction p′ p₁
⊥-⊎ p₁ (inj₂ p′) = p′

resolve⁺ : ∀ l s c → holdsˡ l → holds⁺ c s → holds⁺ c (insert (flipˡ l) s)

resolve⁺ l s (inj₁ l′ ∷ xs) h₁ h₂
  with dec-≡ˡ l′ l | dec-≡ˡ l′ (flipˡ l) | l′ ∈? s | inspect (l′ ∈?_) s

... | yes p₁ | _ | true | [ eq ]
  rewrite p₁ | set-other l (flipˡ l) s (flipˡ-≢ l) | eq = resolve⁺ l s xs h₁ h₂

... | yes p₁ | _ | false | [ eq ]
  rewrite p₁ | set-other l (flipˡ l) s (flipˡ-≢ l) | eq = inj₁ h₁

... | _ | yes p₂ | true | _
  rewrite p₂ | set-insed (flipˡ l) s = resolve⁺ l s xs h₁ h₂

... | _ | yes p₂ | false | _
  rewrite p₂ | set-insed (flipˡ l) s = resolve⁺ l s xs h₁ (⊥-⊎ (flipˡ-¬ {l} h₁) h₂)

... | _ | no p₂ | true | [ eq ]
  rewrite set-other l′ (flipˡ l) s p₂ | eq = resolve⁺ l s xs h₁ h₂

... | _ | no p₂ | false | [ eq ]
  rewrite set-other l′ (flipˡ l) s p₂ | eq with h₂
... | inj₁ h′ = inj₁ h′
... | inj₂ h′ = inj₂ (resolve⁺ l s xs h₁ h′)

resolve⁺ l s (inj₂ (join c′) ∷ xs) h₁ (inj₁ h′) = inj₁ (resolve⁺ l s c′ h₁ h′)
resolve⁺ l s (inj₂ (join c′) ∷ xs) h₁ (inj₂ h′) = inj₂ (resolve⁺ l s xs h₁ h′)

resolve⁺ l s (inj₂ (skip l′) ∷ xs) h₁ h₂
  rewrite holds⁺-com l′ (flipˡ l) s xs = resolve⁺ l (insert l′ s) xs h₁ h₂

resolve⁺-r : ∀ {c₁ c₂} → holds⁺ c₁ empty → holds⁺ c₂ empty → (v : Var) →
  holds⁺ (inj₂ (join (inj₂ (skip (pos v)) ∷ c₁)) ∷ inj₂ (skip (neg v)) ∷ c₂) empty

resolve⁺-r {c₁} {c₂} h₁ h₂ v with evalᵛ v | inspect evalᵛ v
... | true  | [ eq ] = inj₂ (resolve⁺ (pos v) empty c₂ (evalᵛ-t eq) h₂)
... | false | [ eq ] = inj₁ (resolve⁺ (neg v) empty c₁ (evalᵛ-f eq) h₁)

resolve⁺-q : ∀ {c₁ c₂} → holds⁺ c₁ empty → holds⁺ c₂ empty → (v : Var) →
  holds⁺ (inj₂ (join (inj₂ (skip (neg v)) ∷ c₁)) ∷ inj₂ (skip (pos v)) ∷ c₂) empty

resolve⁺-q {c₁} {c₂} h₁ h₂ v with evalᵛ v | inspect evalᵛ v
... | true  | [ eq ] = inj₁ (resolve⁺ (pos v) empty c₁ (evalᵛ-t eq) h₁)
... | false | [ eq ] = inj₂ (resolve⁺ (neg v) empty c₂ (evalᵛ-f eq) h₂)

compl : Clause → Clause⁺
compl = map inj₁

simpl : Clause⁺ → ⟨Set⟩ → Clause
simpl []                   _ = []
simpl (inj₁ l        ∷ xs) s = if l ∈? s then simpl xs s else l ∷ simpl xs s
simpl (inj₂ (join c) ∷ xs) s = simpl c s ++ simpl xs s
simpl (inj₂ (skip l) ∷ xs) s = simpl xs (insert l s)

holds-holds⁺ : ∀ {c} → holds c → holds⁺ (compl c) empty
holds-holds⁺ {(l′ ∷ ls)} (inj₁ h′) = inj₁ h′
holds-holds⁺ {(l′ ∷ ls)} (inj₂ h′) = inj₂ (holds-holds⁺ {ls} h′)

holds-++ʳ : ∀ {c₁ c₂} → holds c₁ → holds (c₁ ++ c₂)
holds-++ʳ {x ∷ xs} (inj₁ h′) = inj₁ h′
holds-++ʳ {x ∷ xs} (inj₂ h′) = inj₂ (holds-++ʳ h′)

holds-++ˡ : ∀ {c₁ c₂} → holds c₂ → holds (c₁ ++ c₂)
holds-++ˡ {[]}     h = h
holds-++ˡ {x ∷ xs} h = inj₂ (holds-++ˡ h)

simpl-holds : ∀ c s → holds⁺ c s → holds (simpl c s)

simpl-holds (inj₁ l′ ∷ xs) s h with l′ ∈? s
... | true  = simpl-holds xs s h
... | false with h
... | inj₁ h′ = inj₁ h′
... | inj₂ h′ = inj₂ (simpl-holds xs s h′)

simpl-holds (inj₂ (join c′) ∷ xs) s (inj₁ h′) = holds-++ʳ (simpl-holds c′ s h′)
simpl-holds (inj₂ (join c′) ∷ xs) s (inj₂ h′) = holds-++ˡ (simpl-holds xs s h′)
simpl-holds (inj₂ (skip l′) ∷ xs) s h         = simpl-holds xs (insert l′ s) h

mp⁺ : ∀ {c₁ c₂} → holds⁺ c₁ empty → (holds (simpl c₁ empty) → holds c₂) → holds c₂
mp⁺ {c₁} h₁ t = t (simpl-holds c₁ empty h₁)

mp : ∀ {c₁ c₂} → holds c₁ → (holds c₁ → holds c₂) → holds c₂
mp h₁ h₁⇒h₂ = h₁⇒h₂ h₁

dedup : Clause → ⟨Set⟩ → Clause
dedup []       _ = []
dedup (l ∷ ls) s = if l ∈? s then dedup ls s else l ∷ dedup ls (insert l s)

dedup-≡ : ∀ s₁ s₂ c → set-≡ s₁ s₂ → dedup c s₁ ≡ dedup c s₂
dedup-≡ s₁ s₂ [] p = refl

dedup-≡ s₁ s₂ (l′ ∷ ls) p
  rewrite p l′
        | dedup-≡ s₁ s₂ ls p
        | dedup-≡ (insert l′ s₁) (insert l′ s₂) ls (set-add-mono l′ s₁ s₂ p)
        = refl

dedup-com : ∀ l₁ l₂ s c → dedup c (insert l₁ (insert l₂ s)) ≡ dedup c (insert l₂ (insert l₁ s))
dedup-com l₁ l₂ s c =
  dedup-≡ (insert l₁ (insert l₂ s)) (insert l₂ (insert l₁ s)) c (set-add-com l₁ l₂ s)

dedup-flipˡ : ∀ l s c → holdsˡ l → holds (dedup c s) → holds (dedup c (insert (flipˡ l) s))

dedup-flipˡ l s (l′ ∷ ls) h₁ h₂ with dec-≡ˡ l′ (flipˡ l)
... | yes p rewrite p | set-insed (flipˡ l) s with (flipˡ l) ∈? s
... | true = dedup-flipˡ l s ls h₁ h₂
... | false with h₂
... | inj₁ h′ = contradiction h′ (flipˡ-¬ {l} h₁)
... | inj₂ h′ = h′

dedup-flipˡ l s (l′ ∷ ls) h₁ h₂ | no p rewrite set-other l′ (flipˡ l) s p with l′ ∈? s
... | true  = dedup-flipˡ l s ls h₁ h₂
... | false with h₂
... | inj₁ h′ = inj₁ h′
... | inj₂ h′ rewrite dedup-com l′ (flipˡ l) s ls = inj₂ (dedup-flipˡ l (insert l′ s) ls h₁ h′)

dedup-holds : ∀ c → holds c → holds (dedup c empty)
dedup-holds (l ∷ ls) (inj₁ h) = inj₁ h

dedup-holds (pos v ∷ ls) (inj₂ h) with evalᵛ v | inspect evalᵛ v
... | true  | _      = inj₁ tt
... | false | [ eq ] = inj₂ (dedup-flipˡ (neg v) empty ls (evalᵛ-f eq) (dedup-holds ls h))

dedup-holds (neg v ∷ ls) (inj₂ h) with evalᵛ v | inspect evalᵛ v
... | true  | [ eq ] = inj₂ (dedup-flipˡ (pos v) empty ls (evalᵛ-t eq) (dedup-holds ls h))
... | false | _      = inj₁ id

--- SMT ---

formula-op₁ = Formula → Formula
formula-op₂ = Formula → Formula → Formula
formula-op₃ = Formula → Formula → Formula → Formula

data Formula where
  trueᶠ  : Formula
  falseᶠ : Formula

  notᶠ   : formula-op₁
  andᶠ   : formula-op₂
  orᶠ    : formula-op₂

holdsᶠ : Formula → Set
holdsᶠ trueᶠ  = ⊤
holdsᶠ falseᶠ = ⊥

holdsᶠ (notᶠ f) = ¬ holdsᶠ f
holdsᶠ (andᶠ f₁ f₂) = holdsᶠ f₁ × holdsᶠ f₂
holdsᶠ (orᶠ f₁ f₂) = holdsᶠ f₁ ⊎ holdsᶠ f₂

evalᶠ : Formula → Bool
evalᶠ trueᶠ = true
evalᶠ falseᶠ = false

evalᶠ (notᶠ f) = not (evalᶠ f)
evalᶠ (andᶠ f₁ f₂) = evalᶠ f₁ ∧ evalᶠ f₂
evalᶠ (orᶠ f₁ f₂) = evalᶠ f₁ ∨ evalᶠ f₂

evalᶠ-t : ∀ {f} → evalᶠ f ≡ true → holdsᶠ f
evalᶠ-f : ∀ {f} → evalᶠ f ≡ false → ¬ holdsᶠ f

evalᶠ-t {trueᶠ} p = tt

evalᶠ-t {notᶠ f} p with evalᶠ f | inspect evalᶠ f
evalᶠ-t {notᶠ f} () | true  | _
evalᶠ-t {notᶠ f} _  | false | [ eq ] = evalᶠ-f eq

evalᶠ-t {andᶠ f₁ f₂} p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
evalᶠ-t {andᶠ f₁ f₂} _  | true  | [ eq₁ ] | true  | [ eq₂ ] = evalᶠ-t eq₁ , evalᶠ-t eq₂
evalᶠ-t {andᶠ f₁ f₂} () | true  | _       | false | _
evalᶠ-t {andᶠ f₁ f₂} () | false | _       | true  | _
evalᶠ-t {andᶠ f₁ f₂} () | false | _       | false | _

evalᶠ-t {orᶠ f₁ f₂} p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
evalᶠ-t {orᶠ f₁ f₂} _  | true  | [ eq₁ ] | _     | _       = inj₁ (evalᶠ-t eq₁)
evalᶠ-t {orᶠ f₁ f₂} _  | false | _       | true  | [ eq₂ ] = inj₂ (evalᶠ-t eq₂)
evalᶠ-t {orᶠ f₁ f₂} () | false | _       | false | _

evalᶠ-f {falseᶠ} p = id

evalᶠ-f {notᶠ f} p with evalᶠ f | inspect evalᶠ f
evalᶠ-f {notᶠ f} _  | true  | [ eq ] = λ x → x (evalᶠ-t eq)
evalᶠ-f {notᶠ f} () | false | _

evalᶠ-f {andᶠ f₁ f₂} p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
evalᶠ-f {andᶠ f₁ f₂} () | true  | [ eq₁ ] | true  | [ eq₂ ]

evalᶠ-f {andᶠ f₁ f₂} _  | true  | [ eq₁ ] | false | [ eq₂ ] =
  λ { (_ , p₂) → contradiction p₂ (evalᶠ-f eq₂) }

evalᶠ-f {andᶠ f₁ f₂} _  | false | [ eq₁ ] | true  | [ eq₂ ] =
  λ { (p₁ , _) → contradiction p₁ (evalᶠ-f eq₁) }

evalᶠ-f {andᶠ f₁ f₂} _  | false | [ eq₁ ] | false | [ eq₂ ] =
  λ { (p₁ , _) → contradiction p₁ (evalᶠ-f eq₁) }

evalᶠ-f {orᶠ f₁ f₂} p  with evalᶠ f₁ | inspect evalᶠ f₁ | evalᶠ f₂ | inspect evalᶠ f₂
evalᶠ-f {orᶠ f₁ f₂} () | true  | _       | _     | _
evalᶠ-f {orᶠ f₁ f₂} () | false | _       | true  | _

evalᶠ-f {orᶠ f₁ f₂} _  | false | [ eq₁ ] | false | [ eq₂ ] =
  λ {
    (inj₁ p₁) → contradiction p₁ (evalᶠ-f eq₁) ;
    (inj₂ p₂) → contradiction p₂ (evalᶠ-f eq₂)
  }

atom : Var → Formula → Set
atom v f = evalᵛ v ≡ evalᶠ f

decl-atom : ∀ {v f} → atom v f → (∀ {v} → atom v f → holds []) → holds []
decl-atom a fn = fn a

claus-t : ∀ {v f} → atom v f → holdsᶠ f → holds (pos v ∷ [])
claus-t {v} {f} a h with evalᶠ f | inspect evalᶠ f
... | true  | _      rewrite a = inj₁ tt
... | false | [ eq ] = contradiction h (evalᶠ-f eq)

claus-f : ∀ {v f} → atom v f → holdsᶠ (notᶠ f) → holds (neg v ∷ [])
claus-f {v} {f} a h with evalᶠ f | inspect evalᶠ f
... | true  | [ eq ] = contradiction (evalᶠ-t eq) h
... | false | [ eq ] rewrite a = inj₁ id

assum-t : ∀ {v f c} → atom v f → (holdsᶠ f → holds c) → holds (neg v ∷ c)
assum-t {v} {f} {c} a fn with evalᶠ f | inspect evalᶠ f
... | true  | [ eq ] = inj₂ (fn (evalᶠ-t eq))
... | false | _      rewrite a = inj₁ id

assum-f : ∀ {v f c} → atom v f → (holdsᶠ (notᶠ f) → holds c) → holds (pos v ∷ c)
assum-f {v} {f} {c} a fn with evalᶠ f | inspect evalᶠ f
... | true  | _      rewrite a = inj₁ tt
... | false | [ eq ] = inj₂ (fn (evalᶠ-f eq))

{-
--- SMT ---

formula-op₁ = Formula → Formula
formula-op₂ = Formula → Formula → Formula
formula-op₃ = Formula → Formula → Formula → Formula

data Sørt where
  Boöl : Sørt

data Formula where
  trueᶠ  : Formula
  falseᶠ : Formula

  notᶠ   : formula-op₁
  andᶠ   : formula-op₂
  orᶠ    : formula-op₂
  implᶠ  : formula-op₂
  iffᶠ   : formula-op₂
  xorᶠ   : formula-op₂
  ite₁ᶠ  : formula-op₃

  =ᶠ     : {s : Sørt} → Term s → Term s → Formula
  ite₂ᶠ  : {s : Sørt} → Formula → Term s → Term s → Formula
  -- XXX - add let, flet

  appᶠ   : Term Boöl → Formula

data Term where
  trueᵗ  : Term Boöl
  falseᵗ : Term Boöl

eval-term : {s : Sørt} → (t : Term s) → Bool
eval-term trueᵗ  = true
eval-term falseᵗ = false

eval-form : (f : Formula) → Bool

eval-form trueᶠ            = true
eval-form falseᶠ           = false

eval-form (notᶠ  f       ) = not (eval-form f )
eval-form (andᶠ  f₁ f₂   ) =      eval-form f₁  ∧      eval-form f₂
eval-form (orᶠ   f₁ f₂   ) =      eval-form f₁                       ∨      eval-form f₂
eval-form (implᶠ f₁ f₂   ) = not (eval-form f₁)                      ∨      eval-form f₂
eval-form (iffᶠ  f₁ f₂   ) =      eval-form f₁  ∧      eval-form f₂  ∨ not (eval-form f₁) ∧ not (eval-form f₂)
eval-form (xorᶠ  f₁ f₂   ) =      eval-form f₁  ∧ not (eval-form f₂) ∨ not (eval-form f₁) ∧      eval-form f₂
eval-form (ite₁ᶠ f₁ f₂ f₃) =      eval-form f₁  ∧      eval-form f₂  ∨ not (eval-form f₁) ∧      eval-form f₃

eval-form (=ᶠ    t₁ t₂   ) =      eval-term t₁  ∧      eval-term t₂  ∨ not (eval-term t₁) ∧ not (eval-term t₂)
eval-form (ite₂ᶠ f₁ t₁ t₂) =      eval-form f₁  ∧      eval-term t₁  ∨ not (eval-form f₁) ∧      eval-term t₂

eval-form (appᶠ t        ) =      eval-term t

data ThHolds : Formula → Set where
  th-holds : (f : Formula) → eval-form f ≡ true → ThHolds f
-}
