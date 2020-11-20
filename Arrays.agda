open import Data.Nat using (ℕ)

module Arrays (bitsᵏ bitsᵛ : ℕ) where

open import Data.Bool using (true ; false ; _∨_ ; not)
open import Data.Bool.Properties using (∨-zeroˡ ; ∨-zeroʳ ; not-¬)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (zero ; suc ; _⊔_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using () renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)

open import Function using (_$_ ; _∘_)

open import Level using (Level ; 0ℓ)

open import Relation.Binary using (Decidable) renaming (DecSetoid to DSD)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; trans ; cong ; subst ; inspect ; [_])

open import Relation.Nullary using (Dec ; _because_ ; does ; ofʸ ; ofⁿ ; ¬_)
open import Relation.Nullary.Negation using (contradiction)

open import BitVec using (BitVec ; bv-dsd ; bv-func-≟ ; null)
open import SAT using (Env ; Holdsᶜ ; not-t⇒f ; f⇒not-t)
open import SMT using (orᶠ ; notᶠ ; equᶠ ; Holds ; holds)

dsdᵏ = bv-dsd {bitsᵏ}
dsdᵛ = bv-dsd {bitsᵛ}

defᵛ = null {bitsᵛ}
defᵏ = null {bitsᵏ}

open DSD dsdᵏ using () renaming (Carrier to Key ; _≟_ to _≟ᵏ_)
open DSD dsdᵛ using () renaming (Carrier to Val ; _≟_ to _≟ᵛ_)

valid : {S : Set} → (l r : Maybe S) → Set
valid nothing nothing = ⊥
valid _       _       = ⊤

one-valid : {S : Set} → {l r : Maybe S} → (v₁ v₂ : valid l r) → v₁ ≡ v₂
one-valid {l = just _}  {just _}  v₁ v₂ = refl
one-valid {l = just _}  {nothing} v₁ v₂ = refl
one-valid {l = nothing} {just _}  v₁ v₂ = refl

data Trie : ℕ → Set where
  node : {h : ℕ} → (l r : Maybe (Trie h)) → {valid l r} → Trie (suc h)
  leaf : Val → Trie 0

-- helper to get |valid l r| for unknown left sub-tries
node′ : {h : ℕ} → (l : Maybe (Trie h)) → (r : Trie h) → Trie (suc h)
node′ nothing  r = node nothing  (just r)
node′ (just l) r = node (just l) (just r)

just-inj : {ℓ : Level} → {S : Set ℓ} → {x y : S} → just x ≡ just y → x ≡ y
just-inj refl = refl

leaf-inj : {v₁ v₂ : Val} → leaf v₁ ≡ leaf v₂ → v₁ ≡ v₂
leaf-inj refl = refl

node-injˡ : ∀ {h l₁ l₂ r₁ r₂ v₁ v₂} → node {h} l₁ r₁ {v₁} ≡ node {h} l₂ r₂ {v₂} → l₁ ≡ l₂
node-injˡ refl = refl

node-injʳ : ∀ {h l₁ l₂ r₁ r₂ v₁ v₂} → node {h} l₁ r₁ {v₁} ≡ node {h} l₂ r₂ {v₂} → r₁ ≡ r₂
node-injʳ refl = refl

-- LFSC: Array
Array = Maybe (Trie bitsᵏ)

infix 4 _≟_

_≟_ : {h : ℕ} → (a₁ a₂ : Maybe (Trie h)) → Dec (a₁ ≡ a₂)
_≟_ {zero} nothing          nothing          = true  because ofʸ refl
_≟_ {zero} nothing          (just (leaf v₂)) = false because ofⁿ λ ()
_≟_ {zero} (just (leaf v₁)) nothing          = false because ofⁿ λ ()

_≟_ {zero} (just (leaf v₁)) (just (leaf v₂))
  with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = true  because ofʸ refl
... | false because ofⁿ p    = false because ofⁿ (p ∘ leaf-inj ∘ just-inj)

_≟_ {suc h} nothing  nothing  = true  because ofʸ refl
_≟_ {suc h} nothing  (just _) = false because ofⁿ λ ()
_≟_ {suc h} (just _) nothing  = false because ofⁿ λ ()

_≟_ {suc h} (just (node l₁ r₁ {v₁})) (just (node l₂ r₂ {v₂}))
  with l₁ ≟ l₂
... | false because ofⁿ p    = false because ofⁿ (p ∘ node-injˡ ∘ just-inj)
... | true  because ofʸ refl
  with r₁ ≟ r₂
... | false because ofⁿ q    = false because ofⁿ (q ∘ node-injʳ ∘ just-inj)
... | true  because ofʸ refl
  rewrite one-valid v₁ v₂
  = true  because ofʸ refl

array-dsd : DSD 0ℓ 0ℓ
array-dsd = record {
    Carrier = Array ;
    _≈_ = _≡_ ;
    isDecEquivalence = record {
        isEquivalence = record {
            refl  = refl ;
            sym   = sym ;
            trans = trans
          } ;
        _≟_ = _≟_
      }
  }

insert : {h : ℕ} → BitVec h → Val → Maybe (Trie h) → Trie h
insert []ᵛ           v nothing             = leaf v
insert (true  ∷ᵛ bv) v nothing             = let t = insert bv v nothing in node (just t) nothing
insert (false ∷ᵛ bv) v nothing             = let t = insert bv v nothing in node nothing (just t)
insert []ᵛ           v (just (leaf _))     = leaf v
insert (true  ∷ᵛ bv) v (just (node aˡ aʳ)) = let t = insert bv v aˡ in node (just t) aʳ
insert (false ∷ᵛ bv) v (just (node aˡ aʳ)) = let t = insert bv v aʳ in node′ aˡ t

-- LFSC: write
write : Array → Key → Val → Array
write a k v = just $ insert k v a

lookup : {h : ℕ} → BitVec h → Maybe (Trie h) → Maybe Val
lookup _             nothing             = nothing
lookup []ᵛ           (just (leaf v))     = just v
lookup (true  ∷ᵛ bv) (just (node aˡ _))  = lookup bv aˡ
lookup (false ∷ᵛ bv) (just (node _  aʳ)) = lookup bv aʳ

-- LFSC: read
read : Array → Key → Val
read a k with lookup k a
... | nothing = defᵛ
... | just v  = v

insed : {h : ℕ} → (a : Maybe (Trie h)) → (k : BitVec h) → (v : Val) →
  lookup k (just (insert k v a)) ≡ just v

insed nothing                   []ᵛ           _ = refl
insed nothing                   (true  ∷ᵛ bv) v = insed nothing bv v
insed nothing                   (false ∷ᵛ bv) v = insed nothing bv v
insed (just (leaf _))           []ᵛ           _ = refl
insed (just (node aˡ       _))  (true  ∷ᵛ bv) v = insed aˡ bv v
-- extra case split for |node′|
insed (just (node nothing  aʳ)) (false ∷ᵛ bv) v = insed aʳ bv v
insed (just (node (just _) aʳ)) (false ∷ᵛ bv) v = insed aʳ bv v

trim-≉ : ∀ {n b} → {bv₁ bv₂ : BitVec n} → (b ∷ᵛ bv₁) ≢ (b ∷ᵛ bv₂) → bv₁ ≢ bv₂
trim-≉ {b = b} {bv₁} {bv₂} p n = p $ cong (b ∷ᵛ_) n

other : {h : ℕ} → (a : Maybe (Trie h)) → (k₁ k₂ : BitVec h) → (v : Val) → k₁ ≢ k₂ →
  lookup k₂ (just (insert k₁ v a)) ≡ lookup k₂ a

pattern J x = just x
pattern N   = nothing

other _                   []ᵛ            []ᵛ            _ k₁≉k₂ = contradiction refl k₁≉k₂
other N                   (true  ∷ᵛ bv₁) (true  ∷ᵛ bv₂) v k₁≉k₂ = other N  bv₁ bv₂ v (trim-≉ k₁≉k₂)
other (J (node aˡ    _))  (true  ∷ᵛ bv₁) (true  ∷ᵛ bv₂) v k₁≉k₂ = other aˡ bv₁ bv₂ v (trim-≉ k₁≉k₂)
other N                   (true  ∷ᵛ _)   (false ∷ᵛ _)   _ _     = refl
other (J (node _     _))  (true  ∷ᵛ _)   (false ∷ᵛ _)   _ _     = refl
other N                   (false ∷ᵛ _)   (true  ∷ᵛ _)   _ _     = refl
-- extra case split for |node′|
other (J (node N  _))     (false ∷ᵛ _)   (true  ∷ᵛ _)   _ _     = refl
other (J (node (J _) _))  (false ∷ᵛ _)   (true  ∷ᵛ _)   _ _     = refl
other N                   (false ∷ᵛ bv₁) (false ∷ᵛ bv₂) v k₁≉k₂ = other N  bv₁ bv₂ v (trim-≉ k₁≉k₂)
-- extra case split for |node′|
other (J (node N     aʳ)) (false ∷ᵛ bv₁) (false ∷ᵛ bv₂) v k₁≉k₂ = other aʳ bv₁ bv₂ v (trim-≉ k₁≉k₂)
other (J (node (J _) aʳ)) (false ∷ᵛ bv₁) (false ∷ᵛ bv₂) v k₁≉k₂ = other aʳ bv₁ bv₂ v (trim-≉ k₁≉k₂)

-- LFSC: row1
row-≈ : (a : Array) → (k : Key) → (v : Val) → Holds (equᶠ {{dsdᵛ}} (read (write a k v) k) v)
row-≈ a k v with read (write a k v) k ≟ᵛ v | inspect (read (write a k v) k ≟ᵛ_) v
... | true  because _     | [ eq ] = holds _ (cong does eq)
... | false because ofⁿ p | _      rewrite insed a k v = contradiction refl p

-- LFSC: row
row-≉ : (a : Array) → (k₁ k₂ : Key) → (v : Val) →
  Holds (notᶠ (equᶠ {{dsdᵏ}} k₁ k₂)) →
  Holds (equᶠ {{dsdᵛ}} (read (write a k₁ v) k₂) (read a k₂))

row-≉ a k₁ k₂ v (holds _ h)
  with read (write a k₁ v) k₂ ≟ᵛ read a k₂ | inspect (read (write a k₁ v) k₂ ≟ᵛ_) (read a k₂)

... | true  because _     | [ eq ] = holds _ (cong does eq)
... | false because ofⁿ p | _      with k₁ ≟ᵏ k₂
... | false because ofⁿ q rewrite other a k₁ k₂ v q = contradiction refl p

-- LFSC: negativerow
¬-row-≉ : (a : Array) → (k₁ k₂ : Key) → (v : Val) →
  Holds (notᶠ (equᶠ {{dsdᵛ}} (read (write a k₁ v) k₂) (read a k₂))) →
  Holds (equᶠ {{dsdᵏ}} k₁ k₂)

¬-row-≉ a k₁ k₂ v (holds _ h) with does (k₁ ≟ᵏ k₂) | inspect does (k₁ ≟ᵏ k₂)
... | true  | [ eq ] = holds _ eq
... | false | [ eq ] with (holds _ h′) ← row-≉ a k₁ k₂ v (holds _ (f⇒not-t eq)) =
  contradiction h′ (not-¬ (not-t⇒f h))

≢-lookup : {h : ℕ} → {a₁ a₂ : Maybe (Trie h)} → a₁ ≢ a₂ → (∃ λ k → lookup k a₁ ≢ lookup k a₂)
≢-lookup {_}    {N}           {N}           a₁≢a₂ = contradiction refl a₁≢a₂
≢-lookup {zero} {J (leaf v₁)} {N}           a₁≢a₂ = []ᵛ , λ ()
≢-lookup {zero} {N}           {J (leaf v₂)} a₁≢a₂ = []ᵛ , λ ()

≢-lookup {zero} {J (leaf v₁)} {J (leaf v₂)} a₁≢a₂
  with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = contradiction refl a₁≢a₂
... | false because ofⁿ p    = []ᵛ , λ n → p $ just-inj n

-- no |node N N| cases because of |valid l r| magic

≢-lookup {suc h} {J (node (J l₁) _)} {N} a₁≢a₂ =
  let (k , p) = ≢-lookup {h} {J l₁} {N} λ () in true ∷ᵛ k , p

≢-lookup {suc h} {J (node N (J r₁))} {N} a₁≢a₂ =
  let (k , p) = ≢-lookup {h} {J r₁} {N} λ () in false ∷ᵛ k , p

≢-lookup {suc h} {N} {J (node (J l₂) _)} a₁≢a₂ =
  let (k , p) = ≢-lookup {h} {N} {J l₂} λ () in true ∷ᵛ k , p

≢-lookup {suc h} {N} {J (node N (J r₂))} a₁≢a₂ =
  let (k , p) = ≢-lookup {h} {N} {J r₂} λ () in false ∷ᵛ k , p

≢-lookup {suc h} {J (node l₁ r₁)} {J (node l₂ r₂)} a₁≢a₂
  with l₁ ≟ l₂
... | false because ofⁿ p    = let (k , q) = ≢-lookup {h} {l₁} {l₂} p in true ∷ᵛ k , q
... | true  because ofʸ refl
  with r₁ ≟ r₂
... | false because ofⁿ r    = let (k , s) = ≢-lookup {h} {r₁} {r₂} r in false ∷ᵛ k , s
... | true  because ofʸ refl
  with l₁
... | J _                    = contradiction refl a₁≢a₂
... | N
  with r₁
... | J _                    = contradiction refl a₁≢a₂

≢-read : {a₁ a₂ : Array} → a₁ ≢ a₂ → (∃ λ k → read a₁ k ≢ read a₂ k)
≢-read {a₁} {a₂} a₁≢a₂
  with (k , p) ← ≢-lookup a₁≢a₂ = k , lem
  where
  lem : read a₁ k ≢ read a₂ k
  lem with lookup k a₁ | lookup k a₂
  ... | J v₁ | J v₂ = p ∘ cong J
  ... | J v₁ | N    = {!!}
  ... | N    | J v₂ = {!!}
  ... | N    | N    = contradiction refl p

lookup-≋ : {h : ℕ} → (a₁ a₂ : Maybe (Trie h)) →
  (∀ k → lookup k a₁ ≡ lookup k a₂) ⊎ (∃ λ k → lookup k a₁ ≢ lookup k a₂)

lookup-≋        nothing          nothing          = inj₁ λ _ → refl
lookup-≋ {zero} (just (leaf v₁)) nothing          = inj₂ ([]ᵛ , λ ())
lookup-≋ {zero} nothing          (just (leaf v₂)) = inj₂ ([]ᵛ , λ ())

lookup-≋ {zero} (just (leaf v₁)) (just (leaf v₂))
  with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = inj₁ λ _ → refl
... | false because ofⁿ p    = inj₂ ([]ᵛ , p ∘ just-inj)

lookup-≋ {suc h} (just (node l₁ r₁)) nothing
  with lookup-≋ l₁ nothing
... | inj₂ (k , p) = inj₂ (true ∷ᵛ k , p)
... | inj₁ p
  with lookup-≋ r₁ nothing
... | inj₂ (k , q) = inj₂ (false ∷ᵛ k , q)
... | inj₁ q = inj₁ λ { (true ∷ᵛ k) → p k ; (false ∷ᵛ k) → q k }

lookup-≋ {suc h} nothing (just (node l₂ r₂))
  with lookup-≋ nothing l₂
... | inj₂ (k , p) = inj₂ (true ∷ᵛ k , p)
... | inj₁ p
  with lookup-≋ nothing r₂
... | inj₂ (k , q) = inj₂ (false ∷ᵛ k , q)
... | inj₁ q = inj₁ λ { (true ∷ᵛ k) → p k ; (false ∷ᵛ k) → q k }

lookup-≋ {suc h} (just (node l₁ r₁)) (just (node l₂ r₂))
  with lookup-≋ l₁ l₂
... | inj₂ (k , p) = inj₂ (true ∷ᵛ k , p)
... | inj₁ p
  with lookup-≋ r₁ r₂
... | inj₂ (k , q) = inj₂ (false ∷ᵛ k , q)
... | inj₁ q = inj₁ λ { (true ∷ᵛ k) → p k ; (false ∷ᵛ k) → q k }

module _ (env : Env) where
  ext-lem₁ : {a : Array} → does (a ≟ a) ≡ true
  ext-lem₁ {a} with a ≟ a
  ... | true  because ofʸ _ = refl
  ... | false because ofⁿ p = contradiction refl p

  ext-lem₂ : {a₁ a₂ : Array} → {k : Key} →
    read a₁ k ≢ read a₂ k → not (does (read a₁ k ≟ᵛ read a₂ k)) ≡ true

  ext-lem₂ {a₁} {a₂} {k} p
    with read a₁ k ≟ᵛ read a₂ k
  ... | true  because ofʸ q = contradiction q p
  ... | false because ofⁿ _ = refl

  -- LFSC: ext
  exten : (a₁ a₂ : Array) →
    ((k : Key) →
      Holds (orᶠ (equᶠ {{array-dsd}} a₁ a₂) (notᶠ (equᶠ {{dsdᵛ}} (read a₁ k) (read a₂ k)))) →
      Holdsᶜ env []) →
    Holdsᶜ env []

  exten a₁ a₂ p with a₁ ≟ a₂
  ... | true because ofʸ refl = p defᵏ $ holds _ lem
    where
    lem : ∀ {x} → does (a₁ ≟ a₁) ∨ x ≡ true
    lem rewrite ext-lem₁ {a = a₁} = refl

  ... | false because ofⁿ q
    with (k , r) ← ≢-read q = p k $ holds _ lem
    where
    lem : ∀ {x} → x ∨ not (does (read a₁ k ≟ᵛ read a₂ k)) ≡ true
    lem {x} rewrite ext-lem₂ {a₁ = a₁} {a₂} {k} r = ∨-zeroʳ x

splitˡ : {h : ℕ} → {T : Set} → (f : Trie (suc h) → T) → Trie h → T
splitˡ f t = f (node (just t) nothing)

joinˡ : {h : ℕ} → {T : Set} → (T-≈ : T → T → Set) → (f₁ f₂ : Trie (suc h) → T) →
  ¬ ({t₁ t₂ : Trie h} → t₁ ≡ t₂ → T-≈ (splitˡ f₁ t₁) (splitˡ f₂ t₂)) →
  ¬ ({t₁ t₂ : Trie (suc h)} → t₁ ≡ t₂ → T-≈ (f₁ t₁) (f₂ t₂))

joinˡ T-≈ f₁ f₂ p n = p $ λ { refl → n refl }

splitʳ : {h : ℕ} → {T : Set} → (f : Trie (suc h) → T) → Trie h → T
splitʳ f t = f (node nothing (just t))

joinʳ : {h : ℕ} → {T : Set} → (T-≈ : T → T → Set) → (f₁ f₂ : Trie (suc h) → T) →
  ¬ ({t₁ t₂ : Trie h} → t₁ ≡ t₂ → T-≈ (splitʳ f₁ t₁) (splitʳ f₂ t₂)) →
  ¬ ({t₁ t₂ : Trie (suc h)} → t₁ ≡ t₂ → T-≈ (f₁ t₁) (f₂ t₂))

joinʳ T-≈ f₁ f₂ p n = p $ λ { refl → n refl }

split : {h : ℕ} → {T : Set} → (f : Trie (suc h) → T) → Trie h → Trie h → T
split f tˡ tʳ = f (node (just tˡ) (just tʳ))

join⁻ : {h : ℕ} → {T : Set} → (T-≈ : T → T → Set) → (f₁ f₂ : Trie (suc h) → T) →
  ¬ ({l₁ l₂ : Trie h} → l₁ ≡ l₂ → {r₁ r₂ : Trie h} → r₁ ≡ r₂ →
    T-≈ (split f₁ l₁ r₁) (split f₂ l₂ r₂)) →
  ¬ ({t₁ t₂ : Trie (suc h)} → t₁ ≡ t₂ → T-≈ (f₁ t₁) (f₂ t₂))

join⁻ T-≈ f₁ f₂ p n = p $ λ { {tˡ} refl {tʳ} refl → n refl }

join⁺ : {h : ℕ} → {T : Set} → (T-≈ : T → T → Set) → (f₁ f₂ : Trie (suc h) → T) →
  ({t₁ t₂ : Trie h} → t₁ ≡ t₂ → T-≈ (splitˡ f₁ t₁) (splitˡ f₂ t₂)) →
  ({t₁ t₂ : Trie h} → t₁ ≡ t₂ → T-≈ (splitʳ f₁ t₁) (splitʳ f₂ t₂)) →
  ({l₁ l₂ : Trie h} → l₁ ≡ l₂ → {r₁ r₂ : Trie h} → r₁ ≡ r₂ →
    T-≈ (split f₁ l₁ r₁) (split f₂ l₂ r₂)) →
  ({t₁ t₂ : Trie (suc h)} → t₁ ≡ t₂ → T-≈ (f₁ t₁) (f₂ t₂))

join⁺ T-≈ f₁ f₂ p q r {node (just tˡ) nothing}   refl = p refl
join⁺ T-≈ f₁ f₂ p q r {node nothing   (just tʳ)} refl = q refl
join⁺ T-≈ f₁ f₂ p q r {node (just tˡ) (just tʳ)} refl = r refl refl

Func-≈ = λ {h : ℕ} (dsdᵗ : DSD 0ℓ 0ℓ) (f₁ f₂ : Trie h → DSD.Carrier dsdᵗ) →
  (∀ {t₁} {t₂} → t₁ ≡ t₂ → DSD._≈_ dsdᵗ (f₁ t₁) (f₂ t₂))

func-≟ : {h : ℕ} → (dsdᵗ : DSD 0ℓ 0ℓ) → Decidable (Func-≈ {h} dsdᵗ)

build-dsd : ℕ → (dsdᵗ : DSD 0ℓ 0ℓ) → DSD 0ℓ 0ℓ
build-dsd h dsdᵗ = record {
    Carrier = Trie h → Carᵗ ;
    _≈_ = λ f₁ f₂ → ∀ {t₁ t₂} → t₁ ≡ t₂ → f₁ t₁ ≈ᵗ f₂ t₂ ;
    isDecEquivalence = record {
        isEquivalence = record {
            refl  = λ { {f} {t₁} {t₂} refl → reflᵗ } ;
            sym   = λ p₁ p₂ → symᵗ (p₁ (sym p₂)) ;
            trans = λ p₁ p₂ p₃ → transᵗ (p₁ refl) (p₂ p₃)
          } ;
        _≟_ = func-≟ dsdᵗ
      }
  }

  where
  open DSD dsdᵗ using ()
    renaming (Carrier to Carᵗ ; _≈_ to _≈ᵗ_ ; refl to reflᵗ ; sym to symᵗ ; trans to transᵗ)

func-≟ {zero} dsdᵗ f₁ f₂ with bv-func-≟ dsdᵗ (f₁ ∘ leaf) (f₂ ∘ leaf)
... | true  because ofʸ p = true  because ofʸ λ { {leaf _} refl → p refl }
... | false because ofⁿ p = false because ofⁿ λ n → p $ λ { {bv₁} {bv₂} refl → n {leaf bv₁} refl }

func-≟ {suc h} dsdᵗ f₁ f₂
  with func-≟ dsdᵗ (splitˡ f₁) (splitˡ f₂)
... | false because ofⁿ p = false because ofⁿ (joinˡ (DSD._≈_ dsdᵗ) f₁ f₂ p)
... | true  because ofʸ p
  with func-≟ dsdᵗ (splitʳ f₁) (splitʳ f₂)
... | false because ofⁿ q = false because ofⁿ (joinʳ (DSD._≈_ dsdᵗ) f₁ f₂ q)
... | true  because ofʸ q
  with func-≟ (build-dsd h dsdᵗ) (split f₁) (split f₂)
... | false because ofⁿ r = false because ofⁿ (join⁻ (DSD._≈_ dsdᵗ) f₁ f₂ r)
... | true  because ofʸ r = true  because ofʸ (join⁺ (DSD._≈_ dsdᵗ) f₁ f₂ p q r)
