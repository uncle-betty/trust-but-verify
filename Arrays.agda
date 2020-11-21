open import Data.Nat using (ℕ)

module Arrays (bitsᵏ bitsᵛ : ℕ) where

open import Data.Bool using (true ; false ; _∨_ ; not)
open import Data.Bool.Properties using (∨-zeroˡ ; ∨-zeroʳ ; not-¬)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (zero ; suc ; _⊔_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using () renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)

open import Function using (_$_ ; _∘_ ; flip)

open import Level using (Level ; 0ℓ)

open import Relation.Binary using (Decidable) renaming (DecSetoid to DSD)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; trans ; cong ; subst ; inspect ; [_])

open import Relation.Nullary using (Dec ; _because_ ; does ; ofʸ ; ofⁿ ; ¬_)
open import Relation.Nullary.Decidable using (False ; fromWitnessFalse ; toWitnessFalse)
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

node-✓ : {S : Set} → (l r : Maybe S) → Set
node-✓ nothing nothing = ⊥
node-✓ _       _       = ⊤

one-node-✓ : {S : Set} → {l r : Maybe S} → (✓₁ ✓₂ : node-✓ l r) → ✓₁ ≡ ✓₂
one-node-✓ {l = just _}  {just _}  ✓₁ ✓₂ = refl
one-node-✓ {l = just _}  {nothing} ✓₁ ✓₂ = refl
one-node-✓ {l = nothing} {just _}  ✓₁ ✓₂ = refl

value-✓ : Val → Set
value-✓ v = False (v ≟ᵛ defᵛ)

one-value-✓ : {v : Val} → (✓₁ ✓₂ : value-✓ v) → ✓₁ ≡ ✓₂
one-value-✓ {v} ✓₁ ✓₂ with v ≟ᵛ defᵛ
... | true  because _ = ⊥-elim ✓₁
... | false because _ = refl

data Trie : ℕ → Set where
  node : {h : ℕ} → (l r : Maybe (Trie h)) → {node-✓ l r} → Trie (suc h)
  leaf : (v : Val) → {value-✓ v} → Trie 0

-- helper to automatically find |node­✓| for unknown left sub-tries
node′ : {h : ℕ} → (l : Maybe (Trie h)) → (r : Trie h) → Trie (suc h)
node′ nothing  r = node nothing  (just r)
node′ (just l) r = node (just l) (just r)

just-inj : {ℓ : Level} → {S : Set ℓ} → {x y : S} → just x ≡ just y → x ≡ y
just-inj refl = refl

leaf-inj : ∀ {v₁ v₂ ✓₁ ✓₂} → leaf v₁ {✓₁} ≡ leaf v₂ {✓₂} → v₁ ≡ v₂
leaf-inj refl = refl

node-injˡ : ∀ {h l₁ l₂ r₁ r₂ ✓₁ ✓₂} → node {h} l₁ r₁ {✓₁} ≡ node {h} l₂ r₂ {✓₂} → l₁ ≡ l₂
node-injˡ refl = refl

node-injʳ : ∀ {h l₁ l₂ r₁ r₂ ✓₁ ✓₂} → node {h} l₁ r₁ {✓₁} ≡ node {h} l₂ r₂ {✓₂} → r₁ ≡ r₂
node-injʳ refl = refl

-- LFSC: Array
Array = Maybe (Trie bitsᵏ)

infix 4 _≟_

_≟_ : {h : ℕ} → (a₁ a₂ : Maybe (Trie h)) → Dec (a₁ ≡ a₂)
_≟_ {zero} nothing          nothing          = true  because ofʸ refl
_≟_ {zero} nothing          (just (leaf v₂)) = false because ofⁿ λ ()
_≟_ {zero} (just (leaf v₁)) nothing          = false because ofⁿ λ ()

_≟_ {zero} (just (leaf v₁ {✓₁})) (just (leaf v₂ {✓₂}))
  with v₁ ≟ᵛ v₂
... | true  because ofʸ refl
  rewrite one-value-✓ ✓₁ ✓₂
  = true  because ofʸ refl

... | false because ofⁿ p    = false because ofⁿ (p ∘ leaf-inj ∘ just-inj)

_≟_ {suc h} nothing  nothing  = true  because ofʸ refl
_≟_ {suc h} nothing  (just _) = false because ofⁿ λ ()
_≟_ {suc h} (just _) nothing  = false because ofⁿ λ ()

_≟_ {suc h} (just (node l₁ r₁ {✓₁})) (just (node l₂ r₂ {✓₂}))
  with l₁ ≟ l₂
... | false because ofⁿ p    = false because ofⁿ (p ∘ node-injˡ ∘ just-inj)
... | true  because ofʸ refl
  with r₁ ≟ r₂
... | false because ofⁿ q    = false because ofⁿ (q ∘ node-injʳ ∘ just-inj)
... | true  because ofʸ refl
  rewrite one-node-✓ ✓₁ ✓₂
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

pattern J x = just x
pattern N   = nothing

insert : {h : ℕ} → BitVec h → (v : Val) → {value-✓ v} → Maybe (Trie h) → Trie h
insert []ᵛ           v {✓} N                = leaf v {✓}
insert (true  ∷ᵛ bv) v {✓} N                = let t = insert bv v {✓} N in node (J t) N
insert (false ∷ᵛ bv) v {✓} N                = let t = insert bv v {✓} N in node N (J t)
insert []ᵛ           v {✓} (J (leaf _))     = leaf v {✓}
insert (true  ∷ᵛ bv) v {✓} (J (node aˡ aʳ)) = let t = insert bv v {✓} aˡ in node (J t) aʳ
insert (false ∷ᵛ bv) v {✓} (J (node aˡ aʳ)) = let t = insert bv v {✓} aʳ in node′ aˡ t

remove : {h : ℕ} → BitVec h → Maybe (Trie h) → Maybe (Trie h)
remove []ᵛ           (J (leaf _))             = N
remove (true  ∷ᵛ bv) (J (node aˡ     N))
  with remove bv aˡ
... | N     = N
... | (J a) = J (node (J a) N)
remove (true  ∷ᵛ bv) (J (node aˡ     (J aʳ))) = J (node′ (remove bv aˡ) aʳ)
remove (false ∷ᵛ bv) (J (node N      aʳ))
  with remove bv aʳ
... | N     = N
... | (J a) = J (node′ N a)
remove (false ∷ᵛ bv) (J (node (J aˡ) aʳ))     = J (node (J aˡ) (remove bv aʳ))
remove _             N                        = N

-- LFSC: write
write : Array → Key → Val → Array
write a k v with v ≟ᵛ defᵛ
... | true  because _     = remove k a
... | false because ofⁿ p = just $ insert k v {fromWitnessFalse p} a

lookup : {h : ℕ} → BitVec h → Maybe (Trie h) → Val
lookup _             N                = defᵛ
lookup []ᵛ           (J (leaf v))     = v
lookup (true  ∷ᵛ bv) (J (node aˡ _))  = lookup bv aˡ
lookup (false ∷ᵛ bv) (J (node _  aʳ)) = lookup bv aʳ

-- LFSC: read
read : Array → Key → Val
read = flip lookup

insert-≡ : {h : ℕ} → (a : Maybe (Trie h)) → (k : BitVec h) → (v : Val) → (p : v ≢ defᵛ) →
  lookup k (just (insert k v {fromWitnessFalse p} a)) ≡ v

insert-≡ N                   []ᵛ           _ _ = refl
insert-≡ N                   (true  ∷ᵛ bv) v p = insert-≡ N bv v p
insert-≡ N                   (false ∷ᵛ bv) v p = insert-≡ N bv v p
insert-≡ (J (leaf _))        []ᵛ           _ _ = refl
insert-≡ (J (node aˡ     _)) (true  ∷ᵛ bv) v p = insert-≡ aˡ bv v p
-- extra case split for |node′|
insert-≡ (J (node N     aʳ)) (false ∷ᵛ bv) v p = insert-≡ aʳ bv v p
insert-≡ (J (node (J _) aʳ)) (false ∷ᵛ bv) v p = insert-≡ aʳ bv v p

remove-≡ : {h : ℕ} → (a : Maybe (Trie h)) → (k : BitVec h) → lookup k (remove k a) ≡ defᵛ

remove-≡ N                         []ᵛ           = refl
remove-≡ N                         (true  ∷ᵛ _)  = refl
remove-≡ N                         (false ∷ᵛ _)  = refl
remove-≡ (J (leaf _))              []ᵛ           = refl

remove-≡ (J (node aˡ     N))       (true  ∷ᵛ bv)
  with remove bv aˡ | inspect (remove bv) aˡ
... | N     | _      = refl
... | (J _) | [ eq ] = subst (λ # → lookup bv # ≡ defᵛ) eq (remove-≡ aˡ bv)

remove-≡ (J (node aˡ     (J aʳ)))  (true  ∷ᵛ bv)
  with remove bv aˡ | inspect (remove bv) aˡ
... | N     | _      = refl
... | (J _) | [ eq ] = subst (λ # → lookup bv # ≡ defᵛ) eq (remove-≡ aˡ bv)

remove-≡ (J (node N      aʳ))      (false ∷ᵛ bv)
  with remove bv aʳ | inspect (remove bv) aʳ
... | N     | _      = refl
... | (J _) | [ eq ] = subst (λ # → lookup bv # ≡ defᵛ) eq (remove-≡ aʳ bv)

remove-≡ (J (node (J aˡ) aʳ))      (false ∷ᵛ bv)
  with remove bv aʳ | inspect (remove bv) aʳ
... | N     | _      = refl
... | (J _) | [ eq ] = subst (λ # → lookup bv # ≡ defᵛ) eq (remove-≡ aʳ bv)

write-≡ : (a : Array) → (k : Key) → (v : Val) → read (write a k v) k ≡ v
write-≡ a k v with v ≟ᵛ defᵛ
... | true  because ofʸ refl = remove-≡ a k
... | false because ofⁿ p    = insert-≡ a k v p

trim-≢ : ∀ {n b} → {bv₁ bv₂ : BitVec n} → (b ∷ᵛ bv₁) ≢ (b ∷ᵛ bv₂) → bv₁ ≢ bv₂
trim-≢ {b = b} {bv₁} {bv₂} p n = p $ cong (b ∷ᵛ_) n

insert-≢ : {h : ℕ} → (a : Maybe (Trie h)) → (k₁ k₂ : BitVec h) → (v : Val) → (p : v ≢ defᵛ) →
  k₁ ≢ k₂ → lookup k₂ (just (insert k₁ v {fromWitnessFalse p} a)) ≡ lookup k₂ a

insert-≢ _                   []ᵛ            []ᵛ            _ _ k₁≢k₂ = contradiction refl k₁≢k₂

insert-≢ N                   (true  ∷ᵛ bv₁) (true  ∷ᵛ bv₂) v p k₁≢k₂ =
  insert-≢ N  bv₁ bv₂ v p (trim-≢ k₁≢k₂)

insert-≢ (J (node aˡ    _))  (true  ∷ᵛ bv₁) (true  ∷ᵛ bv₂) v p k₁≢k₂ =
  insert-≢ aˡ bv₁ bv₂ v p (trim-≢ k₁≢k₂)

insert-≢ N                   (true  ∷ᵛ _)   (false ∷ᵛ _)   _ _ _     = refl
insert-≢ (J (node _     _))  (true  ∷ᵛ _)   (false ∷ᵛ _)   _ _ _     = refl
insert-≢ N                   (false ∷ᵛ _)   (true  ∷ᵛ _)   _ _ _     = refl
-- extra case split for |node′|
insert-≢ (J (node N  _))     (false ∷ᵛ _)   (true  ∷ᵛ _)   _ _ _     = refl
insert-≢ (J (node (J _) _))  (false ∷ᵛ _)   (true  ∷ᵛ _)   _ _ _     = refl

insert-≢ N                   (false ∷ᵛ bv₁) (false ∷ᵛ bv₂) v p k₁≢k₂ =
  insert-≢ N  bv₁ bv₂ v p (trim-≢ k₁≢k₂)

-- extra case split for |node′|
insert-≢ (J (node N     aʳ)) (false ∷ᵛ bv₁) (false ∷ᵛ bv₂) v p k₁≢k₂ =
  insert-≢ aʳ bv₁ bv₂ v p (trim-≢ k₁≢k₂)

insert-≢ (J (node (J _) aʳ)) (false ∷ᵛ bv₁) (false ∷ᵛ bv₂) v p k₁≢k₂ =
  insert-≢ aʳ bv₁ bv₂ v p (trim-≢ k₁≢k₂)

remove-≢ : {h : ℕ} → (a : Maybe (Trie h)) → (k₁ k₂ : BitVec h) → k₁ ≢ k₂ →
  lookup k₂ (remove k₁ a) ≡ lookup k₂ a

remove-≢ N []ᵛ _ _ = refl
remove-≢ N (false ∷ᵛ _) _ _ = refl
remove-≢ N (true  ∷ᵛ _) _ _ = refl
remove-≢ (J (leaf v)) []ᵛ []ᵛ k₁≢k₂ = contradiction refl k₁≢k₂

-- XXX - a lot of identical with-abstractions below - how to reduce repetition?

remove-≢ (J (node aˡ N)) (true ∷ᵛ k₁) (true ∷ᵛ k₂) k₁≢k₂
  with remove k₁ aˡ | inspect (remove k₁) aˡ
... | N     | [ eq ] =
  subst (λ # → lookup k₂ # ≡ lookup k₂ aˡ) eq (remove-≢ aˡ k₁ k₂ (trim-≢ k₁≢k₂))
... | (J _) | [ eq ] =
  subst (λ # → lookup k₂ # ≡ lookup k₂ aˡ) eq (remove-≢ aˡ k₁ k₂ (trim-≢ k₁≢k₂))

remove-≢ (J (node aˡ (J x))) (true ∷ᵛ k₁) (true ∷ᵛ k₂) k₁≢k₂
  with remove k₁ aˡ | inspect (remove k₁) aˡ
... | N     | [ eq ] =
  subst (λ # → lookup k₂ # ≡ lookup k₂ aˡ) eq (remove-≢ aˡ k₁ k₂ (trim-≢ k₁≢k₂))
... | (J _) | [ eq ] =
  subst (λ # → lookup k₂ # ≡ lookup k₂ aˡ) eq (remove-≢ aˡ k₁ k₂ (trim-≢ k₁≢k₂))

remove-≢ (J (node aˡ N)) (true ∷ᵛ k₁) (false ∷ᵛ k₂) k₁≢k₂
  with remove k₁ aˡ
... | N     = refl
... | (J _) = refl

remove-≢ (J (node aˡ (J _))) (true ∷ᵛ k₁) (false ∷ᵛ k₂) k₁≢k₂
  with remove k₁ aˡ
... | N     = refl
... | (J _) = refl

remove-≢ (J (node N aˡ)) (false ∷ᵛ k₁) (true ∷ᵛ k₂) k₁≢k₂
  with remove k₁ aˡ
... | N     = refl
... | (J _) = refl

remove-≢ (J (node (J _) aˡ)) (false ∷ᵛ k₁) (true ∷ᵛ k₂) k₁≢k₂
  with remove k₁ aˡ
... | N     = refl
... | (J _) = refl

remove-≢ (J (node N aʳ)) (false ∷ᵛ k₁) (false ∷ᵛ k₂) k₁≢k₂
  with remove k₁ aʳ | inspect (remove k₁) aʳ
... | N     | [ eq ] =
  subst (λ # → lookup k₂ # ≡ lookup k₂ aʳ) eq (remove-≢ aʳ k₁ k₂ (trim-≢ k₁≢k₂))
... | (J _) | [ eq ] =
  subst (λ # → lookup k₂ # ≡ lookup k₂ aʳ) eq (remove-≢ aʳ k₁ k₂ (trim-≢ k₁≢k₂))

remove-≢ (J (node (J _) aʳ)) (false ∷ᵛ k₁) (false ∷ᵛ k₂) k₁≢k₂
  with remove k₁ aʳ | inspect (remove k₁) aʳ
... | N     | [ eq ] =
  subst (λ # → lookup k₂ # ≡ lookup k₂ aʳ) eq (remove-≢ aʳ k₁ k₂ (trim-≢ k₁≢k₂))
... | (J _) | [ eq ] =
  subst (λ # → lookup k₂ # ≡ lookup k₂ aʳ) eq (remove-≢ aʳ k₁ k₂ (trim-≢ k₁≢k₂))

write-≢ : (a : Array) → (k₁ k₂ : Key) → (v : Val) → k₁ ≢ k₂ → read (write a k₁ v) k₂ ≡ read a k₂
write-≢ a k₁ k₂ v k₁≢k₂ with v ≟ᵛ defᵛ
... | true  because ofʸ refl = remove-≢ a k₁ k₂ k₁≢k₂
... | false because ofⁿ p    = insert-≢ a k₁ k₂ v p k₁≢k₂

-- LFSC: row1
row-≡ : (a : Array) → (k : Key) → (v : Val) → Holds (equᶠ {{dsdᵛ}} (read (write a k v) k) v)
row-≡ a k v with read (write a k v) k ≟ᵛ v | inspect (read (write a k v) k ≟ᵛ_) v
... | true  because _     | [ eq ] = holds _ (cong does eq)
... | false because ofⁿ p | _      rewrite write-≡ a k v = contradiction refl p

-- LFSC: row
row-≢ : (a : Array) → (k₁ k₂ : Key) → (v : Val) →
  Holds (notᶠ (equᶠ {{dsdᵏ}} k₁ k₂)) →
  Holds (equᶠ {{dsdᵛ}} (read (write a k₁ v) k₂) (read a k₂))

row-≢ a k₁ k₂ v (holds _ h)
  with read (write a k₁ v) k₂ ≟ᵛ read a k₂ | inspect (read (write a k₁ v) k₂ ≟ᵛ_) (read a k₂)

... | true  because _     | [ eq ] = holds _ (cong does eq)
... | false because ofⁿ p | _      with k₁ ≟ᵏ k₂
... | false because ofⁿ q rewrite write-≢ a k₁ k₂ v q = contradiction refl p

-- LFSC: negativerow
¬-row-≢ : (a : Array) → (k₁ k₂ : Key) → (v : Val) →
  Holds (notᶠ (equᶠ {{dsdᵛ}} (read (write a k₁ v) k₂) (read a k₂))) →
  Holds (equᶠ {{dsdᵏ}} k₁ k₂)

¬-row-≢ a k₁ k₂ v (holds _ h) with does (k₁ ≟ᵏ k₂) | inspect does (k₁ ≟ᵏ k₂)
... | true  | [ eq ] = holds _ eq
... | false | [ eq ] with (holds _ h′) ← row-≢ a k₁ k₂ v (holds _ (f⇒not-t eq)) =
  contradiction h′ (not-¬ (not-t⇒f h))

≢-lookup : {h : ℕ} → {a₁ a₂ : Maybe (Trie h)} → a₁ ≢ a₂ → (∃ λ k → lookup k a₁ ≢ lookup k a₂)
≢-lookup {_}    {N}                {N}                a₁≢a₂ = contradiction refl a₁≢a₂
≢-lookup {zero} {J (leaf v₁ {✓})}  {N}                a₁≢a₂ = []ᵛ , toWitnessFalse ✓
≢-lookup {zero} {N}                {J (leaf v₂ {✓})}  a₁≢a₂ = []ᵛ , ≢-sym (toWitnessFalse ✓)

≢-lookup {zero} {J (leaf v₁ {✓₁})} {J (leaf v₂ {✓₂})} a₁≢a₂
  with v₁ ≟ᵛ v₂
... | true  because ofʸ refl rewrite one-value-✓ ✓₁ ✓₂ = contradiction refl a₁≢a₂
... | false because ofⁿ p                              = []ᵛ , p

-- no |node N N| cases because of |node­✓| magic

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
≢-read a₁≢a₂ = ≢-lookup a₁≢a₂

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

func-≟ {zero} dsdᵗ f₁ f₂ = {!!}
{-
with bv-func-≟ dsdᵗ (f₁ ∘ leaf) (f₂ ∘ leaf)
... | true  because ofʸ p = true  because ofʸ λ { {leaf _} refl → p refl }
... | false because ofⁿ p = false because ofⁿ λ n → p $ λ { {bv₁} {bv₂} refl → n {leaf bv₁} refl }
-}

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
