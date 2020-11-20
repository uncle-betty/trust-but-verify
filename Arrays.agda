open import Data.Nat using (ℕ)

module Arrays (bitsᵏ bitsᵛ : ℕ) where

open import BitVec using (BitVec ; bv-dsd ; bv-sto ; bv-func-≟ ; null)

stoᵏ = bv-sto {bitsᵏ}
dsdᵏ = bv-dsd {bitsᵏ}
dsdᵛ = bv-dsd {bitsᵛ}
defᵏ = null {bitsᵏ}
defᵛ = null {bitsᵛ}

open import Data.Bool using (true ; false ; _∨_ ; not)
open import Data.Bool.Properties using (∨-zeroˡ ; ∨-zeroʳ ; not-¬)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Membership.DecSetoid dsdᵏ using (_∈_ ; _∉_ ; _∈?_)
open import Data.List.Relation.Unary.Any using (here ; there)

open import Data.List.Relation.Unary.Linked
  using () renaming ([] to []ᴸ ; [-] to [-]ᴸ ; _∷_ to _∷ᴸ_)

open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (zero ; suc ; _⊔_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Tree.AVL stoᵏ using (tree)

open import Data.Tree.AVL.Indexed stoᵏ
  using (Tree ; K&_ ; ⊥⁺<[_]<⊤⁺) renaming (lookup to lookup′)

open import Data.Tree.AVL.Map stoᵏ using (Map ; lookup ; insert)
open import Data.Vec using () renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)

open import Function using (_$_ ; _∘_)

open import Level using (Level ; 0ℓ)

open import Relation.Binary
  using (tri< ; tri≈ ; tri> ; Decidable) renaming (DecSetoid to DSD ; StrictTotalOrder to STO)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; trans ; cong ; subst ; inspect ; [_])

open import Relation.Nullary using (Dec ; _because_ ; does ; ofʸ ; ofⁿ ; ¬_)
open import Relation.Nullary.Negation using (contradiction)

open DSD dsdᵏ using () renaming (
    Carrier to Key ; _≈_ to _≈ᵏ_ ; _≟_ to _≟ᵏ_ ; refl to reflᵏ ; sym to symᵏ ; trans to transᵏ
  )

open DSD dsdᵛ using () renaming (
    Carrier to Val ; _≈_ to _≈ᵛ_ ; _≟_ to _≟ᵛ_ ; refl to reflᵛ ; sym to symᵛ ; trans to transᵛ
  )

open STO stoᵏ using () renaming (
    _<_ to _<ᵏ_ ; compare to compᵏ ; trans to <-transᵏ ; irrefl to irreflᵏ ; <-resp-≈ to <-resp-≈ᵏ
  )

open import AVL stoᵏ Val using (V ; flat ; get ; put ; avl-insed ; avl-other)
  renaming (lookup≡get to lookup′≡get ; insert≡put to insert′≡put)

open import SAT using (Env ; Holdsᶜ ; not-t⇒f ; f⇒not-t)
open import SMT using (orᶠ ; notᶠ ; equᶠ ; Holds ; holds)

-- LFSC: Array
Array : Set
Array = Map Val

-- LFSC: write
write : Array → Key → Val → Array
write a k v = insert k v a

-- LFSC: read
read : Array → Key → Val
read a k with lookup k a
... | nothing = defᵛ
... | just v  = v

flatten : Array → List (K& V)
flatten (tree t) = flat t

write′ : List (K& V) → Key → Val → List (K& V)
write′ kvs k v = put k (λ _ → v) kvs

read′ : List (K& V) → Key → Val
read′ kvs k with get k kvs
... | nothing = defᵛ
... | just v  = v

insert≡put : ∀ {h} → (k : Key) → (v : Val) → (t : Tree _ _ _ h) →
  flatten (insert k v (tree t)) ≡ put k (λ _ → v) (flat t)

insert≡put k v t = insert′≡put k (λ _ → v) t ⊥⁺<[ k ]<⊤⁺

lookup≡get : ∀ {h} → (k : Key) → (t : Tree _ _ _ h) → lookup k (tree t) ≡ get k (flat t)
lookup≡get k t = lookup′≡get k t ⊥⁺<[ k ]<⊤⁺

write≡write′ : (a : Array) → (k : Key) → (v : Val) → flatten (write a k v) ≡ write′ (flatten a) k v
write≡write′ (tree t) k v = insert≡put k v t

read≡read′ : (a : Array) → (k : Key) → read a k ≡ read′ (flatten a) k
read≡read′ (tree t) k rewrite lookup≡get k t with get k (flat t)
... | nothing = refl
... | just _  = refl

lookup-insed : (a : Array) → (k : Key) → (v : Val) → lookup k (insert k v a) ≡ just v
lookup-insed a k v = avl-insed k v a

lookup-other : (a : Array) → (k′ k : Key) → (v : Val) → ¬ k′ ≈ᵏ k →
  lookup k (insert k′ v a) ≡ lookup k a

lookup-other a k′ k v k₁≉k₂ = avl-other k k′ v a (k₁≉k₂ ∘ symᵏ)

keys : List (K& V) → List Key
keys = map proj₁

read′-def : ∀ {k kvs} → k ∉ keys kvs → read′ kvs k ≈ᵛ defᵛ
read′-def {k} {[]} p = reflᵛ
read′-def {k} {(k′ , v′) ∷ kvs′} p with compᵏ k′ k
... | tri< _ _  _  = read′-def λ { n → p (there n) }
... | tri≈ _ p₂ _  = contradiction (here (symᵏ p₂)) p
... | tri> _ _  _  = reflᵛ

read′-≈ : ∀ {k₁ k₂} → (kvs : List (K& V)) → k₁ ≈ᵏ k₂ → read′ kvs k₁ ≈ᵛ read′ kvs k₂
read′-≈ {k₁} {k₂} [] p = reflᵛ
read′-≈ {k₁} {k₂} ((k′ , v′) ∷ kvs′) p with compᵏ k′ k₁ | compᵏ k′ k₂
... | tri< _ _ _ | tri< _ _ _ = read′-≈ kvs′ p
... | tri< q _ _ | tri≈ r _ _ = contradiction (proj₁ <-resp-≈ᵏ p q) r
... | tri< q _ _ | tri> r _ _ = contradiction (proj₁ <-resp-≈ᵏ p q) r

... | tri≈ _ q _ | tri< _ r _ = contradiction (transᵏ q p) r
... | tri≈ _ _ _ | tri≈ _ _ _ = reflᵛ
... | tri≈ _ q _ | tri> _ r _ = contradiction (transᵏ q p) r

... | tri> _ _ q | tri< _ _ r = contradiction (proj₂ <-resp-≈ᵏ p q) r
... | tri> _ _ q | tri≈ _ _ r = contradiction (proj₂ <-resp-≈ᵏ p q) r
... | tri> _ _ _ | tri> _ _ _ = reflᵛ

match-keys : (ks : List Key) → (kvs₁ kvs₂ : List (K& V)) →
  (∀ k → k ∈ ks → read′ kvs₁ k ≈ᵛ read′ kvs₂ k) ⊎
  (∃ λ k → ¬ read′ kvs₁ k ≈ᵛ read′ kvs₂ k)

match-keys [] kvs₁ kvs₂ = inj₁ λ k ()
match-keys (k ∷ ks) kvs₁ kvs₂ with match-keys ks kvs₁ kvs₂
... | inj₂ p = inj₂ p
... | inj₁ p with read′ kvs₁ k ≟ᵛ read′ kvs₂ k
... | false because ofⁿ q = inj₂ (k , q)
... | true  because ofʸ q = inj₁ λ {
    k′ (here r)  → transᵛ (transᵛ (read′-≈ kvs₁ r) q) (symᵛ (read′-≈ kvs₂ r)) ;
    k′ (there r) → p k′ r
  }

matched-all : ∀ {kvs₁ kvs₂} →
  (∀ k → k ∈ keys kvs₁ → read′ kvs₁ k ≈ᵛ read′ kvs₂ k) →
  (∀ k → k ∈ keys kvs₂ → read′ kvs₁ k ≈ᵛ read′ kvs₂ k) →
  (∀ k → read′ kvs₁ k ≈ᵛ read′ kvs₂ k)

matched-all {kvs₁} {kvs₂} p₁ p₂ k with k ∈? keys kvs₁ | k ∈? keys kvs₂
... | true  because ofʸ q₁ | true  because _      = p₁ k q₁
... | true  because ofʸ q₁ | false because _      = p₁ k q₁
... | false because _      | true  because ofʸ q₂ = p₂ k q₂
... | false because ofⁿ q₁ | false because ofⁿ q₂ = transᵛ (read′-def q₁) (symᵛ (read′-def q₂))

comp-flat : (kvs₁ kvs₂ : List (K& V)) →
  (∀ k → read′ kvs₁ k ≈ᵛ read′ kvs₂ k) ⊎ (∃ λ k → ¬ read′ kvs₁ k ≈ᵛ read′ kvs₂ k)

comp-flat kvs₁ kvs₂ with match-keys (keys kvs₁) kvs₁ kvs₂
... | inj₂ p = inj₂ p
... | inj₁ p with match-keys (keys kvs₂) kvs₁ kvs₂
... | inj₂ q = inj₂ q
... | inj₁ q = inj₁ (matched-all p q)

∃¬⇒¬∀ : {A : Set} → {B : A → Set} → ∃ (λ a → ¬ B a) → ¬ (∀ a → B a)
∃¬⇒¬∀ (a , b) n = b (n a)

≟-flat : ∀ kvs₁ kvs₂ → Dec (∀ k → read′ kvs₁ k ≈ᵛ read′ kvs₂ k)
≟-flat kvs₁ kvs₂ with comp-flat kvs₁ kvs₂
... | inj₁ p = true  because ofʸ p
... | inj₂ p = false because ofⁿ (∃¬⇒¬∀ p)

infix 4 _≈ᵃ_

_≈ᵃ_ : (a₁ a₂ : Array) → Set
a₁ ≈ᵃ a₂ = ∀ k → read a₁ k ≈ᵛ read a₂ k

infix 4 _≟ᵃ_

_≟ᵃ_ : (a₁ a₂ : Array) → Dec (a₁ ≈ᵃ a₂)
a₁ ≟ᵃ a₂ with ≟-flat (flatten a₁) (flatten a₂)

... | true  because ofʸ p = true  because ofʸ λ k →
  subst (λ # → read a₁ k ≈ᵛ #) (sym $ read≡read′ a₂ k) $
  subst (λ # → # ≈ᵛ read′ (flatten a₂) k) (sym $ read≡read′ a₁ k) $
  p k

... | false because ofⁿ p = false because ofⁿ λ n → p λ k →
  subst (λ # → read′ (flatten a₁) k ≈ᵛ #) (read≡read′ a₂ k) $
  subst (λ # → # ≈ᵛ read a₂ k) (read≡read′ a₁ k) $
  n k

array-dsd : DSD 0ℓ 0ℓ
array-dsd = record {
    Carrier = Array ;
    _≈_ = _≈ᵃ_ ;
    isDecEquivalence = record {
        isEquivalence = record {
            refl  = λ _ → reflᵛ ;
            sym   = λ p k → symᵛ (p k) ;
            trans = λ p₁ p₂ k → transᵛ (p₁ k) (p₂ k)
          } ;
        _≟_ = _≟ᵃ_
      }
  }

comp : (a₁ a₂ : Array) → (∀ k → read a₁ k ≈ᵛ read a₂ k) ⊎ (∃ λ k → ¬ read a₁ k ≈ᵛ read a₂ k)
comp a₁ a₂ with comp-flat (flatten a₁) (flatten a₂)
... | inj₁ p = inj₁ λ k →
  subst (λ # → read a₁ k ≈ᵛ #) (sym $ read≡read′ a₂ k) $
  subst (λ # → # ≈ᵛ read′ (flatten a₂) k) (sym $ read≡read′ a₁ k) $
  p k

... | inj₂ (k , p) = inj₂ (k , λ n → p $
  subst (λ # → read′ (flatten a₁) k ≈ᵛ #) (read≡read′ a₂ k) $
  subst (λ # → # ≈ᵛ read a₂ k) (read≡read′ a₁ k) $
  n)

module _ (env : Env) where
  ext-lem₁ : ∀ a₁ a₂ → (∀ k → read a₁ k ≈ᵛ read a₂ k) → does (a₁ ≟ᵃ a₂) ≡ true
  ext-lem₁ a₁ a₂ p with a₁ ≟ᵃ a₂
  ... | true  because ofʸ _ = refl
  ... | false because ofⁿ q = contradiction p q

  ext-lem₂ : ∀ a₁ a₂ k → ¬ read a₁ k ≈ᵛ read a₂ k → not (does (read a₁ k ≟ᵛ read a₂ k)) ≡ true
  ext-lem₂ a₁ a₂ k p with read a₁ k ≟ᵛ read a₂ k
  ... | true  because ofʸ q = contradiction q p
  ... | false because ofⁿ _ = refl

  -- LFSC: ext
  exten : (a₁ a₂ : Array) →
    ((k : Key) →
      Holds (orᶠ (equᶠ {{array-dsd}} a₁ a₂) (notᶠ (equᶠ {{dsdᵛ}} (read a₁ k) (read a₂ k)))) →
      Holdsᶜ env []) →
    Holdsᶜ env []

  exten a₁ a₂ p with comp a₁ a₂
  ... | inj₁ q =
    let
      s₁ = λ # → # ∨ not (does (read a₁ defᵏ ≟ᵛ read a₂ defᵏ)) ≡ true
      s₂ = sym $ ext-lem₁ a₁ a₂ q
      s₃ = ∨-zeroˡ (not (does (read a₁ defᵏ ≟ᵛ read a₂ defᵏ)))
    in
      p defᵏ (holds _ (subst s₁ s₂ s₃))

  ... | inj₂ (k , q) =
    let
      s₁ = λ # → does (a₁ ≟ᵃ a₂) ∨ # ≡ true
      s₂ = sym $ ext-lem₂ a₁ a₂ k q
      s₃ = ∨-zeroʳ (does (a₁ ≟ᵃ a₂))
    in
      p k (holds _ (subst s₁ s₂ s₃))

-- LFSC: row1
row-≈ : (a : Array) → (k : Key) → (v : Val) → Holds (equᶠ {{dsdᵛ}} (read (write a k v) k) v)
row-≈ a k v with read (write a k v) k ≟ᵛ v | inspect (read (write a k v) k ≟ᵛ_) v
... | true  because _     | [ eq ] = holds _ (cong does eq)
... | false because ofⁿ p | _      rewrite lookup-insed a k v = contradiction reflᵛ p

-- LFSC: row
row-≉ : (a : Array) → (k₁ k₂ : Key) → (v : Val) →
  Holds (notᶠ (equᶠ {{dsdᵏ}} k₁ k₂)) →
  Holds (equᶠ {{dsdᵛ}} (read (write a k₁ v) k₂) (read a k₂))

row-≉ a k₁ k₂ v (holds _ h)
  with read (write a k₁ v) k₂ ≟ᵛ read a k₂ | inspect (read (write a k₁ v) k₂ ≟ᵛ_) (read a k₂)

... | true  because _     | [ eq ] = holds _ (cong does eq)
... | false because ofⁿ p | _      with k₁ ≟ᵏ k₂
... | false because ofⁿ q rewrite lookup-other a k₁ k₂ v q = contradiction reflᵛ p

-- LFSC: negativerow
¬-row-≉ : (a : Array) → (k₁ k₂ : Key) → (v : Val) →
  Holds (notᶠ (equᶠ {{dsdᵛ}} (read (write a k₁ v) k₂) (read a k₂))) →
  Holds (equᶠ {{dsdᵏ}} k₁ k₂)

¬-row-≉ a k₁ k₂ v (holds _ h) with does (k₁ ≟ᵏ k₂) | inspect does (k₁ ≟ᵏ k₂)
... | true  | [ eq ] = holds _ eq
... | false | [ eq ] with (holds _ h′) ← row-≉ a k₁ k₂ v (holds _ (f⇒not-t eq)) =
  contradiction h′ (not-¬ (not-t⇒f h))

data Trie : ℕ → Set where
  node : {h : ℕ} → Maybe (Trie h) → Maybe (Trie h) → Trie (suc h)
  leaf : Val → Trie 0

lookupᵗ : {h : ℕ} → BitVec h → Maybe (Trie h) → Maybe Val
lookupᵗ _             nothing             = nothing
lookupᵗ []ᵛ           (just (leaf v))     = just v
lookupᵗ (true  ∷ᵛ bv) (just (node ml _))  = lookupᵗ bv ml
lookupᵗ (false ∷ᵛ bv) (just (node _  mr)) = lookupᵗ bv mr

insertᵗ : {h : ℕ} → BitVec h → Val → Maybe (Trie h) → Maybe (Trie h)
insertᵗ []ᵛ           v nothing             = just $ leaf v
insertᵗ (true  ∷ᵛ bv) v nothing             = just $ let t = insertᵗ bv v nothing in node t nothing
insertᵗ (false ∷ᵛ bv) v nothing             = just $ let t = insertᵗ bv v nothing in node nothing t
insertᵗ []ᵛ           v (just (leaf _))     = just $ leaf v
insertᵗ (true  ∷ᵛ bv) v (just (node ml mr)) = just $ let t = insertᵗ bv v ml in node t mr
insertᵗ (false ∷ᵛ bv) v (just (node ml mr)) = just $ let t = insertᵗ bv v mr in node ml t

insed : {h : ℕ} → (mt : Maybe (Trie h)) → (k : BitVec h) → (v : Val) →
  lookupᵗ k (insertᵗ k v mt) ≡ just v

insed nothing             []ᵛ           _ = refl
insed nothing             (true  ∷ᵛ bv) v = insed nothing bv v
insed nothing             (false ∷ᵛ bv) v = insed nothing bv v
insed (just (leaf _))     []ᵛ           _ = refl
insed (just (node ml _ )) (true  ∷ᵛ bv) v = insed ml bv v
insed (just (node _  mr)) (false ∷ᵛ bv) v = insed mr bv v

open DSD using () renaming (Carrier to Carˣ ; _≈_ to _≈ˣ_ ; _≟_ to _≟ˣ_ ; refl to reflˣ)

trim-≉ : ∀ {n b} → {bv₁ bv₂ : BitVec n} → ¬ _≈ˣ_ bv-dsd (b ∷ᵛ bv₁) (b ∷ᵛ bv₂) → ¬ _≈ˣ_ bv-dsd bv₁ bv₂
trim-≉ {b = b} {bv₁} {bv₂} p n = p $ cong (b ∷ᵛ_) n

other : {h : ℕ} → (mt : Maybe (Trie h)) → (k₁ k₂ : BitVec h) → (v : Val) → ¬ _≈ˣ_ bv-dsd k₁ k₂ →
  lookupᵗ k₂ (insertᵗ k₁ v mt) ≡ lookupᵗ k₂ mt

other _                   []ᵛ            []ᵛ            _ k₁≉k₂ = contradiction (reflˣ bv-dsd) k₁≉k₂
other nothing             (true  ∷ᵛ bv₁) (true  ∷ᵛ bv₂) v k₁≉k₂ = other nothing bv₁ bv₂ v (trim-≉ k₁≉k₂)
other (just (node ml _ )) (true  ∷ᵛ bv₁) (true  ∷ᵛ bv₂) v k₁≉k₂ = other ml      bv₁ bv₂ v (trim-≉ k₁≉k₂)
other nothing             (true  ∷ᵛ _)   (false ∷ᵛ _)   _ _     = refl
other (just (node _  mr)) (true  ∷ᵛ _)   (false ∷ᵛ _)   _ _     = refl
other nothing             (false ∷ᵛ _)   (true  ∷ᵛ _)   _ _     = refl
other (just (node ml _ )) (false ∷ᵛ _)   (true  ∷ᵛ _)   _ _     = refl
other nothing             (false ∷ᵛ bv₁) (false ∷ᵛ bv₂) v k₁≉k₂ = other nothing bv₁ bv₂ v (trim-≉ k₁≉k₂)
other (just (node _  mr)) (false ∷ᵛ bv₁) (false ∷ᵛ bv₂) v k₁≉k₂ = other mr      bv₁ bv₂ v (trim-≉ k₁≉k₂)

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
  T-≈ (f₁ (node nothing nothing)) (f₂ (node nothing nothing)) →
  ({t₁ t₂ : Trie h} → t₁ ≡ t₂ → T-≈ (splitˡ f₁ t₁) (splitˡ f₂ t₂)) →
  ({t₁ t₂ : Trie h} → t₁ ≡ t₂ → T-≈ (splitʳ f₁ t₁) (splitʳ f₂ t₂)) →
  ({l₁ l₂ : Trie h} → l₁ ≡ l₂ → {r₁ r₂ : Trie h} → r₁ ≡ r₂ →
    T-≈ (split f₁ l₁ r₁) (split f₂ l₂ r₂)) →
  ({t₁ t₂ : Trie (suc h)} → t₁ ≡ t₂ → T-≈ (f₁ t₁) (f₂ t₂))

join⁺ T-≈ f₁ f₂ p q r s {node nothing   nothing}   refl = p
join⁺ T-≈ f₁ f₂ p q r s {node (just tˡ) nothing}   refl = q refl
join⁺ T-≈ f₁ f₂ p q r s {node nothing   (just tʳ)} refl = r refl
join⁺ T-≈ f₁ f₂ p q r s {node (just tˡ) (just tʳ)} refl = s refl refl

Func-≈ = λ {h : ℕ} (dsdᵗ : DSD 0ℓ 0ℓ) (f₁ f₂ : Trie h → Carˣ dsdᵗ) →
  (∀ {t₁} {t₂} → t₁ ≡ t₂ → _≈ˣ_ dsdᵗ (f₁ t₁) (f₂ t₂))

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
  with (_≟ˣ_ dsdᵗ) (f₁ (node nothing nothing)) (f₂ (node nothing nothing))
... | false because ofⁿ p = false because ofⁿ λ n →  p $ n refl
... | true  because ofʸ p
  with func-≟ dsdᵗ (splitˡ f₁) (splitˡ f₂)
... | false because ofⁿ q = false because ofⁿ (joinˡ (_≈ˣ_ dsdᵗ) f₁ f₂ q)
... | true  because ofʸ q
  with func-≟ dsdᵗ (splitʳ f₁) (splitʳ f₂)
... | false because ofⁿ r = false because ofⁿ (joinʳ (_≈ˣ_ dsdᵗ) f₁ f₂ r)
... | true  because ofʸ r
  with func-≟ (build-dsd h dsdᵗ) (split f₁) (split f₂)
... | false because ofⁿ s = false because ofⁿ (join⁻ (_≈ˣ_ dsdᵗ) f₁ f₂ s)
... | true  because ofʸ s = true  because ofʸ (join⁺ (_≈ˣ_ dsdᵗ) f₁ f₂ p q r s)

just-inj : {ℓ : Level} → {S : Set ℓ} → {x y : S} → just x ≡ just y → x ≡ y
just-inj refl = refl

leaf-inj : {x y : Val} → leaf x ≡ leaf y → x ≡ y
leaf-inj refl = refl

node-≢ˡ : ∀ {h ml₁ ml₂ mr₁ mr₂} → ml₁ ≢ ml₂ → node {h} ml₁ mr₁ ≢ node {h} ml₂ mr₂
node-≢ˡ p refl = contradiction refl p

node-≢ʳ : ∀ {h ml₁ ml₂ mr₁ mr₂} → mr₁ ≢ mr₂ → node {h} ml₁ mr₁ ≢ node {h} ml₂ mr₂
node-≢ʳ p refl = contradiction refl p

lookup-≋ : {h : ℕ} → (a₁ a₂ : Maybe (Trie h)) →
  (∀ k → lookupᵗ k a₁ ≡ lookupᵗ k a₂) ⊎ (∃ λ k → lookupᵗ k a₁ ≢ lookupᵗ k a₂)

lookup-≋        nothing          nothing          = inj₁ λ _ → refl
lookup-≋ {zero} (just (leaf v₁)) nothing          = inj₂ ([]ᵛ , λ ())
lookup-≋ {zero} nothing          (just (leaf v₂)) = inj₂ ([]ᵛ , λ ())

lookup-≋ {zero} (just (leaf v₁)) (just (leaf v₂))
  with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = inj₁ λ _ → refl
... | false because ofⁿ p    = inj₂ ([]ᵛ , p ∘ just-inj)

lookup-≋ {suc h} (just (node ml₁ mr₁)) nothing
  with lookup-≋ ml₁ nothing
... | inj₂ (k , p) = inj₂ (true ∷ᵛ k , p)
... | inj₁ p
  with lookup-≋ mr₁ nothing
... | inj₂ (k , q) = inj₂ (false ∷ᵛ k , q)
... | inj₁ q = inj₁ λ { (true ∷ᵛ k) → p k ; (false ∷ᵛ k) → q k }

lookup-≋ {suc h} nothing (just (node ml₂ mr₂))
  with lookup-≋ nothing ml₂
... | inj₂ (k , p) = inj₂ (true ∷ᵛ k , p)
... | inj₁ p
  with lookup-≋ nothing mr₂
... | inj₂ (k , q) = inj₂ (false ∷ᵛ k , q)
... | inj₁ q = inj₁ λ { (true ∷ᵛ k) → p k ; (false ∷ᵛ k) → q k }

lookup-≋ {suc h} (just (node ml₁ mr₁)) (just (node ml₂ mr₂))
  with lookup-≋ ml₁ ml₂
... | inj₂ (k , p) = inj₂ (true ∷ᵛ k , p)
... | inj₁ p
  with lookup-≋ mr₁ mr₂
... | inj₂ (k , q) = inj₂ (false ∷ᵛ k , q)
... | inj₁ q = inj₁ λ { (true ∷ᵛ k) → p k ; (false ∷ᵛ k) → q k }

array-≟ : {h : ℕ} → (a₁ a₂ : Maybe (Trie h)) → Dec (a₁ ≡ a₂)
array-≟ {zero} nothing          nothing          = true  because ofʸ refl
array-≟ {zero} nothing          (just (leaf v₂)) = false because ofⁿ λ ()
array-≟ {zero} (just (leaf v₁)) nothing          = false because ofⁿ λ ()

array-≟ {zero} (just (leaf v₁)) (just (leaf v₂))
  with v₁ ≟ᵛ v₂
... | true  because ofʸ refl = true  because ofʸ refl
... | false because ofⁿ p    = false because ofⁿ (p ∘ leaf-inj ∘ just-inj)

array-≟ {suc h} nothing  nothing  = true  because ofʸ refl
array-≟ {suc h} nothing  (just _) = false because ofⁿ λ ()
array-≟ {suc h} (just x) nothing  = false because ofⁿ λ ()

array-≟ {suc h} (just (node ml₁ mr₁)) (just (node ml₂ mr₂))
  with array-≟ ml₁ ml₂
... | false because ofⁿ p    = false because ofⁿ (node-≢ˡ p ∘ just-inj)
... | true  because ofʸ refl
  with array-≟ mr₁ mr₂
... | false because ofⁿ q    = false because ofⁿ (node-≢ʳ q ∘ just-inj)
... | true  because ofʸ refl = true  because ofʸ refl
