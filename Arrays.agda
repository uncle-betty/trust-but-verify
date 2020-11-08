open import Level using (0ℓ)
open import Relation.Binary.Bundles using () renaming (DecSetoid to DSD ; StrictTotalOrder to STO)

module Arrays (stoᵏ : STO 0ℓ 0ℓ 0ℓ) (dsdᵛ : DSD 0ℓ 0ℓ)
  (defᵏ : STO.Carrier stoᵏ) (defᵛ : DSD.Carrier dsdᵛ) where

dsdᵏ = STO.decSetoid stoᵏ

open import Data.Bool using (Bool ; true ; false ; _∨_ ; not)
open import Data.Bool.Properties using (∨-zeroˡ ; ∨-zeroʳ)
open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Properties using () renaming (≡-dec to ≡-decˡ)
open import Data.List.Membership.DecSetoid dsdᵏ using (_∈_ ; _∉_ ; _∈?_)
open import Data.List.Relation.Unary.Any using (here ; there)

open import Data.List.Relation.Unary.Linked
  using () renaming ([] to []ᴸ ; [-] to [-]ᴸ ; _∷_ to _∷ᴸ_)

open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; ∃)
open import Data.Product.Properties using () renaming (≡-dec to ≡-decᵖ)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Tree.AVL stoᵏ using (tree)

open import Data.Tree.AVL.Indexed stoᵏ
  using (Tree ; K&_ ; const ; ⊥⁺<[_]<⊤⁺) renaming (lookup to lookup′)

open import Data.Tree.AVL.Map stoᵏ using (Map ; empty ; lookup ; insert)

open import Function using (id ; _$_ ; _∘_)

open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; ≢-sym ; trans ; cong ; subst ; inspect ; [_])

open import Relation.Nullary using (Dec ; _because_ ; does ; ofʸ ; ofⁿ ; ¬_)
open import Relation.Nullary.Negation using (contraposition ; contradiction)

open DSD dsdᵏ using () renaming (
    Carrier to K ; _≈_ to _≈ᵏ_ ; _≟_ to _≟ᵏ_ ; refl to reflᵏ ; sym to symᵏ ; trans to transᵏ
  )

open DSD dsdᵛ using () renaming (
    Carrier to Val ; _≈_ to _≈ᵛ_ ; _≟_ to _≟ᵛ_ ; refl to reflᵛ ; sym to symᵛ ; trans to transᵛ
  )

open STO stoᵏ using () renaming (
    _<_ to _<ᵏ_ ; compare to compᵏ ; trans to <-transᵏ ; irrefl to irreflᵏ ; <-resp-≈ to <-resp-≈ᵏ
  )

open import AVL stoᵏ Val using (V ; flat ; get ; put)
  renaming (lookup≡get to lookup′≡get ; insert≡put to insert′≡put)

open import SAT using (Env ; Holdsᶜ)
open import SMT using (orᶠ ; notᶠ ; equᶠ ; Holds ; holds)

-- LFSC: Array
Array : Set
Array = Map Val

-- LFSC: write
write : Array → K → Val → Array
write a k v = insert k v a

-- LFSC: read
read : Array → K → Val
read a k with lookup k a
... | nothing = defᵛ
... | just v  = v

flatten : Array → List (K& V)
flatten (tree t) = flat t

write′ : List (K& V) → K → Val → List (K& V)
write′ kvs k v = put k (λ _ → v) kvs

read′ : List (K& V) → K → Val
read′ kvs k with get k kvs
... | nothing = defᵛ
... | just v  = v

insert≡put : ∀ {h} → (k : K) → (v : Val) → (t : Tree _ _ _ h) →
  flatten (insert k v (tree t)) ≡ put k (λ _ → v) (flat t)

insert≡put k v t = insert′≡put k (λ _ → v) t ⊥⁺<[ k ]<⊤⁺

lookup≡get : ∀ {h} → (k : K) → (t : Tree _ _ _ h) → lookup k (tree t) ≡ get k (flat t)
lookup≡get k t = lookup′≡get k t ⊥⁺<[ k ]<⊤⁺

write≡write′ : (a : Array) → (k : K) → (v : Val) → flatten (write a k v) ≡ write′ (flatten a) k v
write≡write′ (tree t) k v = insert≡put k v t

read≡read′ : (a : Array) → (k : K) → read a k ≡ read′ (flatten a) k
read≡read′ (tree t) k rewrite lookup≡get k t with get k (flat t)
... | nothing = refl
... | just _  = refl

keys : List (K& V) → List K
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

match-keys : (ks : List K) → (kvs₁ kvs₂ : List (K& V)) →
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
    ((k : K) →
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
