open import Agda.Primitive using (Level)
open import Relation.Binary.Bundles using () renaming (StrictTotalOrder to STO)
open import Data.Tree.AVL.Indexed using (Value)
open import Relation.Binary.PropositionalEquality using (_≡_ ; subst)

module Avl
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
  (sto : STO ℓ₁ ℓ₂ ℓ₃)
  (V : Value sto ℓ₄)
  (equal′ : ∀ {x y} → STO._≈_ sto x y → x ≡ y)
  (reduce′ : ∀ {k} p →
    (v : Value.family {ℓ₁} {ℓ₂} {ℓ₃} {sto} {ℓ₄} V k) →
    Value.respects {ℓ₁} {ℓ₂} {ℓ₃} {sto} {ℓ₄} V p v ≡ v) where

open import Agda.Primitive using (_⊔_) renaming (lzero to 0ℓ)

open import Data.Bool using (true ; false)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++ᴬ)

open import Data.List.Relation.Unary.Linked
  using (Linked) renaming ([] to []ᴸ ; [-] to [-]ᴸ ; _∷_ to _∷ᴸ_)

open import Data.List.Properties using (++-monoid)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (suc)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Data.Tree.AVL.Indexed sto
  using (
    Key⁺ ;  K&_ ;
    _<⁺_ ; _<_<_ ; [_]ᴿ ; ⊥⁺ ; ⊤⁺ ; ⊥⁺<[_]<⊤⁺ ; trans⁺ ;
    Tree ; leaf ; node ; 0# ; 1# ; ∼- ; ∼0 ; ∼+ ;
    lookup ; insertWith ; joinˡ⁺ ; joinʳ⁺
  ) renaming ([_] to [_]ᴱ)

open import Function using (id ; _∘_)

open import Relation.Binary using (Transitive ; tri< ; tri≈ ; tri>)

open import Relation.Binary.Construct.Add.Extrema.Strict (STO._<_ sto)
  using () renaming ([<]-injective to strip-<⁺)

open import Relation.Binary.PropositionalEquality
  using (refl ; _≢_ ; trans ; sym ; ≢-sym ; cong ; inspect ; [_])

open import Relation.Nullary using (Dec ; _because_ ; ofʸ ; ofⁿ ; yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import Tactic.MonoidSolver using (solve)

open STO sto using () renaming (_<_ to <ᴷ ; trans to <-transᴷ ; compare to compᴷ ; <-resp-≈ to <-resp-≡ᴷ)
open STO.Eq sto using () renaming (sym to symᴷ ; trans to transᴷ ; _≈_ to _≡ᴷ_ ; refl to reflexᴷ)

Key = STO.Carrier sto
Val = Value.family {ℓ₁} {ℓ₂} {ℓ₃} {sto} {ℓ₄} V
V≈  = Value.respects {ℓ₁} {ℓ₂} {ℓ₃} {sto} {ℓ₄} V

equal : ∀ {x y} → x ≡ᴷ y → x ≡ y
equal = equal′

reduce : ∀ {k} p → (v : Val k) → V≈ p v ≡ v
reduce = reduce′

lo<up : ∀ {l u h} → Tree V l u h → l <⁺ u
lo<up     (leaf l<u)       = l<u
lo<up {l} (node _ tˡ tʳ _) = trans⁺ l (lo<up tˡ) (lo<up tʳ)

pivot : ∀ {l u h} → Tree V l u (suc h) → Key
pivot (node (k′ , _) _ _ _) = k′

pi<up : ∀ {l u h} → (t : Tree V l u (suc h)) → [ pivot t ]ᴱ <⁺ u
pi<up (node _     _    (leaf l<u)       _) = l<u
pi<up (node (k′ , _) _ (node _ tˡ tʳ _) _) = trans⁺ [ k′ ]ᴱ (lo<up tˡ) (lo<up tʳ)

lo<pi : ∀ {l u h} → (t : Tree V l u (suc h)) → l <⁺ [ pivot t ]ᴱ
lo<pi     (node _ (leaf l<u)       _ _) = l<u
lo<pi {l} (node _ (node _ tˡ tʳ _) _ _) = trans⁺ l (lo<up tˡ) (lo<up tʳ)

flat : ∀ {l u h} → Tree V l u h → List (K& V)
flat (leaf _)          = []
flat (node kv tˡ tʳ _) = flat tˡ ++ kv ∷ flat tʳ

data <ᴸ : K& V → K& V → Set (ℓ₁ ⊔ ℓ₃) where
  l<l : ∀ {k₁ k₂} → [ k₁ ]ᴱ <⁺ [ k₂ ]ᴱ → (v₁ : Val k₁) → (v₂ : Val k₂) → <ᴸ (k₁ , v₁) (k₂ , v₂)

transᴸ : Transitive <ᴸ
transᴸ {k₁ , v₁} {k₂ , v₂} {k₃ , v₃} (l<l x<y v₁ v₂) (l<l y<z v₂ v₃) =
  l<l (trans⁺ [ k₁ ]ᴱ x<y y<z) v₁ v₃

Lo : Key⁺ → Pred (K& V) (ℓ₁ ⊔ ℓ₃)
Lo l (k , _) = l <⁺ [ k ]ᴱ

Up : Key⁺ → Pred (K& V) (ℓ₁ ⊔ ℓ₃)
Up u (k , _) = [ k ]ᴱ <⁺ u

lo-lax : ∀ {l k kvs} → l <⁺ k → All (Lo k) kvs → All (Lo l) kvs
lo-lax l<k []ᴬ = []ᴬ
lo-lax {l} {k} {(k′ , v′) ∷ kvs′} l<k (p ∷ᴬ ps) = trans⁺ l l<k p ∷ᴬ lo-lax l<k ps

up-lax : ∀ {k u kvs} → k <⁺ u → All (Up k) kvs → All (Up u) kvs
up-lax k<u []ᴬ = []ᴬ
up-lax {k} {u} {(k′ , v′) ∷ kvs′} k<u (p ∷ᴬ ps) = trans⁺ [ k′ ]ᴱ p k<u ∷ᴬ up-lax k<u ps

all-lo : ∀ {l u h} → (t : Tree V l u h) → All (Lo l) (flat t)
all-lo (leaf _) = []ᴬ
all-lo t@(node (k′ , v′) tˡ tʳ _) =
  let aˡ = all-lo tˡ in
  let aʳ = all-lo tʳ in
  ++ᴬ aˡ (lo<pi t ∷ᴬ (lo-lax (lo<pi t) aʳ))

all-up : ∀ {l u h} → (t : Tree V l u h) → All (Up u) (flat t)
all-up (leaf _) = []ᴬ
all-up t@(node (k′ , v′) tˡ tʳ _) =
  let aˡ = all-up tˡ in
  let aʳ = all-up tʳ in
  ++ᴬ (up-lax (pi<up t) aˡ) ((pi<up t) ∷ᴬ aʳ)

{-
∷ᴸ⁺ : ∀ {k xs} → (v : Val k) → Linked <ᴸ xs → All (Lo [ k ]ᴱ) xs → Linked <ᴸ ((k , v) ∷ xs)
∷ᴸ⁺               v []ᴸ       []ᴬ        = [-]ᴸ
∷ᴸ⁺ {xs = x ∷ xs} v [-]ᴸ      (a ∷ᴬ []ᴬ) = l<l a v (proj₂ x) ∷ᴸ [-]ᴸ
∷ᴸ⁺ {xs = x ∷ xs} v (l ∷ᴸ ls) (a ∷ᴬ as)  = l<l a v (proj₂ x) ∷ᴸ l ∷ᴸ ls
-}

++ᴸ : ∀ {k xs ys} → Linked <ᴸ xs → Linked <ᴸ ys → All (Up [ k ]ᴱ) xs → All (Lo [ k ]ᴱ) ys →
  (v : Val k) → Linked <ᴸ (xs ++ (k , v) ∷ ys)

++ᴸ {xs = []}           {[]}           []ᴸ       []ᴸ       []ᴬ       []ᴬ       v = [-]ᴸ

++ᴸ {xs = []}           {y₁ ∷ []}      []ᴸ       [-]ᴸ      []ᴬ       (b ∷ᴬ bs) v =
  l<l b v (proj₂ y₁) ∷ᴸ [-]ᴸ

++ᴸ {xs = []}           {y₁ ∷ y₂ ∷ ys} []ᴸ       (m ∷ᴸ ms) []ᴬ       (b ∷ᴬ bs) v =
  l<l b v (proj₂ y₁) ∷ᴸ m ∷ᴸ ms

++ᴸ {xs = x₁ ∷ []}      {[]}           [-]ᴸ      []ᴸ       (a ∷ᴬ as) []ᴬ       v =
  l<l a (proj₂ x₁) v ∷ᴸ [-]ᴸ

++ᴸ {xs = x₁ ∷ []}      {y₁ ∷ []}      [-]ᴸ      [-]ᴸ      (a ∷ᴬ as) (b ∷ᴬ bs) v =
  l<l a (proj₂ x₁) v ∷ᴸ l<l b v (proj₂ y₁) ∷ᴸ [-]ᴸ

++ᴸ {xs = x₁ ∷ []}      {y₁ ∷ _ ∷ _}   [-]ᴸ      (m ∷ᴸ ms) (a ∷ᴬ as) (b ∷ᴬ bs) v =
  l<l a (proj₂ x₁) v ∷ᴸ l<l b v (proj₂ y₁) ∷ᴸ m ∷ᴸ ms

++ᴸ {xs = x₁ ∷ x₂ ∷ xs} {[]}           (l ∷ᴸ ls) []ᴸ       (a ∷ᴬ as) []ᴬ       v =
  l ∷ᴸ ++ᴸ ls []ᴸ as []ᴬ v

++ᴸ {xs = x₁ ∷ x₂ ∷ xs} {_ ∷ []}       (l ∷ᴸ ls) [-]ᴸ      (a ∷ᴬ as) (b ∷ᴬ bs) v =
  l ∷ᴸ ++ᴸ ls [-]ᴸ as (b ∷ᴬ bs) v

++ᴸ {xs = x₁ ∷ x₂ ∷ xs} {_ ∷ _ ∷ _}    (l ∷ᴸ ls) (m ∷ᴸ ms) (a ∷ᴬ as) (b ∷ᴬ bs) v =
  l ∷ᴸ ++ᴸ ls (m ∷ᴸ ms) as (b ∷ᴬ bs) v

ordered : ∀ {l u h} → (t : Tree V l u h) → Linked <ᴸ (flat t)
ordered (leaf l<u) = []ᴸ
ordered (node (k′ , v′) tˡ tʳ _) =
  let x₁ = ordered tˡ in
  let x₂ = ordered tʳ in
  ++ᴸ x₁ x₂ (all-up tˡ) (all-lo tʳ) v′

get : (k : Key) → List (K& V) → Maybe (Val k)
get k [] = nothing

get k ((k′ , v′) ∷ xs) with compᴷ k′ k
... | tri< _ _ _ = get k xs
... | tri≈ _ p _ = just (V≈ p v′)
... | tri> _ _ _ = nothing

put : (k : Key) → (f : Maybe (Val k) → Val k) → (l : List (K& V)) → List (K& V)
put k f [] = (k , f nothing) ∷ []

put k f ((k′ , v′) ∷ kvs) with compᴷ k k′
... | tri< _ _  _ = (k , f nothing) ∷ (k′ , v′) ∷ kvs
... | tri≈ _ p₂ _ = (k′ , V≈ p₂ (f (just (V≈ (symᴷ p₂) v′)))) ∷ kvs
... | tri> _ _  _ = (k′ , v′) ∷ (put k f kvs)

lookup≡get : ∀ {l u h} → (k : Key) → (t : Tree V l u h) → (l<k<u : l < k < u) →
  lookup k t l<k<u ≡ get k (flat t)

lookup≡get k t l<k<u = {!!}

insert≡put : ∀ {l u h} → (k : Key) → (f : Maybe (Val k) → Val k) → (t : Tree V l u h) →
  (l<k<u : l < k < u) → flat (proj₂ (insertWith k f t l<k<u)) ≡ put k f (flat t)

insert≡put k f t l<k<u = {!!}

get-insed : ∀ {k} f kvs → get k (put k f kvs) ≡ just (f (get k kvs))

get-insed {k} f kvs with compᴷ k k | inspect (compᴷ k) k
get-insed {k} f _                  | tri< _ p₁ _ | _ = contradiction reflexᴷ p₁
get-insed {k} f _                  | tri> _ p₁ _ | _ = contradiction reflexᴷ p₁

get-insed {k} f []                 | tri≈ _ p₁ _ | [ eq₁ ]
  rewrite eq₁ | reduce p₁ (f nothing)
  = refl

get-insed {k} f ((k′ , v′) ∷ kvs′) | tri≈ _ p₁ _ | [ eq₁ ]
  with compᴷ k k′ | compᴷ k′ k | inspect (compᴷ k) k′ | inspect (compᴷ k′) k

... | tri< p₂ _  _  | tri< _  _  p₃ | _       | _       = contradiction p₂ p₃
... | tri< p₂ _  _  | tri≈ _  _  p₃ | _       | _       = contradiction p₂ p₃
... | tri≈ _  p₂ _  | tri< _  p₃ _  | _       | _       = contradiction (symᴷ p₂) p₃
... | tri≈ _  p₂ _  | tri> _  p₃ _  | _       | _       = contradiction (symᴷ p₂) p₃
... | tri> _  _  p₂ | tri≈ p₃ _  _  | _       | _       = contradiction p₂ p₃
... | tri> _  _  p₂ | tri> p₃ _  _  | _       | _       = contradiction p₂ p₃

... | tri< p₂ _  _  | tri> _  _  p₃ | _       | _       rewrite eq₁ | reduce p₁ (f nothing) = refl
... | tri> _  _  p₂ | tri< p₃ _  _  | [ eq₂ ] | [ eq₃ ] rewrite eq₃ = get-insed f kvs′

... | tri≈ _  p₂ _  | tri≈ _  p₃ _  | [ eq₂ ] | [ eq₃ ] with equal p₂
... | refl
  rewrite eq₃
        | reduce p₃ v′
        | reduce (symᴷ p₂) v′
        | reduce p₂ (f (just v′))
        | reduce p₃ (f (just v′))
  = refl

get-other : ∀ {k k′} f kvs → ¬ k′ ≡ᴷ k → get k′ (put k f kvs) ≡ get k′ kvs

get-other {k} {k′} f [] k′≢k with compᴷ k k′
... | tri< _  _  _  = refl
... | tri≈ _  p₁ _  = contradiction (symᴷ p₁) k′≢k
... | tri> _  _  _  = refl

get-other {k} {k′} f ((k″ , v″) ∷ kvs″) k′≢k with compᴷ k k′ | inspect (compᴷ k) k′

get-other {k} {k′} f ((k″ , v″) ∷ kvs″) k′≢k | tri< _  p₁ _  | [ eq₁ ]
  with compᴷ k k″ | compᴷ k″ k′ | inspect (compᴷ k″) k′

... | tri< _  _  _  | tri< _  _  _  | [ eq₂ ] rewrite eq₁ | eq₂ = refl
... | tri< _  _  _  | tri≈ _  _  _  | [ eq₂ ] rewrite eq₁ | eq₂ = refl
... | tri< _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₁ | eq₂ = refl

... | tri≈ _  _  _  | tri< _  _  _  | [ eq₂ ] rewrite eq₂ = refl
... | tri≈ _  p₂ _  | tri≈ _  p₃ _  | [ eq₂ ] = contradiction (transᴷ p₂ p₃) p₁
... | tri≈ _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₂ = refl

... | tri> _  _  _  | tri< _  _  _  | [ eq₂ ] rewrite eq₂ = get-other f kvs″ k′≢k
... | tri> _  _  _  | tri≈ _  _  _  | [ eq₂ ] rewrite eq₂ = refl
... | tri> _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₂ = refl

get-other {k} {k′} f ((k″ , v″) ∷ kvs″) k′≢k | tri≈ _  p₁ _  | [ eq₁ ] =
  contradiction (symᴷ p₁) k′≢k

get-other {k} {k′} f ((k″ , v″) ∷ kvs″) k′≢k | tri> p₁ p₂ _  | [ eq₁ ]
  with compᴷ k k″ | compᴷ k″ k′ | inspect (compᴷ k″) k′

... | tri< p₃ _  _  | tri< p₄ _  _  | [ eq₂ ] = contradiction (<-transᴷ p₃ p₄) p₁
... | tri< p₃ _  _  | tri≈ _  p₄ _  | [ eq₂ ] = contradiction (proj₁ <-resp-≡ᴷ p₄ p₃) p₁
... | tri< _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₁ = refl

... | tri≈ _  p₃ _  | tri< p₄ _  _  | [ eq₂ ] = contradiction (proj₂ <-resp-≡ᴷ (symᴷ p₃) p₄) p₁
... | tri≈ _  p₃ _  | tri≈ _  p₄ _  | [ eq₂ ] = contradiction (transᴷ p₃ p₄) p₂
... | tri≈ _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₂ = refl

... | tri> _  _  _  | tri< _  _  _  | [ eq₂ ] rewrite eq₂ = get-other f kvs″ k′≢k
... | tri> _  _  _  | tri≈ _  _  _  | [ eq₂ ] rewrite eq₂ = refl
... | tri> _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₂ = refl

lookup-insed : ∀ {k h} → (f : Maybe (Val k) → Val k) → (t : Tree V ⊥⁺ ⊤⁺ h) →
  lookup k (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k ]<⊤⁺ ≡ just (f (lookup k t ⊥⁺<[ k ]<⊤⁺))

lookup-insed {k} f t
  rewrite lookup≡get k t ⊥⁺<[ k ]<⊤⁺
        | lookup≡get k (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k ]<⊤⁺
        | insert≡put k f t ⊥⁺<[ k ]<⊤⁺
  = get-insed f (flat t)

lookup-other : ∀ {k k′ h} → (f : Maybe (Val k) → Val k) → (t : Tree V ⊥⁺ ⊤⁺ h) → ¬ k′ ≡ᴷ k →
  lookup k′ (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k′ ]<⊤⁺ ≡ lookup k′ t ⊥⁺<[ k′ ]<⊤⁺

lookup-other {k} {k′} f t k′≢k
  rewrite lookup≡get k′ t ⊥⁺<[ k′ ]<⊤⁺
        | lookup≡get k′ (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k′ ]<⊤⁺
        | insert≡put k f t ⊥⁺<[ k ]<⊤⁺
  = get-other f (flat t) k′≢k

{-
data Max : Key⁺ → List (K& V) → Set where
  max-[] : {m : Key⁺} → Max m []
  max-∷  : ∀ {k m l} → [ k ]ᴱ <⁺ m → Max m l → (v : Val k) → Max m ((k , v)  ∷ l)

max-++ : ∀ {m l₁ l₂} → Max m l₁ → Max m l₂ → Max m (l₁ ++ l₂)
max-++ {_} {[]}     _                p₂ = p₂
max-++ {_} {x ∷ xs} (max-∷ p₁ ps₁ v) p₂ = max-∷ p₁ (max-++ ps₁ p₂) v
max-lax : ∀ {m₁ m₂ l} → Max m₁ l → m₁ <⁺ m₂ → Max m₂ l
max-lax {_} {_} {[]} _ _ = max-[]

max-lax {_} {_} {(k , v) ∷ xs} (max-∷ p ps .v) m₁<m₂ =
  max-∷ (trans⁺ [ k ]ᴱ p m₁<m₂) (max-lax ps m₁<m₂) v

data Min : Key⁺ → List (K& V) → Set where
  min-[] : {m : Key⁺} → Min m []
  min-∷  : ∀ {k m l} → m <⁺ [ k ]ᴱ → Min [ k ]ᴱ l → (v : Val k) → Min m ((k , v) ∷ l)

min-++ : ∀ {m k v l₁ l₂} → Min m l₁ → Max [ k ]ᴱ l₁ → Min [ k ]ᴱ l₂ → Min m (l₁ ++ (k , v) ∷ l₂)
min-++ {m} {k} {v} {[]}               {l₂} m₁ m₂ m₃ = min-∷ {!!} m₃ v
min-++ {m} {k} {v} {(k′ , v′) ∷ kvs′} {l₂} (min-∷ m<k′ m₁′ .v′) (max-∷ k′<k m₂′ .v′) m₃ =
  min-∷ m<k′ (min-++ m₁′ m₂′ m₃) v′

dec-≡ : (k₁ k₂ : Key) → Dec (k₁ ≡ k₂)
dec-≡ k₁ k₂ with <-cmp k₁ k₂
... | tri< _ p _ = false because ofⁿ p
... | tri≈ _ p _ = true  because ofʸ p
... | tri> _ p _ = false because ofⁿ p

dec-≡-refl : ∀ k → dec-≡ k k ≡ yes refl
dec-≡-refl k with dec-≡ k k
dec-≡-refl k | yes refl = refl
dec-≡-refl k | no  k≢k  = contradiction refl k≢k

flat-max : ∀ {l u h} → (t : Tree V l u h) → Max u (flat t)
flat-max (leaf _)                  = max-[]
flat-max t@(node (_ , v′) tˡ tʳ _) =
  max-++ (max-lax (flat-max tˡ) (pi<up t)) (max-∷ (pi<up t) (flat-max tʳ) v′)

flat-min : ∀ {l u h} → (t : Tree V l u h) → Min l (flat t)
flat-min (leaf _)                 = min-[]
flat-min (node (k′ , v′) tˡ tʳ _) = min-++ (flat-min tˡ) (flat-max tˡ) (flat-min tʳ)

get : (k : Key) → List (K& V) → Maybe (Val k)
get k []               = nothing

get k ((k′ , v′) ∷ xs) with dec-≡ k′ k
... | yes p = just (V≈ p v′)
... | no  _ = get k xs

get₂ : (k : Key) → List (K& V) → List (K& V) → Maybe (Val k)
get₂ k xs ys with get k xs
... | just v′ = just v′
... | nothing = get k ys

get-pre : ∀ {k xs ys} → get k xs ≡ nothing → get k (xs ++ ys) ≡ get k ys
get-pre {_} {[]}             eq = refl

get-pre {k} {(k′ , v′) ∷ xs} eq with dec-≡ k′ k
get-pre {k} {(k′ , v′) ∷ xs} eq | no  _ = get-pre {k} {xs} eq
get-pre {_} {(k′ , v′) ∷ xs} () | yes _

get-app : ∀ {k v xs ys} → get k xs ≡ just v → get k (xs ++ ys) ≡ just v
get-app {k} {_} {(k′ , v′) ∷ xs} eq with dec-≡ k′ k
... | yes _ = eq
... | no  _ = get-app {k} {_} {xs} eq

get-split : (k : Key) → (xs ys : List (K& V)) → get k (xs ++ ys) ≡ get₂ k xs ys
get-split _ []               _  = refl
get-split k ((k′ , v′) ∷ xs) ys with dec-≡ k′ k
... | yes _ = refl
... | no  _ with get k xs | inspect (get k) xs
... | nothing | [ eq ] = get-pre {k} {xs} eq
... | just v″ | [ eq ] = get-app {k} {v″} {xs} eq

failˡ : ∀ {l u h} → (k : Key) → (t : Tree V l u h) → u <⁺ [ k ]ᴱ ⊎ u ≡ [ k ]ᴱ → get k (flat t) ≡ nothing
failˡ _ (leaf _) _ = refl

failˡ k (node (k′ , v′) tˡ tʳ _) (inj₁ u<k)
  rewrite get-split k (flat tˡ) ((k′ , v′) ∷ flat tʳ)
        | failˡ k tˡ (inj₁ (trans⁺ [ k′ ]ᴱ (lo<up tʳ) u<k))
  with dec-≡ k′ k
... | yes p  = contradiction p (<⇒≢ (strip-<⁺ (trans⁺ [ k′ ]ᴱ (lo<up tʳ) u<k)))
... | no  _  = failˡ k tʳ (inj₁ u<k)

failˡ k (node (k′ , v′) tˡ tʳ _) (inj₂ u≡k)
  rewrite get-split k (flat tˡ) ((k′ , v′) ∷ flat tʳ)
        | failˡ k tˡ (inj₁ (subst ([ k′ ]ᴱ <⁺_) u≡k (lo<up tʳ)))
  with dec-≡ k′ k
... | yes p = contradiction p (<⇒≢ (strip-<⁺ (subst (λ # → [ k′ ]ᴱ <⁺ #) u≡k (lo<up tʳ))))
... | no  _ = failˡ k tʳ (inj₂ u≡k)

failʳ : ∀ {l u h} → (k : Key) → (t : Tree V l u h) → [ k ]ᴱ <⁺ l ⊎ [ k ]ᴱ ≡ l → get k (flat t) ≡ nothing
failʳ _ (leaf _) _ = refl

failʳ k (node (k′ , v′) tˡ tʳ _) (inj₁ k<u)
  rewrite get-split k (flat tˡ) ((k′ , v′) ∷ flat tʳ)
        | failʳ k tˡ (inj₁ k<u)
  with dec-≡ k′ k
... | yes p = contradiction p (≢-sym (<⇒≢ (strip-<⁺ (trans⁺ [ k ]ᴱ k<u (lo<up tˡ)))))
... | no  _ = failʳ k tʳ (inj₁ (trans⁺ [ k ]ᴱ k<u (lo<up tˡ)))

failʳ k (node (k′ , v′) tˡ tʳ _) (inj₂ k≡u)
  rewrite get-split k (flat tˡ) ((k′ , v′) ∷ flat tʳ)
        | failʳ k tˡ (inj₂ k≡u)
  with dec-≡ k′ k
... | yes p = contradiction p (≢-sym (<⇒≢ (strip-<⁺ (subst (_<⁺ [ k′ ]ᴱ) (sym k≡u) (lo<up tˡ)))))
... | no  _ = failʳ k tʳ (inj₁ (subst (_<⁺ [ k′ ]ᴱ) (sym k≡u) (lo<up tˡ)))

get≡lookup : ∀ {l u h} → (k : Key) → (t : Tree V l u h) → (l<k<u : l < k < u) →
  get k (flat t) ≡ lookup k t l<k<u

get≡lookup k (leaf l<u) l<k<u = refl

get≡lookup k (node (k′ , v′) tˡ tʳ _) (l<k , k<u)
  rewrite get-split k (flat tˡ) ((k′ , v′) ∷ flat tʳ)
  with <-cmp k′ k | inspect (<-cmp k′) k

... | tri< p₁ _  _ | [ eq ]
  rewrite failˡ k tˡ (inj₁ [ p₁ ]ᴿ)
        | eq
  = get≡lookup k tʳ ([ p₁ ]ᴿ , k<u)

... | tri≈ _  p₂ _ | [ eq ]
  rewrite failˡ k tˡ (inj₂ (cong [_]ᴱ p₂))
        | p₂
        | eq
  = refl

... | tri> p₁ p₂ p₃ | [ eq ] with get k (flat tˡ) | inspect (get k) (flat tˡ)

... | nothing | [ eq₂ ]
  rewrite sym (get≡lookup k tˡ (l<k , [ p₃ ]ᴿ))
        | eq₂
        | eq
  = failʳ k tʳ (inj₁ [ p₃ ]ᴿ)

... | just v  | [ eq₂ ]
  rewrite sym (get≡lookup k tˡ (l<k , [ p₃ ]ᴿ))
        | eq₂
  = refl

join-pat₁ : (as bs cs ds : List (K& V)) → (as ++ bs) ++ cs ++ ds ≡ (as ++ bs ++ cs) ++ ds
join-pat₁ as bs cs ds = solve (++-monoid (K& V))

join-pat₂ : (as bs cs : List (K& V)) → as ++ bs ++ cs ≡ (as ++ bs) ++ cs
join-pat₂ as bs cs = solve (++-monoid (K& V))

join-pat₃ : (as bs cs ds : List (K& V)) → as ++ (bs ++ cs) ++ ds ≡ (as ++ bs ++ cs) ++ ds
join-pat₃ as bs cs ds = solve (++-monoid (K& V))

join-pat₄ : (as bs cs ds : List (K& V)) → (as ++ bs) ++ cs ++ ds ≡ as ++ (bs ++ cs) ++ ds
join-pat₄ as bs cs ds = solve (++-monoid (K& V))

flat-joinˡ⁺ :
  ∀ {l u hˡ hʳ h} k v i → (tˡ : Tree V _ _ _) → ∀ tʳ b →
  flat (proj₂ (joinˡ⁺ {l = l} {u} {hˡ} {hʳ} {h} (k , v) (i , tˡ) tʳ b)) ≡ flat tˡ ++ ((k , v) ∷ flat tʳ)

flat-joinˡ⁺ k₆ v₆ 1# (node (k₂ , v₂) t₁ (node (k₄ , v₄) t₃ t₅ b) ∼+) t₇ ∼- =
  join-pat₁ (flat t₁) ((k₂ , v₂) ∷ flat t₃) ((k₄ , v₄) ∷ flat t₅) ((k₆ , v₆) ∷ flat t₇)

flat-joinˡ⁺ k₄ v₄ 1# (node (k₂ , v₂) t₁ (leaf _)                 ∼-) t₅ ∼- =
  join-pat₂ (flat t₁) ((k₂ , v₂) ∷ []) ((k₄ , v₄) ∷ flat t₅)

flat-joinˡ⁺ k₄ v₄ 1# (node (k₂ , v₂) t₁ (node (k₃ , v₃) t₈ t₉ _) ∼-) t₅ ∼- =
  join-pat₃ (flat t₁) ((k₂ , v₂) ∷ flat t₈) ((k₃ , v₃) ∷ flat t₉) ((k₄ , v₄) ∷ flat t₅)

flat-joinˡ⁺ k₄ v₄ 1# (node (k₂ , v₂) t₁ (node (k₃ , v₃) t₆ t₇ _) ∼0) t₅ ∼- =
  join-pat₃ (flat t₁) ((k₂ , v₂) ∷ flat t₆) ((k₃ , v₃) ∷ flat t₇) ((k₄ , v₄) ∷ flat t₅)

flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼+) t₃ ∼0 = refl
flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (leaf _)         ∼0) t₃ ∼0 = refl
flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼0) t₃ ∼0 = refl
flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (leaf _)         ∼-) t₃ ∼0 = refl
flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼-) t₃ ∼0 = refl

flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼+) t₃ ∼+ = refl
flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (leaf _)         ∼0) t₃ ∼+ = refl
flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼0) t₃ ∼+ = refl
flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (leaf _)         ∼-) t₃ ∼+ = refl
flat-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼-) t₃ ∼+ = refl

flat-joinˡ⁺ k₂ v₂ 0# t₁                                      t₃ b  = refl

flat-joinʳ⁺ :
  ∀ {l u hˡ hʳ h} k v tˡ i → (tʳ : Tree V _ _ _) → ∀ b →
  flat (proj₂ (joinʳ⁺ {l = l} {u} {hˡ} {hʳ} {h} (k , v) tˡ (i , tʳ) b)) ≡ flat tˡ ++ ((k , v) ∷ flat tʳ)

flat-joinʳ⁺ k₂ v₂ t₁ 1# (node (k₆ , v₆) (node (k₄ , v₄) t₃ t₅ b)    t₇ ∼-) ∼+ =
  join-pat₄ (flat t₁) ((k₂ , v₂) ∷ flat t₃) ((k₄ , v₄) ∷ flat t₅) ((k₆ , v₆) ∷ flat t₇)

flat-joinʳ⁺ k₂ v₂ t₁ 1# (node (k₄ , v₄) t₃@(leaf _)                 t₅ ∼+) ∼+ =
  sym (join-pat₂ (flat t₁) ((k₂ , v₂) ∷ []) ((k₄ , v₄) ∷ flat t₅))

flat-joinʳ⁺ k₂ v₂ t₁ 1# (node (k₄ , v₄) t₃@(node (k₆ , v₆) t₇ t₈ _) t₅ ∼+) ∼+ =
  sym (join-pat₃ (flat t₁) ((k₂ , v₂) ∷ flat t₇) ((k₆ , v₆) ∷ flat t₈) ((k₄ , v₄) ∷ flat t₅))

flat-joinʳ⁺ k₂ v₂ t₁ 1# (node (k₄ , v₄) t₃@(node (k₆ , v₆) t₇ t₈ _) t₅ ∼0) ∼+ =
  sym (join-pat₃ (flat t₁) ((k₂ , v₂) ∷ flat t₇) ((k₆ , v₆) ∷ flat t₈) ((k₄ , v₄) ∷ flat t₅))

flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼-) ∼0 = refl
flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (leaf _)       _ ∼0) ∼0 = refl
flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼0) ∼0 = refl
flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (leaf _)       _ ∼+) ∼0 = refl
flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼+) ∼0 = refl

flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼-) ∼- = refl
flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (leaf _)       _ ∼0) ∼- = refl
flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼0) ∼- = refl
flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (leaf _)       _ ∼+) ∼- = refl
flat-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼+) ∼- = refl

flat-joinʳ⁺ k₂ v₂ t₁ 0# t₃                              _  = refl

put-lem₁ : ∀ {k k′} f v′ l₁ l₂ → k < k′ →
  put k f (l₁ ++ (k′ , v′) ∷ l₂) ≡ (put k f l₁) ++ (k′ , v′) ∷ l₂

put-lem₁ {k} {k′} f v' [] l₂ k<k′ with <-cmp k k′
... | tri< _  _ _ = refl
... | tri≈ p₁ _ _ = contradiction k<k′ p₁
... | tri> p₁ _ _ = contradiction k<k′ p₁

put-lem₁ {k} f v′ ((k″ , v″) ∷ l₁′) l₂ k<k′ with <-cmp k k″
... | tri< _ _ _ = refl
... | tri≈ _ _ _ = refl
... | tri> _ _ _ rewrite put-lem₁ f v′ l₁′ l₂ k<k′ = refl

put-lem₂ : ∀ {k k′ kvs} f v′ kvs′ → Max [ k′ ]ᴱ kvs → k′ ≤ k →
  put k f (kvs ++ (k′ , v′) ∷ kvs′) ≡ kvs ++ (put k f ((k′ , v′) ∷ kvs′))

put-lem₂ {_} {_} {[]} _ _ _ _ _ = refl

put-lem₂ {k} {_} {(k″ , v″) ∷ kvs″} f v′ kvs′ (max-∷ p p′ v″) k′≤k with <-cmp k k″
... | tri< _ _ p₃ = contradiction (<-transˡ (strip-<⁺ p) k′≤k) p₃
... | tri≈ _ _ p₃ = contradiction (<-transˡ (strip-<⁺ p) k′≤k) p₃
... | tri> _ _ _  = cong ((k″ , v″) ∷_) (put-lem₂ {k} {_} {kvs″} f v′ kvs′ p′ k′≤k)

put≡insert : ∀ {l u h} → (k : Key) → (f : Maybe (Val k) → Val k) → (t : Tree V l u h) →
  (l<k<u : l < k < u) → put k f (flat t) ≡ flat (proj₂ (insertWith k f t l<k<u))

put≡insert _ _ (leaf _) _ = refl

put≡insert k f (node (k′ , v′) tˡ tʳ _) (l<k , k<u) with <-cmp k k′ | inspect (<-cmp k) k′

put≡insert k f (node (k′ , v′) tˡ tʳ b) (l<k , k<u) | tri< p₁ _ _ | _
  rewrite put-lem₁ f v′ (flat tˡ) (flat tʳ) p₁
        | (let # = insertWith k f tˡ (l<k , [ p₁ ]ᴿ) in flat-joinˡ⁺ k′ v′ (proj₁ #) (proj₂ #) tʳ b)
        | put≡insert k f tˡ (l<k , [ p₁ ]ᴿ)
  = refl

put≡insert k f (node (k′ , v′) tˡ tʳ _) (l<k , k<u) | tri≈ _ p₂ _ | [ eq ]
  rewrite put-lem₂ f v′ (flat tʳ) (flat-max tˡ) (subst (_≤ k) p₂ (≤-refl {k}))
        | eq
        | p₂
  = refl

put≡insert k f (node (k′ , v′) tˡ tʳ b) (l<k , k<u) | tri> _ _ p₃ | [ eq ]
  rewrite (let # = insertWith k f tʳ ([ p₃ ]ᴿ , k<u) in flat-joinʳ⁺ k′ v′ tˡ (proj₁ #) (proj₂ #) b)
        | put-lem₂ f v′ (flat tʳ) (flat-max tˡ) (<⇒≤ p₃)
        | eq
        | put≡insert k f tʳ ([ p₃ ]ᴿ , k<u)
  = refl

min-get : ∀ {m l k} → Min m l → [ k ]ᴱ <⁺ m → get k l ≡ nothing
min-get min-[] _ = refl
min-get {_} {(k′ , v′) ∷ kvs′} {k} (min-∷ m<k′ m′ .v′) k<m with dec-≡ k′ k
... | yes p = contradiction p (≢-sym (<⇒≢ (strip-<⁺ (trans⁺ [ k ]ᴱ k<m m<k′))))
... | no  _ = min-get m′ (trans⁺ [ k ]ᴱ k<m m<k′)

get-other : ∀ {k k′} f l → k′ ≢ k → get k′ (put k f l) ≡ get k′ l

get-other {k} {k′} f [] k′≢k with dec-≡ k k′
... | yes p = contradiction p (≢-sym k′≢k)
... | no  p = refl

get-other {k} {k′} f ((k″ , v″) ∷ kvs″) k′≢k
  with dec-≡ k k′ | inspect (dec-≡ k) k′ | <-cmp k k″ | dec-≡ k″ k′ | inspect (dec-≡ k″) k′
... | yes k≡k′ | _       | _             | _         | _       = contradiction k≡k′ (≢-sym k′≢k)
... | no  _    | [ eq₁ ] | tri< _  _  _  | _         | [ eq₂ ] rewrite eq₁ | eq₂ = refl
... | no  k≢k′ | _       | tri≈ _  p₂ _  | yes k″≡k′ | _       = contradiction (trans p₂ k″≡k′) k≢k′
... | no  _    | _       | tri≈ _  _  _  | no  _     | [ eq₂ ] rewrite eq₂ = refl
... | no  _    | _       | tri> _  _  _  | yes _     | [ eq₂ ] rewrite eq₂ = refl
... | no  _    | _       | tri> _  _  _  | no  _     | [ eq₂ ] rewrite eq₂ = get-other f kvs″ k′≢k

lookup-other : ∀ {k k′ h} → (f : Maybe (Val k) → Val k) → (t : Tree V ⊥⁺ ⊤⁺ h) → k′ ≢ k →
  lookup k′ (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k′ ]<⊤⁺ ≡ lookup k′ t ⊥⁺<[ k′ ]<⊤⁺

lookup-other {k} {k′} f t k′≢k
  rewrite sym (get≡lookup k′ t ⊥⁺<[ k′ ]<⊤⁺)
        | sym (get≡lookup k′ (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k′ ]<⊤⁺)
        | sym (put≡insert k f t ⊥⁺<[ k ]<⊤⁺)
  = get-other f (flat t) k′≢k

get-insed : ∀ {m l k} f → Min m l → get k (put k f l) ≡ just (f (get k l))

get-insed {m} {l} {k} f min-[] with dec-≡ k k
... | yes refl rewrite reduce (f nothing) = refl
... | no  p    = contradiction refl p

get-insed {m} {(k′ , v′) ∷ kvs′} {k} f (min-∷ m<k′ m′ .v′)
  with <-cmp k k′ | dec-≡ k′ k | inspect (dec-≡ k′) k

... | tri< p₁ p₂ p₃ | yes p₄ | _ = contradiction (sym p₄) p₂

... | tri< p₁ p₂ p₃ | no  p₄ | _
  rewrite dec-≡-refl k
        | reduce (f nothing)
        | min-get m′ [ p₁ ]ᴿ
  = refl

... | tri≈ p₁ p₂ p₃ | yes p₄ | _
  rewrite p₂
        | dec-≡-refl k′
        | p₄
        | reduce v′
        | reduce (f (just v′))
        | reduce (f (just v′))
  = refl

... | tri≈ p₁ p₂ p₃ | no  p₄ | _ = contradiction (sym p₂) p₄
... | tri> p₁ p₂ p₃ | yes p₄ | _ = contradiction (sym p₄) p₂
... | tri> p₁ p₂ p₃ | no  p₄ | [ eq ] rewrite eq = get-insed f m′


lookup-insed : ∀ {k h} → (f : Maybe (Val k) → Val k) → (t : Tree V ⊥⁺ ⊤⁺ h) →
  lookup k (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k ]<⊤⁺ ≡ just (f (lookup k t ⊥⁺<[ k ]<⊤⁺))

lookup-insed {k} f t
  rewrite sym (get≡lookup k t ⊥⁺<[ k ]<⊤⁺)
        | sym (get≡lookup k (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k ]<⊤⁺)
        | sym (put≡insert k f t ⊥⁺<[ k ]<⊤⁺)
  = get-insed f (flat-min t)
-}
