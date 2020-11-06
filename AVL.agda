open import Level using (Level)
open import Relation.Binary.Bundles using () renaming (StrictTotalOrder to STO)

module AVL {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (stoᴷ : STO ℓ₁ ℓ₂ ℓ₃) (Val : Set ℓ₄) where

open import Level using (0ℓ ; _⊔_)

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

open import Data.Tree.AVL.Indexed stoᴷ
  using (
    Key⁺ ;  K&_ ; Value ; MkValue ;
    _<⁺_ ; _<_<_ ; [_]ᴿ ; ⊥⁺ ; ⊤⁺ ; ⊥⁺<[_]<⊤⁺ ; trans⁺ ;
    Tree ; leaf ; node ; 0# ; 1# ; ∼- ; ∼0 ; ∼+ ;
    lookup ; insertWith ; joinˡ⁺ ; joinʳ⁺
  ) renaming ([_] to [_]ᴱ)

open import Function using (id ; _∘_ ; _$_ ; const)

open import Relation.Binary using (tri< ; tri≈ ; tri>)

open import Relation.Binary.Construct.Add.Extrema.Strict (STO._<_ stoᴷ)
  using () renaming ([<]-injective to strip-<⁺)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; _≢_ ; trans ; sym ; cong ; inspect ; [_])

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import Tactic.MonoidSolver using (solve)

open STO stoᴷ
  using () renaming (
    _<_ to _<ᴷ_ ;
    trans to <-transᴷ ; <-resp-≈ to <-resp-≈ᴷ ; irrefl to <-irreflᴷ ;
    compare to compᴷ
  )

open STO.Eq stoᴷ using () renaming (_≈_ to _≈ᴷ_ ; refl to reflexᴷ ; sym to symᴷ ; trans to transᴷ)

Key : Set ℓ₁
Key = STO.Carrier stoᴷ

V≈ : {k₁ k₂ : Key} → k₁ ≈ᴷ k₂ → Val → Val
V≈ _ = id

V = MkValue (const Val) V≈

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

Lo : Key⁺ → Pred (K& V) (ℓ₁ ⊔ ℓ₃)
Lo l (k , _) = l <⁺ [ k ]ᴱ

Up : Key⁺ → Pred (K& V) (ℓ₁ ⊔ ℓ₃)
Up u (k , _) = [ k ]ᴱ <⁺ u

Ord : Pred (List (K& V)) (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄)
Ord kvs = Linked (λ (k₁ , _) (k₂ , _) → k₁ <ᴷ k₂) kvs

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

ord-∷ : ∀ {k v kvs} → All (Lo [ k ]ᴱ) kvs → Ord kvs → Ord ((k , v) ∷ kvs)
ord-∷ {k} {v} {[]}               lo                 ord = [-]ᴸ
ord-∷ {k} {v} {(k′ , v′) ∷ kvs′} ([ k<k′ ]ᴿ ∷ᴬ lo′) ord = k<k′ ∷ᴸ ord

ord-++ : ∀ {k v kvs₁ kvs₂} →
  All (Up [ k ]ᴱ) kvs₁ → Ord kvs₁ → All (Lo [ k ]ᴱ) kvs₂ → Ord kvs₂ →
  Ord (kvs₁ ++ (k , v) ∷ kvs₂)

ord-++ {k} {v} {[]}                              {kvs₂} up             ord₁        lo ord₂ = ord-∷ lo ord₂
ord-++ {k} {v} {(k₁ , v₁) ∷ []}                  {kvs₂} ([ u ]ᴿ ∷ᴬ up) [-]ᴸ        lo ord₂ = u ∷ᴸ ord-++ []ᴬ []ᴸ lo ord₂
ord-++ {k} {v} {(k₁ , v₁) ∷ (k₁′ , v₁′) ∷ kvs₁′} {kvs₂} ([ u ]ᴿ ∷ᴬ up) (o ∷ᴸ ord₁) lo ord₂ = o ∷ᴸ ord-++ up ord₁ lo ord₂

all-ord : ∀ {l u h} → (t : Tree V l u h) → Ord (flat t)
all-ord (leaf  _)                = []ᴸ
all-ord (node (k′ , v′) tˡ tʳ _) = ord-++ (all-up tˡ) (all-ord tˡ) (all-lo tʳ) (all-ord tʳ)

get : (k : Key) → List (K& V) → Maybe Val
get k [] = nothing

get k ((k′ , v′) ∷ kvs′) with compᴷ k′ k
... | tri< _ _ _ = get k kvs′
... | tri≈ _ p _ = just (V≈ p v′)
... | tri> _ _ _ = nothing

put : (k : Key) → (f : Maybe Val → Val) → (l : List (K& V)) → List (K& V)
put k f [] = (k , f nothing) ∷ []

put k f ((k′ , v′) ∷ kvs′) with compᴷ k k′
... | tri< _ _ _ = (k , f nothing) ∷ (k′ , v′) ∷ kvs′
... | tri≈ _ p _ = (k′ , V≈ p (f (just (V≈ (symᴷ p) v′)))) ∷ kvs′
... | tri> _ _ _ = (k′ , v′) ∷ (put k f kvs′)

failˡ : ∀ {u} → (k : Key) → (kvs : List (K& V)) → All (Up [ u ]ᴱ) kvs → ¬ k <ᴷ u →
  get k kvs ≡ nothing

failˡ _ [] []ᴬ _ = refl

failˡ k ((k′ , v′) ∷ kvs′) (a ∷ᴬ as) ¬k<u with compᴷ k′ k
... | tri< _ _ _ = failˡ k kvs′ as ¬k<u
... | tri≈ _ p _ = contradiction (proj₂ <-resp-≈ᴷ p (strip-<⁺ a)) ¬k<u
... | tri> _ _ _ = refl

get₂ : (k : Key) → List (K& V) → List (K& V) → Maybe Val
get₂ k xs ys with get k xs
... | just v′ = just v′
... | nothing = get k ys

get-split : (k : Key) → (k″ : Key) → (v″ : Val) → (kvs kvs″ : List (K& V)) →
  All (Up [ k″ ]ᴱ) kvs → get k (kvs ++ (k″ , v″) ∷ kvs″) ≡ get₂ k kvs ((k″ , v″) ∷ kvs″)

get-split k k″ v″ [] kvs″ as = refl

get-split k k″ v″ ((k′ , v′) ∷ kvs′) kvs″ (a′ ∷ᴬ as′) with compᴷ k′ k
... | tri< _ _ _  = get-split k k″ v″ kvs′ kvs″ as′
... | tri≈ _ _ _  = refl

... | tri> p₁ _  p₂ with compᴷ k″ k
... | tri< p₃ _  _  = contradiction (<-transᴷ (<-transᴷ p₂ (strip-<⁺ a′)) p₃) (<-irreflᴷ reflexᴷ)
... | tri≈ _  p₄ _  = contradiction (proj₁ <-resp-≈ᴷ p₄ (strip-<⁺ a′)) p₁
... | tri> _  _  _  = refl

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
  flat (proj₂ (joinˡ⁺ {l = l} {u} {hˡ} {hʳ} {h} (k , v) (i , tˡ) tʳ b)) ≡
  flat tˡ ++ ((k , v) ∷ flat tʳ)

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
  flat (proj₂ (joinʳ⁺ {l = l} {u} {hˡ} {hʳ} {h} (k , v) tˡ (i , tʳ) b)) ≡
  flat tˡ ++ ((k , v) ∷ flat tʳ)

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

put-++ˡ : ∀ {k k′} f v′ l₁ l₂ → k <ᴷ k′ →
  put k f (l₁ ++ (k′ , v′) ∷ l₂) ≡ (put k f l₁) ++ (k′ , v′) ∷ l₂

put-++ˡ {k} {k′} f v' [] l₂ k<k′ with compᴷ k k′
... | tri< _ _ _ = refl
... | tri≈ p _ _ = contradiction k<k′ p
... | tri> p _ _ = contradiction k<k′ p

put-++ˡ {k} {k′} f v′ ((k″ , v″) ∷ kvs″) l₂ k<k′ with compᴷ k k″
... | tri< _ _ _ = refl
... | tri≈ _ _ _ = refl
... | tri> _ _ _ rewrite put-++ˡ f v′ kvs″ l₂ k<k′ = refl

put-++ʳ : ∀ {k k′} f v′ l₁ l₂ → All (Up [ k′ ]ᴱ) l₁ → ¬ k <ᴷ k′ →
  put k f (l₁ ++ (k′ , v′) ∷ l₂) ≡ l₁ ++ (put k f ((k′ , v′) ∷ l₂))

put-++ʳ {k} {k′} f v′ [] l₂ as ¬k<k′ = refl

put-++ʳ {k} {k′} f v′ ((k″ , v″) ∷ kvs″) l₂ (a′ ∷ᴬ as′) ¬k<k′ with compᴷ k k″
... | tri< p _ _ = contradiction (<-transᴷ p (strip-<⁺ a′)) ¬k<k′
... | tri≈ _ p _ = contradiction (proj₂ <-resp-≈ᴷ (symᴷ p) (strip-<⁺ a′)) ¬k<k′
... | tri> _ _ _ = cong ((k″ , v″) ∷_) (put-++ʳ f v′ kvs″ l₂ as′ ¬k<k′)

lookup≡get : ∀ {l u h} → (k : Key) → (t : Tree V l u h) → (l<k<u : l < k < u) →
  lookup k t l<k<u ≡ get k (flat t)

lookup≡get k (leaf l<u) l<k<u = refl

lookup≡get k (node (k′ , v′) tˡ tʳ _) l<k<u
  rewrite get-split k k′ v′ (flat tˡ) (flat tʳ) (all-up tˡ)
  with compᴷ k′ k | inspect (compᴷ k′) k

lookup≡get k (node (k′ , v′) tˡ tʳ _) (l<k , k<u) | tri< p₁ _  p₂ | [ eq₁ ]
  rewrite failˡ k (flat tˡ) (all-up tˡ) p₂
        | eq₁
  = lookup≡get k tʳ ([ p₁ ]ᴿ , k<u)

lookup≡get k (node (k′ , v′) tˡ tʳ _) (l<k , k<u) | tri≈ _  _  p₁ | [ eq₁ ]
  rewrite failˡ k (flat tˡ) (all-up tˡ) p₁
        | eq₁
  = refl

lookup≡get k (node (k′ , v′) tˡ tʳ _) (l<k , k<u) | tri> _  _  p₁ | [ eq₁ ]
  rewrite lookup≡get k tˡ (l<k , [ p₁ ]ᴿ)
  with get k (flat tˡ)
... | just v  = refl
... | nothing rewrite eq₁ = refl

insert≡put : ∀ {l u h} → (k : Key) → (f : Maybe Val → Val) → (t : Tree V l u h) →
  (l<k<u : l < k < u) → flat (proj₂ (insertWith k f t l<k<u)) ≡ put k f (flat t)

insert≡put _ _ (leaf _) _ = refl
insert≡put k f (node (k′ , v′) tˡ tʳ b) (l<k , k<u) with compᴷ k k′ | inspect (compᴷ k) k′

insert≡put k f (node (k′ , v′) tˡ tʳ b) (l<k , k<u) | tri< p₁ _ _ | [ eq₁ ]
  rewrite (let # = insertWith k f tˡ (l<k , [ p₁ ]ᴿ) in flat-joinˡ⁺ k′ v′ (proj₁ #) (proj₂ #) tʳ b)
        | insert≡put k f tˡ (l<k , [ p₁ ]ᴿ)
        | put-++ˡ f v′ (flat tˡ) (flat tʳ) p₁
  = refl

insert≡put k f (node (k′ , v′) tˡ tʳ b) (l<k , k<u) | tri≈ p₁ p₂ _ | [ eq₁ ]
  rewrite put-++ʳ f v′ (flat tˡ) (flat tʳ) (all-up tˡ) p₁
        | eq₁
  = refl

insert≡put k f (node (k′ , v′) tˡ tʳ b) (l<k , k<u) | tri> p₁ _ p₂ | [ eq₁ ]
  rewrite (let # = insertWith k f tʳ ([ p₂ ]ᴿ , k<u) in flat-joinʳ⁺ k′ v′ tˡ (proj₁ #) (proj₂ #) b)
        | insert≡put k f tʳ ([ p₂ ]ᴿ , k<u)
        | put-++ʳ f v′ (flat tˡ) (flat tʳ) (all-up tˡ) p₁
        | eq₁
  = refl

get-insed : ∀ {k} f kvs → get k (put k f kvs) ≡ just (f (get k kvs))

get-insed {k} f kvs with compᴷ k k | inspect (compᴷ k) k
get-insed {k} f _                  | tri< _ p₁ _ | _ = contradiction reflexᴷ p₁
get-insed {k} f _                  | tri> _ p₁ _ | _ = contradiction reflexᴷ p₁

get-insed {k} f []                 | tri≈ _ p₁ _ | [ eq₁ ] rewrite eq₁ = refl

get-insed {k} f ((k′ , v′) ∷ kvs′) | tri≈ _ p₁ _ | [ eq₁ ]
  with compᴷ k k′ | compᴷ k′ k | inspect (compᴷ k) k′ | inspect (compᴷ k′) k

... | tri< p₂ _  _  | tri< _  _  p₃ | _       | _       = contradiction p₂ p₃
... | tri< p₂ _  _  | tri≈ _  _  p₃ | _       | _       = contradiction p₂ p₃
... | tri≈ _  p₂ _  | tri< _  p₃ _  | _       | _       = contradiction (symᴷ p₂) p₃
... | tri≈ _  p₂ _  | tri> _  p₃ _  | _       | _       = contradiction (symᴷ p₂) p₃
... | tri> _  _  p₂ | tri≈ p₃ _  _  | _       | _       = contradiction p₂ p₃
... | tri> _  _  p₂ | tri> p₃ _  _  | _       | _       = contradiction p₂ p₃

... | tri< p₂ _  _  | tri> _  _  p₃ | _       | _       rewrite eq₁ = refl
... | tri> _  _  p₂ | tri< p₃ _  _  | [ eq₂ ] | [ eq₃ ] rewrite eq₃ = get-insed f kvs′
... | tri≈ _  p₂ _  | tri≈ _  p₃ _  | [ eq₂ ] | [ eq₃ ] rewrite eq₃ = refl

get-other : ∀ {k k′} f kvs → ¬ k′ ≈ᴷ k → get k′ (put k f kvs) ≡ get k′ kvs

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
... | tri< p₃ _  _  | tri≈ _  p₄ _  | [ eq₂ ] = contradiction (proj₁ <-resp-≈ᴷ p₄ p₃) p₁
... | tri< _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₁ = refl

... | tri≈ _  p₃ _  | tri< p₄ _  _  | [ eq₂ ] = contradiction (proj₂ <-resp-≈ᴷ (symᴷ p₃) p₄) p₁
... | tri≈ _  p₃ _  | tri≈ _  p₄ _  | [ eq₂ ] = contradiction (transᴷ p₃ p₄) p₂
... | tri≈ _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₂ = refl

... | tri> _  _  _  | tri< _  _  _  | [ eq₂ ] rewrite eq₂ = get-other f kvs″ k′≢k
... | tri> _  _  _  | tri≈ _  _  _  | [ eq₂ ] rewrite eq₂ = refl
... | tri> _  _  _  | tri> _  _  _  | [ eq₂ ] rewrite eq₂ = refl

lookup-insed : ∀ {k h} → (f : Maybe Val → Val) → (t : Tree V ⊥⁺ ⊤⁺ h) →
  lookup k (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k ]<⊤⁺ ≡ just (f (lookup k t ⊥⁺<[ k ]<⊤⁺))

lookup-insed {k} f t
  rewrite lookup≡get k t ⊥⁺<[ k ]<⊤⁺
        | lookup≡get k (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k ]<⊤⁺
        | insert≡put k f t ⊥⁺<[ k ]<⊤⁺
  = get-insed f (flat t)

lookup-other : ∀ {k k′ h} → (f : Maybe Val → Val) → (t : Tree V ⊥⁺ ⊤⁺ h) → ¬ k′ ≈ᴷ k →
  lookup k′ (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k′ ]<⊤⁺ ≡ lookup k′ t ⊥⁺<[ k′ ]<⊤⁺

lookup-other {k} {k′} f t k′≢k
  rewrite lookup≡get k′ t ⊥⁺<[ k′ ]<⊤⁺
        | lookup≡get k′ (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k′ ]<⊤⁺
        | insert≡put k f t ⊥⁺<[ k ]<⊤⁺
  = get-other f (flat t) k′≢k

import Data.Tree.AVL stoᴷ as A using (Tree ; tree ; insert ; lookup)

avl-insed : (k : Key) → (v : Val) → (t : A.Tree V) → (A.lookup k (A.insert k v t)) ≡ just v
avl-insed k v (A.tree t′) = lookup-insed (const v) t′

avl-other : (k′ k : Key) → (v : Val) → (t : A.Tree V) → ¬ k′ ≈ᴷ k →
  (A.lookup k′ (A.insert k v t)) ≡ A.lookup k′ t

avl-other k′ k v (A.tree t′) k′≢k = lookup-other (const v) t′ k′≢k
