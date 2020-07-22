open import Agda.Primitive using (Level)
open import Data.Bool using (true ; false)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.List.Properties using (++-monoid)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (suc ; _<_ ; _≤_)
open import Data.Nat.Properties using (<-strictTotalOrder ; <-cmp ; <⇒≢; <⇒≤ ; <-transˡ ; ≤-refl)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (id)
open import Relation.Binary using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.Bundles using () renaming (StrictTotalOrder to STO)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; trans ; sym ; ≢-sym ; cong ; subst ; inspect ; [_])
open import Relation.Nullary using (Dec ; _because_ ; ofʸ ; ofⁿ ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Tactic.MonoidSolver using (solve)

open import Data.Tree.AVL.Indexed <-strictTotalOrder renaming ([_] to [_]ᴱ)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using () renaming ([<]-injective to strip-<⁺)

module Avl
  {ℓⱽ : Level}
  (V : Value ℓⱽ)
  (reduce : ∀ {k} (v : Value.family V k) → Value.respects V refl v ≡ v) where

private
  Key = STO.Carrier <-strictTotalOrder
  Val = Value.family V
  V≈  = Value.respects V

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
  min-∷  : ∀ {k m l} → m <⁺ [ k ]ᴱ → Min m l → (v : Val k) → Min m ((k , v) ∷ l)

min-++ : ∀ {m l₁ l₂} → Min m l₁ → Min m l₂ → Min m (l₁ ++ l₂)
min-++ {_} {[]}     _                p₂ = p₂
min-++ {_} {x ∷ xs} (min-∷ p₁ ps₁ v) p₂ = min-∷ p₁ (min-++ ps₁ p₂) v

min-lax : ∀ {m₁ m₂ l} → Min m₁ l → m₂ <⁺ m₁ → Min m₂ l
min-lax {_} {_} {[]} _ _ = min-[]

min-lax {_} {m₂} {(k , v) ∷ xs} (min-∷ p ps .v) m₂<m₁ =
  min-∷ (trans⁺ m₂ m₂<m₁ p) (min-lax ps m₂<m₁) v

min : Key → Key⁺ → Key⁺
min k₁ ⊤⁺ = [ k₁ ]ᴱ
min k₁ ⊥⁺ = ⊥⁺
min k₁ [ k₂ ]ᴱ with <-cmp k₁ k₂
... | tri< _ _ _ = [ k₁ ]ᴱ
... | tri≈ _ _ _ = [ k₁ ]ᴱ
... | tri> _ _ _ = [ k₂ ]ᴱ

<-min : ∀ {k₁ k₂ k₃} → [ k₁ ]ᴱ <⁺ [ k₂ ]ᴱ → [ k₁ ]ᴱ <⁺ [ k₃ ]ᴱ → [ k₁ ]ᴱ <⁺ min k₂ [ k₃ ]ᴱ
<-min {k₁} {k₂} {k₃} k₁<k₂ k₁<k₃ with <-cmp k₂ k₃
... | tri< _ _ _ = k₁<k₂
... | tri≈ _ _ _ = k₁<k₂
... | tri> _ _ _ = k₁<k₃

dec-≡ : (k₁ k₂ : Key) → Dec (k₁ ≡ k₂)
dec-≡ k₁ k₂ with <-cmp k₁ k₂
... | tri< _ p _ = false because ofⁿ p
... | tri≈ _ p _ = true  because ofʸ p
... | tri> _ p _ = false because ofⁿ p

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

flat-max : ∀ {l u h} → (t : Tree V l u h) → Max u (flat t)
flat-max (leaf _)                  = max-[]
flat-max t@(node (_ , v′) tˡ tʳ _) =
  max-++ (max-lax (flat-max tˡ) (pi<up t)) (max-∷ (pi<up t) (flat-max tʳ) v′)

flat-min : ∀ {l u h} → (t : Tree V l u h) → Min l (flat t)
flat-min     (leaf _)                   = min-[]
flat-min {l} t@(node (k′ , v′) tˡ tʳ _) =
  min-++ (flat-min tˡ) (min-++ (min-∷ (lo<pi t) min-[] v′) (min-lax (flat-min tʳ) (lo<pi t)))

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

put : (k : Key) → (f : Maybe (Val k) → Val k) → (l : List (K& V)) → List (K& V)
put k f [] = (k , f nothing) ∷ []

put k f ((k′ , v′) ∷ kvs) with <-cmp k k′
... | tri< _ _  _ = (k , f nothing) ∷ (k′ , v′) ∷ kvs
... | tri≈ _ p₂ _ = (k′ , V≈ p₂ (f (just (V≈ (sym p₂) v′)))) ∷ kvs
... | tri> _ _  _ = (k′ , v′) ∷ (put k f kvs)

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

put-get : ∀ {l u h} → (t : Tree V l u h) → (k k′ : Key) → (f : Maybe (Val k) → Val k) →
  (l<k<u : l < k < u) (l<k′<u : l < k′ < u) →
  get k′ (put k f (flat t)) ≡ lookup k′ (proj₂ (insertWith k f t l<k<u)) l<k′<u

put-get t k k′ f l<k<u l<k′<u
  rewrite put≡insert k f t l<k<u
        | get≡lookup k′ (proj₂ (insertWith k f t l<k<u)) l<k′<u
  = refl

min-get : ∀ {m l k} → Min m l → [ k ]ᴱ <⁺ m → get k l ≡ nothing
min-get min-[] _ = refl

min-get {m} {(k′ , v′) ∷ kvs′} {k} (min-∷ m<k′ m′ .v′) k<m with dec-≡ k′ k
... | yes p = contradiction p (≢-sym (<⇒≢ (strip-<⁺ (trans⁺ [ k ]ᴱ k<m m<k′))))
... | no  p = min-get m′ k<m

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

get-insed {m} {(k′ , v′) ∷ kvs′} {k} f (min-∷ k′<m′ m′ v) = {!!}

lookup-insed : ∀ {k h} → (f : Maybe (Val k) → Val k) → (t : Tree V ⊥⁺ ⊤⁺ h) →
  lookup k (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k ]<⊤⁺ ≡ just (f (lookup k t ⊥⁺<[ k ]<⊤⁺))

lookup-insed {k} f t
  rewrite sym (get≡lookup k t ⊥⁺<[ k ]<⊤⁺)
        | sym (get≡lookup k (proj₂ (insertWith k f t ⊥⁺<[ k ]<⊤⁺)) ⊥⁺<[ k ]<⊤⁺)
        | sym (put≡insert k f t ⊥⁺<[ k ]<⊤⁺)
  = get-insed f (flat-min t)

{-
insert-ok₂ : ∀ k f m l → Ord m l → get k (put k f l) ≡ just (f (get k l))

insert-ok₂ k f .⊤⁺ [] ord-[]
  rewrite ≟-diag (refl {x = k})
        | CHEATER (f nothing)
        = refl

insert-ok₂ k f [ k′ ]ᴱ ((.k′ , v′) ∷ kvs′) (ord-∷ k′<m o′ .v′) with <-cmp k k′

insert-ok₂ k f [ k′ ]ᴱ ((.k′ , v′) ∷ kvs′) (ord-∷ k′<m o′ .v′) | tri< p₁ p₂ _
  rewrite ≟-diag (refl {x = k})
     with k ≟ k′
... | yes p₄ = contradiction p₄ p₂
... | no  _
  rewrite ord-lookup k kvs′ o′ (trans⁺ [ k ]ᴱ [ p₁ ]ᴿ k′<m)
        | CHEATER (f nothing)
        = refl

insert-ok₂ k f [ k′ ]ᴱ ((.k′ , v′) ∷ kvs′) (ord-∷ k′<m o′ .v′) | tri≈ _ p₂ _
  rewrite p₂
        | ≟-diag (refl {x = k′})
        | CHEATER v′
        | CHEATER (f (just v′))
        | CHEATER (f (just v′))
        = refl

insert-ok₂ k f [ k′ ]ᴱ ((.k′ , v′) ∷ kvs′) (ord-∷ k′<m o′ .v′) | tri> _ p₂ _ with k ≟ k′
... | yes p₄ = contradiction p₄ p₂
... | no  p₄ = insert-ok₂ k f _ kvs′ o′
-}
