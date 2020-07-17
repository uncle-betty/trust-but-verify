open import Agda.Primitive using (Level)
open import Data.List using (List ; [] ; _∷_ ; _++_) renaming ([_] to [_]ᴸ)
open import Data.List.Properties using (++-monoid)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_)
open import Data.Nat.Properties using (<-strictTotalOrder ; <-cmp ; _≟_ ; ≟-diag ; <⇒≢; <⇒≤ ; <-transˡ ; ≤-refl)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; trans ; sym ; ≢-sym ; cong ; subst ; inspect ; [_])
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Tactic.MonoidSolver using (solve)

open import Data.Tree.AVL.Indexed <-strictTotalOrder renaming ([_] to [_]ᴱ)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using () renaming ([<]-injective to strip-<⁺)

module Avl {ℓⱽ : Level} (V : Value ℓⱽ) where

private
  Val = Value.family V
  V≈  = Value.respects V

postulate CHEATER : ∀ {k} (v : Val k) → V≈ refl v ≡ v

bounds-< : ∀ {l u h} → Tree V l u h → l <⁺ u
bounds-<         (leaf l<u)       = l<u
bounds-< {l = l} (node _ tˡ tʳ _) = trans⁺ l (bounds-< tˡ) (bounds-< tʳ)

pivot : ∀ {l u h} → Tree V l u (suc h) → ℕ
pivot (node (k′ , _) _ _ _) = k′

pivot-< : ∀ {l u h} → (t : Tree V l u (suc h)) → [ pivot t ]ᴱ <⁺ u
pivot-< (node _     _    (leaf l<u)       _) = l<u
pivot-< (node (k′ , _) _ (node _ tˡ tʳ _) _) = trans⁺ [ k′ ]ᴱ (bounds-< tˡ) (bounds-< tʳ)

pivot-> : ∀ {l u h} → (t : Tree V l u (suc h)) → l <⁺ [ pivot t ]ᴱ
pivot->         (node _        (leaf l<u)       _ _) = l<u
pivot-> {l = l} (node (k′ , _) (node _ tˡ tʳ _) _ _) = trans⁺ l (bounds-< tˡ) (bounds-< tʳ)

flatten : ∀ {l u h} → Tree V l u h → List (K& V)
flatten (leaf _)                 = []
flatten (node (k′ , v′) tˡ tʳ _) = flatten tˡ ++ (k′ , v′) ∷ flatten tʳ

data Max (m : Key⁺) : List (K& V) → Set where
  max-[] : Max m []
  max-∷ : {kv : K& V} → {kvs : List (K& V)} → ([ proj₁ kv ]ᴱ <⁺ m) → Max m kvs → Max m (kv ∷ kvs)

max-++ : ∀ {m l₁ l₂} → Max m l₁ → Max m l₂ → Max m (l₁ ++ l₂)
max-++ {l₁ = []} _ p₂ = p₂
max-++ {l₁ = e ∷ es} (max-∷ pᵉ pᵉˢ) p₂ = max-∷ pᵉ (max-++ pᵉˢ p₂) 

max-lax : ∀ {m m′ l} → Max m l → m <⁺ m′ → Max m′ l
max-lax {l = []} pᵐ m<m′ = max-[]
max-lax {m = m} {l = e ∷ es} (max-∷ pᵉ pᵉˢ) m<m′ = max-∷ (trans⁺ [ proj₁ e ]ᴱ pᵉ m<m′) (max-lax pᵉˢ m<m′ )

flatten-max : ∀ {l u h} (t : Tree V l u h) → Max u (flatten t)
flatten-max (leaf _) = max-[]
flatten-max t@(node (k , v) tˡ tʳ _) = max-++ (max-lax (flatten-max tˡ) (pivot-< t)) (max-∷ (pivot-< t) (flatten-max tʳ)) 

lookupˡ : (k : ℕ) → List (K& V) → Maybe (Val k)
lookupˡ k []               = nothing
lookupˡ k ((k′ , v′) ∷ xs) with k ≟ k′
... | yes p = just (V≈ (sym p) v′)
... | no  _ = lookupˡ k xs

lookupˡ₂ : (k : ℕ) → List (K& V) → List (K& V) → Maybe (Val k)
lookupˡ₂ k xs ys with lookupˡ k xs
... | just v′ = just v′
... | nothing = lookupˡ k ys

lookupˡ-prepend : ∀ {k xs ys} → lookupˡ k xs ≡ nothing → lookupˡ k (xs ++ ys) ≡ lookupˡ k ys
lookupˡ-prepend         {xs = []}        eq = refl
lookupˡ-prepend {k = k} {(k′ , v′) ∷ xs} eq with k ≟ k′
... | no  _ = lookupˡ-prepend {k = k} {xs} eq
... | yes _ with eq
... | ()

lookupˡ-append : ∀ {k v xs ys} → lookupˡ k xs ≡ just v → lookupˡ k (xs ++ ys) ≡ just v
lookupˡ-append {k = k} {xs = (k′ , v′) ∷ xs} eq with k ≟ k′
... | yes _ = eq
... | no  _ = lookupˡ-append {xs = xs} eq

lookupˡ-split : (k : ℕ) → (xs ys : List (K& V)) → lookupˡ k (xs ++ ys) ≡ lookupˡ₂ k xs ys
lookupˡ-split _ []               _  = refl
lookupˡ-split k ((k′ , v′) ∷ xs) ys with k ≟ k′
... | yes _ = refl
... | no  _ with lookupˡ k xs | inspect (lookupˡ k) xs
... | nothing  | [ eq ] = lookupˡ-prepend {xs = xs} eq
... | just v′′ | [ eq ] = lookupˡ-append {xs = xs} eq

failˡ : ∀ {l u h} → (k : ℕ) → (t : Tree V l u h) → (u <⁺ [ k ]ᴱ ⊎ u ≡ [ k ]ᴱ) → lookupˡ k (flatten t) ≡ nothing
failˡ _ (leaf _) _ = refl

failˡ k (node (k′ , v′) tˡ tʳ _) (inj₁ u<k)
  rewrite lookupˡ-split k (flatten tˡ) ((k′ , v′) ∷ flatten tʳ)
        | failˡ k tˡ (inj₁ (trans⁺ [ k′ ]ᴱ (bounds-< tʳ) u<k))
     with k ≟ k′
... | yes p  = contradiction p (≢-sym (<⇒≢ (strip-<⁺ (trans⁺ [ k′ ]ᴱ (bounds-< tʳ) u<k))))
... | no  _  = failˡ k tʳ (inj₁ u<k)

failˡ k (node (k′ , v′) tˡ tʳ _) (inj₂ u≡k)
  rewrite lookupˡ-split k (flatten tˡ) ((k′ , v′) ∷ flatten tʳ)
        | failˡ k tˡ (inj₁ (subst (λ # → [ k′ ]ᴱ <⁺ #) u≡k (bounds-< tʳ)))
     with k ≟ k′
... | yes p = contradiction p (≢-sym (<⇒≢ (strip-<⁺ (subst (λ # → [ k′ ]ᴱ <⁺ #) u≡k (bounds-< tʳ)))))
... | no  _ = failˡ k tʳ (inj₂ u≡k)

failʳ : ∀ {l u h} → (k : ℕ) → (t : Tree V l u h) → [ k ]ᴱ <⁺ l ⊎ [ k ]ᴱ ≡ l → lookupˡ k (flatten t) ≡ nothing
failʳ _ (leaf _) _ = refl

failʳ k (node (k′ , v′) tˡ tʳ _) (inj₁ k<u)
  rewrite lookupˡ-split k (flatten tˡ) ((k′ , v′) ∷ flatten tʳ)
        | failʳ k tˡ (inj₁ k<u)
     with k ≟ k′
... | yes p = contradiction p (<⇒≢ (strip-<⁺ (trans⁺ [ k ]ᴱ k<u (bounds-< tˡ))))
... | no  _ = failʳ k tʳ (inj₁ (trans⁺ [ k ]ᴱ k<u (bounds-< tˡ)))

failʳ k (node (k′ , v′) tˡ tʳ _) (inj₂ k≡u)
  rewrite lookupˡ-split k (flatten tˡ) ((k′ , v′) ∷ flatten tʳ)
        | failʳ k tˡ (inj₂ k≡u)
     with k ≟ k′
... | yes p = contradiction p (<⇒≢ (strip-<⁺ (subst (λ # → # <⁺ [ k′ ]ᴱ) (sym k≡u) (bounds-< tˡ))))
... | no  _ = failʳ k tʳ (inj₁ (subst (λ # → # <⁺ [ k′ ]ᴱ) (sym k≡u) (bounds-< tˡ)))

lookup-≡ : ∀ {l u h} → (k : ℕ) (t : Tree V l u h) (l<k<u : l < k < u) → lookupˡ k (flatten t) ≡ lookup k t l<k<u
lookup-≡ k (leaf l<u) l<k<u = refl
lookup-≡ k (node (k′ , v′) tˡ tʳ _) (l<k , k<u)
  rewrite lookupˡ-split k (flatten tˡ) ((k′ , v′) ∷ flatten tʳ)
     with <-cmp k′ k | k ≟ k′ | inspect (k ≟_) k′

... | tri< _  p₂ _  | yes p₄ | _       = contradiction p₄ (≢-sym p₂)
... | tri< p₁ _  _  | no  _  | [ eq₁ ]
  rewrite failˡ k tˡ (inj₁ [ p₁ ]ᴿ)
        | eq₁ 
        = lookup-≡ k tʳ ([ p₁ ]ᴿ , k<u)

... | tri≈ _  p₂ _  | yes p₄  | [ eq₁ ]
  rewrite failˡ k tˡ (inj₂ (cong [_]ᴱ p₂))
        | eq₁
        | p₂
        | p₄
        = refl
        
... | tri≈ _  p₂ _  | no  p₄ | _      = contradiction p₂ (≢-sym p₄)
... | tri> _  p₂ _  | yes p₄ | _      = contradiction p₄ (≢-sym p₂)

... | tri> p₁ p₂ p₃ | no  _  | [ eq₁ ] with lookupˡ k (flatten tˡ) | inspect (lookupˡ k) (flatten tˡ)

... | nothing | [ eq₂ ]
  rewrite eq₁
        | sym (lookup-≡ k tˡ (l<k , [ p₃ ]ᴿ))
        | eq₂
        = failʳ k tʳ (inj₁ [ p₃ ]ᴿ) 

... | just v  | [ eq₂ ]
  rewrite sym (lookup-≡ k tˡ (l<k , [ p₃ ]ᴿ))
        | eq₂
        = refl

pat-join₁ : (as bs cs ds : List (K& V)) → (as ++ bs) ++ cs ++ ds ≡ (as ++ bs ++ cs) ++ ds
pat-join₁ as bs cs ds = solve (++-monoid (K& V))

pat-join₂ : (as bs cs : List (K& V)) → as ++ bs ++ cs ≡ (as ++ bs) ++ cs
pat-join₂ as bs cs = solve (++-monoid (K& V))

pat-join₃ : (as bs cs ds : List (K& V)) → as ++ (bs ++ cs) ++ ds ≡ (as ++ bs ++ cs) ++ ds
pat-join₃ as bs cs ds = solve (++-monoid (K& V))

pat-join₄ : (as bs cs ds : List (K& V)) → (as ++ bs) ++ cs ++ ds ≡ as ++ (bs ++ cs) ++ ds
pat-join₄ as bs cs ds = solve (++-monoid (K& V))

lem-joinˡ⁺ :
  ∀ {l u hˡ hʳ h} k v i → (tˡ : Tree V _ _ _) → ∀ tʳ b → 
  flatten (proj₂ (joinˡ⁺ {l = l} {u} {hˡ} {hʳ} {h} (k , v) (i , tˡ) tʳ b)) ≡ flatten tˡ ++ ((k , v) ∷ flatten tʳ)

lem-joinˡ⁺ k₆ v₆ 1# (node (k₂ , v₂) t₁ (node (k₄ , v₄) t₃ t₅ b) ∼+) t₇ ∼- =
  pat-join₁ (flatten t₁) ((k₂ , v₂) ∷ flatten t₃) ((k₄ , v₄) ∷ flatten t₅) ((k₆ , v₆) ∷ flatten t₇)

lem-joinˡ⁺ k₄ v₄ 1# (node (k₂ , v₂) t₁ (leaf _)                 ∼-) t₅ ∼- =
  pat-join₂ (flatten t₁) ((k₂ , v₂) ∷ []) ((k₄ , v₄) ∷ flatten t₅)

lem-joinˡ⁺ k₄ v₄ 1# (node (k₂ , v₂) t₁ (node (k₃ , v₃) t₈ t₉ _) ∼-) t₅ ∼- =
  pat-join₃ (flatten t₁) ((k₂ , v₂) ∷ flatten t₈) ((k₃ , v₃) ∷ flatten t₉) ((k₄ , v₄) ∷ flatten t₅)

lem-joinˡ⁺ k₄ v₄ 1# (node (k₂ , v₂) t₁ (node (k₃ , v₃) t₆ t₇ _) ∼0) t₅ ∼- =
  pat-join₃ (flatten t₁) ((k₂ , v₂) ∷ flatten t₆) ((k₃ , v₃) ∷ flatten t₇) ((k₄ , v₄) ∷ flatten t₅) 

lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼+) t₃ ∼0 = refl
lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (leaf _)         ∼0) t₃ ∼0 = refl
lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼0) t₃ ∼0 = refl
lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (leaf _)         ∼-) t₃ ∼0 = refl
lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼-) t₃ ∼0 = refl

lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼+) t₃ ∼+ = refl
lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (leaf _)         ∼0) t₃ ∼+ = refl
lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼0) t₃ ∼+ = refl
lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (leaf _)         ∼-) t₃ ∼+ = refl
lem-joinˡ⁺ k₂ v₂ 1# (node (k₁ , v₁) t₄ (node _ _ _ _)   ∼-) t₃ ∼+ = refl

lem-joinˡ⁺ k₂ v₂ 0# t₁                                      t₃ b  = refl

lem-joinʳ⁺ :
  ∀ {l u hˡ hʳ h} k v tˡ i → (tʳ : Tree V _ _ _) → ∀ b → 
  flatten (proj₂ (joinʳ⁺ {l = l} {u} {hˡ} {hʳ} {h} (k , v) tˡ (i , tʳ) b)) ≡ flatten tˡ ++ ((k , v) ∷ flatten tʳ)

lem-joinʳ⁺ k₂ v₂ t₁ 1# (node (k₆ , v₆) (node (k₄ , v₄) t₃ t₅ b)    t₇ ∼-) ∼+ =
  pat-join₄ (flatten t₁) ((k₂ , v₂) ∷ flatten t₃) ((k₄ , v₄) ∷ flatten t₅) ((k₆ , v₆) ∷ flatten t₇)

lem-joinʳ⁺ k₂ v₂ t₁ 1# (node (k₄ , v₄) t₃@(leaf _)                 t₅ ∼+) ∼+ =
  sym (pat-join₂ (flatten t₁) ((k₂ , v₂) ∷ []) ((k₄ , v₄) ∷ flatten t₅))
  
lem-joinʳ⁺ k₂ v₂ t₁ 1# (node (k₄ , v₄) t₃@(node (k₆ , v₆) t₇ t₈ _) t₅ ∼+) ∼+ =
  sym (pat-join₃ (flatten t₁) ((k₂ , v₂) ∷ flatten t₇) ((k₆ , v₆) ∷ flatten t₈) ((k₄ , v₄) ∷ flatten t₅))

lem-joinʳ⁺ k₂ v₂ t₁ 1# (node (k₄ , v₄) t₃@(node (k₆ , v₆) t₇ t₈ _) t₅ ∼0) ∼+ =
  sym (pat-join₃ (flatten t₁) ((k₂ , v₂) ∷ flatten t₇) ((k₆ , v₆) ∷ flatten t₈) ((k₄ , v₄) ∷ flatten t₅))

lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼-) ∼0 = refl
lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (leaf _)       _ ∼0) ∼0 = refl
lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼0) ∼0 = refl
lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (leaf _)       _ ∼+) ∼0 = refl
lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼+) ∼0 = refl

lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼-) ∼- = refl
lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (leaf _)       _ ∼0) ∼- = refl
lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼0) ∼- = refl
lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (leaf _)       _ ∼+) ∼- = refl
lem-joinʳ⁺ k₂ v₂ t₁ 1# t₃@(node _ (node _ _ _ _) _ ∼+) ∼- = refl

lem-joinʳ⁺ k₂ v₂ t₁ 0# t₃                              _  = refl

insertWithˡ : (k : ℕ) → (f : Maybe (Val k) → Val k) → (l : List (K& V)) → List (K& V)
insertWithˡ k f [] = [ (k , f nothing) ]ᴸ
insertWithˡ k f ((k′ , v′) ∷ kvs) with <-cmp k k′
... | tri< _ _  _ = (k , f nothing) ∷ (k′ , v′) ∷ kvs 
... | tri≈ _ p₂ _ = (k′ , V≈ p₂ (f (just (V≈ (sym p₂) v′)))) ∷ kvs
... | tri> _ _  _ = (k′ , v′) ∷ (insertWithˡ k f kvs) 

lem-insert₁ : ∀ k f k′ v′ l₁ l₂ → (k<k′ : k < k′) → insertWithˡ k f (l₁ ++ (k′ , v′) ∷ l₂) ≡ (insertWithˡ k f l₁) ++ (k′ , v′) ∷ l₂

lem-insert₁ k f k′ v' [] l₂ k<k′ with <-cmp k k′
... | tri< _  _ _ = refl
... | tri≈ p₁ _ _ = contradiction k<k′ p₁
... | tri> p₁ _ _ = contradiction k<k′ p₁

lem-insert₁ k f k′ v′ ((k′′ , v′′) ∷ l₁′) l₂ k<k′ with <-cmp k k′′
... | tri< _ _ _ = refl
... | tri≈ _ _ _ = refl
... | tri> _ _ _ rewrite lem-insert₁ k f k′ v′ l₁′ l₂ k<k′ = refl

lem-insert₂ : ∀ k f kvs k′ v′ kvs′ → Max [ k′ ]ᴱ kvs → k′ ≤ k → insertWithˡ k f (kvs ++ (k′ , v′) ∷ kvs′) ≡ kvs ++ (insertWithˡ k f ((k′ , v′) ∷ kvs′))
lem-insert₂ _ _ []                    _  _  _    _            _    = refl
lem-insert₂ k f ((k′′ , v′′) ∷ kvs′′) k′ v′ kvs′ (max-∷ p p′) k′≤k with <-cmp k k′′
... | tri< _ _ p₃ = contradiction (<-transˡ (strip-<⁺ p) k′≤k) p₃
... | tri≈ _ _ p₃ = contradiction (<-transˡ (strip-<⁺ p) k′≤k) p₃
... | tri> _ _ _  = cong ((k′′ , v′′) ∷_) (lem-insert₂ k f kvs′′ k′ v′ kvs′ p′ k′≤k)

insert-≡ : ∀ {l u h} → (k : ℕ) → (f : Maybe (Val k) → Val k) → (t : Tree V l u h) (l<k<u : l < k < u) →
  flatten (proj₂ (insertWith k f t l<k<u)) ≡ insertWithˡ k f (flatten t)
insert-≡ _ _ (leaf _) _ = refl
insert-≡ k f (node (k′ , v′) tˡ tʳ _) (l<k , k<u) with <-cmp k k′ | inspect (<-cmp k) k′

insert-≡ k f (node (k′ , v′) tˡ tʳ b) (l<k , k<u) | tri< p₁ _ _ | _
  rewrite lem-insert₁ k f k′ v′ (flatten tˡ) (flatten tʳ) p₁
        | lem-joinˡ⁺ k′ v′ (proj₁ (insertWith k f tˡ (l<k , [ p₁ ]ᴿ))) (proj₂ (insertWith k f tˡ (l<k , [ p₁ ]ᴿ))) tʳ b
        | insert-≡ k f tˡ (l<k , [ p₁ ]ᴿ)
        = refl

insert-≡ k f (node (k′ , v′) tˡ tʳ _) (l<k , k<u) | tri≈ _ p₂ _ | [ eq₁ ]
  rewrite lem-insert₂ k f (flatten tˡ) k′ v′ (flatten tʳ) (flatten-max tˡ) (subst (_≤ k) p₂ (≤-refl {k}))
        | eq₁
        | p₂
        = refl

insert-≡ k f (node (k′ , v′) tˡ tʳ b) (l<k , k<u) | tri> _ _ p₃ | [ eq₁ ]
  rewrite lem-joinʳ⁺ k′ v′ tˡ (proj₁ (insertWith k f tʳ ([ p₃ ]ᴿ , k<u))) (proj₂ (insertWith k f tʳ ([ p₃ ]ᴿ , k<u))) b
        | lem-insert₂ k f (flatten tˡ) k′ v′ (flatten tʳ) (flatten-max tˡ) (<⇒≤ p₃)
        | eq₁
        | insert-≡ k f tʳ ([ p₃ ]ᴿ , k<u)
        = refl

insert-lookup-≡ : ∀ {l u h} (t : Tree V l u h) k k′ f (l<k<u : l < k < u) (l<k′<u : l < k′ < u) →
  lookupˡ k (insertWithˡ k′ f (flatten t)) ≡ lookup k (proj₂ (insertWith k′ f t l<k′<u)) l<k<u

insert-lookup-≡ t k k′ f l<k<u l<k′<u
  rewrite sym (insert-≡ k′ f t l<k′<u)
        | lookup-≡ k (proj₂ (insertWith k′ f t l<k′<u)) l<k<u
        = refl

data Ord : Key⁺ → List (K& V) → Set where
  ord-[] : Ord ⊤⁺ []
  ord-∷  : {k : ℕ} {m : Key⁺} {l : List (K& V)} → [ k ]ᴱ <⁺ m → Ord m l → ∀ v → Ord [ k ]ᴱ ((k , v) ∷ l)

new-min : ℕ → Key⁺ → Key⁺
new-min k ⊤⁺ = [ k ]ᴱ
new-min k ⊥⁺ = ⊥⁺
new-min k [ m ]ᴱ with <-cmp k m
... | tri< _ _ _ = [ k ]ᴱ
... | tri≈ _ _ _ = [ k ]ᴱ
... | tri> _ _ _ = [ m ]ᴱ

<-min : ∀ {k k′ k′′} → [ k′ ]ᴱ <⁺ [ k ]ᴱ → [ k′ ]ᴱ <⁺ [ k′′ ]ᴱ → [ k′ ]ᴱ <⁺ new-min k [ k′′ ]ᴱ
<-min {k} {k′} {k′′} k′<k k′<k′′ with <-cmp k k′′
... | tri< _ _ _ = k′<k 
... | tri≈ _ _ _ = k′<k 
... | tri> _ _ _ = k′<k′′ 

ord-insert : ∀ k f m′ l → Ord m′ l → Ord (new-min k m′) (insertWithˡ k f l)
ord-insert k f ⊤⁺ [] ord-[] = ord-∷ [ k ]<⊤⁺ ord-[] (f nothing)

ord-insert k f [ k′ ]ᴱ ((.k′ , v′) ∷ []) (ord-∷ k′<k′′ ord-[] .v′) with <-cmp k k′
... | tri< p₁ _  _  = ord-∷ [ p₁ ]ᴿ (ord-∷ [ k′ ]<⊤⁺ ord-[] v′) (f nothing)

... | tri≈ _  p₂ _
  rewrite p₂
        | CHEATER v′
        | CHEATER (f (just v′))
        = ord-∷ [ k′ ]<⊤⁺ ord-[] (f (just v′))

... | tri> _  _  p₃ = ord-∷ [ p₃ ]ᴿ (ord-∷ [ k ]<⊤⁺ ord-[] (f nothing)) v′

ord-insert k f [ k′ ]ᴱ ((.k′ , v′) ∷ (k′′ , v′′) ∷ kvs′′) (ord-∷ k′<k′′ (ord-∷ k′′<m o′′ .v′′) .v′)
  with <-cmp k k′ | ord-insert k f [ k′′ ]ᴱ ((k′′ , v′′) ∷ kvs′′) (ord-∷ k′′<m o′′ v′′)
... | tri< p₁ _  _  | _   = ord-∷ [ p₁ ]ᴿ (ord-∷ k′<k′′ (ord-∷ k′′<m o′′ v′′) v′) (f nothing)

... | tri≈ _  p₂ _  | _
  rewrite p₂
        | CHEATER v′
        | CHEATER (f (just v′))
        = ord-∷ k′<k′′ (ord-∷ k′′<m o′′ v′′) (f (just v′))

... | tri> _  _  p₃ | rec = ord-∷ (<-min [ p₃ ]ᴿ k′<k′′) rec v′

ord-lookup : ∀ {m} k l → Ord m l → [ k ]ᴱ <⁺ m → lookupˡ k l ≡ nothing
ord-lookup _ [] _ _ = refl
ord-lookup k ((k′ , v′) ∷ kvs′) (ord-∷ k′<m o′ .v′) k<k′ with k ≟ k′
... | yes p = contradiction p (<⇒≢ (strip-<⁺ k<k′))
... | no  _ = ord-lookup k kvs′ o′ (trans⁺ [ k ]ᴱ k<k′ k′<m)

insert-ok₁ : ∀ k k′ f l → k ≢ k′ → lookupˡ k (insertWithˡ k′ f l) ≡ lookupˡ k l
insert-ok₁ k k′ f [] k≢k′ with k ≟ k′
... | yes p = contradiction p k≢k′
... | no  p = refl

insert-ok₁ k k′ f ((k′′ , v′′) ∷ kvs′′) k≢k′ with <-cmp k′ k′′ | k ≟ k′′ | k ≟ k′ | inspect (k ≟_) k′′ | inspect (k ≟_) k′
... | _             | _      | yes p₅ | _       | _       = contradiction p₅ k≢k′
... | tri≈ _  p₂ _  | yes p₄ | _      | _       | _       = contradiction (subst (λ # → # ≡ k′) (sym p₄) (sym p₂)) k≢k′
... | tri< _  _  _  | yes _  | no  _  | [ eq₁ ] | [ eq₂ ] rewrite eq₂ | eq₁ = refl
... | tri> _  _  _  | yes _  | no  _  | [ eq₁ ] | _       rewrite eq₁ = refl
... | tri< p₁ p₂ p₃ | no  p₄ | no  p₅ | [ eq₁ ] | [ eq₂ ] rewrite eq₂ | eq₁ = refl
... | tri≈ _  _  _  | no  _  | no  _  | [ eq₁ ] | _       rewrite eq₁ = refl
... | tri> _  _  _  | no  _  | no  _  | [ eq₁ ] | _       rewrite eq₁ = insert-ok₁ k k′ f kvs′′ k≢k′   

insert-ok₂ : ∀ k f m l → Ord m l → lookupˡ k (insertWithˡ k f l) ≡ just (f (lookupˡ k l))

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
