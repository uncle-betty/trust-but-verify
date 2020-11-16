module BitVec where

open import Data.Bool using (Bool ; true ; false ; f<t) renaming (_<_ to _<ᵇ_)

open import Data.Bool.Properties using () renaming (
    _≟_ to _≟ᵇ_ ; _<?_ to _<?ᵇ_ ; <-cmp to <-cmpᵇ ; <-asym to <ᵇ-asym ; <-trans to <-transᵇ
  )

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate)
open import Data.Vec.Properties using (≡-dec)

open import Function using (_$_)

open import Level using (0ℓ)

open import Relation.Binary using (
    Asymmetric ; Irreflexive ; Transitive ; Decidable ; Trichotomous ; tri< ; tri≈ ; tri>
  ) renaming (
    DecSetoid to DSD ; StrictTotalOrder to STO ; IsStrictTotalOrder to ISTO
  )

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; sym)
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)
open import Relation.Nullary using (Dec ; _because_ ; ofʸ ; ofⁿ ; ¬_)
open import Relation.Nullary.Negation using (contradiction)

BitVec : ℕ → Set
BitVec = Vec Bool

bv-dsd : {ℕ} → DSD 0ℓ 0ℓ
bv-dsd {n} = decSetoid $ ≡-dec _≟ᵇ_ {n}

infix 4 _≟_

_≟_ : {n : ℕ} → Decidable (_≡_ {0ℓ} {BitVec n})
_≟_ {n} = DSD._≟_ (bv-dsd {n})

infix 4 _≮ᵇ_

_≮ᵇ_ : Bool → Bool → Set
_≮ᵇ_ b₁ b₂ = ¬ b₁ <ᵇ b₂

infix 4 _<_

data _<_ : {n : ℕ} → BitVec n → BitVec n → Set where
  <⁰ : {n : ℕ} → {bv₁ bv₂ : BitVec n} → {b₁ b₂ : Bool} →
    bv₁ ≡ bv₂ → b₁ <ᵇ b₂ → (b₁ ∷ bv₁) < (b₂ ∷ bv₂)

  <⁺ : {n : ℕ} → {bv₁ bv₂ : BitVec n} → {b₁ b₂ : Bool} →
    bv₁ < bv₂ → (b₁ ∷ bv₁) < (b₂ ∷ bv₂)

infix 4 _≮_

_≮_ : {n : ℕ} → BitVec n → BitVec n → Set
_≮_ bv₁ bv₂ = ¬ bv₁ < bv₂

[]≮[] : [] ≮ []
[]≮[] ()

<-irrefl : {n : ℕ} → Irreflexive _≡_ (_<_ {n})
<-irrefl {_} {[]}       {[]}       _                 = []≮[]
<-irrefl {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} refl (<⁺ bv₁<bv₂) = <-irrefl refl bv₁<bv₂

<-asym : {n : ℕ} → Asymmetric (_<_ {n})
<-asym {_} {[]}       {[]}       _               = []≮[]

<-asym {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} (<⁰ refl b₁<b₂) (<⁰ refl b₂<b₁) =
  contradiction b₂<b₁ (<ᵇ-asym b₁<b₂)

<-asym {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} (<⁰ refl b₁<b₂) (<⁺ bv₁<bv₁)    = <-irrefl refl bv₁<bv₁
<-asym {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} (<⁺ bv₁<bv₂)    (<⁰ refl b₂<b₁) = <-irrefl refl bv₁<bv₂
<-asym {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} (<⁺ bv₁<bv₂)    (<⁺ bv₂<bv₁)    = <-asym bv₁<bv₂ bv₂<bv₁

<ᵇ⇒≢ : {b₁ b₂ : Bool} → b₁ <ᵇ b₂ → b₁ ≢ b₂
<ᵇ⇒≢ {false} {true} f<t = λ ()

∷-≢₁ : {n : ℕ} → {b₁ b₂ : Bool} → {bv₁ bv₂ : BitVec n} → b₁ ≢ b₂ → b₁ ∷ bv₁ ≢ b₂ ∷ bv₂
∷-≢₁ {_} {b₁} {b₂} {bv₁} {bv₂} b₁≢b₂ with b₁ ∷ bv₁ ≟ b₂ ∷ bv₂
... | true  because ofʸ refl = contradiction refl b₁≢b₂
... | false because ofⁿ p = p

∷-≢₂ : {n : ℕ} → {b₁ b₂ : Bool} → {bv₁ bv₂ : BitVec n} → bv₁ ≢ bv₂ → b₁ ∷ bv₁ ≢ b₂ ∷ bv₂
∷-≢₂ {_} {b₁} {b₂} {bv₁} {bv₂} bv₁≢bv₂ with b₁ ∷ bv₁ ≟ b₂ ∷ bv₂
... | true because ofʸ refl = contradiction refl bv₁≢bv₂
... | false because ofⁿ p = p

<⇒≢ : {n : ℕ} → {bv₁ bv₂ : BitVec n} → bv₁ < bv₂ → bv₁ ≢ bv₂
<⇒≢ {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} (<⁰ refl b₁<b₂) = ∷-≢₁ (<ᵇ⇒≢ b₁<b₂)
<⇒≢ {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} (<⁺ bv₁<bv₂) = ∷-≢₂ (<⇒≢ bv₁<bv₂)

infix 4 _<?_

_<?_ : {n : ℕ} → Decidable (_<_ {n})
_<?_ [] [] = false because ofⁿ []≮[]

_<?_ (b₁ ∷ bv₁) (b₂ ∷ bv₂) with bv₁ <? bv₂
... | true because ofʸ bv₁<bv₂ = true because ofʸ (<⁺ bv₁<bv₂)
... | false because ofⁿ bv₁≮bv₂ with bv₁ ≟ bv₂

... | false because ofⁿ bv₁≢bv₂ = false because ofⁿ (lem bv₁≢bv₂ bv₁≮bv₂)
  where
  lem : {n : ℕ} → {bv₁ bv₂ : BitVec n} → {b₁ b₂ : Bool} →
    bv₁ ≢ bv₂ → bv₁ ≮ bv₂ → (b₁ ∷ bv₁) ≮ (b₂ ∷ bv₂)

  lem bv₁≢bv₂ _       (<⁰ bv₁≡bv₂ _) = contradiction bv₁≡bv₂ bv₁≢bv₂
  lem _       bv₁≮bv₂ (<⁺ bv₁<bv₂)   = contradiction bv₁<bv₂ bv₁≮bv₂

... | true  because ofʸ bv₁≡bv₂ with b₁ <?ᵇ b₂
... | true  because ofʸ b₁<b₂ = true  because ofʸ (<⁰ bv₁≡bv₂ b₁<b₂)

... | false because ofⁿ b₁≮b₂ = false because ofⁿ (lem bv₁≮bv₂ b₁≮b₂)
  where
  lem : {n : ℕ} → {bv₁ bv₂ : BitVec n} → {b₁ b₂ : Bool} →
    bv₁ ≮ bv₂ → b₁ ≮ᵇ b₂ → (b₁ ∷ bv₁) ≮ (b₂ ∷ bv₂)

  lem _       b₁≮b₂ (<⁰ _ b₁<b₂) = contradiction b₁<b₂ b₁≮b₂
  lem bv₁≮bv₂ _     (<⁺ bv₁<bv₂) = contradiction bv₁<bv₂ bv₁≮bv₂

≢-≮⇒> : {n : ℕ} → {bv₁ bv₂ : BitVec n} → bv₁ ≢ bv₂ → bv₁ ≮ bv₂ → bv₂ < bv₁
≢-≮⇒> {_} {[]}       {[]}       bv₁≢bv₂ bv₁≮bv₂ = contradiction refl bv₁≢bv₂
≢-≮⇒> {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} bv₁≢bv₂ bv₁≮bv₂ with bv₂ <? bv₁
... | true  because ofʸ bv₂<bv₁ = <⁺ bv₂<bv₁
... | false because ofⁿ bv₂≮bv₁ with bv₂ ≟ bv₁
... | false because ofⁿ bv₂≢bv₁ = contradiction (<⁺ (≢-≮⇒> bv₂≢bv₁ bv₂≮bv₁)) bv₁≮bv₂
... | true  because ofʸ refl    with <-cmpᵇ b₂ b₁
... | tri< b₂<b₁ _    _     = <⁰ refl b₂<b₁
... | tri≈ _     refl _     = contradiction refl bv₁≢bv₂
... | tri> _     _    b₁<b₂ = contradiction (<⁰ refl b₁<b₂) bv₁≮bv₂

<-trans : {n : ℕ} → Transitive (_<_ {n})

<-trans {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} {b₃ ∷ bv₃} (<⁰ refl b₁<ᵇb₂) (<⁰ refl b₂<ᵇb₃) =
  <⁰ refl (<-transᵇ b₁<ᵇb₂ b₂<ᵇb₃)

<-trans {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} {b₃ ∷ bv₃} (<⁰ refl b₁<ᵇb₂) (<⁺ bv₂<bv₃)     = <⁺ bv₂<bv₃
<-trans {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} {b₃ ∷ bv₃} (<⁺ bv₁<bv₂)     (<⁰ refl b₂<b₃)  = <⁺ bv₁<bv₂

<-trans {_} {b₁ ∷ bv₁} {b₂ ∷ bv₂} {b₃ ∷ bv₃} (<⁺ bv₁<bv₂)     (<⁺ bv₂<bv₃)     =
  <⁺ (<-trans bv₁<bv₂ bv₂<bv₃)

comp : {n : ℕ} → Trichotomous _≡_ (_<_ {n})
comp bv₁ bv₂ with bv₁ <? bv₂
... | true  because ofʸ bv₁<bv₂ = tri< bv₁<bv₂            (<⇒≢ bv₁<bv₂) (<-asym bv₁<bv₂)
... | false because ofⁿ bv₁≮bv₂ with bv₁ ≟ bv₂
... | true  because ofʸ bv₁≡bv₂ = tri≈ (<-irrefl bv₁≡bv₂) bv₁≡bv₂       (<-irrefl (sym bv₁≡bv₂))
... | false because ofⁿ bv₁≢bv₂ = tri> bv₁≮bv₂            bv₁≢bv₂       (≢-≮⇒> bv₁≢bv₂ bv₁≮bv₂)

bv-isto : {n : ℕ} → ISTO _≡_ _<_
bv-isto {n} = record {
    isEquivalence = DSD.isEquivalence (bv-dsd {n}) ;
    trans         = <-trans ;
    compare       = comp
  }

bv-sto : {n : ℕ} → STO 0ℓ 0ℓ 0ℓ
bv-sto {n} = record {
    Carrier            = BitVec n ;
    _≈_                = _≡_ ;
    _<_                = _<_ ;
    isStrictTotalOrder = bv-isto
  }

null : {n : ℕ} → BitVec n
null = replicate false

module _ {T : Set} (T-≈ : T → T → Set) (T-≟ : Decidable T-≈) where
  split : {n↓ : ℕ} → (f : BitVec (suc n↓) → T) → Bool → BitVec n↓ → T
  split f b bv = f (b ∷ bv)

  join : {n↓ : ℕ} → (f₁ f₂ : BitVec (suc n↓) → T) →
    (∀ bv → T-≈ (f₁ (true ∷ bv)) (f₂ (true ∷ bv))) →
    (∀ bv → T-≈ (f₁ (false ∷ bv)) (f₂ (false ∷ bv))) →
    (∀ bv → T-≈ (f₁ bv) (f₂ bv))

  join f₁ f₂ p q (true ∷ bv)  = p bv
  join f₁ f₂ p q (false ∷ bv) = q bv

  bv-func-≟ : {n↑ n↓ : ℕ} → (f₁ f₂ : BitVec n↓ → T) →
    (∀ bv → T-≈ (f₁ bv) (f₂ bv)) ⊎ (∃ λ bv → ¬ T-≈ (f₁ bv) (f₂ bv))

  bv-func-≟ {n↑} {zero} f₁ f₂ with T-≟ (f₁ []) (f₂ [])
  ... | true  because ofʸ p = inj₁ λ { [] → p }
  ... | false because ofⁿ p = inj₂ ([] , p)

  bv-func-≟ {n↑} {suc n↓} f₁ f₂
    with bv-func-≟ {suc n↑} {n↓} (split f₁ true) (split f₂ true)
  ... | inj₂ (bv , p) = inj₂ (true ∷ bv , p)
  ... | inj₁ qᵗ
    with bv-func-≟ {suc n↑} {n↓} (split f₁ false) (split f₂ false)
  ... | inj₂ (bv , p) = inj₂ (false ∷ bv , p)
  ... | inj₁ qᶠ = inj₁ (join f₁ f₂ qᵗ qᶠ)
