module Transliterate where

open import Level using (0ℓ ; Lift)

open import Category.Monad using (RawMonad)
open import Category.Monad.State using (StateMonad ; State ; RawMonadState ; StateMonadState)

open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char) renaming (_≟_ to _≟-char_)
open import Data.Empty using (⊥)

open import Data.List
  using (List ; [] ; _∷_ ; [_] ; reverse ; drop ; dropWhile ; span) renaming (map to mapₗ)

open import Data.Maybe
  using (Maybe ; just ; nothing ; _<∣>_ ; fromMaybe) renaming (map to mapₘ ; _>>=_ to _>>=ₘ_)

open import Data.Nat using (ℕ ; zero; suc ; _∸_)
open import Data.Nat.Properties using () renaming (<-strictTotalOrder to <-STO-ℕ)
open import Data.Product using (_×_ ; _,_) renaming (map₁ to ×-map₁ ; map₂ to ×-map₂)
open import Data.String using (String ; fromList) renaming (_≟_ to _≟-str_ ; toList to toListₛ)
open import Data.String.Properties using () renaming (<-strictTotalOrder-≈ to <-STO-Str)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂) renaming (map₁ to ⊎-map₁ ; map₂ to ⊎-map₂)
open import Data.Sum.Categorical.Left (List String) using (Sumₗ) renaming (monadT to ⊎-monadT)
open import Data.Tree.AVL.Map using (Map ; empty ; insert ; lookup) renaming (toList to toListₘ)
open import Data.Unit using (⊤ ; tt)

open import Function using (_$_ ; _∘_ ; _|>_ ; case_of_)

open import Reflection.Abstraction using (abs)
open import Reflection.Argument using (Arg ; arg)
open import Reflection.Argument.Information using (arg-info)
open import Reflection.Argument.Relevance using (relevant)
open import Reflection.Argument.Visibility using (visible ; hidden)
open import Reflection.Literal using (nat)
open import Reflection.Name using (Name)

open import Reflection.Term
  using (Term ; var ; con ; def ; lam ; pat-lam ; pi ; lit ; unknown ; clause)

open import Reflection.TypeChecking.Monad using (TC ; unify ; typeError ; strErr)

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; does ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation using (¬?)

import SAT
import SMT
import Base

data BindingType : Set where
  binTyNormal : BindingType
  binTyAtom   : BindingType

data Binding : Set where
  binding : ℕ → BindingType → Binding

record Context : Set where
  field
    ctxInput   : List Char
    -- ^ input LFSC proof
    ctxVarNo   : ℕ
    -- ^ numbers the variables that hold atoms
    ctxDepth   : ℕ
    -- ^ current nesting depth of λ-abstractions (use: de Bruin indexes)
    ctxBins    : Map <-STO-Str Binding
    -- ^ λ-bound variables and the nesting depth of their λ-abstractions (use: de Bruin indexes)
    ctxSig     : List Term
    -- ^ types of the top-level λ-bindings (use: proof term's type signature)

open Context
open RawMonad (⊎-monadT 0ℓ (StateMonad Context)) using (return ; _>>=_ ; _>>_ ; _<$>_)

open RawMonadState (StateMonadState Context)
  using () renaming (return to return↑ ; get to get′ ; put to put′ ; modify to modify′)

StateEither : Set → Set
StateEither S = State Context (Sumₗ 0ℓ S)

data Token : Set where
  Open  : Token
  Close : Token
  Ident : String → Token

fail↑ : {S : Set} → List String → StateEither S
fail↑ ss = return↑ $ inj₁ ss

get↑ : StateEither Context
get↑ = (×-map₁ inj₂) ∘ get′

put↑ : Context → StateEither (Lift 0ℓ ⊤)
put↑ ctx = (×-map₁ inj₂) ∘ (put′ ctx)

modify↑ : (Context → Context) → StateEither (Lift 0ℓ ⊤)
modify↑ f = (×-map₁ inj₂) ∘ (modify′ f)

runState : {S : Set} → StateEither S → Context → Sumₗ 0ℓ S
runState m s = m s |> λ { (x , _) → x }

showToken : Token → String
showToken Open          = "("
showToken Close         = ")"
showToken (Ident ident) = ident

notNewLine = ¬? ∘ (_≟-char '\n')
whiteSpace = λ c → c ≟-char ' ' ⊎-dec c ≟-char '\t' ⊎-dec c ≟-char '\r' ⊎-dec c ≟-char '\n'
notEndOfToken = ¬? ∘ λ c → c ≟-char ')' ⊎-dec whiteSpace c

skipToToken : StateEither (Lift 0ℓ ⊤)
skipToToken = do
  ctx ← get↑
  case dropWhile whiteSpace (ctxInput ctx) of λ where
    (';' ∷ cs) → do
      finishUp ctx $ dropWhile notNewLine cs
      skipToToken
    cs → finishUp ctx cs
  where
    finishUp = λ ctx cs → put↑ $ record ctx {
        ctxInput = cs
      }

extractToken : StateEither Token
extractToken = do
  ctx ← get↑
  case ctxInput ctx of λ where
    ('(' ∷ cs) → finishUp ctx cs Open
    (')' ∷ cs) → finishUp ctx cs Close
    cs → case span notEndOfToken cs of λ where
      ([] , _ ) → fail↑ [ "LFSC - unexpected end of input" ]
      (ts , cs) → finishUp ctx cs $ Ident (fromList ts)
  where
    finishUp = λ ctx cs t → do
      put↑ $ record ctx {
          ctxInput = cs
        }
      return t

nextToken : StateEither Token
nextToken = skipToToken >> extractToken

expectOpen = nextToken >>= λ where
  Open  → return tt
  token → fail↑ $ "LFSC - expected '(', found '" ∷ showToken token ∷ "'" ∷ []

expectClose = nextToken >>= λ where
  Close → return tt
  token → fail↑ $ "LFSC - expected ')', found '" ∷ showToken token ∷ "'" ∷ []

newContext : String → Context
newContext input = record {
    ctxInput   = toListₛ input ;
    ctxVarNo   = 0 ;
    ctxDepth   = 0 ;
    ctxBins    = empty <-STO-Str ;
    ctxSig     = []
  }

localContext : {S : Set} → StateEither S → StateEither S
localContext toWrap = do
  saved ← get↑
  result ← toWrap
  modify↑ λ ctx → record saved {
      ctxInput = ctxInput ctx ;
      ctxVarNo = ctxVarNo ctx ;
      ctxSig   = ctxSig ctx
    }
  return result

module _ where
  open SAT
  open SMT

  pass₁ : ∀ {ℓ} → {S : Set ℓ} → S → S
  pass₁ x = x

  Directions = (List (Arg Term) → Term) × ℕ × ℕ

  constMap : Map <-STO-Str Directions
  constMap =
    -- pass the last argument through
    noEnv "check" (def (quote pass₁) , 0 , 1) $
    noEnv "term"  (def (quote pass₁) , 0 , 1) $

    -- built-ins
    noEnv "Bool"  (def (quote Data.Bool.Bool)     , 0 , 0) $
    noEnv "cln"   (con (quote Data.List.List.[])  , 0 , 0) $
    noEnv "clc"   (con (quote Data.List.List._∷_) , 0 , 2) $
    noEnv "cnfn"  (con (quote Data.List.List.[])  , 0 , 0) $
    noEnv "cnfc"  (con (quote Data.List.List._∷_) , 0 , 2) $
    noEnv "apply" (def (quote Function._$_)       , 2 , 2) $

    -- SAT
    -- bool, tt, ff, var, lit
    noEnv "pos"               (con (quote pos)        , 0 , 1) $
    noEnv "neg"               (con (quote neg)        , 0 , 1) $
    -- lit_flip, clause, concat_cl, clr, clause_append, simplify_clause
    withEnv "holds"           (def (quote Holdsᶜ)     , 0 , 1) $
    withEnv "R"               (def (quote resolve-r⁺) , 2 , 3) $
    withEnv "Q"               (def (quote resolve-q⁺) , 2 , 3) $
    withEnv "satlem_simplify" (def (quote mp⁺)        , 3 , 2) $
    withEnv "satlem"          (def (quote mpᶜ)        , 2 , 2) $
    -- clause_dedup, cnf_holds, cnfn_proof, cnfc_proof

    -- SMT
    -- formula
    noEnv "th_holds"          (def (quote Holds)           , 0 , 1) $
    noEnv "true"              (con (quote trueᶠ)           , 0 , 0) $
    noEnv "false"             (con (quote falseᶠ)          , 0 , 0) $
    -- formula_op1, formula_op2, formula_op3
    noEnv "not"               (con (quote notᶠ)            , 0 , 1) $
    noEnv "and"               (con (quote andᶠ)            , 0 , 2) $
    noEnv "or"                (con (quote orᶠ)             , 0 , 2) $
    noEnv "impl"              (con (quote implᶠ)           , 0 , 2) $
    noEnv "iff"               (con (quote iffᶠ)            , 0 , 2) $
    noEnv "xor"               (con (quote xorᶠ)            , 0 , 2) $
    noEnv "ifte"              (con (quote iteᶠ)            , 0 , 3) $
    -- sort, term
    noEnv "="                 (con (quote equᶠ)            , 1 , 2) $
    -- ite, let, flet, Bool
    noEnv "p_app"             (con (quote appᵇ)            , 0 , 1) $
    -- t_true, t_false
    noEnv "t_t_neq_f"         (def (quote t≢fᵇ)            , 0 , 0) $
    noEnv "pred_eq_t"         (def (quote x⇒x≡tᵇ)          , 1 , 1) $
    noEnv "pred_eq_f"         (def (quote ¬x⇒x≡fᵇ)         , 1 , 1) $
    -- f_to_b
    noEnv "true_preds_equal"  (def (quote x⇒y⇒x≡yᵇ)        , 2 , 2) $
    noEnv "false_preds_equal" (def (quote ¬x⇒¬y⇒x≡yᵇ)      , 2 , 2) $
    noEnv "pred_refl_pos"     (def (quote x⇒x≡xᵇ)          , 1 , 1) $
    noEnv "pred_refl_neg"     (def (quote ¬x⇒x≡xᵇ)         , 1 , 1) $
    noEnv "pred_not_iff_f"    (def (quote ¬f⇔x⇒t≡xᵇ)       , 1 , 1) $
    noEnv "pred_not_iff_f_2"  (def (quote ¬x⇔f⇒x≡tᵇ)       , 1 , 1) $
    noEnv "pred_not_iff_t"    (def (quote ¬t⇔x⇒f≡xᵇ)       , 1 , 1) $
    noEnv "pred_not_iff_t_2"  (def (quote ¬x⇔t⇒x≡fᵇ)       , 1 , 1) $
    noEnv "pred_iff_f"        (def (quote f⇔x⇒f≡xᵇ)        , 1 , 1) $
    noEnv "pred_iff_f_2"      (def (quote x⇔f⇒x≡fᵇ)        , 1 , 1) $
    noEnv "pred_iff_t"        (def (quote t⇔x⇒t≡xᵇ)        , 1 , 1) $
    noEnv "pred_iff_t_2"      (def (quote x⇔t⇒x≡tᵇ)        , 1 , 1) $
    -- atom, bvatom, decl_atom, decl_bvatom
    noEnv "clausify_form"     (def (quote clausi)          , 2 , 2) $
    noEnv "clausify_form_not" (def (quote clausi-¬)        , 2 , 2) $
    noEnv "clausify_false"    (def (quote clausi-f)        , 0 , 1) $
    noEnv "th_let_pf"         (def (quote mp)              , 1 , 2) $
    noEnv "iff_symm"          (def (quote x⇔x)             , 0 , 1) $
    noEnv "contra"            (def (quote contra)          , 1 , 2) $
    noEnv "truth"             (def (quote truth)           , 0 , 0) $
    noEnv "not_not_intro"     (def (quote ¬-¬-intro)       , 1 , 1) $
    noEnv "not_not_elim"      (def (quote ¬-¬-elim)        , 1 , 1) $
    noEnv "or_elim_1"         (def (quote ∨-elimˡ)         , 2 , 2) $
    noEnv "or_elim_2"         (def (quote ∨-elimʳ)         , 2 , 2) $
    noEnv "not_or_elim"       (def (quote de-morgan₁)      , 2 , 1) $
    noEnv "and_elim_1"        (def (quote ∧-elimʳ)         , 2 , 1) $
    noEnv "and_elim_2"        (def (quote ∧-elimˡ)         , 2 , 1) $
    noEnv "not_and_elim"      (def (quote de-morgan₂)      , 2 , 1) $
    noEnv "impl_intro"        (def (quote ⇒-intro)         , 2 , 1) $
    noEnv "impl_elim"         (def (quote ⇒-elim)          , 2 , 1) $
    noEnv "not_impl_elim"     (def (quote ¬-⇒-elim)        , 2 , 1) $
    noEnv "iff_elim_1"        (def (quote ⇔-elim-⇒)        , 2 , 1) $
    noEnv "iff_elim_2"        (def (quote ⇔-elim-⇐)        , 2 , 1) $
    noEnv "not_iff_elim"      (def (quote ¬-⇔-elim)        , 2 , 1) $
    noEnv "xor_elim_1"        (def (quote xor-elim-¬)      , 2 , 1) $
    noEnv "xor_elim_2"        (def (quote xor-elim)        , 2 , 1) $
    noEnv "not_xor_elim"      (def (quote ¬-xor-elim)      , 2 , 1) $
    noEnv "ite_elim_1"        (def (quote ite-elim-then)   , 3 , 1) $
    noEnv "ite_elim_2"        (def (quote ite-elim-else)   , 3 , 1) $
    noEnv "ite_elim_3"        (def (quote ite-elim-both)   , 3 , 1) $
    noEnv "not_ite_elim_1"    (def (quote ¬-ite-elim-then) , 3 , 1) $
    noEnv "not_ite_elim_2"    (def (quote ¬-ite-elim-else) , 3 , 1) $
    noEnv "not_ite_elim_3"    (def (quote ¬-ite-elim-both) , 3 , 1) $
    noEnv "ast"               (def (quote assum)           , 3 , 2) $
    noEnv "asf"               (def (quote assum-¬)         , 3 , 2) $
    -- bv_asf, bv_ast, mpz_sub, mp_ispos, mpz_eq, mpz_lt, mpz_lte

    -- Base
    -- arrow, apply
    noEnv "trust"     (def (quote Base.trust-f)  , 0 , 0) $
    noEnv "trust_f"   (def (quote Base.trust)    , 0 , 1) $
    noEnv "refl"      (def (quote Base.refl)     , 1 , 1) $
    noEnv "symm"      (def (quote Base.sym)      , 3 , 1) $
    noEnv "trans"     (def (quote Base.trans)    , 4 , 2) $
    noEnv "negsymm"   (def (quote Base.¬-sym)    , 3 , 1) $
    noEnv "negtrans1" (def (quote Base.¬-trans₁) , 4 , 2) $
    noEnv "negtrans2" (def (quote Base.¬-trans₂) , 4 , 2) $
    noEnv "cong"      (def (quote Base.cong)     , 6 , 2) $

    end

    where
    withEnv : String → Directions → Map <-STO-Str Directions → Map <-STO-Str Directions
    withEnv = insert <-STO-Str

    noEnv : String → Directions → Map <-STO-Str Directions → Map <-STO-Str Directions
    noEnv s = insert <-STO-Str s ∘ ×-map₁ (_∘ drop 1)

    end = empty <-STO-Str

termFromExpr′ : StateEither Term

visArg : {S : Set} → S → Arg S
visArg = arg (arg-info visible relevant)

envTerm′ : ℕ → Map <-STO-Str Binding → Maybe Term
envTerm′ depth bins =
  case lookup <-STO-Str "env" bins of (λ where
    (just (binding depthᵇ binTyNormal)) → just $ var (depth ∸ depthᵇ) []
    (just (binding _      binTyAtom))   → nothing
    nothing                             → just $ def (quote SAT.ε) [])

envTerm : ℕ → Map <-STO-Str Binding → StateEither Term
envTerm depth bins = do
  ctx ← get↑
  case envTerm′ (ctxDepth ctx) (ctxBins ctx) of λ where
    nothing  → fail↑ [ "LFSC - invalid binding type for 'env'" ]
    (just t) → return t

termFromBin : String → ℕ → Map <-STO-Str Binding → Maybe Term
termFromBin ident depth bins =
  lookup <-STO-Str ident bins >>=ₘ λ where
    (binding depthᵇ binTy) → ((case binTy of λ where
        binTyNormal → just []
        binTyAtom   →
          envTerm′ depth bins >>=ₘ
          λ t → just $ visArg t ∷ visArg (con (quote refl) []) ∷ []) >>=ₘ
      just ∘ var (depth ∸ depthᵇ))

termFromConst : String → ℕ → Map <-STO-Str Binding → Maybe Term
termFromConst ident depth bins = case lookup <-STO-Str ident constMap of λ where
  (just (cons , zero , zero)) → envTerm′ depth bins >>=ₘ λ t → just $ cons [ visArg t ]
  _                           → nothing

termFromIdent : String → StateEither Term
termFromIdent ident = do
  ctx ← get↑
  let depth = ctxDepth ctx
  let bins = ctxBins ctx
  mt ← return $ termFromBin ident depth bins <∣> termFromConst ident depth bins
  case mt of λ where
    nothing  → fail↑ $ "LFSC - unknown identifier '" ∷ ident ∷ "'" ∷ []
    (just t) → return t

stripDot : String → String
stripDot = fromList ∘ go ∘ toListₛ
  where
  go : List Char → List Char
  go ('.' ∷ cs) = cs
  go cs         = cs

skipImplicits : ℕ → StateEither ⊤
skipImplicits zero = return tt
skipImplicits (suc n) = do
  (Ident "_") ← nextToken
    where token → fail↑ $ "LFSC - expected '_', found '" ∷ showToken token ∷ "'" ∷ []
  skipImplicits n

-- XXX - convince the termination checker that ctxInput keeps getting shorter
{-# TERMINATING #-}
buildTerms : List Term → ℕ → StateEither (List Term)
buildTerms ts zero = return $ reverse ts
buildTerms ts (suc n) = do
  token ← nextToken
  case token of λ where
    Open → do
      t ← termFromExpr′
      buildTerms (t ∷ ts) n
    Close → fail↑ [ "LFSC - unexpected end of arguments" ]
    (Ident ident) → do
      t ← termFromIdent ident
      buildTerms (t ∷ ts) n

buildOneTerm : StateEither Term
buildOneTerm = do
  (t ∷ []) ← buildTerms [] 1
    where _ → fail↑ $ [ "LFSC - impossible" ]
  return t

getVariable : StateEither String
getVariable = do
  (Ident ident) ← nextToken
    where token → fail↑ $ "LFSC - expected variable, found '" ∷ showToken token ∷ "'" ∷ []
  return ident

lambdaContext : String → BindingType → StateEither (Lift 0ℓ ⊤)
lambdaContext name binTy =
  modify↑ λ ctx →
    let depth = suc (ctxDepth ctx) in
      record ctx {
          ctxDepth = depth ;
          ctxBins  = insert <-STO-Str name (binding depth binTy) $ ctxBins ctx
        }

handleTypedLambda : StateEither Term
handleTypedLambda = do
  name ← getVariable
  t₁ ← buildOneTerm
  t₂ ← localContext $ do
    lambdaContext name binTyNormal
    modify↑ λ ctx →
        record ctx {
          ctxSig   = t₁ ∷ ctxSig ctx
        }
    buildOneTerm
  return $ lam visible $ abs (stripDot name) t₂

handleLambda : StateEither Term
handleLambda = do
  name ← getVariable
  t ← localContext $ do
    lambdaContext name binTyNormal
    buildOneTerm
  return $ lam visible $ abs (stripDot name) t

handleLet : StateEither Term
handleLet = do
  name ← getVariable
  t₁ ← buildOneTerm
  t₂ ← localContext $ do
    lambdaContext name binTyNormal
    buildOneTerm
  return $ def (quote SMT.bind-let) $
    visArg t₁ ∷
    visArg (pat-lam [
        clause
          [ (stripDot name , visArg unknown) ]
          (visArg (var 0)  ∷ visArg (con (quote refl) []) ∷ [])
          t₂
      ] []) ∷
    []

handleAscribe : StateEither Term
handleAscribe = do
  _ ← buildOneTerm
  t ← buildOneTerm
  return $ def (quote SMT.holdsᶜ-[]-ε) [ visArg t ]

handleDeclAtom : StateEither Term
handleDeclAtom = do
  t₁ ← buildOneTerm
  expectOpen ; expectLambda
  v ← getVariable
  expectOpen ; expectLambda
  a ← getVariable
  t₂ ← buildBindAtom t₁ v a
  expectClose ; expectClose
  return t₂

  where
  expectLambda = nextToken >>= λ where
    (Ident "\\") → return tt
    token        → fail↑ $ "LFSC - expected '\\', found '" ∷ showToken token ∷ "'" ∷ []

  buildBindAtom : Term → String → String → StateEither Term
  buildBindAtom t₁ v a = do
    modify↑ λ ctx → record ctx {
        ctxVarNo = suc $ ctxVarNo ctx
      }
    ctx ← get↑
    env ← envTerm (ctxDepth ctx) (ctxBins ctx)
    t₂ ← localContext $ do
      lambdaContext v binTyNormal
      lambdaContext "env" binTyNormal
      lambdaContext a binTyAtom
      buildOneTerm
    return $ def (quote SMT.bind-atom) $
      visArg (lit (nat (ctxVarNo ctx))) ∷
      visArg t₁ ∷
      visArg env ∷
      visArg (pat-lam [
          clause
            ((stripDot v , visArg unknown) ∷ ("env" , visArg unknown) ∷
              (stripDot a , visArg unknown) ∷ [])
            (visArg (var 2)  ∷ visArg (con (quote refl) []) ∷
              visArg (var 1)  ∷ visArg (con (quote refl) []) ∷
              visArg (var 0) ∷ [])
            t₂
        ] []) ∷
      []

handleArrow : StateEither Term
handleArrow = do
  t₁ ← buildOneTerm
  t₂ ← buildOneTerm
  return $ pi (visArg t₁) (abs "_" t₂)

handleAppl : String → StateEither Term
handleAppl ident = do
  (cons , nImpls , nArgs) ← constLookup ident
  skipImplicits nImpls
  ctx ← get↑
  env ← case envTerm′ (ctxDepth ctx) (ctxBins ctx) of λ where
    nothing  → fail↑ [ "LFSC - invalid binding type for 'env'" ]
    (just t) → return t
  args ← buildTerms [] nArgs
  return $ cons $ mapₗ visArg $ env ∷ args

  where
  constLookup : String → StateEither $ (List (Arg Term) → Term) × ℕ × ℕ
  constLookup ident = case lookup <-STO-Str ident constMap of λ where
    nothing  → fail↑ $ "LFSC - unknown identifier '" ∷ ident ∷ "'" ∷ []
    (just x) → return x

handleBody : StateEither Term
handleBody = do
  (Ident ident) ← nextToken
    where token → fail↑ $ "LFSC - expected identifier, found '" ∷ showToken token ∷ "'" ∷ []
  case ident of λ where
    "%"         → handleTypedLambda
    "\\"        → handleLambda
    "@"         → handleLet
    ":"         → handleAscribe
    "decl_atom" → handleDeclAtom
    "arrow"     → handleArrow
    _           → handleAppl ident

termFromExpr′ = do
  term ← handleBody
  expectClose
  return term

termFromExpr : StateEither Term
termFromExpr = do
  expectOpen
  termFromExpr′

buildType : List Term → StateEither Term
buildType [] = do
  ctx ← get↑
  -- Holdsᶜ []
  return $ def (quote SAT.Holdsᶜ) $
    visArg (def (quote SAT.ε) []) ∷
    visArg (con (quote Data.List.List.[]) []) ∷
    []
buildType (t ∷ ts) =
  -- t → <rest>
  (λ # → pi (visArg t) (abs "_" #)) <$>
  buildType ts

buildProof : StateEither (Term × Term)
buildProof = do
  term ← termFromExpr
  ctx ← get↑
  type ← buildType $ reverse $ ctxSig ctx
  return $ type , term

convertProof : String → Sumₗ 0ℓ (Term × Term)
convertProof input = runState buildProof $ newContext input

macro
  proofType : List String ⊎ (Term × Term) → Term → TC ⊤
  proofType (inj₁ ss)      _    = typeError $ mapₗ strErr ss
  proofType (inj₂ (t , _)) hole = unify hole t

  proofTerm : List String ⊎ (Term × Term) → Term → TC ⊤
  proofTerm (inj₁ ss)      _    = typeError $ mapₗ strErr ss
  proofTerm (inj₂ (_ , t)) hole = unify hole t
