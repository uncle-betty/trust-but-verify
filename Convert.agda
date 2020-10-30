module Convert where

open import Level using (0ℓ ; Lift)

open import Category.Monad using (RawMonad)
open import Category.Monad.State using (StateMonad ; State ; RawMonadState ; StateMonadState)

open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char) renaming (_≟_ to _≟-char_)
open import Data.Empty using (⊥)

open import Data.List
  using (List ; [] ; _∷_ ; [_] ; reverse ; drop ; dropWhile ; span) renaming (map to mapₗ)

open import Data.Maybe using (Maybe ; just ; nothing ; _<∣>_) renaming (map to mapₘ)
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

record Context : Set where
  field
    ctxInput   : List Char
    -- ^ input LFSC proof
    ctxVarNo   : ℕ
    -- ^ numbers the variables that hold atoms
    ctxDepth   : ℕ
    -- ^ current nesting depth of λ-abstractions (use: de Bruin indexes)
    ctxArgs    : Map <-STO-Str ℕ
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
    ctxArgs    = empty <-STO-Str ;
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

  pass₂ : ∀ {ℓ₁ ℓ₂} → {S₁ : Set ℓ₁} → {S₂ : Set ℓ₂} → S₁ → S₂ → S₂
  pass₂ _ x = x

  Directions = (List (Arg Term) → Term) × ℕ × ℕ

  constMap : Map <-STO-Str Directions
  constMap =
    -- pass the last argument through
    entry "check" (def (quote pass₁) , 0 , 1) $
    entry ":"     (def (quote pass₂) , 0 , 2) $
    entry "term"  (def (quote pass₁) , 0 , 1) $

    -- built-ins
    entry "Bool" (def (quote Data.Bool.Bool)     , 0 , 0) $
    entry "cln"  (con (quote Data.List.List.[])  , 0 , 0) $
    entry "clc"  (con (quote Data.List.List._∷_) , 0 , 2) $
    entry "cnfn" (con (quote Data.List.List.[])  , 0 , 0) $
    entry "cnfc" (con (quote Data.List.List._∷_) , 0 , 2) $

    -- SAT - with leading (visible!) env argument
    -- bool, tt, ff, var, lit
    entry "pos"             (con (quote pos)        , 0 , 1) $
    entry "neg"             (con (quote neg)        , 0 , 1) $
    -- lit_flip, clause, concat_cl, clr, clause_append, simplify_clause
    entry "holds"           (def (quote Holdsᶜ)     , 0 , 1) $
    entry "R"               (def (quote resolve-r⁺) , 2 , 3) $
    entry "Q"               (def (quote resolve-q⁺) , 2 , 3) $
    entry "satlem_simplify" (def (quote mp⁺)        , 3 , 2) $
    entry "satlem"          (def (quote mpᶜ)        , 2 , 2) $
    -- clause_dedup, cnf_holds, cnfn_proof, cnfc_proof

    -- SMT - no leading env argument
    -- formula
    entry "th_holds" (def (quote Holds)  , 0 , 1) $
    entry "true"     (con (quote trueᶠ)  , 0 , 0) $
    entry "false"    (con (quote falseᶠ) , 0 , 0) $
    -- formula_op1, formula_op2, formula_op3
    entry "not"      (con (quote notᶠ)   , 0 , 1) $
    entry "and"      (con (quote andᶠ)   , 0 , 2) $
    entry "or"       (con (quote orᶠ)    , 0 , 2) $
    entry "impl"     (con (quote implᶠ)  , 0 , 2) $
    entry "iff"      (con (quote iffᶠ)   , 0 , 2) $
    entry "xor"      (con (quote xorᶠ)   , 0 , 2) $
    entry "ifte"     (con (quote iteᶠ)   , 0 , 3) $
    -- sort, term
    entry "="        (con (quote equᶠ)   , 1 , 2) $
    -- ite, let, flet, Bool
    entry "p_app"    (con (quote appᵇ)   , 0 , 1) $
    -- t_true, t_false

    -- SMT.Rules - with leading (visible!) env argument
    entry "t_t_neq_f"         (def (quote t≢fᵇ)            , 0 , 0) $
    entry "pred_eq_t"         (def (quote x⇒x≡tᵇ)          , 1 , 2) $
    entry "pred_eq_f"         (def (quote ¬x⇒x≡fᵇ)         , 1 , 2) $
    -- f_to_b
    entry "true_preds_equal"  (def (quote x⇒y⇒x≡yᵇ)        , 2 , 2) $
    entry "false_preds_equal" (def (quote ¬x⇒¬y⇒x≡yᵇ)      , 2 , 2) $
    entry "pred_refl_pos"     (def (quote x⇒x≡xᵇ)          , 1 , 1) $
    entry "pred_refl_neg"     (def (quote ¬x⇒x≡xᵇ)         , 1 , 1) $
    entry "pred_not_iff_f"    (def (quote ¬f⇔x⇒t≡xᵇ)       , 1 , 1) $
    entry "pred_not_iff_f_2"  (def (quote ¬x⇔f⇒x≡tᵇ)       , 1 , 1) $
    entry "pred_not_iff_t"    (def (quote ¬t⇔x⇒f≡xᵇ)       , 1 , 1) $
    entry "pred_not_iff_t_2"  (def (quote ¬x⇔t⇒x≡fᵇ)       , 1 , 1) $
    entry "pred_iff_f"        (def (quote f⇔x⇒f≡xᵇ)        , 1 , 1) $
    entry "pred_iff_f_2"      (def (quote x⇔f⇒x≡fᵇ)        , 1 , 1) $
    entry "pred_iff_t"        (def (quote t⇔x⇒t≡xᵇ)        , 1 , 1) $
    entry "pred_iff_t_2"      (def (quote x⇔t⇒x≡tᵇ)        , 1 , 1) $
    -- atom, bvatom, decl_atom, decl_bvatom
    entry "clausify_form"     (def (quote clausi)          , 2 , 2) $
    entry "clausify_form_not" (def (quote clausi-¬)        , 2 , 2) $
    entry "clausify_false"    (def (quote clausi-f)        , 0 , 1) $
    entry "th_let_pf"         (def (quote mp)              , 1 , 2) $
    entry "iff_symm"          (def (quote x⇔x)             , 0 , 1) $
    entry "contra"            (def (quote contra)          , 1 , 2) $
    entry "truth"             (def (quote truth)           , 0 , 0) $
    entry "not_not_intro"     (def (quote ¬-¬-intro)       , 1 , 1) $
    entry "not_not_elim"      (def (quote ¬-¬-elim)        , 1 , 1) $
    entry "or_elim_1"         (def (quote ∨-elimˡ)         , 2 , 2) $
    entry "or_elim_2"         (def (quote ∨-elimʳ)         , 2 , 2) $
    entry "not_or_elim"       (def (quote de-morgan₁)      , 2 , 1) $
    entry "and_elim_1"        (def (quote ∧-elimʳ)         , 2 , 1) $
    entry "and_elim_2"        (def (quote ∧-elimˡ)         , 2 , 1) $
    entry "not_and_elim"      (def (quote de-morgan₂)      , 2 , 1) $
    entry "impl_intro"        (def (quote ⇒-intro)         , 2 , 1) $
    entry "impl_elim"         (def (quote ⇒-elim)          , 2 , 1) $
    entry "not_impl_elim"     (def (quote ¬-⇒-elim)        , 2 , 1) $
    entry "iff_elim_1"        (def (quote ⇔-elim-⇒)        , 2 , 1) $
    entry "iff_elim_2"        (def (quote ⇔-elim-⇐)        , 2 , 1) $
    entry "not_iff_elim"      (def (quote ¬-⇔-elim)        , 2 , 1) $
    entry "xor_elim_1"        (def (quote xor-elim-¬)      , 2 , 1) $
    entry "xor_elim_2"        (def (quote xor-elim)        , 2 , 1) $
    entry "not_xor_elim"      (def (quote ¬-xor-elim)      , 2 , 1) $
    entry "ite_elim_1"        (def (quote ite-elim-then)   , 3 , 1) $
    entry "ite_elim_2"        (def (quote ite-elim-else)   , 3 , 1) $
    entry "ite_elim_3"        (def (quote ite-elim-both)   , 3 , 1) $
    entry "not_ite_elim_1"    (def (quote ¬-ite-elim-then) , 3 , 1) $
    entry "not_ite_elim_2"    (def (quote ¬-ite-elim-else) , 3 , 1) $
    entry "not_ite_elim_3"    (def (quote ¬-ite-elim-both) , 3 , 1) $
    entry "ast"               (def (quote assum)           , 3 , 2) $
    entry "asf"               (def (quote assum-¬)         , 3 , 2) $
    -- bv_asf, bv_ast, mpz_sub, mp_ispos, mpz_eq, mpz_lt, mpz_lte

    -- Base
    -- arrow, apply
    entry "trust"     (def (quote Base.trust-f)  , 0 , 0) $
    entry "trust_f"   (def (quote Base.trust)    , 0 , 1) $
    entry "refl"      (def (quote Base.refl)     , 1 , 1) $
    entry "symm"      (def (quote Base.sym)      , 3 , 1) $
    entry "trans"     (def (quote Base.trans)    , 4 , 2) $
    entry "negsymm"   (def (quote Base.¬-sym)    , 3 , 1) $
    entry "negtrans1" (def (quote Base.¬-trans₁) , 4 , 2) $
    entry "negtrans2" (def (quote Base.¬-trans₂) , 4 , 2) $
    -- XXX - figure out cong

    end

    where
    entry : String → Directions → Map <-STO-Str Directions → Map <-STO-Str Directions
    entry = insert <-STO-Str

    end = empty <-STO-Str

termFromExpr′ : StateEither Term

constLookup : String → StateEither $ (List (Arg Term) → Term) × ℕ × ℕ
constLookup ident = case lookup <-STO-Str ident constMap of λ where
  nothing  → fail↑ $ "LFSC - unknown identifier '" ∷ ident ∷ "'" ∷ []
  (just x) → return x

termFromArg : String → ℕ → Map <-STO-Str ℕ → Maybe Term
termFromArg ident depth args =
  mapₘ (λ x → var (depth ∸ x) []) $
  lookup <-STO-Str ident args

termFromLet : String → Map <-STO-Str Term → Maybe Term
termFromLet ident lets = lookup <-STO-Str ident lets

termFromConst : String → Maybe Term
termFromConst ident = case lookup <-STO-Str ident constMap of λ where
  (just (cons , zero , zero)) → just (cons [])
  _                           → nothing

termFromIdent : String → StateEither Term
termFromIdent ident = do
  ctx ← get↑
  mt ← return $ termFromArg ident (ctxDepth ctx) (ctxArgs ctx) <∣> termFromConst ident
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

visArg : {S : Set} → S → Arg S
visArg = arg (arg-info visible relevant)

lambdaContext : String → StateEither (Lift 0ℓ ⊤)
lambdaContext name =
  modify↑ λ ctx →
    let depth = suc (ctxDepth ctx) in
      record ctx {
          ctxDepth = depth ;
          ctxArgs  = insert <-STO-Str name depth $ ctxArgs ctx
        }

handleTypedLambda : StateEither Term
handleTypedLambda = do
  name ← getVariable
  t₁ ← buildOneTerm
  t₂ ← localContext $ do
    lambdaContext name
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
    lambdaContext name
    buildOneTerm
  return $ lam visible $ abs (stripDot name) t

handleLet : StateEither Term
handleLet = do
  name ← getVariable
  t₁ ← buildOneTerm
  t₂ ← localContext $ do
    lambdaContext name
    buildOneTerm
  return $ def (quote SMT.bind-let) $
    visArg t₁ ∷
    visArg (pat-lam [
        clause
          [ (name , visArg unknown) ]
          (visArg (var 0)  ∷ visArg (con (quote refl) []) ∷ [])
          t₂
      ] []) ∷
    []

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
    t₂ ← localContext $ do
      lambdaContext v
      lambdaContext a
      buildOneTerm
    ctx ← get↑
    return $ def (quote SMT.bind-atom) $
      visArg (lit (nat (ctxVarNo ctx))) ∷
      visArg t₁ ∷
      visArg (pat-lam [
          clause
            ((v , visArg unknown) ∷ (a , visArg unknown) ∷ [])
            (visArg (var 1)  ∷ visArg (con (quote refl) []) ∷ visArg (var 0) ∷ [])
            t₂
        ] []) ∷
      []

handleAppl : String → StateEither Term
handleAppl ident = do
  (cons , nImpls , nArgs) ← constLookup ident
  skipImplicits nImpls
  args ← buildTerms [] nArgs
  return $ cons $ mapₗ (arg $ arg-info visible relevant) args

handleBody : StateEither Term
handleBody = do
  (Ident ident) ← nextToken
    where token → fail↑ $ "LFSC - expected identifier, found '" ∷ showToken token ∷ "'" ∷ []
  case ident of λ where
    "%"         → handleTypedLambda
    "\\"        → handleLambda
    "@"         → handleLet
    "decl_atom" → handleDeclAtom
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
  -- Holdsᶜ <envName> []
  return $ def (quote SAT.Holdsᶜ) $
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
