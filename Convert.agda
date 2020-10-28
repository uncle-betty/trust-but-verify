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

open import Reflection
  using (
    Name ; Arg ; Term ;
    def ; con ; var ; pi ; lam ; lit ; nat ; abs ;
    arg ; arg-info ; visible ; hidden ; relevant ; unknown ;
    TC ;
    unify ;
    typeError ; strErr
  )

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; does ; _because_ ; ofʸ ; ofⁿ)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation using (¬?)

import Env
import SAT
import SMT
import Base

record Context : Set where
  field
    ctxEnvName : Name
    -- ^ name of the variable to hold the evaluation environment
    ctxInput   : List Char
    -- ^ input LFSC proof
    ctxVarNo   : ℕ
    -- ^ numbers the variables that hold atoms
    ctxDepth   : ℕ
    -- ^ current nesting depth of λ-abstractions (use: de Bruin indexes)
    ctxArgs    : Map <-STO-Str ℕ
    -- ^ λ-bound variables and the nesting depth of their λ-abstractions (use: de Bruin indexes)
    ctxLets    : Map <-STO-Str Term
    -- ^ let-bound variables and their bound terms; we don't transliterate let-bindings, but
    -- ^ instead replace occurrences of let-bound variables with their bound terms
    ctxSig     : List Term
    -- ^ types of the top-level λ-bindings (use: proof term's type signature)
    ctxEnv     : Map <-STO-ℕ Term
    -- ^ variables and the associated atoms (use: implement decl_atom, evaluation environment)

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

newContext : Name → String → Context
newContext envName input = record {
    ctxEnvName = envName ;
    ctxInput   = toListₛ input ;
    ctxVarNo   = 0 ;
    ctxDepth   = 0 ;
    ctxArgs    = empty <-STO-Str ;
    ctxLets    = empty <-STO-Str ;
    ctxSig     = [] ;
    ctxEnv     = empty <-STO-ℕ
  }

localContext : {S : Set} → StateEither S → StateEither S
localContext toWrap = do
  saved ← get↑
  result ← toWrap
  modify↑ λ ctx → record saved {
      ctxInput = ctxInput ctx ;
      ctxVarNo = ctxVarNo ctx ;
      ctxSig   = ctxSig ctx ;
      ctxEnv   = ctxEnv ctx
    }
  return result

visibleArg : Term → Arg Term
visibleArg = arg (arg-info visible relevant)

hiddenArg : Term → Arg Term
hiddenArg = arg (arg-info hidden relevant)

unknownArg : Arg Term
unknownArg = arg (arg-info hidden relevant) unknown

module _ where
  open SAT
  open SMT
  open SMT.Rules

  pass₁ : ∀ {ℓ} → {S : Set ℓ} → S → S
  pass₁ x = x

  pass₂ : ∀ {ℓ₁ ℓ₂} → {S₁ : Set ℓ₁} → {S₂ : Set ℓ₂} → S₁ → S₂ → S₂
  pass₂ _ x = x

  Directions = (List (Arg Term) → Term) × ℕ × ℕ

  constMap : Map <-STO-Str Directions
  constMap =
    -- pass the last argument through
    noEnv "check" (def (quote pass₁) , 0 , 1) $
    noEnv ":"     (def (quote pass₂) , 0 , 2) $
    noEnv "term"  (def (quote pass₁) , 0 , 1) $

    -- built-ins
    noEnv "Bool" (def (quote Data.Bool.Bool)     , 0 , 0) $
    noEnv "cln"  (con (quote Data.List.List.[])  , 0 , 0) $
    noEnv "clc"  (con (quote Data.List.List._∷_) , 0 , 2) $
    noEnv "cnfn" (con (quote Data.List.List.[])  , 0 , 0) $
    noEnv "cnfc" (con (quote Data.List.List._∷_) , 0 , 2) $

    -- SAT - with leading (visible!) env argument
      -- bool, tt, ff, var, lit
    withEnv "pos"             (con (quote pos)        , 0 , 1) $
    withEnv "neg"             (con (quote neg)        , 0 , 1) $
      -- lit_flip, clause, concat_cl, clr, clause_append, simplify_clause
    withEnv "holds"           (def (quote Holdsᶜ)     , 0 , 1) $
    withEnv "R"               (def (quote resolve-r⁺) , 2 , 3) $
    withEnv "Q"               (def (quote resolve-q⁺) , 2 , 3) $
    withEnv "satlem_simplify" (def (quote mp⁺)        , 3 , 2) $
    withEnv "satlem"          (def (quote mpᶜ)        , 2 , 2) $
      -- clause_dedup, cnf_holds, cnfn_proof, cnfc_proof

    -- SMT - no leading env argument
      -- formula
    noEnv "th_holds" (def (quote Holds)  , 0 , 1) $
    noEnv "true"     (con (quote trueᶠ)  , 0 , 0) $
    noEnv "false"    (con (quote falseᶠ) , 0 , 0) $
      -- formula_op1, formula_op2, formula_op3
    noEnv "not"      (con (quote notᶠ)   , 0 , 1) $
    noEnv "and"      (con (quote andᶠ)   , 0 , 2) $
    noEnv "or"       (con (quote orᶠ)    , 0 , 2) $
    noEnv "impl"     (con (quote implᶠ)  , 0 , 2) $
    noEnv "iff"      (con (quote iffᶠ)   , 0 , 2) $
    noEnv "xor"      (con (quote xorᶠ)   , 0 , 2) $
    noEnv "ifte"     (con (quote iteᶠ)   , 0 , 3) $
      -- sort, term
    noEnv "="        (con (quote equᶠ)   , 1 , 2) $
      -- ite, let, flet, Bool
    noEnv "p_app"    (con (quote appᵇ)   , 0 , 1) $
      -- t_true, t_false

    -- SMT.Rules - with leading (visible!) env argument
    withEnv "t_t_neq_f"         (def (quote t≢fᵇ)            , 0 , 0) $
    withEnv "pred_eq_t"         (def (quote x⇒x≡tᵇ)          , 1 , 2) $
    withEnv "pred_eq_f"         (def (quote ¬x⇒x≡fᵇ)         , 1 , 2) $
      -- f_to_b
    withEnv "true_preds_equal"  (def (quote x⇒y⇒x≡yᵇ)        , 2 , 2) $
    withEnv "false_preds_equal" (def (quote ¬x⇒¬y⇒x≡yᵇ)      , 2 , 2) $
    withEnv "pred_refl_pos"     (def (quote x⇒x≡xᵇ)          , 1 , 1) $
    withEnv "pred_refl_neg"     (def (quote ¬x⇒x≡xᵇ)         , 1 , 1) $
    withEnv "pred_not_iff_f"    (def (quote ¬f⇔x⇒t≡xᵇ)       , 1 , 1) $
    withEnv "pred_not_iff_f_2"  (def (quote ¬x⇔f⇒x≡tᵇ)       , 1 , 1) $
    withEnv "pred_not_iff_t"    (def (quote ¬t⇔x⇒f≡xᵇ)       , 1 , 1) $
    withEnv "pred_not_iff_t_2"  (def (quote ¬x⇔t⇒x≡fᵇ)       , 1 , 1) $
    withEnv "pred_iff_f"        (def (quote f⇔x⇒f≡xᵇ)        , 1 , 1) $
    withEnv "pred_iff_f_2"      (def (quote x⇔f⇒x≡fᵇ)        , 1 , 1) $
    withEnv "pred_iff_t"        (def (quote t⇔x⇒t≡xᵇ)        , 1 , 1) $
    withEnv "pred_iff_t_2"      (def (quote x⇔t⇒x≡tᵇ)        , 1 , 1) $
      -- atom, bvatom, decl_atom, decl_bvatom
    withEnv "clausify_form"     (def (quote clausi)          , 2 , 2) $
    withEnv "clausify_form_not" (def (quote clausi-¬)        , 2 , 2) $
    withEnv "clausify_false"    (def (quote clausi-f)        , 0 , 1) $
    withEnv "th_let_pf"         (def (quote mp)              , 1 , 2) $
    withEnv "iff_symm"          (def (quote x⇔x)             , 0 , 1) $
    withEnv "contra"            (def (quote contra)          , 1 , 2) $
    withEnv "truth"             (def (quote truth)           , 0 , 0) $
    withEnv "not_not_intro"     (def (quote ¬-¬-intro)       , 1 , 1) $
    withEnv "not_not_elim"      (def (quote ¬-¬-elim)        , 1 , 1) $
    withEnv "or_elim_1"         (def (quote ∨-elimˡ)         , 2 , 2) $
    withEnv "or_elim_2"         (def (quote ∨-elimʳ)         , 2 , 2) $
    withEnv "not_or_elim"       (def (quote de-morgan₁)      , 2 , 1) $
    withEnv "and_elim_1"        (def (quote ∧-elimʳ)         , 2 , 1) $
    withEnv "and_elim_2"        (def (quote ∧-elimˡ)         , 2 , 1) $
    withEnv "not_and_elim"      (def (quote de-morgan₂)      , 2 , 1) $
    withEnv "impl_intro"        (def (quote ⇒-intro)         , 2 , 1) $
    withEnv "impl_elim"         (def (quote ⇒-elim)          , 2 , 1) $
    withEnv "not_impl_elim"     (def (quote ¬-⇒-elim)        , 2 , 1) $
    withEnv "iff_elim_1"        (def (quote ⇔-elim-⇒)        , 2 , 1) $
    withEnv "iff_elim_2"        (def (quote ⇔-elim-⇐)        , 2 , 1) $
    withEnv "not_iff_elim"      (def (quote ¬-⇔-elim)        , 2 , 1) $
    withEnv "xor_elim_1"        (def (quote xor-elim-¬)      , 2 , 1) $
    withEnv "xor_elim_2"        (def (quote xor-elim)        , 2 , 1) $
    withEnv "not_xor_elim"      (def (quote ¬-xor-elim)      , 2 , 1) $
    withEnv "ite_elim_1"        (def (quote ite-elim-then)   , 3 , 1) $
    withEnv "ite_elim_2"        (def (quote ite-elim-else)   , 3 , 1) $
    withEnv "ite_elim_3"        (def (quote ite-elim-both)   , 3 , 1) $
    withEnv "not_ite_elim_1"    (def (quote ¬-ite-elim-then) , 3 , 1) $
    withEnv "not_ite_elim_2"    (def (quote ¬-ite-elim-else) , 3 , 1) $
    withEnv "not_ite_elim_3"    (def (quote ¬-ite-elim-both) , 3 , 1) $
    withEnv "ast"               (def (quote assum)           , 3 , 2) $
    withEnv "asf"               (def (quote assum-¬)         , 3 , 2) $
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

    end

    where
    withEnv : String → Directions → Map <-STO-Str Directions → Map <-STO-Str Directions
    withEnv = insert <-STO-Str

    noEnv : String → Directions → Map <-STO-Str Directions → Map <-STO-Str Directions
    noEnv s (f , n₁ , n₂) m = insert <-STO-Str s (f ∘ drop 1 , n₁ , n₂) m

    end = empty <-STO-Str

termFromExpr′ : StateEither Term

visibleEnvArg : StateEither (Arg Term)
visibleEnvArg = do
  ctx ← get↑
  return $ visibleArg (def (ctxEnvName ctx) [])

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

termFromConst : String → Arg Term → Maybe Term
termFromConst ident envArg = case lookup <-STO-Str ident constMap of λ where
  (just (cons , zero , zero)) → just (cons [ envArg ])
  _                           → nothing

termFromIdent : String → StateEither Term
termFromIdent ident = do
  ctx ← get↑
  envArg ← visibleEnvArg
  mt ← return $
    (termFromArg ident (ctxDepth ctx) (ctxArgs ctx) <∣>
    termFromLet ident (ctxLets ctx)) <∣>
    termFromConst ident envArg
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

handleTypedLambda : StateEither Term
handleTypedLambda = do
  name ← getVariable
  t₁ ← buildOneTerm
  t₂ ← localContext $ do
    modify↑ λ ctx →
      let depth = suc (ctxDepth ctx) in
        record ctx {
          ctxDepth = depth ;
          ctxArgs  = insert <-STO-Str name depth $ ctxArgs ctx ;
          ctxSig   = t₁ ∷ ctxSig ctx
        }
    buildOneTerm
  return $ lam visible $ abs (stripDot name) t₂

handleLambda : StateEither Term
handleLambda = do
  name ← getVariable
  t ← localContext $ do
    modify↑ λ ctx →
      let depth = suc (ctxDepth ctx) in
        record ctx {
          ctxDepth = depth ;
          ctxArgs  = insert <-STO-Str name depth $ ctxArgs ctx
        }
    buildOneTerm
  return $ lam visible $ abs (stripDot name) t

handleLet : StateEither Term
handleLet = do
  name ← getVariable
  t₁ ← localContext $ do
    -- don't allow access to previous arguments; at lookup time we might be at a more deeply
    -- nested level within t₂, i.e, their de Bruijn indices might be outdated
    modify↑ λ ctx → record ctx {
        ctxArgs = empty <-STO-Str
      }
    buildOneTerm
  t₂ ← localContext $ do
    modify↑ λ ctx → record ctx {
        ctxLets = insert <-STO-Str name t₁ $ ctxLets ctx
      }
    buildOneTerm
  return t₂

handleDeclAtom : StateEither Term
handleDeclAtom = do
  t₁ ← buildOneTerm
  expectOpen ; expectLambda
  v ← getVariable
  expectOpen ; expectLambda
  a ← getVariable
  t₂ ← localContext $ prepareContext t₁ v a >> buildOneTerm
  expectClose ; expectClose
  return t₂

  where
  expectLambda = nextToken >>= λ where
    (Ident "\\") → return tt
    token        → fail↑ $ "LFSC - expected '\\', found '" ∷ showToken token ∷ "'" ∷ []

  prepareContext : Term → String → String → StateEither (Lift 0ℓ ⊤)
  prepareContext t₁ v a = modify↑ λ ctx →
    let
      varNo = suc (ctxVarNo ctx)
      -- var <varNo>
      vVal = con (quote Env.Var.var) $
        visibleArg (lit (nat varNo)) ∷
        []
      -- atom {<envName>} (var <varNo>) t₁ (refl {_} {_} {_})
      aVal = con (quote SMT.Rules.Atom.atom) $
        hiddenArg (def (ctxEnvName ctx) []) ∷
        visibleArg vVal ∷
        visibleArg t₁ ∷
        visibleArg (con (quote Relation.Binary.PropositionalEquality._≡_.refl) $
          hiddenArg unknown ∷
          hiddenArg unknown ∷
          hiddenArg unknown ∷
          []) ∷
        []
    in
      record ctx {
          ctxVarNo = varNo ;
          ctxLets =
            insert <-STO-Str v vVal $
            insert <-STO-Str a aVal $
            ctxLets ctx ;
          ctxEnv = insert <-STO-ℕ varNo t₁ $ ctxEnv ctx
        }

handleAppl : String → StateEither Term
handleAppl ident = do
  (cons , nImpls , nArgs) ← constLookup ident
  skipImplicits nImpls
  envArg ← visibleEnvArg
  args ← buildTerms [] nArgs
  return $ cons $ envArg ∷ mapₗ (arg $ arg-info visible relevant) args

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

buildEnv : List (ℕ × Term) → StateEither Term
buildEnv [] =
  -- ε {0ℓ} {Bool}
  return $ def (quote Env.ε) $
    hiddenArg (def (quote Level.zero) []) ∷
    hiddenArg (def (quote Data.Bool.Bool) []) ∷
    []
buildEnv ((n , t) ∷ nts) =
  -- assignᵛ (var <n>) (eval <t>) <rest>
  (λ # → def (quote Env.assignᵛ) $
    visibleArg (con (quote Env.Var.var) $
      visibleArg (lit (nat n)) ∷
      []) ∷
    visibleArg (def (quote SMT.eval) $
      visibleArg t ∷
      []) ∷
    visibleArg # ∷
    []) <$> buildEnv nts

buildType : List Term → StateEither Term
buildType [] = do
  ctx ← get↑
  -- Holdsᶜ <envName> []
  return $ def (quote SAT.Holdsᶜ) $
    visibleArg (def (ctxEnvName ctx) []) ∷
    visibleArg (con (quote Data.List.List.[]) $
      hiddenArg unknown ∷
      hiddenArg unknown ∷
      []) ∷
    []
buildType (t ∷ ts) =
  -- t → <rest>
  (λ # → pi (visibleArg t) (abs "_" #)) <$>
  buildType ts

buildProof : StateEither (Term × Term × Term)
buildProof = do
  term ← termFromExpr
  ctx ← get↑
  type ← buildType $ reverse $ ctxSig ctx
  env ← buildEnv $ toListₘ <-STO-ℕ $ ctxEnv ctx
  return $ env , type , term

convertProof : Name → String → Sumₗ 0ℓ (Term × Term × Term)
convertProof envName input = runState buildProof $ newContext envName input

macro
  proofEnv : List String ⊎ (Term × Term × Term) → Term → TC ⊤
  proofEnv (inj₁ ss)          _    = typeError $ mapₗ strErr ss
  proofEnv (inj₂ (t , _ , _)) hole = unify hole t

  proofType : List String ⊎ (Term × Term × Term) → Term → TC ⊤
  proofType (inj₁ ss)          _    = typeError $ mapₗ strErr ss
  proofType (inj₂ (_ , t , _)) hole = unify hole t

  proofTerm : List String ⊎ (Term × Term × Term) → Term → TC ⊤
  proofTerm (inj₁ ss)          _    = typeError $ mapₗ strErr ss
  proofTerm (inj₂ (_ , _ , t)) hole = unify hole t

module Test where
  open Env renaming (var to var′)
  open SAT
  open SMT
  open SMT.Rules

  testEnv : Env

  test : String → List String ⊎ Term
  test s = runState termFromExpr $ newContext (quote testEnv) s

  test′ : String → List String ⊎ (Term × Term)
  test′ s = ⊎-map₂ (λ { (_ , type , term) → type , term }) $ convertProof (quote testEnv) s

  test″ : String → List String ⊎ (Term × Term × Term)
  test″ = convertProof (quote testEnv)

  expTest₁ : test "(true)" ≡ (inj₂ $ quoteTerm trueᶠ)
  expTest₁ = refl

  expTest₂ : test "(and true false)" ≡ (inj₂ $ quoteTerm (andᶠ trueᶠ falseᶠ))
  expTest₂ = refl

  lamTest₁ : {S : Set} → test "(\\ .x .x)" ≡ (inj₂ $ quoteTerm λ (x : S) → x)
  lamTest₁ = refl

  lamTest₂ : {S : Set} → test "(\\ .x (\\ .y .x))" ≡ (inj₂ $ quoteTerm λ (x : S) (y : S) → x)
  lamTest₂ = refl

  lamTest₃ : test "(% .x (th_holds true) .x)" ≡ (inj₂ $ quoteTerm λ (x : Bool) → x)
  lamTest₃ = refl

  lamTest₄ : {S : Set} →
    test′ "(% .x (th_holds true) .x)" ≡
    (inj₂ $ (quoteTerm (Holds trueᶠ → Holdsᶜ testEnv []) , quoteTerm λ (x : S) → x))
  lamTest₄ = refl

  lamTest₅ : {S : Set} →
    test′ "(% .x (th_holds true) (% .y (th_holds false) .x))" ≡
    (inj₂ $ quoteTerm (Holds trueᶠ → Holds falseᶠ → Holdsᶜ testEnv []) ,
      quoteTerm λ (x : S) (y : S) → x)
  lamTest₅ = refl

  letTest₁ : test "(\\ .x (@ a .x))" ≡ inj₁ _
  letTest₁ = refl

  letTest₂ : test "(@ a true a)" ≡ (inj₂ $ quoteTerm trueᶠ)
  letTest₂ = refl

  letTest₃ : test "(@ a true (@ b false a))" ≡ (inj₂ $ quoteTerm trueᶠ)
  letTest₃ = refl

  mixTest₁ : test "(@ a true (\\ .x (and .x a)))" ≡ (inj₂ $ quoteTerm λ x → andᶠ x trueᶠ)
  mixTest₁ = refl

  mixTest₂ : test "(\\ .x (@ a true (and .x a)))" ≡ (inj₂ $ quoteTerm λ x → andᶠ x trueᶠ)
  mixTest₂ = refl

  atomTest₁ : test "(decl_atom true (\\ .x (\\ .y .x)))" ≡ (inj₂ $ quoteTerm (var′ 1))
  atomTest₁ = refl

  testEnv =
    assignᵛ (var′ 1) (eval trueᶠ) $
    ε

  {- XXX - test broken; {testEnv} is quoted into {_} for some reason
  atomTest₂ :
    test "(decl_atom true (\\ .x (\\ .y .y)))" ≡
    (inj₂ $ quoteTerm (atom {testEnv} (var′ 1) trueᶠ refl))
  atomTest₂ = {!!}
  -}

  atomTest₃ : {S : Set} →
    test″ "(% .x (th_holds true) (decl_atom true (\\ .y (\\ .z .y))))" ≡
    (inj₂ $
      (quoteTerm (assignᵛ (var′ 1) (eval trueᶠ) ε) ,
      quoteTerm (Holds trueᶠ → Holdsᶜ testEnv []) ,
      quoteTerm (λ (x : S) → var′ 1)))
  atomTest₃ = refl
