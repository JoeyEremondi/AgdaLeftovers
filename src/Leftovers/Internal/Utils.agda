{-# OPTIONS --without-K #-}
module Leftovers.Internal.Utils where

open import Data.String using (String)
open import Data.List as List

open import Reflection
open import Reflection.Term
open import Reflection.Pattern as P
open import Reflection.Argument as A
import Agda.Builtin.Reflection
open Agda.Builtin.Reflection using (Visibility ; Modality ; Relevance ; Quantity ; modality ; quantity-ω ; relevant)
-- open import Reflection.TypeChecking.Monad.Instances
open import Data.Nat
open import Data.Product
open import Data.Unit

open import Function using (_$_; case_of_) public

import Data.List.Categorical
open import Level


freshMeta : Type → TC Term
freshMeta = newMeta
-- freshMeta t = do
--   theMeta ← newMeta t
--   debugPrint "Leftovers" 2 (strErr "Fresh meta " ∷ termErr theMeta ∷ strErr " with type " ∷ termErr t ∷ [])
--   ctx ← getContext
--   getMeta theMeta
--   -- logHole (mkHole m theMeta ctx)
--   return theMeta
--   where
--     getMeta : Term → TC Meta
--     getMeta (meta m _ ) = return m
--     getMeta t =  (typeError (strErr "GetMeta returned invlaid meta " ∷ termErr t ∷  []))

-- case_of_ : ∀ {A B : Set} → A → (A → B) → B
-- case x of f = f x

λv_↦_  λh_↦_ : String → Term → Term
λv x ↦ body  = lam visible (abs x body)
λh x ↦ body  = lam hidden (abs x body)

identity : ∀ {ℓ} { X : Set ℓ} → X → X
identity x = x


the : ∀ {ℓ} → (T : Set ℓ) → T → T
the _ = identity

_⦂_ : Term → Type → Term
t ⦂ T = def (quote the) (vArg T ∷ vArg t ∷ [])

extendClause : String → Visibility →  Clause → Clause
extendClause argNm v (clause tel ps t) =
  clause ((argNm , arg info unknown) ∷ tel) (arg info (var 0) ∷ ps) t
  where
    info = (arg-info v (modality relevant quantity-ω))
extendClause argNm v (absurd-clause tel ps) = absurd-clause ((argNm , arg info unknown) ∷ tel) (arg info (var 0) ∷ ps)
  where
    info = (arg-info v (modality relevant quantity-ω))

clauses : Term → List Clause
clauses (pat-lam clauses types) = clauses
clauses (lam vis (abs argNm body))
  with subClauses ← clauses body = List.map (extendClause argNm vis) subClauses
clauses t = [ clause [] [] t ]

happ : Term → Term → Term
happ f x = def (quote doHapp) (vArg f ∷ hArg x ∷ [])
  where
    doHapp : ∀ {ℓ1 ℓ2} {X : Set ℓ1} {Y : Set ℓ2} -> ({X} → Y) → {x : X} → Y
    doHapp f {x = x} = f {x}

iapp : Term → Term → Term
iapp f x = def (quote doIapp) (vArg f ∷ hArg x ∷ [])
  where
    doIapp : ∀ {ℓ1 ℓ2} {X : Set ℓ1} {Y : Set ℓ2} -> ({{_ : X}} → Y) → {{x : X}} → Y
    doIapp f {{x}} = f {{x}}

app : Term → Term → Term
app f x = def (quote _$_) (vArg f ∷ vArg x ∷ [])

genericApp : Term → Arg Term → Term
genericApp f (arg (arg-info visible m) x) = app f x
genericApp f (arg (arg-info hidden m) x) = happ f x
genericApp f (arg (arg-info instance′ m) x) = iapp f x



returnTypeFor : Type → Term → TC Type
returnTypeFor (pi (arg _ dom) cod) x = do
  debugPrint "Leftovers" 2 (strErr "Checking pattern " ∷ termErr x ∷ strErr "  against type  " ∷ termErr dom ∷ [])
  -- checkType x dom
  return (app (lam visible cod) x)
returnTypeFor t x = do
  ldom ← freshMeta (quoteTerm Level)
  lcod ← freshMeta (quoteTerm Level)
  dom ← freshMeta (sort (set ldom))
  cod ← extendContext (vArg dom) (freshMeta (sort (set lcod)))
  unify t (pi (vArg dom) (abs "x" cod))
  return (app (lam visible (abs "x" cod)) x)

-- --Try an action (usually unification) but continue without it
-- -- if it fails
-- try : TC ⊤ → TC ⊤
-- try x = catchLeftovers x (pure tt)

-- tryUnify : Term → Term → Leftovers ⊤
-- tryUnify x y = try (unify x y)

{- Syntactic sugar for trying a computation, if it fails then try the other one -}
-- try-fun : ∀ {a} {A : Set a} → Leftovers A → Leftovers A → Leftovers A
-- try-fun = catchLeftovers

-- syntax try-fun t f = try t or-else f

constructors : Definition → List Name
constructors (data-type pars cs) = cs
constructors _ = []

import Reflection.Show

record CtorArg : Set where
  constructor mkCtorArg
  field
    pat : Arg Pattern
    term : Arg Term
    type : Arg Type

-- Do the comutation in the context extended with the given list
-- Tightest bindings are at the start of the list
-- i.e. if we have (T3 :: T2 :: T1) then T3 can refer to T2 and T1
extendContexts :  ∀  {ℓ} {A : Set ℓ} → List (Arg Type) → TC A → TC A
extendContexts [] x = x
extendContexts (h ∷ t) x = extendContext h (extendContexts t x)

open import Data.String as String
open import Data.Bool

-- Given a name, get its type
-- and generate fresh metas for each argument
-- e.g. turn (a -> b -> c -> d) into [_ , _ , _]
-- Leftmost patterns are at the start of the list,
-- so that thing are in the same order that pat-lam/clause expect
fully-applied-pattern : Name → TC (List (CtorArg))
fully-applied-pattern nm =
  do
    -- x ← quoteTC (the ((ℕ × ⊤) → Bool → ℕ) λ {(x , y) z → x})
    -- debugPrint "Leftovers" 2 (strErr "Test show term " ∷ strErr (showTerm x)  ∷ [])
    ctx ← getContext
    debugPrint "Leftovers" 2 (strErr "Full App Got context " ∷ strErr (String.intersperse ":::" (List.map (λ { (arg i x) → showTerm x}) ctx)) ∷ [])
    nmType ← getType nm
    debugPrint "Leftovers" 2 (strErr "fully-applied-pattern " ∷ nameErr nm ∷ strErr " got type " ∷ termErr nmType ∷ [])
    ret ← full-app-type nmType (pred (count-arrows nmType))
    debugPrint "Leftovers" 2
        (strErr "Full app returning: "
        ∷ strErr (Data.String.intersperse ",  " (List.map (λ x → (showPattern (unArg (CtorArg.pat x))) Data.String.++ " :: " Data.String.++ showTerm (unArg (CtorArg.type x) )) ret))
        ∷ [])
    return ret
  where
    -- We need to get the number of arrows, so we know where to start our DeBruijn index
    count-arrows : Type → ℕ
    count-arrows (pi (arg info dom) (abs s cod)) = 1 + (count-arrows cod)
    count-arrows _ = 0
    full-app-type : Type → ℕ → TC (List (CtorArg))
    full-app-type (pi (arg info dom) (abs s cod)) debr = do
      ctorArgType ← freshMeta (sort (lit 0))
      extendContext (arg info ctorArgType) do
        let retHead = mkCtorArg
                  (arg info (P.var debr))
                  (arg info (var debr []))
                  (arg info ctorArgType)
        retTail ← full-app-type cod (pred debr)
        return (retHead ∷ retTail)
      -- ((arg info (P.var pos) , arg info (var pos [])) ∷ full-app-type x (1 + pos))
    full-app-type t count = return []
