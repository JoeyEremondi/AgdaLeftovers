{-# OPTIONS --without-K #-}
module Leftovers.Internal.Utils where

open import Data.String using (String)
open import Data.List as List

-- open import Reflection
open import Leftovers.Internal.Monad
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
open Data.List.Categorical.TraversableM {m = Level.zero} leftoversMonad

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



returnTypeFor : Type → Term → Leftovers Type
returnTypeFor (pi (arg _ dom) cod) x = do
  debugPrint "returnTypeFor" 2 (strErr "Checking pattern " ∷ termErr x ∷ strErr "  against type  " ∷ termErr dom ∷ [])
  checkType x dom
  pure (app (lam visible cod) x)
returnTypeFor t x = do
  ldom ← freshMeta (quoteTerm Level)
  lcod ← freshMeta (quoteTerm Level)
  dom ← freshMeta (sort (set ldom))
  cod ← extendContext (vArg dom) (freshMeta (sort (set lcod)))
  unify t (pi (vArg dom) (abs "x" cod))
  pure (app (lam visible (abs "x" cod)) x)

--Try an action (usually unification) but continue without it
-- if it fails
try : Leftovers ⊤ → Leftovers ⊤
try x = catchLeftovers x (pure tt)

tryUnify : Term → Term → Leftovers ⊤
tryUnify x y = try (unify x y)

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

-- Given a name, get its type
-- and generate fresh metas for each argument
-- e.g. turn (a -> b -> c -> d) into [_ , _ , _]
fully-applied-pattern : Name → Leftovers (List (CtorArg))
fully-applied-pattern nm =
  do
    nmType ← getType nm
    -- debugPrint "full-app" 2 (strErr "fullApp " ∷ nameErr nm ∷ termErr nmType ∷ [])
    pure (full-app-type nmType 0)
  where
    full-app-type : Type → ℕ → List (CtorArg)
    full-app-type (pi (arg info dom) (abs s x)) pos =
      (mkCtorArg
        (arg info (P.var pos))
        (arg info (var pos []))
        (arg info unknown)) ∷ full-app-type x (1 + pos)
      -- ((arg info (P.var pos) , arg info (var pos [])) ∷ full-app-type x (1 + pos))
    full-app-type t pos = []
