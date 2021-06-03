{-# OPTIONS --without-K #-}
module Leftovers.Utils where

open import Data.String using (String)
open import Data.List as List

-- open import Reflection
open import Leftovers.Monad
open import Reflection.Term
open import Reflection.Pattern as P
-- open import Reflection.TypeChecking.Monad.Instances
open import Data.Nat
open import Data.Product
open import Data.Unit

open import Function using (_$_)

import Data.List.Categorical
open import Level
open Data.List.Categorical.TraversableM {m = Level.zero} leftoversMonad

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

λv_↦_  λh_↦_ : String → Term → Term
λv x ↦ body  = lam visible (abs x body)
λh x ↦ body  = lam hidden (abs x body)

identity : ∀ {ℓ} {@0 X : Set ℓ} → X → X
identity x = x


the : ∀ {ℓ} → (@0 T : Set ℓ) → T → T
the _ = identity

_⦂_ : Term → Type → Term
t ⦂ T = def (quote the) (vArg T ∷ vArg t ∷ [])


app : Term → Term → Term
app f x = def (quote _$_) (vArg f ∷ vArg x ∷ [])

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
