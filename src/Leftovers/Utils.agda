{-# OPTIONS --without-K #-}
module Leftovers.Utils where

open import Data.String using (String)
open import Data.List as List

-- open import Reflection
open import Leftovers.Monad
open import Reflection.Term
open import Reflection.Pattern as P
open import Reflection.TypeChecking.Monad.Instances
open import Data.Nat

open import Data.Unit

open import Function using (_$_)

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

λv_↦_  λh_↦_ : String → Term → Term
λv x ↦ body  = lam visible (abs x body)
λh x ↦ body  = lam hidden (abs x body)

app : Term → Term → Term
app f x = def (quote _$_) (vArg f ∷ vArg x ∷ [])

returnTypeFor : Type → Term → Leftovers Type
returnTypeFor (pi (arg _ dom) cod) x = do
  checkType x dom
  pure (app (lam visible cod) x)
returnTypeFor t _ = typeError (strErr "Can't get return type of non-pi type " ∷ termErr t ∷ [])

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

-- Given a name, get its type
-- and generate fresh metas for each argument
-- e.g. turn (a -> b -> c -> d) into [_ , _ , _]
fully-applied-pattern : Name → Leftovers (List (Arg Pattern))
fully-applied-pattern nm =
  do
    nmType ← getType nm
    -- debugPrint "full-app" 2 (strErr "fullApp " ∷ nameErr nm ∷ termErr nmType ∷ [])
    full-app-type nmType 0
  where
    full-app-type : Type → ℕ → Leftovers (List (Arg Pattern))
    full-app-type (pi (arg info dom) (abs s x)) pos = do
      rec ← full-app-type x (1 + pos)
      hole ← freshMeta dom
      pure (arg info (P.var pos) ∷ rec)
    full-app-type t pos = pure []
