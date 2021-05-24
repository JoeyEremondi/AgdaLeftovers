{-# OPTIONS --without-K #-}
module Leftovers.Utils where

open import Data.String using (String)
open import Data.List as List

open import Reflection
open import Reflection.Term
open import Reflection.Pattern as P
open import Reflection.TypeChecking.Monad.Instances
open import Data.Nat


case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

λv_↦_  λh_↦_ : String → Term → Term
λv x ↦ body  = lam visible (abs x body)
λh x ↦ body  = lam hidden (abs x body)


{- Syntactic sugar for trying a computation, if it fails then try the other one -}
try-fun : ∀ {a} {A : Set a} → TC A → TC A → TC A
try-fun = catchTC

syntax try-fun t f = try t or-else f

constructors : Definition → List Name
constructors (data-type pars cs) = cs
constructors _ = []



-- Given a name, get its type
-- and generate fresh metas for each argument
-- e.g. turn (a -> b -> c -> d) into [_ , _ , _]
fully-applied-pattern : Name → TC (List (Arg Pattern))
fully-applied-pattern nm =
  do
    nmType ← getType nm
    full-app-type nmType 0
  where
    full-app-type : Type → ℕ → TC (List (Arg Pattern))
    full-app-type (pi (arg info dom) (abs s x)) pos = do
      rec ← full-app-type x (1 + pos)
      hole ← newMeta dom
      return (arg info (P.var pos) ∷ rec)
    full-app-type t pos = return []
