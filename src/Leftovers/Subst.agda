{-# OPTIONS --without-K #-}
module Leftovers.Subst where

open import Reflection
open import Reflection.TypeChecking.Monad.Instances
open import Data.Nat as Nat
open import Data.Nat.Show as NShow
open import Relation.Nullary
open import Data.List
open import Data.Maybe using (just ; nothing)

open import Leftovers.Utils
open import Reflection.DeBruijn using (weaken ; strengthen)
open import Leftovers.Everywhere tcMonad
open import Data.Product using (_,_)
open import Data.Bool

specNorm : Term → TC Term
specNorm t = runSpeculative $ do
  ret ← normalise t
  return (ret , false)


tsubst : Term → ℕ → Term → TC Term
tsubst replacement x t = do
  subbed ← everywhere defaultActions action t
  let strongSubbed = strengthen subbed
  case strongSubbed of λ
    { nothing → typeError (strErr "Bug in subst, failed to replace var " ∷ strErr (NShow.show x) ∷ strErr " in " ∷ termErr t ∷ [])
    ; (just ret) → return ret}
  where
    action : Action Term
    action Γ t@(var y args) with (Cxt.len Γ + x Nat.≟ y)
    ... | yes _ = return (foldr (λ argTerm accum → genericApp accum argTerm) replacement args)
    ... | no _ = return t
    action _ t = return t


subName : ∀ {ℓ} {X : Set ℓ} -> Name → (X → X) → TC Term
subName {X = X} nm f = do
  XType ← quoteTC X
  XX ← quoteTC (X → X)
  fterm ← quoteTC f
  debugPrint "subName" 2 (strErr "subName input " ∷ termErr fterm ∷ [] )
  -- checkType goal XType
  case fterm of λ
    {( lam _ (abs _ body)) → do
      ret ← tsubst (def nm []) 0 body
      nf ← specNorm (ret ⦂ XType)
      debugPrint "subName" 2 (strErr "subName result " ∷ termErr nf ∷ [] )
      return (nf ⦂ XType)
    ; _ → typeError (strErr "Can't replace var in non-lambda term " ∷ termErr fterm ∷ [])
    }


