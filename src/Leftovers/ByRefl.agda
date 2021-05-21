{-# OPTIONS --without-K #-}
module Leftovers.ByRefl where

open import Leftovers.Utils
open import Leftovers.Leftovers


import Level as Level
open import Reflection
open import Reflection.Term
open import Reflection.Pattern as P
open import Reflection.TypeChecking.Monad.Instances

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary


open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product
open import Data.List as List
open import Data.Char as Char
open import Data.String as String


import Data.List.Categorical
open Data.List.Categorical.TraversableM {m = Level.zero} tcMonad

--This file was adapted from https://github.com/alhassy/gentle-intro-to-reflection


macro
  by-refls : Name → Term → TC ⊤
  by-refls typeName hole -- thm-you-hope-is-provable-by-refls
    = do
      -- let η = nom
      δ ← getDefinition typeName
      clauses ← mapM mk-cls (constructors δ)
      holeType ← inferType hole
      -- declareDef (vArg η) holeType
      let retFun = pat-lam clauses []
      unify hole retFun
    where
      mk-cls : Name → TC Clause
      mk-cls ctor =
         do
           pat <- fully-applied-pattern ctor
           return (clause [ vArg (con ctor pat) ] (con (quote refl) []))

≡-type-info : Term → TC (Arg Term × Arg Term × Term × Term)
≡-type-info (def (quote _≡_) (𝓁 ∷ 𝒯 ∷ arg _ l ∷ arg _ r ∷ [])) = return (𝓁 , 𝒯 , l , r)
≡-type-info _ = typeError [ strErr "Term is not a ≡-type." ]

{- If we have “f $ args” return “f”. -}
$-head : Term → Term
$-head (var v args) = var v []
$-head (con c args) = con c []
$-head (def f args) = def f []
$-head (pat-lam cs args) = pat-lam cs []
$-head t = t



import Agda.Builtin.Reflection as Builtin

_$-≟_ : Term → Term → Bool
con c args $-≟ con c′ args′ = Builtin.primQNameEquality c c′
def f args $-≟ def f′ args′ = Builtin.primQNameEquality f f′
var x args $-≟ var x′ args′ = does (x Nat.≟ x′)
_ $-≟ _ = false

{- Only gets heads and as much common args, not anywhere deep. :'( -}
infix 5 _⊓_
{-# TERMINATING #-} {- Fix this by adding fuel (con c args) ≔ 1 + length args -}
_⊓_ : Term → Term → Term
l ⊓ r with l $-≟ r | l | r
...| false | x | y = unknown
...| true | var f args | var f′ args′ = var f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | con f args | con f′ args′ = con f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | def f args | def f′ args′ = def f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | ll | _ = ll {- Left biased; using ‘unknown’ does not ensure idempotence. -}

{- ‘unknown’ goes to a variable, a De Bruijn index -}
unknown-elim : ℕ → List (Arg Term) → List (Arg Term)
unknown-elim n [] = []
unknown-elim n (arg i unknown ∷ xs) = arg i (var n []) ∷ unknown-elim (n + 1) xs
unknown-elim n (arg i (var x args) ∷ xs) = arg i (var (n + suc x) args) ∷ unknown-elim n xs
unknown-elim n (arg i x ∷ xs)       = arg i x ∷ unknown-elim n xs
{- Essentially we want: body(unknownᵢ)  ⇒  λ _ → body(var 0)
   However, now all “var 0” references in “body” refer to the wrong argument;
   they now refer to “one more lambda away than before”. -}

unknown-count : List (Arg Term) → ℕ
unknown-count [] = 0
unknown-count (arg i unknown ∷ xs) = 1 + unknown-count xs
unknown-count (arg i _ ∷ xs) = unknown-count xs

unknown-λ : ℕ → Term → Term
unknown-λ zero body = body
unknown-λ (suc n) body = unknown-λ n (λv "section" ↦ body)

{- Replace ‘unknown’ with sections -}
patch : Term → Term
patch it@(def f args) = unknown-λ (unknown-count args) (def f (unknown-elim 0 args))
patch it@(var f args) = unknown-λ (unknown-count args) (var f (unknown-elim 0 args))
patch it@(con f args) = unknown-λ (unknown-count args) (con f (unknown-elim 0 args))
patch t = t


macro
  spine : Term → Term → TC ⊤
  spine p goal =
    do τ ← inferType p
       _ , _ , l , r ← ≡-type-info τ
       unify goal (patch (l ⊓ r))

macro
  applyEq : Term → Term → TC ⊤
  applyEq p hole =
    do
       τ ← inferType hole
       _ , _ , l , r ← ≡-type-info τ
       unify hole ((def (quote cong) (vArg (patch (l ⊓ r)) ∷ vArg p ∷ [])))

