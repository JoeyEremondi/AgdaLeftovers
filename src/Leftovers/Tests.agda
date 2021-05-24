-- Like Leftovers.Examples, but more meant to stress-test the library
-- than to be clear/readable
module Leftovers.Tests where

open import Leftovers.Leftovers
open import Leftovers.ByRefl

open import Level
open import Reflection
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Data.Unit
open import Data.List

--Make sure findLeftovers works with

data Foo : Set(Level.suc Level.zero) where
  Bar : Set → ℕ → ((n : ℕ) → n ≡ n + 0) → Foo

makePair : Term → TC ⊤
makePair = λ goal →
    do
      hole1 <- newMeta (quoteTerm Set)
      hole2 <- newMeta (quoteTerm ℕ)
      hole3 <- newMeta (quoteTerm ((n : ℕ) → n ≡ n + 0))
      body <- extendContext (vArg (quoteTerm ℕ)) do
        tyHole ← newMeta (quoteTerm Set)
        newHole ← newMeta tyHole
        return (def (quote sym) (vArg newHole ∷ []))
      unify hole3 (lam visible (abs "arg" body))
      unify hole2 (quoteTerm 4)
      unify goal (con (quote Bar) (vArg hole1 ∷ vArg hole2 ∷ vArg hole3 ∷ []))

p0 : ∀ n → n + 0 ≡ n
p0 zero = refl
p0 (suc n) rewrite p0 n = refl



f : Foo
f =
  by
    makePair
  andAlso
    p0
    ℕ
