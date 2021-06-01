
{-# OPTIONS -v 2 #-}
module Leftovers.Examples where

open import Leftovers.Leftovers
open import Leftovers.Equality

open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Product

notNot : ∀ b → not (not b) ≡ b
notNot = by {A = ∀ b → not (not b) ≡ b} (cases (quote Bool)) {!!} -- ({!refl!} , {!!})

-- plusZeroR : ∀ n → n + 0 ≡ n
-- plusZeroR = by (refl-cases (quote ℕ)) ?
