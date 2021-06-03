{-# OPTIONS -v 2 #-}
module Leftovers.Junk where

open import Data.Bool
open import Relation.Binary.PropositionalEquality



id : ∀ {X : Set} → X → X
id x = x

the : ∀ X → X → X
the X = id {X}

badEq :
  let f = the (Bool -> Bool -> Bool) (λ x → λ {true → false ; false → true})
  in f true ≡ f false
badEq = {!!} -- refl does not typecheck


goodEq :
  let f = the (Bool -> Bool -> Bool) (λ x → id λ {true → false ; false → true})
  in f true ≡ f false
goodEq = {!!}
