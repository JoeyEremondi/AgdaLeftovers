{-# OPTIONS -v 2 --prop #-}
module Leftovers.Junk where


open import Reflection
open import Reflection.Term
open import Reflection.TypeChecking.Monad.Instances
open import Reflection.Argument using (unArg)

open import Data.Unit

open import Data.String
open import Data.List
open import Data.Nat

data SString : Prop where
  squash : String → SString

data SSString : Set where
  unsquash : SString → SSString

data Foo : Set where
  Bar : SString → Foo


myMacro : SString → Term → TC ⊤
myMacro t ret = do
  tterm ← quoteTC (unsquash t)
  debugPrint "Leftovers" 2 (strErr "Squashed string " ∷ termErr tterm ∷ [])
  unify ret (lit (nat 0))

myFun : (s : SString) -> {@(tactic myMacro s) x : ℕ} -> ℕ
myFun _ {x} = x

foo : ℕ
foo = myFun (squash "foo1")

bar : ℕ
bar = myFun (squash "bar2")
