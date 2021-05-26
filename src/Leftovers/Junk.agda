{-# OPTIONS -v 2 #-}
module Leftovers.Junk where

open import Reflection
import Reflection.Pattern as P
open import Reflection.Term

open import Data.Bool
open import Data.Unit
open import Data.List as List
open import Data.Product

makeTrueFalse : Term → TC ⊤
makeTrueFalse hole
    = do
      holeType ← inferType hole
      rhs1 <- newMeta unknown
      rhs2 <- newMeta unknown
      let clause1 = clause [] [ vArg (con (quote true) []) ] rhs1
      let clause2 = clause [] [ vArg (con (quote false) []) ] rhs2
      let retFun = pat-lam (clause1 ∷ clause2 ∷ []) []
      redFun ← reduce retFun
      normFun ← normalise retFun
      debugPrint "refl-cases" 2 (strErr "Before normalise or reduce " ∷ termErr retFun ∷ [])
      debugPrint "refl-cases" 2 (strErr "Reduced form " ∷ termErr redFun ∷ [])
      debugPrint "refl-cases" 2 (strErr "Normal form " ∷ termErr normFun ∷ [])
      unify hole normFun




foo : Bool → Bool
foo = unquote makeTrueFalse
