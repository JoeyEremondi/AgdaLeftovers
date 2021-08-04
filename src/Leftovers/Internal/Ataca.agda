module Leftovers.Internal.Ataca where

open import Ataca.Core


open import Reflection
open import Reflection.Show using (showName)
open import Leftovers.Internal.Proofs
open import Leftovers.Internal.FindHoles

open import Data.String
open import Data.String.Properties using (_==_)
open import Data.Unit
open import Data.Product
open import Data.List.Membership.Propositional

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat
open import Data.Empty

open import Leftovers.Internal.Generic using (getMatch)
open import Leftovers.Internal.Generic using (Case_by_⦊_) public

DoCase_by_⦊_ :
    (str : String) →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (MkLM goal mem) : LabelMatch goals} →
    (tac : Tac ⊤) →
    {@(tactic runSpec (findHoles (unLabel goal) (runTac tac))) wh : WithHoles (unLabel goal)} →
    MiddleGoalType IndHyp wh mem ->
    Proofs IndHyp goals
DoCase_by_⦊_ str {IndHyp} {goals} {MkLM goal mem} _ {wh}  = solveMember wh mem


