module Leftovers.Internal.Ataca where

open import Ataca.Utils
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

open import Data.List.Relation.Unary.All as All

open import Leftovers.Internal.Generic hiding (DoCase_by_⦊_ ; AllBy_⦊_) public

import Data.Maybe as Maybe
open import Data.Product


DoCase_by_⦊_ :
    (str : String) →
    ∀ {IndHyp goals} →
    (tac : Tac ⊤) →
    let
      mGoalMem = findLabel (subString str) goals
      mgoal = Maybe.map LabelMatch.matchedGoal mGoalMem
    in
    {@(tactic runSpec (MfindHoles mgoal (runTac tac))) wh : MWithHoles mgoal} →
    MMiddleGoalType IndHyp mGoalMem wh ->
    Proofs IndHyp goals
DoCase_by_⦊_ str {IndHyp} {goals}  _ {wh} pf = solveMMember (findLabel (subString str) goals) wh pf


TryCase_by_⦊_ :
    (str : String) →
    ∀ {IndHyp goals} →
    (tac : Tac ⊤) →
    let
      mGoalMem = findLabel (subString str) goals
      mgoal = Maybe.map LabelMatch.matchedGoal mGoalMem
    in
    {@(tactic runSpec (MfindHoles mgoal (runTac (tac <|> skip)))) wh : MWithHoles mgoal} →
    MMiddleGoalType IndHyp mGoalMem wh ->
    Proofs IndHyp goals
TryCase_by_⦊_ str {IndHyp} {goals} tac {wh} pf =  DoCase_by_⦊_ str {IndHyp} {goals} (tac <|> skip) {wh} pf

DoAll_⦊_ :
    ∀ {IndHyp goals} →
    (tac : Tac ⊤) →
    {@(tactic runSpec (findHolesInAll goals (runTac tac))) whs : All WithHoles (unLabels goals)} →
    Proofs IndHyp (concatMap (λ (_ , wh) → subGoalsForWH IndHyp wh) (All.toList whs )) ->
    Proofs IndHyp goals
DoAll_⦊_ _ {whs = whs} proofs = solveAll whs proofs


TryAll_⦊_ :
    ∀ {IndHyp goals} →
    (tac : Tac ⊤) →
    {@(tactic runSpec (findHolesInAll goals (runTac (tac <|> skip)))) whs : All WithHoles (unLabels goals)} →
    Proofs IndHyp (concatMap (λ (_ , wh) → subGoalsForWH IndHyp wh) (All.toList whs )) ->
    Proofs IndHyp goals
TryAll_⦊_ _ {whs = whs} proofs = solveAll whs proofs
