module Leftovers.Internal.Induction where

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

open import Data.Maybe using (just ; nothing)

getMatch : (str : String) → (goals : List LSet) → Term → TC ⊤
getMatch str goals unifGoal with findLabel (_==_ str) goals
... | nothing = typeError (strErr "No goal matching " ∷ strErr str ∷ [])
... | just ret = do
  retTerm ← quoteTC ret
  unify unifGoal retTerm

strCase_by_⦊_ :
    (str : String) →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (goal , member , match) : Σ-syntax LSet λ goal → goal ∈ goals × (theLabel goal == str) ≡ true}
    (tac : Term → TC ⊤) →
    {@(tactic runSpec (findLeftovers (unLabel goal) tac)) wh : WithHoles (unLabel goal)} →
    MiddleGoalType IndHyp wh member ->
    Proofs IndHyp goals
strCase_by_⦊_ str {IndHyp} {goals} {(goal , member , _)} tac {wh} = solveMember wh member

macro

  Case_by_⦊_ : Name → Term → TC ⊤
  Case_by_⦊_ nm unifGoal = unify unifGoal (quoteTerm (strCase_by_⦊_ (showName nm)))
