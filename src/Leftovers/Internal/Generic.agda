module Leftovers.Internal.Generic where

open import Reflection
open import Reflection.Show using (showName)
open import Leftovers.Internal.Proofs
open import Leftovers.Internal.FindHoles

open import Data.String renaming (toList to sToList ; _++_ to _++s_)
-- open import Data.String.Properties using (_==_)
open import Data.Char as Char
open import Data.Char.Properties as Char
open import Data.Unit
open import Data.Product
open import Data.List.Membership.Propositional

open import Data.List as List
open import Data.List.Properties as List
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat
open import Data.Empty

open import Data.Maybe using (Maybe ; just ; nothing)

open import Data.List.Relation.Unary.All
open import Function

open import Relation.Binary.Structures

-- data FoundLabel (goals : List LSet) : Maybe (∃[ goal ](goal ∈ goals)) → Set where
--   instance FoundJust : ∀ {pair} → FoundLabel goals (just pair)

-- foundLSet : ∀ {goals m} → FoundLabel goals m → LSet
-- foundLSet (FoundJust {pair}) = (proj₁ pair)

-- foundSet : ∀ {goals m} → FoundLabel goals m → Set
-- foundSet pf = unLabel (foundLSet pf)

-- foundMember :  ∀ {goals m} → (pf : FoundLabel goals m) → (foundLSet pf) ∈ goals
-- foundMember (FoundJust {(goal , mem)}) = mem

subString : String → String → Bool
subString s1 s2  = does (sToList s1 ⊆? sToList s2)
  where
    open import Relation.Nullary
    open import Data.List.Relation.Binary.Sublist.DecPropositional Char._≟_ as SubList
    open IsDecPartialOrder ⊆-isDecPartialOrder

getMatch : (str : String) → (goals : List LSet) → Term → TC ⊤
getMatch str goals unifGoal with findLabel (subString str) goals
... | nothing = typeError (strErr "No goal matching " ∷ strErr str ∷ [])
... | just ret = do
  goalsTerm ← quoteTC goals
  retTerm ← quoteTC ret
  debugPrint "Leftovers" 2 (strErr "Found matching LSet " ∷ termErr retTerm ∷ [])
  unify unifGoal retTerm

maybeLamName : Term → TC String
maybeLamName (lam v (abs s x)) = return s
maybeLamName _ = typeError (strErr "Impossible, got lambda name of non-lambda" ∷ [])

getName : ∀ {ℓ} {A : Set ℓ} → (⊤ → A ) → Term → TC ⊤
getName fun unifGoal = do
  theFun ← quoteTC fun
  theName ← maybeLamName theFun
  unify unifGoal (lit (string theName))


DoCase_by_⦊_ :
    (str : String) →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (MkLM goal mem) : LabelMatch goals}
    (tac : Term → TC ⊤) →
    {@(tactic runSpec (findHoles goal tac)) wh : WithHoles (unLabel goal)} →
    MiddleGoalType IndHyp wh mem ->
    Proofs IndHyp goals
DoCase_by_⦊_ str {IndHyp} {goals} {MkLM goal mem} _ {wh}  = solveMember wh mem


Case_by_⦊_ :
    (str : String) →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (MkLM goal mem) : LabelMatch goals}
    (result : unLabel goal) →
    MiddleGoalType IndHyp (trivialHole result) mem ->
    Proofs IndHyp goals
Case_by_⦊_ str {IndHyp} {goals} {MkLM goal mem} result   = solveMember (trivialHole result) mem



AllBy_⦊_ :
    ∀ {IndHyp goals} →
    (tac : Term → TC ⊤) →
    {@(tactic runSpec (findHolesInAll goals tac)) whs : All WithHoles (unLabels goals)} →
    Proofs IndHyp (concatMap (λ (_ , wh) → subGoalsForWH IndHyp wh) (toList whs )) ->
    Proofs IndHyp goals
AllBy_⦊_ _ {whs = whs} proofs = solveAll whs proofs



open import Data.List.Properties using (++-identityʳ )

prove_byInduction_⦊_ : ∀ (A : Set)
  → (@0 theMacro : Term → TC ⊤)
  → {@(tactic runSpec (findHoles ("--Goal" ⦂⦂ A) theMacro)) wh : WithHoles A}
  → (holes : Proofs A (List.map (λ (label ⦂⦂ Goal) → label ⦂⦂ (Hyp A → Goal) ) (WithHoles.labeledTypes wh)) )
  -- → {@(tactic runSpec (subName selfName (λ rec → f {!!}))) x : A}
  → IndProof A
prove_byInduction_⦊_ A theMacro {wh} holes = pcons wh (subst (Proofs A) (sym (List.++-identityʳ _ )) holes) --  (wh ∷ []) (concatProofs holes)

nextBy_⦊_ : ∀ {IndHyp : Set} {goal : LSet} {goals : List LSet} →
  (@0 theMacro : Term → TC ⊤) →
  {@(tactic runSpec (findHoles goal theMacro)) wh : WithHoles (unLabel goal)}
  → Proofs IndHyp (subGoalsForWH IndHyp wh ++ goals)
  → Proofs IndHyp (goal ∷ goals)
nextBy_⦊_  _ {wh} holes
  = pcons wh holes
