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
open import Data.Nat
open import Data.Empty

open import Data.Maybe using (Maybe ; just ; nothing)

-- data FoundLabel (goals : List LSet) : Maybe (∃[ goal ](goal ∈ goals)) → Set where
--   instance FoundJust : ∀ {pair} → FoundLabel goals (just pair)

-- foundLSet : ∀ {goals m} → FoundLabel goals m → LSet
-- foundLSet (FoundJust {pair}) = (proj₁ pair)

-- foundSet : ∀ {goals m} → FoundLabel goals m → Set
-- foundSet pf = unLabel (foundLSet pf)

-- foundMember :  ∀ {goals m} → (pf : FoundLabel goals m) → (foundLSet pf) ∈ goals
-- foundMember (FoundJust {(goal , mem)}) = mem

getMatch : (str : String) → (goals : List LSet) → Term → TC ⊤
getMatch str goals unifGoal with findLabel (_==_ str) goals
... | nothing = typeError (strErr "No goal matching " ∷ strErr str ∷ [])
... | just ret = do
  goalsTerm ← quoteTC goals
  retTerm ← quoteTC ret
  unify unifGoal retTerm

maybeLamName : Term → TC String
maybeLamName (lam v (abs s x)) = return s
maybeLamName _ = typeError (strErr "Impossible, got lambda name of non-lambda" ∷ [])

getName : (⊤ → ⊥ → ⊤ ) → Term → TC ⊤
getName fun unifGoal = do
  theFun ← quoteTC fun
  theName ← maybeLamName theFun
  unify unifGoal (lit (string theName))

memberCaseBy :
    ∀ {IndHyp goals} →
    (goal : LSet) → (mem : goal ∈ goals) →
    (tac : Term → TC ⊤) →
    {@(tactic runSpec (findLeftovers (unLabel goal) tac)) wh : WithHoles (unLabel goal)} →
    MiddleGoalType IndHyp wh mem ->
    Proofs IndHyp goals
memberCaseBy goal mem _ {wh} = solveMember wh mem

strCase_by_⦊_ :
    (str : String) →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (MkLM goal mem) : LabelMatch goals}
    (tac : Term → TC ⊤) →
    {@(tactic runSpec (findLeftovers (unLabel goal) tac)) wh : WithHoles (unLabel goal)} →
    MiddleGoalType IndHyp wh mem ->
    Proofs IndHyp goals
strCase_by_⦊_ str {IndHyp} {goals} {MkLM goal mem}  = memberCaseBy goal mem

lambdaCaseBy :
    (dummy : ⊤ → ⊥ → ⊤)
    {@(tactic getName dummy) str : String} →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (MkLM goal mem) : LabelMatch goals}
    (tac : Term → TC ⊤) →
    -- (tac : Term → TC ⊤) →
    {@(tactic runSpec (findLeftovers (unLabel goal) tac)) wh : WithHoles (unLabel goal)} →
    MiddleGoalType IndHyp wh mem ->
    Proofs IndHyp goals
lambdaCaseBy dummy {str} {IndHyp} {goals} {MkLM goal mem}  = memberCaseBy goal mem


-- syntax lambdaCaseBy (λ x → 0) tac rest = Case x by tac ⦊ rest ⦊ n

-- macro
--   Case_by_⦊_ : Name → Term → TC ⊤
--   Case_by_⦊_ nm unifGoal = unify unifGoal (quoteTerm (strCase_by_⦊_ (showName nm)))
