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

open import Function

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

getName : ∀ {ℓ} {A : Set ℓ} → (⊤ → A ) → Term → TC ⊤
getName fun unifGoal = do
  theFun ← quoteTC fun
  theName ← maybeLamName theFun
  unify unifGoal (lit (string theName))


stringCase :
    (str : String) →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (MkLM goal mem) : LabelMatch goals}
    (tac : Term → TC ⊤) →
    {@(tactic runSpec (findLeftovers (unLabel goal) tac)) wh : WithHoles (unLabel goal)} →
    MiddleGoalType IndHyp wh mem ->
    Proofs IndHyp goals
stringCase str {IndHyp} {goals} {MkLM goal mem} _ {wh}  = solveMember wh mem

-- Terrible hack: we thunk the tactic argument
-- and use the parameter name of the thunk as the name of the case
-- so that we don't need to put everything in quotes
DoCase-syntax :
    (tac : ⊤ → Term → TC ⊤) →
    {@(tactic getName tac) str : String} →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (MkLM goal mem) : LabelMatch goals}
    -- (tac : Term → TC ⊤) →
    {@(tactic runSpec (findLeftovers (unLabel goal) (tac tt))) wh : WithHoles (unLabel goal)} →
    MiddleGoalType IndHyp wh mem ->
    Proofs IndHyp goals
DoCase-syntax _ {goals = goals} {MkLM goal mem} {wh} = solveMember wh mem

ExactCase-syntax :
    ∀ {A : Set} →
    (result : ⊤ → A) →
    {@(tactic getName result) str : String} →
    ∀ {IndHyp goals} →
    {@(tactic getMatch str goals) (MkLM goal mem) : LabelMatch goals} →
    {@(tactic (λ t → unify t (quoteTerm (refl {x = A})))) eq : A ≡ unLabel goal} →
    MiddleGoalType IndHyp (withHoles [] (λ _ → subst (λ x → x) eq (result tt))) mem →
    Proofs IndHyp goals
ExactCase-syntax result {goals = goals} {MkLM goal mem} {eq} =
  solveMember ((withHoles [] (λ _ → subst (λ x → x) eq (result tt)))) mem

syntax DoCase-syntax (λ x → tac) rest = DoCase x by tac ⦊ rest
syntax ExactCase-syntax (λ x → result) rest = Case x by result ⦊ rest
