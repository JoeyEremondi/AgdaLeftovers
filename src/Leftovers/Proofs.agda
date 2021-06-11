module Leftovers.Proofs where

open import Data.Nat
open import Data.List as List
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties as All
open import Data.Product

open import Function

HList : List Set → Set1
HList = All id

record WithHoles (A : Set) : Set1 where
  constructor withHoles
  field
    -- numHoles : ℕ
    types : List Set
    holeyFun : HList types → A

collectSubgoals : ∀ {goals} → Set → All WithHoles goals → List (List Set)
collectSubgoals target whs = List.map (λ (Goal , (withHoles types fun)) → List.map (λ Hole → {target} → Hole) types) (toList whs)

data Proofs (target : Set) : List Set → Set1 where
  trivial : Proofs target []
  exact : ∀ {goal} → goal → Proofs target [ goal ]
  prove : ∀ {goals} →
    (whs : All WithHoles goals) →
    Proofs target (concat (collectSubgoals target whs)) ->
    Proofs target goals

Proof_⇒_ : Set → Set → Set1
Proof A ⇒ B = Proofs A [ B ]

IndProof : Set → Set1
IndProof A = Proofs A [ A ]

seqProofs : ∀ {target} goals → target → (whs : All WithHoles goals) →
  HList (concat (collectSubgoals target whs)) ->
  HList goals
seqProofs [] target whs leftovers = []
seqProofs {target} (goal ∷ goals) a ((withHoles types fun) ∷ whs) leftovers
  with (fst ∷ rest) ← concat⁻ {xss = collectSubgoals target ((withHoles types fun) ∷ whs)} leftovers
  with fstUnmapped ← All.map⁻ fst
  with fstApplied ← All.map (λ fun → fun {a}) fstUnmapped = fun fstApplied ∷ seqProofs goals a whs (concat⁺ rest)


runNonRecursiveList : ∀ {A Bs} → Proofs A  Bs → A → HList Bs
runNonRecursiveList trivial a = []
runNonRecursiveList (exact x) a = x ∷ []
runNonRecursiveList  (prove whs proofs) a
  with results ←  (runNonRecursiveList proofs a)
    = seqProofs _ a whs results


runNonRecursive : ∀ {A B} → Proof A ⇒ B → A → B
runNonRecursive proofs a
  with (b ∷ []) ← runNonRecursiveList proofs a  = b

open import Reflection
open import Data.Unit

runIndProof : ∀ {A : Set} → Name → IndProof A → TC ⊤
runIndProof {A} nm proof = do
  let
    recFun : A → A
    recFun = λ x → runNonRecursive proof x
  funTerm ← quoteTC recFun
  case funTerm of λ
    { (lam _ (abs _ body)) → {!!}
    ; _ → typeError (strErr "Impossible, lambda didn't turn into lambda: " ∷ termErr funTerm ∷ [])
    }
  return tt
