module Leftovers.Proofs where

open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All
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


data Proofs (target : Set) : List Set → Set1 where
  trivial : Proofs target []
  exact : ∀ {goal} → goal → Proofs target [ goal ]
  prove : ∀ {goals} →
    (whs : All WithHoles goals) →
    Proofs target (concat (Data.List.map (λ (Goal , (withHoles types fun)) → Data.List.map (λ Hole → {target} → Hole) types) (toList whs))) ->
    Proofs target goals

unConcatHList : ∀ setList → HList (concat setList) → All HList setList
unConcatHList [] [] = []
unConcatHList (set ∷ rest) inhabs = {!inhabs!} ∷ {!!}

runNonRecursive : ∀ {A Bs} → A → Proofs A  Bs → HList Bs
runNonRecursive a trivial = []
runNonRecursive a (exact x) = x ∷ []
runNonRecursive a (prove whs proofs) with results ← runNonRecursive a proofs = {!!}

runProof : ∀ {A} → (proofs : Proofs A [ A ]) → A
runProof proofs = {!!}
