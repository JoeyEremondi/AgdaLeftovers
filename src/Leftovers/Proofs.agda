{-# OPTIONS --without-K #-}
module Leftovers.Proofs where

open import Data.Nat
open import Data.List as List
open import Data.List.Relation.Unary.All
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties as All
open import Data.Product
open import Data.List.Relation.Unary.All using ([] ; _∷_) public

open import Function

open import Leftovers.Subst
open import Relation.Binary.PropositionalEquality hiding ([_])

HList : List Set → Set1
HList = All id

NaryFun : ∀ {ℓ} → List Set → Set ℓ → Set ℓ
NaryFun [] cod = cod
NaryFun (dom ∷ doms) cod = dom → NaryFun doms cod

uncurryHList : ∀ {ℓ} doms (cod : Set ℓ) → NaryFun doms cod → HList doms → cod
uncurryHList [] cod x [] = x
uncurryHList (dom ∷ doms) cod f (x ∷ xs) = uncurryHList doms cod (f x) xs


curryHList : ∀ {ℓ} {doms} {cod : Set ℓ} → (HList doms → cod) → NaryFun doms cod
curryHList {doms = []} {cod} f = f []
curryHList {doms = dom ∷ doms} {cod} f = λ x → curryHList {doms = doms} λ ds → f (x ∷ ds)


record WithHoles (A : Set) : Set1 where
  constructor withHoles
  field
    -- numHoles : ℕ
    types : List Set
    holeyFun : HList types → A


uncurryWithHoles : ∀ doms cod → NaryFun doms cod → WithHoles cod
uncurryWithHoles doms cod f = withHoles doms (uncurryHList doms cod f)

subGoalsForWH : ∀ target → (∃[ X  ] WithHoles X) → List Set
subGoalsForWH target = (λ (Goal , (withHoles types fun)) → List.map (λ Hole → {target} → Hole) types)

collectSubgoals : ∀ {goals} → Set → All WithHoles goals → List (List Set)
collectSubgoals target whs = List.map (subGoalsForWH target) (toList whs)

data Proofs (target : Set) : List Set → Set1 where
  exact : ∀ {goals} → HList goals → Proofs target goals
  chain : ∀ {goals} →
    (whs : All WithHoles goals) →
    Proofs target (concat (collectSubgoals target whs)) ->
    Proofs target goals

getHoles : ∀ {target goals} → Proofs target goals → All WithHoles goals
getHoles (exact x) = All.map (λ soln → withHoles [] (λ _ → soln)) x
getHoles (chain whs p) = whs

getProofs : ∀ {target goals} → (p : Proofs target goals) → Proofs target (concat (collectSubgoals target (getHoles p)))
getProofs (chain whs p) = p
getProofs {target = target} (exact x) = exact (subst HList (sym (helper x)) [])
  where
    helper : ∀ {goals} (x : HList goals) → (concat
       (collectSubgoals target
        (All.map (λ soln → withHoles [] (λ _ → soln)) x))) ≡ []
    helper [] = refl
    helper (x ∷ x₁) rewrite helper x₁ = refl


Proof_⇒_ : Set → Set → Set1
Proof A ⇒ B = Proofs A [ B ]

IndProof : Set → Set1
IndProof A = Proofs A [ A ]

∎ : ∀ {target} → Proofs target []
∎ = exact []

seqProofs : ∀ {target} goals → target → (whs : All WithHoles goals) →
  HList (concat (collectSubgoals target whs)) ->
  HList goals
seqProofs [] target whs leftovers = []
seqProofs {target} (goal ∷ goals) a ((withHoles types fun) ∷ whs) leftovers
  with (fst ∷ rest) ← concat⁻ {xss = collectSubgoals target ((withHoles types fun) ∷ whs)} leftovers
  with fstUnmapped ← All.map⁻ fst
  with fstApplied ← All.map (λ fun → fun {a}) fstUnmapped = fun fstApplied ∷ seqProofs goals a whs (concat⁺ rest)

open import Data.List.Properties using (++-identityʳ )

-- Helper for making proofs for result of concat, which always has ++ [] at the end
concatProofs[] : ∀ {target goals} → Proofs target goals → Proofs target (goals ++ [])
concatProofs[] {goals = goals} p rewrite ++-identityʳ goals = p

unconcatProofs[] : ∀ {target goals} → Proofs target (goals ++ []) → Proofs target goals
unconcatProofs[] {goals = goals} p rewrite ++-identityʳ goals = p

manual_⦊_ : ∀ {target goal goals} → goal → Proofs target goals → Proofs target (goal ∷ goals)
manual pgoal ⦊ exact pgoals = exact (pgoal ∷ pgoals)
manual pgoal ⦊ chain whs proofs = chain ((withHoles [] (λ _ → pgoal )) ∷ whs) proofs


proofCons : ∀ {target goal goals} → Proof target ⇒ goal → Proofs target goals → Proofs target (goal ∷ goals)
proof++ : ∀ {target goals1 goals2} → Proofs target goals1 → Proofs target goals2 →
  Proofs target (goals1 ++ goals2)

proofHead : ∀ {target goal goals} → Proofs target (goal ∷ goals) → Proof target ⇒ goal
proofHead (exact (px ∷ x)) = exact (px ∷ [])
proofHead (chain (px ∷ whs) p) = chain (px ∷ []) (concatProofs[] {!All.concat⁻!})

proofCons (exact (px ∷ x)) prest = manual px ⦊ prest
proofCons {target = target} {goal = goal} (chain (px ∷ []) phead) prest
  with uc ← unconcatProofs[] phead
  = chain (px ∷ (getHoles prest)) (proof++ {goals1 = subGoalsForWH target (goal , px)} uc (getProofs prest))

proof++ {goals1 = []} p1 p2 = p2
proof++ {target = target} {goals1 = x ∷ goals1} p1 p2 = subst (Proofs target) {!!} (proofCons {!!} {!!})

runNonRecursiveList : ∀ {A Bs} → Proofs A  Bs → A → HList Bs
runNonRecursiveList (exact x) a = x
runNonRecursiveList  (chain whs proofs) a
  with results ←  (runNonRecursiveList proofs a)
    = seqProofs _ a whs results


runNonRecursive : ∀ {A B} → Proof A ⇒ B → A → B
runNonRecursive proofs a
  with (b ∷ []) ← runNonRecursiveList proofs a  = b

open import Reflection
open import Data.Unit
open import Leftovers.Utils

open import Data.Bool
open import Data.String as String


runIndProof : ∀ {A : Set} → Name → IndProof A → TC ⊤
runIndProof {A} nm proof = do
  fixpoint ← runSpeculative $ do
    ret ← subName nm (λ (x) → the A (runNonRecursive proof x))
    nf ← normalise ret
    return (nf , false)
  let cls = clauses fixpoint
  debugPrint "" 2 (strErr "got clauses" ∷ List.map (λ c → strErr (" " String.++ (showClause c) String.++ " ")) cls)
  defineFun nm cls
  return tt
