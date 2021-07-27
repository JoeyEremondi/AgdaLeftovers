{-# OPTIONS --without-K --auto-inline --prop #-}
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

open import Data.String as String using (String)

data Label : Prop where
  label : String → Label

record LSet : Set1 where
  constructor LS
  field
    theLabel : Label
    unLabel : Set

open LSet

pattern _⦂_ l X = LS (label l) X

unLabels : List LSet -> List Set
unLabels = List.map unLabel

HList : List Set → Set1
HList = All id

LHList : List LSet → Set1
LHList l = HList (unLabels l)

Labels : List Set -> Set1
Labels tipes =  All (λ _ → String) tipes



NaryFun : ∀ {ℓ} → List Set → Set ℓ → Set ℓ
NaryFun [] cod = cod
NaryFun (dom ∷ doms) cod = dom → NaryFun doms cod

uncurryHList : ∀ {ℓ} doms (cod : Set ℓ) → NaryFun doms cod → HList doms → cod
uncurryHList [] cod x [] = x
uncurryHList (dom ∷ doms) cod f (x ∷ xs) = uncurryHList doms cod (f x) xs


curryHList : ∀ {ℓ} {doms} {cod : Set ℓ} → (HList doms → cod) → NaryFun doms cod
curryHList {doms = []} {cod} f = f []
curryHList {doms = dom ∷ doms} {cod} f = λ x → curryHList {doms = doms} λ ds → f (x ∷ ds)


-- dummyLabel : Set → LSet
-- dummyLabel X = ("" , X)

-- dummyLabels : List Set → List LSet
-- dummyLabels = List.map dummyLabel

record WithHoles (A : Set) : Set1 where
  constructor withHoles
  field
    -- numHoles : ℕ
    labeledTypes : List LSet
  types : List Set
  types = unLabels labeledTypes
  field
    holeyFun : HList types → A




uncurryWithHoles : ∀ (doms : List LSet) cod → NaryFun (unLabels doms) cod → WithHoles cod
uncurryWithHoles doms cod f =  withHoles doms (uncurryHList (unLabels doms) cod f)

holdsUnderIndHypLS : Set → LSet → LSet
holdsUnderIndHypLS IndHyp Goal = LS (theLabel Goal) ({indHyp : IndHyp} → unLabel Goal)


holdsUnderIndHyp : Set → LSet → Set
holdsUnderIndHyp IndHyp X = unLabel (holdsUnderIndHypLS IndHyp X)

subGoalsForWH : ∀ IndHyp { goal} → WithHoles goal → List LSet
subGoalsForWH IndHyp wh = List.map (holdsUnderIndHypLS IndHyp) (WithHoles.labeledTypes wh)

open import Relation.Unary

applyIndHyp : ∀ {IndHyp} → IndHyp → (holdsUnderIndHyp IndHyp) ⊆ unLabel
applyIndHyp hyp fun = fun {hyp}


-- applyIndHypAll : ∀ {IndHyp types} → IndHyp → All (holdsUnderIndHyp IndHyp) types → LHList types
-- applyIndHypAll hyp = {!All.map !} -- All.map (applyIndHyp hyp)

-- collectSubgoals : ∀ {goal} → Set → All WithHoles goal → List Set
-- collectSubgoals IndHyp whs = List.map {!!} (toList whs)

data Proofs (IndHyp : Set) : (tipes : List LSet) → Set1 where
  ∎ :  Proofs IndHyp []
  pcons : ∀ {goal goals} →
    (wh : WithHoles (unLabel goal)) →
      Proofs IndHyp ((subGoalsForWH IndHyp wh) ++ goals) ->
    Proofs IndHyp (goal ∷ goals)


exact : ∀ {IndHyp goals} → HList (unLabels goals) → Proofs IndHyp goals
exact {goals = []} [] = ∎
exact {goals = x ∷ goals} (px ∷ elems) = pcons (withHoles [] (λ _ → px)) (exact elems)

-- nextBy_⦊_ : ∀ {IndHyp : Set} {goal goals label labels} → (wh : WithHoles goal) →
--               Proofs IndHyp ((subGoalsForWH _ wh) ++ goals) → Proofs IndHyp (goal ∷ goals)
-- nextBy_⦊_ = pcons

manual : ∀ {a} → a → WithHoles a
manual x = withHoles [] λ _ → x

-- getHoles : ∀ {IndHyp goals} → Proofs IndHyp goals → All WithHoles goals
-- getHoles (exact x) = All.map (λ soln → withHoles [] (λ _ → soln)) x
-- getHoles (chain whs p) = whs

-- getProofs : ∀ {IndHyp goals} → (p : Proofs IndHyp goals) → Proofs IndHyp (concat (collectSubgoals IndHyp (getHoles p)))
-- getProofs (chain whs p) = p
-- getProofs {IndHyp = IndHyp} (exact x) = exact (subst HList (sym (helper x)) [])
--   where
--     helper : ∀ {goals} (x : HList goals) → (concat
--        (collectSubgoals IndHyp
--         (All.map (λ soln → withHoles [] (λ _ → soln)) x))) ≡ []
--     helper [] = refl
--     helper (x ∷ x₁) rewrite helper x₁ = refl


Proof_⇒_ : Set → Set → Set1
Proof A ⇒ B = Proofs A [ "Goal" ⦂ B ]

IndProof : Set → Set1
IndProof A = Proofs A [ "Goal" ⦂ A ]

open import Data.List.Properties


unconcatProof :
  ∀ {IndHyp goals1 goals2}
  → Proofs IndHyp (goals1 ++ goals2)
  → (Proofs IndHyp goals1) × Proofs IndHyp goals2
unconcatProof {goals1 = []}  proofs = ∎ , proofs
unconcatProof {IndHyp = IndHyp} {goals1 = x ∷ goals1} {goals2} (pcons wh proofs)
  rewrite sym (++-assoc (subGoalsForWH IndHyp wh) goals1 goals2)
  -- rewrite sym (++-assoc (subGoalsForWH IndHyp wh) goals1 goals2)
  with (rec1 , rec2 ) ← unconcatProof {goals1 = subGoalsForWH IndHyp wh ++ goals1 } {goals2 =  goals2} proofs
  = pcons wh rec1 , rec2


-- seqProofs : ∀ {IndHyp} goals → IndHyp → (whs : All WithHoles goals) →
--   HList (concat (collectSubgoals IndHyp whs)) ->
--   HList goals
-- seqProofs goals whs _ = ?
-- seqProofs [] IndHyp whs leftovers = []
-- seqProofs {IndHyp} (goal ∷ goals) a ((withHoles types fun) ∷ whs) leftovers
--   with (fst ∷ rest) ← concat⁻ {xss = collectSubgoals IndHyp ((withHoles types fun) ∷ whs)} leftovers
--   with fstUnmapped ← All.map⁻ fst
--   with fstApplied ← All.map (λ fun → fun {a}) fstUnmapped = fun fstApplied ∷ seqProofs goals a whs (concat⁺ rest)

-- open import Data.List.Properties using (++-identityʳ )

-- -- Helper for making proofs for result of concat, which always has ++ [] at the end
-- concatProofs[] : ∀ {IndHyp goals} → Proofs IndHyp goals → Proofs IndHyp (goals ++ [])
-- concatProofs[] {goals = goals} p rewrite ++-identityʳ goals = p

-- unconcatProofs[] : ∀ {IndHyp goals} → Proofs IndHyp (goals ++ []) → Proofs IndHyp goals
-- unconcatProofs[] {goals = goals} p rewrite ++-identityʳ goals = p

-- manual_⦊_ : ∀ {IndHyp goal goals} → goal → Proofs IndHyp goals → Proofs IndHyp (goal ∷ goals)
-- manual pgoal ⦊ exact pgoals = exact (pgoal ∷ pgoals)
-- manual pgoal ⦊ chain whs proofs = chain ((withHoles [] (λ _ → pgoal )) ∷ whs) proofs


-- proofCons : ∀ {IndHyp goal goals} → Proof IndHyp ⇒ goal → Proofs IndHyp goals → Proofs IndHyp (goal ∷ goals)
-- proof++ : ∀ {IndHyp goals1 goals2} → Proofs IndHyp goals1 → Proofs IndHyp goals2 →
--   Proofs IndHyp (goals1 ++ goals2)

-- proofHead : ∀ {IndHyp goal goals} → Proofs IndHyp (goal ∷ goals) → Proof IndHyp ⇒ goal
-- proofHead (exact (px ∷ x)) = exact (px ∷ [])
-- proofHead (chain (px ∷ whs) p) = chain (px ∷ []) (concatProofs[] {!All.concat⁻!})

-- proofCons (exact (px ∷ x)) prest = manual px ⦊ prest
-- proofCons {IndHyp = IndHyp} {goal = goal} (chain (px ∷ []) phead) prest
--   with uc ← unconcatProofs[] phead
--   = chain (px ∷ (getHoles prest)) (proof++ {goals1 = subGoalsForWH IndHyp (goal , px)} uc (getProofs prest))

-- proof++ {goals1 = []} p1 p2 = p2
-- proof++ {IndHyp = IndHyp} {goals1 = x ∷ goals1} p1 p2 = subst (Proofs IndHyp) {!!} (proofCons {!!} {!!})

-- runNonRecursiveList : ∀ {A Bs} → Proofs A  Bs → A → LHList Bs
-- runNonRecursiveList {A} {.[]} ∎ a = []
-- runNonRecursiveList {A} {(goal ∷ goals)} (pcons wh proofs) a
--   = WithHoles.holeyFun wh (applyIndHypAll a (map⁻ {f = λ Goal → LS _ ({indHyp : A} → unLabel Goal)} {!proj₁ recLR!})) ∷ proj₂ recLR
--   -- = WithHoles.holeyFun wh (applyIndHypAll a (map⁻ (proj₁ recLR))) ∷ proj₂ recLR
--     where
--       rec : LHList (subGoalsForWH A wh ++ goals)
--       rec with ret <- runNonRecursiveList proofs a = runNonRecursiveList proofs a -- runNonRecursiveList proofs a
--       recLR : LHList (subGoalsForWH A wh) × LHList goals
--       recLR = ++⁻ (unLabels (subGoalsForWH A wh)) {!rec!} -- ++⁻ (subGoalsForWH A wh) rec


-- runNonRecursive : ∀ {A B} → Proof A ⇒ B → A → B
-- runNonRecursive proofs a
--   with (b ∷ []) ← runNonRecursiveList proofs a  = b

-- open import Reflection
-- open import Data.Unit
-- open import Leftovers.Utils

-- open import Data.Bool
-- open import Data.String as String


-- runIndProof : ∀ {A : Set} → Name → IndProof A → TC ⊤
-- runIndProof {A} nm proof = do
--   fixpoint ← runSpeculative $ do
--     ret ← subName nm (λ (x) → the A (runNonRecursive proof x))
--     nf ← normalise ret
--     return (nf , false)
--   let cls = clauses fixpoint
--   debugPrint "" 2 (strErr "got clauses" ∷ List.map (λ c → strErr (" " String.++ (showClause c) String.++ " ")) cls)
--   defineFun nm cls
--   return tt
