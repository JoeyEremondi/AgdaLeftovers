{-# OPTIONS --without-K --auto-inline #-}
module Leftovers.Proofs where

open import Data.Nat
open import Data.List as List
open import Data.List.Relation.Unary.All
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties as All
open import Data.Product
open import Data.List.Relation.Unary.All using ([] ; _∷_) public
import Data.List.Properties as LProp
open import Function
open import Leftovers.Subst
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.String as String using (String)
open import Relation.Unary


------------------------------------------------------------------
------ Labes, HList and Nary functions
------------------------------------------------------------------

-- A labeled set is a type, along with a string describing it
-- This string will be used for e.g. naming goals after different cases
record LSet : Set1 where
  constructor _⦂⦂_
  field
    theLabel : String
    unLabel : Set

open LSet public


unLabels : List LSet -> List Set
unLabels = List.map unLabel

-- A Heterogeneous List is an element from each of a list of types
HList : List Set → Set1
HList = All id

-- Like HList, but remove the labels from the types
LHList : List LSet → Set1
LHList l = HList (unLabels l)

-- Given a list of types and a return type, NAry fun builds the curried function
-- type, from all argument types in the list to the return
NaryFun : ∀ {ℓ} → List Set → Set ℓ → Set ℓ
NaryFun [] cod = cod
NaryFun (dom ∷ doms) cod = dom → NaryFun doms cod

-- Given argument types and a return type, turn an n-ary function from the arguments to the return
-- into a function that takes an HList and produces the return
uncurryHList : ∀ {ℓ} doms (cod : Set ℓ) → NaryFun doms cod → HList doms → cod
uncurryHList [] cod x [] = x
uncurryHList (dom ∷ doms) cod f (x ∷ xs) = uncurryHList doms cod (f x) xs

-- Opposite of above: turn a function expecting an HList into an n-ary function
curryHList : ∀ {ℓ} {doms} {cod : Set ℓ} → (HList doms → cod) → NaryFun doms cod
curryHList {doms = []} {cod} f = f []
curryHList {doms = dom ∷ doms} {cod} f = λ x → curryHList {doms = doms} λ ds → f (x ∷ ds)

-- Helpers for dealing with hypothesis
-- Produces the LSet that is inhabited
-- iff the input LSet is inhabited whenever the given hypothesis is
-- i.e. produces the proper implicit function type
holdsUnderIndHypLS : Set → LSet → LSet
holdsUnderIndHypLS IndHyp (label ⦂⦂ Goal) = label ⦂⦂ ({indHyp : IndHyp} → Goal)

-- Same as above, but removes the labels from the result
holdsUnderIndHyp : Set → LSet → Set
holdsUnderIndHyp IndHyp X = unLabel (holdsUnderIndHypLS IndHyp X)


-- If each element of a list of LSets is implied by some hypothesis,
-- and we have a proof of that hypthesis,
-- then each element is inhabited.
applyIndHypAll : ∀ {IndHyp types} → IndHyp → All (holdsUnderIndHyp IndHyp) types → LHList types
applyIndHypAll hyp allUnder = All.map (λ {x} fun → fun {hyp}) (map⁺ allUnder)

---------------------------------------------------
------ Types with holes
---------------------------------------------------

-- The type (WithHoles A) denotes a values of type A containing some "holes".
-- It consists of a list of types (the hole types), along with a function from the hole types
-- to A (i.e. a "holey" version of A).
-- Use this type to chain proofs together: if we have an A with a B-shaped hole, and a B with a C-shaped hole
-- then compose to get an A with a C-shaped hole
record WithHoles (A : Set) : Set1 where
  constructor withHoles
  field
    labeledTypes : List LSet
  types : List Set
  types = unLabels labeledTypes
  field
    holeyFun : HList types → A


-- Take an n-ary function, and pack it with the domain type to produce a WithHoles value for the return type
uncurryWithHoles : ∀ (doms : List LSet) cod → NaryFun (unLabels doms) cod → WithHoles cod
uncurryWithHoles doms cod f =  withHoles doms (uncurryHList (unLabels doms) cod f)


-- Given a WithHoles A, get the labeled types of each hole
subGoalsForWH : ∀ IndHyp { goal} → WithHoles goal → List LSet
subGoalsForWH IndHyp wh = List.map (holdsUnderIndHypLS IndHyp) (WithHoles.labeledTypes wh)


-------------------------------------------------
-- Proofs: abstracting over and chaining-together lists of goals
-------------------------------------------------

-- The type `Proofs IH `[LS1 ... LSn]` is inhabited if,
-- given a proof of IH, we can construct a proof of each LSi
-- The labels are there for convenience, and shouldn't affect whether the type is inhabited
data Proofs (IndHyp : Set) : (goals : List LSet) → Set1 where
  -- We can trivially prove the empty set of goals
  ∎ :  Proofs IndHyp []
  -- To prove (goal ∷ goals), it suffices to provide
  -- a proof of `goal` containing holes (i.e. subgoals),
  -- a proof for each hole,
  -- and a proof for each remaining member of `goals`
  pcons : ∀ {goal goals} →
    (wh : WithHoles (unLabel goal)) →
      Proofs IndHyp ((subGoalsForWH IndHyp wh) ++ goals) ->
    Proofs IndHyp (goal ∷ goals)

-- If we have inhabitants for each goal type, then we have a proof of those goals under any hypothesis
exact : ∀ {IndHyp goals} → HList (unLabels goals) → Proofs IndHyp goals
exact {goals = []} [] = ∎
exact {goals = x ∷ goals} (px ∷ elems) = pcons (withHoles [] (λ _ → px)) (exact elems)


-- Every proof is a 0-hole holey proof
manual : ∀ {a} → a → WithHoles a
manual x = withHoles [] λ _ → x

plength : ∀ {IndHyp types} → Proofs IndHyp types → ℕ
plength ∎ = 0
plength (pcons wh p) = suc (plength p)

-- Syntactic sugar for pcons
nextBy_⦊_ : ∀ {IndHyp goal goals} →
    (wh : WithHoles (unLabel goal)) →
      Proofs IndHyp ((subGoalsForWH IndHyp wh) ++ goals) ->
    Proofs IndHyp (goal ∷ goals)
nextBy_⦊_ = pcons



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
Proof A ⇒ B = Proofs A [ "Goal" ⦂⦂ B ]

IndProof : Set → Set1
IndProof A = Proofs A [ "Goal" ⦂⦂ A ]

open import Data.List.Properties


-- We can partition a proof of some goals arbitrarily
unconcatProof :
  ∀ {IndHyp} goals1 goals2
  → Proofs IndHyp (goals1 ++ goals2)
  → (Proofs IndHyp goals1) × Proofs IndHyp goals2
unconcatProof [] _  proofs = ∎ , proofs
unconcatProof {IndHyp = IndHyp} (x ∷ goals1) goals2 (pcons wh proofs)
  rewrite sym (++-assoc (subGoalsForWH IndHyp wh) goals1 goals2)
  -- rewrite sym (++-assoc (subGoalsForWH IndHyp wh) goals1 goals2)
  with (rec1 , rec2 ) ← unconcatProof (subGoalsForWH IndHyp wh ++ goals1) goals2 proofs
  = pcons wh rec1 , rec2

unconcatLength :
  ∀ {IndHyp} goals1 goals2
  → (p : Proofs IndHyp (goals1 ++ goals2))
  → plength (proj₁ (unconcatProof goals1 goals2 p)) + plength (proj₂ (unconcatProof goals1 goals2 p)) ≡ plength p
unconcatLength [] goals2 p = refl
unconcatLength {IndHyp = IndHyp} (x ∷ goals1) goals2 (pcons wh p)
  rewrite sym (++-assoc (subGoalsForWH IndHyp wh) goals1 goals2)
  with rec ← unconcatLength _ goals2 p = cong suc rec

open import Data.Nat.Induction using (<-rec)



open import Data.Nat.Properties as NProp


-- We can concatenate proofs of different goal lists
concatProof : ∀ {IndHyp} goals1 goals2
  → (p1 : Proofs IndHyp goals1)
  → (p2 : Proofs IndHyp goals2)
  → Proofs IndHyp (goals1 ++ goals2)
concatProof goals1 goals2 p1 p2 =
    (<-rec
      (λ n1 → ∀ {IndHyp} goals1 goals2 → (p1 : Proofs IndHyp goals1) → (p2 : Proofs IndHyp goals2) → n1 ≡ plength p1 → Proofs IndHyp (goals1 ++ goals2)  )
      helper)
    _ goals1 goals2 p1 p2 refl
    where
        helper : _
        helper n1 rec [] goals2 ∎ p2 refl = p2
        helper n1 rec (x ∷ goals1) goals2 (pcons wh p1) p2 eq
          with eqn ← unconcatLength (subGoalsForWH _ wh) goals1 p1
          with (psub , p1') ← unconcatProof (subGoalsForWH _ wh) goals1 p1
          rewrite sym eqn
          rewrite eq
          with prec12 ← rec _ (s≤s (m≤n+m (plength p1') (plength psub))) goals1 goals2 p1' p2 refl
          with prec ← rec _ (s≤s (m≤m+n (plength psub) (plength p1'))) (subGoalsForWH _ wh) (goals1 ++ goals2) psub prec12 refl
          = pcons wh prec
  -- -- with (pfsub , pf1') ← unconcatProof (subGoalsForWH _ wh) goals1 pf1
  --  = {!!}

--We can reorder proofs. Applying this repeatedly allows for arbitrary permutations
switchProof :  ∀ {IndHyp} goals1 goals2
  → (p : Proofs IndHyp (goals1 ++ goals2))
  → Proofs IndHyp (goals2 ++ goals1)
switchProof goals1 goals2 p with (p1 , p2) ← unconcatProof goals1 goals2 p = concatProof _ _ p2 p1


-- If we have an A, and a proof of Bs assuming A, then we have Bs
runNonRecursiveList : ∀ {A Bs} → Proofs A  Bs → A → LHList Bs
runNonRecursiveList {A} {.[]} ∎ a = []
runNonRecursiveList {A} {(goal ∷ goals)} (pcons wh proofs) a
  = fun (applyIndHypAll a (map⁻ recL)) ∷ proj₂ recLR
  -- = WithHoles.holeyFun wh (applyIndHypAll a (map⁻ {f = λ Goal → LS _ ({indHyp : A} → unLabel Goal)} {!proj₁ recLR!})) ∷ proj₂ recLR
  -- -- = WithHoles.holeyFun wh (applyIndHypAll a (map⁻ (proj₁ recLR))) ∷ proj₂ recLR
    where
      fun : HList (unLabels (WithHoles.labeledTypes wh)) → unLabel goal
      fun = WithHoles.holeyFun wh
      recResult : LHList (subGoalsForWH A wh ++ goals)
      recResult with ret <- runNonRecursiveList proofs a = runNonRecursiveList proofs a -- runNonRecursiveList proofs a
      recLR : LHList (subGoalsForWH A wh) × LHList goals
      recLR
        = ++⁻ (unLabels (subGoalsForWH A wh))
          (subst (All id) (LProp.map-++-commute unLabel (List.map (holdsUnderIndHypLS A) (WithHoles.labeledTypes wh)) goals) recResult) -- ++⁻ (subGoalsForWH A wh) rec
      recL : All unLabel
               (List.map (holdsUnderIndHypLS A) (WithHoles.labeledTypes wh))
      recL = map⁻ {f = unLabel} (proj₁ recLR)

-- Special case of the above: if we have a proof of B assuming A, and we have A
-- then we have B
runNonRecursive : ∀ {A B} → Proof A ⇒ B → A → B
runNonRecursive proofs a
  with (b ∷ []) ← runNonRecursiveList proofs a  = b

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
