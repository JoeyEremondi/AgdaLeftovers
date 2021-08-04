{-# OPTIONS --without-K --auto-inline #-}
module Leftovers.Internal.Proofs where

open import Data.Nat
open import Data.List as List
open import Data.List.Relation.Unary.All
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties as All
open import Data.Product
open import Data.List.Relation.Unary.All using ([] ; _∷_) public
import Data.List.Properties as LProp
open import Function
open import Leftovers.Internal.Subst
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.String as String using (String)
open import Relation.Unary hiding (_∈_)


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

-- Here just so that Auto doesn't prematurely pick up the inductive hypothesis
record Hyp A : Set where
  constructor packHyp
  field
    recur : A

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
holdsUnderIndHypLS IndHyp (label ⦂⦂ Goal) = label ⦂⦂ (Hyp IndHyp → Goal)

-- Same as above, but removes the labels from the result
holdsUnderIndHyp : Set → LSet → Set
holdsUnderIndHyp IndHyp X = unLabel (holdsUnderIndHypLS IndHyp X)


-- If each element of a list of LSets is implied by some hypothesis,
-- and we have a proof of that hypthesis,
-- then each element is inhabited.
applyIndHypAll : ∀ {IndHyp types} → Hyp IndHyp → All (holdsUnderIndHyp IndHyp) types → LHList types
applyIndHypAll hyp allUnder = All.map (λ {x} fun → fun hyp) (map⁺ allUnder)

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

trivialHole : ∀ {A} → A → WithHoles A
trivialHole x = withHoles [] (λ _ → x)

-- If we have inhabitants for each goal type, then we have a proof of those goals under any hypothesis
exact : ∀ {IndHyp goals} → HList (unLabels goals) → Proofs IndHyp goals
exact {goals = []} [] = ∎
exact {goals = x ∷ goals} (px ∷ elems) = pcons (trivialHole px) (exact elems)


-- Every proof is a 0-hole holey proof
manual : ∀ {a} → a → WithHoles a
manual x = withHoles [] λ _ → x

plength : ∀ {IndHyp types} → Proofs IndHyp types → ℕ
plength ∎ = 0
plength (pcons wh p) = suc (plength p)

-- Syntactic sugar for pcons
-- nextBy_⦊_ : ∀ {IndHyp goal goals} →
--     (wh : WithHoles (unLabel goal)) →
--       Proofs IndHyp ((subGoalsForWH IndHyp wh) ++ goals) ->
--     Proofs IndHyp (goal ∷ goals)
-- nextBy_⦊_ = pcons



---------  Some synonyms for readability

-- A proof that A implies B
Proof_⇒_ : Set → Set → Set1
Proof A ⇒ B = Proofs A [ "Goal" ⦂⦂ B ]

-- An inductive proof of A.
-- If A is a function type, and all uses of the assumption A are made on structurally-smaller arguments,
-- then we can use reflection to extract a value of type A.
-- Generally should be used with the "cases" macro
-- TODO: where is this?
IndProof : Set → Set1
IndProof A = Proofs A [ "Goal" ⦂⦂ A ]

open import Data.List.Properties


--------------------------------------

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
  = fun (applyIndHypAll (packHyp a) (map⁻ recL)) ∷ proj₂ recLR
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

open import Reflection
open import Data.Unit
open import Leftovers.Internal.Utils

open import Data.Bool
-- open import Data.String as String


-- Use reflection to take  `proof : IndProof A`
-- and turn it into a definition named `nm` with type A
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


----------------------------------------
-- Solving goals in the middle of a list

open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.Maybe

record LabelMatch (goals : List LSet) : Set1 where
  constructor MkLM
  field
    matchedGoal : LSet
    matchMember : matchedGoal ∈ goals

-- Find the first goal whose label matches the given predicate
findLabel : (pred : String → Bool) → (goals : List LSet) → Maybe (LabelMatch goals)
findLabel pred [] = nothing
findLabel pred (goal ∷ goals) with pred (theLabel goal)
... | true = just (MkLM goal (here refl))
... | false with findLabel pred goals
... | nothing = nothing
... | just (MkLM result member) = just (MkLM result (there member))


-- Solve a goal in the middle of a goal list
solveMiddle : ∀ {IndHyp goal goals1 goals2} →
    (wh : WithHoles (unLabel goal)) →
      Proofs IndHyp ((subGoalsForWH IndHyp wh) ++ goals1 ++ goals2) ->
    Proofs IndHyp (goals1 ++ [ goal ] ++ goals2)
solveMiddle {IndHyp} {goal = goal} {goals1} {goals2} wh pf
  with (pfgoal , pf12) ← unconcatProof (subGoalsForWH IndHyp wh) (goals1 ++ goals2) pf
  with (pf1 , pf2) ← unconcatProof goals1 goals2 pf12
  = switchProof ([ goal ] ++ goals2) goals1
    (pcons wh
      (concatProof (subGoalsForWH IndHyp wh) (([] ++ goals2) ++ goals1) pfgoal
      (concatProof goals2 goals1 pf2 pf1)))

-- Helper: make Proofs type from the evidence that a goal is in a goal list
MiddleGoalType : ∀ (IndHyp : Set) {goal goals} → WithHoles (unLabel goal) → goal ∈ goals → Set1
MiddleGoalType IndHyp wh member with (goals1 , goals2 , _) ← ∈-∃++ member =
  Proofs IndHyp (subGoalsForWH IndHyp wh ++ goals1 ++ goals2)

-- Given a goal occurring somewhere in a goal list, and a holey proof of that goal, and proofs of the remaining goals,
-- construct a proof of the entire goal list
solveMember : ∀ {IndHyp goal goals} →
    (wh : WithHoles (unLabel goal)) →
    (member : goal ∈ goals) →
    MiddleGoalType IndHyp wh member ->
    Proofs IndHyp goals
solveMember wh member pf with (goals1 , goals2 , refl) ← ∈-∃++ member = solveMiddle wh pf


solveAll : ∀ {IndHyp goals} →
  (whs : All WithHoles (unLabels goals)) →
  Proofs IndHyp (concatMap (λ (_ , wh ) → subGoalsForWH IndHyp wh) (toList whs))
  → Proofs IndHyp goals
solveAll {goals = []} [] pf = pf
solveAll {goals = x ∷ goals} (wh ∷ whs) pf
  with (phead , prest) ←
    unconcatProof
      (subGoalsForWH _ wh)
      ((concatMap (λ (_ , wh ) → subGoalsForWH _ wh) (toList whs))) pf =
  pcons wh (concatProof _ goals phead (solveAll whs prest))
