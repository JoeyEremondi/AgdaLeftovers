{-# OPTIONS --without-K #-}
module Leftovers.Internal.FindHoles where

open import Function using (_$_)
open import Data.Bool
open import Data.String as String using (String)

open import Leftovers.Internal.TraverseTerm
open import Leftovers.Internal.Utils

import Level as Level
open import Reflection
open import Reflection.Term
open import Reflection.TypeChecking.Monad.Instances
open import Reflection.Argument using (unArg)

open import Data.Fin using (toℕ ; Fin)


open import Reflection.DeBruijn using (weaken ; strengthen)
import Leftovers.Internal.Everywhere
import Category.Monad.State as State

open Leftovers.Internal.Everywhere tcMonad
-- open import SE tcMonad -- renaming (everywhere to Severywhere ; Cxt to SCxt ; defaultActions to SdefaultActions)

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Nat.Show as NShow
open import Data.Product
import Data.List as List
import Data.List.Properties as List
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
open import Data.List using (List ; [] ; _∷_ ; foldr ; length ; _++_ ; [_])
import Data.Vec as Vec
open import Data.Vec using (Vec)
import Data.Vec.Categorical as VCat
open import Reflection.DeBruijn

import Data.List.Categorical
open Data.List.Categorical.TraversableM {m = Level.zero} tcMonad

open import Data.Maybe using (just ; nothing)

-- open import Function.Nary.NonDependent
-- open import Data.Product.Nary.NonDependent


import Category.Monad as Monad


open import Level.Literals using (#_)

import Data.Fin.Reflection
import Data.Nat.Reflection

-- import Leftovers.Internal.Monad as L
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Leftovers.Internal.Subst
open import Leftovers.Internal.Proofs



run : (TC Term) → Term → TC ⊤
run comp goal = do
  t ← comp
  unify t goal
  debugPrint "" 2 (strErr "run generating " ∷ termErr t ∷ [])


runSpec : (TC Term) → Term → TC ⊤
runSpec comp goal = do
  t ← runSpeculative $ do
    t' ← comp
    return (t' , false)
  unify t goal
  debugPrint "" 2 (strErr "runSpec generating " ∷ termErr t ∷ [])



open import Agda.Builtin.Nat using (_-_)




-- sep : Term → TC Term
-- sep t = do
--   debugPrint "" 2 (strErr "Finding sep for " ∷ strErr (showTerm t) ∷ [])
--   ty ← inferType t
--   debugPrint "" 2 (strErr "sep got type " ∷ strErr (showTerm ty) ∷ [])
--   let ret = (def (quote  identity) [ vArg t ]) -- ⦂ ty
--   return ret




record Hole : Set  where
  constructor mkHole
  field
    holeMeta : Meta
    hole : Term
    context : List (Arg Type)


import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Definitions as D
open import Data.Empty using (⊥)
EquivHole : ∀ (x y : Hole) → Set
EquivHole (mkHole x _ _ ) (mkHole y _ _) = x Eq.≡ y

open import Relation.Nullary using (yes ; no)

equivDec : D.Decidable EquivHole
equivDec (mkHole x _ _) (mkHole y _ _) = x Meta.≟ y
  where import Reflection.Meta as Meta

getMetas : Term → TC (List Hole)
getMetas t = do
    -- body <- newMeta goalType
    debugPrint "Hello" 2 (strErr "Ran macro, body var is " ∷ termErr t ∷ [])
    -- L.runLeftovers (theMacro body)
      --Now we see what holes are left
    let
        handleMetas : _ → Meta → Data.Maybe.Maybe Hole
        handleMetas ctx m = just (mkHole m (meta m (List.map (λ x → vArg (var x [])) (List.downFrom (length ctx )))) (List.map proj₂ ctx))
    debugPrint "L" 2 (strErr "After ALLMETAS " ∷ [])
      -- debugPrint "L" 2 (strErr "ALLMETAS NORM " ∷ List.map termErr normMetas)
    let metaList =  (collectFromSubterms
                      (record
                        { onVar = λ _ _ → nothing
                        ; onMeta = handleMetas
                        ; onCon = λ _ _ → nothing
                        ; onDef = λ _ _ → nothing }) t
              )
    return (List.deduplicate equivDec metaList)



-- Given the size of the starting context, a hole,
-- and the list of parameters to add to the start context,
-- Generate a new hole whose context has the new parameters
-- inserted into the middle.
-- We need this because a meta might occur in a deeper scope than
-- where we're inserting the new variables.
-- weakenMeta : ℕ → List (Arg Type) → Hole → Hole
-- weakenMeta startSize newParams hole =
--   mkHole (Reflection.DeBruijn.weakenFrom (numNew + 1) (length newParams) (Hole.hole hole)) fullCtx
--   where
--     numNew = List.length (Hole.context hole) - startSize
--     fullCtx : List (Arg Type)
--     fullCtx with (newCtx , startCtx) ← List.splitAt numNew (Hole.context hole)
--       = newCtx ++ newParams ++ startCtx

-- Given the length of the current context
-- and a meta in a possibly deeper context
-- return the type of the meta in the original context
-- e.g. a function type abstracting over any new variables
abstractMetaType : ℕ → (Hole × Type) → Type
abstractMetaType numStart (hole , ty) =
  foldr (λ param ty → pi param (abs "arg" ty)) ty
    (List.take (length (Hole.context hole) - numStart) (Hole.context hole))


-- Given the size of the current context and a list of new parameter types to add
-- freshen all metas to take new parameters and weaken DeBruijn variables accordingly
-- Also forgets any blocked constraints on those metas, since they're replaced by new ones
injectParameters : List Type → List Type → Term → TC Term
injectParameters currentCtx injectedCtx t = everywhere defaultActions freshenMeta  (weaken (length injectedCtx) t)
  where
    freshenMeta : Cxt → Term → TC Term
    freshenMeta innerVars (meta m xs) = do
      mtype ← inferType (meta m xs)
      newMeta mtype
    freshenMeta innerVars t = return t

open import Data.Maybe using (Maybe ; just ; nothing)

record MacroResult : Set where
  constructor macroResult
  field
    body : Term
    numMetas : ℕ
    holes : Vec Hole numMetas
    types : Vec Type numMetas
    indexFor : Meta → Maybe (Fin numMetas)

getMacroHoles : Type → List (Arg Type) → (Term → TC ⊤) → TC MacroResult
getMacroHoles targetType ctx theMacro = runSpeculative $
      do
        body ← do
          hole ← freshMeta targetType
          theMacro hole
          return  hole
        normBody ← specNorm body
        metas ← getMetas normBody
        let metaVec = Vec.fromList metas
        debugPrint "Leftovers" 2 (strErr "All holes " ∷ [])
      -- debugPrint "Leftovers" 2 (strErr "All holes " ∷ List.map (λ m → termErr (Hole.hole m)) metas)
      -- Now we know how many arguments we need to take
        debugPrint "Leftovers" 2 (strErr "Unified num holes " ∷ [])
    -- Get the type of each hole *in its context*
        types <- VCat.TraversableM.forM {a = Level.zero} {n = length metas} tcMonad (metaVec)
          λ hole → inContext (Hole.context hole ++ ctx) do
             -- debugPrint "" 2 (strErr "Context : " ∷ strErr (String.intersperse ",, " (List.map (λ x → showTerm (unArg x)) (contextForHole hole))) ∷ [])
             debugPrint "" 2 (strErr "Getting type of hole " ∷ termErr ( (Hole.hole hole) ) ∷ strErr " !" ∷  [])
             ty ← inferType (Hole.hole hole)
             debugPrint "" 2 [ strErr "got type" ]
             return ty
        let indexedHoles = Vec.toList (Vec.zip (Vec.allFin (length metas)) metaVec)
        debugPrint "" 2 (strErr "Indexed holes: " ∷ List.map (λ x → termErr (meta (Hole.holeMeta (proj₂ x)) [])) indexedHoles)
        let
          indexForMeta m =
            Data.Maybe.map proj₁ $
              List.head (List.filter (λ y → m Meta.≟ Hole.holeMeta (proj₂ y)) indexedHoles)
        debugPrint "Hello" 2 (strErr "normalised MacroBody " ∷ termErr normBody ∷ [])
        return (macroResult normBody _ metaVec types indexForMeta , false) -- ((body , metas , types) , false)
        where
          open import Reflection.Meta as Meta


metaToArg : MacroResult → Cxt → Term → TC Term
metaToArg results cxt t@(meta m _) with (MacroResult.indexFor results m)
... | just i = do
  let
    ithHole = Vec.lookup (MacroResult.holes results) i
    numNewInContext = length (Hole.context ithHole)
    argNum = (numNewInContext + ((MacroResult.numMetas results - 1) - toℕ i))
  debugPrint "" 2 (strErr "Replacing meta " ∷ strErr (showTerm (meta m [])) ∷ strErr " with arg " ∷ strErr (NShow.show argNum) ∷ [])
  return (var argNum (List.map (λ x → vArg (var x [])) (List.upTo numNewInContext)))
... | nothing = typeError (strErr "Internal Error: unfound meta " ∷ termErr (meta m []) ∷ strErr " when finding Leftover holes" ∷ [])
metaToArg _ _ t = return t

open import Data.List renaming (_∷_ to cons ; [] to nil)

private
  consNm : Name
  consNm = quote cons

open import Leftovers.Internal.LabelMetas

findLeftovers : ∀ {ℓ} → Set ℓ → (Term → TC ⊤) → TC Term
findLeftovers targetSet theMacro =
  do
    startContext ← getContext
    let startCtxLen = List.length startContext
    targetType ← quoteTC targetSet

    -- Run the given macro on a fresh hole
    -- in a context extended with the argument with the Holes
    debugPrint "Leftovers" 2 (strErr "goalType before run theMacro" ∷ termErr targetType ∷ [])
    result ← getMacroHoles targetType startContext theMacro
    let numMetas = MacroResult.numMetas result
    debugPrint "Leftovers" 2 (strErr "Got holes types " ∷ [])
    -- debugPrint "Hello" 2 (strErr "Got hole types" ∷ List.map termErr (Vec.toList holeTypes))
    let
      abstractedTypes = (Vec.map (abstractMetaType startCtxLen)
            (Vec.zip (MacroResult.holes result) (MacroResult.types result)))
      nil : List Set
      nil = List.[]
      sets =
        Vec.foldr
          (λ _ → Term)
          (λ h t → con consNm (vArg h ∷ vArg t ∷ []))
          (quoteTerm nil) abstractedTypes
      numHoles =  (Data.Nat.Reflection.toTerm numMetas)
    debugPrint "Hello" 2 (strErr "Raw sets " ∷ strErr (showTerm sets) ∷ [])
    checkType sets (quoteTerm (List Set))
    -- sets ← normalise (rawSets ⦂ (quoteTerm (List Set)))

    -- debugPrint "Hello" 2 (strErr "Made sets " ∷ strErr (showTerm sets) ∷ [])

    --This gives us enough information to make a function parameterized over the types of holes
    --We traverse the result of the macro, replacing each meta with a parameter
    --and wrap the hole thing in an n-ary lambda taking parameters of the hole types
    funBody ← everywhere defaultActions (metaToArg result) (MacroResult.body result)
    debugPrint "" 2 (strErr "got fun body: " ∷ strErr (showTerm funBody) ∷ [])
    -- sepBody ← inContext (List.map vArg (List.reverse $ Vec.toList abstractedTypes) ++ startContext) $ sep funBody
    -- debugPrint "" 2 (strErr "got fun body " ∷ strErr (showTerm sepBody) ∷ [])
    nflam ← specNorm (naryLam numMetas funBody ⦂ def (quote NaryFun) (vArg sets ∷ vArg targetType ∷ []))
    debugPrint "" 2 (strErr "making fun fun " ∷ strErr (showTerm nflam) ∷ [])
    --Produce the function that gives the result of the last macro
    labelPairs ← labelMetas (MacroResult.body result)
    let labels = Vec.map (λ x → labelFor (Hole.holeMeta x) labelPairs) (MacroResult.holes result)
        termLabels = 
          Vec.foldr
            (λ _ → Term)
            (λ h t → con consNm (vArg (lit (string h)) ∷ vArg t ∷ []))
            (quoteTerm nil) labels
    normSets ← normalise ((def (quote List.zipWith) (vArg (quoteTerm _⦂⦂_) ∷ vArg termLabels ∷ vArg sets ∷ [])))
    let
      finalResult =
        (def (quote uncurryWithHoles)
          (
            -- ∷ vArg (Data.Nat.Reflection.toTerm numMetas)
            vArg normSets
            ∷ vArg targetType
            ∷ vArg (naryLam numMetas (funBody ⦂ targetType)) ∷ []))
    -- unify goal finalResult
    debugPrint "Hello" 2 (strErr "Final Result " ∷ termErr finalResult ∷ [])
    return finalResult
  where
    naryLam : ℕ → Term → Term
    naryLam 0 x = x
    naryLam (suc n) x = lam visible (abs ("hole" String.++ NShow.show (suc n)) (naryLam n x))


    -- quoteSets : ∀ {n} → Vec.Vec Term n → Term
    -- quoteSets Vec.[] = con (quote Level.lift) (vArg (quoteTerm tt) ∷ [])
    -- quoteSets {n = suc n} (x Vec.∷ v) = (con (quote _,_) (vArg x ∷ vArg (quoteSets v) ∷ [] ))

open import Relation.Nullary

-- infixr 10 [_⇒_]
--

open import Data.List.Properties using (++-identityʳ )

prove_byInduction_⦊_ : ∀ (A : Set)
  → (@0 theMacro : Term → TC ⊤)
  → {@(tactic runSpec (findLeftovers A theMacro)) wh : WithHoles A}
  → (holes : Proofs A (List.map (λ (label ⦂⦂ Goal) → label ⦂⦂ ({A} → Goal) ) (WithHoles.labeledTypes wh)) )
  -- → {@(tactic runSpec (subName selfName (λ rec → f {!!}))) x : A}
  → IndProof A
prove_byInduction_⦊_ A theMacro {wh} holes = pcons wh (subst (Proofs A) (sym (List.++-identityʳ _ )) holes) --  (wh ∷ []) (concatProofs holes)

by_⦊_ : ∀ {IndHyp : Set} {goal : LSet} {goals : List LSet} →
  (@0 theMacro : Term → TC ⊤) →
  {@(tactic runSpec (findLeftovers (unLabel goal) theMacro)) wh : WithHoles (unLabel goal)}
  → Proofs IndHyp (subGoalsForWH IndHyp wh ++ goals)
  → Proofs IndHyp (goal ∷ goals)
by_⦊_  _ {wh} holes
  = pcons wh holes

doRun : ∀ {A : Set} → (theMacro : TC Term) → {@(tactic run theMacro) x : A} → A
doRun _ {x} = x


-- defineBy : ∀ {A : Set }
--   → (selfName : Name)
--   → (theMacro : Term → L.Leftovers ⊤)
--   → {@(tactic runSpec (findLeftovers A theMacro)) (withHoles n types f) : WithHoles A}
--   → (holes : {A} → Product n (toSets types) )
--   → TC ⊤
-- defineBy nm _ {(withHoles _ _ f)} holes = do
--   body ← subName nm (λ rec → f (makeHoles (holes {rec})))
--   defineFun nm [ clause [] [] body ]
--   return tt

open import Relation.Nullary


default : ∀ {ℓ} {A : Set ℓ} → A → Term → TC ⊤
default x hole = bindTC (quoteTC x) (unify hole)
