{-# OPTIONS --without-K #-}
module Leftovers.Leftovers where

open import Function using (_$_)
open import Data.Bool
import Data.String as String

open import Leftovers.TraverseTerm
open import Leftovers.Utils

import Level as Level
open import Reflection
open import Reflection.Term
open import Reflection.TypeChecking.Monad.Instances
open import Reflection.Argument using (unArg)

open import Data.Fin using (toℕ ; Fin)


open import Reflection.DeBruijn using (weaken ; strengthen)
open import Leftovers.Everywhere tcMonad

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Nat.Show as NShow
open import Data.Product
open import Data.List as List
import Data.Vec as Vec
open import Data.Vec using (Vec)
import Data.Vec.Categorical as VCat
open import Reflection.DeBruijn

import Data.List.Categorical
open Data.List.Categorical.TraversableM {m = Level.zero} tcMonad

open import Data.Maybe using (just ; nothing)

-- open import Function.Nary.NonDependent
-- open import Data.Product.Nary.NonDependent


open import Category.Monad.State
import Category.Monad as Monad


open import Level.Literals using (#_)

import Data.Fin.Reflection
import Data.Nat.Reflection

import Leftovers.Monad as L
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Leftovers.Subst
open import Leftovers.Proofs

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

--Given a hole, infer its function type,
--taking anything in the hole's context that's not in the current context
-- as an argument
inferHoleType : L.Hole → TC Type
inferHoleType hole = do
  currentContext ← getContext
  let
    numExtras = (List.length (L.Hole.context hole)) - (List.length currentContext)
    extras = List.take numExtras (L.Hole.context hole)
  holeType ← inContext (L.Hole.context hole) (inferType (L.Hole.hole hole))
  addArrows extras holeType
  where
    open import Agda.Builtin.Nat
    addArrows : List (Arg Type) → Term → TC Type
    addArrows [] holeType = return holeType
    addArrows (x ∷ extras) holeType = do
      rec ← addArrows extras holeType
      return (pi x (abs "ctx" rec))

data Dummy : Set where
  dummy : Dummy



sep : Term → TC Term
sep t = do
  debugPrint "" 2 (strErr "Finding sep for " ∷ strErr (showTerm t) ∷ [])
  ty ← inferType t
  debugPrint "" 2 (strErr "sep got type " ∷ strErr (showTerm ty) ∷ [])
  let ret = (def (quote  identity) [ vArg t ]) -- ⦂ ty
  return ret



getMetas : Term → TC (List L.Hole)
getMetas t = do
    -- body <- newMeta goalType
    debugPrint "Hello" 2 (strErr "Ran macro, body var is " ∷ termErr t ∷ [])
    -- L.runLeftovers (theMacro body)
      --Now we see what holes are left
    let
        handleMetas : _ → Meta → Data.Maybe.Maybe L.Hole
        handleMetas ctx m = just (L.mkHole m (meta m (List.map (λ x → vArg (var x [])) (List.downFrom (length ctx )))) (List.map proj₂ ctx))
    debugPrint "L" 2 (strErr "After ALLMETAS " ∷ [])
      -- debugPrint "L" 2 (strErr "ALLMETAS NORM " ∷ List.map termErr normMetas)
    let metaList =  (collectFromSubterms
                      (record
                        { onVar = λ _ _ → nothing
                        ; onMeta = handleMetas
                        ; onCon = λ _ _ → nothing
                        ; onDef = λ _ _ → nothing }) t
              )
    return (List.deduplicate L.equivDec metaList)

-- Given the size of the starting context, a hole,
-- and the list of parameters to add to the start context,
-- Generate a new hole whose context has the new parameters
-- inserted into the middle.
-- We need this because a meta might occur in a deeper scope than
-- where we're inserting the new variables.
-- weakenMeta : ℕ → List (Arg Type) → L.Hole → L.Hole
-- weakenMeta startSize newParams hole =
--   L.mkHole (Reflection.DeBruijn.weakenFrom (numNew + 1) (length newParams) (L.Hole.hole hole)) fullCtx
--   where
--     numNew = List.length (L.Hole.context hole) - startSize
--     fullCtx : List (Arg Type)
--     fullCtx with (newCtx , startCtx) ← List.splitAt numNew (L.Hole.context hole)
--       = newCtx ++ newParams ++ startCtx

-- Given the length of the current context
-- and a meta in a possibly deeper context
-- return the type of the meta in the original context
-- e.g. a function type abstracting over any new variables
abstractMetaType : ℕ → (L.Hole × Type) → Type
abstractMetaType numStart (hole , ty) =
  foldr (λ param ty → pi param (abs "arg" ty)) ty
    (take (length (L.Hole.context hole) - numStart) (L.Hole.context hole))


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
    holes : Vec L.Hole numMetas
    types : Vec Type numMetas
    indexFor : Meta → Maybe (Fin numMetas)

getMacroHoles : Type → List (Arg Type) → (Term → L.Leftovers ⊤) → TC MacroResult
getMacroHoles targetType ctx theMacro = runSpeculative $
      do
        (body , _) ← L.runLeftovers
          ((L.freshMeta targetType) L.>>=
          λ hole → theMacro hole L.>> L.pure hole)
        normBody ← specNorm body
        metas ← getMetas normBody
        let metaVec = Vec.fromList metas
        debugPrint "Leftovers" 2 (strErr "All holes " ∷ [])
      -- debugPrint "Leftovers" 2 (strErr "All holes " ∷ List.map (λ m → termErr (L.Hole.hole m)) metas)
      -- Now we know how many arguments we need to take
        debugPrint "Leftovers" 2 (strErr "Unified num holes " ∷ [])
    -- Get the type of each hole *in its context*
        types <- VCat.TraversableM.forM {a = Level.zero} {n = length metas} tcMonad (metaVec)
          λ hole → inContext (L.Hole.context hole ++ ctx) do
             -- debugPrint "" 2 (strErr "Context : " ∷ strErr (String.intersperse ",, " (List.map (λ x → showTerm (unArg x)) (contextForHole hole))) ∷ [])
             debugPrint "" 2 (strErr "Getting type of hole " ∷ termErr ( (L.Hole.hole hole) ) ∷ strErr " !" ∷  [])
             ty ← inferType (L.Hole.hole hole)
             debugPrint "" 2 [ strErr "got type" ]
             return ty
        let indexedHoles = Vec.toList (Vec.zip (Vec.allFin (length metas)) metaVec)
        debugPrint "" 2 (strErr "Indexed holes: " ∷ List.map (λ x → termErr (meta (L.Hole.holeMeta (proj₂ x)) [])) indexedHoles)
        let
          indexForMeta m =
            Data.Maybe.map proj₁ $
              head (filter (λ y → m Meta.≟ L.Hole.holeMeta (proj₂ y)) indexedHoles)
        debugPrint "Hello" 2 (strErr "normalised MacroBody " ∷ termErr normBody ∷ [])
        return (macroResult normBody _ metaVec types indexForMeta , false) -- ((body , metas , types) , false)
        where
          open import Reflection.Meta as Meta


metaToArg : MacroResult → Cxt → Term → TC Term
metaToArg results cxt t@(meta m _) with (MacroResult.indexFor results m)
... | just i = do
  let
    ithHole = Vec.lookup (MacroResult.holes results) i
    numNewInContext = length (L.Hole.context ithHole)
    argNum = (numNewInContext + ((MacroResult.numMetas results - 1) - toℕ i))
  debugPrint "" 2 (strErr "Replacing meta " ∷ strErr (showTerm (meta m [])) ∷ strErr " with arg " ∷ strErr (NShow.show argNum) ∷ [])
  return (var argNum (List.map (λ x → vArg (var x [])) (List.upTo numNewInContext)))
... | nothing = typeError (strErr "Internal Error: unfound meta " ∷ termErr (meta m []) ∷ strErr " when finding Leftover holes" ∷ [])
metaToArg _ _ t = return t

findLeftovers : ∀ {ℓ} → Set ℓ → (Term → L.Leftovers ⊤) → TC Term
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
      sets =
        quoteSets abstractedTypes
      numHoles =  (Data.Nat.Reflection.toTerm numMetas)
    debugPrint "Hello" 2 (strErr "Made sets " ∷ strErr (showTerm sets) ∷ [])

    --This gives us enough information to make a function parameterized over the types of holes
    --We traverse the result of the macro, replacing each meta with a parameter
    --and wrap the hole thing in an n-ary lambda taking parameters of the hole types
    funBody ← everywhere defaultActions (metaToArg result) (MacroResult.body result)
    sepBody ← inContext (List.map vArg (List.reverse $ Vec.toList abstractedTypes) ++ startContext) $ sep funBody
    debugPrint "" 2 (strErr "got fun body " ∷ strErr (showTerm sepBody) ∷ [])
    nflam ← specNorm (naryLam numMetas sepBody ⦂ def (quote NaryFun) (vArg sets ∷ vArg targetType ∷ []))
    debugPrint "" 2 (strErr "making fun fun " ∷ strErr (showTerm nflam) ∷ [])
    --Produce the function that gives the result of the last macro
    let
      finalResult =
        (def (quote uncurryHList)
          (
            vArg targetType
            ∷ vArg (Data.Nat.Reflection.toTerm numMetas)
            ∷ vArg sets
            ∷ vArg (naryLam numMetas (sepBody ⦂ targetType)) ∷ []))
    -- unify goal finalResult
    debugPrint "Hello" 2 (strErr "Final Result " ∷ termErr finalResult ∷ [])
    return finalResult
  where
    naryLam : ℕ → Term → Term
    naryLam 0 x = x
    naryLam (suc n) x = lam visible (abs ("hole" String.++ NShow.show (suc n)) (naryLam n x))

    quoteLevels : ∀ {n} → Vec.Vec Term n → TC Term
    quoteLevels Vec.[] = return (con (quote Level.lift) (vArg (quoteTerm tt) ∷ []))
    quoteLevels {n = suc n} (x Vec.∷ v) = do
      rec ← quoteLevels {n = n} v
      typeOfType ← inferType x
      let
        theLevel = case typeOfType of λ
          { (sort (set l)) →  l
          ; (sort (lit l)) →  (def (quote #_) (vArg (lit (nat l)) ∷ [] ))
          ;  _ → quoteTerm Level.zero }

      return (con (quote _,_) (vArg theLevel ∷ vArg rec ∷ [] ))

    quoteSets : ∀ {n} → Vec.Vec Term n → Term
    quoteSets Vec.[] = con (quote Level.lift) (vArg (quoteTerm tt) ∷ [])
    quoteSets {n = suc n} (x Vec.∷ v) = (con (quote _,_) (vArg x ∷ vArg (quoteSets v) ∷ [] ))

open import Relation.Nullary

-- infixr 10 [_⇒_]
--

open import Data.List.Properties using (++-identityʳ )

byInduction : ∀ {A : Set }
  → (theMacro : Term → L.Leftovers ⊤)
  → {@(tactic runSpec (findLeftovers A theMacro)) (withHoles types f) : WithHoles A}
  → (holes : Proofs A (List.map (λ Goal → {A} → Goal) types) )
  -- → {@(tactic runSpec (subName selfName (λ rec → f {!!}))) x : A}
  → IndProof A
byInduction {A = A} theMacro {wh} holes = prove (wh ∷ []) (concatProofs holes)
-- by _ _ _ {x = x} = x

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


default : {A : Set} → A → Term → TC ⊤
default x hole = bindTC (quoteTC x) (unify hole)
