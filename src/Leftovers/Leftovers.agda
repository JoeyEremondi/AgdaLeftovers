{-# OPTIONS --without-K #-}
module Leftovers.Leftovers where

import Data.String as String

open import Leftovers.TraverseTerm
open import Leftovers.Utils

import Level as Level
open import Reflection
open import Reflection.Term
open import Reflection.TypeChecking.Monad.Instances



open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Product
open import Data.List as List
import Data.Vec as Vec
import Data.Vec.Categorical as VCat


import Data.List.Categorical
open Data.List.Categorical.TraversableM {m = Level.zero} tcMonad

open import Data.Maybe using (just ; nothing)


open import Function.Nary.NonDependent
open import Data.Product.Nary.NonDependent


open import Category.Monad.State
import Category.Monad as Monad


open import Level.Literals using (#_)

import Data.Fin.Reflection

import Leftovers.Monad as L

data Holes (n : ℕ) (levels : Levels n) (sets : Sets n levels ) : Set (⨆ n levels)    where
  makeHoles : Product n sets → Holes n levels sets

getHoles : ∀ {n ls sets} → Holes n ls sets → Product n sets
getHoles (makeHoles p) = p

nthHole : ∀ n {ls} {as : Sets n ls } k → Holes n ls as → Projₙ as k
nthHole n k h = projₙ n k (getHoles h)

infixr 10 _∥_

_∥_ : ∀ {n : ℕ} {levels : Levels n} {sets : Sets n levels}
   {ℓ} {X : Set ℓ} →
  Holes n levels sets → X →
  Holes (suc n) (ℓ , levels) (X , sets)
_∥_ {n = zero} {sets = sets} {X = X} holes x = makeHoles x
_∥_ {n = suc n} {sets = sets} {X = X} holes x = makeHoles (x , getHoles holes)

-- fillHoles : ∀ {ℓ} {n} {ls} {types : Sets n ls} {T : Set ℓ} → (Holes n ls types → T) → Product n types → T
-- fillHoles f args = f (makeHoles args)


-- quoteSets {n = suc n} (x Vec.∷ v) = app (app (quoteTerm (_,_   {A = Set} {B = λ x₁ → Sets n (proj₂ nSet)}  )) x) (quoteSets v)


-- record MetaInContext : Set where
--   constructor Cmeta
--   field
--     context : LCxt
--     unapplied : Term
--     applied : Term
--
--
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



findLeftovers : (Term → L.Leftovers ⊤) → Term → TC ⊤
findLeftovers theMacro goal =
  do
    -- We're producing a function from hole-fills to the goal type
    funType ← inferType goal
    debugPrint "Leftovers" 2 (strErr "Goal function type " ∷ termErr funType ∷ [])
    -- Unification variable for number of holes, we don't know how many yet
    numHoles ← newMeta (quoteTerm ℕ)
    -- Unification variables for the HVec of holes
    levels ← newMeta (def (quote Levels) (vArg numHoles ∷ [])) -- def (quote nSet) [ hArg numHoles ]
    sets ← newMeta (def (quote Sets) (vArg numHoles ∷ vArg levels ∷ []))
    let productType = def (quote Holes) (vArg numHoles ∷ vArg levels ∷ vArg sets ∷ [])
    -- The return type of the function we're producing
    (argType , goalAbs) ← case funType of λ
      { (pi (arg _ dom) cod) → return (dom , cod)
      ; _ → typeError (strErr "Need to give as argument to applyPartial" ∷ [])}
    unify productType argType
    -- goalType ← extendContext (vArg productType) (newMeta (quoteTerm Set))
    unify funType (pi (vArg productType) goalAbs)

    -- Run the given macro in the extended context
    funBody <- extendContext (vArg productType) do
      goalType ← case goalAbs of λ
        { (abs _ goalType) → return goalType }
    -- hole ← newMeta goalType
      debugPrint "Leftovers" 2 (strErr "goalType before run theMacro" ∷ termErr goalType ∷ [])
      (body , allMetas) ← L.runLeftovers
        ((L.freshMeta goalType) L.>>=
        λ hole → theMacro hole L.>> L.pure hole)
      -- body <- newMeta goalType
      debugPrint "Hello" 2 (strErr "Ran macro, body var is " ∷ termErr body ∷ [])
      -- L.runLeftovers (theMacro body)

      --Now we see what holes are left
      normBody <- normalise body -- body
      debugPrint "Hello" 2 (strErr "normalised MacroBody " ∷ termErr normBody ∷ [])
      let
        handleMetas : _ → Meta → Data.Maybe.Maybe L.Hole
        handleMetas ctx m = just (L.mkHole (meta m (vArg (var 0 []) ∷ List.map proj₂ ctx)) (List.map proj₂ ctx))
          --
      -- debugPrint "L" 2 (strErr "Before ALLMETAS " ∷ [])
      -- debugPrint "L" 2 (strErr "ALLMETAS " ∷ List.map (λ x → strErr (showTerm (L.Hole.hole x))) allMetas)
      -- normMetas ← forM allMetas λ hole → do
      --   debugPrint "L" 2 (strErr ("normalizing " String.++ (showTerm (L.Hole.hole hole))) ∷ [])
      --   inContext (L.Hole.context hole) (normalise (L.Hole.hole hole))
      debugPrint "L" 2 (strErr "After ALLMETAS " ∷ [])
      -- debugPrint "L" 2 (strErr "ALLMETAS NORM " ∷ List.map termErr normMetas)
      metaList ←
          forM allMetas λ hole → inContext (L.Hole.context hole) do
            debugPrint "L" 2 (strErr "getting subMetas from" ∷ strErr (showTerm (L.Hole.hole hole)) ∷ [])
            nf ← normalise (L.Hole.hole hole)
            debugPrint "L" 2 (strErr ("normalized " String.++ (showTerm (L.Hole.hole hole)) String.++  " to ") ∷ termErr nf ∷ [])
            return (case nf of λ
              {(meta x args)
                →  [ hole ]
              ;_ →
                    collectFromSubterms
                      (record
                        { onVar = λ _ _ → nothing
                        ; onMeta = handleMetas
                        ; onCon = λ _ _ → nothing
                        ; onDef = λ _ _ → nothing }) nf
              } )
      let
        metas = List.deduplicate L.equivDec (List.concat metaList)
        indexedMetas = (Vec.zip (Vec.allFin _) (Vec.fromList metas))
      debugPrint "Leftovers" 2 (strErr "All holes " ∷ [])
      -- debugPrint "Leftovers" 2 (strErr "All holes " ∷ List.map (λ m → termErr (L.Hole.hole m)) metas)
      -- Now we know how many elements are in our Product
      unify (lit (nat (List.length metas))) numHoles

      debugPrint "Leftovers" 2 (strErr "Unified num holes " ∷ [])
      -- Function to get the ith metavariable from the argument
      -- accessor i as = projₙ (List.length metas) {ls = nSet} {as = as} i
      holeTypes <- VCat.TraversableM.forM {a = Level.zero} {n = List.length metas} tcMonad indexedMetas
        λ {(i , hole) →  inferHoleType hole }
      debugPrint "Leftovers" 2 (strErr "Got holes types " ∷ [])
      -- debugPrint "Hello" 2 (strErr "Got hole types" ∷ List.map termErr (Vec.toList holeTypes))
      let setsFromTypes = quoteSets holeTypes
      debugPrint "Hello" 2 (strErr "Made sets " ∷ strErr (showTerm setsFromTypes) ∷ [])
      levelsFromTypes ← quoteLevels holeTypes
      debugPrint "Hello" 2 (strErr "Made levels " ∷ [])
      debugPrint "Hello" 2 (strErr "Made levels " ∷ strErr (showTerm levelsFromTypes) ∷ [])
      -- Now we know the types of our holes
      unify sets setsFromTypes
      unify levels levelsFromTypes
    -- Replace the ith meta with the ith element of the HList
      forM (Vec.toList indexedMetas) λ ( i , hole ) → inContext (L.Hole.context hole) do
      -- let lhs = (meta mt (List.map proj₂ ctx))
        let
          holeCtx = L.Hole.context hole
          numArgs = length holeCtx - 1
          rhs =
            (def (quote nthHole)
              (vArg (lit (nat (List.length metas)))
              -- ∷ hArg (quoteTerm nSet)
              ∷ hArg levels
              ∷ hArg sets
              ∷ vArg (Data.Fin.Reflection.toTerm i)
              --TODO hidden args for context vars?
              ∷ vArg (var numArgs [])
              ∷ (List.map (λ n → vArg (var n [])) (List.upTo numArgs))))
        debugPrint "Hello" 2 (strErr "Unify LHS " ∷ strErr (showTerm (L.Hole.hole hole)) ∷ [] )
        debugPrint "Hello" 2 (strErr "Unify RHS " ∷ strErr (showTerm rhs) ∷ [] )
        unify (L.Hole.hole hole) rhs
      return body
    --Produce the function that gives the result of the last macro
    unify goal (lam visible (abs "holes" funBody))
    -- finalResult ← reduce goal
    -- debugPrint "Hello" 2 (strErr "Final Result" ∷ termErr finalResult ∷ [])
    -- return tt


  where

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

-- infixr 10 [_⇒_]

by : ∀ {ℓ} {A : Set ℓ} {n} {ls} {types : Sets n ls}
  → (theMacro : Term → L.Leftovers ⊤)
  → {@(tactic findLeftovers theMacro) f : Holes n ls types → A}
  → Product n types → A
by {n = n} _ {f} x = f (makeHoles x)

-- by {n = n} _ {f} = curryₙ n (λ x → f (makeHoles x))

-- syntax withLeftovers tac x = ► tac ⇒ x ◄
