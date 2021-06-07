{-# OPTIONS --without-K #-}
module Leftovers.Leftovers where

import Data.String as String

open import Leftovers.TraverseTerm
open import Leftovers.Utils

import Level as Level
open import Reflection
open import Reflection.Term
open import Reflection.TypeChecking.Monad.Instances
open import Reflection.Argument using (unArg)

open import Data.Fin using (toℕ)

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Nat.Show as NShow
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
{-# INLINE getHoles #-}

nthHole : ∀ n {ls} {as : Sets n ls } k → Holes n ls as → Projₙ as k
nthHole n k h = projₙ n k (getHoles h)
{-# INLINE nthHole #-}

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

data Dummy : Set where
  dummy : Dummy



sep : Term → TC Term
sep t = do
  ty ← inferType t
  let ret = (def (quote  identity) [ vArg t ]) ⦂ ty
  return ret

open import Reflection.DeBruijn using (weaken)
open import Leftovers.Everywhere tcMonad

-- Hack using case-lambda to convince Agda that a term is a definition
-- Helps with the termination checker
-- makeDef : Term → TC Term
-- makeDef t = do

--   ty ← inferType t
--   let ret = pat-lam [ clause [] [ vArg (con (quote dummy) []) ] t ] []
--   return (app (def (quote the) (vArg (pi (vArg (quoteTerm Dummy)) (abs "_" (weaken 1 ty))) ∷ vArg ret ∷ [])) (quoteTerm dummy))

getMetas : Term → TC (List L.Hole)
getMetas t = do
    -- body <- newMeta goalType
    debugPrint "Hello" 2 (strErr "Ran macro, body var is " ∷ termErr t ∷ [])
    -- L.runLeftovers (theMacro body)
      --Now we see what holes are left
    normTerm <- normalise t -- body
    debugPrint "Hello" 2 (strErr "normalised MacroBody " ∷ termErr normTerm ∷ [])
    let
        handleMetas : _ → Meta → Data.Maybe.Maybe L.Hole
        handleMetas ctx m = just (L.mkHole (meta m (List.map (λ x → vArg (var x [])) (List.downFrom (length ctx + 1 )))) (List.map proj₂ ctx))
    debugPrint "L" 2 (strErr "After ALLMETAS " ∷ [])
      -- debugPrint "L" 2 (strErr "ALLMETAS NORM " ∷ List.map termErr normMetas)
    let metaList =  (collectFromSubterms
                      (record
                        { onVar = λ _ _ → nothing
                        ; onMeta = handleMetas
                        ; onCon = λ _ _ → nothing
                        ; onDef = λ _ _ → nothing }) normTerm
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
  foldr (λ param ty → pi param (abs "hole" ty)) ty
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

findLeftovers : ∀ {ℓ} → Set ℓ → (Term → L.Leftovers ⊤) → Term → TC ⊤
findLeftovers targetSet theMacro goal =
  do
    startContext ← getContext
    let startCtxLen = List.length startContext
    targetType ← quoteTC targetSet
    -- Unification variable for number of holes, we don't know how many yet
    numHoles ← newMeta (quoteTerm ℕ)
    -- Unification variables for the HVec of holes
    let levelsType = (def (quote Levels) (vArg numHoles ∷ []))
    levels ← newMeta levelsType -- def (quote nSet) [ hArg numHoles ]
    let setsType = (def (quote Sets) (vArg numHoles ∷ vArg levels ∷ []))
    sets ← newMeta setsType
    let productType = def (quote Holes) (vArg numHoles ∷ vArg levels ∷ vArg sets ∷ [])

    -- Make sure the type of the function we produce matches (unifies with)
    -- (Holes -> Target Type)
    let funType = pi (vArg productType) (abs "holes" targetType)
    checkType goal funType
    let extContext = vArg productType ∷ startContext
    let
      contextForHole : L.Hole → List (Arg Type)
      contextForHole hole = (L.Hole.context hole) ++ extContext

    debugPrint "Leftovers" 2 (strErr "Goal function type " ∷ termErr funType ∷ [])
    -- The return type of the function we're producing
    -- (argType , goalAbs) ← case funType of λ
    --   { (pi (arg _ dom) cod) → return (dom , cod)
    --   ; _ → typeError (strErr "Need to give as argument to applyPartial" ∷ [])}
    -- unify productType argType
    -- -- goalType ← extendContext (vArg productType) (newMeta (quoteTerm Set))
    -- unify funType (pi (vArg productType) goalAbs)

    -- Run the given macro on a fresh hole
    -- in a context extended with the argument with the Holes
    debugPrint "Leftovers" 2 (strErr "goalType before run theMacro" ∷ termErr targetType ∷ [])
    (body , metas) ← extendContext (vArg productType)
      do
        (body , _) ← L.runLeftovers
          ((L.freshMeta targetType) L.>>=
          λ hole → theMacro hole L.>> L.pure hole)
        metas ← getMetas body
        return (body , metas)
    let numMetas = length metas
    let metaVec = Vec.fromList metas
    debugPrint "Leftovers" 2 (strErr "All holes " ∷ [])
      -- debugPrint "Leftovers" 2 (strErr "All holes " ∷ List.map (λ m → termErr (L.Hole.hole m)) metas)
      -- Now we know how many arguments we need to take
    debugPrint "Leftovers" 2 (strErr "Unified num holes " ∷ [])
    -- Get the type of each hole *in its context*
    holesWithTypes <- VCat.TraversableM.forM {a = Level.zero} {n = numMetas} tcMonad (metaVec)
      λ hole → inContext (contextForHole hole) do
             debugPrint "" 2 (strErr "Context : " ∷ strErr (String.intersperse ",, " (List.map (λ x → showTerm (unArg x)) (contextForHole hole))) ∷ [])
             debugPrint "" 2 (strErr "Getting type of hole " ∷ termErr ( (L.Hole.hole hole) ) ∷ strErr " !" ∷  [])
             ty ← inferType (L.Hole.hole hole)
             debugPrint "" 2 [ strErr "got type" ]
             return (hole , ty)
    let holeTypes = Vec.map (abstractMetaType startCtxLen) holesWithTypes
    debugPrint "Leftovers" 2 (strErr "Got holes types " ∷ [])
    debugPrint "Hello" 2 (strErr "Got hole types" ∷ List.map termErr (Vec.toList holeTypes))
    let setsFromTypes = quoteSets holeTypes
    debugPrint "Hello" 2 (strErr "Made sets " ∷ strErr (showTerm setsFromTypes) ∷ [])
    levelsFromTypes ← quoteLevels holeTypes
    debugPrint "Hello" 2 (strErr "Made levels " ∷ strErr (showTerm levelsFromTypes) ∷ [])
      -- Now we know the types of our holes
    unify sets setsFromTypes
    unify levels levelsFromTypes
    -- Pair each meta with its index
    let indexedMetas = (Vec.zip (Vec.allFin _) metaVec)
    -- Replace the ith meta with the ith element of the HList
    forM (Vec.toList indexedMetas) λ ( i , hole ) → inContext (contextForHole hole) do
      -- TODO is this bad? why re-infer?
        holeType ← inferType (L.Hole.hole hole)
        let
           holeCtx = L.Hole.context hole
           numArgs = length holeCtx
           rhs =
            (def (quote nthHole)
              (vArg (lit (nat (List.length metas)))
              -- ∷ hArg (quoteTerm nSet)
              ∷ hArg (levels ⦂ levelsType)
              ∷ hArg (sets ⦂ setsType)
              ∷ vArg (Data.Fin.Reflection.toTerm i)
              --TODO hidden args for context vars?
              ∷ vArg (var numArgs [] ⦂ productType)
              ∷ (List.map (λ n → vArg (var n [])) (List.upTo numArgs))))
        debugPrint "Hello" 2 (strErr "Unify LHS " ∷ strErr (showTerm (L.Hole.hole hole)) ∷ [] )
        debugPrint "Hello" 2 (strErr "Unify RHS " ∷ strErr (showTerm rhs) ∷ [] )
        unify (L.Hole.hole hole) (rhs )
        debugPrint "" 2 (strErr "done unify" ∷ [])
      --Hack to help with termination
    let funBody = (body ⦂ targetType)
    debugPrint "" 2 (strErr "done sep" ∷ [])
    -- return (funBody , List.length metas)
    --Produce the function that gives the result of the last macro
    unify goal ((lam visible (abs "holes" funBody)) ⦂ funType )
    finalResult ← reduce goal
    debugPrint "Hello" 2 (strErr "Final Result" ∷ termErr finalResult ∷ [])
    -- return tt


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

-- infixr 10 [_⇒_]

by : ∀ {ℓ} {A : Set ℓ} {n} {ls} {types : Sets n ls}
  → (theMacro : Term → L.Leftovers ⊤)
  → {@(tactic findLeftovers A theMacro) f : Holes n ls types → A}
  → Product n types → A
by {n = n} _ {f} x = f (makeHoles x)



by' : ∀ {ℓ} {A : Set ℓ} {n} {ls} {types : Sets n ls}
  → (theMacro : Term → L.Leftovers ⊤)
  → {@(tactic findLeftovers A theMacro) f : Holes n ls types → A}
  → ⊤ → Product n types → A
by' {n = n} _ {f} _ x = f (makeHoles x)

-- by {n = n} _ {f} = curryₙ n (λ x → f (makeHoles x))

open import Relation.Nullary

-- syntax withLeftovers tac x = ► tac ⇒ x ◄
macro
  getNormal : ∀ {X : Set} → X → Term → TC ⊤
  getNormal {X = X} x goal = do
    t ← quoteTC x
    ttype ← quoteTC X
    checkType goal ttype
    debugPrint "" 2 (strErr "get Normal term " ∷ termErr t ∷ [])
    debugPrint "" 2 (strErr "get Normal term type " ∷ termErr ttype ∷ [])
    goalType ← inferType goal
    debugPrint "" 2 (strErr "get Normal goal type " ∷ termErr goalType ∷ [])
    unify goalType ttype
    nf ← normalise t
    nfSimplified ←  everywhere defaultActions action t
    debugPrint "" 2 (strErr "get Normal term nf " ∷ termErr nf ∷ [])
    unify goal nfSimplified
    where
      open import Reflection.Name as N
      action : Cxt → Term → TC Term
      action ctx t@(def gholes (arg _ arg1 ∷ []) ) = do
        case  (gholes N.≟ quote getHoles) of λ
          { (yes _) → do
            nf1 ← normalise arg1
            case nf1 of λ
              { (def mholes (arg _ tup ∷ [])) →
                case (mholes N.≟ quote makeHoles) of λ
                  {(yes _) → normalise tup
                  ; (no _) → return t}
              ; _ → return t}
          ; (no _) → return t }

      action _ t = return t


  -- applyNormal : ∀ {ℓ1 ℓ2} {X : Set ℓ1} {Y : Set ℓ2} → (X → Y) → X → Term → TC ⊤
  -- applyNormal {X = X} {Y} f x goal = do
  --   goalType ← inferType goal
  --   tX ← quoteTC X
  --   tY ← quoteTC Y
  --   tf ← quoteTC f
  --   tx ← quoteTC x
  --   nf ← normalise (app tf tx)
  --   unify goalType tY
  --   unify nf goal

default : {A : Set} → A → Term → TC ⊤
default x hole = bindTC (quoteTC x) (unify hole)

