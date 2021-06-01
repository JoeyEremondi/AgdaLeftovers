{-# OPTIONS --without-K #-}
module Leftovers.Leftovers where


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


record MetaInContext : Set where
  constructor Cmeta
  field
    context : LCxt
    unapplied : Term
    applied : Term

open import Data.Empty
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Definitions as D

EquivMeta : ∀ (x y : MetaInContext) → Set
EquivMeta (Cmeta _ (meta x _) _) (Cmeta _ (meta y _) _) = x Eq.≡ y
EquivMeta (Cmeta _ x _) (Cmeta _ y _) = ⊥

open import Relation.Nullary using (yes ; no)

equivDec : D.Decidable EquivMeta
equivDec (Cmeta _ (meta x _) _) (Cmeta _ (meta y _) _) = x Meta.≟ y
  where import Reflection.Meta as Meta
equivDec (Cmeta _ (var x args) _) (Cmeta _ y _) =  no (λ z → z)
equivDec (Cmeta _ (con c args) _) (Cmeta _ y _) = no (λ z → z)
equivDec (Cmeta _ (def f args) _) (Cmeta _ y _) = no (λ z → z)
equivDec (Cmeta _ (lam v t) _) (Cmeta _ y _) = no (λ z → z)
equivDec (Cmeta _ (pat-lam cs args) _) (Cmeta _ y _) = no (λ z → z)
equivDec (Cmeta _ (pi a b) _) (Cmeta _ y _) = no (λ z → z)
equivDec (Cmeta _ (sort s) _) (Cmeta _ y _) = no (λ z → z)
equivDec (Cmeta _ (lit l) _) (Cmeta _ y _) = no (λ z → z)
equivDec (Cmeta _ unknown _) (Cmeta _ y _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ (var x₂ args) _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ (con c args) _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ (def f args) _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ (lam v t) _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ (pat-lam cs args) _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ (pi a b) _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ (sort s) _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ (lit l) _) = no (λ z → z)
equivDec (Cmeta _ (meta x x₁) _) (Cmeta _ unknown _) = no (λ z → z)

import Leftovers.Monad as L

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
      -- L.runLeftovers (theMacro body)

      --Now we see what holes are left
      normBody <- normalise body -- body
      -- debugPrint "Hello" 2 (strErr "MacroBody " ∷ termErr body ∷ [])
      -- debugPrint "Hello" 2 (strErr "normalised MacroBody " ∷ termErr normBody ∷ [])
      let
        handleMetas : _ → Meta → Data.Maybe.Maybe MetaInContext
        handleMetas ctx m = just (record
          {context = ctx
          ; unapplied = meta m (vArg (var 0 []) ∷ [])
          ; applied = meta m (vArg (var 0 []) ∷ (List.map proj₂ ctx))}) -- just (record {context = ctx (meta m (vArg (var 0 []) ∷ [])) ?})
          --
      debugPrint "L" 2 (strErr "ALLMETAS " ∷ List.map (λ x → termErr (L.Hole.hole x)) allMetas)
      normMetas ← forM allMetas (λ hole → normalise (L.Hole.hole hole))
      debugPrint "L" 2 (strErr "ALLMETAS NORM " ∷ List.map termErr normMetas)
      metaList ←
          forM allMetas λ hole → do
            nf ← inContext (L.Hole.context hole) (normalise (L.Hole.hole hole))
            case nf of λ
              {(meta x args) → return [ Cmeta (List.map (λ x → "arg" , x) (L.Hole.context hole)) (meta x []) (meta x args)   ]
              ;_ → do
                let
                  metas =
                    collectFromSubterms
                      (record
                        { onVar = λ _ _ → nothing
                        ; onMeta = handleMetas
                        ; onCon = λ _ _ → nothing
                        ; onDef = λ _ _ → nothing }) nf
                return (List.map (λ (Cmeta ctx a b) → Cmeta (ctx List.++ List.map (λ x → "arg" , x) (L.Hole.context hole)) a b) metas)
              }
      let
        metas = List.deduplicate equivDec (List.concat metaList)
        indexedMetas = (Vec.zip (Vec.allFin _) (Vec.fromList metas))
      debugPrint "Leftovers" 2 (strErr "All holes " ∷ List.map (λ m → termErr (MetaInContext.applied m)) metas)
      -- Now we know how many elements are in our Product
      unify (lit (nat (List.length metas))) numHoles

      -- Function to get the ith metavariable from the argument
      -- accessor i as = projₙ (List.length metas) {ls = nSet} {as = as} i
      holeTypes <- VCat.TraversableM.forM {a = Level.zero} {n = List.length metas} tcMonad indexedMetas
        λ {(i , Cmeta ctx  m mapp) → inferType mapp}
      debugPrint "Hello" 2 (strErr "Got hole types" ∷ List.map termErr (Vec.toList holeTypes))
      let setsFromTypes = quoteSets holeTypes
      debugPrint "Hello" 2 (strErr "Made sets" ∷ termErr setsFromTypes ∷ [])
      levelsFromTypes ← quoteLevels holeTypes
      debugPrint "Hello" 2 (strErr "Made levels" ∷ termErr levelsFromTypes ∷ [])
      -- Now we know the types of our holes
      unify sets setsFromTypes
      unify levels levelsFromTypes
    -- Replace the ith meta with the ith element of the HList
      forM (Vec.toList indexedMetas) λ ( i , (Cmeta ctx mt mtApp) ) → do
      -- let lhs = (meta mt (List.map proj₂ ctx))
        let
          rhs =
            (def (quote nthHole)
              (vArg (lit (nat (List.length metas)))
              -- ∷ hArg (quoteTerm nSet)
              ∷ hArg levels
              ∷ hArg sets
              ∷ vArg (Data.Fin.Reflection.toTerm i)
              ∷ vArg (var 0 [])
              ∷ []))
        debugPrint "Hello" 2 (strErr "Unify RHS" ∷ termErr rhs ∷ [] )
        unify mtApp rhs
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
