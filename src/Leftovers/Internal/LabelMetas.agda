{-# OPTIONS --without-K #-}
module Leftovers.Internal.LabelMetas where

open import Reflection as TC hiding (_>>_ ; _>>=_)
open import Data.Product
import Data.String as String
open import Data.String using (String)
open import Data.List as List
open import Category.Monad.State as State
open import Reflection.Term
open import Reflection.TypeChecking.Monad.Instances
open import Reflection.Argument using (unArg)
open import Data.Unit

open import Reflection.Show as Show


private
  record LabelState : Set where
    constructor St
    field
      currentTags : List String
      allTags : List String
      metaLabels : List (Meta × String)


  push : String → LabelState → LabelState
  push s (St current all labels) = St (s ∷ current) all labels

  pop : LabelState → LabelState
  pop (St (_ ∷ current) all labels) = St current all labels
  pop s = s

  addLabel : (Meta × String) → LabelState → LabelState
  addLabel pr (St current all labels) = St current all (pr ∷ labels)

open RawIMonadState (StateTMonadState LabelState tcMonad) renaming (return to sReturn)
open import Leftovers.Internal.Everywhere (State.StateTMonad LabelState tcMonad)

import Data.Char as Char

private
  shortName : Name → String
  shortName n with List.reverse (String.wordsBy (λ c → c Char.≟ '.') (Show.showName n))
  ... | [] = ""
  ... | s ∷ _ = s

  lift : ∀ {A : Set} → TC A → State.StateT LabelState TC A
  lift comp s = comp TC.>>= λ x → return (x , s)

  patString : Arg Pattern → String
  patString (arg i (con c ps)) = shortName c
  patString (arg i (dot t)) = ""
  patString (arg i (var x)) = ""
  patString (arg i (lit l)) = Show.showLiteral l
  patString (arg i (proj f)) = shortName f
  patString (arg i (absurd x)) = ""

  clauseString : Clause → String
  clauseString (clause tel ps t) = String.intersperse "--" (List.map patString ps)
  clauseString (absurd-clause tel ps) = String.intersperse "--" (List.map patString ps)

  beforeAfter : Cxt → BeforeAfter → Cursor → State.StateT LabelState TC ⊤
  beforeAfter _ Before (CClause c) = do
    modify (push (clauseString c))
    lift (debugPrint "" 2 (strErr "Adding ctx " ∷ strErr (clauseString c) ∷ []))
    sReturn tt
  beforeAfter _ After (CClause c) = do
    modify pop
    sReturn tt
  beforeAfter _ _ curs = sReturn tt

  metaAction : Action Meta
  metaAction Γ m = do
    st ← get
    lift (debugPrint "" 2 (strErr "Logging meta " ∷ termErr (meta m []) ∷ []))
    modify (addLabel ((m , String.intersperse "--" (LabelState.currentTags st))))
    sReturn m

eachAction : Term →  State.StateT LabelState TC Term
eachAction t = do
  lift (debugPrint "" 2 (strErr "At term " ∷ termErr t ∷ []))
  sReturn t

labelMetas : Term → TC (List (Meta × String))
labelMetas t =
  contextualEverywhere (record defaultActions {onMeta = metaAction}) beforeAfter (λ _ t → sReturn t) t (St [] [] [])
  TC.>>= λ (_ , ls) → TC.return (LabelState.metaLabels ls)

open import Reflection.Meta as M

labelFor : Meta → List (Meta × String) → String
labelFor m labels with List.filter (λ (m' , _) → m M.≟ m') labels
... | [] = Show.showMeta m
... | (_ , s) ∷ l = s
