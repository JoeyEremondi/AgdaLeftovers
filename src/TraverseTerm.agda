{-# OPTIONS --without-K #-}
module TraverseTerm where

open import Data.List
open import Category.Monad.State

open import Reflection using (Term ; Meta ; Name ; Arg)
import Reflection.Traversal

open import Relation.Binary.PropositionalEquality



open import Data.Product
open import Data.Nat
open import Data.Maybe
open import Data.String

LCxt : Set
LCxt = List (String × Arg Term)

record LeafInfoMaker (A : Set) : Set where
  field
    onVar : LCxt → ℕ → Maybe A
    onMeta : LCxt → Meta → Maybe A
    onCon : LCxt → Name → Maybe A
    onDef : LCxt → Name → Maybe A

collectFromSubterms : ∀ {A} → LeafInfoMaker A → Term → List A
collectFromSubterms {A} f t = proj₂ (stateResult [])
 where
   open RawMonadState (StateMonadState (List A))
   open import Reflection.Traversal rawIApplicative using (traverseTerm ; Action ; Cxt)

   toAction : ∀ {X} → (LCxt → X → Maybe A) → Action X
   toAction f cxt x with f (Cxt.context cxt) x
   ... | nothing = return x
   ... | just fx =
     do
       modify (fx ∷_)
       return x

   stateResult : State (List A) Term
   stateResult =
        traverseTerm (record
          { onVar = toAction (LeafInfoMaker.onVar f)
          ; onMeta = toAction (LeafInfoMaker.onMeta f)
          ; onCon = toAction (LeafInfoMaker.onCon f)
          ; onDef = toAction (LeafInfoMaker.onDef f) }) (0 Reflection.Traversal., []) t
