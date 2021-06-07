{-# OPTIONS --without-K #-}
module Leftovers.TraverseTerm where

open import Data.List
-- We only need the writer monad, but as far as I can tell
-- it's not in the Agda stdlib
open import Category.Monad.State

open import Reflection using (Term ; Meta ; Name ; Arg)
import Leftovers.Everywhere

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

collectFromSubterms : ∀ {A : Set} → LeafInfoMaker A → Term → List A
collectFromSubterms {A} f t = proj₂ (stateResult [])
 where
   open RawMonadState (StateMonadState (List A))
   open import Leftovers.Everywhere (StateMonad (List A))

   toAction : ∀ {X : Set} → (LCxt → X → Maybe A) → Action X
   toAction f cxt x with f (Cxt.context cxt) x
   ... | nothing = return x
   ... | just fx =
     do
       modify (fx ∷_)
       return x

   stateResult : State (List A) Term
   stateResult =
        everywhere (record
          { onVar = toAction (LeafInfoMaker.onVar f)
          ; onMeta = toAction (LeafInfoMaker.onMeta f)
          ; onCon = toAction (LeafInfoMaker.onCon f)
          ; onDef = toAction (LeafInfoMaker.onDef f) }) (λ Γ x → return x) t
