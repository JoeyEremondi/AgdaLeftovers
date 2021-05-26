module Leftovers.Monad where


open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.List.Base using ([])
open import Function.Base using (_∘_)
open import Level


open import Data.List
import Reflection as TC
open import Reflection.TypeChecking.Monad.Instances

open TC using (Term ; Type ; Arg)

private
  variable
    ℓ : Level

record Hole : Set ℓ where
  constructor mkHole
  field
    hole : Term
    context : List (Arg Type)

open import Category.Monad.State
open import Category.Monad.Indexed using (RawIMonad)
open import Category.Applicative.Indexed using (RawIApplicative)

Leftovers : Set ℓ → Set ℓ
Leftovers = StateT (List Hole) TC.TC


tacMonad : RawMonad {ℓ} Leftovers
tacMonad = StateTMonad (List Hole) tcMonad

tacApplicative : RawApplicative {ℓ} Leftovers
tacApplicative = RawIMonad.rawIApplicative tacMonad

tacFunctor : RawFunctor {ℓ} Leftovers
tacFunctor = RawIApplicative.rawFunctor tacApplicative


tacMonadZero : RawMonadZero {ℓ} Leftovers
tacMonadZero = StateTMonadZero (List Hole) tcMonadZero

tacMonadPlus : RawMonadPlus {ℓ} Leftovers
tacMonadPlus = StateTMonadPlus (List Hole) tcMonadPlus
