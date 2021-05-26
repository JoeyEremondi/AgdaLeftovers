{-# OPTIONS --without-K -v 2 #-}
module Leftovers.Monad where


open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Level
open import Data.Unit

open import Data.List
import Reflection as TC
open import Reflection.TypeChecking.Monad.Instances

open import Reflection.Abstraction as Abstraction public
  using (Abs; abs)
open import Reflection.Argument as Argument public
  using (Arg; arg; Args; vArg; hArg; iArg)
open import Reflection.Definition as Definition  public
  using (Definition)
open import Reflection.Meta as Meta public
  using (Meta)
open import Reflection.Name as Name public
  using (Name; Names)
open import Reflection.Literal as Literal public
  using (Literal)
open import Reflection.Pattern as Pattern public
  using (Pattern)
open import Reflection.Term as Term public
  using (Term; Type; Clause; Clauses; Sort)

open import Reflection using (ErrorPart ; strErr; termErr ; nameErr) public

open import Data.Bool

import Reflection.Argument.Relevance as Relevance
import Reflection.Argument.Visibility as Visibility
import Reflection.Argument.Information as Information

open Definition.Definition public
open Information.ArgInfo public
open Literal.Literal public
open Relevance.Relevance public
open Term.Term public
open Visibility.Visibility public


private
  variable
    ℓ : Level
    A : Set ℓ
    B : Set ℓ

record Hole : Set  where
  constructor mkHole
  field
    hole : Term
    context : List (Arg Type)

open import Category.Monad.State
open import Category.Monad.Indexed using (RawIMonad ; RawIMonadPlus)
open import Category.Applicative.Indexed using (RawIApplicative ; RawIAlternative)
open import Data.Product using (_×_ ; _,_)

Leftovers : Set ℓ  → Set ℓ
Leftovers = StateT (Lift _ (List Hole)) TC.TC


leftoversMonad : RawMonad {f = ℓ}  Leftovers
leftoversMonad = StateTMonad _ tcMonad

leftoversApplicative : RawApplicative {f = ℓ}  Leftovers
leftoversApplicative = RawIMonad.rawIApplicative leftoversMonad

leftoversFunctor : RawFunctor {ℓ = ℓ}  Leftovers
leftoversFunctor = RawIApplicative.rawFunctor leftoversApplicative


leftoversMonadZero : RawMonadZero {f = ℓ} Leftovers
leftoversMonadZero = StateTMonadZero _ tcMonadZero

leftoversMonadPlus : RawMonadPlus {f = ℓ}  Leftovers
leftoversMonadPlus = StateTMonadPlus _ tcMonadPlus

private

  -- Lift a TC operation into the Leftovers Monad
  -- WARNING: this will *NOT* track metas declared in the TC operation
  -- and should only be used for primitive operations
  liftTC :  TC.TC A → Leftovers A
  liftTC comp s = TC.bindTC comp λ a → TC.return (a , s)


  liftTCA1 : (B → TC.TC A) → B → Leftovers A
  liftTCA1 comp x  = liftTC (comp x)


  liftTCA2 : ∀ {A B C : Set ℓ} → (C → B → TC.TC A) → C → B → Leftovers A
  liftTCA2 comp x y = liftTC (comp x y)
------------------------------------------------------------------------
-- Monad syntax

returnLeftovers : A → Leftovers A
returnLeftovers = RawMonad.return leftoversMonad

bindLeftovers : ∀ {A B : Set ℓ } ->  Leftovers A → (A → Leftovers B)  → Leftovers B
bindLeftovers a f = RawMonad._=<<_ leftoversMonad f a

pure : A → Leftovers A
pure = returnLeftovers
{-# INLINE pure #-}

infixl 3 _<|>_
_<|>_ : Leftovers A → Leftovers A → Leftovers A
_<|>_ = RawIAlternative._∣_ (RawIMonadPlus.alternative leftoversMonadPlus)
{-# INLINE _<|>_ #-}

infixl 1 _>>=_ _>>_ _<&>_
_>>=_ : ∀ {A B : Set ℓ} → Leftovers A → (A → Leftovers B) → Leftovers B
_>>=_ = bindLeftovers
{-# INLINE _>>=_ #-}

_>>_ : ∀ {A B : Set ℓ} → Leftovers A → Leftovers B → Leftovers B
xs >> ys = bindLeftovers xs (λ _ → ys)
{-# INLINE _>>_ #-}

infixl 4 _<$>_ _<*>_ _<$_
_<*>_ : ∀ {A B : Set ℓ} → Leftovers (A → B) → Leftovers A → Leftovers B
fs <*> xs = bindLeftovers fs (λ f → bindLeftovers xs (λ x → returnLeftovers (f x)))
{-# INLINE _<*>_ #-}

_<$>_ : ∀ {A B : Set ℓ} →(A → B) → Leftovers A → Leftovers B
f <$> xs = bindLeftovers xs (λ x → returnLeftovers (f x))
{-# INLINE _<$>_ #-}

_<$_ : ∀ {A B : Set ℓ} →A → Leftovers B → Leftovers A
x <$ xs = bindLeftovers xs (λ _ → returnLeftovers x)
{-# INLINE _<$_ #-}

_<&>_ : ∀ {A B : Set ℓ} → Leftovers A → (A → B) → Leftovers B
xs <&> f = bindLeftovers xs (λ x → returnLeftovers (f x))
{-# INLINE _<&>_ #-}

logHole : Hole → Leftovers ⊤
logHole hole = do
  RawMonadState.modify (StateTMonadState _ tcMonad) λ { (lift lst) → lift (hole ∷ lst)}
  pure tt
-- logHole hole = RawMonadState.modify (StateTMonadState _ tcMonad)
--   (λ {lst → ?})
--   pure tt

freshMeta : Type → Leftovers Term
freshMeta t = do
  theMeta ← liftTC (TC.newMeta t)
  ctx ← liftTC TC.getContext
  logHole (mkHole theMeta ctx)
  pure theMeta

open import Data.String



-- Re-export all of the TC functions
unify            : Term → Term → Leftovers ⊤
unify = liftTCA2 TC.unify

typeError        : ∀ {A : Set ℓ} → List TC.ErrorPart → Leftovers A
typeError x = liftTC (TC.typeError x)

inferType        : Term → Leftovers Type
inferType = liftTCA1 TC.inferType

checkType        : Term → Type → Leftovers Term
checkType = liftTCA2 TC.checkType

normalise        : Term → Leftovers Term
normalise = liftTCA1 TC.normalise

reduce           : Term → Leftovers Term
reduce = liftTCA1 TC.reduce

catchLeftovers          : ∀  {A : Set ℓ} → Leftovers A → Leftovers A → Leftovers A
catchLeftovers comp fallback s =
  --We revert any state changes if we have to go to the fallback
  TC.catchTC (comp s) (fallback s)

quoteLeftovers          : ∀  {A : Set ℓ} → A → Leftovers Term
quoteLeftovers = liftTCA1 TC.quoteTC

unquoteLeftovers        : ∀  {A : Set ℓ} → Term → Leftovers A
unquoteLeftovers = liftTCA1 TC.unquoteTC

getContext       : Leftovers (List (Arg Type))
getContext = liftTC TC.getContext

extendContext    : ∀  {A : Set ℓ} → Arg Type → Leftovers A → Leftovers A
extendContext x comp s = TC.extendContext x (comp s)

inContext        : ∀  {A : Set ℓ} → List (Arg Type) → Leftovers A → Leftovers A
inContext ctx comp s = TC.inContext ctx (comp s)

freshName        : String → Leftovers Name
freshName = liftTCA1 TC.freshName

declareDef       : Arg Name → Type → Leftovers ⊤
declareDef = liftTCA2 TC.declareDef

declarePostulate : Arg Name → Type → Leftovers ⊤
declarePostulate = liftTCA2 TC.declarePostulate

defineFun        : Name → List Clause → Leftovers ⊤
defineFun = liftTCA2 TC.defineFun

getType          : Name → Leftovers Type
getType = liftTCA1 TC.getType

getDefinition    : Name → Leftovers Definition
getDefinition = liftTCA1 TC.getDefinition

blockOnMeta      : ∀  {A : Set ℓ} → Meta → Leftovers A
blockOnMeta = liftTCA1 TC.blockOnMeta

--TODO: is there state stuff to do here?
commitLeftovers         : Leftovers ⊤
commitLeftovers = liftTC TC.commitTC

isMacro          : Name → Leftovers Bool
isMacro = liftTCA1 TC.isMacro

open import Data.Nat

  -- If the argument is 'true' makes the following primitives also normalise
  -- their results: inferType, checkType, quoteLeftovers, getType, and getContext
withNormalisation : ∀ {a} {A : Set a} → Bool → Leftovers A → Leftovers A
withNormalisation flag comp s = TC.withNormalisation flag (comp s)

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
debugPrint : String → ℕ → List TC.ErrorPart → Leftovers ⊤
debugPrint s n err = liftTC (TC.debugPrint s n err)

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
noConstraints : ∀ {a} {A : Set a} → Leftovers A → Leftovers A
noConstraints comp s = TC.noConstraints (comp s)

  -- Run the given Leftovers action and return the first component. Resets to
  -- the old Leftovers state if the second component is 'false', or keep the
  -- new Leftovers state if it is 'true'.
runSpeculative : ∀ {a} {A : Set a} → Leftovers (A × Bool) → Leftovers A
runSpeculative comp oldState =
  TC.bindTC
    (TC.runSpeculative (TC.bindTC (comp oldState) λ{((a , flag) , midState) → TC.return (((a , flag) , midState) , flag)}))
    λ {
      -- Only keep state if the computation succeeds
      ((a , false) , newState) → TC.return ((a , oldState)) ;
      ((a , true) , newState) → TC.return (a , newState)}

runLeftovers : Leftovers A → TC.TC (A × List Hole)
runLeftovers comp  = TC.bindTC (comp (lift []))
  ((λ { (a , lift holes) → TC.return (a , holes) }) )
