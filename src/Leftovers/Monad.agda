module Leftovers.Monad where


open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Level
open import Data.Unit

open import Data.List
import Reflection as TC
open import Reflection.TypeChecking.Monad.Instances

open TC using (Term ; Type ; Arg ; Name ; Clause ; Pattern ; Definition ; Meta)
open import Data.Bool

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


tacMonad : RawMonad {f = ℓ}  Leftovers
tacMonad = StateTMonad _ tcMonad

tacApplicative : RawApplicative {f = ℓ}  Leftovers
tacApplicative = RawIMonad.rawIApplicative tacMonad

tacFunctor : RawFunctor {ℓ = ℓ}  Leftovers
tacFunctor = RawIApplicative.rawFunctor tacApplicative


tacMonadZero : RawMonadZero {f = ℓ} Leftovers
tacMonadZero = StateTMonadZero _ tcMonadZero

tacMonadPlus : RawMonadPlus {f = ℓ}  Leftovers
tacMonadPlus = StateTMonadPlus _ tcMonadPlus

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
returnLeftovers = RawMonad.return tacMonad

bindLeftovers : ∀ {A B : Set ℓ } ->  Leftovers A → (A → Leftovers B)  → Leftovers B
bindLeftovers a f = RawMonad._=<<_ tacMonad f a

pure : A → Leftovers A
pure = returnLeftovers
{-# INLINE pure #-}

infixl 3 _<|>_
_<|>_ : Leftovers A → Leftovers A → Leftovers A
_<|>_ = RawIAlternative._∣_ (RawIMonadPlus.alternative tacMonadPlus)
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
