{-# OPTIONS --without-K #-}
module Leftovers where

import Level as Level
open import Reflection
open import Reflection.Term
open import Reflection.Pattern as P
open import Category.Monad
open import Reflection.TypeChecking.Monad.Instances

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary


open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product
open import Data.List as List
open import Data.Char as Char
open import Data.String as String


import Data.List.Categorical
open Data.List.Categorical.TraversableM {m = Level.zero} tcMonad

open import TraverseTerm
open import Data.Maybe using (just ; nothing)

λv_↦_  λh_↦_ : String → Term → Term
λv x ↦ body  = lam visible (abs x body)
λh x ↦ body  = lam hidden (abs x body)



constructors : Definition → List Name
constructors (data-type pars cs) = cs
constructors _ = []


case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

-- Given a name, get its type
-- and generate _ patterns for each argument
-- e.g. turn (a -> b -> c -> d) into [_ , _ , _]
fully-applied-pattern : Name → TC (List (Arg Pattern))
fully-applied-pattern nm =
  do
    nmType ← getType nm
    return (full-app-type nmType)
  where
    full-app-type : Type → List (Arg Pattern)
    full-app-type (pi (arg info _) (abs s x)) = arg info (var "_") ∷ full-app-type x
    full-app-type t = []

macro
  by-refls : Name → Term → TC ⊤
  by-refls typeName hole -- thm-you-hope-is-provable-by-refls
    = do
      -- let η = nom
      δ ← getDefinition typeName
      clauses ← mapM mk-cls (constructors δ)
      holeType ← inferType hole
      -- declareDef (vArg η) holeType
      let retFun = pat-lam clauses []
      unify hole retFun
    where
      mk-cls : Name → TC Clause
      mk-cls ctor =
         do
           pat <- fully-applied-pattern ctor
           return (clause [ vArg (con ctor pat) ] (con (quote refl) []))
{- Syntactic sugar for trying a computation, if it fails then try the other one -}
try-fun : ∀ {a} {A : Set a} → TC A → TC A → TC A
try-fun = catchTC

syntax try-fun t f = try t or-else f

≡-type-info : Term → TC (Arg Term × Arg Term × Term × Term)
≡-type-info (def (quote _≡_) (𝓁 ∷ 𝒯 ∷ arg _ l ∷ arg _ r ∷ [])) = return (𝓁 , 𝒯 , l , r)
≡-type-info _ = typeError [ strErr "Term is not a ≡-type." ]

{- If we have “f $ args” return “f”. -}
$-head : Term → Term
$-head (var v args) = var v []
$-head (con c args) = con c []
$-head (def f args) = def f []
$-head (pat-lam cs args) = pat-lam cs []
$-head t = t

-- macro
--   apply₄ : Term → Term → TC ⊤
--   apply₄ p goal =
--     try
--       (do
--         τ ← inferType goal
--         _ , _ , l , r ← ≡-type-info τ
--         unify goal ((def (quote cong) (vArg ($-head l) ∷ vArg p ∷ []))))
--     or-else
--       unify goal p


{- Should definitily be in the standard library -}
⌊_⌋ : ∀ {a} {A : Set a} → Dec A → Bool
⌊ yes p ⌋ = true
⌊ no ¬p ⌋ = false

import Agda.Builtin.Reflection as Builtin

_$-≟_ : Term → Term → Bool
con c args $-≟ con c′ args′ = Builtin.primQNameEquality c c′
def f args $-≟ def f′ args′ = Builtin.primQNameEquality f f′
var x args $-≟ var x′ args′ = ⌊ x Nat.≟ x′ ⌋
_ $-≟ _ = false

{- Only gets heads and as much common args, not anywhere deep. :'( -}
infix 5 _⊓_
{-# TERMINATING #-} {- Fix this by adding fuel (con c args) ≔ 1 + length args -}
_⊓_ : Term → Term → Term
l ⊓ r with l $-≟ r | l | r
...| false | x | y = unknown
...| true | var f args | var f′ args′ = var f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | con f args | con f′ args′ = con f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | def f args | def f′ args′ = def f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | ll | _ = ll {- Left biased; using ‘unknown’ does not ensure idempotence. -}

{- ‘unknown’ goes to a variable, a De Bruijn index -}
unknown-elim : ℕ → List (Arg Term) → List (Arg Term)
unknown-elim n [] = []
unknown-elim n (arg i unknown ∷ xs) = arg i (var n []) ∷ unknown-elim (n + 1) xs
unknown-elim n (arg i (var x args) ∷ xs) = arg i (var (n + suc x) args) ∷ unknown-elim n xs
unknown-elim n (arg i x ∷ xs)       = arg i x ∷ unknown-elim n xs
{- Essentially we want: body(unknownᵢ)  ⇒  λ _ → body(var 0)
   However, now all “var 0” references in “body” refer to the wrong argument;
   they now refer to “one more lambda away than before”. -}

unknown-count : List (Arg Term) → ℕ
unknown-count [] = 0
unknown-count (arg i unknown ∷ xs) = 1 + unknown-count xs
unknown-count (arg i _ ∷ xs) = unknown-count xs

unknown-λ : ℕ → Term → Term
unknown-λ zero body = body
unknown-λ (suc n) body = unknown-λ n (λv "section" ↦ body)

{- Replace ‘unknown’ with sections -}
patch : Term → Term
patch it@(def f args) = unknown-λ (unknown-count args) (def f (unknown-elim 0 args))
patch it@(var f args) = unknown-λ (unknown-count args) (var f (unknown-elim 0 args))
patch it@(con f args) = unknown-λ (unknown-count args) (con f (unknown-elim 0 args))
patch t = t


macro
  spine : Term → Term → TC ⊤
  spine p goal =
    do τ ← inferType p
       _ , _ , l , r ← ≡-type-info τ
       unify goal (patch (l ⊓ r))

macro
  applyEq : Term → Term → TC ⊤
  applyEq p hole =
    do
       τ ← inferType hole
       _ , _ , l , r ← ≡-type-info τ
       unify hole ((def (quote cong) (vArg (patch (l ⊓ r)) ∷ vArg p ∷ [])))

open import Function.Nary.NonDependent
open import Data.Product.Nary.NonDependent



data Holes (n : ℕ) (levels : Levels n) (sets : Sets n levels ) : Set (⨆ n levels)    where
  makeHoles : Product n sets → Holes n levels sets

getHoles : ∀ {n ls sets} → Holes n ls sets → Product n sets
getHoles (makeHoles p) = p

nthHole : ∀ n {ls} {as : Sets n ls } k → Holes n ls as → Projₙ as k
nthHole n k h = projₙ n k (getHoles h)


runPartial : ∀ {ℓ} {n} {ls} {types : Sets n ls} {T : Set ℓ} → (Holes n ls types → T) → Product n types → T
runPartial f args = f (makeHoles args)

open import Category.Monad.State
import Category.Monad as Monad


-- apply : ∀ {A B : Set} → (A → B) → A → B
-- apply f x = f x

-- app : Term → Term → Term
-- app x y = def (quote apply) (vArg x ∷ vArg y ∷ [])

record MetaInfo : Set where
  field
   foo : ℕ

import Data.Vec as Vec

import Data.Vec.Categorical as VCat

open import Level.Literals using (#_)

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
-- quoteSets {n = suc n} (x Vec.∷ v) = app (app (quoteTerm (_,_   {A = Set} {B = λ x₁ → Sets n (proj₂ nSet)}  )) x) (quoteSets v)

import Data.Fin.Reflection

record MetaInContext : Set where
  constructor Cmeta
  field
    context : LCxt
    unapplied : Term
    applied : Term

macro
 findUnsolved : (Term → TC ⊤) → Term → TC ⊤
 findUnsolved theMacro goal =
  do
    -- We're producing a function from hole-fills to the goal type
    funType ← inferType goal
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
      body <- newMeta goalType
      theMacro body

      --Now we see what holes are left
      normBody <- normalise body
      debugPrint "Hello" 2 (strErr "MacroBody" ∷ termErr normBody ∷ [])
      let
        handleMetas : _ → Meta → Data.Maybe.Maybe MetaInContext
        handleMetas ctx m = just (record
          {context = ctx
          ; unapplied = meta m (vArg (var 0 []) ∷ [])
          ; applied = meta m (vArg (var 0 []) ∷ (List.map proj₂ ctx))}) -- just (record {context = ctx (meta m (vArg (var 0 []) ∷ [])) ?})
        metas = collectFromSubterms  (record { onVar = λ _ _ → nothing ; onMeta = handleMetas ; onCon = λ _ _ → nothing ; onDef = λ _ _ → nothing }) normBody
        indexedMetas = (Vec.zip (Vec.allFin _) (Vec.fromList metas))

      -- Now we know how many elements are in our Product
      unify (lit (nat (List.length metas))) numHoles

      -- Function to get the ith metavariable from the argument
      -- accessor i as = projₙ (List.length metas) {ls = nSet} {as = as} i
      holeTypes <- VCat.TraversableM.forM {a = Level.zero} {n = List.length metas} tcMonad indexedMetas
        λ {(i , Cmeta ctx  m mapp) → inferType m}
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
        unify mt rhs
      return body
    --Produce the function that gives the result of the last macro
    unify goal (lam visible (abs "holes" funBody))
    finalResult ← reduce goal
    debugPrint "Hello" 2 (strErr "Final Result" ∷ termErr finalResult ∷ [])
    return tt



data Foo : Set (Level.suc Level.zero) where
  Bar : Set → ℕ → ((n : ℕ) → n ≡ n + 0) → Foo

makePair : Term → TC ⊤
makePair = λ goal →
    do
      hole1 <- newMeta (quoteTerm Set)
      hole2 <- newMeta (quoteTerm ℕ)
      hole3 <- newMeta (quoteTerm ((n : ℕ) → n ≡ n + 0))
      body <- extendContext (vArg (quoteTerm ℕ)) do
        tyHole ← newMeta (quoteTerm Set)
        newHole ← newMeta tyHole
        return (def (quote sym) (vArg newHole ∷ []))
      unify hole3 (lam visible (abs "arg" body))
      unify hole2 (quoteTerm 4)
      unify goal (con (quote Bar) (vArg hole1 ∷ vArg hole2 ∷ vArg hole3 ∷ []))

p0 : ∀ n → n + 0 ≡ n
p0 zero = refl
p0 (suc n) rewrite p0 n = refl



f : Foo
f = runPartial (findUnsolved makePair) {!!}
