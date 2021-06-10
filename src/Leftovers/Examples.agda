
{-# OPTIONS -v 2 --auto-inline #-}
module Leftovers.Examples where

open import Leftovers.Utils
open import Leftovers.Leftovers
open import Leftovers.Equality

open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Product

open import Data.Unit
open import Data.List using (_∷_ ; [])

open import Reflection
open import Function

-- notNot :  ∀ b → not (not b) ≡ b
-- notNot = (by {A = ∀ b → not (not b) ≡ b} (quote notNot) (cases (quote Bool)) (refl , refl) ) -- (refl , refl)

-- applyTo : ∀ {ℓ1 ℓ2} {X : Set ℓ1} { Y : Set ℓ2 } → (X → Y) → X → Y
-- applyTo f x = f x

-- infixr 40 applyTo
-- syntax applyTo e₁ (λ x → e₂) = x ≔ e₁ ︔ e₂

-- This one works and passes the termination checker
plusZero : ∀ n → n ≡ n + 0
plusZero = λ { zero → refl
             ; (suc arg0) → cong suc (plusZero arg0)
             }

-- This produces the exact same term as above, but doesn't pass the checker
-- Even though all it's doing is defining the exact same term
mkDef : Name → TC ⊤
mkDef nm = do
  ty ← inferType (def nm [])
  debugPrint "" 2 (strErr "got ty (" ∷ termErr ty ∷ strErr ") for name " ∷ nameErr nm ∷ [])
  subbedTerm ← runSpeculative $ do
    ret ← subName nm (λ (self : ∀ n → n ≡ n + 0) → the (∀ n → n ≡ n + 0) λ
                     { zero → refl
                     ; (suc arg0) → (cong suc (self arg0)) })
    nf ← normalise ret
    return (nf , false)
  clauses ← case subbedTerm of λ
    { (pat-lam clauses types) → return clauses
    ; _ → typeError (strErr "result was not pat-lam " ∷ termErr subbedTerm ∷ []) }
  debugPrint "mkDef" 2 (strErr "Subbed term " ∷ termErr subbedTerm ∷ [])
  defineFun nm clauses
  return tt

plusZero' : ∀ n → n ≡ n + 0
unquoteDef plusZero' = mkDef plusZero'

-- plusZero : ∀ n → n ≡ n + 0
-- unquoteDef plusZero = defineBy {A = ∀ n → n ≡ n + 0} plusZero (cases (quote ℕ)) (λ {self} → (λ x → cong suc (self x)) , refl)
-- plusZero =
--    (by {A = ∀ n → n ≡ n + 0} (quote plusZero) (cases (quote ℕ)) (λ {self} → (λ x → cong suc (self x)) , refl) )
   -- (by {A = ∀ n → n ≡ n + 0} (cases (quote ℕ)) ((λ x → cong suc (plusZero x)) , refl))

-- plusZero' : ∀ n → n ≡ n + 0
-- plusZero' = doRun {A = ∀ n → n ≡ n + 0} ( return ( quoteTerm λ { zero → the (zero ≡ zero + 0) refl
--                  ; (suc arg0)
--                      → the (suc arg0 ≡ suc arg0 + 0) (cong suc (plusZero' arg0))
--                  }))


-- plusZero' : ∀ n → n ≡ n + 0
-- plusZero' = getNormal
--   ((the ((zero ≡ zero × (∀ x → suc x ≡ suc x + 0)) → ∀ n → n ≡ n + 0) λ h → identity (λ { zero → proj₁ h ; (suc x) → (proj₂ h) x }))
--     (refl , λ x → cong suc (plusZero' x)))

-- -- plusZero'' : ∀ n → n ≡ n + 0
-- -- plusZero'' = (the (zero ≡ zero → (∀ x → suc x ≡ suc x + 0) → ∀ n → n ≡ n + 0) λ h1 h2 → (λ { zero → h1 ; (suc x) → h2 x})) refl  ((the (Dummy → ∀ x → suc x ≡ suc x + 0) (λ {dummy → λ x → cong suc (plusZero'' x)})) dummy)

-- -- plusZero' =
-- --   let
-- --     h : (zero ≡ zero × ∀ n → suc n ≡ (suc n) + 0)
-- --     h = refl , λ n → cong suc (plusZero' n)
-- --   in λ { zero → proj₁ h ; (suc x) → (proj₂ h) x}
-- -- plusZeroR : ∀ n → n + 0 ≡ n
-- -- plusZeroR = by (refl-cases (quote ℕ)) ?
