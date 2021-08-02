
{-# OPTIONS -v 2 --auto-inline #-}
module Leftovers.Examples.Examples where

open import Leftovers.Leftovers

-- open import Leftovers.Utils
-- open import Leftovers.FindHoles
-- open import Leftovers.Equality

open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Product

open import Data.Unit
open import Data.List using (_∷_ ; [])

open import Reflection
open import Function
open import Data.Nat


-- notNot :  ∀ b → not (not b) ≡ b
-- notNot = (by {A = ∀ b → not (not b) ≡ b} (quote notNot) (cases (quote Bool)) (refl , refl) ) -- (refl , refl)

-- applyTo : ∀ {ℓ1 ℓ2} {X : Set ℓ1} { Y : Set ℓ2 } → (X → Y) → X → Y
-- applyTo f x = f x

-- infixr 40 applyTo
-- syntax applyTo e₁ (λ x → e₂) = x ≔ e₁ ︔ e₂

open import Leftovers.Internal.Proofs
open import Data.List.Any

-- This one works and passes the termination checker
plusZero : ∀ n → n ≡ n + 0
plusZero = helper
  where
    proof : IndProof (∀ n → n ≡ n + 0)
    proof =
      prove (∀ n → n ≡ n + 0 ) byInduction (cases (quote ℕ)) ⦊
      DoCase zero by
        (default (λ {_ : (n : ℕ) → n ≡ n + 0} → refl {x = 0})) ⦊
      ExactCase-syntax (λ suc → λ {rec} x → cong {!suc!} {!!})  ∎
      -- (nextBy manual (λ {self} x → cong suc (self x)) ⦊
      -- (nextBy manual refl ⦊ ∎ ))
    helper : ∀ n → n ≡ n + 0
    -- unquoteDef helper = runIndProof helper proof

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
