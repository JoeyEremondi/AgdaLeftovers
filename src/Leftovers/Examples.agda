
{-# OPTIONS -v 2 #-}
module Leftovers.Examples where

open import Leftovers.Utils
open import Leftovers.Leftovers
open import Leftovers.Equality

open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Product

open import Data.Unit




notNot :  ∀ b → not (not b) ≡ b
notNot = (by {A = ∀ b → not (not b) ≡ b} (cases (quote Bool)) ?) -- (refl , refl)

-- applyTo : ∀ {ℓ1 ℓ2} {X : Set ℓ1} { Y : Set ℓ2 } → (X → Y) → X → Y
-- applyTo f x = f x

-- infixr 40 applyTo
-- syntax applyTo e₁ (λ x → e₂) = x ≔ e₁ ︔ e₂


-- plusZero : ∀ n → n ≡ n + 0
-- plusZero =
--   getNormal ((by {A = ∀ n → n ≡ n + 0} (cases (quote ℕ))) ((λ ctx → cong suc (plusZero ctx)) , refl))



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
