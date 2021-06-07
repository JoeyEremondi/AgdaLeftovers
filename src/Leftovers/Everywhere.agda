------------------------------------------------------------------------
-- The Agda standard library
--
-- de Bruijn-aware generic traversal of reflected terms.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Category.Applicative using (RawApplicative)
open import Category.Monad using (RawMonad)

module Leftovers.Everywhere {F : Set → Set} (MF : RawMonad F) where

open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.List    using (List; []; _∷_; _++_; reverse; length)
open import Data.Product using (_×_; _,_)
open import Data.String  using (String)
open import Function     using (_∘_)
open import Reflection

open RawMonad MF

------------------------------------------------------------------------
-- Context representation

-- Track both number of variables and actual context, to avoid having to
-- compute the length of the context everytime it's needed.
record Cxt : Set where
  constructor _,,_
  pattern
  field
    len     : ℕ
    context : List (String × Arg Term)

private
  _∷cxt_ : String × Arg Term → Cxt → Cxt
  e ∷cxt (n ,, Γ) = (suc n ,, (e ∷ Γ))

  _++cxt_ : List (String × Arg Term) → Cxt → Cxt
  es ++cxt (n ,, Γ) = ((length es + n) ,, (es ++ Γ))

------------------------------------------------------------------------
-- Actions

Action : Set → Set
Action A = Cxt → A → F A
-- A traversal gets to operate on variables, metas, and names.
record Actions : Set where
  field
    onVar  : Action ℕ
    onMeta : Action Meta
    onCon  : Action Name
    onDef  : Action Name

-- Default action: do nothing.
defaultActions : Actions
defaultActions .Actions.onVar  _ = pure
defaultActions .Actions.onMeta _ = pure
defaultActions .Actions.onCon  _ = pure
defaultActions .Actions.onDef  _ = pure

------------------------------------------------------------------------
-- Traversal functions
private
 module Params (actions : Actions) (everyAction : Action Term) where

  open Actions actions

  everywhereTerm    : Action Term
  everywhereTerm'    : Action Term
  everywhereSort    : Action Sort
  everywherePattern : Action Pattern
  everywhereArgs    : Action (List (Arg Term))
  everywhereArg     : Action (Arg Term)
  everywherePats    : Action (List (Arg Pattern))
  everywhereAbs     : Arg Term → Action (Abs Term)
  everywhereClauses : Action Clauses
  everywhereClause  : Action Clause
  everywhereTel     : Action (List (String × Arg Term))

  everywhereTerm Γ t = everyAction Γ =<< everywhereTerm' Γ t

  everywhereTerm' Γ (var x args)      = var       <$> onVar Γ x ⊛ everywhereArgs Γ args
  everywhereTerm' Γ (con c args)      = con       <$> onCon Γ c ⊛ everywhereArgs Γ args
  everywhereTerm' Γ (def f args)      = def       <$> onDef Γ f ⊛ everywhereArgs Γ args
  everywhereTerm' Γ (pat-lam cs args) = pat-lam   <$> everywhereClauses Γ cs ⊛ everywhereArgs Γ args
  everywhereTerm' Γ (pi a b)          = pi        <$> everywhereArg Γ a ⊛ everywhereAbs a Γ b
  everywhereTerm' Γ (agda-sort s)     = agda-sort <$> everywhereSort Γ s
  everywhereTerm' Γ (meta x args)     = meta      <$> onMeta Γ x ⊛ everywhereArgs Γ args
  everywhereTerm' Γ t@(lit _)         = pure t
  everywhereTerm' Γ t@unknown         = pure t
  everywhereTerm' Γ (lam v t)         = lam v     <$> everywhereAbs (arg (arg-info v m) unknown) Γ t
    where
    m = defaultModality

  everywhereArg Γ (arg i t) = arg i <$> everywhereTerm Γ t
  everywhereArgs Γ []       = pure []
  everywhereArgs Γ (a ∷ as) = _∷_ <$> everywhereArg Γ a ⊛ everywhereArgs Γ as

  everywhereAbs ty Γ (abs x t) = abs x <$> everywhereTerm ((x , ty) ∷cxt Γ) t

  everywhereClauses Γ []       = pure []
  everywhereClauses Γ (c ∷ cs) = _∷_ <$> everywhereClause Γ c ⊛ everywhereClauses Γ cs

  everywhereClause Γ (Clause.clause tel ps t) =
      Clause.clause <$> everywhereTel Γ tel
                     ⊛  everywherePats Γ′ ps
                     ⊛ everywhereTerm Γ′ t
    where Γ′ = reverse tel ++cxt Γ
  everywhereClause Γ (Clause.absurd-clause tel ps) =
      Clause.absurd-clause <$> everywhereTel Γ tel
                            ⊛  everywherePats Γ′ ps
    where Γ′ = reverse tel ++cxt Γ

  everywhereTel Γ [] = pure []
  everywhereTel Γ ((x , ty) ∷ tel) =
    _∷_ ∘ (x ,_) <$> everywhereArg Γ ty ⊛ everywhereTel ((x , ty) ∷cxt Γ) tel

  everywhereSort Γ (Sort.set t)       = Sort.set <$> everywhereTerm Γ t
  everywhereSort Γ t@(Sort.lit _)     = pure t
  everywhereSort Γ (Sort.prop t)      = Sort.prop <$> everywhereTerm Γ t
  everywhereSort Γ t@(Sort.propLit _) = pure t
  everywhereSort Γ t@(Sort.inf _)     = pure t
  everywhereSort Γ t@Sort.unknown     = pure t

  everywherePattern Γ (Pattern.con c ps) = Pattern.con <$> onCon Γ c ⊛ everywherePats Γ ps
  everywherePattern Γ (Pattern.dot t)    = Pattern.dot <$> everywhereTerm Γ t
  everywherePattern Γ (Pattern.var x)    = Pattern.var <$> onVar Γ x
  everywherePattern Γ p@(Pattern.lit _)  = pure p
  everywherePattern Γ p@(Pattern.proj _) = pure p
  everywherePattern Γ (Pattern.absurd x) = Pattern.absurd <$> onVar Γ x

  everywherePats Γ [] = pure []
  everywherePats Γ (arg i p ∷ ps) = _∷_ ∘ arg i <$> everywherePattern Γ p ⊛ everywherePats Γ ps

everywhere : (actions : Actions) → (everyAction : Action Term) → Term → F Term
everywhere actions every = Params.everywhereTerm actions every (0 ,, [])
