{-# OPTIONS --without-K --rewriting --guardedness #-}

module All where

-- The universe of polynomial monads and their families
open import Monad
open import MonadOver
open import SigmaMonad
open import MonadMap

-- Their algebras
open import Algebras
open import AlgebrasOver

-- Opetopic types
open import OpetopicType
open import Sigma

-- Explicit definition of the composition induced by
-- an iterated algebraic family
open import ExplicitComp

-- Equivalence between multicategories and set-truncated fibrant opetopic types
open import Multicategory

-- ∞-categories
open import CategoryTheory.InftyCategory
open import CategoryTheory.Fibrations
open import CategoryTheory.Functor
