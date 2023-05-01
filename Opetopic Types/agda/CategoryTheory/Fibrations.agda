{-# OPTIONS --without-K --rewriting --guardedness #-}

open import HoTT
open import OpetopicType
open import Monad
open import MonadOver
open import Algebras
open import AlgebrasOver
open import CategoryTheory.InftyCategory

module CategoryTheory.Fibrations where

  module _ (C@(X , X-fib) : ∞-category) ((X↓ , X↓-fib) :  ∞-category↓ C) where

    open IdentityCells↓ X-fib X↓ X↓-fib
    open SlcAlg (Pb Id (Ob X)) (base-fib X-fib)
    open SlcAlg↓ (Pb↓ (Id↓ ⊤) (Ob X) (Ob↓ X↓)) (base-fib X-fib) (base-fib↓ X↓-fib)
    
    
    is-cartesian : {x y : Obj} {x' : Obj↓ x} {y' : Obj↓ y} {f : Arrow x y} (f' : Arrow↓ x' y' f) → Set
    is-cartesian {x} {y} {x'} {y'} {f} f' = (z : Obj) (z' : Obj↓ z)
      → (g : Arrow z y) (g' : Arrow↓ z' y' g) (h : Arrow z x)
      → (p : μ-alg f (cst h) == g)
      → is-contr (Σ (Arrow↓ z' x' h) λ h' → μ↓-alg f' (cst h') == g' [ Arrow↓ z' y' ↓ p ])

    is-cocartesian : {x y : Obj} {x' : Obj↓ x} {y' : Obj↓ y} {f : Arrow x y} (f' : Arrow↓ x' y' f) → Set
    is-cocartesian {x} {y} {x'} {y'} {f} f' = (z : Obj) (z' : Obj↓ z)
      → (g : Arrow x z) (g' : Arrow↓ x' z' g) (h : Arrow y z)
      → (p : μ-alg h (cst f) == g)
      → is-contr (Σ (Arrow↓ y' z' h) λ h' → μ↓-alg h' (cst f') == g' [ Arrow↓ x' z' ↓ p ])
                     
    is-fibration : Set
    is-fibration = {x y : Obj} (f : Arrow x y)
      → (y' : Obj↓ y)
      → Σ (Obj↓ x) λ x' →
        Σ (Arrow↓ x' y' f) λ f' →
          is-cartesian f'

    is-opfibration : Set
    is-opfibration = {x y : Obj} (f : Arrow x y)
      → (x' : Obj↓ x)
      → Σ (Obj↓ y) λ y' → 
        Σ (Arrow↓ x' y' f) λ f' →
          is-cocartesian f'
