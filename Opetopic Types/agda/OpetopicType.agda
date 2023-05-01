{-# OPTIONS --without-K --rewriting --guardedness #-}

open import HoTT
open import Monad
open import MonadOver

module OpetopicType where

  --
  --  Opetopic Types
  --
  
  record OpetopicType (M : ℳ) : Set (lsucc lzero) where
    coinductive
    field
    
      Ob : Idx M → Set
      Hom : OpetopicType (Slc (Pb M Ob))

  open OpetopicType public

  --
  --  Fibrancy 
  --

  is-algebraic : (M : ℳ) (A : Idx M → Set)
    → (W : Idx (Slc (Pb M A)) → Set)
    → Set
  is-algebraic M A W = {f : Idx M} (σ : Cns M f)
    → (ν : (p : Pos M σ) → A (Typ M σ p))
    → is-contr (Σ (A f) (λ a → W ((f , a) , σ , ν)))

  record is-fibrant {M : ℳ} (X : OpetopicType M) : Set where
    coinductive
    field

      base-fib : is-algebraic M (Ob X) (Ob (Hom X))
      hom-fib : is-fibrant (Hom X)
 
  open is-fibrant public

  --
  --  The terminal opetopic type
  --

  Terminal : (M : ℳ) → OpetopicType M
  Ob (Terminal M) = cst ⊤
  Hom (Terminal M) = Terminal (Slc (Pb M (cst ⊤)))

  Terminal-is-fib : (M : ℳ) → is-fibrant (Terminal M)
  base-fib (Terminal-is-fib M) σ ν = Σ-level Unit-level λ _ → Unit-level
  hom-fib (Terminal-is-fib M) = Terminal-is-fib _

  --
  --  The opetopic type associated to a monad over
  --
  
  ↓-to-OpType : (M : ℳ) (M↓ : ℳ↓ M)
    → OpetopicType M
  Ob (↓-to-OpType M M↓) = Idx↓ M↓ 
  Hom (↓-to-OpType M M↓) =
    ↓-to-OpType (Slc (Pb M (Idx↓ M↓)))
                       (Slc↓ (Pb↓ M↓ (Idx↓ M↓) (λ j k → j == k)))

  --
  -- Opetopic families
  --
  
  record OpetopicType↓ {M : ℳ} (M↓ : ℳ↓ M) (X : OpetopicType M) : Set₁ where
    coinductive
    field

      Ob↓ : {i : Idx M} → Idx↓ M↓ i → Ob X i → Set
      Hom↓ : OpetopicType↓ (Slc↓ (Pb↓ M↓ (Ob X) Ob↓)) (Hom X) 

  open OpetopicType↓ public

  is-algebraic↓ : {M : ℳ} (M↓ : ℳ↓ M)
    → {A : Idx M → Set} (A↓ : {i : Idx M} → Idx↓ M↓ i → A i → Set)
    → {W : Idx (Slc (Pb M A)) → Set}
    → (W↓ : {i : Idx (Slc (Pb M A))} → Idx↓ (Slc↓ (Pb↓ M↓ A A↓)) i → W i → Set)
    → Set
  is-algebraic↓ {M} M↓ {A} A↓ {W} W↓ = {i : Idx M} {i↓ : Idx↓ M↓ i}
    → {σ : Cns M i} (σ↓ : Cns↓ M↓ i↓ σ)
    → {ν : (p : Pos M σ) → A (Typ M σ p)}
    → (ν↓ : (p : Pos M σ) → A↓ (Typ↓ M↓ σ↓ p) (ν p))
    → {a : A i} (w : W ((i , a) , σ , ν))
    → is-contr (Σ (A↓ i↓ a) (λ a → W↓ ((i↓ , a) , σ↓ , ν↓) w))

  record is-fibrant↓ {M : ℳ} {M↓ : ℳ↓ M} {X : OpetopicType M} (X↓ : OpetopicType↓ M↓ X) : Set where
    coinductive
    field

      base-fib↓ : is-algebraic↓ M↓ (Ob↓ X↓) (Ob↓ (Hom↓ X↓))
      hom-fib↓ : is-fibrant↓ (Hom↓ X↓)

  open is-fibrant↓ public
