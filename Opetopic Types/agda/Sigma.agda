{-# OPTIONS --without-K --rewriting --allow-unsolved-meta --guardedness #-}

open import Monad
open import MonadOver
open import OpetopicType
open import SigmaMonad
open import HoTT
open import MonadMap
open import Algebras
open import AlgebrasOver
open import Utils

module Sigma where

  {-# TERMINATING #-}
  Σₒ : {M : ℳ} {M↓ : ℳ↓ M} (X : OpetopicType M)
    → (X↓ : OpetopicType↓ M↓ X)
    → OpetopicType (ΣM M M↓)
  Ob (Σₒ {M} {M↓} X X↓) (i , i↓) = Σ (Ob X i) (Ob↓ X↓ i↓) 
  Hom (Σₒ {M} {M↓} X X↓) =
    reindexₒ (∘⇒ (ΣM⇒-Slc (Pb M (Ob X)) (Pb↓ M↓ (Ob X) (Ob↓ X↓)))
                 (Slc⇒ (ΣM⇒-Pb M M↓ (Ob X) (Ob↓ X↓))))
             (Σₒ {M / Ob X} {M↓ /↓ Ob↓ X↓} (Hom X) (Hom↓ X↓))

  {-# TERMINATING #-}
  Σₒ-is-fibrant : {M : ℳ} {M↓ : ℳ↓ M}
    → (X : OpetopicType M) (X↓ : OpetopicType↓ M↓ X)
    → (X-is-fibrant : is-fibrant X)
    → (X↓-is-fibrant : is-fibrant↓ X↓)
    → is-fibrant (Σₒ X X↓)
  base-fib (Σₒ-is-fibrant {M} {M↓} X X↓ X-is-fibrant X↓-is-fibrant) {i , i↓} (c , c↓) x =
    let open Alg M (base-fib X-is-fibrant)
        open Alg↓ M↓ (base-fib X-is-fibrant) (base-fib↓ X↓-is-fibrant)
        goal : is-contr  (Σ (Σ (Ob X i) (Ob↓ X↓ i↓)) λ (y , y↓) →
                            Σ (Ob (Hom X) ((i , y) , c , fst ∘ x))
                              (Ob↓ (Hom↓ X↓) ((i↓ , y↓) , (c↓ , snd ∘ x))))
        goal =
          equiv-preserves-level
            (Σ-reassoc (Ob X i)
                   (λ a → Ob (Hom X) ((i , a) , c , fst ∘ x))
                   (Ob↓ X↓ i↓)
                   (λ z y↓ → Ob↓ (Hom↓ X↓) ((i↓ , y↓) , c↓ , snd ∘ x) z))
            ⦃ Σ-level (base-fib X-is-fibrant c (fst ∘ x)) λ (a , b) → base-fib↓ X↓-is-fibrant c↓ (snd ∘ x) b ⦄
    in goal
          
  hom-fib (Σₒ-is-fibrant X X↓ X-is-fibrant X↓-is-fibrant) =
    let hyp = Σₒ-is-fibrant (Hom X) (Hom↓ X↓) (hom-fib X-is-fibrant) (hom-fib↓ X↓-is-fibrant)
    in  reindex-alg _ _ hyp 
  
