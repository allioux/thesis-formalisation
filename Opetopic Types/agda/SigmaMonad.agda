{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver

module SigmaMonad where

  --
  --  Dependent sum of monads
  --

  module _ (M : ℳ) (M↓ : ℳ↓ M) where

    Idx-Σ : Set
    Idx-Σ = Σ (Idx M) (Idx↓ M↓)

    Cns-Σ : Idx-Σ → Set
    Cns-Σ (i , j) = Σ (Cns M i) (Cns↓ M↓ j) 

    Pos-Σ : {ij : Idx-Σ} → Cns-Σ ij → Set
    Pos-Σ {i , j} (c , d) = Pos M c 

    Typ-Σ : {ij : Idx-Σ} (cd : Cns-Σ ij)
      → Pos-Σ cd → Idx-Σ
    Typ-Σ {i , j} (c , d) p = Typ M c p , Typ↓ M↓ d p
    
    η-Σ : (ij : Idx-Σ) → Cns-Σ ij
    η-Σ (i , j) = η M i , η↓ M↓ j

    η-pos-Σ : (ij : Idx-Σ) → Pos-Σ (η-Σ ij)
    η-pos-Σ (i , j) = η-pos M i 

    η-pos-elim-Σ : (ij : Idx-Σ)
      → (X : (p : Pos-Σ (η-Σ ij)) → Set)
      → (η-pos* : X (η-pos-Σ ij))
      → (p : Pos-Σ (η-Σ ij)) → X p
    η-pos-elim-Σ (i , j) X η-pos* p =
      η-pos-elim M i X η-pos* p

    μ-Σ : {ij : Idx-Σ} (cd : Cns-Σ ij )
      → (δ : (p : Pos-Σ cd) → Cns-Σ (Typ-Σ cd p))
      → Cns-Σ ij
    μ-Σ {i , j} (c , d) δ =
      μ M c (fst ∘ δ) , (μ↓ M↓ d (snd ∘ δ)) 

    μ-pos-Σ : {ij : Idx-Σ} (cd : Cns-Σ ij)
      → (δ : (p : Pos-Σ cd) → Cns-Σ (Typ-Σ cd p))
      → (p : Pos-Σ cd) (q : Pos-Σ (δ p))
      → Pos-Σ (μ-Σ cd δ)
    μ-pos-Σ {i , j} (c , d) δ p q =
      μ-pos M c (fst ∘ δ) p q

    μ-pos-fst-Σ : {ij : Idx-Σ} (cd : Cns-Σ ij)
      → (δ : (p : Pos-Σ cd) → Cns-Σ (Typ-Σ cd p))
      → (p : Pos-Σ (μ-Σ cd δ)) → Pos-Σ cd
    μ-pos-fst-Σ {i , j} (c , d) δ p =
      μ-pos-fst M c (fst ∘ δ) p 

    μ-pos-snd-Σ : {ij : Idx-Σ} (cd : Cns-Σ ij)
      → (δ : (p : Pos-Σ cd) → Cns-Σ (Typ-Σ cd p))
      → (p : Pos-Σ (μ-Σ cd δ))
      → Pos-Σ (δ (μ-pos-fst-Σ cd δ p))
    μ-pos-snd-Σ {i , j} (c , d) δ p =
      μ-pos-snd M c (fst ∘ δ) p

    postulate

      ΣM : ℳ 

      Idx-ΣM : Idx ΣM ↦ Idx-Σ
      {-# REWRITE Idx-ΣM #-}

      Cns-ΣM : (ij : Idx-Σ)
        → Cns ΣM ij ↦ Cns-Σ ij
      {-# REWRITE Cns-ΣM #-} 

      Pos-ΣM : {ij : Idx-Σ} (cd : Cns-Σ ij)
        → Pos ΣM {ij} cd ↦ Pos-Σ cd
      {-# REWRITE Pos-ΣM #-}

      Typ-ΣM : {ij : Idx-Σ} (cd : Cns-Σ ij)
        → (p : Pos-Σ cd)
        → Typ ΣM {ij} cd p ↦ Typ-Σ cd p
      {-# REWRITE Typ-ΣM #-}

      η-ΣM : (ij : Idx-Σ)
        → η ΣM ij ↦ η-Σ ij
      {-# REWRITE η-ΣM #-}

      η-pos-ΣM : (ij : Idx-Σ)
        → η-pos ΣM ij ↦ η-pos-Σ ij
      {-# REWRITE η-pos-ΣM #-}

      η-pos-elim-ΣM : (ij : Idx-Σ)
        → (X : (p : Pos-Σ (η-Σ ij)) → Set)
        → (η-pos* : X (η-pos-Σ ij))
        → (p : Pos-Σ (η-Σ ij))
        → η-pos-elim ΣM ij X η-pos* p ↦ η-pos-elim-Σ ij X η-pos* p
      {-# REWRITE η-pos-elim-ΣM #-}

      μ-ΣM : {ij : Idx-Σ} (cd : Cns-Σ ij )
        → (δ : (p : Pos-Σ cd) → Cns-Σ (Typ-Σ cd p))
        → μ ΣM {ij} cd δ ↦ μ-Σ cd δ
      {-# REWRITE μ-ΣM #-}

      μ-pos-ΣM : {ij : Idx-Σ} (cd : Cns-Σ ij)
        → (δ : (p : Pos-Σ cd) → Cns-Σ (Typ-Σ cd p))
        → (p : Pos-Σ cd) (q : Pos-Σ (δ p))
        → μ-pos ΣM {ij} cd δ p q ↦ μ-pos-Σ cd δ p q
      {-# REWRITE μ-pos-ΣM #-}

      μ-pos-fst-ΣM : {ij : Idx-Σ} (cd : Cns-Σ ij)
        → (δ : (p : Pos-Σ cd) → Cns-Σ (Typ-Σ cd p))
        → (p : Pos-Σ (μ-Σ cd δ)) 
        → μ-pos-fst ΣM {ij} cd δ p ↦ μ-pos-fst-Σ cd δ p
      {-# REWRITE μ-pos-fst-ΣM #-}
      
      μ-pos-snd-ΣM : {ij : Idx-Σ} (cd : Cns-Σ ij)
        → (δ : (p : Pos-Σ cd) → Cns-Σ (Typ-Σ cd p))
        → (p : Pos-Σ (μ-Σ cd δ))
        → μ-pos-snd ΣM {ij} cd δ p ↦ μ-pos-snd-Σ cd δ p
      {-# REWRITE μ-pos-snd-ΣM #-}

