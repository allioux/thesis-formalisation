{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad
open import MonadOver

module IdentityMonadOver (A : Set) where

  Idx↓ᵢ : Idx Id → Set
  Idx↓ᵢ _ = A

  Cns↓ᵢ : {i : Idx Id} (a : Idx↓ᵢ i)
    → Cns Id i → Set
  Cns↓ᵢ a _ = ⊤ᵢ

  Typ↓ᵢ : {i : Idx Id} {c : Cns Id i}
    → {a : Idx↓ᵢ i} (d : Cns↓ᵢ {i = i} a c)
    → (p : Pos Id {i = i} c) → Idx↓ᵢ (Typ Id {i = i} c p)
  Typ↓ᵢ {a = a} _ _ = a 

  η↓ᵢ : {i : Idx Id} (a : Idx↓ᵢ i)
    → Cns↓ᵢ {i = i} a (η Id i)
  η↓ᵢ a = ttᵢ

  μ↓ᵢ : {i : Idx Id} {c : Cns Id i}
    → {δ : (p : Pos Id {i = i} c) → Cns Id (Typ Id {i = i} c p)}
    → {a : Idx↓ᵢ i} (d : Cns↓ᵢ {i = i} a c)
    → (δ↓ : (p : Pos Id {i = i} c) → Cns↓ᵢ {i = i} (Typ↓ᵢ {i = i} {c = c} {a = a} d p) (δ p))
    → Cns↓ᵢ {i = i} a (μ Id {i = i} c δ)
  μ↓ᵢ {δ = δ} {a = a} d δ↓ = δ↓ ttᵢ

  postulate

    Id↓ : ℳ↓ Id

    Idx↓-Id↓ : (i : Idx Id)
      → Idx↓ Id↓ i ↦ Idx↓ᵢ i
    {-# REWRITE Idx↓-Id↓ #-}

    Cns↓-Id↓ : {i : Idx Id} (a : Idx↓ᵢ i) (c : Cns Id i)
      → Cns↓ Id↓ {i = i} a c ↦ Cns↓ᵢ {i = i} a c
    {-# REWRITE Cns↓-Id↓ #-}

    Typ↓-Id↓ : {i : Idx Id} {c : Cns Id i}
      → {a : Idx↓ᵢ i} (d : Cns↓ᵢ {i = i} a c)
      → (p : Pos Id {i = i} c)
      → Typ↓ Id↓ {i = i} {c = c} {i↓ = a} d p ↦ Typ↓ᵢ {i = i} {c = c} {a = a} d p
    {-# REWRITE Typ↓-Id↓ #-} 

    η↓-Id↓ : {i : Idx Id} (a : Idx↓ᵢ i)
      → η↓ Id↓ {i = i} a ↦ η↓ᵢ {i = i} a
    {-# REWRITE η↓-Id↓ #-}

    μ↓-Id↓ : {i : Idx Id} {c : Cns Id i}
      → {δ : (p : Pos Id {i = i} c) → Cns Id (Typ Id {i = i} c p)}
      → {a : Idx↓ᵢ i} (d : Cns↓ᵢ {i = i} a c)
      → (δ↓ : (p : Pos Id {i = i} c) → Cns↓ᵢ {i = i} (Typ↓ᵢ {i = i} {c = c} {a = a} d p) (δ p))
      → μ↓ Id↓ {i = i} {c = c} {δ = δ} {i↓ = a} d δ↓ ↦ μ↓ᵢ {i = i} {c = c} {δ = δ} {a = a} d δ↓ 
    {-# REWRITE μ↓-Id↓ #-}
