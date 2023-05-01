{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import HoTT

module Utils where

  Σ-reassoc : ∀ {i j k l} (A : Set i) (B : A → Set j)
    → (C : A → Set k) (D : {a : A}  → B a → C a → Set l)
    →  Σ (Σ A B) (λ (a , b) → (Σ (C a) (λ c → D b c))) ≃ Σ (Σ A C) λ (a , c) → Σ (B a) (λ b → D b c)
  Σ-reassoc = {!!}

  Σ↓ : ∀ {i j k l} {A : Set i} {B : A → Set j} (C : A → Set k) (D : {a : A} → B a → C a → Set k)
    → Σ A B → Set _
  Σ↓ C D (a , b) = Σ (C a) (D b)  
