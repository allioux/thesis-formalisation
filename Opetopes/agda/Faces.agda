{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import HoTT
open import Opetopes

module Faces where

  data Edge : {n : ℕ} {o : 𝒪 n} → 𝒫 o → Set where
  
    lf-edge : {n : ℕ} (o : 𝒪 n) → Edge (lf o)
    
    root-edge : {n : ℕ} {x : 𝒪 n} (y : 𝒫 x) {z : 𝒫ᵗ y}
      → (t : 𝒫ᶠ (y ◂ᶠ z))
      → Edge (nd y t)
      
    nd-edge  : {n : ℕ} {x : 𝒪 n} (y : 𝒫 x) {z : 𝒫ᵗ y}
      → (t : 𝒫ᶠ (y ◂ᶠ z))
      → (p : Pos y)
      → Edge (t p)
      → Edge (nd y t)

  data LowerFace : {n : ℕ} → 𝒪 n → ℕ → Set where
    edge       : {n : ℕ} {o : 𝒪 n} {p : 𝒫 o} → Edge p → LowerFace (o ◂ p) n
    lower-face : {n : ℕ} {o : 𝒪 n} (p : 𝒫 o) {k : ℕ} → LowerFace o k → LowerFace (o ◂ p) k
    
  data Face : {n : ℕ} → 𝒪 n → ℕ → Set where
    lower-face : {n : ℕ} {o : 𝒪 n} {k : ℕ} → LowerFace o k → Face o k 
    top        : {n : ℕ} (o : 𝒪 n) → Face o (S n)
    target     : {n : ℕ} (o : 𝒪 (S n)) → Face o (S n)
    src        : {n : ℕ} {o : 𝒪 n} {f : 𝒫 o} → Pos f → Face (o ◂ f) (S n)

  -- Face of ●
  f : Face ● 1
  f = top ●

  -- Faces of (● ◂ arr)
  
  f1 : Face (● ◂ arr) 2
  f1 = top (● ◂ arr)

  f2 : Face (● ◂ arr) 1
  f2 = target (● ◂ arr)

  f3 : Face (● ◂ arr) 1
  f3 = src tt

  -- Faces of (● ◂ arr ◂ lf ●)

  g1 : Face (● ◂ arr ◂ lf ●) 3
  g1 = top (● ◂ arr ◂ lf ●)

  g2 : Face (● ◂ arr ◂ lf ●) 2
  g2 = target (● ◂ arr ◂ lf ●) 

  g3 : Face (● ◂ arr ◂ lf ●) 1
  g3 = lower-face (edge (lf-edge ●))

  -- Faces of 2-simplex

  h1 : Face 2-simplex 3
  h1 = top 2-simplex

  h2 : Face 2-simplex 2
  h2 = target 2-simplex

  h3 : Face 2-simplex 2
  h3 = src (inl tt)

  h4 : Face 2-simplex 2
  h4 = src (inr (tt , inl tt))
 
  h5 : Face 2-simplex 1
  h5 = lower-face (edge (root-edge _ _))

  h6 : Face 2-simplex 1
  h6 =
    let e : Edge (nd arr (λ p → lf ●))
        e = root-edge _ _
    in lower-face (edge (nd-edge _ _ tt e))

  h7 : Face 2-simplex 1
  h7 =
    let e : Edge (nd arr (λ p → lf ●))
        e = nd-edge _ _ tt (lf-edge _)
    in lower-face (edge (nd-edge _ _ tt e))
