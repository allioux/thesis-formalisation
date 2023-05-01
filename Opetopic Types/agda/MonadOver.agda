{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import Monad

module MonadOver where

  postulate

    ℳ↓ : (M : ℳ) → Set

    Idx↓ : {M : ℳ} (M↓ : ℳ↓ M) → Idx M → Set 
    Cns↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} (i↓ : Idx↓ M↓ i)
      → Cns M i → Set 

    Typ↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} {c : Cns M i} 
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → (p : Pos M c) → Idx↓ M↓ (Typ M c p)

    η↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} (i↓ : Idx↓ M↓ i)
      → Cns↓ M↓ i↓ (η M i)

    μ↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
      → Cns↓ M↓ i↓ (μ M c δ)

    -- typ↓ laws 
    η-pos-typ↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} (i↓ : Idx↓ M↓ i)
      → (p : Pos M (η M i))
      → Typ↓ M↓ (η↓ M↓ i↓) p ↦ i↓
    {-# REWRITE η-pos-typ↓ #-}

    μ-pos-typ↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → (i↓ : Idx↓ M↓ i) (c↓ : Cns↓ M↓ i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
      → (p : Pos M (μ M c δ))
      → Typ↓ M↓ (μ↓ M↓ c↓ δ↓) p ↦ Typ↓ M↓ (δ↓ (μ-pos-fst M c δ p)) (μ-pos-snd M c δ p) 
    {-# REWRITE μ-pos-typ↓ #-}
    
    -- μ↓ laws
    μ-unit-right↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} {c : Cns M i}
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → μ↓ M↓ c↓ (λ p → η↓ M↓ (Typ↓ M↓ c↓ p)) ↦ c↓
    {-# REWRITE μ-unit-right↓ #-}

    μ-unit-left↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} {i↓ : Idx↓ M↓ i}
      → {δ : (p : Pos M (η M i)) → Cns M i}
      → (δ↓ : (p : Pos M (η M i)) → Cns↓ M↓ i↓ (δ p))
      → μ↓ M↓ (η↓ M↓ i↓) δ↓ ↦ δ↓ (η-pos M i) 
    {-# REWRITE μ-unit-left↓ #-}
    
    μ-assoc↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → {ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p)}
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
      → (ε↓ : (p : Pos M (μ M c δ)) → Cns↓ M↓ (Typ↓ M↓ (μ↓ M↓ c↓ δ↓) p) (ε p))
      → μ↓ M↓ (μ↓ M↓ c↓ δ↓) ε↓ ↦ μ↓ M↓ c↓ (λ p → μ↓ M↓ (δ↓ p) (λ q → ε↓ (μ-pos M c δ p q)))
    {-# REWRITE μ-assoc↓ #-} 

    --
    --  Extension of colors
    --
    
    Ext : (M : ℳ) (F↓ : Idx M → Set) → ℳ↓ M

    Idx↓-Ext : (M : ℳ) (F↓ : Idx M → Set)
      → Idx↓ (Ext M F↓) ↦ F↓
    {-# REWRITE Idx↓-Ext #-}

    Cns↓-Ext : (M : ℳ) (F↓ : Idx M → Set)
      → {i : Idx M} (c : Cns M i) 
      → (i↓ : F↓ i)
      → Cns↓ (Ext M F↓) i↓ c ↦ ((p : Pos M c) → F↓ (Typ M c p) )
    {-# REWRITE Cns↓-Ext #-}
    
    Typ↓-Ext : (M : ℳ) (F↓ : Idx M → Set)
      → {i : Idx M} (c : Cns M i) 
      → (i↓ : F↓ i) (c↓ : Cns↓ (Ext M F↓) i↓ c)
      → (p : Pos M c)
      → Typ↓ (Ext M F↓) {c = c} {i↓ = i↓} c↓ p ↦ c↓ p 
    {-# REWRITE Typ↓-Ext #-}

    η↓-Ext : (M : ℳ) (F↓ : Idx M → Set)
      → {i : Idx M} (i↓ : Idx↓ (Ext M F↓) i)
      → η↓ (Ext M F↓) i↓ ↦ (λ _ → i↓)
    {-# REWRITE η↓-Ext #-}
    
    μ↓-Ext : {M : ℳ} (F↓ : Idx M → Set)
      → {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → {i↓ : Idx↓ (Ext M F↓) i} (c↓ : Cns↓ (Ext M F↓) i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ (Ext M F↓) (Typ↓ (Ext M F↓) {i↓ = i↓} c↓ p) (δ p))
      → μ↓ (Ext M F↓) {i↓ = i↓} c↓ δ↓ ↦ (λ p → δ↓ (μ-pos-fst M c δ p) (μ-pos-snd M c δ p))
    {-# REWRITE μ↓-Ext #-}

  --
  --  Decoration for η↓ 
  --

  η↓-dec : {M : ℳ} (M↓ : ℳ↓ M)
    → {X : Idx M → Set} (Y : {i : Idx M} → Idx↓ M↓ i → X i → Set)
    → {i : Idx M} {x : X i} {j : Idx↓ M↓ i} (y : Y j x)
    → (p : Pos M (η M i)) → Y (Typ↓ M↓ (η↓ M↓ j) p) (η-dec M X x p)
  η↓-dec {M} M↓ {X} Y {i} {x} {j} y = η-pos-elim M i (λ p → Y (Typ↓ M↓ (η↓ M↓ j) p) (η-dec M X x p)) y

  ---
  --- Id↓
  ---

  module _ (A : Set) where

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
  
  --
  -- Slc↓
  --

  Idx↓ₛ : {M : ℳ} (M↓ : ℳ↓ M)
    → Idx (Slc M) → Set
  Idx↓ₛ M↓ (i , c) = Σ (Idx↓ M↓ i) (λ i↓ → Cns↓ M↓ i↓ c)

  data Pd↓ {M : ℳ} (M↓ : ℳ↓ M) : {i : Idx (Slc M)} → Idx↓ₛ M↓ i → Cns (Slc M) i → Set where

    lf↓ : {i : Idx M} (i↓ : Idx↓ M↓ i)
      → Pd↓ M↓ (i↓ , η↓ M↓ i↓) (lf i) 
    
    nd↓ : {i : Idx M} {c : Cns M i}
      → {δ : (p : Pos M c) → Cns M (Typ M c p)}
      → {ε : (p : Pos M c) → Pd M (Typ M c p , δ p)}
      → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
      → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
      → (ε↓ : (p : Pos M c) → Pd↓ M↓ (Typ↓ M↓ c↓ p , δ↓ p) (ε p))
      → Pd↓ M↓ (i↓ , μ↓ M↓ c↓ δ↓) (nd c δ ε) 

  Cns↓ₛ : {M : ℳ} (M↓ : ℳ↓ M)
    → {i : Idx (Slc M)} (i↓ : Idx↓ₛ M↓ i)
    → Cns (Slc M) i → Set 
  Cns↓ₛ M↓ (i↓ , c↓) c = Pd↓ M↓ (i↓ , c↓) c 
  
  Typ↓ₛ : {M : ℳ} (M↓ : ℳ↓ M)
    → {i : Idx (Slc M)} {c : Cns (Slc M) i} 
    → {i↓ : Idx↓ₛ M↓ i} (c↓ : Cns↓ₛ M↓ i↓ c)
    → (p : Pos (Slc M) c) → Idx↓ₛ M↓ (Typ (Slc M) c p)
  Typ↓ₛ M↓ (nd↓ {i↓ = i↓} c↓ δ↓ ε↓) (inl unit) = i↓ , c↓
  Typ↓ₛ M↓ (nd↓ c↓ δ↓ ε↓) (inr (p , q)) = Typ↓ₛ M↓ (ε↓ p) q

  γ↓ : {M : ℳ} (M↓ : ℳ↓ M)
    → {i : Idx M} {c : Cns M i} {ρ : Cns (Slc M) (i , c)}
    → {δ : (p : Pos M c) → Cns M (Typ M c p)}
    → {ε : (p : Pos M c) → Cns (Slc M) (Typ M c p , δ p)}
    → {i↓ : Idx↓ M↓ i} {c↓ : Cns↓ M↓ i↓ c}
    → (ρ↓ : Cns↓ₛ M↓ (i↓ , c↓) ρ)
    → (δ↓ : (p : Pos M c) → Cns↓ M↓ (Typ↓ M↓ c↓ p) (δ p))
    → (ε↓ : (p : Pos M c) → Cns↓ₛ M↓ (Typ↓ M↓ c↓ p , δ↓ p) (ε p))
    → Cns↓ₛ M↓ (i↓ , μ↓ M↓ c↓ δ↓) (γ M ρ ε) 
  
  η↓ₛ : {M : ℳ} (M↓ : ℳ↓ M)
    → {i : Idx (Slc M)} (i↓ : Idx↓ₛ M↓ i)
    → Cns↓ₛ M↓ i↓ (η (Slc M) i)
  η↓ₛ M↓ (i↓ , c↓) =
    let η-dec↓ p = η↓ M↓ (Typ↓ M↓ c↓ p)
        lf-dec↓ p = lf↓ (Typ↓ M↓ c↓ p)
    in nd↓ c↓ η-dec↓ lf-dec↓

  μ↓ₛ : {M : ℳ} (M↓ : ℳ↓ M)
    → {i : Idx (Slc M)} {c : Cns (Slc M) i}
    → {δ : (p : Pos (Slc M) c) → Cns (Slc M) (Typ (Slc M) c p)}
    → {i↓ : Idx↓ₛ M↓ i} (c↓ : Cns↓ₛ M↓ i↓ c)
    → (δ↓ : (p : Pos (Slc M) c) → Cns↓ₛ M↓ (Typ↓ₛ M↓ {i↓ = i↓} c↓ p) (δ p))
    → Cns↓ₛ M↓ i↓ (μ (Slc M) c δ)
  μ↓ₛ M↓ (lf↓ i↓) κ↓ = lf↓ i↓
  μ↓ₛ M↓ (nd↓ c↓ δ↓ ε↓) κ↓ = 
    let w↓ = κ↓ (inl unit)
        κ↓↑ p q = κ↓ (inr (p , q))
        ψ↓ p = μ↓ₛ M↓ (ε↓ p) (κ↓↑ p) 
    in γ↓ M↓ w↓ δ↓ ψ↓
  
  γ↓ {M = M} M↓ (lf↓ {i = i} i↓) ϕ↓ ψ↓ = ψ↓ (η-pos M i)
  γ↓ {M = M} M↓ (nd↓ {c = c} {δ = δ} c↓ δ↓ ε↓) ϕ↓ ψ↓ =
    let ϕ↓↑ p q = ϕ↓ (μ-pos M c δ p q)
        ψ↓↑ p q = ψ↓ (μ-pos M c δ p q)
        δ↓↑ p = μ↓ M↓ (δ↓ p) (ϕ↓↑ p)
        ε↓↑ p = γ↓ M↓ (ε↓ p) (ϕ↓↑ p) (ψ↓↑ p)
    in nd↓ c↓ δ↓↑ ε↓↑

  postulate

    Slc↓ : {M : ℳ} (M↓ : ℳ↓ M) → ℳ↓ (Slc M)

    Idx↓-Slc↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → Idx↓ (Slc↓ M↓) ↦ Idx↓ₛ M↓
    {-# REWRITE Idx↓-Slc↓ #-}
    
    Cns↓-Slc↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx (Slc M)} (i↓ : Idx↓ (Slc↓ M↓) i)
      → Cns↓ (Slc↓ M↓) i↓ ↦ Cns↓ₛ M↓ i↓
    {-# REWRITE Cns↓-Slc↓ #-}

    Typ↓-Slc↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx (Slc M)} {c : Cns (Slc M) i} 
      → {i↓ : Idx↓ₛ M↓ i} (c↓ : Cns↓ₛ M↓ i↓ c)
      → (p : Pos (Slc M) c)
      → Typ↓ (Slc↓ M↓) c↓ p ↦ Typ↓ₛ M↓ c↓ p
    {-# REWRITE Typ↓-Slc↓ #-}

    η↓-Slc↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx (Slc M)} (i↓ : Idx↓ₛ M↓ i)
      → η↓ (Slc↓ M↓) i↓ ↦ η↓ₛ M↓ i↓
    {-# REWRITE η↓-Slc↓ #-}

    μ↓-Slc↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → {i : Idx (Slc M)} {c : Cns (Slc M) i}
      → {δ : (p : Pos (Slc M) c) → Cns (Slc M) (Typ (Slc M) c p)}
      → {i↓ : Idx↓ₛ M↓ i} (c↓ : Cns↓ₛ M↓ i↓ c)
      → (δ↓ : (p : Pos (Slc M) c) → Cns↓ₛ M↓ (Typ↓ₛ M↓ {i↓ = i↓} c↓ p) (δ p))
      → μ↓ (Slc↓ M↓) c↓ δ↓ ↦ μ↓ₛ M↓ c↓ δ↓
    {-# REWRITE μ↓-Slc↓ #-}

  --
  --  Pb↓ 
  --

  module _ {M : ℳ} (M↓ : ℳ↓ M)
    (X : Idx M → Set) 
    (Y : {i : Idx M} → Idx↓ M↓ i → X i → Set) where

    Idx↓ₚ : Idx (Pb M X) → Set
    Idx↓ₚ (i , x) = Σ (Idx↓ M↓ i) (λ j → Y j x)

    Cns↓ₚ : {i : Idx (Pb M X)} (j : Idx↓ₚ i) (c : Cns (Pb M X) i) → Set
    Cns↓ₚ (j , y) (c , ν) = Σ (Cns↓ M↓ j c) (λ d →
      (p : Pos M c) → Y (Typ↓ M↓ d p) (ν p))

    Typ↓ₚ : {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {j : Idx↓ₚ i} (d : Cns↓ₚ j c)
      → (p : Pos (Pb M X) {i = i} c) → Idx↓ₚ (Typ (Pb M X) {i = i} c p)
    Typ↓ₚ (d , κ) p = Typ↓ M↓ d p , κ p 
    
    η↓ₚ : {i : Idx (Pb M X)} 
      → (j : Idx↓ₚ i) → Cns↓ₚ j (η (Pb M X) i)
    η↓ₚ (j , y) = η↓ M↓ j , η↓-dec M↓ Y y

    μ↓ₚ : {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {δ : (p : Pos (Pb M X) {i = i} c) → Cns (Pb M X) (Typ (Pb M X) {i = i} c p)}
      → {j : Idx↓ₚ i} (d : Cns↓ₚ j c)
      → (δ↓ : (p : Pos (Pb M X) {i = i} c) → Cns↓ₚ (Typ↓ₚ {j = j} d p) (δ p))
      → Cns↓ₚ j (μ (Pb M X) {i = i} c δ)
    μ↓ₚ {i , x} {c , ν} {δ} {j = j , y} (d , κ) δ↓ =
      let δ' p = fst (δ p)
          ν' p = snd (δ (μ-pos-fst M c δ' p)) (μ-pos-snd M c δ' p)
          δ↓' p = fst (δ↓ p)
          κ' p = snd (δ↓ (μ-pos-fst M c δ' p)) (μ-pos-snd M c δ' p)  
      in μ↓ M↓ {δ = δ'} d δ↓' , κ'

  postulate

    Pb↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → (X : Idx M → Set)
      → (Y : {i : Idx M} → Idx↓ M↓ i → X i → Set)
      → ℳ↓ (Pb M X) 

    Idx↓-Pb↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → (X : Idx M → Set)
      → (Y : {i : Idx M} → Idx↓ M↓ i → X i → Set)
      → (i : Idx M) (x : X i)
      → Idx↓ (Pb↓ M↓ X Y) (i , x) ↦ Idx↓ₚ M↓ X Y (i , x)
    {-# REWRITE Idx↓-Pb↓ #-}

    Cns↓-Pb↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → (X : Idx M → Set)
      → (Y : {i : Idx M} → Idx↓ M↓ i → X i → Set)
      → (i : Idx (Pb M X)) (j : Idx↓ₚ M↓ X Y i)
      → (c : Cns (Pb M X) i)
      → Cns↓ (Pb↓ M↓ X Y) j c ↦ Cns↓ₚ M↓ X Y j c
    {-# REWRITE Cns↓-Pb↓ #-}

    Typ↓-Pb↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → (X : Idx M → Set)
      → (Y : {i : Idx M} → Idx↓ M↓ i → X i → Set)
      → {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {j : Idx↓ₚ M↓ X Y i} (d : Cns↓ₚ M↓ X Y j c)
      → (p : Pos (Pb M X) {i = i} c)
      → Typ↓ (Pb↓ M↓ X Y) {i↓ = j} d p ↦ Typ↓ₚ M↓ X Y {j = j} d p 
    {-# REWRITE Typ↓-Pb↓ #-}

    η↓-Pb↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → (X : Idx M → Set)
      → (Y : {i : Idx M} → Idx↓ M↓ i → X i → Set)
      → {i : Idx (Pb M X)}
      → (j : Idx↓ₚ M↓ X Y i) 
      → η↓ (Pb↓ M↓ X Y) j ↦ η↓ₚ M↓ X Y j 
    {-# REWRITE η↓-Pb↓ #-}

    μ↓-Pb↓ : {M : ℳ} (M↓ : ℳ↓ M)
      → (X : Idx M → Set)
      → (Y : {i : Idx M} → Idx↓ M↓ i → X i → Set)
      → {i : Idx (Pb M X)} {c : Cns (Pb M X) i}
      → {δ : (p : Pos (Pb M X) {i = i} c) → Cns (Pb M X) (Typ (Pb M X) {i = i} c p)}
      → {j : Idx↓ₚ M↓ X Y i} (d : Cns↓ₚ M↓ X Y j c)
      → (δ↓ : (p : Pos (Pb M X) {i = i} c) → Cns↓ₚ M↓ X Y (Typ↓ₚ M↓ X Y {j = j} d p) (δ p))
      → μ↓ (Pb↓ M↓ X Y) {i↓ = j} d δ↓  ↦ μ↓ₚ M↓ X Y {j = j} d δ↓ 
    {-# REWRITE μ↓-Pb↓ #-}

  Cell↓ : {M : ℳ} (M↓ : ℳ↓ M) (X : Cell M) → Set₁
  Cell↓ {M} M↓ X = {i : Idx M} (i↓ : Idx↓ M↓ i) → X i → Set

  _/↓_ : {M : ℳ} (M↓ : ℳ↓ M) {X : Cell M} (X↓ : Cell↓ M↓ X) → ℳ↓ (M / X)
  M↓ /↓ X↓ = Slc↓ (Pb↓ M↓ _ X↓)

  infixl 10 _/↓_

  Fam↓ : {M : ℳ} (M↓ : ℳ↓ M) {X : Cell M} (X↓ : Cell↓ M↓ X)
    → {i : Idx M} {i↓ : Idx↓ M↓ i} {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
    → Fam M X c → Set
  Fam↓ {M} M↓ X↓ {c = c} c↓ x = (p : Pos M c) → X↓ (Typ↓ M↓ c↓ p) (x p)

  Fam↓ₛ : {M : ℳ} (M↓ : ℳ↓ M) {X : Cell (Slc M)} (X↓ : Cell↓ (Slc↓ M↓) X)
    → {i : Idx M} {i↓ : Idx↓ M↓ i} {x : Cns M i} (x↓ : Cns↓ M↓ i↓ x)
    → {y : Fam M (Cns M) x} (y↓ : Fam↓ M↓ (Cns↓ M↓) x↓ y)
    → Famₛ M X x y → Set
  Fam↓ₛ {M} M↓ X↓ {x = x} x↓ y↓ f = (p : Pos M x) → X↓ (Typ↓ M↓ x↓ p , y↓ p) (f p)

  ⟦_⟧↓ : {M : ℳ} (M↓ : ℳ↓ M) {X : Cell M} (X↓ : Cell↓ M↓ X) {i : Idx M} → Idx↓ M↓ i → ⟦ M ⟧ X i → Set
  ⟦ M↓ ⟧↓ X↓ i↓ (c , x) = Σ (Cns↓ M↓ i↓ c) λ c↓ → Fam↓ M↓ X↓ c↓ x 
