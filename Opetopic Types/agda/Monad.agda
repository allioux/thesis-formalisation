{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module Monad where

  data ℳ : Set₁

  Idx : ℳ → Set
  Cns : (M : ℳ) → Idx M → Set
  Pos : (M : ℳ) {i : Idx M} → Cns M i → Set
  Typ : (M : ℳ) {i : Idx M} (c : Cns M i) → Pos M c → Idx M
  
  data ℳ where
    Id : ℳ
    Slc : ℳ → ℳ
    Pb : (M : ℳ) → (Idx M → Set) → ℳ
  
  η : (M : ℳ) (i : Idx M) → Cns M i

  η-pos : (M : ℳ) (i : Idx M)
      → Pos M (η M i)

  η-pos-elim : (M : ℳ) (i : Idx M)
      → (X : (p : Pos M (η M i)) → Set)
      → (η-pos* : X (η-pos M i))
      → (p : Pos M (η M i)) → X p

  μ : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → Cns M i

  μ-pos : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → Pos M (μ M c δ)

  μ-pos-fst : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → Pos M (μ M c δ) → Pos M c

  μ-pos-snd : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M (μ M c δ))
      → Pos M (δ (μ-pos-fst M c δ p))

  data ⊤ᵢ : Set where
    ttᵢ : ⊤ᵢ

  Idx Id = ⊤ᵢ
  Idx (Slc M) = Σ (Idx M) (Cns M)
  Idx (Pb M X) = Σ (Idx M) X

  data Pd (M : ℳ) : Idx (Slc M) → Set where

    lf : (i : Idx M) → Pd M (i , η M i)

    nd : {x : Idx M} (y : Cns M x) (z : (p : Pos M y) → Cns M (Typ M y p))
      → (t : (p : Pos M y) → Pd M (Typ M y p , z p))
      → Pd M (x , μ M y z)

  Posₛ : (M : ℳ) {i : Idx (Slc M)} → Pd M i → Set
  Posₛ M (lf i) = ⊥
  Posₛ M (nd y z t) = ⊤ ⊔ Σ (Pos M y) λ p → Posₛ M (t p)

  Typₛ : (M : ℳ) {i : Idx (Slc M)}
    → (c : Pd M i) (p : Posₛ M c)
    → Idx (Slc M)
  Typₛ M (nd c _ ε) (inl unit) = _ , c 
  Typₛ M (nd c _ ε) (inr (p , q)) = Typₛ M (ε p) q

  Cns Id x = ⊤ᵢ
  Cns (Slc M) = Pd M
  Cns (Pb M X) (i , x) = Σ (Cns M i) λ c → (p : Pos M c) → X (Typ M c p)

  Pos Id c = ⊤ᵢ
  Pos (Slc M) = Posₛ M
  Pos (Pb M x) (c , _) = Pos M c

  Typ Id c x = ttᵢ
  Typ (Slc M) = Typₛ M
  Typ (Pb M x₁) (c , x) p = Typ M c p , x p

  -- laws

  postulate
    η-pos-typ : (M : ℳ) (i : Idx M)
      → (p : Pos M (η M i))
      → Typ M (η M i) p ↦ i
    {-# REWRITE η-pos-typ #-}

    η-pos-elim-β : (M : ℳ) (i : Idx M)
      → (X : (p : Pos M (η M i)) → Set)
      → (η-pos* : X (η-pos M i))
      → η-pos-elim M i X η-pos* (η-pos M i) ↦ η-pos*
    {-# REWRITE η-pos-elim-β #-}

    μ-pos-typ : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M (μ M c δ))
      → Typ M (μ M c δ) p ↦ Typ M (δ (μ-pos-fst M c δ p)) (μ-pos-snd M c δ p)
    {-# REWRITE μ-pos-typ #-}

    μ-pos-fst-β : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → μ-pos-fst M c δ (μ-pos M c δ p q) ↦ p
    {-# REWRITE μ-pos-fst-β #-}

    μ-pos-snd-β : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M c) (q : Pos M (δ p))
      → μ-pos-snd M c δ (μ-pos M c δ p q) ↦ q
    {-# REWRITE μ-pos-snd-β #-}
    
    μ-pos-η : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (p : Pos M (μ M c δ))
      → μ-pos M c δ (μ-pos-fst M c δ p) (μ-pos-snd M c δ p) ↦ p
    {-# REWRITE μ-pos-η #-}
    
    μ-unit-right : (M : ℳ) (i : Idx M)
      → (c : Cns M i)
      → μ M c (λ p → η M (Typ M c p)) ↦ c
    {-# REWRITE μ-unit-right #-}

    μ-unit-left : (M : ℳ) (i : Idx M) 
      → (δ : (p : Pos M (η M i)) → Cns M i)
      → μ M (η M i) δ ↦ δ (η-pos M i)
    {-# REWRITE μ-unit-left #-}

    μ-assoc : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p))
      → μ M (μ M c δ) ε ↦ μ M c (λ p → μ M (δ p) (λ q → ε (μ-pos M c δ p q)))
    {-# REWRITE μ-assoc #-}

    -- μ pos compatibilities
    μ-pos-unit-right : (M : ℳ) (i : Idx M)
      → (c : Cns M i)
      → (p : Pos M c) (q : Pos M (η M (Typ M c p)))
      → μ-pos M c (λ p → η M (Typ M c p)) p q ↦ p 
    {-# REWRITE μ-pos-unit-right #-}

    μ-pos-unit-left : (M : ℳ) (i : Idx M) 
      → (δ : (p : Pos M (η M i)) → Cns M i)
      → (p : Pos M (η M i)) (q : Pos M (δ p))
      → μ-pos M (η M i) δ p q ↦ η-pos-elim M i (λ p → Pos M (δ p) → Pos M (δ (η-pos M i))) (λ p → p) p q 
    {-# REWRITE μ-pos-unit-left #-} 

    μ-pos-assoc : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p))
      → (p : Pos M (μ M c δ)) (q : Pos M (ε p))
      → μ-pos M (μ M c δ) ε p q ↦ μ-pos M c
              (λ p → μ M (δ p) (λ q → ε (μ-pos M c δ p q))) (μ-pos-fst M c δ p)
              (μ-pos M (δ (μ-pos-fst M c δ p)) (λ q → ε (μ-pos M c δ (μ-pos-fst M c δ p) q)) (μ-pos-snd M c δ p) q) 
    {-# REWRITE μ-pos-assoc #-}

    μ-pos-fst-unit-right : (M : ℳ) {i : Idx M}
      → (c : Cns M i) (p : Pos M c)
      → μ-pos-fst M c (λ p → η M (Typ M c p)) p ↦ p 
    {-# REWRITE μ-pos-fst-unit-right #-}

    μ-pos-snd-unit-right : (M : ℳ) {i : Idx M}
      → (c : Cns M i) (p : Pos M c)
      → μ-pos-snd M c (λ p → η M (Typ M c p)) p ↦ η-pos M (Typ M c p)
    {-# REWRITE μ-pos-snd-unit-right #-}

    μ-pos-fst-unit-left : (M : ℳ) (i : Idx M) 
      → (δ : (p : Pos M (η M i)) → Cns M i)
      → (p : Pos M (δ (η-pos M i)))
      → μ-pos-fst M (η M i) δ p ↦ η-pos M i
    {-# REWRITE μ-pos-fst-unit-left #-}

    μ-pos-snd-unit-left : (M : ℳ) (i : Idx M)
      → (δ : (p : Pos M (η M i)) → Cns M i)
      → (p : Pos M (δ (η-pos M i)))
      → μ-pos-snd M (η M i) δ p ↦ p
    {-# REWRITE μ-pos-snd-unit-left  #-}

    μ-pos-fst-assoc : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p))
      → (p : Pos M (μ M c (λ p → μ M (δ p) (ε ∘ (μ-pos M c δ p)))))
      → μ-pos-fst M (μ M c δ) ε p
        ↦ μ-pos M c δ (μ-pos-fst M c (λ p → μ M (δ p) (ε ∘ (μ-pos M c δ p))) p)
                      (μ-pos-fst M (δ (μ-pos-fst M c (λ p → μ M (δ p) (ε ∘ (μ-pos M c δ p))) p))
                                   (ε ∘ μ-pos M c δ (μ-pos-fst M c (λ p → μ M (δ p) (ε ∘ (μ-pos M c δ p))) p))
                                   (μ-pos-snd M c (λ p → μ M (δ p) (ε ∘ (μ-pos M c δ p))) p))
    {-# REWRITE μ-pos-fst-assoc  #-}

    μ-pos-snd-assoc : (M : ℳ) {i : Idx M} (c : Cns M i)
      → (δ : (p : Pos M c) → Cns M (Typ M c p))
      → (ε : (p : Pos M (μ M c δ)) → Cns M (Typ M (μ M c δ) p))
      → (p : Pos M (μ M c (λ p → μ M (δ p) (ε ∘ (μ-pos M c δ p)))))
      → μ-pos-snd M (μ M c δ) ε p
        ↦ μ-pos-snd M (δ (μ-pos-fst M c (λ p → μ M (δ p) (ε ∘ (μ-pos M c δ p))) p))
                      (λ q → ε (μ-pos M c δ (μ-pos-fst M c (λ p → μ M (δ p) (ε ∘ μ-pos M c δ p)) p) q))
                      (μ-pos-snd M c (λ p → μ M (δ p) (ε ∘ (μ-pos M c δ p))) p) 
    {-# REWRITE μ-pos-snd-assoc #-}

  --
  --  Free monad signature
  --

  γ : (M : ℳ) {x : Idx M} {y : Cns M x} {z : (p : Pos M y) → Cns M (Typ M y p)}
    → (t : Cns (Slc M) (x , y))
    → (u : (p : Pos M y) → Cns (Slc M) (Typ M y p , z p))
    → Cns (Slc M) (x , μ M y z)

  γ-pos-inl : (M : ℳ) {x : Idx M} {y : Cns M x} {z : (p : Pos M y) → Cns M (Typ M y p)}
    → (t : Cns (Slc M) (x , y))
    → (u : (p : Pos M y) → Cns (Slc M) (Typ M y p , z p))
    → Posₛ M t → Posₛ M (γ M t u)
  
  γ-pos-inr : (M : ℳ) {x : Idx M} {y : Cns M x} {z : (p : Pos M y) → Cns M (Typ M y p)}
    → (t : Cns (Slc M) (x , y))
    → (u : (p : Pos M y) → Cns (Slc M) (Typ M y p , z p))
    → (p : Pos M y) (q : Posₛ M (u p))
    → Posₛ M (γ M t u)

  γ-pos-elim : (M : ℳ) {x : Idx M} {y : Cns M x} {z : (p : Pos M y) → Cns M (Typ M y p)}
    → (t : Cns (Slc M) (x , y))
    → (u : (p : Pos M y) → Cns (Slc M) (Typ M y p , z p))
    → (X : Posₛ M (γ M t u) → Set)
    → (inl* : (p : Posₛ M t) → X (γ-pos-inl M t u p))
    → (inr* : (p : Pos M y) (q : Posₛ M (u p)) → X (γ-pos-inr M t u p q))
    → (p : Posₛ M (γ M t u)) → X p

  postulate
    -- γ elim comp rules
    γ-pos-elim-inl-β : (M : ℳ) {x : Idx M} {y : Cns M x} {z : (p : Pos M y) → Cns M (Typ M y p)}
      → (t : Cns (Slc M) (x , y))
      → (u : (p : Pos M y) → Cns (Slc M) (Typ M y p , z p))
      → (X : Posₛ M (γ M t u) → Set)
      → (inl* : (p : Posₛ M t) → X (γ-pos-inl M t u p))
      → (inr* : (p : Pos M y) (q : Posₛ M (u p)) → X (γ-pos-inr M t u p q))
      → (p : Posₛ M t)
      → γ-pos-elim M t u X inl* inr* (γ-pos-inl M t u p) ↦ inl* p
    {-# REWRITE γ-pos-elim-inl-β #-}

    γ-pos-elim-inr-β : (M : ℳ) {x : Idx M} {y : Cns M x} {z : (p : Pos M y) → Cns M (Typ M y p)}
      → (t : Cns (Slc M) (x , y))
      → (u : (p : Pos M y) → Cns (Slc M) (Typ M y p , z p))
      → (X : Posₛ M (γ M t u) → Set)
      → (inl* : (p : Posₛ M t) → X (γ-pos-inl M t u p))
      → (inr* : (p : Pos M y) (q : Posₛ M (u p)) → X (γ-pos-inr M t u p q))
      → (p : Pos M y) (q : Posₛ M (u p))
      → γ-pos-elim M t u X inl* inr* (γ-pos-inr M t u p q) ↦ inr* p q
    {-# REWRITE γ-pos-elim-inr-β #-}

    γ-unit-r : (M : ℳ) {i : Idx M} {c : Cns M i} 
      → (ρ : Cns (Slc M) (i , c))
      → γ M ρ (λ p → lf (Typ M c p)) ↦ ρ
    {-# REWRITE γ-unit-r #-}

  --
  --  Slice implementation 
  --

  ηₛ : (M : ℳ) → (i : Idx (Slc M)) → Cns (Slc M) i
  ηₛ M (i , c) = nd c _ (λ p → lf (Typ M c p))

  μₛ : (M : ℳ) {i : Idx (Slc M)} (c : Cns (Slc M) i)
    → (δ : (p : Pos (Slc M) c) → Cns (Slc M) (Typ (Slc M) c p))
    → Cns (Slc M) i
  μₛ M (lf τ) κ = lf τ
  μₛ M (nd c _ ε) κ =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p) 
    in γ M w ψ

  μ-posₛ : (M : ℳ) {i : Idx (Slc M)} (c : Cns (Slc M) i)
    → (δ : (p : Posₛ M c) → Cns (Slc M) (Typₛ M c p))
    → (p : Posₛ M c) (q : Posₛ M (δ p))
    → Posₛ M (μₛ M c δ)
  μ-posₛ M (nd c _ ε) κ (inl unit) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
    in γ-pos-inl M w ψ r
  μ-posₛ M (nd c _ ε) κ (inr (p , q)) r = 
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
    in γ-pos-inr M w ψ p (μ-posₛ M (ε p) (κ↑ p) q r)

  μ-pos-fstₛ : (M : ℳ) {i : Idx (Slc M)} (c : Cns (Slc M) i)
    → (δ : (p : Posₛ M c) → Cns (Slc M) (Typₛ M c p))
    → Posₛ M (μₛ M c δ) → Posₛ M c
  μ-pos-fstₛ M (nd c _ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
        X _ = ⊤ ⊔ Σ (Pos M c) (λ p → Posₛ M (ε p))
        inl* p = inl unit
        inr* p q = inr (p , μ-pos-fstₛ M (ε p) (κ↑ p) q)
    in γ-pos-elim M w ψ X inl* inr* p

  μ-pos-sndₛ : (M : ℳ) {i : Idx (Slc M)} (c : Cns (Slc M) i)
    → (δ : (p : Posₛ M c) → Cns (Slc M) (Typₛ M c p))
    → (p : Posₛ M (μₛ M c δ))
    → Posₛ M (δ (μ-pos-fstₛ M c δ p))
  μ-pos-sndₛ M (nd c _ ε) κ p =
    let w = κ (inl unit)
        κ↑ p q = κ (inr (p , q))
        ψ p = μₛ M (ε p) (κ↑ p)
        X p = Posₛ M (κ (μ-pos-fstₛ M (nd c _ ε) κ p))
        inl* p = p
        inr* p q = μ-pos-sndₛ M (ε p) (κ↑ p) q
    in γ-pos-elim M w ψ X inl* inr* p

  γ M (lf i) ψ = ψ (η-pos M i)
  γ M (nd x y t) ψ = 
    let ψ↑ p q = ψ (μ-pos M x y p q)
        t↑ p = γ M (t p) (ψ↑ p)
    in nd x _ t↑

  γ-pos-inl M (nd x y ε) ψ (inl unit) = inl unit
  γ-pos-inl M (nd x y ε) ψ (inr (p , q)) = 
    let ψ↑ p q = ψ (μ-pos M x y p q)
        ε↑ p = γ M (ε p) (ψ↑ p)
    in inr (p , γ-pos-inl M (ε p) (ψ↑ p) q)

  γ-pos-inr M (lf i) ψ p q = 
     η-pos-elim M i (λ p → Posₛ M (ψ p) → Posₛ M (ψ (η-pos M i))) (λ p → p) p q 
  γ-pos-inr M (nd x y ε) ψ p q = 
    let ψ↑ p q = ψ (μ-pos M x y p q)
        ε↑ p = γ M (ε p) (ψ↑ p)
        p₀ = μ-pos-fst M x y p
        p₁ = μ-pos-snd M x y p
    in inr (p₀ , γ-pos-inr M (ε p₀) (ψ↑ p₀) p₁ q)

  γ-pos-elim M (lf i) ψ X inl* inr* p =  inr* (η-pos M i) p 
  γ-pos-elim M (nd x y ε) ψ X inl* inr* (inl unit) =  inl* (inl unit) 
  γ-pos-elim M (nd x y ε) ψ X inl* inr* (inr (p , q)) = 
    let ψ↑ p q = ψ (μ-pos M x y p q)
        ε↑ p = γ M (ε p) (ψ↑ p)
        X↑ p q = X (inr (p , q))
        inl*↑ p q = inl* (inr (p , q))
        inr*↑ p q r = inr* (μ-pos M x y p q) r
    in γ-pos-elim M (ε p) (ψ↑ p) (X↑ p) (inl*↑ p) (inr*↑ p) q

  --
  --  η-decoration helper
  --
 
  η-dec : (M : ℳ) (X : Idx M → Set)
    → {i : Idx M} (x : X i)
    → (p : Pos M (η M i)) → X (Typ M (η M i) p)
  η-dec M X {i} x = η-pos-elim M i (λ p → X (Typ M (η M i) p)) x 

  postulate
    η-dec-β : (M : ℳ) (X : Set)
      → {i : Idx M} (x : X)
      → (p : Pos M (η M i))
      → η-pos-elim M i (cst X) x p ↦ x
    {-# REWRITE η-dec-β #-}

  η Id _ = ttᵢ
  η (Slc M) = ηₛ M
  η (Pb M X) (i , x) = η M i , η-dec M X x

  η-pos Id _ = ttᵢ
  η-pos (Slc M) (i , c) = inl tt
  η-pos (Pb M X) (i , x) = η-pos M i

  η-pos-elim Id i X η-pos* ttᵢ = η-pos*
  η-pos-elim (Slc M) i X η-pos* (inl tt) = η-pos*
  η-pos-elim (Pb M _) (i , x) X η-pos* p = η-pos-elim M i X η-pos* p 

  μ Id _ _ = ttᵢ
  μ (Slc M) = μₛ M
  μ (Pb M X) (c , x) d =
    let x' p = snd (d (μ-pos-fst M c (fst ∘ d) p)) (μ-pos-snd M c (fst ∘ d) p)
    in μ M c (fst ∘ d) , x'

  μ-pos Id c δ p q = ttᵢ
  μ-pos (Slc M) = μ-posₛ M
  μ-pos (Pb M x) (c , _) d p q = μ-pos M c (fst ∘ d) p q

  μ-pos-fst Id c δ x = ttᵢ
  μ-pos-fst (Slc M) = μ-pos-fstₛ M
  μ-pos-fst (Pb M x) (c , _) d = μ-pos-fst M c (fst ∘ d)

  μ-pos-snd Id c δ p = ttᵢ
  μ-pos-snd (Slc M) = μ-pos-sndₛ M
  μ-pos-snd (Pb M x) (c , _) d = μ-pos-snd M c (fst ∘ d)

  postulate

    μ-pos-fst-βₛ : (M : ℳ) {i : Idx (Slc M)} (c : Cns (Slc M) i)
      → (δ : (p : Posₛ M c) → Cns (Slc M) (Typₛ M c p))
      → (p : Posₛ M c) (q : Posₛ M (δ p))
      → μ-pos-fstₛ M c δ (μ-posₛ M c δ p q) ↦ p
    {-# REWRITE μ-pos-fst-βₛ #-}

    μ-pos-snd-βₛ : (M : ℳ) {i : Idx (Slc M)} (c : Cns (Slc M) i)
      → (δ : (p : Pos (Slc M) c) → Cns (Slc M) (Typ (Slc M) c p))
      → (p : Pos (Slc M) c) (q : Pos (Slc M) (δ p))
      → μ-pos-sndₛ M c δ (μ-posₛ M c δ p q) ↦ q
    {-# REWRITE μ-pos-snd-βₛ #-}

    μ-pos-typₛ : (M : ℳ) {i : Idx (Slc M)} (c : Cns (Slc M) i)
      → (δ : (p : Pos (Slc M) c) → Cns (Slc M) (Typ (Slc M) c p))
      → (p : Pos (Slc M) (μ (Slc M) c δ))
      → Typₛ M (μₛ M c δ) p ↦ Typₛ M (δ (μ-pos-fstₛ M c δ p)) (μ-pos-sndₛ M c δ p)
    {-# REWRITE μ-pos-typₛ #-}

  ⟦_⟧ : (M : ℳ) → (Idx M → Set) → (Idx M → Set)
  ⟦ M ⟧ X i = Σ (Cns M i) (λ c → (p : Pos M c) → X (Typ M c p))

  Cell : ℳ → Set₁
  Cell M = Idx M → Set

  _/_ : (M : ℳ) (X : Idx M → Set) → ℳ
  M / X = Slc (Pb M X)

  infixl 10 _/_

  _◂_ : ∀ {i j} {A : Set i} {B : A → Set j} (x : A) → B x → Σ A B
  x ◂ y = x , y

  -- Decoration of a constructor in M indexed by Idx M 
  Fam : (M : ℳ) (X : Idx M → Set) {i : Idx M} (c : Cns M i) → Set
  Fam M X c = (p : Pos M c) → X (Typ M c p)

  -- Fam M X c == Π (Pos M c) (X ∘ Typ M c)

  Famₛ : (M : ℳ) (X : Idx (Slc M) → Set) {i : Idx M} (c : Cns M i) (d : Fam M (Cns M) c) → Set
  Famₛ M X c d = (p : Pos M c) → X (Typ M c p ◂ d p)
