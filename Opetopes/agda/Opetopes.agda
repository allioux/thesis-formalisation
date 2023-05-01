{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import HoTT

module Opetopes where

  𝒰 = Set

  data 𝒪 : ℕ → 𝒰
  data 𝒫 : {n : ℕ} (f : 𝒪 n) → 𝒰
  Pos : {n : ℕ} {f : 𝒪 n} → 𝒫 f → 𝒰
  
  infixl 40 _◂_

  data 𝒪 where
    ●   : 𝒪 O
    _◂_ : {n : ℕ} (f : 𝒪 n) → 𝒫 f → 𝒪 (S n)

  Typ : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f) (s : Pos o) → 𝒪 n

  -- Notations
  𝒪ᶠ : {m : ℕ} {o : 𝒪 m} (t : 𝒫 o) → ℕ → 𝒰
  𝒪ᶠ {m} t n = Pos t → 𝒪 n

  𝒫ᶠ : {m n : ℕ} {o : 𝒪 m} {t : 𝒫 o} → 𝒪ᶠ t n → 𝒰
  𝒫ᶠ {t = t} o = (p : Pos t) → 𝒫 (o p)

  𝒫ᵗ : {n : ℕ} {o : 𝒪 n} → 𝒫 o → 𝒰
  𝒫ᵗ t = 𝒫ᶠ (Typ t)

  _◂ᶠ_ : {n : ℕ} {o : 𝒪 n} (t : 𝒫 o) → 𝒫ᵗ t → 𝒪ᶠ t _
  _◂ᶠ_ t u p = Typ t p ◂ u p

  -- Positions are invariant under transport

  Pos-transpᵖ : {n : ℕ} {o : 𝒪 n} {f₁ f₂ : 𝒫 o}
    → (f' : 𝒫 (o ◂ f₁)) (p : f₁ == f₂)
    → Pos f' == Pos (transport (λ f → 𝒫 (o ◂ f)) p f') 
  Pos-transpᵖ f' idp = idp

  Pos-transpᵖ-in : {n : ℕ} {x : 𝒪 n} {y z : 𝒫 x} (p : y == z) (t : 𝒫 (x ◂ y))
    → Pos t → Pos (transport _ p t)
  Pos-transpᵖ-in p t q = coe (Pos-transpᵖ _ p) q

  Pos-transpᵖ-elim : {n : ℕ} {x : 𝒪 n} {y z : 𝒫 x} (p : y == z)
    → (t : 𝒫 (x ◂ y))
    → (X : Pos (transport (λ y → 𝒫 (x ◂ y)) p t) → Set)
    → (e : (q : Pos t) → X (Pos-transpᵖ-in p t q))
    → (p : Pos (transport (λ y → 𝒫 (x ◂ y)) p t))
    → X p
  Pos-transpᵖ-elim idp t X e p = e p

  Pos-transpᵒ : {n : ℕ} {o₁ o₂ : 𝒪 n} {f₁ : 𝒫 o₁} {f₂ : 𝒫 o₂}
    → (f' : 𝒫 (o₁ ◂ f₁)) (p : (o₁ , f₁) == (o₂ , f₂))
    → Pos f' == Pos (transport (λ (o , f) → 𝒫 (o ◂ f)) p f')  
  Pos-transpᵒ f' p = ↓-cst-out (ap↓ Pos (transp-↓ (λ (o , f) → 𝒫 (o ◂ f)) p f' ))

  Pos-transpᵒ-in : {n : ℕ} {x₀ x₁ : 𝒪 n} {y₀ : 𝒫 x₀} {y₁ : 𝒫 x₁} (p : (x₀ , y₀) == (x₁ , y₁))
    → (t : 𝒫 (x₀ ◂ y₀))
    → Pos t → Pos (transport _ p t)
  Pos-transpᵒ-in p t q = coe (Pos-transpᵒ _ p) q

  Pos-transpᵒ-elim : {n : ℕ} {o₁ o₂ : 𝒪 n} {f₁ : 𝒫 o₁} {f₂ : 𝒫 o₂}
    → (p : (o₁ , f₁) == (o₂ , f₂))
    → (t : 𝒫 (o₁ ◂ f₁)) 
    → (X : Pos (transport (λ (o , f) → 𝒫 (o ◂ f)) p t) → Set)
    → (e : (q : Pos t) → X (Pos-transpᵒ-in p t q))
    → (p : Pos (transport (λ (o , f) → 𝒫 (o ◂ f)) p t))
    → X p
  Pos-transpᵒ-elim idp t X e p = e p

  -- Operations
  η : {n : ℕ} (o : 𝒪 n) → 𝒫 o

  η-pos : {n : ℕ} (o : 𝒪 n) → Pos (η o)
  
  η-pos-elim : {n : ℕ} (o : 𝒪 n) (A : (p : Pos (η o)) → 𝒰)
    → (η-pos* : A (η-pos o)) (p : Pos (η o)) → A p
  
  μ : {n : ℕ} {o : 𝒪 n} (t : 𝒫 o) (κ : 𝒫ᵗ t)
    → 𝒫 o
  
  μ-pos : {n : ℕ} {o : 𝒪 n} (t : 𝒫 o) (κ : 𝒫ᵗ t)
    → (p : Pos t) (q : Pos (κ p))
    → Pos (μ t κ)
  
  μ-pos-fst : {n : ℕ} {o : 𝒪 n} (t : 𝒫 o)
    → (κ : 𝒫ᵗ t)
    → Pos (μ t κ) → Pos t
   
  μ-pos-snd : {n : ℕ} {o : 𝒪 n} (t : 𝒫 o)
    → (κ : 𝒫ᵗ t)
    → (p : Pos (μ t κ)) → Pos (κ (μ-pos-fst t κ p))
  
  γ : {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} {z : 𝒫ᵗ y}
    → (t : 𝒫 (x ◂ y))
    → (u : 𝒫ᶠ (y ◂ᶠ z))
    → 𝒫 (x ◂ μ y z)
  
  γ-pos-inl : {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} {z : 𝒫ᵗ y}
    → (t : 𝒫 (x ◂ y))
    → (u : 𝒫ᶠ (y ◂ᶠ z))
    → Pos t → Pos (γ t u)
  
  γ-pos-inr : {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} {z : 𝒫ᵗ y}
    → (t : 𝒫 (x ◂ y))
    → (u : 𝒫ᶠ (y ◂ᶠ z))
    → (p : Pos y) (q : Pos (u p))
    → Pos (γ t u)

  γ-pos-elim : {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} {z : 𝒫ᵗ y}
    → (t : 𝒫 (x ◂ y))
    → (u : 𝒫ᶠ (y ◂ᶠ z))
    → (X : Pos (γ t u) → 𝒰)
    → (left : (p : Pos t) → X (γ-pos-inl t u p))
    → (right : (p : Pos y) (q : Pos (u p)) → X (γ-pos-inr t u p q))
    → (p : Pos (γ t u)) → X p

  data 𝒫 where
    arr : 𝒫 ●
    lf  : {n : ℕ} (o : 𝒪 n) → 𝒫 (o ◂ η o)
    nd  : {n : ℕ} {x : 𝒪 n} (y : 𝒫 x) {z : 𝒫ᵗ y}
            → 𝒫ᶠ (y ◂ᶠ z) 
            → 𝒫 (x ◂ μ y z)
      
  -- Pos : {n : ℕ} {f : 𝒪 n} → 𝒫 f → 𝒰  
  Pos arr = ⊤
  Pos (lf f) = ⊥
  Pos (nd c ε) = ⊤ ⊔ Σ (Pos c) (λ p → Pos (ε p))
  
  -- Typ : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f) (s : Pos o) → 𝒪 n
  Typ arr tt = ●
  Typ (lf f) ()
  Typ (nd {x = x} y t) (inl tt) = x ◂ y
  Typ (nd x t) (inr (p , q)) = Typ (t p) q

  postulate
    -- η-pos laws
    η-pos-typ : {n : ℕ} (f : 𝒪 n)
      → (p : Pos (η f))
      → Typ (η f) p == f    
  
    η-pos-elim-β : {n : ℕ} (o : 𝒪 n)
      → (A : (p : Pos (η o)) → 𝒰)
      → (η-pos* : A (η-pos o))
      → η-pos-elim o A η-pos* (η-pos o) == η-pos*

    -- μ-pos laws
    μ-pos-fst-β : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
      → (κ : (s : Pos o) → 𝒫 (Typ o s))
      → (s : Pos o) (t : Pos (κ s))
      → μ-pos-fst o κ (μ-pos o κ s t) == s

    μ-pos-snd-β : {n : ℕ} {o : 𝒪 n} (t : 𝒫 o)
      → (u : (p : Pos t) → 𝒫 (Typ t p))
      → (p : Pos t) (q : Pos (u p))
      → μ-pos-snd t u (μ-pos t u p q) == q [ (λ p → Pos (u p)) ↓ (μ-pos-fst-β t u p q) ]
      
    μ-pos-η : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
      → (κ : (s : Pos o) → 𝒫 (Typ o s))
      → (s : Pos (μ o κ))
      → μ-pos o κ (μ-pos-fst o κ s) (μ-pos-snd o κ s) == s

    μ-pos-typ : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
      → (κ : (s : Pos o) → 𝒫 (Typ o s))
      → (s : Pos (μ o κ))
      → Typ (μ o κ) s == Typ (κ (μ-pos-fst o κ s)) (μ-pos-snd o κ s)

  μ-pos-typ-aux : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
      → (κ : (s : Pos o) → 𝒫 (Typ o s))
      → (p : Pos o) (q : Pos (κ p))
      → Typ (μ o κ) (μ-pos o κ p q) == Typ (κ p) q
  μ-pos-typ-aux o κ p q =
    μ-pos-typ o κ (μ-pos o κ p q)
    ∙ ap (λ (p , q) → Typ (κ p) q) (pair= (μ-pos-fst-β o κ p q) (μ-pos-snd-β o κ p q)) 

  postulate
    -- μ laws
    μ-unit-r : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
      → μ o (λ s → η (Typ o s)) == o

    μ-unit-l : {n : ℕ} {f : 𝒪 n} (ϕ : (s : Pos (η f)) → 𝒫 (Typ (η f) s))
      →  μ (η f) ϕ  == ϕ (η-pos f) [ 𝒫 ↓ ! (η-pos-typ f (η-pos f))  ]

    μ-assoc : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
      → (κ : (s : Pos o) → 𝒫 (Typ o s))
      → (θ : (s : Pos (μ o κ)) → 𝒫 (Typ (μ o κ) s))
      → μ (μ o κ) θ == μ o (λ s → μ (κ s) λ t → transport 𝒫 (μ-pos-typ-aux o κ s t) (θ (μ-pos o κ s t)))

    -- γ elim rules
    γ-pos-elim-inl-β : {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} {z : 𝒫ᵗ y}
      → (t : 𝒫 (x ◂ y))
      → (u : 𝒫ᶠ (y ◂ᶠ z))
      → (X : Pos (γ t u) → 𝒰)
      → (left : (p : Pos t) → X (γ-pos-inl t u p))
      → (right : (p : Pos y) (q : Pos (u p)) → X (γ-pos-inr t u p q))
      → (p : Pos t)
      → γ-pos-elim t u X left right (γ-pos-inl t u p) == left p

    γ-pos-elim-inr-β : {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} {z : 𝒫ᵗ y}
      → (t : 𝒫 (x ◂ y))
      → (u : 𝒫ᶠ (y ◂ᶠ z))
      → (X : Pos (γ t u) → 𝒰)
      → (left : (p : Pos t) → X (γ-pos-inl t u p))
      → (right : (p : Pos y) (q : Pos (u p)) → X (γ-pos-inr t u p q))
      → (p : Pos y) (q : Pos (u p))
      → γ-pos-elim t u X left right (γ-pos-inr t u p q) == right p q

    -- γ pos laws
    γ-pos-inl-typ : {n : ℕ} (f : 𝒪 n) (o : 𝒫 f) (p : 𝒫 (f ◂ o))
      → (δ : (s : Pos o) → 𝒫 (Typ o s))
      → (ε : (s : Pos o) → 𝒫 (Typ o s ◂ δ s))
      → (s : Pos p)
      → Typ (γ p ε) (γ-pos-inl p ε s) == Typ p s

    γ-pos-inr-typ : {n : ℕ} (f : 𝒪 n) (o : 𝒫 f) (p : 𝒫 (f ◂ o))
      → (δ : (s : Pos o) → 𝒫 (Typ o s))
      → (ε : (s : Pos o) → 𝒫 (Typ o s ◂ δ s))
      → (s : Pos o) (t : Pos (ε s))
      → Typ (γ p ε) (γ-pos-inr p ε s t) == Typ (ε s) t

    γ-unit-r : {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} (t : 𝒫 (x ◂ y))
      → γ t (λ p → lf (Typ y p)) == t [ (λ t → 𝒫 (x ◂ t)) ↓ μ-unit-r y ]

    γ-unit-l : {n : ℕ} {x : 𝒪 n} {y : 𝒫ᵗ (η x)}
      → (t : 𝒫ᶠ (η x ◂ᶠ y))
      → γ (lf x) t == t (η-pos x)
           [ (λ (x , y) → 𝒫 (x ◂ y)) ↓ pair= (! (η-pos-typ x (η-pos x))) (μ-unit-l y) ]

    γ-assoc : {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} {z : 𝒫ᵗ y} {w : 𝒫ᵗ (μ y z)}
      → (t : 𝒫 (x ◂ y))
      → (u : 𝒫ᶠ (y ◂ᶠ z))
      → (v : 𝒫ᶠ (μ y z ◂ᶠ w))
      → let v' p q =
              transport (λ (o , t) → 𝒫 (o ◂ t))
                (pair= (μ-pos-typ-aux y z p q) (transp-↓ 𝒫 _ _))
                (v (μ-pos y z p q))
        in γ (γ t u) v == γ t (λ p → γ (u p) (v' p)) [ (λ t → 𝒫 (x ◂ t)) ↓ μ-assoc y z w ]

  -- η : {n : ℕ} (f : 𝒪 n) → 𝒫 f
  η ● = arr
  η (o ◂ t) =
    let u = nd t (λ p → lf (Typ t p))
    in transport (λ t → 𝒫 (o ◂ t)) (μ-unit-r t) u

  Pos-η-is-contr : {n : ℕ} (o : 𝒪 n) → is-contr (Pos (η o))

  Pos-η-is-contr ● = Unit-level
  Pos-η-is-contr (o ◂ t) = 
    let ρ = nd t (λ p → lf (Typ t p))
    
        Pos-ρ-is-contr : is-contr (Pos ρ)
        Pos-ρ-is-contr = has-level-in (inl unit , λ { (inl tt) → idp })

        Pos= : Pos ρ == Pos (η (o ◂ t))
        Pos= = Pos-transpᵖ ρ (μ-unit-r t)

    in transport is-contr Pos= Pos-ρ-is-contr

  -- η-pos : {n : ℕ} (f : 𝒪 n)
  --   → Pos (η f)
  η-pos o = contr-center (Pos-η-is-contr o)

  -- η-pos-elim : {n : ℕ} (o : 𝒪 n) (A : (p : Pos (η o)) → 𝒰)
  --   → (η-pos* : A (η-pos o)) (p : Pos (η o)) → A p
  η-pos-elim o A η-pos* p = transport A (contr-path (Pos-η-is-contr o) p) η-pos*

  -- μ : {n : ℕ} {o : 𝒪 n} (t : 𝒫 o) (κ : 𝒫ᵗ t) → 𝒫 o
  μ arr t = t tt
  μ (lf x) t = lf x
  μ (nd y t) u =
    let t' p = μ (t p) (λ q → u (inr (p , q)))
    in γ (u (inl tt)) t'

  module γ-nd {n : ℕ} {x : 𝒪 n} {y : 𝒫 x} {z : 𝒫ᵗ y} {w : 𝒫ᵗ (μ y z)} (t : 𝒫ᶠ (y ◂ᶠ z)) (u : 𝒫ᶠ (μ y z ◂ᶠ w)) where

    w' : (p : Pos y) → 𝒫ᵗ (z p)
    w' p q = transport 𝒫 (μ-pos-typ-aux y z p q) (w (μ-pos y z p q))

    pth : (p : Pos y) (q : Pos (z p))
      → Typ (μ y z) (μ-pos y z p q) , w (μ-pos y z p q)
        == Typ (z p) q , transport 𝒫 (μ-pos-typ-aux y z p q) (w (μ-pos y z p q))
    pth p q = pair= (μ-pos-typ-aux y z p q) (transp-↓ 𝒫 (μ-pos-typ-aux y z p q) (w (μ-pos y z p q)))

    u' : (p : Pos y) → 𝒫ᶠ (z p ◂ᶠ w' p)
    u' p q = transport (λ (o , t) → 𝒫 (o ◂ t)) (pth p q) (u (μ-pos y z p q))

    v : 𝒫ᶠ (y ◂ᶠ (λ p → μ (z p) ((w' p))))
    v p = γ (t p) (u' p)

  -- γ : {n : ℕ} (f : 𝒪 n) (o : 𝒫 f) (p : 𝒫 (f ◂ o))
  --   → (δ : (s : Pos o) → 𝒫 (Typ o s))
  --   → (ε : (s : Pos o) → 𝒫 (Typ o s ◂ δ s))
  --   → 𝒫 (f ◂ μ o δ)
  γ {z = y} (lf x) t =
    transport (λ (x , y) → 𝒫 (x ◂ y))
      (! (pair= (! (η-pos-typ x (η-pos x))) (μ-unit-l y)))
      (t (η-pos x))
  γ {z = w} (nd {x = x} y {z} t) u =
    let open γ-nd t u
    in transport (λ t → 𝒫 (x ◂ t)) (! (μ-assoc y z w) ) (nd y {λ p → μ (z p) ((w' p))} v) 

  -- μ-pos : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
  --   → (κ : (s : Pos o) → 𝒫 (Typ o s))
  --   → (s : Pos o) (t : Pos (κ s))
  --   → Pos (μ o κ)
  μ-pos arr κ tt p = p
  μ-pos (nd t ε) κ (inl tt) p =
    let κ-here = κ (inl tt)
        ε' p = μ (ε p) (λ q → κ (inr (p , q)))
    in γ-pos-inl κ-here ε' p
  μ-pos (nd t ε) κ (inr (p , q)) r =
    let κ-here = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μ (ε p) (κ' p)
    in γ-pos-inr κ-here ε' p (μ-pos (ε p) (κ' p) q r)

  -- μ-pos-fst : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
  --   → (κ : (s : Pos o) → 𝒫 (Typ o s))
  --   → Pos (μ o κ) → Pos o
  μ-pos-fst arr κ _ = tt
  μ-pos-fst (nd t ε) κ =
    let κ-here = κ (inl tt)
        κ' p q = κ (inr (p , q))
        ε' p = μ (ε p) (κ' p)
    in γ-pos-elim κ-here ε' _ (λ _ → inl tt) 
       (λ p q → inr (p , (μ-pos-fst (ε p) (κ' p) q)))

  -- μ-pos-snd : {n : ℕ} {f : 𝒪 n} (o : 𝒫 f)
  --   → (δ : (s : Pos o) → 𝒫 (Typ o s))
  --   → (s : Pos (μ o δ)) → Pos (δ (μ-pos-fst o δ s))
  μ-pos-snd arr δ p = p
  μ-pos-snd (nd t ε) δ = 
    let κ-here = δ (inl tt)
        δ' p q = δ (inr (p , q))
        ε' p = μ (ε p) (δ' p)

        A _ = Pos (nd t ε)
        aₗ p = inl tt
        aᵣ p q = inr (p , μ-pos-fst (ε p) (δ' p) q)

        B p = Pos (δ (μ-pos-fst (nd t ε) δ p))
        bₗ p =
          transport (Pos ∘ δ)
            (! (γ-pos-elim-inl-β κ-here ε' A aₗ aᵣ p))
            p
        bᵣ p q =
          transport (Pos ∘ δ)
            (! (γ-pos-elim-inr-β κ-here ε' A aₗ aᵣ p q))
            (μ-pos-snd (ε p) (δ' p) q)
    in γ-pos-elim κ-here ε' B bₗ bᵣ

  -- γ-pos-inl : {n : ℕ} (f : 𝒪 n) (o : 𝒫 f) (p : 𝒫 (f ◂ o))
  --   → (δ : (s : Pos o) → 𝒫 (Typ o s))
  --   → (ε : (s : Pos o) → 𝒫 (Typ o s ◂ δ s))
  --   → Pos p → Pos (γ p δ ε)
  γ-pos-inl {z = w} (nd y {z = z} t) u (inl tt) =
    let open γ-nd t u
    in Pos-transpᵖ-in (! (μ-assoc y z w)) (nd y v) (inl tt) 
  γ-pos-inl {z = w} (nd y {z = z} t) u (inr (p , q)) =
    let open γ-nd t u
    in Pos-transpᵖ-in (! (μ-assoc y z w)) (nd y v) (inr (p , (γ-pos-inl _ _ q)))

  -- γ-pos-inr : {n : ℕ} (f : 𝒪 n) (o : 𝒫 f) (p : 𝒫 (f ◂ o))
  --   → (δ : (s : Pos o) → 𝒫 (Typ o s))
  --   → (ε : (s : Pos o) → 𝒫 (Typ o s ◂ δ s))
  --   → (s : Pos o) (t : Pos (ε s))
  --   → Pos (γ p δ ε)
  γ-pos-inr {z = z} (lf x) t p q =
    let pos = η-pos-elim x (λ p → Pos (t p) → Pos (t (η-pos x))) (λ p → p)
    in Pos-transpᵒ-in _ _ (pos p q)
  γ-pos-inr {z = z} (nd x {y} t) u p q =
    let open γ-nd t u
    
        p₀ = μ-pos-fst x y p
        p₁ = μ-pos-snd x y p
       
        q' = coe (Pos-transpᵒ _ _) (transport (Pos ∘ u) (! (μ-pos-η x y p)) q)
        r = inr (p₀ , γ-pos-inr (t p₀) (u' p₀) p₁ q')

    in  Pos-transpᵖ-in _ _ r

  -- γ-pos-elim : {n : ℕ} (f : 𝒪 n) (o : 𝒫 f) (p : 𝒫 (f ◂ o))
  --   → (δ : (s : Pos o) → 𝒫 (Typ o s))
  --   → (ε : (s : Pos o) → 𝒫 (Typ o s ◂ δ s))
  --   → (X : Pos (γ p δ ε) → 𝒰)
  --   → (left : (s : Pos p) → X (γ-pos-inl f o p δ ε s))
  --   → (right : (s : Pos o) (t : Pos (ε s)) → X (γ-pos-inr f o p δ ε s t))
  --   → (s : Pos (γ p δ ε)) → X s
  γ-pos-elim {z = y} (lf x) t X left right s =
    Pos-transpᵒ-elim (! (pair= (! (η-pos-typ x (η-pos x))) (μ-unit-l y))) (t (η-pos x)) X aux s
    where aux : (q : Pos (t (η-pos x))) → X (Pos-transpᵒ-in _ _ q)
          aux q =
            transport
              (λ p → X (Pos-transpᵒ-in _ (t (η-pos x)) (p q)))
              (η-pos-elim-β x (λ p → Pos (t p) → Pos (t (η-pos x))) (λ p → p))
              (right (η-pos x) q)
    
  γ-pos-elim {z = w} (nd {x = x} y {z} t) u X left right p =
    Pos-transpᵖ-elim (! (μ-assoc y z w)) (nd y v) X aux p
    where open γ-nd t u
          n = nd y (λ p → γ (t p) (u' p))

          X' : Pos n → Set
          X' p = X (Pos-transpᵖ-in _ _ p)

          aux : (p : Pos n) → X' p
          aux true = left true
          aux (inr (p , q)) = hyp
            where right' : (q : Pos (z p)) (r : Pos (u' p q)) → X' (inr (p , γ-pos-inr (t p) (u' p) q r))
                  right' q r =
                    let pth p r = (pair= (μ-pos-typ-aux y z p r) (transp-↓ 𝒫 (μ-pos-typ-aux y z p r) (w (μ-pos y z p r))))

                        p' = μ-pos-fst y z (μ-pos y z p q)
                        q' = μ-pos-snd y z (μ-pos y z p q)

                        r' : Pos (u' p' q')
                        r' = Pos-transpᵒ-in (pth _ _) _
                               (coe (ap (Pos ∘ u) (! (μ-pos-η y z (μ-pos y z p q))))
                                    (coe (! (Pos-transpᵒ _ (pth p q))) r))

                        -- The LHS is of the form 'transform Pos p r' for some path p in a set with same source and target
                        -- and should therefore be equal to refl 
                        r'=r :
                          transport
                            (λ (p , q) → Pos (u' p q))
                            (pair= (μ-pos-fst-β y z p q) (μ-pos-snd-β y z p q))
                            r'
                            == r
                        r'=r = {!!} 

                        e = ap (λ (a , b , c) → inr (a , γ-pos-inr (t a) (u' a) b c))
                                 (pair= (μ-pos-fst-β y z p q) (↓-Σ-in (μ-pos-snd-β y z p q) (from-transp _ _ r'=r)))
                        
                    in  transport X' e (right (μ-pos y z p q) (coe (! (Pos-transpᵒ _ (pth p q))) r))

                  hyp = γ-pos-elim (t p) (u' p) (λ q → X' (inr (p , q)))
                          (λ q → left (inr (p , q)))
                          right'
                          q
          
  --
  --  Examples
  --

  ob : 𝒪 0
  ob = ●

  arrow : 𝒪 1
  arrow = ● ◂ arr

  2-drop : 𝒪 2
  2-drop = ● ◂ arr ◂ lf ● 

  2-globe : 𝒪 2
  2-globe = ● ◂ arr ◂ nd arr (λ { arr-pos → lf ● })

  2-simplex : 𝒪 2
  2-simplex = ● ◂ arr ◂ nd arr (λ p → nd arr λ q → lf (Typ arr q))




