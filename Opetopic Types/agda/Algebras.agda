{-# OPTIONS --without-K --rewriting --guardedness #-}

open import HoTT
open import Monad
open import OpetopicType
open import FundamentalThm

module Algebras where

  -- Annoying rewrite rules that we have to repeat
  postulate
    γ-pos-inl-typₛ : (M : ℳ) {i : Idx M} {c : Cns M i} 
      → (ρ : Cns (Slc M) (i , c))
      → (δ : (p : Pos M {i = i} c) → Cns M (Typ M {i = i} c p))
      → (ε : (p : Pos M {i = i} c) → Cns (Slc M) (Typ M {i = i} c p , δ p))
      → (p : Posₛ M ρ)
      → Typₛ M (γ M ρ ε) (γ-pos-inl M ρ ε p)
        ↦ Typₛ M ρ p
    {-# REWRITE γ-pos-inl-typₛ #-}

    γ-pos-inr-typₛ : (M : ℳ) {i : Idx M} {c : Cns M i} 
      → (ρ : Cns (Slc M) (i , c))
      → (δ : (p : Pos M {i = i} c) → Cns M (Typ M {i = i} c p))
      → (ε : (p : Pos M {i = i} c) → Cns (Slc M) (Typ M {i = i} c p , δ p))
      → (p : Pos M c)
      → (q : Posₛ M (ε p)) 
      → Typₛ M (γ M ρ ε) (γ-pos-inr M ρ ε p q)
        ↦ Typₛ M (ε p) q
    {-# REWRITE γ-pos-inr-typₛ #-}
    
  is-unary : (M : ℳ) {i : Idx M} (c : Cns M i) → Set
  is-unary M c = is-contr (Pos M c)

  module _ (M : ℳ) (X : Idx (Slc M) → Set)
           {x : Idx M} {y : Cns M x} {z : Fam M (Cns M) y}
           (f : X (x , y)) (g : Famₛ M X y z) where

    src-pd : Pd M (x , μ M y z)
    src-pd = nd y z (λ p → η (Slc M) (Typ M y p ◂ z p)) 
  
    src-pd-δ : Fam (Slc M) X src-pd
    src-pd-δ (inl tt) = f
    src-pd-δ (inr (p , inl tt)) = g p

    pd₂ : ⟦ Slc M ⟧ X (x , μ M y z)
    pd₂ = (src-pd , src-pd-δ)

  module _ (M : ℳ) where

    module Alg {X₀ : Cell M} {X₁ : Cell (M / X₀)}
               (X₁-is-alg : is-algebraic M X₀ X₁) where

      comp : {i : Idx M}
        → (c : Cns M i)
        → (δ : Fam M X₀ c)
        → X₀ i
      comp c δ = fst $ contr-center $ X₁-is-alg c δ

      fill : {i : Idx M}
        → (c : Cns M i)
        → (δ : Fam M X₀ c)
        → X₁ ((i , comp c δ) , c , δ)
      fill c δ = snd $ contr-center $ X₁-is-alg c δ

      cell-eq-id : {i : Idx M}
        → {c : Cns M i} {y : Fam M X₀ c}
        → {z : X₀ i} (f : X₁ ((i , z) ◂ (c , y)))
        → (x : X₀ i)
        → X₁ ((i , x) , c , y) ≃ (z == x) 
      cell-eq-id {i} {c} {y} {z} f x =
        fundamental-thm (X₀ i) (λ x → X₁ ((i , x) , (c , y))) (X₁-is-alg c y) z f x

      cell-eq-id-β : {i : Idx M}
        → {c : Cns M i} {y : Fam M X₀ c}
        → {z : X₀ i} (f : X₁ ((i , z) ◂ (c , y)))
        → –> (cell-eq-id f z) f == idp
      cell-eq-id-β {i} {c} {y} {z} f =
        fundamental-thm-β (X₀ i) (λ x → X₁ ((i , x) , (c , y))) (X₁-is-alg c y) z f

      alg-levelₛ : (n : ℕ₋₂) (p : (i : Idx M) → has-level (S n) (X₀ i))
        → (i : Idx (M / X₀)) → has-level n (X₁ i)
      alg-levelₛ n p ((i , x) , (c , y)) =
        equiv-preserves-level (cell-eq-id (fill c y) x ⁻¹) ⦃ has-level-apply (p i) (comp c y) x ⦄

      alg-level₋₂ : (p : (i : Idx M) → is-contr (X₀ i))
        → (i : Idx (M / X₀)) → is-contr (X₁ i)
      alg-level₋₂ p ((i , x) , (c , y)) =
        equiv-preserves-level (cell-eq-id (fill c y) x ⁻¹) ⦃ =-preserves-level (p i) ⦄

      alg-elim : {i : Idx M} {c : Cns M i} {x : Fam M X₀ c}
        → (P : {y : X₀ i} → X₁ ((i , y) , (c , x)) → Set)
        → (d : P (fill c x))
        → {y : X₀ i} (p : X₁ ((i , y) , (c , x)))
        → P p
      alg-elim {c = c} {x} P d p = transport (λ (y , p) → P {y} p) (contr-path (X₁-is-alg c x) (_ , p)) d

  module _ (M : ℳ) where    

    module SlcAlg {X₀ : Cell (Slc M)} {X₁ : Cell (Slc M / X₀)}
                  (X₁-is-alg : is-algebraic (Slc M) X₀ X₁) where
    
      open Alg (Slc M) X₁-is-alg

      η-alg : (i : Idx M)
        → X₀ (i , η M i)
      η-alg i = comp (lf i) ⊥-elim

      η-alg-fill : (i : Idx M)
        → X₁ (((i , η M i) , η-alg i) , lf i , ⊥-elim)
      η-alg-fill i = fill (lf i) ⊥-elim

      μ-alg : {x : Idx M} {y : Cns M x}
        → {z : Fam M (Cns M) {i = x} y}
        → (α : X₀ (x , y))
        → (β : Famₛ M X₀ {i = x} y z)
        → X₀ (x , μ M y z)
      μ-alg α β =
        let (c , v) = pd₂ M X₀ α β
        in comp c v

      μ-alg-fill : {x : Idx M} {y : Cns M x}
        → {z : Fam M (Cns M) {i = x} y}
        → (α : X₀ (x , y))
        → (β : Famₛ M X₀ {i = x} y z)
        → X₁ (((x , μ M y z) , μ-alg α β) , pd₂ M X₀ α β)
      μ-alg-fill α β =
        let (c , v) = pd₂ M X₀ α β
        in fill c v

  module _ (M : ℳ) where
  
    module AlgLaws {X₀ : Cell M} {X₁ : Cell (M / X₀)} {X₂ : Cell (M / X₀ / X₁)}
                   (X₁-is-alg : is-algebraic M X₀ X₁)
                   (X₂-is-alg : is-algebraic (M / X₀) X₁ X₂) where

      open Alg M X₁-is-alg
      open SlcAlg (Pb M X₀) X₂-is-alg

      alg-η : {i : Idx M} (x : Fam M X₀ (η M i))
        → comp (η M i) x == x (η-pos M i)
      alg-η {i} x =
        let x-fill = transport (λ x → X₁ ((i , x (η-pos M i)) , η M i , x))
                               (λ= (η-pos-elim M i (λ p → x (η-pos M _) == x p) idp))
                               (SlcAlg.η-alg (Pb M X₀) X₂-is-alg (_ , x (η-pos M i)))
        in –> (cell-eq-id (fill (η M i) x) (x (η-pos M i))) x-fill

      alg-μ : {x : Idx M} (y : Cns M x) (z : Fam M (Cns M) y)
        → (v : Fam M X₀ (μ M y z))
        → comp (μ M y z) v == comp y λ p → comp (z p) λ q → v (μ-pos M y z p q)
      alg-μ y z v =
        let v₀ = fill _ λ p → comp _ (λ q → v (μ-pos M y z p q))
            v₁ p = fill (z p) (λ q → v (μ-pos M y z p q))
        in –> (cell-eq-id (fill (μ M y z) v) (comp y _)) (μ-alg v₀ v₁)

  module _ (M : ℳ) where
    
    module _ {X₀ : Cell (Slc M)} {X₁ : Cell (Slc M / X₀)} {X₂ : Cell (Slc M / X₀ / X₁)}
             (X₁-is-alg : is-algebraic (Slc M) X₀ X₁)
             (X₂-is-alg : is-algebraic (Slc M / X₀) X₁ X₂) where
             
      open Alg (Slc M) X₁-is-alg
      open AlgLaws (Slc M) X₁-is-alg X₂-is-alg
      open SlcAlg M X₁-is-alg

      module _ {x : Idx M} {y : Cns M x} {z : (p : Pos M y) → Cns M (Typ M y p)}
               (t : Cns (Slc M) (x , y))
               (u : (p : Pos M y) → Cns (Slc M) (Typ M y p , z p))
               (x : Fam (Slc M) X₀ (γ M t u)) where

        x₀ : Fam (Slc M) X₀ t
        x₀ p = x (γ-pos-inl M t u p) 
     
        x₁ : (p : _) → Fam (Slc M) X₀ (u p)
        x₁ p q = x (γ-pos-inr M t u p q)

        private pd = pd₂ M X₀ (comp t x₀) (λ p → comp (u p) (x₁ p))
        private c = fst pd
        private v = snd pd

        deco : Fam (Slc M) (Cns (Slc M)) c
        deco true = t
        deco (inr (p , true)) = u p

        alg-γ : comp (γ M t u) x == μ-alg (v (inl tt)) λ p → v (inr (p , inl tt))
        alg-γ = alg-μ c deco x ∙ ap (comp c) (λ= aux)
          where aux : (p : _) → _
                aux (inl tt) = idp
                aux (inr (p , true)) = idp

      alg-nd : {x : Idx M} {y : Cns M x}
        → {z : Fam M (Cns M) {i = x} y}
        → (t : Famₛ M (Cns (Slc M)) {i = x} y z)
        → (v : Fam (Slc M) X₀ (nd {x = x} y z t))
        → comp (nd y z t) v == μ-alg (v (inl tt)) (λ p → comp (t p) (λ q → v (inr (p , q)))) 
      alg-nd {x} {y} {z} t v =
        alg-γ (ηₛ M (_ , y)) t v
        ∙ ap (comp _) (λ= aux) 
        where aux : (p : _) → _
              aux true =  alg-η (x₀ (η (Slc M) (x , y)) t v)
              aux (inr (p , true)) = idp

  module _ (M : ℳ) where

    module SlcAlgLaws {X₀ : Cell (Slc M)} {X₁ : Cell (Slc M / X₀)} {X₂ : Cell (Slc M / X₀ / X₁)}
                      (X₁-is-alg : is-algebraic (Slc M) X₀ X₁)
                      (X₂-is-alg : is-algebraic (Slc M / X₀) X₁ X₂) where
  
      private module X₁-alg = SlcAlg M X₁-is-alg
      private module X₂-alg = SlcAlg (Pb (Slc M) X₀) X₂-is-alg

      --- μ-alg-unit-l
      module UnitL {x : Idx M} {y : Fam M (Cns M) (η M x)} (f : Famₛ M X₀ (η M x) y) where
        private pd = pd₂ M X₀ (X₁-alg.η-alg x) f
        private c = fst pd
        private v = snd pd

        ηf = X₁-alg.μ-alg (X₁-alg.η-alg x) f
        ηfᶠ = X₁-alg.μ-alg-fill (X₁-alg.η-alg x) f

        t : Fam (Pb (Slc M) X₀) (Cns (Pb (Slc M) X₀))
                   {i = (x , y (η-pos M x)) , f (η-pos M x)}
                   (c , v)
        t (inl tt) = lf x , ⊥-elim
        t (inr (p , inl tt)) = η (Pb (Slc M) X₀) ((x , y p) , f p) 

        tᶠ : Famₛ (Pb (Slc M) X₀) X₁ {i = (x , y (η-pos M x)) , f (η-pos M x)}
                    (c , v) t
        tᶠ (inl tt) = X₁-alg.η-alg-fill x
        tᶠ (inr (p , inl tt)) = X₂-alg.η-alg ((x , y p) , f p)

        μ=η : μ (Pb (Slc M) X₀) {i = (x , y (η-pos M x)) , f (η-pos M x)}
                (c , v) t
              == η (Pb (Slc M) X₀) ((x , y (η-pos M x)) , f (η-pos M x))
        μ=η = pair= idp (λ= λ { (inl tt) → idp })

      μ-alg-unit-l : {x : Idx M} {y : Fam M (Cns M) (η M x)} (f : Famₛ M X₀ (η M x) y)
        → X₁-alg.μ-alg (X₁-alg.η-alg x) f == f (η-pos M x)
      μ-alg-unit-l {x} {y} f =
        let open UnitL f
            f-refl = X₂-alg.η-alg ((x , y (η-pos M x)) , f (η-pos M x))
            β-comp = transport (λ k → X₁ (((x , y (η-pos M x)) , ηf) ◂ k))
                               μ=η
                               (X₂-alg.μ-alg ηfᶠ tᶠ)
        in fst= (contr-has-all-paths ⦃ X₁-is-alg (η (Slc M) (x , y (η-pos M x)))
                                                 (η-dec (Slc M) X₀ (f (η-pos M x))) ⦄
                                     (ηf , β-comp) (f (η-pos M x) , f-refl))


      --μ-alg-unit-r
      module UnitR {x : Idx M} {y : Cns M x} (f : X₀ (x , y))  where   

        private pd = pd₂ M X₀ f (λ p → X₁-alg.η-alg (Typ M y p))
        private c = fst pd
        private v = snd pd
        
        fη = X₁-alg.μ-alg f (λ p → X₁-alg.η-alg (Typ M y p))
        fηᶠ = X₁-alg.μ-alg-fill f (λ p → X₁-alg.η-alg (Typ M y p))

        t : Fam (Pb (Slc M) X₀) (Cns (Pb (Slc M) X₀)) {i = (x , y) , f} (c , v)
        t (inl _) = η (Pb (Slc M) X₀) ((x , y) , f)
        t (inr (p , inl tt)) = lf (Typ M y p) , ⊥-elim

        tᶠ : Famₛ (Pb (Slc M) X₀) X₁ {i = (x , y) , f} (c , v) t
        tᶠ (inl tt) = X₂-alg.η-alg (_ , f)
        tᶠ (inr (p , inl tt)) = X₁-alg.η-alg-fill (Typ M y p)

        μ=η : μ (Pb (Slc M) X₀) {i = (x , y) , f} (c , v) t
              == η (Pb (Slc M) X₀) ((x , y) , f)
        μ=η = pair= idp (λ= λ { (inl tt) → idp })
        
      μ-alg-unit-r : {x : Idx M} {y : Cns M x} (f : X₀ (x , y))
        → X₁-alg.μ-alg f (λ p → X₁-alg.η-alg (Typ M y p)) == f 
      μ-alg-unit-r {x} {y} f =
        let open UnitR f
            f-refl = X₂-alg.η-alg ((x , y) , f)
            β-comp =  transport (λ k → X₁ (((x , y) , fη) , k)) μ=η
                                (X₂-alg.μ-alg fηᶠ tᶠ)

        in fst= (contr-has-all-paths ⦃ X₁-is-alg (η (Slc M) (x , y))
                                 (η-dec (Slc M) X₀ f) ⦄
                                 (fη , β-comp) (f , f-refl))
            
      module Assoc {x : Idx M} {y : Cns M x} {z : Fam M (Cns M) y} {t : Fam M (Cns M) (μ M y z)}
                   (f : X₀ (x ◂ y)) (g : Famₛ M X₀ y z) (h : Famₛ M X₀ (μ M y z) t) where

        module LHS where
        
          gh : Famₛ M X₀ y λ p → μ M (z p) λ q → t (μ-pos M y z p q)
          gh p = X₁-alg.μ-alg (g p) λ q → h (μ-pos M y z p q)

          ghᶠ : (p : _) → _
          ghᶠ p = X₁-alg.μ-alg-fill (g p) λ q → h (μ-pos M y z p q)

          f⟨gh⟩ : X₀ (x ◂ μ M y λ p → μ M (z p) λ q → t (μ-pos M y z p q))
          f⟨gh⟩ = X₁-alg.μ-alg f gh

          f⟨gh⟩ᶠ : X₁ ((_ , f⟨gh⟩) ◂ _)
          f⟨gh⟩ᶠ = X₁-alg.μ-alg-fill f gh

          GH : (p : _) → _
          GH p = pd₂ M X₀ (g p) (λ q → h (μ-pos M y z p q))
          F⟨GH⟩ = pd₂ M X₀ f gh

          i : Idx (Pb (Slc M) X₀)
          i = (x , μ M y λ p → μ M (z p) λ q → t (μ-pos M y z p q)) , f⟨gh⟩
          
          δ : Fam (Pb (Slc M) X₀) (Cns (Pb (Slc M) X₀)) {i = i} F⟨GH⟩
          δ (inl tt) = η (Pb (Slc M) X₀) ((x , y) , f)
          δ (inr (p , inl tt)) = GH p

          ϵ : Famₛ (Pb (Slc M) X₀) X₁ {i = i} F⟨GH⟩ δ
          ϵ (inl tt) = X₂-alg.η-alg ((x , y) , f)
          ϵ (inr (p , inl tt)) = ghᶠ p

          LHS : X₁ ((_ , f⟨gh⟩) ◂ μ (Pb (Slc M) X₀) {i = i} F⟨GH⟩ δ)
          LHS = X₂-alg.μ-alg f⟨gh⟩ᶠ ϵ
        
        module RHS where

          fg = X₁-alg.μ-alg f g
          fgᶠ = X₁-alg.μ-alg-fill f g

          ⟨fg⟩h = X₁-alg.μ-alg fg h
          ⟨fg⟩hᶠ = X₁-alg.μ-alg-fill fg h

          i : Idx (Pb (Slc M) X₀)
          i = (x , μ M (μ M y z) t) , ⟨fg⟩h
  
          ⟨FG⟩H = pd₂ M X₀ fg h
          FG = pd₂ M X₀ f g

          δ : Fam (Pb (Slc M) X₀) (Cns (Pb (Slc M) X₀)) {i = i} ⟨FG⟩H
          δ (inl tt) = FG
          δ (inr (p , inl tt)) = η (Pb (Slc M) X₀) (_ , h p)
            
          ϕ : Famₛ (Pb (Slc M) X₀) X₁ {i = i} ⟨FG⟩H δ
          ϕ (inl tt) = fgᶠ
          ϕ (inr (p , inl tt)) = X₂-alg.η-alg (_ , h p)

          RHS : X₁ ((_ , ⟨fg⟩h) ◂ μ (Pb (Slc M) X₀) {i = i} ⟨FG⟩H δ)
          RHS = X₂-alg.μ-alg ⟨fg⟩hᶠ ϕ
   
        a=b : μ (Pb (Slc M) X₀) {i = LHS.i} LHS.F⟨GH⟩ LHS.δ
             == μ (Pb (Slc M) X₀) {i = RHS.i} RHS.⟨FG⟩H RHS.δ
        a=b = pair= idp (λ= λ { (inl tt) → idp ; (inr (p , inl tt)) → idp ; (inr (p , inr (q , inl tt))) → idp })

      μ-alg-assoc : {x : Idx M} {y : Cns M x} {z : Fam M (Cns M) y} {t : Fam M (Cns M) (μ M y z)}
        → (f : X₀ (x ◂ y)) (g : Famₛ M X₀ y z) (h : Famₛ M X₀ (μ M y z) t)
        → Assoc.LHS.f⟨gh⟩ f g h == Assoc.RHS.⟨fg⟩h f g h
      μ-alg-assoc {x} {y} {z} {t} f g h =
        let open Assoc f g h in
          fst= (contr-has-all-paths ⦃ X₁-is-alg _ _ ⦄
            (LHS.f⟨gh⟩ , LHS.LHS)
            (RHS.⟨fg⟩h , transport! (λ x → X₁ ((_ , RHS.⟨fg⟩h) ◂ x)) a=b RHS.RHS))
