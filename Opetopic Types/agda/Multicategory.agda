{-# OPTIONS --without-K --rewriting --guardedness --allow-unsolved-meta #-}

open import HoTT
open import Monad
open import OpetopicType
open import Algebras
open import MonadMap

module Multicategory where

  record WildMulticategory (M : ℳ) (X : Idx (Slc M) → Set) : Set where
    field
      μ-alg : {x : Idx M} {y : Cns M x}
        → {z : Fam M (Cns M) {i = x} y}
        → (α : X (x , y))
        → (β : Famₛ M X {i = x} y z)
        → X (x , μ M y z)
      η-alg : (i : Idx M) → X (i , η M i)
      μ-alg-unit-r : {x : Idx M} {y : Cns M x}
        → (α : X (x , y))
        → μ-alg α (λ p → η-alg (Typ M y p)) == α
      μ-alg-unit-l : {x : Idx M}
        → {y : Fam M (Cns M) (η M x)}
        → (α : Famₛ M X (η M x) y)
        → μ-alg (η-alg x) α == α (η-pos M x)
      μ-alg-assoc : {i : Idx M} {c : Cns M i}
        → {d : Fam M (Cns M) c}
        → {e : Fam M (Cns M) (μ M {i = i} c d)}
        → (x : X (i , c))
        → (y : Famₛ M X c d)      
        → (z : Famₛ M X (μ M c d) e)
        → μ-alg x (λ p → μ-alg (y p) (λ q → z (μ-pos M c d p q)))
          == μ-alg (μ-alg x y) z

  -- Wild multicategory from algebraic families
  module _ (M : ℳ) where

    module From {X₀ : Cell (Slc M)} {X₁ : Cell (Slc M / X₀)} {X₂ : Cell (Slc M / X₀ / X₁)}
                (X₁-is-alg : is-algebraic (Slc M) X₀ X₁)
                (X₂-is-alg : is-algebraic (Slc M / X₀) X₁ X₂) where
                
      open Alg (Slc M) X₁-is-alg
      open SlcAlg M X₁-is-alg
      open SlcAlgLaws M X₁-is-alg X₂-is-alg

      module WM = WildMulticategory

      wcat : WildMulticategory M X₀
      WM.μ-alg wcat = μ-alg
      WM.η-alg wcat = η-alg 
      WM.μ-alg-unit-r wcat = μ-alg-unit-r
      WM.μ-alg-unit-l wcat = μ-alg-unit-l
      WM.μ-alg-assoc wcat = μ-alg-assoc

  -- Algebraic families from wild multicategory
  module To (M : ℳ) {X₀ : Idx (Slc M) → Set} (cat : WildMulticategory M X₀) where
    open WildMulticategory cat

    -- unbiased composition from the biased one
    μ-alg-nb₀ : {i : Idx (Slc M)} (c : Cns (Slc M) i) (x : Fam (Slc M) X₀ c) → X₀ i
    μ-alg-nb₀ (lf x) _ = η-alg x
    μ-alg-nb₀ (nd c δ ε) x =
      let x₁ p q = x (inr (p , q))
          x₂ p = μ-alg-nb₀ (ε p) (x₁ p)
      in μ-alg (x (inl tt)) x₂

    X₁ : Idx (Slc M / X₀) → Set
    X₁ ((i , y) , c , x) = μ-alg-nb₀ c x == y

    X₁-is-alg : is-algebraic (Slc M) X₀ X₁
    X₁-is-alg c x = pathfrom-is-contr (μ-alg-nb₀ c x)

    μ-alg-nb₀-η : {x : Idx (Slc M)} (v : Fam (Slc M) X₀ (η (Slc M) x))
      → μ-alg-nb₀ (η (Slc M) x) v == v (η-pos (Slc  M) x)
    μ-alg-nb₀-η v = μ-alg-unit-r (v (η-pos (Slc  M) _))

    μ-alg-nb₀-γ : {x : Idx M} {y : Cns M x}
      → {z : (p : Pos M y) → Cns M (Typ M y p)}
      → (t : Cns (Slc M) (x , y))
      → (u : (p : Pos M y) → Cns (Slc M) (Typ M y p , z p))
      → (v : Fam (Slc M) X₀ (γ M t u))
      → μ-alg-nb₀ (γ M t u) v
        == μ-alg (μ-alg-nb₀ t λ p → v (γ-pos-inl M t u p))
                 λ p → μ-alg-nb₀ (u p) (λ q → v (γ-pos-inr M t u p q))
    μ-alg-nb₀-γ (lf x) u v = ! (μ-alg-unit-l _)
    
    μ-alg-nb₀-γ (nd {x = x} y z t) u v =
      let v₁ = v true
          v₂ p = μ-alg-nb₀ (t p) (λ q →
            v (inr (p , γ-pos-inl M (t p) (λ q₁ → u (μ-pos M y z p q₁)) q)))
          v₃ p = μ-alg-nb₀ (u p) (λ q → v (inr (μ-pos-fst M y z p ,
            γ-pos-inr M (t (μ-pos-fst M y z p))
              (λ q₁ → u (μ-pos M y z (μ-pos-fst M y z p) q₁))
              (μ-pos-snd M y z p) q)))

          hyp : (p : Pos M y)
            → μ-alg-nb₀ (γ M (t p) (λ q → u (μ-pos M y z p q))) (λ q → v (inr (p , q)))
              == μ-alg (v₂ p) (λ q → v₃ (μ-pos M y z p q))
          hyp p = μ-alg-nb₀-γ (t p) (λ q → u (μ-pos M y z p q)) (λ q → v (inr (p , q)))
      in ap (μ-alg (v true)) (λ= hyp) ∙ μ-alg-assoc v₁ v₂ v₃

    μ-alg-nb₀-μ : {x : Idx (Slc M)} (y : Cns (Slc M) x)
      → (z : Fam (Slc M) (Cns (Slc M)) y)
      → (v : Fam (Slc M) X₀ (μ (Slc M) y z))
      →  μ-alg-nb₀ (μ (Slc M) y z) v
        == μ-alg-nb₀ y (λ p → μ-alg-nb₀ (z p) (λ q → v (μ-pos (Slc M) y z p q)))
    μ-alg-nb₀-μ (lf x) _ _ = idp
    μ-alg-nb₀-μ (nd y z t) u v =
      let u' p q = u (inr (p , q))
          v' p q = v (γ-pos-inr M (u (inl tt)) (λ p → μₛ M (t p) (u' p)) p q)
          hyp p =  μ-alg-nb₀-μ (t p) (u' p) (v' p)
          v₁ = μ-alg-nb₀ (u true) (λ q → v (γ-pos-inl M (u true) (λ p → μₛ M (t p) (λ q₁ → u (inr (p , q₁)))) q))
          v₂ p q = μ-alg-nb₀ (u (inr (p , q))) (λ r →
               v
               (γ-pos-inr M (u true)
                (λ p → μₛ M (t p) (λ q → u (inr (p , q)))) p
                (μ-posₛ M (t p) (λ q → u (inr (p , q))) q r)))
      in μ-alg-nb₀ (γ M (u true) (λ p → μₛ M (t p) (λ q → u (inr (p , q))))) v 
       =⟨ μ-alg-nb₀-γ (u true) (λ p → μₛ M (t p) (λ q → u (inr (p , q)))) v ⟩
         μ-alg v₁ (λ p → μ-alg-nb₀ (μₛ M (t p) (λ q → u (inr (p , q)))) (λ q →
            v
            (γ-pos-inr M (u true)
             (λ p₁ → μₛ M (t p₁) (λ q₁ → u (inr (p₁ , q₁)))) p q)))
       =⟨ ap (μ-alg _) (λ= hyp) ⟩
         μ-alg v₁ (λ p → μ-alg-nb₀ (t p) (v₂ p))
       =∎ 
         
    μ-alg-nb₁ : {i : Idx (Slc M / X₀)} (c : Cns (Slc M / X₀) i)
      → (x : Fam (Slc M / X₀) X₁ c) → X₁ i
    μ-alg-nb₁ (lf (i , x)) _ =  μ-alg-nb₀-η (η-dec (Slc M) X₀ x)  
    μ-alg-nb₁ (nd {i , x} (c , y) z t) v =
         μ-alg-nb₀-μ c (fst ∘ z) (λ p → snd (z (μ-pos-fst (Slc M) _ _ p)) (μ-pos-snd (Slc M) c (fst ∘ z) p)) 
        ∙ ap (μ-alg-nb₀ c) (λ= λ p →  μ-alg-nb₁ (t p) (λ q → v (inr (p , q))) ) 
        ∙ v (inl tt)

    X₂ : Idx (Slc M / X₀ / X₁) → Set
    X₂ ((i , y) , c , x) = μ-alg-nb₁ c x == y
 
    X₂-is-alg : is-algebraic (Slc M / X₀) X₁ X₂
    X₂-is-alg c x = pathfrom-is-contr (μ-alg-nb₁ c x)

    X :  OpetopicType (Slc M)
    Ob X = X₀
    Ob (Hom X) = X₁
    Ob (Hom (Hom X)) = X₂
    Hom (Hom (Hom X)) = Terminal (Slc M / X₀ / X₁ / X₂)

    -- If, in addition, X₁ is a set, then X is fibrant
    module _ (X₀-is-set : (i : Idx (Slc M)) → is-set (X₀ i)) where

      X₁-is-prop : (i : Idx (Slc M / X₀)) → is-prop (X₁ i)
      X₁-is-prop = Alg.alg-levelₛ (Slc M) X₁-is-alg -1 X₀-is-set 

      X₂-is-contr : (i : Idx (Slc M / X₀ / X₁)) → is-contr (X₂ i)
      X₂-is-contr ((i , y) , (c , x)) =  has-level-apply (X₁-is-prop i) _ _
  
      X-is-fib : is-fibrant X
      base-fib X-is-fib = X₁-is-alg
      base-fib (hom-fib X-is-fib) = X₂-is-alg
      base-fib (hom-fib (hom-fib X-is-fib)) {i} σ ν =
        Σ-level (X₂-is-contr i) (cst Unit-level)
      hom-fib (hom-fib (hom-fib X-is-fib)) = Terminal-is-fib _
    
  
  module _ (M : ℳ) where
    
    module ToFrom {X₀ : Cell (Slc M)} {X₁ : Cell (Slc M / X₀)} {X₂ : Cell (Slc M / X₀ / X₁)}
                  (X₁-is-alg : is-algebraic (Slc M) X₀ X₁)
                  (X₂-is-alg : is-algebraic (Slc M / X₀) X₁ X₂) where
      open Alg (Slc M) X₁-is-alg
      open SlcAlg M X₁-is-alg

      comp=μ-alg-nb₀ : {i : Idx (Slc M)} (c : Cns (Slc M) i) (x : Fam (Slc M) X₀ c)
        → comp c x
          == To.μ-alg-nb₀ M (From.wcat M X₁-is-alg X₂-is-alg) c x
      comp=μ-alg-nb₀ (lf i) x = ap (comp _) (λ= ⊥-elim)
      comp=μ-alg-nb₀ (nd {i} c δ ε) x =
        let hyp p = comp=μ-alg-nb₀ (ε p) (λ q → x (inr (p , q)))
        in alg-nd M X₁-is-alg X₂-is-alg ε x
           ∙ ap (μ-alg (x true)) (λ= hyp) 

      to-from-X₁ : (i : Idx (Slc M / X₀))
        → To.X₁ M (From.wcat M X₁-is-alg X₂-is-alg) i ≃ X₁ i
      to-from-X₁ ((i , y) , (c , x)) =
        let e = cell-eq-id (fill c x) y ⁻¹
        in transport (λ z → (z == y) ≃ X₁ ((i , y) , (c , x))) (comp=μ-alg-nb₀ c x) e 
      
      module _ (Xₙ : OpetopicType (Slc M / X₀ / X₁ / X₂))
               (Xₙ-is-alg : is-fibrant Xₙ)
               (X₃-is-alg : is-algebraic (Slc M / X₀ / X₁) X₂ (Ob Xₙ))
               (X₀-is-set : (i : Idx (Slc M)) → is-set (X₀ i)) where

        X : OpetopicType (Slc M)
        Ob X = X₀
        Ob (Hom X) = X₁
        Ob (Hom (Hom X)) = X₂
        Hom (Hom (Hom X)) = Xₙ

        X-is-fib : is-fibrant X
        base-fib X-is-fib = X₁-is-alg
        base-fib (hom-fib X-is-fib) = X₂-is-alg
        base-fib (hom-fib (hom-fib X-is-fib)) = X₃-is-alg
        hom-fib (hom-fib (hom-fib X-is-fib)) = Xₙ-is-alg
        
        X' = To.X M (From.wcat M X₁-is-alg X₂-is-alg)
        X'-is-alg = To.X-is-fib M (From.wcat M X₁-is-alg X₂-is-alg) X₀-is-set

        X₂'-is-contr = To.X₂-is-contr M (From.wcat M X₁-is-alg X₂-is-alg) X₀-is-set
        X₁-is-prop = alg-levelₛ -1 X₀-is-set
        X₂-is-contr = Alg.alg-levelₛ (Slc M / X₀) X₂-is-alg -2 X₁-is-prop 

        lem : (M : ℳ) {X Y : OpetopicType M}
          → (X-is-alg : is-fibrant X)
          → (Y-is-alg : is-fibrant Y)
          → (X₀-is-contr : (i : Idx M) → is-contr (Ob X i))
          → (Y₀-is-contr : (i : Idx M) → is-contr (Ob Y i))
          → X ≃ₒ Y
        Ob≃ (lem M X-is-alg Y-is-alg X₀-is-contr Y₀-is-contr) i =
          cst (contr-center (Y₀-is-contr i)) , contr-to-contr-is-equiv _ (X₀-is-contr i) (Y₀-is-contr i)
        Hom≃ (lem M X-is-alg Y-is-alg X₀-is-contr Y₀-is-contr) =
          let X₁-is-contr = Alg.alg-level₋₂ M (base-fib X-is-alg) X₀-is-contr  
              Y₁-is-contr = Alg.alg-level₋₂ M (base-fib Y-is-alg) Y₀-is-contr
          in lem _ (hom-fib X-is-alg) (reindex-alg _ _ (hom-fib Y-is-alg)) X₁-is-contr λ _ → Y₁-is-contr _

        X≃X' : X ≃ₒ X'
        Ob≃ X≃X' i = ide _
        Ob≃ (Hom≃ X≃X') i = to-from-X₁ i ⁻¹
        Hom≃ (Hom≃ X≃X') = lem _ (hom-fib (hom-fib X-is-fib))
                       (reindex-alg _ _ (reindex-alg _ _ (hom-fib (hom-fib X'-is-alg)))) X₂-is-contr
                       (λ i → X₂'-is-contr (idx⇒ [ [ Id⇒ (Slc M) / idf _ ]* / <– (to-from-X₁ _) ]*  i))

    module FromTo {X₀ : Cell (Slc M)} {X₁ : Cell (Slc M / X₀)} (C : WildMulticategory M X₀) where
      open WildMulticategory

      X₁-is-alg = To.X₁-is-alg M C
      X₂-is-alg = To.X₂-is-alg M C
    
      C' = From.wcat M X₁-is-alg X₂-is-alg

      η=η' : (i : Idx M) → η-alg C i == η-alg C' i
      η=η' i = idp

      μ=μ' : {x :  Idx M} {y : Cns M x} {z : Fam M (Cns M) y}
        → (f : X₀ (x , y)) (g : Famₛ M X₀ y z) → μ-alg C f g == μ-alg C' f g
      μ=μ' f g = ap (μ-alg C f) (λ= λ p → ! (μ-alg-unit-r C (g p))) 


