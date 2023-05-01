{-# OPTIONS --without-K --rewriting --guardedness --allow-unsolved-meta #-}

open import HoTT
open import Monad
open import MonadOver
open import OpetopicType
open import Algebras
open import FundamentalThm
open import MonadMap
open import Utils

module ExplicitComp where

  module _ (M : ℳ) {X₀ : Cell M}
           {X₁ : Cell (M / X₀)} {X₂ : Cell (M / X₀ / X₁)}
           (X₁-is-alg : is-algebraic M X₀ X₁) (X₂-is-alg : is-algebraic (M / X₀) X₁ X₂)  where

    open Alg M X₁-is-alg
    
    tree-contr : {i : Idx M} (c : Cns M i) (d : Fam M (Cns M) c)
      → (z : Fam M X₀ (μ M c d))
      → is-contr (Σ (Σ (X₀ i) (λ x → (Fam M X₀ c))) λ (x , y) →
                    Σ (X₁ ((i , x) , (c , y))) λ _ → Famₛ (Pb M X₀) X₁ {i = i , x} (c , y) (λ p → d p , λ q → z (μ-pos M c d p q)))
    tree-contr {i} c d z = {!!}
     -- {! Σ-level (equiv-preserves-level (eq {C = λ p x → X₁ ((Typ M c p , x) , (d p , _))} ⁻¹)
     --                   ⦃ Π-level λ p → X₁-is-alg (d p)  _ ⦄) λ (y , _) → X₁-is-alg c y !}
      where eq : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
               → Σ (Π A B) (λ f → (a : A) → C a (f a)) ≃ ((a : A) → Σ (B a) (λ b → C a b))
            eq = equiv (λ f a → fst f a , snd f a) (λ f → fst ∘ f , snd ∘ f) (λ _ → idp) λ _ → idp

    tree-elim : {i : Idx M} {c : Cns M i} {d : Fam M (Cns M) c}
        → {z : Fam M X₀ (μ M c d)}
        → (P : {x : X₀ i} {y : Fam M X₀ c} 
          → (f : X₁ ((i , x) , (c , y)))
          → (g : Famₛ (Pb M X₀) X₁ {i = i , x} (c , y) (λ p → d p , λ q → z (μ-pos M c d p q)))
          → Set)
        → (p* : P (fill c (λ p → comp (d p) λ q → z (μ-pos M c d p q)))
                  (λ p → fill (d p) λ q → z (μ-pos M c d p q)))
        → {x : X₀ i} {y : Fam M X₀ c} 
        → (f : X₁ ((i , x) , (c , y)))
        → (g : Famₛ (Pb M X₀) X₁ {i = i , x}  (c , y) (λ p → d p , λ q → z (μ-pos M c d p q)))
        → P f g
    tree-elim {c = c} {d} {z} P p* f g =
      transport (λ ((x , y) , (f , g)) → P f g) (contr-has-all-paths ⦃ tree-contr c d z ⦄ _ _) p* 

  module _ (M : ℳ) {X₀ : Cell M}
           {X₁ : Cell (M / X₀)} (X₁-is-alg : is-algebraic M X₀ X₁)  where
    open Alg M X₁-is-alg

    X₁' : Cell (M / X₀)
    X₁' ((i , x) , (c , y)) = comp c y == x

    X₁'-is-alg : is-algebraic M X₀ X₁'
    X₁'-is-alg c y = pathfrom-is-contr (comp c y)

    X₁≃X₁' : (i : Idx (M / X₀)) → X₁ i ≃ X₁' i
    X₁≃X₁' ((i , x) , (c , y)) = cell-eq-id (fill c y) x

    module _ {X₂ : Cell (M / X₀ / X₁)} (X₂-is-alg : is-algebraic (M / X₀) X₁ X₂)
             {X₃ : Cell (M / X₀ / X₁ / X₂)} (X₃-is-alg : is-algebraic (M / X₀ / X₁) X₂ X₃) where

      open SlcAlg (Pb M X₀) X₂-is-alg
      open AlgLaws M X₁-is-alg X₂-is-alg

      module _ {i : Idx M}  
         {c : Cns M i}
         {d : Fam M (Cns M) c}
         {x : X₀ i}
         {y : Fam M X₀ c}
         {z : Fam M X₀ (μ M c d)}
         (f : X₁ ((i , x) , (c , y)))
         (g : Famₛ (Pb M X₀) X₁ {i = i , x} (c , y) λ p → d p , λ q → z (μ-pos M c d p q)) where
         
        μ-alg-map : –> (cell-eq-id (fill (μ M c d) z) x) (μ-alg f g)
                == alg-μ c d z
                  ∙ ap (comp c) (λ= λ p → –> (cell-eq-id (fill (d p) _) _) (g p))
                  ∙ –> (cell-eq-id (fill c y) _) f
        μ-alg-map = tree-elim M X₁-is-alg X₂-is-alg {z = z} P d* f g 
          where f' = (fill c (λ p → comp (d p) (λ q₁ → z (μ-pos M c (λ p₁ → d p₁) p q₁))))

                g' : (p : _) → _
                g' p = fill (d p) (λ q₁ → z (μ-pos M c (λ p₁ → d p₁) p q₁))

                d* = –> (cell-eq-id (fill (μ M c d) z) _) (μ-alg f' g')
                    =⟨ idp ⟩
                  alg-μ c d z
                    =⟨ ! (∙-unit-r _) ⟩
                  alg-μ c d z ∙ idp ∙ idp
                    =⟨ ap (λ (p , q) → alg-μ c d z ∙ (ap (comp c) p) ∙ q)
                         (pair×= (λ=-η idp ∙ ap λ= (λ= λ p → ! (cell-eq-id-β (fill (d p) _))))
                                 (! (cell-eq-id-β (fill c _)))) ⟩
                  alg-μ c d z
                  ∙ ap (comp c) (λ= λ p → –> (cell-eq-id (fill (d p) _) _) (g' p))
                  ∙ –> (cell-eq-id (fill c _) _) f' =∎ 
          
                P : {x : X₀ i} {y : _} (f : _) (g : _) → Set
                P {x} {y} f g =
                  –> (cell-eq-id (fill (μ M c d) z) x) (μ-alg f g)
                  == alg-μ c d z
                     ∙ ap (comp c) (λ= λ p → –> (cell-eq-id (fill (d p) _) _) (g p))
                     ∙ –> (cell-eq-id (fill c y) _) f
                                 
         
      comp₂ : {i : Idx (M / X₀)} (c : Cns (M / X₀) i) → Fam (M / X₀) X₁' c → X₁' i 
      comp₂ (lf (i , x)) _ = alg-η (cst x)
      comp₂ (nd {x = i , x} (c , y) z t) f =
        let hyp p = comp₂ (t p) λ q → f (inr (p , q))
        in alg-μ c (fst ∘ z) (λ p → snd (z (μ-pos-fst M c (fst ∘ z) p)) (μ-pos-snd M c (fst ∘ z) p))
          ∙ ap (comp c) (λ= hyp) 
          ∙ f (inl tt)

      X₂' : Cell (M / X₀ / X₁')
      X₂' ((i , x) , (c , y)) = comp₂ c y == x

      X₂'-is-alg : is-algebraic (M / X₀) X₁' X₂'
      X₂'-is-alg c y = pathfrom-is-contr (comp₂ c y)

      module X₂-alg = Alg (M / X₀) X₂-is-alg
      
      -- X₁≃X₁'is a morphism of algebras
      X₁≃X₁'-map : {i : Idx (M / X₀)} (c : Cns (M / X₀) i) (x : Fam (M / X₀) X₁ c)
        → –> (X₁≃X₁' i) (X₂-alg.comp c x) == comp₂ c (λ p → –> (X₁≃X₁' _) (x p))
      X₁≃X₁'-map (lf (i , x)) _ = 
        let e = X₁≃X₁' ((i , x) , η M i , η-dec M (λ z → X₀ z) x)

            P x = X₁ ((i , x (η-pos M i)) , η M i , x)

            p : λ= (cst idp) == idp
            p = ! (λ=-η idp)

            q =
              transport P (λ= (cst idp)) (η-alg (_ , x))
                =⟨ ap (λ p → transport P p (η-alg (_ , x))) p ⟩
              η-alg (_ , x)
                =⟨ ap (X₂-alg.comp (lf (i , x))) (λ= λ ()) ⟩
              X₂-alg.comp (lf (i , x)) _ =∎

        in ap (–> e) (! q) 
      X₁≃X₁'-map (nd {x = (i , x)} (c , y) z t) v = d*
        where z' : (p : _) → _
              z' p = snd (z (μ-pos-fst M c (fst ∘ z) p)) (μ-pos-snd M c (fst ∘ z) p)

              d* =
                let d' = (nd {x = (i , x)} (c , y) z t)
                    
                in –> (X₁≃X₁' ((i , _) , μ M c (fst ∘ (λ p → z p)) , z')) (X₂-alg.comp d' v)
                   
                     =⟨ ap (–> (X₁≃X₁' ((i , _) , μ M c (fst ∘ (λ p → z p)) , z')))
                           (alg-nd (Pb M X₀) X₂-is-alg X₃-is-alg _ v) ⟩
                        
                   –> (X₁≃X₁' ((i , _) , μ M c (fst ∘ (λ p → z p)) , z'))
                      (μ-alg (v (inl tt)) (λ p → X₂-alg.comp _ (λ q → v (inr (p , q)))))
                     
                     =⟨ μ-alg-map (v (inl tt)) (λ p → X₂-alg.comp _ (λ q → v (inr (p , q)))) ⟩
           
                   alg-μ c (fst ∘ z) (λ p → snd (z (μ-pos-fst M c (fst ∘ z) p))
                     (μ-pos-snd M c (fst ∘ z) p))
                   ∙ ap (comp c) (λ= λ p → –> (X₁≃X₁' _) (X₂-alg.comp _ (λ q → (v (inr (p , q)))))) 
                   ∙ –> (X₁≃X₁' ((i , _) , c , _)) (v (inl tt))
                
                     =⟨ ap (λ p → alg-μ c (fst ∘ z) (λ p → snd (z (μ-pos-fst M c (fst ∘ z) p))
                          (μ-pos-snd M c (fst ∘ z) p))
                        ∙ ap (comp c) (λ= p) 
                        ∙ –> (X₁≃X₁' ((i , _) , c , _)) (v (inl tt))) (λ= λ p → X₁≃X₁'-map (t p)
                          (λ q → v (inr (p , q)))) ⟩
                       
                   alg-μ c (fst ∘ z) (λ p → snd (z (μ-pos-fst M c (fst ∘ z) p))
                     (μ-pos-snd M c (fst ∘ z) p))
                   ∙ ap (comp c) (λ= λ p → comp₂ _ λ q → –> (X₁≃X₁' _) (v (inr (p , q)))) 
                   ∙ –> (X₁≃X₁' ((i , _) , c , _)) (v (inl tt)) =∎
                   
      X₂≃X₂' : (i : Idx (M / X₀)) (c : Cns (M / X₀) i) (x : Fam (M / X₀) X₁ c) (y : X₁ i)
        → X₂ ((i , y) ◂ (c , x))
          ≃ X₂' ((i , –> (X₁≃X₁' i) y) ◂ (c , λ p → –> (X₁≃X₁' (Typ (M / X₀) c p)) (x p)))
      X₂≃X₂' i c x y =
        coe-equiv (ap (λ x → x == –> (X₁≃X₁' i) y) (X₁≃X₁'-map c x)) 
        ∘e ap-equiv (X₁≃X₁' i) (X₂-alg.comp c x) y 
        ∘e X₂-alg.cell-eq-id (X₂-alg.fill c x) y 
