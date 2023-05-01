{-# OPTIONS --without-K --rewriting --guardedness #-}

open import HoTT
open import Monad
open import MonadOver
open import OpetopicType
open import FundamentalThm
open import MonadMap
open import MonadOver
open import Algebras

module AlgebrasOver where

  module _ {M : ℳ} (M↓ : ℳ↓ M) {X : Cell (Slc M)} (X↓ : Cell↓ (Slc↓ M↓) X)
           {x : Idx M} {y : Cns M x} {z : Fam M (Cns M) y}
           {x↓ : Idx↓ M↓ x} {y↓ : Cns↓ M↓ x↓ y} {z↓ : Fam↓ M↓ (Cns↓ M↓) y↓ z}
           {f : X (x , y)} {g : Famₛ M X y z}
           (f↓ : X↓ (x↓ , y↓) f) (g↓ : Fam↓ₛ M↓ X↓ y↓ z↓ g) where

    src-pd↓ : Pd↓ M↓ (x↓ , μ↓ M↓ y↓ z↓) (src-pd M X f g) 
    src-pd↓ = nd↓ y↓ z↓ (λ p → η↓ (Slc↓ M↓) (Typ↓ M↓ y↓ p , z↓ p))  
  
    src-pd-δ↓ : Fam↓ (Slc↓ M↓) X↓ src-pd↓ (src-pd-δ M X f g)
    src-pd-δ↓ (inl tt) = f↓
    src-pd-δ↓ (inr (p , inl tt)) = g↓ p

    pd₂↓ : ⟦ Slc↓ M↓ ⟧↓ X↓ (x↓ , μ↓ M↓ y↓ z↓) (pd₂ M X f g)
    pd₂↓ = (src-pd↓ , src-pd-δ↓)

  module _ {M : ℳ} (M↓ : ℳ↓ M) where

    module Alg↓ {X₀ : Cell M} {X₁ : Cell (M / X₀)}
                (X₁-is-alg : is-algebraic M X₀ X₁)
                {X↓₀ : Cell↓ M↓ X₀} {X↓₁ : Cell↓ (M↓ /↓ X↓₀) X₁}
                (X↓₁-is-alg : is-algebraic↓ M↓ X↓₀ X↓₁)
                where
                
      open Alg M X₁-is-alg
               
      comp↓' : {i : Idx M} {i↓ : Idx↓ M↓ i}
        → {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
        → {x : Fam M X₀ c} (x↓ : Fam↓ M↓ X↓₀ c↓ x)
        → {y : X₀ i} (yᶠ : X₁ ((i , y) , (c , x)))
        → X↓₀ i↓ y
      comp↓' {c = c} c↓ {x = x} x↓ yᶠ = fst $ contr-center $ X↓₁-is-alg c↓ x↓ yᶠ

      fill↓' : {i : Idx M} {i↓ : Idx↓ M↓ i}
        → {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
        → {x : Fam M X₀ c} (x↓ : Fam↓ M↓ X↓₀ c↓ x)
        → {y : X₀ i} (yᶠ : X₁ ((i , y) , (c , x)))
        → X↓₁ ((i↓ , comp↓' c↓ x↓ yᶠ) , (c↓ , x↓)) yᶠ
      fill↓' {c = c} c↓ {x} x↓ yᶠ = snd $ contr-center $ X↓₁-is-alg c↓ x↓ yᶠ

      cell-eq-id↓' : {i : Idx M} {c : Cns M i} {x : Fam M X₀ c} {y : X₀ i}
        → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c) (x↓ : Fam↓ M↓ X↓₀ c↓ x) (y↓ : X↓₀ i↓ y)
        → (f : X₁ ((i , y) , (c , x)))
        → X↓₁ ((i↓ , y↓) , c↓ , x↓) f ≃ (comp↓' c↓ x↓ f == y↓)
      cell-eq-id↓' {i} {c} {x} {y} {i↓ = i↓} c↓ x↓ y↓ f =
        fundamental-thm (X↓₀ i↓ y) (λ y↓ → X↓₁ ((i↓ , y↓) , (c↓ , x↓)) f)
          (X↓₁-is-alg c↓ x↓ f) (comp↓' c↓ x↓ f) (fill↓' c↓ x↓ f) y↓

      comp↓ : {i : Idx M} {i↓ : Idx↓ M↓ i}
        → {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
        → {x : Fam M X₀ c} (x↓ : Fam↓ M↓ X↓₀ c↓ x)
        → X↓₀ i↓ (comp c x)
      comp↓ {c = c} c↓ {x = x} x↓ = comp↓' c↓ x↓ (fill c x)

      fill↓ : {i : Idx M} {i↓ : Idx↓ M↓ i}
        → {c : Cns M i} (c↓ : Cns↓ M↓ i↓ c)
        → {x : Fam M X₀ c} (x↓ : Fam↓ M↓ X↓₀ c↓ x)
        → X↓₁ ((i↓ , comp↓ c↓ x↓) , (c↓ , x↓)) (fill c x)
      fill↓ {c = c} c↓ {x} x↓ = fill↓' c↓ x↓ (fill c x)

      cell-eq-id↓ : {i : Idx M} {c : Cns M i} {x : Fam M X₀ c}
        → {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c) (x↓ : Fam↓ M↓ X↓₀ c↓ x) (y↓ : X↓₀ i↓ (comp c x))
        → X↓₁ ((i↓ , y↓) ◂ (c↓ , x↓)) (fill c x) ≃ (comp↓ c↓ x↓ == y↓)
      cell-eq-id↓ {i} {c} {x} {i↓ = i↓} c↓ x↓ y↓ =
        fundamental-thm (X↓₀ i↓ (comp c x)) (λ y↓ → X↓₁ ((i↓ , y↓) , (c↓ , x↓)) (fill c x))
          (X↓₁-is-alg c↓ x↓ (fill c x)) (comp↓' c↓ x↓ (fill c x)) (fill↓' c↓ x↓ (fill c x)) y↓

  module _ {M : ℳ} (M↓ : ℳ↓ M) where
  
    module SlcAlg↓ {X₀ : Cell (Slc M)} {X₁ : Cell (Slc M / X₀)}
                (X₁-is-alg : is-algebraic (Slc M) X₀ X₁)
                {X↓₀ : Cell↓ (Slc↓ M↓) X₀} {X↓₁ : Cell↓ (Slc↓ M↓ /↓ X↓₀) X₁}
                (X↓₁-is-alg : is-algebraic↓ (Slc↓ M↓) X↓₀ X↓₁) where

      open SlcAlg M X₁-is-alg
      open Alg↓ (Slc↓ M↓) X₁-is-alg X↓₁-is-alg

      η↓-alg : {i : Idx M} (i↓ : Idx↓ M↓ i)
        → X↓₀ (i↓ , η↓ M↓ i↓) (η-alg i)
      η↓-alg {i} i↓ = comp↓ (lf↓ i↓) ⊥-elim

      η↓-alg-fill : {i : Idx M} (i↓ : Idx↓ M↓ i)
        → X↓₁ (((i↓ , η↓ M↓ i↓) , η↓-alg i↓) , (lf↓ i↓ , ⊥-elim)) (η-alg-fill i)
      η↓-alg-fill {i} i↓ = fill↓ (lf↓ i↓) ⊥-elim

      μ↓-alg : {x : Idx M} {y : Cns M x}
        → {z : Fam M (Cns M) {i = x} y}
        → {f : X₀ (x , y)}
        → {g : Famₛ M X₀ {i = x} y z}
        → {x↓ : Idx↓ M↓ x} {y↓ : Cns↓ M↓ x↓ y}
        → {z↓ : Fam↓ M↓ (Cns↓ M↓) y↓ z}
        → (f↓ : X↓₀ (x↓ , y↓) f)
        → (g↓ : Fam↓ₛ M↓ X↓₀ y↓ z↓ g)
        → X↓₀ (x↓ , μ↓ M↓ y↓ z↓) (μ-alg f g)
      μ↓-alg f↓ g↓ =
        let (c , v) = pd₂↓ M↓ X↓₀ f↓ g↓ 
        in comp↓ c v

      μ↓-alg-fill : {x : Idx M} {y : Cns M x}
        → {z : Fam M (Cns M) {i = x} y}
        → {f : X₀ (x , y)}
        → {g : Famₛ M X₀ {i = x} y z}
        → {x↓ : Idx↓ M↓ x} {y↓ : Cns↓ M↓ x↓ y}
        → {z↓ : Fam↓ M↓ (Cns↓ M↓) y↓ z}
        → (f↓ : X↓₀ (x↓ , y↓) f)
        → (g↓ : Fam↓ₛ M↓ X↓₀ y↓ z↓ g)
        → X↓₁ (((x↓ , μ↓ M↓ y↓ z↓) , μ↓-alg f↓ g↓) , pd₂↓ M↓ X↓₀ f↓ g↓) (μ-alg-fill f g)
      μ↓-alg-fill f↓ g↓ =
        let (c , v) = pd₂↓ M↓ X↓₀ f↓ g↓ 
        in fill↓ c v

  module _ {M : ℳ} (M↓ : ℳ↓ M) where

    module _ {X₀ : Cell M} {X₁ : Cell (M / X₀)} {X₂ : Cell (M / X₀ / X₁)}
             {X↓₀ : Cell↓ M↓ X₀} {X↓₁ : Cell↓ (M↓ /↓ X↓₀) X₁} {X↓₂ : Cell↓ (M↓ /↓ X↓₀ /↓ X↓₁) X₂}
             (X₁-is-alg : is-algebraic M X₀ X₁) (X₂-is-alg : is-algebraic (M / X₀) X₁ X₂)
             (X↓₁-is-alg : is-algebraic↓ M↓ X↓₀ X↓₁) (X↓₂-is-alg : is-algebraic↓ (M↓ /↓ X↓₀) X↓₁ X↓₂)
             where
      open Alg↓ M↓ X₁-is-alg X↓₁-is-alg
      open AlgLaws M X₁-is-alg X₂-is-alg

      postulate
      
        alg-η↓ : {i : Idx M} (x : Fam M X₀ (η M i))
          → (i↓ : Idx↓ M↓ i) (x↓ : Fam↓ M↓ X↓₀ (η↓ M↓ i↓) x)
          → comp↓ (η↓ M↓ i↓) x↓
            == x↓ (η-pos M i) [ X↓₀ i↓ ↓ alg-η x ]

        alg-μ↓ : {x : Idx M} {y : Cns M x} {z : Fam M (Cns M) y}
          → (v : Fam M X₀ (μ M y z))
          → {x↓ : Idx↓ M↓ x} (y↓ : Cns↓ M↓ x↓ y) (z↓ : Fam↓ M↓ (Cns↓ M↓) y↓ z)
          → (v↓ : Fam↓ M↓ X↓₀ (μ↓ M↓ y↓ z↓) v)
          → comp↓ (μ↓ M↓ y↓ z↓) v↓
            == comp↓ y↓ (λ p → comp↓ (z↓ p) (λ q → v↓ (μ-pos M y z p q)))
            [ X↓₀ x↓ ↓ alg-μ y z v ]

  module _ {M : ℳ} (M↓ : ℳ↓ M) where
  
    module Laws↓ {X₀ : Cell (Slc M)} {X₁ : Cell (Slc M / X₀)} {X₂ : Cell (Slc M / X₀ / X₁)}
                 {X↓₀ : Cell↓ (Slc↓ M↓) X₀} {X↓₁ : Cell↓ (Slc↓ M↓ /↓ X↓₀) X₁}
                 {X↓₂ : Cell↓ (Slc↓ M↓ /↓ X↓₀ /↓ X↓₁) X₂}
                 {X₁-is-alg : is-algebraic (Slc M) X₀ X₁}
                 {X₂-is-alg : is-algebraic (Slc M / X₀) X₁ X₂}
                 (X↓₁-is-alg : is-algebraic↓ (Slc↓ M↓) X↓₀ X↓₁)
                 (X↓₂-is-alg : is-algebraic↓ (Slc↓ M↓ /↓ X↓₀) X↓₁ X↓₂) where
                 
      open Alg↓ (Slc↓ M↓) X₁-is-alg X↓₁-is-alg
      open SlcAlg↓ M↓ X₁-is-alg X↓₁-is-alg
      open AlgLaws (Slc M) X₁-is-alg X₂-is-alg
      open SlcAlgLaws M X₁-is-alg X₂-is-alg

      postulate
      
        μ↓-alg-unit-r : {x : Idx M} {y : Cns M x} {f : X₀ (x , y)}
          → {x↓ : Idx↓ M↓ x} {y↓ : Cns↓ M↓ x↓ y} (f↓ : X↓₀ (x↓ , y↓) f)
          → μ↓-alg f↓ (λ p → η↓-alg (Typ↓ M↓ y↓ p)) == f↓
            [ X↓₀ (x↓ , y↓) ↓ μ-alg-unit-r f ]

        μ↓-alg-unit-l : {x : Idx M} {y : Fam M (Cns M) (η M x)} {f : Famₛ M X₀ (η M x) y}
          → {x↓ : Idx↓ M↓ x} {y↓ : Fam↓ M↓ (Cns↓ M↓) (η↓ M↓ x↓) y}
          → (f↓ : Fam↓ₛ M↓ X↓₀ (η↓ M↓ x↓) y↓ f)
          → μ↓-alg (η↓-alg x↓) f↓ == f↓ (η-pos M x)
            [ X↓₀ (x↓ , y↓ (η-pos M x)) ↓ μ-alg-unit-l f ]

        μ↓-alg-assoc : {x : Idx M} {y : Cns M x}
          → {z : Fam M (Cns M) y}
          → {t : Fam M (Cns M) (μ M {i = x} y z)}
          → {f : X₀ (x , y)}
          → {g : Famₛ M X₀ y z}      
          → {h : Famₛ M X₀ (μ M y z) t}
          → {x↓ : Idx↓ M↓ x} {y↓ : Cns↓ M↓ x↓ y}
          → {z↓ : Fam↓ M↓ (Cns↓ M↓) y↓ z}
          → {t↓ : Fam↓ M↓ (Cns↓ M↓) (μ↓ M↓ {i = x} y↓ z↓) t}
          → (f↓ : X↓₀ (x↓ , y↓) f)
          → (g↓ : Fam↓ₛ M↓ X↓₀ y↓ z↓ g)      
          → (h↓ : Fam↓ₛ M↓ X↓₀ (μ↓ M↓ y↓ z↓) t↓ h)
          →  μ↓-alg f↓ (λ p → μ↓-alg (g↓ p) (λ q → h↓ (μ-pos M y z p q)))
             == μ↓-alg (μ↓-alg f↓ g↓) h↓
             [ X↓₀ (x↓ , μ↓ M↓ y↓ (λ p → μ↓ M↓ (z↓ p) λ q → t↓ (μ-pos M y z p q)))
               ↓ μ-alg-assoc f g h ] 
       
