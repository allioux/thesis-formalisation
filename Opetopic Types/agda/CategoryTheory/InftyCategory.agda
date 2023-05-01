{-# OPTIONS --rewriting --without-K --allow-unsolved-metas --guardedness #-}

open import HoTT
open import OpetopicType
open import Monad
open import Algebras
open import AlgebrasOver
open import SigmaMonad
open import MonadOver

module CategoryTheory.InftyCategory where

  ∞-category : Set (lsucc lzero)
  ∞-category = Σ (OpetopicType Id) (is-fibrant ∘ Hom)

  ∞-category↓ : (C : ∞-category) → Set (lsucc lzero)
  ∞-category↓ C = Σ (OpetopicType↓ (Id↓ ⊤) (fst C)) (is-fibrant↓ ∘ Hom↓)

  module IdentityCells (X : OpetopicType Id) (X-is-fib : is-fibrant (Hom X)) where

    X₀ = Ob X
    X₁ = Ob (Hom X)
    X₂ = Ob (Hom (Hom X))
    X₁-is-alg = base-fib X-is-fib
    X₂-is-alg = base-fib (hom-fib X-is-fib)
    
    open SlcAlg (Pb Id (Ob X)) (base-fib X-is-fib)
    open SlcAlgLaws (Pb Id (Ob X)) (base-fib X-is-fib) (base-fib (hom-fib X-is-fib))
    
    Obj : Set
    Obj = X₀ ttᵢ

    Arrow : (x y : Obj) → Set
    Arrow x y = X₁ ((ttᵢ , y) , (ttᵢ , cst x))

    Simplex : {x y z : Obj}
      → (f : Arrow x y) (g : Arrow y z)
      → (h : Arrow x z) → Set
    Simplex {x} {y} {z} f g h = Ob (Hom (Hom X))
      ((((ttᵢ , z) , (ttᵢ , cst x)) , h) ,
        src-pd (Pb Id (Ob X)) (Ob (Hom X)) g (cst f) ,
        src-pd-δ (Pb Id (Ob X)) (Ob (Hom X)) g (cst f))

    comp : {x y z : Obj} (g : Arrow y z) (f : Arrow x y) → Arrow x z
    comp g f = μ-alg g (cst f)

    id : (x : Obj) → Arrow x x
    id x = η-alg (ttᵢ , x)

    comp-unit-r : {x y : Obj} (f : Arrow x y) → comp f (id x) == f
    comp-unit-r f = μ-alg-unit-r f

    comp-unit-l : {x y : Obj} (f : Arrow x y) → comp (id y) f == f
    comp-unit-l f = μ-alg-unit-l (cst f)

    comp-assoc : {x y z t : Obj} (f : Arrow x y) (g : Arrow y z) (h : Arrow z t)
      → comp h (comp g f) == comp (comp h g) f
    comp-assoc f g h = μ-alg-assoc h (cst g) (cst f)

    is-iso : {x y : Obj} (f : Arrow x y) → Set
    is-iso {x} {y} f = {z : Obj} (g : Arrow x z)
      → is-contr (Σ (Arrow y z) λ h → comp h f == g)

    _≊_ : (x y : Obj) → Set
    x ≊ y = Σ (Arrow x y) is-iso

    id-is-iso : (x : Obj) → is-iso (id x)
    id-is-iso x g =
      let open Alg (Id / Ob X) (base-fib X-is-fib)
      in equiv-preserves-level
           (Σ-emap-r (λ f → coe-equiv (ap (λ f → f == g) (! (comp-unit-r f)))))
           ⦃ pathto-is-contr g ⦄

    id-to-iso : {x y : Obj} → x == y → x ≊ y
    id-to-iso {x} idp = id x , id-is-iso x

    is-univalent : Set
    is-univalent = (x y : Obj) → is-equiv (id-to-iso {x} {y})

  module IdentityCells↓ {X : OpetopicType Id} (X-is-fib : is-fibrant (Hom X))
                        (X↓ : OpetopicType↓ (Id↓ ⊤) X)
                        (X↓-is-fib : is-fibrant↓ (Hom↓ X↓)) where

    open IdentityCells X X-is-fib public

    X↓₀ = Ob↓ X↓
    X↓₁ = Ob↓ (Hom↓ X↓)
    X↓₂ = Ob↓ (Hom↓ (Hom↓ X↓))
    X↓₁-is-alg = base-fib↓ X↓-is-fib
    X↓₂-is-alg = base-fib↓ (hom-fib↓ X↓-is-fib)
   
    open SlcAlg↓ (Pb↓ (Id↓ ⊤) _ _) (base-fib X-is-fib) (base-fib↓ X↓-is-fib)
    open Laws↓ (Pb↓ (Id↓ ⊤) _ _) {X₁-is-alg = X₁-is-alg} {X₂-is-alg} (base-fib↓ X↓-is-fib) (base-fib↓ (hom-fib↓ X↓-is-fib))

    Obj↓ : Ob X ttᵢ → Set
    Obj↓ x = Ob↓ X↓ tt x

    Arrow↓ : {x y : Obj} (x' : Obj↓ x) (y' : Obj↓ y) (f : Arrow x y) → Set
    Arrow↓ {x} {y} x' y' f = Ob↓ (Hom↓ X↓) ((tt , y') , ttᵢ , cst x') f

    Simplex↓ : {x y z : Obj} {x↓ : Obj↓ x} {y↓ : Obj↓ y} {z↓ : Obj↓ z}
      → {f : Arrow x y} {g : Arrow y z} {h : Arrow x z}
      → (f↓ : Arrow↓ x↓ y↓ f) (g↓ : Arrow↓ y↓ z↓ g) (h↓ : Arrow↓ x↓ z↓ h)
      → Simplex f g h
      → Set
    Simplex↓ {x} {y} {z} {x↓} {y↓} {z↓} {f} {g} {h} f↓ g↓ h↓ α = Ob↓ (Hom↓ (Hom↓ X↓))
      
        ((((tt , z↓) , (ttᵢ , cst x↓)) , h↓) ,
        src-pd↓ (Pb↓ (Id↓ ⊤) (Ob X) (Ob↓ X↓)) (λ {i} → Ob↓ (Hom↓ X↓) {i = i}) g↓ (cst f↓) ,
        src-pd-δ↓ (Pb↓ (Id↓ ⊤) (Ob X) (Ob↓ X↓)) (λ {i} → Ob↓ (Hom↓ X↓) {i = i}) g↓ (cst f↓)) α

    comp↓ : {x y z : Obj} {g : Arrow y z} {f : Arrow x y}
      → {x↓ : Obj↓ x} {y↓ : Obj↓ y} {z↓ : Obj↓ z}
      → (g↓ : Arrow↓ y↓ z↓ g) (f↓ : Arrow↓ x↓ y↓ f)
      → Arrow↓ x↓ z↓ (comp g f)
    comp↓ g↓ f↓ = μ↓-alg g↓ (cst f↓)

    id↓ : {x : Obj} (x↓ : Obj↓ x) → Arrow↓ x↓ x↓ (id x)
    id↓ x↓ = η↓-alg (tt , x↓) 

    comp↓-unit-r : {x y : Obj} {f : Arrow x y}
      → {x↓ : Obj↓ x} {y↓ : Obj↓ y} (f↓ : Arrow↓ x↓ y↓ f)
      → comp↓ f↓ (id↓ x↓) == f↓ [ Arrow↓ x↓ y↓ ↓ comp-unit-r f ]
    comp↓-unit-r f↓ = μ↓-alg-unit-r f↓

    comp↓-unit-l : {x y : Obj} {f : Arrow x y}
      → {x↓ : Obj↓ x} {y↓ : Obj↓ y} (f↓ : Arrow↓ x↓ y↓ f)
      → comp↓ (id↓ y↓) f↓ == f↓ [ Arrow↓ x↓ y↓ ↓ comp-unit-l f ]
    comp↓-unit-l f↓ = μ↓-alg-unit-l (cst f↓)

    comp↓-assoc : {x y z t : Obj} {f : Arrow x y} {g : Arrow y z} {h : Arrow z t}
      → {x↓ : Obj↓ x} {y↓ : Obj↓ y} {z↓ : Obj↓ z} {t↓ : Obj↓ t}
      → (f↓ : Arrow↓ x↓ y↓ f) (g↓ : Arrow↓ y↓ z↓ g) (h↓ : Arrow↓ z↓ t↓ h)
      → comp↓ h↓ (comp↓ g↓ f↓) == comp↓ (comp↓ h↓ g↓) f↓ [ Arrow↓ x↓ t↓ ↓ comp-assoc f g h ]
    comp↓-assoc f↓ g↓ h↓ = μ↓-alg-assoc h↓ (cst g↓) (cst f↓)    

    is-iso↓ : {x y : Obj} {f : Arrow x y}
      → {x↓ : Obj↓ x} {y↓ : Obj↓ y} (f↓ : Arrow↓ x↓ y↓ f)
      → is-iso f
      → Set
    is-iso↓ {x} {x↓ = x↓} {y↓} f↓ f-is-iso =
      {z : Obj} {z↓ : Obj↓ z} {g : Arrow x z} (g↓ : Arrow↓ x↓ z↓ g)
      → is-contr (Σ (Arrow↓ y↓ z↓ (fst (contr-center (f-is-iso g)))) λ h↓ →
                    comp↓ h↓ f↓ == g↓ [ Arrow↓ x↓ z↓ ↓ snd (contr-center (f-is-iso g)) ])

    _≊↓_[_] : {x y : Obj} (x↓ : Obj↓ x) (y↓ : Obj↓ y) → x ≊ y → Set
    _≊↓_[_] {x} {y} x↓ y↓ (f , f-is-iso) = Σ (Arrow↓ x↓ y↓ f) λ f↓ → is-iso↓ f↓ f-is-iso

    pathto↓-is-contr : ∀ {i j} {A : Set i} {B : A → Set j}
      → {x y : A} (u : B y) (p : x == y) 
      → is-contr (Σ (B x) λ v → v == u [ B ↓ p ])
    pathto↓-is-contr {A} {B} u idp = pathto-is-contr u

    id↓-is-iso : {x : Obj} (x↓ : Obj↓ x)  → is-iso↓ (id↓ x↓) (id-is-iso x)
    id↓-is-iso {x} x↓ {z = z} {z↓ = z↓} {g} g↓ = {!!}
    
    id↓-to-iso : {x y : Obj} {x↓ : Obj↓ x} {y↓ : Obj↓ y}
      → {p : x == y}
      → x↓ == y↓ [ Obj↓ ↓ p ]
      → x↓ ≊↓ y↓ [ id-to-iso p ]
    id↓-to-iso {x↓ = x↓} {p = idp} idp = id↓ x↓ , id↓-is-iso x↓

    is-univalent↓ : Set
    is-univalent↓ = {x y : Obj} (x↓ : Obj↓ x) (y↓ : Obj↓ y) (p : x == y) → is-equiv (id↓-to-iso {x↓ = x↓} {y↓} {p})
