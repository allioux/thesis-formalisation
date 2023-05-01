{-# OPTIONS --rewriting --without-K --guardedness #-}

open import OpetopicType
open import HoTT
open import AlgebrasOver
open import Monad
open import MonadOver
open import CategoryTheory.InftyCategory
open import CategoryTheory.Interval
open import CategoryTheory.Fibrations

module CategoryTheory.Functor where

  module _ (C↓ : ∞-category↓ 𝟚)
           (fib : is-fibration 𝟚 C↓)
           (opfib : is-opfibration 𝟚 C↓) where
    
    private
      X↓ = fst C↓
      fib↓ = snd C↓
      C↓₂-is-alg = base-fib↓ fib↓

    open IdentityCells↓ 𝟚ₒ-is-fibrant X↓ fib↓
    open Alg↓ (Id↓ ⊤ /↓ Ob↓ X↓) (base-fib 𝟚ₒ-is-fibrant) (base-fib↓ fib↓)
    open SlcAlg↓ (Pb↓ (Id↓ ⊤) (cst Bool) (Ob↓ X↓)) (base-fib 𝟚ₒ-is-fibrant) (base-fib↓ fib↓)

    f₀ : Ob↓ X↓ tt false → Ob↓ X↓ tt true
    f₀ x = fst (opfib tt x)

    f₀ᶠ : (x : Ob↓ X↓ tt false) → Arrow↓ x (f₀ x) tt
    f₀ᶠ x = fst (snd (opfib tt x))

    f₀ᶠ-is-cocart : (x : Ob↓ X↓ tt false) → is-cocartesian 𝟚 C↓ (f₀ᶠ x)
    f₀ᶠ-is-cocart x = snd (snd (opfib tt x))

    g₀ : Ob↓ X↓ tt true → Ob↓ X↓ tt false
    g₀ x = fst (fib tt x)

    g₀ᶠ : (x : Ob↓ X↓ tt true) → Arrow↓ (g₀ x) x tt
    g₀ᶠ x = fst (snd (fib tt x))

    g₀ᶠ-is-cart : (x : Ob↓ X↓ tt true) → is-cartesian 𝟚 C↓ (g₀ᶠ x)
    g₀ᶠ-is-cart x = snd (snd (fib tt x))

    adj : (x : Ob↓ X↓ tt false)
      → (y : Ob↓ X↓ tt true)
      → Arrow↓ x (g₀ y) tt
        ≃ Arrow↓ (f₀ x) y tt
    adj x y = g , is-eq g h g-h h-g
      where

            g-aux : (f : Arrow↓ x (g₀ y) tt)
              → Σ (Arrow↓ (f₀ x) y tt) λ f' →
                  μ↓-alg f' (cst (f₀ᶠ x)) == μ↓-alg (g₀ᶠ y) (cst f)
            g-aux f = contr-center (f₀ᶠ-is-cocart x true y tt (μ↓-alg (g₀ᶠ y) (cst f)) tt idp)

            g : Arrow↓ x (g₀ y) tt → Arrow↓ (f₀ x) y tt
            g = fst ∘ g-aux

            h-aux : (f : Arrow↓ (f₀ x) y tt)
              → Σ (Arrow↓ x (g₀ y) tt) λ h →
                  μ↓-alg (g₀ᶠ y) (cst h) == μ↓-alg f (cst (f₀ᶠ x))
            h-aux f = contr-center (g₀ᶠ-is-cart y false x tt (μ↓-alg f (cst (f₀ᶠ x))) tt idp)

            h : Arrow↓ (f₀ x) y tt → Arrow↓ x (g₀ y) tt
            h = fst ∘ h-aux

            g-h : g ∘ h ∼ idf _
            g-h f = 
              let p : μ↓-alg (g₀ᶠ y) (cst (h f)) == μ↓-alg f (cst (f₀ᶠ x))
                  p = let (c , v) = pd₂↓ (Pb↓ (Id↓ ⊤) (Ob (fst 𝟚)) (Ob↓ X↓)) (Ob↓ (Hom↓ X↓))
                                         (g₀ᶠ y) (cst (h f))
                      in fst= (contr-has-all-paths ⦃ base-fib↓ fib↓ c v tt ⦄
                                (μ↓-alg (g₀ᶠ y) (cst (h f)) , μ↓-alg-fill (g₀ᶠ y) (cst (h f)))
                                (μ↓-alg f (cst (f₀ᶠ x)) ,
                                  <– (cell-eq-id↓ _ _ _) (snd (h-aux f)))) 
  
                   
                  q : μ↓-alg (g (h f)) (cst (f₀ᶠ x)) == μ↓-alg f (cst (f₀ᶠ x))
                  q = transport (λ y → μ↓-alg (g (h f)) (cst (f₀ᶠ x)) == y)
                          p
                          (snd (g-aux (h f)))

              in fst= $ contr-has-all-paths ⦃ f₀ᶠ-is-cocart x true y tt (μ↓-alg f (cst (f₀ᶠ x))) tt idp ⦄
                                            (g (h f) , q)
                                            (f ,  idp)

            h-g : h ∘ g ∼ idf _
            h-g f = 
              let p : μ↓-alg (g f) (cst (f₀ᶠ x)) == μ↓-alg (g₀ᶠ y) (cst f)
                  p = let (c , v) = pd₂↓ (Pb↓ (Id↓ ⊤) (Ob (fst 𝟚)) (Ob↓ X↓)) (Ob↓ (Hom↓ X↓))
                                         (g f) (cst (f₀ᶠ x))
                      in fst= (contr-has-all-paths ⦃ base-fib↓ fib↓ c v tt ⦄
                                (μ↓-alg (g f) (cst (f₀ᶠ x)) , μ↓-alg-fill (g f) (cst (f₀ᶠ x)))
                                (μ↓-alg (g₀ᶠ y) (cst f) , <– (cell-eq-id↓ _ _ _) (snd (g-aux f))))
  
                   
                  q : μ↓-alg (g₀ᶠ y) (cst (h (g f))) == μ↓-alg (g₀ᶠ y) (cst f)
                  q = transport (λ k → μ↓-alg (g₀ᶠ y) (cst (h (g f))) == k)
                                  p
                                  (snd (h-aux (g f)))

              in fst= $ contr-has-all-paths ⦃ g₀ᶠ-is-cart y false x tt (μ↓-alg (g₀ᶠ y) (cst f)) tt idp ⦄
                                            (h (g f) , q)
                                            (f ,  idp)
