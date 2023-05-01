{-# OPTIONS --without-K --rewriting --allow-unsolved-meta --guardedness #-}

open import HoTT
open import OpetopicType
open import Monad
open import CategoryTheory.InftyCategory

module CategoryTheory.Interval where

  𝟚ₒ : OpetopicType Id
  Ob 𝟚ₒ _ = Bool
  Ob (Hom 𝟚ₒ) ((ttᵢ , true) , ttᵢ , ν) = ⊤
  Ob (Hom 𝟚ₒ) ((ttᵢ , false) , ttᵢ , ν) with ν ttᵢ
  ... | false = ⊤
  ... | true = ⊥
  Hom (Hom 𝟚ₒ) = Terminal _

  
  𝟚ₒ-is-fibrant : is-fibrant (Hom 𝟚ₒ)
  base-fib 𝟚ₒ-is-fibrant {f = ((ttᵢ , true) , ttᵢ , ν)} σ ν' =
    has-level-in ((tt , tt) , λ { (tt , tt) → idp })
  base-fib 𝟚ₒ-is-fibrant {f = ((ttᵢ , false) , ttᵢ , ν)} σ ν' with ν ttᵢ
  ... | false = has-level-in ((tt , tt) , λ { (tt , tt) → idp })
  ... | true = {!!}
  hom-fib 𝟚ₒ-is-fibrant = Terminal-is-fib _

  𝟚 : ∞-category
  𝟚 = 𝟚ₒ , 𝟚ₒ-is-fibrant
