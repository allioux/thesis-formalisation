{-# OPTIONS --without-K --rewriting --guardedness --allow-unsolved-meta --type-in-type #-}

open import HoTT hiding (Rel)
open import Monad
open import MonadOver
open import OpetopicType
open import Algebras
open import AlgebrasOver
open import SigmaMonad
open import Sigma
open import MonadMap

module _  where

  Rel : {M : ℳ} (M↓ : ℳ↓ M) → Cell M
  Rel M↓ i = Idx↓ M↓ i → Set

  Rel↓ : {M : ℳ} (M↓ : ℳ↓ M) → Cell↓ M↓ (Rel M↓)
  Rel↓ M↓ i↓ R = R i↓

  is-fib-rel : {M : ℳ} (M↓ : ℳ↓ M) (X : Cell M) (X↓ : Cell↓ M↓ X)
    → {i : Idx M} (y : X i)
    → (c : Cns M i) (x : Fam M X c)
    → (R : Rel (M↓ /↓ X↓) ((i , y) , (c , x)))
    → Set
  is-fib-rel {M} M↓ X X↓ {i} y c x R = 
     {i↓ : Idx↓ M↓ i} (c↓ : Cns↓ M↓ i↓ c)
     → (x↓ : Fam↓ M↓ X↓ c↓ x)
     → is-contr (Σ (X↓ i↓ y) λ y↓ → R ((i↓ , y↓) , (c↓ , x↓)))

  𝒰' : (M : ℳ) (M↓ : ℳ↓ M) (X : Cell M) (X↓ : Cell↓ M↓ X)
    → OpetopicType (M / X)                
  𝒰↓' : (M : ℳ) (M↓ : ℳ↓ M) (X : Cell M) (X↓ : Cell↓ M↓ X)
    → OpetopicType↓ (M↓ /↓ X↓) (𝒰' M M↓ X X↓)
  
  Rel' : (M : ℳ) (M↓ : ℳ↓ M) (X : Cell M) (X↓ : Cell↓ M↓ X)
    → Cell (M / X)
  Rel' M M↓ X X↓ ((i , x) , (c , y)) =
    Σ (Rel (M↓ /↓ X↓) ((i , x) , (c , y)))
      (is-fib-rel M↓ X X↓ x c y)
  
  Rel↓' : (M : ℳ) (M↓ : ℳ↓ M) (X : Cell M) (X↓ : Cell↓ M↓ X)
    → Cell↓ (M↓ /↓ X↓) (Rel' M M↓ X X↓)
  Rel↓' M M↓ X X↓ i↓ (R , _) = R i↓

  Ob (𝒰' M M↓ X X↓) = Rel' M M↓ X X↓
  Hom (𝒰' M M↓ X X↓) =
    𝒰' (M / X) (M↓ /↓ X↓) (Rel' M M↓ X X↓) (Rel↓' M M↓ X X↓)

  Ob↓ (𝒰↓' M M↓ X X↓) = Rel↓' M M↓ X X↓
  Hom↓ (𝒰↓' M M↓ X X↓) =
    𝒰↓' (M / X) (M↓ /↓ X↓) (Rel' M M↓ X X↓) (Rel↓' M M↓ X X↓)

  𝒰 : (M : ℳ) (M↓ : ℳ↓ M) → OpetopicType M
  Ob (𝒰 M M↓) = Rel M↓
  Hom (𝒰 M M↓) = 𝒰' M M↓ (Rel M↓) (Rel↓ M↓)

  𝒰↓ : (M : ℳ) (M↓ : ℳ↓ M) → OpetopicType↓ M↓ (𝒰 M M↓)
  Ob↓ (𝒰↓ M M↓) = Rel↓ M↓
  Hom↓ (𝒰↓ M M↓) = 𝒰↓' M M↓ (Rel M↓) (Rel↓ M↓)    
