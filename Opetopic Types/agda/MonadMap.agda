{-# OPTIONS --without-K --rewriting --allow-unsolved-meta --guardedness #-}

open import Monad
open import MonadOver
open import OpetopicType
open import HoTT
open import SigmaMonad

module MonadMap where

  postulate
    _⇒_ : (M N : ℳ) → Set

  module _ {M N : ℳ} (f : M ⇒ N) where

    postulate
      -- Data defining a monad morphism
      idx⇒ : Idx M → Idx N
      cns⇒ : {i : Idx M} → Cns M i → Cns N (idx⇒ i)
      pos⇒ : {i : Idx M} (c : Cns M i) → Pos M c → Pos N (cns⇒ c)
      pos⇐ : {i : Idx M} (c : Cns M i) → Pos N (cns⇒ c) → Pos M c

      -- Definitional laws of monad morphisms
      Typ-cns⇒ : {i : Idx M} (c : Cns M i) (p : Pos M c)
        → idx⇒ (Typ M c p) ↦ Typ N (cns⇒ c) (pos⇒ c p)
      {-# REWRITE Typ-cns⇒ #-}

      pos⇒-inv-r : {i : Idx M} (c : Cns M i) (p : Pos M c)
        → pos⇐ _ (pos⇒ _ p) ↦ p
      {-# REWRITE pos⇒-inv-r #-}

      pos⇒-inv-l : {i : Idx M} (c : Cns M i) (p : Pos N (cns⇒ c))
        → pos⇒ c (pos⇐ c p) ↦ p
      {-# REWRITE pos⇒-inv-l #-}

      cns⇒-η : (i : Idx M) → cns⇒ (η M i) ↦ η N (idx⇒ i)
      {-# REWRITE cns⇒-η #-}

      η-pos⇒ : (i : Idx M) → pos⇒ _ (η-pos M i) ↦ η-pos N (idx⇒ i)
      {-# REWRITE η-pos⇒ #-}

      η-pos⇐ : (i : Idx M) → pos⇐ _ (η-pos N (idx⇒ i)) ↦ η-pos M i
      {-# REWRITE η-pos⇐ #-}

      cns⇒-μ : {i : Idx M} (c : Cns M i) (δ : (p : Pos M c) → Cns M (Typ M c p))
        → cns⇒ (μ M c δ) ↦ μ N (cns⇒ c) λ p → cns⇒ (δ (pos⇐ c p))
      {-# REWRITE cns⇒-μ #-}

      μ-pos⇒ : {i : Idx M} (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos M c) (q : Pos M (δ p))
        → pos⇒ _ (μ-pos M c δ p q) ↦ μ-pos N (cns⇒ c) (λ p → cns⇒ (δ (pos⇐ _ p))) (pos⇒ c p) (pos⇒ (δ p) q)
      {-# REWRITE μ-pos⇒ #-}

      μ-pos⇐ : {i : Idx M} (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos N (cns⇒ c)) (q : Pos N (cns⇒ (δ (pos⇐ _ p))))
        → pos⇐ _ (μ-pos N (cns⇒ c) (λ p → cns⇒ (δ (pos⇐ _ p))) p q)
          ↦ μ-pos M c δ (pos⇐ _ p) (pos⇐ _ q)
      {-# REWRITE μ-pos⇐ #-}

      μ-pos-fst⇒ : {i : Idx M} (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos M (μ M c δ))
        → pos⇒ _ (μ-pos-fst M c δ p) ↦ μ-pos-fst N (cns⇒ c) (λ p → cns⇒ (δ (pos⇐ _ p))) (pos⇒ _ p)
      {-# REWRITE μ-pos-fst⇒ #-}

      μ-pos-fst⇐ : {i : Idx M} (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos N (μ N (cns⇒ c) (λ p → cns⇒ (δ (pos⇐ _ p)))))
        → pos⇐ c (μ-pos-fst N (cns⇒ c) (λ p → cns⇒ (δ (pos⇐ c p))) p) ↦ μ-pos-fst M c δ (pos⇐ (μ M c δ) p)
      --{-# REWRITE μ-pos-fst⇐ #-} weird bug

{-
      Doesn't typecheck without μ-pos-fst⇐
      μ-pos-snd⇒ : {i : Idx M} (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos M (μ M c δ))
        → pos⇒ _ (μ-pos-snd M c δ p) ↦ μ-pos-snd N (cns⇒ c) (λ p → cns⇒ (δ (pos⇐ _ p))) (pos⇒ _ p)
      {-# REWRITE μ-pos-snd⇒ #-}

      μ-pos-snd⇐ : {i : Idx M} (c : Cns M i)
        → (δ : (p : Pos M c) → Cns M (Typ M c p))
        → (p : Pos M (μ M c δ))
        → pos⇐ _ (μ-pos-snd N (cns⇒ c) (λ p → cns⇒ (δ (pos⇐ _ p))) (pos⇒ _ p)) ↦ μ-pos-snd M c δ p 
      {-# REWRITE μ-pos-snd⇐ #-}
-}
    
  module _ (M : ℳ) where

    postulate
      Id⇒ : M ⇒ M
      idx-Id⇒ : (i : Idx M) → idx⇒ Id⇒ i ↦ i
      {-# REWRITE idx-Id⇒ #-}
      
      cns-Id⇒ : {i : Idx M} (c : Cns M i) → cns⇒ Id⇒ c ↦ c
      {-# REWRITE cns-Id⇒ #-}

      pos-Id⇒ : {i : Idx M} (c : Cns M i) (p : Pos M c)
        → pos⇒ Id⇒ c p ↦ p
      {-# REWRITE pos-Id⇒ #-}

      pos-Id⇒⁻¹ : {i : Idx M} (c : Cns M i) (p : Pos M c)
        → pos⇐ Id⇒ c p ↦ p
      {-# REWRITE pos-Id⇒⁻¹ #-}

  module _ {M N : ℳ} (f : M ⇒ N) where
  
    postulate
      Slc⇒ : Slc M ⇒ Slc N

      idx-Slc⇒ : ((i , c) : Idx (Slc M)) → idx⇒ Slc⇒ (i , c) ↦ idx⇒ f i , cns⇒ f c
      {-# REWRITE idx-Slc⇒ #-}

    cns-Slc⇒ : {(i , c) : Idx (Slc M)}
      → Cns (Slc M) (i , c) → Cns (Slc N) (idx⇒ f i , cns⇒ f c) 
    cns-Slc⇒ (lf i) = lf (idx⇒ f i)
    cns-Slc⇒ (nd c δ ε) =
      let δ₁ p = cns⇒ f (δ (pos⇐ f c p))
          ε₁ p = cns-Slc⇒ (ε (pos⇐ f c p))
      in nd (cns⇒ f c) δ₁ ε₁

    postulate 
      cns-Slc⇒-rew : {i : Idx (Slc M)} → cns⇒ Slc⇒ {i} ↦ cns-Slc⇒
      {-# REWRITE cns-Slc⇒-rew #-}

      Typ-cns-Slc⇒₁ : (i : Idx (Slc M)) (c : Cns (Slc M) i) (p : Pos (Slc M) c)
        → idx⇒ f (fst (Typ (Slc M) c p))  ↦ fst (Typₛ N (cns⇒ Slc⇒ c) (pos⇒ Slc⇒ c p))
      {-# REWRITE Typ-cns-Slc⇒₁ #-}

      Typ-cns-Slc⇒₂ : (i : Idx (Slc M)) (c : Cns (Slc M) i) (p : Pos (Slc M) c)
        → cns⇒ f (snd (Typ (Slc M) c p))  ↦ snd (Typₛ N (cns⇒ Slc⇒ c) (pos⇒ Slc⇒ c p))
      {-# REWRITE Typ-cns-Slc⇒₂ #-}

    pos-Slc⇒ : {i : Idx (Slc M)} (c : Cns (Slc M) i) (p : Pos (Slc M) c)
      → Pos (Slc N) (cns⇒ Slc⇒ c)
    pos-Slc⇒ (nd c δ ε) (inl tt) = inl tt
    pos-Slc⇒ (nd c δ ε) (inr (p , q)) = inr (pos⇒ f c p , pos-Slc⇒ (ε p) q)

    pos-Slc⇒⁻¹ : {i : Idx (Slc M)} (c : Cns (Slc M) i) (p : Pos (Slc N) (cns-Slc⇒ c))
      → Pos (Slc M) c 
    pos-Slc⇒⁻¹ (nd c δ ε) (inl tt) = inl tt
    pos-Slc⇒⁻¹ (nd c δ ε) (inr (p , q)) = inr (pos⇐ f c p , pos-Slc⇒⁻¹ (ε (pos⇐ f c p)) q)
     
    postulate
      pos-Slc⇒-rew : {i : Idx (Slc M)} (c : Cns (Slc M) i) (p : Pos (Slc M) c)
        → pos⇒ Slc⇒ c p ↦ pos-Slc⇒ c p
      {-# REWRITE pos-Slc⇒-rew #-}

      pos-Slc⇒⁻¹-rew : {i : Idx (Slc M)} (c : Cns (Slc M) i) (p : Pos (Slc N) (cns-Slc⇒ c))
        → pos⇐ Slc⇒ c p ↦ pos-Slc⇒⁻¹ c p
      {-# REWRITE pos-Slc⇒⁻¹-rew #-}

    module _ {A : Idx M → Set} {B : Idx N → Set}
             (g : {i : Idx M} → A i → B (idx⇒ f i)) where 

      postulate
        Pb⇒ : Pb M A ⇒ Pb N B

        idx-Pb⇒ : ((i , x) : Idx (Pb M A)) → idx⇒ Pb⇒ (i , x) ↦ idx⇒ f i , g x
        {-# REWRITE idx-Pb⇒ #-}

        cns-Pb⇒ : {i : Idx (Pb M A)} ((c , x) : Cns (Pb M A) i) → cns⇒ Pb⇒ {i} (c , x) ↦ cns⇒ f c , λ p → g (x (pos⇐ f c p))
        {-# REWRITE cns-Pb⇒ #-}

        pos-Pb⇒-rew : {i : Idx (Pb M A)} ((c , x) : Cns (Pb M A) i) (p : Pos (Pb M A) {i = i} (c , x))
          → pos⇒ Pb⇒ {i = i} (c , x) p ↦ pos⇒ f c p
        {-# REWRITE pos-Pb⇒-rew #-}

        pos-Pb⇒⁻¹-rew : {i : Idx (Pb M A)} ((c , x) : Cns (Pb M A) i) (p : Pos (Pb N B) {i = idx⇒ Pb⇒ i} (cns⇒ Pb⇒ {i = i} (c , x)))
          → pos⇐ Pb⇒ {i = i} (c , x) p ↦ pos⇐ f c p
        {-# REWRITE pos-Pb⇒⁻¹-rew #-}

  module _ {X Y Z : ℳ} (g : Y ⇒ Z) (f : X ⇒ Y) where

    postulate
      ∘⇒ : X ⇒ Z 

      idx-∘⇒ : idx⇒ ∘⇒ ↦ idx⇒ g ∘ idx⇒ f
      {-# REWRITE idx-∘⇒ #-}

      cns-∘⇒ : {i : Idx X} (c : Cns X i) → cns⇒ ∘⇒ c ↦ cns⇒ g (cns⇒ f c)
      {-# REWRITE cns-∘⇒ #-}

      pos-∘⇒ : {i : Idx X} (c : Cns X i) (p : Pos X c)
        → pos⇒ ∘⇒ c p ↦ pos⇒ g _ (pos⇒ f c p)
      {-# REWRITE pos-∘⇒ #-}

      pos-∘⇐ : {i : Idx X} (c : Cns X i) (p : Pos Z _)
        → pos⇐ ∘⇒ c p ↦ pos⇐ f _ (pos⇐ g _ p)
      {-# REWRITE pos-∘⇐ #-}

  postulate
    ∘⇒-Slc : {X Y Z : ℳ} (g : Y ⇒ Z) (f : X ⇒ Y)
      → ∘⇒ (Slc⇒ g) (Slc⇒ f) ↦ Slc⇒ (∘⇒ g f)
    {-# REWRITE ∘⇒-Slc  #-}    

    ∘⇒-Pb : {X₀ Y₀ Z₀ : ℳ}
      → {X₁ : Idx X₀ → Set} {Y₁ : Idx Y₀ → Set} {Z₁ : Idx Z₀ → Set}
      → (g₀ : Y₀ ⇒ Z₀) (f₀ : X₀ ⇒ Y₀)
      → (g₁ : {i : Idx Y₀} → Y₁ i → Z₁ (idx⇒ g₀ i))
      → (f₁ : {i : Idx X₀} → X₁ i → Y₁ (idx⇒ f₀ i))
      → ∘⇒ (Pb⇒ g₀ {Y₁} {Z₁} g₁) (Pb⇒ f₀ f₁)
        ↦ Pb⇒ (∘⇒ g₀ f₀) λ {i} x → g₁ (f₁ {i} x)
    {-# REWRITE ∘⇒-Pb #-}
  
  module _ {M N : ℳ} (f : M ⇒ N)
           {A : Idx M → Set} {B : Idx N → Set}
           (g : {i : Idx M} → A i → B (idx⇒ f i)) where
           
    [_/_]* : (M / A) ⇒ (N / B)
    [_/_]* =  Slc⇒ (Pb⇒ f g)

  -- Sigma map
  module _ (M : ℳ) (M↓ : ℳ↓ M) where

    cns-Slc-ΣM : {((i , i↓) , (c , c↓)) : Idx (Slc (ΣM M M↓))} (d : Cns (Slc (ΣM M M↓)) ((i , i↓) , (c , c↓)))
      → Cns (ΣM (Slc M) (Slc↓ M↓)) ((i , c) , (i↓ , c↓))
    cns-Slc-ΣM (lf (i , i↓)) = lf i , lf↓ i↓
    cns-Slc-ΣM (nd (c , c↓) z t) =
      let hyp p = cns-Slc-ΣM (t p)
      in (nd c _ (fst ∘ hyp) , nd↓ c↓ _ (snd ∘ hyp))

    pos-Slc-ΣM : {i : Idx (Slc (ΣM M M↓))} (c : Cns (Slc (ΣM M M↓)) i) (p : Pos (Slc (ΣM M M↓)) c)
      → Pos (ΣM (Slc M) (Slc↓ M↓)) (cns-Slc-ΣM c)
    pos-Slc-ΣM (nd y z t) (inl tt) = inl tt
    pos-Slc-ΣM (nd y z t) (inr (p , q)) = inr (p , pos-Slc-ΣM (t p) q)

    pos-Slc-ΣM⁻¹ : {i : Idx (Slc (ΣM M M↓))} (c : Cns (Slc (ΣM M M↓)) i) (p : Pos (ΣM (Slc M) (Slc↓ M↓)) (cns-Slc-ΣM c))
      → Pos (Slc (ΣM M M↓)) c
    pos-Slc-ΣM⁻¹ (nd y z t) (inl tt) = inl tt
    pos-Slc-ΣM⁻¹ (nd y z t) (inr (p , q)) = inr (p , pos-Slc-ΣM⁻¹ (t p) q)

    postulate
      ΣM⇒-Slc : Slc (ΣM M M↓) ⇒ ΣM (Slc M) (Slc↓ M↓)

      idx-ΣM⇒-Slc : (((i , i↓) , (c , c↓)) : Idx (Slc (ΣM M M↓)))
        → idx⇒ ΣM⇒-Slc ((i , i↓) , (c , c↓)) ↦ (i , c) , (i↓ , c↓)
      {-# REWRITE idx-ΣM⇒-Slc #-}

      cns-ΣM⇒-Slc : (i : Idx (Slc (ΣM M M↓))) (c : Cns (Slc (ΣM M M↓)) i)
        → cns⇒ ΣM⇒-Slc c ↦ cns-Slc-ΣM c
      {-# REWRITE cns-ΣM⇒-Slc #-}

      pos-ΣM⇒-Slc : (i : Idx (Slc (ΣM M M↓))) (c : Cns (Slc (ΣM M M↓)) i) (p : Pos (Slc (ΣM M M↓)) c)
        → pos⇒ ΣM⇒-Slc c p ↦ pos-Slc-ΣM c p
      {-# REWRITE pos-ΣM⇒-Slc #-}

      pos-ΣM⇐-Slc : (i : Idx (Slc (ΣM M M↓))) (c : Cns (Slc (ΣM M M↓)) i) (p : Pos (ΣM (Slc M) (Slc↓ M↓)) (cns⇒ ΣM⇒-Slc c))
        → pos⇐ ΣM⇒-Slc c p ↦ pos-Slc-ΣM⁻¹ c p
      {-# REWRITE pos-ΣM⇐-Slc #-}

  module _ (M : ℳ) (M↓ : ℳ↓ M) (X : Cell M) (X↓ : Cell↓ {M} M↓ X) where

    postulate
  
      ΣM⇒-Pb : Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓)) ⇒ ΣM (Pb M X) (Pb↓ M↓ X X↓)

      idx-ΣM⇒-Pb : (((i , i↓) , (x , x↓)) : Idx ((Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓)))))
        → idx⇒ ΣM⇒-Pb ((i , i↓) , (x , x↓)) ↦ ((i , x) , (i↓ , x↓))
      {-# REWRITE idx-ΣM⇒-Pb #-}

      cns-ΣM⇒-Pb : {i : Idx ((Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓))))}
        → (((c , c↓) , x) : Cns ((Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓)))) i)
        → cns⇒ ΣM⇒-Pb {i} ((c , c↓) , x) ↦ (c , fst ∘ x) , (c↓ , snd ∘ x)
      {-# REWRITE cns-ΣM⇒-Pb #-}

      pos-ΣM⇒-Pb : {i : Idx ((Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓))))}
        → (c : Cns ((Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓)))) i)
        → (p : Pos (Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓))) {i} c)
        → pos⇒ ΣM⇒-Pb {i} c p ↦ p
      {-# REWRITE pos-ΣM⇒-Pb #-}

      pos-ΣM⇐-Pb : {i : Idx ((Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓))))}
        → (c : Cns ((Pb (ΣM M M↓) (λ (i , i↓) → Σ (X i) (X↓ i↓)))) i)
        → (p : Pos (ΣM (Pb M X) (Pb↓ M↓ X X↓)) {idx⇒ ΣM⇒-Pb i} (cns⇒ ΣM⇒-Pb {i} c))
        → pos⇐ ΣM⇒-Pb {i} c p ↦ p
      {-# REWRITE pos-ΣM⇐-Pb #-}

  reindexₒ : {M N : ℳ}
    → (f : M ⇒ N)
    → OpetopicType N
    → OpetopicType M
  Ob (reindexₒ f X) x = Ob X (idx⇒ f x)
  Hom (reindexₒ {M} {N} f X) = reindexₒ {M / ((Ob X) ∘ (idx⇒ f))} [ f /   idf _ ]* (Hom X)

  reindex-alg : {M N : ℳ}
    → (f : M ⇒ N)
    → (X : OpetopicType N)
    → (X-is-algebraic : is-fibrant X)
    → is-fibrant (reindexₒ f X)
  base-fib (reindex-alg f X X-is-algebraic) _ _ = base-fib X-is-algebraic  _ _
  hom-fib (reindex-alg f X X-is-algebraic) = reindex-alg _ (Hom X) (hom-fib X-is-algebraic)

  record _⇒ₒ_ {M : ℳ} (X Y : OpetopicType M) : Set where
    coinductive
    field
      Ob⇒ : (i : Idx M) → Ob X i → Ob Y i
      Hom⇒ : Hom X ⇒ₒ reindexₒ  [ Id⇒ M / Ob⇒ _ ]* (Hom Y) 

  record _≃ₒ_ {M : ℳ} (X Y : OpetopicType M) : Set where
    coinductive
    field
      Ob≃ : (i : Idx M) → Ob X i ≃ Ob Y i
      Hom≃ : (Hom X) ≃ₒ reindexₒ [ Id⇒ M / –> (Ob≃ _) ]* (Hom Y)
      
  open _≃ₒ_ public
