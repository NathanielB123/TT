{-# OPTIONS --smart-with --prop --rewriting --show-irrelevant #-}

open import Utils.Prop
open import Utils.MacroProp

module Models.GrpdProp.Grpd where 

module Grpd where
  record Sorts : Set₁ where
    eta-equality
    field
      Car : Set
      Rel : Car → Car → Set
  module _ (𝒮 : Sorts) where
    open Sorts 𝒮
    module Vars where variable
      x y z x₁ x₂ x₃ x₄ : Car 
      x₁₂ x₂₃ x₂₄ x₁₃ x₃₄ x₂₁ x₃₂ x₁₂′ : Rel x₁ x₂
    open Vars
    record Data : Set where 
      eta-equality
      field
        id  : (x : Car) → Rel x x
        _⁻¹ : Rel x y → Rel y x
        _∘_ : Rel x y → Rel y z → Rel x z
        
        id∘ : (x₁₂ : Rel x₁ x₂) → id x₁ ∘ x₁₂ ≡ x₁₂
        ∘id : (x₁₂ : Rel x₁ x₂) → x₁₂ ∘ id x₂ ≡ x₁₂
        ∘∘  : (x₁₂ : Rel x₁ x₂) (x₂₃ : Rel x₂ x₃) (x₃₄ : Rel x₃ x₄)
            → (x₁₂ ∘ x₂₃) ∘ x₃₄ ≡ x₁₂ ∘ (x₂₃ ∘ x₃₄)
        ∘⁻¹ : (x₁₂ : Rel x₁ x₂) → x₁₂ ∘ (x₁₂ ⁻¹) ≡ id x₁
        ⁻¹∘ : (x₁₂ : Rel x₁ x₂) → (x₁₂ ⁻¹) ∘ x₁₂ ≡ id x₂

      -- TODO: Can we get rid of the opaques in the prop version?
      opaque
        id⁻¹ : (x : Car) → id x ⁻¹ ≡ id x
        id⁻¹ x =
          id x ⁻¹
          ≡⟨ sym (id∘ _) ⟩
          id x ∘ (id x ⁻¹)
          ≡⟨ ∘⁻¹ _ ⟩
          id x ∎
      
      id∘id : (x₁₂ : Rel x₁ x₂) → id x₁ ∘ x₁₂ ≡ x₁₂ ∘ id x₂
      id∘id {x₁ = x₁} {x₂ = x₂} x₁₂ =
        id x₁ ∘ x₁₂
        ≡⟨ id∘ x₁₂ ⟩
        x₁₂
        ≡⟨ sym (∘id x₁₂) ⟩
        x₁₂ ∘ id x₂ ∎

      ⁻¹∘id∘ : (x₁₂ : Rel x₁ x₂) → (x₁₂ ⁻¹) ∘ (id x₁ ∘ x₁₂) ≡ id x₂
      ⁻¹∘id∘ {x₁ = x₁} {x₂ = x₂} x₁₂ = 
        (x₁₂ ⁻¹) ∘ ⌜ id x₁ ∘ x₁₂ ⌝
        ≡⟨ ap! (id∘ x₁₂) ⟩
        (x₁₂ ⁻¹) ∘ x₁₂
        ≡⟨ ⁻¹∘ x₁₂ ⟩ 
        id x₂ ∎

      id⁻¹∘∘id : (x₁₂ : Rel x₁ x₂) → (id x₁ ⁻¹) ∘ (x₁₂ ∘ id x₂) ≡ x₁₂
      id⁻¹∘∘id {x₁ = x₁} {x₂ = x₂} x₁₂ = 
        (id x₁ ⁻¹) ∘ ⌜ x₁₂ ∘ id x₂ ⌝
        ≡⟨ ap! (∘id x₁₂) ⟩
        ⌜ id x₁ ⁻¹ ⌝ ∘ x₁₂
        ≡⟨ ap! (id⁻¹ x₁) ⟩
        id x₁ ∘ x₁₂
        ≡⟨ id∘ x₁₂ ⟩
        x₁₂ ∎

      ⁻¹∘∘ : (x₁₂ : Rel x₁ x₂) (x₂₃ : Rel x₂ x₃) 
           → ((x₁₂ ⁻¹) ∘ x₁₂) ∘ x₂₃ ≡ x₂₃ 
      ⁻¹∘∘ x₁₂ x₂₃ =
        ⌜ (x₁₂ ⁻¹) ∘ x₁₂ ⌝ ∘ x₂₃
        ≡⟨ ap! (⁻¹∘ _) ⟩
        id _ ∘ x₂₃
        ≡⟨ id∘ _ ⟩
        x₂₃ ∎

      ∘⟨⁻¹∘⟩ : (x₁₂ : Rel x₁ x₂) (x₃₂ : Rel x₃ x₂) 
             → x₁₂ ∘ ((x₃₂ ⁻¹) ∘ x₃₂) ≡ x₁₂
      ∘⟨⁻¹∘⟩ x₁₂ x₃₂ =
        x₁₂ ∘ ⌜ (x₃₂ ⁻¹) ∘ x₃₂ ⌝ 
        ≡⟨ ap! (⁻¹∘ _) ⟩
        x₁₂ ∘ id _
        ≡⟨ ∘id _ ⟩
        x₁₂ ∎

      ⟨∘⁻¹⟩∘ : (x₂₁ : Rel x₂ x₁) (x₂₃ : Rel x₂ x₃) 
             → (x₂₁ ∘ (x₂₁ ⁻¹)) ∘ x₂₃ ≡ x₂₃
      ⟨∘⁻¹⟩∘ x₂₁ x₂₃ =
        ⌜ x₂₁ ∘ (x₂₁ ⁻¹) ⌝ ∘ x₂₃ 
        ≡⟨ ap! (∘⁻¹ _) ⟩
        id _ ∘ x₂₃
        ≡⟨ id∘ _ ⟩
        x₂₃ ∎

      opaque
        ⁻¹⁻¹  : (x₁₂ : Rel x₁ x₂) → x₁₂ ⁻¹ ⁻¹ ≡ x₁₂
        ⁻¹⁻¹ x₁₂ = 
          x₁₂ ⁻¹ ⁻¹
          ≡⟨ sym (∘⟨⁻¹∘⟩ _ _) ⟩
          (x₁₂ ⁻¹ ⁻¹) ∘ ((x₁₂ ⁻¹) ∘ x₁₂)
          ≡⟨ sym (∘∘ _ _ _) ⟩
          ((x₁₂ ⁻¹ ⁻¹) ∘ (x₁₂ ⁻¹)) ∘ x₁₂
          ≡⟨ ⁻¹∘∘ _ _ ⟩
          x₁₂ ∎

      id⁻¹∘ : (id _ ⁻¹) ∘ x₁₂ ≡ x₁₂
      id⁻¹∘ {x₁₂ = x₁₂} =
        ⌜ id _ ⁻¹ ⌝ ∘ x₁₂
        ≡⟨ ap! (id⁻¹ _) ⟩
        id _ ∘ x₁₂
        ≡⟨ id∘ _ ⟩
        x₁₂ ∎

      ∘∘⁻¹ : (x₁₂ : Rel x₁ x₂) (x₂₃ : Rel x₂ x₃) 
           → x₁₂ ∘ (x₂₃ ∘ (x₂₃ ⁻¹)) ≡ x₁₂
      ∘∘⁻¹ x₁₂ x₂₃ =
        x₁₂ ∘ ⌜ x₂₃ ∘ (x₂₃ ⁻¹) ⌝ 
        ≡⟨ ap! (∘⁻¹ _) ⟩
        x₁₂ ∘ id _
        ≡⟨ ∘id _ ⟩
        x₁₂ ∎

      opaque
        ⟨∘⟩⁻¹ : (x₁₂ : Rel x₁ x₂) (x₂₃ : Rel x₂ x₃)
              → (x₁₂ ∘ x₂₃) ⁻¹ ≡ (x₂₃ ⁻¹) ∘ (x₁₂ ⁻¹)
        ⟨∘⟩⁻¹ x₁₂ x₂₃ = 
          (x₁₂ ∘ x₂₃) ⁻¹
          ≡⟨ sym (∘∘⁻¹ _ _) ⟩
          ((x₁₂ ∘ x₂₃) ⁻¹) ∘ (⌜ x₁₂ ⌝ ∘ (x₁₂ ⁻¹))
          ≡⟨ ap! (sym (∘∘⁻¹ _ _)) ⟩
          ((x₁₂ ∘ x₂₃) ⁻¹) ∘ (⌜ x₁₂ ∘ (x₂₃ ∘ (x₂₃ ⁻¹)) ⌝ ∘ (x₁₂ ⁻¹))
          ≡⟨ ap! (sym (∘∘ _ _ _)) ⟩
          ((x₁₂ ∘ x₂₃) ⁻¹) ∘ ⌜ ((x₁₂ ∘ x₂₃) ∘ (x₂₃ ⁻¹)) ∘ (x₁₂ ⁻¹) ⌝
          ≡⟨ ap! (∘∘ _ _ _) ⟩
          ((x₁₂ ∘ x₂₃) ⁻¹) ∘ ((x₁₂ ∘ x₂₃) ∘ ((x₂₃ ⁻¹) ∘ (x₁₂ ⁻¹)))
          ≡⟨ sym (∘∘ _ _ _) ⟩
          (((x₁₂ ∘ x₂₃) ⁻¹) ∘ (x₁₂ ∘ x₂₃)) ∘ ((x₂₃ ⁻¹) ∘ (x₁₂ ⁻¹))
          ≡⟨ ⁻¹∘∘ _ _ ⟩
          (x₂₃ ⁻¹) ∘ (x₁₂ ⁻¹) ∎

      ∘-inj₁ : {x₁₂ x₁₂' : Rel x₁ x₂} (x₂₃ : Rel x₂ x₃) 
             → x₁₂ ∘ x₂₃ ≡ x₁₂' ∘ x₂₃ → x₁₂ ≡ x₁₂'
      ∘-inj₁ {x₁₂ = x₁₂} {x₁₂' = x₁₂'} x₂₃ p =
        x₁₂
        ≡⟨ sym (∘∘⁻¹ x₁₂ x₂₃) ⟩
        x₁₂ ∘ (x₂₃ ∘ (x₂₃ ⁻¹))
        ≡⟨ sym (∘∘ x₁₂ x₂₃ (x₂₃ ⁻¹)) ⟩
        ⌜ x₁₂ ∘ x₂₃ ⌝ ∘ (x₂₃ ⁻¹)
        ≡⟨ ap! p ⟩
        (x₁₂' ∘ x₂₃) ∘ (x₂₃ ⁻¹)
        ≡⟨ ∘∘ x₁₂' x₂₃ (x₂₃ ⁻¹) ⟩
        x₁₂' ∘ (x₂₃ ∘ (x₂₃ ⁻¹))
        ≡⟨ ∘∘⁻¹ x₁₂' x₂₃ ⟩
        x₁₂' ∎

  open Sorts public
  open Data  public
 
Grpd : Set₁
Grpd = Σ Grpd.Sorts Grpd.Data

-- Fibrant displayed groupoids
-- Equivalent to functors from |G| to |Grpd|
module Grpdᴰ (G : Grpd) where
  open Grpd.Sorts (G .fst)
  open Grpd.Vars  (G .fst) 
  open Grpd.Data  (G .snd)
  record Sorts : Set₁ where 
    eta-equality
    field
      Carᴰ : Car → Set
      Relᴰ : Carᴰ x₁ → Carᴰ x₂ → Rel x₁ x₂ → Set
  module _ (𝒮 : Sorts) where
    open Sorts 𝒮
    module Vars where variable
      xᴰ yᴰ zᴰ x₁ᴰ x₂ᴰ x₃ᴰ xᴰ′ : Carᴰ x
      x₁₂ᴰ x₂₃ᴰ x₃₄ᴰ xᴰ~ : Relᴰ x₁ᴰ x₂ᴰ x₁₂
    open Vars
    record Data : Set where 
      eta-equality
      field
        idᴰ  : (xᴰ : Carᴰ x) → Relᴰ xᴰ xᴰ (id x)
        _⁻¹ᴰ : {x₁ᴰ : Carᴰ x₁} {x₂ᴰ : Carᴰ x₂}
             → Relᴰ x₁ᴰ x₂ᴰ x₁₂ → Relᴰ x₂ᴰ x₁ᴰ (x₁₂ ⁻¹)
        _∘ᴰ_ : {x₁ᴰ : Carᴰ x₁} {x₂ᴰ : Carᴰ x₂} {x₃ᴰ : Carᴰ x₃}
             → Relᴰ x₁ᴰ x₂ᴰ x₁₂ → Relᴰ x₂ᴰ x₃ᴰ x₂₃ → Relᴰ x₁ᴰ x₃ᴰ (x₁₂ ∘ x₂₃)
        
        -- Equations
        id∘ᴰ : {x₁ᴰ : Carᴰ x₁} {x₂ᴰ : Carᴰ x₂} (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) 
             → idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ ≡[ ap (Relᴰ x₁ᴰ x₂ᴰ) (id∘ x₁₂) ]≡ x₁₂ᴰ
        ∘idᴰ : {x₁ᴰ : Carᴰ x₁} {x₂ᴰ : Carᴰ x₂} (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂)
             → x₁₂ᴰ ∘ᴰ idᴰ x₂ᴰ ≡[ ap (Relᴰ x₁ᴰ x₂ᴰ) (∘id x₁₂) ]≡ x₁₂ᴰ
        ∘∘ᴰ  : {x₁ᴰ : Carᴰ x₁} {x₂ᴰ : Carᴰ x₂} {x₃ᴰ : Carᴰ x₃} {x₄ᴰ : Carᴰ x₄}
               (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃)
               (x₃₄ᴰ : Relᴰ x₃ᴰ x₄ᴰ x₃₄)
             → (x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ∘ᴰ x₃₄ᴰ 
             ≡[ ap (Relᴰ x₁ᴰ x₄ᴰ) (∘∘ x₁₂ x₂₃ x₃₄) ]≡ x₁₂ᴰ ∘ᴰ (x₂₃ᴰ ∘ᴰ x₃₄ᴰ)
        ∘⁻¹ᴰ : {x₁ᴰ : Carᴰ x₁} {x₂ᴰ : Carᴰ x₂} (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) 
             → x₁₂ᴰ ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ) ≡[ ap (Relᴰ x₁ᴰ x₁ᴰ) (∘⁻¹ x₁₂) ]≡ idᴰ x₁ᴰ
        ⁻¹∘ᴰ : {x₁ᴰ : Carᴰ x₁} {x₂ᴰ : Carᴰ x₂} (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂)
             → (x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ ≡[ ap (Relᴰ x₂ᴰ x₂ᴰ) (⁻¹∘ x₁₂) ]≡ idᴰ x₂ᴰ

        -- Fibrancy
        coeG   : Rel x₁ x₂ → Carᴰ x₁ → Carᴰ x₂
        cohG   : (x₁₂ : Rel x₁ x₂) (xᴰ : Carᴰ x₁) → Relᴰ xᴰ (coeG x₁₂ xᴰ) x₁₂
        coe-id : (xᴰ : Carᴰ x) → coeG (id x) xᴰ ≡ xᴰ
        coe-∘  : (x₁₂ : Rel x₁ x₂) (x₂₃ : Rel x₂ x₃) (xᴰ : Carᴰ x₁)
               → coeG (x₁₂ ∘ x₂₃) xᴰ ≡ coeG x₂₃ (coeG x₁₂ xᴰ)
        coh-id : (xᴰ : Carᴰ x)
               →  cohG (id x) xᴰ ≡[ ap (λ □ → Relᴰ xᴰ □ (id x)) (coe-id xᴰ) 
               ]≡ idᴰ xᴰ
        coh-∘  : (x₁₂ : Rel x₁ x₂) (x₂₃ : Rel x₂ x₃) (xᴰ : Carᴰ x₁)
               → cohG (x₁₂ ∘ x₂₃) xᴰ
               ≡[ ap (λ □ → Relᴰ xᴰ □ (x₁₂ ∘ x₂₃)) (coe-∘ x₁₂ x₂₃ xᴰ)
               ]≡ cohG x₁₂ xᴰ ∘ᴰ cohG x₂₃ (coeG x₁₂ xᴰ)

      ∘⟨⁻¹∘⟩ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) (x₃₂ᴰ : Relᴰ x₃ᴰ x₂ᴰ x₃₂) 
              →  x₁₂ᴰ ∘ᴰ ((x₃₂ᴰ ⁻¹ᴰ) ∘ᴰ x₃₂ᴰ) 
              ≡[ ap (Relᴰ x₁ᴰ x₂ᴰ) (∘⟨⁻¹∘⟩ x₁₂ x₃₂) 
              ]≡ x₁₂ᴰ
      ∘⟨⁻¹∘⟩ᴰ {x₁₂ = x₁₂} {x₃₂ = x₃₂} x₁₂ᴰ x₃₂ᴰ 
        rewrite ↑≡ ∘id x₁₂
        rewrite ↑≡ ⁻¹∘ x₃₂
        = coe[]
        (x₁₂ᴰ ∘ᴰ ⌜ (x₃₂ᴰ ⁻¹ᴰ) ∘ᴰ x₃₂ᴰ ⌝ 
        ≡⟨ ap! (⁻¹∘ᴰ x₃₂ᴰ .[]coe) ⟩
        x₁₂ᴰ ∘ᴰ idᴰ _
        ≡⟨ ∘idᴰ _ .[]coe ⟩
        x₁₂ᴰ ∎)

      ⁻¹∘∘ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃) 
            → ((x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ) ∘ᴰ x₂₃ᴰ ≡[ ap (Relᴰ _ _) (⁻¹∘∘ _ _) ]≡ x₂₃ᴰ 
      ⁻¹∘∘ᴰ {x₁₂ = x₁₂} {x₂₃ = x₂₃} x₁₂ᴰ x₂₃ᴰ
        rewrite ↑≡ ⁻¹∘ x₁₂
        rewrite ↑≡ id∘ x₂₃
        = coe[]
        (⌜ (x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ ⌝ ∘ᴰ x₂₃ᴰ
        ≡⟨ ap! (⁻¹∘ᴰ x₁₂ᴰ .[]coe) ⟩
        idᴰ _ ∘ᴰ x₂₃ᴰ
        ≡⟨ id∘ᴰ x₂₃ᴰ .[]coe ⟩
        x₂₃ᴰ ∎)

      opaque
        ⁻¹⁻¹ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) 
              → x₁₂ᴰ ⁻¹ᴰ ⁻¹ᴰ ≡[ ap (Relᴰ _ _) (⁻¹⁻¹ x₁₂) ]≡ x₁₂ᴰ
        ⁻¹⁻¹ᴰ {x₁₂ = x₁₂} x₁₂ᴰ 
          rewrite ↑≡ ⁻¹⁻¹ x₁₂
          rewrite ↑≡ id∘ x₁₂
          rewrite ↑≡ ∘id x₁₂
          rewrite ↑≡ ∘⁻¹ x₁₂
          rewrite ↑≡ ⁻¹∘ x₁₂
          = coe[] 
          (x₁₂ᴰ ⁻¹ᴰ ⁻¹ᴰ
          ≡⟨ sym (∘⟨⁻¹∘⟩ᴰ ((x₁₂ᴰ ⁻¹ᴰ) ⁻¹ᴰ) x₁₂ᴰ .[]coe) ⟩
          (x₁₂ᴰ ⁻¹ᴰ ⁻¹ᴰ) ∘ᴰ ((x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ)
          ≡⟨ sym (∘∘ᴰ (x₁₂ᴰ ⁻¹ᴰ ⁻¹ᴰ) (x₁₂ᴰ ⁻¹ᴰ) x₁₂ᴰ .[]coe) ⟩
          ((x₁₂ᴰ ⁻¹ᴰ ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ)) ∘ᴰ x₁₂ᴰ
          ≡⟨ ⁻¹∘∘ᴰ (x₁₂ᴰ ⁻¹ᴰ) x₁₂ᴰ .[]coe ⟩
          x₁₂ᴰ ∎)

      opaque
        id⁻¹ᴰ : (xᴰ : Carᴰ x) → idᴰ xᴰ ⁻¹ᴰ ≡[ ap (Relᴰ _ _) (id⁻¹ x) ]≡ idᴰ xᴰ
        id⁻¹ᴰ {x = x} xᴰ 
          rewrite ↑≡ id⁻¹ x
          rewrite ↑≡ id∘ (id x)
          = coe[]
          (idᴰ xᴰ ⁻¹ᴰ
          ≡⟨ sym (id∘ᴰ (idᴰ xᴰ ⁻¹ᴰ) .[]coe) ⟩
          idᴰ xᴰ ∘ᴰ (idᴰ xᴰ ⁻¹ᴰ)
          ≡⟨ ∘⁻¹ᴰ (idᴰ xᴰ) .[]coe ⟩
          idᴰ xᴰ ∎)

      ∘∘⁻¹ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃) 
           → x₁₂ᴰ ∘ᴰ (x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ)) ≡[ ap (Relᴰ _ _) (∘∘⁻¹ _ _) ]≡ x₁₂ᴰ
      ∘∘⁻¹ᴰ {x₁₂ = x₁₂} {x₂₃ = x₂₃} x₁₂ᴰ x₂₃ᴰ 
        rewrite ↑≡ ∘⁻¹ x₂₃
        rewrite ↑≡ ∘id x₁₂
        = coe[] 
        (x₁₂ᴰ ∘ᴰ ⌜ x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ) ⌝
        ≡⟨ ap! (∘⁻¹ᴰ x₂₃ᴰ .[]coe) ⟩
        x₁₂ᴰ ∘ᴰ idᴰ _
        ≡⟨ ∘idᴰ x₁₂ᴰ .[]coe ⟩
        x₁₂ᴰ ∎)

      ⟨∘⁻¹⟩∘ᴰ : (x₂₁ᴰ : Relᴰ x₂ᴰ x₁ᴰ x₂₁) (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃) 
              →  (x₂₁ᴰ ∘ᴰ (x₂₁ᴰ ⁻¹ᴰ)) ∘ᴰ x₂₃ᴰ 
              ≡[ ap (Relᴰ _ _) (⟨∘⁻¹⟩∘ _ _) 
              ]≡ x₂₃ᴰ
      ⟨∘⁻¹⟩∘ᴰ {x₂₁ = x₂₁} {x₂₃ = x₂₃} x₂₁ᴰ x₂₃ᴰ 
        rewrite ↑≡ ∘⁻¹ x₂₁
        rewrite ↑≡ id∘ x₂₃ 
        = coe[] 
        (⌜ x₂₁ᴰ ∘ᴰ (x₂₁ᴰ ⁻¹ᴰ) ⌝ ∘ᴰ x₂₃ᴰ
        ≡⟨ ap! (∘⁻¹ᴰ x₂₁ᴰ .[]coe) ⟩
        idᴰ _ ∘ᴰ x₂₃ᴰ
        ≡⟨ id∘ᴰ x₂₃ᴰ .[]coe ⟩
        x₂₃ᴰ ∎)

      id∘idᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂)
             → idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ ≡[ ap (Relᴰ _ _) (id∘id _) ]≡ x₁₂ᴰ ∘ᴰ idᴰ x₂ᴰ
      id∘idᴰ {x₁ᴰ = x₁ᴰ} {x₂ᴰ = x₂ᴰ} {x₁₂ = x₁₂} x₁₂ᴰ 
        rewrite ↑≡ id∘ x₁₂
        rewrite ↑≡ ∘id x₁₂
        = coe[]
        (idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ
        ≡⟨ id∘ᴰ x₁₂ᴰ .[]coe ⟩
        x₁₂ᴰ
        ≡⟨ sym (∘idᴰ x₁₂ᴰ .[]coe) ⟩
        x₁₂ᴰ ∘ᴰ idᴰ x₂ᴰ ∎)

      id⁻¹∘ᴰ : (x₁₂ᴰ : Relᴰ {x₁ = x₁} x₁ᴰ x₂ᴰ x₁₂) 
             → (idᴰ _ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ ≡[ ap (Relᴰ _ _) id⁻¹∘ ]≡ x₁₂ᴰ
      id⁻¹∘ᴰ {x₁ = x₁} {x₁₂ = x₁₂} x₁₂ᴰ 
        rewrite ↑≡ id⁻¹ x₁ 
        rewrite ↑≡ id∘ x₁₂ 
        = coe[]
        (⌜ idᴰ _ ⁻¹ᴰ ⌝ ∘ᴰ x₁₂ᴰ
        ≡⟨ ap! (id⁻¹ᴰ _ .[]coe) ⟩
        idᴰ _ ∘ᴰ x₁₂ᴰ
        ≡⟨ id∘ᴰ _ .[]coe ⟩
        x₁₂ᴰ ∎)

      ⁻¹∘id∘ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂)
              → (x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ (idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ)
              ≡[ ap (Relᴰ _ _) (⁻¹∘id∘ x₁₂) 
              ]≡ idᴰ x₂ᴰ
      ⁻¹∘id∘ᴰ {x₁ᴰ = x₁ᴰ} {x₂ᴰ = x₂ᴰ} {x₁₂ = x₁₂} x₁₂ᴰ 
        rewrite ↑≡ id∘ x₁₂
        rewrite ↑≡ ⁻¹∘ x₁₂ 
        = coe[] 
        ((x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ ⌜ idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ ⌝
        ≡⟨ ap! (id∘ᴰ x₁₂ᴰ .[]coe) ⟩
        (x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ
        ≡⟨ ⁻¹∘ᴰ x₁₂ᴰ .[]coe ⟩ 
        idᴰ x₂ᴰ ∎)

      opaque
        ⟨∘⟩⁻¹ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃)
               → (x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ ≡[ ap (Relᴰ _ _) (⟨∘⟩⁻¹ _ _) ]≡ (x₂₃ᴰ ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ)
        ⟨∘⟩⁻¹ᴰ {x₁₂ = x₁₂} {x₂₃ = x₂₃} x₁₂ᴰ x₂₃ᴰ 
          rewrite ↑≡ ⟨∘⟩⁻¹ x₁₂ x₂₃
          rewrite ↑≡ ∘id ((x₁₂ ∘ x₂₃) ⁻¹)
          rewrite ↑≡ ∘⁻¹ x₁₂
          rewrite ↑≡ ∘id x₁₂
          rewrite ↑≡ ∘⁻¹ x₂₃
          rewrite ↑≡ ∘⁻¹ (x₁₂ ∘ x₂₃)
          rewrite ↑≡ id∘ ((x₁₂ ∘ x₂₃) ⁻¹)
          rewrite ↑≡ ⁻¹∘ (x₁₂ ∘ x₂₃)
          rewrite ↑≡ ∘∘ x₁₂ x₂₃ (x₂₃ ⁻¹)
          = coe[] 
          ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ
          ≡⟨ sym (∘∘⁻¹ᴰ ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ) x₁₂ᴰ .[]coe) ⟩
          ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ) ∘ᴰ (⌜ x₁₂ᴰ ⌝ ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ))
          ≡⟨ ap! (sym (∘∘⁻¹ᴰ x₁₂ᴰ x₂₃ᴰ .[]coe)) ⟩
          ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ) ∘ᴰ 
          (⌜ x₁₂ᴰ ∘ᴰ (x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ)) ⌝ ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ))
          ≡⟨ ap! (sym (∘∘ᴰ _ _ _ .[]coe))  ⟩
          ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ) ∘ᴰ 
          ⌜ ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ)) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ) ⌝
          ≡⟨ ap! (∘∘ᴰ (x₁₂ᴰ ∘ᴰ x₂₃ᴰ) (x₂₃ᴰ ⁻¹ᴰ) (x₁₂ᴰ ⁻¹ᴰ) .[]coe) ⟩
          ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ) ∘ᴰ ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ∘ᴰ ((x₂₃ᴰ ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ)))
          ≡⟨ sym (∘∘ᴰ ((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ) (x₁₂ᴰ ∘ᴰ x₂₃ᴰ) 
                      ((x₂₃ᴰ ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ)) .[]coe) ⟩
          (((x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ∘ᴰ x₂₃ᴰ)) ∘ᴰ ((x₂₃ᴰ ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ))
          ≡⟨ ⁻¹∘∘ᴰ (x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ((x₂₃ᴰ ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ)) .[]coe ⟩
          (x₂₃ᴰ ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ) ∎)

      coeG⁻¹  : Rel x₁ x₂ → Carᴰ x₂ → Carᴰ x₁
      coeG⁻¹ x₁₂ = coeG (x₁₂ ⁻¹)
      cohG⁻¹ : (x₂₁ : Rel x₂ x₁) (xᴰ : Carᴰ x₁) → Relᴰ (coeG⁻¹ x₂₁ xᴰ) xᴰ x₂₁
      cohG⁻¹ x₂₁ xᴰ = tr (Relᴰ _ _) (⁻¹⁻¹ _) (cohG (x₂₁ ⁻¹) _ ⁻¹ᴰ)

      coe-coe⁻¹ : (x₂₁ : Rel x₂ x₁) (x₁ᴰ : Carᴰ x₁)
                → coeG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ) ≡ x₁ᴰ
      coe-coe⁻¹ x₂₁ x₁ᴰ =
        coeG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ)
        ≡⟨ sym (coe-∘ _ _ _) ⟩
        coeG ⌜ (x₂₁ ⁻¹) ∘ x₂₁ ⌝ x₁ᴰ
        ≡⟨ ap! (⁻¹∘ x₂₁) ⟩
        coeG (id _) x₁ᴰ
        ≡⟨ coe-id x₁ᴰ ⟩
        x₁ᴰ ∎

      coh-coe⁻¹ : (x₂₁ : Rel x₂ x₁) (x₁ᴰ : Carᴰ x₁) 
                →  cohG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ) 
                ≡[ ap₂ (Relᴰ _) (coe-coe⁻¹ x₂₁ x₁ᴰ) (sym (⁻¹⁻¹ x₂₁)) 
                ]≡ cohG (x₂₁ ⁻¹) x₁ᴰ ⁻¹ᴰ
      coh-coe⁻¹ x₂₁ x₁ᴰ 
        rewrite ↑≡ ⁻¹∘ x₂₁
        rewrite ↑≡ ∘⁻¹ x₂₁
        rewrite ↑≡ ∘id x₂₁
        rewrite ↑≡ id∘ x₂₁
        rewrite ↑≡ coe-id x₁ᴰ
        rewrite ↑≡ coe-id (coeG (x₂₁ ⁻¹) x₁ᴰ)
        rewrite ↑≡ ⁻¹⁻¹ x₂₁
        rewrite ↑≡ sym (coe-∘ (x₂₁ ⁻¹) x₂₁ x₁ᴰ)
        = coe[] 
        (cohG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ)
        ≡⟨ sym (∘∘⁻¹ᴰ (cohG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ)) 
                      (cohG (x₂₁ ⁻¹) x₁ᴰ) .[]coe) ⟩
        cohG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ) ∘ᴰ
        (cohG (x₂₁ ⁻¹) x₁ᴰ ∘ᴰ (cohG (x₂₁ ⁻¹) x₁ᴰ ⁻¹ᴰ))
        ≡⟨ sym (∘∘ᴰ (cohG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ)) (cohG (x₂₁ ⁻¹) x₁ᴰ) 
                    (cohG (x₂₁ ⁻¹) x₁ᴰ ⁻¹ᴰ) .[]coe) ⟩
        ⌜ cohG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ) ∘ᴰ cohG (x₂₁ ⁻¹) x₁ᴰ ⌝ ∘ᴰ 
        (cohG (x₂₁ ⁻¹) x₁ᴰ ⁻¹ᴰ)
        ≡⟨ ap! (sym (coh-∘ x₂₁ (x₂₁ ⁻¹) (coeG (x₂₁ ⁻¹) x₁ᴰ) .[]coe)) ⟩
        ⌜ cohG (id _) (coeG (x₂₁ ⁻¹) x₁ᴰ) ⌝ ∘ᴰ (cohG (x₂₁ ⁻¹) x₁ᴰ ⁻¹ᴰ)
        ≡⟨ ap! (coh-id (coeG (x₂₁ ⁻¹) x₁ᴰ) .[]coe) ⟩
        idᴰ (coeG (x₂₁ ⁻¹) x₁ᴰ) ∘ᴰ (cohG (x₂₁ ⁻¹) x₁ᴰ ⁻¹ᴰ)
        ≡⟨ id∘ᴰ (cohG (x₂₁ ⁻¹) x₁ᴰ ⁻¹ᴰ) .[]coe ⟩
        cohG (x₂₁ ⁻¹) x₁ᴰ ⁻¹ᴰ ∎)

      ∘-inj₁ᴰ : {x₁₂ᴰ x₁₂'ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂} (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃) 
             → x₁₂ᴰ ∘ᴰ x₂₃ᴰ ≡ x₁₂'ᴰ ∘ᴰ x₂₃ᴰ → x₁₂ᴰ ≡ x₁₂'ᴰ
      ∘-inj₁ᴰ {x₁₂ = x₁₂} {x₂₃ = x₂₃} {x₁₂ᴰ = x₁₂ᴰ} {x₁₂'ᴰ = x₁₂'ᴰ} x₂₃ᴰ p 
        rewrite ↑≡ ∘⁻¹ x₂₃
        rewrite ↑≡ ∘id x₁₂
        rewrite ↑≡ ∘∘ x₁₂ x₂₃ (x₂₃ ⁻¹) =
        x₁₂ᴰ
        ≡⟨ sym (∘∘⁻¹ᴰ x₁₂ᴰ x₂₃ᴰ .[]coe) ⟩
        x₁₂ᴰ ∘ᴰ (x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ))
        ≡⟨ sym (∘∘ᴰ x₁₂ᴰ x₂₃ᴰ (x₂₃ᴰ ⁻¹ᴰ) .[]coe) ⟩
        ⌜ x₁₂ᴰ ∘ᴰ x₂₃ᴰ ⌝ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ)
        ≡⟨ ap! p ⟩
        ((x₁₂'ᴰ ∘ᴰ x₂₃ᴰ) ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ))
        ≡⟨ ∘∘ᴰ x₁₂'ᴰ x₂₃ᴰ (x₂₃ᴰ ⁻¹ᴰ) .[]coe ⟩
        x₁₂'ᴰ ∘ᴰ (x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ))
        ≡⟨ ∘∘⁻¹ᴰ x₁₂'ᴰ x₂₃ᴰ .[]coe ⟩
        x₁₂'ᴰ ∎

  -- Congruence
  module _ (𝒮₁ 𝒮₂ : Sorts) where
    private
      module 𝒮₁ = Sorts 𝒮₁
      module 𝒮₂ = Sorts 𝒮₂

    GrpdSorts≡ : (Carᴰ≡ : ∀ x → 𝒮₁.Carᴰ x ≡ 𝒮₂.Carᴰ x)
               → (∀ {x y} x₁ᴰ y₁ᴰ x₂ᴰ y₂ᴰ (xy : Rel x y)
                    (x₁₂ᴰ : x₁ᴰ ≡[ Carᴰ≡ x ]≡ x₂ᴰ)
                    (y₁₂ᴰ : y₁ᴰ ≡[ Carᴰ≡ y ]≡ y₂ᴰ)
               → 𝒮₁.Relᴰ x₁ᴰ y₁ᴰ xy ≡ 𝒮₂.Relᴰ x₂ᴰ y₂ᴰ xy)
    GrpdSorts≡ = {!!}

  module _ {𝒮} (𝒟₁ 𝒟₂ : Data 𝒮) where
    open Sorts 𝒮
    private
      module 𝒟₁ = Data 𝒟₁
      module 𝒟₂ = Data 𝒟₂

    GrpdData≡ : (idᴰ≡ : ∀ {x} (xᴰ : Carᴰ x) → 𝒟₁.idᴰ xᴰ ≡ 𝒟₂.idᴰ xᴰ)
              → {!!} -- ...
              → 𝒟₁ ≡ 𝒟₂
    GrpdData≡ = {!!}

  Grpdᴰ : Set₁
  Grpdᴰ = Σ Sorts Data

  module _ (𝒢₁ 𝒢₂ : Grpdᴰ) where
    private
      module 𝒮₁ = Sorts (𝒢₁ .fst)
      module 𝒮₂ = Sorts (𝒢₁ .fst)
      module 𝒟₁ = Data (𝒢₁ .snd)
      module 𝒟₂ = Data (𝒢₁ .snd)

    -- Idea: Use GrpdSort≡ first to force the sorts to be equal and then use 
    -- GrpdData≡
    -- I think the equations between fields of the Data parts are going to be 
    -- really ugly...
    Grpdᴰ≡ : (Carᴰ≡ : ∀ x → 𝒮₁.Carᴰ x ≡ 𝒮₂.Carᴰ x)
          → {!!} -- ...
          → 𝒢₁ ≡ 𝒢₂
    Grpdᴰ≡ = {!!}

  open Sorts public
  open Data  public

open Grpdᴰ using (Grpdᴰ) public

open Grpd.Sorts public
open Grpd.Data public

open Grpdᴰ.Sorts public
open Grpdᴰ.Data public

-- Groupoid homomorphisms 
module _ (𝒢₁ : Grpd) (𝒢₂ : Grpd) where
  open Grpd.Vars (𝒢₁ .fst)
  private
    module 𝒮₁ = Grpd.Sorts (𝒢₁ .fst)
    module 𝒮₂ = Grpd.Sorts (𝒢₂ .fst)
    module 𝒟₁ = Grpd.Data (𝒢₁ .snd)
    module 𝒟₂ = Grpd.Data (𝒢₂ .snd)
  record _⇒_ : Set where 
    eta-equality
    field
      act  : 𝒮₁.Car → 𝒮₂.Car
      pres : 𝒮₁.Rel x y → 𝒮₂.Rel (act x) (act y)
      id   : (x : 𝒮₁.Car) → pres (𝒟₁.id x) ≡ 𝒟₂.id _
      _⁻¹  : (x₁₂ : 𝒮₁.Rel x₁ x₂) → pres (x₁₂ 𝒟₁.⁻¹) ≡ pres x₁₂ 𝒟₂.⁻¹
      _∘_  : (x₁₂ : 𝒮₁.Rel x₁ x₂) (x₂₃ : 𝒮₁.Rel x₂ x₃) 
          → pres (x₁₂ 𝒟₁.∘ x₂₃) ≡ pres x₁₂ 𝒟₂.∘ pres x₂₃

  -- Congruence
  module _ (F G : _⇒_) where
    private
      module F = _⇒_ F
      module G = _⇒_ G

    ⇒≡'' : (act≡ : F.act ≡ G.act) 
          →  (λ {x₁} {x₂} → F.pres {x₁} {x₂}) 
          ≡[ (piexti λ {x₁} → piexti λ {x₂} → piext λ x₁₂ 
           → ap₂ 𝒮₂.Rel (happly act≡) (happly act≡)) 
          ]≡ G.pres → F ≡ G
    ⇒≡'' refl refl[] = refl

    ⇒≡' : (act≡ : F.act ≡ G.act)
        → (∀ {x₁ x₂} (x₁₂ : 𝒮₁.Rel x₁ x₂) 
          →  F.pres x₁₂ 
          ≡[ ap₂ 𝒮₂.Rel (happly act≡) (happly act≡) 
          ]≡ G.pres x₁₂)
        → F ≡ G
    ⇒≡' refl pres≡ 
      = ⇒≡'' refl 
      (coe[] (funexti λ {x₁} → funexti λ {x₂} → funext λ x₁₂ 
             → pres≡ x₁₂ .[]coe))

    ⇒≡ : (act≡ : ∀ x → F.act x ≡ G.act x)
         → (∀ {x₁ x₂} (x₁₂ : 𝒮₁.Rel x₁ x₂) 
           → F.pres x₁₂ ≡[ ap₂ 𝒮₂.Rel (act≡ x₁) (act≡ x₂) ]≡ G.pres x₁₂)
         → F ≡ G
    ⇒≡ act≡ pres≡ = ⇒≡' (funext λ x → act≡ x) pres≡
open _⇒_ public

-- Dependent groupoid homomorphisms (sections)
module _ (𝒢 : Grpd) (𝒢ᴰ : Grpdᴰ 𝒢) where
  open Grpd.Vars (𝒢 .fst)
  private
    module 𝒮 = Grpd.Sorts (𝒢 .fst)
    module 𝒟 = Grpd.Data (𝒢 .snd)
    module 𝒮ᴰ = Grpdᴰ.Sorts (𝒢ᴰ .fst)
    module 𝒟ᴰ = Grpdᴰ.Data (𝒢ᴰ .snd)
  record _⇒ᴰ_ : Set where 
    eta-equality
    field
      act  : ∀ (x : 𝒮.Car) → 𝒮ᴰ.Carᴰ x
      pres : ∀ (x₁₂ : 𝒮.Rel x₁ x₂) → 𝒮ᴰ.Relᴰ (act x₁) (act x₂) x₁₂
      id   : (x : 𝒮.Car) → pres (𝒟.id x) ≡ 𝒟ᴰ.idᴰ _
      _⁻¹  : (x₁₂ : 𝒮.Rel x₁ x₂) → pres (x₁₂ 𝒟.⁻¹) ≡ pres x₁₂ 𝒟ᴰ.⁻¹ᴰ
      _∘_  : (x₁₂ : 𝒮.Rel x₁ x₂) (x₂₃ : 𝒮.Rel x₂ x₃) 
          → pres (x₁₂ 𝒟.∘ x₂₃) ≡ pres x₁₂ 𝒟ᴰ.∘ᴰ pres x₂₃
open _⇒ᴰ_ public
