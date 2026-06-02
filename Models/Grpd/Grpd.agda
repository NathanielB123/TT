{-# OPTIONS --smart-with --allow-unsolved-metas #-}

import Agda.Builtin.Equality.Rewrite

open import Utils
open import Utils.WithK
open import Utils.Macro

module Models.Grpd.Grpd where 

module Grpd where
  record Sorts : Set₁ where no-eta-equality; field
    Car : Set
    Rel : Car → Car → Set
  module _ (𝒮 : Sorts) where
    open Sorts 𝒮
    module Vars where variable
      x y z x₁ x₂ x₃ x₄ : Car 
      x₁₂ x₂₃ x₂₄ x₁₃ x₃₄ x₂₁ x₃₂ x₁₂′ : Rel x₁ x₂
    open Vars
    record Data : Set where 
      no-eta-equality
      field
        id  : (x : Car) → Rel x x
        _⁻¹ : Rel x y → Rel y x
        _∘_ : Rel x y → Rel y z → Rel x z
        
        -- Equations 
        -- TODO: I think it is probably worth making all of these proof args
        -- explicit...
        id∘ : (x₁₂ : Rel x₁ x₂) → id x₁ ∘ x₁₂ ≡ x₁₂
        ∘id : (x₁₂ : Rel x₁ x₂) → x₁₂ ∘ id x₂ ≡ x₁₂
        ∘∘  : (x₁₂ : Rel x₁ x₂) (x₂₃ : Rel x₂ x₃) (x₃₄ : Rel x₃ x₄)
            → (x₁₂ ∘ x₂₃) ∘ x₃₄ ≡ x₁₂ ∘ (x₂₃ ∘ x₃₄)
        ∘⁻¹ : (x₁₂ : Rel x₁ x₂) → x₁₂ ∘ (x₁₂ ⁻¹) ≡ id x₁
        ⁻¹∘ : (x₁₂ : Rel x₁ x₂) → (x₁₂ ⁻¹) ∘ x₁₂ ≡ id x₂

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
        ⟨∘⟩⁻¹ : (x₁₂ ∘ x₂₃) ⁻¹ ≡ (x₂₃ ⁻¹) ∘ (x₁₂ ⁻¹)
        ⟨∘⟩⁻¹ {x₁₂ = x₁₂} {x₂₃ = x₂₃} = 
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
  record Sorts : Set₁ where no-eta-equality; field
    Carᴰ : Car → Set
    Relᴰ : Carᴰ x₁ → Carᴰ x₂ → Rel x₁ x₂ → Set
  module _ (𝒮 : Sorts) where
    open Sorts 𝒮
    module Vars where variable
      xᴰ yᴰ zᴰ x₁ᴰ x₂ᴰ x₃ᴰ xᴰ′ : Carᴰ x
      x₁₂ᴰ x₂₃ᴰ x₃₄ᴰ xᴰ~ : Relᴰ x₁ᴰ x₂ᴰ x₁₂
    open Vars
    record Data : Set where 
      no-eta-equality
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

      opaque
        ⁻¹⁻¹ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) 
              → x₁₂ᴰ ⁻¹ᴰ ⁻¹ᴰ ≡[ ap (Relᴰ _ _) (⁻¹⁻¹ x₁₂) ]≡ x₁₂ᴰ
        ⁻¹⁻¹ᴰ = {!!}

      opaque
        id⁻¹ᴰ : (xᴰ : Carᴰ x) → idᴰ xᴰ ⁻¹ᴰ ≡[ ap (Relᴰ _ _) (id⁻¹ x) ]≡ idᴰ xᴰ
        id⁻¹ᴰ {x = x} xᴰ 
          rewrite id⁻¹ x
          rewrite id∘ (id x)
          -- Reflexive equations
          rewrite ∘⁻¹ (id x)
          = coe[]
          (idᴰ xᴰ ⁻¹ᴰ
          ≡⟨ sym (id∘ᴰ (idᴰ xᴰ ⁻¹ᴰ) .[]coe) ⟩
          idᴰ xᴰ ∘ᴰ (idᴰ xᴰ ⁻¹ᴰ)
          ≡⟨ ∘⁻¹ᴰ (idᴰ xᴰ) .[]coe ⟩
          idᴰ xᴰ ∎)

      ∘∘⁻¹ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃) 
           → x₁₂ᴰ ∘ᴰ (x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ)) ≡[ ap (Relᴰ _ _) (∘∘⁻¹ _ _) ]≡ x₁₂ᴰ
      ∘∘⁻¹ᴰ {x₁₂ = x₁₂} {x₂₃ = x₂₃} x₁₂ᴰ x₂₃ᴰ 
        rewrite ∘⁻¹ x₂₃
        rewrite ∘id x₁₂
        = coe[] 
        (x₁₂ᴰ ∘ᴰ ⌜ x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ) ⌝
        ≡⟨ ap! (∘⁻¹ᴰ x₂₃ᴰ .[]coe) ⟩
        x₁₂ᴰ ∘ᴰ idᴰ _
        ≡⟨ ∘idᴰ x₁₂ᴰ .[]coe ⟩
        x₁₂ᴰ ∎)

      ⁻¹∘∘ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃) 
           → ((x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ) ∘ᴰ x₂₃ᴰ ≡[ ap (Relᴰ _ _) (⁻¹∘∘ _ _) ]≡ x₂₃ᴰ 
      ⁻¹∘∘ᴰ {x₁₂ = x₁₂} {x₂₃ = x₂₃} x₁₂ᴰ x₂₃ᴰ
        rewrite ⁻¹∘ x₁₂
        rewrite id∘ x₂₃
        = coe[]
        (⌜ (x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ ⌝ ∘ᴰ x₂₃ᴰ
        ≡⟨ ap! (⁻¹∘ᴰ x₁₂ᴰ .[]coe) ⟩
        idᴰ _ ∘ᴰ x₂₃ᴰ
        ≡⟨ id∘ᴰ x₂₃ᴰ .[]coe ⟩
        x₂₃ᴰ ∎)

      ⟨∘⁻¹⟩∘ᴰ : (x₂₁ᴰ : Relᴰ x₂ᴰ x₁ᴰ x₂₁) (x₂₃ᴰ : Relᴰ x₂ᴰ x₃ᴰ x₂₃) 
              →  (x₂₁ᴰ ∘ᴰ (x₂₁ᴰ ⁻¹ᴰ)) ∘ᴰ x₂₃ᴰ 
              ≡[ ap (Relᴰ _ _) (⟨∘⁻¹⟩∘ _ _) 
              ]≡ x₂₃ᴰ
      ⟨∘⁻¹⟩∘ᴰ {x₂₁ = x₂₁} {x₂₃ = x₂₃} x₂₁ᴰ x₂₃ᴰ 
        rewrite ∘⁻¹ x₂₁
        rewrite id∘ x₂₃ 
        = coe[] 
        (⌜ x₂₁ᴰ ∘ᴰ (x₂₁ᴰ ⁻¹ᴰ) ⌝ ∘ᴰ x₂₃ᴰ
        ≡⟨ ap! (∘⁻¹ᴰ x₂₁ᴰ .[]coe) ⟩
        idᴰ _ ∘ᴰ x₂₃ᴰ
        ≡⟨ id∘ᴰ x₂₃ᴰ .[]coe ⟩
        x₂₃ᴰ ∎)

      id∘idᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂)
             → idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ ≡[ ap (Relᴰ _ _) (id∘id _) ]≡ x₁₂ᴰ ∘ᴰ idᴰ x₂ᴰ
      id∘idᴰ = {!!}

      id⁻¹∘ᴰ : (idᴰ _ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ ≡[ ap (Relᴰ _ _) id⁻¹∘ ]≡ x₁₂ᴰ
      id⁻¹∘ᴰ = {!!}

      ⁻¹∘id∘ᴰ : (x₁₂ᴰ : Relᴰ x₁ᴰ x₂ᴰ x₁₂)
              →  (x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ (idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ)
              ≡[ ap (Relᴰ _ _) (⁻¹∘id∘ x₁₂) 
              ]≡ idᴰ x₂ᴰ
      ⁻¹∘id∘ᴰ = {!!}

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
        rewrite ⁻¹∘ x₂₁
        rewrite ∘⁻¹ x₂₁
        rewrite ∘id x₂₁
        rewrite id∘ x₂₁
        rewrite coe-id x₁ᴰ
        rewrite coe-id (coeG (x₂₁ ⁻¹) x₁ᴰ)
        rewrite ⁻¹⁻¹ x₂₁
        rewrite sym (coe-∘ (x₂₁ ⁻¹) x₂₁ x₁ᴰ)
        -- Reflexive rewrites
        rewrite ∘⁻¹ (x₂₁ ⁻¹)
        rewrite ∘∘ x₂₁ (x₂₁ ⁻¹) x₂₁
        rewrite coe-∘ x₂₁ (x₂₁ ⁻¹) (coeG (x₂₁ ⁻¹) x₁ᴰ)
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
  open Sorts public
  open Data  public

Grpdᴰ : Grpd → Set₁
Grpdᴰ 𝒢 = Σ (Grpdᴰ.Sorts 𝒢) (Grpdᴰ.Data 𝒢)

open Grpd.Sorts public
open Grpd.Data public

open Grpdᴰ.Sorts public
open Grpdᴰ.Data public

-- Groupoid homomorphisms 
module _ (𝒢₁ : Grpd) (𝒢₂ : Grpd) (let (𝒮₁ , 𝒟₁) = 𝒢₁) (let (𝒮₂ , 𝒟₂) = 𝒢₂) where
  open Grpd.Vars 𝒮₁
  record _⇒_ : Set where no-eta-equality; field
    act  : 𝒮₁ .Car → 𝒮₂ .Car
    pres : 𝒮₁ .Rel x y → 𝒮₂ .Rel (act x) (act y)
    id   : (x : 𝒮₁ .Car) → pres (𝒟₁ .id x) ≡ 𝒟₂ .id _
    _⁻¹  : (x₁₂ : 𝒮₁ .Rel x₁ x₂) → pres (𝒟₁ ._⁻¹ x₁₂) ≡ 𝒟₂ ._⁻¹ (pres x₁₂)
    _∘_  : (x₁₂ : 𝒮₁ .Rel x₁ x₂) (x₂₃ : 𝒮₁ .Rel x₂ x₃) 
         → pres (𝒟₁ ._∘_ x₁₂ x₂₃) ≡ 𝒟₂ ._∘_ (pres x₁₂) (pres x₂₃)
open _⇒_ public

-- Displayed groupoid homomorphisms
module _ (𝒢 : Grpd) (𝒢ᴰ : Grpdᴰ 𝒢) (let (𝒮 , 𝒟) = 𝒢) (let (𝒮ᴰ , 𝒟ᴰ) = 𝒢ᴰ) where
  open Grpd.Vars 𝒮
  record _⇒ᴰ_ : Set where no-eta-equality; field
    act  : ∀ (x : 𝒮 .Car) → 𝒮ᴰ .Carᴰ x
    pres : ∀ (x₁₂ : 𝒮 .Rel x₁ x₂) → 𝒮ᴰ .Relᴰ (act x₁) (act x₂) x₁₂
    id   : (x : 𝒮 .Car) → pres (𝒟 .id x) ≡ 𝒟ᴰ .idᴰ _
    _⁻¹  : (x₁₂ : 𝒮 .Rel x₁ x₂) → pres (𝒟 ._⁻¹ x₁₂) ≡ 𝒟ᴰ ._⁻¹ᴰ (pres x₁₂)
    _∘_  : (x₁₂ : 𝒮 .Rel x₁ x₂) (x₂₃ : 𝒮 .Rel x₂ x₃) 
         → pres (𝒟 ._∘_ x₁₂ x₂₃) ≡ 𝒟ᴰ ._∘ᴰ_ (pres x₁₂) (pres x₂₃)
open _⇒ᴰ_ public
