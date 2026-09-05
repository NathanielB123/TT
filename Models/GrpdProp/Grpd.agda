{-# OPTIONS --smart-with --prop --rewriting --show-irrelevant --allow-unsolved-metas #-}

open import Utils.Prop
open import Utils.MacroProp

module Models.GrpdProp.Grpd where

module Grpd where
  record Sorts : Set₁ where
    eta-equality
    field
      Ob  : Set
      Hom : Ob → Ob → Set
  module _ (𝒮 : Sorts) where
    open Sorts 𝒮
    module Vars where variable
      x y z x₁ x₂ x₃ x₄ : Ob
      x₁₂ x₂₃ x₂₄ x₁₃ x₃₄ x₂₁ x₃₂ x₁₂′ : Hom x₁ x₂
    open Vars
    record Data : Set where
      eta-equality
      field
        id  : (x : Ob) → Hom x x
        _⁻¹ : Hom x y → Hom y x
        _∘_ : Hom x y → Hom y z → Hom x z

        id∘ : (x₁₂ : Hom x₁ x₂) → id x₁ ∘ x₁₂ ≡ x₁₂
        ∘id : (x₁₂ : Hom x₁ x₂) → x₁₂ ∘ id x₂ ≡ x₁₂
        ∘∘  : (x₁₂ : Hom x₁ x₂) (x₂₃ : Hom x₂ x₃) (x₃₄ : Hom x₃ x₄)
            → (x₁₂ ∘ x₂₃) ∘ x₃₄ ≡ x₁₂ ∘ (x₂₃ ∘ x₃₄)
        ∘⁻¹ : (x₁₂ : Hom x₁ x₂) → x₁₂ ∘ (x₁₂ ⁻¹) ≡ id x₁
        ⁻¹∘ : (x₁₂ : Hom x₁ x₂) → (x₁₂ ⁻¹) ∘ x₁₂ ≡ id x₂

      -- TODO: Can we get rid of the opaques in the prop version?
      opaque
        id⁻¹ : (x : Ob) → id x ⁻¹ ≡ id x
        id⁻¹ x =
          id x ⁻¹
          ≡⟨ sym (id∘ _) ⟩
          id x ∘ (id x ⁻¹)
          ≡⟨ ∘⁻¹ _ ⟩
          id x ∎

      id∘id : (x₁₂ : Hom x₁ x₂) → id x₁ ∘ x₁₂ ≡ x₁₂ ∘ id x₂
      id∘id {x₁ = x₁} {x₂ = x₂} x₁₂ =
        id x₁ ∘ x₁₂
        ≡⟨ id∘ x₁₂ ⟩
        x₁₂
        ≡⟨ sym (∘id x₁₂) ⟩
        x₁₂ ∘ id x₂ ∎

      ⁻¹∘id∘ : (x₁₂ : Hom x₁ x₂) → (x₁₂ ⁻¹) ∘ (id x₁ ∘ x₁₂) ≡ id x₂
      ⁻¹∘id∘ {x₁ = x₁} {x₂ = x₂} x₁₂ =
        (x₁₂ ⁻¹) ∘ ⌜ id x₁ ∘ x₁₂ ⌝
        ≡⟨ ap! (id∘ x₁₂) ⟩
        (x₁₂ ⁻¹) ∘ x₁₂
        ≡⟨ ⁻¹∘ x₁₂ ⟩
        id x₂ ∎

      id⁻¹∘∘id : (x₁₂ : Hom x₁ x₂) → (id x₁ ⁻¹) ∘ (x₁₂ ∘ id x₂) ≡ x₁₂
      id⁻¹∘∘id {x₁ = x₁} {x₂ = x₂} x₁₂ =
        (id x₁ ⁻¹) ∘ ⌜ x₁₂ ∘ id x₂ ⌝
        ≡⟨ ap! (∘id x₁₂) ⟩
        ⌜ id x₁ ⁻¹ ⌝ ∘ x₁₂
        ≡⟨ ap! (id⁻¹ x₁) ⟩
        id x₁ ∘ x₁₂
        ≡⟨ id∘ x₁₂ ⟩
        x₁₂ ∎

      ⁻¹∘∘ : (x₁₂ : Hom x₁ x₂) (x₂₃ : Hom x₂ x₃)
           → ((x₁₂ ⁻¹) ∘ x₁₂) ∘ x₂₃ ≡ x₂₃
      ⁻¹∘∘ x₁₂ x₂₃ =
        ⌜ (x₁₂ ⁻¹) ∘ x₁₂ ⌝ ∘ x₂₃
        ≡⟨ ap! (⁻¹∘ _) ⟩
        id _ ∘ x₂₃
        ≡⟨ id∘ _ ⟩
        x₂₃ ∎

      ∘⟨⁻¹∘⟩ : (x₁₂ : Hom x₁ x₂) (x₃₂ : Hom x₃ x₂)
             → x₁₂ ∘ ((x₃₂ ⁻¹) ∘ x₃₂) ≡ x₁₂
      ∘⟨⁻¹∘⟩ x₁₂ x₃₂ =
        x₁₂ ∘ ⌜ (x₃₂ ⁻¹) ∘ x₃₂ ⌝
        ≡⟨ ap! (⁻¹∘ _) ⟩
        x₁₂ ∘ id _
        ≡⟨ ∘id _ ⟩
        x₁₂ ∎

      ⟨∘⁻¹⟩∘ : (x₂₁ : Hom x₂ x₁) (x₂₃ : Hom x₂ x₃)
             → (x₂₁ ∘ (x₂₁ ⁻¹)) ∘ x₂₃ ≡ x₂₃
      ⟨∘⁻¹⟩∘ x₂₁ x₂₃ =
        ⌜ x₂₁ ∘ (x₂₁ ⁻¹) ⌝ ∘ x₂₃
        ≡⟨ ap! (∘⁻¹ _) ⟩
        id _ ∘ x₂₃
        ≡⟨ id∘ _ ⟩
        x₂₃ ∎

      opaque
        ⁻¹⁻¹  : (x₁₂ : Hom x₁ x₂) → x₁₂ ⁻¹ ⁻¹ ≡ x₁₂
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

      ∘∘⁻¹ : (x₁₂ : Hom x₁ x₂) (x₂₃ : Hom x₂ x₃)
           → x₁₂ ∘ (x₂₃ ∘ (x₂₃ ⁻¹)) ≡ x₁₂
      ∘∘⁻¹ x₁₂ x₂₃ =
        x₁₂ ∘ ⌜ x₂₃ ∘ (x₂₃ ⁻¹) ⌝
        ≡⟨ ap! (∘⁻¹ _) ⟩
        x₁₂ ∘ id _
        ≡⟨ ∘id _ ⟩
        x₁₂ ∎

      opaque
        ⟨∘⟩⁻¹ : (x₁₂ : Hom x₁ x₂) (x₂₃ : Hom x₂ x₃)
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

      ∘-inj₁ : {x₁₂ x₁₂' : Hom x₁ x₂} (x₂₃ : Hom x₂ x₃)
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
      Obᴰ  : Ob → Set
      Homᴰ : Obᴰ x₁ → Obᴰ x₂ → Hom x₁ x₂ → Set
  module _ (𝒮 : Sorts) where
    open Sorts 𝒮
    module Vars where variable
      xᴰ yᴰ zᴰ x₁ᴰ x₂ᴰ x₃ᴰ xᴰ′ : Obᴰ x
      x₁₂ᴰ x₂₃ᴰ x₃₄ᴰ xᴰ~ : Homᴰ x₁ᴰ x₂ᴰ x₁₂
    open Vars
    record Data : Set where
      eta-equality
      field
        idᴰ  : (xᴰ : Obᴰ x) → Homᴰ xᴰ xᴰ (id x)
        _⁻¹ᴰ : {x₁ᴰ : Obᴰ x₁} {x₂ᴰ : Obᴰ x₂}
             → Homᴰ x₁ᴰ x₂ᴰ x₁₂ → Homᴰ x₂ᴰ x₁ᴰ (x₁₂ ⁻¹)
        _∘ᴰ_ : {x₁ᴰ : Obᴰ x₁} {x₂ᴰ : Obᴰ x₂} {x₃ᴰ : Obᴰ x₃}
             → Homᴰ x₁ᴰ x₂ᴰ x₁₂ → Homᴰ x₂ᴰ x₃ᴰ x₂₃ → Homᴰ x₁ᴰ x₃ᴰ (x₁₂ ∘ x₂₃)

        -- Equations
        id∘ᴰ : {x₁ᴰ : Obᴰ x₁} {x₂ᴰ : Obᴰ x₂} (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂)
             → idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ ≡[ ap (Homᴰ x₁ᴰ x₂ᴰ) (id∘ x₁₂) ]≡ x₁₂ᴰ
        ∘idᴰ : {x₁ᴰ : Obᴰ x₁} {x₂ᴰ : Obᴰ x₂} (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂)
             → x₁₂ᴰ ∘ᴰ idᴰ x₂ᴰ ≡[ ap (Homᴰ x₁ᴰ x₂ᴰ) (∘id x₁₂) ]≡ x₁₂ᴰ
        ∘∘ᴰ  : {x₁ᴰ : Obᴰ x₁} {x₂ᴰ : Obᴰ x₂} {x₃ᴰ : Obᴰ x₃} {x₄ᴰ : Obᴰ x₄}
               (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Homᴰ x₂ᴰ x₃ᴰ x₂₃)
               (x₃₄ᴰ : Homᴰ x₃ᴰ x₄ᴰ x₃₄)
             → (x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ∘ᴰ x₃₄ᴰ
             ≡[ ap (Homᴰ x₁ᴰ x₄ᴰ) (∘∘ x₁₂ x₂₃ x₃₄) ]≡ x₁₂ᴰ ∘ᴰ (x₂₃ᴰ ∘ᴰ x₃₄ᴰ)
        ∘⁻¹ᴰ : {x₁ᴰ : Obᴰ x₁} {x₂ᴰ : Obᴰ x₂} (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂)
             → x₁₂ᴰ ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ) ≡[ ap (Homᴰ x₁ᴰ x₁ᴰ) (∘⁻¹ x₁₂) ]≡ idᴰ x₁ᴰ
        ⁻¹∘ᴰ : {x₁ᴰ : Obᴰ x₁} {x₂ᴰ : Obᴰ x₂} (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂)
             → (x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ ≡[ ap (Homᴰ x₂ᴰ x₂ᴰ) (⁻¹∘ x₁₂) ]≡ idᴰ x₂ᴰ

        -- Fibrancy
        coeG   : Hom x₁ x₂ → Obᴰ x₁ → Obᴰ x₂
        cohG   : (x₁₂ : Hom x₁ x₂) (xᴰ : Obᴰ x₁) → Homᴰ xᴰ (coeG x₁₂ xᴰ) x₁₂
        coe-id : (xᴰ : Obᴰ x) → coeG (id x) xᴰ ≡ xᴰ
        coe-∘  : (x₁₂ : Hom x₁ x₂) (x₂₃ : Hom x₂ x₃) (xᴰ : Obᴰ x₁)
               → coeG (x₁₂ ∘ x₂₃) xᴰ ≡ coeG x₂₃ (coeG x₁₂ xᴰ)
        coh-id : (xᴰ : Obᴰ x)
               →  cohG (id x) xᴰ ≡[ ap (λ □ → Homᴰ xᴰ □ (id x)) (coe-id xᴰ)
               ]≡ idᴰ xᴰ
        coh-∘  : (x₁₂ : Hom x₁ x₂) (x₂₃ : Hom x₂ x₃) (xᴰ : Obᴰ x₁)
               → cohG (x₁₂ ∘ x₂₃) xᴰ
               ≡[ ap (λ □ → Homᴰ xᴰ □ (x₁₂ ∘ x₂₃)) (coe-∘ x₁₂ x₂₃ xᴰ)
               ]≡ cohG x₁₂ xᴰ ∘ᴰ cohG x₂₃ (coeG x₁₂ xᴰ)

      ∘⟨⁻¹∘⟩ᴰ : (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂) (x₃₂ᴰ : Homᴰ x₃ᴰ x₂ᴰ x₃₂)
              →  x₁₂ᴰ ∘ᴰ ((x₃₂ᴰ ⁻¹ᴰ) ∘ᴰ x₃₂ᴰ)
              ≡[ ap (Homᴰ x₁ᴰ x₂ᴰ) (∘⟨⁻¹∘⟩ x₁₂ x₃₂)
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

      ⁻¹∘∘ᴰ : (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Homᴰ x₂ᴰ x₃ᴰ x₂₃)
            → ((x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ) ∘ᴰ x₂₃ᴰ ≡[ ap (Homᴰ _ _) (⁻¹∘∘ _ _) ]≡ x₂₃ᴰ
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
        ⁻¹⁻¹ᴰ : (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂)
              → x₁₂ᴰ ⁻¹ᴰ ⁻¹ᴰ ≡[ ap (Homᴰ _ _) (⁻¹⁻¹ x₁₂) ]≡ x₁₂ᴰ
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
        id⁻¹ᴰ : (xᴰ : Obᴰ x) → idᴰ xᴰ ⁻¹ᴰ ≡[ ap (Homᴰ _ _) (id⁻¹ x) ]≡ idᴰ xᴰ
        id⁻¹ᴰ {x = x} xᴰ
          rewrite ↑≡ id⁻¹ x
          rewrite ↑≡ id∘ (id x)
          = coe[]
          (idᴰ xᴰ ⁻¹ᴰ
          ≡⟨ sym (id∘ᴰ (idᴰ xᴰ ⁻¹ᴰ) .[]coe) ⟩
          idᴰ xᴰ ∘ᴰ (idᴰ xᴰ ⁻¹ᴰ)
          ≡⟨ ∘⁻¹ᴰ (idᴰ xᴰ) .[]coe ⟩
          idᴰ xᴰ ∎)

      ∘∘⁻¹ᴰ : (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Homᴰ x₂ᴰ x₃ᴰ x₂₃)
           → x₁₂ᴰ ∘ᴰ (x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ)) ≡[ ap (Homᴰ _ _) (∘∘⁻¹ _ _) ]≡ x₁₂ᴰ
      ∘∘⁻¹ᴰ {x₁₂ = x₁₂} {x₂₃ = x₂₃} x₁₂ᴰ x₂₃ᴰ
        rewrite ↑≡ ∘⁻¹ x₂₃
        rewrite ↑≡ ∘id x₁₂
        = coe[]
        (x₁₂ᴰ ∘ᴰ ⌜ x₂₃ᴰ ∘ᴰ (x₂₃ᴰ ⁻¹ᴰ) ⌝
        ≡⟨ ap! (∘⁻¹ᴰ x₂₃ᴰ .[]coe) ⟩
        x₁₂ᴰ ∘ᴰ idᴰ _
        ≡⟨ ∘idᴰ x₁₂ᴰ .[]coe ⟩
        x₁₂ᴰ ∎)

      ⟨∘⁻¹⟩∘ᴰ : (x₂₁ᴰ : Homᴰ x₂ᴰ x₁ᴰ x₂₁) (x₂₃ᴰ : Homᴰ x₂ᴰ x₃ᴰ x₂₃)
              →  (x₂₁ᴰ ∘ᴰ (x₂₁ᴰ ⁻¹ᴰ)) ∘ᴰ x₂₃ᴰ
              ≡[ ap (Homᴰ _ _) (⟨∘⁻¹⟩∘ _ _)
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

      id∘idᴰ : (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂)
             → idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ ≡[ ap (Homᴰ _ _) (id∘id _) ]≡ x₁₂ᴰ ∘ᴰ idᴰ x₂ᴰ
      id∘idᴰ {x₁ᴰ = x₁ᴰ} {x₂ᴰ = x₂ᴰ} {x₁₂ = x₁₂} x₁₂ᴰ
        rewrite ↑≡ id∘ x₁₂
        rewrite ↑≡ ∘id x₁₂
        = coe[]
        (idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ
        ≡⟨ id∘ᴰ x₁₂ᴰ .[]coe ⟩
        x₁₂ᴰ
        ≡⟨ sym (∘idᴰ x₁₂ᴰ .[]coe) ⟩
        x₁₂ᴰ ∘ᴰ idᴰ x₂ᴰ ∎)

      id⁻¹∘ᴰ : (x₁₂ᴰ : Homᴰ {x₁ = x₁} x₁ᴰ x₂ᴰ x₁₂)
             → (idᴰ _ ⁻¹ᴰ) ∘ᴰ x₁₂ᴰ ≡[ ap (Homᴰ _ _) id⁻¹∘ ]≡ x₁₂ᴰ
      id⁻¹∘ᴰ {x₁ = x₁} {x₁₂ = x₁₂} x₁₂ᴰ
        rewrite ↑≡ id⁻¹ x₁
        rewrite ↑≡ id∘ x₁₂
        = coe[]
        (⌜ idᴰ _ ⁻¹ᴰ ⌝ ∘ᴰ x₁₂ᴰ
        ≡⟨ ap! (id⁻¹ᴰ _ .[]coe) ⟩
        idᴰ _ ∘ᴰ x₁₂ᴰ
        ≡⟨ id∘ᴰ _ .[]coe ⟩
        x₁₂ᴰ ∎)

      ⁻¹∘id∘ᴰ : (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂)
              → (x₁₂ᴰ ⁻¹ᴰ) ∘ᴰ (idᴰ x₁ᴰ ∘ᴰ x₁₂ᴰ)
              ≡[ ap (Homᴰ _ _) (⁻¹∘id∘ x₁₂)
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
        ⟨∘⟩⁻¹ᴰ : (x₁₂ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂) (x₂₃ᴰ : Homᴰ x₂ᴰ x₃ᴰ x₂₃)
               → (x₁₂ᴰ ∘ᴰ x₂₃ᴰ) ⁻¹ᴰ ≡[ ap (Homᴰ _ _) (⟨∘⟩⁻¹ _ _) ]≡ (x₂₃ᴰ ⁻¹ᴰ) ∘ᴰ (x₁₂ᴰ ⁻¹ᴰ)
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

      coeG⁻¹  : Hom x₁ x₂ → Obᴰ x₂ → Obᴰ x₁
      coeG⁻¹ x₁₂ = coeG (x₁₂ ⁻¹)
      cohG⁻¹ : (x₂₁ : Hom x₂ x₁) (xᴰ : Obᴰ x₁) → Homᴰ (coeG⁻¹ x₂₁ xᴰ) xᴰ x₂₁
      cohG⁻¹ x₂₁ xᴰ = tr (Homᴰ _ _) (⁻¹⁻¹ _) (cohG (x₂₁ ⁻¹) _ ⁻¹ᴰ)

      coe-coe⁻¹ : (x₂₁ : Hom x₂ x₁) (x₁ᴰ : Obᴰ x₁)
                → coeG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ) ≡ x₁ᴰ
      coe-coe⁻¹ x₂₁ x₁ᴰ =
        coeG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ)
        ≡⟨ sym (coe-∘ _ _ _) ⟩
        coeG ⌜ (x₂₁ ⁻¹) ∘ x₂₁ ⌝ x₁ᴰ
        ≡⟨ ap! (⁻¹∘ x₂₁) ⟩
        coeG (id _) x₁ᴰ
        ≡⟨ coe-id x₁ᴰ ⟩
        x₁ᴰ ∎

      coh-coe⁻¹ : (x₂₁ : Hom x₂ x₁) (x₁ᴰ : Obᴰ x₁)
                →  cohG x₂₁ (coeG (x₂₁ ⁻¹) x₁ᴰ)
                ≡[ ap₂ (Homᴰ _) (coe-coe⁻¹ x₂₁ x₁ᴰ) (sym (⁻¹⁻¹ x₂₁))
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

      ∘-inj₁ᴰ : {x₁₂ᴰ x₁₂'ᴰ : Homᴰ x₁ᴰ x₂ᴰ x₁₂} (x₂₃ᴰ : Homᴰ x₂ᴰ x₃ᴰ x₂₃)
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

  -- Equality of displayed groupoid sorts
  module _ {𝒮₁ 𝒮₂ : Sorts} where
    private
      module 𝒮₁ = Sorts 𝒮₁
      module 𝒮₂ = Sorts 𝒮₂

    sorts≡'' : (Obᴰ≡ : 𝒮₁.Obᴰ ≡ 𝒮₂.Obᴰ)
             → ((λ {x y} → 𝒮₁.Homᴰ {x} {y})
                ≡[ (piexti λ {x} → piexti λ {y} → piext[] (happly Obᴰ≡) λ x₁₂ᴰ
                   → piext[] (happly Obᴰ≡) λ y₁₂ᴰ → refl)
                ]≡ 𝒮₂.Homᴰ)
             → 𝒮₁ ≡ 𝒮₂
    sorts≡'' refl refl[] = refl

    sorts≡' : (Obᴰ≡ : 𝒮₁.Obᴰ ≡ 𝒮₂.Obᴰ)
            → (∀ {x y x₁ᴰ y₁ᴰ x₂ᴰ y₂ᴰ} (xy : Hom x y)
                 (x₁₂ᴰ : x₁ᴰ ≡[ happly Obᴰ≡ ]≡ x₂ᴰ)
                 (y₁₂ᴰ : y₁ᴰ ≡[ happly Obᴰ≡ ]≡ y₂ᴰ)
               → 𝒮₁.Homᴰ x₁ᴰ y₁ᴰ xy ≡ 𝒮₂.Homᴰ x₂ᴰ y₂ᴰ xy)
            → 𝒮₁ ≡ 𝒮₂
    sorts≡' refl Homᴰ≡ =
      sorts≡'' refl (coe[] (funexti λ {x} → funexti λ {y} → funext λ xᴰ →
      funext λ yᴰ → funext λ xy → Homᴰ≡ xy refl[] refl[]))

    sorts≡ : (Obᴰ≡ : ∀ x → 𝒮₁.Obᴰ x ≡ 𝒮₂.Obᴰ x)
           → (∀ {x y x₁ᴰ y₁ᴰ x₂ᴰ y₂ᴰ} (xy : Hom x y)
                (x₁₂ᴰ : x₁ᴰ ≡[ Obᴰ≡ x ]≡ x₂ᴰ)
                (y₁₂ᴰ : y₁ᴰ ≡[ Obᴰ≡ y ]≡ y₂ᴰ)
              → 𝒮₁.Homᴰ x₁ᴰ y₁ᴰ xy ≡ 𝒮₂.Homᴰ x₂ᴰ y₂ᴰ xy)
           → 𝒮₁ ≡ 𝒮₂
    sorts≡ Obᴰ≡ Homᴰ≡ = sorts≡' (funext λ x → Obᴰ≡ x) Homᴰ≡

  -- Equality of displayed groupoid data
  module _ {𝒮} {𝒟₁ 𝒟₂ : Data 𝒮} where
    open Sorts 𝒮
    private
      module 𝒟₁ = Data 𝒟₁
      module 𝒟₂ = Data 𝒟₂

    data≡'' : (idᴰ≡ : (λ {x} → 𝒟₁.idᴰ {x}) ≡ 𝒟₂.idᴰ)
              (⁻¹ᴰ≡ : (λ {x y xy xᴰ yᴰ} → 𝒟₁._⁻¹ᴰ {x} {y} {xy} {xᴰ} {yᴰ})
                    ≡ 𝒟₂._⁻¹ᴰ)
              (∘ᴰ≡ : (λ {x y z xy yz xᴰ yᴰ zᴰ}
                      → 𝒟₁._∘ᴰ_ {x} {y} {z} {xy} {yz} {xᴰ} {yᴰ} {zᴰ})
                   ≡ 𝒟₂._∘ᴰ_)
              (coeG≡ : (λ {x y} → 𝒟₁.coeG {x} {y}) ≡ 𝒟₂.coeG)
              (cohG≡ : (λ {x y} → 𝒟₁.cohG {x} {y})
                     ≡[ (piexti λ {x} → piexti λ {y} →
                        piext λ xy → piext λ xᴰ →
                        ap (λ □ → Homᴰ xᴰ □ xy)
                           (happly (happly (happlyi (happlyi coeG≡)))))
                     ]≡ 𝒟₂.cohG)
                → 𝒟₁ ≡ 𝒟₂
    data≡'' refl refl refl refl refl[] = refl

    data≡' : (idᴰ≡ : (λ {x} → 𝒟₁.idᴰ {x}) ≡ 𝒟₂.idᴰ)
             (⁻¹ᴰ≡ : (λ {x y xy xᴰ yᴰ} → 𝒟₁._⁻¹ᴰ {x} {y} {xy} {xᴰ} {yᴰ})
                   ≡ 𝒟₂._⁻¹ᴰ)
             (∘ᴰ≡ : (λ {x y z xy yz xᴰ yᴰ zᴰ}
                     → 𝒟₁._∘ᴰ_ {x} {y} {z} {xy} {yz} {xᴰ} {yᴰ} {zᴰ})
                  ≡ 𝒟₂._∘ᴰ_)
             (coeG≡ : (λ {x y} → 𝒟₁.coeG {x} {y}) ≡ 𝒟₂.coeG)
             (cohG≡ : ∀ {x y} (xy : Hom x y) (xᴰ : Obᴰ x)
                    → 𝒟₁.cohG xy xᴰ
                    ≡[ ap (λ □ → Homᴰ xᴰ □ xy)
                          (happly (happly (happlyi (happlyi coeG≡))))
                    ]≡ 𝒟₂.cohG xy xᴰ)
               → 𝒟₁ ≡ 𝒟₂
    data≡' refl refl refl refl cohG≡ =
      data≡'' refl refl refl refl (coe[] (funexti λ {x} → funexti λ {y} →
      funext λ xy → funext λ xᴰ → cohG≡ xy xᴰ .[]coe))

    data≡ : (idᴰ≡ : ∀ {x} (xᴰ : Obᴰ x) → 𝒟₁.idᴰ xᴰ ≡ 𝒟₂.idᴰ xᴰ)
            (⁻¹ᴰ≡ : ∀ {x y xᴰ yᴰ} {xy : Hom x y} (xyᴰ : Homᴰ xᴰ yᴰ xy)
                  → xyᴰ 𝒟₁.⁻¹ᴰ ≡ xyᴰ 𝒟₂.⁻¹ᴰ)
            (∘ᴰ≡ : ∀ {x y z xᴰ yᴰ zᴰ} {xy : Hom x y} {yz : Hom y z}
                     (xyᴰ : Homᴰ xᴰ yᴰ xy) (yzᴰ : Homᴰ yᴰ zᴰ yz)
                 → xyᴰ 𝒟₁.∘ᴰ yzᴰ ≡ xyᴰ 𝒟₂.∘ᴰ yzᴰ)
            (coeG≡ : ∀ {x y} (xy : Hom x y) (xᴰ : Obᴰ x)
                   → 𝒟₁.coeG xy xᴰ ≡ 𝒟₂.coeG xy xᴰ)
            (cohG≡ : ∀ {x y} (xy : Hom x y) (xᴰ : Obᴰ x)
                   → 𝒟₁.cohG xy xᴰ
                   ≡[ ap (λ □ → Homᴰ xᴰ □ xy) (coeG≡ xy xᴰ)
                   ]≡ 𝒟₂.cohG xy xᴰ)
              → 𝒟₁ ≡ 𝒟₂
    data≡ idᴰ≡ ⁻¹ᴰ≡ ∘ᴰ≡ coeG≡ cohG≡ =
      data≡' (funexti λ {x} → funext λ xᴰ → idᴰ≡ xᴰ)
             (funexti λ {x} → funexti λ {y} → funexti λ {xᴰ} → funexti λ {yᴰ} →
             funexti λ {xy} → funext λ xyᴰ → ⁻¹ᴰ≡ xyᴰ)
             (funexti λ {x} → funexti λ {y} → funexti λ {z} → funexti λ {xᴰ} →
             funexti λ {yᴰ} → funexti λ {zᴰ} → funexti λ {xy} →
             funexti λ {yz} → funext λ xyᴰ → funext λ yzᴰ → ∘ᴰ≡ xyᴰ yzᴰ)
             (funexti λ {x} → funexti λ {y} → funext λ xy → funext λ xᴰ →
             coeG≡ xy xᴰ)
             cohG≡

  Grpdᴰ : Set₁
  Grpdᴰ = Σ Sorts Data

  -- Equality of displayed groupoids
  module _ (𝒢₁ 𝒢₂ : Grpdᴰ) where
    private
      module 𝒮₁ = Sorts (𝒢₁ .fst)
      module 𝒮₂ = Sorts (𝒢₂ .fst)
      module 𝒟₁ = Data (𝒢₁ .snd)
      module 𝒟₂ = Data (𝒢₂ .snd)

    record Grpdᴰ≡ : Prop₁ where
      field
        Obᴰ≡ : ∀ x → 𝒮₁.Obᴰ x ≡ 𝒮₂.Obᴰ x
        Homᴰ≡ : ∀ {x y x₁ᴰ y₁ᴰ x₂ᴰ y₂ᴰ} (xy : Hom x y)
                  (x₁₂ᴰ : x₁ᴰ ≡[ Obᴰ≡ x ]≡ x₂ᴰ)
                  (y₁₂ᴰ : y₁ᴰ ≡[ Obᴰ≡ y ]≡ y₂ᴰ)
              → 𝒮₁.Homᴰ x₁ᴰ y₁ᴰ xy ≡ 𝒮₂.Homᴰ x₂ᴰ y₂ᴰ xy

        idᴰ≡ : ∀ {x x₁ᴰ x₂ᴰ} (x₁₂ᴰ : x₁ᴰ ≡[ Obᴰ≡ x ]≡ x₂ᴰ)
             → 𝒟₁.idᴰ x₁ᴰ ≡[ Homᴰ≡ (id x) x₁₂ᴰ x₁₂ᴰ ]≡ 𝒟₂.idᴰ x₂ᴰ
        ⁻¹ᴰ≡ : ∀ {x y x₁ᴰ x₂ᴰ y₁ᴰ y₂ᴰ}
                 (x₁₂ᴰ : x₁ᴰ ≡[ Obᴰ≡ x ]≡ x₂ᴰ)
                 (y₁₂ᴰ : y₁ᴰ ≡[ Obᴰ≡ y ]≡ y₂ᴰ)
                 {xy : Hom x y}
                 {xy₁ᴰ xy₂ᴰ}
              → xy₁ᴰ ≡[ Homᴰ≡ xy x₁₂ᴰ y₁₂ᴰ ]≡ xy₂ᴰ
              → xy₁ᴰ 𝒟₁.⁻¹ᴰ ≡[ Homᴰ≡ (xy ⁻¹) y₁₂ᴰ x₁₂ᴰ ]≡ xy₂ᴰ 𝒟₂.⁻¹ᴰ
        ∘ᴰ≡ : ∀ {x y z x₁ᴰ y₁ᴰ z₁ᴰ x₂ᴰ y₂ᴰ z₂ᴰ}
                (x₁₂ᴰ : x₁ᴰ ≡[ Obᴰ≡ x ]≡ x₂ᴰ)
                (y₁₂ᴰ : y₁ᴰ ≡[ Obᴰ≡ y ]≡ y₂ᴰ)
                (z₁₂ᴰ : z₁ᴰ ≡[ Obᴰ≡ z ]≡ z₂ᴰ)
                {xy : Hom x y} {yz : Hom y z}
                {xy₁ᴰ xy₂ᴰ yz₁ᴰ yz₂ᴰ}
            →   (xy₁ᴰ ≡[ Homᴰ≡ xy x₁₂ᴰ y₁₂ᴰ ]≡ xy₂ᴰ)
            →   (yz₁ᴰ ≡[ Homᴰ≡ yz y₁₂ᴰ z₁₂ᴰ ]≡ yz₂ᴰ)
            → xy₁ᴰ 𝒟₁.∘ᴰ yz₁ᴰ ≡[ Homᴰ≡ (xy ∘ yz) x₁₂ᴰ z₁₂ᴰ ]≡ xy₂ᴰ 𝒟₂.∘ᴰ yz₂ᴰ
        coeG≡ : ∀ {x y x₁ᴰ x₂ᴰ} (xy : Hom x y)
                  (x₁₂ᴰ : x₁ᴰ ≡[ Obᴰ≡ x ]≡ x₂ᴰ)
              → 𝒟₁.coeG xy x₁ᴰ ≡[ Obᴰ≡ y ]≡ 𝒟₂.coeG xy x₂ᴰ
        cohG≡ : ∀ {x y x₁ᴰ x₂ᴰ} (xy : Hom x y)
                  (x₁₂ᴰ : x₁ᴰ ≡[ Obᴰ≡ x ]≡ x₂ᴰ)
              → 𝒟₁.cohG xy x₁ᴰ
              ≡[ Homᴰ≡ xy x₁₂ᴰ (coeG≡ xy x₁₂ᴰ)
              ]≡ 𝒟₂.cohG xy x₂ᴰ

      grpd≡ : 𝒢₁ ≡ 𝒢₂
      grpd≡ with refl ← ↑≡ (sorts≡ Obᴰ≡ Homᴰ≡)
        = ap (_ ,_)
          (data≡ (λ xᴰ → idᴰ≡ refl[] .[]coe)
                 (λ xyᴰ → ⁻¹ᴰ≡ refl[] refl[] refl[] .[]coe)
                 (λ xyᴰ yzᴰ → ∘ᴰ≡ refl[] refl[] refl[] refl[] refl[] .[]coe)
                 (λ xy xᴰ → coeG≡ xy refl[] .[]coe)
                 (λ xy xᴰ → cohG≡ xy refl[]))

open Grpdᴰ using (Grpdᴰ; Grpdᴰ≡) public

open Grpd.Sorts public
open Grpd.Data public

open Grpdᴰ.Sorts public
open Grpdᴰ.Data public
open Grpdᴰ≡ public

-- Groupoid homomorphisms (functors)
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
      act  : 𝒮₁.Ob → 𝒮₂.Ob
      pres : 𝒮₁.Hom x y → 𝒮₂.Hom (act x) (act y)
      pres-∘  : (x₁₂ : 𝒮₁.Hom x₁ x₂) (x₂₃ : 𝒮₁.Hom x₂ x₃)
          → pres (x₁₂ 𝒟₁.∘ x₂₃) ≡ pres x₁₂ 𝒟₂.∘ pres x₂₃

    -- Preservation of identity and inverse is derivable
    pres-id : (x : 𝒮₁.Ob) → pres (𝒟₁.id x) ≡ 𝒟₂.id (act x)
    pres-id x =
      pres (𝒟₁.id x)
      ≡⟨ sym (𝒟₂.∘∘⁻¹ (pres (𝒟₁.id x)) (pres (𝒟₁.id x))) ⟩
      pres (𝒟₁.id x) 𝒟₂.∘ (pres (𝒟₁.id x) 𝒟₂.∘ (pres (𝒟₁.id x) 𝒟₂.⁻¹))
      ≡⟨ sym (𝒟₂.∘∘ (pres (𝒟₁.id x)) (pres (𝒟₁.id x))
                    (pres (𝒟₁.id x) 𝒟₂.⁻¹)) ⟩
      ⌜ pres (𝒟₁.id x) 𝒟₂.∘ pres (𝒟₁.id x) ⌝ 𝒟₂.∘ (pres (𝒟₁.id x) 𝒟₂.⁻¹)
      ≡⟨ ap! (sym (pres-∘ (𝒟₁.id x) (𝒟₁.id x))) ⟩
      (pres ⌜ 𝒟₁.id x 𝒟₁.∘ 𝒟₁.id x ⌝) 𝒟₂.∘ (pres (𝒟₁.id x) 𝒟₂.⁻¹)
      ≡⟨ ap! (𝒟₁.id∘ (𝒟₁.id x)) ⟩
      pres (𝒟₁.id x) 𝒟₂.∘ (pres (𝒟₁.id x) 𝒟₂.⁻¹)
      ≡⟨ 𝒟₂.∘⁻¹ (pres (𝒟₁.id x)) ⟩
      𝒟₂.id (act x) ∎

    pres-⁻¹ : (x₁₂ : 𝒮₁.Hom x₁ x₂) → pres (x₁₂ 𝒟₁.⁻¹) ≡ pres x₁₂ 𝒟₂.⁻¹
    pres-⁻¹ {x₁ = x₁} {x₂ = x₂} x₁₂ =
      pres (x₁₂ 𝒟₁.⁻¹)
      ≡⟨ sym (𝒟₂.∘∘⁻¹ (pres (x₁₂ 𝒟₁.⁻¹)) (pres x₁₂)) ⟩
      pres (x₁₂ 𝒟₁.⁻¹) 𝒟₂.∘ (pres x₁₂ 𝒟₂.∘ (pres x₁₂ 𝒟₂.⁻¹))
      ≡⟨ sym (𝒟₂.∘∘ (pres (x₁₂ 𝒟₁.⁻¹)) (pres x₁₂) (pres x₁₂ 𝒟₂.⁻¹)) ⟩
      ⌜ pres (x₁₂ 𝒟₁.⁻¹) 𝒟₂.∘ pres x₁₂ ⌝ 𝒟₂.∘ (pres x₁₂ 𝒟₂.⁻¹)
      ≡⟨ ap! (sym (pres-∘ (x₁₂ 𝒟₁.⁻¹) x₁₂)) ⟩
      pres ⌜ (x₁₂ 𝒟₁.⁻¹) 𝒟₁.∘ x₁₂ ⌝ 𝒟₂.∘ (pres x₁₂ 𝒟₂.⁻¹)
      ≡⟨ ap! (𝒟₁.⁻¹∘ x₁₂) ⟩
      ⌜ pres (𝒟₁.id x₂) ⌝ 𝒟₂.∘ (pres x₁₂ 𝒟₂.⁻¹)
      ≡⟨ ap! (pres-id x₂) ⟩
      𝒟₂.id (act x₂) 𝒟₂.∘ (pres x₁₂ 𝒟₂.⁻¹)
      ≡⟨ 𝒟₂.id∘ (pres x₁₂ 𝒟₂.⁻¹)  ⟩
      pres x₁₂ 𝒟₂.⁻¹ ∎

  -- Equality of groupoid functors
  module _ {F G : _⇒_} where
    private
      module F = _⇒_ F
      module G = _⇒_ G

    ⇒≡'' : (act≡ : F.act ≡ G.act)
          →  (λ {x₁} {x₂} → F.pres {x₁} {x₂})
          ≡[ (piexti λ {x₁} → piexti λ {x₂} → piext λ x₁₂
           → ap₂ 𝒮₂.Hom (happly act≡) (happly act≡))
          ]≡ G.pres → F ≡ G
    ⇒≡'' refl refl[] = refl

    ⇒≡' : (act≡ : F.act ≡ G.act)
        → (∀ {x₁ x₂} (x₁₂ : 𝒮₁.Hom x₁ x₂)
          →  F.pres x₁₂
          ≡[ ap₂ 𝒮₂.Hom (happly act≡) (happly act≡)
          ]≡ G.pres x₁₂)
        → F ≡ G
    ⇒≡' refl pres≡ = ⇒≡'' refl
      (coe[] (funexti λ {x₁} → funexti λ {x₂} → funext λ x₁₂ →
      pres≡ x₁₂ .[]coe))

    ⇒≡ : (act≡ : ∀ x → F.act x ≡ G.act x)
         → (∀ {x₁ x₂} (x₁₂ : 𝒮₁.Hom x₁ x₂)
           → F.pres x₁₂ ≡[ ap₂ 𝒮₂.Hom (act≡ x₁) (act≡ x₂) ]≡ G.pres x₁₂)
         → F ≡ G
    ⇒≡ act≡ pres≡ = ⇒≡' (funext λ x → act≡ x) pres≡

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
      act     : ∀ (x : 𝒮.Ob) → 𝒮ᴰ.Obᴰ x
      pres    : ∀ (x₁₂ : 𝒮.Hom x₁ x₂) → 𝒮ᴰ.Homᴰ (act x₁) (act x₂) x₁₂
      pres-∘ᴰ : (x₁₂ : 𝒮.Hom x₁ x₂) (x₂₃ : 𝒮.Hom x₂ x₃)
              → pres (x₁₂ 𝒟.∘ x₂₃) ≡ pres x₁₂ 𝒟ᴰ.∘ᴰ pres x₂₃

    pres-idᴰ  : (x : 𝒮.Ob) → pres (𝒟.id x) ≡ 𝒟ᴰ.idᴰ (act x)
    pres-idᴰ x
      rewrite ↑≡ 𝒟.id∘ (𝒟.id x)
      rewrite ↑≡ 𝒟.id⁻¹ x =
      pres (𝒟.id x)
      ≡⟨ sym (𝒟ᴰ.∘∘⁻¹ᴰ (pres (𝒟.id x)) (pres (𝒟.id x)) .[]coe) ⟩
      pres (𝒟.id x) 𝒟ᴰ.∘ᴰ (pres (𝒟.id x) 𝒟ᴰ.∘ᴰ (pres (𝒟.id x) 𝒟ᴰ.⁻¹ᴰ))
      ≡⟨ sym (𝒟ᴰ.∘∘ᴰ (pres (𝒟.id x)) (pres (𝒟.id x))
                     (pres (𝒟.id x) 𝒟ᴰ.⁻¹ᴰ) .[]coe) ⟩
      ⌜ pres (𝒟.id x) 𝒟ᴰ.∘ᴰ pres (𝒟.id x) ⌝ 𝒟ᴰ.∘ᴰ (pres (𝒟.id x) 𝒟ᴰ.⁻¹ᴰ)
      ≡⟨ ap! (sym (pres-∘ᴰ (𝒟.id x) (𝒟.id x))) ⟩
      (pres ⌜ 𝒟.id x 𝒟.∘ 𝒟.id x ⌝ 𝒟ᴰ.∘ᴰ (pres (𝒟.id x) 𝒟ᴰ.⁻¹ᴰ))
      ≡⟨⟩
      pres (𝒟.id x) 𝒟ᴰ.∘ᴰ (pres (𝒟.id x) 𝒟ᴰ.⁻¹ᴰ)
      ≡⟨ 𝒟ᴰ.∘⁻¹ᴰ (pres (𝒟.id x)) .[]coe ⟩
      𝒟ᴰ.idᴰ (act x) ∎

    pres-⁻¹ᴰ  : (x₁₂ : 𝒮.Hom x₁ x₂) → pres (x₁₂ 𝒟.⁻¹) ≡ pres x₁₂ 𝒟ᴰ.⁻¹ᴰ
    pres-⁻¹ᴰ {x₁ = x₁} {x₂ = x₂} x₁₂
      rewrite ↑≡ 𝒟.∘⁻¹ x₁₂
      rewrite ↑≡ 𝒟.⁻¹∘ x₁₂
      rewrite ↑≡ 𝒟.∘id (x₁₂ 𝒟.⁻¹)
      rewrite ↑≡ 𝒟.id∘ (x₁₂ 𝒟.⁻¹)
      =
      pres (x₁₂ 𝒟.⁻¹)
      ≡⟨ sym (𝒟ᴰ.∘∘⁻¹ᴰ (pres (x₁₂ 𝒟.⁻¹)) (pres x₁₂) .[]coe) ⟩
      pres (x₁₂ 𝒟.⁻¹) 𝒟ᴰ.∘ᴰ (pres x₁₂ 𝒟ᴰ.∘ᴰ (pres x₁₂ 𝒟ᴰ.⁻¹ᴰ))
      ≡⟨ sym (𝒟ᴰ.∘∘ᴰ (pres (x₁₂ 𝒟.⁻¹)) (pres x₁₂) (pres x₁₂ 𝒟ᴰ.⁻¹ᴰ) .[]coe) ⟩
      ⌜ pres (x₁₂ 𝒟.⁻¹) 𝒟ᴰ.∘ᴰ pres x₁₂ ⌝ 𝒟ᴰ.∘ᴰ (pres x₁₂ 𝒟ᴰ.⁻¹ᴰ)
      ≡⟨ ap! (sym (pres-∘ᴰ (x₁₂ 𝒟.⁻¹) x₁₂)) ⟩
      (pres ⌜ (x₁₂ 𝒟.⁻¹) 𝒟.∘ x₁₂ ⌝ 𝒟ᴰ.∘ᴰ (pres x₁₂ 𝒟ᴰ.⁻¹ᴰ))
      ≡⟨⟩
      ⌜ pres (𝒟.id x₂) ⌝ 𝒟ᴰ.∘ᴰ (pres x₁₂ 𝒟ᴰ.⁻¹ᴰ)
      ≡⟨ ap! (pres-idᴰ x₂) ⟩
      𝒟ᴰ.idᴰ (act x₂) 𝒟ᴰ.∘ᴰ (pres x₁₂ 𝒟ᴰ.⁻¹ᴰ)
      ≡⟨ 𝒟ᴰ.id∘ᴰ (pres x₁₂ 𝒟ᴰ.⁻¹ᴰ) .[]coe ⟩
      pres x₁₂ 𝒟ᴰ.⁻¹ᴰ ∎

open _⇒_ public
open _⇒ᴰ_ public
