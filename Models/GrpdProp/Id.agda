{-# OPTIONS --rewriting --prop --smart-with --show-irrelevant #-}

open import Utils.Prop
open import Utils.MacroProp

open import Models.GrpdProp.Grpd
open import Models.GrpdProp.Motives
open import Models.GrpdProp.Subst

-- Identity types
module Models.GrpdProp.Id where

-- Identity types
module _ (⟦A⟧ : ⟦Ty⟧ ⟦Γ⟧) (⟦t⟧ ⟦u⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧) where
  private
    module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
    module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
    module ⟦t⟧ = _⇒ᴰ_ ⟦t⟧
    module ⟦u⟧ = _⇒ᴰ_ ⟦u⟧

  ⟦Id⟧ : ⟦Ty⟧ ⟦Γ⟧
  ⟦Id⟧ .fst .Carᴰ ρ 
    = ⟦A⟧ .fst .Relᴰ (⟦t⟧.act ρ) (⟦u⟧.act ρ) (⟦Γ⟧.id ρ)
  ⟦Id⟧ .fst .Relᴰ τ₁ τ₂ ρ₁₂ 
    = Lift (tr (⟦A⟧ .fst .Relᴰ _ _) (⟦Γ⟧.⁻¹∘id∘ ρ₁₂) 
           ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)) ≡ τ₂)
  ⟦Id⟧ .snd .idᴰ {x = ρ} τ .lower
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ =
    (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ ⟦A⟧.∘ᴰ ⌜ ⟦u⟧.pres (⟦Γ⟧.id ρ) ⌝)
    ≡⟨ ap! (⟦u⟧.id ρ) ⟩
    (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ τ ⟦A⟧.∘ᴰ ⟦A⟧.idᴰ (⟦u⟧.act ρ) ⌝
    ≡⟨ ap! (⟦A⟧.∘idᴰ τ .[]coe) ⟩
    (⌜ ⟦t⟧.pres (⟦Γ⟧.id ρ) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ τ
    ≡⟨ ap! (⟦t⟧.id ρ) ⟩
    (⟦A⟧.idᴰ (⟦t⟧ .act ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ τ
    ≡⟨ ⟦A⟧.id⁻¹∘ᴰ τ .[]coe ⟩
    τ ∎
  ⟦Id⟧ .snd ._⁻¹ᴰ {x₁ = ρ₁} {x₂ = ρ₂} {x₁₂ = ρ₁₂} {x₁ᴰ = τ} (lift refl) .lower
    rewrite ↑≡ ⟦Γ⟧.⁻¹⁻¹ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ↑≡ ⟦Γ⟧.∘id (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.∘⁻¹ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₁) =
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ 
    ⌜ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)) ⟦A⟧.∘ᴰ 
    ⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⌝
    ≡⟨ ap! (⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)
                    (⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹)) .[]coe) ⟩
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    ⌜ (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⟦A⟧.∘ᴰ ⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⌝)
    ≡⟨ ap! (⟦A⟧.∘∘ᴰ τ (⟦u⟧.pres ρ₁₂) (⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹)) .[]coe) ⟩
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    (τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⌜ ⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⌝)))
    ≡⟨ ap! (ρ₁₂ ⟦u⟧.⁻¹) ⟩
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    ⌜ τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⌝)
    ≡⟨ ap! (⟦A⟧.∘∘⁻¹ᴰ τ (⟦u⟧.pres ρ₁₂) .[]coe) ⟩
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ τ)
    ≡⟨ sym (⟦A⟧.∘∘ᴰ (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) 
                    (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) τ .[]coe) ⟩
    ((⌜ ⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ τ
    ≡⟨ ap! (ρ₁₂ ⟦t⟧.⁻¹) ⟩
    ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ τ
    ≡⟨ ⟦A⟧.⁻¹∘∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) τ .[]coe ⟩
    τ ∎
  ⟦Id⟧ .snd ._∘ᴰ_ {x₁₂ = ρ₁₂} {x₂₃ = ρ₂₃} {x₁ᴰ = τ} (lift refl) (lift refl)
    .lower 
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₂₃
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘ ρ₂₃
    rewrite ↑≡ ⟦Γ⟧.id∘ (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃)
    rewrite ↑≡ ⟦Γ⟧.⟨∘⟩⁻¹ ρ₁₂ ρ₂₃
    rewrite ↑≡ sym (⟦Γ⟧.∘∘ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂ ρ₂₃) 
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘id∘ (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) =
    -- Reflexive rewrite ↑≡s 
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    (τ ⟦A⟧.∘ᴰ ⌜ ⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) ⌝)
    ≡⟨ ap! (ρ₁₂ ⟦u⟧.∘ ρ₂₃) ⟩
    (⌜ ⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    (τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃))
    ≡⟨ ap! (⟦t⟧._∘_ ρ₁₂ ρ₂₃) ⟩
    ⌜ (⟦t⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦t⟧.pres ρ₂₃) ⟦A⟧.⁻¹ᴰ ⌝ ⟦A⟧.∘ᴰ
    (τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃))
    ≡⟨ ap! (⟦A⟧.⟨∘⟩⁻¹ᴰ (⟦t⟧.pres ρ₁₂) (⟦t⟧.pres ρ₂₃) .[]coe) ⟩
    ((⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ
    ⌜ τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) ⌝
    ≡⟨ ap! (sym (⟦A⟧.∘∘ᴰ τ (⟦u⟧.pres ρ₁₂) (⟦u⟧.pres ρ₂₃) .[]coe)) ⟩
    ((⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ
    ((τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃)
    ≡⟨ ⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) 
               ((τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) .[]coe ⟩
    (⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ 
    ((τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) ⌝
    ≡⟨ ap! (sym (⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)
                           (⟦u⟧.pres ρ₂₃) .[]coe)) ⟩
    (⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ 
    (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) ∎
  ⟦Id⟧ .snd .coeG   ρ₁₂ τ
    = tr (⟦A⟧ .fst .Relᴰ _ _) (⟦Γ⟧.⁻¹∘id∘ ρ₁₂)
      ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂))
  ⟦Id⟧ .snd .id∘ᴰ _     = coe[] refl
  ⟦Id⟧ .snd .∘idᴰ _     = coe[] refl
  ⟦Id⟧ .snd .∘∘ᴰ  _ _ _ = coe[] refl
  ⟦Id⟧ .snd .∘⁻¹ᴰ _     = coe[] refl
  ⟦Id⟧ .snd .⁻¹∘ᴰ _     = coe[] refl
  ⟦Id⟧ .snd .cohG _ _   = lift refl
  -- Literally identical to the "idᴰ" case...
  ⟦Id⟧ .snd .coe-id {x = ρ} τ 
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ =
    (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ ⟦A⟧.∘ᴰ ⌜ ⟦u⟧.pres (⟦Γ⟧.id ρ) ⌝)
    ≡⟨ ap! (⟦u⟧.id ρ) ⟩
    (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ τ ⟦A⟧.∘ᴰ ⟦A⟧.idᴰ (⟦u⟧.act ρ) ⌝
    ≡⟨ ap! (⟦A⟧.∘idᴰ τ .[]coe) ⟩
    (⌜ ⟦t⟧.pres (⟦Γ⟧.id ρ) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ τ
    ≡⟨ ap! (⟦t⟧.id ρ) ⟩
    (⟦A⟧.idᴰ (⟦t⟧ .act ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ τ
    ≡⟨ ⟦A⟧.id⁻¹∘ᴰ τ .[]coe ⟩
    τ ∎
  -- Identical to the _∘ᴰ_ case...
  ⟦Id⟧ .snd .coe-∘ ρ₁₂ ρ₂₃ τ 
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₂₃
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘ ρ₂₃
    rewrite ↑≡ ⟦Γ⟧.id∘ (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃)
    rewrite ↑≡ ⟦Γ⟧.⟨∘⟩⁻¹ ρ₁₂ ρ₂₃
    rewrite ↑≡ sym (⟦Γ⟧.∘∘ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂ ρ₂₃) 
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘id∘ (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) = 
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    (τ ⟦A⟧.∘ᴰ ⌜ ⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) ⌝)
    ≡⟨ ap! (ρ₁₂ ⟦u⟧.∘ ρ₂₃) ⟩
    (⌜ ⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    (τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃))
    ≡⟨ ap! (⟦t⟧._∘_ ρ₁₂ ρ₂₃) ⟩
    ⌜ (⟦t⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦t⟧.pres ρ₂₃) ⟦A⟧.⁻¹ᴰ ⌝ ⟦A⟧.∘ᴰ
    (τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃))
    ≡⟨ ap! (⟦A⟧.⟨∘⟩⁻¹ᴰ (⟦t⟧.pres ρ₁₂) (⟦t⟧.pres ρ₂₃) .[]coe) ⟩
    ((⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ
    ⌜ τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) ⌝
    ≡⟨ ap! (sym (⟦A⟧.∘∘ᴰ τ (⟦u⟧.pres ρ₁₂) (⟦u⟧.pres ρ₂₃) .[]coe)) ⟩
    ((⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ
    ((τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃)
    ≡⟨ ⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) 
               ((τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) .[]coe ⟩
    (⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ 
    ((τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) ⌝
    ≡⟨ ap! (sym (⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)
                         (⟦u⟧.pres ρ₂₃) .[]coe)) ⟩
    (⟦t⟧.pres ρ₂₃ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ 
    (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) ∎
  ⟦Id⟧ .snd .coh-id  τ   = coe[] refl
  ⟦Id⟧ .snd .coh-∘ _ _ _ = coe[] refl

module _ {⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧} where
  private
    module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
    module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
    module ⟦t⟧ = _⇒ᴰ_ ⟦t⟧

  ⟦refl⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Id⟧ ⟦A⟧ ⟦t⟧ ⟦t⟧)
  ⟦refl⟧ .act ρ = ⟦A⟧.idᴰ (⟦t⟧.act ρ)
  ⟦refl⟧ .pres {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ .lower
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘ ρ₁₂ =
    (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    ⌜ ⟦A⟧.idᴰ (⟦t⟧.act ρ₁) ⟦A⟧.∘ᴰ ⟦t⟧.pres ρ₁₂ ⌝
    ≡⟨ ap! (⟦A⟧.id∘ᴰ (⟦t⟧.pres ρ₁₂) .[]coe) ⟩
    (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⟦t⟧.pres ρ₁₂
    ≡⟨ ⟦A⟧.⁻¹∘ᴰ (⟦t⟧.pres ρ₁₂) .[]coe ⟩
    ⟦A⟧.idᴰ (⟦t⟧.act ρ₂) ∎
    -- = coe _ ((⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._⁻¹ᴰ (⟦t⟧ .pres ρ₁₂)))
    --                          (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd .idᴰ _) (⟦t⟧ .pres ρ₁₂)))
    --   ≡⟨ sym (exttr (⟦Γ⟧ .snd .∘∘ _ _ _) (⟦A⟧ .snd .∘∘ᴰ _ _ _) .[]coe) ⟩
    --   coe ⌜ _ ⌝ (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._⁻¹ᴰ (⟦t⟧ .pres ρ₁₂))
    --                                             (⟦A⟧ .snd .idᴰ _))
    --                             (⟦t⟧ .pres ρ₁₂))
    --   ≡⟨ ap! uip ⟩
    --   coe _ (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._⁻¹ᴰ (⟦t⟧ .pres ρ₁₂))
    --                                         (⟦A⟧ .snd .idᴰ _))
    --                         (⟦t⟧ .pres ρ₁₂))
    --   ≡⟨ ⁻¹∘id∘ᴰ (⟦A⟧ .snd) _ .[]coe ⟩
    --   ⟦A⟧ .snd .idᴰ _ ∎
  ⟦refl⟧ .id  _   = refl
  ⟦refl⟧ ._⁻¹ _   = refl
  ⟦refl⟧ ._∘_ _ _ = refl

-- TODO: Prove these substitution laws!
postulate
  ⟦Id[]T⟧ : ⟦[]T⟧ (⟦Id⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧) ⟦δ⟧ 
          ≡ ⟦Id⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧) (⟦[]⟧ ⟦t⟧ ⟦δ⟧) (⟦[]⟧ ⟦u⟧ ⟦δ⟧)

  ⟦[][]T⟧ : ⟦[]T⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧) ⟦σ⟧ ≡ ⟦[]T⟧ ⟦A⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧) 
 
 
  ⟦[][]⟧ : {⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧} {⟦δ⟧ : ⟦Sub⟧ ⟦Δ⟧ ⟦Γ⟧} {⟦σ⟧ : ⟦Sub⟧ ⟦Θ⟧ ⟦Δ⟧} 
        → ⟦[]⟧ (⟦[]⟧ ⟦t⟧ ⟦δ⟧) ⟦σ⟧ 
        ≡[ ap (⟦Tm⟧ ⟦Θ⟧) (⟦[][]T⟧ {⟦A⟧ = ⟦A⟧} {⟦δ⟧ = ⟦δ⟧} {⟦σ⟧ = ⟦σ⟧})
        ]≡ ⟦[]⟧ ⟦t⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧) 
 

-- Transport
module _ (⟦P⟧ : ⟦Ty⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧))
         (⟦d⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ (⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦t⟧)))
         (⟦p⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Id⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧)) where
  private
    module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
    module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
    module ⟦P⟧ = Grpdᴰ.Data (⟦P⟧ .snd)
    module ⟦t⟧ = _⇒ᴰ_ ⟦t⟧
    module ⟦u⟧ = _⇒ᴰ_ ⟦u⟧
    module ⟦d⟧ = _⇒ᴰ_ ⟦d⟧
    module ⟦p⟧ = _⇒ᴰ_ ⟦p⟧
  
  ⟦tr⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ (⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦u⟧))
  ⟦tr⟧ .act  ρ   = ⟦P⟧.coeG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ)
  ⟦tr⟧ .pres {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ 
      rewrite ↑≡ ⟦Γ⟧.∘id ρ₁₂
      rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
      rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₁)
      rewrite ↑≡ ⟦Γ⟧.∘⁻¹ ρ₁₂
      rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₁
      rewrite ↑≡ ⟦Γ⟧.⁻¹∘id∘ ρ₁₂
      = tr (λ □ → ⟦P⟧ .fst .Relᴰ _ _ (ρ₁₂ , □)) 
      ((⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⌜ ⟦p⟧.act ρ₂ ⌝)
      ≡⟨ ap! (sym (⟦p⟧.pres ρ₁₂ .lower)) ⟩
      (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ ⟦t⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ 
      ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)) ⌝
      ≡⟨ ap! (sym (⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₁₂) (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)
                           (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) .[]coe)) ⟩
      (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ (⟦t⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ 
      (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⌝
      ≡⟨ ap! (⟦A⟧.⟨∘⁻¹⟩∘ᴰ (⟦t⟧.pres ρ₁₂) 
                          (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) .[]coe) ⟩
      (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)
      ≡⟨ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) (⟦p⟧.act ρ₁) (⟦u⟧.pres ρ₁₂) .[]coe) ⟩
      ((⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⟦p⟧.act ρ₁) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂
      ≡⟨ ⟦A⟧.⁻¹∘∘ᴰ (⟦p⟧.act ρ₁) (⟦u⟧.pres ρ₁₂) .[]coe ⟩
      ⟦u⟧.pres ρ₁₂ ∎)
      ((⟦P⟧.cohG (⟦Γ⟧.id ρ₁ , ⟦p⟧.act ρ₁) (⟦d⟧.act ρ₁) ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ 
      (⟦d⟧.pres ρ₁₂ ⟦P⟧.∘ᴰ ⟦P⟧.cohG (⟦Γ⟧.id ρ₂ , ⟦p⟧.act ρ₂) (⟦d⟧.act ρ₂)))
  ⟦tr⟧ .id   ρ 
    rewrite ↑≡ ⟦Γ⟧.∘id (⟦Γ⟧.id ρ)
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ
    rewrite ↑≡ ⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦A⟧.idᴰ (⟦t⟧.act ρ)) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦A⟧.idᴰ (⟦u⟧.act ρ)) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦A⟧.∘idᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦u⟧.id ρ
    rewrite ↑≡ ⟦t⟧.id ρ =  
    (⟦P⟧.cohG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ) ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ
    (⌜ ⟦d⟧.pres (⟦Γ⟧.id ρ) ⌝ ⟦P⟧.∘ᴰ 
    ⟦P⟧.cohG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ))
    ≡⟨ ap! (⟦d⟧.id ρ) ⟩
    (⟦P⟧.cohG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ) ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ
    ⌜ ⟦P⟧.idᴰ (⟦d⟧.act ρ) ⟦P⟧.∘ᴰ 
    ⟦P⟧.cohG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ) ⌝
    ≡⟨ ap! (⟦P⟧.id∘ᴰ (⟦P⟧.cohG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ)) .[]coe) ⟩
    (⟦P⟧.cohG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ) ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ
    ⟦P⟧.cohG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ)
    ≡⟨ ⟦P⟧.⁻¹∘ᴰ (⟦P⟧.cohG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ)) .[]coe ⟩
    ⟦P⟧.idᴰ (⟦P⟧.coeG (⟦Γ⟧.id ρ , ⟦p⟧.act ρ) (⟦d⟧.act ρ)) ∎
  -- TODO...
  ⟦tr⟧ ._⁻¹  ρ₁₂ = {!   !}
  ⟦tr⟧ ._∘_  ρ₁₂ ρ₂₃ = {!   !}

-- The J rule
module _ 
        (let Id-t-vz = ⟦Id⟧ (⟦[]T⟧ ⟦A⟧ (⟦wk⟧ ⟦A⟧)) (⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧)) 
                                                   (⟦vz⟧ ⟦A⟧))
        (let id,t = ⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦t⟧)
        (let id,u = ⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦u⟧)
        (⟦P⟧ : ⟦Ty⟧ (⟦▷⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) Id-t-vz)) 
        (⟦d⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ 
                        (⟦,⟧ Id-t-vz id,t
                           (tr (⟦Tm⟧ ⟦Γ⟧) (sym (⟦Id[]T⟧ 
                            {⟦t⟧ = (⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧))}
                            {⟦u⟧ =  (⟦vz⟧ ⟦A⟧)}
                            {⟦δ⟧ = id,t})) 
                            ⟦refl⟧))))
         (⟦p⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Id⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧))
         where
        
  private
    module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
    module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
    module ⟦P⟧ = Grpdᴰ.Data (⟦P⟧ .snd)
    module ⟦t⟧ = _⇒ᴰ_ ⟦t⟧
    module ⟦u⟧ = _⇒ᴰ_ ⟦u⟧
    module ⟦d⟧ = _⇒ᴰ_ ⟦d⟧
    module ⟦p⟧ = _⇒ᴰ_ ⟦p⟧
    module ⟦Γ▷A⟧ = Grpd.Data (⟦▷⟧ ⟦Γ⟧ ⟦A⟧ .snd)

  ⟦J⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ 
                 (⟦,⟧ Id-t-vz (⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦u⟧) 
                      (tr (⟦Tm⟧ ⟦Γ⟧) 
                      (sym  (⟦Id[]T⟧ {⟦t⟧ = ⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧)} 
                                     {⟦u⟧ =  (⟦vz⟧ ⟦A⟧)} 
                                     {⟦δ⟧ = id,u}))
                      ⟦p⟧)))
  ⟦J⟧ .act  ρ 
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ) .[]coe
    = ⟦P⟧.coeG ((⟦Γ⟧.id ρ , ⟦p⟧.act ρ) , lift 
      ((⌜ ⟦t⟧.pres (⟦Γ⟧.id ρ) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⟦p⟧.act ρ
      ≡⟨ ap! (⟦t⟧.id ρ) ⟩ 
      ⌜ ⟦A⟧.idᴰ (⟦t⟧.act ρ) ⟦A⟧.⁻¹ᴰ ⌝ ⟦A⟧.∘ᴰ ⟦p⟧.act ρ
      ≡⟨ ap! (⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ) .[]coe) ⟩ 
      ⟦A⟧.idᴰ (⟦t⟧.act ρ) ⟦A⟧.∘ᴰ ⟦p⟧.act ρ
      ≡⟨⟩ 
      ⟦p⟧.act ρ ∎)) 
      (⟦d⟧.act ρ)
  ⟦J⟧ .pres {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ 
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₁
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₂
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₁)
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₂)
    rewrite ↑≡ ⟦Γ⟧.∘id ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.∘⁻¹ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘id∘ ρ₁₂
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ₁) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ₂) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ₁) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ₂) .[]coe
    rewrite ↑≡ ⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ₁) .[]coe
    rewrite ↑≡ ⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ₂) .[]coe
    rewrite ↑≡ ⟦t⟧.id ρ₁
    rewrite ↑≡ ⟦t⟧.id ρ₂
    rewrite ↑≡ 
      ((⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⌜ ⟦p⟧.act ρ₂ ⌝)
      ≡⟨ ap! (sym (⟦p⟧.pres ρ₁₂ .lower)) ⟩
      (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ ⟦t⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ 
      ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)) ⌝
      ≡⟨ ap! (sym (⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₁₂) (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)
                          (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) .[]coe)) ⟩
      (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ (⟦t⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ 
      (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⌝
      ≡⟨ ap! (⟦A⟧.⟨∘⁻¹⟩∘ᴰ (⟦t⟧.pres ρ₁₂) 
                          (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) .[]coe) ⟩
      (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)
      ≡⟨ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) (⟦p⟧.act ρ₁) (⟦u⟧.pres ρ₁₂) .[]coe) ⟩
      ((⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⟦p⟧.act ρ₁) ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂
      ≡⟨ ⟦A⟧.⁻¹∘∘ᴰ (⟦p⟧.act ρ₁) (⟦u⟧.pres ρ₁₂) .[]coe ⟩
      ⟦u⟧.pres ρ₁₂ ∎) =
      (⟦P⟧.cohG ((⟦Γ⟧.id ρ₁ , ⟦p⟧.act ρ₁) , lift refl) (⟦d⟧.act ρ₁) ⟦P⟧.⁻¹ᴰ)
      ⟦P⟧.∘ᴰ (⟦d⟧.pres ρ₁₂ 
      ⟦P⟧.∘ᴰ ⟦P⟧.cohG ((⟦Γ⟧.id ρ₂ , ⟦p⟧.act ρ₂) , lift refl) (⟦d⟧.act ρ₂))
  ⟦J⟧ .id   = {!   !}
  ⟦J⟧ ._⁻¹  = {!   !}
  ⟦J⟧ ._∘_  = {!   !}
 