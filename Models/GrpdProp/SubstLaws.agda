{-# OPTIONS --smart-with --prop --rewriting --show-irrelevant #-}

open import Utils.Prop
open import Utils.MacroProp

open import Models.GrpdProp.Grpd
open import Models.GrpdProp.Motives
open import Models.GrpdProp.Subst

-- Substitution calculus
module Models.GrpdProp.SubstLaws where

⟦[id]T⟧ : ⟦[]T⟧ ⟦A⟧ ⟦id⟧ ≡ ⟦A⟧
⟦[id]T⟧ = refl

module _ {⟦A⟧ : ⟦Ty⟧ ⟦Γ⟧} {⟦δ⟧ : ⟦Sub⟧ ⟦Δ⟧ ⟦Γ⟧} {⟦σ⟧ : ⟦Sub⟧ ⟦Θ⟧ ⟦Δ⟧}
         (let module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
              module ⟦Δ⟧ = Grpd.Data (⟦Δ⟧ .snd)
              module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
              module ⟦δ⟧ = _⇒_ ⟦δ⟧
              module ⟦σ⟧ = _⇒_ ⟦σ⟧)
         where
  ⟦[][]T⟧' : Grpdᴰ≡ ⟦Θ⟧ (⟦[]T⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧) ⟦σ⟧)
                        (⟦[]T⟧ ⟦A⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧))
  ⟦[][]T⟧' .Obᴰ≡  ρ                 = refl
  ⟦[][]T⟧' .Homᴰ≡ ρ₁₂ refl[] refl[] = refl

  ⟦[][]T⟧' .idᴰ≡ {x = ρ} {x₁ᴰ = τ₁} {x₂ᴰ = τ₂} τ₁₂
    rewrite ↑≡ ⟦δ⟧.pres-id (⟦σ⟧.act ρ)
    rewrite ↑≡ ⟦σ⟧.pres-id ρ
    rewrite ↑≡ τ₁₂ .[]coe
    = refl[]
  ⟦[][]T⟧' .⁻¹ᴰ≡ {x = ρ₁} {y = ρ₂} τ₁₂ υ₁₂ {xy = ρ₁₂}
                 {xy₁ᴰ = τυ₁} {xy₂ᴰ = τυ₂} τυ₁₂
    rewrite ↑≡ ⟦δ⟧.pres-⁻¹ (⟦σ⟧.pres ρ₁₂)
    rewrite ↑≡ ⟦σ⟧.pres-⁻¹ ρ₁₂
    rewrite ↑≡ τ₁₂ .[]coe
    rewrite ↑≡ υ₁₂ .[]coe
    rewrite ↑≡ []coe {p = refl} τυ₁₂
    = refl[]
  ⟦[][]T⟧' .∘ᴰ≡ {x = ρ₁} {y = ρ₂} {z = ρ₃} τ₁₂ υ₁₂ _
    = {!   !}
  ⟦[][]T⟧' .coeG≡
    = {!   !}
  ⟦[][]T⟧' .cohG≡
    = {!   !}

  ⟦[][]T⟧ : ⟦[]T⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧) ⟦σ⟧ ≡ ⟦[]T⟧ ⟦A⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧)
  ⟦[][]T⟧ = apd₂ _,_ refl (coe[] {!!})

⟦wk,⟧ : {⟦t⟧ : ⟦Tm⟧ ⟦Δ⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧)}
      → ⟦⨾⟧ (⟦wk⟧ ⟦A⟧) (⟦,⟧ ⟦A⟧ ⟦δ⟧ ⟦t⟧) ≡ ⟦δ⟧
⟦wk,⟧ = refl

⟦[id]⟧ : {⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧} → ⟦[]⟧ ⟦t⟧ ⟦id⟧ ≡ ⟦t⟧
⟦[id]⟧ = refl

⟦[][]⟧ : {⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧} {⟦δ⟧ : ⟦Sub⟧ ⟦Δ⟧ ⟦Γ⟧} {⟦σ⟧ : ⟦Sub⟧ ⟦Θ⟧ ⟦Δ⟧}
       → ⟦[]⟧ (⟦[]⟧ ⟦t⟧ ⟦δ⟧) ⟦σ⟧
       ≡[ ap (⟦Tm⟧ ⟦Θ⟧) (⟦[][]T⟧ {⟦A⟧ = ⟦A⟧} {⟦δ⟧ = ⟦δ⟧} {⟦σ⟧ = ⟦σ⟧})
       ]≡ ⟦[]⟧ ⟦t⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧)
⟦[][]⟧ = coe[] {!!}

⟦vz,⟧  : ⟦[]⟧ (⟦vz⟧ ⟦A⟧) (⟦,⟧ ⟦A⟧ ⟦δ⟧ ⟦u⟧) ≡ ⟦u⟧
⟦vz,⟧ = refl
