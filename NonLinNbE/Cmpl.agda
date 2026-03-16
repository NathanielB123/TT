{-# OPTIONS --rewriting --prop --show-irrelevant #-}

open import Utils renaming (_,_ to _Σ,_)
open import Utils.Prop
open import Utils.WithK

open import NonLinNbE.SyntaxEta
open import NonLinNbE.Nf

-- Completeness of NbE
module NonLinNbE.Cmpl where

~≡     : t₁ ~ t₂ → t₁ ≡ t₂
cmplNe : NeCmpl Γ A₁ t₁ tᴿ → NeCmpl Γ A₂ t₂ tᴿ
       → Σ (A₁ ≡ A₂) (λ A≡ → t₁ ≡[ ap (Tm Γ) A≡ ]≡ t₂)
cmplNf : NfCmpl Γ A₁ t₁ tᴿ → NfCmpl Γ A₂ t₂ tᴿ
       → (A≡ : A₁ ≡ A₂) → t₁ ≡[ ap (Tm Γ) A≡ ]≡ t₂

~≡ rfl~          = {!   !}
~≡ (sym~ t~)     = {!   !}
~≡ (t~₁ ∙~ t~₂)  = {!   !}
~≡ (ap~ f t~)    = ap f (~≡ t~)
~≡ (ne~ tC₁ tC₂) = sym coe-K ∙ cmplNe tC₁ tC₂ .snd .[]coe

cmplNe (coe~ t~ tC₁) tC₂ .fst 
  = cmplNe tC₁ tC₂ .fst 
cmplNe (coe~ t~ tC₁) tC₂ .snd .[]coe
  = ap (coe _) (sym (~≡ t~)) ∙ cmplNe tC₁ tC₂ .snd .[]coe
cmplNe tC₁ (coe~ t~ tC₂) = {!   !}
cmplNe (varC xC₁) (varC xC₂) = {!   !}
-- Here we really need the type normal forms...
-- And critically the type normal forms need to be structurally smaller than
-- the |appC| args.
-- So we need to normalise types inside eval...
cmplNe (appC tC₁ uC₁) (appC tC₂ uC₂) 
  = {!   !}
cmplNe (-neC tC₁ uC₁ p) (-neC tC₂ uC₂ q) 
  = {!   !}
cmplNe (ne-C tC₁ uC₁) (ne-C tC₂ uC₂) 
  = {!   !}
cmplNe (ze-C tC₁) (ze-C tC₂) 
  = refl Σ, coe[] (ap (λ □ → ze - su □) 
                  (cmplNf tC₁ tC₂ refl .[]coe))
