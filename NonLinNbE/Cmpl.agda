{-# OPTIONS --rewriting --prop --show-irrelevant #-}

open import Utils renaming (_,_ to _Σ,_)
open import Utils.Prop
open import Utils.WithK

open import NonLinNbE.SyntaxEta
open import NonLinNbE.Nf

-- Completeness of NbE
module NonLinNbE.Cmpl where

cmplVar : VarCmpl Γ A₁ t₁ xᴿ → VarCmpl Γ A₂ t₂ xᴿ 
        → Σ (A₁ ≡ A₂) (λ A≡ → t₁ ≡[ ap (Tm Γ) A≡ ]≡ t₂)

cmplVar vzC       vzC       = refl Σ, refl[]
cmplVar (vsC tC₁) (vsC tC₂) .fst = ap (_[ p ]T) (cmplVar tC₁ tC₂ .fst)
cmplVar (vsC {t = t₁} tC₁) (vsC {t = t₂} tC₂) .snd .[]coe = 
  coe _ (t₁ [ p ])
  ≡⟨ coe≡-K (refl {x = t₁ [ p ]}) ⟩
  coe _ (t₁ [ p ])
  ≡⟨ apdd₂ (Tm _) (λ _ → _[ p ]) (cmplVar tC₁ tC₂ .fst) .[]coe  ⟩
  transp (Tm _) (cmplVar tC₁ tC₂ .fst) t₁ [ p ]
  ≡⟨ ap (_[ p ]) (cmplVar tC₁ tC₂ .snd .[]coe) ⟩
  t₂ [ p ] ∎

~≡       : t₁ ~ t₂ → t₁ ≡ t₂
cmplNe   : NeCmpl Γ A₁ t₁ tᴿ → NeCmpl Γ A₂ t₂ tᴿ
         → Σ (A₁ ≡ A₂) (λ A≡ → t₁ ≡[ ap (Tm Γ) A≡ ]≡ t₂)
cmplNf   : NfCmpl Γ A₁ t₁ tᴿ → NfCmpl Γ A₂ t₂ tᴿ
         → (A≡ : A₁ ≡ A₂) → t₁ ≡[ ap (Tm Γ) A≡ ]≡ t₂
cmplℤ    : ℤCmpl Γ t₁ tᴿ → ℤCmpl Γ t₂ tᴿ
         → t₁ ≡ t₂
cmplℤPar : ℤParCmpl Γ t₁ tᴿ → ℤParCmpl Γ t₂ tᴿ
         → t₁ ≡ t₂

~≡ rfl~          = refl
~≡ (sym~ t~)     = sym (~≡ t~)
~≡ (t~₁ ∙~ t~₂)  = ~≡ t~₁ ∙ ~≡ t~₂
~≡ (ap~ f t~)    = ap f (~≡ t~)
~≡ (ne~ tC₁ tC₂) = []coe-K (cmplNe tC₁ tC₂ .snd)

cmplNe (coe~ t~ tC₁) tC₂ .fst 
  = cmplNe tC₁ tC₂ .fst 
cmplNe (coe~ t~ tC₁) tC₂ .snd .[]coe
  = ap (coe _) (sym (~≡ t~)) ∙ cmplNe tC₁ tC₂ .snd .[]coe
cmplNe tC₁ (coe~ t~ tC₂) .fst 
  = cmplNe tC₁ tC₂ .fst 
cmplNe tC₁ (coe~ t~ tC₂) .snd .[]coe
  = reix[] (cmplNe tC₁ tC₂ .snd) .[]coe ∙ ~≡ t~
cmplNe (varC xC₁) (varC xC₂) = {!   !}
-- Here we really need the type normal forms...
-- And critically the type normal forms need to be structurally smaller than
-- the |appC| args.
-- So we need to normalise types inside eval...
cmplNe (appC tC₁ uC₁) (appC tC₂ uC₂) 
  = {!   !}
cmplNe (-neC tC₁ uC₁ p) (-neC tC₂ uC₂ q) 
  = refl Σ, coe[] (ap₂ _-_ (cmplNf tC₁ tC₂ refl .[]coe) 
                           ([]coe-K (cmplNe uC₁ uC₂ .snd)))
cmplNe (ne-C tC₁ uC₁) (ne-C tC₂ uC₂) 
  = refl Σ, coe[] (ap₂ (λ □₁ □₂ → □₁ - su □₂) 
                       ([]coe-K (cmplNe tC₁ tC₂ .snd)) 
                       (cmplNf uC₁ uC₂ refl .[]coe))
cmplNe (ze-C tC₁) (ze-C tC₂) 
  = refl Σ, coe[] (ap (λ □ → ze - su □) 
                  (cmplNf tC₁ tC₂ refl .[]coe))
 
cmplNf (coe~ t~ tC₁) tC₂ refl .[]coe 
  = sym (~≡ t~) ∙ cmplNf tC₁ tC₂ refl .[]coe
cmplNf tC₁ (coe~ t~ tC₂) refl .[]coe
  = cmplNf tC₁ tC₂ refl .[]coe ∙ ~≡ t~
cmplNf (lamC tC₁)  (lamC tC₂)  A≡ = {!   !}
cmplNf (valℤC tC₁) (valℤC tC₂) A≡ = {!   !}

-- Impossible cases
cmplNf (lamC  tC₁) (valℤC tC₂) A≡ = {!   !}
cmplNf (valℤC tC₁) (lamC tC₂)  A≡ = {!   !}