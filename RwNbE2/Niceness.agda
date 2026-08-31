{-# OPTIONS --prop --rewriting #-}

open import Utils.Prop hiding (Σ; Σᴾ; fst; snd) 
  renaming (_,_ to _×,_; tt to true; ff to false)

open import RwNbE2.Syntax
open import RwNbE2.Nf.Nf

module RwNbE2.Niceness where

data NiceCtx {Ξ} : (Γ : Ctx Ξ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) 
                   (tsᴿ : Nfsᴿ (lenSig Ξ) (len Γ))
                 → Set where
  •ᴺ    : NiceCtx • εᴿ εᴿ
  _▷ᴺ_  : NiceCtx Γ usᴿ tsᴿ 
        → NiceCtx (Γ ▷ A) (usᴿ [ wkᴿ ]Nesᴿ) (tsᴿ [ wkᴿ ]Nfsᴿ)
  _▷~ᴺ_ : NiceCtx Γ usᴿ tsᴿ
        → ((Aᴺᶠ ×, t₁ᴺᵉ ×, t₂ᴺᶠ ×, _) 
          : (Aᴺᶠ  ∶ TyNf Γ usᴿ A
          × t₁ᴺᵉ  ∶ Ne Γ A Aᴿ usᴿ t₁
          × t₂ᴺᶠ  ∶ Nf Γ A Aᴿ usᴿ t₂
          × Aᴼᶜᶜ  ∶ ¬OccursTyNf (Aᴺᶠ .raw) (t₁ᴺᵉ .raw) (Aᴺᶠ .raw)
          × t₂ᴼᶜᶜ ∶ ¬OccursNf (Aᴺᶠ .raw) (t₁ᴺᵉ .raw) (Aᴺᶠ .raw) (t₂ᴺᶠ .raw)
          × usᴼᶜᶜ ∶ ¬OccursFaults (Aᴺᶠ .raw) (t₁ᴺᵉ .raw) usᴿ
          ×         ¬OccursNfs (Aᴺᶠ .raw) (t₁ᴺᵉ .raw) tsᴿ))
        → NiceCtx (Γ ▷ t₁ ~ t₂) 
                  (usᴿ ,ᴿ (Aᴺᶠ .raw ×, t₁ᴺᵉ .raw)) 
                  (tsᴿ ,ᴿ (Aᴺᶠ .raw ×, t₂ᴺᶠ .raw))
