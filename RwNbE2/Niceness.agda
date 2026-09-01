{-# OPTIONS --prop --rewriting #-}

open import Utils.Prop hiding (Σ; Σᴾ; fst; snd) 
  renaming (_,_ to _×,_; tt to true; ff to false)

open import RwNbE2.Syntax
open import RwNbE2.Nf.Nf

module RwNbE2.Niceness where

-- Left-hand sides may not be exceptions
-- data Is! : Neᴿ l n → Set where
--   Is! 

data NiceCtx {Ξ} : (Γ : Ctx Ξ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) 
                   (tsᴿ : Nfsᴿ (lenSig Ξ) (len Γ))
                 → Set where
  •ᴺ    : NiceCtx • εᴿ εᴿ
  _▷ᴺ_  : NiceCtx Γ usᴿ tsᴿ 
        → NiceCtx (Γ ▷ A) (usᴿ [ wkᴿ ]Nesᴿ) (tsᴿ [ wkᴿ ]Nfsᴿ)
  _▷~ᴺ_ : NiceCtx Γ usᴿ tsᴿ
        → ((t₁ᴺᵉ ×, t₂ᴺᶠ ×, _) 
          : (t₁ᴺᵉ  ∶ Ne Γ A usᴿ t₁
          × t₂ᴺᶠ  ∶ Nf Γ A usᴿ t₂
          × t₂ᴼᶜᶜ ∶ ¬OccursNf (t₁ᴺᵉ .raw) (t₂ᴺᶠ .raw)
          × usᴼᶜᶜ ∶ ¬OccursFaults (t₁ᴺᵉ .raw) usᴿ
          × tsᴼᶜᶜ ∶ ¬OccursNfs (t₁ᴺᵉ .raw) tsᴿ
          × (∀ {A₁ᴺᶠ A₂ᴺᶠ tᴺᶠ} → t₁ᴺᵉ .raw ≡ !ᴿ A₁ᴺᶠ A₂ᴺᶠ tᴺᶠ → 𝟘)))
        → NiceCtx (Γ ▷ t₁ ~ t₂) 
                  (usᴿ ,ᴿ t₁ᴺᵉ .raw) 
                  (tsᴿ ,ᴿ t₂ᴺᶠ .raw)
