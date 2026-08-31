{-# OPTIONS --prop --rewriting #-}

open import Utils.Prop hiding (Σ; Σᴾ; fst; snd) 
  renaming (_,_ to _×,_; tt to true; ff to false)

open import RwNbE2.Syntax
open import RwNbE2.Nf.Nf

module RwNbE2.Rewriting where

data RewEnv   (Δ : Ctx Ξ) 
          : ∀ (Γ : Ctx Ξ) 
              (wsᴿ : Nesᴿ (lenSig Ξ) (len Δ))
              (usᴿ : Nesᴿ (lenSig Ξ) (len Γ))
              (tsᴿ : Nfsᴿ (lenSig Ξ) (len Γ)) 
              {δ} (δᵀʰ~ : Thin~ Δ Γ δ)
          → Set where
  εᴿᵉʷ    : RewEnv Δ • wsᴿ εᴿ εᴿ εᵀʰ~
  _,ᴿᵉʷ   : RewEnv Δ Γ wsᴿ usᴿ tsᴿ (wkᵀʰ~ ⨾ᵀʰ~ δᵀʰ~)
          → RewEnv Δ (Γ ▷ A) wsᴿ (usᴿ [ wkᴿ ]Nesᴿ) (tsᴿ [ wkᴿ ]Nfsᴿ) δᵀʰ~
  _,~ᴿᵉʷ_ : RewEnv Δ Γ wsᴿ usᴿ tsᴿ (wk~ᵀʰ~ ⨾ᵀʰ~ δᵀʰ~)
          → t₁ᴿ ∶ Neᴿ (lenSig Ξ) (len Γ)
          × t₂ᴿ ∶ Nfᴿ (lenSig Ξ) (len Γ)
          × t₁ᴾ ∶ NePred Γ A t₁ t₁ᴿ
          × t₂ᴾ ∶ NfPred Γ A t₂ t₂ᴿ
          × t₁[]ᴾᴺᵉ ∶ PreNe Δ (A [ δ ]T) wsᴿ (t₁ [ δ ])
          × t₂[]ᴺᶠ  ∶ FONf Δ (A [ δ ]T) wsᴿ (t₂ [ δ ])
          × Lift ( (t₁ᴿ [ δᵀʰ~ .raw ]Neᴿ ≡ t₁[]ᴾᴺᵉ .raw)
                 ∧ (t₂ᴿ [ δᵀʰ~ .raw ]Nfᴿ ≡ t₂[]ᴺᶠ .raw))  
          → RewEnv Δ (Γ ▷ t₁ ~ t₂) wsᴿ (usᴿ ,ᴿ t₁ᴿ) (tsᴿ ,ᴿ t₂ᴿ) δᵀʰ~


FullRewEnv : (Γ : Ctx Ξ) 
             (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (tsᴿ : Nfsᴿ (lenSig Ξ) (len Γ))
           → Set
FullRewEnv Γ usᴿ tsᴿ = RewEnv Γ Γ usᴿ usᴿ tsᴿ idᵀʰ~

-- TODO
postulate
  rw : PreNe Γ A usᴿ t → FONf Γ A usᴿ t ＋ Ne Γ A usᴿ t