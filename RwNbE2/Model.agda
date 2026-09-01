{-# OPTIONS --rewriting --prop #-}

open import Utils.Prop renaming (_,_ to _×,_)
open import RwNbE2.Syntax
open import RwNbE2.SyntaxExtras
open import RwNbE2.Motives
open import RwNbE2.Nf.Nf

-- Normalisation model
module RwNbE2.Model where

•ᴹ : Ctxᴹ Ψ •
•ᴹ .Env usᴿ Δᴿᵉʷ δ = 𝟙

•ᴹ .quote* ⟨⟩ = tr (Nfs _ _ _) (sym •ηᵀᵐˢ) εᴺᶠ

module _ (Γᴹ : Ctxᴹ Ψ Γ) (Aᴹ : Tyᴹ Γᴹ A) 
         (let module Γᴹ = CtxNS Γᴹ
              module Aᴹ = TyNS Aᴹ)
         where
  _▷ᴹ_ : CtxNS Ψ (Γ ▷ A)
  _▷ᴹ_ .Env usᴿ Δᴿᵉʷ δ  = ρ ∶ Γᴹ.Env usᴿ Δᴿᵉʷ (π₁ δ) 
                        × Aᴹ.Val ρ (π₂ δ)

  _▷ᴹ_ .quote* (ρ ×, τ) 
    = Γᴹ.quote* ρ ,ᴺᶠ Aᴹ.quoteⱽ ρ τ

module _ (Γᴹ : Ctxᴹ Ψ Γ) (ψ : SigWk Φ Ψ) 
         (let module Γᴹ = CtxNS Γᴹ) where
  _[_]Cᴹ : Ctxᴹ Φ (Γ [ ψ ]C)
  _[_]Cᴹ .Env  usᴿ Δᴿᵉʷ δ  = Γᴹ.Env usᴿ Δᴿᵉʷ (⇑ᵂᵏ ψ ⨾ δ)
  _[_]Cᴹ .quote* ρ = Γᴹ.quote* ρ

module _ {Δᴹ : Ctxᴹ Φ Δ} {Γᴹ : Ctxᴹ Ψ Γ} 
         (ψ : SigWk Φ Ψ) {ts} (tsᴹ : Tmsᴹ Δᴹ (Γᴹ [ ψ ]Cᴹ) ts)
         (let module tsᴹ = SubNS tsᴹ)
         where
  _∥ᴹ_ : Subᴹ Δᴹ Γᴹ (ψ ∥ ts)
  _∥ᴹ_ .eval* ρ = tsᴹ.eval* ρ

module _ {Γᴹ : Ctxᴹ Ψ Γ} {Δᴹ : Ctxᴹ Ψ Δ} {Θᴹ : Ctxᴹ Φ Θ}
         (tsᴹ : Tmsᴹ Δᴹ Γᴹ ts) (δᴹ : Subᴹ Θᴹ Δᴹ δ)
         where
  _[_]*ᴹ : Tmsᴹ Θᴹ (Γᴹ [ δ .⇓ᵂᵏ ]Cᴹ) (ts [ δ ]*)
  _[_]*ᴹ .eval* ρ = tsᴹ .eval* (eval* δᴹ ρ)
