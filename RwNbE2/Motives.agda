{-# OPTIONS --prop --rewriting #-}

open import Utils.Prop
open import RwNbE2.Syntax
open import RwNbE2.Nf.Nf
open import RwNbE2.Rewriting

module RwNbE2.Motives where

-- TODO
postulate
  ⇓ᵂᵏ  : Sub {Φ} {Ψ} Δ Γ → SigWk Φ Ψ
  ⇓ˢᵘᵇ : (δ : Sub Δ Γ) → Sub Δ (Γ [ ⇓ᵂᵏ δ ]C)

variable
  Γᴿᵉʷ Δᴿᵉʷ Θᴿᵉʷ : RewEnv _ _ _ _ _ _

record CtxNS (Ψ : Sig) (Γ : Ctx Ψ) : Set₁ where
  field
    Env : (usᴿ : Nesᴿ (lenSig Φ) (len Δ))
          (Δᴿᵉʷ : FullRewEnv Δ usᴿ tsᴿ)
          (δ : Sub Δ Γ)
        → Set
    -- TODO: Env thinning and functor laws

    quote* : (ρ : Env usᴿ Δᴿᵉʷ δ)
           → Nfs Δ (Γ [ ⇓ᵂᵏ δ ]C) usᴿ (⇓ˢᵘᵇ δ)
    -- TODO: Naturality of quote*

module _ (Γᴹ : CtxNS Ψ Γ) (A : Ty Γ) 
         (let module Γᴹ = CtxNS Γᴹ)
         where
          
  record TyNS  : Set₁ where
    field
      Val : (ρ : Γᴹ.Env usᴿ Δᴿᵉʷ δ)
            (t : Tm Δ (A [ δ ]T))
          → Set
      -- TODO: Val thinning and functor lawsy

      tyNf : (ρ : Γᴹ.Env usᴿ Δᴿᵉʷ δ)
           → TyNf Δ usᴿ (A [ δ ]T)
      -- TODO: Naturality of tyNf

      unquoteᴺᶠ : (ρ : Γᴹ.Env usᴿ Δᴿᵉʷ δ)
                  (tᴺᶠ : FONf Δ (A [ δ ]T) usᴿ t)
                → tyOfᴿ (tᴺᶠ .raw) ≡ tyNf ρ .raw 
                → Val ρ t
      -- TODO: Naturality of unquoteᴺᶠ

      unquoteᴺᵉ : (ρ : Γᴹ.Env usᴿ Δᴿᵉʷ δ)
                  (tᴺᵉ : Ne Δ (A [ δ ]T) usᴿ t)
                → Val ρ t
      -- TODO: Naturality of unquoteᴺᵉ

      quoteⱽ : (ρ : Γᴹ.Env usᴿ Δᴿᵉʷ δ)
               (τ : Val ρ t)
              → Nf Δ (A [ δ ]T) usᴿ t
      -- TODO: Naturality of quoteⱽ

      -- Quotation is injective on first order normal forms
      -- i.e. the normalisation structure for which we cannot prove this
      -- during construction of the model is that of function types, and
      -- quotation at function type always produces abstractions
      quote-inj : (ρ : Γᴹ.Env usᴿ Δᴿᵉʷ δ)
                  (τ₁ τ₂ : Val ρ t)
                  (tᴺᶠ : FONf Δ (A [ δ ]T) usᴿ t)
                → quoteⱽ ρ τ₁ .raw ≡ tᴺᶠ .raw 
                → τ₁ ≡ τ₂

    try-unquoteᴺᶠ : (ρ : Γᴹ.Env usᴿ Δᴿᵉʷ δ)
                 (tᴺᶠ : FONf Δ (A [ δ ]T) usᴿ t)
               → Val ρ t
    try-unquoteᴺᶠ ρ tᴺᶠ with tyOfᴿ (tᴺᶠ .raw) ≡TyNfᴿ? tyNf ρ .raw
    ... | yes p = unquoteᴺᶠ ρ tᴺᶠ p
    ... | no  e = unquoteᴺᵉ ρ (!ᴺᵉ (tyNf ρ) (forgetFO tᴺᶠ) e)

    unquoteᴾᴺᵉ : (ρ : Γᴹ.Env usᴿ Δᴿᵉʷ δ)
                 (tᴾᴺᵉ : PreNe Δ (A [ δ ]T) usᴿ t)
               → Val ρ t
    unquoteᴾᴺᵉ ρ tᴾᴺᵉ with rw tᴾᴺᵉ
    ... | inl tᴺᶠ = try-unquoteᴺᶠ ρ tᴺᶠ
    ... | inr tᴺᵉ = unquoteᴺᵉ ρ tᴺᵉ

module _ (Δᴹ : CtxNS Φ Δ) (Γᴹ : CtxNS Ψ Γ) (δ : Sub Δ Γ) 
         (let module Δᴹ = CtxNS Δᴹ) (let module Γᴹ = CtxNS Γᴹ)
         where
  record TmsNS : Set where
    field
      eval* : (ρ : Δᴹ.Env usᴿ Θᴿᵉʷ σ)
            → Γᴹ.Env usᴿ Θᴿᵉʷ (δ ⨾ σ)
      -- TODO: Naturality of |eval*|

module _ (Γᴹ : CtxNS Ψ Γ) (Aᴹ : TyNS Γᴹ A)
         (t : Tm Γ A)
         (let module Γᴹ = CtxNS Γᴹ) (let module Aᴹ = TyNS Aᴹ)
         where
  record TmNS : Set where
    field
      eval : (ρ : Γᴹ.Env {Δ = Δ} usᴿ Δᴿᵉʷ δ)
             (t : Tm Γ A)
           → Aᴹ.Val ρ (t [ δ ])
    -- TODO: Naturality of |eval|
