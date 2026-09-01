{-# OPTIONS --rewriting --prop #-}

open import Utils.Prop renaming (_,_ to _×,_)

open import RwNbE2.Syntax

module RwNbE2.Nf.Nf where

open import RwNbE2.Nf.FirstOrder
  public
open import RwNbE2.Nf.Occurs
  public
open import RwNbE2.Nf.Pred
  public
open import RwNbE2.Nf.Raw
  public
open import RwNbE2.Nf.PredInj
  public

record Var (Γ : Ctx Ξ) (A : Ty Γ) (t : Tm Γ A) : Set where
  field
    raw  : Varᴿ (len Γ)
    pred : VarPred Γ A t raw

record Def (Ξ : Sig) (Γ : Ctx Ξ) {A t₁ t₂} (B : Ty Γ) (eq : Tm Γ (Id A t₁ t₂))
           (u : Tm Γ B) 
         : Set where
  field
    raw  : Defᴿ (lenSig Ξ)
    pred : DefPred Ξ Γ B eq u raw

record PreNe (Γ : Ctx Ξ) (A : Ty Γ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) 
             (t : Tm Γ A)
     : Set where
  field
    raw  : Neᴿ (lenSig Ξ) (len Γ)
    pred : NePred Γ A t raw
    stab : StablePreNe usᴿ raw

record Ne (Γ : Ctx Ξ) (A : Ty Γ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (t : Tm Γ A)
        : Set where
  field
    raw  : Neᴿ (lenSig Ξ) (len Γ)
    pred : NePred Γ A t raw
    stab : StableNe usᴿ raw

record Nf (Γ : Ctx Ξ) (A : Ty Γ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (t : Tm Γ A)
        : Set where
  field
    raw  : Nfᴿ (lenSig Ξ) (len Γ)
    pred : NfPred Γ A t raw
    stab : StableNf usᴿ raw

record FONf (Γ : Ctx Ξ) (A : Ty Γ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (t : Tm Γ A)
          : Set where
  field
    raw  : Nfᴿ (lenSig Ξ) (len Γ)
    pred : NfPred Γ A t raw
    stab : StableNf usᴿ raw
    fo   : FirstOrder raw
  
  forgetFO : Nf Γ A usᴿ t
  forgetFO = record {raw = raw; pred = pred; stab = stab}

record Nfs (Δ : Ctx Ξ) (Γ : Ctx Ξ) (usᴿ : Nesᴿ (lenSig Ξ) (len Δ)) 
           (ts : Tms Δ Γ)
         : Set where
  field
    raw  : Nfsᴿ (lenSig Ξ) (len Δ)
    pred : NfsPred Δ Γ ts raw
    stab : StableNfs usᴿ raw

record TyNf (Γ : Ctx Ξ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (A : Ty Γ) : Set where
  field
    raw  : TyNfᴿ (lenSig Ξ) (len Γ)
    pred : TyNfPred Γ A raw
    stab : StableTyNf usᴿ raw

open Var public
open Def public
open PreNe public
open Ne public
open Nf public
open FONf public
open Nfs public
open TyNf public

-- TODO: All constructors for normal forms

εᴺᶠ : Nfs Δ • usᴿ εᵀᵐˢ
εᴺᶠ .raw    = εᴿ
εᴺᶠ .pred   = εᴾ
εᴺᶠ .stab f = εᴼᶜᶜ

_,ᴺᶠ_ : Nfs Δ Γ usᴿ ts → Nf Δ (A [ ⇑ᵀᵐˢ ts ]T) usᴿ t
      → Nfs Δ (Γ ▷ A) usᴿ (ts ,ᵀᵐˢ t)
(tsᴺᶠ ,ᴺᶠ tᴺᶠ) .raw    = tsᴺᶠ .raw ,ᴿ tᴺᶠ .raw
(tsᴺᶠ ,ᴺᶠ tᴺᶠ) .pred   = tsᴺᶠ .pred ,ᴾ tᴺᶠ .pred
(tsᴺᶠ ,ᴺᶠ tᴺᶠ) .stab f = tsᴺᶠ .stab f ,ᴼᶜᶜ tᴺᶠ .stab f

!ᴺᵉ : (Aᴺᶠ : TyNf Γ usᴿ A) (tᴺᶠ : Nf Γ A usᴿ t) 
    → (tyOfᴿ (tᴺᶠ .raw) ≡ Aᴺᶠ .raw → 𝟘) 
    → Ne Γ A usᴿ t 
!ᴺᵉ Aᴺᶠ tᴺᶠ e .raw    = !ᴿ (Aᴺᶠ .raw) (tᴺᶠ .raw)
!ᴺᵉ Aᴺᶠ tᴺᶠ e .pred   = !ᴾ (Aᴺᶠ .pred) (tᴺᶠ .pred) e
!ᴺᵉ Aᴺᶠ tᴺᶠ e .stab f = !ᴼᶜᶜ (Aᴺᶠ .stab f) (tᴺᶠ .stab f)

record Thin (Δ Γ : Ctx Ξ) (δ : Sub Δ Γ) : Set where
  field
    raw  : Thinᴿ (len Δ) (len Γ)
    pred : ThinPred Δ Γ δ raw
open Thin public

record Thin~ (Δ Γ : Ctx Ξ) (δ : Sub Δ Γ) : Set where
  field
    raw  : Thinᴿ (len Δ) (len Γ)
    pred : ThinPred~ Δ Γ δ raw
open Thin~ public

variable
  δᵀʰ~ : Thin~ Δ Γ δ

-- TODO
postulate
  εᵀʰ~ : Thin~ Δ • (ε idᵂᵏ)

  _⁺ᵀʰ~ : Thin~ Δ Γ δ → Thin~ (Δ ▷ A) Γ (δ ⨾ wk)

  _⁺~ᵀʰ~ : Thin~ Δ Γ δ → Thin~ (Δ ▷ t₁ ~ t₂) Γ (δ ⨾ wk~)


  _⨾ᵀʰ~_ : Thin~ Δ Γ δ → Thin~ Θ Δ σ → Thin~ Θ Γ (δ ⨾ σ)

  idᵀʰ~ : Thin~ Γ Γ id

  wkᵀʰ~ : Thin~ (Γ ▷ A) Γ wk

  wk~ᵀʰ~ : Thin~ (Γ ▷ t₁ ~ t₂) Γ wk~
