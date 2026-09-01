{-# OPTIONS --rewriting --prop #-}

open import Utils.Prop renaming (_,_ to _×,_) hiding (tt; ff)

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
  constructor var
  field
    raw  : Varᴿ (len Γ)
    pred : VarPred Γ A t raw

record Def (Ξ : Sig) (Γ : Ctx Ξ) {A t₁ t₂} (B : Ty Γ) (eq : Tm Γ (Id A t₁ t₂))
           (u : Tm Γ B) 
         : Set where
  constructor def
  field
    raw  : Defᴿ (lenSig Ξ)
    pred : DefPred Ξ Γ B eq u raw

record PreNe (Γ : Ctx Ξ) (A : Ty Γ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) 
             (t : Tm Γ A)
     : Set where
  constructor prene
  field
    raw  : Neᴿ (lenSig Ξ) (len Γ)
    pred : NePred Γ A t raw
    stab : StablePreNe usᴿ raw

record Ne (Γ : Ctx Ξ) (A : Ty Γ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (t : Tm Γ A)
        : Set where
  constructor ne
  field
    raw  : Neᴿ (lenSig Ξ) (len Γ)
    pred : NePred Γ A t raw
    stab : StableNe usᴿ raw

record Nf (Γ : Ctx Ξ) (A : Ty Γ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (t : Tm Γ A)
        : Set where
  constructor nf
  field
    raw  : Nfᴿ (lenSig Ξ) (len Γ)
    pred : NfPred Γ A t raw
    stab : StableNf usᴿ raw

record FONf (Γ : Ctx Ξ) (A : Ty Γ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (t : Tm Γ A)
          : Set where
  constructor fonf
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
  constructor nfs
  field
    raw  : Nfsᴿ (lenSig Ξ) (len Δ)
    pred : NfsPred Δ Γ ts raw
    stab : StableNfs usᴿ raw

record TyNf (Γ : Ctx Ξ) (usᴿ : Nesᴿ (lenSig Ξ) (len Γ)) (A : Ty Γ) : Set where
  constructor tynf
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

tyOfᴺᶠ : Nf Γ A usᴿ t → TyNf Γ usᴿ A
tyOfᴺᶠ tᴺᶠ .raw    = tyOfᴿ (tᴺᶠ .raw)
tyOfᴺᶠ tᴺᶠ .pred   = tyOfᴾ (tᴺᶠ .pred)
tyOfᴺᶠ tᴺᶠ .stab f = tyOfᴼᶜᶜ (tᴺᶠ .stab f)

εᴺᶠ : Nfs Δ • usᴿ εᵀᵐˢ
εᴺᶠ .raw    = εᴿ
εᴺᶠ .pred   = εᴾ
εᴺᶠ .stab f = εᴼᶜᶜ

_,ᴺᶠ_ : Nfs Δ Γ usᴿ ts → Nf Δ (A [ ⇑ᵀᵐˢ ts ]T) usᴿ t
      → Nfs Δ (Γ ▷ A) usᴿ (ts ,ᵀᵐˢ t)
(tsᴺᶠ ,ᴺᶠ tᴺᶠ) .raw    = tsᴺᶠ .raw ,ᴿ tᴺᶠ .raw
(tsᴺᶠ ,ᴺᶠ tᴺᶠ) .pred   = tsᴺᶠ .pred ,ᴾ tᴺᶠ .pred
(tsᴺᶠ ,ᴺᶠ tᴺᶠ) .stab f = tsᴺᶠ .stab f ,ᴼᶜᶜ tᴺᶠ .stab f

!ᴺᵉ : (A₁ᴺᶠ A₂ᴺᶠ : TyNf Γ usᴿ A) (tᴺᶠ : Nf Γ A usᴿ t) 
    → (A₁ᴺᶠ .raw ≡ A₂ᴺᶠ .raw → 𝟘) 
    → Ne Γ A usᴿ t 
!ᴺᵉ A₁ᴺᶠ A₂ᴺᶠ tᴺᶠ e .raw    = !ᴿ (A₁ᴺᶠ .raw) (A₂ᴺᶠ .raw) (tᴺᶠ .raw)
!ᴺᵉ A₁ᴺᶠ A₂ᴺᶠ tᴺᶠ e .pred   = !ᴾ (A₁ᴺᶠ .pred) (A₂ᴺᶠ .pred) (tᴺᶠ .pred) e
!ᴺᵉ A₁ᴺᶠ A₂ᴺᶠ tᴺᶠ e .stab f = !ᴼᶜᶜ (A₁ᴺᶠ .stab f) (A₂ᴺᶠ .stab f) (tᴺᶠ .stab f)

𝔹ᴺᶠ : TyNf Γ usᴿ 𝔹
𝔹ᴺᶠ .raw    = 𝔹ᴿ
𝔹ᴺᶠ .pred   = 𝔹ᴾ
𝔹ᴺᶠ .stab f = 𝔹ᴼᶜᶜ

ttᴺᶠ : Nf Γ 𝔹 usᴿ tt
ttᴺᶠ .raw    = ttᴿ
ttᴺᶠ .pred   = ttᴾ
ttᴺᶠ .stab f = ttᴼᶜᶜ

ffᴺᶠ : Nf Γ 𝔹 usᴿ ff
ffᴺᶠ .raw    = ffᴿ
ffᴺᶠ .pred   = ffᴾ
ffᴺᶠ .stab f = ffᴼᶜᶜ

ne𝔹ᴺᶠ : Ne Γ 𝔹 usᴿ t → Nf Γ 𝔹 usᴿ t
ne𝔹ᴺᶠ tᴺᵉ .raw    = ne𝔹ᴿ (tᴺᵉ .raw)
ne𝔹ᴺᶠ tᴺᵉ .pred   = ne𝔹ᴾ (tᴺᵉ .pred)
ne𝔹ᴺᶠ tᴺᵉ .stab f = ne𝔹ᴼᶜᶜ (tᴺᵉ .stab f)

module _ {t₁ᴺᶠ t₂ᴺᶠ : Nf Γ A usᴿ t} where
  postulate
    nf≡ : t₁ᴺᶠ .raw ≡ t₂ᴺᶠ .raw → t₁ᴺᶠ ≡ t₂ᴺᶠ

module _ {t₁ᴺᵉ t₂ᴺᵉ : Ne Γ A usᴿ t} where
  postulate
    ne≡ : t₁ᴺᵉ .raw ≡ t₂ᴺᵉ .raw → t₁ᴺᵉ ≡ t₂ᴺᵉ

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
