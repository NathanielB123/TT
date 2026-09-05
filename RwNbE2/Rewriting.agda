{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Utils.Prop hiding (Σ; Σᴾ; fst; snd)
  renaming (_,_ to _×,_; tt to true; ff to false)

open import RwNbE2.Syntax
open import RwNbE2.Nf.Nf
open import RwNbE2.Niceness

module RwNbE2.Rewriting where

data RewEnv   (Δ : Ctx Ξ)
          : ∀ (Γ : Ctx Ξ)
              (wsᴿ : Nesᴿ (defs Ξ) (vars Δ))
              (usᴿ : Nesᴿ (defs Ξ) (vars Γ))
              (tsᴿ : Nfsᴿ (defs Ξ) (vars Γ))
              {vs} (δᵀʰ~ : Thin~ Δ Γ vs)
          → Set where
  εᴿᵉʷ    : RewEnv Δ • wsᴿ εᴿ εᴿ δᵀʰ~
  _,ᴿᵉʷ   : RewEnv Δ Γ wsᴿ usᴿ tsᴿ (wkᵀʰ~ ⨾ᵀʰ~ δᵀʰ~)
          → RewEnv Δ (Γ ▷ A) wsᴿ (usᴿ [ wkᴿ ]Nesᴿ) (tsᴿ [ wkᴿ ]Nfsᴿ) δᵀʰ~
  _,~ᴿᵉʷ_ : {δᵀʰ~ : Thin~ Δ (Γ ▷ t₁ ~ t₂) (vs ,~ᵀᵐˢ t₁₂)}
          → RewEnv Δ Γ wsᴿ usᴿ tsᴿ (wk~ᵀʰ~ ⨾ᵀʰ~ δᵀʰ~)
          → ((t₁ᴿ ×, t₂ᴿ ×, _)
            : t₁ᴿ ∶ Neᴿ (defs Ξ) (vars Γ)
            × t₂ᴿ ∶ Nfᴿ (defs Ξ) (vars Γ)
            × t₁ᴾ ∶ NePred Γ A t₁ t₁ᴿ
            × t₂ᴾ ∶ NfPred Γ A t₂ t₂ᴿ
            × t₁[]ᴾᴺᵉ ∶ PreNe Δ (A [ ⇑ᵀᵐˢ vs ]T) wsᴿ (t₁ [ ⇑ᵀᵐˢ vs ])
            × t₂[]ᴺᶠ  ∶ FONf Δ (A [ ⇑ᵀᵐˢ vs ]T) wsᴿ (t₂ [ ⇑ᵀᵐˢ vs ])
            × Lift ( (t₁ᴿ [ δᵀʰ~ .raw ]Neᴿ ≡ t₁[]ᴾᴺᵉ .raw)
                   ∧ (t₂ᴿ [ δᵀʰ~ .raw ]Nfᴿ ≡ t₂[]ᴺᶠ .raw)))
          → RewEnv Δ (Γ ▷ t₁ ~ t₂) wsᴿ (usᴿ ,ᴿ t₁ᴿ) (tsᴿ ,ᴿ t₂ᴿ) δᵀʰ~


FullRewEnv : (Γ : Ctx Ξ)
             (usᴿ : Nesᴿ (defs Ξ) (vars Γ)) (tsᴿ : Nfsᴿ (defs Ξ) (vars Γ))
           → Set
FullRewEnv Γ usᴿ tsᴿ = RewEnv Γ Γ usᴿ usᴿ tsᴿ idᵀʰ~

variable
  Γᴿᵉʷ  Δᴿᵉʷ Θᴿᵉʷ : RewEnv _ _ _ _ _ _

-- TODO
postulate
  _[_]ᴿᵉʷ : (Γᴿᵉʷ : FullRewEnv Γ usᴿ tsᴿ) (δᵀʰ : Thin Δ Γ vs)
          → FullRewEnv Δ (usᴿ [ δᵀʰ .raw ]Nesᴿ) (tsᴿ [ δᵀʰ .raw ]Nfsᴿ)

  [id]ᴿᵉʷ : Γᴿᵉʷ [ idᵀʰ ]ᴿᵉʷ ≡S Γᴿᵉʷ
  {-# REWRITE [id]ᴿᵉʷ #-}

  [][]ᴿᵉʷ : Γᴿᵉʷ [ δᵀʰ ]ᴿᵉʷ [ σᵀʰ ]ᴿᵉʷ ≡S Γᴿᵉʷ [ δᵀʰ ⨾ᵀʰ σᵀʰ ]ᴿᵉʷ
  {-# REWRITE [][]ᴿᵉʷ #-}

  _[_]ᴿᵉʷ~ : (Δᴿᵉʷ : RewEnv Δ Γ wsᴿ usᴿ tsᴿ δᵀʰ~)
             (σᵀʰ~ : Thin~ Θ Δ vs)
           → RewEnv Θ Γ (wsᴿ [ σᵀʰ~ .raw ]Nesᴿ) usᴿ tsᴿ (δᵀʰ~ ⨾ᵀʰ~ σᵀʰ~)

  exposeRew : (Δᴿᵉʷ : RewEnv {Ξ} Δ Γ wsᴿ usᴿ tsᴿ δᵀʰ~)
              (wᴿ : Neᴿ (defs Ξ) (vars Δ))
            → ¬OccursNes wᴿ (usᴿ [ δᵀʰ~ .raw ]Nesᴿ)
            → ¬OccursNfs wᴿ (tsᴿ [ δᵀʰ~ .raw ]Nfsᴿ)
            → RewEnv Δ Γ (wsᴿ ,ᴿ wᴿ) usᴿ tsᴿ δᵀʰ~

  exposeFONf : (tᴺᶠ : FONf Γ A usᴿ t) → ¬OccursNf uᴿ (tᴺᶠ .raw)
            → FONf Γ A (usᴿ ,ᴿ uᴿ) t

  exposeSelfNe : (tᴺᵉ : Ne Γ A usᴿ t) → ¬! (tᴺᵉ .raw)
              → PreNe Γ A (usᴿ ,ᴿ tᴺᵉ .raw) t

buildRew : NiceCtx Γ usᴿ tsᴿ → FullRewEnv Γ usᴿ tsᴿ
buildRew •ᴺ         = εᴿᵉʷ
buildRew (Γᴺ ▷ᴺ)    = buildRew Γᴺ [ wkᵀʰ ]ᴿᵉʷ
buildRew (Γᴺ ▷~ᴺ (t₁ᴺᵉ ×, t₂ᴺᶠ ×, t₂ᴼᶜᶜ ×, usᴼᶜᶜ ×, tsᴼᶜᶜ ×, ¬e))
  =
  _,~ᴿᵉʷ_ {t₁₂ = ez~}
  ((exposeRew (buildRew Γᴺ) (t₁ᴺᵉ .raw) usᴼᶜᶜ tsᴼᶜᶜ) [ wk~ᵀʰ~ ]ᴿᵉʷ~)
  (t₁ᴺᵉ .raw ×, t₂ᴺᶠ .raw ×, t₁ᴺᵉ .pred ×, t₂ᴺᶠ .pred
  ×, (exposeSelfNe t₁ᴺᵉ ¬e [ wk~ᵀʰ~ ]PreNe)
  ×, (exposeFONf t₂ᴺᶠ t₂ᴼᶜᶜ [ wk~ᵀʰ~ ]FONf)
  ×, lift ({!!} ∧, {!!}))

-- Rewriting
rw-ind : (Δᴿᵉʷ : RewEnv Δ Γ wsᴿ usᴿ tsᴿ δᵀʰ~)
         (tᴾᴺᵉ : PreNe Δ A wsᴿ t)
       → FONf Δ A wsᴿ t
       ＋ (Faulty (usᴿ [ δᵀʰ~ .raw ]Nesᴿ) (tᴾᴺᵉ .raw) → 𝟘)
rw-ind εᴿᵉʷ tᴾᴺᵉ           = inr λ ()
rw-ind (Δᴿᵉʷ ,ᴿᵉʷ) tᴾᴺᵉ    with rw-ind Δᴿᵉʷ tᴾᴺᵉ
... | inl tᴺᶠ   = inl tᴺᶠ
... | inr tDisj = inr λ f → tDisj f
rw-ind (_,~ᴿᵉʷ_ {t₁ = u₁} {t₂ = u₂} {vs = vs} {t₁₂ = u₁₂}
                Δᴿᵉʷ (u₁ᴿ ×, u₂ᴿ ×, _ ×, _ ×, u₁ᴾᴺᵉ ×, u₂ᴺᶠ
                     ×, lift (raw-eq₁ ∧, raw-eq₂))) tᴾᴺᵉ
  with rw-ind Δᴿᵉʷ tᴾᴺᵉ
... | inl tᴺᶠ = inl tᴺᶠ
... | inr tDisj
  with u₁ᴾᴺᵉ .raw ≡Neᴿ? tᴾᴺᵉ .raw
... | yes eq
  with A≡ ∧, t≡ ← injNePred (tᴾᴺᵉ .pred) (tr (NePred _ _ _) eq (u₁ᴾᴺᵉ .pred))
  with refl ← ↑≡ A≡
  with refl ← ↑≡ t≡ .[]coe
  = inl (tr (FONf _ _ _)
            (sym (ap (_[ _,~_ {t₁ = u₁} {t₂ = u₂} (⇑ᵀᵐˢ vs) u₁₂ ]) ez~)) u₂ᴺᶠ)
... | no neq
  with refl ← ↑≡ raw-eq₁
  = inr λ where fz     → neq refl
                (fs f) → tDisj f

rw : (Γᴿᵉʷ : FullRewEnv Γ usᴿ tsᴿ)
   → PreNe Γ A usᴿ t → FONf Γ A usᴿ t ＋ Ne Γ A usᴿ t
rw Γᴿᵉʷ tᴾᴺᵉ with rw-ind Γᴿᵉʷ tᴾᴺᵉ
... | inl tᴺᶠ   = inl tᴺᶠ
... | inr tDisj = inr (ne (tᴾᴺᵉ .raw) (tᴾᴺᵉ .pred)
                      λ f → neᴼᶜᶜ (λ where eq → tDisj (tr (Faulty _) eq f))
                                  (tᴾᴺᵉ .stab f))
