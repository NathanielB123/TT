{-# OPTIONS --rewriting --prop --show-irrelevant --smart-with #-}

open import Utils.Prop hiding (Σ; tt; ff) renaming (_,_ to _×,_)
  hiding (fst; snd)
open import RwNbE2.Syntax
open import RwNbE2.Nf.Nf
open import RwNbE2.Rewriting
open import RwNbE2.Motives
open import RwNbE2.Model.Subst

open import RwNbE2.Cheat

module RwNbE2.Model.Id where

data IdVal   (Γ : Ctx Ξ) {A} (usᴿ : Nesᴿ (defs Ξ) (vars Γ))
             (Aⱽ : Tm Γ A → Set)
         : ∀ {t₁ t₂} (τ₁ : Aⱽ t₁) (τ₂ : Aⱽ t₂)
             (eq : Tm Γ (Id A t₁ t₂))
         → Set where
  rflⱽ  : ∀ {τ : Aⱽ t} → IdVal Γ usᴿ Aⱽ τ τ rfl
  neIdⱽ : ∀ {τ₁ : Aⱽ t₁} {τ₂ : Aⱽ t₂}
        → Ne Γ (Id A t₁ t₂) usᴿ eq
        → IdVal Γ usᴿ Aⱽ τ₁ τ₂  eq

rflℱⱽ : {Aⱽ : Tm Γ A → Set} {τ₁ : Aⱽ t₁} {τ₂ : Aⱽ t₂}
      → (t₁₂ : t₁ ≡ t₂)
      → (rflℱ t₁₂ ≡ eq)
      → τ₁ ≡[ ap Aⱽ t₁₂ ]≡ τ₂
      → IdVal Γ usᴿ Aⱽ τ₁ τ₂ eq
rflℱⱽ  t₁₂ rfl≡ τ₁₂
  with refl ← ↑≡ t₁₂
  with refl ← ↑≡ rfl≡
  with refl ← ↑≡ τ₁₂ .[]coe
  = rflⱽ


module _ (Aᴹ : Tyᴹ Γᴹ A) (t₁ᴹ : Tmᴹ Γᴹ Aᴹ t₁) (t₂ᴹ : Tmᴹ Γᴹ Aᴹ t₂)
         (let module Γᴹ = CtxNS Γᴹ
              module Aᴹ = TyNS Aᴹ
              module t₁ᴹ = TmNS t₁ᴹ
              module t₂ᴹ = TmNS t₂ᴹ) where

  Idᴹ : Tyᴹ Γᴹ (Id A t₁ t₂)
  Idᴹ .Val {Δ = Δ} {usᴿ = usᴿ} ρ t =
    IdVal Δ usᴿ (Aᴹ.Val ρ) (t₁ᴹ.eval ρ) (t₂ᴹ.eval ρ) t
  Idᴹ ._[_]ⱽ = todo
  Idᴹ .tyNf ρ =
    Idᴺᶠ (Aᴹ.tyNf ρ) (Aᴹ.quoteⱽ ρ (t₁ᴹ.eval ρ))
                     (Aᴹ.quoteⱽ ρ (t₂ᴹ.eval ρ))
  Idᴹ .unquoteᴺᶠℱ {δ = δ} ρ A≡
    (fonf (rflᴿ tᴿ) (rflᴾ tᴾ) tStab (rflFO tFO)) tyNf≡
    using t₁₂ᴺᶠ ← sym (Idᴿ-inj₂ tyNf≡) ∙ Idᴿ-inj₃ tyNf≡
    using _ ∧, (coe[] t₁₂)
      ← injNfPred (Aᴹ.quoteⱽ ρ (t₁ᴹ.eval ρ) .pred)
                  (tr (NfPred _ _ _) (sym t₁₂ᴺᶠ)
                      (Aᴹ.quoteⱽ ρ (t₂ᴹ.eval ρ) .pred))
    = rflℱⱽ t₁₂ todoℙ
            (Aᴹ.quote-injℱ ρ t₁₂ (t₁ᴹ.eval ρ) (t₂ᴹ.eval ρ) t₁₂ᴺᶠ
                           (tr FirstOrder (Idᴿ-inj₂ tyNf≡) tFO))
  Idᴹ .unquoteᴺᶠℱ ρ A≡
    (fonf (neIdᴿ t₁ᴿ t₂ᴿ uᴿ) (neIdᴾ t₁ᴾ t₂ᴾ uᴾ) tStab tFO) tyNf≡
    rewrite ↑≡ sym A≡
    = neIdⱽ (ne uᴿ uᴾ {!   !})
  Idᴹ .unquoteᴺᵉ = {!   !}
  Idᴹ .quoteⱽ = {!   !}
  Idᴹ .quote-injℱ = {!   !}
  Idᴹ .[id]ⱽ = {!   !}
  Idᴹ .[][]ⱽ = {!   !}
  Idᴹ .tyNf[] = {!   !}
  Idᴹ .unquoteᴺᶠ[] = {!   !}
  Idᴹ .unquoteᴺᵉ[] = {!   !}
  Idᴹ .quote[] = {!   !}

rflℱᴹ : t₁ᴹ ≡[ ap (Tmᴹ Γᴹ Aᴹ) t₁₂ ]≡ t₂ᴹ
      → Tmᴹ Γᴹ (Idᴹ Aᴹ t₁ᴹ t₂ᴹ) (rflℱ t₁₂)

module _ {Γᴹ : Ctxᴹ Ψ Γ} {Aᴹ : Tyᴹ Γᴹ A}
         {t₁ᴹ : Tmᴹ Γᴹ Aᴹ t₁}
         {t₂ᴹ : Tmᴹ Γᴹ Aᴹ t₂}
         {Bᴹ : Tyᴹ Γᴹ B}
         {eqᴹ : Tmᴹ Γᴹ (Idᴹ Aᴹ t₁ᴹ t₂ᴹ) eq}
         {u}
         {uᴹ : Tmᴹ ((Γᴹ ▷ᴹ t₁ᴹ ~ t₂ᴹ)
                        ▷ᴹ (eqᴹ [ wk~ᴹ ]ᴹ) ~ {!rflℱᴹ _!})
                   (Bᴹ [ wk~ᴹ ⨾ᴹ wk~ᴹ ]Tᴹ) u}
         where

  callᴹ : Tmᴹ {Ψ def Γ to B reflect eq begin u end}
              (Γᴹ [ defᵂᵏ ]Cᴹ)
              (Bᴹ [ ⇑ᵂᵏᴹ defᵂᵏ ]Tᴹ)
              call
