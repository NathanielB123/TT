{-# OPTIONS --rewriting --prop --show-irrelevant --smart-with #-}

open import Utils.Prop hiding (Σ; tt; ff) renaming (_,_ to _×,_)
  hiding (fst; snd)
open import RwNbE2.Syntax
open import RwNbE2.Nf.Nf
open import RwNbE2.Rewriting
open import RwNbE2.Motives

open import RwNbE2.Cheat

module RwNbE2.Model.Subst where

•ᴹ : Ctxᴹ Ψ •
•ᴹ .Env usᴿ Δᴿᵉʷ δ = 𝟙

•ᴹ .quote* ⟨⟩ = tr (Nfs _ _ _) (sym •ηᵀᵐˢ) εᴺᶠ

•ᴹ ._[_]ᴱ    = todo
•ᴹ .[id]ᴱ    = todoℙ
•ᴹ .[][]ᴱ    = todoℙ
•ᴹ .quote*[] = todoℙ

module _ (Γᴹ : Ctxᴹ Ψ Γ) (Aᴹ : Tyᴹ Γᴹ A)
         (let module Γᴹ = CtxNS Γᴹ
              module Aᴹ = TyNS Aᴹ)
         where
  _▷ᴹ_ : CtxNS Ψ (Γ ▷ A)
  _▷ᴹ_ .Env usᴿ Δᴿᵉʷ δ  = ρ ∶ Γᴹ.Env usᴿ Δᴿᵉʷ (π₁ δ)
                        × Aᴹ.Val ρ (π₂ δ)

  _▷ᴹ_ .quote* (ρ ×, τ)
    = Γᴹ.quote* ρ ,ᴺᶠ Aᴹ.quoteⱽ ρ τ

  _▷ᴹ_ ._[_]ᴱ    = todo
  _▷ᴹ_ .[id]ᴱ    = todoℙ
  _▷ᴹ_ .[][]ᴱ    = todoℙ
  _▷ᴹ_ .quote*[] = todoℙ

module _ (Γᴹ : Ctxᴹ Ψ Γ) {Aᴹ : Tyᴹ Γᴹ A}
         (t₁ᴹ : Tmᴹ Γᴹ Aᴹ t₁) (t₂ᴹ : Tmᴹ Γᴹ Aᴹ t₂)
         (let module Γᴹ = CtxNS Γᴹ
              module Aᴹ = TyNS Aᴹ
              module t₁ᴹ = TmNS t₁ᴹ
              module t₂ᴹ = TmNS t₂ᴹ)
         where
  _▷ᴹ_~_ : CtxNS Ψ (Γ ▷ t₁ ~ t₂)
  _▷ᴹ_~_ .Env usᴿ Δᴿᵉʷ δ  = ρ ∶ Γᴹ.Env usᴿ Δᴿᵉʷ (π₁~ δ)
                          × Lift (t₁ᴹ.eval ρ
                          ≡[ ap (Aᴹ.Val ρ) (π₂~ δ)
                               ]≡ t₂ᴹ.eval ρ)
  _▷ᴹ_~_ .quote* {δ = δ} (ρ ×, τ₁₂)
    = _,~ᴺᶠ {t₁₂ = π₂~ δ} (Γᴹ.quote* ρ)
  _▷ᴹ_~_ ._[_]ᴱ    = todo
  _▷ᴹ_~_ .[id]ᴱ    = todoℙ
  _▷ᴹ_~_ .[][]ᴱ    = todoℙ
  _▷ᴹ_~_ .quote*[] = todoℙ


module _ (Γᴹ : Ctxᴹ Ψ Γ) (ψ : SigWk Φ Ψ)
         (let module Γᴹ = CtxNS Γᴹ) where
  _[_]Cᴹ : Ctxᴹ Φ (Γ [ ψ ]C)
  _[_]Cᴹ .Env  usᴿ Δᴿᵉʷ δ  = Γᴹ.Env usᴿ Δᴿᵉʷ (⇑ᵂᵏ ψ ⨾ δ)
  _[_]Cᴹ .quote* ρ = Γᴹ.quote* ρ

  _[_]Cᴹ ._[_]ᴱ ρ σᵀʰ = ρ Γᴹ.[ σᵀʰ ]ᴱ

  _[_]Cᴹ .[id]ᴱ    = todoℙ
  _[_]Cᴹ .[][]ᴱ    = todoℙ
  _[_]Cᴹ .quote*[] = todoℙ

module _ (Aᴹ : TyNS Γᴹ A) (δᴹ : SubNS Δᴹ Γᴹ δ)
         (let module Γᴹ = CtxNS Γᴹ
              module Δᴹ = CtxNS Δᴹ
              module Aᴹ = TyNS Aᴹ
              module δᴹ = SubNS δᴹ)
         where
  _[_]Tᴹ : TyNS Δᴹ (A [ δ ]T)
  _[_]Tᴹ .Val ρ t = Aᴹ.Val (δᴹ.eval* ρ) t
  _[_]Tᴹ .tyNf ρ = Aᴹ.tyNf (δᴹ.eval* ρ)

  _[_]Tᴹ .quoteⱽ    ρ τ = Aᴹ.quoteⱽ (δᴹ.eval* ρ) τ
  _[_]Tᴹ .unquoteᴺᵉ ρ tᴺᵉ = Aᴹ.unquoteᴺᵉ (δᴹ.eval* ρ) tᴺᵉ
  _[_]Tᴹ .unquoteᴺᶠℱ ρ A≡ tᴺᶠ eq = Aᴹ.unquoteᴺᶠℱ (δᴹ.eval* ρ) A≡ tᴺᶠ eq

  _[_]Tᴹ ._[_]ⱽ       = todo
  _[_]Tᴹ .quote-injℱ  = todoℙ
  _[_]Tᴹ .[id]ⱽ       = todoℙ
  _[_]Tᴹ .[][]ⱽ       = todoℙ
  _[_]Tᴹ .tyNf[]      = todoℙ
  _[_]Tᴹ .unquoteᴺᶠ[] = todoℙ
  _[_]Tᴹ .unquoteᴺᵉ[] = todoℙ
  _[_]Tᴹ .quote[]     = todoℙ

module _ (tᴹ : TmNS Γᴹ Aᴹ t) (δᴹ : SubNS Δᴹ Γᴹ δ)
         (let module tᴹ = TmNS tᴹ
              module δᴹ = SubNS δᴹ)
         where
  _[_]ᴹ : TmNS Δᴹ (Aᴹ [ δᴹ ]Tᴹ) (t [ δ ])
  _[_]ᴹ .eval   ρ = tᴹ.eval (δᴹ.eval* ρ)
  _[_]ᴹ .eval[] = todoℙ

module _ {t₁ᴹ : TmNS Γᴹ Aᴹ t₁} {t₂ᴹ : TmNS Γᴹ Aᴹ t₂}
         (δᴹ : SubNS Δᴹ Γᴹ δ)
         (t₁₂ᴹ : t₁ᴹ [ δᴹ ]ᴹ  ≡[ ap (TmNS Δᴹ (Aᴹ [ δᴹ ]Tᴹ)) t₁₂ ]≡ t₂ᴹ [ δᴹ ]ᴹ)
         (let module t₁ᴹ = TmNS t₁ᴹ
              module t₂ᴹ = TmNS t₂ᴹ
              module δᴹ = SubNS δᴹ)
          where
  _,~ᴹ_ : SubNS Δᴹ (Γᴹ ▷ᴹ t₁ᴹ ~ t₂ᴹ) (δ ,~ t₁₂)
  _,~ᴹ_ .eval* {σ = σ} ρ
    -- This rewrite is non-confluent due to the global rewrite rule!
    -- |t₁ [ δ ] ↝ t₂ [ δ ]| does not fire on |t₁ [ δ ⨾ σ ]|!
    rewrite ↑≡ t₁₂
    rewrite ↑≡ π₂~ {t₁ = t₁} {t₂ = t₂} ((δ ,~ t₁₂) ⨾ σ)
    = δᴹ.eval* ρ ×, lift (coe[] (ap (λ □ → eval □ ρ) (t₁₂ᴹ .[]coe)))
  _,~ᴹ_ .eval*[] = todoℙ


module _ (ψ : SigWk Φ Ψ) {ts} (tsᴹ : Tmsᴹ Δᴹ (Γᴹ [ ψ ]Cᴹ) ts)
         (let module tsᴹ = SubNS tsᴹ)
         where
  _⇑ᴹ_ : Subᴹ Δᴹ Γᴹ (ψ ⇑ ts)
  _⇑ᴹ_ .eval* ρ = tsᴹ.eval* ρ

  _⇑ᴹ_ .eval*[] = todoℙ

module _ {Γᴹ : Ctxᴹ Ψ Γ}
         (let module Γᴹ = CtxNS Γᴹ)
         where
  idᴹ : Subᴹ Γᴹ Γᴹ id
  idᴹ .eval* ρ = ρ
  idᴹ .eval*[] = todoℙ

module _ (tsᴹ : Tmsᴹ Δᴹ Γᴹ ts) (δᴹ : Subᴹ Θᴹ Δᴹ δ)
         where
  _[_]*ᴹ : Tmsᴹ Θᴹ (Γᴹ [ δ .⇓ᵂᵏ ]Cᴹ) (ts [ δ ]*)
  _[_]*ᴹ .eval* ρ = tsᴹ .eval* (eval* δᴹ ρ)

  _[_]*ᴹ .eval*[] = todoℙ

module _ (δᴹ : Subᴹ Δᴹ Γᴹ δ)
         (let module δᴹ = SubNS δᴹ) where
  ⇓ᵀᵐˢᴹ : Tmsᴹ Δᴹ (Γᴹ [ ⇓ᵂᵏ δ ]Cᴹ) (⇓ᵀᵐˢ δ)
  ⇓ᵀᵐˢᴹ .eval* ρ = δᴹ.eval* ρ
  ⇓ᵀᵐˢᴹ .eval*[] = todoℙ

module _ (tsᴹ : Tmsᴹ Δᴹ (Γᴹ ▷ᴹ Aᴹ) ts)
         (let module tsᴹ = SubNS tsᴹ) where
  π₁ᵀᵐˢᴹ : Tmsᴹ Δᴹ Γᴹ (π₁ᵀᵐˢ ts)
  π₁ᵀᵐˢᴹ .eval* ρ using ξ ×, _ ← tsᴹ.eval* ρ = ξ
  π₁ᵀᵐˢᴹ .eval*[] = todoℙ

module _ (tsᴹ : Tmsᴹ Δᴹ (Γᴹ ▷ᴹ t₁ᴹ ~ t₂ᴹ) ts)
         (let module tsᴹ = SubNS tsᴹ) where
  π₁~ᵀᵐˢᴹ : Tmsᴹ Δᴹ Γᴹ (π₁~ᵀᵐˢ ts)
  π₁~ᵀᵐˢᴹ .eval* ρ using ξ ×, _ ← tsᴹ.eval* ρ = ξ
  π₁~ᵀᵐˢᴹ .eval*[] = todoℙ

⇑ᵂᵏᴹ : (ψ : SigWk Φ Ψ) →  Subᴹ (Γᴹ [ ψ ]Cᴹ) Γᴹ (⇑ᵂᵏ ψ)
⇑ᵂᵏᴹ ψ = ψ ⇑ᴹ idᴹ

module _ (δᴹ : Subᴹ Δᴹ (Γᴹ ▷ᴹ Aᴹ) δ) where
  π₁ᴹ : Subᴹ Δᴹ Γᴹ (π₁ δ)
  π₁ᴹ = ⇓ᵂᵏ δ ⇑ᴹ π₁ᵀᵐˢᴹ {Aᴹ = Aᴹ [ ⇑ᵂᵏᴹ (⇓ᵂᵏ δ) ]Tᴹ} (⇓ᵀᵐˢᴹ δᴹ)

module _ (δᴹ : Subᴹ Δᴹ (Γᴹ ▷ᴹ t₁ᴹ ~ t₂ᴹ) δ) where
  π₁~ᴹ : Subᴹ Δᴹ Γᴹ (π₁~ δ)
  π₁~ᴹ = ⇓ᵂᵏ δ ⇑ᴹ π₁~ᵀᵐˢᴹ {t₁ᴹ = t₁ᴹ [ ⇑ᵂᵏᴹ (⇓ᵂᵏ δ) ]ᴹ}
                          {t₂ᴹ = t₂ᴹ [ ⇑ᵂᵏᴹ (⇓ᵂᵏ δ) ]ᴹ} (⇓ᵀᵐˢᴹ δᴹ)

module _ {Aᴹ : Tyᴹ Γᴹ A} where
  wkᴹ : Subᴹ (Γᴹ ▷ᴹ Aᴹ) Γᴹ wk
  wkᴹ = π₁ᴹ {Aᴹ = Aᴹ} idᴹ

module _ {t₁ᴹ : Tmᴹ Γᴹ Aᴹ t₁} {t₂ᴹ : Tmᴹ Γᴹ Aᴹ t₂} where
  wk~ᴹ : Subᴹ (Γᴹ ▷ᴹ t₁ᴹ ~ t₂ᴹ) Γᴹ wk~
  wk~ᴹ = π₁~ᴹ {t₁ᴹ = t₁ᴹ} {t₂ᴹ = t₂ᴹ} idᴹ

module _ (δᴹ : Subᴹ Δᴹ Γᴹ δ) (σᴹ : Subᴹ Θᴹ Δᴹ σ) where
  _⨾ᴹ_ : Subᴹ Θᴹ Γᴹ (δ ⨾ σ)
  _⨾ᴹ_ = (⇓ᵂᵏ δ ⨾ᵂᵏ ⇓ᵂᵏ σ) ⇑ᴹ (⇓ᵀᵐˢᴹ δᴹ [ σᴹ ]*ᴹ)

module _ {Γᴹ : Ctxᴹ Ψ Γ} (ρ : Γᴹ .Env usᴿ Δᴿᵉʷ δ)
         (Aᴹ : Tyᴹ Γᴹ A)
         (let module Γᴹ = CtxNS Γᴹ
              module Aᴹ = TyNS Aᴹ) where

  _^ᴱ_ : (Γᴹ ▷ᴹ Aᴹ) .Env (usᴿ [ wkᴿ ]Nesᴿ) (Δᴿᵉʷ [ wkᵀʰ ]ᴿᵉʷ) (δ ^ A)
  _^ᴱ_ = (ρ Γᴹ.[ wkᵀʰ ]ᴱ) ×, Aᴹ.vzⱽ (ρ Γᴹ.[ wkᵀʰ ]ᴱ)
