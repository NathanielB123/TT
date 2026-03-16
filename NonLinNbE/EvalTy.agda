{-# OPTIONS --rewriting --prop #-}

open import Utils
open import Utils.WithK

open import NonLinNbE.SyntaxEta
open import NonLinNbE.Elim
open import NonLinNbE.Nf
open import NonLinNbE.Thin
open import NonLinNbE.EvalMotives
open import NonLinNbE.Eval

module NonLinNbE.EvalTy where

record TyVal (Γᴹ : Env Γ) (A : Ty Γ) : Set where
  constructor mk
  field
    evalTy : Γᴹ .El Δ δ → TyNf Δ (A [ δ ]T)
    natTy  : {ρ : Γᴹ .El Δ δ} {σTh : Thin Θ Δ σ}
           → evalTy ρ [ σTh ]TyNf ≡ evalTy (Γᴹ ._[_]E ρ σTh)
open TyVal public

opaque
  tyVal≡' : {Γᴹ : Env Γ} {A₁ᴹ A₂ᴹ : TyVal Γᴹ A}
          → (λ {Δ δ} → A₁ᴹ .evalTy {Δ} {δ}) ≡ A₂ᴹ .evalTy
          → A₁ᴹ ≡ A₂ᴹ
  tyVal≡' refl 
    = ap (mk _) 
        ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_} 
        → funexti λ {_} → funexti λ {_} → uip)

  tyVal≡ : {Γᴹ : Env Γ} {A₁ᴹ A₂ᴹ : TyVal Γᴹ A}
         → (∀ {Δ δ} (ρ : Γᴹ .El Δ δ) → A₁ᴹ .evalTy ρ ≡ A₂ᴹ .evalTy ρ)
         → A₁ᴹ ≡ A₂ᴹ
  tyVal≡ p = tyVal≡' (funexti λ {_} → funexti λ {_} → funext λ ρ → p ρ)

evalTy𝕄 : Motives _ _ _ _

evalTy𝕄 .Ctxᴹ Γ    = 𝟙
evalTy𝕄 .Tyᴹ  ⟨⟩ A = TyVal (elimCtx eval𝕞 _) A
evalTy𝕄 .Tmᴹ  ⟨⟩ Aᴹ t = 𝟙
evalTy𝕄 .Tmsᴹ ⟨⟩ ⟨⟩ δ = 𝟙

evalTy𝕞 : Methods evalTy𝕄

evalTy𝕞 ._[_]Tᴹ {δ = δ} Aᴹ ⟨⟩ .evalTy ρ 
  = Aᴹ .evalTy (elimTms eval𝕞 δ .act ρ)
evalTy𝕞 ._[_]Tᴹ {δ = δ} Aᴹ ⟨⟩ .natTy    
  = Aᴹ .natTy ∙ ap (Aᴹ .evalTy) (elimTms eval𝕞 δ .nat)
evalTy𝕞 .[id]Tᴹ    = {!   !}
evalTy𝕞 .[][]Tᴹ    = {!   !}
evalTy𝕞 .Πᴹ        = {!   !}
evalTy𝕞 .Π[]ᴹ      = {!   !}
evalTy𝕞 .ℤᴹ        .evalTy ρ = {!!}
evalTy𝕞 .ℤᴹ        .natTy    = {!!}
evalTy𝕞 .IF-ZEᴹ {t = t} ⟨⟩ Aᴹ Bᴹ .evalTy ρ 
  = IF-ZEⱽ (elimTm eval𝕞 t .act ρ) (Aᴹ .evalTy ρ) (Bᴹ .evalTy ρ)
evalTy𝕞 .IF-ZEᴹ {t = t} ⟨⟩ Aᴹ Bᴹ .natTy    
  = {!   !}
evalTy𝕞 .ℤ[]ᴹ      = {!   !}
evalTy𝕞 .IF-ZE[]ᴹ  = {!   !}
evalTy𝕞 .IF-ZE-zeᴹ = tyVal≡' refl
evalTy𝕞 .IF-ZE-suᴹ = tyVal≡' refl

evalTy𝕞 .idᴹ         = ⟨⟩
evalTy𝕞 ._⨾ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
evalTy𝕞 .id⨾ᴹ        = refl
evalTy𝕞 .⨾idᴹ        = refl
evalTy𝕞 .⨾⨾ᴹ         = refl
evalTy𝕞 ._[_]ᴹ ⟨⟩ ⟨⟩ = ⟨⟩
evalTy𝕞 .[id]ᴹ       = refl[]
evalTy𝕞 .[][]ᴹ       = refl[]
evalTy𝕞 .•ᴹ          = ⟨⟩
evalTy𝕞 .εᴹ          = ⟨⟩
evalTy𝕞 .•ηᴹ         = refl
evalTy𝕞 ._▷ᴹ_ ⟨⟩ _   = ⟨⟩
evalTy𝕞 ._,ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
evalTy𝕞 .pᴹ          = ⟨⟩
evalTy𝕞 .qᴹ          = ⟨⟩
evalTy𝕞 .,⨾ᴹ         = refl
evalTy𝕞 .p,ᴹ         = refl
evalTy𝕞 .q,ᴹ         = refl[]
evalTy𝕞 .▷ηᴹ         = refl
evalTy𝕞 .lamᴹ ⟨⟩     = ⟨⟩
evalTy𝕞 .appᴹ ⟨⟩     = ⟨⟩
evalTy𝕞 .lam[]ᴹ      = refl[]
evalTy𝕞 .βᴹ          = refl
evalTy𝕞 .ηᴹ          = refl[]
evalTy𝕞 .zeᴹ         = ⟨⟩
evalTy𝕞 .suᴹ ⟨⟩      = ⟨⟩
evalTy𝕞 ._-ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
evalTy𝕞 .ze[]ᴹ       = refl[]
evalTy𝕞 .su[]ᴹ       = refl[]
evalTy𝕞 .-[]ᴹ        = refl[]
evalTy𝕞 .-zeᴹ        = refl
evalTy𝕞 .-cancelᴹ    = refl
evalTy𝕞 .-suᴹ        = refl


