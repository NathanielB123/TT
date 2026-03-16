{-# OPTIONS --rewriting #-}

open import Utils renaming (_,_ to _Σ,_)
open import Utils.Trunc
open import Utils.WithK

open import NonLinNbE.SyntaxEta
open import NonLinNbE.Elim
open import NonLinNbE.Nf
open import NonLinNbE.Thin
open import NonLinNbE.Eval
open import NonLinNbE.EvalMotives

module NonLinNbE.QuoteUnquote where

env : ∀ Δ Γ → Tms Δ Γ → Set
env Δ Γ δ = elimCtx eval𝕞 Γ .El Δ δ

val : (A : Ty Γ) → env Δ Γ δ → Tm Δ (A [ δ ]T) → Set
val A ρ t = elimTy eval𝕞 A .El ρ t

_⊢_[_]ᴱ : ∀ Γ {δ} → env Δ Γ δ → Thin Θ Δ σ → env Θ Γ (δ ⨾ σ)
Γ ⊢ ρ [ σTh ]ᴱ = elimCtx eval𝕞 Γ ._[_]E ρ σTh

_∋_[_]ⱽ : ∀ {ρ : env Δ Γ δ} A {t : Tm Δ (A [ δ ]T)}
        → val A ρ t → (σTh : Thin Θ Δ σ) → val A (Γ ⊢ ρ [ σTh ]ᴱ) (t [ σ ])
A ∋ τ [ σTh ]ⱽ = elimTy eval𝕞 A ._[_]V τ σTh

[id]ᴱ : {ρ : env Δ Γ δ} → elimCtx eval𝕞 Γ ._[_]E ρ idTh ≡ ρ
[id]ᴱ {Γ = Γ} = elimCtx eval𝕞 Γ .[id]E

[][]ᴱ : {ρ : env Δ Γ δ} {σTh : Thin Θ Δ σ} {γTh : Thin Λ Θ γ} 
      → Γ ⊢ (Γ ⊢ ρ [ σTh ]ᴱ) [ γTh ]ᴱ ≡ Γ ⊢ ρ [ σTh ⨾Th γTh ]ᴱ
[][]ᴱ {Γ = Γ} = elimCtx eval𝕞 Γ .[][]E

record “” (A : Ty Γ) : Set where
  constructor mk
  field
    -- "Quote"
    “ : {ρ : env Δ Γ δ} 
      → val A ρ t → Nf Δ (A [ δ ]T) t
    -- "Unquote"
    ” : {ρ : env Δ Γ δ} 
      → Ne Δ (A [ δ ]T) t → val A ρ t

    ”[] : {ρ : env Δ Γ δ} {tᴺᵉ : Ne Δ (A [ δ ]T) t} {σTh : Thin Θ Δ σ}
        → _≡_ {A = val A (Γ ⊢ ρ [ σTh ]ᴱ) (t [ σ ])} 
              (A ∋ (” tᴺᵉ) [ σTh ]ⱽ) (” (tᴺᵉ [ σTh ]Ne))
open “”

opaque
  “”≡' : {A₁ᴹ A₂ᴹ : “” A}
      → _≡_ {A = ∀ {Δ δ t} {ρ : env Δ Γ δ} → val A ρ t → Nf Δ (A [ δ ]T) t} 
            (A₁ᴹ .“) (A₂ᴹ .“)
      → _≡_ {A = ∀ {Δ δ t} {ρ : env Δ Γ δ} → Ne Δ (A [ δ ]T) t → val A ρ t} 
            (A₁ᴹ .”) (A₂ᴹ .”)
      → A₁ᴹ ≡ A₂ᴹ
  “”≡' refl refl = ap (mk _ _) {!!} -- A bunch of funext followed by UIP

  “”≡ : {A₁ᴹ A₂ᴹ : “” A} 
      → (∀ {Δ δ t} {ρ : env Δ Γ δ} (τ : val A ρ t) 
        → A₁ᴹ .“ {Δ} {δ} {t} {ρ} τ ≡ A₂ᴹ .“ τ)
      → (∀ {Δ δ t} {ρ : env Δ Γ δ} (tᴺᵉ : Ne Δ (A [ δ ]T) t) 
        → A₁ᴹ .” {Δ} {δ} {t} {ρ} tᴺᵉ ≡ A₂ᴹ .” tᴺᵉ)
      → A₁ᴹ ≡ A₂ᴹ
  “”≡ “≡ ”≡ 
    = “”≡' ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_} 
          → funext λ τ → “≡ τ) 
          ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_} 
          → funext λ tᴺᵉ → ”≡ tᴺᵉ)

“”𝕄 : Motives _ _ _ _
“”𝕄 .Ctxᴹ _     = 𝟙
“”𝕄 .Tyᴹ  ⟨⟩ A  = “” A
“”𝕄 .Tmᴹ  _ _ _ = 𝟙
“”𝕄 .Tmsᴹ _ _ _ = 𝟙

{-# NON_COVERING #-}
“”𝕞 : Methods “”𝕄
“”𝕞 ._[_]Tᴹ Aᴹ ⟨⟩ .“ τ   = Aᴹ .“ τ
“”𝕞 ._[_]Tᴹ Aᴹ ⟨⟩ .” tᴺᵉ = Aᴹ .” tᴺᵉ

“”𝕞 .[id]Tᴹ = “”≡' refl refl
“”𝕞 .[][]Tᴹ = “”≡' refl refl

“”𝕞 .Πᴹ {A = A} Aᴹ Bᴹ .“ {δ = δ} τ   
  = lamᴺᶠ (Bᴹ .“ (τ .act (idTh ⁺Th (A [ δ ]T)) (Aᴹ .” vzᴺᵉ))) 
“”𝕞 .Πᴹ Aᴹ Bᴹ .” tᴺᵉ .act σTh υ = Bᴹ .” (appᴺᵉ (tᴺᵉ [ σTh ]Ne) (Aᴹ .“ υ))
“”𝕞 .Πᴹ {A = A} {B = B} Aᴹ Bᴹ .” tᴺᵉ .nat σTh γTh υ .[]coe = 
  coe _ (B ∋ Bᴹ .” (appᴺᵉ (tᴺᵉ [ σTh ]Ne) (Aᴹ .“ υ)) [ γTh ]ⱽ)
  ≡⟨ ap (coe _)(Bᴹ .”[]) ⟩
  coe _ (Bᴹ .” (appᴺᵉ (tᴺᵉ [ σTh ]Ne) (Aᴹ .“ υ) [ γTh ]Ne))
  ≡⟨ {!!} ⟩
  coe _ (Bᴹ .” (appᴺᵉ (tᴺᵉ [ σTh ]Ne [ γTh ]Ne) ((Aᴹ .“ υ) [ γTh ]Nf)))
  ≡⟨ {!!} ⟩
  Bᴹ .” (appᴺᵉ (tᴺᵉ [ σTh ⨾Th γTh ]Ne) (Aᴹ .“ (coe _ (A ∋ υ [ γTh ]ⱽ)))) ∎

-- -- (appᴺᵉ (tᴺᵉ [ σTh ⨾Th γTh ]Ne)
-- --        (Aᴹ .“
-- --         (transp (λ □ → El (elimTy eval𝕞 A) □ (u [ γ ]))
-- --          ([][]E (elimCtx eval𝕞 A.1)) ((elimTy eval𝕞 A [ υ ]V) γTh))))


--   -- apd-K (Bᴹ .”) {!!}

-- “”𝕞 .Π[]ᴹ = {!!}
-- “”𝕞 .ℤᴹ .“ (tᴿ Σ, tC) = tᴿ      Σ, ∥-∥-map valℤC tC
-- “”𝕞 .ℤᴹ .” (tᴿ Σ, tC) = neℤᴿ tᴿ Σ, ∥-∥-map neC tC

-- “”𝕞 .ℤ[]ᴹ = {!!}
-- “”𝕞 .IF-ZEᴹ ⟨⟩ Aᴹ Bᴹ = {!!}
-- “”𝕞 .IF-ZE[]ᴹ = {!   !}
-- “”𝕞 .IF-ZE-zeᴹ = {!   !}
-- “”𝕞 .IF-ZE-suᴹ = {!   !}
-- “”𝕞 .IF-ZE-ze-ᴹ = {!   !}


-- “”𝕞 .idᴹ         = ⟨⟩
-- “”𝕞 ._⨾ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
-- “”𝕞 .id⨾ᴹ        = refl
-- “”𝕞 .⨾idᴹ        = refl
-- “”𝕞 .⨾⨾ᴹ         = refl
-- “”𝕞 ._[_]ᴹ ⟨⟩ ⟨⟩ = ⟨⟩
-- “”𝕞 .[id]ᴹ       = refl[]
-- “”𝕞 .[][]ᴹ       = refl[]
-- “”𝕞 .•ᴹ          = ⟨⟩
-- “”𝕞 .εᴹ          = ⟨⟩
-- “”𝕞 .•ηᴹ         = refl
-- “”𝕞 ._▷ᴹ_ ⟨⟩ _   = ⟨⟩
-- “”𝕞 ._,ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
-- “”𝕞 .pᴹ          = ⟨⟩
-- “”𝕞 .qᴹ          = ⟨⟩
-- “”𝕞 .,⨾ᴹ         = refl
-- “”𝕞 .p,ᴹ         = refl
-- “”𝕞 .q,ᴹ         = refl[]
-- “”𝕞 .▷ηᴹ         = refl
-- “”𝕞 .lamᴹ ⟨⟩     = ⟨⟩
-- “”𝕞 .appᴹ ⟨⟩     = ⟨⟩
-- “”𝕞 .lam[]ᴹ      = refl[]
-- “”𝕞 .βᴹ          = refl
-- “”𝕞 .ηᴹ          = refl[]
-- “”𝕞 .zeᴹ         = ⟨⟩
-- “”𝕞 .suᴹ ⟨⟩      = ⟨⟩
-- “”𝕞 ._-ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
-- “”𝕞 .ze[]ᴹ       = refl[]
-- “”𝕞 .su[]ᴹ       = refl[]
-- “”𝕞 .-[]ᴹ        = refl[]
-- “”𝕞 .-zeᴹ        = refl
-- “”𝕞 .-cancelᴹ    = refl
-- “”𝕞 .-suᴹ        = refl
