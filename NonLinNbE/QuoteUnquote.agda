{-# OPTIONS --rewriting --prop #-}

open import Utils renaming (_,_ to _Σ,_)
open import Utils.WithK
open import Utils.Prop

open import NonLinNbE.SyntaxEta
open import NonLinNbE.Elim
open import NonLinNbE.Nf
open import NonLinNbE.Thin
open import NonLinNbE.Eval
open import NonLinNbE.EvalMotives

module NonLinNbE.QuoteUnquote where

env : ∀ Δ Γ → Tms Δ Γ → Set
env Δ Γ δ = elimCtx eval𝕞 Γ .El Δ δ

{-# DISPLAY Env.El (elimCtx eval𝕞 Γ) Δ δ = env Δ Γ δ #-}

val : (A : Ty Γ) → env Δ Γ δ → Tm Δ (A [ δ ]T) → Set
val A ρ t = elimTy eval𝕞 A .El ρ t

{-# DISPLAY Val.El (elimTy eval𝕞) A ρ t = val A ρ t #-}

_⊢_[_]ᴱ : ∀ Γ {δ} → env Δ Γ δ → Thin Θ Δ σ → env Θ Γ (δ ⨾ σ)
Γ ⊢ ρ [ σTh ]ᴱ = elimCtx eval𝕞 Γ ._[_]E ρ σTh

{-# DISPLAY _[_]E (elimCtx eval𝕞 Γ) ρ σTh = Γ ⊢ ρ [ σTh ]ᴱ #-}

_∋_[_]ⱽ : ∀ {ρ : env Δ Γ δ} A {t : Tm Δ (A [ δ ]T)}
        → val A ρ t → (σTh : Thin Θ Δ σ) → val A (Γ ⊢ ρ [ σTh ]ᴱ) (t [ σ ])
A ∋ τ [ σTh ]ⱽ = elimTy eval𝕞 A ._[_]V τ σTh

{-# DISPLAY _[_]V (elimTy eval𝕞 A) τ σTh = A ∋ τ [ σTh ]ⱽ #-}

[id]ᴱ : ∀ Γ {δ} {ρ : env Δ Γ δ} → elimCtx eval𝕞 Γ ._[_]E ρ idTh ≡ ρ
[id]ᴱ Γ = elimCtx eval𝕞 Γ .[id]E

{-# DISPLAY [id]E (elimCtx eval𝕞 Γ) = [id]ᴱ Γ #-}

[][]ᴱ : ∀ Γ {δ} {ρ : env Δ Γ δ} {σTh : Thin Θ Δ σ} {γTh : Thin Λ Θ γ} 
      → Γ ⊢ (Γ ⊢ ρ [ σTh ]ᴱ) [ γTh ]ᴱ ≡ Γ ⊢ ρ [ σTh ⨾Th γTh ]ᴱ
[][]ᴱ Γ = elimCtx eval𝕞 Γ .[][]E

{-# DISPLAY [][]E (elimCtx eval𝕞 Γ) = [][]ᴱ Γ #-}

record “” (A : Ty Γ) : Set where
  constructor mk
  field
    -- "Quote"
    “ : (ρ : env Δ Γ δ) → val A ρ t → Nf Δ (A [ δ ]T) t
    -- "Unquote"
    ” : (ρ : env Δ Γ δ) → Ne Δ (A [ δ ]T) t → val A ρ t


    “[] : {ρ : env Δ Γ δ} {τ : val A ρ t} {σTh : Thin Θ Δ σ}
        → _≡_ {A = Nf Θ (A [ δ ⨾ σ ]T) (t [ σ ])}
              ((“ ρ τ) [ σTh ]Nf) (“ (Γ ⊢ ρ [ σTh ]ᴱ) (A ∋ τ [ σTh ]ⱽ))
    ”[] : {ρ : env Δ Γ δ} {tᴺᵉ : Ne Δ (A [ δ ]T) t} {σTh : Thin Θ Δ σ}
        → _≡_ {A = val A (Γ ⊢ ρ [ σTh ]ᴱ) (t [ σ ])} 
              (A ∋ (” ρ tᴺᵉ) [ σTh ]ⱽ) (” (Γ ⊢ ρ [ σTh ]ᴱ) (tᴺᵉ [ σTh ]Ne))
open “”

opaque
  “”≡' : {A₁ᴹ A₂ᴹ : “” A}
      → _≡_ {A = ∀ {Δ δ t} (ρ : env Δ Γ δ) → val A ρ t → Nf Δ (A [ δ ]T) t} 
            (A₁ᴹ .“) (A₂ᴹ .“)
      → _≡_ {A = ∀ {Δ δ t} (ρ : env Δ Γ δ) → Ne Δ (A [ δ ]T) t → val A ρ t} 
            (A₁ᴹ .”) (A₂ᴹ .”)
      → A₁ᴹ ≡ A₂ᴹ
  “”≡' refl refl 
    = ap₂ (mk _ _) 
          ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_} 
          → funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_}
          → uip) 
          ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_} 
          → funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_}
          → uip) 

  “”≡ : {A₁ᴹ A₂ᴹ : “” A} 
      → (∀ {Δ δ t} (ρ : env Δ Γ δ) (τ : val A ρ t) 
        → A₁ᴹ .“ {Δ} {δ} {t} ρ τ ≡ A₂ᴹ .“ ρ τ)
      → (∀ {Δ δ t} (ρ : env Δ Γ δ) (tᴺᵉ : Ne Δ (A [ δ ]T) t) 
        → A₁ᴹ .” {Δ} {δ} {t} ρ tᴺᵉ ≡ A₂ᴹ .” ρ tᴺᵉ)
      → A₁ᴹ ≡ A₂ᴹ
  “”≡ “≡ ”≡ 
    = “”≡' ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funext λ ρ 
           → funext λ τ → “≡ ρ τ) 
           ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funext λ ρ 
           → funext λ tᴺᵉ → ”≡ ρ tᴺᵉ)

“”𝕄 : Motives _ _ _ _
“”𝕄 .Ctxᴹ _     = 𝟙
“”𝕄 .Tyᴹ  ⟨⟩ A  = “” A
“”𝕄 .Tmᴹ  _ _ _ = 𝟙
“”𝕄 .Tmsᴹ _ _ _ = 𝟙

{-# NON_COVERING #-}
“”𝕞 : Methods “”𝕄
“”𝕞 ._[_]Tᴹ Aᴹ ⟨⟩ .“ ρ τ   = Aᴹ .“ _ τ
“”𝕞 ._[_]Tᴹ Aᴹ ⟨⟩ .” ρ tᴺᵉ = Aᴹ .” _ tᴺᵉ
-- “”𝕞 ._[_]Tᴹ Aᴹ ⟨⟩ .“[] = {!Aᴹ .“[]!}
“”𝕞 ._[_]Tᴹ {A = A} {δ = δ} Aᴹ ⟨⟩ .”[] {ρ = ρ} {tᴺᵉ = tᴺᵉ} {σTh = σTh} =
  coe _ (A ∋ ” Aᴹ (elimTms eval𝕞 δ .act ρ) tᴺᵉ [ σTh ]ⱽ)
  ≡⟨ ap (coe _) (Aᴹ .”[] {tᴺᵉ = tᴺᵉ} {σTh = σTh}) ⟩
  coe _ (Aᴹ .” _ (tᴺᵉ [ σTh ]Ne))
  ≡⟨ apd (λ □ → Aᴹ .” □ _) (elimTms eval𝕞 δ .nat) .[]coe ⟩
  Aᴹ .” _ (tᴺᵉ [ σTh ]Ne) ∎

“”𝕞 .[id]Tᴹ = “”≡' refl refl
“”𝕞 .[][]Tᴹ = “”≡' refl refl

“”𝕞 .Πᴹ {A = A} Aᴹ Bᴹ .“ {δ = δ} ρ τ   
  = lamᴺᶠ (Bᴹ .“ _ (τ .act (idTh ⁺Th (A [ δ ]T)) 
          (Aᴹ .” _ vzᴺᵉ))) 
“”𝕞 .Πᴹ  Aᴹ Bᴹ .” ρ tᴺᵉ .act σTh υ = Bᴹ .” _ (appᴺᵉ (tᴺᵉ [ σTh ]Ne) (Aᴹ .“ _ υ))
“”𝕞 .Πᴹ {Γ = Γ} {A = A} {B = B} Aᴹ Bᴹ .” ρ tᴺᵉ .nat σTh γTh υ .[]coe = 
  coe _ (B ∋ Bᴹ .” _ (appᴺᵉ (tᴺᵉ [ σTh ]Ne) (Aᴹ .“ _ υ)) [ γTh ]ⱽ)
  ≡⟨ coe≡-K (Bᴹ .”[]) ⟩
  coe _ (Bᴹ .” _ (appᴺᵉ (tᴺᵉ [ σTh ⨾Th γTh ]Ne) ((Aᴹ .“ _ υ) [ γTh ]Nf)))
  ≡⟨ apdd₂' _ (Bᴹ .”) (apd₂ _Σ,_ ([][]ᴱ Γ) refl[]) refl[]-K .[]coe ⟩
  Bᴹ .” _ (appᴺᵉ (tᴺᵉ [ σTh ⨾Th γTh ]Ne) ((Aᴹ .“ _ υ) [ γTh ]Nf))
  ≡⟨ ap (λ □ → Bᴹ .” _ (appᴺᵉ (tᴺᵉ [ σTh ⨾Th γTh ]Ne) □)) (Aᴹ .“[]) ⟩
  Bᴹ .” _ (appᴺᵉ (tᴺᵉ [ σTh ⨾Th γTh ]Ne) (Aᴹ .“ _ (A ∋ υ [ γTh ]ⱽ)))
  ≡⟨ apd₂ (λ _ □ → Bᴹ .” _ (appᴺᵉ (tᴺᵉ [ σTh ⨾Th γTh ]Ne) (Aᴹ .“  _ □))) 
          _ refl[] ⟩
  Bᴹ .” _ (appᴺᵉ (tᴺᵉ [ σTh ⨾Th γTh ]Ne) (Aᴹ .“ _ (coe _ (A ∋ υ [ γTh ]ⱽ)))) ∎
-- “”𝕞 .Πᴹ Aᴹ Bᴹ .“[] = {!!}
-- “”𝕞 .Πᴹ Aᴹ Bᴹ .”[] = {!!}

-- “”𝕞 .Π[]ᴹ = “”≡ {!!} {!!}

“”𝕞 .ℤᴹ .“ _ (tᴿ ∃, tC) = tᴿ      ∃, valℤC tC
“”𝕞 .ℤᴹ .” _ (tᴿ ∃, tC) = neℤᴿ tᴿ ∃, neC tC
“”𝕞 .ℤᴹ .“[] = refl
“”𝕞 .ℤᴹ .”[] = refl

“”𝕞 .ℤ[]ᴹ = “”≡' refl refl
-- “”𝕞 .IF-ZEᴹ ⟨⟩ Aᴹ Bᴹ = {!!}
-- “”𝕞 .IF-ZE[]ᴹ = {!   !}
-- “”𝕞 .IF-ZE-zeᴹ = {!   !}
-- “”𝕞 .IF-ZE-suᴹ = {!   !}
-- “”𝕞 .IF-ZE-ze-ᴹ = {!   !}


“”𝕞 .idᴹ         = ⟨⟩
“”𝕞 ._⨾ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
“”𝕞 .id⨾ᴹ        = refl
“”𝕞 .⨾idᴹ        = refl
“”𝕞 .⨾⨾ᴹ         = refl
“”𝕞 ._[_]ᴹ ⟨⟩ ⟨⟩ = ⟨⟩
“”𝕞 .[id]ᴹ       = refl[]
“”𝕞 .[][]ᴹ       = refl[]
“”𝕞 .•ᴹ          = ⟨⟩
“”𝕞 .εᴹ          = ⟨⟩
“”𝕞 .•ηᴹ         = refl
“”𝕞 ._▷ᴹ_ ⟨⟩ _   = ⟨⟩
“”𝕞 ._,ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
“”𝕞 .pᴹ          = ⟨⟩
“”𝕞 .qᴹ          = ⟨⟩
“”𝕞 .,⨾ᴹ         = refl
“”𝕞 .p,ᴹ         = refl
“”𝕞 .q,ᴹ         = refl[]
“”𝕞 .▷ηᴹ         = refl
“”𝕞 .lamᴹ ⟨⟩     = ⟨⟩
“”𝕞 .appᴹ ⟨⟩     = ⟨⟩
“”𝕞 .lam[]ᴹ      = refl[]
“”𝕞 .βᴹ          = refl
“”𝕞 .ηᴹ          = refl[]
“”𝕞 .zeᴹ         = ⟨⟩
“”𝕞 .suᴹ ⟨⟩      = ⟨⟩
“”𝕞 ._-ᴹ_ ⟨⟩ ⟨⟩  = ⟨⟩
“”𝕞 .ze[]ᴹ       = refl[]
“”𝕞 .su[]ᴹ       = refl[]
“”𝕞 .-[]ᴹ        = refl[]
“”𝕞 .-zeᴹ        = refl
“”𝕞 .-cancelᴹ    = refl
“”𝕞 .-suᴹ        = refl
