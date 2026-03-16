{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils renaming (_,_ to _Σ,_)
open import Utils.WithK

open import NonLinNbE.SyntaxEta
open import NonLinNbE.Elim
open import NonLinNbE.Nf
open import NonLinNbE.Thin
open import NonLinNbE.EvalMotives

module NonLinNbE.Eval where

eval𝕄 : Motives _ _ _ _
eval𝕞 : Methods eval𝕄

eval𝕄 .Ctxᴹ Γ       = Env Γ
eval𝕄 .Tyᴹ  Γᴹ A    = Val Γᴹ A
eval𝕄 .Tmᴹ  Γᴹ Aᴹ t = eval Γᴹ Aᴹ t
eval𝕄 .Tmsᴹ Δᴹ Γᴹ δ = eval* Δᴹ Γᴹ δ

postulate
  todo  : ∀ {A : Set ℓ} → A
  cheat : ∀ {A : Set ℓ} → A

{-# NON_COVERING #-}
eval𝕞 .idᴹ        .act ρ = ρ
eval𝕞 .idᴹ        .nat   = refl
eval𝕞 ._⨾ᴹ_ δᴹ σᴹ .act ρ = δᴹ .act (σᴹ .act ρ)
eval𝕞 ._⨾ᴹ_ δᴹ σᴹ .nat   = δᴹ .nat ∙ ap (δᴹ .act) (σᴹ .nat)

eval𝕞 .id⨾ᴹ = eval*≡' refl
eval𝕞 .⨾idᴹ = eval*≡' refl
eval𝕞 .⨾⨾ᴹ  = eval*≡' refl

eval𝕞 ._[_]Tᴹ Aᴹ δᴹ .El ρ t 
  = Aᴹ .El (δᴹ .act ρ) t
eval𝕞 ._[_]Tᴹ Aᴹ δᴹ ._[_]V τ σTh 
  = τ A.[ σTh ] (δᴹ .nat) V
  where module A = Val Aᴹ
eval𝕞 ._[_]Tᴹ Aᴹ δᴹ .[id]V = [id]V' Aᴹ
eval𝕞 ._[_]Tᴹ Aᴹ δᴹ .[][]V = [][]V' Aᴹ
eval𝕞 ._[_]ᴹ  tᴹ δᴹ .act ρ = tᴹ .act (δᴹ .act ρ)
eval𝕞 ._[_]ᴹ {Γᴹ = Γᴹ} {Aᴹ = Aᴹ} {Δᴹ = Δᴹ} tᴹ δᴹ .nat {ρ = ρ} {σTh = σTh} = 
  coe _ (tᴹ .act (δᴹ .act ρ) A.[ σTh ]V)
  ≡⟨ ap (coe _) (tᴹ .nat) ⟩
  coe _ (tᴹ .act (δᴹ .act ρ Γ.[ σTh ]E))
  ≡⟨ apd (tᴹ .act) (nat δᴹ) .[]coe ⟩
  tᴹ .act (δᴹ .act (ρ Δ.[ σTh ]E)) ∎
  where module Γ = Env Γᴹ
        module Δ = Env Δᴹ
        module A = Val Aᴹ
eval𝕞 .[id]Tᴹ = val≡'' refl refl[]
eval𝕞 .[id]ᴹ  = eval≡[]' refl[]-K
eval𝕞 .[][]Tᴹ {Aᴹ = Aᴹ} {δᴹ = δᴹ} {σᴹ = σᴹ} 
  = val≡' refl λ {τ₁ = τ₁} {τ₂ = τ₂} τ≡ γTh → coe[] (
  transp (λ □ → El Aᴹ (δᴹ .act □) _) (nat σᴹ)
    (transp (λ □ → El Aᴹ □ _) (nat δᴹ) (τ₁ A.[ γTh ]V))
  ≡⟨ coe-coe {p = ap (λ □ → El Aᴹ (δᴹ .act □) _) (nat σᴹ)} 
             {q = ap (λ □ → El Aᴹ □ _) (nat δᴹ)} ⟩
  coe _ (τ₁ A.[ γTh ]V)
  ≡⟨ coe≡-K (ap (A._[ γTh ]V) (τ≡ .[]coe)) ⟩
  coe _ (τ₂ A.[ γTh ]V) ∎
  )
  where module A = Val Aᴹ
eval𝕞 .[][]ᴹ  = eval≡[]' refl[]-K

eval𝕞 .•ᴹ .El    Δ δ   = 𝟙
eval𝕞 .•ᴹ ._[_]E ρ δTh = ⟨⟩
eval𝕞 .•ᴹ .[id]E       = refl
eval𝕞 .•ᴹ .[][]E       = refl

eval𝕞 .εᴹ .act ρ = ⟨⟩
eval𝕞 .εᴹ .nat   = refl
eval𝕞 .•ηᴹ       = eval*≡' refl

eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ .El Δ δ = Σ (Γᴹ .El Δ (π₁ δ)) λ ρ → Aᴹ .El ρ (π₂ δ)
eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ ._[_]E (ρ Σ, τ) δTh .fst = ρ Γ.[ δTh ]E
  where module Γ = Env Γᴹ
eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ ._[_]E (ρ Σ, τ) δTh .snd = τ A.[ δTh ]V
  where module A = Val Aᴹ
eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ .[id]E = apd₂ _Σ,_ (Γᴹ .[id]E) (Aᴹ .[id]V)
eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ .[][]E = apd₂ _Σ,_ (Γᴹ .[][]E) (Aᴹ .[][]V)

eval𝕞 ._,ᴹ_ δᴹ tᴹ .act ρ .fst = δᴹ .act ρ
eval𝕞 ._,ᴹ_ δᴹ tᴹ .act ρ .snd = tᴹ .act ρ
eval𝕞 ._,ᴹ_ δᴹ tᴹ .nat        = apd₂ _Σ,_ (δᴹ .nat) (coe[] (tᴹ .nat))

eval𝕞 .pᴹ .act (ρ Σ, τ) = ρ
eval𝕞 .pᴹ .nat          = refl
eval𝕞 .qᴹ .act (ρ Σ, τ) = τ
eval𝕞 .qᴹ .nat          = refl

eval𝕞 .,⨾ᴹ {Aᴹ = Aᴹ} {δᴹ = δᴹ} {t = t} {Θᴹ = Θᴹ} {σ = σ} {tᴹ = tᴹ} {σᴹ = σᴹ} 
  = eval*≡ λ ρ → ap (_ Σ,_) (
  tᴹ .act (act σᴹ ρ)
  ≡⟨ sym coe-K ⟩
  coe _ (tᴹ .act (act σᴹ ρ))
  ≡⟨ apdd₂ (λ □ → eval Θᴹ □ (t [ σ ])) (λ _ □ → □ .act ρ) (val≡' _ _) .[]coe ⟩
  _ ∎)
eval𝕞 .p,ᴹ = eval*≡' refl
eval𝕞 .q,ᴹ = eval≡[]' refl[]-K
eval𝕞 .▷ηᴹ {Aᴹ = Aᴹ} {δᴹ = δᴹ} = eval*≡ λ ρ → ap (_ Σ,_) (
  δᴹ .act ρ .snd
  ≡⟨ sym coe-K ⟩
  coe _ (δᴹ .act ρ .snd)
  ≡⟨ apdd₂ (λ □ → eval _ □ _) (λ _ □ → □ .act ρ) (val≡' refl _) .[]coe ⟩
  _ ∎)

eval𝕞 .Πᴹ {Γᴹ = Γᴹ} Aᴹ Bᴹ .El ρ t = ΠVal Aᴹ Bᴹ ρ t
eval𝕞 .Πᴹ {Γᴹ = Γᴹ} Aᴹ Bᴹ ._[_]V {t = t} τ σTh .act γTh υ 
  = transp (λ □ → Bᴹ .El □ (app t [ _ , _ ])) 
           (apd₂ _Σ,_ (sym (Γᴹ .[][]E)) sym-transp[]) 
           (τ .act (σTh ⨾Th γTh) (transp (λ □ → Aᴹ .El □ _) (Γᴹ .[][]E) υ))
eval𝕞 .Πᴹ Aᴹ Bᴹ ._[_]V τ σTh .nat γTh θTh υ = cheat
eval𝕞 .Πᴹ Aᴹ Bᴹ .[id]V = cheat
eval𝕞 .Πᴹ Aᴹ Bᴹ .[][]V = cheat
eval𝕞 .lamᴹ tᴹ .act ρ .act σTh υ     = tᴹ .act (_ Σ, υ)
eval𝕞 .lamᴹ tᴹ .act ρ .nat σTh γTh υ = cheat
eval𝕞 .lamᴹ {Aᴹ = Aᴹ} {Bᴹ = Bᴹ} {t = t} tᴹ .nat {δ = δ} {σ = σ}               
  = ΠVal≡ Aᴹ Bᴹ (lam t [ δ ⨾ σ ]) λ γTh υ → cheat
eval𝕞 .appᴹ {Γᴹ = Γᴹ} {Aᴹ = Aᴹ} {Bᴹ = Bᴹ} tᴹ .act (ρ Σ, υ)
  = transp (λ □ → Bᴹ .El □ _) (apd₂ _Σ,_ (Γᴹ .[id]E) transp-sym[])
           (tᴹ .act ρ .act idTh (transp (λ □ → Aᴹ .El □ _) (sym (Γᴹ .[id]E)) υ))
eval𝕞 .appᴹ {Γᴹ = Γᴹ} {Aᴹ = Aᴹ} {Bᴹ = Bᴹ} tᴹ .nat = cheat
eval𝕞 .Π[]ᴹ {Aᴹ = Aᴹ} {Bᴹ = Bᴹ} {Δᴹ = Δᴹ} {δᴹ = δᴹ} 
  = cheat
  -- = val≡
  -- (λ ρ t → apd₂ ΠVal' (piexti λ {_} → piexti λ {_} → piexti λ {_} 
  -- → piext λ σTh → piext[] (ap (λ □ → Aᴹ .El □ _) (δᴹ .nat)) λ {υ₁ υ₂} υ≡ 
  -- → ap (λ □ → Bᴹ .El □ (app t [ _ ])) (apd₂ _Σ,_ (δᴹ .nat) (coe[] (
  -- transp (λ □ → El Aᴹ □ _) (δᴹ .nat) υ₁
  -- ≡⟨ υ≡ .[]coe ⟩
  -- υ₂
  -- ≡⟨ sym coe-K ⟩
  -- coe _ υ₂
  -- ≡⟨ apdd₂ (λ □ → eval (eval𝕞 ._▷ᴹ_ Δᴹ (eval𝕞 ._[_]Tᴹ Aᴹ δᴹ)) □ q) 
  --          (λ _ □ → □ .act ((ρ Δ.[ σTh ]E) Σ, υ₂)) (val≡' refl _) .[]coe ⟩
  -- _ ∎)
  -- ))) cheat) -- This is provable with propext 
  -- cheat
  -- where module Δ = Env Δᴹ
eval𝕞 .lam[]ᴹ = eval≡[] λ ρ → cheat 
  -- We have entered the ninth circle of transport hell
eval𝕞 .βᴹ {Γᴹ = Γᴹ} {tᴹ = tᴹ}
  = eval≡ λ (ρ Σ, υ) → apd (tᴹ .act) (apd₂ _Σ,_ (Γᴹ .[id]E) transp-sym[]) .[]coe
eval𝕞 .ηᴹ = cheat
  -- η is a bit more tedious than β because η is not strict in the syntax

eval𝕞 .ℤᴹ .El    ρ t   = ℤVal _ t
eval𝕞 .ℤᴹ ._[_]V τ δTh = τ [ δTh ]ℤ
-- eval𝕞 .ℤᴹ .[id]V = {!   !}
-- eval𝕞 .ℤᴹ .[][]V = {!   !}

eval𝕞 .zeᴹ .act ρ = zeⱽ
-- eval𝕞 .zeᴹ .nat   = {!   !}

eval𝕞 .suᴹ tᴹ .act ρ = suⱽ (tᴹ .act ρ)
-- eval𝕞 .suᴹ tᴹ .nat = {!   !}

eval𝕞 ._-ᴹ_ tᴹ uᴹ .act ρ = tᴹ .act ρ -ⱽ uᴹ .act ρ
-- eval𝕞 ._-ᴹ_ tᴹ uᴹ .nat   = {!   !}

-- eval𝕞 .IF-ZEᴹ = {!   !}

eval𝕞 .ℤ[]ᴹ  = val≡' refl todo
eval𝕞 .ze[]ᴹ = eval≡[]' refl[]-K
-- eval𝕞 .su[]ᴹ    = {!!}
-- eval𝕞 .-[]ᴹ     = {!   !}
-- eval𝕞 .IF-ZE[]ᴹ = {!   !}

eval𝕞 .-zeᴹ               = eval≡ λ ρ → refl
eval𝕞 .-cancelᴹ {tᴹ = tᴹ} = eval≡ λ ρ → -cancelⱽ {tⱽ = tᴹ .act ρ}
eval𝕞 .-suᴹ               = eval≡ λ ρ → refl
-- eval𝕞 .IF-ZE-zeᴹ  = {!   !}
-- eval𝕞 .IF-ZE-suᴹ  = {!   !}
-- eval𝕞 .IF-ZE-ze-ᴹ = {!   !}
