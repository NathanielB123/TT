{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils

open import NonLinNbE.SyntaxEta

module NonLinNbE.Thin where

_⁺_ : Tms Δ Γ → ∀ A → Tms (Δ ▷ A) Γ
δ ⁺ A = δ ⨾ p

data Thin : ∀ Δ Γ → Tms Δ Γ → Set where
  εTh   : Thin • • ε
  _⁺Th_ : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ A) Γ (δ ⁺ A)
  _^Th_ : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ (A [ δ ]T)) (Γ ▷ A) (δ ^ A)

variable
  δTh σTh γTh : Thin _ _ _

idTh : Thin Γ Γ id
idTh {Γ = •}     = εTh
idTh {Γ = Γ ▷ A} = idTh ^Th A

_⨾Th_ : Thin Δ Γ δ → Thin Θ Δ σ → Thin Θ Γ (δ ⨾ σ)
εTh         ⨾Th σTh                   = σTh
(δTh ^Th A) ⨾Th (σTh ^Th .(A [ _ ]T)) = (δTh ⨾Th σTh) ^Th A
(δTh ⁺Th A) ⨾Th (σTh ^Th A)           = (δTh ⨾Th σTh) ⁺Th (A [ _ ]T)
δTh         ⨾Th (σTh ⁺Th A)           = (δTh ⨾Th σTh) ⁺Th A

⨾⁺Th : {δTh : Thin Δ Γ δ} {σTh : Thin Θ Δ σ} {A : Ty Θ} 
     → δTh ⨾Th (σTh ⁺Th A) ≡ (δTh ⨾Th σTh) ⁺Th A
⨾⁺Th {δTh = εTh}       = refl
⨾⁺Th {δTh = δTh ⁺Th A} = refl
⨾⁺Th {δTh = δTh ^Th A} = refl

⨾⁺Th' : {δTh : Thin Δ Γ δ} {σTh : Thin Θ Δ σ} {A : Ty Θ} 
      → _⨾Th_ {σ = ⟨ _ ⟩} δTh (σTh ⁺Th A) ≡ (δTh ⨾Th σTh) ⁺Th A
⨾⁺Th' = ⨾⁺Th
{-# REWRITE ⨾⁺Th' #-}

id⨾Th : idTh {Γ = Γ} ⨾Th σTh ≡ σTh
id⨾Th {Γ = •}                       = refl
id⨾Th {Γ = Γ ▷ A} {σTh = σTh ⁺Th B} = ap (_⁺Th B) id⨾Th
id⨾Th {Γ = Γ ▷ A} {σTh = σTh ^Th A} = ap (_^Th A) id⨾Th

⨾idTh : δTh ⨾Th idTh {Γ = Γ} ≡ δTh
⨾idTh {δTh = εTh}       = refl
⨾idTh {δTh = δTh ⁺Th A} = ap (_⁺Th A) ⨾idTh
⨾idTh {δTh = δTh ^Th A} = ap (_^Th A) ⨾idTh

⨾⨾Th : {δTh : Thin Δ Γ δ} {σTh : Thin Θ Δ σ} {γTh : Thin Λ Θ γ}
     → (δTh ⨾Th σTh) ⨾Th γTh ≡ δTh ⨾Th (σTh ⨾Th γTh)
⨾⨾Th {δTh = εTh}       = refl
⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh ⁺Th A} 
  = ap (_⁺Th A) (⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh})
⨾⨾Th {δTh = δTh} {σTh = σTh ⁺Th A} {γTh = γTh ^Th A} 
  = ap (_⁺Th (A [ _ ]T)) (⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh}) 
⨾⨾Th {δTh = δTh ⁺Th A} {σTh = σTh ^Th A} {γTh = γTh ^Th .(A [ _ ]T)} 
  = ap (_⁺Th (A [ _ ]T)) (⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh}) 
⨾⨾Th {δTh = δTh ^Th A} {σTh = σTh ^Th _} {γTh = γTh ^Th _}    
  = ap (_^Th A) (⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh})

{-# REWRITE id⨾Th ⨾idTh ⨾⨾Th #-}
