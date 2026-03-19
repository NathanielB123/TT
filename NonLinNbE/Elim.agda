{-# OPTIONS --rewriting -WnoRewriteVariablesBoundInSingleton #-}

open import Utils renaming (_,_ to _Σ,_)

open import NonLinNbE.SyntaxEta

-- We postulate an induction principle for the strictified syntax
module NonLinNbE.Elim where

record Motives ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Set (lsuc (ℓ₁ ⊔l ℓ₂ ⊔l ℓ₃ ⊔l ℓ₄)) where
  field
    Ctxᴹ : Ctx → Set ℓ₁
    Tyᴹ  : Ctxᴹ Γ → Ty Γ → Set ℓ₂
    Tmᴹ  : ∀ Γᴹ → Tyᴹ Γᴹ A → Tm Γ A → Set ℓ₃
    Tmsᴹ : Ctxᴹ Δ → Ctxᴹ Γ → Tms Δ Γ → Set ℓ₄
module _ (𝕄 : Motives ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open Motives 𝕄
  module Vars where variable
      Γᴹ Δᴹ Θᴹ Λᴹ : Ctxᴹ _
      Aᴹ Bᴹ Cᴹ : Tyᴹ _ _
      tᴹ uᴹ vᴹ : Tmᴹ _ _ _
      δᴹ σᴹ γᴹ : Tmsᴹ _ _ _
  open Vars
  record Methods : Set (ℓ₁ ⊔l ℓ₂ ⊔l ℓ₃ ⊔l ℓ₄) where
    field
      idᴹ  : Tmsᴹ Γᴹ Γᴹ id
      _⨾ᴹ_ : Tmsᴹ Δᴹ Γᴹ δ → Tmsᴹ Θᴹ Δᴹ σ → Tmsᴹ Θᴹ Γᴹ (δ ⨾ σ)

      id⨾ᴹ : idᴹ ⨾ᴹ δᴹ ≡ δᴹ
      ⨾idᴹ : δᴹ ⨾ᴹ idᴹ ≡ δᴹ
      ⨾⨾ᴹ  : {Γᴹ : Ctxᴹ Γ} {Δᴹ : Ctxᴹ Δ} {Θᴹ : Ctxᴹ Θ} {Λᴹ : Ctxᴹ Λ} 
             {δᴹ : Tmsᴹ Δᴹ Γᴹ δ} {σᴹ : Tmsᴹ Θᴹ Δᴹ σ} {γᴹ : Tmsᴹ Λᴹ Θᴹ γ}   
           → (δᴹ ⨾ᴹ σᴹ) ⨾ᴹ γᴹ ≡ δᴹ ⨾ᴹ (σᴹ ⨾ᴹ γᴹ)

      _[_]Tᴹ : Tyᴹ Γᴹ A → Tmsᴹ Δᴹ Γᴹ δ → Tyᴹ Δᴹ (A [ δ ]T)
      _[_]ᴹ  : Tmᴹ Γᴹ Aᴹ t → (δᴹ : Tmsᴹ Δᴹ Γᴹ δ) 
              → Tmᴹ Δᴹ (Aᴹ [ δᴹ ]Tᴹ) (t [ δ ])

      [id]Tᴹ : Aᴹ [ idᴹ ]Tᴹ ≡ Aᴹ
      [id]ᴹ  : tᴹ [ idᴹ ]ᴹ ≡[ ap (λ □ → Tmᴹ Γᴹ □ t) ([id]Tᴹ {Aᴹ = Aᴹ}) ]≡ tᴹ
      [][]Tᴹ : Aᴹ [ δᴹ ]Tᴹ [ σᴹ ]Tᴹ ≡ Aᴹ [ δᴹ ⨾ᴹ σᴹ ]Tᴹ
      [][]ᴹ  : {tᴹ : Tmᴹ Γᴹ Aᴹ t} {δᴹ : Tmsᴹ Δᴹ Γᴹ δ} {σᴹ : Tmsᴹ Θᴹ Δᴹ σ}
              →  tᴹ [ δᴹ ]ᴹ [ σᴹ ]ᴹ 
              ≡[ ap (λ □ → Tmᴹ Θᴹ □ (t [ δ ⨾ σ ])) [][]Tᴹ 
              ]≡ tᴹ [ δᴹ ⨾ᴹ σᴹ ]ᴹ

      •ᴹ  : Ctxᴹ •
      εᴹ  : Tmsᴹ Δᴹ •ᴹ ε
      •ηᴹ : δᴹ ≡ εᴹ

      _▷ᴹ_ : ∀ Γᴹ → Tyᴹ Γᴹ A → Ctxᴹ (Γ ▷ A)
      _,ᴹ_ : (δᴹ : Tmsᴹ Δᴹ Γᴹ δ) → Tmᴹ Δᴹ (Aᴹ [ δᴹ ]Tᴹ) t 
            → Tmsᴹ Δᴹ (Γᴹ ▷ᴹ Aᴹ) (δ , t)
      pᴹ   : Tmsᴹ (Γᴹ ▷ᴹ Aᴹ) Γᴹ p
      qᴹ   : Tmᴹ (Γᴹ ▷ᴹ Aᴹ) (Aᴹ [ pᴹ ]Tᴹ) q
      ,⨾ᴹ  : {tᴹ : Tmᴹ Δᴹ (Aᴹ [ δᴹ ]Tᴹ) t} {σᴹ : Tmsᴹ Θᴹ Δᴹ σ}
           → (δᴹ ,ᴹ tᴹ) ⨾ᴹ σᴹ 
           ≡ (δᴹ ⨾ᴹ σᴹ) 
             ,ᴹ (transp (λ □ → Tmᴹ Θᴹ □ (t [ σ ])) [][]Tᴹ (tᴹ [ σᴹ ]ᴹ))
      p,ᴹ  : pᴹ ⨾ᴹ (δᴹ ,ᴹ tᴹ) ≡ δᴹ
      q,ᴹ  :  qᴹ [ δᴹ ,ᴹ tᴹ ]ᴹ 
            ≡[ ap (λ □ → Tmᴹ Δᴹ □ t) ([][]Tᴹ ∙ ap (Aᴹ [_]Tᴹ) p,ᴹ) 
            ]≡ tᴹ
      ▷ηᴹ  : {Γᴹ : Ctxᴹ Γ} {Δᴹ : Ctxᴹ Δ} {Aᴹ : Tyᴹ Γᴹ A} 
             {δᴹ : Tmsᴹ Δᴹ (Γᴹ ▷ᴹ Aᴹ) δ}
            →  δᴹ 
            ≡  (pᴹ ⨾ᴹ δᴹ) 
            ,ᴹ transp (λ □ → Tmᴹ Δᴹ □ (q [ δ ])) [][]Tᴹ (qᴹ [ δᴹ ]ᴹ)

    _^ᴹ_ : ∀ (δᴹ : Tmsᴹ Δᴹ Γᴹ δ) Aᴹ 
          → Tmsᴹ (Δᴹ ▷ᴹ (Aᴹ [ δᴹ ]Tᴹ)) (Γᴹ ▷ᴹ Aᴹ) (δ ^ A)
    δᴹ ^ᴹ Aᴹ = (δᴹ ⨾ᴹ pᴹ) ,ᴹ transp (λ □ → Tmᴹ _ □ q) [][]Tᴹ qᴹ

    field
      Πᴹ   : ∀ Aᴹ → Tyᴹ (Γᴹ ▷ᴹ Aᴹ) B → Tyᴹ {Γ = Γ} Γᴹ (Π A B)
      lamᴹ : Tmᴹ (Γᴹ ▷ᴹ Aᴹ) Bᴹ t → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) (lam t)
      appᴹ : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) t → Tmᴹ (Γᴹ ▷ᴹ Aᴹ) Bᴹ (app t)

      Π[]ᴹ   : Πᴹ {Γᴹ = Γᴹ} Aᴹ Bᴹ [ δᴹ ]Tᴹ 
             ≡ Πᴹ {Γᴹ = Δᴹ} (Aᴹ [ δᴹ ]Tᴹ) (Bᴹ [ δᴹ ^ᴹ Aᴹ ]Tᴹ)
      -- I avoid generalised variables here because typechecking is REALLY slow
      lam[]ᴹ : ∀ {Γ Δ A B t δ}
               {Γᴹ : Ctxᴹ Γ} {Δᴹ : Ctxᴹ Δ} 
               {Aᴹ : Tyᴹ Γᴹ A} {Bᴹ : Tyᴹ (Γᴹ ▷ᴹ Aᴹ) B}  
               {tᴹ : Tmᴹ (Γᴹ ▷ᴹ Aᴹ) Bᴹ t} {δᴹ : Tmsᴹ Δᴹ Γᴹ δ} 
              →  lamᴹ tᴹ [ δᴹ ]ᴹ 
              ≡[ ap (λ □ → Tmᴹ Δᴹ □ (lam (t [ δ ^ A ]))) Π[]ᴹ 
              ]≡ lamᴹ (tᴹ [ δᴹ ^ᴹ Aᴹ ]ᴹ)

      βᴹ : appᴹ {Γᴹ = Γᴹ} {Aᴹ = Aᴹ} {Bᴹ = Bᴹ} (lamᴹ tᴹ) ≡ tᴹ
      ηᴹ : tᴹ ≡[ ap (Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ)) η ]≡ lamᴹ (appᴹ tᴹ)

      ℤᴹ     : Tyᴹ Γᴹ ℤ
      zeᴹ    : Tmᴹ Γᴹ ℤᴹ ze
      suᴹ    : Tmᴹ Γᴹ ℤᴹ t → Tmᴹ Γᴹ ℤᴹ (su t)
      _-ᴹ_   : Tmᴹ Γᴹ ℤᴹ t → Tmᴹ Γᴹ ℤᴹ u → Tmᴹ Γᴹ ℤᴹ (t - u)
      IF-ZEᴹ : Tmᴹ Γᴹ ℤᴹ t → Tyᴹ Γᴹ A → Tyᴹ Γᴹ B → Tyᴹ Γᴹ (IF-ZE t A B)

      ℤ[]ᴹ  : ℤᴹ [ δᴹ ]Tᴹ ≡ ℤᴹ
      ze[]ᴹ : zeᴹ [ δᴹ ]ᴹ ≡[ ap (λ □ → Tmᴹ Δᴹ □ ze) ℤ[]ᴹ ]≡ zeᴹ
      su[]ᴹ : {tᴹ : Tmᴹ Γᴹ ℤᴹ t} {δᴹ : Tmsᴹ Δᴹ Γᴹ δ}
            →  suᴹ tᴹ [ δᴹ ]ᴹ 
            ≡[ ap (λ □ → Tmᴹ Δᴹ □ (su (t [ δ ]))) ℤ[]ᴹ
            ]≡ suᴹ (transp (λ □ → Tmᴹ Δᴹ □ (t [ δ ])) ℤ[]ᴹ (tᴹ [ δᴹ ]ᴹ))
      -[]ᴹ  : {tᴹ : Tmᴹ Γᴹ ℤᴹ t} {uᴹ : Tmᴹ Γᴹ ℤᴹ u} {δᴹ : Tmsᴹ Δᴹ Γᴹ δ}
            →  (tᴹ -ᴹ uᴹ) [ δᴹ ]ᴹ
            ≡[ ap (λ □ → Tmᴹ Δᴹ □ ((t [ δ ]) - (u [ δ ]))) ℤ[]ᴹ
            ]≡ (  (transp (λ □ → Tmᴹ Δᴹ □ (t [ δ ])) ℤ[]ᴹ (tᴹ [ δᴹ ]ᴹ))
                -ᴹ (transp (λ □ → Tmᴹ Δᴹ □ (u [ δ ])) ℤ[]ᴹ (uᴹ [ δᴹ ]ᴹ)))
      IF-ZE[]ᴹ : {tᴹ : Tmᴹ Γᴹ ℤᴹ t} {δᴹ : Tmsᴹ Δᴹ Γᴹ δ}
                → IF-ZEᴹ tᴹ Aᴹ Bᴹ [ δᴹ ]Tᴹ 
                ≡ IF-ZEᴹ (transp (λ □ → Tmᴹ Δᴹ □ (t [ δ ])) ℤ[]ᴹ (tᴹ [ δᴹ ]ᴹ)) 
                         (Aᴹ [ δᴹ ]Tᴹ) (Bᴹ [ δᴹ ]Tᴹ)

      -zeᴹ       : tᴹ -ᴹ zeᴹ ≡ tᴹ
      -cancelᴹ   : tᴹ -ᴹ tᴹ ≡ zeᴹ
      -suᴹ       : suᴹ tᴹ -ᴹ suᴹ uᴹ ≡ tᴹ -ᴹ uᴹ
      IF-ZE-zeᴹ  : IF-ZEᴹ zeᴹ Aᴹ Bᴹ ≡ Aᴹ
      IF-ZE-suᴹ  : IF-ZEᴹ (suᴹ tᴹ) Aᴹ Bᴹ ≡ Bᴹ
      -- IF-ZE-ze-ᴹ : IF-ZEᴹ (zeᴹ -ᴹ tᴹ) Aᴹ Bᴹ ≡ IF-ZEᴹ tᴹ Aᴹ Bᴹ

module _ {𝕄 : Motives ℓ₁ ℓ₂ ℓ₃ ℓ₄} (𝕞 : Methods 𝕄) where  
  open Motives 𝕄
  open Methods 𝕞
  
  postulate
    elimCtx : ∀ Γ → Ctxᴹ Γ
    elimTy  : ∀ A → Tyᴹ (elimCtx Γ) A
    elimTm  : ∀ t → Tmᴹ (elimCtx Γ) (elimTy A) t
    elimTms : ∀ δ → Tmsᴹ (elimCtx Δ) (elimCtx Γ) δ

    elim-id : elimTms (id {Γ = Γ}) ≡ idᴹ
    {-# REWRITE elim-id #-}
    elim-⨾  : elimTms (δ ⨾ σ) ≡ elimTms δ ⨾ᴹ elimTms σ
    {-# REWRITE elim-⨾ #-}

    elim-[]T : elimTy (A [ δ ]T) ≡ elimTy A [ elimTms δ ]Tᴹ
    {-# REWRITE elim-[]T #-}
    elim-[]  : elimTm (t [ δ ]) ≡ elimTm t [ elimTms δ ]ᴹ

    elim-• : elimCtx • ≡ •ᴹ
    {-# REWRITE elim-• #-}
    elim-ε : elimTms {Δ = Δ} ε ≡ εᴹ
    {-# REWRITE elim-ε #-}
    elim-▷ : elimCtx (Γ ▷ A) ≡ elimCtx Γ ▷ᴹ elimTy A
    {-# REWRITE elim-▷ #-}
    elim-, : elimTms (δ , t) ≡ elimTms δ ,ᴹ elimTm t
    {-# REWRITE elim-, #-}
    elim-p : elimTms (p {A = A}) ≡ pᴹ
    {-# REWRITE elim-p #-}
    elim-q : elimTm (q {Γ = Γ} {A = A}) ≡ qᴹ
    {-# REWRITE elim-q #-}

    elim-Π : elimTy (Π A B) ≡ Πᴹ (elimTy A) (elimTy B)
    {-# REWRITE elim-Π #-}
    elim-lam : elimTm (lam t) ≡ lamᴹ (elimTm t)
    {-# REWRITE elim-lam #-}
    elim-app : elimTm (app t) ≡ appᴹ (elimTm t)
    {-# REWRITE elim-app #-}

    elim-ℤ : elimTy (ℤ {Γ = Γ}) ≡ ℤᴹ
    {-# REWRITE elim-ℤ #-}
    elim-ze : elimTm (ze {Γ = Γ}) ≡ zeᴹ
    {-# REWRITE elim-ze #-}
    elim-su : elimTm (su t) ≡ suᴹ (elimTm t)
    {-# REWRITE elim-su #-}
    elim-- : elimTm (t - u) ≡ elimTm t -ᴹ elimTm u
    {-# REWRITE elim-- #-}
    elim-IF-ZE : elimTy (IF-ZE t A B) ≡ IF-ZEᴹ (elimTm t) (elimTy A) (elimTy B)
    {-# REWRITE elim-IF-ZE #-}

open Motives public
open Methods public
