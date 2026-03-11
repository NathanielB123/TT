{-# OPTIONS --rewriting -WnoRewriteVariablesBoundInSingleton #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils renaming (_,_ to _Σ,_)

-- We postulate a strictified syntax and induction principle
module NonLinNbE.SyntaxEta where

data Ctx : Set
postulate
  Ty  : Ctx → Set
  Tm  : ∀ Γ → Ty Γ → Set

-- Hack to get definitional injectivity of and η for substitutions
Tms' : Ctx → Ctx → Set

record Tms (Δ : Ctx) (Γ : Ctx) : Set where
  constructor ⟪_⟫
  eta-equality
  inductive
  field
    tms : Tms' Δ Γ
open Tms

variable  
  Γ Δ Θ Λ Γ₁ Γ₂ Δ₁ Δ₂ Θ₁ Θ₂ : Ctx
  A B A₁ A₂ B₁ B₂ : Ty _
  t u v t₁ t₂ : Tm _ _
  δ σ γ : Tms _ _

data Ctx where
  •   : Ctx
  _▷_ : ∀ Γ → Ty Γ → Ctx

postulate
  _[_]T : Ty Γ → Tms Δ Γ → Ty Δ
  _[_]  : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)

record Tms• (Δ : Ctx) : Set where
  constructor ε'
  eta-equality

record Tms▷ (Δ : Ctx) (Γ : Ctx) (A : Ty Γ) : Set where
  constructor _,'_
  eta-equality
  inductive
  field
    π₁' : Tms Δ Γ
    π₂' : Tm Δ (A [ π₁' ]T)
open Tms▷

pattern ε       = ⟪ ε' ⟫ 
pattern _,_ δ t = ⟪ δ ,' t ⟫

Tms' Δ •       = Tms• Δ
Tms' Δ (Γ ▷ A) = Tms▷ Δ Γ A

π₁ : Tms Δ (Γ ▷ A) → Tms Δ Γ
π₁ δ = δ .tms .π₁'
{-# INLINE π₁ #-}

π₂ : (δ : Tms Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
π₂ δ = δ .tms .π₂'
{-# INLINE π₂ #-}

postulate
  id  : Tms Γ Γ
  _⨾_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ

  id⨾ : id ⨾ δ ≡ δ
  {-# REWRITE id⨾ #-}
  ⨾id : δ ⨾ id ≡ δ
  {-# REWRITE ⨾id #-}
  ⨾⨾  : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
  {-# REWRITE ⨾⨾ #-}

  [id]T : A [ id ]T ≡ A
  {-# REWRITE [id]T #-}
  [id]  : t [ id ] ≡ t
  {-# REWRITE [id] #-}
  [][]T : A [ δ ]T [ σ ]T ≡ A [ δ ⨾ σ ]T
  {-# REWRITE [][]T #-}
  [][]  : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]

[][]' : _[_] {A = ⟨ _ ⟩} (t [ δ ]) σ ≡ t [ δ ⨾ σ ]
[][]' {t = t} {δ = δ} = [][] {t = t} {δ = δ}
{-# REWRITE [][]' #-}

•η  : δ ≡ ε
•η = refl

p : Tms (Γ ▷ A) Γ
p = π₁ id
{-# INLINE p #-}

q : Tm (Γ ▷ A) (A [ p ]T) 
q = π₂ id
{-# INLINE q #-}

postulate
  ,⨾ : (δ , t) ⨾ σ ≡ (δ ⨾ σ) , (t [ σ ])
  {-# REWRITE ,⨾ #-}

  p,  : p ⨾ (δ , t) ≡ δ
  {-# REWRITE p, #-}

  q,  : q [ δ , t ] ≡ t

q,' : _[_] {A = ⟨ _ ⟩} q (δ , t) ≡ t
q,' = q,
{-# REWRITE q,' #-}

▷η  : δ ≡ (p ⨾ δ) , (q [ δ ])
▷η = refl

_^_ : ∀ δ A → Tms (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
δ ^ A = (δ ⨾ p) , q

postulate
  -- Π types
  Π     : ∀ A → Ty (Γ ▷ A) → Ty Γ
  lam   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → Tm (Γ ▷ A) B

  Π[]   : Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Π[] #-}
  lam[] : lam t [ δ ] ≡ lam (t [ δ ^ A ])
  {-# REWRITE lam[] #-}

  β : app (lam t) ≡ t
  {-# REWRITE β #-}
  η : t ≡ lam (app t)

app[] : {t : Tm Γ (Π A B)} → app (t [ δ ]) ≡ app t [ δ ^ A ]
app[] {A = A} {δ = δ} {t = t} = 
  app (t [ δ ])
  ≡⟨ ap {x = t} (λ □ → app (□ [ δ ])) η ⟩
  app ((lam (app t)) [ δ ])
  ≡⟨⟩  
  app t [ δ ^ A ] ∎

app[]' : {t : Tm Γ (Π A B)} 
       → app {A = ⟨ _ ⟩} {B = ⟨ _ ⟩} (t [ δ ]) ≡ app t [ δ ^ A ]
app[]' {t = t} = app[] {t = t}
{-# REWRITE app[]' #-}

η' : lam (app t) ≡ t
η' = sym η
{-# REWRITE η' #-}

postulate
  -- An example type with a non-linear reduction rule
  ℤ   : Ty Γ
  ze  : Tm Γ ℤ
  su  : Tm Γ ℤ → Tm Γ ℤ
  _-_ : Tm Γ ℤ → Tm Γ ℤ → Tm Γ ℤ
  IF-ZE : Tm Γ ℤ → Ty Γ → Ty Γ → Ty Γ

  ℤ[]  : ℤ [ δ ]T ≡ ℤ
  {-# REWRITE ℤ[] #-}
  ze[] : ze [ δ ] ≡ ze
  {-# REWRITE ze[] #-}
  su[] : su t [ δ ] ≡ su (t [ δ ])
  {-# REWRITE su[] #-}
  -[]  : (t - u) [ δ ] ≡ (t [ δ ]) - (u [ δ ])
  {-# REWRITE -[] #-}
  IF-ZE[] : IF-ZE t A B [ δ ]T ≡ IF-ZE (t [ δ ]) (A [ δ ]T) (B [ δ ]T)
  {-# REWRITE IF-ZE[] #-}

  -- This is not a complete set of equations, but it should be enough to make
  -- things interesting
  -ze       : t - ze ≡ t
  {-# REWRITE -ze #-}
  -cancel   : t - t ≡ ze
  {-# REWRITE -cancel #-}
  -su       : su t - su u ≡ t - u
  {-# REWRITE -su #-}
  IF-ZE-ze  : IF-ZE ze A B ≡ A
  {-# REWRITE IF-ZE-ze #-}
  IF-ZE-su  : IF-ZE (su t) A B ≡ B
  {-# REWRITE IF-ZE-su #-}
  IF-ZE-ze- : IF-ZE (ze - t) A B ≡ IF-ZE t A B
  {-# REWRITE IF-ZE-ze- #-}

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
      Πᴹ   : ∀ Aᴹ → Tyᴹ (Γᴹ ▷ᴹ Aᴹ) B → Tyᴹ Γᴹ (Π A B)
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

      βᴹ : appᴹ (lamᴹ tᴹ) ≡ tᴹ
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
      IF-ZE-ze-ᴹ : IF-ZEᴹ (zeᴹ -ᴹ tᴹ) Aᴹ Bᴹ ≡ IF-ZEᴹ tᴹ Aᴹ Bᴹ

module _ {𝕄 : Motives ℓ₁ ℓ₂ ℓ₃ ℓ₄} (𝕞 : Methods 𝕄) where  
  open Motives 𝕄
  open Methods 𝕞
  postulate
    elimCtx : ∀ Γ → Ctxᴹ Γ
    elimTy  : ∀ A → Tyᴹ (elimCtx Γ) A
    elimTm  : ∀ t → Tmᴹ (elimCtx Γ) (elimTy A) t
    elimTms : ∀ δ → Tmsᴹ (elimCtx Δ) (elimCtx Γ) δ

open Motives public
open Methods public
