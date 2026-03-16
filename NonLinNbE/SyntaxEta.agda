{-# OPTIONS --rewriting -WnoRewriteVariablesBoundInSingleton #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils renaming (_,_ to _Σ,_)

-- We postulate a strictified syntax and induction principle
module NonLinNbE.SyntaxEta where

data Ctx : Set
postulate
  Ty  : Ctx → Set
  Tm  : ∀ Γ → Ty Γ → Set

-- Hack to get η for substitutions
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
  t u v t₁ t₂ t₃ : Tm _ _
  δ σ γ δ₁ δ₂ : Tms _ _

-- We define contexts as a datatype to get disjointness and injectivity of
-- constructors during pattern-matching
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
