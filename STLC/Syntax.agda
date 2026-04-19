{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Minimal postulated STLC syntax as a QIT
-- Uses explicit variables and substitutions encoded as functions (I'm not
-- convinced this is actually a good idea, but I wanted to try it out)
module STLC.Syntax where

module Utils where
  infix 4 _≡[_]≡_
  
  private variable
    A B : Set _
    x y : A

  _≡[_]≡_ : A → A ≡ B → B → Set _
  x ≡[ refl ]≡ y = x ≡ y

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl

open Utils

data Ty : Set where
  *   : Ty
  _⇒_ : Ty → Ty → Ty

data Ctx : Set where
  •   : Ctx
  _▷_ : Ctx → Ty → Ctx

variable
  Γ Δ Θ : Ctx
  A B C : Ty

data Var : Ctx → Ty → Set where
  vz : Var (Γ ▷ A) A
  vs : Var Γ A → Var (Γ ▷ B) A

postulate
  Tm : Ctx → Ty → Set

Sub : Ctx → Ctx → Set
Sub Δ Γ = ∀ {A} → Var Γ A → Tm Δ A

variable
  i j k : Var _ _
  t u v : Tm _ _
  δ σ γ : Sub _ _

-- Constructors of 'Tm'
postulate
  var : Var Γ A → Tm Γ A
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  lam : Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)

  _[_]  : Tm Γ A → Sub Δ Γ → Tm Δ A

id : Sub Γ Γ
id = var

_,_ : Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▷ A)
(δ , t) vz     = t
(δ , t) (vs i) = δ i

wk : Sub (Γ ▷ A) Γ
wk i = var (vs i)

_⁺_ : Sub Δ Γ → ∀ A → Sub (Δ ▷ A) Γ
(δ ⁺ A) i = δ i [ wk ]

_^_ : Sub Δ Γ → ∀ A → Sub (Δ ▷ A) (Γ ▷ A)
δ ^ A = (δ ⁺ A) , var vz

-- Path constructors of 'Tm'
postulate
  var[] : var i [ δ ] ≡ δ i
  app[] : app t u [ δ ] ≡ app (t [ δ ]) (u [ δ ])
  lam[] : lam t [ δ ] ≡ lam (t [ δ ^ A ])
  
  -- Technically these substitution laws are path constructors and so should
  -- only be propositional, but I think making them compute is very convenient
  -- and it doesn't break much
  {-# REWRITE var[] #-}
  {-# REWRITE app[] #-}
  {-# REWRITE lam[] #-}

  β : app (lam t) u ≡ t [ id , u ]
  η : t ≡ lam (app (t [ wk ]) (var vz))

Motive : Set₁
Motive = ∀ Γ A → Tm Γ A → Set

record Methods (Tmᴹ : Motive) : Set where
  field
    varᴹ : (i : Var Γ A) → Tmᴹ Γ A (var i)
    appᴹ : Tmᴹ Γ (A ⇒ B) t → Tmᴹ Γ A u → Tmᴹ Γ B (app t u)
    lamᴹ : Tmᴹ (Γ ▷ A) B t → Tmᴹ Γ (A ⇒ B) (lam t)

  Subᴹ : (Δ Γ : Ctx) → Sub Δ Γ → Set
  Subᴹ Δ Γ δ = ∀ {A} → (i : Var Γ A) → Tmᴹ Δ A (δ i) 

  idᴹ : Subᴹ Γ Γ id
  idᴹ = varᴹ

  _,ᴹ_ : Subᴹ Δ Γ δ → Tmᴹ Δ A t → Subᴹ Δ (Γ ▷ A) (δ , t)
  (δᴹ ,ᴹ tᴹ) = λ where vz     → tᴹ
                       (vs i) → δᴹ i

  wkᴹ : Subᴹ (Γ ▷ A) Γ wk
  wkᴹ i = varᴹ (vs i)

  field
    _[_]ᴹ : Tmᴹ Γ A t → Subᴹ Δ Γ δ → Tmᴹ Δ A (t [ δ ])

  _⁺ᴹ_ : Subᴹ Δ Γ δ → ∀ A → Subᴹ (Δ ▷ A) Γ (δ ⁺ A)
  (δᴹ ⁺ᴹ A) i = δᴹ i [ wkᴹ ]ᴹ

  _^ᴹ_ : Subᴹ Δ Γ δ → ∀ A → Subᴹ (Δ ▷ A) (Γ ▷ A) (δ ^ A)
  δᴹ ^ᴹ A = (δᴹ ⁺ᴹ A) ,ᴹ varᴹ vz

  field
    var[]ᴹ : ∀ {δᴹ : Subᴹ Δ Γ δ} 
           → varᴹ i [ δᴹ ]ᴹ ≡ δᴹ i
    app[]ᴹ : ∀ {δᴹ : Subᴹ Δ Γ δ} {tᴹ : Tmᴹ Γ (A ⇒ B) t} {uᴹ : Tmᴹ Γ A u}
           → appᴹ tᴹ uᴹ [ δᴹ ]ᴹ ≡ appᴹ (tᴹ [ δᴹ ]ᴹ) (uᴹ [ δᴹ ]ᴹ)
    lam[]ᴹ : ∀ {δᴹ : Subᴹ Δ Γ δ} {tᴹ : Tmᴹ (Γ ▷ A) B t}
           → lamᴹ tᴹ [ δᴹ ]ᴹ ≡ lamᴹ (tᴹ [ δᴹ ^ᴹ A ]ᴹ)

    βᴹ : ∀ {tᴹ : Tmᴹ (Γ ▷ A) B t} {uᴹ : Tmᴹ Γ A u}
       → appᴹ (lamᴹ tᴹ) uᴹ ≡[ ap (Tmᴹ Γ B) β ]≡ tᴹ [ idᴹ ,ᴹ uᴹ ]ᴹ

    ηᴹ : ∀ {tᴹ : Tmᴹ Γ (A ⇒ B) t}
       → tᴹ ≡[ ap (Tmᴹ Γ (A ⇒ B)) η ]≡ lamᴹ (appᴹ (tᴹ [ wkᴹ ]ᴹ) (varᴹ vz))

-- Eliminator
module _ (Tmᴹ : Motive) (𝕞 : Methods Tmᴹ) where
  open Methods 𝕞
  postulate
    elimTm  : ∀ t → Tmᴹ Γ A t

  elimSub : ∀ (δ : Sub Δ Γ) → Subᴹ Δ Γ δ
  elimSub δ i = elimTm (δ i)
  
  postulate
    elimTm-var : elimTm (var i) ≡ varᴹ i
    {-# REWRITE elimTm-var #-}
    elimTm-app : elimTm (app t u) ≡ appᴹ (elimTm t) (elimTm u)
    {-# REWRITE elimTm-app #-}
    elimTm-lam : elimTm (lam t) ≡ lamᴹ (elimTm t)
    {-# REWRITE elimTm-lam #-}
    elimTm-[]  : elimTm (t [ δ ]) ≡ elimTm t [ elimSub δ ]ᴹ
    {-# REWRITE elimTm-[] #-}
