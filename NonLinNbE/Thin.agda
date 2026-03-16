{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils renaming (_,_ to _Σ,_)
open import Utils.Prop

open import NonLinNbE.SyntaxEta
open import NonLinNbE.Nf

module NonLinNbE.Thin where

_⁺_ : Tms Δ Γ → ∀ A → Tms (Δ ▷ A) Γ
δ ⁺ A = δ ⨾ p

data RawThin : Nat → Nat → Set where
  εᴿ  : RawThin zero zero
  _^ᴿ : RawThin m n → RawThin (suc m) (suc n)
  _⁺ᴿ : RawThin m n → RawThin (suc m) n

variable
  δᴿ σᴿ γᴿ : RawThin _ _

idᴿ : RawThin n n
idᴿ {n = zero}  = εᴿ
idᴿ {n = suc n} = idᴿ ^ᴿ

_⨾ᴿ_ : RawThin m n → RawThin l m → RawThin l n
εᴿ      ⨾ᴿ σᴿ = σᴿ
(δᴿ ^ᴿ) ⨾ᴿ (σᴿ ^ᴿ) = (δᴿ ⨾ᴿ σᴿ) ^ᴿ
(δᴿ ⁺ᴿ) ⨾ᴿ (σᴿ ^ᴿ) = (δᴿ ⨾ᴿ σᴿ) ⁺ᴿ
δᴿ      ⨾ᴿ (σᴿ ⁺ᴿ) = (δᴿ ⨾ᴿ σᴿ) ⁺ᴿ

⨾⁺ : δᴿ ⨾ᴿ (σᴿ ⁺ᴿ) ≡ (δᴿ ⨾ᴿ σᴿ) ⁺ᴿ
⨾⁺ {δᴿ = εᴿ}    = refl
⨾⁺ {δᴿ = δᴿ ^ᴿ} = refl
⨾⁺ {δᴿ = δᴿ ⁺ᴿ} = refl
{-# REWRITE ⨾⁺ #-}

id⨾ᴿ : idᴿ ⨾ᴿ σᴿ ≡ σᴿ
id⨾ᴿ {σᴿ = εᴿ}    = refl
id⨾ᴿ {σᴿ = σᴿ ^ᴿ} = ap _^ᴿ id⨾ᴿ
id⨾ᴿ {σᴿ = σᴿ ⁺ᴿ} = ap _⁺ᴿ id⨾ᴿ

⨾idᴿ : δᴿ ⨾ᴿ idᴿ ≡ δᴿ
⨾idᴿ {δᴿ = εᴿ}    = refl
⨾idᴿ {δᴿ = δᴿ ^ᴿ} = ap _^ᴿ ⨾idᴿ
⨾idᴿ {δᴿ = δᴿ ⁺ᴿ} = ap _⁺ᴿ ⨾idᴿ

⨾⨾ᴿ : (δᴿ ⨾ᴿ σᴿ) ⨾ᴿ γᴿ ≡ δᴿ ⨾ᴿ (σᴿ ⨾ᴿ γᴿ)
⨾⨾ᴿ {δᴿ = εᴿ} = refl
⨾⨾ᴿ {δᴿ = δᴿ} {σᴿ = σᴿ} {γᴿ = γᴿ ⁺ᴿ} 
  = ap _⁺ᴿ (⨾⨾ᴿ {δᴿ = δᴿ} {σᴿ = σᴿ} {γᴿ = γᴿ})
⨾⨾ᴿ {δᴿ = δᴿ} {σᴿ = σᴿ ⁺ᴿ} {γᴿ = γᴿ ^ᴿ} 
  = ap _⁺ᴿ (⨾⨾ᴿ {δᴿ = δᴿ} {σᴿ = σᴿ} {γᴿ = γᴿ})
⨾⨾ᴿ {δᴿ = δᴿ ⁺ᴿ} {σᴿ = σᴿ ^ᴿ} {γᴿ = γᴿ ^ᴿ} 
  = ap _⁺ᴿ (⨾⨾ᴿ {δᴿ = δᴿ} {σᴿ = σᴿ} {γᴿ = γᴿ})
⨾⨾ᴿ {δᴿ = δᴿ ^ᴿ} {σᴿ = σᴿ ^ᴿ} {γᴿ = γᴿ ^ᴿ} 
  = ap _^ᴿ (⨾⨾ᴿ {δᴿ = δᴿ} {σᴿ = σᴿ} {γᴿ = γᴿ})

{-# REWRITE id⨾ᴿ ⨾idᴿ ⨾⨾ᴿ #-}

data IsThin : ∀ Δ Γ → Tms Δ Γ → RawThin (len Δ) (len Γ) → Prop where
  εC  : IsThin • • ε εᴿ
  _^C : IsThin Δ Γ δ δᴿ → IsThin (Δ ▷ (A [ δ ]T)) (Γ ▷ A) (δ ^ A) (δᴿ ^ᴿ)
  _⁺C : IsThin Δ Γ δ δᴿ → IsThin (Δ ▷ A) Γ (δ ⁺ A) (δᴿ ⁺ᴿ)

idC : IsThin Γ Γ id idᴿ
idC {Γ = •}     = εC
idC {Γ = Γ ▷ A} = idC ^C

_⨾C_ : IsThin Δ Γ δ δᴿ → IsThin Θ Δ σ σᴿ → IsThin Θ Γ (δ ⨾ σ) (δᴿ ⨾ᴿ σᴿ) 
εC      ⨾C σC      = σC
(δC ^C) ⨾C (σC ^C) = (δC ⨾C σC) ^C
(δC ⁺C) ⨾C (σC ^C) = (δC ⨾C σC) ⁺C
δC      ⨾C (σC ⁺C) = (δC ⨾C σC) ⁺C

variable
  t₁ᴿ t₂ᴿ u₁ᴿ u₂ᴿ : Raw _
  
lookupᴿ : RawVar n → RawThin m n → RawVar m
lookupᴿ xᴿ       (δᴿ ⁺ᴿ) = vsᴿ (lookupᴿ xᴿ δᴿ)
lookupᴿ vzᴿ      (δᴿ ^ᴿ) = vzᴿ
lookupᴿ (vsᴿ xᴿ) (δᴿ ^ᴿ) = vsᴿ (lookupᴿ xᴿ δᴿ)

_[_]ᴿ : Raw n → RawThin m n → Raw m
varᴿ tᴿ    [ δᴿ ]ᴿ = varᴿ (lookupᴿ tᴿ δᴿ)
neℤᴿ tᴿ    [ δᴿ ]ᴿ = neℤᴿ (tᴿ [ δᴿ ]ᴿ)
lamᴿ tᴿ    [ δᴿ ]ᴿ = lamᴿ (tᴿ [ δᴿ ^ᴿ ]ᴿ)
appᴿ tᴿ uᴿ [ δᴿ ]ᴿ = appᴿ (tᴿ [ δᴿ ]ᴿ) (uᴿ [ δᴿ ]ᴿ)
zeᴿ        [ δᴿ ]ᴿ = zeᴿ
suᴿ tᴿ     [ δᴿ ]ᴿ = suᴿ (tᴿ [ δᴿ ]ᴿ)
(tᴿ -ᴿ uᴿ) [ δᴿ ]ᴿ = (tᴿ [ δᴿ ]ᴿ) -ᴿ (uᴿ [ δᴿ ]ᴿ)

vsᴿ-inj : vsᴿ xᴿ ≡ vsᴿ yᴿ → xᴿ ≡ yᴿ
vsᴿ-inj refl = refl

varᴿ-inj : varᴿ xᴿ ≡ varᴿ yᴿ → xᴿ ≡ yᴿ
varᴿ-inj refl = refl

neℤᴿ-inj : neℤᴿ tᴿ ≡ neℤᴿ uᴿ → tᴿ ≡ uᴿ
neℤᴿ-inj refl = refl

lamᴿ-inj : lamᴿ tᴿ ≡ lamᴿ uᴿ → tᴿ ≡ uᴿ
lamᴿ-inj refl = refl

appᴿ-inj₁ : appᴿ t₁ᴿ t₂ᴿ ≡ appᴿ u₁ᴿ u₂ᴿ → t₁ᴿ ≡ u₁ᴿ
appᴿ-inj₁ refl = refl

appᴿ-inj₂ : appᴿ t₁ᴿ t₂ᴿ ≡ appᴿ u₁ᴿ u₂ᴿ → t₂ᴿ ≡ u₂ᴿ
appᴿ-inj₂ refl = refl

suᴿ-inj : suᴿ tᴿ ≡ suᴿ uᴿ → tᴿ ≡ uᴿ
suᴿ-inj refl = refl

-ᴿ-inj₁ : (t₁ᴿ -ᴿ t₂ᴿ) ≡ (u₁ᴿ -ᴿ u₂ᴿ) → t₁ᴿ ≡ u₁ᴿ
-ᴿ-inj₁ refl = refl

-ᴿ-inj₂ : (t₁ᴿ -ᴿ t₂ᴿ) ≡ (u₁ᴿ -ᴿ u₂ᴿ) → t₂ᴿ ≡ u₂ᴿ
-ᴿ-inj₂ refl = refl

lookupᴿ-inj : lookupᴿ xᴿ δᴿ ≡ lookupᴿ yᴿ δᴿ → xᴿ ≡ yᴿ
lookupᴿ-inj {δᴿ = δᴿ ⁺ᴿ} p 
  = lookupᴿ-inj (vsᴿ-inj p)
lookupᴿ-inj {xᴿ = vzᴿ} {δᴿ = δᴿ ^ᴿ} {yᴿ = vzᴿ} _ 
  = refl
lookupᴿ-inj {xᴿ = vsᴿ xᴿ} {δᴿ = δᴿ ^ᴿ} {yᴿ = vsᴿ yᴿ} p 
  = ap vsᴿ (lookupᴿ-inj (vsᴿ-inj p))

[]ᴿ-inj : tᴿ [ δᴿ ]ᴿ ≡ uᴿ [ δᴿ ]ᴿ → tᴿ ≡ uᴿ
[]ᴿ-inj {tᴿ = varᴿ x} {uᴿ = varᴿ y} p 
  = ap varᴿ (lookupᴿ-inj (varᴿ-inj p))
[]ᴿ-inj {tᴿ = neℤᴿ tᴿ} {uᴿ = neℤᴿ uᴿ} p 
  = ap neℤᴿ ([]ᴿ-inj (neℤᴿ-inj p))
[]ᴿ-inj {tᴿ = lamᴿ tᴿ} {uᴿ = lamᴿ uᴿ} p 
  = ap lamᴿ ([]ᴿ-inj (lamᴿ-inj p))
[]ᴿ-inj {tᴿ = appᴿ t₁ᴿ t₂ᴿ} {uᴿ = appᴿ u₁ᴿ u₂ᴿ} p 
  = ap₂ appᴿ ([]ᴿ-inj (appᴿ-inj₁ p)) ([]ᴿ-inj (appᴿ-inj₂ p))
[]ᴿ-inj {tᴿ = zeᴿ} {uᴿ = zeᴿ} p 
  = refl
[]ᴿ-inj {tᴿ = suᴿ tᴿ} {uᴿ = suᴿ uᴿ} p 
  = ap suᴿ ([]ᴿ-inj (suᴿ-inj p))
[]ᴿ-inj {tᴿ = t₁ᴿ -ᴿ t₂ᴿ} {uᴿ = u₁ᴿ -ᴿ u₂ᴿ} p 
  = ap₂ _-ᴿ_ ([]ᴿ-inj (-ᴿ-inj₁ p)) ([]ᴿ-inj (-ᴿ-inj₂ p))

_[_]VarC : VarCmpl Γ A t xᴿ → (δC : IsThin Δ Γ δ δᴿ) 
         → VarCmpl Δ (A [ δ ]T) (t [ δ ]) (lookupᴿ xᴿ δᴿ)
_[_]NeC : NeCmpl Γ A t tᴿ → (δC : IsThin Δ Γ δ δᴿ) 
        → NeCmpl Δ (A [ δ ]T) (t [ δ ]) (tᴿ [ δᴿ ]ᴿ)
_[_]NfC : NfCmpl Γ A t tᴿ → (δC : IsThin Δ Γ δ δᴿ) 
        → NfCmpl Δ (A [ δ ]T) (t [ δ ]) (tᴿ [ δᴿ ]ᴿ)
_[_]ℤC : ℤCmpl Γ t tᴿ → (δC : IsThin Δ Γ δ δᴿ) 
       → ℤCmpl Δ (t [ δ ]) (tᴿ [ δᴿ ]ᴿ)
_[_]ℤParC : ℤParCmpl Γ t tᴿ → (δC : IsThin Δ Γ δ δᴿ) 
          → ℤParCmpl Δ (t [ δ ]) (tᴿ [ δᴿ ]ᴿ)
      
xC     [ δC ⁺C ]VarC = vsC (xC [ δC ]VarC)
vzC    [ δC ^C ]VarC = vzC
vsC xC [ δC ^C ]VarC = vsC (xC [ δC ]VarC)

coe~ t~ tC   [ δC ]NeC = coe~ (ap~ (_[ _ ]) t~) (tC [ δC ]NeC)
varC xC      [ δC ]NeC = varC (xC [ δC ]VarC)
appC tC uC   [ δC ]NeC = appC (tC [ δC ]NeC) (uC [ δC ]NfC)
-neC tC uC p [ δC ]NeC 
  = -neC (tC [ δC ]NfC) (uC [ δC ]NeC) λ q → p ([]ᴿ-inj q)
ne-C tC uC   [ δC ]NeC = ne-C (tC [ δC ]NeC) (uC [ δC ]NfC)
ze-C uC      [ δC ]NeC = ze-C (uC [ δC ]NfC)

coe~ t~ tC      [ δC ]NfC = coe~ (ap~ (_[ _ ]) t~) (tC [ δC ]NfC)
lamC tC         [ δC ]NfC = lamC (tC [ δC ^C ]NfC)
valℤC tC        [ δC ]NfC = valℤC (tC [ δC ]ℤC)

parC tC [ δC ]ℤC = parC (tC [ δC ]ℤParC)
neC tC  [ δC ]ℤC = neC  (tC [ δC ]NeC)

coe~ t~ tC [ δC ]ℤParC = coe~ (ap~ (_[ _ ]) t~) (tC [ δC ]ℤParC)
zeC        [ δC ]ℤParC = zeC
suC tC     [ δC ]ℤParC = suC (tC [ δC ]ℤC)


Thin : ∀ Δ Γ → Tms Δ Γ → Set
Thin Δ Γ δ = ∃ (RawThin (len Δ) (len Γ)) (IsThin Δ Γ δ)

_⁺Th_ : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ A) Γ (δ ⁺ A)
(δᴿ ∃, δC) ⁺Th A = (δᴿ ⁺ᴿ) ∃, (δC ⁺C)

_^Th_ : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ (A [ δ ]T)) (Γ ▷ A) (δ ^ A)
(δᴿ ∃, δC) ^Th A = (δᴿ ^ᴿ) ∃, (δC ^C)

idTh : Thin Γ Γ id
idTh = idᴿ ∃, idC

_⨾Th_ : Thin Δ Γ δ → Thin Θ Δ σ → Thin Θ Γ (δ ⨾ σ)
(δᴿ ∃, δC) ⨾Th (σᴿ ∃, σC) = (δᴿ ⨾ᴿ σᴿ) ∃, (δC ⨾C σC)

variable
  δTh σTh γTh : Thin _ _ _

_[_]Ne : Ne Γ A t → Thin Δ Γ δ → Ne Δ (A [ δ ]T) (t [ δ ])
_[_]Nf : Nf Γ A t → Thin Δ Γ δ → Nf Δ (A [ δ ]T) (t [ δ ])
_[_]ℤ  : ℤVal Γ t → Thin Δ Γ δ → ℤVal Δ (t [ δ ])

(tᴿ ∃, tC) [ (δᴿ ∃, δC) ]Ne = (tᴿ [ δᴿ ]ᴿ) ∃, (tC [ δC ]NeC)
(tᴿ ∃, tC) [ (δᴿ ∃, δC) ]Nf = (tᴿ [ δᴿ ]ᴿ) ∃, (tC [ δC ]NfC)
(tᴿ ∃, tC) [ (δᴿ ∃, δC) ]ℤ  = (tᴿ [ δᴿ ]ᴿ) ∃, (tC [ δC ]ℤC)

variable
  tᴺᶠ uᴺᶠ : Nf Γ A t
  tᴺᵉ uᴺᵉ : Ne Γ A t

lookup-idᴿ : lookupᴿ xᴿ (idᴿ {n = n}) ≡ xᴿ 
lookup-idᴿ {n = suc n} {xᴿ = vzᴿ}    = refl
lookup-idᴿ {n = suc n} {xᴿ = vsᴿ xᴿ} = ap vsᴿ lookup-idᴿ

[id]ᴿ : tᴿ [ idᴿ ]ᴿ ≡ tᴿ
[id]ᴿ {tᴿ = varᴿ xᴿ}    = ap varᴿ lookup-idᴿ
[id]ᴿ {tᴿ = neℤᴿ tᴿ}    = ap neℤᴿ [id]ᴿ
[id]ᴿ {tᴿ = lamᴿ tᴿ}    = ap lamᴿ [id]ᴿ
[id]ᴿ {tᴿ = appᴿ tᴿ uᴿ} = ap₂ appᴿ [id]ᴿ [id]ᴿ
[id]ᴿ {tᴿ = zeᴿ}        = refl
[id]ᴿ {tᴿ = suᴿ tᴿ}     = ap suᴿ [id]ᴿ
[id]ᴿ {tᴿ = tᴿ -ᴿ uᴿ}   = ap₂ _-ᴿ_ [id]ᴿ [id]ᴿ

lookup-lookupᴿ : lookupᴿ (lookupᴿ xᴿ δᴿ) σᴿ ≡ lookupᴿ xᴿ (δᴿ ⨾ᴿ σᴿ)
lookup-lookupᴿ {δᴿ = δᴿ ⁺ᴿ} {σᴿ = σᴿ ^ᴿ} 
  = ap vsᴿ lookup-lookupᴿ
lookup-lookupᴿ {δᴿ = δᴿ ⁺ᴿ} {σᴿ = σᴿ ⁺ᴿ} 
  = ap vsᴿ (lookup-lookupᴿ {δᴿ = δᴿ ⁺ᴿ})
lookup-lookupᴿ {xᴿ = vzᴿ} {δᴿ = δᴿ ^ᴿ} {σᴿ = σᴿ ^ᴿ} 
  = refl
lookup-lookupᴿ {xᴿ = vzᴿ} {δᴿ = δᴿ ^ᴿ} {σᴿ = σᴿ ⁺ᴿ} 
  = ap vsᴿ lookup-lookupᴿ
lookup-lookupᴿ {xᴿ = vsᴿ xᴿ} {δᴿ = δᴿ ^ᴿ} {σᴿ = σᴿ ^ᴿ} 
  = ap vsᴿ lookup-lookupᴿ
lookup-lookupᴿ {xᴿ = vsᴿ xᴿ} {δᴿ = δᴿ ^ᴿ} {σᴿ = σᴿ ⁺ᴿ} 
  = ap vsᴿ (lookup-lookupᴿ {δᴿ = δᴿ ^ᴿ})

[][]ᴿ : tᴿ [ δᴿ ]ᴿ [ σᴿ ]ᴿ ≡ tᴿ [ δᴿ ⨾ᴿ σᴿ ]ᴿ
[][]ᴿ {tᴿ = varᴿ x}     = ap varᴿ lookup-lookupᴿ
[][]ᴿ {tᴿ = neℤᴿ tᴿ}    = ap neℤᴿ [][]ᴿ
[][]ᴿ {tᴿ = lamᴿ tᴿ}    = ap lamᴿ [][]ᴿ
[][]ᴿ {tᴿ = appᴿ tᴿ uᴿ} = ap₂ appᴿ [][]ᴿ [][]ᴿ
[][]ᴿ {tᴿ = zeᴿ}        = refl
[][]ᴿ {tᴿ = suᴿ tᴿ}     = ap suᴿ [][]ᴿ
[][]ᴿ {tᴿ = tᴿ -ᴿ uᴿ}   = ap₂ _-ᴿ_ [][]ᴿ [][]ᴿ

{-# REWRITE lookup-idᴿ [id]ᴿ lookup-lookupᴿ [][]ᴿ #-}
