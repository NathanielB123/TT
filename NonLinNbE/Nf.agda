{-# OPTIONS --rewriting #-}

open import Utils renaming (_,_ to _Σ,_)

open import NonLinNbE.SyntaxEta 

module NonLinNbE.Nf where

-- We define neutral and normal forms in a slightly unusual way
-- The idea is twofold:
-- * We need to be able to syntactically compare normal/neutral forms during
--   NbE (when we don't yet have injectivity of type formers)
-- * We need to relax completeness such that we can actually take advantage
--   of these syntactic normal/neutral comparisons

-- Raw syntax of normal forms
data Raw : Set where
  vzᴿ  : Raw
  vsᴿ  : Raw → Raw
  varᴿ : Raw → Raw
  neℤᴿ : Raw → Raw
  
  lamᴿ : Raw → Raw
  appᴿ : Raw → Raw → Raw

  zeᴿ  : Raw
  suᴿ  : Raw → Raw
  _-ᴿ_ : Raw → Raw → Raw

variable
  tᴿ uᴿ vᴿ : Raw

-- Implementing this is very standard (I'll do it at some point!)
postulate
  _≟_ : (tᴿ uᴿ : Raw) → Dec (tᴿ ≡ uᴿ)

-- Relaxed convertibility
data _~_ : Tm Γ A → Tm Γ A → Set

-- Variable/neutral/normal form predicates
data VarCmpl  : ∀ Γ A → Tm Γ A → Raw → Set
data NeCmpl   : ∀ Γ A → Tm Γ A → Raw → Set
data NfCmpl   : ∀ Γ A → Tm Γ A → Raw → Set
data ℤParCmpl : ∀ Γ → Tm Γ ℤ → Raw → Set
data ℤCmpl    : ∀ Γ → Tm Γ ℤ → Raw → Set

data _~_ where
  rfl~ : t ~ t
  sym~ : t₁ ~ t₂ → t₂ ~ t₁
  _∙~_ : t₁ ~ t₂ → t₂ ~ t₃ → t₁ ~ t₃

  ap~  : (f : Tm Γ A → Tm Δ B) → t₁ ~ t₂ → f t₁ ~ f t₂
  -- Relaxed neutral convertibility
  -- I think we have quite a bit of flexibility w.r.t. how much to relax.
  -- E.g. we could have relaxed convertibility of ℤ-typed neutrals only.
  ne~  : NeCmpl Γ A t₁ tᴿ → NeCmpl Γ A t₂ tᴿ → t₁ ~ t₂

data VarCmpl where
  vzC : VarCmpl (Γ ▷ A) (A [ p ]T) q vzᴿ
  vsC : VarCmpl Γ A t tᴿ 
      → VarCmpl (Γ ▷ B) (A [ p ]T) (t [ p ]) (vsᴿ tᴿ)

data NeCmpl where
  coe~ : t₁ ~ t₂ → NeCmpl Γ A t₁ tᴿ → NeCmpl Γ A t₂ tᴿ
  varC : VarCmpl Γ A t tᴿ → NeCmpl Γ A t (varᴿ tᴿ)
  appC : NeCmpl Γ (Π A B) t tᴿ → NfCmpl Γ A u uᴿ 
        → NeCmpl Γ (B [ id , u ]T) (app t [ id , u ]) (appᴿ tᴿ uᴿ)
  -- LHS is normal but RHS is neutral
  -- OR both sides are neutral and not convertible
  -neC : NfCmpl Γ ℤ t tᴿ → NeCmpl Γ ℤ u uᴿ
       → (tᴿ ≡ neℤᴿ uᴿ → 𝟘) → NeCmpl Γ ℤ (t - u) (tᴿ -ᴿ neℤᴿ uᴿ)
  -- LHS is neutral and RHS is successor of something
  ne-C : NeCmpl Γ ℤ t tᴿ → NfCmpl Γ ℤ u uᴿ
       → NeCmpl Γ ℤ (t - su u) (tᴿ -ᴿ suᴿ uᴿ)
  -- LHS is zero and RHS is successor of something
  ze-C : NfCmpl Γ ℤ u uᴿ → NeCmpl Γ ℤ (ze - su u) (zeᴿ -ᴿ suᴿ uᴿ)

data NfCmpl where 
  coe~  : t₁ ~ t₂ → NfCmpl Γ A t₁ tᴿ → NfCmpl Γ A t₂ tᴿ
  lamC  : NfCmpl (Γ ▷ A) B t tᴿ → NfCmpl Γ (Π A B) (lam t) (lamᴿ tᴿ)
  valℤC : ℤCmpl Γ t tᴿ → NfCmpl Γ ℤ t tᴿ

-- Constructor-headed ℤ-typed value
data ℤParCmpl where
  coe~   : t₁ ~ t₂ → ℤParCmpl Γ t₁ tᴿ → ℤParCmpl Γ t₂ tᴿ 
  zeC    : ℤParCmpl Γ ze zeᴿ
  suC    : ℤCmpl Γ t tᴿ → ℤParCmpl Γ (su t) (suᴿ tᴿ)

-- Possibly-neutral ℤ-typed value
data ℤCmpl where
  parC : ℤParCmpl Γ t tᴿ → ℤCmpl Γ t tᴿ
  neC  : NeCmpl Γ ℤ t tᴿ → ℤCmpl Γ t (neℤᴿ tᴿ)

Var : ∀ Γ A → Tm Γ A → Set
Var Γ A t = Σ Raw (VarCmpl Γ A t)

Ne : ∀ Γ A → Tm Γ A → Set
Ne Γ A t = Σ Raw (NeCmpl Γ A t)

Nf : ∀ Γ A → Tm Γ A → Set
Nf Γ A t = Σ Raw (NfCmpl Γ A t)

ℤPar : ∀ Γ → Tm Γ ℤ → Set
ℤPar Γ t = Σ Raw (ℤParCmpl Γ t)

ℤVal : ∀ Γ → Tm Γ ℤ → Set
ℤVal Γ t = Σ Raw (ℤCmpl Γ t)

pattern parⱽ tᴿ tC = tᴿ      Σ, parC tC
pattern neℤⱽ tᴿ tC = neℤᴿ tᴿ Σ, neC  tC
pattern zeᴾ        = zeᴿ Σ, zeC
pattern suᴾ tᴿ tC  = suᴿ tᴿ Σ, suC tC

zeⱽ : ℤVal Γ ze
zeⱽ = zeᴿ Σ, parC zeC

suⱽ : ℤVal Γ t → ℤVal Γ (su t)
suⱽ (tᴿ Σ, tC) = suᴿ tᴿ Σ, parC (suC tC)

coeℤ~ : t₁ ~ t₂ → ℤVal Γ t₁ → ℤVal Γ t₂
coeℤ~ t~ (tᴿ      Σ, parC tC) = tᴿ      Σ, parC (coe~ t~ tC)
coeℤ~ t~ (neℤᴿ tᴿ Σ, neC  tC) = neℤᴿ tᴿ Σ, neC  (coe~ t~ tC)

-- Relaxed version of the non-linear '-cancel' conversion rule
-cancel~ : NeCmpl Γ ℤ t₁ tᴿ → NeCmpl Γ ℤ t₂ tᴿ → (t₁ - t₂) ~ ze
-cancel~ {t₁ = t₁} {t₂ = t₂} t₁C t₂C = ap~ (_- t₂) (ne~ t₁C t₂C)

ℤ/ne : ℤParCmpl Γ t₁ (neℤᴿ tᴿ) → NeCmpl Γ ℤ t₂ tᴿ → 𝟘
ℤ/ne (coe~ _ tC₁) tC₂ = ℤ/ne tC₁ tC₂

-- The decomposition into helpers in needed to ensure termination
_-ⱽ_  : ℤVal Γ t → ℤVal Γ u → ℤVal Γ (t - u)
_ⱽ-ᴾ_ : ℤVal Γ t → ℤPar Γ u → ℤVal Γ (t - u)
_ᴾ-ⱽ_ : ℤPar Γ t → ℤVal Γ u → ℤVal Γ (t - u)
_ᴾ-ᴾ_ : ℤPar Γ t → ℤPar Γ u → ℤVal Γ (t - u)

tⱽ         -ⱽ parⱽ uᴿ uC = tⱽ ⱽ-ᴾ (uᴿ Σ, uC)
parⱽ tᴿ tC -ⱽ uⱽ         = (tᴿ Σ, tC) ᴾ-ⱽ uⱽ
neℤⱽ tᴿ tC -ⱽ neℤⱽ uᴿ uC with tᴿ ≟ uᴿ 
... | yes refl = coeℤ~ (sym~ (-cancel~ tC uC)) (zeᴿ Σ, parC zeC)
... | no  p    = _ Σ, neC (-neC (valℤC (neC tC)) uC λ where refl → p refl)

tⱽ         ⱽ-ᴾ zeᴾ       = tⱽ
neℤⱽ tᴿ tC ⱽ-ᴾ suᴾ uᴿ uC 
  = neℤⱽ (tᴿ -ᴿ suᴿ uᴿ) (ne-C tC (valℤC uC))
parⱽ tᴿ tC ⱽ-ᴾ uⱽ = (tᴿ Σ, tC) ᴾ-ᴾ uⱽ

_ⱽ-ᴾ_ {t = t} tⱽ (uᴿ Σ, coe~ u~ uC) 
  = coeℤ~ (ap~ (t -_) u~) (tⱽ ⱽ-ᴾ (uᴿ Σ, uC))

tⱽ         ᴾ-ⱽ parⱽ uᴿ uC = tⱽ ᴾ-ᴾ (uᴿ Σ, uC)
(tᴿ Σ, tC) ᴾ-ⱽ neℤⱽ uᴿ uC 
  = neℤⱽ _ (-neC (valℤC (parC tC)) uC λ where refl → ℤ/ne tC uC)

(tᴿ Σ, tC) ᴾ-ᴾ zeᴾ       = parⱽ tᴿ tC
suᴾ tᴿ tC  ᴾ-ᴾ suᴾ uᴿ uC = (tᴿ Σ, tC) -ⱽ (uᴿ Σ, uC)
zeᴾ        ᴾ-ᴾ suᴾ uᴿ uC = neℤⱽ (zeᴿ -ᴿ suᴿ uᴿ) (ze-C (valℤC uC))

_ᴾ-ᴾ_ {u = u} (tᴿ Σ, coe~ t~ tC) uⱽ 
  = coeℤ~ (ap~ (_- u) t~) ((tᴿ Σ, tC) ᴾ-ᴾ uⱽ)
_ᴾ-ᴾ_ {t = t} tⱽ (uᴿ Σ, coe~ u~ uC) 
  = coeℤ~ (ap~ (t -_) u~) (tⱽ ᴾ-ᴾ (uᴿ Σ, uC))
