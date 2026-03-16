{-# OPTIONS --rewriting --prop #-}

open import Utils renaming (_,_ to _Σ,_)
open import Utils.STrunc
open import Utils.WithK

open import NonLinNbE.SyntaxEta 

module NonLinNbE.Nf where

variable
  n m l : Nat

len : Ctx → Nat
len •       = zero
len (Γ ▷ A) = suc (len Γ)

-- We define neutral and normal forms in a slightly unusual way
-- The idea is twofold:
-- * We need to be able to syntactically compare normal/neutral forms during
--   NbE (when we don't yet have injectivity of type formers)
-- * We need to relax completeness such that we can actually take advantage
--   of these syntactic normal/neutral comparisons

-- Well-scoped raw syntax of normal forms

data RawVar : Nat → Set where
  vzᴿ  : RawVar (suc n)
  vsᴿ  : RawVar n → RawVar (suc n)

data Raw (n : Nat) : Set where
  varᴿ : RawVar n → Raw n
  neℤᴿ : Raw n → Raw n
  
  lamᴿ : Raw (suc n) → Raw n
  appᴿ : Raw n → Raw n → Raw n

  zeᴿ  : Raw n
  suᴿ  : Raw n → Raw n
  _-ᴿ_ : Raw n → Raw n → Raw n

variable
  xᴿ yᴿ zᴿ : RawVar _
  tᴿ uᴿ vᴿ : Raw _

-- Implementing this is very standard (I'll do it at some point!)
postulate
  _≟_ : (tᴿ uᴿ : Raw n) → Dec (tᴿ ≡ uᴿ)

-- Relaxed convertibility
data _~_ : Tm Γ A → Tm Γ A → Set

-- Variable/neutral/normal form predicates
data VarCmpl  : ∀ Γ A → Tm Γ A → RawVar (len Γ) → Set
data NeCmpl   : ∀ Γ A → Tm Γ A → Raw (len Γ) → Set
data NfCmpl   : ∀ Γ A → Tm Γ A → Raw (len Γ) → Set
data ℤParCmpl : ∀ Γ → Tm Γ ℤ → Raw (len Γ) → Set
data ℤCmpl    : ∀ Γ → Tm Γ ℤ → Raw (len Γ) → Set

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
  vsC : VarCmpl Γ A t xᴿ 
      → VarCmpl (Γ ▷ B) (A [ p ]T) (t [ p ]) (vsᴿ xᴿ)

data NeCmpl where
  coe~ : t₁ ~ t₂ → NeCmpl Γ A t₁ tᴿ → NeCmpl Γ A t₂ tᴿ
  varC : VarCmpl Γ A t xᴿ → NeCmpl Γ A t (varᴿ xᴿ)
  appC : NeCmpl Γ (Π A B) t tᴿ → NfCmpl Γ A u uᴿ 
        → NeCmpl Γ (B [ id , u ]T) (app t [ id , u ]) (appᴿ tᴿ uᴿ)
  -- LHS is normal but RHS is neutral
  -- OR both sides are neutral and not convertible
  -neC : NfCmpl Γ ℤ t tᴿ → NeCmpl Γ ℤ u uᴿ
       → (tᴿ ≡ neℤᴿ uᴿ → 𝟘) → NeCmpl Γ ℤ (t - u) (tᴿ -ᴿ neℤᴿ uᴿ)
  -- LHS is neutral and RHS is successor of something
  ne-C : NeCmpl Γ ℤ t tᴿ → NfCmpl Γ ℤ u uᴿ
       → NeCmpl Γ ℤ (t - su u) (neℤᴿ tᴿ -ᴿ suᴿ uᴿ)
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
Var Γ A t = ∃ (RawVar (len Γ)) (VarCmpl Γ A t)

Ne : ∀ Γ A → Tm Γ A → Set
Ne Γ A t = ∃ (Raw (len Γ)) (NeCmpl Γ A t)

Nf : ∀ Γ A → Tm Γ A → Set
Nf Γ A t = ∃ (Raw (len Γ)) (NfCmpl Γ A t)

ℤPar : ∀ Γ → Tm Γ ℤ → Set
ℤPar Γ t = ∃ (Raw (len Γ)) (ℤParCmpl Γ t)

ℤVal : ∀ Γ → Tm Γ ℤ → Set
ℤVal Γ t = ∃ (Raw (len Γ)) (ℤCmpl Γ t)

zeⱽ : ℤVal Γ ze
zeⱽ = zeᴿ ∃, parC zeC

suⱽ : ℤVal Γ t → ℤVal Γ (su t)
suⱽ (tᴿ Σ,  tC) .fst       = suᴿ tᴿ
suⱽ (tᴿ ∃, tC) .snd .proj = incᴾ (parC (suC tC))

coeℤ~ : t₁ ~ t₂ → ℤCmpl Γ t₁ tᴿ → ℤCmpl Γ t₂ tᴿ
coeℤ~ t~ (parC tC) = parC (coe~ t~ tC)
coeℤ~ t~ (neC  tC) = neC  (coe~ t~ tC)

-- Relaxed version of the non-linear '-cancel' conversion rule
-cancel~ : NeCmpl Γ ℤ t₁ tᴿ → NeCmpl Γ ℤ t₂ tᴿ → (t₁ - t₂) ~ ze
-cancel~ {t₁ = t₁} {t₂ = t₂} t₁C t₂C = ap~ (_- t₂) (ne~ t₁C t₂C)

ℤ/ne : ℤParCmpl Γ t₁ (neℤᴿ tᴿ) → NeCmpl Γ ℤ t₂ tᴿ → 𝟘
ℤ/ne (coe~ _ tC₁) tC₂ = ℤ/ne tC₁ tC₂

-- Recursive subtraction
_-ᴿ'_ : Raw n → Raw n → Raw n
tᴿ      -ᴿ' zeᴿ     = tᴿ
suᴿ tᴿ  -ᴿ' suᴿ uᴿ  = tᴿ -ᴿ' uᴿ
neℤᴿ tᴿ -ᴿ' neℤᴿ uᴿ with tᴿ ≟ uᴿ 
... | yes _ = zeᴿ
... | no  _ = neℤᴿ (neℤᴿ tᴿ -ᴿ neℤᴿ uᴿ)
-- Fallthrough
tᴿ      -ᴿ' uᴿ = neℤᴿ (tᴿ -ᴿ uᴿ)

-neᴿ : ℤParCmpl Γ t tᴿ → tᴿ -ᴿ' neℤᴿ uᴿ ≡ neℤᴿ (tᴿ -ᴿ neℤᴿ uᴿ)
-neᴿ (coe~ _ tC) = -neᴿ tC
-neᴿ zeC         = refl
-neᴿ (suC tC)    = refl

_ⱽ-ⱽ_ : ℤCmpl Γ t tᴿ → ℤCmpl Γ u uᴿ → ℤCmpl Γ (t - u) (tᴿ -ᴿ' uᴿ)
_ⱽ-ᴾ_ : ℤCmpl Γ t tᴿ → ℤParCmpl Γ u uᴿ → ℤCmpl Γ (t - u) (tᴿ -ᴿ' uᴿ)
_ᴾ-ⱽ_ : ℤParCmpl Γ t tᴿ → ℤCmpl Γ u uᴿ → ℤCmpl Γ (t - u) (tᴿ -ᴿ' uᴿ)
_ᴾ-ᴾ_ : ℤParCmpl Γ t tᴿ → ℤParCmpl Γ u uᴿ → ℤCmpl Γ (t - u) (tᴿ -ᴿ' uᴿ)

tC      ⱽ-ⱽ parC uC = tC ⱽ-ᴾ uC
parC tC ⱽ-ⱽ uC      = tC ᴾ-ⱽ uC
_ⱽ-ⱽ_ {tᴿ = neℤᴿ tᴿ} {uᴿ = neℤᴿ uᴿ} (neC tC) (neC uC) with tᴿ ≟ uᴿ 
... | yes refl = coeℤ~ (sym~ (-cancel~ tC uC)) (parC zeC)
... | no  p    = neC (-neC (valℤC (neC tC)) uC λ where refl → p refl)

_ⱽ-ᴾ_ {t = t} tC (coe~ u~ uC) 
  = coeℤ~ (ap~ (t -_) u~) (tC ⱽ-ᴾ uC)

tC      ⱽ-ᴾ zeC    = tC
neC tC  ⱽ-ᴾ suC uC = neC (ne-C tC (valℤC uC))
parC tC ⱽ-ᴾ uC     = tC ᴾ-ᴾ uC

tC ᴾ-ⱽ parC uC = tC ᴾ-ᴾ uC
tC ᴾ-ⱽ neC uC
  = transp (ℤCmpl _ _) (sym (-neᴿ tC)) 
           (neC (-neC (valℤC (parC tC)) uC λ where refl → ℤ/ne tC uC))

tC     ᴾ-ᴾ zeC    = parC tC
suC tC ᴾ-ᴾ suC uC = tC ⱽ-ⱽ uC
zeC    ᴾ-ᴾ suC uC = neC (ze-C (valℤC uC))

_ᴾ-ᴾ_ {u = u} (coe~ t~ tC) uC 
  = coeℤ~ (ap~ (_- u) t~) (tC ᴾ-ᴾ uC)
_ᴾ-ᴾ_ {t = t} tC (coe~ u~ uC) 
  = coeℤ~ (ap~ (t -_) u~) (tC ᴾ-ᴾ uC)

_-ⱽ_ : ℤVal Γ t → ℤVal Γ u → ℤVal Γ (t - u)
((tᴿ Σ, tC) -ⱽ (uᴿ Σ, uC)) .fst       = tᴿ -ᴿ' uᴿ
((tᴿ ∃, tC) -ⱽ (uᴿ ∃, uC)) .snd .proj = incᴾ (tC ⱽ-ⱽ uC)
  -- (tᴿ -ᴿ' uᴿ) ∃, (tC ⱽ-ⱽ uC)

-cancelᴿ : ℤCmpl Γ t tᴿ → tᴿ -ᴿ' tᴿ ≡ zeᴿ
-cancelᴾ : ℤParCmpl Γ t tᴿ → tᴿ -ᴿ' tᴿ ≡ zeᴿ

-cancelᴾ (coe~ t~ tC) = -cancelᴾ tC
-cancelᴾ zeC          = refl
-cancelᴾ (suC tC)     = -cancelᴿ tC

-cancelᴿ                (parC tC) = -cancelᴾ tC
-cancelᴿ {tᴿ = neℤᴿ tᴿ} (neC  tC) with tᴿ ≟ tᴿ
... | yes _ = refl
... | no  p = absurd (p refl)

-cancelⱽ : {tⱽ : ℤVal Γ t} → tⱽ -ⱽ tⱽ ≡ zeⱽ
-cancelⱽ {tⱽ = tᴿ Σ, tC} = ∃≡ (↑∥≡∥ (∥-∥-map -cancelᴿ tC))

vzᴺᵉ : Ne (Γ ▷ A) (A [ p ]T) q
vzᴺᵉ = varᴿ vzᴿ ∃, varC vzC

lamᴺᶠ : Nf (Γ ▷ A) B t → Nf Γ (Π A B) (lam t)
lamᴺᶠ (tᴿ Σ, tC) .fst       = lamᴿ tᴿ
lamᴺᶠ (tᴿ ∃, tC) .snd .proj = incᴾ (lamC tC)

appᴺᵉ : Ne Γ (Π A B) t → Nf Γ A u → Ne Γ (B [ id , u ]T) (app t [ id , u ])
appᴺᵉ (tᴿ Σ, tC) (uᴿ Σ, uC) .fst       = appᴿ tᴿ uᴿ
appᴺᵉ (tᴿ ∃, tC) (uᴿ ∃, uC) .snd .proj = incᴾ (appC tC uC)
