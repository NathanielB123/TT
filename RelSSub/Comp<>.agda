{-# OPTIONS --rewriting #-}

open import Utils
open import Common.Sort
open import Common.SortEq

open import RelSSub.Syntax
open import RelSSub.SubUniq
open import RelSSub.Laws1
open import RelSSub.Laws2

-- Finally, we show substitution is computable!
module RelSSub.Comp<> where

open import RelSSub.CompWk
  renaming (_[_]T to _[_]Tᵂᵏ ; _[_]_ to _[_]ᵂᵏ_; []T to []Tᵂᵏ; [] to []ᵂᵏ
           ; []T≡ to []T≡ᵂᵏ ; []≡ to []≡ᵂᵏ)
  public

_[_]T : Ty Γ → Sub[ T ] Δ Γ → Ty Δ
_[_]_ : Tm[ q ] Γ A → ∀ (δ : Sub[ T ] Δ Γ) → A [ δ ]T≔ A[] 
      → Tm[ T ] Δ A[]
[]T   : A [ δ ]T≔ (A [ δ ]T)
[]    : t [ δ ] A𝒢 ≔ (_[_]_ {q = q} {A[] = A[]} t δ A𝒢)

[]T≡ : A [ δ ]T≔ A[] → A [ δ ]T ≡ A[]
[]≡  : t [ δ ] A𝒢 ≔ t[] → _[_]_ t δ A𝒢 ≡ t[]

U     [ δ ]T = U
El t  [ δ ]T = El (t [ δ ] U[])
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ^ []T ]T)

vz A𝒢₁   [ < u > ]   A𝒢₂ = coeTm (sym ([]T≡ (wk<>T A𝒢₁)) ∙ []T≡ A𝒢₂) u
vs i A𝒢₁ [ < u > ]   A𝒢₂ = coeTm (sym ([]T≡ (wk<>T A𝒢₁)) ∙ []T≡ A𝒢₂) (` i)

vz A𝒢₁   [ δ ^ A𝒢₂ ] A𝒢₃ = tm⊑ V⊑ (vz (wk^T A𝒢₁ A𝒢₂ A𝒢₃))
vs i A𝒢₁ [ δ ^ B𝒢 ]  A𝒢₂ = (i [ δ ] []T) [ wk ]ᵂᵏ (wk^T A𝒢₁ []T A𝒢₂)

(` i) [ δ ] A𝒢 = tm⊑ ⊑T (i [ δ ] A𝒢)
lam t [ δ ] Π[] A𝒢 B𝒢
  = lam (t [ δ ^ A𝒢 ] B𝒢)
app t u B𝒢₁ [ δ ] B𝒢₂ 
  = app (t [ δ ] Π[] []T []T) (u [ δ ] []T) (^<>T B𝒢₁ []T B𝒢₂ [])

coh[] : ∀ {A≡ : A₁ ≡ A₂}
      → t [ δ ] coe[]T-rhs (sym A≡) A𝒢 ≔ t[] → t [ δ ] A𝒢 ≔ coeTm A≡ t[]
coh[] {A≡ = refl} t𝒢 = t𝒢

[]T {A = U}     = U[]
[]T {A = El t}  = El[] []
[]T {A = Π A B} = Π[] []T []T

[] {t = vz A𝒢}    {δ = < u >}   = coh[] vz<>
[] {t = vs i A𝒢}  {δ = < u >}   = coh[] vs<>
[] {t = vz A𝒢₁}   {δ = δ ^ A𝒢₂} = vz^
[] {t = vs i A𝒢₁} {δ = δ ^ A𝒢₂} = vs^ [] []ᵂᵏ

[] {t = ` i}                  = `[] []
[] {t = lam t} {A𝒢 = Π[] _ _} = lam[] []
[] {t = app t u B𝒢}           = app[] {B𝒢₁ = []T} [] []

module Helpers where
  Π[]≡ : ∀ (A≡ : A [ δ ]T ≡ A[]) → B [ δ ^ A𝒢 ]T ≡ B[] 
        → Π A B [ δ ]T ≡ Π A[] B[]
  Π[]≡ {A𝒢 = A𝒢} refl refl with refl ← u[]Tp []T A𝒢  = refl

  lam[]≡ : t [ δ ^ A𝒢 ] B𝒢 ≡ t[] 
          → lam t [ δ ] (Π[] A𝒢 B𝒢) ≡ lam t[]
  lam[]≡ refl = refl

  app[]≡ : A [ δ ]T ≡ A[] → B [ δ ^ A𝒢 ]T ≡ B[]
          → t [ δ ] (Π[] A𝒢 B𝒢₂) ≡ t[] → u [ δ ] A𝒢 ≡ u[]
          → app {A = A} {B = B} t u B𝒢₁ [ δ ] B𝒢₃ 
          ≡ app {A = A[]} {B = B[]} t[] u[] B𝒢₄
  app[]≡ {A𝒢 = A𝒢} {B𝒢₂ = B𝒢₂} {B𝒢₁ = B𝒢₁} {B𝒢₃ = B𝒢₃} {B𝒢₄ = B𝒢₄} refl refl refl refl 
    with refl ← u[]Tp A𝒢 []T
       | refl ← u[]Tp B𝒢₂ []T 
       | refl ← u[]Tp B𝒢₄ (^<>T B𝒢₁ []T B𝒢₃ [])
    = refl

  vz≡ : vz A𝒢₁ ≡ vz A𝒢₂
  vz≡ {A𝒢₁ = A𝒢₁} {A𝒢₂ = A𝒢₂}
    with refl ← u[]Tp A𝒢₁ A𝒢₂
    = refl

  [][wk]≡ : A [ δ ]T ≡ A[] → _[_]_ {A = A} {A[] = A[]} t δ A𝒢₂ ≡ t[] 
          → t[] [ wk ]ᵂᵏ A𝒢₃ ≡ t[][]
          → (t [ δ ] []T) [ wk ]ᵂᵏ A𝒢₄ ≡ t[][]
  [][wk]≡ {A𝒢₂ = A𝒢₂} {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄} refl refl refl 
    with refl ← u[]Tp A𝒢₂ []T
       | refl ← u[]Tp A𝒢₃ A𝒢₄
    = refl
open Helpers

[]T≡ U[]         = refl
[]T≡ (El[] t𝒢)   = cong El ([]≡ t𝒢)
[]T≡ (Π[] A𝒢 B𝒢) = Π[]≡ ([]T≡ A𝒢) ([]T≡ B𝒢)

[]≡ (vz<> {A𝒢₁ = A𝒢₁} {A𝒢₂ = A𝒢₂})
  with refl ← sym ([]T≡ (wk<>T^^ A𝒢₁)) ∙ []T≡ A𝒢₂
  = refl
[]≡ (vs<> {A𝒢₁ = A𝒢₁} {A𝒢₂ = A𝒢₂})
  with refl ← sym ([]T≡ (wk<>T^^ A𝒢₁)) ∙ []T≡ A𝒢₂
  = refl

[]≡ vz^ = cong (tm⊑ V⊑) vz≡
[]≡ (vs^ {i = i} {A𝒢₁ = A𝒢₁} i𝒢 i[]𝒢)
  = [][wk]≡ {t = i} ([]T≡ A𝒢₁) ([]≡ i𝒢) ([]≡ᵂᵏ i[]𝒢)

[]≡ (`[] i𝒢) = cong (tm⊑ ⊑T) ([]≡ i𝒢)
[]≡ (lam[] {t = t} {B𝒢 = B𝒢} t𝒢) = lam[]≡ {t = t} ([]≡ t𝒢)
[]≡ (app[] {t = t} {A𝒢 = A𝒢} {B𝒢₁ = B𝒢} t𝒢 u𝒢)
  = app[]≡ {t = t} ([]T≡ A𝒢) ([]T≡ B𝒢) ([]≡ t𝒢) ([]≡ u𝒢) 
