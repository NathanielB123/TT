{-# OPTIONS --rewriting #-}

open import Utils
open import Common.Sort
open import Common.SortEq

open import RelSSub.Syntax

-- To implement substitution recursively, we need some laws.
-- We start by proving that weakening followed by substituting the new
-- fresh variable is identity.
--
-- When proving substitution laws, to deal with the cases for binders 
-- (|Π| and |lam|) we need to account for arbitrarily-many "lifts" (|_^_|).
-- Parameterising over telescopes achieves this.
module RelSSub.Laws1 where

wk<>T  : A [ wk ]T≔ A[] → A[] [ < t > ]T≔ A

data Tel (Γ : Ctx) : Set

_▷▷_ : ∀ Γ → Tel Γ → Ctx

data Tel Γ where
  •   : Tel Γ
  _▷_ : ∀ (Ξ : Tel Γ) → Ty (Γ ▷▷ Ξ) → Tel Γ

Γ ▷▷ •       = Γ
Γ ▷▷ (Ξ ▷ A) = (Γ ▷▷ Ξ) ▷ A

variable
  Ξ Ξ[] Ξ[][] Ξ[]₁ Ξ[]₂ Ξwk Ξwk[] : Tel Γ

data _[_]Ts≔_ : Tel Γ → Sub[ r ] Δ Γ → Tel Δ → Set

_^^_ : ∀ (δ : Sub[ q ] Δ Γ) → Ξ [ δ ]Ts≔ Ξ[] → Sub[ q ] (Δ ▷▷ Ξ[]) (Γ ▷▷ Ξ) 
  
data _[_]Ts≔_ where
  •[] : • [ δ ]Ts≔ •
  ▷[] : ∀ (Ξ𝒢 : Ξ [ δ ]Ts≔ Ξ[]) → A [ δ ^^ Ξ𝒢 ]T≔ A[] 
      → (Ξ ▷ A) [ δ ]Ts≔ (Ξ[] ▷ A[])

δ ^^ •[]       = δ
δ ^^ ▷[] Ξ𝒢 A𝒢 = (δ ^^ Ξ𝒢) ^ A𝒢

variable
  Ξ𝒢 Ξ𝒢₁ Ξ𝒢₂ Ξ𝒢₃ Ξ𝒢₄ : Ξ [ δ ]Ts≔ Ξ[]
  t𝒢 u𝒢 : t [ δ ] _ ≔ t[] 

wk<>T^^ : ∀ {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]} {Ξ𝒢₂ : Ξ[] [ < u > ]Ts≔ Ξ}
        → A [ wk ^^ Ξ𝒢₁ ]T≔ A[] → A[] [ < u > ^^ Ξ𝒢₂ ]T≔ A
wk<>^^  : ∀ {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]} {Ξ𝒢₂ : Ξ[] [ < u > ]Ts≔ Ξ} {A𝒢}
        → t [ wk ^^ Ξ𝒢₁ ] A𝒢 ≔ t[] 
        → t[] [ < u > ^^ Ξ𝒢₂ ] wk<>T^^ A𝒢 ≔ tm⊑ ⊑T t

wk<>T^^ U[]         = U[]
wk<>T^^ (El[] t𝒢)   = El[] (wk<>^^ t𝒢)
wk<>T^^ (Π[] A𝒢 B𝒢) = Π[] (wk<>T^^ A𝒢) (wk<>T^^ B𝒢)

wk<>^^ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} i[wk] = vs<>

wk<>^^ (`[] i𝒢)             = `[] (wk<>^^ i𝒢)
wk<>^^ (lam[] {A𝒢 = A𝒢} t𝒢) = lam[] {A𝒢 = wk<>T^^ A𝒢} (wk<>^^ t𝒢)
wk<>^^ (app[] {B𝒢₂ = B𝒢₂} t𝒢 u𝒢) 
  = app[] {B𝒢₂ = wk<>T^^ B𝒢₂} (wk<>^^ t𝒢) (wk<>^^ u𝒢)

wk<>^^ {t = vz A𝒢} {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} vz^ = vz^
wk<>^^ {t = vs i A𝒢} {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} (vs^ i𝒢 i[wk]) 
  = vs^ (wk<>^^ i𝒢) (`[] i[wk])

wk<>T = wk<>T^^
