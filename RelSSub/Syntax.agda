{-# OPTIONS --prop --show-irrelevant --rewriting #-}

open import Utils
open import Common.Sort
open import Common.SortEq

-- Weak Type Theory (no definitional β/η) defined inductive-inductively without 
-- setoids or quotients
--
-- We use single substitutions as in 
-- https://raw.githubusercontent.com/szumixie/single-subst/main/lfmtp/p.pdf
-- (also https://github.com/NathanielB123/dep-ty-chk)
-- as this drastically cuts down on the number of operations
module RelSSub.Syntax where

data Ctx    : Set
data Ty     : Ctx → Set
data Tm[_] : Sort → ∀ Γ → Ty Γ → Set
data Sub[_] : Sort → Ctx → Ctx → Set

Tm  = Tm[ T ]
Var = Tm[ V ]

variable
  Γ Δ Θ Γ₁ Γ₂         : Ctx
  A B A₁ A₂ A[] A[]₁ A[]₂ A[][] B₁ B₂ B[]   : Ty Γ
  δ σ  δ₁ δ₂          : Sub[ q ] Δ Γ
  t u v t[] t[]₁ t[]₂ t[][] u[] i[] i[][] t₁ t₂ t₃ u₁ u₂ : Tm[ q ] Γ A
  i j k i₁ i₂        : Var Γ A
  
data Ctx where
  •   : Ctx
  _▷_ : ∀ Γ → Ty Γ → Ctx

-- Substitution as a relation ("graph of the function")
data _[_]T≔_   : Ty Γ → Sub[ q ] Δ Γ → Ty Δ → Set
data _[_]_≔_   : Tm[ q ] Γ A → ∀ (δ : Sub[ r ] Δ Γ) → A [ δ ]T≔ A[] 
               → Tm[ q ⊔ r ] Δ A[] → Set

variable
  A𝒢 B𝒢 A𝒢₁ A𝒢₂ A𝒢₃ A𝒢₄ B𝒢₁ B𝒢₂ B𝒢₃ B𝒢₄ : A [ δ ]T≔ A[]

data Ty where
  U  : Ty Γ
  El : Tm Γ U → Ty Γ
  Π  : ∀ A → Ty (Γ ▷ A) → Ty Γ

data Sub[_] where
  wk  : Sub[ V ] (Γ ▷ A) Γ
  <_> : Tm Γ A → Sub[ T ] Γ (Γ ▷ A)
  _^_ : ∀ (δ : Sub[ q ] Δ Γ) → A [ δ ]T≔ A[] → Sub[ q ] (Δ ▷ A[]) (Γ ▷ A)

data Tm[_] where 
  vz    : A [ wk ]T≔ A[] → Var (Γ ▷ A) A[]
  vs    : Var Γ A → A [ wk ]T≔ A[] → Var (Γ ▷ B) A[]
  `_    : Var Γ A → Tm Γ A
  lam   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → ∀ (u : Tm Γ A)
        → B [ < u > ]T≔ B[] → Tm Γ B[]

tm⊑ : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
tm⊑ {q = V} {r = V} _ i = i
tm⊑ {q = V} {r = T} _ i = ` i
tm⊑ {q = T} {r = T} _ t = t

data _[_]T≔_ where
  U[]  : U [ δ ]T≔ U
  El[] : t [ δ ] U[] ≔ t[] → El t [ δ ]T≔ El t[]
  Π[]  : ∀ (A𝒢 : A [ δ ]T≔ A[]) → B [ δ ^ A𝒢 ]T≔ B[] → Π A B [ δ ]T≔ Π A[] B[]

data _[_]_≔_ where
  i[wk] : i [ wk ] A𝒢 ≔ vs i A𝒢
  vz<> : vz A𝒢₁ [ < u > ] A𝒢₂ ≔ u
  -- vz<>  : ∀ {A𝒢 : A [ wk ]T≔ A[]} {u₁ : Tm Γ A} {A𝒢₂ : A[] [ < u₁ > ]T≔ A[][]}
  --       → u₁ ≡[ A≡ ]Tm u₂
  --       → vz A𝒢 [ < u₁ > ] A𝒢₂ ≔ u₂
  -- I think we could define the substitution relation without
  -- reference to the laws (we can just ask for the relevant equations
  -- when necessary).
  vs<>  : vs i A𝒢₁ [ < u > ] A𝒢₂ ≔ (` i)
  vs^   : i [ δ ] A𝒢₂ ≔ i[] → i[] [ wk ] A𝒢₄ ≔ i[][]
        → vs i A𝒢₁ [ δ ^ B𝒢 ] A𝒢₃ ≔ i[][]
  vz^   : vz A𝒢₁ [ δ ^ A𝒢₂ ] A𝒢₃ ≔ tm⊑ V⊑ (vz A𝒢₄)
  `[]   : i [ δ ] A𝒢 ≔ i[] → (` i) [ δ ] A𝒢 ≔ tm⊑ ⊑T i[]
  lam[] : t [ δ ^ A𝒢 ] B𝒢 ≔ t[] → lam t [ δ ] Π[] A𝒢 B𝒢 ≔ lam t[]
  app[] : t [ δ ] Π[] A𝒢 B𝒢₂ ≔ t[] → ∀ (u𝒢 : u [ δ ] A𝒢 ≔ u[])
        → app t u B𝒢₁ [ δ ] B𝒢₃
        ≔ app t[] u[] B𝒢₄

coeTm : A₁ ≡ A₂ → Tm[ q ] Γ A₁ → Tm[ q ] Γ A₂
coeTm refl t = t

coe[]T-lhs : A₁ ≡ A₂ → A₁ [ δ ]T≔ A[] → A₂ [ δ ]T≔ A[]
coe[]T-lhs refl A𝒢 = A𝒢 

coe[]T-rhs : A[]₁ ≡ A[]₂ → A [ δ ]T≔ A[]₁ → A [ δ ]T≔ A[]₂
coe[]T-rhs refl A𝒢 = A𝒢

coe[]-lhs : ∀ (t≡ : t₁ ≡ t₂)
          → t₁ [ δ ] A𝒢 ≔ t[]
          → t₂ [ δ ] A𝒢 ≔ t[]
coe[]-lhs refl t𝒢 = t𝒢
