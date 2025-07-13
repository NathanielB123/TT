{-# OPTIONS --rewriting #-}

open import Utils
open import Common.Sort
open import Common.SortEq

open import RelSSub.Syntax

-- The substitution relation acts like a function (there is exactly one output 
-- for every input term/type and substitution) and is a proposition (declaring
-- substitution in |Prop| would ensure this definitionally)
module RelSSub.SubUniq where

tm⊑[] : ∀ {q⊑r : q ⊑ r} {δ : Sub[ s ] Δ Γ} {A𝒢} → t [ δ ] A𝒢 ≔ t[] 
      → tm⊑ q⊑r t [ δ ] A𝒢 ≔ tm⊑ (⊑⊔s {s = s} q⊑r) t[]
tm⊑[] {q = V} {r = V} {s = V} t[] = t[]
tm⊑[] {q = V} {r = V} {s = T} t[] = t[]
tm⊑[] {q = V} {r = T} {s = V} t[] = `[] t[]
tm⊑[] {q = V} {r = T} {s = T} t[] = `[] t[]
tm⊑[] {q = T} {r = T} {s = s} t[] = t[]

-- Uniqueness of substitution proofs
u[]Tp : ∀ (A𝒢₁ A𝒢₂ : A [ δ ]T≔ A[]) 
      → A𝒢₁ ≡ A𝒢₂
u[]p : ∀ {δ : Sub[ r ] Δ Γ} {A𝒢} (t𝒢₁ t𝒢₂ : t [ δ ] A𝒢 ≔ t[]) 
     → t𝒢₁ ≡ t𝒢₂

-- Substitution is a function
[]T-uniq : A [ δ ]T≔ A[]₁ → A [ δ ]T≔ A[]₂ → A[]₁ ≡ A[]₂
[]-uniq : t [ δ ] A𝒢 ≔ t[]₁ → t [ δ ] A𝒢 ≔ t[]₂ → t[]₁ ≡ t[]₂

u[]Tp U[]        U[]        = refl
u[]Tp (El[] t𝒢₁) (El[] t𝒢₂) = cong El[] (u[]p t𝒢₁ t𝒢₂)
u[]Tp (Π[] A𝒢₁ B𝒢₁) (Π[] A𝒢₂ B𝒢₂) 
  with refl ← u[]Tp A𝒢₁ A𝒢₂
  = cong (Π[] _) (u[]Tp B𝒢₁ B𝒢₂)

u[]p         i[wk] i[wk] = refl
u[]p         vz<>  vz<>  = refl
u[]p         vs<>  vs<>  = refl
u[]p {r = V} vz^   vz^   = refl
u[]p {r = T} vz^   vz^   = refl

u[]p (vs^ {A𝒢₂ = A𝒢₁} {A𝒢₄ = A𝒢₁′} i𝒢₁ i[]𝒢₁) 
     (vs^ {A𝒢₂ = A𝒢₂} {A𝒢₄ = A𝒢₂′} i𝒢₂ i[]𝒢₂) 
  with refl ← []T-uniq A𝒢₁ A𝒢₂
  with refl ← u[]Tp A𝒢₁ A𝒢₂
  with refl ← []-uniq i𝒢₁ i𝒢₂
  with refl ← u[]p i𝒢₁ i𝒢₂
  with refl ← []T-uniq A𝒢₁′ A𝒢₂′
  with refl ← u[]Tp A𝒢₁′ A𝒢₂′
  = cong (vs^ _) (u[]p i[]𝒢₁ i[]𝒢₂)

u[]p {r = V} (`[] i𝒢₁)   (`[] i𝒢₂)      = cong `[] (u[]p i𝒢₁ i𝒢₂)
u[]p {r = T} (`[] i𝒢₁)   (`[] i𝒢₂)      = cong `[] (u[]p i𝒢₁ i𝒢₂)
u[]p         (lam[] t𝒢₁) (lam[] t𝒢₂) = cong lam[] (u[]p t𝒢₁ t𝒢₂)
u[]p (app[] {A𝒢 = A𝒢₁} {B𝒢₂ = B𝒢₁} t𝒢₁ u𝒢₁) 
     (app[] {A𝒢 = A𝒢₂} {B𝒢₂ = B𝒢₂} t𝒢₂ u𝒢₂) 
  with refl ← []T-uniq A𝒢₁ A𝒢₂
  with refl ← u[]Tp A𝒢₁ A𝒢₂
  with refl ← []T-uniq B𝒢₁ B𝒢₂
  with refl ← u[]Tp B𝒢₁ B𝒢₂
  with refl ← []-uniq t𝒢₁ t𝒢₂
  with refl ← u[]p t𝒢₁ t𝒢₂
  = cong (app[] _) (u[]p u𝒢₁ u𝒢₂)

[]T-uniq U[]           U[] = refl
[]T-uniq (El[] t𝒢₁)    (El[] t𝒢₂) = cong El ([]-uniq t𝒢₁ t𝒢₂)
[]T-uniq (Π[] A𝒢₁ B𝒢₁) (Π[] A𝒢₂ B𝒢₂) 
  with refl ← []T-uniq A𝒢₁ A𝒢₂
  with refl ← u[]Tp A𝒢₁ A𝒢₂
  = cong (Π _) ([]T-uniq B𝒢₁ B𝒢₂)

[]-uniq i[wk] i[wk] = refl
[]-uniq vz<>  vz<>  = refl
[]-uniq vs<>  vs<>  = refl
[]-uniq (vz^ {A𝒢₄ = A𝒢₁}) (vz^ {A𝒢₄ = A𝒢₂})  
  = cong (λ □ → tm⊑ V⊑ (vz □)) (u[]Tp A𝒢₁ A𝒢₂)
[]-uniq (vs^ {A𝒢₂ = A𝒢₁} {A𝒢₄ = A𝒢₁′} i𝒢₁ i[]𝒢₁) 
        (vs^ {A𝒢₂ = A𝒢₂} {A𝒢₄ = A𝒢₂′} i𝒢₂ i[]𝒢₂)
  with refl ← []T-uniq A𝒢₁ A𝒢₂
  with refl ← u[]Tp A𝒢₁ A𝒢₂
  with refl ← []-uniq i𝒢₁ i𝒢₂
  with refl ← []T-uniq A𝒢₁′ A𝒢₂′
  with refl ← u[]Tp A𝒢₁′ A𝒢₂′
  = []-uniq i[]𝒢₁ i[]𝒢₂
[]-uniq (`[] i𝒢₁)   (`[] i𝒢₂)   = cong (tm⊑ ⊑T) ([]-uniq i𝒢₁ i𝒢₂)
[]-uniq (lam[] t𝒢₁) (lam[] t𝒢₂) = cong lam ([]-uniq t𝒢₁ t𝒢₂)
[]-uniq (app[] {A𝒢 = A𝒢₁} {B𝒢₂ = B𝒢₁} t𝒢₁ u𝒢₁) 
        (app[] {A𝒢 = A𝒢₂} {B𝒢₂ = B𝒢₂} t𝒢₂ u𝒢₂)
  with refl ← []T-uniq A𝒢₁ A𝒢₂
  with refl ← u[]Tp A𝒢₁ A𝒢₂
  with refl ← []T-uniq B𝒢₁ B𝒢₂
  with refl ← u[]Tp B𝒢₁ B𝒢₂
  with refl ← []-uniq t𝒢₁ t𝒢₂
  with refl ← []-uniq u𝒢₁ u𝒢₂
  = cong (app _ _) (u[]Tp _ _)

coh[]-rhs : ∀ (A≡ : A[]₁ ≡ A[]₂)
          → t [ δ ] A𝒢₁ ≔ t[]
          → t [ δ ] A𝒢₂ ≔ coeTm A≡ t[]
coh[]-rhs {A𝒢₁ = A𝒢₁} {A𝒢₂ = A𝒢₂} refl t𝒢
  with refl ← u[]Tp A𝒢₁ A𝒢₂
  = t𝒢

coh[]-lhs : ∀ (A≡ : A₁ ≡ A₂)
          → t [ δ ] A𝒢₁ ≔ t[]
          → coeTm A≡ t [ δ ] A𝒢₂ ≔ t[]
coh[]-lhs {A𝒢₁ = A𝒢₁} {A𝒢₂ = A𝒢₂} refl t𝒢
  with refl ← u[]Tp A𝒢₁ A𝒢₂
  = t𝒢
