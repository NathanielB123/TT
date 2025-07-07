{-# OPTIONS --prop --show-irrelevant --rewriting #-}

open import Utils
open import Utils.IdExtras
open import Common.Sort
open import Common.SortEq

-- Weak Type Theory (no definitional β/η) defined inductive-inductively without 
-- setoids or quotients
--
-- We use single substitutions as in 
-- https://raw.githubusercontent.com/szumixie/single-subst/main/lfmtp/p.pdf
-- as this drastically cuts down on the number of operations we need
module RelSSub where

data Ctx    : Set
data Ty     : Ctx → Set
data Tm[_] : Sort → ∀ Γ → Ty Γ → Set
data Sub[_] : Sort → Ctx → Ctx → Set

Tm  = Tm[ T ]
Var = Tm[ V ]

variable
  Γ Δ Θ         : Ctx
  A B A₁ A₂ A[] A[]₁ A[]₂ A[][] B[]   : Ty Γ
  δ σ           : Sub[ q ] Δ Γ
  t u v t[] u[] i[] i[][] u₁ u₂ : Tm[ q ] Γ A
  i j k         : Var Γ A
  
data Ctx where
  •   : Ctx
  _▷_ : ∀ Γ → Ty Γ → Ctx

-- Substitution as a relation ("graph of the function")
data _[_]T≔_   : Ty Γ → Sub[ q ] Δ Γ → Ty Δ → Prop
data _[_]_≔_   : Tm[ q ] Γ A → ∀ (δ : Sub[ r ] Δ Γ) → A [ δ ]T≔ A[] 
               → Tm[ q ⊔ r ] Δ A[] → Prop

variable
  A𝒢 B𝒢 A𝒢₁ A𝒢₂ A𝒢₃ A𝒢₄ B𝒢₁ B𝒢₂ B𝒢₃ : A [ δ ]T≔ A[]

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

-- Subsingleton elim
-- I don't think |Prop| is essential to the technique anyhow though
coeTm : A₁ ≡ᴾ A₂ → Tm[ q ] Γ A₁ → Tm[ q ] Γ A₂


tm⊑ : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
tm⊑ {q = V} {r = V} _ i = i
tm⊑ {q = V} {r = T} _ i = ` i
tm⊑ {q = T} {r = T} _ t = t

data _[_]T≔_ where
  U[]  : U [ δ ]T≔ U
  El[] : t [ δ ] U[] ≔ t[] → El t [ δ ]T≔ El t[]
  Π[]  : ∀ (A𝒢 : A [ δ ]T≔ A[]) → B [ δ ^ A𝒢 ]T≔ B[] → Π A B [ δ ]T≔ Π A[] B[]

wk<>  : A [ wk ]T≔ A[] → A[] [ < t > ]T≔ A
wk^   : A [ wk ]T≔ A[]₁ → A [ δ ]T≔ A[]₂
      → A[]₁ [ δ ^ B𝒢 ]T≔ A[][]
      → A[]₂ [ wk ]T≔ A[][]

^<>   : A [ < u > ]T≔ A[]₁
      → A [ δ ^ B𝒢 ]T≔ A[]₂
      → A[]₁ [ δ ]T≔ A[][]
      → u [ δ ] B𝒢 ≔ u[]
      → A[]₂ [ < u[] > ]T≔ A[][]

variable
  A≡ : A₁ ≡ᴾ A₂

data _[_]_≔_ where
  i[wk] : i [ wk ] A𝒢 ≔ vs i A𝒢
  -- Much neater, but produces recursive unification equations
  -- vz<> : vz A𝒢 [ < u₁ > ] wk<> A𝒢 ≔ u₂
  vz<>  : ∀ {A𝒢 : A [ wk ]T≔ A[]} {u₁ : Tm Γ A} {A𝒢₂ : A[] [ < u₁ > ]T≔ A[][]}
        → coeTm A≡ u₁ ≡ᴾ u₂ 
        → vz A𝒢 [ < u₁ > ] A𝒢₂ ≔ u₂
  vs<>  : vs i A𝒢 [ < u > ] wk<> A𝒢 ≔ (` i)
  vs^   : i [ δ ] A𝒢₂ ≔ i[] → i[] [ wk ] wk^ A𝒢₁ A𝒢₂ A𝒢₃ ≔ i[][]
        → vs i A𝒢₁ [ δ ^ B𝒢 ] A𝒢₃ ≔ i[][]
  vz^   : vz A𝒢₁ [ δ ^ A𝒢₂ ] A𝒢₃ ≔ tm⊑ V⊑ (vz (wk^ A𝒢₁ A𝒢₂ A𝒢₃))
  `[]   : i [ δ ] A𝒢 ≔ i[] → (` i) [ δ ] A𝒢 ≔ tm⊑ ⊑T i[]
  lam[] : t [ δ ^ A𝒢 ] B𝒢 ≔ t[] → lam t [ δ ] Π[] A𝒢 B𝒢 ≔ lam t[]
  app[] : t [ δ ] Π[] A𝒢 B𝒢₂ ≔ t[] → ∀ (u𝒢 : u [ δ ] A𝒢 ≔ u[])
        → app t u B𝒢₁ [ δ ] B𝒢₃
        ≔ app t[] u[] (^<> B𝒢₁ B𝒢₂ B𝒢₃ u𝒢)

data Tel (Γ : Ctx) : Set

_▷▷_ : ∀ Γ → Tel Γ → Ctx

data Tel Γ where
  •   : Tel Γ
  _▷_ : ∀ (Ξ : Tel Γ) → Ty (Γ ▷▷ Ξ) → Tel Γ

Γ ▷▷ •       = Γ
Γ ▷▷ (Ξ ▷ A) = (Γ ▷▷ Ξ) ▷ A

variable
  Ξ Ξ[] Ξ[][] : Tel Γ

data _[_]Ts≔_ : Tel Γ → Sub[ q ] Δ Γ → Tel Δ → Set

_^^_ : ∀ (δ : Sub[ q ] Δ Γ) → Ξ [ δ ]Ts≔ Ξ[] → Sub[ q ] (Δ ▷▷ Ξ[]) (Γ ▷▷ Ξ) 
  
data _[_]Ts≔_ where
  •[] : • [ δ ]Ts≔ •
  ▷[] : ∀ (Ξ𝒢 : Ξ [ δ ]Ts≔ Ξ[]) → A [ δ ^^ Ξ𝒢 ]T≔ A[] 
      → (Ξ ▷ A) [ δ ]Ts≔ (Ξ[] ▷ A[])

δ ^^ •[]       = δ
δ ^^ ▷[] Ξ𝒢 A𝒢 = (δ ^^ Ξ𝒢) ^ A𝒢

variable
  Ξ𝒢 Ξ𝒢₁ Ξ𝒢₂ : Ξ [ δ ]Ts≔ Ξ[]

wk<>Ts  : Ξ [ wk ]Ts≔ Ξ[] → Ξ[] [ < u > ]Ts≔ Ξ
wk<>T^^ : ∀ {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]} {Ξ𝒢₂ : Ξ[] [ < u > ]Ts≔ Ξ}
        → A [ wk ^^ Ξ𝒢₁ ]T≔ A[] → A[] [ < u > ^^ Ξ𝒢₂ ]T≔ A
wk<>^^  : ∀ {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]} {Ξ𝒢₂ : Ξ[] [ < u > ]Ts≔ Ξ} {A𝒢}
        → t [ wk ^^ Ξ𝒢₁ ] A𝒢 ≔ t[] 
        → t[] [ < u > ^^ Ξ𝒢₂ ] wk<>T^^ A𝒢 ≔ tm⊑ ⊑T t

wk<>Ts •[]         = •[]
wk<>Ts (▷[] Ξ𝒢 A𝒢) = ▷[] (wk<>Ts Ξ𝒢) (wk<>T^^ A𝒢)

wk<>T^^ U[]         = U[]
wk<>T^^ (El[] t𝒢)   = El[] (wk<>^^ t𝒢)
wk<>T^^ (Π[] A𝒢 B𝒢) 
  = Π[] (wk<>T^^ A𝒢) (wk<>T^^ B𝒢)

wk<>^^ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} i[wk] = vs<>
wk<>^^ (`[] i𝒢)   = `[] (wk<>^^ i𝒢)
wk<>^^ (lam[] {A𝒢 = A𝒢} t𝒢) = lam[] {A𝒢 = wk<>T^^ A𝒢} (wk<>^^ t𝒢)
wk<>^^ (app[] {B𝒢₂ = B𝒢₂} t𝒢 u𝒢) 
  = app[] {B𝒢₂ = wk<>T^^ B𝒢₂} (wk<>^^ t𝒢) (wk<>^^ u𝒢)
wk<>^^ {t = vs i A𝒢} {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} (vs^ i𝒢 i[wk]) 
  = vs^ (wk<>^^ i𝒢) (`[] i[wk])
wk<>^^ {t = vz A𝒢} {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} vz^ = vz^

wk<> = wk<>T^^

_[_]T : Ty Γ → Sub[ q ] Δ Γ → Ty Δ
_[_]  : Tm[ q ] Γ A → ∀ (δ : Sub[ r ] Δ Γ) → Tm[ q ⊔ r ] Δ (A [ δ ]T)
[]T   : A [ δ ]T≔ (A [ δ ]T)
[]    : t [ δ ] []T ≔ (t [ δ ])

[]T≡ : A [ δ ]T≔ A[] → (A [ δ ]T) ≡ᴾ A[]
[]≡  : t [ δ ] []T ≔ t[] → (_[_] {q = q} {A = A} t δ) ≡ᴾ t[]

U     [ δ ]T = U
El t  [ δ ]T = El (t [ δ ])
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ^ []T ]T)


-- Curiously, termination fails if we squish these cases together.
-- Exact splits for operations like substitution is probably a good idea
-- anyway...
-- _[_] {q = V} i wk  = vs i []T
(vz A𝒢)   [ wk ]       = vs (vz A𝒢) []T
(vs i A𝒢) [ wk ]       = vs (vs i A𝒢) []T
vz A𝒢     [ < u > ]    = coeTm (symᴾ ([]T≡ (wk<> A𝒢))) u
vs i A𝒢   [ < u > ]    = ` coeTm (symᴾ ([]T≡ (wk<> A𝒢))) i
vz A𝒢₁     [ δ ^ A𝒢₂ ] = tm⊑ V⊑ (vz (wk^ A𝒢₁ A𝒢₂ []T))
_[_] {r = V} (vs i A𝒢) (δ ^ B𝒢) = vs (i [ δ ]) (wk^ A𝒢 []T []T)
_[_] {r = T} (vs i A𝒢) (δ ^ B𝒢) 
  = coeTm ([]T≡ (wk^ A𝒢 []T []T)) (i [ δ ] [ wk ])

(` i)      [ δ ] = tm⊑ ⊑T (i [ δ ])
lam t      [ δ ] = lam (t [ δ ^ []T ])
app t u B𝒢 [ δ ] = app (t [ δ ]) (u [ δ ]) (^<> B𝒢 []T []T [])

[]T {A = U}     = U[]
[]T {A = El t}  = El[] []
[]T {A = Π A B} = Π[] []T []T

[] {t = vz A𝒢}      = {!   !}
[] {t = vs i A𝒢}    = {!   !}
[] {t = ` i}        = `[] []
[] {t = lam t}      = lam[] []
[] {t = app t u B𝒢} = app[] {B𝒢₂ = []T} [] []

[]T≡ U[]         = refl
[]T≡ (El[] t𝒢)   = {!  []≡ t𝒢 !}
[]T≡ (Π[] A𝒢 B𝒢) = {! []T≡ B𝒢  !}

[]≡ {q = T} (`[] t𝒢)      = {!t𝒢   !}
[]≡ {q = T} (lam[] t𝒢)    = {!   !}
[]≡ {q = T} (app[] t𝒢 u𝒢) = {!   !}
[]≡ {q = V} vz^           = {! t𝒢 !}
[]≡ {q = V} (vs^ i𝒢 i[]𝒢) = {! t𝒢 !}
[]≡ {q = V} vs<>          = {!!}
[]≡ {q = V} i[wk]         = {!!}
[]≡ {q = V} (vz<> t≡)     = t≡
